import SHH.BitGame.Decision

/-!
# A perfect decision procedure on the initial operators: every move is toward the goal

With only the initial one-bit operators (the hypercube, P2), every move changes the distance to
the goal by exactly one, and from any state other than the goal some move reduces it
(`succs_ham`, `exists_closer`). At `r = 1` the decision procedure (P3) keeps only the moves
that minimize the distance and gives the others probability zero, so **every move it can make
reduces the Hamming distance by exactly one** (`r1_moves_closer`), for every number of bits.
Every run therefore reaches the goal in exactly the Hamming distance's number of moves: the
paper's "r = 1 corresponds to a perfect decision procedure in which search and backtracking are
never required" (p. 415), proved for the initial operators. With learned operators this fails
(see `notes/CLAIMS.md`, S3).
-/

namespace SHH.BitGame

theorem apply_cons (e : Entry) (o : Op) (c : Bool) (x : State) :
    apply (e :: o) (c :: x) = if e.ok c then (apply o x).map (List.cons (e.res c)) else none := by
  unfold apply
  by_cases h1 : e.ok c = true
  · by_cases h2 : o.length = x.length ∧ (List.zipWith Entry.ok o x).all id = true
    · simp [h1, h2]
    · simp only [List.length_cons, Nat.add_right_cancel_iff, List.zipWith_cons_cons,
        List.all_cons, id, h1, Bool.true_and, if_true]
      rw [if_neg h2, if_neg h2]; rfl
  · simp [h1]

theorem apply_replicate (x : State) : apply (List.replicate x.length none) x = some x := by
  induction x with
  | nil => simp [apply]
  | cons c x ih =>
    rw [List.length_cons, List.replicate_succ, apply_cons]
    simp [Entry.ok, Entry.res, ih]

/-- **A one-bit operator flips its bit, if the bit matches.** -/
theorem apply_flip (x : State) (i : Nat) (a : Bool) (hi : i < x.length) :
    apply (flipOp x.length i a) x = if x[i]? = some a then some (x.set i (!a)) else none := by
  induction x generalizing i with
  | nil => simp at hi
  | cons c x ih =>
    cases i with
    | zero =>
      simp only [List.length_cons, flipOp, apply_cons, Entry.ok, Entry.res, apply_replicate,
        List.getElem?_cons_zero, Option.some.injEq, List.set_cons_zero]
      by_cases h : c = a <;> simp [h]
    | succ i =>
      simp only [List.length_cons, flipOp, apply_cons, Entry.ok, Entry.res,
        List.getElem?_cons_succ, List.set_cons_succ, if_true]
      rw [ih i (by simp at hi; omega)]
      split <;> simp

theorem ham_cons (c d : Bool) (x g : State) :
    ham (c :: x) (d :: g) = (if c = d then 0 else 1) + ham x g := by
  unfold ham
  simp only [List.zipWith_cons_cons, List.count_cons]
  by_cases h : c = d <;> simp [h] <;> omega

/-- **Flipping one bit changes the distance by one**: up if the bit already agreed with the
goal, down if it did not. -/
theorem ham_flip (x g : State) (i : Nat) (a c : Bool) (hx : x[i]? = some a) (hg : g[i]? = some c) :
    (a = c → ham (x.set i (!a)) g = ham x g + 1) ∧ (a ≠ c → ham (x.set i (!a)) g + 1 = ham x g) := by
  induction x generalizing g i with
  | nil => simp at hx
  | cons b x ih =>
    cases g with
    | nil => simp at hg
    | cons d g =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hg
        subst hx; subst hg
        simp only [List.set_cons_zero, ham_cons]
        constructor
        · intro h; subst h; cases b <;> simp [ham_cons] <;> omega
        · intro h; cases b <;> cases d <;> simp_all [ham_cons] <;> omega
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx hg
        simp only [List.set_cons_succ, ham_cons]
        have := ih g i hx hg
        constructor
        · intro h; rw [this.1 h]; omega
        · intro h; have := this.2 h; omega

theorem mem_initialOps (B : Nat) (o : Op) :
    o ∈ initialOps B ↔ ∃ i, i < B ∧ ∃ a, o = flipOp B i a := by
  simp only [initialOps, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff,
    or_false]
  constructor
  · rintro ⟨i, hi, h | h⟩ <;> exact ⟨i, hi, _, h⟩
  · rintro ⟨i, hi, a, rfl⟩; cases a
    · exact ⟨i, hi, Or.inl rfl⟩
    · exact ⟨i, hi, Or.inr rfl⟩

/-- **The successors under the initial operators are the one-bit flips.** -/
theorem mem_succs (x : State) (y : State) :
    y ∈ succs (initialOps x.length) x ↔ ∃ i a, x[i]? = some a ∧ y = x.set i (!a) := by
  simp only [succs, List.mem_filterMap, mem_initialOps]
  constructor
  · rintro ⟨o, ⟨i, hi, a, rfl⟩, h⟩
    rw [apply_flip x i a hi] at h
    split at h
    · exact ⟨i, a, by assumption, by simp_all⟩
    · simp at h
  · rintro ⟨i, a, hx, rfl⟩
    have hi : i < x.length := by
      rcases List.getElem?_eq_some_iff.1 hx with ⟨h, _⟩; exact h
    exact ⟨flipOp x.length i a, ⟨i, hi, a, rfl⟩, by rw [apply_flip x i a hi, if_pos hx]⟩

/-- Every successor is one step closer or one step farther. -/
theorem succs_ham (x g : State) (hlen : x.length = g.length) (y : State)
    (hy : y ∈ succs (initialOps x.length) x) :
    ham y g = ham x g + 1 ∨ ham y g + 1 = ham x g := by
  obtain ⟨i, a, hx, rfl⟩ := (mem_succs x y).1 hy
  have hi : i < g.length := by
    rcases List.getElem?_eq_some_iff.1 hx with ⟨h, _⟩; omega
  obtain ⟨c, hc⟩ : ∃ c, g[i]? = some c := ⟨g[i], List.getElem?_eq_getElem hi⟩
  have := ham_flip x g i a c hx hc
  by_cases h : a = c
  · exact Or.inl (this.1 h)
  · exact Or.inr (this.2 h)

/-- From any state but the goal, some successor is one step closer. -/
theorem exists_closer (x g : State) (hlen : x.length = g.length) (hne : x ≠ g) :
    ∃ y ∈ succs (initialOps x.length) x, ham y g + 1 = ham x g := by
  have : ∃ (i : Nat) (a c : Bool), x[i]? = some a ∧ g[i]? = some c ∧ a ≠ c := by
    by_contra hno
    push Not at hno
    apply hne
    apply List.ext_getElem?
    intro n
    by_cases hn : n < x.length
    · obtain ⟨a, ha⟩ : ∃ a, x[n]? = some a := ⟨x[n], List.getElem?_eq_getElem hn⟩
      obtain ⟨c, hc⟩ : ∃ c, g[n]? = some c := ⟨g[n], List.getElem?_eq_getElem (by omega)⟩
      rw [ha, hc, hno n a c ha hc]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  obtain ⟨i, a, c, hx, hg, hac⟩ := this
  exact ⟨x.set i (!a), (mem_succs x _).2 ⟨i, a, hx, rfl⟩, (ham_flip x g i a c hx hg).2 hac⟩

theorem best_le (g : State) (ys : List State) (y : State) (hy : y ∈ ys) : best g ys ≤ ham y g := by
  induction ys with
  | nil => simp at hy
  | cons z ys ih =>
    simp only [best, List.map_cons, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Nat.min_le_left _ _
    · exact le_trans (Nat.min_le_right _ _) (ih hy)

theorem le_best (g : State) (ys : List State) (k : Nat) (h : ∀ y ∈ ys, k ≤ ham y g)
    (hk : k ≤ g.length + 1) : k ≤ best g ys := by
  induction ys with
  | nil => simpa [best] using hk
  | cons z ys ih =>
    simp only [best, List.map_cons, List.foldr_cons] at ih ⊢
    exact le_min (h z (List.mem_cons_self ..)) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem ham_le (x g : State) : ham x g ≤ g.length := by
  unfold ham
  calc _ ≤ (List.zipWith (· != ·) x g).length := List.count_le_length
    _ ≤ g.length := by simp

/-- **With a perfect decision procedure and the initial operators, every move is toward the
goal**: any successor given positive probability at `r = 1` is exactly one bit closer.
Postulates P1–P3; condition `r = 1`; for every number of bits, every state and every goal. -/
theorem r1_moves_closer (x g : State) (hlen : x.length = g.length) (hne : x ≠ g) :
    ∀ yp ∈ stepDist (initialOps x.length) 1 g x, 0 < yp.2 → ham yp.1 g + 1 = ham x g := by
  intro yp hyp hp
  obtain ⟨y₀, hy₀, hcl⟩ := exists_closer x g hlen hne
  have hne' : succs (initialOps x.length) x ≠ [] := List.ne_nil_of_mem hy₀
  set d := ham x g
  have hm : best g (succs (initialOps x.length) x) = d - 1 := by
    apply le_antisymm
    · have := best_le g _ y₀ hy₀; omega
    · apply le_best
      · intro y hy
        rcases succs_ham x g hlen y hy with h | h <;> omega
      · have := ham_le x g; omega
  simp only [stepDist, hne', if_false, List.mem_append, List.mem_map, List.mem_filter] at hyp
  rcases hyp with ⟨y, ⟨_, hy⟩, rfl⟩ | ⟨y, ⟨_, _⟩, rfl⟩
  · simp only [beq_iff_eq, hm] at hy
    have : 1 ≤ d := by omega
    simp only; omega
  · simp [pBad] at hp

end SHH.BitGame
