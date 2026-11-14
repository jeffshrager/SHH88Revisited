import Mathlib

/-!
# Expected hitting times of a finite chain

A finite Markov chain is given by a list of states and, for each state, a list of weighted
successors. The expected number of steps to reach a goal `g` satisfies

  T g = 0,   T x = 1 + Σ p · T y   (x ≠ g),

(`HitSys`). `hit_unique` proves this system has at most one solution when the weights are
nonnegative and sum to one, successors stay among the states, and the goal is reachable
from every state with positive probability (`Reach`). The proof is the maximum principle:
the difference `U` of two solutions is harmonic away from the goal, so a state where `U` is
maximal passes its maximum to every successor, and following a path to the goal forces the
maximum to be `U g = 0`.

So a table checked to satisfy the system (by evaluation) *is* the vector of expected steps.
`reachB` is a bounded search whose success implies `Reach` (`reachB_sound`), so reachability
is checked by evaluation too. This is a library fact about chains, not about cognition.
-/

namespace SHH.Markov

variable {S : Type}

theorem sum_zero_of_nonneg (l : List ℚ) (h : ∀ t ∈ l, 0 ≤ t) (hs : l.sum = 0) : ∀ t ∈ l, t = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.mem_cons, forall_eq_or_imp, List.sum_cons] at h hs ⊢
    have hl : 0 ≤ l.sum := List.sum_nonneg h.2
    have ha : a = 0 := by linarith [h.1]
    exact ⟨ha, ih h.2 (by linarith)⟩

/-- The expectation of `T` under a weighted list. -/
def ev (d : List (S × ℚ)) (T : S → ℚ) : ℚ := (d.map fun yp => yp.2 * T yp.1).sum

/-- **The system for expected steps to `g`.** -/
structure HitSys (states : List S) (step : S → List (S × ℚ)) (g : S) (T : S → ℚ) : Prop where
  goal : T g = 0
  eqn : ∀ x ∈ states, x ≠ g → T x = 1 + ev (step x) T

/-- The goal is reachable from `x` by steps of positive probability. -/
inductive Reach (step : S → List (S × ℚ)) (g : S) : S → Prop
  | here : Reach step g g
  | next {x y : S} {p : ℚ} : (y, p) ∈ step x → 0 < p → Reach step g y → Reach step g x

/-- A bounded search for a path to the goal. -/
def reachB [DecidableEq S] (step : S → List (S × ℚ)) (g : S) : ℕ → S → Bool
  | 0, x => x == g
  | n + 1, x => x == g || (step x).any fun yp => decide (0 < yp.2) && reachB step g n yp.1

theorem reachB_sound [DecidableEq S] (step : S → List (S × ℚ)) (g : S) :
    ∀ n x, reachB step g n x = true → Reach step g x := by
  intro n
  induction n with
  | zero => intro x h; simp [reachB] at h; subst h; exact Reach.here
  | succ n ih =>
    intro x h
    simp only [reachB, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at h
    rcases h with h | ⟨⟨y, p⟩, hm, hp, hr⟩
    · subst h; exact Reach.here
    · exact Reach.next hm hp (ih y hr)

theorem ev_sub (d : List (S × ℚ)) (T₁ T₂ : S → ℚ) :
    ev d T₁ - ev d T₂ = ev d (fun x => T₁ x - T₂ x) := by
  induction d with
  | nil => simp [ev]
  | cons a d ih => simp only [ev, List.map_cons, List.sum_cons] at ih ⊢; rw [← ih]; ring

theorem gap_eq (d : List (S × ℚ)) (U : S → ℚ) (M : ℚ) :
    (d.map Prod.snd).sum * M - ev d U = (d.map fun yp => yp.2 * (M - U yp.1)).sum := by
  induction d with
  | nil => simp [ev]
  | cons a d ih =>
    simp only [ev, List.map_cons, List.sum_cons] at ih ⊢
    linear_combination ih

/-- **Expected hitting times are unique.** Two solutions of the system agree at every state. -/
theorem hit_unique [DecidableEq S] (states : List S) (step : S → List (S × ℚ)) (g : S) (T₁ T₂ : S → ℚ)
    (hg : g ∈ states)
    (hnn : ∀ x ∈ states, ∀ yp ∈ step x, 0 ≤ yp.2)
    (hmass : ∀ x ∈ states, x ≠ g → ((step x).map Prod.snd).sum = 1)
    (hcl : ∀ x ∈ states, ∀ yp ∈ step x, yp.1 ∈ states)
    (hreach : ∀ x ∈ states, Reach step g x)
    (h₁ : HitSys states step g T₁) (h₂ : HitSys states step g T₂) :
    ∀ x ∈ states, T₁ x = T₂ x := by
  -- one direction, for any ordered pair of solutions
  have half : ∀ (A B : S → ℚ), HitSys states step g A → HitSys states step g B →
      ∀ x ∈ states, A x - B x ≤ 0 := by
    intro A B hA hB
    set U : S → ℚ := fun x => A x - B x with hU
    have hUg : U g = 0 := by simp [hU, hA.goal, hB.goal]
    have harm : ∀ x ∈ states, x ≠ g → U x = ev (step x) U := by
      intro x hx hxg
      simp only [hU]; rw [hA.eqn x hx hxg, hB.eqn x hx hxg, ← ev_sub]; ring
    have hne : states.toFinset.Nonempty := ⟨g, by simpa using hg⟩
    obtain ⟨xm, hxm, hmax⟩ := states.toFinset.exists_max_image U hne
    simp only [List.mem_toFinset] at hxm hmax
    set M := U xm
    by_contra hpos
    push Not at hpos
    obtain ⟨x0, hx0, hx0pos⟩ := hpos
    have hMpos : 0 < M := lt_of_lt_of_le hx0pos (hmax x0 hx0)
    -- along any path to the goal, a state at the maximum passes it on
    have key : ∀ z, Reach step g z → z ∈ states → U z = M → False := by
      intro z hz
      induction hz with
      | here => intro _ h; rw [hUg] at h; linarith
      | @next x y p hm hp hr ih =>
        intro hx hUx
        have hxg : x ≠ g := by intro h; subst h; rw [hUg] at hUx; linarith
        have hy : y ∈ states := hcl x hx (y, p) hm
        apply ih hy
        have hgap := gap_eq (step x) U M
        rw [hmass x hx hxg, one_mul, ← harm x hx hxg, hUx, sub_self] at hgap
        have hterms : ∀ t ∈ (step x).map (fun yp => yp.2 * (M - U yp.1)), 0 ≤ t := by
          intro t ht
          simp only [List.mem_map] at ht
          obtain ⟨⟨y', p'⟩, hm', rfl⟩ := ht
          exact mul_nonneg (hnn x hx _ hm') (by linarith [hmax y' (hcl x hx _ hm')])
        have hz := sum_zero_of_nonneg _ hterms hgap.symm
        have := hz (p * (M - U y)) (List.mem_map.2 ⟨(y, p), hm, rfl⟩)
        rcases mul_eq_zero.1 this with h0 | h0
        · linarith
        · linarith
    exact key xm (hreach xm hxm) hxm rfl
  intro x hx
  have a := half T₁ T₂ h₁ h₂ x hx
  have b := half T₂ T₁ h₂ h₁ x hx
  linarith

end SHH.Markov
