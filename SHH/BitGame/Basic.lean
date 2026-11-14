import Mathlib

/-!
# The bit game: states, operators, chunking

Shrager, Hogg & Huberman (1988), pp. 414–415 (postulates P1, P2, P4 of `notes/POSTULATES.md`).

* A **state** is a vector of `B` bits (P1).
* An **operator** is a pattern → result pair with don't-care positions (P1): each position is
  either `none` (don't care: it must not change) or `some (a, b)`: the position must hold `a`
  and becomes `b`. The operator applies when every specified position matches.
* The **initial operators** are the `2B` one-bit operators, bit `i` from `0` to `1` and from `1`
  to `0` (P2): "a B-dimensional hypercube".
* **Chunking** a solved game `start → goal` adds the operator with `(start_i, goal_i)` where the
  two differ and don't-care where they agree (P4): "the operator that solves this particular game
  in one step". For `01110 → 10101` it is `01?10 → 10?01` (`chunk_paper`), which applies to
  exactly two states (`chunk_paper_applies`): it "connects two pairs of states".

`chunk_apply` proves in general that a chunk takes its own start to its own goal.
-/

namespace SHH.BitGame

/-- A state: a vector of bits. -/
abbrev State := List Bool

/-- One position of an operator: don't care, or `(must hold, becomes)`. -/
abbrev Entry := Option (Bool × Bool)

/-- An operator: one entry per position. -/
abbrev Op := List Entry

def Entry.ok : Entry → Bool → Bool
  | none, _ => true
  | some (a, _), x => x == a

def Entry.res : Entry → Bool → Bool
  | none, x => x
  | some (_, b), _ => b

/-- Apply an operator: `none` if it does not apply (wrong length or a fixed bit mismatches). -/
def apply (o : Op) (x : State) : Option State :=
  if o.length = x.length ∧ (List.zipWith Entry.ok o x).all id then
    some (List.zipWith Entry.res o x)
  else none

/-- The Hamming distance. -/
def ham (x y : State) : Nat := (List.zipWith (· != ·) x y).count true

/-- The one-bit operator on position `i` of `B`, from `a` to `!a`. -/
def flipOp (B i : Nat) (a : Bool) : Op :=
  (List.range B).map fun j => if j = i then some (a, !a) else none

/-- **The initial operators** (P2): the `2B` one-bit operators. -/
def initialOps (B : Nat) : List Op :=
  (List.range B).flatMap fun i => [flipOp B i false, flipOp B i true]

/-- **Chunking** (P4): the operator that solves `s → g` in one step. -/
def chunk (s g : State) : Op :=
  List.zipWith (fun a b => if a = b then none else some (a, b)) s g

/-- All states of `B` bits. -/
def allStates : Nat → List State
  | 0 => [[]]
  | B + 1 => (allStates B).flatMap fun x => [false :: x, true :: x]

theorem chunk_length (s g : State) (h : s.length = g.length) : (chunk s g).length = s.length := by
  simp [chunk, h]

theorem chunk_ok (s g : State) (h : s.length = g.length) :
    (List.zipWith Entry.ok (chunk s g) s).all id = true := by
  induction s generalizing g with
  | nil => simp [chunk]
  | cons a s ih =>
    cases g with
    | nil => simp at h
    | cons b g =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have := ih g h
      simp only [chunk] at this ⊢
      simp only [List.zipWith_cons_cons, List.all_cons, this, Bool.and_true]
      split <;> simp [Entry.ok]

theorem chunk_res (s g : State) (h : s.length = g.length) :
    List.zipWith Entry.res (chunk s g) s = g := by
  induction s generalizing g with
  | nil => cases g <;> simp_all [chunk]
  | cons a s ih =>
    cases g with
    | nil => simp at h
    | cons b g =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have := ih g h
      simp only [chunk] at this ⊢
      simp only [List.zipWith_cons_cons, this]
      split
      · simp [Entry.res, *]
      · simp [Entry.res]

/-- **A chunk takes its own start to its own goal**, in one step (P4). -/
theorem chunk_apply (s g : State) (h : s.length = g.length) : apply (chunk s g) s = some g := by
  unfold apply
  rw [if_pos ⟨chunk_length s g h, chunk_ok s g h⟩, chunk_res s g h]

/-- The paper's example: `01110 → 10101` chunks to `01?10 → 10?01`. -/
theorem chunk_paper :
    chunk [false, true, true, true, false] [true, false, true, false, true] =
      [some (false, true), some (true, false), none, some (true, false), some (false, true)] := by
  decide

/-- **It connects two pairs of states**: of the 32 five-bit states it applies to exactly
`01010` and `01110`. -/
theorem chunk_paper_applies :
    (allStates 5).filter (fun x =>
      (apply (chunk [false, true, true, true, false] [true, false, true, false, true]) x).isSome) =
      [[false, true, false, true, false], [false, true, true, true, false]] := by
  decide

theorem initialOps_length (B : Nat) : (initialOps B).length = 2 * B := by
  induction B with
  | zero => rfl
  | succ B ih =>
    simp only [initialOps, List.range_succ, List.flatMap_append, List.length_append] at ih ⊢
    simp [List.length_flatMap] at ih ⊢
    omega

end SHH.BitGame
