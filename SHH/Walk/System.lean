import Mathlib

/-!
# The walk: expected steps as a linear system

Shrager, Hogg & Huberman (1988), p. 416, idealize problem solving as a one-dimensional
random walk on the distance to the goal: states 0, …, D, the goal 0 absorbing; from distance
k the solver moves one step closer with probability `p` (the paper's P₋, Eq. 1) and one step
farther with probability `1 - p`; the walk is "constrained to remain within distance D", which
we read as forced reflection at D (a step from D goes to D − 1). The expected number of
steps to reach the goal, `T k` from distance `k`, satisfies the linear system below
(van Kampen 1981, ch. XII; the paper's "standard techniques").

Postulate W (the walk) is the system itself. SIMPLIFIED: the system is taken as the definition
of expected steps; OPEN: derive it as the limit of finite-horizon expectations of the chain.

The boundary convention matters: the paper reports s = D² in the symmetric case, which holds
for forced reflection (`SHH.Walk.s_half`); staying at D with probability `1 - p` gives
D² + D (`SysStay`, kept here for comparison).
-/

namespace SHH.Walk

/-- **The system for expected steps** (postulate W): from distance `k` with `1 ≤ k < D`, one
step plus the expectation after moving closer (probability `p`) or farther (`1 - p`); at the
goal nothing remains; at `D`, forced reflection. -/
structure Sys (p : ℚ) (D : ℕ) (T : ℕ → ℚ) : Prop where
  zero : T 0 = 0
  interior : ∀ k, 1 ≤ k → k < D → T k = 1 + p * T (k - 1) + (1 - p) * T (k + 1)
  top : 0 < D → T D = 1 + T (D - 1)

/-- The other boundary convention: at `D`, stay with probability `1 - p`. Not the paper's
(see `s_half` and `stay_half`). -/
structure SysStay (p : ℚ) (D : ℕ) (T : ℕ → ℚ) : Prop where
  zero : T 0 = 0
  interior : ∀ k, 1 ≤ k → k < D → T k = 1 + p * T (k - 1) + (1 - p) * T (k + 1)
  top : 0 < D → T D = 1 + p * T (D - 1) + (1 - p) * T D

end SHH.Walk
