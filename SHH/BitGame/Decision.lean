import SHH.BitGame.Basic

/-!
# The decision procedure with parameter `r`

Postulate P3 (p. 415): at a state, find the applicable operators and their successors; the
**good** successors minimize the Hamming distance to the goal, the others are **bad**; each bad
one is removed with probability `r`; one is chosen uniformly from what remains. With `G` good
and `b` bad successors, the number `K` of bad ones kept is binomial `(b, 1 − r)`, so

* each good successor is chosen with probability `Σ_k P(K = k) / (G + k)` (`pGood`),
* each bad one with probability `(1 − r) Σ_k P(K' = k) / (G + 1 + k)`, `K'` binomial `(b − 1, 1 − r)`
  (`pBad`).

`r = 1` chooses uniformly among the good ones; `r = 0` uniformly among all (a random walk on the
operator graph). `stepDist` is the resulting distribution over next states, as a list of
weighted outcomes (duplicates not merged). SIMPLIFIED: a state with no applicable operator
stays put (never happens with the initial operators, which apply everywhere).
-/

namespace SHH.BitGame

/-- `P(K = k)` for `K` binomial `(n, 1 − r)`. -/
def binom (n k : Nat) (r : ℚ) : ℚ := (Nat.choose n k : ℚ) * (1 - r)^k * r^(n - k)

/-- The probability of each good successor. -/
def pGood (G b : Nat) (r : ℚ) : ℚ :=
  ((List.range (b + 1)).map fun k => binom b k r / ((G + k : Nat) : ℚ)).sum

/-- The probability of each bad successor. -/
def pBad (G b : Nat) (r : ℚ) : ℚ :=
  (1 - r) * ((List.range b).map fun k => binom (b - 1) k r / ((G + 1 + k : Nat) : ℚ)).sum

/-- The successors of `x` under the operators. -/
def succs (ops : List Op) (x : State) : List State := ops.filterMap fun o => apply o x

/-- The smallest distance to the goal among the successors. -/
def best (g : State) (ys : List State) : Nat := (ys.map fun y => ham y g).foldr min (g.length + 1)

/-- **One decision (P3)**: the distribution over next states. -/
def stepDist (ops : List Op) (r : ℚ) (g x : State) : List (State × ℚ) :=
  let ys := succs ops x
  if ys = [] then [(x, 1)] else
  let m := best g ys
  let good := ys.filter fun y => ham y g == m
  let bad := ys.filter fun y => ham y g != m
  good.map (fun y => (y, pGood good.length bad.length r)) ++
    bad.map (fun y => (y, pBad good.length bad.length r))

/-- Total probability of a weighted list. -/
def mass (d : List (State × ℚ)) : ℚ := (d.map Prod.snd).sum

/-- The step distribution is a probability distribution at every state of the three-bit game,
for every goal, at `r = 0, 1/2, 1`, with the initial operators. -/
theorem stepDist_mass_three :
    ∀ r ∈ [(0 : ℚ), 1/2, 1], ∀ g ∈ allStates 3, ∀ x ∈ allStates 3,
      mass (stepDist (initialOps 3) r g x) = 1 := by
  decide +kernel

end SHH.BitGame
