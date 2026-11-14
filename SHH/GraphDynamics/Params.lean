import SHH.Walk.Regimes

/-!
# The graph-dynamic parameterization

Shrager, Hogg & Huberman (1988), p. 416, idealize a typical problem space as a random graph
(idealization I1): `n` nodes, mean branching `μ`, start and goal about the diameter
`D = ln n / ln μ` apart, and at each node one edge toward the goal and `μ − 1` away. The
decision procedure removes each bad edge with probability `r` (idealization I2), so a step
goes toward the goal with probability

  P₋ = 1 / (1 + (μ − 1)(1 − r))        (Eq. 1)

`pOf` and `DOf` are these two maps, over the reals. Nothing here derives them from the bit
game; they are the paper's idealizations, stated as definitions.

The paper's Eq. 5 comes from Eq. 4 with `(1 − p)/p = (μ − 1)(1 − r)`, approximating
`(μ − 1)^(D−1)` by `μ^(D−1) = n/μ` (the printed equations are in `notes/equations.txt`). `eq5_error_factor` and `eq5_error_bound` give the omitted factor,
`((μ − 1)/μ)^D ≤ exp(−D/μ)`: at `μ = 3`, `n = 10⁴` (`D ≈ 8.4`) it is below `e^{−2.8}`, so
the approximation is off by more than an order of magnitude where the paper applies it to
small `μ`.
-/

namespace SHH.GD

/-- **Eq. 1** (idealization I2): the probability of a step toward the goal, from the mean
branching `μ` and the decision effectiveness `r`. -/
noncomputable def pOf (μ r : ℝ) : ℝ := 1 / (1 + (μ - 1) * (1 - r))

/-- **The diameter** (idealization I1): `D = ln n / ln μ`. -/
noncomputable def DOf (n μ : ℝ) : ℝ := Real.log n / Real.log μ

theorem pOf_one (μ : ℝ) : pOf μ 1 = 1 := by simp [pOf]

theorem pOf_zero (μ : ℝ) : pOf μ 0 = 1 / μ := by
  unfold pOf; congr 1; ring

theorem pOf_pos (μ r : ℝ) (hμ : 2 ≤ μ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : 0 < pOf μ r := by
  unfold pOf
  apply div_pos one_pos
  nlinarith

theorem pOf_le_one (μ r : ℝ) (hμ : 2 ≤ μ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : pOf μ r ≤ 1 := by
  unfold pOf
  rw [div_le_one (by nlinarith)]
  nlinarith

/-- With no decision procedure a step is toward the goal with probability `1/μ`, below `1/2`
as soon as `μ > 2`: the random walk is in the diffusion regime on any graph with mean
branching above 2. -/
theorem pOf_zero_lt_half (μ : ℝ) (hμ : 2 < μ) : pOf μ 0 < 1/2 := by
  rw [pOf_zero]
  rw [div_lt_div_iff_of_pos_left one_pos (by linarith) (by norm_num)]
  linarith

/-- **The factor Eq. 5 omits**: `(μ − 1)^D = μ^D · ((μ − 1)/μ)^D`. -/
theorem eq5_error_factor (μ : ℝ) (hμ : μ ≠ 0) (D : ℕ) :
    (μ - 1)^D = μ^D * ((μ - 1)/μ)^D := by
  rw [← mul_pow]; congr 1; field_simp

/-- **The omitted factor is at most `exp(−D/μ)`**, from `1 − 1/μ ≤ exp(−1/μ)`. -/
theorem eq5_error_bound (μ : ℝ) (hμ : 1 ≤ μ) (D : ℕ) :
    ((μ - 1)/μ)^D ≤ Real.exp (-(D : ℝ)/μ) := by
  have hμ0 : 0 < μ := by linarith
  have h1 : (μ - 1)/μ = -(1/μ) + 1 := by field_simp; ring
  have h2 : (μ - 1)/μ ≤ Real.exp (-(1/μ)) := by
    rw [h1]; exact Real.add_one_le_exp _
  have h0 : 0 ≤ (μ - 1)/μ := div_nonneg (by linarith) hμ0.le
  calc ((μ - 1)/μ)^D ≤ (Real.exp (-(1/μ)))^D := pow_le_pow_left₀ h0 h2 D
    _ = Real.exp ((D : ℝ) * (-(1/μ))) := (Real.exp_nat_mul _ D).symm
    _ = Real.exp (-(D : ℝ)/μ) := by congr 1; ring

end SHH.GD
