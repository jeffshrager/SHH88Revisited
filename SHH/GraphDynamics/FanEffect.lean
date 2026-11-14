import SHH.GraphDynamics.Params
import SHH.Phenomena.LearningCurve

/-!
# The fan effect in the idealized model

Adding edges raises the mean branching `μ`, which does two things in the paper's idealization:
it shortens the diameter `D = ln n / ln μ`, and it lowers the probability of a step toward the
goal, `p = 1/(1 + (μ − 1)(1 − r))`. The paper says the first wins at `r = 0` and `r = 1`
(improvement with practice) and the second wins over a range at intermediate `r` (the
problem-solving fan effect), with the condition "|ln(1 − r)| ln n > (ln μ)²" (p. 416).

Here the trade-off is made exact at settings where `D` is an integer, so the walk's closed
form applies without real exponents: `n = 2^16` nodes and `μ ∈ {2, 4, 16, 256}`, where `D` is
exactly `16, 8, 4, 2` (`DOf_pow2`). At `r = 0`, going from `μ = 2` to `μ = 4` raises the
expected steps from 256 to 9824, and by `μ = 16` they have fallen again, to 7744
(`fan_pow2_zero`; numerically the peak is near `μ = 6`). So the paper's own idealized model shows a fan effect at `r = 0`, where
the paper says more edges always help; its Eq. 5 reaches that conclusion by replacing
`(μ − 1)^(D−1)` with `μ^(D−1) = n/μ` (see `eq5_error_bound`), an approximation the paper
states for `μ(1 − r) ≫ 1`, which excludes the small `μ` where the rise occurs.

The effect depends on the size of the space. At `n = 8, 16` the same model shows no fan
effect at `r = 0` or at `r = 1/2` (`no_fan_small`). The bit game at that size improves on
average at `r = 0` and worsens at `r = 1/2` (`SHH.BitGame.figure1_pattern_three`), so at the
game's own size the idealization agrees with the game at `r = 0` and misses its fan effect
at `r = 1/2`.

OPEN: the same at non-integer `D` (the closed form with a real exponent), and an exact
condition for the sign of `ds/dμ` in the drift regime to replace the paper's.
-/

namespace SHH.GD

open Real

/-- **The diameters are exact at powers of two**: with `n = 2^16`, `D(n, 2^k) = 16/k`. -/
theorem DOf_pow2 (k : ℕ) (hk : 0 < k) : DOf ((2 : ℝ)^16) ((2 : ℝ)^k) = 16 / k := by
  unfold DOf
  rw [Real.log_pow, Real.log_pow]
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk' : (k : ℝ) ≠ 0 := by positivity
  field_simp
  norm_num

theorem DOf_2_2 : DOf ((2 : ℝ)^16) 2 = 16 := by
  have := DOf_pow2 1 one_pos; simpa using this
theorem DOf_2_4 : DOf ((2 : ℝ)^16) 4 = 8 := by
  have := DOf_pow2 2 (by norm_num); norm_num at this ⊢; exact this
theorem DOf_2_16 : DOf ((2 : ℝ)^16) 16 = 4 := by
  have := DOf_pow2 4 (by norm_num); norm_num at this ⊢; exact this
theorem DOf_2_256 : DOf ((2 : ℝ)^16) 256 = 2 := by
  have := DOf_pow2 8 (by norm_num); norm_num at this ⊢; exact this

/-- At `r = 0`, `p = 1/μ` (`pOf_zero`), so the four settings are the walks
`s (1/2) 16`, `s (1/4) 8`, `s (1/16) 4`, `s (1/256) 2`. -/
theorem pOf_zero_values : pOf 2 0 = 1/2 ∧ pOf 4 0 = 1/4 ∧ pOf 16 0 = 1/16 ∧ pOf 256 0 = 1/256 := by
  simp only [pOf_zero]; norm_num

/-- **A fan effect at `r = 0` in the paper's idealized model.** With `n = 2^16` nodes and
no decision procedure, raising the mean branching from 2 to 4 raises the expected steps from
256 to 9824; from 4 to 16 lowers them to 7744; from 16 to 256 to 512. More edges hurt first
and help later. (Postulates: the walk, I1, I2; condition: `r = 0`.) -/
theorem fan_pow2_zero :
    Walk.s (1/2) 16 = 256 ∧ Walk.s (1/4) 8 = 9824 ∧ Walk.s (1/16) 4 = 7744 ∧
      Walk.s (1/256) 2 = 512 := by
  unfold Walk.s; norm_num

/-- The same fact as a worsening: the curve of expected steps over the four settings, read
in order of increasing `μ`, worsens from its first point to its second. -/
theorem fan_pow2_worsens :
    Phenomena.Worsens (fun i => [Walk.s (1/2) 16, Walk.s (1/4) 8, Walk.s (1/16) 4,
      Walk.s (1/256) 2].getD i 0) 0 3 := by
  refine ⟨0, le_rfl, by norm_num, ?_⟩
  show Walk.s (1/2) 16 < Walk.s (1/4) 8
  unfold Walk.s; norm_num

/-- At `r = 1/2` and the same `n`: `p = 1/(1 + (μ − 1)/2)`; `μ = 2 → p = 2/3, D = 16`;
`μ = 4 → p = 2/5, D = 8`; `μ = 16 → p = 2/17, D = 4`. Steps 44.0 → 255.5 → 1117.75:
the fan effect at the paper's "mediocre" setting, exactly. -/
theorem fan_pow2_half :
    Walk.s (2/3) 16 < Walk.s (2/5) 8 ∧ Walk.s (2/5) 8 < Walk.s (2/17) 4 := by
  unfold Walk.s; norm_num

theorem pOf_half_values : pOf 2 (1/2) = 2/3 ∧ pOf 4 (1/2) = 2/5 ∧ pOf 16 (1/2) = 2/17 := by
  unfold pOf; norm_num

/-- The `r = 1/2` column exactly, including `μ = 256` (`p = 2/257`, `D = 2`):
`720897/16384 ≈ 44.0`, `16355/64 ≈ 255.5`, `4471/4 = 1117.75`, `257`. So at `r = 1/2` more
edges still hurt at `μ = 16` and help only by `μ = 256`. -/
theorem fan_pow2_half_values :
    Walk.s (2/3) 16 = 720897/16384 ∧ Walk.s (2/5) 8 = 16355/64 ∧ Walk.s (2/17) 4 = 4471/4 ∧
      Walk.s (2/257) 2 = 257 := by
  unfold Walk.s; norm_num

/-! ### The fan effect depends on the size of the space

The same idealized model at the size of the games that can be solved exactly: `n = 2^m` for
`m = 3, 4` (the three- and four-bit games' state counts), at every `μ = 2^k` with `k ∣ m`,
where the diameter is the integer `m/k` (`DOf_pow2_gen`). Between those settings, and at
`n = 32`, the prototype (`tools/walk_check.py`, real exponent) also shows no rise; by
`n = 64` a slight one appears (36 → 39.8 at `μ = 3`, `r = 0`). NOT MODELED: a certificate at
non-integer `D`. -/

/-- The diameters at powers of two, any size: `D(2^m, 2^k) = m/k`. -/
theorem DOf_pow2_gen (m k : ℕ) (hk : 0 < k) : DOf ((2 : ℝ)^m) ((2 : ℝ)^k) = m / k := by
  unfold DOf
  rw [Real.log_pow, Real.log_pow]
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk' : (k : ℝ) ≠ 0 := by positivity
  field_simp

/-- **No fan effect in small spaces, in the paper's idealized model.** With `n = 8` or `16`
nodes, the expected steps fall at every increase of `μ` over the integer-diameter settings,
both with no decision procedure (`r = 0`: 9 → 1; 16 → 8 → 1) and with a mediocre one
(`r = 1/2`: 11/2 → 1; 33/4 → 5 → 1). The fan
effect of `fan_pow2_zero` and `fan_pow2_half` is a property of large spaces. (Postulates: the
walk, I1, I2.) -/
theorem no_fan_small :
    -- n = 8: μ = 2, 8 (D = 3, 1)
    (Walk.s (1/2) 3 = 9 ∧ Walk.s (1/8) 1 = 1) ∧ (Walk.s (2/3) 3 = 11/2 ∧ Walk.s (2/9) 1 = 1) ∧
    -- n = 16: μ = 2, 4, 16 (D = 4, 2, 1)
    (Walk.s (1/2) 4 = 16 ∧ Walk.s (1/4) 2 = 8 ∧ Walk.s (1/16) 1 = 1) ∧
    (Walk.s (2/3) 4 = 33/4 ∧ Walk.s (2/5) 2 = 5 ∧ Walk.s (2/17) 1 = 1) := by
  unfold Walk.s; norm_num

end SHH.GD
