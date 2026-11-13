import SHH.GraphDynamics.Params

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
expected steps from 256 to 9824, and only from `μ = 16` on do more edges help
(`fan_pow2_zero`). So the paper's own idealized model shows a fan effect at `r = 0`, where
the paper says more edges always help; its Eq. 5 reaches that conclusion by replacing
`(μ − 1)^D` with `μ^D = n` (see `eq5_error_bound`). The paper's simulation at `r = 0`
(Fig. 1A) does improve with practice, so it is the tree idealization I1 that fails there, not
the simulation.

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
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  unfold Walk.s; norm_num

/-- At `r = 1/2` and the same `n`: `p = 1/(1 + (μ − 1)/2)`; `μ = 2 → p = 2/3, D = 16`;
`μ = 4 → p = 2/5, D = 8`; `μ = 16 → p = 2/17, D = 4`. Steps 42.1 → 115.5 → 213.8:
the fan effect at the paper's "mediocre" setting, exactly. -/
theorem fan_pow2_half :
    Walk.s (2/3) 16 < Walk.s (2/5) 8 ∧ Walk.s (2/5) 8 < Walk.s (2/17) 4 := by
  unfold Walk.s; norm_num

theorem pOf_half_values : pOf 2 (1/2) = 2/3 ∧ pOf 4 (1/2) = 2/5 ∧ pOf 16 (1/2) = 2/17 := by
  unfold pOf; norm_num

end SHH.GD
