import SHH.Walk.ClosedForm

/-!
# Regimes of the walk

The paper's three regimes (p. 416), stated exactly about the closed form `s`:

* **drift** (P₋ > P₊, i.e. `p > 1/2`): `s` lies between `D/(2p − 1) − 2p(1 − p)/(2p − 1)²` and
  `D/(2p − 1)` (`drift_bounds`; the paper's Eq. 3 is the upper bound, "s ≈ D/(P₋ − P₊)");
* **symmetric** (`p = 1/2`): `s = D²` (`s_half`);
* **diffusion** (P₊ > P₋, `p < 1/2`): `s = 2p(1 − p)(((1 − p)/p)^D − 1)/(1 − 2p)² − D/(1 − 2p)`,
  exponential in `D` since `(1 − p)/p > 1` (`s_diffusion_form`; the paper's Eq. 4).

Two exact monotonicity facts: more distance always costs more steps (`s_strictMono_D`), and
the exact increment `s p (D+1) − s p D` (`s_succ`).

And the fan effect inside the walk, exactly (`fan_witness_walk`): a shorter walk with worse
odds can cost more steps. With the paper's P₋ = 1/(1 + (μ − 1)(1 − r)) at r = 0, going from
μ = 3 (p = 1/3) at distance 8 to μ = 5 (p = 1/5) at distance 6 raises the expected steps
from 996 to 3630. This is the mechanism of the problem-solving fan effect, before any
idealization about how D depends on μ.
-/

namespace SHH.Walk

/-- **The increment in `D`**, for `p ∉ {0, 1/2}`. -/
theorem s_succ (p : ℚ) (D : ℕ) (hp0 : p ≠ 0) (hph : p ≠ 1/2) :
    s p (D + 1) - s p D = (1 - 2*(1 - p)*((1 - p)/p)^D)/(2*p - 1) := by
  have h2 : (2*p - 1) ≠ 0 := by intro h; apply hph; linarith
  unfold s
  simp only [hph, ite_false]
  push_cast
  rw [pow_succ]
  field_simp
  ring

/-- **More distance costs more steps**, for every `0 < p < 1`. -/
theorem s_strictMono_D (p : ℚ) (D : ℕ) (hp0 : 0 < p) (hp1 : p < 1) : s p D < s p (D + 1) := by
  by_cases hph : p = 1/2
  · subst hph; rw [s_half, s_half]; push_cast
    have : (0 : ℚ) ≤ D := by positivity
    nlinarith
  · have h := s_succ p D hp0.ne' hph
    have hq : 0 < 1 - p := by linarith
    have ha : 0 ≤ (1 - p)/p := by positivity
    suffices 0 < (1 - 2*(1 - p)*((1 - p)/p)^D)/(2*p - 1) by linarith
    rcases lt_or_gt_of_ne hph with hlt | hgt
    · -- p < 1/2: numerator and denominator both negative
      have h1 : 1 ≤ (1 - p)/p := by rw [le_div_iff₀ hp0]; linarith
      have hpow : 1 ≤ ((1 - p)/p)^D := one_le_pow₀ h1
      have hnum : 1 - 2*(1 - p)*((1 - p)/p)^D < 0 := by nlinarith
      have hden : 2*p - 1 < 0 := by linarith
      exact div_pos_of_neg_of_neg hnum hden
    · -- p > 1/2: both positive
      have h1 : (1 - p)/p ≤ 1 := by rw [div_le_iff₀ hp0]; linarith
      have hpow : ((1 - p)/p)^D ≤ 1 := pow_le_one₀ ha h1
      have hnum : 0 < 1 - 2*(1 - p)*((1 - p)/p)^D := by nlinarith
      have hden : 0 < 2*p - 1 := by linarith
      exact div_pos hnum hden

/-- **The drift regime** (P₋ > P₊): two-sided exact bounds, the paper's Eq. 3
`s ≈ D/(P₋ − P₊)` as the upper bound, with the gap at most `2p(1 − p)/(2p − 1)²`. -/
theorem drift_bounds (p : ℚ) (D : ℕ) (hp : 1/2 < p) (hp1 : p ≤ 1) :
    (D : ℚ)/(2*p - 1) - 2*p*(1 - p)/(2*p - 1)^2 ≤ s p D ∧ s p D ≤ (D : ℚ)/(2*p - 1) := by
  have hph : p ≠ 1/2 := by intro h; linarith
  have hden : 0 < (2*p - 1)^2 := pow_pos (by linarith) 2
  have hq : 0 ≤ 1 - p := by linarith
  have hp0 : 0 < p := by linarith
  have hx0 : 0 ≤ ((1 - p)/p)^D := by positivity
  have hx1 : ((1 - p)/p)^D ≤ 1 := pow_le_one₀ (by positivity) (by rw [div_le_iff₀ hp0]; linarith)
  unfold s
  simp only [hph, ite_false]
  set x := ((1 - p)/p)^D
  have hc : 0 ≤ 2*p*(1 - p) := by positivity
  constructor
  · apply sub_le_sub_left
    apply div_le_div_of_nonneg_right _ hden.le
    exact mul_le_of_le_one_right hc (by linarith)
  · apply sub_le_self
    apply div_nonneg _ hden.le
    exact mul_nonneg hc (by linarith)

/-- **The diffusion regime** (P₊ > P₋): the paper's Eq. 4, exactly. The first term is
exponential in `D`, since `(1 − p)/p > 1`. -/
theorem s_diffusion_form (p : ℚ) (D : ℕ) (hp : p < 1/2) :
    s p D = 2*p*(1 - p)*(((1 - p)/p)^D - 1)/(1 - 2*p)^2 - (D : ℚ)/(1 - 2*p) := by
  have hph : p ≠ 1/2 := by intro h; linarith
  have h2 : (1 - 2*p) ≠ 0 := by intro h; linarith
  have h2' : (2*p - 1) ≠ 0 := by intro h; linarith
  unfold s
  simp only [hph, ite_false]
  field_simp
  ring

/-- **The fan effect inside the walk, exactly**: at r = 0, μ = 3 → 5 (p = 1/3 → 1/5) with the
distance falling 8 → 6, expected steps rise from 996 to 3630. Fewer levels but more
branching costs more. -/
theorem fan_witness_walk : s (1/3) 8 < s (1/5) 6 := by
  unfold s; norm_num

/-- The same at r = 1/2: μ = 3 (p = 1/2) at distance 8 gives 64 steps; μ = 10 (p = 2/11) at
distance 4 gives 1177/4 ≈ 294. -/
theorem fan_witness_half : s (1/2) 8 < s (2/11) 4 := by
  unfold s; norm_num

/-! ### The other boundary convention -/

/-- Under the stay convention (`SysStay`) the symmetric walk's expected steps are
`k(2D + 1 − k)` from distance `k` … -/
theorem stay_half_sys (D : ℕ) : SysStay (1/2) D (fun k => (k : ℚ) * (2*D + 1 - k)) where
  zero := by simp
  interior := by
    intro k hk _
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; push_cast; ring
  top := by
    intro hD
    obtain ⟨m, rfl⟩ : ∃ m, D = m + 1 := ⟨D - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; push_cast; ring

/-- … so `D² + D` from `D`, not the paper's `D²`: the paper's walk reflects at `D`. -/
theorem stay_half_value (D : ℕ) : (fun k : ℕ => (k : ℚ) * (2*D + 1 - k)) D = (D : ℚ)^2 + D := by
  simp; ring

end SHH.Walk
