import SHH.Walk.Regimes

/-!
# The paper's printed equations

Equations 2 and 4 of Shrager, Hogg & Huberman (1988, p. 416), as printed (transcribed in
`notes/equations.txt`), checked against the closed form `s` proved in `ClosedForm.lean`.

* Eq. 2 is exactly `s` for every `p ∉ {0, 1/2}` (`eq2_printed`). The paper's formula is
  right; it is the same function written differently.
* Eq. 4 is Eq. 2's exponential term alone; the rest is a term linear in `D`
  (`eq4_remainder`), so in the diffusion regime Eq. 4 is `s` up to that term.
-/

namespace SHH.Walk

/-- Eq. 2 as printed: `s = 2/(2p − 1)² · [p² + p(D − 1) − D/2 + (1 − p)^(D+1)/p^(D−1)]`. -/
noncomputable def eq2 (p : ℚ) (D : ℕ) : ℚ :=
  2/(2*p - 1)^2 * (p^2 + p*((D : ℚ) - 1) - (D : ℚ)/2 + (1 - p)^(D+1)/p^((D : ℤ) - 1))

/-- Eq. 4 as printed: `s ≈ 2 ((1 − p)/p)^(D−1) ((1 − p)/(1 − 2p))²`. -/
noncomputable def eq4 (p : ℚ) (D : ℕ) : ℚ :=
  2 * ((1 - p)/p)^((D : ℤ) - 1) * ((1 - p)/(1 - 2*p))^2

/-- **The printed Eq. 2 is the closed form**, for every `p ∉ {0, 1/2}` and every `D`. -/
theorem eq2_printed (p : ℚ) (D : ℕ) (hp0 : p ≠ 0) (hph : p ≠ 1/2) : eq2 p D = s p D := by
  have h2 : (2*p - 1) ≠ 0 := by intro h; apply hph; linarith
  unfold eq2 s
  simp only [hph, ite_false]
  rw [zpow_sub₀ hp0, zpow_one, zpow_natCast, div_pow]
  field_simp
  ring

/-- **Eq. 4 is Eq. 2's exponential term**: the difference is a term linear in `D`. -/
theorem eq4_remainder (p : ℚ) (D : ℕ) (hp0 : p ≠ 0) (hph : p ≠ 1/2) :
    s p D - eq4 p D = 2*(p^2 + p*((D : ℚ) - 1) - (D : ℚ)/2)/(2*p - 1)^2 := by
  have h2 : (2*p - 1) ≠ 0 := by intro h; apply hph; linarith
  have h2' : (1 - 2*p) ≠ 0 := by intro h; apply hph; linarith
  rw [← eq2_printed p D hp0 hph]
  unfold eq2 eq4
  by_cases hq : (1 - p) = 0
  · have : p = 1 := by linarith
    subst this; norm_num
  · simp only [div_zpow, zpow_sub₀ hp0, zpow_sub₀ hq, zpow_one,
      zpow_natCast]
    field_simp
    ring

end SHH.Walk
