import SHH.Walk.System

/-!
# The closed form

The expected number of steps from distance `D` in the walk of `SHH/Walk/System.lean`:

  s(p, D) = D/(2p − 1) − 2p(1 − p)(1 − ((1 − p)/p)^D)/(2p − 1)²   for p ≠ 1/2,   s(1/2, D) = D².

`term p D k` is the solution at every distance `k ≤ D` (the general term
`k/(2p − 1) + B((p/(1 − p))^k − 1)` with `B = −2(1 − p)^(D+1)/(p^(D−1)(2p − 1)²)`; for
`p = 1/2`, `k(2D − k)`). `term_sys` shows it satisfies the system, `term_top` that its value
at `D` is `s p D`, and `sys_unique` that the system has at most one solution, so `s p D` *is*
the expected number of steps the paper's Eq. 2 expresses. The symmetric value `D²`
(`s_half`) is the one the paper reports, which fixes the boundary convention.
-/

namespace SHH.Walk

/-- **The closed form for expected steps from distance `D`** (Eq. 2 of SHH 1988, as derived
here; postulate W). -/
def s (p : ℚ) (D : ℕ) : ℚ :=
  if p = 1/2 then (D : ℚ)^2
  else (D : ℚ)/(2*p - 1) - 2*p*(1 - p)*(1 - ((1 - p)/p)^D)/(2*p - 1)^2

/-- The general term: expected steps from distance `k` in the walk of length `D`. -/
def term (p : ℚ) (D k : ℕ) : ℚ :=
  if p = 1/2 then (k : ℚ) * (2*D - k)
  else (k : ℚ)/(2*p - 1) - 2*(1 - p)^(D+1)/(p^(D-1)*(2*p - 1)^2) * ((p/(1 - p))^k - 1)

theorem term_zero (p : ℚ) (D : ℕ) : term p D 0 = 0 := by
  unfold term; split_ifs <;> simp

/-- The interior equation, for `p ∉ {0, 1/2, 1}`, at `k = j + 1`. -/
theorem term_interior_gen (p : ℚ) (D j : ℕ) (hp0 : p ≠ 0) (hp1 : p ≠ 1) (hph : p ≠ 1/2) :
    term p D (j + 1) = 1 + p * term p D j + (1 - p) * term p D (j + 2) := by
  have hq : (1 - p) ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  have h2 : (2*p - 1) ≠ 0 := by
    intro h; apply hph; linarith
  unfold term
  simp only [hph, ite_false]
  set B : ℚ := 2*(1 - p)^(D+1)/(p^(D-1)*(2*p - 1)^2) with hB
  set a : ℚ := p/(1 - p) with ha
  have hqa : (1 - p) * a = p := by rw [ha]; field_simp
  have hd : (2*p - 1) * (2*p - 1)⁻¹ = 1 := mul_inv_cancel₀ h2
  push_cast
  rw [pow_succ, pow_succ, pow_succ]
  linear_combination hd + (B * a^j * (a - 1)) * hqa

/-- The interior equation at `p = 1/2`. -/
theorem term_interior_half (D j : ℕ) :
    term (1/2) D (j + 1) = 1 + (1/2) * term (1/2) D j + (1 - 1/2) * term (1/2) D (j + 2) := by
  unfold term; simp only [ite_true]; push_cast; ring

/-- The interior equation at `p = 1`. -/
theorem term_interior_one (D j : ℕ) :
    term 1 D (j + 1) = 1 + 1 * term 1 D j + (1 - 1) * term 1 D (j + 2) := by
  unfold term
  have : (1 : ℚ) ≠ 1/2 := by norm_num
  simp only [this, ite_false]; push_cast; norm_num <;> ring

/-- The top equation at `D = m + 1`, for `p ∉ {0, 1/2, 1}`. -/
theorem term_top_gen (p : ℚ) (m : ℕ) (hp0 : p ≠ 0) (hp1 : p ≠ 1) (hph : p ≠ 1/2) :
    term p (m + 1) (m + 1) = 1 + term p (m + 1) m := by
  have hq : (1 - p) ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  have h2 : (2*p - 1) ≠ 0 := by
    intro h; apply hph; linarith
  unfold term
  simp only [hph, ite_false, Nat.add_sub_cancel]
  push_cast
  rw [div_pow, div_pow, pow_succ p m, pow_succ (1 - p) (m + 1), pow_succ (1 - p) m]
  field_simp
  ring

theorem term_top_half (m : ℕ) : term (1/2) (m + 1) (m + 1) = 1 + term (1/2) (m + 1) m := by
  unfold term; simp only [ite_true]; push_cast; ring

theorem term_top_one (m : ℕ) : term 1 (m + 1) (m + 1) = 1 + term 1 (m + 1) m := by
  unfold term
  have : (1 : ℚ) ≠ 1/2 := by norm_num
  simp only [this, ite_false]; push_cast; norm_num <;> ring

/-- **The general term solves the system** (postulate W), for every `0 < p ≤ 1`. -/
theorem term_sys (p : ℚ) (D : ℕ) (hp0 : 0 < p) (hp1 : p ≤ 1) : Sys p D (term p D) where
  zero := term_zero p D
  interior := by
    intro k hk _
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    by_cases hph : p = 1/2
    · subst hph; exact term_interior_half D j
    · by_cases hp1' : p = 1
      · subst hp1'; exact term_interior_one D j
      · exact term_interior_gen p D j hp0.ne' hp1' hph
  top := by
    intro hD
    obtain ⟨m, rfl⟩ : ∃ m, D = m + 1 := ⟨D - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    by_cases hph : p = 1/2
    · subst hph; exact term_top_half m
    · by_cases hp1' : p = 1
      · subst hp1'; exact term_top_one m
      · exact term_top_gen p m hp0.ne' hp1' hph

/-- The general term at `D` is the closed form. -/
theorem term_top (p : ℚ) (D : ℕ) (hp0 : 0 < p) (hp1 : p ≤ 1) : term p D D = s p D := by
  unfold term s
  by_cases hph : p = 1/2
  · simp only [hph, ite_true]; ring
  · simp only [hph, ite_false]
    by_cases hp1' : p = 1
    · subst hp1'; simp
    · have hq : (1 - p) ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1')
      have h2 : (2*p - 1) ≠ 0 := by intro h; apply hph; linarith
      rcases D with _ | m
      · simp
      · simp only [Nat.add_sub_cancel]
        rw [div_pow, div_pow, pow_succ p m, pow_succ (1 - p) (m + 1)]
        field_simp <;> ring

/-- **The system has at most one solution** (for `p ≠ 0`): two solutions agree at every
distance up to `D`. With `term_sys`, the closed form is the unique solution. -/
theorem sys_unique (p : ℚ) (D : ℕ) (T₁ T₂ : ℕ → ℚ) (hp : p ≠ 0)
    (h₁ : Sys p D T₁) (h₂ : Sys p D T₂) : ∀ k, k ≤ D → T₁ k = T₂ k := by
  -- the difference `U` has constant increments zero, by downward induction from `D`
  set U : ℕ → ℚ := fun k => T₁ k - T₂ k with hU
  have hU0 : U 0 = 0 := by simp [hU, h₁.zero, h₂.zero]
  have step : ∀ m, ∀ i, i + m = D → 1 ≤ i → U i = U (i - 1) := by
    intro m
    induction m with
    | zero =>
      intro i hi h1
      have hiD : i = D := by omega
      subst hiD
      have t₁ := h₁.top (by omega); have t₂ := h₂.top (by omega)
      simp only [hU]
      linarith
    | succ m ih =>
      intro i hi h1
      have hi' : i + 1 + m = D := by omega
      have hnext : U (i + 1) = U i := by
        have := ih (i + 1) hi' (by omega)
        simpa using this
      have e₁ := h₁.interior i h1 (by omega)
      have e₂ := h₂.interior i h1 (by omega)
      have : U i = p * U (i - 1) + (1 - p) * U (i + 1) := by
        simp only [hU]; linarith
      rw [hnext] at this
      have : p * U i = p * U (i - 1) := by linarith
      exact mul_left_cancel₀ hp this
  have all : ∀ k, k ≤ D → U k = 0 := by
    intro k
    induction k with
    | zero => intro _; exact hU0
    | succ k ih =>
      intro hk
      have := step (D - (k + 1)) (k + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at this
      rw [this]; exact ih (by omega)
  intro k hk
  have := all k hk
  simp only [hU] at this
  linarith

/-- The closed form is the unique solution's value at `D`. -/
theorem sys_eq_s (p : ℚ) (D : ℕ) (T : ℕ → ℚ) (hp0 : 0 < p) (hp1 : p ≤ 1) (h : Sys p D T) :
    T D = s p D := by
  rw [← term_top p D hp0 hp1]
  exact sys_unique p D T (term p D) hp0.ne' h (term_sys p D hp0 hp1) D le_rfl

/-! ### Special cases and values -/

/-- **With a perfect decision procedure the walk never steps back**: `s 1 D = D`
(the paper's Eq. 6 regime at r = 1). -/
theorem s_one (D : ℕ) : s 1 D = D := by
  unfold s; norm_num

/-- **The symmetric walk takes `D²` steps**: the value the paper reports for P₊ = P₋, which
holds for forced reflection at `D` (`stay_half` gives `D² + D` for the other convention). -/
theorem s_half (D : ℕ) : s (1/2) D = (D : ℚ)^2 := by
  unfold s; simp

/-- Values used in the paper and as witnesses (`tools/walk_check.py`). -/
theorem s_values :
    s (1/3) 8 = 996 ∧ s (1/5) 6 = 3630 ∧ s (9/10) 5 = 39161/6561 ∧ s (2/3) 5 = 89/8 ∧
      s (2/11) 4 = 1177/4 := by
  unfold s; norm_num

end SHH.Walk
