import SHH.GraphDynamics.Params
import SHH.Phenomena.RealCurve

/-!
# The practice curve with a strong decision procedure: logarithmic, not a power law

At `r = 1` the walk never steps back, so `s = D` exactly (`SHH.Walk.s_one`), and in the
paper's idealization `D = ln n / ln μ` (Eq. 6: "s ≈ ln n / ln μ"). The paper reads this as a
power-law decay with practice. To read it as a learning curve at all needs a further
condition, C3: each trial adds a bounded number of edges, so the mean branching grows about
linearly in trials, `μ = μ₀ + c·t`. The curve is then

  T(t) = ln n / ln(μ₀ + c·t),

`curveGD`. It has every qualitative signature the library attributes to a power law: it
improves (`curveGD_improves`) with strictly diminishing relative returns
(`curveGD_diminishingRelative`, from the strict concavity of the logarithm). But it is not a
power law, even approximately, over long ranges: the doubling ratio `T(2t)/T(t)` tends to 1,
so for any exponent and tolerance with `(1 + ε)·r < 1` there is a range on which approximate
scale invariance fails (`curveGD_not_powerLaw`). Over trials 1–100 at `n = 10⁴`, `μ₀ = 2`,
`c = 1` the curve is within 12% of `7.41·t^{−0.29}` (`tools/walk_check.py`): straight enough
on a log-log plot over one decade, which is what Figure 1 shows. NOT MODELED here: a Lean
certificate of that numeric fit (it needs rational bounds on `ln 3 … ln 100`).

Postulates: the walk and the idealizations I1–I2. Conditions: `r = 1`; C3.
-/

namespace SHH.GD

open Real Phenomena

/-- **The r = 1 practice curve** (Eq. 6 under condition C3): `ln n / ln(μ₀ + c t)`. -/
noncomputable def curveGD (n μ₀ c : ℝ) : RCurve := fun t => Real.log n / Real.log (μ₀ + c * t)

section
variable {n μ₀ c : ℝ} (hn : 1 < n) (hμ : 1 < μ₀) (hc : 0 < c)
include hn hμ hc

theorem curveGD_pos (t : ℕ) : 0 < curveGD n μ₀ c t := by
  unfold curveGD
  apply div_pos (Real.log_pos hn)
  apply Real.log_pos
  have : (0 : ℝ) ≤ c * t := by positivity
  linarith

/-- **The curve improves**: more trials, fewer steps. -/
theorem curveGD_improves (lo hi : ℕ) : RImproves (curveGD n μ₀ c) lo hi := by
  intro t _ _
  unfold curveGD
  apply div_le_div_of_nonneg_left (Real.log_pos hn).le
  · apply Real.log_pos
    have : (0 : ℝ) ≤ c * t := by positivity
    linarith
  · apply Real.log_le_log
    · have : (0 : ℝ) ≤ c * t := by positivity
      linarith
    · push_cast; linarith

/-- **Strictly diminishing relative returns**: the proportional gain shrinks every trial, the
signature that distinguishes a power curve from an exponential one. From the strict
concavity of the logarithm. -/
theorem curveGD_diminishingRelative (lo hi : ℕ) :
    RDiminishingRelativeReturns (curveGD n μ₀ c) lo hi := by
  intro t _ _
  unfold curveGD
  set A := Real.log n with hA
  have hA0 : 0 < A := Real.log_pos hn
  have hct : (0 : ℝ) ≤ c * t := by positivity
  set x₀ : ℝ := μ₀ + c * t with hx₀
  have hx₀1 : 1 < x₀ := by linarith
  have hmid : (μ₀ + c * ((t + 1 : ℕ) : ℝ)) = (1/2 : ℝ) * x₀ + (1/2 : ℝ) * (μ₀ + c * ((t + 2 : ℕ) : ℝ)) := by
    push_cast; ring
  set x₂ : ℝ := μ₀ + c * ((t + 2 : ℕ) : ℝ) with hx₂
  have hc2 : c * ((t + 2 : ℕ) : ℝ) = c * t + 2 * c := by push_cast; ring
  have hx₂1 : 1 < x₂ := by rw [hx₂, hc2]; linarith
  have hne : x₀ ≠ x₂ := by rw [hx₀, hx₂, hc2]; intro h; linarith
  have L0 : 0 < Real.log x₀ := Real.log_pos hx₀1
  have L2 : 0 < Real.log x₂ := Real.log_pos hx₂1
  have hconc := (strictConcaveOn_log_Ioi).2 (Set.mem_Ioi.mpr (by linarith : (0:ℝ) < x₀))
    (Set.mem_Ioi.mpr (by linarith : (0:ℝ) < x₂)) hne (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
    (by norm_num)
  simp only [smul_eq_mul] at hconc
  rw [hmid]
  set L1 := Real.log ((1/2 : ℝ) * x₀ + (1/2 : ℝ) * x₂) with hL1
  have hL1pos : 0 < L1 := by linarith
  -- goal: (A/L1)² < (A/log x₀)(A/log x₂), i.e. log x₀ · log x₂ < L1², from L1 > (log x₀ + log x₂)/2
  rw [div_mul_div_comm, div_mul_div_comm]
  apply div_lt_div_of_pos_left (by positivity) (by positivity)
  nlinarith [sq_nonneg (Real.log x₀ - Real.log x₂)]

end

/-- **Not a power law over long ranges**: for any exponent `r` and tolerance `ε` with
`(1 + ε)·r < 1`, approximate scale invariance under doubling fails beyond some trial. The
doubling ratio `T(2t)/T(t) = ln(μ₀ + ct)/ln(μ₀ + 2ct)` tends to 1. -/
theorem curveGD_not_powerLaw {n μ₀ c : ℝ} (hn : 1 < n) (hμ : 1 < μ₀) (hc : 0 < c)
    (r ε : ℝ) (hr : (1 + ε) * r < 1) (lo : ℕ) :
    ∃ hi, ¬ RApproxScaleRatio (curveGD n μ₀ c) 2 r ε lo hi := by
  set ρ := (1 + ε) * r with hρ
  have hA0 : 0 < Real.log n := Real.log_pos hn
  -- choose t ≥ lo with ln(μ₀ + c t) > ρ ln 2 / (1 − ρ) (when ρ > 0)
  set K : ℝ := max 0 (ρ * Real.log 2 / (1 - ρ)) + 1 with hK
  obtain ⟨m, hm⟩ := exists_nat_ge (Real.exp K / c)
  refine ⟨2 * (lo + m), fun h => ?_⟩
  have ht := h (lo + m) (by omega) le_rfl
  set t : ℕ := lo + m with htdef
  have hct : Real.exp K ≤ c * t := by
    rw [div_le_iff₀ hc] at hm
    have : (m : ℝ) ≤ t := by simp [htdef]
    nlinarith
  have hx : 1 < μ₀ + c * t := by
    have : (0:ℝ) ≤ c * t := by positivity
    linarith
  set L := Real.log (μ₀ + c * t) with hL
  have hLK : K ≤ L := by
    rw [hL, ← Real.log_exp K]
    apply Real.log_le_log (Real.exp_pos _)
    linarith
  have hL2 : Real.log (μ₀ + c * ((2 * t : ℕ) : ℝ)) ≤ Real.log 2 + L := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    apply Real.log_le_log (by push_cast; nlinarith)
    push_cast; nlinarith
  have hL2pos : 0 < Real.log (μ₀ + c * ((2 * t : ℕ) : ℝ)) := by
    apply Real.log_pos; push_cast; nlinarith
  have hTt : curveGD n μ₀ c t = Real.log n / L := rfl
  have hT2 : curveGD n μ₀ c (2 * t) = Real.log n / Real.log (μ₀ + c * ((2 * t : ℕ) : ℝ)) := rfl
  obtain ⟨_, hupper⟩ := ht
  rw [hT2, hTt] at hupper
  -- hupper : log n / log(μ₀ + 2ct) ≤ ρ · (log n / L); refute it
  have hLpos : 0 < L := by linarith [hK, le_max_left 0 (ρ * Real.log 2 / (1 - ρ))]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hρpos : ρ ≤ 0
  · have : Real.log n / Real.log (μ₀ + c * ((2 * t : ℕ) : ℝ)) > 0 := div_pos hA0 hL2pos
    have : ρ * (Real.log n / L) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg hρpos; positivity
    linarith
  · push_neg at hρpos
    have h1ρ : 0 < 1 - ρ := by linarith
    have hKval : ρ * Real.log 2 / (1 - ρ) + 1 ≤ K := by
      rw [hK]; linarith [le_max_right (0:ℝ) (ρ * Real.log 2 / (1 - ρ))]
    -- from hupper: L ≤ ρ (log 2 + L) after clearing, contradiction with L > ρ log 2/(1−ρ)
    have hA : Real.log n / (Real.log 2 + L) ≤ Real.log n / Real.log (μ₀ + c * ((2 * t : ℕ) : ℝ)) :=
      div_le_div_of_nonneg_left hA0.le hL2pos hL2
    have hupper' : Real.log n / Real.log (μ₀ + c * ((2 * t : ℕ) : ℝ)) ≤ ρ * (Real.log n / L) := by
      calc _ ≤ (1 + ε) * (r * (Real.log n / L)) := hupper
        _ = ρ * (Real.log n / L) := by rw [hρ]; ring
    have hcomb : Real.log n / (Real.log 2 + L) ≤ ρ * (Real.log n / L) := le_trans hA hupper'
    rw [mul_div_assoc', div_le_iff₀ (by linarith : (0:ℝ) < Real.log 2 + L)] at hcomb
    rw [div_mul_eq_mul_div, le_div_iff₀ hLpos] at hcomb
    -- hcomb : log n · L ≤ ρ · log n · (log 2 + L)
    have : L ≤ ρ * (Real.log 2 + L) := by
      by_contra hcon
      push_neg at hcon
      have := mul_lt_mul_of_pos_left hcon hA0
      nlinarith
    have : L * (1 - ρ) ≤ ρ * Real.log 2 := by linarith
    have : L ≤ ρ * Real.log 2 / (1 - ρ) := by rw [le_div_iff₀ h1ρ]; linarith
    linarith

end SHH.GD
