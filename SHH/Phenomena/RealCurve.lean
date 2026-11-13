import Mathlib
import SHH.Phenomena.LearningCurve

/-!
# Learning-curve phenomena over the reals

The predicates of `LearningCurve.lean` restated for curves `ℕ → ℝ`, for mechanisms whose
curves involve logarithms (the graph-dynamic model's `ln n / ln μ`). Theory-neutral: none
mentions a mechanism. `scaleRatio_iff_cast` connects the two (adapted from CogLean's
`ACTR/ACTR/PowerLaw.lean`).
-/

namespace SHH.Phenomena

abbrev RCurve := ℕ → ℝ

/-- Over `[lo, hi]`, performance never gets worse. -/
def RImproves (T : RCurve) (lo hi : ℕ) : Prop :=
  ∀ n, lo ≤ n → n < hi → T (n + 1) ≤ T n

/-- Each trial's gain is at most the previous trial's. -/
def RDiminishingReturns (T : RCurve) (lo hi : ℕ) : Prop :=
  ∀ n, lo ≤ n → n + 2 ≤ hi → T (n + 1) - T (n + 2) ≤ T n - T (n + 1)

/-- Each trial's proportional gain is strictly smaller than the last (a power-law signature
that an exponential curve lacks). -/
def RDiminishingRelativeReturns (T : RCurve) (lo hi : ℕ) : Prop :=
  ∀ n, lo ≤ n → n + 2 ≤ hi → T (n + 1) * T (n + 1) < T n * T (n + 2)

/-- Scale invariance, the form an exact power law takes: `T (k n) = r · T n`. -/
def RScaleRatio (T : RCurve) (k : ℕ) (r : ℝ) (lo hi : ℕ) : Prop :=
  ∀ n, lo ≤ n → k * n ≤ hi → T (k * n) = r * T n

/-- Approximately a power law: scale invariance within relative error `ε` over `[lo, hi]`. -/
def RApproxScaleRatio (T : RCurve) (k : ℕ) (r ε : ℝ) (lo hi : ℕ) : Prop :=
  ∀ n, lo ≤ n → k * n ≤ hi →
    (1 - ε) * (r * T n) ≤ T (k * n) ∧ T (k * n) ≤ (1 + ε) * (r * T n)

/-- Somewhere in `[lo, hi)` performance gets worse: the fan effect. -/
def RWorsens (T : RCurve) (lo hi : ℕ) : Prop :=
  ∃ n, lo ≤ n ∧ n < hi ∧ T n < T (n + 1)

theorem rworsens_not_rimproves (T : RCurve) (lo hi : ℕ) (h : RWorsens T lo hi) :
    ¬ RImproves T lo hi := by
  intro hi'
  obtain ⟨n, hlo, hhi, hlt⟩ := h
  have := hi' n hlo hhi
  linarith

/-- A rational curve is scale-invariant iff its cast is. -/
theorem scaleRatio_iff_cast (T : Curve) (k : ℕ) (r : ℚ) (lo hi : ℕ) :
    ScaleRatio T k r lo hi ↔ RScaleRatio (fun n => (T n : ℝ)) k (r : ℝ) lo hi := by
  constructor
  · intro h n hlo hhi
    have := h n hlo hhi
    simp only
    rw [this]; push_cast; ring
  · intro h n hlo hhi
    have := h n hlo hhi
    simp only at this
    exact_mod_cast this

end SHH.Phenomena
