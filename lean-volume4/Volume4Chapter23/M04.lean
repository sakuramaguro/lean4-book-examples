import Volume4Elementary.FiniteSumExamples

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open Volume4Elementary
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter23

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {a b : ℝ≥0}

theorem constant_integral_formula [IsProbabilityMeasure P]
    (T : ℝ≥0) (hT : 0 < T) (σ : ℝ)
    (W : ℝ≥0 → Ω → ℝ) {t : ℝ≥0} (ht : t ≤ T) (ω : Ω) :
    (Elementary.constant (ℱ := ℱ) (P := P) T hT σ).integral W t ω =
      σ * (W t ω - W 0 ω) := by
  rw [Elementary.constant, Elementary.integral_oneStep]
  simp [min_eq_left ht]

end Volume4Chapter23
