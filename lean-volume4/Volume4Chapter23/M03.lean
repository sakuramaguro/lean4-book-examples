import Volume4Elementary.FiniteSumExamples

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open Volume4Elementary
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter23

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {a b : ℝ≥0}

theorem subdivision_integral
    (H : Elementary ℱ P a b) (R : H.Refinement)
    (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    H.refinedIntegral R W t ω = H.integral W t ω := by
  apply Finset.sum_congr rfl
  intro i _
  exact Elementary.integral_onPartition _ _ _ _ _ _ _

end Volume4Chapter23
