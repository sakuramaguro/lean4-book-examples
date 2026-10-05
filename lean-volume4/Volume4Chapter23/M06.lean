import Volume4Elementary.FiniteSumExamples

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open Volume4Elementary
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter23

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {a b : ℝ≥0}

theorem one_interval_isometry
    (hW : IsFilteredPreBrownian W ℱ P)
    (a b : ℝ≥0) (hab : a < b) (ξ : Ω → ℝ)
    (hξ : StronglyMeasurable[ℱ a] ξ) (hLp : MemLp ξ 2 P) (t : ℝ≥0) :
    (∫ ω, ((Elementary.oneStep a b hab ξ hξ hLp).integral W t ω) ^ 2 ∂P) =
      ∫ ω, (∫ s in (0 : ℝ)..(t : ℝ),
        ((Elementary.oneStep a b hab ξ hξ hLp).value s.toNNReal ω) ^ 2) ∂P := by
  simp_rw [OneStep.oneStep_time_energy]
  rw [integral_const_mul]
  exact OneStep.integral_oneStep_second_moment hW a b hab ξ hξ hLp t

end Volume4Chapter23
