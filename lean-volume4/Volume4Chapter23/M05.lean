import Volume4Elementary.FiniteSumExamples

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open Volume4Elementary
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter23

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {a b : ℝ≥0}

theorem weighted_increment_L2_and_moment
    (hW : IsFilteredPreBrownian W ℱ P) (hab : a ≤ b)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ a] ξ) (hLp : MemLp ξ 2 P) :
    MemLp (fun ω => ξ ω * (W b ω - W a ω)) 2 P ∧
      (∫ ω, (ξ ω * (W b ω - W a ω)) ^ 2 ∂P) =
        ((b : ℝ) - a) * ∫ ω, ξ ω ^ 2 ∂P :=
  ⟨OneStep.weighted_increment_memLp hW hab hξ hLp,
    OneStep.weighted_increment_second_moment hW hab hξ hLp⟩

end Volume4Chapter23
