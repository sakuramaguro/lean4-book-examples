import Volume4Elementary.FiniteSumExamples

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open Volume4Elementary
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter23

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {a b : ℝ≥0}

theorem cross_term_integrable_and_zero [IsProbabilityMeasure P]
    (hW : IsFilteredPreBrownian W ℱ P)
    (H : Elementary ℱ P a b) (t : ℝ≥0)
    {i j : Fin H.partition.n} (hij : i ≠ j) :
    Integrable (fun ω => FiniteSum.term H W t i ω * FiniteSum.term H W t j ω) P ∧
      (∫ ω, FiniteSum.term H W t i ω * FiniteSum.term H W t j ω ∂P) = 0 :=
  ⟨FiniteSum.term_mul_integrable hW H t i j,
    FiniteSum.term_cross_moment hW H t hij⟩

end Volume4Chapter23
