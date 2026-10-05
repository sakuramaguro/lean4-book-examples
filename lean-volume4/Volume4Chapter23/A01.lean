import Volume4Elementary.FiniteSumExamples

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open Volume4Elementary
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter23

theorem step_endpoint_values (ω : ℝ≥0 → ℝ) :
    Examples.brownianStep.value 1 ω = 0 ∧
    Examples.brownianStep.value 2 ω = brownian 1 ω ∧
    Examples.brownianStep.integral brownian 3 ω =
      brownian 1 ω * (brownian 2 ω - brownian 1 ω) := by
  refine ⟨Examples.brownianStep_value_at_one ω,
    Examples.brownianStep_value_at_two ω, ?_⟩
  norm_num [Examples.brownianStep_integral]

end Volume4Chapter23
