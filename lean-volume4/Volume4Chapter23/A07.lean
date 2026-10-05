import Volume4Elementary.FiniteSumExamples

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open Volume4Elementary
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter23

theorem two_step_moments_at_endpoints :
    (∫ ω, (FiniteExamples.brownianTwoStep.integral brownian 2 ω) ^ 2
      ∂gaussianLimit) = 1 ∧
    (∫ ω, (FiniteExamples.brownianTwoStep.integral brownian 3 ω) ^ 2
      ∂gaussianLimit) = 3 ∧
    (∫ ω, (FiniteExamples.brownianTwoStep.integral brownian 4 ω) ^ 2
      ∂gaussianLimit) = 3 := by
  norm_num [FiniteExamples.brownianTwoStep_second_moment]

end Volume4Chapter23
