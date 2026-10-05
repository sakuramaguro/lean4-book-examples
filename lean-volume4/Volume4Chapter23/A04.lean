import Volume4Elementary.FiniteSumExamples

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open Volume4Elementary
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter23

theorem half_step_second_moment :
    (∫ ω, (Examples.brownianStep.integral brownian (3 / 2) ω) ^ 2
      ∂gaussianLimit) = (1 / 2 : ℝ) := by
  norm_num [OneStep.brownianStep_second_moment]

end Volume4Chapter23
