import Volume4Elementary.FiniteSumExamples

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open Volume4Elementary
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter23

theorem random_step_before_start {t : ℝ≥0} (ht : t ≤ 1) (ω : ℝ≥0 → ℝ) :
    Examples.brownianStep.integral brownian t ω = 0 :=
  Examples.brownianStep_integral_before_one ht ω

theorem random_step_terminal (ω : ℝ≥0 → ℝ) :
    Examples.brownianStep.integral brownian 2 ω =
      brownian 1 ω * (brownian 2 ω - brownian 1 ω) :=
  Examples.brownianStep_integral_at_two ω

end Volume4Chapter23
