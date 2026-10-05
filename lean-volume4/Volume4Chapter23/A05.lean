import Volume4Elementary.FiniteSumExamples

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open Volume4Elementary
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter23

theorem future_increment_not_measurable :
    ¬ StronglyMeasurable[naturalFiltration 1]
      (fun ω => brownian 2 ω - brownian 1 ω) := by
  intro hξ
  have hLp : MemLp (fun ω => brownian 2 ω - brownian 1 ω) 2 gaussianLimit :=
    OneStep.increment_memLp filtered_brownian 1 2
  have hz := OneStep.weighted_increment_mean_zero filtered_brownian
    (show (1 : ℝ≥0) ≤ 2 by norm_num) hξ hLp
  have hzero : (∫ ω, (brownian 2 ω - brownian 1 ω) ^ 2 ∂gaussianLimit) = 0 := by
    simpa only [pow_two] using hz
  have hone : (∫ ω, (brownian 2 ω - brownian 1 ω) ^ 2 ∂gaussianLimit) = 1 := by
    have hm := OneStep.increment_second_moment filtered_brownian
      (show (1 : ℝ≥0) ≤ 2 by norm_num)
    norm_num at hm
    exact hm
  have hfalse : (0 : ℝ) = 1 := hzero.symm.trans hone
  norm_num at hfalse

end Volume4Chapter23
