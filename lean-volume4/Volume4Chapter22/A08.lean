import Volume4Stage0.BrownianCheck
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter22

theorem affine_coefficient_at_one :
    StronglyMeasurable[naturalFiltration 1]
      (fun ω => (2 : ℝ) * brownian 1 ω + 3) ∧
    MemLp (fun ω => (2 : ℝ) * brownian 1 ω + 3) 2 gaussianLimit := by
  constructor
  · exact (stronglyMeasurable_const.mul
      (filtered_brownian.stronglyAdapted 1)).add stronglyMeasurable_const
  · have hL : MemLp (brownian 1) 2 gaussianLimit :=
      (constructed_brownian.toIsPreBrownianReal.hasLaw_eval 1).hasGaussianLaw.memLp_two
    exact (hL.const_mul 2).add (memLp_const 3)

end Volume4Chapter22
