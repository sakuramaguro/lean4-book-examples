import Volume4Stage0.BrownianCheck
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter22

theorem coefficient_for_next_interval :
    StronglyMeasurable[naturalFiltration 1] (brownian 1) ∧
    MemLp (brownian 1) 2 gaussianLimit :=
  ⟨filtered_brownian.stronglyAdapted 1,
    (constructed_brownian.toIsPreBrownianReal.hasLaw_eval 1).hasGaussianLaw.memLp_two⟩

end Volume4Chapter22
