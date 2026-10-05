import Volume4Stage0.BrownianCheck
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter22

theorem increment_one_to_three :
    HasLaw (brownian 3 - brownian 1) (gaussianReal 0 2) gaussianLimit := by
  have h := constructed_brownian.toIsPreBrownianReal.hasLaw_sub 3 1
  convert h using 1
  norm_num [Real.nndist_eq]

end Volume4Chapter22
