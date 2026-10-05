import Volume4Stage0.BrownianCheck
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter22

theorem predict_time_three_at_one :
    gaussianLimit[brownian 3 | naturalFiltration 1] =ᵐ[gaussianLimit] brownian 1 :=
  brownian_martingale.condExp_ae_eq (by norm_num)

end Volume4Chapter22
