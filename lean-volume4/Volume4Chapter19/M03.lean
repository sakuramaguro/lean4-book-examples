import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter19

theorem finite_integrability_and_mean :
    Integrable terminal P ∧ (∫ ω, terminal ω ∂P) = 0 := by
  constructor
  · exact Integrable.of_finite
  · norm_num [P, PMF.integral_eq_sum, PMF.uniformOfFintype_apply,
      Fintype.sum_prod_type, terminal, ξ₁, ξ₂, sign]

end Volume4Chapter19
