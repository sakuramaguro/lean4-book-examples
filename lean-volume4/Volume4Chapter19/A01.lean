import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter19

theorem second_moment_from_four_values :
    (∫ ω, (terminal ω) ^ 2 ∂P) = 5 := by
  norm_num [P, PMF.integral_eq_sum, PMF.uniformOfFintype_apply,
    Fintype.sum_prod_type, terminal, ξ₁, ξ₂, sign]

end Volume4Chapter19
