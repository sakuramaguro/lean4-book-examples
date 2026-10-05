import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter19

theorem four_point_probability_and_values :
    (∀ ω : Ω, P {ω} = (1 / 4 : ℝ≥0∞)) ∧
    terminal (false, false) = -3 ∧ terminal (false, true) = 1 ∧
    terminal (true, false) = -1 ∧ terminal (true, true) = 3 := by
  constructor
  · intro ω
    simp [P, PMF.uniformOfFintype_apply]
  · norm_num [terminal, ξ₁, ξ₂, sign]

end Volume4Chapter19
