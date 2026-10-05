import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter19

theorem no_information_and_full_information :
    P[terminal | ⊥] = (fun _ => (0 : ℝ)) ∧
      P[terminal | (inferInstance : MeasurableSpace Ω)] = terminal := by
  constructor
  · rw [condExp_bot, expectation_terminal]
  · exact condExp_of_stronglyMeasurable le_rfl
      (measurable_of_finite terminal).stronglyMeasurable integrable_terminal

end Volume4Chapter19
