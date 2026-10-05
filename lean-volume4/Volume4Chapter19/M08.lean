import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter19

theorem nested_information_and_repeated_conditioning :
    P[P[terminal | firstInfo] | ⊥] =ᵐ[P] P[terminal | ⊥] ∧
      P[P[terminal | firstInfo] | firstInfo] =ᵐ[P] P[terminal | firstInfo] := by
  constructor
  · exact condExp_condExp_of_le bot_le firstInfo_le
  · exact condExp_condExp_of_le le_rfl firstInfo_le

end Volume4Chapter19
