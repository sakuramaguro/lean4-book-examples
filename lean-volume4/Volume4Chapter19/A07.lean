import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter19

theorem averaging_first_does_not_restore_information :
    P[P[terminal | ⊥] | firstInfo] = (fun _ => (0 : ℝ)) := by
  rw [condExp_terminal_bot]
  exact condExp_const firstInfo_le 0

end Volume4Chapter19
