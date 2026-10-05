import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter19

theorem conditional_mean_preserves_mean :
    (∫ ω, (P[terminal | firstInfo]) ω ∂P) = 0 := by
  rw [integral_condExp firstInfo_le, expectation_terminal]

end Volume4Chapter19
