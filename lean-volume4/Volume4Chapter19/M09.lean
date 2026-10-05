import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter19

theorem conditional_mean_at_every_point :
    P[terminal | firstInfo] = ξ₁ := by
  funext ω
  exact (ae_iff_of_countable.mp condExp_terminal_first) ω
    (by rw [point_mass]; norm_num)

end Volume4Chapter19
