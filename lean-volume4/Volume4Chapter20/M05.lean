import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter20

theorem table_is_terminal_forecast (n : Fin 3) :
    process n =ᵐ[P] P[terminal | filtration n] := by
  fin_cases n
  · change (fun _ : Ω => (0 : ℝ)) =ᵐ[P] P[terminal | ⊥]
    rw [condExp_terminal_bot]
  · change ξ₁ =ᵐ[P] P[terminal | firstInfo]
    exact condExp_terminal_first.symm
  · change terminal =ᵐ[P] P[terminal | (inferInstance : MeasurableSpace Ω)]
    rw [condExp_terminal_full]

end Volume4Chapter20
