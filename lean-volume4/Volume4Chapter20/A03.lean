import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter20

theorem all_three_means_zero (n : Fin 3) :
    (∫ ω, process n ω ∂P) = 0 := by
  fin_cases n
  · simp [process]
  · simpa [process] using expectation_first
  · simpa [process] using expectation_terminal

end Volume4Chapter20
