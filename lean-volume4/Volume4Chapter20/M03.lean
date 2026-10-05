import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter20

theorem table_process_values :
    process 0 = (fun _ => 0) ∧ process 1 = ξ₁ ∧ process 2 = terminal := by
  norm_num [process]

end Volume4Chapter20
