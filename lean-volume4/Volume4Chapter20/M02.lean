import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter20

def tableFiltration : Filtration (Fin 3) (inferInstance : MeasurableSpace Ω) where
  seq := information
  mono' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [information, firstInfo_le]
  le' := by
    intro i
    fin_cases i <;> simp [information, firstInfo_le]

theorem table_filtration_agrees : tableFiltration = filtration := rfl

end Volume4Chapter20
