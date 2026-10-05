import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter20

theorem table_martingale_from_tower : Martingale process filtration P := by
  refine ⟨process_stronglyAdapted, ?_⟩
  intro i j hij
  calc
    P[process j | filtration i] =ᵐ[P]
        P[P[terminal | filtration j] | filtration i] :=
      condExp_congr_ae (process_eq_condExp j)
    _ =ᵐ[P] P[terminal | filtration i] :=
      condExp_condExp_of_le (filtration.mono hij) (filtration.le j)
    _ =ᵐ[P] process i := (process_eq_condExp i).symm

end Volume4Chapter20
