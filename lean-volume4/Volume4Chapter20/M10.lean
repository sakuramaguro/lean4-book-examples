import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter20

def fullInformation : Filtration (Fin 3) (inferInstance : MeasurableSpace Ω) :=
  Filtration.const (Fin 3) inferInstance le_rfl

theorem full_information_changes_martingale :
    StronglyAdapted fullInformation process ∧
      ¬ Martingale process fullInformation P := by
  constructor
  · intro n
    change StronglyMeasurable (process n)
    exact (measurable_of_finite (process n)).stronglyMeasurable
  · intro h
    have hcond := h.condExp_ae_eq (by decide : (1 : Fin 3) ≤ 2)
    have hknown : P[process 2 | fullInformation 1] = process 2 := by
      change P[process 2 | (inferInstance : MeasurableSpace Ω)] = process 2
      exact condExp_of_stronglyMeasurable le_rfl
        (measurable_of_finite (process 2)).stronglyMeasurable (process_integrable 2)
    rw [hknown] at hcond
    have hpoint := (ae_iff_of_countable.mp hcond) (false, false)
      (by rw [point_mass]; norm_num)
    norm_num [process, terminal, ξ₁, ξ₂, sign] at hpoint

end Volume4Chapter20
