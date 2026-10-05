import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter19

theorem integrable_does_not_mean_known :
    Integrable terminal P ∧ ¬ StronglyMeasurable[firstInfo] terminal := by
  refine ⟨integrable_terminal, ?_⟩
  intro h
  have hs : MeasurableSet[firstInfo] (terminal ⁻¹' ({1} : Set ℝ)) :=
    h.measurable (measurableSet_singleton 1)
  obtain ⟨u, _, hu⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have ht : (false, true) ∈ Prod.fst ⁻¹' u := by
    rw [hu]
    norm_num [terminal, ξ₁, ξ₂, sign]
  have hf : (false, false) ∈ Prod.fst ⁻¹' u := ht
  rw [hu] at hf
  norm_num [terminal, ξ₁, ξ₂, sign] at hf

end Volume4Chapter19
