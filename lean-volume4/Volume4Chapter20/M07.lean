import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter20

variable {S ι : Type*} [Preorder ι] {mS : MeasurableSpace S}
  {μ : Measure S} {ℱ : Filtration ι mS} {M : ι → S → ℝ}

theorem martingale_means_equal [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) {i j : ι} (hij : i ≤ j) :
    (∫ ω, M j ω ∂μ) = ∫ ω, M i ω ∂μ := by
  have h := hM.setIntegral_eq hij (s := Set.univ) MeasurableSet.univ
  simpa only [MeasureTheory.setIntegral_univ] using h.symm

end Volume4Chapter20
