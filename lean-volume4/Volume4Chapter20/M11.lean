import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter20

variable {S ι : Type*} [Preorder ι] {mS : MeasurableSpace S}
  {μ : Measure S} {ℱ : Filtration ι mS} {M : ι → S → ℝ}

theorem forecast_martingale_and_terminal [IsProbabilityMeasure μ]
    {Z : S → ℝ} (hZ : Integrable Z μ) (T : ι)
    (hZT : StronglyMeasurable[ℱ T] Z) :
    Martingale (fun i => μ[Z | ℱ i]) ℱ μ ∧ μ[Z | ℱ T] = Z :=
  ⟨martingale_condExp Z ℱ μ,
    condExp_of_stronglyMeasurable (ℱ.le T) hZT hZ⟩

end Volume4Chapter20
