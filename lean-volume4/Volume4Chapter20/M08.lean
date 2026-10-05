import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter20

variable {S ι : Type*} [Preorder ι] {mS : MeasurableSpace S}
  {μ : Measure S} {ℱ : Filtration ι mS} {M : ι → S → ℝ}

theorem martingale_increment_mean_zero
    (hM : Martingale M ℱ μ) {i j : ι} (hij : i ≤ j) :
    μ[M j - M i | ℱ i] =ᵐ[μ] (fun _ => (0 : ℝ)) := by
  filter_upwards [condExp_sub (hM.integrable j) (hM.integrable i) (ℱ i),
    hM.condExp_ae_eq hij, hM.condExp_ae_eq (le_refl i)] with ω hsub hj hi
  simpa only [Pi.sub_apply, hj, hi, sub_self] using hsub

end Volume4Chapter20
