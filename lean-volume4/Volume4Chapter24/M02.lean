import Volume4Elementary.ConstantSDEExamples

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Volume4Elementary
open Volume4Elementary.ConstantSDE
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter24

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ≥0 mΩ} {W X Y : ℝ≥0 → Ω → ℝ}

theorem constant_integral
    (T : ℝ≥0) (hT : 0 < T) (σ : ℝ)
    (hzero : W 0 =ᵐ[P] (fun _ => (0 : ℝ))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      (Elementary.constant (ℱ := ℱ) (P := P) T hT σ).integral W t ω =
        σ * W t ω := by
  filter_upwards [hzero] with ω hω
  intro t ht
  rw [Elementary.integral_constant T hT σ W ht ω, hω, sub_zero]

end Volume4Chapter24
