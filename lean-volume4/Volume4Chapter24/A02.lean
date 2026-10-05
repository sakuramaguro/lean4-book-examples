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

theorem initial_from_equation
    (T : ℝ≥0) (hT : 0 < T) (x₀ a σ : ℝ)
    (hEq : ∀ t : ℝ≥0, t ≤ T → X t =ᵐ[P] (fun ω =>
      x₀ + (∫ _s in (0 : ℝ)..(t : ℝ), a) +
        (Elementary.constant (ℱ := ℱ) (P := P) T hT σ).integral W t ω)) :
    X 0 =ᵐ[P] (fun _ => x₀) := by
  filter_upwards [hEq 0 bot_le] with ω hω
  simpa only [NNReal.coe_zero, intervalIntegral.integral_same,
    Elementary.integral_zero_time, add_zero] using hω

end Volume4Chapter24
