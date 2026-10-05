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

theorem fixed_time_unique
    {T : ℝ≥0} {hT : 0 < T} {x₀ a σ : ℝ}
    (hX : IsSolution (ℱ := ℱ) (P := P) W T hT x₀ a σ X)
    (hY : IsSolution (ℱ := ℱ) (P := P) W T hT x₀ a σ Y)
    {t : ℝ≥0} (ht : t ≤ T) : X t =ᵐ[P] Y t :=
  (hX.integral_eq t ht).trans (hY.integral_eq t ht).symm

end Volume4Chapter24
