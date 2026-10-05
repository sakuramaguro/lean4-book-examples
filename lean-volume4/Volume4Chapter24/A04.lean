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

theorem zero_diffusion_unique
    (hW : IsFilteredPreBrownian W ℱ P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => W t ω))
    {T : ℝ≥0} {hT : 0 < T} {x₀ a : ℝ}
    (hX : IsSolution (ℱ := ℱ) (P := P) W T hT x₀ a 0 X) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T → X t ω = x₀ + a * (t : ℝ) := by
  simpa only [zero_mul, add_zero] using hX.eq_candidate hW hcont

end Volume4Chapter24
