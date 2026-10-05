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

theorem terminal_value
    (hW : IsFilteredPreBrownian W ℱ P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => W t ω))
    {T : ℝ≥0} {hT : 0 < T} {x₀ a σ : ℝ}
    (hX : IsSolution (ℱ := ℱ) (P := P) W T hT x₀ a σ X) :
    X T =ᵐ[P] (fun ω => x₀ + a * (T : ℝ) + σ * W T ω) :=
  (hX.eq_candidate hW hcont).mono (fun _ hω => hω T le_rfl)

end Volume4Chapter24
