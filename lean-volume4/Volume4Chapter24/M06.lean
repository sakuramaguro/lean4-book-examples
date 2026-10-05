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

theorem existence_and_uniqueness
    (hW : IsFilteredPreBrownian W ℱ P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => W t ω))
    (T : ℝ≥0) (hT : 0 < T) (x₀ a σ : ℝ) :
    ∃ X : ℝ≥0 → Ω → ℝ,
      IsSolution (ℱ := ℱ) (P := P) W T hT x₀ a σ X ∧
      ∀ Y : ℝ≥0 → Ω → ℝ,
        IsSolution (ℱ := ℱ) (P := P) W T hT x₀ a σ Y →
          ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T → Y t ω = X t ω := by
  have hX := candidate_isSolution hW hcont T hT x₀ a σ
  exact ⟨candidate W x₀ a σ, hX, fun _ hY => hY.indistinguishable hX⟩

end Volume4Chapter24
