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

theorem simultaneous_unique
    {T : ℝ≥0} {hT : 0 < T} {x₀ a σ : ℝ}
    (hX : IsSolution (ℱ := ℱ) (P := P) W T hT x₀ a σ X)
    (hY : IsSolution (ℱ := ℱ) (P := P) W T hT x₀ a σ Y) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T → X t ω = Y t ω := by
  have h := indistinguishable_on_closed_interval T
    (fun t : Set.Icc (0 : ℝ≥0) T => X t)
    (fun t : Set.Icc (0 : ℝ≥0) T => Y t)
    hX.continuous_paths hY.continuous_paths
    (fun t => hX.ae_eq_at hY t.property.2)
  filter_upwards [h] with ω hω
  intro t ht
  exact hω ⟨t, bot_le, ht⟩

end Volume4Chapter24
