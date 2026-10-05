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

theorem cutoff_solution
    {T : ℝ≥0} {hT : 0 < T} {x₀ a σ : ℝ}
    (hX : IsSolution (ℱ := ℱ) (P := P) W T hT x₀ a σ X) :
    IsSolution (ℱ := ℱ) (P := P) W T hT x₀ a σ
      (fun t ω => if t ≤ T then X t ω else 0) where
  measurable_at t ht := by
    simpa only [if_pos ht] using hX.measurable_at t ht
  continuous_paths := by
    filter_upwards [hX.continuous_paths] with ω hω
    have hpath :
        (fun t : Set.Icc (0 : ℝ≥0) T =>
          if (t : ℝ≥0) ≤ T then X t ω else 0) =
        (fun t : Set.Icc (0 : ℝ≥0) T => X t ω) := by
      funext t
      exact if_pos t.property.2
    rw [hpath]
    exact hω
  initial := by
    simpa only [if_pos (show (0 : ℝ≥0) ≤ T from bot_le)] using hX.initial
  integral_eq t ht := by
    simpa only [if_pos ht] using hX.integral_eq t ht

end Volume4Chapter24
