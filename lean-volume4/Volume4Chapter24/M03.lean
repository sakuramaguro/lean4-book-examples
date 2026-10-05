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

theorem explicit_solution
    (hW : IsFilteredPreBrownian W ℱ P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => W t ω))
    (T : ℝ≥0) (hT : 0 < T) (x₀ a σ : ℝ) :
    IsSolution (ℱ := ℱ) (P := P) W T hT x₀ a σ
      (candidate W x₀ a σ) where
  measurable_at t _ :=
    (candidate_stronglyAdapted hW.stronglyAdapted x₀ a σ t).measurable
  continuous_paths := candidate_continuous_paths x₀ a σ T hcont
  initial := candidate_initial x₀ a σ hW.eval_zero_ae_eq_zero
  integral_eq t ht :=
    (candidate_integral_equation (ℱ := ℱ) T hT x₀ a σ
      hW.eval_zero_ae_eq_zero).mono (fun _ hω => hω t ht)

end Volume4Chapter24
