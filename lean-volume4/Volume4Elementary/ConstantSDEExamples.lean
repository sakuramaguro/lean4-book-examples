import Volume4Elementary.ConstantSDE

/-!
# The constructed Brownian motion supplies a concrete SDE model

Existence is instantiated on gaussianLimit with the natural filtration.
Two special cases identify the deterministic drift and Brownian motion itself.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Volume4Stage0.BrownianCheck
open Volume4Elementary.ConstantSDE

namespace Volume4Elementary.SDEExamples

theorem brownian_candidate_isSolution (T : ℝ≥0) (hT : 0 < T) (x₀ drift diffusion : ℝ) :
    IsSolution (ℱ := naturalFiltration) (P := gaussianLimit)
      brownian T hT x₀ drift diffusion (candidate brownian x₀ drift diffusion) :=
  candidate_isSolution filtered_brownian constructed_brownian.cont T hT x₀ drift diffusion

theorem brownian_unique_on_interval (T : ℝ≥0) (hT : 0 < T) (x₀ drift diffusion : ℝ)
    {X : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ}
    (hX : IsSolution (ℱ := naturalFiltration) (P := gaussianLimit)
      brownian T hT x₀ drift diffusion X) :
    ∀ᵐ ω ∂gaussianLimit, ∀ t : ℝ≥0, t ≤ T →
      X t ω = x₀ + drift * (t : ℝ) + diffusion * brownian t ω :=
  hX.eq_candidate filtered_brownian constructed_brownian.cont

theorem brownian_exists_solution_unique (T : ℝ≥0) (hT : 0 < T) (x₀ drift diffusion : ℝ) :
    ∃ X : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ,
      IsSolution (ℱ := naturalFiltration) (P := gaussianLimit)
        brownian T hT x₀ drift diffusion X ∧
      ∀ Y : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ,
        IsSolution (ℱ := naturalFiltration) (P := gaussianLimit)
          brownian T hT x₀ drift diffusion Y →
          ∀ᵐ ω ∂gaussianLimit, ∀ t : ℝ≥0, t ≤ T → Y t ω = X t ω :=
  exists_solution_unique_on_interval filtered_brownian constructed_brownian.cont
    T hT x₀ drift diffusion

theorem zero_diffusion_isSolution (T : ℝ≥0) (hT : 0 < T) (x₀ drift : ℝ) :
    IsSolution (ℱ := naturalFiltration) (P := gaussianLimit)
      brownian T hT x₀ drift 0 (fun t _ => x₀ + drift * (t : ℝ)) := by
  convert brownian_candidate_isSolution T hT x₀ drift 0 using 1
  funext t ω
  simp only [candidate, zero_mul, add_zero]

theorem zero_drift_unit_diffusion_isSolution (T : ℝ≥0) (hT : 0 < T) :
    IsSolution (ℱ := naturalFiltration) (P := gaussianLimit)
      brownian T hT 0 0 1 brownian := by
  convert brownian_candidate_isSolution T hT 0 0 1 using 1
  funext t ω
  simp only [candidate, zero_mul, zero_add, one_mul]

end Volume4Elementary.SDEExamples
