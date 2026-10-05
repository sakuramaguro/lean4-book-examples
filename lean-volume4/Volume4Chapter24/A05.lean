import Volume4Elementary.ConstantSDEExamples

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Volume4Elementary
open Volume4Elementary.ConstantSDE
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter24

theorem changed_coefficients_solution (T : ℝ≥0) (hT : 0 < T) :
    IsSolution (ℱ := naturalFiltration) (P := gaussianLimit)
      brownian T hT 2 (-1 / 2) 3
      (candidate brownian 2 (-1 / 2) 3) :=
  Volume4Elementary.SDEExamples.brownian_candidate_isSolution T hT 2 (-1 / 2) 3

theorem changed_coefficients_unique
    (T : ℝ≥0) (hT : 0 < T) {X : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ}
    (hX : IsSolution (ℱ := naturalFiltration) (P := gaussianLimit)
      brownian T hT 2 (-1 / 2) 3 X) :
    ∀ᵐ ω ∂gaussianLimit, ∀ t : ℝ≥0, t ≤ T →
      X t ω = 2 + (-1 / 2 : ℝ) * (t : ℝ) + 3 * brownian t ω :=
  hX.eq_candidate filtered_brownian constructed_brownian.cont

end Volume4Chapter24
