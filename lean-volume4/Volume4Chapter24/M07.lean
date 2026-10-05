import Volume4Elementary.ConstantSDEExamples

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Volume4Elementary
open Volume4Elementary.ConstantSDE
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter24

theorem concrete_solution (T : ℝ≥0) (hT : 0 < T) (x₀ a σ : ℝ) :
    IsSolution (ℱ := naturalFiltration) (P := gaussianLimit)
      brownian T hT x₀ a σ (candidate brownian x₀ a σ) :=
  candidate_isSolution filtered_brownian constructed_brownian.cont T hT x₀ a σ

end Volume4Chapter24
