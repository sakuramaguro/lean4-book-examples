import Volume4Elementary.FiniteSumExamples

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open Volume4Elementary
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter23

theorem negative_constant_brownian_integral (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂gaussianLimit, ∀ t : ℝ≥0, t ≤ T →
      (Elementary.constant (ℱ := naturalFiltration) (P := gaussianLimit)
        T hT (-2)).integral brownian t ω = (-2 : ℝ) * brownian t ω :=
  Examples.constant_brownian_integral T hT (-2)

end Volume4Chapter23
