import Volume4Elementary.FiniteSumExamples

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open Volume4Elementary
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter23

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {a b : ℝ≥0}

theorem split_same_coefficient (ξ : Ω → ℝ)
    (a c b t : ℝ≥0) (ω : Ω) :
    ξ ω * (W (min t c) ω - W (min t a) ω) +
      ξ ω * (W (min t b) ω - W (min t c) ω) =
        ξ ω * (W (min t b) ω - W (min t a) ω) := by
  ring

end Volume4Chapter23
