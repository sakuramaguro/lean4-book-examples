import Volume4Elementary.ConstantSDEExamples

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Volume4Elementary
open Volume4Elementary.ConstantSDE
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter24

theorem negative_drift_integral (t : ℝ≥0) :
    (∫ _s in (0 : ℝ)..(t : ℝ), (-2 : ℝ)) = (-2 : ℝ) * (t : ℝ) :=
  drift_integral (-2) t

end Volume4Chapter24
