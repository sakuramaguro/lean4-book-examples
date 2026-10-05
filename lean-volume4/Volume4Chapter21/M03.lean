import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Volume4Chapter21

theorem independent_coordinates
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IndepFun (fun ω : ℝ × ℝ => ω.1) (fun ω : ℝ × ℝ => ω.2) (μ.prod ν) :=
  indepFun_prod measurable_id measurable_id

end Volume4Chapter21
