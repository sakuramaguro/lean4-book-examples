import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Volume4Chapter21

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {X Y : Ω → ℝ}

theorem product_with_centered_variable
    (hind : IndepFun X Y P) (hX : Integrable X P) (hY : Integrable Y P)
    (hmean : (∫ ω, Y ω ∂P) = 0) :
    Integrable (X * Y) P ∧ (∫ ω, X ω * Y ω ∂P) = 0 := by
  refine ⟨hind.integrable_mul hX hY, ?_⟩
  rw [hind.integral_fun_mul_eq_mul_integral
    hX.aestronglyMeasurable hY.aestronglyMeasurable, hmean, mul_zero]

end Volume4Chapter21
