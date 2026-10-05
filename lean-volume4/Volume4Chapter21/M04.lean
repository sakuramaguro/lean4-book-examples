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

theorem independent_integrable_product
    (hind : IndepFun X Y P) (hX : Integrable X P) (hY : Integrable Y P) :
    Integrable (X * Y) P ∧
      (∫ ω, X ω * Y ω ∂P) = (∫ ω, X ω ∂P) * ∫ ω, Y ω ∂P :=
  ⟨hind.integrable_mul hX hY,
    hind.integral_fun_mul_eq_mul_integral
      hX.aestronglyMeasurable hY.aestronglyMeasurable⟩

theorem centered_product_mean_zero
    (hind : IndepFun X Y P) (hX : Integrable X P) (hY : Integrable Y P)
    (hmean : (∫ ω, Y ω ∂P) = 0) :
    Integrable (X * Y) P ∧ (∫ ω, X ω * Y ω ∂P) = 0 := by
  obtain ⟨hprod, hfactor⟩ := independent_integrable_product hind hX hY
  exact ⟨hprod, by simpa only [hmean, mul_zero] using hfactor⟩

end Volume4Chapter21
