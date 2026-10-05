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

theorem independent_L2_product
    (hind : IndepFun X Y P) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    MemLp (X * Y) 2 P ∧
      (∫ ω, (X ω * Y ω) ^ 2 ∂P) =
        (∫ ω, (X ω) ^ 2 ∂P) * ∫ ω, (Y ω) ^ 2 ∂P := by
  have hsq : IndepFun (fun ω => (X ω) ^ 2) (fun ω => (Y ω) ^ 2) P :=
    hind.comp (by fun_prop : Measurable (fun x : ℝ => x ^ 2))
      (by fun_prop : Measurable (fun x : ℝ => x ^ 2))
  constructor
  · apply (memLp_two_iff_integrable_sq
      (hX.aestronglyMeasurable.mul hY.aestronglyMeasurable)).2
    have hprod := hsq.integrable_mul hX.integrable_sq hY.integrable_sq
    change Integrable (fun ω => (X ω) ^ 2 * (Y ω) ^ 2) P at hprod
    change Integrable (fun ω => (X ω * Y ω) ^ 2) P
    simpa only [mul_pow] using hprod
  · simpa only [mul_pow] using
      hsq.integral_fun_mul_eq_mul_integral
        hX.integrable_sq.aestronglyMeasurable hY.integrable_sq.aestronglyMeasurable

end Volume4Chapter21
