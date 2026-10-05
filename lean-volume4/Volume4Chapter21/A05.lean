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

theorem zero_variance_gaussian {a : ℝ}
    (hX : HasLaw X (gaussianReal a 0) P) :
    X =ᵐ[P] (fun _ => a) := by
  rw [gaussianReal_zero_var] at hX
  exact hX.ae_eq_of_dirac

end Volume4Chapter21
