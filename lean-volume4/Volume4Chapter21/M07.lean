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

theorem independent_gaussian_sum {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0}
    (hind : IndepFun X Y P)
    (hX : HasLaw X (gaussianReal m₁ v₁) P)
    (hY : HasLaw Y (gaussianReal m₂ v₂) P) :
    HasLaw (X + Y) (gaussianReal (m₁ + m₂) (v₁ + v₂)) P where
  aemeasurable := hX.aemeasurable.add hY.aemeasurable
  map_eq := gaussianReal_add_gaussianReal_of_indepFun hind hX.map_eq hY.map_eq

end Volume4Chapter21
