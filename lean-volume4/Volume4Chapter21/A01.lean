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

theorem cdf_from_law {ν : Measure ℝ}
    (hX : HasLaw X ν P) (c : ℝ) :
    P {ω | X ω ≤ c} = ν (Set.Iic c) :=
  hX.measure_eq measurableSet_Iic

end Volume4Chapter21
