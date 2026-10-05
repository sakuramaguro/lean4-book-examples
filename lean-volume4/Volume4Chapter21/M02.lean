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

theorem integral_from_law {ν : Measure ℝ} {g : ℝ → ℝ}
    (hX : HasLaw X ν P) (hg : Integrable g ν) :
    Integrable (g ∘ X) P ∧
      (∫ ω, g (X ω) ∂P) = ∫ x, g x ∂ν := by
  constructor
  · have hg' : Integrable g (P.map X) := by
      simpa only [hX.map_eq] using hg
    exact hg'.comp_aemeasurable hX.aemeasurable
  · exact hX.integral_comp hg.aestronglyMeasurable

end Volume4Chapter21
