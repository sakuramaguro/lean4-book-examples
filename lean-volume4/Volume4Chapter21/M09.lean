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

theorem information_measurable_independent
    {m : MeasurableSpace Ω} {ξ Δ : Ω → ℝ}
    (hξ : StronglyMeasurable[m] ξ)
    (hind : Indep (MeasurableSpace.comap Δ inferInstance) m P) :
    IndepFun ξ Δ P := by
  apply (IndepFun_iff_Indep _ _ _).2
  exact (indep_of_indep_of_le_right hind hξ.measurable.comap_le).symm

end Volume4Chapter21
