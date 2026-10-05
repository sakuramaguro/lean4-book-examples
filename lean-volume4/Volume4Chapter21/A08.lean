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

theorem centered_gaussian_conditional_mean [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {v : ℝ≥0}
    (hX : Measurable[mΩ] X) (hlaw : HasLaw X (gaussianReal 0 v) P)
    (hind : Indep (MeasurableSpace.comap X inferInstance) m P) :
    Integrable X P ∧ P[X | m] =ᵐ[P] (fun _ => (0 : ℝ)) := by
  refine ⟨hlaw.hasGaussianLaw.integrable, ?_⟩
  have hcond : P[X | m] =ᵐ[P] (fun _ => ∫ ω, X ω ∂P) :=
    condExp_indep_eq hX.comap_le hm (comap_measurable X).stronglyMeasurable hind
  have hmean : (∫ ω, X ω ∂P) = 0 :=
    hlaw.integral_eq.trans integral_id_gaussianReal
  simpa only [hmean] using hcond

end Volume4Chapter21
