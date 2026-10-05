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

theorem conditional_mean_of_independence [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hX : Measurable[mΩ] X) (hL : Integrable X P)
    (hind : Indep (MeasurableSpace.comap X inferInstance) m P) :
    Integrable X P ∧ P[X | m] =ᵐ[P] (fun _ => ∫ ω, X ω ∂P) := by
  refine ⟨hL, ?_⟩
  exact condExp_indep_eq hX.comap_le hm
    (comap_measurable X).stronglyMeasurable hind

end Volume4Chapter21
