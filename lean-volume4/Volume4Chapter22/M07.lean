import Volume4Stage0.BrownianCheck
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter22

theorem countable_same_null_set
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    {P : Measure Ω} (X Y : ι → Ω → ℝ)
    (h : ∀ t, X t =ᵐ[P] Y t) :
    ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω :=
  ae_all_iff.2 h

end Volume4Chapter22
