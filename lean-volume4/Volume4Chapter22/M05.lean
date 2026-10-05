import Volume4Stage0.BrownianCheck
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter22

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ}

theorem increment_condExp_zero [IsProbabilityMeasure P]
    (hW : IsFilteredPreBrownian W ℱ P) {s t : ℝ≥0} (hst : s ≤ t) :
    P[W t - W s | ℱ s] =ᵐ[P] (fun _ => (0 : ℝ)) := by
  have hmeas (u : ℝ≥0) : Measurable (W u) :=
    ((hW.stronglyAdapted u).mono (ℱ.le u)).measurable
  have hcond : P[W t - W s | ℱ s] =ᵐ[P]
      (fun _ => ∫ ω, (W t ω - W s ω) ∂P) := by
    refine condExp_indep_eq ?_ (ℱ.le s) ?_ (hW.indep s t hst)
    · exact Measurable.comap_le ((hmeas t).sub (hmeas s))
    · exact (comap_measurable (W t - W s)).stronglyMeasurable
  have hmean : (∫ ω, (W t ω - W s ω) ∂P) = 0 := by
    rw [integral_sub (hW.integrable_eval t) (hW.integrable_eval s),
      hW.integral_eval, hW.integral_eval, sub_self]
  simpa only [hmean] using hcond

end Volume4Chapter22
