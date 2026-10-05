import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter19

theorem conditional_mean_from_characterization :
    P[terminal | firstInfo] =ᵐ[P] ξ₁ := by
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq firstInfo_le integrable_terminal
  · intro s _ _
    exact integrable_first.integrableOn
  · intro s hs _
    obtain ⟨u, hu, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    rw [← integral_indicator (measurable_fst hu),
      ← integral_indicator (measurable_fst hu)]
    classical
    by_cases hfalse : false ∈ u <;> by_cases htrue : true ∈ u <;>
      norm_num [P, PMF.integral_eq_sum, PMF.uniformOfFintype_apply,
        Fintype.sum_prod_type, terminal, ξ₁, ξ₂, sign, Set.indicator, hfalse, htrue]
  · exact first_stronglyMeasurable.aestronglyMeasurable

end Volume4Chapter19
