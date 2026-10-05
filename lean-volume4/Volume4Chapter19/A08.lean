import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter19

theorem conditional_second_moment :
    P[fun ω => (terminal ω) ^ 2 | firstInfo] =ᵐ[P] (fun _ => (5 : ℝ)) := by
  have hf : Integrable (fun ω => (terminal ω) ^ 2) P := Integrable.of_finite
  have hg : Integrable (fun _ : Ω => (5 : ℝ)) P := Integrable.of_finite
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq firstInfo_le hf
  · intro s _ _
    exact hg.integrableOn
  · intro s hs _
    obtain ⟨u, hu, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    rw [← integral_indicator (measurable_fst hu),
      ← integral_indicator (measurable_fst hu)]
    classical
    by_cases hfalse : false ∈ u <;> by_cases htrue : true ∈ u <;>
      norm_num [P, PMF.integral_eq_sum, PMF.uniformOfFintype_apply,
        Fintype.sum_prod_type, terminal, ξ₁, ξ₂, sign, Set.indicator, hfalse, htrue]
  · exact stronglyMeasurable_const.aestronglyMeasurable

theorem square_of_conditional_mean :
    (fun ω => ((P[terminal | firstInfo]) ω) ^ 2) =ᵐ[P] (fun _ => (1 : ℝ)) := by
  filter_upwards [condExp_terminal_first] with ω hω
  rw [hω]
  rcases ω with ⟨a, b⟩
  cases a <;> norm_num [ξ₁, sign]

end Volume4Chapter19
