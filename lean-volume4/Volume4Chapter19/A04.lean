import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter19

@[implicit_reducible] def secondInfo : MeasurableSpace Ω :=
  MeasurableSpace.comap Prod.snd inferInstance

theorem conditional_mean_with_second_coordinate :
    P[terminal | secondInfo] =ᵐ[P] (fun ω => 2 * ξ₂ ω) := by
  have hle : secondInfo ≤ (inferInstance : MeasurableSpace Ω) :=
    measurable_snd.comap_le
  have hmeas : StronglyMeasurable[secondInfo] (fun ω => 2 * ξ₂ ω) := by
    have hsnd : @Measurable Ω Bool secondInfo _ Prod.snd :=
      measurable_iff_comap_le.mpr le_rfl
    have hsign : Measurable[secondInfo] ξ₂ :=
      (measurable_of_finite sign).comp hsnd
    exact (measurable_const.mul hsign).stronglyMeasurable
  have hint : Integrable (fun ω => 2 * ξ₂ ω) P := Integrable.of_finite
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hle integrable_terminal
  · intro s _ _
    exact hint.integrableOn
  · intro s hs _
    obtain ⟨u, hu, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    rw [← integral_indicator (measurable_snd hu),
      ← integral_indicator (measurable_snd hu)]
    classical
    by_cases hfalse : false ∈ u <;> by_cases htrue : true ∈ u <;>
      norm_num [P, PMF.integral_eq_sum, PMF.uniformOfFintype_apply,
        Fintype.sum_prod_type, terminal, ξ₁, ξ₂, sign, Set.indicator, hfalse, htrue]
  · exact hmeas.aestronglyMeasurable

end Volume4Chapter19
