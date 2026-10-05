import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter19

theorem affine_conditional_mean (a b c : ℝ) :
    P[fun ω => a * ξ₁ ω + b * ξ₂ ω + c | firstInfo] =ᵐ[P]
      (fun ω => a * ξ₁ ω + c) := by
  have hf : Integrable (fun ω => a * ξ₁ ω + b * ξ₂ ω + c) P :=
    Integrable.of_finite
  have hg : Integrable (fun ω => a * ξ₁ ω + c) P := Integrable.of_finite
  have hmeas : StronglyMeasurable[firstInfo] (fun ω => a * ξ₁ ω + c) :=
    ((measurable_const.mul first_stronglyMeasurable.measurable).add
      measurable_const).stronglyMeasurable
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
        Fintype.sum_prod_type, ξ₁, ξ₂, sign, Set.indicator, hfalse, htrue] <;> ring
  · exact hmeas.aestronglyMeasurable

end Volume4Chapter19
