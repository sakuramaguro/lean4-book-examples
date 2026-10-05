import Volume4Stage0.BrownianCheck
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter22

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ}

theorem increment_mean_and_second_moment
    (hW : IsFilteredPreBrownian W ℱ P) {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, (W t ω - W s ω) ∂P) = 0 ∧
    (∫ ω, (W t ω - W s ω) ^ 2 ∂P) = (t : ℝ) - s := by
  constructor
  · rw [integral_sub (hW.integrable_eval t) (hW.integrable_eval s),
      hW.integral_eval, hW.integral_eval, sub_self]
  · have hg (v : ℝ≥0) :
        (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = (v : ℝ) := by
      have hv := variance_fun_id_gaussianReal (μ := 0) (v := v)
      rw [variance_eq_integral (X := fun x : ℝ => x) (by fun_prop)] at hv
      simpa only [integral_id_gaussianReal, sub_zero] using hv
    calc
      _ = ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 (nndist (t : ℝ) (s : ℝ)) :=
        (hW.toIsPreBrownianReal.hasLaw_sub t s).integral_comp (by fun_prop)
      _ = (nndist (t : ℝ) (s : ℝ) : ℝ) := hg _
      _ = (t : ℝ) - s := by
        rw [coe_nndist, Real.dist_eq, abs_of_nonneg]
        exact sub_nonneg.mpr (by exact_mod_cast hst)

end Volume4Chapter22
