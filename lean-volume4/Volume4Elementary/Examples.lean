import Volume4Elementary.Basic
import Volume4Stage0.BrownianCheck
import Mathlib.Tactic.NormNum

/-!
# Constant and one-step Brownian examples

The integrals below are obtained from the finite-sum definition in `Basic`.
The coefficient in the random example is the already observed value W₁.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open Volume4Stage0.BrownianCheck

namespace Volume4Elementary.Examples

theorem constant_brownian_integral (T : ℝ≥0) (hT : 0 < T) (σ : ℝ) :
    ∀ᵐ ω ∂gaussianLimit, ∀ t : ℝ≥0, t ≤ T →
      (Elementary.constant (ℱ := naturalFiltration) (P := gaussianLimit) T hT σ).integral
        brownian t ω = σ * brownian t ω := by
  filter_upwards [brownian_zero] with ω hω
  intro t ht
  rw [Elementary.integral_constant T hT σ brownian ht ω, hω, sub_zero]

def zeroOneTwo : Partition (0 : ℝ≥0) 2 where
  n := 2
  time := ![0, 1, 2]
  strictMono_time := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  time_zero := rfl
  time_last := rfl

/-- The process is zero on (0,1] and W₁ on (1,2]. -/
noncomputable def brownianStep : Elementary naturalFiltration gaussianLimit 0 2 where
  partition := zeroOneTwo
  coeff i := if i.val = 0 then (fun _ => 0) else brownian 1
  measurable_coeff i := by
    fin_cases i
    · exact stronglyMeasurable_const
    · exact filtered_brownian.stronglyAdapted 1
  memLp_coeff i := by
    fin_cases i
    · exact memLp_const (0 : ℝ)
    · exact (isGaussianProcess_brownian.hasGaussianLaw_eval 1).memLp_two

theorem brownianStep_value (t : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    brownianStep.value t ω = if 1 < t ∧ t ≤ 2 then brownian 1 ω else 0 := by
  unfold Elementary.value
  change (∑ i : Fin 2, _) = _
  rw [Fin.sum_univ_two]
  simp [brownianStep, zeroOneTwo, segment]

theorem brownianStep_integral (t : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    brownianStep.integral brownian t ω =
      brownian 1 ω * (brownian (min t 2) ω - brownian (min t 1) ω) := by
  unfold Elementary.integral
  change (∑ i : Fin 2, _) = _
  rw [Fin.sum_univ_two]
  simp [brownianStep, zeroOneTwo]

theorem brownianStep_integral_before_one {t : ℝ≥0} (ht : t ≤ 1) (ω : ℝ≥0 → ℝ) :
    brownianStep.integral brownian t ω = 0 := by
  have ht2 : t ≤ 2 := ht.trans (by norm_num)
  simp [brownianStep_integral, min_eq_left ht, min_eq_left ht2]

theorem brownianStep_integral_at_two (ω : ℝ≥0 → ℝ) :
    brownianStep.integral brownian 2 ω = brownian 1 ω * (brownian 2 ω - brownian 1 ω) := by
  norm_num [brownianStep_integral]

theorem brownianStep_value_at_one (ω : ℝ≥0 → ℝ) : brownianStep.value 1 ω = 0 := by
  norm_num [brownianStep_value]

theorem brownianStep_value_at_two (ω : ℝ≥0 → ℝ) :
    brownianStep.value 2 ω = brownian 1 ω := by
  norm_num [brownianStep_value]

end Volume4Elementary.Examples
