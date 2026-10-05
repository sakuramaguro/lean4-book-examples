import Volume4Elementary.FiniteSumIsometry

/-!
# Two nonzero random coefficients

The coefficient W₂ on (2,3] can depend on the preceding increment W₂ - W₁.
The general cross-moment theorem applies without independence of summands.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open Volume4Stage0.BrownianCheck

namespace Volume4Elementary.FiniteExamples

def oneTwoThree : Partition (1 : ℝ≥0) 3 where
  n := 2
  time := ![1, 2, 3]
  strictMono_time := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *
  time_zero := rfl
  time_last := rfl

/-- H is W₁ on (1,2] and W₂ on (2,3], and zero elsewhere. -/
noncomputable def brownianTwoStep : Elementary naturalFiltration gaussianLimit 1 3 where
  partition := oneTwoThree
  coeff i := brownian (oneTwoThree.time i.castSucc)
  measurable_coeff i := filtered_brownian.stronglyAdapted (oneTwoThree.time i.castSucc)
  memLp_coeff i :=
    (isGaussianProcess_brownian.hasGaussianLaw_eval (oneTwoThree.time i.castSucc)).memLp_two

theorem brownian_second_moment (t : ℝ≥0) :
    (∫ ω, (brownian t ω) ^ 2 ∂gaussianLimit) = (t : ℝ) := by
  calc
    _ = ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 t :=
      hasLaw_brownian_eval.integral_comp (by fun_prop)
    _ = (t : ℝ) := OneStep.gaussian_second_moment t

theorem brownianTwoStep_value (s : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    brownianTwoStep.value s ω =
      (if 1 < s ∧ s ≤ 2 then brownian 1 ω else 0) +
      (if 2 < s ∧ s ≤ 3 then brownian 2 ω else 0) := by
  unfold Elementary.value
  change (∑ i : Fin 2, _) = _
  rw [Fin.sum_univ_two]
  rfl

theorem brownianTwoStep_integral (t : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    brownianTwoStep.integral brownian t ω =
      brownian 1 ω * (brownian (min t 2) ω - brownian (min t 1) ω) +
      brownian 2 ω * (brownian (min t 3) ω - brownian (min t 2) ω) := by
  unfold Elementary.integral
  change (∑ i : Fin 2, _) = _
  rw [Fin.sum_univ_two]
  simp [brownianTwoStep, oneTwoThree]

theorem brownianTwoStep_memLp (t : ℝ≥0) :
    MemLp (brownianTwoStep.integral brownian t) 2 gaussianLimit :=
  FiniteSum.integral_memLp filtered_brownian brownianTwoStep t

theorem brownianTwoStep_cross_moment (t : ℝ≥0) :
    (∫ ω, (brownian 1 ω * (brownian (min t 2) ω - brownian (min t 1) ω)) *
      (brownian 2 ω * (brownian (min t 3) ω - brownian (min t 2) ω)) ∂gaussianLimit) = 0 := by
  have h := FiniteSum.term_cross_moment_of_lt filtered_brownian brownianTwoStep t
    (show (0 : Fin 2) < 1 by decide)
  simpa [FiniteSum.term, brownianTwoStep, oneTwoThree] using h

theorem brownianTwoStep_second_moment (t : ℝ≥0) :
    (∫ ω, (brownianTwoStep.integral brownian t ω) ^ 2 ∂gaussianLimit) =
      (↑(min t (2 : ℝ≥0)) - ↑(min t (1 : ℝ≥0)) : ℝ) +
        2 * (↑(min t (3 : ℝ≥0)) - ↑(min t (2 : ℝ≥0)) : ℝ) := by
  rw [FiniteSum.integral_second_moment filtered_brownian brownianTwoStep t]
  change (∑ i : Fin 2, _) = _
  rw [Fin.sum_univ_two]
  simp [brownianTwoStep, oneTwoThree, brownian_second_moment, mul_comm]

theorem brownianTwoStep_second_moment_at_three :
    (∫ ω, (brownianTwoStep.integral brownian 3 ω) ^ 2 ∂gaussianLimit) = 3 := by
  norm_num [brownianTwoStep_second_moment]

theorem brownianTwoStep_ito_isometry (t : ℝ≥0) :
    (∫ ω, (brownianTwoStep.integral brownian t ω) ^ 2 ∂gaussianLimit) =
      ∫ ω, (∫ s in (0 : ℝ)..(t : ℝ), (brownianTwoStep.value s.toNNReal ω) ^ 2)
        ∂gaussianLimit :=
  FiniteSum.ito_isometry filtered_brownian brownianTwoStep t

end Volume4Elementary.FiniteExamples
