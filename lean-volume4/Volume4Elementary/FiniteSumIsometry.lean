import Volume4Elementary.OneStepIsometry

/-!
# The Itô isometry for elementary integrals on finite deterministic partitions

Coefficients need only be measurable at their left endpoints and belong to L².
The weighted increments are orthogonal; they need not be independent.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Volume4Elementary.FiniteSum

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {a b : ℝ≥0}

theorem earlier_end_le_later_start (p : Partition a b) {i j : Fin p.n} (hij : i < j) :
    p.time i.succ ≤ p.time j.castSucc := by
  apply p.strictMono_time.monotone
  change i.val + 1 ≤ j.val
  exact Nat.succ_le_of_lt hij

/-- A single summand in the finite-sum definition of the elementary integral. -/
noncomputable def term (H : Elementary ℱ P a b) (W : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (i : Fin H.partition.n) (ω : Ω) : ℝ :=
  H.coeff i ω * (W (min t (H.partition.time i.succ)) ω -
    W (min t (H.partition.time i.castSucc)) ω)

theorem integral_eq_sum_terms (H : Elementary ℱ P a b) (t : ℝ≥0) (ω : Ω) :
    H.integral W t ω = ∑ i, term H W t i ω := rfl

theorem term_eq_zero_of_le (H : Elementary ℱ P a b) (i : Fin H.partition.n)
    {t : ℝ≥0} (ht : t ≤ H.partition.time i.castSucc) (ω : Ω) :
    term H W t i ω = 0 := by
  simp only [term, min_eq_left ht,
    min_eq_left (ht.trans (H.partition.adjacent_lt i).le), sub_self, mul_zero]

theorem term_memLp [IsProbabilityMeasure P] (hW : IsFilteredPreBrownian W ℱ P)
    (H : Elementary ℱ P a b) (t : ℝ≥0) (i : Fin H.partition.n) :
    MemLp (term H W t i) 2 P := by
  convert OneStep.integral_oneStep_memLp hW _ _ (H.partition.adjacent_lt i)
    (H.coeff i) (H.measurable_coeff i) (H.memLp_coeff i) t using 1
  funext ω
  exact (Elementary.integral_oneStep _ _ _ _ _ _ W t ω).symm

theorem term_second_moment (hW : IsFilteredPreBrownian W ℱ P)
    (H : Elementary ℱ P a b) (t : ℝ≥0) (i : Fin H.partition.n) :
    (∫ ω, (term H W t i ω) ^ 2 ∂P) =
      (↑(min t (H.partition.time i.succ)) - ↑(min t (H.partition.time i.castSucc)) : ℝ) *
        ∫ ω, H.coeff i ω ^ 2 ∂P := by
  simpa only [term, Elementary.integral_oneStep] using
    OneStep.integral_oneStep_second_moment hW _ _ (H.partition.adjacent_lt i)
      (H.coeff i) (H.measurable_coeff i) (H.memLp_coeff i) t

theorem term_stronglyMeasurable_of_end_le (hW : IsFilteredPreBrownian W ℱ P)
    (H : Elementary ℱ P a b) (t : ℝ≥0) (i : Fin H.partition.n)
    {s : ℝ≥0} (hs : H.partition.time i.succ ≤ s) :
    StronglyMeasurable[ℱ s] (term H W t i) := by
  have hcoeff := (H.measurable_coeff i).mono
    (ℱ.mono ((H.partition.adjacent_lt i).le.trans hs))
  have hend := (hW.stronglyAdapted (min t (H.partition.time i.succ))).mono
    (ℱ.mono ((min_le_right _ _).trans hs))
  have hstart := (hW.stronglyAdapted (min t (H.partition.time i.castSucc))).mono
    (ℱ.mono ((min_le_right _ _).trans ((H.partition.adjacent_lt i).le.trans hs)))
  exact hcoeff.mul (hend.sub hstart)

theorem integrable_past_mul_increment_mean_zero (hW : IsFilteredPreBrownian W ℱ P)
    {c d : ℝ≥0} (hcd : c ≤ d) {ζ : Ω → ℝ}
    (hζ : StronglyMeasurable[ℱ c] ζ) (hL1 : Integrable ζ P) :
    (∫ ω, ζ ω * (W d ω - W c ω) ∂P) = 0 := by
  have hind := OneStep.coefficient_indep_increment hW hcd hζ
  have hfactor := hind.integral_fun_mul_eq_mul_integral hL1.aestronglyMeasurable
    (OneStep.increment_memLp hW c d).aestronglyMeasurable
  simp only [Pi.sub_apply] at hfactor
  rw [hfactor, integral_sub (hW.integrable_eval d) (hW.integrable_eval c),
    hW.integral_eval, hW.integral_eval, sub_self, mul_zero]

theorem term_mul_integrable [IsProbabilityMeasure P] (hW : IsFilteredPreBrownian W ℱ P)
    (H : Elementary ℱ P a b) (t : ℝ≥0) (i j : Fin H.partition.n) :
    Integrable (fun ω => term H W t i ω * term H W t j ω) P :=
  (term_memLp hW H t i).integrable_mul (term_memLp hW H t j)

theorem term_cross_moment_of_lt [IsProbabilityMeasure P]
    (hW : IsFilteredPreBrownian W ℱ P) (H : Elementary ℱ P a b) (t : ℝ≥0)
    {i j : Fin H.partition.n} (hij : i < j) :
    (∫ ω, term H W t i ω * term H W t j ω ∂P) = 0 := by
  by_cases ht : t ≤ H.partition.time j.castSucc
  · simp only [term_eq_zero_of_le H j ht, mul_zero, integral_zero]
  · have hstart : H.partition.time j.castSucc ≤ t := (lt_of_not_ge ht).le
    have hζ : StronglyMeasurable[ℱ (H.partition.time j.castSucc)]
        (fun ω => term H W t i ω * H.coeff j ω) :=
      (term_stronglyMeasurable_of_end_le hW H t i
        (earlier_end_le_later_start H.partition hij)).mul (H.measurable_coeff j)
    have hL1 : Integrable (fun ω => term H W t i ω * H.coeff j ω) P :=
      (term_memLp hW H t i).integrable_mul (H.memLp_coeff j)
    have hz := integrable_past_mul_increment_mean_zero hW
      (le_min hstart (H.partition.adjacent_lt j).le) hζ hL1
    simpa only [term, min_eq_right hstart, mul_assoc] using hz

theorem term_cross_moment [IsProbabilityMeasure P]
    (hW : IsFilteredPreBrownian W ℱ P) (H : Elementary ℱ P a b) (t : ℝ≥0)
    {i j : Fin H.partition.n} (hij : i ≠ j) :
    (∫ ω, term H W t i ω * term H W t j ω ∂P) = 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact term_cross_moment_of_lt hW H t hlt
  · simpa only [mul_comm] using term_cross_moment_of_lt hW H t hgt

theorem integral_memLp [IsProbabilityMeasure P] (hW : IsFilteredPreBrownian W ℱ P)
    (H : Elementary ℱ P a b) (t : ℝ≥0) : MemLp (H.integral W t) 2 P := by
  exact memLp_finsetSum _ (fun i _ => term_memLp hW H t i)

theorem integral_sq_sum_of_cross_moments_zero {ι : Type*} [Fintype ι]
    (X : ι → Ω → ℝ) (hLp : ∀ i, MemLp (X i) 2 P)
    (hcross : ∀ i j, i ≠ j → (∫ ω, X i ω * X j ω ∂P) = 0) :
    (∫ ω, (∑ i, X i ω) ^ 2 ∂P) = ∑ i, ∫ ω, (X i ω) ^ 2 ∂P := by
  classical
  have hprod : ∀ i j, Integrable (fun ω => X i ω * X j ω) P :=
    fun i j => (hLp i).integrable_mul (hLp j)
  calc
    _ = ∫ ω, ∑ i, ∑ j, X i ω * X j ω ∂P := by
      simp_rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ i, ∑ j, ∫ ω, X i ω * X j ω ∂P := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hprod i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j _ => hprod i j)
    _ = ∑ i, ∫ ω, (X i ω) ^ 2 ∂P := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp only [pow_two]
      · intro j _ hji
        exact hcross i j hji.symm
      · simp

theorem integral_second_moment [IsProbabilityMeasure P]
    (hW : IsFilteredPreBrownian W ℱ P) (H : Elementary ℱ P a b) (t : ℝ≥0) :
    (∫ ω, (H.integral W t ω) ^ 2 ∂P) =
      ∑ i, (↑(min t (H.partition.time i.succ)) -
        ↑(min t (H.partition.time i.castSucc)) : ℝ) * ∫ ω, H.coeff i ω ^ 2 ∂P := by
  simp_rw [integral_eq_sum_terms]
  rw [integral_sq_sum_of_cross_moments_zero (term H W t)
    (term_memLp hW H t) (fun _ _ hij => term_cross_moment hW H t hij)]
  exact Finset.sum_congr rfl (fun i _ => term_second_moment hW H t i)

theorem sq_sum_of_mul_eq_zero {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hcross : ∀ i j, i ≠ j → x i * x j = 0) :
    (∑ i, x i) ^ 2 = ∑ i, x i ^ 2 := by
  classical
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · exact (pow_two _).symm
  · intro j _ hji
    exact hcross i j hji.symm
  · simp

theorem segments_mul_eq_zero_of_lt (H : Elementary ℱ P a b)
    {i j : Fin H.partition.n} (hij : i < j) (s : ℝ≥0) (ω : Ω) :
    segment (H.partition.time i.castSucc) (H.partition.time i.succ) (H.coeff i ω) s *
      segment (H.partition.time j.castSucc) (H.partition.time j.succ) (H.coeff j ω) s = 0 := by
  by_cases hi : H.partition.time i.castSucc < s ∧ s ≤ H.partition.time i.succ
  · have hj : ¬(H.partition.time j.castSucc < s ∧ s ≤ H.partition.time j.succ) := by
      intro hj
      exact (not_lt_of_ge (hi.2.trans (earlier_end_le_later_start H.partition hij))) hj.1
    simp only [segment, if_pos hi, if_neg hj, mul_zero]
  · simp only [segment, if_neg hi, zero_mul]

theorem value_sq_eq_sum (H : Elementary ℱ P a b) (s : ℝ≥0) (ω : Ω) :
    (H.value s ω) ^ 2 =
      ∑ i, (segment (H.partition.time i.castSucc) (H.partition.time i.succ)
        (H.coeff i ω) s) ^ 2 := by
  apply sq_sum_of_mul_eq_zero
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact segments_mul_eq_zero_of_lt H hlt s ω
  · simpa only [mul_comm] using segments_mul_eq_zero_of_lt H hgt s ω

theorem value_sq_intervalIntegrable (H : Elementary ℱ P a b) (t : ℝ≥0) (ω : Ω) :
    IntervalIntegrable (fun s : ℝ => (H.value s.toNNReal ω) ^ 2) volume 0 (t : ℝ) := by
  simp_rw [value_sq_eq_sum]
  apply intervalIntegrable_iff.mpr
  exact integrable_finsetSum _ (fun i _ =>
    (OneStep.segment_sq_intervalIntegrable (H.partition.time i.castSucc)
      (H.partition.time i.succ) (H.coeff i ω) t).def')

theorem time_energy (H : Elementary ℱ P a b) (t : ℝ≥0) (ω : Ω) :
    (∫ s in (0 : ℝ)..(t : ℝ), (H.value s.toNNReal ω) ^ 2) =
      ∑ i, (↑(min t (H.partition.time i.succ)) -
        ↑(min t (H.partition.time i.castSucc)) : ℝ) * H.coeff i ω ^ 2 := by
  simp_rw [value_sq_eq_sum]
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    OneStep.segment_sq_intervalIntegrable (H.partition.time i.castSucc)
      (H.partition.time i.succ) (H.coeff i ω) t)]
  exact Finset.sum_congr rfl (fun i _ =>
    OneStep.segment_time_energy (H.partition.adjacent_lt i).le (H.coeff i ω) t)

theorem time_energy_integrable (H : Elementary ℱ P a b) (t : ℝ≥0) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(t : ℝ), (H.value s.toNNReal ω) ^ 2) P := by
  simp_rw [time_energy]
  exact integrable_finsetSum _ (fun i _ => (H.memLp_coeff i).integrable_sq.const_mul _)

theorem ito_isometry [IsProbabilityMeasure P] (hW : IsFilteredPreBrownian W ℱ P)
    (H : Elementary ℱ P a b) (t : ℝ≥0) :
    (∫ ω, (H.integral W t ω) ^ 2 ∂P) =
      ∫ ω, (∫ s in (0 : ℝ)..(t : ℝ), (H.value s.toNNReal ω) ^ 2) ∂P := by
  simp_rw [time_energy]
  rw [integral_finsetSum _ (fun i _ => (H.memLp_coeff i).integrable_sq.const_mul _)]
  simp_rw [integral_const_mul]
  exact integral_second_moment hW H t

end Volume4Elementary.FiniteSum
