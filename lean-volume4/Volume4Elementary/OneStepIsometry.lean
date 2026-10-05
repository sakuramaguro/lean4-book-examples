import Volume4Elementary.Examples
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# L² integrability and the Itô isometry for one elementary interval

Only L² integrability of the coefficient is assumed. Independence of the
future increment supplies the integrability of the product of squares.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Volume4Elementary.OneStep

theorem gaussian_second_moment (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = (v : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral (X := fun x : ℝ => x) (by fun_prop)] at h
  simpa only [integral_id_gaussianReal, sub_zero] using h

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

theorem coefficient_indep_increment (hW : IsFilteredPreBrownian W ℱ P)
    {a b : ℝ≥0} (hab : a ≤ b) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ a] ξ) :
    IndepFun ξ (W b - W a) P := by
  apply (IndepFun_iff_Indep _ _ _).2
  exact (indep_of_indep_of_le_right (hW.indep a b hab) hξ.measurable.comap_le).symm

theorem increment_memLp (hW : IsFilteredPreBrownian W ℱ P) (a b : ℝ≥0) :
    MemLp (W b - W a) 2 P :=
  (hW.toIsPreBrownianReal.hasLaw_sub b a).hasGaussianLaw.memLp_two

theorem increment_second_moment (hW : IsFilteredPreBrownian W ℱ P)
    {a b : ℝ≥0} (hab : a ≤ b) :
    (∫ ω, (W b ω - W a ω) ^ 2 ∂P) = (b : ℝ) - a := by
  calc
    _ = ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 (nndist (b : ℝ) (a : ℝ)) :=
      (hW.toIsPreBrownianReal.hasLaw_sub b a).integral_comp (by fun_prop)
    _ = (nndist (b : ℝ) (a : ℝ) : ℝ) := gaussian_second_moment _
    _ = (b : ℝ) - a := by
      rw [coe_nndist, Real.dist_eq, abs_of_nonneg]
      exact sub_nonneg.mpr (by exact_mod_cast hab)

theorem weighted_increment_memLp (hW : IsFilteredPreBrownian W ℱ P)
    {a b : ℝ≥0} (hab : a ≤ b) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ a] ξ) (hLp : MemLp ξ 2 P) :
    MemLp (fun ω => ξ ω * (W b ω - W a ω)) 2 P := by
  have hinc := increment_memLp hW a b
  have hind := coefficient_indep_increment hW hab hξ
  have hsq : IndepFun (fun ω => ξ ω ^ 2) (fun ω => (W b ω - W a ω) ^ 2) P :=
    hind.comp (by fun_prop : Measurable (fun x : ℝ => x ^ 2))
      (by fun_prop : Measurable (fun x : ℝ => x ^ 2))
  apply (memLp_two_iff_integrable_sq
    (hLp.aestronglyMeasurable.mul hinc.aestronglyMeasurable)).2
  have hprod := hsq.integrable_mul hLp.integrable_sq hinc.integrable_sq
  change Integrable (fun ω => ξ ω ^ 2 * (W b ω - W a ω) ^ 2) P at hprod
  change Integrable (fun ω => (ξ ω * (W b ω - W a ω)) ^ 2) P
  simpa only [mul_pow] using hprod

theorem weighted_increment_second_moment (hW : IsFilteredPreBrownian W ℱ P)
    {a b : ℝ≥0} (hab : a ≤ b) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ a] ξ) (hLp : MemLp ξ 2 P) :
    (∫ ω, (ξ ω * (W b ω - W a ω)) ^ 2 ∂P) =
      ((b : ℝ) - a) * ∫ ω, ξ ω ^ 2 ∂P := by
  have hinc := increment_memLp hW a b
  have hind := coefficient_indep_increment hW hab hξ
  have hsq : IndepFun (fun ω => ξ ω ^ 2) (fun ω => (W b ω - W a ω) ^ 2) P :=
    hind.comp (by fun_prop : Measurable (fun x : ℝ => x ^ 2))
      (by fun_prop : Measurable (fun x : ℝ => x ^ 2))
  simp_rw [mul_pow]
  rw [hsq.integral_fun_mul_eq_mul_integral hLp.integrable_sq.aestronglyMeasurable
    hinc.integrable_sq.aestronglyMeasurable, increment_second_moment hW hab]
  exact mul_comm _ _

theorem weighted_increment_mean_zero (hW : IsFilteredPreBrownian W ℱ P)
    {a b : ℝ≥0} (hab : a ≤ b) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ a] ξ) (hLp : MemLp ξ 2 P) :
    (∫ ω, ξ ω * (W b ω - W a ω) ∂P) = 0 := by
  have hind := coefficient_indep_increment hW hab hξ
  have hfactor := hind.integral_fun_mul_eq_mul_integral hLp.aestronglyMeasurable
    (increment_memLp hW a b).aestronglyMeasurable
  simp only [Pi.sub_apply] at hfactor
  rw [hfactor]
  have hzero : (∫ ω, W b ω - W a ω ∂P) = 0 := by
    rw [integral_sub (hW.integrable_eval b) (hW.integrable_eval a),
      hW.integral_eval, hW.integral_eval, sub_self]
  rw [hzero, mul_zero]

theorem integral_oneStep_memLp [IsProbabilityMeasure P] (hW : IsFilteredPreBrownian W ℱ P)
    (a b : ℝ≥0) (hab : a < b) (ξ : Ω → ℝ)
    (hξ : StronglyMeasurable[ℱ a] ξ) (hLp : MemLp ξ 2 P) (t : ℝ≥0) :
    MemLp ((Elementary.oneStep a b hab ξ hξ hLp).integral W t) 2 P := by
  change MemLp (fun ω => (Elementary.oneStep a b hab ξ hξ hLp).integral W t ω) 2 P
  simp_rw [Elementary.integral_oneStep]
  by_cases hat : a ≤ t
  · simpa only [min_eq_right hat] using
      weighted_increment_memLp hW (le_min hat hab.le) hξ hLp
  · have hta : t ≤ a := (lt_of_not_ge hat).le
    simp only [min_eq_left hta, min_eq_left (hta.trans hab.le), sub_self, mul_zero]
    exact memLp_const 0

theorem integral_oneStep_second_moment (hW : IsFilteredPreBrownian W ℱ P)
    (a b : ℝ≥0) (hab : a < b) (ξ : Ω → ℝ)
    (hξ : StronglyMeasurable[ℱ a] ξ) (hLp : MemLp ξ 2 P) (t : ℝ≥0) :
    (∫ ω, ((Elementary.oneStep a b hab ξ hξ hLp).integral W t ω) ^ 2 ∂P) =
      ((min t b : ℝ≥0) - (min t a : ℝ≥0) : ℝ) * ∫ ω, ξ ω ^ 2 ∂P := by
  simp_rw [Elementary.integral_oneStep]
  by_cases hat : a ≤ t
  · simpa only [min_eq_right hat] using
      weighted_increment_second_moment hW (le_min hat hab.le) hξ hLp
  · have hta : t ≤ a := (lt_of_not_ge hat).le
    simp [min_eq_left hta, min_eq_left (hta.trans hab.le)]

theorem integral_oneStep_second_moment_terminal (hW : IsFilteredPreBrownian W ℱ P)
    (a b : ℝ≥0) (hab : a < b) (ξ : Ω → ℝ)
    (hξ : StronglyMeasurable[ℱ a] ξ) (hLp : MemLp ξ 2 P) :
    (∫ ω, ((Elementary.oneStep a b hab ξ hξ hLp).integral W b ω) ^ 2 ∂P) =
      ((b : ℝ) - a) * ∫ ω, ξ ω ^ 2 ∂P := by
  simpa only [min_self, min_eq_right hab.le] using
    integral_oneStep_second_moment hW a b hab ξ hξ hLp b

theorem segment_sq_eq_indicator (a b : ℝ≥0) (x : ℝ) :
    (fun s : ℝ => (segment a b x s.toNNReal) ^ 2) =
      (Set.Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => x ^ 2) := by
  funext s
  simp only [segment, Real.lt_toNNReal_iff_coe_lt, Real.toNNReal_le_iff_le_coe]
  by_cases hs : (a : ℝ) < s ∧ s ≤ (b : ℝ)
  · simp [Set.indicator, Set.mem_Ioc, hs]
  · simp [Set.indicator, Set.mem_Ioc, hs]

theorem segment_sq_intervalIntegrable (a b : ℝ≥0) (x : ℝ) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => (segment a b x s.toNNReal) ^ 2)
      volume 0 (t : ℝ) := by
  rw [segment_sq_eq_indicator]
  have hconst : IntegrableOn (fun _ : ℝ => x ^ 2) (Set.Ioc (a : ℝ) (b : ℝ)) :=
    integrableOn_const measure_Ioc_lt_top.ne
  exact (hconst.integrable_indicator measurableSet_Ioc).intervalIntegrable

/-- The deterministic time integral uses Lebesgue measure on real time. -/
theorem segment_time_energy {a b : ℝ≥0} (hab : a ≤ b) (x : ℝ) (t : ℝ≥0) :
    (∫ s in (0 : ℝ)..(t : ℝ), (segment a b x s.toNNReal) ^ 2) =
      ((min t b : ℝ≥0) - (min t a : ℝ≥0) : ℝ) * x ^ 2 := by
  rw [segment_sq_eq_indicator, intervalIntegral.integral_of_le t.coe_nonneg,
    integral_indicator_const _ measurableSet_Ioc, measureReal_restrict_apply measurableSet_Ioc]
  have hset : Set.Ioc (a : ℝ) (b : ℝ) ∩ Set.Ioc 0 (t : ℝ) =
      Set.Ioc (a : ℝ) (min t b : ℝ≥0) := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ioc, NNReal.coe_min, le_min_iff]
    constructor
    · rintro ⟨⟨has, hsb⟩, ⟨_, hst⟩⟩
      exact ⟨has, hst, hsb⟩
    · rintro ⟨has, hst, hsb⟩
      exact ⟨⟨has, hsb⟩, lt_of_le_of_lt a.coe_nonneg has, hst⟩
  rw [hset, Real.volume_real_Ioc, smul_eq_mul]
  by_cases hat : a ≤ t
  · rw [min_eq_right hat, max_eq_left]
    exact sub_nonneg.mpr (by exact_mod_cast le_min hat hab)
  · have hta : t ≤ a := (lt_of_not_ge hat).le
    rw [min_eq_left hta, min_eq_left (hta.trans hab), sub_self, zero_mul,
      max_eq_right (sub_nonpos.mpr (by exact_mod_cast hta)), zero_mul]

theorem oneStep_time_energy (a b : ℝ≥0) (hab : a < b) (ξ : Ω → ℝ)
    (hξ : StronglyMeasurable[ℱ a] ξ) (hLp : MemLp ξ 2 P) (t : ℝ≥0) (ω : Ω) :
    (∫ s in (0 : ℝ)..(t : ℝ),
      ((Elementary.oneStep a b hab ξ hξ hLp).value s.toNNReal ω) ^ 2) =
      ((min t b : ℝ≥0) - (min t a : ℝ≥0) : ℝ) * ξ ω ^ 2 := by
  simpa only [Elementary.oneStep, Elementary.value_onPartition] using
    segment_time_energy hab.le (ξ ω) t

theorem oneStep_sq_intervalIntegrable (a b : ℝ≥0) (hab : a < b) (ξ : Ω → ℝ)
    (hξ : StronglyMeasurable[ℱ a] ξ) (hLp : MemLp ξ 2 P) (t : ℝ≥0) (ω : Ω) :
    IntervalIntegrable (fun s : ℝ =>
      ((Elementary.oneStep a b hab ξ hξ hLp).value s.toNNReal ω) ^ 2)
      volume 0 (t : ℝ) := by
  simpa only [Elementary.oneStep, Elementary.value_onPartition] using
    segment_sq_intervalIntegrable a b (ξ ω) t

theorem oneStep_time_energy_integrable (a b : ℝ≥0) (hab : a < b) (ξ : Ω → ℝ)
    (hξ : StronglyMeasurable[ℱ a] ξ) (hLp : MemLp ξ 2 P) (t : ℝ≥0) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(t : ℝ),
      ((Elementary.oneStep a b hab ξ hξ hLp).value s.toNNReal ω) ^ 2) P := by
  simp_rw [oneStep_time_energy]
  exact hLp.integrable_sq.const_mul _

theorem oneStep_ito_isometry (hW : IsFilteredPreBrownian W ℱ P)
    (a b : ℝ≥0) (hab : a < b) (ξ : Ω → ℝ)
    (hξ : StronglyMeasurable[ℱ a] ξ) (hLp : MemLp ξ 2 P) (t : ℝ≥0) :
    (∫ ω, ((Elementary.oneStep a b hab ξ hξ hLp).integral W t ω) ^ 2 ∂P) =
      ∫ ω, (∫ s in (0 : ℝ)..(t : ℝ),
        ((Elementary.oneStep a b hab ξ hξ hLp).value s.toNNReal ω) ^ 2) ∂P := by
  simp_rw [oneStep_time_energy]
  rw [integral_const_mul]
  exact integral_oneStep_second_moment hW a b hab ξ hξ hLp t

open Volume4Stage0.BrownianCheck Examples

theorem brownianStep_memLp (t : ℝ≥0) :
    MemLp (brownianStep.integral brownian t) 2 gaussianLimit := by
  have hLp : MemLp (brownian 1) 2 gaussianLimit :=
    (isGaussianProcess_brownian.hasGaussianLaw_eval 1).memLp_two
  convert integral_oneStep_memLp filtered_brownian 1 2 (by norm_num) (brownian 1)
    (filtered_brownian.stronglyAdapted 1) hLp t using 1
  ext ω
  rw [brownianStep_integral, Elementary.integral_oneStep]

theorem brownian_one_second_moment : (∫ ω, (brownian 1 ω) ^ 2 ∂gaussianLimit) = 1 := by
  calc
    _ = ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 := hasLaw_brownian_eval.integral_comp (by fun_prop)
    _ = 1 := gaussian_second_moment 1

theorem brownianStep_second_moment (t : ℝ≥0) :
    (∫ ω, (brownianStep.integral brownian t ω) ^ 2 ∂gaussianLimit) =
      ((min t 2 : ℝ≥0) - (min t 1 : ℝ≥0) : ℝ) := by
  have hLp : MemLp (brownian 1) 2 gaussianLimit :=
    (isGaussianProcess_brownian.hasGaussianLaw_eval 1).memLp_two
  have h := integral_oneStep_second_moment filtered_brownian 1 2 (by norm_num) (brownian 1)
    (filtered_brownian.stronglyAdapted 1) hLp t
  simpa only [Elementary.integral_oneStep, brownianStep_integral,
    brownian_one_second_moment, mul_one] using h

theorem brownianStep_second_moment_at_two :
    (∫ ω, (brownianStep.integral brownian 2 ω) ^ 2 ∂gaussianLimit) = 1 := by
  norm_num [brownianStep_second_moment]

theorem brownianStep_time_energy (t : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    (∫ s in (0 : ℝ)..(t : ℝ), (brownianStep.value s.toNNReal ω) ^ 2) =
      ((min t 2 : ℝ≥0) - (min t 1 : ℝ≥0) : ℝ) * (brownian 1 ω) ^ 2 := by
  simpa only [brownianStep_value, segment] using
    segment_time_energy (by norm_num : (1 : ℝ≥0) ≤ 2) (brownian 1 ω) t

theorem brownianStep_ito_isometry (t : ℝ≥0) :
    (∫ ω, (brownianStep.integral brownian t ω) ^ 2 ∂gaussianLimit) =
      ∫ ω, (∫ s in (0 : ℝ)..(t : ℝ), (brownianStep.value s.toNNReal ω) ^ 2)
        ∂gaussianLimit := by
  simp_rw [brownianStep_time_energy]
  rw [integral_const_mul, brownian_one_second_moment, mul_one,
    brownianStep_second_moment]

end Volume4Elementary.OneStep
