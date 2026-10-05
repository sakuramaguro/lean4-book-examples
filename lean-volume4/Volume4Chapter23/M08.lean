import Volume4Elementary.FiniteSumExamples

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open Volume4Elementary
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter23

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {a b : ℝ≥0}

theorem finite_sum_L2_and_isometry [IsProbabilityMeasure P]
    (hW : IsFilteredPreBrownian W ℱ P)
    (H : Elementary ℱ P a b) (t : ℝ≥0) :
    MemLp (H.integral W t) 2 P ∧
      (∫ ω, (H.integral W t ω) ^ 2 ∂P) =
        ∫ ω, (∫ s in (0 : ℝ)..(t : ℝ),
          (H.value s.toNNReal ω) ^ 2) ∂P := by
  refine ⟨FiniteSum.integral_memLp hW H t, ?_⟩
  simp_rw [FiniteSum.time_energy]
  rw [integral_finsetSum _
    (fun i _ => (H.memLp_coeff i).integrable_sq.const_mul _)]
  simp_rw [integral_const_mul]
  exact FiniteSum.integral_second_moment hW H t

end Volume4Chapter23
