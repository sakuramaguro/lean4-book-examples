import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter20

theorem square_process_adapted_not_martingale :
    StronglyAdapted filtration (fun n ω => (process n ω) ^ 2) ∧
      ¬ Martingale (fun n ω => (process n ω) ^ 2) filtration P := by
  constructor
  · intro n
    simpa only [pow_two, Pi.mul_def] using
      (process_stronglyAdapted n).mul (process_stronglyAdapted n)
  · intro h
    have heq := h.setIntegral_eq (by decide : (1 : Fin 3) ≤ 2)
      (s := Set.univ) MeasurableSet.univ
    simp only [MeasureTheory.setIntegral_univ] at heq
    norm_num [process, P, PMF.integral_eq_sum, PMF.uniformOfFintype_apply,
      Fintype.sum_prod_type, terminal, ξ₁, ξ₂, sign] at heq

end Volume4Chapter20
