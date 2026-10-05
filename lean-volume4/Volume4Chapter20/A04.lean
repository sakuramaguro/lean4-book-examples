import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter20

theorem last_increment_formula_and_forecast :
    process 2 - process 1 = (fun ω => 2 * ξ₂ ω) ∧
      P[process 2 - process 1 | filtration 1] =ᵐ[P] (fun _ => (0 : ℝ)) := by
  constructor
  · funext ω
    norm_num [process, terminal]
  · filter_upwards [condExp_sub (process_integrable 2) (process_integrable 1) (filtration 1),
      process_martingale.condExp_ae_eq (by decide : (1 : Fin 3) ≤ 2),
      process_martingale.condExp_ae_eq (le_refl (1 : Fin 3))] with ω hsub hj hi
    simpa only [Pi.sub_apply, hj, hi, sub_self] using hsub

end Volume4Chapter20
