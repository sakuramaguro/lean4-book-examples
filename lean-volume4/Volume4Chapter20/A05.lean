import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter20

theorem affine_transform_is_martingale (a b : ℝ) :
    Martingale (fun n ω => a * process n ω + b) filtration P := by
  simpa only [Pi.add_def, Pi.smul_def, smul_eq_mul] using
    (process_martingale.smul a).add (martingale_const filtration P b)

end Volume4Chapter20
