import Volume4Stage0.BrownianCheck
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter22

theorem equality_on_observation_sequence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (T : ℝ≥0) (X Y : ℝ≥0 → Ω → ℝ) (times : ℕ → ℝ≥0)
    (htimes : ∀ n, times n ≤ T)
    (h : ∀ t, t ≤ T → X t =ᵐ[P] Y t) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, X (times n) ω = Y (times n) ω :=
  ae_all_iff.2 (fun n => h (times n) (htimes n))

end Volume4Chapter22
