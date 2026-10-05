import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter20

theorem adapted_and_integrable :
    StronglyAdapted filtration process ∧ ∀ n, Integrable (process n) P := by
  constructor
  · intro n
    fin_cases n
    · change StronglyMeasurable[⊥] (fun _ : Ω => (0 : ℝ))
      exact stronglyMeasurable_const
    · change StronglyMeasurable[firstInfo] ξ₁
      exact first_stronglyMeasurable
    · change StronglyMeasurable terminal
      exact (measurable_of_finite terminal).stronglyMeasurable
  · intro n
    exact Integrable.of_finite

end Volume4Chapter20
