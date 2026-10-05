import Volume4Stage0.BrownianCheck
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter22

theorem continuous_modifications_on_horizon
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (T : ℝ≥0) (X Y : ℝ≥0 → Ω → ℝ)
    (hX : ∀ᵐ ω ∂P,
      Continuous (fun t : Set.Icc (0 : ℝ≥0) T => X t ω))
    (hY : ∀ᵐ ω ∂P,
      Continuous (fun t : Set.Icc (0 : ℝ≥0) T => Y t ω))
    (h : ∀ t, t ≤ T → X t =ᵐ[P] Y t) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T → X t ω = Y t ω := by
  have hI := indistinguishable_on_closed_interval T
    (fun t => X t) (fun t => Y t) hX hY (fun t => h t t.property.2)
  filter_upwards [hI] with ω hω
  intro t ht
  exact hω ⟨t, bot_le, ht⟩

end Volume4Chapter22
