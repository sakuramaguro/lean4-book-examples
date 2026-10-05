import Volume4Stage0.BrownianCheck
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter22

theorem continuous_version_of_brownian
    (T : ℝ≥0) (Y : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hY : ∀ᵐ ω ∂gaussianLimit,
      Continuous (fun t : Set.Icc (0 : ℝ≥0) T => Y t ω))
    (heq : ∀ t, t ≤ T → Y t =ᵐ[gaussianLimit] brownian t) :
    ∀ᵐ ω ∂gaussianLimit, ∀ t : ℝ≥0, t ≤ T → Y t ω = brownian t ω := by
  have hB : ∀ᵐ ω ∂gaussianLimit,
      Continuous (fun t : Set.Icc (0 : ℝ≥0) T => brownian t ω) :=
    Filter.Eventually.of_forall (fun ω =>
      (brownian_path_continuous ω).comp continuous_subtype_val)
  have hI := indistinguishable_on_closed_interval T
    (fun t => Y t) (fun t => brownian t) hY hB (fun t => heq t t.property.2)
  filter_upwards [hI] with ω hω
  intro t ht
  exact hω ⟨t, bot_le, ht⟩

end Volume4Chapter22
