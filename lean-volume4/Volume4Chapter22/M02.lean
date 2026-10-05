import Volume4Stage0.BrownianCheck
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter22

theorem constructed_interface :
    IsFilteredPreBrownian brownian naturalFiltration gaussianLimit ∧
    (brownian 0 =ᵐ[gaussianLimit] (fun _ => (0 : ℝ))) ∧
    ∀ ω : ℝ≥0 → ℝ, Continuous (fun t => brownian t ω) :=
  ⟨filtered_brownian, brownian_zero, brownian_path_continuous⟩

end Volume4Chapter22
