import Volume4Stage0.BrownianCheck
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter22

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ}

theorem increment_law_and_L2
    (hW : IsFilteredPreBrownian W ℱ P) (s t : ℝ≥0) :
    HasLaw (W t - W s) (gaussianReal 0 (nndist (t : ℝ) (s : ℝ))) P ∧
    MemLp (W t - W s) 2 P :=
  ⟨hW.toIsPreBrownianReal.hasLaw_sub t s,
    (hW.toIsPreBrownianReal.hasLaw_sub t s).hasGaussianLaw.memLp_two⟩

end Volume4Chapter22
