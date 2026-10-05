import Volume4Stage0.BrownianCheck
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter22

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ}

theorem martingale_from_filtered_brownian [IsProbabilityMeasure P]
    (hW : IsFilteredPreBrownian W ℱ P) : Martingale W ℱ P := by
  letI := hW
  exact IsPreBrownianReal.isMartingale W ℱ P

end Volume4Chapter22
