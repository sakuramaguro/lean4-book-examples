import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Volume4Chapter21

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {X Y : Ω → ℝ}

theorem gaussian_three_four [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 3 4) P) :
    (∫ ω, X ω ∂P) = 3 ∧ Var[X; P] = 4 ∧
      (∫ ω, (X ω) ^ 2 ∂P) = 13 := by
  have hmean : (∫ ω, X ω ∂P) = 3 :=
    hX.integral_eq.trans integral_id_gaussianReal
  have hvar : Var[X; P] = (4 : ℝ≥0) :=
    hX.variance_eq.trans variance_id_gaussianReal
  refine ⟨hmean, hvar, ?_⟩
  have hs := variance_eq_sub hX.hasGaussianLaw.memLp_two
  rw [hvar, hmean] at hs
  have hmoment := eq_add_of_sub_eq hs.symm
  norm_num at hmoment ⊢
  exact hmoment

end Volume4Chapter21
