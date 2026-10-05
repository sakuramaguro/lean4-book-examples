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

theorem gaussian_moments [IsProbabilityMeasure P] {m : ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal m v) P) :
    MemLp X 2 P ∧
      (∫ ω, X ω ∂P) = m ∧ Var[X; P] = (v : ℝ) ∧
      (∫ ω, (X ω) ^ 2 ∂P) = (v : ℝ) + m ^ 2 := by
  have hL : MemLp X 2 P := hX.hasGaussianLaw.memLp_two
  have hmean : (∫ ω, X ω ∂P) = m :=
    hX.integral_eq.trans integral_id_gaussianReal
  have hvar : Var[X; P] = (v : ℝ) :=
    hX.variance_eq.trans variance_id_gaussianReal
  refine ⟨hL, hmean, hvar, ?_⟩
  have hs := variance_eq_sub hL
  rw [hvar, hmean] at hs
  exact eq_add_of_sub_eq hs.symm

end Volume4Chapter21
