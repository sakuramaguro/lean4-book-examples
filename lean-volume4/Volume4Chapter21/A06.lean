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

theorem centered_gaussian_product [IsProbabilityMeasure P]
    (hind : IndepFun X Y P)
    (hX : HasLaw X (gaussianReal 0 2) P)
    (hY : HasLaw Y (gaussianReal 0 3) P) :
    (∫ ω, (X ω * Y ω) ^ 2 ∂P) = 6 := by
  have hmoment (Z : Ω → ℝ) (v : ℝ≥0)
      (hZ : HasLaw Z (gaussianReal 0 v) P) :
      (∫ ω, (Z ω) ^ 2 ∂P) = (v : ℝ) := by
    have hm : (∫ ω, Z ω ∂P) = 0 :=
      hZ.integral_eq.trans integral_id_gaussianReal
    have hv : Var[Z; P] = (v : ℝ) :=
      hZ.variance_eq.trans variance_id_gaussianReal
    have hs := variance_eq_sub hZ.hasGaussianLaw.memLp_two
    rw [hv, hm] at hs
    have h := eq_add_of_sub_eq hs.symm
    simpa only [Pi.pow_apply, zero_pow (by decide : 2 ≠ 0), add_zero] using h
  have hsq : IndepFun (fun ω => (X ω) ^ 2) (fun ω => (Y ω) ^ 2) P :=
    hind.comp (by fun_prop : Measurable (fun x : ℝ => x ^ 2))
      (by fun_prop : Measurable (fun x : ℝ => x ^ 2))
  have hfactor := hsq.integral_fun_mul_eq_mul_integral
    hX.hasGaussianLaw.memLp_two.integrable_sq.aestronglyMeasurable
    hY.hasGaussianLaw.memLp_two.integrable_sq.aestronglyMeasurable
  rw [hmoment X 2 hX, hmoment Y 3 hY] at hfactor
  norm_num at hfactor
  simpa only [mul_pow] using hfactor

end Volume4Chapter21
