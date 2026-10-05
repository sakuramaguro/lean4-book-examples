import BrownianMotion.Gaussian.BrownianMotion

/-!
# The Brownian-motion interface needed by Volume 4

This file connects a constructed Brownian motion to its natural filtration.
It does not construct a stochastic integral or solve an SDE.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Volume4Stage0.BrownianCheck

noncomputable def naturalFiltration :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)) :=
  Filtration.natural brownian (fun t => (measurable_brownian t).stronglyMeasurable)

theorem constructed_brownian : IsBrownianReal brownian gaussianLimit :=
  isBrownianReal_brownian

theorem filtered_brownian :
    IsFilteredPreBrownian brownian naturalFiltration gaussianLimit :=
  isBrownianReal_brownian.toIsPreBrownianReal.isFilteredPreBrownian measurable_brownian

theorem brownian_martingale : Martingale brownian naturalFiltration gaussianLimit := by
  letI := filtered_brownian
  exact IsPreBrownianReal.isMartingale brownian naturalFiltration gaussianLimit

theorem brownian_zero : brownian 0 =ᵐ[gaussianLimit] (fun _ => (0 : ℝ)) :=
  isBrownianReal_brownian.toIsPreBrownianReal.eval_zero_ae_eq_zero

theorem brownian_path_continuous (ω : ℝ≥0 → ℝ) :
    Continuous (fun t => brownian t ω) :=
  continuous_brownian ω

theorem brownian_increment_law (s t : ℝ≥0) :
    HasLaw (brownian t - brownian s) (gaussianReal 0 (nndist t s)) gaussianLimit :=
  hasLaw_brownian_sub

theorem brownian_increment_independent_of_past (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (brownian t - brownian s) inferInstance)
      (naturalFiltration s) gaussianLimit :=
  filtered_brownian.indep s t hst

/-- Use the closed time interval as the index type. The modification theorem
then applies to the whole index type and does not require an open interval. -/
theorem indistinguishable_on_closed_interval
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (T : ℝ≥0)
    (X Y : Set.Icc (0 : ℝ≥0) T → Ω → ℝ)
    (hX : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (h : ∀ t, X t =ᵐ[P] Y t) :
    ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  exact indistinguishable_of_modification hX hY h

end Volume4Stage0.BrownianCheck
