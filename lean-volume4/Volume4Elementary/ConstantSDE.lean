import Volume4Elementary.Examples
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Constant-coefficient SDEs on a finite closed time interval

A solution is defined by adaptation, continuous paths, an initial value,
and a stochastic integral equation. The explicit formula is a proved solution.
Uniqueness is indistinguishability on [0,T], not equality of process functions.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Volume4Elementary.ConstantSDE

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W X Y : ℝ≥0 → Ω → ℝ}

noncomputable def candidate (W : ℝ≥0 → Ω → ℝ) (x₀ drift diffusion : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  x₀ + drift * (t : ℝ) + diffusion * W t ω

/-- Only times at most T are constrained. Each integral equation has its own
a.e. quantifier; simultaneous equality is proved later using continuity. -/
structure IsSolution [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (hT : 0 < T) (x₀ drift diffusion : ℝ) (X : ℝ≥0 → Ω → ℝ) : Prop where
  measurable_at : ∀ t, t ≤ T → Measurable[ℱ t] (X t)
  continuous_paths : ∀ᵐ ω ∂P,
    Continuous (fun t : Set.Icc (0 : ℝ≥0) T => X t ω)
  initial : X 0 =ᵐ[P] (fun _ => x₀)
  integral_eq : ∀ t, t ≤ T → X t =ᵐ[P] (fun ω =>
    x₀ + (∫ _s in (0 : ℝ)..(t : ℝ), drift) +
      (Elementary.constant (ℱ := ℱ) (P := P) T hT diffusion).integral W t ω)

theorem drift_intervalIntegrable (drift : ℝ) (t : ℝ≥0) :
    IntervalIntegrable (fun _s : ℝ => drift) volume 0 (t : ℝ) :=
  intervalIntegrable_const

theorem drift_integral (drift : ℝ) (t : ℝ≥0) :
    (∫ _s in (0 : ℝ)..(t : ℝ), drift) = drift * (t : ℝ) := by
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul, mul_comm]

theorem candidate_stronglyAdapted (hW : StronglyAdapted ℱ W) (x₀ drift diffusion : ℝ) :
    StronglyAdapted ℱ (candidate W x₀ drift diffusion) := by
  intro t
  exact (stronglyMeasurable_const.add stronglyMeasurable_const).add
    (stronglyMeasurable_const.mul (hW t))

theorem candidate_continuous (x₀ drift diffusion : ℝ) (ω : Ω)
    (hW : Continuous (fun t => W t ω)) :
    Continuous (fun t => candidate W x₀ drift diffusion t ω) := by
  unfold candidate
  fun_prop

theorem candidate_continuous_paths (x₀ drift diffusion : ℝ) (T : ℝ≥0)
    (hW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω)) :
    ∀ᵐ ω ∂P, Continuous (fun t : Set.Icc (0 : ℝ≥0) T =>
      candidate W x₀ drift diffusion t ω) := by
  filter_upwards [hW] with ω hω
  exact (candidate_continuous x₀ drift diffusion ω hω).comp continuous_subtype_val

theorem candidate_initial (x₀ drift diffusion : ℝ)
    (hW : W 0 =ᵐ[P] (fun _ => (0 : ℝ))) :
    candidate W x₀ drift diffusion 0 =ᵐ[P] (fun _ => x₀) := by
  filter_upwards [hW] with ω hω
  simp only [candidate, NNReal.coe_zero, mul_zero, add_zero, hω]

theorem candidate_integral_equation [IsProbabilityMeasure P]
    (T : ℝ≥0) (hT : 0 < T) (x₀ drift diffusion : ℝ)
    (hW : W 0 =ᵐ[P] (fun _ => (0 : ℝ))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      candidate W x₀ drift diffusion t ω =
        x₀ + (∫ _s in (0 : ℝ)..(t : ℝ), drift) +
          (Elementary.constant (ℱ := ℱ) (P := P) T hT diffusion).integral W t ω := by
  filter_upwards [hW] with ω hω
  intro t ht
  rw [drift_integral, Elementary.integral_constant T hT diffusion W ht ω, hω, sub_zero]
  rfl

theorem candidate_isSolution [IsProbabilityMeasure P]
    (hW : IsFilteredPreBrownian W ℱ P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => W t ω))
    (T : ℝ≥0) (hT : 0 < T) (x₀ drift diffusion : ℝ) :
    IsSolution (ℱ := ℱ) (P := P) W T hT x₀ drift diffusion
      (candidate W x₀ drift diffusion) where
  measurable_at t _ := (candidate_stronglyAdapted hW.stronglyAdapted x₀ drift diffusion t).measurable
  continuous_paths := candidate_continuous_paths x₀ drift diffusion T hcont
  initial := candidate_initial x₀ drift diffusion hW.eval_zero_ae_eq_zero
  integral_eq t ht :=
    (candidate_integral_equation (ℱ := ℱ) T hT x₀ drift diffusion hW.eval_zero_ae_eq_zero).mono
      (fun _ hω => hω t ht)

theorem IsSolution.ae_eq_at [IsProbabilityMeasure P]
    {T : ℝ≥0} {hT : 0 < T} {x₀ drift diffusion : ℝ}
    (hX : IsSolution (ℱ := ℱ) (P := P) W T hT x₀ drift diffusion X)
    (hY : IsSolution (ℱ := ℱ) (P := P) W T hT x₀ drift diffusion Y)
    {t : ℝ≥0} (ht : t ≤ T) : X t =ᵐ[P] Y t :=
  (hX.integral_eq t ht).trans (hY.integral_eq t ht).symm

theorem IsSolution.indistinguishable [IsProbabilityMeasure P]
    {T : ℝ≥0} {hT : 0 < T} {x₀ drift diffusion : ℝ}
    (hX : IsSolution (ℱ := ℱ) (P := P) W T hT x₀ drift diffusion X)
    (hY : IsSolution (ℱ := ℱ) (P := P) W T hT x₀ drift diffusion Y) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T → X t ω = Y t ω := by
  have h := Volume4Stage0.BrownianCheck.indistinguishable_on_closed_interval T
    (fun t : Set.Icc (0 : ℝ≥0) T => X t)
    (fun t : Set.Icc (0 : ℝ≥0) T => Y t)
    hX.continuous_paths hY.continuous_paths (fun t => hX.ae_eq_at hY t.property.2)
  filter_upwards [h] with ω hω
  intro t ht
  exact hω ⟨t, bot_le, ht⟩

theorem IsSolution.eq_candidate [IsProbabilityMeasure P]
    (hW : IsFilteredPreBrownian W ℱ P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => W t ω))
    {T : ℝ≥0} {hT : 0 < T} {x₀ drift diffusion : ℝ}
    (hX : IsSolution (ℱ := ℱ) (P := P) W T hT x₀ drift diffusion X) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T → X t ω = x₀ + drift * (t : ℝ) + diffusion * W t ω :=
  hX.indistinguishable (candidate_isSolution hW hcont T hT x₀ drift diffusion)

theorem IsSolution.integral_eq_simultaneously [IsProbabilityMeasure P]
    (hW : IsFilteredPreBrownian W ℱ P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => W t ω))
    {T : ℝ≥0} {hT : 0 < T} {x₀ drift diffusion : ℝ}
    (hX : IsSolution (ℱ := ℱ) (P := P) W T hT x₀ drift diffusion X) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T → X t ω =
      x₀ + (∫ _s in (0 : ℝ)..(t : ℝ), drift) +
        (Elementary.constant (ℱ := ℱ) (P := P) T hT diffusion).integral W t ω := by
  have heq := hX.indistinguishable (candidate_isSolution hW hcont T hT x₀ drift diffusion)
  have hcand := candidate_integral_equation (ℱ := ℱ) T hT x₀ drift diffusion
    hW.eval_zero_ae_eq_zero
  filter_upwards [heq, hcand] with ω hω hcω
  intro t ht
  exact (hω t ht).trans (hcω t ht)

theorem exists_solution_unique_on_interval [IsProbabilityMeasure P]
    (hW : IsFilteredPreBrownian W ℱ P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => W t ω))
    (T : ℝ≥0) (hT : 0 < T) (x₀ drift diffusion : ℝ) :
    ∃ X : ℝ≥0 → Ω → ℝ,
      IsSolution (ℱ := ℱ) (P := P) W T hT x₀ drift diffusion X ∧
      ∀ Y : ℝ≥0 → Ω → ℝ,
        IsSolution (ℱ := ℱ) (P := P) W T hT x₀ drift diffusion Y →
          ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T → Y t ω = X t ω := by
  have hX := candidate_isSolution hW hcont T hT x₀ drift diffusion
  exact ⟨candidate W x₀ drift diffusion, hX, fun _ hY => hY.indistinguishable hX⟩

end Volume4Elementary.ConstantSDE
