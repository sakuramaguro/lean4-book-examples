import Volume4Stage0.BrownianCheck
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter22

noncomputable def diagonal (t ω : ℝ) : ℝ := by
  classical
  exact if ω = t then 1 else 0

theorem diagonal_zero_at_fixed_time (t : ℝ) :
    diagonal t =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] (fun _ => (0 : ℝ)) := by
  change ∀ᵐ ω ∂volume.restrict (Set.Icc (0 : ℝ) 1), diagonal t ω = 0
  apply ae_iff.mpr
  have hset : {ω | ¬ diagonal t ω = 0} = {t} := by
    ext ω
    simp [diagonal]
  rw [hset]
  simp

theorem diagonal_no_zero_path {ω : ℝ} (hω : ω ∈ Set.Icc (0 : ℝ) 1) :
    ¬ ∀ t ∈ Set.Icc (0 : ℝ) 1, diagonal t ω = 0 := by
  intro h
  have hdiag := h ω hω
  norm_num [diagonal] at hdiag

theorem diagonal_not_indistinguishable :
    ¬ ∀ᵐ ω ∂volume.restrict (Set.Icc (0 : ℝ) 1),
      ∀ t ∈ Set.Icc (0 : ℝ) 1, diagonal t ω = 0 := by
  intro h
  have hfalse : ∀ᵐ ω ∂volume.restrict (Set.Icc (0 : ℝ) 1), False := by
    filter_upwards [h, ae_restrict_mem measurableSet_Icc] with ω hpath hω
    exact diagonal_no_zero_path hω hpath
  have hzero := ae_iff.mp hfalse
  norm_num at hzero

end Volume4Chapter22
