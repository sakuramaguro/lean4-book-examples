import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Elementary stochastic integrals on deterministic finite partitions

Coefficients are measurable at the left endpoint and belong to L².
The finite sum is defined for every driving process. Brownian properties are
needed later for moment estimates, not for the algebraic refinement identity.
-/

open MeasureTheory
open scoped NNReal BigOperators

namespace Volume4Elementary

structure Partition (a b : ℝ≥0) where
  n : ℕ
  time : Fin (n + 1) → ℝ≥0
  strictMono_time : StrictMono time
  time_zero : time 0 = a
  time_last : time (Fin.last n) = b

namespace Partition

variable {a b : ℝ≥0} (p : Partition a b)

theorem start_le (i : Fin (p.n + 1)) : a ≤ p.time i := by
  simpa only [p.time_zero] using p.strictMono_time.monotone (Fin.zero_le i)

theorem le_end (i : Fin (p.n + 1)) : p.time i ≤ b := by
  simpa only [p.time_last] using p.strictMono_time.monotone (Fin.le_last i)

theorem start_le_end (p : Partition a b) : a ≤ b := by
  simpa only [p.time_last] using p.start_le (Fin.last p.n)

theorem adjacent_lt (i : Fin p.n) : p.time i.castSucc < p.time i.succ :=
  p.strictMono_time Fin.castSucc_lt_succ

def single (a b : ℝ≥0) (hab : a < b) : Partition a b where
  n := 1
  time := ![a, b]
  strictMono_time := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  time_zero := rfl
  time_last := rfl

end Partition

theorem sum_adjacent_sub (n : ℕ) (f : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (f i.succ - f i.castSucc)) = f (Fin.last n) - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    simp_rw [Fin.castSucc_succ]
    rw [ih (fun i => f i.succ)]
    simp only [Fin.succ_last, Fin.castSucc_zero, Fin.succ_zero_eq_one]
    ring

theorem sum_weighted_increments (n : ℕ) (x : ℝ) (f : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, x * (f i.succ - f i.castSucc)) =
      x * (f (Fin.last n) - f 0) := by
  rw [← Finset.mul_sum, sum_adjacent_sub]

noncomputable def segment (a b : ℝ≥0) (x : ℝ) (s : ℝ≥0) : ℝ :=
  if a < s ∧ s ≤ b then x else 0

theorem segment_eq_increment (a b : ℝ≥0) (hab : a ≤ b) (x : ℝ) (s : ℝ≥0) :
    segment a b x s =
      x * ((if s ≤ b then (1 : ℝ) else 0) - (if s ≤ a then 1 else 0)) := by
  by_cases hsa : s ≤ a
  · have hsb : s ≤ b := hsa.trans hab
    simp [segment, hsa, hsb, not_lt.mpr hsa]
  · have has : a < s := lt_of_not_ge hsa
    by_cases hsb : s ≤ b <;> simp [segment, hsa, has, hsb]

theorem sum_segments {a b : ℝ≥0} (p : Partition a b) (x : ℝ) (s : ℝ≥0) :
    (∑ i : Fin p.n, segment (p.time i.castSucc) (p.time i.succ) x s) =
      segment a b x s := by
  calc
    _ = ∑ i : Fin p.n, x *
        ((if s ≤ p.time i.succ then (1 : ℝ) else 0) -
          (if s ≤ p.time i.castSucc then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact segment_eq_increment _ _ (p.adjacent_lt i).le _ _
    _ = x * ((if s ≤ b then 1 else 0) - (if s ≤ a then 1 else 0)) := by
      rw [sum_weighted_increments p.n x (fun i => if s ≤ p.time i then (1 : ℝ) else 0)]
      rw [p.time_last, p.time_zero]
    _ = segment a b x s := (segment_eq_increment a b p.start_le_end x s).symm

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

structure Elementary (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω) (a b : ℝ≥0) where
  partition : Partition a b
  coeff : Fin partition.n → Ω → ℝ
  measurable_coeff : ∀ i, StronglyMeasurable[ℱ (partition.time i.castSucc)] (coeff i)
  memLp_coeff : ∀ i, MemLp (coeff i) 2 P

namespace Elementary

variable {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω} {a b : ℝ≥0}

noncomputable def value (H : Elementary ℱ P a b) (s : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, segment (H.partition.time i.castSucc) (H.partition.time i.succ) (H.coeff i ω) s

noncomputable def integral (H : Elementary ℱ P a b) (W : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, H.coeff i ω *
    (W (min t (H.partition.time i.succ)) ω -
      W (min t (H.partition.time i.castSucc)) ω)

theorem value_stronglyAdapted (H : Elementary ℱ P a b) : StronglyAdapted ℱ H.value := by
  intro s
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  by_cases h : H.partition.time i.castSucc < s ∧ s ≤ H.partition.time i.succ
  · simpa only [segment, if_pos h] using
      (H.measurable_coeff i).mono (ℱ.mono h.1.le)
  · simpa only [segment, if_neg h] using
      (stronglyMeasurable_const : StronglyMeasurable[ℱ s] (fun _ : Ω => (0 : ℝ)))

theorem value_zero (H : Elementary ℱ P a b) (ω : Ω) : H.value 0 ω = 0 := by
  simp [value, segment]

theorem integral_zero_time (H : Elementary ℱ P a b) (W : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    H.integral W 0 ω = 0 := by
  simp [integral]

theorem integral_zero_coeff (H : Elementary ℱ P a b) (W : ℝ≥0 → Ω → ℝ)
    (hc : ∀ i ω, H.coeff i ω = 0) (t : ℝ≥0) (ω : Ω) : H.integral W t ω = 0 := by
  simp [integral, hc]

theorem integral_before_start (H : Elementary ℱ P a b) (W : ℝ≥0 → Ω → ℝ)
    {t : ℝ≥0} (ht : t ≤ a) (ω : Ω) : H.integral W t ω = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hleft := ht.trans (H.partition.start_le i.castSucc)
  have hright := ht.trans (H.partition.start_le i.succ)
  simp [min_eq_left hleft, min_eq_left hright]

/-- A coefficient known at `a` can be reused on all subintervals of `[a,b]`. -/
noncomputable def onPartition (p : Partition a b) (ξ : Ω → ℝ)
    (hξ : StronglyMeasurable[ℱ a] ξ) (hLp : MemLp ξ 2 P) : Elementary ℱ P a b where
  partition := p
  coeff := fun _ => ξ
  measurable_coeff i := hξ.mono (ℱ.mono (p.start_le i.castSucc))
  memLp_coeff _ := hLp

theorem value_onPartition (p : Partition a b) (ξ : Ω → ℝ)
    (hξ : StronglyMeasurable[ℱ a] ξ) (hLp : MemLp ξ 2 P) (s : ℝ≥0) (ω : Ω) :
    (onPartition p ξ hξ hLp).value s ω = segment a b (ξ ω) s :=
  sum_segments p (ξ ω) s

theorem integral_onPartition (p : Partition a b) (ξ : Ω → ℝ)
    (hξ : StronglyMeasurable[ℱ a] ξ) (hLp : MemLp ξ 2 P)
    (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    (onPartition p ξ hξ hLp).integral W t ω =
      ξ ω * (W (min t b) ω - W (min t a) ω) := by
  change (∑ i : Fin p.n, ξ ω *
    (W (min t (p.time i.succ)) ω - W (min t (p.time i.castSucc)) ω)) = _
  rw [sum_weighted_increments p.n (ξ ω) (fun i => W (min t (p.time i)) ω),
    p.time_last, p.time_zero]

/-- Every original interval may be subdivided into an arbitrary finite partition. -/
def Refinement (H : Elementary ℱ P a b) :=
  (i : Fin H.partition.n) →
    Partition (H.partition.time i.castSucc) (H.partition.time i.succ)

noncomputable def refinedBlock (H : Elementary ℱ P a b) (R : H.Refinement)
    (i : Fin H.partition.n) :
    Elementary ℱ P (H.partition.time i.castSucc) (H.partition.time i.succ) :=
  onPartition (R i) (H.coeff i) (H.measurable_coeff i) (H.memLp_coeff i)

noncomputable def refinedValue (H : Elementary ℱ P a b) (R : H.Refinement)
    (s : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, (H.refinedBlock R i).value s ω

noncomputable def refinedIntegral (H : Elementary ℱ P a b) (R : H.Refinement)
    (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, (H.refinedBlock R i).integral W t ω

theorem refinement_preserves_value (H : Elementary ℱ P a b) (R : H.Refinement)
    (s : ℝ≥0) (ω : Ω) : H.refinedValue R s ω = H.value s ω := by
  apply Finset.sum_congr rfl
  intro i _
  exact value_onPartition _ _ _ _ _ _

theorem refinement_preserves_integral (H : Elementary ℱ P a b) (R : H.Refinement)
    (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    H.refinedIntegral R W t ω = H.integral W t ω := by
  apply Finset.sum_congr rfl
  intro i _
  exact integral_onPartition _ _ _ _ _ _ _

noncomputable def oneStep (a b : ℝ≥0) (hab : a < b) (ξ : Ω → ℝ)
    (hξ : StronglyMeasurable[ℱ a] ξ) (hLp : MemLp ξ 2 P) : Elementary ℱ P a b :=
  onPartition (Partition.single a b hab) ξ hξ hLp

theorem integral_oneStep (a b : ℝ≥0) (hab : a < b) (ξ : Ω → ℝ)
    (hξ : StronglyMeasurable[ℱ a] ξ) (hLp : MemLp ξ 2 P)
    (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    (oneStep a b hab ξ hξ hLp).integral W t ω =
      ξ ω * (W (min t b) ω - W (min t a) ω) :=
  integral_onPartition _ _ _ _ _ _ _

noncomputable def constant [IsFiniteMeasure P] (T : ℝ≥0) (hT : 0 < T) (σ : ℝ) :
    Elementary ℱ P 0 T :=
  oneStep 0 T hT (fun _ => σ) stronglyMeasurable_const (memLp_const σ)

theorem integral_constant [IsFiniteMeasure P] (T : ℝ≥0) (hT : 0 < T) (σ : ℝ)
    (W : ℝ≥0 → Ω → ℝ) {t : ℝ≥0} (ht : t ≤ T) (ω : Ω) :
    (constant (ℱ := ℱ) (P := P) T hT σ).integral W t ω =
      σ * (W t ω - W 0 ω) := by
  rw [constant, integral_oneStep]
  simp [min_eq_left ht]

end Elementary
end Volume4Elementary
