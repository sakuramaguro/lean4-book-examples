import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# A four-point conditional-expectation example for Chapters 19 and 20

Each point has probability 1/4. `false` represents -1 and `true` represents +1.
The intermediate information reveals the first coordinate only.
All displayed conditional expectations use Mathlib's `condExp`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Volume4Stage0.FourPoint

abbrev Ω := Bool × Bool

noncomputable def P : Measure Ω := (PMF.uniformOfFintype Ω).toMeasure

instance : IsProbabilityMeasure P := by
  unfold P
  infer_instance

def sign (b : Bool) : ℝ := if b then 1 else -1
def ξ₁ (ω : Ω) : ℝ := sign ω.1
def ξ₂ (ω : Ω) : ℝ := sign ω.2
def terminal (ω : Ω) : ℝ := ξ₁ ω + 2 * ξ₂ ω

theorem point_mass (ω : Ω) : P {ω} = (1 / 4 : ℝ≥0∞) := by
  simp [P, PMF.uniformOfFintype_apply]

theorem terminal_values :
    terminal (false, false) = -3 ∧ terminal (false, true) = 1 ∧
    terminal (true, false) = -1 ∧ terminal (true, true) = 3 := by
  norm_num [terminal, ξ₁, ξ₂, sign]

theorem integrable_terminal : Integrable terminal P := Integrable.of_finite
theorem integrable_first : Integrable ξ₁ P := Integrable.of_finite

theorem expectation_terminal : (∫ ω, terminal ω ∂P) = 0 := by
  norm_num [P, PMF.integral_eq_sum, PMF.uniformOfFintype_apply,
    Fintype.sum_prod_type, terminal, ξ₁, ξ₂, sign]

theorem expectation_first : (∫ ω, ξ₁ ω ∂P) = 0 := by
  norm_num [P, PMF.integral_eq_sum, PMF.uniformOfFintype_apply,
    Fintype.sum_prod_type, ξ₁, sign]

@[implicit_reducible] def firstInfo : MeasurableSpace Ω :=
  MeasurableSpace.comap Prod.fst inferInstance

theorem firstInfo_le : firstInfo ≤ (inferInstance : MeasurableSpace Ω) :=
  measurable_fst.comap_le

theorem first_stronglyMeasurable : StronglyMeasurable[firstInfo] ξ₁ := by
  have hfst : @Measurable Ω Bool firstInfo _ Prod.fst :=
    measurable_iff_comap_le.mpr le_rfl
  exact ((measurable_of_finite sign).comp hfst).stronglyMeasurable

theorem condExp_terminal_first : P[terminal | firstInfo] =ᵐ[P] ξ₁ := by
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq firstInfo_le integrable_terminal
  · intro s _ _
    exact integrable_first.integrableOn
  · intro s hs _
    obtain ⟨u, hu, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    rw [← integral_indicator (measurable_fst hu),
      ← integral_indicator (measurable_fst hu)]
    classical
    by_cases hfalse : false ∈ u <;> by_cases htrue : true ∈ u <;>
      norm_num [P, PMF.integral_eq_sum, PMF.uniformOfFintype_apply,
        Fintype.sum_prod_type, terminal, ξ₁, ξ₂, sign, Set.indicator,
        hfalse, htrue]
  · exact first_stronglyMeasurable.aestronglyMeasurable

theorem condExp_terminal_bot : P[terminal | ⊥] = fun _ => (0 : ℝ) := by
  rw [condExp_bot, expectation_terminal]

theorem condExp_first_bot : P[ξ₁ | ⊥] = fun _ => (0 : ℝ) := by
  rw [condExp_bot, expectation_first]

theorem condExp_terminal_full :
    P[terminal | (inferInstance : MeasurableSpace Ω)] = terminal :=
  condExp_of_stronglyMeasurable le_rfl
    (measurable_of_finite terminal).stronglyMeasurable integrable_terminal

theorem tower_first_bot :
    P[P[terminal | firstInfo] | ⊥] =ᵐ[P] P[terminal | ⊥] := by
  exact condExp_condExp_of_le bot_le firstInfo_le

@[implicit_reducible] def information (n : Fin 3) : MeasurableSpace Ω :=
  if n.val = 0 then ⊥ else if n.val = 1 then firstInfo else inferInstance

def filtration : Filtration (Fin 3) (inferInstance : MeasurableSpace Ω) where
  seq := information
  mono' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [information, firstInfo_le]
  le' := by
    intro i
    fin_cases i <;> simp [information, firstInfo_le]

def process (n : Fin 3) : Ω → ℝ :=
  if n.val = 0 then fun _ => 0 else if n.val = 1 then ξ₁ else terminal

theorem process_values : process 0 = (fun _ => 0) ∧
    process 1 = ξ₁ ∧ process 2 = terminal := by
  norm_num [process]

theorem process_stronglyAdapted : StronglyAdapted filtration process := by
  intro n
  fin_cases n
  · change StronglyMeasurable[⊥] (fun _ : Ω => (0 : ℝ))
    exact stronglyMeasurable_const
  · change StronglyMeasurable[firstInfo] ξ₁
    exact first_stronglyMeasurable
  · change StronglyMeasurable terminal
    exact (measurable_of_finite terminal).stronglyMeasurable

theorem process_integrable (n : Fin 3) : Integrable (process n) P :=
  Integrable.of_finite

theorem process_eq_condExp (n : Fin 3) :
    process n =ᵐ[P] P[terminal | filtration n] := by
  fin_cases n
  · change (fun _ : Ω => (0 : ℝ)) =ᵐ[P] P[terminal | ⊥]
    rw [condExp_terminal_bot]
  · change ξ₁ =ᵐ[P] P[terminal | firstInfo]
    exact condExp_terminal_first.symm
  · change terminal =ᵐ[P] P[terminal | (inferInstance : MeasurableSpace Ω)]
    rw [condExp_terminal_full]

theorem process_martingale : Martingale process filtration P := by
  refine ⟨process_stronglyAdapted, ?_⟩
  intro i j hij
  calc
    P[process j | filtration i] =ᵐ[P]
        P[P[terminal | filtration j] | filtration i] :=
      condExp_congr_ae (process_eq_condExp j)
    _ =ᵐ[P] P[terminal | filtration i] :=
      condExp_condExp_of_le (filtration.mono hij) (filtration.le j)
    _ =ᵐ[P] process i := (process_eq_condExp i).symm

theorem one_step_condExp : P[process 2 | filtration 1] =ᵐ[P] process 1 :=
  process_martingale.condExp_ae_eq (by decide : (1 : Fin 3) ≤ 2)

theorem terminal_second_moment : (∫ ω, (terminal ω) ^ 2 ∂P) = 5 := by
  norm_num [P, PMF.integral_eq_sum, PMF.uniformOfFintype_apply,
    Fintype.sum_prod_type, terminal, ξ₁, ξ₂, sign]

end Volume4Stage0.FourPoint
