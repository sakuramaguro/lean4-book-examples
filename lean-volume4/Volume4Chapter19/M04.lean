import Volume4Stage0.FourPoint
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Volume4Stage0.FourPoint

namespace Volume4Chapter19

theorem first_coordinate_is_known :
    firstInfo ≤ (inferInstance : MeasurableSpace Ω) ∧
      StronglyMeasurable[firstInfo] ξ₁ := by
  constructor
  · exact measurable_fst.comap_le
  · have hfst : @Measurable Ω Bool firstInfo _ Prod.fst :=
      measurable_iff_comap_le.mpr le_rfl
    exact ((measurable_of_finite sign).comp hfst).stronglyMeasurable

end Volume4Chapter19
