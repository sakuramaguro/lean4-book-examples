import Volume4Elementary.ConstantSDEExamples

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Volume4Elementary
open Volume4Elementary.ConstantSDE
open Volume4Stage0.BrownianCheck

namespace Volume4Chapter24

#print Volume4Elementary.ConstantSDE.IsSolution
set_option pp.explicit true in
#check Volume4Elementary.ConstantSDE.IsSolution.measurable_at
set_option pp.explicit true in
#check Volume4Elementary.ConstantSDE.IsSolution.continuous_paths
#check Volume4Elementary.ConstantSDE.candidate_isSolution
#check Volume4Elementary.ConstantSDE.exists_solution_unique_on_interval

end Volume4Chapter24
