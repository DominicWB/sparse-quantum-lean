import QLSHoeffding.Hoeffding
import QLSHoeffding.Estimator
import QLSHoeffding.Schedule
import QLSHoeffding.Algorithm
import QLSHoeffding.Cost
import QLSHoeffding.Main
import QLSHoeffding.Constants

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`. The audits cover every theorem of the
library, beginning with the final theorems. -/

/-! ### Final theorems: the repetition count of `qls:eq:hoeffding` -/

/-- info: 'QLSHoeffding.main_ampH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.main_ampH

/-- info: 'QLSHoeffding.mainH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.mainH

/-- info: 'QLSHoeffding.main_exactH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.main_exactH

/-- info: 'QLSHoeffding.main_exactH_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.main_exactH_exists

/-! ### Hoeffding's inequality for the binomial law -/

/-- info: 'QLSHoeffding.base_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.base_pos

/-- info: 'QLSHoeffding.hasDerivAt_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.hasDerivAt_base

/-- info: 'QLSHoeffding.hasDerivAt_tilt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.hasDerivAt_tilt

/-- info: 'QLSHoeffding.tilt_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.tilt_mul_le

/-- info: 'QLSHoeffding.tilt_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.tilt_zero

/-- info: 'QLSHoeffding.hasDerivAt_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.hasDerivAt_slope

/-- info: 'QLSHoeffding.slope_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.slope_monotone

/-- info: 'QLSHoeffding.slope_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.slope_zero

/-- info: 'QLSHoeffding.hasDerivAt_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.hasDerivAt_gap

/-- info: 'QLSHoeffding.gap_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.gap_zero

/-- info: 'QLSHoeffding.gap_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.gap_nonneg

/-- info: 'QLSHoeffding.log_mgf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.log_mgf_le

/-- info: 'QLSHoeffding.mgf_base_le_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.mgf_base_le_sharp

/-- info: 'QLSHoeffding.mgf_le_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.mgf_le_sharp

/-- info: 'QLSHoeffding.upper_tail_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.upper_tail_sharp

/-- info: 'QLSHoeffding.lower_tail_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.lower_tail_sharp

/-- info: 'QLSHoeffding.two_sided_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.two_sided_sharp

/-- info: 'QLSHoeffding.two_sided_le_of_count_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.two_sided_le_of_count_sharp

/-! ### The estimator with a tail budget -/

/-- info: 'QLSHoeffding.tailOK_hoeffding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.tailOK_hoeffding

/-- info: 'QLSHoeffding.tailOK_released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.tailOK_released

/-- info: 'QLSHoeffding.count_step_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.count_step_tail

/-- info: 'QLSHoeffding.candidates_le_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.candidates_le_tail

/-- info: 'QLSHoeffding.stages_le_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.stages_le_tail

/-- info: 'QLSHoeffding.algorithm_bad_le_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.algorithm_bad_le_tail

/-! ### The repetition schedule -/

/-- info: 'QLSHoeffding.zeta_eq_zetaMs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.zeta_eq_zetaMs

/-- info: 'QLSHoeffding.repsH_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.repsH_spec

/-- info: 'QLSHoeffding.repsH_eq_ms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.repsH_eq_ms

/-- info: 'QLSHoeffding.repsH_tailOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.repsH_tailOK

/-- info: 'QLSHoeffding.repsH_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.repsH_le

/-- info: 'QLSHoeffding.zetaMs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.zetaMs_le

/-- info: 'QLSHoeffding.four_log_two_le_log_ten_div_zetaMs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.four_log_two_le_log_ten_div_zetaMs

/-- info: 'QLSHoeffding.repsH_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.repsH_bracket

/-! ### The protocol, its correctness and its costs -/

/-- info: 'QLSHoeffding.impl_correctnessH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.impl_correctnessH

/-- info: 'QLSHoeffding.walkStepsH_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.walkStepsH_le

/-- info: 'QLSHoeffding.impl_worstCostH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.impl_worstCostH

/-- info: 'QLSHoeffding.impl_matrix_queriesH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.impl_matrix_queriesH

/-- info: 'QLSHoeffding.impl_source_queriesH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QLSHoeffding.impl_source_queriesH
