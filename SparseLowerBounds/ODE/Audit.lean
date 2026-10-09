import SparseLowerBounds.ODE.Statements

set_option synthInstance.maxHeartbeats 400000

section
/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. The audits cover every theorem
of the dissipative-ODE lower bounds (Theorem `odel:thm:combined`, manuscript
lines 3654-3953 and 4001-4009, with Lemma `odel:lem:outer`, Theorem
`odel:thm:joint` and Lemma `odel:lem:herald` in the ODE model; 230 theorems)
and every Prop-valued field of the structures `Family`, `Family.InClass`,
`Solver`, `Family.Witnesses`, `JointRange` and `CombinedRange` (23 fields).
Every report lists `propext`, `Classical.choice` and `Quot.sound`, except for
7 elementary lemmas, whose reports list a subset of these three axioms (5 of
them depend on no axiom). In module order, helper modules included: the
generic additive adversary `Query/PositiveAdversary` (with
`Helpers/Adversary/PhaseInner`), the promise problem and outer adversary
(`ODE/Promise`, `Helpers/Ode/OuterGraph/*`, `ODE/JointGraph`,
`ODE/JointAdversary`), the model (`ODE/Model`, `ODE/Uniqueness`), the joint
family (`ODE/Parameters`, `Helpers/Ode/JointFamily/*`, `ODE/JointInstance`,
`ODE/JointCompile`, `ODE/JointTheorem`), the `g = 1` families
(`Helpers/Ode/Precision/Transfer`, `ODE/Precision`) and the combined theorem
(`ODE/Theorem`). Definitions are not listed; the proof fields of the data and
family constructions (`jointData`, `jointFamily`, `jointFamilyAt`, `hamData`,
`hamFamily`, `timeFamilyAt`, `mixedFamilyAt`, `precisionFamilyAt`) are reached
through the theorems about them (`joint_witness`, `herald_witness`,
`combined`). -/

/-! ### `SparseLowerBounds.Helpers.Adversary.PhaseInner` -/

/-- info: 'SparseLowerBounds.PositiveAdversary.inner_map_map_of_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.inner_map_map_of_isUnitary

/-- info: 'SparseLowerBounds.PositiveAdversary.norm_map_of_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.norm_map_of_isUnitary

/-- info: 'SparseLowerBounds.PositiveAdversary.inner_apply_eq_of_isStarProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.inner_apply_eq_of_isStarProjection

/-- info: 'SparseLowerBounds.PositiveAdversary.proj_apply_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.proj_apply_proj

/-- info: 'SparseLowerBounds.PositiveAdversary.phase_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.phase_apply

/-- info: 'SparseLowerBounds.PositiveAdversary.proj_phase_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.proj_phase_apply

/-- info: 'SparseLowerBounds.PositiveAdversary.rest_phase_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.rest_phase_apply

/-- info: 'SparseLowerBounds.PositiveAdversary.inner_eq_rest_add_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.inner_eq_rest_add_sum

/-- info: 'SparseLowerBounds.PositiveAdversary.re_inner_phase_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.re_inner_phase_sub

/-- info: 'SparseLowerBounds.PositiveAdversary.sum_norm_proj_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.sum_norm_proj_sq_le

/-! ### `SparseLowerBounds.Query.PositiveAdversary` -/

/-- info: 'SparseLowerBounds.PositiveAdversary.masked_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.masked_nonneg

/-- info: 'SparseLowerBounds.PositiveAdversary.masked_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.masked_symm

/-- info: 'SparseLowerBounds.PositiveAdversary.mul_le_amgm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.mul_le_amgm

/-- info: 'SparseLowerBounds.PositiveAdversary.schur_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.schur_bound

/-- info: 'SparseLowerBounds.PositiveAdversary.abs_sum_neg_two_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.abs_sum_neg_two_mul_le

/-- info: 'SparseLowerBounds.PositiveAdversary.abs_progress_query_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.abs_progress_query_sub_le

/-- info: 'SparseLowerBounds.PositiveAdversary.abs_progress_program_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.abs_progress_program_sub_le

/-- info: 'SparseLowerBounds.PositiveAdversary.abs_re_inner_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.abs_re_inner_sub_le

/-- info: 'SparseLowerBounds.PositiveAdversary.norm_inner_le_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.norm_inner_le_of_gap

/-- info: 'SparseLowerBounds.PositiveAdversary.count_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.count_ge

/-- info: 'SparseLowerBounds.PositiveAdversary.decision_count_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PositiveAdversary.decision_count_ge

/-! ### `SparseLowerBounds.ODE.Promise` -/

/-- info: 'SparseLowerBounds.ODE.oddCand_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.oddCand_spec

/-- info: 'SparseLowerBounds.ODE.isOddCand_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.isOddCand_iff

/-- info: 'SparseLowerBounds.ODE.parity_eq_neg_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.parity_eq_neg_one_iff

/-- info: 'SparseLowerBounds.ODE.parity_eq_one_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.parity_eq_one_of_ne

/-- info: 'SparseLowerBounds.ODE.parity_oddCand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.parity_oddCand

/-- info: 'SparseLowerBounds.ODE.abs_halfSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.abs_halfSign

/-- info: 'SparseLowerBounds.ODE.halfSign_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.halfSign_sq

/-- info: 'SparseLowerBounds.ODE.nonempty_promised' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.nonempty_promised

/-! ### `SparseLowerBounds.Helpers.Ode.OuterGraph.Counting` -/

/-- info: 'SparseLowerBounds.ODE.sum_le_sum_of_injOn_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.sum_le_sum_of_injOn_support

/-- info: 'SparseLowerBounds.ODE.sum_triple_ite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.sum_triple_ite

/-- info: 'SparseLowerBounds.ODE.sum_triple_ite_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.sum_triple_ite_le

/-- info: 'SparseLowerBounds.ODE.card_fin_not_lt_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.card_fin_not_lt_half

/-- info: 'SparseLowerBounds.ODE.card_fin_lt_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.card_fin_lt_half

/-- info: 'SparseLowerBounds.ODE.card_fin_mod_two_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.card_fin_mod_two_ne

/-! ### `SparseLowerBounds.Helpers.Ode.OuterGraph.Halves` -/

/-- info: 'SparseLowerBounds.ODE.OppHalf.symm' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.OppHalf.symm

/-- info: 'SparseLowerBounds.ODE.OppHalf.ne' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.OppHalf.ne

/-- info: 'SparseLowerBounds.ODE.card_oppHalf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.card_oppHalf

/-- info: 'SparseLowerBounds.ODE.halfSign_of_oppHalf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.halfSign_of_oppHalf

/-! ### `SparseLowerBounds.Helpers.Ode.OuterGraph.InnerGraph` -/

/-- info: 'SparseLowerBounds.ODE.InnerAdj.symm' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.InnerAdj.symm

/-- info: 'SparseLowerBounds.ODE.InnerAdj.parity_ne_of_ne' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.InnerAdj.parity_ne_of_ne

/-- info: 'SparseLowerBounds.ODE.InnerAdj.eq_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.InnerAdj.eq_update

/-- info: 'SparseLowerBounds.ODE.InnerAdj.sum_mod_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.InnerAdj.sum_mod_ne

/-- info: 'SparseLowerBounds.ODE.innerAdj_update' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.innerAdj_update

/-- info: 'SparseLowerBounds.ODE.card_innerAdj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.card_innerAdj

/-- info: 'SparseLowerBounds.ODE.card_innerAdj_ne_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.card_innerAdj_ne_le

/-- info: 'SparseLowerBounds.ODE.card_innerAdj_eq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.card_innerAdj_eq_le

/-! ### `SparseLowerBounds.ODE.JointGraph` -/

/-- info: 'SparseLowerBounds.ODE.OuterAdj.symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.OuterAdj.symm

/-- info: 'SparseLowerBounds.ODE.outerGamma_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.outerGamma_nonneg

/-- info: 'SparseLowerBounds.ODE.outerGamma_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.outerGamma_symm

/-- info: 'SparseLowerBounds.ODE.outerAdj_of_outerGamma_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.outerAdj_of_outerGamma_ne_zero

/-- info: 'SparseLowerBounds.ODE.halfSign_oddCand_of_outerGamma_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.halfSign_oddCand_of_outerGamma_ne_zero

/-- info: 'SparseLowerBounds.ODE.OuterAdj.ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.OuterAdj.ext

/-- info: 'SparseLowerBounds.ODE.nbr_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.nbr_self

/-- info: 'SparseLowerBounds.ODE.nbr_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.nbr_old

/-- info: 'SparseLowerBounds.ODE.nbr_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.nbr_other

/-- info: 'SparseLowerBounds.ODE.isOddCand_nbr_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.isOddCand_nbr_iff

/-- info: 'SparseLowerBounds.ODE.mkNbr_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.mkNbr_val

/-- info: 'SparseLowerBounds.ODE.oddCand_mkNbr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.oddCand_mkNbr

/-- info: 'SparseLowerBounds.ODE.outerAdj_mkNbr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.outerAdj_mkNbr

/-- info: 'SparseLowerBounds.ODE.outerDeg_le_sum_outerGamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.outerDeg_le_sum_outerGamma

/-- info: 'SparseLowerBounds.ODE.outerLam_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.outerLam_nonneg

/-- info: 'SparseLowerBounds.ODE.certWeight_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.certWeight_pos

/-- info: 'SparseLowerBounds.ODE.survivor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.survivor

/-- info: 'SparseLowerBounds.ODE.oddCand_eq_of_changed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.oddCand_eq_of_changed

/-- info: 'SparseLowerBounds.ODE.masked_row_le_triple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.masked_row_le_triple

/-- info: 'SparseLowerBounds.ODE.arith_center_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.arith_center_same

/-- info: 'SparseLowerBounds.ODE.arith_leaf_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.arith_leaf_same

/-- info: 'SparseLowerBounds.ODE.arith_center_opp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.arith_center_opp

/-- info: 'SparseLowerBounds.ODE.arith_leaf_opp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.arith_leaf_opp

/-- info: 'SparseLowerBounds.ODE.outer_schurCert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.outer_schurCert

/-! ### `SparseLowerBounds.ODE.JointAdversary` -/

/-- info: 'SparseLowerBounds.ODE.outer_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.outer_arith

/-- info: 'SparseLowerBounds.ODE.outer_count_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.outer_count_ge

/-! ### `SparseLowerBounds.ODE.Model` -/

/-- info: 'SparseLowerBounds.ODE.Family.len_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.len_nonneg

/-- info: 'SparseLowerBounds.ODE.Family.lenNat_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.lenNat_of_lt

/-- info: 'SparseLowerBounds.ODE.Family.lenNat_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.lenNat_nonneg

/-- info: 'SparseLowerBounds.ODE.Family.start_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.start_zero

/-- info: 'SparseLowerBounds.ODE.Family.start_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.start_succ

/-- info: 'SparseLowerBounds.ODE.Family.start_succ_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.start_succ_fin

/-- info: 'SparseLowerBounds.ODE.Family.start_le_start_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.start_le_start_succ

/-- info: 'SparseLowerBounds.ODE.Family.start_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.start_mono

/-- info: 'SparseLowerBounds.ODE.Family.start_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.start_nonneg

/-- info: 'SparseLowerBounds.ODE.Family.T_eq_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.T_eq_start

/-- info: 'SparseLowerBounds.ODE.Family.T_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.T_eq_sum

/-- info: 'SparseLowerBounds.ODE.Family.T_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.T_nonneg

/-- info: 'SparseLowerBounds.ODE.Family.row_sparsity_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.row_sparsity_le

/-- info: 'SparseLowerBounds.ODE.Family.col_sparsity_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.col_sparsity_le

/-- info: 'SparseLowerBounds.ODE.Family.InClass.accretive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.InClass.accretive

/-- info: 'SparseLowerBounds.ODE.Family.InClass.row_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.InClass.row_norm

/-- info: 'SparseLowerBounds.ODE.Family.InClass.col_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.InClass.col_norm

/-- info: 'SparseLowerBounds.ODE.Family.InClass.solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.InClass.solution

/-- info: 'SparseLowerBounds.ODE.Family.access_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.access_unitary

/-- info: 'SparseLowerBounds.ODE.Solver.seed_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Solver.seed_norm_le

/-- info: 'SparseLowerBounds.ODE.Solver.out_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Solver.out_isometry

/-- info: 'SparseLowerBounds.ODE.Solver.herald_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Solver.herald_proj

/-- info: 'SparseLowerBounds.ODE.Solver.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Solver.success

/-- info: 'SparseLowerBounds.ODE.Solver.accurate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Solver.accurate

/-- info: 'SparseLowerBounds.ODE.Family.Witnesses.inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.Witnesses.inClass

/-- info: 'SparseLowerBounds.ODE.Family.Witnesses.time_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.Witnesses.time_eq

/-- info: 'SparseLowerBounds.ODE.Family.Witnesses.forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.Witnesses.forces

/-- info: 'SparseLowerBounds.ODE.Family.Witnesses.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.Witnesses.mono

/-- info: 'SparseLowerBounds.ODE.matrixOperator_I_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.matrixOperator_I_smul

/-- info: 'SparseLowerBounds.ODE.accretive_I_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.accretive_I_smul

/-! ### `SparseLowerBounds.ODE.Uniqueness` -/

/-- info: 'SparseLowerBounds.ODE.solvesODE_const_eqOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.solvesODE_const_eqOn

/-- info: 'SparseLowerBounds.ODE.Family.solves_eqOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.solves_eqOn

/-- info: 'SparseLowerBounds.ODE.Family.solves_endpoint_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.solves_endpoint_unique

/-- info: 'SparseLowerBounds.ODE.Family.forall_solves_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.Family.forall_solves_iff

/-! ### `SparseLowerBounds.ODE.Parameters` -/

/-- info: 'SparseLowerBounds.ODE.JointRange.s_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.JointRange.s_ge

/-- info: 'SparseLowerBounds.ODE.JointRange.tau_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.JointRange.tau_ge

/-- info: 'SparseLowerBounds.ODE.JointRange.gbar_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.JointRange.gbar_ge

/-- info: 'SparseLowerBounds.ODE.JointRange.eps_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.JointRange.eps_pos

/-- info: 'SparseLowerBounds.ODE.JointRange.eps_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.JointRange.eps_le

/-- info: 'SparseLowerBounds.ODE.one_le_jointMu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.one_le_jointMu

/-- info: 'SparseLowerBounds.ODE.two_le_jointMu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.two_le_jointMu

/-- info: 'SparseLowerBounds.ODE.two_pow_jointMu_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.two_pow_jointMu_le

/-- info: 'SparseLowerBounds.ODE.lt_two_mul_two_pow_jointMu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.lt_two_mul_two_pow_jointMu

/-- info: 'SparseLowerBounds.ODE.jointMu_eq_hsMu_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointMu_eq_hsMu_add_one

/-- info: 'SparseLowerBounds.ODE.half_lt_two_pow_jointMu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.half_lt_two_pow_jointMu

/-- info: 'SparseLowerBounds.ODE.two_le_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.two_le_two_pow

/-- info: 'SparseLowerBounds.ODE.even_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.even_two_pow

/-- info: 'SparseLowerBounds.ODE.jointN_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointN_time

/-- info: 'SparseLowerBounds.ODE.le_jointN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.le_jointN

/-- info: 'SparseLowerBounds.ODE.fifth_lt_jointN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.fifth_lt_jointN

/-- info: 'SparseLowerBounds.ODE.one_le_jointN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.one_le_jointN

/-- info: 'SparseLowerBounds.ODE.even_jointM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.even_jointM

/-- info: 'SparseLowerBounds.ODE.four_le_jointM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.four_le_jointM

/-- info: 'SparseLowerBounds.ODE.jointM_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointM_le

/-- info: 'SparseLowerBounds.ODE.half_sq_le_jointM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.half_sq_le_jointM

/-- info: 'SparseLowerBounds.ODE.sqrt_jointM_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.sqrt_jointM_le

/-- info: 'SparseLowerBounds.ODE.div_sqrt_two_le_sqrt_jointM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.div_sqrt_two_le_sqrt_jointM

/-- info: 'SparseLowerBounds.ODE.sqrt_jointM_mul_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.sqrt_jointM_mul_ge

/-- info: 'SparseLowerBounds.ODE.corr_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.corr_ge

/-- info: 'SparseLowerBounds.ODE.joint_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.joint_numeric

/-! ### `SparseLowerBounds.Helpers.Ode.JointFamily.Defs` -/

/-- info: 'SparseLowerBounds.ODE.card_jointIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.card_jointIndex

/-! ### `SparseLowerBounds.Helpers.Ode.JointFamily.Eigen` -/

/-- info: 'SparseLowerBounds.ODE.sum_gadget_mul_alt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.sum_gadget_mul_alt

/-- info: 'SparseLowerBounds.ODE.sum_gadget_mul_alt'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.sum_gadget_mul_alt'

/-- info: 'SparseLowerBounds.ODE.candState_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.candState_inl

/-- info: 'SparseLowerBounds.ODE.candState_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.candState_inr

/-- info: 'SparseLowerBounds.ODE.sum_stageHam_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.sum_stageHam_row

/-- info: 'SparseLowerBounds.ODE.stageHam_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.stageHam_symm

/-- info: 'SparseLowerBounds.ODE.star_stageHam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.star_stageHam

/-- info: 'SparseLowerBounds.ODE.stageHam_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.stageHam_isHermitian

/-- info: 'SparseLowerBounds.ODE.stageHam_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.stageHam_support

/-- info: 'SparseLowerBounds.ODE.sum_norm_sq_stageHam_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.sum_norm_sq_stageHam_row

/-- info: 'SparseLowerBounds.ODE.sum_norm_sq_stageHam_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.sum_norm_sq_stageHam_col

/-- info: 'SparseLowerBounds.ODE.matrixOperator_stageHam_candState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.matrixOperator_stageHam_candState

/-- info: 'SparseLowerBounds.ODE.jointGen_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointGen_support

/-- info: 'SparseLowerBounds.ODE.accretive_jointGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.accretive_jointGen

/-- info: 'SparseLowerBounds.ODE.sum_norm_sq_jointGen_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.sum_norm_sq_jointGen_row

/-- info: 'SparseLowerBounds.ODE.sum_norm_sq_jointGen_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.sum_norm_sq_jointGen_col

/-- info: 'SparseLowerBounds.ODE.sum_norm_sq_alt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.sum_norm_sq_alt

/-- info: 'SparseLowerBounds.ODE.norm_candState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.norm_candState

/-- info: 'SparseLowerBounds.ODE.inner_candState_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.inner_candState_of_ne

/-- info: 'SparseLowerBounds.ODE.inner_candState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.inner_candState

/-- info: 'SparseLowerBounds.ODE.norm_sum_candState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.norm_sum_candState

/-- info: 'SparseLowerBounds.ODE.norm_jointInit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.norm_jointInit

/-- info: 'SparseLowerBounds.ODE.norm_neg_negI_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.norm_neg_negI_pow

/-- info: 'SparseLowerBounds.ODE.norm_jointSrc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.norm_jointSrc

/-- info: 'SparseLowerBounds.ODE.halfObs_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.halfObs_inl

/-- info: 'SparseLowerBounds.ODE.halfObs_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.halfObs_inr

/-- info: 'SparseLowerBounds.ODE.halfObs_candState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.halfObs_candState

/-- info: 'SparseLowerBounds.ODE.halfObs_isSelfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.halfObs_isSelfAdjoint

/-- info: 'SparseLowerBounds.ODE.norm_halfObs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.norm_halfObs_le

/-! ### `SparseLowerBounds.Helpers.Ode.JointFamily.Solution` -/

/-- info: 'SparseLowerBounds.ODE.hasDerivWithinAt_ramp_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.hasDerivWithinAt_ramp_below

/-- info: 'SparseLowerBounds.ODE.hasDerivWithinAt_ramp_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.hasDerivWithinAt_ramp_above

/-- info: 'SparseLowerBounds.ODE.hasDerivWithinAt_ramp_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.hasDerivWithinAt_ramp_mid

/-- info: 'SparseLowerBounds.ODE.hasDerivWithinAt_phasePath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.hasDerivWithinAt_phasePath

/-- info: 'SparseLowerBounds.ODE.hasDerivWithinAt_candPhase_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.hasDerivWithinAt_candPhase_stage

/-- info: 'SparseLowerBounds.ODE.hasDerivWithinAt_candPhase_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.hasDerivWithinAt_candPhase_after

/-- info: 'SparseLowerBounds.ODE.candPhase_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.candPhase_zero

/-- info: 'SparseLowerBounds.ODE.candPhase_of_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.candPhase_of_ge

/-- info: 'SparseLowerBounds.ODE.exp_neg_I_mul_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.exp_neg_I_mul_sign

/-- info: 'SparseLowerBounds.ODE.exp_candPhase_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.exp_candPhase_final

/-- info: 'SparseLowerBounds.ODE.one_le_of_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.one_le_of_time

/-- info: 'SparseLowerBounds.ODE.jointSol_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointSol_zero

/-- info: 'SparseLowerBounds.ODE.jointSol_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointSol_end

/-- info: 'SparseLowerBounds.ODE.solvesODE_hidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.solvesODE_hidden

/-- info: 'SparseLowerBounds.ODE.solvesODE_idle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.solvesODE_idle

/-- info: 'SparseLowerBounds.ODE.solvesODE_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.solvesODE_source

/-! ### `SparseLowerBounds.ODE.JointInstance` -/

/-- info: 'SparseLowerBounds.ODE.jointTable_word_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointTable_word_mem

/-- info: 'SparseLowerBounds.ODE.stageHam_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.stageHam_inl

/-- info: 'SparseLowerBounds.ODE.wordDecode_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.wordDecode_stage

/-- info: 'SparseLowerBounds.ODE.jointGen_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointGen_decoded

/-- info: 'SparseLowerBounds.ODE.jointLoc_inl' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointLoc_inl

/-- info: 'SparseLowerBounds.ODE.jointGen_row_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointGen_row_covers

/-- info: 'SparseLowerBounds.ODE.jointGen_col_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointGen_col_covers

/-- info: 'SparseLowerBounds.ODE.jointData_locators_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointData_locators_const

/-- info: 'SparseLowerBounds.ODE.jointData_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointData_dyadic

/-- info: 'SparseLowerBounds.ODE.jointFamily_lenNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointFamily_lenNat

/-- info: 'SparseLowerBounds.ODE.jointFamily_start_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointFamily_start_le

/-- info: 'SparseLowerBounds.ODE.jointFamily_start_idle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointFamily_start_idle

/-- info: 'SparseLowerBounds.ODE.jointFamily_start_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointFamily_start_end

/-- info: 'SparseLowerBounds.ODE.jointFamily_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointFamily_T

/-- info: 'SparseLowerBounds.ODE.jointFamily_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointFamily_mass

/-- info: 'SparseLowerBounds.ODE.jointSol_solves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointSol_solves

/-- info: 'SparseLowerBounds.ODE.jointSol_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointSol_T

/-- info: 'SparseLowerBounds.ODE.norm_jointSol_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.norm_jointSol_T

/-- info: 'SparseLowerBounds.ODE.unitDirection_jointSol_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.unitDirection_jointSol_T

/-- info: 'SparseLowerBounds.ODE.jointFamily_inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointFamily_inClass

/-- info: 'SparseLowerBounds.ODE.jointFamily_skew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointFamily_skew

/-- info: 'SparseLowerBounds.ODE.inner_halfObs_jointTarget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.inner_halfObs_jointTarget

/-! ### `SparseLowerBounds.ODE.JointCompile` -/

/-- info: 'SparseLowerBounds.ODE.stageAddressFamily_proj_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.stageAddressFamily_proj_apply

/-- info: 'SparseLowerBounds.ODE.hitProj_stage_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.hitProj_stage_apply

/-- info: 'SparseLowerBounds.ODE.stageGate_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.stageGate_apply

/-- info: 'SparseLowerBounds.ODE.stageGate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.stageGate_unitary

/-- info: 'SparseLowerBounds.ODE.access_value_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.access_value_apply

/-- info: 'SparseLowerBounds.ODE.implementsOn_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.implementsOn_joint

/-! ### `SparseLowerBounds.ODE.JointTheorem` -/

/-- info: 'SparseLowerBounds.ODE.joint_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.joint_general

/-- info: 'SparseLowerBounds.ODE.joint_forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.joint_forces

/-- info: 'SparseLowerBounds.ODE.joint_instance_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.joint_instance_props

/-- info: 'SparseLowerBounds.ODE.jointFamilyAt_g' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointFamilyAt_g

/-- info: 'SparseLowerBounds.ODE.jointCorr_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.jointCorr_ge

/-- info: 'SparseLowerBounds.ODE.joint_bound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.joint_bound_le

/-- info: 'SparseLowerBounds.ODE.joint_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.joint_witness

/-! ### `SparseLowerBounds.Helpers.Ode.Precision.Transfer` -/

/-- info: 'SparseLowerBounds.ODE.solves_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.solves_flow

/-- info: 'SparseLowerBounds.ODE.solves_evolve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.solves_evolve

/-- info: 'SparseLowerBounds.ODE.hamData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.hamData_matrix

/-- info: 'SparseLowerBounds.ODE.oracles_hamData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.oracles_hamData

/-- info: 'SparseLowerBounds.ODE.hamFamily_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.hamFamily_T

/-- info: 'SparseLowerBounds.ODE.hamFamily_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.hamFamily_mass

/-- info: 'SparseLowerBounds.ODE.access_hamFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.access_hamFamily

/-- info: 'SparseLowerBounds.ODE.implementsOn_hamFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.implementsOn_hamFamily

/-- info: 'SparseLowerBounds.ODE.hamFamily_solves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.hamFamily_solves

/-- info: 'SparseLowerBounds.ODE.hamFamily_inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.hamFamily_inClass

/-! ### `SparseLowerBounds.ODE.Precision` -/

/-- info: 'SparseLowerBounds.ODE.hamFamily_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.hamFamily_props

/-- info: 'SparseLowerBounds.ODE.forces_of_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.forces_of_spec

/-- info: 'SparseLowerBounds.ODE.forces_or_of_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.forces_or_of_max

/-- info: 'SparseLowerBounds.ODE.timeFamilyAt_inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.timeFamilyAt_inClass

/-- info: 'SparseLowerBounds.ODE.timeFamilyAt_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.timeFamilyAt_T

/-- info: 'SparseLowerBounds.ODE.mixedFamilyAt_inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.mixedFamilyAt_inClass

/-- info: 'SparseLowerBounds.ODE.precisionFamilyAt_inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.precisionFamilyAt_inClass

/-- info: 'SparseLowerBounds.ODE.mixedFamilyAt_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.mixedFamilyAt_T

/-- info: 'SparseLowerBounds.ODE.precisionFamilyAt_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.precisionFamilyAt_T

/-- info: 'SparseLowerBounds.ODE.time_forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.time_forces

/-- info: 'SparseLowerBounds.ODE.mixed_forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.mixed_forces

/-- info: 'SparseLowerBounds.ODE.precision_forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.precision_forces

/-- info: 'SparseLowerBounds.ODE.precision_forces_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.precision_forces_sqrt

/-- info: 'SparseLowerBounds.ODE.herald_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.herald_max

/-- info: 'SparseLowerBounds.ODE.herald_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.herald_witness

/-- info: 'SparseLowerBounds.ODE.precision_terms_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.precision_terms_witness

/-! ### `SparseLowerBounds.ODE.Theorem` -/

/-- info: 'SparseLowerBounds.ODE.CombinedRange.s_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.CombinedRange.s_ge

/-- info: 'SparseLowerBounds.ODE.CombinedRange.tau_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.CombinedRange.tau_ge

/-- info: 'SparseLowerBounds.ODE.CombinedRange.gbar_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.CombinedRange.gbar_ge

/-- info: 'SparseLowerBounds.ODE.CombinedRange.eps_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.CombinedRange.eps_pos

/-- info: 'SparseLowerBounds.ODE.CombinedRange.eps_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.CombinedRange.eps_le

/-- info: 'SparseLowerBounds.ODE.CombinedRange.toJointRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.CombinedRange.toJointRange

/-- info: 'SparseLowerBounds.ODE.CombinedRange.toHSRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.CombinedRange.toHSRange

/-- info: 'SparseLowerBounds.ODE.combinedConst_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.combinedConst_eq

/-- info: 'SparseLowerBounds.ODE.combinedConst_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.combinedConst_pos

/-- info: 'SparseLowerBounds.ODE.cT_le_inv_200' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.cT_le_inv_200

/-- info: 'SparseLowerBounds.ODE.c0_le_jointConst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.c0_le_jointConst

/-- info: 'SparseLowerBounds.ODE.combined_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.combined_max

/-- info: 'SparseLowerBounds.ODE.combined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ODE.combined
end
