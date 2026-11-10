import LargeSparsityCore.Riesz
import LargeSparsityCore.Clusters
import LargeSparsityCore.ProductFilter
import LargeSparsityCore.FilterBound
import LargeSparsityCore.GeneralResolvent
import LargeSparsityCore.CayleyBlocks
import LargeSparsityCore.CoreFilter
import LargeSparsityCore.Scalars
import LargeSparsityCore.Smoothing
import LargeSparsityCore.Parameters
import LargeSparsityCore.Core
import LargeSparsityCore.NativeLocal
import LargeSparsityCore.NativeOperators
import LargeSparsityCore.NativeMoments
import LargeSparsityCore.NativeCore
import LargeSparsityCore.NativeTwoNorm
import LargeSparsityCore.NativeTwoNormCore

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover every theorem of the library (400 theorems), beginning
with the core theorems, then in module order. 391 reports list exactly `propext`, `Classical.choice`
and `Quot.sound`; the other 9 (polynomial identities in noncommuting variables, proved by
`noncomm_ring`) list a strict subset. -/

/-! ### Final theorems: the core simulation and its main steps -/

/-- info: 'LargeSparsityCore.Native.core_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.core_simulation

/-- info: 'LargeSparsityCore.Native.core_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.core_native

/-- info: 'LargeSparsityCore.Native.core_simulation_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.core_simulation_two

/-- info: 'LargeSparsityCore.Native.core_native_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.core_native_two

/-- info: 'LargeSparsityCore.Native.coreData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.coreData

/-- info: 'LargeSparsityCore.Native.coreData_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.coreData_two

/-- info: 'LargeSparsityCore.Native.compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.compression

/-- info: 'LargeSparsityCore.Native.spectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.spectral

/-- info: 'LargeSparsityCore.Native.active_implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.active_implementsOn

/-- info: 'LargeSparsityCore.Native.physProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.physProgram_count

/-- info: 'LargeSparsityCore.Native.logicalProgram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.logicalProgram_eval

/-- info: 'LargeSparsityCore.Core.core_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Core.core_query

/-- info: 'LargeSparsityCore.Core.core_implementation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Core.core_implementation

/-- info: 'LargeSparsityCore.CoreFilter.filter_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CoreFilter.filter_bound

/-- info: 'LargeSparsityCore.Parameters.Regime.filter_estimate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.filter_estimate

/-- info: 'LargeSparsityCore.Parameters.Regime.catalyst_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.catalyst_le

/-- info: 'LargeSparsityCore.Parameters.Regime.degree_le_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.degree_le_sqrt

/-- info: 'LargeSparsityCore.GeneralResolvent.exists_global_resolvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.GeneralResolvent.exists_global_resolvent

/-- info: 'LargeSparsityCore.FilterBound.filter_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.FilterBound.filter_norm_le

/-- info: 'LargeSparsityCore.Riesz.riesz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.riesz

/-- info: 'LargeSparsityCore.Riesz.dunford' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.dunford

/-! ### Riesz projections and the Dunford formula (`Riesz`) -/

/-- info: 'LargeSparsityCore.Riesz.outer_proj_identity' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.outer_proj_identity

/-- info: 'LargeSparsityCore.Riesz.outer_compl_identity' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.outer_compl_identity

/-- info: 'LargeSparsityCore.Riesz.inner_proj_identity' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.inner_proj_identity

/-- info: 'LargeSparsityCore.Riesz.inner_compl_identity' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.inner_compl_identity

/-- info: 'LargeSparsityCore.Riesz.proj_outer_identity' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.proj_outer_identity

/-- info: 'LargeSparsityCore.Riesz.proj_inner_identity' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.proj_inner_identity

/-- info: 'LargeSparsityCore.Riesz.sub_outer_identity' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.sub_outer_identity

/-- info: 'LargeSparsityCore.Riesz.sub_inner_identity' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.sub_inner_identity

/-- info: 'LargeSparsityCore.Riesz.outer_inner_identity' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.outer_inner_identity

/-- info: 'LargeSparsityCore.Riesz.commute_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.commute_sub

/-- info: 'LargeSparsityCore.Riesz.outer_mul_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.outer_mul_proj

/-- info: 'LargeSparsityCore.Riesz.outer_mul_compl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.outer_mul_compl

/-- info: 'LargeSparsityCore.Riesz.inner_mul_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.inner_mul_proj

/-- info: 'LargeSparsityCore.Riesz.inner_mul_compl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.inner_mul_compl

/-- info: 'LargeSparsityCore.Riesz.commute_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.commute_outer

/-- info: 'LargeSparsityCore.Riesz.commute_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.commute_inner

/-- info: 'LargeSparsityCore.Riesz.commute_sub_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.commute_sub_outer

/-- info: 'LargeSparsityCore.Riesz.commute_sub_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.commute_sub_inner

/-- info: 'LargeSparsityCore.Riesz.outer_mul_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.outer_mul_inner

/-- info: 'LargeSparsityCore.Riesz.isUnit_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.isUnit_sub

/-- info: 'LargeSparsityCore.Riesz.resolvent_eq_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.resolvent_eq_split

/-- info: 'LargeSparsityCore.Riesz.commute_resolvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.commute_resolvent

/-- info: 'LargeSparsityCore.Riesz.commute_aeval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.commute_aeval

/-- info: 'LargeSparsityCore.Riesz.differentiable_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.differentiable_outer

/-- info: 'LargeSparsityCore.Riesz.differentiable_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.differentiable_inner

/-- info: 'LargeSparsityCore.Riesz.differentiableAt_outer_part' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.differentiableAt_outer_part

/-- info: 'LargeSparsityCore.Riesz.differentiableAt_inner_part' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.differentiableAt_inner_part

/-- info: 'LargeSparsityCore.Riesz.differentiableAt_resolvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.differentiableAt_resolvent

/-- info: 'LargeSparsityCore.Riesz.exterior_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.exterior_identity

/-- info: 'LargeSparsityCore.Riesz.norm_exterior_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.norm_exterior_sub_le

/-- info: 'LargeSparsityCore.Riesz.integral_exterior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.integral_exterior

/-- info: 'LargeSparsityCore.Riesz.integral_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.integral_interior

/-- info: 'LargeSparsityCore.Riesz.circleIntegral_comp_clm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.circleIntegral_comp_clm

/-- info: 'LargeSparsityCore.Riesz.differentiable_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.differentiable_quotient

/-- info: 'LargeSparsityCore.Riesz.sub_mul_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.sub_mul_quotient

/-- info: 'LargeSparsityCore.Riesz.norm_proj_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.norm_proj_le

/-- info: 'LargeSparsityCore.Riesz.norm_aeval_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Riesz.norm_aeval_mul_le

/-! ### Spectral clusters (`Clusters`) -/

/-- info: 'LargeSparsityCore.Clusters.linProd_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Clusters.linProd_add

/-- info: 'LargeSparsityCore.Clusters.eval_linProd_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Clusters.eval_linProd_ne_zero

/-- info: 'LargeSparsityCore.Clusters.isCoprime_X_sub_C_linProd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Clusters.isCoprime_X_sub_C_linProd

/-- info: 'LargeSparsityCore.Clusters.isCoprime_linProd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Clusters.isCoprime_linProd

/-- info: 'LargeSparsityCore.Clusters.outer_eq_aeval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Clusters.outer_eq_aeval

/-- info: 'LargeSparsityCore.Clusters.inner_eq_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Clusters.inner_eq_outer

/-- info: 'LargeSparsityCore.Clusters.isUnit_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Clusters.isUnit_outer

/-- info: 'LargeSparsityCore.Clusters.isUnit_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Clusters.isUnit_inner

/-- info: 'LargeSparsityCore.Clusters.not_isUnit_of_mem_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Clusters.not_isUnit_of_mem_roots

/-- info: 'LargeSparsityCore.Clusters.exists_clusters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Clusters.exists_clusters

/-! ### The product filter (`ProductFilter`) -/

/-- info: 'LargeSparsityCore.ProductFilter.natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.ProductFilter.natDegree_le

/-- info: 'LargeSparsityCore.ProductFilter.coeff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.ProductFilter.coeff_nonneg

/-- info: 'LargeSparsityCore.ProductFilter.eval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.ProductFilter.eval_one

/-- info: 'LargeSparsityCore.ProductFilter.reflect_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.ProductFilter.reflect_eq

/-- info: 'LargeSparsityCore.ProductFilter.coeff_palindromic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.ProductFilter.coeff_palindromic

/-- info: 'LargeSparsityCore.ProductFilter.coeff_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.ProductFilter.coeff_sum

/-- info: 'LargeSparsityCore.ProductFilter.absolute_mass_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.ProductFilter.absolute_mass_two

/-- info: 'LargeSparsityCore.ProductFilter.operator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.ProductFilter.operator_eq

/-- info: 'LargeSparsityCore.ProductFilter.aeval_cpoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.ProductFilter.aeval_cpoly

/-- info: 'LargeSparsityCore.ProductFilter.eval_cpoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.ProductFilter.eval_cpoly

/-! ### The filter bound on three circles (`FilterBound`) -/

/-- info: 'LargeSparsityCore.FilterBound.inverse_power_norm_le_sphere' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.FilterBound.inverse_power_norm_le_sphere

/-- info: 'LargeSparsityCore.FilterBound.commute_ring_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.FilterBound.commute_ring_inverse

/-- info: 'LargeSparsityCore.FilterBound.commute_T_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.FilterBound.commute_T_outer

/-- info: 'LargeSparsityCore.FilterBound.inverse_outer_mul_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.FilterBound.inverse_outer_mul_proj

/-- info: 'LargeSparsityCore.FilterBound.outer_sub_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.FilterBound.outer_sub_eq

/-- info: 'LargeSparsityCore.FilterBound.one_sub_smul_bulkInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.FilterBound.one_sub_smul_bulkInverse

/-- info: 'LargeSparsityCore.FilterBound.bulkInverse_mul_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.FilterBound.bulkInverse_mul_one_sub

/-- info: 'LargeSparsityCore.FilterBound.bulkInverse_pow_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.FilterBound.bulkInverse_pow_norm_le

/-- info: 'LargeSparsityCore.FilterBound.average_pow_mul_proj_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.FilterBound.average_pow_mul_proj_norm_le

/-! ### The finite-clock resolvent (`GeneralResolvent`) -/

/-- info: 'LargeSparsityCore.GeneralResolvent.exists_inverse_one_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.GeneralResolvent.exists_inverse_one_add

/-- info: 'LargeSparsityCore.GeneralResolvent.norm_isometry_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.GeneralResolvent.norm_isometry_apply

/-- info: 'LargeSparsityCore.GeneralResolvent.norm_isometry_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.GeneralResolvent.norm_isometry_le

/-- info: 'LargeSparsityCore.GeneralResolvent.norm_feedback_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.GeneralResolvent.norm_feedback_le

/-- info: 'LargeSparsityCore.GeneralResolvent.re_inner_omega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.GeneralResolvent.re_inner_omega

/-- info: 'LargeSparsityCore.GeneralResolvent.kappa_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.GeneralResolvent.kappa_mul

/-- info: 'LargeSparsityCore.GeneralResolvent.c_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.GeneralResolvent.c_mul

/-- info: 'LargeSparsityCore.GeneralResolvent.sigma_sq_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.GeneralResolvent.sigma_sq_mul

/-- info: 'LargeSparsityCore.GeneralResolvent.c_sigma_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.GeneralResolvent.c_sigma_identity

/-- info: 'LargeSparsityCore.GeneralResolvent.feedback_scaling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.GeneralResolvent.feedback_scaling

/-- info: 'LargeSparsityCore.GeneralResolvent.exists_local_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.GeneralResolvent.exists_local_certificate

/-! ### The Cayley block resolvent (`CayleyBlocks`) -/

/-- info: 'LargeSparsityCore.CayleyBlocks.comp_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.comp_one

/-- info: 'LargeSparsityCore.CayleyBlocks.one_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.one_comp

/-- info: 'LargeSparsityCore.CayleyBlocks.commute_R1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.commute_R1

/-- info: 'LargeSparsityCore.CayleyBlocks.Spectral.adjoint_comp_self_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.Spectral.adjoint_comp_self_adjoint

/-- info: 'LargeSparsityCore.CayleyBlocks.Spectral.pp_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.Spectral.pp_k

/-- info: 'LargeSparsityCore.CayleyBlocks.Spectral.pm_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.Spectral.pm_k

/-- info: 'LargeSparsityCore.CayleyBlocks.Spectral.commute_pp_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.Spectral.commute_pp_k

/-- info: 'LargeSparsityCore.CayleyBlocks.Spectral.commute_pm_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.Spectral.commute_pm_k

/-- info: 'LargeSparsityCore.CayleyBlocks.Spectral.commute_D_R1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.Spectral.commute_D_R1

/-- info: 'LargeSparsityCore.CayleyBlocks.Spectral.commute_D' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.Spectral.commute_D

/-- info: 'LargeSparsityCore.CayleyBlocks.Spectral.bulk_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.Spectral.bulk_idem

/-- info: 'LargeSparsityCore.CayleyBlocks.Spectral.bulk_adj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.Spectral.bulk_adj

/-- info: 'LargeSparsityCore.CayleyBlocks.Spectral.commute_bulk_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.Spectral.commute_bulk_k

/-- info: 'LargeSparsityCore.CayleyBlocks.Spectral.sum_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.Spectral.sum_proj

/-- info: 'LargeSparsityCore.CayleyBlocks.Spectral.R1_mul_Pp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.Spectral.R1_mul_Pp

/-- info: 'LargeSparsityCore.CayleyBlocks.Spectral.R1_mul_Pm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.Spectral.R1_mul_Pm

/-- info: 'LargeSparsityCore.CayleyBlocks.Spectral.one_add_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.Spectral.one_add_ne_zero

/-- info: 'LargeSparsityCore.CayleyBlocks.Spectral.one_sub_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.Spectral.one_sub_ne_zero

/-- info: 'LargeSparsityCore.CayleyBlocks.Spectral.eigen_of_R1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.Spectral.eigen_of_R1

/-- info: 'LargeSparsityCore.CayleyBlocks.Spectral.D_mul_Pp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.Spectral.D_mul_Pp

/-- info: 'LargeSparsityCore.CayleyBlocks.Spectral.D_mul_Pm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.Spectral.D_mul_Pm

/-- info: 'LargeSparsityCore.CayleyBlocks.norm_proj_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.norm_proj_le_one

/-- info: 'LargeSparsityCore.CayleyBlocks.norm_adjoint_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.norm_adjoint_comp

/-- info: 'LargeSparsityCore.CayleyBlocks.norm_lamp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.norm_lamp

/-- info: 'LargeSparsityCore.CayleyBlocks.norm_lamm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.norm_lamm

/-- info: 'LargeSparsityCore.CayleyBlocks.exists_resolvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.exists_resolvent

/-- info: 'LargeSparsityCore.CayleyBlocks.isSelfAdjoint_K_bulk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.isSelfAdjoint_K_bulk

/-- info: 'LargeSparsityCore.CayleyBlocks.D_mul_R1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.D_mul_R1

/-- info: 'LargeSparsityCore.CayleyBlocks.exists_resolvent_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CayleyBlocks.exists_resolvent_bounds

/-! ### The filter on the global private block (`CoreFilter`) -/

/-- info: 'LargeSparsityCore.CoreFilter.pointBound_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CoreFilter.pointBound_mono

/-- info: 'LargeSparsityCore.CoreFilter.pointBound_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CoreFilter.pointBound_comm

/-- info: 'LargeSparsityCore.CoreFilter.exists_global_resolvent_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CoreFilter.exists_global_resolvent_gap

/-- info: 'LargeSparsityCore.CoreFilter.ring_inverse_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CoreFilter.ring_inverse_eq

/-- info: 'LargeSparsityCore.CoreFilter.one_sub_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.CoreFilter.one_sub_sq_le

/-! ### Scalar facts (`Scalars`) -/

/-- info: 'LargeSparsityCore.Scalars.lamp_eq_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Scalars.lamp_eq_div

/-- info: 'LargeSparsityCore.Scalars.lamm_eq_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Scalars.lamm_eq_div

/-- info: 'LargeSparsityCore.Scalars.lamp_eq_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Scalars.lamp_eq_exp

/-- info: 'LargeSparsityCore.Scalars.lamm_eq_lamp_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Scalars.lamm_eq_lamp_neg

/-- info: 'LargeSparsityCore.Scalars.lamm_eq_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Scalars.lamm_eq_exp

/-- info: 'LargeSparsityCore.Scalars.exp_pow_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Scalars.exp_pow_eq_one

/-- info: 'LargeSparsityCore.Scalars.lamp_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Scalars.lamp_sub_one

/-- info: 'LargeSparsityCore.Scalars.lamp_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Scalars.lamp_ne_one

/-- info: 'LargeSparsityCore.Scalars.lamm_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Scalars.lamm_ne_one

/-- info: 'LargeSparsityCore.Scalars.norm_one_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Scalars.norm_one_add

/-- info: 'LargeSparsityCore.Scalars.norm_lamp_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Scalars.norm_lamp_sub_one_le

/-- info: 'LargeSparsityCore.Scalars.norm_lamm_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Scalars.norm_lamm_sub_one_le

/-- info: 'LargeSparsityCore.Scalars.norm_lamp_sub_lamm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Scalars.norm_lamp_sub_lamm

/-- info: 'LargeSparsityCore.Scalars.geometricSum_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Scalars.geometricSum_eq_zero

/-- info: 'LargeSparsityCore.Scalars.norm_pow_sub_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Scalars.norm_pow_sub_pow_le

/-- info: 'LargeSparsityCore.Scalars.norm_geometricAverage_root_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Scalars.norm_geometricAverage_root_le

/-- info: 'LargeSparsityCore.Scalars.norm_geometricAverage_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Scalars.norm_geometricAverage_le

/-- info: 'LargeSparsityCore.Scalars.norm_filter_root_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Scalars.norm_filter_root_le

/-! ### Smoothing and amplification (`Smoothing`) -/

/-- info: 'LargeSparsityCore.Smoothing.prepared_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Smoothing.prepared_isometry

/-- info: 'LargeSparsityCore.Smoothing.implementation_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Smoothing.implementation_isometry

/-- info: 'LargeSparsityCore.Smoothing.implementation_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Smoothing.implementation_error

/-- info: 'LargeSparsityCore.Smoothing.implementation_error_to_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Smoothing.implementation_error_to_target

/-- info: 'LargeSparsityCore.Smoothing.exists_implementation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Smoothing.exists_implementation

/-- info: 'LargeSparsityCore.Smoothing.implementation_query_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Smoothing.implementation_query_certificate

/-! ### The parameters (`Parameters`) -/

/-- info: 'LargeSparsityCore.Parameters.pval_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.pval_ge

/-- info: 'LargeSparsityCore.Parameters.steps_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.steps_pos

/-- info: 'LargeSparsityCore.Parameters.le_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.le_steps

/-- info: 'LargeSparsityCore.Parameters.steps_mul_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.steps_mul_w

/-- info: 'LargeSparsityCore.Parameters.w_le_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.w_le_quarter

/-- info: 'LargeSparsityCore.Parameters.kval_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.kval_ge

/-- info: 'LargeSparsityCore.Parameters.mval_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.mval_ge

/-- info: 'LargeSparsityCore.Parameters.B0_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.B0_ge

/-- info: 'LargeSparsityCore.Parameters.sm_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.sm_nonneg

/-- info: 'LargeSparsityCore.Parameters.sw_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.sw_nonneg

/-- info: 'LargeSparsityCore.Parameters.three_add_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.three_add_le_exp

/-- info: 'LargeSparsityCore.Parameters.pointBound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.pointBound_le

/-- info: 'LargeSparsityCore.Parameters.pointBound_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.pointBound_nonneg

/-- info: 'LargeSparsityCore.Parameters.Regime.τ_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.τ_pos

/-- info: 'LargeSparsityCore.Parameters.Regime.L_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.L_pos

/-- info: 'LargeSparsityCore.Parameters.Regime.h_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.h_pos

/-- info: 'LargeSparsityCore.Parameters.Regime.exp_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.exp_h

/-- info: 'LargeSparsityCore.Parameters.Regime.x_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.x_eq

/-- info: 'LargeSparsityCore.Parameters.Regime.x_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.x_ge

/-- info: 'LargeSparsityCore.Parameters.Regime.exp_quarter_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.exp_quarter_ge

/-- info: 'LargeSparsityCore.Parameters.Regime.exp_quarter_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.exp_quarter_le

/-- info: 'LargeSparsityCore.Parameters.Regime.x_ge_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.x_ge_cube

/-- info: 'LargeSparsityCore.Parameters.Regime.x_ge_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.x_ge_sq

/-- info: 'LargeSparsityCore.Parameters.Regime.r_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.r_pos

/-- info: 'LargeSparsityCore.Parameters.Regime.h_tau_le_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.h_tau_le_r

/-- info: 'LargeSparsityCore.Parameters.Regime.qstar_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.qstar_sq

/-- info: 'LargeSparsityCore.Parameters.Regime.h_le_qstar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.h_le_qstar

/-- info: 'LargeSparsityCore.Parameters.Regime.qstar_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.qstar_pos

/-- info: 'LargeSparsityCore.Parameters.Regime.p_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.p_le

/-- info: 'LargeSparsityCore.Parameters.Regime.p_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.p_pos

/-- info: 'LargeSparsityCore.Parameters.Regime.p_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.p_large

/-- info: 'LargeSparsityCore.Parameters.Regime.theta_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.theta_pos

/-- info: 'LargeSparsityCore.Parameters.Regime.p_mul_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.p_mul_theta

/-- info: 'LargeSparsityCore.Parameters.Regime.theta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.theta_le

/-- info: 'LargeSparsityCore.Parameters.Regime.theta_lt_half_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.theta_lt_half_pi

/-- info: 'LargeSparsityCore.Parameters.Regime.sin_theta_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.sin_theta_pos

/-- info: 'LargeSparsityCore.Parameters.Regime.cos_theta_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.cos_theta_pos

/-- info: 'LargeSparsityCore.Parameters.Regime.cot_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.cot_le

/-- info: 'LargeSparsityCore.Parameters.Regime.cot_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.cot_ge

/-- info: 'LargeSparsityCore.Parameters.Regime.q_le_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.q_le_p

/-- info: 'LargeSparsityCore.Parameters.Regime.q_ge_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.q_ge_p

/-- info: 'LargeSparsityCore.Parameters.Regime.q_ge_qstar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.q_ge_qstar

/-- info: 'LargeSparsityCore.Parameters.Regime.h_le_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.h_le_q

/-- info: 'LargeSparsityCore.Parameters.Regime.q_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.q_pos

/-- info: 'LargeSparsityCore.Parameters.Regime.q_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.q_large

/-- info: 'LargeSparsityCore.Parameters.Regime.q_le_two_qstar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.q_le_two_qstar

/-- info: 'LargeSparsityCore.Parameters.Regime.two_pi_q_le_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.two_pi_q_le_p

/-- info: 'LargeSparsityCore.Parameters.Regime.p_le_seven_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.p_le_seven_q

/-- info: 'LargeSparsityCore.Parameters.Regime.five_q_le_p_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.five_q_le_p_sub_one

/-- info: 'LargeSparsityCore.Parameters.Regime.k_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.k_le

/-- info: 'LargeSparsityCore.Parameters.Regime.k_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.k_pos

/-- info: 'LargeSparsityCore.Parameters.Regime.one_le_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.one_le_k

/-- info: 'LargeSparsityCore.Parameters.Regime.one_le_k_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.one_le_k_real

/-- info: 'LargeSparsityCore.Parameters.Regime.h_tau_le_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.h_tau_le_k

/-- info: 'LargeSparsityCore.Parameters.Regime.L_le_hk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.L_le_hk

/-- info: 'LargeSparsityCore.Parameters.Regime.m_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.m_le

/-- info: 'LargeSparsityCore.Parameters.Regime.one_le_m' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.one_le_m

/-- info: 'LargeSparsityCore.Parameters.Regime.B0_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.B0_le

/-- info: 'LargeSparsityCore.Parameters.Regime.B0_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.B0_pos

/-- info: 'LargeSparsityCore.Parameters.Regime.one_le_B0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.one_le_B0

/-- info: 'LargeSparsityCore.Parameters.Regime.rho0_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.rho0_pos

/-- info: 'LargeSparsityCore.Parameters.Regime.B0_mul_rho0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.B0_mul_rho0

/-- info: 'LargeSparsityCore.Parameters.Regime.rho0_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.rho0_le

/-- info: 'LargeSparsityCore.Parameters.Regime.rho0_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.rho0_ge

/-- info: 'LargeSparsityCore.Parameters.Regime.Q0_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.Q0_ge

/-- info: 'LargeSparsityCore.Parameters.Regime.rho0_mul_Q0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.rho0_mul_Q0

/-- info: 'LargeSparsityCore.Parameters.Regime.zeta_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.zeta_pos

/-- info: 'LargeSparsityCore.Parameters.Regime.q_mul_zeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.q_mul_zeta

/-- info: 'LargeSparsityCore.Parameters.Regime.q_mul_zeta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.q_mul_zeta_le

/-- info: 'LargeSparsityCore.Parameters.Regime.zeta_mul_Q0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.zeta_mul_Q0

/-- info: 'LargeSparsityCore.Parameters.Regime.a_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.a_pos

/-- info: 'LargeSparsityCore.Parameters.Regime.s_tau_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.s_tau_eq

/-- info: 'LargeSparsityCore.Parameters.Regime.a_le_qr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.a_le_qr

/-- info: 'LargeSparsityCore.Parameters.Regime.a_rho0_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.a_rho0_le

/-- info: 'LargeSparsityCore.Parameters.Regime.a_zeta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.a_zeta_le

/-- info: 'LargeSparsityCore.Parameters.Regime.a_sw_sq_div_zeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.a_sw_sq_div_zeta

/-- info: 'LargeSparsityCore.Parameters.Regime.q_sq_div_s' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.q_sq_div_s

/-- info: 'LargeSparsityCore.Parameters.Regime.four_h_tau_div_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.four_h_tau_div_L

/-- info: 'LargeSparsityCore.Parameters.Regime.second_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.second_le_one

/-- info: 'LargeSparsityCore.Parameters.Regime.sm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.sm_le

/-- info: 'LargeSparsityCore.Parameters.Regime.sw_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.sw_sq

/-- info: 'LargeSparsityCore.Parameters.Regime.sw_mul_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.sw_mul_q

/-- info: 'LargeSparsityCore.Parameters.Regime.sw_div_rho0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.sw_div_rho0

/-- info: 'LargeSparsityCore.Parameters.Regime.lamp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.lamp_eq

/-- info: 'LargeSparsityCore.Parameters.Regime.lamm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.lamm_eq

/-- info: 'LargeSparsityCore.Parameters.Regime.lamp_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.lamp_pow

/-- info: 'LargeSparsityCore.Parameters.Regime.lamm_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.lamm_pow

/-- info: 'LargeSparsityCore.Parameters.Regime.sep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.sep

/-- info: 'LargeSparsityCore.Parameters.Regime.inside_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.inside_aux

/-- info: 'LargeSparsityCore.Parameters.Regime.lamp_inside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.lamp_inside

/-- info: 'LargeSparsityCore.Parameters.Regime.lamm_inside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.lamm_inside

/-- info: 'LargeSparsityCore.Parameters.Regime.w_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.w_nonneg

/-- info: 'LargeSparsityCore.Parameters.Regime.w_le_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.w_le_a

/-- info: 'LargeSparsityCore.Parameters.Regime.cubic_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.cubic_le

/-- info: 'LargeSparsityCore.Parameters.Regime.small_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.small_step

/-- info: 'LargeSparsityCore.Parameters.Regime.L_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.L_large

/-- info: 'LargeSparsityCore.Parameters.Regime.eps_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.eps_eq

/-- info: 'LargeSparsityCore.Parameters.Regime.exp_h_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.exp_h_bound

/-- info: 'LargeSparsityCore.Parameters.Regime.h_tau_div_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.h_tau_div_k

/-- info: 'LargeSparsityCore.Parameters.Regime.iso_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.iso_le

/-- info: 'LargeSparsityCore.Parameters.Regime.F_lamp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.F_lamp

/-- info: 'LargeSparsityCore.Parameters.Regime.F_lamm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.F_lamm

/-- info: 'LargeSparsityCore.Parameters.Regime.F_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.F_le

/-- info: 'LargeSparsityCore.Parameters.Regime.iso_term_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.iso_term_le

/-- info: 'LargeSparsityCore.Parameters.Regime.bulk_term_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.bulk_term_le

/-- info: 'LargeSparsityCore.Parameters.Regime.two_le_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.two_le_p

/-- info: 'LargeSparsityCore.Parameters.Regime.one_le_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.one_le_p

/-- info: 'LargeSparsityCore.Parameters.Regime.degree_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.degree_eq

/-- info: 'LargeSparsityCore.Parameters.Regime.degree_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.degree_pos

/-- info: 'LargeSparsityCore.Parameters.Regime.nu_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.nu_pos

/-- info: 'LargeSparsityCore.Parameters.Regime.nu_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.nu_le

/-- info: 'LargeSparsityCore.Parameters.Regime.degree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.degree_le

/-- info: 'LargeSparsityCore.Parameters.Regime.k_le_five_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.k_le_five_r

/-- info: 'LargeSparsityCore.Parameters.Regime.qstar_mul_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.qstar_mul_r

/-- info: 'LargeSparsityCore.Parameters.Regime.qk_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Parameters.Regime.qk_le

/-! ### The abstract core (`Core`) -/

/-- info: 'LargeSparsityCore.Core.adjoint_R1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Core.adjoint_R1

/-- info: 'LargeSparsityCore.Core.adjoint_R1_comp_R1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Core.adjoint_R1_comp_R1

/-- info: 'LargeSparsityCore.Core.endpoint_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Core.endpoint_gram

/-- info: 'LargeSparsityCore.Core.endpoint_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Core.endpoint_sq_le

/-- info: 'LargeSparsityCore.Core.norm_le_one_of_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Core.norm_le_one_of_isometry

/-- info: 'LargeSparsityCore.Core.sign_comp_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Core.sign_comp_output

/-- info: 'LargeSparsityCore.Core.sign_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Core.sign_adjoint

/-- info: 'LargeSparsityCore.Core.sign_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Core.sign_mul_self

/-- info: 'LargeSparsityCore.Core.sign_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Core.sign_unitary

/-- info: 'LargeSparsityCore.Core.mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Core.mass

/-- info: 'LargeSparsityCore.Core.coeff_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Core.coeff_sum

/-- info: 'LargeSparsityCore.Core.input_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Core.input_isometry

/-- info: 'LargeSparsityCore.Core.output_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Core.output_isometry

/-! ### Clipping and the local frame (`NativeLocal`) -/

/-- info: 'LargeSparsityCore.Native.one_add_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.one_add_pos

/-- info: 'LargeSparsityCore.Native.sub_cclip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.sub_cclip

/-- info: 'LargeSparsityCore.Native.norm_div_eta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_div_eta

/-- info: 'LargeSparsityCore.Native.norm_cclip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_cclip

/-- info: 'LargeSparsityCore.Native.norm_cclip_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_cclip_le

/-- info: 'LargeSparsityCore.Native.mul_norm_cclip_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.mul_norm_cclip_le

/-- info: 'LargeSparsityCore.Native.norm_sub_cclip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_sub_cclip

/-- info: 'LargeSparsityCore.Native.norm_sub_cclip_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_sub_cclip_le

/-- info: 'LargeSparsityCore.Native.norm_sub_cclip_le_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_sub_cclip_le_sq

/-- info: 'LargeSparsityCore.Native.ccorr_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.ccorr_eq

/-- info: 'LargeSparsityCore.Native.norm_ccorr_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_ccorr_le_one

/-- info: 'LargeSparsityCore.Native.norm_ccorr_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_ccorr_le

/-- info: 'LargeSparsityCore.Native.cclip_add_ccorr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.cclip_add_ccorr

/-- info: 'LargeSparsityCore.Native.cclip_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.cclip_zero

/-- info: 'LargeSparsityCore.Native.phase_real_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.phase_real_mul

/-- info: 'LargeSparsityCore.Native.phase_clip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.phase_clip

/-- info: 'LargeSparsityCore.Native.phase_ccorr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.phase_ccorr

/-- info: 'LargeSparsityCore.Native.Ocl_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.Ocl_apply

/-- info: 'LargeSparsityCore.Native.Ocl_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.Ocl_false

/-- info: 'LargeSparsityCore.Native.Ocl_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.Ocl_true

/-- info: 'LargeSparsityCore.Native.Ocl_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.Ocl_congr

/-- info: 'LargeSparsityCore.Native.Ocl_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.Ocl_isometry

/-- info: 'LargeSparsityCore.Native.norm_Ocl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_Ocl

/-- info: 'LargeSparsityCore.Native.facQ_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.facQ_eq

/-- info: 'LargeSparsityCore.Native.inner_Ocl_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.inner_Ocl_sign

/-! ### The joint private operators (`NativeOperators`) -/

/-- info: 'LargeSparsityCore.Native.spectral_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.spectral_conj

/-- info: 'LargeSparsityCore.Native.conj_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.conj_comp

/-- info: 'LargeSparsityCore.Native.conj_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.conj_one

/-- info: 'LargeSparsityCore.Native.conj_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.conj_sub

/-- info: 'LargeSparsityCore.Native.conj_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.conj_isometry

/-- info: 'LargeSparsityCore.Native.R1_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.R1_conj

/-- info: 'LargeSparsityCore.Native.bulk_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.bulk_conj

/-- info: 'LargeSparsityCore.Native.dg_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.dg_apply

/-- info: 'LargeSparsityCore.Native.dg_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.dg_comp

/-- info: 'LargeSparsityCore.Native.dg_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.dg_adjoint

/-- info: 'LargeSparsityCore.Native.dg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.dg_one

/-- info: 'LargeSparsityCore.Native.dg_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.dg_zero

/-- info: 'LargeSparsityCore.Native.dg_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.dg_add

/-- info: 'LargeSparsityCore.Native.dg_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.dg_sub

/-- info: 'LargeSparsityCore.Native.dg_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.dg_smul

/-- info: 'LargeSparsityCore.Native.dg_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.dg_congr

/-- info: 'LargeSparsityCore.Native.norm_dg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_dg_le

/-- info: 'LargeSparsityCore.Native.one_add_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.one_add_ne_zero

/-- info: 'LargeSparsityCore.Native.cay_cayley' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.cay_cayley

/-- info: 'LargeSparsityCore.Native.star_cay_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.star_cay_mul

/-- info: 'LargeSparsityCore.Native.frame_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.frame_unitary

/-- info: 'LargeSparsityCore.Native.frame_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.frame_apply

/-- info: 'LargeSparsityCore.Native.U_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.U_unitary

/-- info: 'LargeSparsityCore.Native.U_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.U_isometry

/-- info: 'LargeSparsityCore.Native.U_coisometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.U_coisometry

/-- info: 'LargeSparsityCore.Native.R1_LamK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.R1_LamK

/-- info: 'LargeSparsityCore.Native.spectral_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.spectral_diag

/-- info: 'LargeSparsityCore.Native.LamD_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.LamD_isometry

/-- info: 'LargeSparsityCore.Native.LamD_coisometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.LamD_coisometry

/-- info: 'LargeSparsityCore.Native.Dop_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.Dop_isometry

/-- info: 'LargeSparsityCore.Native.norm_conj_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_conj_le

/-- info: 'LargeSparsityCore.Native.norm_R1_bulk_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_R1_bulk_le

/-- info: 'LargeSparsityCore.Native.phaseGate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.phaseGate_unitary

/-- info: 'LargeSparsityCore.Native.eval_conj_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.eval_conj_program

/-- info: 'LargeSparsityCore.Native.logicalProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.logicalProgram_count

/-- info: 'LargeSparsityCore.Native.logicalProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.logicalProgram_cost

/-! ### The boundary and its moments (`NativeMoments`) -/

/-- info: 'LargeSparsityCore.Native.cleanF_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.cleanF_apply

/-- info: 'LargeSparsityCore.Native.norm_r2_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_r2_sq

/-- info: 'LargeSparsityCore.Native.norm_cleanF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_cleanF

/-- info: 'LargeSparsityCore.Native.Jin_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.Jin_isometry

/-- info: 'LargeSparsityCore.Native.locator_cleanF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.locator_cleanF

/-- info: 'LargeSparsityCore.Native.value_cleanF_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.value_cleanF_apply

/-- info: 'LargeSparsityCore.Native.gflag_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.gflag_zero

/-- info: 'LargeSparsityCore.Native.gflag_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.gflag_one

/-- info: 'LargeSparsityCore.Native.gflag_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.gflag_two

/-- info: 'LargeSparsityCore.Native.frame_input_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.frame_input_apply

/-- info: 'LargeSparsityCore.Native.inner_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.inner_supported

/-- info: 'LargeSparsityCore.Native.norm_sq_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_sq_supported

/-- info: 'LargeSparsityCore.Native.frame_input_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.frame_input_eq

/-- info: 'LargeSparsityCore.Native.dg_frame_input_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.dg_frame_input_eq

/-- info: 'LargeSparsityCore.Native.inner_dg_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.inner_dg_input

/-- info: 'LargeSparsityCore.Native.norm_dg_input_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_dg_input_sq

/-- info: 'LargeSparsityCore.Native.sum_norm_Psi_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.sum_norm_Psi_sq

/-- info: 'LargeSparsityCore.Native.norm_yv_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_yv_sq

/-- info: 'LargeSparsityCore.Native.edge_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.edge_sum_le

/-- info: 'LargeSparsityCore.Native.c1_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.c1_table

/-- info: 'LargeSparsityCore.Native.c2_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.c2_table

/-- info: 'LargeSparsityCore.Native.Promise.entry_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.Promise.entry_le

/-- info: 'LargeSparsityCore.Native.c2_sums' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.c2_sums

/-- info: 'LargeSparsityCore.Native.c1_sums' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.c1_sums

/-- info: 'LargeSparsityCore.Native.norm_gflag_zero_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_gflag_zero_sq

/-- info: 'LargeSparsityCore.Native.norm_gflag_two_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_gflag_two_sq

/-- info: 'LargeSparsityCore.Native.U_adjoint_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.U_adjoint_norm

/-- info: 'LargeSparsityCore.Native.norm_dg_input_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_dg_input_sq_le

/-- info: 'LargeSparsityCore.Native.norm_Ppl_input_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_Ppl_input_sq_le

/-- info: 'LargeSparsityCore.Native.norm_Pmi_input_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_Pmi_input_sq_le

/-- info: 'LargeSparsityCore.Native.Kbulk_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.Kbulk_eq

/-- info: 'LargeSparsityCore.Native.norm_bulk_input_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_bulk_input_sq_le

/-- info: 'LargeSparsityCore.Native.norm_K_input_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_K_input_sq_le

/-- info: 'LargeSparsityCore.Native.inner_signQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.inner_signQ

/-- info: 'LargeSparsityCore.Native.generator_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.generator_add

/-- info: 'LargeSparsityCore.Native.flag_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.flag_term

/-- info: 'LargeSparsityCore.Native.kappa_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.kappa_eq

/-- info: 'LargeSparsityCore.Native.edge_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.edge_term

/-- info: 'LargeSparsityCore.Native.inner_entryGenerator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.inner_entryGenerator

/-- info: 'LargeSparsityCore.Native.inner_input_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.inner_input_K

/-- info: 'LargeSparsityCore.Native.Mjoint_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.Mjoint_eq

/-! ### The native core (`NativeCore`) -/

/-- info: 'LargeSparsityCore.Native.opNorm_le_of_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.opNorm_le_of_sq

/-- info: 'LargeSparsityCore.Native.physProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.physProgram_intertwines

/-- info: 'LargeSparsityCore.Native.input_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.input_isometry

/-- info: 'LargeSparsityCore.Native.matrixOperator_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.matrixOperator_star

/-! ### The joint representation at a separate entry scale (`NativeTwoNorm`) -/

/-- info: 'LargeSparsityCore.Native.c2_sums_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.c2_sums_ratio

/-- info: 'LargeSparsityCore.Native.c1_sums_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.c1_sums_ratio

/-- info: 'LargeSparsityCore.Native.norm_Ppl_input_sq_le_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_Ppl_input_sq_le_ratio

/-- info: 'LargeSparsityCore.Native.norm_Pmi_input_sq_le_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_Pmi_input_sq_le_ratio

/-- info: 'LargeSparsityCore.Native.norm_bulk_input_sq_le_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_bulk_input_sq_le_ratio

/-- info: 'LargeSparsityCore.Native.norm_K_input_sq_le_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.norm_K_input_sq_le_ratio

/-- info: 'LargeSparsityCore.Native.Mjoint_eq_of_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.Mjoint_eq_of_entry

/-- info: 'LargeSparsityCore.Native.compression_of_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.compression_of_entry

/-! ### The native core at a separate entry scale (`NativeTwoNormCore`) -/

/-- info: 'LargeSparsityCore.Native.ratio_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.ratio_div

/-- info: 'LargeSparsityCore.Native.inputS_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LargeSparsityCore.Native.inputS_isometry
