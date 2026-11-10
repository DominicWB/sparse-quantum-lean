import ManuscriptConformance.Defs
import ManuscriptConformance.Readout
import ManuscriptConformance.Hamiltonian
import ManuscriptConformance.HamiltonianLower
import ManuscriptConformance.LinearSystemUpper
import ManuscriptConformance.LinearSystemLower
import ManuscriptConformance.LinearSystemSeparate
import ManuscriptConformance.ODEUpper
import ManuscriptConformance.ODELower
import ManuscriptConformance.ODELowerAdaptive
import ManuscriptConformance.ODETime
import ManuscriptConformance.ODEGeneral
import ManuscriptConformance.Appendix
import ManuscriptConformance.GateDefs
import ManuscriptConformance.GateMain
import ManuscriptConformance.GateHamiltonian
import ManuscriptConformance.GateODE
import ManuscriptConformance.GateODETime
import ManuscriptConformance.GateProps
import ManuscriptConformance.GateGeneralDefs
import ManuscriptConformance.GateGeneral
import ManuscriptConformance.GateDecoderDefs
import ManuscriptConformance.GateDecoder
import ManuscriptConformance.GateMainDecoder
import ManuscriptConformance.GateDecoderTables
import ManuscriptConformance.GateDecoderBinary
import ManuscriptConformance.GateODEGeneral
import ManuscriptConformance.GateODETimeGeneral
import ManuscriptConformance.GateODEDecoder
import ManuscriptConformance.GateODETimeCert
import ManuscriptConformance.GateODETimeCertValid
import ManuscriptConformance.ActualRuns
import ManuscriptConformance.BranchCertificates
import ManuscriptConformance.SourceExecutions
import ManuscriptConformance.EntrywiseCayley
import ManuscriptConformance.SourceExecutionsMore
import ManuscriptConformance.GateODETimeCertFinite
import ManuscriptConformance.GateDecoderTiny
import ManuscriptConformance.TaggedPairEntry
import ManuscriptConformance.TaggedPairSimulation
import ManuscriptConformance.WriterAccess
import ManuscriptConformance.WriterEndpoints
import ManuscriptConformance.WriterProtocols
import ManuscriptConformance.WriterProtocolEndpoints
import ManuscriptConformance.WriterSeparate
import ManuscriptConformance.GatePropsSelective
import ManuscriptConformance.GatePropsKnown
import ManuscriptConformance.WriterTimeEndpoints
import ManuscriptConformance.WriterGeneralEndpoint
import ManuscriptConformance.WriterTimeVariants
import ManuscriptConformance.ApproxRuns
import ManuscriptConformance.WriterGateAccess
import ManuscriptConformance.WriterGates
import ManuscriptConformance.WriterGatesDecoder
import ManuscriptConformance.WriterODEGates
import ManuscriptConformance.WriterODETimeGates
import ManuscriptConformance.WriterODECert
import ManuscriptConformance.WriterODESources
import ManuscriptConformance.WriterGeneralZero
import ManuscriptConformance.WriterDecoderAccess
import ManuscriptConformance.WriterDecoderODE
import ManuscriptConformance.WriterDecoderCert
import ManuscriptConformance.WriterDecoderSources
import ManuscriptConformance.WriterBranchCerts
import ManuscriptConformance.WriterGateVariants
import ManuscriptConformance.PrepColumn
import ManuscriptConformance.PrepLoader
import ManuscriptConformance.SourceLoaderColumns
import ManuscriptConformance.MeshLoaderColumns
import ManuscriptConformance.RobustLoaderColumns
import ManuscriptConformance.DysonLoaderColumns
import ManuscriptConformance.DysonLoaderActual
import ManuscriptConformance.TimeLoaderColumns
import ManuscriptConformance.TimeLoaderRuns
import ManuscriptConformance.TimeLoaderBranch
import ManuscriptConformance.LoaderApprox
import ManuscriptConformance.TimeLoaderApprox
import ManuscriptConformance.TimeLoaderBranchApprox

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover every public theorem of the library (857 theorems),
beginning with the conformance theorems of the summary table of `Statements`, then in module order;
the theorems of `ActualRuns`, `BranchCertificates`, `SourceExecutions`, `EntrywiseCayley`,
`SourceExecutionsMore`, `GateODETimeCertFinite`, `GateDecoderTiny`, `TaggedPairEntry`,
`TaggedPairSimulation`, `WriterAccess`, `WriterProtocols`, `WriterEndpoints`,
`WriterProtocolEndpoints`, `GatePropsSelective`, `GatePropsKnown`, `WriterTimeEndpoints`,
`WriterGeneralEndpoint`, `WriterTimeVariants`, `ApproxRuns`, `WriterGateAccess`, `WriterGates`,
`WriterGatesDecoder`, `WriterODEGates`, `WriterODETimeGates`, `WriterODECert`, `WriterODESources`,
`WriterGeneralZero`, `WriterDecoderAccess`, `WriterDecoderODE`, `WriterDecoderCert`,
`WriterDecoderSources`, `WriterBranchCerts`, `WriterGateVariants`, `PrepColumn`, `PrepLoader`,
`SourceLoaderColumns`, `MeshLoaderColumns`, `RobustLoaderColumns`, `DysonLoaderColumns`,
`DysonLoaderActual`, `TimeLoaderColumns`, `TimeLoaderRuns`, `TimeLoaderBranch`, `LoaderApprox`,
`TimeLoaderApprox` and `TimeLoaderBranchApprox` (their summary-table theorems included) are in
their own sections at the end. 845 reports
list exactly `propext`, `Classical.choice` and `Quot.sound`; the other 12 list a strict subset. -/

/-! ### The conformance theorems of the summary table -/

/-- info: 'ManuscriptConformance.hs_thm_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_main

/-- info: 'ManuscriptConformance.hs_thm_main_spectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_main_spectral

/-- info: 'ManuscriptConformance.hs_thm_main_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_main_zero

/-- info: 'ManuscriptConformance.hs_thm_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_time

/-- info: 'ManuscriptConformance.hs_thm_time_mesh_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_time_mesh_exists

/-- info: 'ManuscriptConformance.hs_thm_time_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_time_zero

/-- info: 'ManuscriptConformance.hs_thm_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_optimal

/-- info: 'ManuscriptConformance.hs_thm_optimal_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_optimal_theta

/-- info: 'ManuscriptConformance.hs_thm_two_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_two_norm

/-- info: 'ManuscriptConformance.gate_thm_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_thm_main

/-- info: 'ManuscriptConformance.gate_thm_main_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_thm_main_general

/-- info: 'ManuscriptConformance.gate_thm_main_decoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_thm_main_decoder

/-- info: 'ManuscriptConformance.gate_thm_main_decoder_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_thm_main_decoder_tables

/-- info: 'ManuscriptConformance.gate_thm_main_general_of_decoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_thm_main_general_of_decoder

/-- info: 'ManuscriptConformance.hs_cor_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_cor_unitary

/-- info: 'ManuscriptConformance.hs_cor_unitary_inexact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_cor_unitary_inexact

/-- info: 'ManuscriptConformance.hs_cor_unitary_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_cor_unitary_theta

/-- info: 'ManuscriptConformance.hs_cor_unitary_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_cor_unitary_optimal

/-- info: 'ManuscriptConformance.hs_cor_unitary_optimal_inexact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_cor_unitary_optimal_inexact

/-- info: 'ManuscriptConformance.hs_thm_gates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_gates

/-- info: 'ManuscriptConformance.hs_thm_gates_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_gates_general

/-- info: 'ManuscriptConformance.hs_thm_gates_decoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_gates_decoder

/-- info: 'ManuscriptConformance.hs_thm_gates_decoder_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_gates_decoder_tables

/-- info: 'ManuscriptConformance.hs_thm_gates_general_of_decoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_gates_general_of_decoder

/-- info: 'ManuscriptConformance.hsl_thm_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hsl_thm_main

/-- info: 'ManuscriptConformance.hsl_cor_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hsl_cor_power

/-- info: 'ManuscriptConformance.hsl_prop_two_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hsl_prop_two_norm

/-- info: 'ManuscriptConformance.ode_thm_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_main

/-- info: 'ManuscriptConformance.ode_thm_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_time

/-- info: 'ManuscriptConformance.ode_thm_time_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_time_approx

/-- info: 'ManuscriptConformance.ode_thm_time_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_time_clock

/-- info: 'ManuscriptConformance.ode_thm_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_general

/-- info: 'ManuscriptConformance.ode_thm_general_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_general_zero

/-- info: 'ManuscriptConformance.ode_thm_gates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates

/-- info: 'ManuscriptConformance.ode_thm_gates_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_general

/-- info: 'ManuscriptConformance.ode_thm_gates_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time

/-- info: 'ManuscriptConformance.ode_thm_gates_time_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_general

/-- info: 'ManuscriptConformance.ode_thm_gates_decoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_decoder

/-- info: 'ManuscriptConformance.ode_thm_gates_time_decoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_decoder

/-- info: 'ManuscriptConformance.ode_thm_gates_time_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_cert

/-- info: 'ManuscriptConformance.ode_thm_gates_time_decoder_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_decoder_cert

/-- info: 'ManuscriptConformance.ode_thm_gates_time_cert_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_cert_valid

/-- info: 'ManuscriptConformance.ode_thm_gates_time_decoder_cert_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_decoder_cert_valid

/-- info: 'ManuscriptConformance.gate_select_sample_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_select_sample_certificate

/-- info: 'ManuscriptConformance.odel_thm_combined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.odel_thm_combined

/-- info: 'ManuscriptConformance.odel_thm_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.odel_thm_joint

/-- info: 'ManuscriptConformance.odel_rem_homogeneous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.odel_rem_homogeneous

/-- info: 'ManuscriptConformance.odel_thm_psd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.odel_thm_psd

/-- info: 'ManuscriptConformance.odel_thm_combined_adaptive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.odel_thm_combined_adaptive

/-- info: 'ManuscriptConformance.odel_thm_joint_adaptive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.odel_thm_joint_adaptive

/-- info: 'ManuscriptConformance.odel_rem_homogeneous_adaptive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.odel_rem_homogeneous_adaptive

/-- info: 'ManuscriptConformance.odel_thm_psd_adaptive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.odel_thm_psd_adaptive

/-- info: 'ManuscriptConformance.qls_thm_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.qls_thm_main

/-- info: 'ManuscriptConformance.qls_prop_chebyshev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.qls_prop_chebyshev

/-- info: 'ManuscriptConformance.qls_cor_separate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.qls_cor_separate

/-- info: 'ManuscriptConformance.qlsl_thm_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.qlsl_thm_main

/-- info: 'ManuscriptConformance.opt_thm_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.opt_thm_signed

/-- info: 'ManuscriptConformance.opt_thm_signed_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.opt_thm_signed_identity

/-- info: 'ManuscriptConformance.opt_thm_weights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.opt_thm_weights

/-- info: 'ManuscriptConformance.opt_prop_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.opt_prop_core

/-- info: 'ManuscriptConformance.gate_prop_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_prop_finite

/-- info: 'ManuscriptConformance.gate_prop_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_prop_signed

/-- info: 'ManuscriptConformance.gate_prop_signed_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_prop_signed_native

/-- info: 'ManuscriptConformance.gate_prop_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_prop_core

/-- info: 'ManuscriptConformance.gate_prop_core_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_prop_core_native

/-! ### Quantities and error notions (`Defs`, `Readout`) -/

/-- info: 'ManuscriptConformance.fullOutputError_of_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.fullOutputError_of_norm

/-- info: 'ManuscriptConformance.referenceOutputError_of_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.referenceOutputError_of_norm

/-- info: 'ManuscriptConformance.abs_corr_sub_le_of_traceDistanceLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.abs_corr_sub_le_of_traceDistanceLE

/-- info: 'ManuscriptConformance.reducedDensity_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.reducedDensity_isHermitian

/-- info: 'ManuscriptConformance.systemState_isSelfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.systemState_isSelfAdjoint

/-- info: 'ManuscriptConformance.systemState_sub_pure_isSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.systemState_sub_pure_isSymmetric

/-- info: 'ManuscriptConformance.trace_toEuclideanCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.trace_toEuclideanCLM

/-- info: 'ManuscriptConformance.trace_comp_systemState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.trace_comp_systemState

/-- info: 'ManuscriptConformance.corr_systemState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.corr_systemState

/-- info: 'ManuscriptConformance.accurate_of_traceDistanceLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.accurate_of_traceDistanceLE

/-- info: 'ManuscriptConformance.heraldedAccurate_of_traceDistanceLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.heraldedAccurate_of_traceDistanceLE

/-! ### Hamiltonian simulation (`Hamiltonian`, `HamiltonianLower`) -/

/-- info: 'ManuscriptConformance.rb_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.rb_eq

/-- info: 'ManuscriptConformance.optimal_bound_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.optimal_bound_eq

/-- info: 'ManuscriptConformance.hsR_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hsR_eq

/-- info: 'ManuscriptConformance.lower_shape_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.lower_shape_eq

/-- info: 'ManuscriptConformance.twoNorm_bound_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.twoNorm_bound_eq

/-- info: 'ManuscriptConformance.unitary_bound_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.unitary_bound_eq

/-- info: 'ManuscriptConformance.unitary_optimal_bound_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.unitary_optimal_bound_eq

/-- info: 'ManuscriptConformance.le_count_of_le_labelCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.le_count_of_le_labelCount

/-- info: 'ManuscriptConformance.exists_cheap_of_not_forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.exists_cheap_of_not_forces

/-- info: 'ManuscriptConformance.hsR_eq_hslR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hsR_eq_hslR

/-! ### Linear systems (`LinearSystemUpper`, `LinearSystemLower`) -/

/-- info: 'ManuscriptConformance.filterFun_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.filterFun_eq

/-! ### Dissipative and general ODEs (`ODEUpper`, `ODELower`, `ODETime`, `ODEGeneral`) -/

/-- info: 'ManuscriptConformance.traceDistanceLE_of_runsClose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.traceDistanceLE_of_runsClose

/-- info: 'ManuscriptConformance.runsClose_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.runsClose_of_certificate

/-- info: 'ManuscriptConformance.forcesODE_of_forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.forcesODE_of_forces

/-- info: 'ManuscriptConformance.ForcesODE.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ForcesODE.mono

/-- info: 'ManuscriptConformance.hamFamily_conformance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hamFamily_conformance

/-- info: 'ManuscriptConformance.joint_conformance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.joint_conformance

/-- info: 'ManuscriptConformance.time_log_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.time_log_eq

/-- info: 'ManuscriptConformance.cleanErr_of_fullOutputError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.cleanErr_of_fullOutputError

/-! ### The optimal-precision appendix (`Appendix`) -/

/-- info: 'ManuscriptConformance.signedR_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.signedR_nonneg

/-- info: 'ManuscriptConformance.signedBound_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.signedBound_nonneg

/-- info: 'ManuscriptConformance.rb_eq_signedR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.rb_eq_signedR

/-- info: 'ManuscriptConformance.knownOf_Cop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.knownOf_Cop

/-- info: 'ManuscriptConformance.knownOf_Dop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.knownOf_Dop

/-- info: 'ManuscriptConformance.xi_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.xi_eq

/-- info: 'ManuscriptConformance.Rfun_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.Rfun_eq

/-- info: 'ManuscriptConformance.ces_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ces_eq

/-! ### The gate model and the gate-level results (`GateDefs`, `GateMain`, `GateHamiltonian`, `GateODE`, `GateODETime`, `GateProps`) -/

/-- info: 'ManuscriptConformance.cleanAlong_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.cleanAlong_apply

/-- info: 'ManuscriptConformance.cleanEmb_sysEmb_io' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.cleanEmb_sysEmb_io

/-- info: 'ManuscriptConformance.card_eq_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.card_eq_two_pow

/-- info: 'ManuscriptConformance.synthesis_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.synthesis_of_parts

/-- info: 'ManuscriptConformance.qmu_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.qmu_eq

/-- info: 'ManuscriptConformance.one_le_div_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.one_le_div_of_le

/-- info: 'ManuscriptConformance.logb_nonneg_of_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.logb_nonneg_of_one_le

/-- info: 'ManuscriptConformance.mesh_label_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.mesh_label_words

/-- info: 'ManuscriptConformance.synth_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.synth_factor

/-- info: 'ManuscriptConformance.logb_inv_xi_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.logb_inv_xi_le

/-- info: 'ManuscriptConformance.bd_words_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.bd_words_le

/-- info: 'ManuscriptConformance.bd_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.bd_cost_le

/-- info: 'ManuscriptConformance.sg_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.sg_cost_le

/-- info: 'ManuscriptConformance.cl_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.cl_cost_le

/-- info: 'ManuscriptConformance.claims_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.claims_poly

/-- info: 'ManuscriptConformance.shape_half_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.shape_half_le

/-- info: 'ManuscriptConformance.shape_ge_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.shape_ge_half

/-- info: 'ManuscriptConformance.synth_factor'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.synth_factor'

/-- info: 'ManuscriptConformance.hs_words_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_words_le

/-- info: 'ManuscriptConformance.neg_time_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.neg_time_error

/-- info: 'ManuscriptConformance.shape_eq_mainBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.shape_eq_mainBound

/-- info: 'ManuscriptConformance.odeShape_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.odeShape_eq

/-- info: 'ManuscriptConformance.hasBits_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hasBits_one

/-- info: 'ManuscriptConformance.odePub_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.odePub_ok

/-- info: 'ManuscriptConformance.odePub_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.odePub_gamma

/-- info: 'ManuscriptConformance.odePub_zeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.odePub_zeta

/-- info: 'ManuscriptConformance.one_le_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.one_le_two_mul

/-- info: 'ManuscriptConformance.odePubT_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.odePubT_ok

/-- info: 'ManuscriptConformance.odePubT_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.odePubT_gamma

/-- info: 'ManuscriptConformance.odePubT_zeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.odePubT_zeta

/-- info: 'ManuscriptConformance.sg_nPriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.sg_nPriv

/-- info: 'ManuscriptConformance.secOK_clipCircuit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.secOK_clipCircuit

/-! ### Sparse access of general size in the gate theorems (`GateGeneralDefs`, `GateGeneral`) -/

/-- info: 'ManuscriptConformance.cleanAlong_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.cleanAlong_trans

/-- info: 'ManuscriptConformance.cleanAlong_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.cleanAlong_inl

/-- info: 'ManuscriptConformance.norm_cleanAlong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.norm_cleanAlong

/-- info: 'ManuscriptConformance.norm_cleanAlong_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.norm_cleanAlong_le

/-- info: 'ManuscriptConformance.cleanAlong_castSucc_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.cleanAlong_castSucc_apply

/-- info: 'ManuscriptConformance.sum_mark_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.sum_mark_false

/-- info: 'ManuscriptConformance.matOp_padData_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.matOp_padData_comp

/-- info: 'ManuscriptConformance.exp_padData_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.exp_padData_comp

/-- info: 'ManuscriptConformance.norm_le_of_fullOutputError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.norm_le_of_fullOutputError

/-- info: 'ManuscriptConformance.fullOutputError_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.fullOutputError_apply_le

/-- info: 'ManuscriptConformance.ofBits_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ofBits_false

/-- info: 'ManuscriptConformance.twos_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.twos_false

/-- info: 'ManuscriptConformance.gauss_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gauss_false

/-- info: 'ManuscriptConformance.padFormat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.padFormat

/-- info: 'ManuscriptConformance.card_AW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.card_AW

/-- info: 'ManuscriptConformance.cleanAlong_genSys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.cleanAlong_genSys

/-- info: 'ManuscriptConformance.genCirc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.genCirc_spec

/-- info: 'ManuscriptConformance.genCirc_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.genCirc_error

/-- info: 'ManuscriptConformance.BinaryDecoder.zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.BinaryDecoder.zero

/-- info: 'ManuscriptConformance.sqrt_le_two_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.sqrt_le_two_mul_sqrt

/-- info: 'ManuscriptConformance.k_le_logb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.k_le_logb

/-- info: 'ManuscriptConformance.logb_pow_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.logb_pow_succ_le

/-- info: 'ManuscriptConformance.logb_sP_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.logb_sP_le

/-- info: 'ManuscriptConformance.logb_scale_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.logb_scale_le

/-- info: 'ManuscriptConformance.logInv_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.logInv_nonneg

/-- info: 'ManuscriptConformance.mainBound_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.mainBound_le_of_le

/-- info: 'ManuscriptConformance.mainBound_pad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.mainBound_pad_le

/-- info: 'ManuscriptConformance.twoNormBound_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.twoNormBound_le_of_le

/-- info: 'ManuscriptConformance.gen_gates_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gen_gates_le

/-- info: 'ManuscriptConformance.arith_bound_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.arith_bound_succ

/-- info: 'ManuscriptConformance.comp_signedArith_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.comp_signedArith_succ

/-- info: 'ManuscriptConformance.comp_clipArith_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.comp_clipArith_succ

/-- info: 'ManuscriptConformance.le_twoNormBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.le_twoNormBound

/-! ### General decoders in the gate theorems (`GateDecoderDefs`, `GateDecoder`, `GateMainDecoder`, `GateDecoderTables`, `GateDecoderBinary`) -/

/-- info: 'ManuscriptConformance.matOp_padForm_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.matOp_padForm_comp

/-- info: 'ManuscriptConformance.exp_padForm_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.exp_padForm_comp

/-- info: 'ManuscriptConformance.genCircE_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.genCircE_spec

/-- info: 'ManuscriptConformance.genCircE_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.genCircE_error

/-- info: 'ManuscriptConformance.hs_gates_dataDec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_gates_dataDec

/-- info: 'ManuscriptConformance.padDataE_decode_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.padDataE_decode_flag

/-- info: 'ManuscriptConformance.comp_decArith_padDataE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.comp_decArith_padDataE

/-- info: 'ManuscriptConformance.comp_rotArith_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.comp_rotArith_mono

/-- info: 'ManuscriptConformance.comp_decArith_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.comp_decArith_mono

/-- info: 'ManuscriptConformance.wrap_bound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.wrap_bound_le

/-- info: 'ManuscriptConformance.comp_signedArithD_padDataE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.comp_signedArithD_padDataE

/-- info: 'ManuscriptConformance.comp_clipArithD_padDataE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.comp_clipArithD_padDataE

/-- info: 'ManuscriptConformance.qval_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.qval_nonneg

/-- info: 'ManuscriptConformance.bd_cost_leD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.bd_cost_leD

/-- info: 'ManuscriptConformance.sg_cost_leD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.sg_cost_leD

/-- info: 'ManuscriptConformance.cl_cost_leD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.cl_cost_leD

/-- info: 'ManuscriptConformance.gate_main_dataDec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_main_dataDec

/-- info: 'ManuscriptConformance.comp_rotArith_cmono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.comp_rotArith_cmono

/-- info: 'ManuscriptConformance.comp_signedArithV_cmono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.comp_signedArithV_cmono

/-- info: 'ManuscriptConformance.comp_clipArithV_cmono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.comp_clipArithV_cmono

/-- info: 'ManuscriptConformance.tableConst_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.tableConst_nonneg

/-- info: 'ManuscriptConformance.tableConst_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.tableConst_eq

/-- info: 'ManuscriptConformance.tableConst_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.tableConst_mono

/-- info: 'ManuscriptConformance.table_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.table_bound

/-- info: 'ManuscriptConformance.comp_rotArith_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.comp_rotArith_tables

/-- info: 'ManuscriptConformance.comp_signedArithV_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.comp_signedArithV_tables

/-- info: 'ManuscriptConformance.comp_clipArithV_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.comp_clipArithV_tables

/-- info: 'ManuscriptConformance.cordicArith_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.cordicArith_rot

/-- info: 'ManuscriptConformance.cordicArith_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.cordicArith_cost_le

/-- info: 'ManuscriptConformance.sumElim_inl_inr_injective' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.sumElim_inl_inr_injective

/-- info: 'ManuscriptConformance.rotWordArith_cordic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.rotWordArith_cordic

/-- info: 'ManuscriptConformance.comp_rotArith_binary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.comp_rotArith_binary

/-- info: 'ManuscriptConformance.comp_signedArithV_binary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.comp_signedArithV_binary

/-- info: 'ManuscriptConformance.comp_clipArithV_binary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.comp_clipArithV_binary

/-- info: 'ManuscriptConformance.pow_le_pow_of_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.pow_le_pow_of_word

/-- info: 'ManuscriptConformance.comp_rotArith_dmono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.comp_rotArith_dmono

/-- info: 'ManuscriptConformance.comp_signedArithV_dmono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.comp_signedArithV_dmono

/-- info: 'ManuscriptConformance.comp_clipArithV_dmono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.comp_clipArithV_dmono

/-! ### Sparse access of general size in the ODE gate theorems (`GateODEGeneral`, `GateODETimeGeneral`) -/

/-- info: 'ManuscriptConformance.odePubG_pub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.odePubG_pub

/-- info: 'ManuscriptConformance.markEmb_eq_cleanAlong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.markEmb_eq_cleanAlong

/-- info: 'ManuscriptConformance.qOf_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.qOf_le_of_le

/-- info: 'ManuscriptConformance.bitB_pad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.bitB_pad_le

/-- info: 'ManuscriptConformance.cube_pad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.cube_pad_le

/-- info: 'ManuscriptConformance.odePubTG_pub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.odePubTG_pub

/-- info: 'ManuscriptConformance.qOf_two_le0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.qOf_two_le0

/-- info: 'ManuscriptConformance.bitB_padT_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.bitB_padT_le

/-- info: 'ManuscriptConformance.cube_padT_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.cube_padT_le

/-! ### General decoders in the ODE gate theorems (`GateODEDecoder`) -/

/-- info: 'ManuscriptConformance.binaryEntryDecoding_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.binaryEntryDecoding_copy

/-- info: 'ManuscriptConformance.exists_binaryEntryDecoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.exists_binaryEntryDecoding

/-! ### The manuscript's certificates in the time-dependent ODE gate theorems (`GateODETimeCert`, `GateODETimeCertValid`) -/

/-- info: 'ManuscriptConformance.odeShape_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.odeShape_two_le

/-- info: 'ManuscriptConformance.bitB_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.bitB_two_le

/-- info: 'ManuscriptConformance.cube_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.cube_two_le

/-- info: 'ManuscriptConformance.gates_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gates_two_le

/-- info: 'ManuscriptConformance.calls_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.calls_two_le

/-- info: 'ManuscriptConformance.odePubT_zeta2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.odePubT_zeta2

/-! ### Accuracy of the actual runs (`ActualRuns`) -/

/-- info: 'ManuscriptConformance.trialsClose_of_trialCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.trialsClose_of_trialCertificate

/-- info: 'ManuscriptConformance.trialsClose_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.trialsClose_of_certificate

/-- info: 'ManuscriptConformance.trialsClose_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.trialsClose_congr

/-- info: 'ManuscriptConformance.historiesClose_of_trialsClose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.historiesClose_of_trialsClose

/-- info: 'ManuscriptConformance.runsClose_of_historiesClose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.runsClose_of_historiesClose

/-- info: 'ManuscriptConformance.diagE₀_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.diagE₀_apply

/-- info: 'ManuscriptConformance.diagE₁_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.diagE₁_apply

/-- info: 'ManuscriptConformance.diagAlt_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.diagAlt_apply

/-- info: 'ManuscriptConformance.diagDensity_eq_alt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.diagDensity_eq_alt

/-- info: 'ManuscriptConformance.diag_branch_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.diag_branch_far

/-- info: 'ManuscriptConformance.diagAlt_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.diagAlt_close

/-- info: 'ManuscriptConformance.diagAlt_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.diagAlt_norm

/-- info: 'ManuscriptConformance.runsClose_diagnostic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.runsClose_diagnostic

/-- info: 'ManuscriptConformance.ode_thm_main_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_main_actual

/-- info: 'ManuscriptConformance.ode_thm_time_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_time_actual

/-! ### Certificates on the opposite branches (`BranchCertificates`) -/

/-- info: 'ManuscriptConformance.lchs_add_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.lchs_add_neg

/-- info: 'ManuscriptConformance.lchs_sub_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.lchs_sub_neg

/-- info: 'ManuscriptConformance.hamiltonianPart_eq_branches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hamiltonianPart_eq_branches

/-- info: 'ManuscriptConformance.dissipativePart_eq_branches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.dissipativePart_eq_branches

/-- info: 'ManuscriptConformance.lchs_sub_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.lchs_sub_eq

/-- info: 'ManuscriptConformance.norm_branch_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.norm_branch_eq

/-- info: 'ManuscriptConformance.norm_hamiltonianPart_le_branches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.norm_hamiltonianPart_le_branches

/-- info: 'ManuscriptConformance.norm_dissipativePart_le_branches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.norm_dissipativePart_le_branches

/-- info: 'ManuscriptConformance.norm_le_branches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.norm_le_branches

/-- info: 'ManuscriptConformance.branch_intervalIntegrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.branch_intervalIntegrable

/-- info: 'ManuscriptConformance.cell_dissipative_le_branches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.cell_dissipative_le_branches

/-- info: 'ManuscriptConformance.cell_norm_le_branches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.cell_norm_le_branches

/-- info: 'ManuscriptConformance.branchErr_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.branchErr_nonneg

/-- info: 'ManuscriptConformance.dissErr_le_branchSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.dissErr_le_branchSum

/-- info: 'ManuscriptConformance.sampleErr_le_branchSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.sampleErr_le_branchSum

/-- info: 'ManuscriptConformance.budgets_of_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.budgets_of_branch

/-- info: 'ManuscriptConformance.gate_budgets_of_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_budgets_of_branch

/-- info: 'ManuscriptConformance.sampleError_eq_sampleErr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.sampleError_eq_sampleErr

/-- info: 'ManuscriptConformance.dissipativeError_eq_dissErr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.dissipativeError_eq_dissErr

/-- info: 'ManuscriptConformance.time_budgets_of_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.time_budgets_of_branch

/-- info: 'ManuscriptConformance.ode_thm_time_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_time_branch

/-- info: 'ManuscriptConformance.ode_thm_time_approx_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_time_approx_branch

/-- info: 'ManuscriptConformance.ode_thm_time_actual_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_time_actual_branch

/-- info: 'ManuscriptConformance.ode_thm_gates_time_cert_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_cert_branch

/-- info: 'ManuscriptConformance.ode_thm_gates_time_decoder_cert_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_decoder_cert_branch

/-- info: 'ManuscriptConformance.ode_thm_gates_time_cert_valid_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_cert_valid_branch

/-- info: 'ManuscriptConformance.ode_thm_gates_time_decoder_cert_valid_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_decoder_cert_valid_branch

/-- info: 'ManuscriptConformance.cellError_le_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.cellError_le_branch

/-- info: 'ManuscriptConformance.fullValidAt_of_branch_clipped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.fullValidAt_of_branch_clipped

/-- info: 'ManuscriptConformance.fullValidAt_of_branch_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.fullValidAt_of_branch_raw

/-- info: 'ManuscriptConformance.fullValid_of_branch_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.fullValid_of_branch_raw

/-- info: 'ManuscriptConformance.growC_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.growC_parts

/-- info: 'ManuscriptConformance.norm_real_smul_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.norm_real_smul_one

/-- info: 'ManuscriptConformance.umesh_sum_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.umesh_sum_const

/-- info: 'ManuscriptConformance.growC_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.growC_values

/-- info: 'ManuscriptConformance.nonaccretive_branch_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nonaccretive_branch_accepted

/-! ### Source executions after native macro expansion (`SourceExecutions`) -/

/-- info: 'ManuscriptConformance.aflat_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aflat_nil

/-- info: 'ManuscriptConformance.aflat_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aflat_cons

/-- info: 'ManuscriptConformance.aflat_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aflat_append

/-- info: 'ManuscriptConformance.aflat_flatten_replicate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aflat_flatten_replicate

/-- info: 'ManuscriptConformance.aflat_ainv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aflat_ainv

/-- info: 'ManuscriptConformance.flipTag_beq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.flipTag_beq

/-- info: 'ManuscriptConformance.nexec_ainv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nexec_ainv

/-- info: 'ManuscriptConformance.nexec_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nexec_nil

/-- info: 'ManuscriptConformance.nexec_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nexec_cons

/-- info: 'ManuscriptConformance.nexec_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nexec_append

/-- info: 'ManuscriptConformance.nexec_flatten_replicate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nexec_flatten_replicate

/-- info: 'ManuscriptConformance.nexec_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nexec_none

/-- info: 'ManuscriptConformance.aerase_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aerase_append

/-- info: 'ManuscriptConformance.aerase_flatten_replicate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aerase_flatten_replicate

/-- info: 'ManuscriptConformance.aerase_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aerase_none

/-- info: 'ManuscriptConformance.aerase_ainv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aerase_ainv

/-- info: 'ManuscriptConformance.annotOK_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.annotOK_append

/-- info: 'ManuscriptConformance.annotOK_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.annotOK_none

/-- info: 'ManuscriptConformance.annotOK_flatten_replicate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.annotOK_flatten_replicate

/-- info: 'ManuscriptConformance.annotOK_ainv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.annotOK_ainv

/-- info: 'ManuscriptConformance.nCallsN_aflat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nCallsN_aflat

/-- info: 'ManuscriptConformance.nGatesN_aflat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nGatesN_aflat

/-- info: 'ManuscriptConformance.aflat_annotOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aflat_annotOf

/-- info: 'ManuscriptConformance.annotOK_annotOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.annotOK_annotOf

/-- info: 'ManuscriptConformance.nexec_annotOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nexec_annotOf

/-- info: 'ManuscriptConformance.aerase_annotOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aerase_annotOf

/-- info: 'ManuscriptConformance.aflat_astep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aflat_astep

/-- info: 'ManuscriptConformance.aflat_atrial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aflat_atrial

/-- info: 'ManuscriptConformance.nexec_astep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nexec_astep

/-- info: 'ManuscriptConformance.nexec_atrial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nexec_atrial

/-- info: 'ManuscriptConformance.nexec_atrial_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nexec_atrial_both

/-- info: 'ManuscriptConformance.aerase_astep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aerase_astep

/-- info: 'ManuscriptConformance.aerase_atrial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aerase_atrial

/-- info: 'ManuscriptConformance.annotOK_atrial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.annotOK_atrial

/-- info: 'ManuscriptConformance.labelCount_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.labelCount_decomp

/-- info: 'ManuscriptConformance.labelCount_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.labelCount_add

/-- info: 'ManuscriptConformance.cost_eq_labelCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.cost_eq_labelCount

/-- info: 'ManuscriptConformance.labelCount_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.labelCount_le

/-- info: 'ManuscriptConformance.nhistory_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nhistory_cost

/-- info: 'ManuscriptConformance.nhistory_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nhistory_calls

/-- info: 'ManuscriptConformance.nhistory_gates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nhistory_gates

/-- info: 'ManuscriptConformance.nhistory_calls_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nhistory_calls_src

/-- info: 'ManuscriptConformance.nhistory_gates_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nhistory_gates_src

/-- info: 'ManuscriptConformance.nhistory_calls_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nhistory_calls_le

/-- info: 'ManuscriptConformance.propCount_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.propCount_le

/-- info: 'ManuscriptConformance.nhistory_exec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nhistory_exec_le

/-- info: 'ManuscriptConformance.ninv_srcMacro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ninv_srcMacro

/-- info: 'ManuscriptConformance.nCallsN_srcMacro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nCallsN_srcMacro

/-- info: 'ManuscriptConformance.nGatesN_srcMacro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nGatesN_srcMacro

/-- info: 'ManuscriptConformance.ninv_tsrcMacro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ninv_tsrcMacro

/-- info: 'ManuscriptConformance.nCallsN_tsrcMacro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nCallsN_tsrcMacro

/-- info: 'ManuscriptConformance.nGatesN_tsrcMacro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nGatesN_tsrcMacro

/-- info: 'ManuscriptConformance.aflat_constAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aflat_constAnnot

/-- info: 'ManuscriptConformance.annotOK_constAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.annotOK_constAnnot

/-- info: 'ManuscriptConformance.aerase_constAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aerase_constAnnot

/-- info: 'ManuscriptConformance.nexec_constAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nexec_constAnnot

/-- info: 'ManuscriptConformance.aflat_timeAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aflat_timeAnnot

/-- info: 'ManuscriptConformance.annotOK_timeAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.annotOK_timeAnnot

/-- info: 'ManuscriptConformance.aerase_timeAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aerase_timeAnnot

/-- info: 'ManuscriptConformance.nexec_timeAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nexec_timeAnnot

/-- info: 'ManuscriptConformance.aflat_constAnnotI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aflat_constAnnotI

/-- info: 'ManuscriptConformance.annotOK_constAnnotI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.annotOK_constAnnotI

/-- info: 'ManuscriptConformance.aerase_constAnnotI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aerase_constAnnotI

/-- info: 'ManuscriptConformance.nexec_constAnnotI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nexec_constAnnotI

/-- info: 'ManuscriptConformance.ode_thm_gates_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_sources

/-- info: 'ManuscriptConformance.ode_thm_gates_decoder_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_decoder_sources

/-- info: 'ManuscriptConformance.ode_thm_gates_time_cert_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_cert_sources

/-- info: 'ManuscriptConformance.ode_thm_gates_time_decoder_cert_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_decoder_cert_sources

/-! ### The sparse Cayley representation (`EntrywiseCayley`) -/

/-- info: 'ManuscriptConformance.moment_le_one_of_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.moment_le_one_of_norm

/-- info: 'ManuscriptConformance.energies_of_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.energies_of_norm_le_one

/-- info: 'ManuscriptConformance.adjoint_program_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.adjoint_program_intertwines

/-- info: 'ManuscriptConformance.qls_lem_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.qls_lem_entry

/-! ### Source executions of the remaining gate endpoints (`SourceExecutionsMore`) -/

/-- info: 'ManuscriptConformance.aflat_btimeAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aflat_btimeAnnot

/-- info: 'ManuscriptConformance.annotOK_btimeAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.annotOK_btimeAnnot

/-- info: 'ManuscriptConformance.aerase_btimeAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aerase_btimeAnnot

/-- info: 'ManuscriptConformance.nexec_btimeAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nexec_btimeAnnot

/-- info: 'ManuscriptConformance.ode_thm_gates_general_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_general_sources

/-- info: 'ManuscriptConformance.ode_thm_gates_time_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_sources

/-- info: 'ManuscriptConformance.ode_thm_gates_time_general_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_general_sources

/-- info: 'ManuscriptConformance.ode_thm_gates_time_decoder_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_decoder_sources

/-! ### The certificate-form solver over a finite gate set (`GateODETimeCertFinite`) -/

/-- info: 'ManuscriptConformance.ode_thm_gates_time_cert_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_cert_finite

/-- info: 'ManuscriptConformance.aflat_selAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aflat_selAnnot

/-- info: 'ManuscriptConformance.nexec_selAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nexec_selAnnot

/-- info: 'ManuscriptConformance.aerase_selAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aerase_selAnnot

/-- info: 'ManuscriptConformance.annotOK_selAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.annotOK_selAnnot

/-- info: 'ManuscriptConformance.nSynN_aflat_aerase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nSynN_aflat_aerase

/-- info: 'ManuscriptConformance.selSrc_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.selSrc_retained

/-- info: 'ManuscriptConformance.aflat_binAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aflat_binAnnot

/-- info: 'ManuscriptConformance.annotOK_binAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.annotOK_binAnnot

/-- info: 'ManuscriptConformance.aerase_binAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aerase_binAnnot

/-- info: 'ManuscriptConformance.nexec_binAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nexec_binAnnot

/-- info: 'ManuscriptConformance.tsrcMacro_gateOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.tsrcMacro_gateOf

/-- info: 'ManuscriptConformance.aflat_sbAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aflat_sbAnnot

/-- info: 'ManuscriptConformance.annotOK_sbAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.annotOK_sbAnnot

/-- info: 'ManuscriptConformance.aerase_sbAnnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.aerase_sbAnnot

/-- info: 'ManuscriptConformance.sbSrc_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.sbSrc_facts

/-- info: 'ManuscriptConformance.binary_time_sel_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.binary_time_sel_sources

/-! ### Tiny decoded entries without their phase (`GateDecoderTiny`) -/

/-- info: 'ManuscriptConformance.hs_thm_gates_decoder_tiny' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_gates_decoder_tiny

/-- info: 'ManuscriptConformance.gate_thm_main_decoder_tiny' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_thm_main_decoder_tiny

/-- info: 'SparseHamiltonian.GeneralSparseAccess.dropVal_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.dropVal_false

/-- info: 'SparseHamiltonian.GeneralSparseAccess.dropVal_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.dropVal_ne_zero

/-- info: 'SparseHamiltonian.GeneralSparseAccess.norm_dropVal_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.norm_dropVal_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.dropTiny_prims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.dropTiny_prims

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.dropTiny_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.dropTiny_matrix

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.norm_dropTiny_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.norm_dropTiny_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.dropTiny_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.dropTiny_isHermitian

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.dropTiny_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.dropTiny_row

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.dropTiny_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.dropTiny_col

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.dropTiny_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.dropTiny_entry

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.padMat_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.padMat_isHermitian

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.padMat_dropTiny_sub_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.padMat_dropTiny_sub_apply

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.norm_padMat_dropTiny_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.norm_padMat_dropTiny_sub_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.padMat_dropTiny_sub_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.padMat_dropTiny_sub_ne_zero

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.padMat_dropTiny_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.padMat_dropTiny_sub

/-- info: 'ManuscriptConformance.fullOutputError_evolution_perturb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.fullOutputError_evolution_perturb

/-- info: 'ManuscriptConformance.fullOutputError_dropTiny' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.fullOutputError_dropTiny

/-- info: 'ManuscriptConformance.dropVal_phi_vacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.dropVal_phi_vacuous

/-! ### Lemma `ode:lem:tags` for an arbitrary pair rule (`TaggedPairEntry`, `TaggedPairSimulation`) -/

/-- info: 'ManuscriptConformance.ode_lem_tags_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_lem_tags_rule

/-- info: 'ManuscriptConformance.ode_lem_tags_rule_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_lem_tags_rule_simulation

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.pairMatrix_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.pairMatrix_apply

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.pairMatrix_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.pairMatrix_support

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.pairMatrix_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.pairMatrix_isHermitian

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.lchsRule_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.lchsRule_zero

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.lchsRule_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.lchsRule_conj

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.pairMatrix_lchsRule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.pairMatrix_lchsRule

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.taggedEntry_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.taggedEntry_eq

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.decodedEntry_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.decodedEntry_correct

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.gates_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.gates_unitary

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.gates_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.gates_correct

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.gates_lchsRule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.gates_lchsRule

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.valueProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.valueProgram_count

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.actualEntry_eq_entries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.actualEntry_eq_entries

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.scaledEntry_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.scaledEntry_correct

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.logical_eq_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.logical_eq_diagonal

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.valueProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.valueProgram_intertwines

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.oracleProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.oracleProgram_count

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.oracleProgram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.oracleProgram_eval

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.oracleProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.oracleProgram_intertwines

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.singleProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.singleProgram_count

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.singleProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.singleProgram_intertwines

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.nativeValueProgram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.nativeValueProgram_eval

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.nativeValueProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.nativeValueProgram_count

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.nativeValueProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.nativeValueProgram_cost

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.nativeValueProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.nativeValueProgram_intertwines

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.logicalProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.logicalProgram_count

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.logicalProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.logicalProgram_cost

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.logicalProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.logicalProgram_intertwines

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.compiledProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.compiledProgram_count

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.compiledProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.compiledProgram_cost

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.compiledProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.compiledProgram_intertwines

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.program_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.program_count

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.program_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.program_cost

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.program_row_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.program_row_count

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.program_column_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.program_column_count

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.program_value_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.program_value_count

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.program_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.program_intertwines

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.program_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.program_unitary

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.program_adjoint_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.program_adjoint_intertwines

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.program_adjoint_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.program_adjoint_cost

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.program_lchsRule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.program_lchsRule

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.activeProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.activeProgram_count

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.activeProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.activeProgram_cost

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.activeProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.activeProgram_intertwines

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.activeProgram_implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.activeProgram_implementsOn

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.active_implementsOn_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.active_implementsOn_rule

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.native_at_scale_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.native_at_scale_rule

/-- info: 'SparseHamiltonian.ODETaggedPairEntry.exists_rescaling_rule_simulations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedPairEntry.exists_rescaling_rule_simulations

/-! ### Value access by a writer on clean targets (`WriterAccess`, `WriterProtocols`, `WriterEndpoints`,
`WriterProtocolEndpoints`) -/

/-- info: 'ManuscriptConformance.hs_thm_main_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_main_writer

/-- info: 'ManuscriptConformance.hs_thm_optimal_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_optimal_writer

/-- info: 'ManuscriptConformance.hs_thm_two_norm_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_two_norm_writer

/-- info: 'ManuscriptConformance.qls_thm_main_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.qls_thm_main_writer

/-- info: 'ManuscriptConformance.qls_cor_separate_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.qls_cor_separate_writer

/-- info: 'ManuscriptConformance.ode_thm_main_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_main_writer

/-- info: 'ManuscriptConformance.writer_convert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.writer_convert

/-- info: 'SparseHamiltonian.WriterAccess.layoutW_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.layoutW_apply

/-- info: 'SparseHamiltonian.WriterAccess.layoutW_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.layoutW_symm_apply

/-- info: 'SparseHamiltonian.WriterAccess.writerOp_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.writerOp_apply

/-- info: 'SparseHamiltonian.WriterAccess.writerOp_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.writerOp_unitary

/-- info: 'SparseHamiltonian.WriterAccess.adder_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.adder_apply

/-- info: 'SparseHamiltonian.WriterAccess.adder_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.adder_unitary

/-- info: 'SparseHamiltonian.WriterAccess.clean_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.clean_apply

/-- info: 'SparseHamiltonian.WriterAccess.clean_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.clean_isometry

/-- info: 'SparseHamiltonian.WriterAccess.diagonal_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.diagonal_clean

/-- info: 'SparseHamiltonian.WriterAccess.writerOp_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.writerOp_clean

/-- info: 'SparseHamiltonian.WriterAccess.adder_writer_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.adder_writer_clean

/-- info: 'SparseHamiltonian.WriterAccess.convert_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.convert_clean

/-- info: 'SparseHamiltonian.WriterAccess.writerOracles_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.writerOracles_unitary

/-- info: 'SparseHamiltonian.WriterAccess.circuits_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.circuits_cost

/-- info: 'SparseHamiltonian.WriterAccess.circuits_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.circuits_intertwines

/-- info: 'SparseHamiltonian.WriterAccess.diagProg_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.diagProg_cost

/-- info: 'SparseHamiltonian.WriterAccess.diagProg_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.diagProg_eval

/-- info: 'SparseHamiltonian.WriterAccess.diagHom_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.diagHom_apply

/-- info: 'SparseHamiltonian.WriterAccess.Impl.congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.Impl.congr

/-- info: 'SparseHamiltonian.WriterAccess.Impl.conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.Impl.conj

/-- info: 'SparseHamiltonian.WriterAccess.Impl.diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.Impl.diag

/-- info: 'SparseHamiltonian.WriterAccess.Impl.spectator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.Impl.spectator

/-- info: 'SparseHamiltonian.WriterAccess.Impl.maskedProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.Impl.maskedProgram

/-- info: 'SparseHamiltonian.WriterAccess.transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.transfer

/-- info: 'SparseHamiltonian.WriterAccess.norm_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.norm_encode

/-- info: 'SparseHamiltonian.WriterAccess.fullOutputError_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.fullOutputError_encode

/-- info: 'SparseHamiltonian.WriterAccess.referenceOutputError_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.referenceOutputError_encode

/-- info: 'SparseHamiltonian.WriterAccess.impl_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.impl_writer

/-- info: 'SparseHamiltonian.WriterAccess.impl_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.impl_flat

/-- info: 'SparseHamiltonian.WriterAccess.cost_wcost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.cost_wcost

/-- info: 'SparseHamiltonian.WriterAccess.cost_wcost_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.cost_wcost_one_le

/-- info: 'SparseHamiltonian.WriterAccess.single0_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.single0_apply

/-- info: 'SparseHamiltonian.WriterAccess.single0_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.single0_isometry

/-- info: 'SparseHamiltonian.WriterAccess.swapPi_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.swapPi_apply

/-- info: 'SparseHamiltonian.WriterAccess.swapPi_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.swapPi_symm_apply

/-- info: 'SparseHamiltonian.WriterAccess.HomOf.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.HomOf.refl

/-- info: 'SparseHamiltonian.WriterAccess.HomOf.conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.HomOf.conj

/-- info: 'SparseHamiltonian.WriterAccess.HomOf.diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.HomOf.diag

/-- info: 'SparseHamiltonian.WriterAccess.relabelInl_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.relabelInl_eval

/-- info: 'SparseHamiltonian.WriterAccess.relabelInl_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.relabelInl_cost

/-- info: 'SparseHamiltonian.WriterAccess.Impl.fconj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.Impl.fconj

/-- info: 'SparseHamiltonian.WriterAccess.Impl.fdiag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.Impl.fdiag

/-- info: 'SparseHamiltonian.WriterAccess.FImplH.congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.FImplH.congr

/-- info: 'SparseHamiltonian.WriterAccess.FImplH.conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.FImplH.conj

/-- info: 'SparseHamiltonian.WriterAccess.FImplH.diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.FImplH.diag

/-- info: 'SparseHamiltonian.WriterAccess.FImplH.spectator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.FImplH.spectator

/-- info: 'SparseHamiltonian.WriterAccess.FImplH.masked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.FImplH.masked

/-- info: 'SparseHamiltonian.WriterAccess.Impl.fextra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.Impl.fextra

/-- info: 'SparseHamiltonian.WriterAccess.FImplH.extra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.FImplH.extra

/-- info: 'SparseHamiltonian.WriterAccess.encode_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.encode_isometry

/-- info: 'SparseHamiltonian.WriterAccess.encodeTrials_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.encodeTrials_amplitude

/-- info: 'SparseHamiltonian.WriterAccess.encodeTrials_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.encodeTrials_probability

/-- info: 'SparseHamiltonian.WriterAccess.encodeTrials_meanSuccess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.encodeTrials_meanSuccess

/-- info: 'SparseHamiltonian.WriterAccess.encodeTrials_oneTrialDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.encodeTrials_oneTrialDensity

/-- info: 'SparseHamiltonian.WriterAccess.encodeTrials_maxCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.encodeTrials_maxCost

/-- info: 'SparseHamiltonian.WriterAccess.encodeProtocol_failureMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.encodeProtocol_failureMass

/-- info: 'SparseHamiltonian.WriterAccess.encodeProtocol_successMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.encodeProtocol_successMass

/-- info: 'SparseHamiltonian.WriterAccess.encodeProtocol_successDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.encodeProtocol_successDensity

/-- info: 'SparseHamiltonian.WriterAccess.encodeProtocol_conditionalDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.encodeProtocol_conditionalDensity

/-- info: 'SparseHamiltonian.WriterAccess.encodeProtocol_worstCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.encodeProtocol_worstCost

/-- info: 'SparseHamiltonian.WriterAccess.encodeProtocol_repeat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.encodeProtocol_repeat

/-- info: 'SparseHamiltonian.WriterAccess.encodeProtocol_fourTrials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.encodeProtocol_fourTrials

/-- info: 'SparseHamiltonian.WriterAccess.encodeRun_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.encodeRun_probability

/-- info: 'SparseHamiltonian.WriterAccess.encodeTree_successMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.encodeTree_successMass

/-- info: 'SparseHamiltonian.WriterAccess.encodeTree_successDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.encodeTree_successDensity

/-- info: 'SparseHamiltonian.WriterAccess.encodeTree_conditionalDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.encodeTree_conditionalDensity

/-- info: 'SparseHamiltonian.WriterAccess.encodeTree_worstCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.encodeTree_worstCost

/-- info: 'SparseHamiltonian.WriterAccess.cost_le_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.cost_le_mul

/-- info: 'SparseHamiltonian.WriterAccess.protocol_worstCost_le_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.protocol_worstCost_le_mul

/-- info: 'SparseHamiltonian.WriterAccess.tree_worstCost_le_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.tree_worstCost_le_mul

/-- info: 'SparseHamiltonian.WriterAccess.fimpl_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.fimpl_writer

/-- info: 'SparseHamiltonian.WriterAccess.fimplH_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.fimplH_writer

/-- info: 'SparseHamiltonian.WriterAccess.fimplH_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.fimplH_flat

/-- info: 'SparseHamiltonian.WriterAccess.wcostU_wMat_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.wcostU_wMat_le

/-- info: 'SparseHamiltonian.WriterAccess.wcostU_wSrc' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.wcostU_wSrc

/-- info: 'SparseHamiltonian.WriterAccess.wcostB_wMat_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.wcostB_wMat_le

/-- info: 'SparseHamiltonian.WriterAccess.wcostB_wSrc' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.wcostB_wSrc

/-! ### Finite-set forms of the Appendix D propositions with a supplied private circuit (`GatePropsSelective`) -/

/-- info: 'ManuscriptConformance.pcSel_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.pcSel_spec

/-- info: 'ManuscriptConformance.sel_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.sel_transfer

/-- info: 'ManuscriptConformance.gate_prop_finite_sel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_prop_finite_sel

/-- info: 'ManuscriptConformance.gate_prop_finite_sel_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_prop_finite_sel_native

/-- info: 'ManuscriptConformance.gate_prop_core_sel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_prop_core_sel

/-- info: 'ManuscriptConformance.gate_prop_core_sel_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_prop_core_sel_native

/-- info: 'ManuscriptConformance.unc_inv_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.unc_inv_approx

/-- info: 'ManuscriptConformance.localOp_rePW_liftB_uncIdeal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.localOp_rePW_liftB_uncIdeal

/-- info: 'ManuscriptConformance.pcSel_unc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.pcSel_unc

/-- info: 'ManuscriptConformance.hmacroP_unc_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hmacroP_unc_approx

/-- info: 'ManuscriptConformance.hcircP_unc_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hcircP_unc_approx

/-- info: 'ManuscriptConformance.hcircP_unc_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hcircP_unc_error

/-- info: 'ManuscriptConformance.sel_signed_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.sel_signed_transfer

/-- info: 'ManuscriptConformance.gate_prop_signed_sel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_prop_signed_sel

/-- info: 'ManuscriptConformance.gate_prop_signed_sel_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_prop_signed_sel_native

/-! ### `gate:prop:signed` for a general known success projection and sign reflection (`GatePropsKnown`) -/

/-- info: 'ManuscriptConformance.factor_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.factor_conj

/-- info: 'ManuscriptConformance.Cop_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.Cop_conj

/-- info: 'ManuscriptConformance.Dop_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.Dop_conj

/-- info: 'ManuscriptConformance.ham_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ham_conj

/-- info: 'ManuscriptConformance.Converts.adj_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.Converts.adj_comp

/-- info: 'ManuscriptConformance.Converts.ham' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.Converts.ham

/-- info: 'ManuscriptConformance.Converts.Dop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.Converts.Dop

/-- info: 'ManuscriptConformance.gate_prop_signed_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_prop_signed_known

/-- info: 'ManuscriptConformance.gate_prop_signed_known_sel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_prop_signed_known_sel

/-- info: 'ManuscriptConformance.approxOn_sandwich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.approxOn_sandwich

/-- info: 'ManuscriptConformance.approxOn_sandwich_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.approxOn_sandwich_eq

/-- info: 'ManuscriptConformance.nrun_placeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nrun_placeC

/-- info: 'ManuscriptConformance.nGatesN_convFactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nGatesN_convFactor

/-- info: 'ManuscriptConformance.nCallsN_convFactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.nCallsN_convFactor

/-- info: 'ManuscriptConformance.placeC_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.placeC_valid

/-- info: 'ManuscriptConformance.convFactor_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.convFactor_valid

/-- info: 'ManuscriptConformance.placeC_gates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.placeC_gates

/-- info: 'ManuscriptConformance.convFactor_gates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.convFactor_gates

/-- info: 'ManuscriptConformance.uncIdeal_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.uncIdeal_preserves

/-- info: 'ManuscriptConformance.convFactor_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.convFactor_approx

/-- info: 'ManuscriptConformance.UJop_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.UJop_append

/-- info: 'ManuscriptConformance.converts_of_gates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.converts_of_gates

/-- info: 'ManuscriptConformance.gate_prop_signed_known_conv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_prop_signed_known_conv

/-! ### `ode:thm:time` with a time-indexed writer value oracle (`WriterTimeEndpoints`) -/

/-- info: 'SparseHamiltonian.WriterAccess.injB_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.injB_apply

/-- info: 'SparseHamiltonian.WriterAccess.blk_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.blk_apply

/-- info: 'SparseHamiltonian.WriterAccess.eq_sum_injB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.eq_sum_injB

/-- info: 'SparseHamiltonian.WriterAccess.apply_eq_sum_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.apply_eq_sum_blk

/-- info: 'SparseHamiltonian.WriterAccess.ext_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.ext_blk

/-- info: 'SparseHamiltonian.WriterAccess.blk_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.blk_comp

/-- info: 'SparseHamiltonian.WriterAccess.blk_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.blk_one

/-- info: 'SparseHamiltonian.WriterAccess.blk_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.blk_zero

/-- info: 'SparseHamiltonian.WriterAccess.blk_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.blk_add

/-- info: 'SparseHamiltonian.WriterAccess.blk_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.blk_smul

/-- info: 'SparseHamiltonian.WriterAccess.blk_sum_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.blk_sum_inj

/-- info: 'SparseHamiltonian.WriterAccess.blk_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.blk_adjoint

/-- info: 'SparseHamiltonian.WriterAccess.blk_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.blk_diagonal

/-- info: 'SparseHamiltonian.WriterAccess.blk_ampFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.blk_ampFun

/-- info: 'SparseHamiltonian.WriterAccess.ampHom_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.ampHom_apply

/-- info: 'SparseHamiltonian.WriterAccess.ampHom_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.ampHom_diagonal

/-- info: 'SparseHamiltonian.WriterAccess.labelProg_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.labelProg_cost

/-- info: 'SparseHamiltonian.WriterAccess.labelProg_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.labelProg_eval

/-- info: 'SparseHamiltonian.WriterAccess.Impl.flabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.Impl.flabel

/-- info: 'SparseHamiltonian.WriterAccess.FImplH.label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.FImplH.label

/-- info: 'SparseHamiltonian.WriterAccess.FImplH.homOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.FImplH.homOf

/-- info: 'SparseHamiltonian.WriterAccess.homOf_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.homOf_time

/-- info: 'SparseHamiltonian.WriterAccess.wcostS_wMat_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.wcostS_wMat_le

/-- info: 'SparseHamiltonian.WriterAccess.wcostS_wSrc' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.wcostS_wSrc

/-- info: 'SparseHamiltonian.WriterAccess.fimplH_meshActual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.fimplH_meshActual

/-- info: 'ManuscriptConformance.ode_thm_time_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_time_writer

/-! ### `ode:thm:general` with a writer value oracle (`WriterGeneralEndpoint`) -/

/-- info: 'SparseHamiltonian.WriterAccess.single0_eq_injB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.single0_eq_injB

/-- info: 'SparseHamiltonian.WriterAccess.ampHom_single0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.ampHom_single0

/-- info: 'SparseHamiltonian.WriterAccess.Impl.fhom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.Impl.fhom

/-- info: 'SparseHamiltonian.WriterAccess.Impl.fhomL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.Impl.fhomL

/-- info: 'SparseHamiltonian.WriterAccess.powOracle_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.powOracle_eq

/-- info: 'SparseHamiltonian.WriterAccess.masked_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.masked_eq

/-- info: 'SparseHamiltonian.WriterAccess.wcostG_wMat_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.wcostG_wMat_le

/-- info: 'SparseHamiltonian.WriterAccess.wcostG_wSrc' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.wcostG_wSrc

/-- info: 'SparseHamiltonian.WriterAccess.fimplH_generalFlat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.fimplH_generalFlat

/-- info: 'SparseHamiltonian.WriterAccess.impl_generalPhysical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.WriterAccess.impl_generalPhysical

/-- info: 'ManuscriptConformance.ode_thm_general_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_general_writer

/-! ### Per-run accuracy and approximate sources with a time-indexed writer (`WriterTimeVariants`) -/

/-- info: 'ManuscriptConformance.encodeTrials_outputDirection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.encodeTrials_outputDirection

/-- info: 'ManuscriptConformance.trialsClose_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.trialsClose_encode

/-- info: 'ManuscriptConformance.historiesClose_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.historiesClose_encode

/-- info: 'ManuscriptConformance.ode_thm_time_actual_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_time_actual_writer

/-- info: 'ManuscriptConformance.fimplH_meshMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.fimplH_meshMatrix

/-- info: 'ManuscriptConformance.fimplH_workActual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.fimplH_workActual

/-- info: 'ManuscriptConformance.ode_thm_time_approx_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_time_approx_writer

/-! ### The successful runs for approximate source preparations (`ApproxRuns`) -/

/-- info: 'ManuscriptConformance.norm_unitDirection_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.norm_unitDirection_sub_le

/-- info: 'ManuscriptConformance.direction_close_of_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.direction_close_of_near

/-- info: 'ManuscriptConformance.lowWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.lowWeight_le

/-- info: 'SparseHamiltonian.CleanWorkODE.work_certificate_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.work_certificate_runs

/-- info: 'SparseHamiltonian.CleanWorkODE.work_approx_build_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.work_approx_build_runs

/-- info: 'SparseHamiltonian.CleanWorkODE.work_approx_solver_nonneg_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.work_approx_solver_nonneg_runs

/-- info: 'SparseHamiltonian.CleanWorkODE.work_approx_solver_nonneg_regular_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.work_approx_solver_nonneg_regular_runs

/-- info: 'ManuscriptConformance.ode_thm_time_approx_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_time_approx_runs

/-! ### The gate-level value oracle from a writer on valid clean inputs (`WriterGateAccess`) -/

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.Writer.prims_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.Writer.prims_row

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.Writer.prims_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.Writer.prims_col

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.Writer.prims_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.Writer.prims_value

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.Writer.prims_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.Writer.prims_isUnitary

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.Writer.adjoint_comp_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.Writer.adjoint_comp_self

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.Writer.norm_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.Writer.norm_phase

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.Writer.adjoint_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.Writer.adjoint_write

/-- info: 'SparseHamiltonian.GeneralSparseAccess.qlift_refl_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.qlift_refl_bas

/-- info: 'SparseHamiltonian.GeneralSparseAccess.posV_ne_v' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.posV_ne_v

/-- info: 'SparseHamiltonian.GeneralSparseAccess.posV_ne_g₂' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.posV_ne_g₂

/-- info: 'SparseHamiltonian.GeneralSparseAccess.tl_ne_sc' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.tl_ne_sc

/-- info: 'SparseHamiltonian.GeneralSparseAccess.nrun_wCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.nrun_wCall

/-- info: 'SparseHamiltonian.GeneralSparseAccess.cfgRun_copyC_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.cfgRun_copyC_out

/-- info: 'SparseHamiltonian.GeneralSparseAccess.cfgRun_copyC_v' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.cfgRun_copyC_v

/-- info: 'SparseHamiltonian.GeneralSparseAccess.copyBit_of_false' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.copyBit_of_false

/-- info: 'SparseHamiltonian.GeneralSparseAccess.cfgRun_copyC_overwrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.cfgRun_copyC_overwrite

/-- info: 'SparseHamiltonian.GeneralSparseAccess.gRun_copyC_put' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.gRun_copyC_put

/-- info: 'SparseHamiltonian.GeneralSparseAccess.valMap_copyC_valMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.valMap_copyC_valMap

/-- info: 'SparseHamiltonian.GeneralSparseAccess.wmid_invalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.wmid_invalid

/-- info: 'SparseHamiltonian.GeneralSparseAccess.wmid_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.wmid_valid

/-- info: 'SparseHamiltonian.GeneralSparseAccess.implValW_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.implValW_bas

/-- info: 'SparseHamiltonian.GeneralSparseAccess.implValW_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.implValW_clean

/-- info: 'SparseHamiltonian.GeneralSparseAccess.valid_implValW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.valid_implValW

/-- info: 'SparseHamiltonian.GeneralSparseAccess.valid_implPW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.valid_implPW

/-- info: 'SparseHamiltonian.GeneralSparseAccess.callsOf_implValW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.callsOf_implValW

/-- info: 'SparseHamiltonian.GeneralSparseAccess.kindOK_implPW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.kindOK_implPW

/-- info: 'SparseHamiltonian.GeneralSparseAccess.nGatesN_implPW_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.nGatesN_implPW_eq

/-- info: 'SparseHamiltonian.GeneralSparseAccess.nGatesN_implPW_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.nGatesN_implPW_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.implOKW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.implOKW

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.pdecode_ptable_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.pdecode_ptable_false

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.padDataEW_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.padDataEW_matrix

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.padDataEW_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.padDataEW_decode

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.padDataEW_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.padDataEW_table

/-- info: 'SparseHamiltonian.GeneralSparseAccess.prims_padEW_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.prims_padEW_row

/-- info: 'SparseHamiltonian.GeneralSparseAccess.prims_padEW_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.prims_padEW_col

/-- info: 'SparseHamiltonian.GeneralSparseAccess.prims_padEW_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.prims_padEW_val

/-- info: 'SparseHamiltonian.GeneralSparseAccess.implOKEW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.implOKEW

/-! ### The general-size gate theorems with a writer (`WriterGates`, `WriterGatesDecoder`) -/

/-- info: 'ManuscriptConformance.genCircW_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.genCircW_spec

/-- info: 'ManuscriptConformance.genCircW_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.genCircW_error

/-- info: 'ManuscriptConformance.hs_thm_gates_general_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_gates_general_writer

/-- info: 'ManuscriptConformance.gate_thm_main_general_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_thm_main_general_writer

/-- info: 'ManuscriptConformance.genCircEW_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.genCircEW_error

/-- info: 'ManuscriptConformance.hs_thm_gates_decoder_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_gates_decoder_writer

/-- info: 'ManuscriptConformance.gate_thm_main_decoder_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_thm_main_decoder_writer

/-! ### The general-size ODE gate theorems with a writer (`WriterODEGates`, `WriterODETimeGates`, `WriterODECert`, `WriterODESources`) -/

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPub.ndW_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPub.ndW_public

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPub.arW_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPub.arW_ok

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPub.ndW_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPub.ndW_nGates

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPub.ndW_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPub.ndW_nCalls

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPub.privGatesW_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPub.privGatesW_le

/-- info: 'SparseHamiltonian.GeneralSparseODE.general_ode_outcome_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.general_ode_outcome_writer

/-- info: 'SparseHamiltonian.GeneralSparseODE.general_ode_budget_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.general_ode_budget_writer

/-- info: 'ManuscriptConformance.ode_thm_gates_general_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_general_writer

/-- info: 'SparseHamiltonian.GeneralSparseODE.primsTGW_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.primsTGW_isUnitary

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPubT.ndW_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPubT.ndW_public

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPubT.arW_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPubT.arW_ok

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPubT.ndW_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPubT.ndW_nGates

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPubT.ndW_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPubT.ndW_nCalls

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPubT.nativeOKW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPubT.nativeOKW

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPubT.privGatesW_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPubT.privGatesW_le

/-- info: 'SparseHamiltonian.GeneralSparseODE.general_time_outcome_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.general_time_outcome_writer

/-- info: 'SparseHamiltonian.GeneralSparseODE.general_time_budget_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.general_time_budget_writer

/-- info: 'ManuscriptConformance.ode_thm_gates_time_general_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_general_writer

/-- info: 'SparseHamiltonian.MeshCertificateODE.general_time_cert_outcome_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.general_time_cert_outcome_writer

/-- info: 'ManuscriptConformance.ode_thm_gates_time_cert_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_cert_writer

/-- info: 'ManuscriptConformance.ode_thm_gates_time_cert_valid_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_cert_valid_writer

/-- info: 'ManuscriptConformance.ode_thm_gates_general_sources_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_general_sources_writer

/-- info: 'ManuscriptConformance.ode_thm_gates_time_general_sources_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_general_sources_writer

/-! ### Theorem `ode:thm:general` at `T = 0` with a writer (`WriterGeneralZero`) -/

/-- info: 'ManuscriptConformance.ode_thm_general_zero_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_general_zero_writer

/-! ### The ODE gate theorems with binary entry decoding and a writer (`WriterDecoderAccess`,
`WriterDecoderODE`, `WriterDecoderCert`, `WriterDecoderSources`) -/

/-- info: 'SparseHamiltonian.GeneralDecoderODE.nGatesN_implDecW_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.nGatesN_implDecW_le

/-- info: 'SparseHamiltonian.GeneralDecoderODE.kindOK_implDecW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.kindOK_implDecW

/-- info: 'SparseHamiltonian.GeneralDecoderODE.valid_implDecW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.valid_implDecW

/-- info: 'SparseHamiltonian.GeneralDecoderODE.valid_implDPW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.valid_implDPW

/-- info: 'SparseHamiltonian.GeneralDecoderODE.nGatesN_implDPW_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.nGatesN_implDPW_le

/-- info: 'SparseHamiltonian.GeneralDecoderODE.kindOK_implDPW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.kindOK_implDPW

/-- info: 'SparseHamiltonian.GeneralDecoderODE.comp_cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.comp_cancel

/-- info: 'SparseHamiltonian.GeneralDecoderODE.gRun_reverse_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.gRun_reverse_comp

/-- info: 'SparseHamiltonian.GeneralDecoderODE.gRun_comp_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.gRun_comp_reverse

/-- info: 'SparseHamiltonian.GeneralDecoderODE.gRun_outGates_twice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.gRun_outGates_twice

/-- info: 'SparseHamiltonian.GeneralDecoderODE.decW_invol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.decW_invol

/-- info: 'SparseHamiltonian.GeneralDecoderODE.posD_local' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.posD_local

/-- info: 'SparseHamiltonian.GeneralDecoderODE.decW_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.decW_valid

/-- info: 'SparseHamiltonian.GeneralDecoderODE.subst_nGatesOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.subst_nGatesOf

/-- info: 'SparseHamiltonian.GeneralDecoderODE.subst_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.subst_congr

/-- info: 'SparseHamiltonian.GeneralDecoderODE.nrun_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.nrun_congr

/-- info: 'SparseHamiltonian.GeneralDecoderODE.overwrite_callEmb_elim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.overwrite_callEmb_elim

/-- info: 'SparseHamiltonian.GeneralDecoderODE.nrun_subst_gates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.nrun_subst_gates

/-- info: 'SparseHamiltonian.GeneralDecoderODE.nrun_copyD_put' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.nrun_copyD_put

/-- info: 'SparseHamiltonian.GeneralDecoderODE.nrun_subst_valCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.nrun_subst_valCall

/-- info: 'SparseHamiltonian.GeneralDecoderODE.cval_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.cval_valid

/-- info: 'SparseHamiltonian.GeneralDecoderODE.cmid_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.cmid_valid

/-- info: 'SparseHamiltonian.GeneralDecoderODE.cmid_invalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.cmid_invalid

/-- info: 'SparseHamiltonian.GeneralDecoderODE.compW_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.compW_bas

/-- info: 'SparseHamiltonian.GeneralDecoderODE.compW_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.compW_value

/-- info: 'SparseHamiltonian.GeneralDecoderODE.implDPW_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.implDPW_eq

/-- info: 'SparseHamiltonian.GeneralDecoderODE.nrun_implDP_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.nrun_implDP_eq

/-- info: 'SparseHamiltonian.GeneralDecoderODE.implOK_implDPW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.implOK_implDPW

/-- info: 'SparseHamiltonian.GeneralDecoderODE.decoder_ode_outcome_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.decoder_ode_outcome_writer

/-- info: 'SparseHamiltonian.GeneralDecoderODE.decoder_ode_budget_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.decoder_ode_budget_writer

/-- info: 'SparseHamiltonian.GeneralDecoderODE.decoder_time_outcome_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.decoder_time_outcome_writer

/-- info: 'SparseHamiltonian.GeneralDecoderODE.decoder_time_budget_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.decoder_time_budget_writer

/-- info: 'ManuscriptConformance.ode_thm_gates_decoder_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_decoder_writer

/-- info: 'ManuscriptConformance.ode_thm_gates_time_decoder_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_decoder_writer

/-- info: 'SparseHamiltonian.MeshCertificateODE.decoder_time_cert_outcome_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.decoder_time_cert_outcome_writer

/-- info: 'ManuscriptConformance.ode_thm_gates_time_decoder_cert_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_decoder_cert_writer

/-- info: 'ManuscriptConformance.ode_thm_gates_time_decoder_cert_valid_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_decoder_cert_valid_writer

/-- info: 'ManuscriptConformance.ode_thm_gates_decoder_sources_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_decoder_sources_writer

/-- info: 'ManuscriptConformance.ode_thm_gates_time_decoder_sources_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_decoder_sources_writer

/-- info: 'ManuscriptConformance.ode_thm_gates_time_decoder_cert_sources_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_decoder_cert_sources_writer

/-- info: 'ManuscriptConformance.ode_thm_gates_time_cert_sources_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_cert_sources_writer

/-! ### The branch-certificate forms of the time-dependent ODE gate theorem with a writer
(`WriterBranchCerts`) -/

/-- info: 'ManuscriptConformance.ode_thm_gates_time_cert_branch_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_cert_branch_writer

/-- info: 'ManuscriptConformance.ode_thm_gates_time_decoder_cert_branch_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_decoder_cert_branch_writer

/-- info: 'ManuscriptConformance.ode_thm_gates_time_cert_valid_branch_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_cert_valid_branch_writer

/-- info: 'ManuscriptConformance.ode_thm_gates_time_decoder_cert_valid_branch_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_gates_time_decoder_cert_valid_branch_writer

/-! ### The variants of the general-decoder gate theorems with a writer (`WriterGateVariants`) -/

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.Writer.prims_dropTiny' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.Writer.prims_dropTiny

/-- info: 'ManuscriptConformance.hs_thm_gates_decoder_tiny_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_gates_decoder_tiny_writer

/-- info: 'ManuscriptConformance.gate_thm_main_decoder_tiny_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_thm_main_decoder_tiny_writer

/-- info: 'ManuscriptConformance.hs_thm_gates_decoder_tables_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_gates_decoder_tables_writer

/-- info: 'ManuscriptConformance.gate_thm_main_decoder_tables_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_thm_main_decoder_tables_writer

/-- info: 'ManuscriptConformance.hs_thm_gates_general_of_decoder_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.hs_thm_gates_general_of_decoder_writer

/-- info: 'ManuscriptConformance.gate_thm_main_general_of_decoder_writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.gate_thm_main_general_of_decoder_writer

/-! ### The native protocol and the column of its preparation (`PrepColumn`) -/

/-- info: 'SparseHamiltonian.ODERepeatProtocol.fourTrials_law_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODERepeatProtocol.fourTrials_law_congr

/-- info: 'SparseHamiltonian.GateNative.trialN_seed_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.trialN_seed_congr

/-- info: 'SparseHamiltonian.GateNative.nprotocol_law_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nprotocol_law_congr

/-- info: 'SparseHamiltonian.SourceAccuracyODE.WOutcome.of_column' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SourceAccuracyODE.WOutcome.of_column

/-- info: 'ManuscriptConformance.heraldedOutput_of_column' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.heraldedOutput_of_column

/-! ### The time-dependent native preparations and the loader's label columns (`PrepLoader`) -/

/-- info: 'SparseHamiltonian.GateNative.load_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.load_agrees

/-- info: 'SparseHamiltonian.GateNative.supp_wprep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.supp_wprep

/-- info: 'SparseHamiltonian.GateNative.wpScratch_of_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.wpScratch_of_exact

/-- info: 'SparseHamiltonian.GateNative.tzprepC_column_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.tzprepC_column_congr

/-- info: 'SparseHamiltonian.GateNative.omacro_tsrc_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.omacro_tsrc_congr

/-- info: 'SparseHamiltonian.GateNative.flatMap_omacro_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.flatMap_omacro_congr

/-- info: 'SparseHamiltonian.GateNative.prepPre_noLoad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.prepPre_noLoad

/-- info: 'SparseHamiltonian.GateNative.prepPost_noLoad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.prepPost_noLoad

/-- info: 'SparseHamiltonian.GateNative.tnprepC_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.tnprepC_eq

/-- info: 'SparseHamiltonian.GateNative.tnprepC_column_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.tnprepC_column_congr

/-- info: 'SparseHamiltonian.GeneralSparseODE.liftC_cols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.liftC_cols

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPubT.prep_column_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPubT.prep_column_congr

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPubT.prep_pres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPubT.prep_pres

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPubT.wOutcome_of_loader_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPubT.wOutcome_of_loader_columns

/-- info: 'SparseHamiltonian.GeneralDecoderODE.prepTI_column_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.prepTI_column_congr

/-- info: 'SparseHamiltonian.GeneralDecoderODE.prepTI_pres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.prepTI_pres

/-- info: 'SparseHamiltonian.GeneralDecoderODE.prepTI_wOutcome_of_loader_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.prepTI_wOutcome_of_loader_columns

/-- info: 'SparseHamiltonian.SourceAccuracyODE.WOutcome.of_loader_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SourceAccuracyODE.WOutcome.of_loader_columns

/-! ### The general-source ODE solver with a loader on its clean columns (`SourceLoaderColumns`) -/

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.single_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.single_smul

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.clean_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.clean_eq_sum

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.clean_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.clean_congr

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.loader_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.loader_single

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.act_seedInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.act_seedInput

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.sourceFamily_eq_sourceFamilyL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.sourceFamily_eq_sourceFamilyL

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.sourceFamilyL_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.sourceFamilyL_true

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.sourceFamilyL_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.sourceFamilyL_false

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.sourceFamily_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.sourceFamily_true

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.sourceFamily_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.sourceFamily_false

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.prepL_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.prepL_unitary

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.sourceFamilyL_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.sourceFamilyL_unitary

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.program_seed_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.program_seed_congr

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.amplified_seed_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.amplified_seed_congr

/-- info: 'SparseHamiltonian.GeneralSourceODE.Native.publicTrials_eq_publicTrialsS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Native.publicTrials_eq_publicTrialsS

/-- info: 'SparseHamiltonian.GeneralSourceODE.Native.publicTrialsS_seed_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Native.publicTrialsS_seed_congr

/-- info: 'SparseHamiltonian.GeneralSourceODE.Native.publicTrialsS_matrix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Native.publicTrialsS_matrix_cost

/-- info: 'SparseHamiltonian.GeneralSourceODE.Native.publicTrialsS_source_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Native.publicTrialsS_source_cost

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.sourceOperationL_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.sourceOperationL_unitary

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.actualOracle_eq_actualOracleL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.actualOracle_eq_actualOracleL

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.actualOracleL_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.actualOracleL_unitary

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.implementationL_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.implementationL_eval

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.implementationL_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.implementationL_matrix

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.implementationL_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.implementationL_weight

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.implementationL_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.implementationL_load

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.implementationL_unweight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.implementationL_unweight

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.implementationL_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.implementationL_source

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.actual_certificate_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.actual_certificate_seed

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.columns_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.columns_certificate

/-- info: 'SparseHamiltonian.GeneralSourceODE.propagated_solver_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.propagated_solver_public

/-- info: 'SparseHamiltonian.GeneralSourceODE.exists_unitary_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.exists_unitary_map

/-- info: 'SparseHamiltonian.GeneralSourceODE.loadUnitary_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.loadUnitary_unitary

/-- info: 'SparseHamiltonian.GeneralSourceODE.loadUnitary_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.loadUnitary_apply

/-- info: 'SparseHamiltonian.GeneralSourceODE.solver_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.solver_columns

/-! ### The mesh general-source ODE solver with a loader on its clean columns (`MeshLoaderColumns`) -/

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshNative.publicTrials_eq_publicTrialsS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshNative.publicTrials_eq_publicTrialsS

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshNative.publicTrialsS_seed_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshNative.publicTrialsS_seed_congr

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshNative.publicTrialsS_matrix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshNative.publicTrialsS_matrix_cost

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshNative.publicTrialsS_source_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshNative.publicTrialsS_source_cost

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.actualOracle_eq_actualOracleL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.actualOracle_eq_actualOracleL

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.actualOracleL_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.actualOracleL_unitary

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementationL_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementationL_eval

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementationL_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementationL_matrix

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementationL_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementationL_weight

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementationL_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementationL_load

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementationL_unweight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementationL_unweight

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementationL_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementationL_source

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.columns_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.columns_certificate

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_propagated_solver_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_propagated_solver_public

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_solver_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_solver_columns

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_solver_integral_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_solver_integral_columns

/-! ### Represented samples of any sign with a loader on its clean columns (`RobustLoaderColumns`) -/

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_propagated_solver_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_propagated_solver_public

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_mesh_solver_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_mesh_solver_columns

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_solver_integral_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_solver_integral_columns

/-! ### The full-class Dyson solver with a loader on its clean columns (`DysonLoaderColumns`) -/

/-- info: 'DysonFullClass.trialCertificate_of_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.trialCertificate_of_seed

/-- info: 'DysonFullClass.compiledTrials_seed_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.compiledTrials_seed_congr

/-- info: 'DysonFullClass.compiledTrials_matrix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.compiledTrials_matrix_cost

/-- info: 'DysonFullClass.compiledTrials_source_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.compiledTrials_source_cost

/-- info: 'DysonFullClass.compiledTrials_total_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.compiledTrials_total_cost

/-- info: 'DysonFullClass.compiledTrials_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.compiledTrials_shape

/-- info: 'DysonFullClass.herald_certificate_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.herald_certificate_columns

/-- info: 'DysonFullClass.full_dyson_shape_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.full_dyson_shape_columns

/-- info: 'DysonFullClass.full_dyson_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.full_dyson_columns

/-! ### The Dyson single program and separate primitives for `Lo` (`DysonLoaderActual`) -/

/-- info: 'DysonFullClass.fullOracleL_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullOracleL_unitary

/-- info: 'DysonFullClass.full_single_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.full_single_columns

/-- info: 'DysonFullClass.fullActualOracleL_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullActualOracleL_unitary

/-- info: 'DysonFullClass.fullImplementationL_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullImplementationL_eval

/-- info: 'DysonFullClass.fullImplementationL_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullImplementationL_matrix

/-- info: 'DysonFullClass.fullImplementationL_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullImplementationL_weight

/-- info: 'DysonFullClass.fullImplementationL_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullImplementationL_load

/-- info: 'DysonFullClass.fullImplementationL_unweight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullImplementationL_unweight

/-- info: 'DysonFullClass.fullImplementationL_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullImplementationL_source

/-- info: 'DysonFullClass.full_actual_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.full_actual_columns

/-! ### Theorem `ode:thm:time` with a loader on its clean columns (`TimeLoaderColumns`) -/

/-- info: 'SparseHamiltonian.RepresentedSampleODE.mesh_zero_time_core_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.mesh_zero_time_core_public

/-- info: 'SparseHamiltonian.RepresentedSampleODE.mesh_zero_generator_core_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.mesh_zero_generator_core_public

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_zero_core_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_zero_core_public

/-- info: 'SparseHamiltonian.RepresentedSampleODE.RobustPublicOutcome.columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.RobustPublicOutcome.columns

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_solver_nonneg_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_solver_nonneg_columns

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_solver_nonneg_regular_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_solver_nonneg_regular_columns

/-- info: 'ManuscriptConformance.ode_thm_time_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_time_columns

/-! ### The actual runs of `ode:thm:time` with a loader on its clean columns (`TimeLoaderRuns`) -/

/-- info: 'ManuscriptConformance.trialsClose_congr_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.trialsClose_congr_seed

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.columns_seed_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.columns_seed_eval

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.columns_trialsClose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.columns_trialsClose

/-- info: 'ManuscriptConformance.ode_thm_time_actual_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_time_actual_columns

/-! ### Branch certificates with a loader on its clean columns (`TimeLoaderBranch`) -/

/-- info: 'ManuscriptConformance.ode_thm_time_branch_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_time_branch_columns

/-- info: 'ManuscriptConformance.ode_thm_time_actual_branch_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_time_actual_branch_columns

/-! ### Approximate-completion stability of the clean-column loader (`LoaderApprox`) -/

/-- info: 'SparseHamiltonian.ODEGroverActual.norm_map_of_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverActual.norm_map_of_isUnitary

/-- info: 'SparseHamiltonian.ODEGroverActual.reflect_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverActual.reflect_norm

/-- info: 'SparseHamiltonian.ODEGroverActual.reflect_norm_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverActual.reflect_norm_two

/-- info: 'SparseHamiltonian.ODEGroverActual.grover_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverActual.grover_norm

/-- info: 'SparseHamiltonian.ODEGroverActual.projector_sub_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverActual.projector_sub_apply_le

/-- info: 'SparseHamiltonian.ODEGroverActual.grover_sub_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverActual.grover_sub_apply_le

/-- info: 'SparseHamiltonian.ODEGroverActual.grover_pow_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverActual.grover_pow_sub_le

/-- info: 'SparseHamiltonian.ODEGroverActual.trial_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverActual.trial_sub_le

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.perturbed_four_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.perturbed_four_seed

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.approx_certificate_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.approx_certificate_seed

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.program_seed_dev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.program_seed_dev

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshNative.publicTrialsS_seed_dev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshNative.publicTrialsS_seed_dev

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.columns_approx_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.columns_approx_certificate

/-! ### Theorem `ode:thm:time` with approximate columns (`TimeLoaderApprox`) -/

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_solver_nonneg_regular_columns_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_solver_nonneg_regular_columns_approx

/-- info: 'ManuscriptConformance.ode_thm_time_columns_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_time_columns_approx

/-! ### Branch certificates with approximate columns (`TimeLoaderBranchApprox`) -/

/-- info: 'ManuscriptConformance.ode_thm_time_branch_columns_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ManuscriptConformance.ode_thm_time_branch_columns_approx
