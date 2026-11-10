import MeshCertificateODE.Errors
import MeshCertificateODE.Target
import MeshCertificateODE.Certificate
import MeshCertificateODE.Native
import MeshCertificateODE.Binary
import MeshCertificateODE.General
import MeshCertificateODE.Decoder
import MeshCertificateODE.Quadrature
import MeshCertificateODE.Valid
import MeshCertificateODE.Selective

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover every theorem of the library (84 theorems), beginning
with the main theorems, then in module order. Every report lists exactly `propext`,
`Classical.choice` and `Quot.sound`. -/

/-! ### Final theorems: the outcomes under the manuscript's certificates, the transfer to the
padded problem, the target analysis, the certificate bounds and the transfer from `ℂ^N` -/

/-- info: 'SparseHamiltonian.MeshCertificateODE.general_time_cert_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.general_time_cert_outcome

/-- info: 'SparseHamiltonian.MeshCertificateODE.decoder_time_cert_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.decoder_time_cert_outcome

/-- info: 'SparseHamiltonian.MeshCertificateODE.general_time_cert_outcomeI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.general_time_cert_outcomeI

/-- info: 'SparseHamiltonian.MeshCertificateODE.cert_native_time_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.cert_native_time_outcome

/-- info: 'SparseHamiltonian.MeshCertificateODE.cert_native_time_zero_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.cert_native_time_zero_outcome

/-- info: 'SparseHamiltonian.MeshCertificateODE.cert_instanceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.cert_instanceOK

/-- info: 'SparseHamiltonian.MeshCertificateODE.cert_tzInstanceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.cert_tzInstanceOK

/-- info: 'SparseHamiltonian.MeshCertificateODE.CertRestG.padded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.CertRestG.padded

/-- info: 'SparseHamiltonian.MeshCertificateODE.certRestG_decData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.certRestG_decData

/-- info: 'SparseHamiltonian.MeshCertificateODE.cert_prep_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.cert_prep_certificate

/-- info: 'SparseHamiltonian.MeshCertificateODE.cert_target_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.cert_target_facts

/-- info: 'SparseHamiltonian.MeshCertificateODE.quad_target_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.quad_target_error

/-- info: 'SparseHamiltonian.MeshCertificateODE.sampleErr_le_of_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.sampleErr_le_of_lipschitz

/-- info: 'SparseHamiltonian.MeshCertificateODE.sampleErr_umesh_le_of_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.sampleErr_umesh_le_of_lipschitz

/-- info: 'SparseHamiltonian.MeshCertificateODE.dissErr_umesh_le_of_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.dissErr_umesh_le_of_lipschitz

/-- info: 'SparseHamiltonian.MeshCertificateODE.dissErr_le_sampleErr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.dissErr_le_sampleErr

/-- info: 'SparseHamiltonian.MeshCertificateODE.negativity_pathNeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.negativity_pathNeg

/-- info: 'SparseHamiltonian.MeshCertificateODE.pathNeg_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.pathNeg_bound

/-- info: 'SparseHamiltonian.MeshCertificateODE.isMeshPropagator_liftU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.isMeshPropagator_liftU

/-- info: 'SparseHamiltonian.MeshCertificateODE.quadSum_liftU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.quadSum_liftU

/-- info: 'SparseHamiltonian.MeshCertificateODE.mass_eq_quadMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.mass_eq_quadMass

/-- info: 'SparseHamiltonian.MeshCertificateODE.srcAmp_eq_quadAmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.srcAmp_eq_quadAmp

/-- info: 'SparseHamiltonian.MeshCertificateODE.isMeshPropagator_liftV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.isMeshPropagator_liftV

/-- info: 'SparseHamiltonian.MeshCertificateODE.mild_liftV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.mild_liftV

/-- info: 'SparseHamiltonian.MeshCertificateODE.quadSum_liftV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.quadSum_liftV

/-- info: 'SparseHamiltonian.MeshCertificateODE.sampleErr_padLift_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.sampleErr_padLift_le

/-- info: 'SparseHamiltonian.MeshCertificateODE.dissErr_padLift_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.dissErr_padLift_le

/-- info: 'SparseHamiltonian.MeshCertificateODE.binary_ode_time_cert_sel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.binary_ode_time_cert_sel

/-! ### Integrated sample errors (`Errors`) -/

/-- info: 'SparseHamiltonian.MeshCertificateODE.sampleErr_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.sampleErr_nonneg

/-- info: 'SparseHamiltonian.MeshCertificateODE.dissErr_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.dissErr_nonneg

/-- info: 'SparseHamiltonian.MeshCertificateODE.pathNeg_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.pathNeg_nonneg

/-- info: 'SparseHamiltonian.MeshCertificateODE.re_inner_le_dissipativePart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.re_inner_le_dissipativePart

/-- info: 'SparseHamiltonian.MeshCertificateODE.dissipativePart_intervalIntegrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.dissipativePart_intervalIntegrable

/-! ### The discretised target against the certificates (`Target`) -/

/-- info: 'SparseHamiltonian.MeshCertificateODE.umesh_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.umesh_apply

/-- info: 'SparseHamiltonian.MeshCertificateODE.umesh_succ_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.umesh_succ_sub

/-- info: 'SparseHamiltonian.MeshCertificateODE.umesh_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.umesh_mono

/-- info: 'SparseHamiltonian.MeshCertificateODE.isMesh_umesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.isMesh_umesh

/-- info: 'SparseHamiltonian.MeshCertificateODE.umesh_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.umesh_mem

/-- info: 'SparseHamiltonian.MeshCertificateODE.meshWidth_umesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.meshWidth_umesh

/-- info: 'SparseHamiltonian.MeshCertificateODE.maskedPropagator_eq_meshNodeProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.maskedPropagator_eq_meshNodeProduct

/-- info: 'SparseHamiltonian.MeshCertificateODE.quad_node_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.quad_node_error

/-- info: 'SparseHamiltonian.MeshCertificateODE.repLs_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.repLs_facts

/-- info: 'SparseHamiltonian.MeshCertificateODE.sampleErr_repLs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.sampleErr_repLs_le

/-- info: 'SparseHamiltonian.MeshCertificateODE.pathκ_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.pathκ_nonneg

/-- info: 'SparseHamiltonian.MeshCertificateODE.pathκ_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.pathκ_bound

/-- info: 'SparseHamiltonian.MeshCertificateODE.negativity_pathκ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.negativity_pathκ

/-! ### The certificate-form instance conditions (`Certificate`) -/

/-- info: 'SparseHamiltonian.MeshCertificateODE.CertInstanceOK.unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.CertInstanceOK.unitary

/-- info: 'SparseHamiltonian.MeshCertificateODE.CertInstanceOK.neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.CertInstanceOK.neg

/-- info: 'SparseHamiltonian.MeshCertificateODE.CertInstanceOK.repaired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.CertInstanceOK.repaired

/-- info: 'SparseHamiltonian.MeshCertificateODE.cert_target_facts'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.cert_target_facts'

/-- info: 'SparseHamiltonian.MeshCertificateODE.branchU_sub_le'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.branchU_sub_le'

/-- info: 'SparseHamiltonian.MeshCertificateODE.sum_range_negativity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.sum_range_negativity

/-! ### The native outcomes (`Native`) -/

/-- info: 'SparseHamiltonian.MeshCertificateODE.cert_target_facts_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.cert_target_facts_of

/-! ### Time-indexed binary data (`Binary`) -/

/-- info: 'SparseHamiltonian.MeshCertificateODE.gens_HsT_LsT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.gens_HsT_LsT

/-! ### Sparse access of general size (`General`) -/

/-- info: 'SparseHamiltonian.MeshCertificateODE.zextL_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.zextL_apply

/-- info: 'SparseHamiltonian.MeshCertificateODE.zext_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.zext_adjoint

/-- info: 'SparseHamiltonian.MeshCertificateODE.dissipativePart_zext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.dissipativePart_zext

/-- info: 'SparseHamiltonian.MeshCertificateODE.regular_zext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.regular_zext

/-- info: 'SparseHamiltonian.MeshCertificateODE.sampleErr_zext_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.sampleErr_zext_le

/-- info: 'SparseHamiltonian.MeshCertificateODE.dissErr_zext_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.dissErr_zext_le

/-- info: 'SparseHamiltonian.MeshCertificateODE.meshScale_markEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.meshScale_markEmb

/-- info: 'SparseHamiltonian.MeshCertificateODE.lowPart_markEmb_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.lowPart_markEmb_apply

/-- info: 'SparseHamiltonian.MeshCertificateODE.liftU_markEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.liftU_markEmb

/-- info: 'SparseHamiltonian.MeshCertificateODE.solves_add_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.solves_add_const

/-! ### The quadrature and the Lipschitz bounds (`Quadrature`) -/

/-- info: 'SparseHamiltonian.MeshCertificateODE.norm_zsrc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.norm_zsrc

/-- info: 'SparseHamiltonian.MeshCertificateODE.dissipativePart_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.dissipativePart_sub

/-- info: 'SparseHamiltonian.MeshCertificateODE.dissErr_eq_sampleErr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.dissErr_eq_sampleErr

/-! ### Problems on `ℂ^N` (`Valid`) -/

/-- info: 'SparseHamiltonian.MeshCertificateODE.validLiftL_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.validLiftL_apply

/-- info: 'SparseHamiltonian.MeshCertificateODE.validEmb_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.validEmb_adjoint

/-- info: 'SparseHamiltonian.MeshCertificateODE.validRes_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.validRes_adjoint

/-- info: 'SparseHamiltonian.MeshCertificateODE.validLift_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.validLift_adjoint

/-- info: 'SparseHamiltonian.MeshCertificateODE.dissipativePart_validLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.dissipativePart_validLift

/-- info: 'SparseHamiltonian.MeshCertificateODE.regular_validLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.regular_validLift

/-- info: 'SparseHamiltonian.MeshCertificateODE.sampleErr_validLift_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.sampleErr_validLift_le

/-- info: 'SparseHamiltonian.MeshCertificateODE.dissErr_validLift_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.dissErr_validLift_le

/-- info: 'SparseHamiltonian.MeshCertificateODE.validEmb_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.validEmb_ne_zero

/-- info: 'SparseHamiltonian.MeshCertificateODE.meshScale_validEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.meshScale_validEmb

/-- info: 'SparseHamiltonian.MeshCertificateODE.quadMass_validEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.quadMass_validEmb

/-- info: 'SparseHamiltonian.MeshCertificateODE.quadAmp_validEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.quadAmp_validEmb

/-- info: 'SparseHamiltonian.MeshCertificateODE.liftV_validEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.liftV_validEmb

/-! ### The finite-gate-set solver under the certificates (`Selective`) -/

/-- info: 'SparseHamiltonian.MeshCertificateODE.cert_time_outcome_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.cert_time_outcome_of

/-- info: 'SparseHamiltonian.MeshCertificateODE.cert_time_prep_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.cert_time_prep_bounds

/-- info: 'SparseHamiltonian.MeshCertificateODE.cert_time_sel_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.cert_time_sel_outcome

/-- info: 'SparseHamiltonian.MeshCertificateODE.cert_time_sel_prep_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MeshCertificateODE.cert_time_sel_prep_bounds
