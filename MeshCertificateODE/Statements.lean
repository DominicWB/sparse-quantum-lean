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

/-!
# The time-dependent gate solver under the manuscript's certificates: statement guide

Theorem `ode:thm:gates` for the time-dependent problem of `ode:thm:time` requires "the Lipschitz
bounds and represented-sample certificates of Lemma `ode:lem:gate-select`; more generally, a
certificate for the same uniform meshes suffices", and for the source a positive quadrature with the
certificates of eq. `ode:eq:gate-source-certificates`:
`‖x(T) - U(T, 0) x₀ - ∑_i w_i U(T, v_i) b(v_i)‖ ≤ ν B`, `0 < B_m ≤ 2B` and
`B ≤ ḡ ‖x(T)‖`. The released time-dependent gate solvers (`GateODE.Time`, `GateBinaryODETime`,
`GeneralSparseODE`, `GeneralDecoderODE`) were stated under the package's uniform-mesh conditions
(a left-point source quadrature on the data mesh, the amplification bound on the discrete mass and
an explicit discretisation certificate; review item G). This library proves the guarantees of the
native time-dependent protocol (`GateNative.tnprepC`) and of the general-size and decoder protocols
under the manuscript's certificates: a source certificate against the exact propagator of the
generator, and the integrated sample error of the represented samples on the uniform mesh of the
time slots, for represented samples of any sign; for time-indexed binary data it gives the
certificate-form instance conditions of the released oracles (`cert_instanceOK`), and with them the
guarantees of the finite-gate-set protocol of `GateSelective.binary_ode_time_budget_sel`
(`Selective`). The protocols and their resource counts are those of the released solvers; only the
instance conditions change.
Below, `ν'` is the precision of the solver's private simulation (`TParams.nu`), as in
`SourceAccuracyODE`; `ν = ε/(10⁴ ḡ)` is the manuscript's.

## Integrated sample errors (`Errors`)

* `sampleErr t G G̃ = ∑_r ∫_{t_r}^{t_{r+1}} ‖G_r(u) - G̃_r‖ du` and `dissErr t G G̃` (the same for
  the Hermitian parts) for generator pieces `G_r` and operator samples `G̃_r` on any Hilbert space;
  `dissErr_le_sampleErr` for integrable pieces (`RepresentedSampleODE.RegularPieces`).
* `pathNeg`: the path negativity of a slot (the average of `‖Herm(G_r(u) - G̃_r)‖`), a negativity
  bound of the sample for accretive integrable pieces (`pathNeg_bound`) with negativity mass the
  dissipative sample error (`negativity_pathNeg`).
* `sampleErr_le_of_lipschitz`: `β_r`-Lipschitz pieces with left-endpoint sample errors `δ_r` have
  `ΔG ≤ ∑_r (β_r Δ_r² / 2 + δ_r Δ_r)`.

## The discretised target against the certificates (`Target`)

* `umesh T M`: the uniform mesh `t_r = r T / M` of the slots; `quadSum T M U x₀ b`: the propagated
  quadrature sum `U(T, 0) x₀ + ∑_r (T/M) U(T, t_r) b_r`.
* `quad_target_error`: for accretive slot generators, the discretised target of the solver (the
  exponential left-endpoint recurrence, `TParams.target`) is within `ΔG · B_m` of the quadrature
  sum.
* `repLs`, `repLs_facts`, `sampleErr_repLs_le`: the positive repairs `repair L_r κ_r` of the
  dissipative samples with slot-dependent negativity bounds; `pathκ`, `negativity_pathκ`: the path
  negativity bounds of the slots, with negativity mass `ΔD`.
* `cert_target_facts`: from the source certificate `ζ B`, the target error, `B_m ≤ c_q B`,
  `B ≤ ḡ ‖x(T)‖`, `c_q ḡ ≤ g` and `ζ + c_q K ≤ ε / (2000 ḡ)`: the target is nonzero,
  `B_m ≤ 2g ‖y‖` and its direction is within `ε / 1000` of that of `x(T)`.

## The instance conditions and the native outcomes (`Certificate`, `Native`)

* `CertInstanceOK`: the certificate-form instance conditions of the time-dependent gate solver
  (the selection hypotheses of the represented samples without positivity, the loading and weight
  preparation, accretive integrable pieces with their propagator, the source certificate
  `‖x(T) - quadSum‖ ≤ ζ B`, `B_m ≤ c_q B`, `B ≤ ḡ ‖x(T)‖`, `c_q ḡ ≤ g`, and the sample budgets
  `ζ + c_q (ΔG + 2 ΔD) ≤ ε / (2000 ḡ)`, `6 R ΔD ≤ ν'`); `cert_prep_certificate`: the actual
  preparation satisfies the released actual-source certificate for the repaired target;
  `branchU_sub_le'`, `cert_target_facts'`.
* `cert_native_time_outcome`, `cert_native_time_zero_outcome` (`CertTZInstanceOK`): the guarantees
  `SourceAccuracyODE.WOutcome … (ε / 100)` of the released native time-dependent protocol against
  `x(T)`, with source circuits within `8 ν'` (budget `24 d ζ + 3 ζ_s ≤ 25 ν'`, vector error at
  most `81 ν' B_m`); `cert_target_facts_of`.

## Binary data, general sizes and decoders (`Binary`, `General`, `Decoder`)

* `CertRest`, `cert_instanceOK`, `cert_tzInstanceOK`: the conditions for time-indexed binary
  sparse data (`GateBinaryODETime.PubT`), with the samples the lifted matrices `mLift D en (x, r)`.
* `CertRestG`: the conditions on the `k`-qubit index register for sparse access of general size;
  `CertRestG.padded`: they give `CertRest` for the padded problem along the marker embedding
  (`zextL`, `liftU`, `isMeshPropagator_liftU`, `quadSum_liftU`, `sampleErr_zext_le`,
  `dissErr_zext_le`); `general_time_cert_outcomeI` (through any implementation of the padded
  oracles) and `general_time_cert_outcome` (the protocol `GeneralSparseODE.GPubT.prep`): the
  guarantees for the coherent sampled-time supplied oracles `primsTG D x`, against the marker
  embedding of `x(T)`.
* `certRestG_decData`, `decoder_time_cert_outcome`: the same for a decoder with an exact binary
  entry decoding (`GeneralDecoderODE.prepTD`).

## The quadrature and the Lipschitz bounds (`Quadrature`)

* `quadMass`, `quadAmp`: the coefficient mass `B_m = ‖x₀‖ + (T/M) ∑_r ‖b_r‖` of the slot quadrature
  and the amplitudes `√(‖x₀‖ / B_m)`, `√((T/M) ‖b_r‖ / B_m)` of its weight preparation, those of the
  solver (`mass_eq_quadMass`, `srcAmp_eq_quadAmp`); for `T > 0` a positive quadrature with weights
  `w_r ≥ 0` at the slot times is the case `(T/M) b_r = w_r b(t_r)`.
* `sampleErr_umesh_le_of_lipschitz`: on the uniform mesh, `β`-Lipschitz pieces with left-endpoint
  sample errors `δ_r` have `ΔG ≤ β T² / (2M) + (T/M) ∑_r δ_r` (Lipschitz bounds as in Lemma
  `ode:lem:gate-select`); `dissErr_umesh_le_of_lipschitz`: the same for the Hermitian parts,
  `ΔD ≤ β_D T² / (2M) + (T/M) ∑_r δ^D_r` (`dissErr_eq_sampleErr`, `dissipativePart_sub`).

## Problems on `ℂ^N` (`Valid`)

* `liftV N k U`: the lift of a propagator on `ℂ^N` to the index register (the embedding `validEmb`
  of the propagated valid part, the invalid part kept); `isMeshPropagator_liftV`: it is the
  propagator of the lifted pieces `validLift ∘ G_r`; `mild_liftV`: the embedding of a mild solution
  on `ℂ^N` is the mild solution of the lifted problem; `regular_validLift` (with
  `GeneralSparseODE.accretive_validLift`) for the pieces.
* `meshScale_validEmb`, `quadMass_validEmb`, `quadAmp_validEmb`, `quadSum_liftV`,
  `validEmb_ne_zero`: the source scale, the coefficient mass, the weight-preparation amplitudes
  and the propagated quadrature sum of the embedded source are those on `ℂ^N`.
* `validLiftL`, `validLift_adjoint`, `dissipativePart_validLift`, `sampleErr_validLift_le`,
  `dissErr_validLift_le`; `sampleErr_padLift_le`, `dissErr_padLift_le`: the integrated sample
  errors of the lifted pieces against the lifts `padLift D (x, r)` of the samples are at most those
  on `ℂ^N` against the samples `matrixOperator (D.matrix (x, r))`.

## The finite-gate-set solver (`Selective`)

* `cert_time_outcome_of`: for every compiled preparation `P` on the released trial register that
  is valid, never touches the fresh flag and pool of the exact zero tests, and is within `ν'/3 + δ`
  on clean inputs of every lifted operator `liftB (conj U)` that the native preparation is within
  `δ` of, the four-attempt
  protocol `nprotocol P (2g)` (the actual `P`, the exact zero tests, the literal reverse-adjoint of
  `P` as its inverse) has the guarantees `GateNative.NOutcome` against `x(T)` under
  `CertInstanceOK`: every successful trial within `ε/500` of `x(T)/‖x(T)‖` up to a global phase,
  success at least `2/3`, conditional trace distance `ε`. The selected-vector error, the amplitude
  and the direction come from the certificate of the actual preparation for the repaired target
  (`cert_prep_certificate`, `cert_target_facts'`); the solver's guarantee is not a hypothesis.
* `cert_time_prep_bounds`: the preparation certificate of the actual preparation `P`: the repaired
  target `y` is nonzero, `‖y‖ ≤ B_m ≤ g ‖y‖`, its direction is within `ε/1000` of that of `x(T)`,
  and the selected vector `d = good† (P s)` of the output on the seed has the selected-vector
  error `‖3 B_m d - y‖ ≤ 10 ν' B_m` and the amplitude `‖d‖ ≥ 1/(3g) - 10ν'/3`.
* `cert_time_sel_outcome`, `cert_time_sel_prep_bounds`: the same for the selective preparation
  `GateSelective.selPrep hS (ν'/3) (tnprepC …)`, through `selPrep_valid`, `selPrep_pres` and
  `selPrep_approx`.
* `binary_ode_time_cert_sel`: for time-indexed binary data (exact binary entries, the uniform mesh,
  the sources at the slot times; the case `PubT.OK`, `T > 0` and `η_H + η_D > 0`), the resource
  conclusions of `GateSelective.binary_ode_time_budget_sel` (valid trials over `𝒢`, synthesised
  occurrences, gates and matrix calls with the supplied loading and weight-preparation circuits
  charged linearly and outside the synthesis logarithm, qubits) and the guarantees under
  `CertRest`, for supplied circuits within `ζ_s` with `98304 q* ζ + 3 ζ_s ≤ ν'`. The exact zero
  tests are assumed in the gate set (`zeroTestKinds ⊆ 𝒢`) and the gate set is closed under
  adjoints (`AdjClosed 𝒢`).

## Use

`ManuscriptConformance.GateODETimeCert` (`ode_thm_gates_time_cert`,
`ode_thm_gates_time_decoder_cert`) states the time-dependent Theorem `ode:thm:gates` for sparse
access of general size (with the decoder `c₀(X + iY)`, resp. a decoder with an exact binary entry
decoding) under these certificates, with the source quadrature nodes at the slot times `r T / M`
(this package's own condition; in the manuscript "the nodes can be computed coherently from their
labels at polynomial cost"), for the protocols of the public data with the amplification
bound `2ḡ`; `ManuscriptConformance.gate_select_sample_certificate` bounds the two sample budgets by
the Lipschitz bounds and sample errors of the pieces and of their Hermitian parts (with the lemma's
conditions at `δ = ν` it gives the first budget, and the second at a `δ` finer by a factor below
`14`; see that module). `ManuscriptConformance.GateODETimeCertValid`
(`ode_thm_gates_time_cert_valid`, `ode_thm_gates_time_decoder_cert_valid`) states the guarantees for
a problem on `ℂ^N` through `Valid`. `ManuscriptConformance.GateODETimeCertFinite`
(`ode_thm_gates_time_cert_finite`) states the finite-gate-set protocol of
`binary_ode_time_cert_sel` with its source executions.
-/
