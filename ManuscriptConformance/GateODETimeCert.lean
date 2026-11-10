import ManuscriptConformance.GateODEDecoder
import ManuscriptConformance.ODETime
import MeshCertificateODE.Decoder
import MeshCertificateODE.Quadrature

/-!
# Conformance: Theorem `ode:thm:gates`, time-dependent, with the manuscript's certificates

Theorem `ode:thm:gates` for the time-dependent problem of `ode:thm:time`
asks for "the Lipschitz bounds and represented-sample certificates of Lemma `ode:lem:gate-select`;
more generally, a certificate for the same uniform meshes suffices", and for the source a positive
quadrature with the certificates of eq. `ode:eq:gate-source-certificates` and the paragraph before
it: `‖x(T) - U(T, 0) x₀ - ∑_i w_i U(T, v_i) b(v_i)‖ ≤ ν B`, `0 < B_m ≤ 2B` and
`B ≤ ḡ ‖x(T)‖`, `B = ‖x₀‖ + ∫ ‖b‖`. The theorems `ode_thm_gates_time_general` and
`ode_thm_gates_time_decoder` take instead the package's conditions `formal_uniformMeshG` (review
item G: a left-point source quadrature on the data mesh, the amplification bound on the discrete
mass and the package's explicit discretisation certificate). This module states both theorems with
the manuscript's certificates (library `MeshCertificateODE`):

* **Mesh and path.** The power-of-two mesh `t_r = r T / M`, `M = 2^m`, of the time slots, at least
  the coarsest admissible one of the padded problem (`odeMeshG … (2ḡ) … ≤ m`, the package's own
  mesh condition; Theorem `ode:thm:gates` chooses `M` from Lemma `ode:lem:gate-select` with
  `δ = ν`). The generator is given by pieces `G_r`
  on the closed mesh intervals (jumps at the mesh points allowed), accretive (the true path is
  dissipative) and integrable (`RepresentedSampleODE.RegularPieces`), with their propagator `U`
  (`formal_classicalPropagator`, review item J); the solution `x` is the mild solution
  (`RepresentedSampleODE.MildSolution`) for forcing pieces `b_r`, and `B = Mesh.meshScale`.
* **Source.** A positive quadrature with nodes at the slot times `t_r`, `r < M`: the source vector
  `b̃_r` of slot `r` enters with weight `T/M`, so for `T > 0` weights `w_r ≥ 0` at the slot times
  are the case `(T/M) b̃_r = w_r b(t_r)` (the node `T` is not a slot time). The weight preparation
  has the amplitudes `√(‖x₀‖ / B_m)` and `√((T/M) ‖b̃_r‖ / B_m)` (`MeshCertificateODE.quadAmp`,
  `B_m = quadMass`), and the loading prepares the directions of `x₀` and of the `b̃_r`. The
  certificates: `x(T) ≠ 0`, `B ≤ ḡ ‖x(T)‖`, `B_m ≤ 2 B` and
  `‖x(T) - U(T, 0) x₀ - ∑_r (T/M) U(T, t_r) b̃_r‖ ≤ ζ B` (`MeshCertificateODE.quadSum`). A
  quadrature on a coarser power-of-two mesh is the case of zero weights off its nodes.
* **Sample certificate** for the same uniform mesh: the integrated sample error
  `ΔG = ∑_r ∫ ‖G_r(u) - G̃_r‖ du` of the represented samples `G̃_r` on the index register
  (`padLift D (x, r)`; `MeshCertificateODE.sampleErr`) and its dissipative part `ΔD` (`dissErr`)
  with `ζ + 2 (ΔG + 2 ΔD) ≤ ε / (2000 ḡ)` and `6 R ΔD ≤ ν'`, `R = radius(2ḡ, ε) = 4 log(16/ν)`,
  `ν' = precision(2ḡ, ε) = ν/8`: the budgets of `ode_thm_time` with `c_q = 2` (the second bounds
  the dissipative part of the integrated branch sample error in the branch certificate). The
  uniform mesh of the slots is the mesh of the initial branch in the lemma. Lipschitz bounds give
  the two errors: `gate_select_sample_certificate` (`ΔG ≤ β T²/(2M) + (T/M) ∑_r δ_r` for
  `β`-Lipschitz pieces with left-endpoint sample errors `δ_r`, and
  `ΔD ≤ β_D T²/(2M) + (T/M) ∑_r δ^D_r` for their Hermitian parts).
* **Protocol.** The package's four-attempt protocol for the public data with the amplification
  bound `2ḡ ≥ B_m / ‖x(T)‖` (internal ratio `4ḡ`, accuracy `ε/2`), fixed before the instance.
* **Conclusions.** Those of `ode_thm_gates_time_general`, resp. `ode_thm_gates_time_decoder`, with
  the manuscript's `q`, `𝔟` and `ν = ε / (10⁴ ḡ)` (source circuits within `ν`), for absolute
  constants `C = 108 C₀` (`C₀` those of the two theorems); represented samples of any sign.

**Formal restrictions.** `formal_gbarOne` (`ḡ ≥ 1`), `formal_classicalPropagator` (review item J),
and for `ode_thm_gates_time_cert` `formal_binaryDecoder` (review item B2; the decoder theorem
`ode_thm_gates_time_decoder_cert` takes a decoder with an exact binary entry decoding instead).
What remains of review item G: the source nodes are the slot times `r T / M`, this package's own
condition (in the manuscript "the nodes can be computed coherently from their labels at polynomial
cost", in the text before Theorem `ode:thm:gates`), and the second sample budget is the branch
budget of the formal solver. The lemma's
conditions at `δ = ν` (`L_* ≥ Lip(H) + R_ms Lip(D)`, `M ≥ 8 L_* T²/δ`, integrated error at most
`δ/16` of the represented samples on every branch `H + kD`, `|k| ≤ R_ms`, for the manuscript's
frequency radius `R_ms = 2 + 2 log((1 + 1/(2π))/ν)`, eq. `ode:eq:nu`) give the first budget
(`ΔG ≤ 3ν/16`) and, from the branches `k = ±R_ms`, `R_ms ΔD ≤ ν/8 = ν'`, where the second asks
`R ΔD ≤ ν'/6` at the
radius `R` of the formal solver, `2 R_ms < R ≤ 2.3 R_ms` (as `ν ≤ 5·10⁻⁵`): they give it at a
`δ` finer by the factor `6R/R_ms < 14`. The theorems are stated on the index register, for the
matrix extended by zero to the index words `≥ N`; `GateODETimeCertValid` states their guarantees
for a problem on `ℂ^N` (`ode_thm_gates_time_cert_valid`, `ode_thm_gates_time_decoder_cert_valid`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit
  SparseHamiltonian.GateNative SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget
  SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GeneralSparseODE (GPubT markEmb padLift primsTG)
open SparseHamiltonian.GeneralDecoderODE (BinDecode DW prepTD)
open SparseHamiltonian.GateBinaryODETime (PubT)
open SparseHamiltonian.ZeroTimeGateODE (BTPublicOK0 BTZeroCase)
open SparseHamiltonian.MeshCertificateODE (umesh quadSum quadAmp quadMass sampleErr dissErr)
open SparseHamiltonian.GeneralSourceExtensions (Mesh.meshScale)
open GatePointerEncoding (wordValue)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

universe u

/-! ### Real estimates for the amplification bound `2ḡ` -/

/-- **The query shape of twice the amplification bound**: `q(2ḡ, ε) ≤ 2 q(ḡ, ε)`. -/
theorem odeShape_two_le {s T ηH ηD g ε : ℝ} (hs : 0 ≤ s) (hT : 0 ≤ T) (hH : 0 ≤ ηH)
    (hD : 0 ≤ ηD) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    odeShape s T ηH ηD (2 * g) ε ≤ 2 * odeShape s T ηH ηD g ε := by
  have hg0 : 0 < g := by linarith
  have hℓ1 : 1 ≤ Real.log (10000 * g / ε) := ImprovedODEQueryBudget.logBudget_ge_one g ε hg hε hε1
  have e : Real.log (10000 * (2 * g) / ε) = Real.log 2 + Real.log (10000 * g / ε) := by
    rw [show 10000 * (2 * g) / ε = 2 * (10000 * g / ε) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    norm_num at this
    linarith
  have hlog20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold odeShape
  rw [e]
  set ℓ := Real.log (10000 * g / ε) with hℓ
  set ℓ' := Real.log 2 + ℓ with hℓ'def
  have hℓ' : ℓ' ≤ 2 * ℓ := by linarith
  have hℓ'0 : 0 ≤ ℓ' := by linarith
  have hTD : 0 ≤ T * ηD := mul_nonneg hT hD
  have hTH : 0 ≤ T * ηH := mul_nonneg hT hH
  have hΘ' : T * ηH + T * ηD * ℓ' ≤ 2 * (T * ηH + T * ηD * ℓ) := by
    have := mul_le_mul_of_nonneg_left hℓ' hTD
    linarith
  have hΘ0 : 0 ≤ T * ηH + T * ηD * ℓ := by
    have := mul_nonneg hTD (by linarith : (0 : ℝ) ≤ ℓ)
    linarith
  have h1 : Real.sqrt s * (T * ηH + T * ηD * ℓ') ≤ 2 * (Real.sqrt s * (T * ηH + T * ηD * ℓ)) := by
    have := mul_le_mul_of_nonneg_left hΘ' (Real.sqrt_nonneg s)
    linarith
  have h2 : Real.sqrt (s * (T * ηH + T * ηD * ℓ') * ℓ') ≤
      2 * Real.sqrt (s * (T * ηH + T * ηD * ℓ) * ℓ) := by
    have h3 : s * (T * ηH + T * ηD * ℓ') * ℓ' ≤ 4 * (s * (T * ηH + T * ηD * ℓ) * ℓ) := by
      have h4 := mul_le_mul hΘ' hℓ' hℓ'0 (by linarith)
      have h5 := mul_le_mul_of_nonneg_left h4 hs
      linarith
    have h6 := Real.sqrt_le_sqrt h3
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      at h6
    exact h6
  linarith

/-- **The word budget of twice the amplification bound**: `𝔟(q', 2ḡ) ≤ 𝔟(q, ḡ) + 2` for
`q' ≤ 2 q`. -/
theorem bitB_two_le {bd N M M' : ℕ} {Q Q' g ε : ℝ} (hQ : 0 ≤ Q) (hQQ : Q' ≤ 2 * Q) (hQ' : 0 ≤ Q')
    (hg : 0 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    bitB bd N M M' Q' (2 * g) ε ≤ bitB bd N M M' Q g ε + 2 := by
  unfold bitB
  have hQg : 0 ≤ Q * g := mul_nonneg hQ hg
  have hX : 1 ≤ (Q * g + 1) / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have hpos : 0 < (Q' * (2 * g) + 1) / ε := by
    refine div_pos ?_ hε
    have := mul_nonneg hQ' (by linarith : (0 : ℝ) ≤ 2 * g)
    linarith
  have h2 : (Q' * (2 * g) + 1) / ε ≤ 4 * ((Q * g + 1) / ε) ^ 1 := by
    rw [pow_one, mul_div_assoc', div_le_div_iff_of_pos_right hε]
    have := mul_le_mul_of_nonneg_right hQQ (by linarith : (0 : ℝ) ≤ 2 * g)
    linarith
  have h3 := logb_le_mul_pow _ 4 _ 2 1 hpos hX (by norm_num) h2
  push_cast at h3
  linarith

/-- `(𝔟' + 1)³ ≤ 27 (𝔟 + 1)³` for `0 ≤ 𝔟' ≤ 𝔟 + 2`. -/
theorem cube_two_le {B B' : ℝ} (hB : 0 ≤ B) (hB' : 0 ≤ B') (h : B' ≤ B + 2) :
    (B' + 1) ^ 3 ≤ 27 * (B + 1) ^ 3 := by
  have h1 : B' + 1 ≤ 3 * (B + 1) := by linarith
  have h2 : (B' + 1) ^ 3 ≤ (3 * (B + 1)) ^ 3 := pow_le_pow_left₀ (by linarith) h1 3
  have e : (3 * (B + 1)) ^ 3 = 27 * (B + 1) ^ 3 := by ring
  linarith

/-- The gate bound for twice the amplification bound. -/
theorem gates_two_le {C₀ g Q Q' Y Y' Gs Z : ℝ} (hC : 0 ≤ C₀) (hg : 0 ≤ g) (hQ : 0 ≤ Q)
    (hQQ : Q' ≤ 2 * Q) (hY' : 0 ≤ Y') (hYY : Y' ≤ 27 * Y) (hGs : 0 ≤ Gs) (hZ : 0 ≤ Z) :
    C₀ * (2 * g) * (Q' * Y' + Gs + Z) ≤ 108 * C₀ * g * (Q * Y + Gs + Z) := by
  have h1 : Q' * Y' ≤ 54 * (Q * Y) := by
    have := mul_le_mul hQQ hYY hY' (by linarith)
    linarith
  have h2 : Q' * Y' + Gs + Z ≤ 54 * (Q * Y + Gs + Z) := by linarith
  have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hC (by linarith : (0 : ℝ) ≤ 2 * g))
  linarith

/-- The call bound for twice the amplification bound. -/
theorem calls_two_le {C₀ g Q Q' I S W : ℝ} {z : Prop} [Decidable z] (hC : 0 ≤ C₀) (hg : 0 ≤ g)
    (hQ : 0 ≤ Q) (hQQ : Q' ≤ 2 * Q) (hI : 0 ≤ I) (hS : 0 ≤ S)
    (hW : W ≤ (if z then 0 else C₀ * (2 * g) * Q' * I) + C₀ * (2 * g) * S) :
    W ≤ (if z then 0 else 108 * C₀ * g * Q * I) + 108 * C₀ * g * S := by
  have hS' : C₀ * (2 * g) * S ≤ 108 * C₀ * g * S := by
    have := mul_nonneg (mul_nonneg hC hg) hS
    linarith
  by_cases hz : z
  · rw [if_pos hz] at hW ⊢
    linarith
  · rw [if_neg hz] at hW ⊢
    have h2 := mul_le_mul_of_nonneg_right hQQ hI
    have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hC (by linarith : (0 : ℝ) ≤ 2 * g))
    have h4 : 0 ≤ C₀ * g * (Q * I) := mul_nonneg (mul_nonneg hC hg) (mul_nonneg hQ hI)
    linarith

/-- **The source budget for the amplification bound `2ḡ`**: for the public data `odePubT … (2ḡ) …`
and source circuits within `ν = ε / (10⁴ ḡ) = 8 ν'` (`ν'` the precision of the internal ratio `4ḡ`
and accuracy `ε/2`), `98304 q' ζ + 3 ζ_s ≤ 25 ν'`. -/
theorem odePubT_zeta2 {q : PubT} {k sb : ℕ} {hsb : sb ≤ k} {b : ℕ} {c0 etaH etaD T gbar ε : ℝ}
    {m : ℕ} (hq : q = odePubT k sb hsb b c0 etaH etaD T (2 * gbar) ε m) (hH : 0 ≤ etaH)
    (hD : 0 ≤ etaD) (hT : 0 ≤ T) (hg : 1 ≤ gbar) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∀ ζs : ℝ, ζs ≤ ImprovedODEQueryBudget.precision gbar ε →
      98304 * GateODEBudget.qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ + 3 * ζs ≤
        25 * q.params.nu := by
  subst hq
  have hg4 : 1 ≤ 2 * (2 * gbar) := by linarith
  have hε' : 0 < ε / 2 := by linarith
  have hε1' : ε / 2 ≤ 1 := by linarith
  have hν : 0 < ImprovedODEQueryBudget.precision (2 * (2 * gbar)) (ε / 2) :=
    ImprovedODEQueryBudget.precision_pos _ _ hg4 hε'
  have hν1 : ImprovedODEQueryBudget.precision (2 * (2 * gbar)) (ε / 2) ≤ 1 :=
    (ImprovedODEQueryBudget.precision_le_one_ten_thousandth _ _ hg4 hε1').trans (by norm_num)
  have hQ1 : 1 ≤ GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD (2 * (2 * gbar)) (ε / 2) :=
    GateRemarks.ODE.one_le_qOf hT hH hD hg4 hε' hε1'
  obtain ⟨-, -, -, hz2⟩ := zetaOf_spec hν hν1 hQ1
  intro ζs h
  have hg0 : gbar ≠ 0 := (by linarith : (0 : ℝ) < gbar).ne'
  have e8 : ImprovedODEQueryBudget.precision gbar ε =
      8 * ImprovedODEQueryBudget.precision (2 * (2 * gbar)) (ε / 2) := by
    rw [show ImprovedODEQueryBudget.precision gbar ε = ε / (10000 * gbar) from rfl,
      show ImprovedODEQueryBudget.precision (2 * (2 * gbar)) (ε / 2) =
        ε / 2 / (10000 * (2 * (2 * gbar))) from rfl]
    field_simp
    ring
  rw [e8] at h
  show 98304 * GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD (2 * (2 * gbar)) (ε / 2) *
      zetaOf (ImprovedODEQueryBudget.precision (2 * (2 * gbar)) (ε / 2))
        (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD (2 * (2 * gbar)) (ε / 2)) + 3 * ζs ≤
    25 * ImprovedODEQueryBudget.precision (2 * (2 * gbar)) (ε / 2)
  linarith

/-! ### The Lipschitz bounds of the selection lemma -/

/-- **The Lipschitz bounds and represented-sample errors of Lemma `ode:lem:gate-select` bound the
sample budgets** of `ode_thm_gates_time_cert` and `ode_thm_gates_time_decoder_cert`: for
`β`-Lipschitz pieces on the closed slot intervals of the uniform mesh `M = 2^m` with left-endpoint
sample errors `δ_r`, whose Hermitian (dissipative) parts are `β_D`-Lipschitz with left-endpoint
dissipative sample errors `δ^D_r`, the integrated sample error is at most
`Δ = β T²/(2M) + (T/M) ∑_r δ_r` and its dissipative part at most
`Δ_D = β_D T²/(2M) + (T/M) ∑_r δ^D_r` (each the freezing error and the integrated
represented-sample error), so `ζ + 2 (Δ + 2 Δ_D) ≤ ε/(2000 ḡ)` and `6 R Δ_D ≤ ν'` give the two
budgets. Under the lemma's conditions at `δ = ν` (see the module docstring) `Δ ≤ 3ν/16` and
`R_ms Δ_D ≤ ν/8 = ν'`, `R_ms` the manuscript's frequency radius: they give the first budget, and
the second at a `δ` finer by the factor `6R/R_ms < 14`. -/
theorem gate_select_sample_certificate {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] {T : ℝ} (hT : 0 ≤ T) (m : ℕ) (G : Fin (2 ^ m) → ℝ → V →L[ℂ] V)
    (Gt : Fin (2 ^ m) → V →L[ℂ] V) (β βD : ℝ) (δ δD : Fin (2 ^ m) → ℝ)
    (hLip : ∀ r : Fin (2 ^ m), ∀ u ∈ Set.Icc (umesh T (2 ^ m) r) (umesh T (2 ^ m) ((r : ℕ) + 1)),
      ∀ w ∈ Set.Icc (umesh T (2 ^ m) r) (umesh T (2 ^ m) ((r : ℕ) + 1)),
        ‖G r u - G r w‖ ≤ β * |u - w|)
    (hδ : ∀ r : Fin (2 ^ m), ‖G r (umesh T (2 ^ m) r) - Gt r‖ ≤ δ r)
    (hLipD : ∀ r : Fin (2 ^ m), ∀ u ∈ Set.Icc (umesh T (2 ^ m) r) (umesh T (2 ^ m) ((r : ℕ) + 1)),
      ∀ w ∈ Set.Icc (umesh T (2 ^ m) r) (umesh T (2 ^ m) ((r : ℕ) + 1)),
        ‖ODEHermitianReduction.dissipativePart (G r u) -
          ODEHermitianReduction.dissipativePart (G r w)‖ ≤ βD * |u - w|)
    (hδD : ∀ r : Fin (2 ^ m),
      ‖ODEHermitianReduction.dissipativePart (G r (umesh T (2 ^ m) r) - Gt r)‖ ≤ δD r)
    {gbar ε ζ : ℝ} (hg : 1 ≤ gbar) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h1 : ζ + 2 * ((β * T ^ 2 / (2 * ((2 ^ m : ℕ) : ℝ)) + T / ((2 ^ m : ℕ) : ℝ) * ∑ r, δ r) +
        2 * (βD * T ^ 2 / (2 * ((2 ^ m : ℕ) : ℝ)) + T / ((2 ^ m : ℕ) : ℝ) * ∑ r, δD r)) ≤
      ε / (2000 * gbar))
    (h2 : 6 * TimeDependentODE.radius (2 * gbar) ε *
        (βD * T ^ 2 / (2 * ((2 ^ m : ℕ) : ℝ)) + T / ((2 ^ m : ℕ) : ℝ) * ∑ r, δD r) ≤
      TimeDependentODE.precision (2 * gbar) ε) :
    ζ + 2 * (sampleErr (umesh T (2 ^ m)) G Gt + 2 * dissErr (umesh T (2 ^ m)) G Gt) ≤
        ε / (2000 * gbar) ∧
      6 * TimeDependentODE.radius (2 * gbar) ε * dissErr (umesh T (2 ^ m)) G Gt ≤
        TimeDependentODE.precision (2 * gbar) ε := by
  have hS := MeshCertificateODE.sampleErr_umesh_le_of_lipschitz hT (Nat.two_pow_pos m) G Gt β δ
    hLip hδ
  have hSD := MeshCertificateODE.dissErr_umesh_le_of_lipschitz hT (Nat.two_pow_pos m) G Gt βD δD
    hLipD hδD
  have hR0 : 0 ≤ TimeDependentODE.radius (2 * gbar) ε :=
    ImprovedODEQueryBudget.radius_nonneg (2 * (2 * gbar)) (ε / 2) (by linarith) (by linarith)
      (by linarith)
  refine ⟨by linarith, ?_⟩
  have h3 := mul_le_mul_of_nonneg_left hSD
    (by linarith : (0 : ℝ) ≤ 6 * TimeDependentODE.radius (2 * gbar) ε)
  linarith

/-! ### Theorem `ode:thm:gates`, time-dependent, with the manuscript's certificates -/

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:gates` for sparse access of general size, time-dependent coefficients, with
the manuscript's certificates**. See the module docstring. For the
time-indexed general sparse access `D` (`2^{k-1} < N ≤ 2^k`) with the decoder `c₀(X + iY)` on a
mesh `M = 2^m` at least the coarsest admissible one, public parameters of at most `b_data` bits,
every `T ≥ 0`, `ḡ ≥ 1`, `0 < ε ≤ 1/2` and valid loading and weight-preparation circuits calling
the coherent sampled-time supplied oracles, the protocol
`nprotocol ((odePubTG … (2ḡ) …).prep N 0 loadC wpC) (4ḡ)` (fixed before the instance) has valid
trials, at most `C ḡ [q (𝔟+1)³ + G_src + A_src]` elementary gates in every history, at most
`C (𝔟+1)³ + C A_src` qubits, at most `C ḡ q` calls of each supplied matrix oracle (none if
`T = 0` or `η_H + η_D = 0`) besides `C ḡ` times the calls inside the source circuits, and on every
instance with the manuscript's certificates (the positive quadrature of the slot nodes with
`B ≤ ḡ ‖x(T)‖`, `B_m ≤ 2B` and source error `ζ B`, and the sample certificate
`ζ + 2 (ΔG + 2 ΔD) ≤ ε / (2000 ḡ)`, `6 R ΔD ≤ ν'`) and source circuits within `ν = ε/(10⁴ ḡ)`:
success at least `2/3`, conditional output within trace distance `ε` of `x(T)/‖x(T)‖` on the index
register (marker clean), and every successful trial within `ε` of it up to a global phase. The
represented samples may have dissipative parts of any sign. Formal restrictions:
`formal_binaryDecoder`, `formal_gbarOne`, `formal_classicalPropagator`. The finite-gate-set bound
with `G_src` entering linearly is a separate result for the binary format (`N = 2^{k_x}`, `T > 0`,
`η_H + η_D > 0`): `GateSelective.binary_ode_time_budget_sel`. -/
theorem ode_thm_gates_time_cert :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (bd : ℕ) (c0 etaH etaD T gbar ε : ℝ) (m : ℕ)
        (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b),
        odeMeshG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε ≤ m →
        2 ^ k < 2 * N → formal_binaryDecoder D c0 → comp_bits b bd [c0, T, etaH, etaD] →
        ∀ (hg : formal_gbarOne gbar) {Zs : Type} [Fintype Zs] [DecidableEq Zs]
          (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
          (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)),
          (∀ i ∈ loadC, i.Valid) → (∀ i ∈ wpC, i.Valid) →
          0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 →
          (∀ j, ∀ i ∈ trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep N
            (fun _ => false) loadC wpC) j, i.Valid) ∧
          ((nprotocol ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep N
              (fun _ => false) loadC wpC) (2 * (2 * gbar))
              (one_le_two_mul (one_le_two_mul hg))).worstCost wGateN : ℝ) ≤
            C * gbar * (odeShape s T etaH etaD gbar ε *
                (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
              ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
          (odeQubitsTG (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m) Zs : ℝ) ≤
            C * (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
              C * Fintype.card Zs ∧
          (∀ c : Query → Bool,
            ((nprotocol ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep N
              (fun _ => false) loadC wpC) (2 * (2 * gbar))
                (one_le_two_mul (one_le_two_mul hg))).worstCost (wCallN c) : ℝ) ≤
            (if T = 0 ∨ etaH + etaD = 0 then 0 else
              C * gbar * odeShape s T etaH etaD gbar ε *
                ((if c Query.rowLocation then 1 else 0) +
                  (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))) +
            C * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
          ∀ x : X,
            (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaH ^ 2) →
            (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaH ^ 2) →
            (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaD ^ 2) →
            (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaD ^ 2) →
            ∀ (Jl : Bool × (Fin m → Bool) → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
              (Wp : Matrix (Cfg (Fin (m + 1))) (Cfg (Fin (m + 1))) ℂ)
              (G : Fin (2 ^ m) → ℝ → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
              (bf : Fin (2 ^ m) → ℝ → Reg (Fin k) ℂ) (sol : ℝ → Reg (Fin k) ℂ)
              (bs : ℕ → Reg (Fin k) ℂ) (U : ℝ → Reg (Fin k) ℂ → ℝ → Reg (Fin k) ℂ) (ζ ζs : ℝ),
            0 ≤ ζs →
            ApproxOn CleanX (nrun (primsTG D x) loadC) (liftB (loadIdeal Jl)) ζs →
            ApproxOn CleanX (nrun (primsTG D x) wpC) (liftB (matOp Wp)) ζs →
            ζs ≤ ImprovedODEQueryBudget.precision gbar ε →
            (∀ c, OracleCircuit.IsUnitary (Jl c)) → Wp.conjTranspose * Wp = 1 →
            Wp * Wp.conjTranspose = 1 →
            (∀ w : Cfg (Fin (m + 1)), Wp w (fun _ => false) =
              ((quadAmp T m (sol 0) bs (w 0, Fin.tail w) : ℝ) : ℂ)) →
            (sol 0 ≠ 0 → Jl (false, fun _ => false) (seedV (S := Fin k)) =
              ODEStateNormalization.unitDirection (sol 0)) →
            (∀ w : Fin m → Bool, bs (wordValue w) ≠ 0 → Jl (true, w) (seedV (S := Fin k)) =
              ODEStateNormalization.unitDirection (bs (wordValue w))) →
            (∀ r : Fin (2 ^ m), ∀ u ∈ Set.Icc (umesh T (2 ^ m) r) (umesh T (2 ^ m) ((r : ℕ) + 1)),
              TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces (umesh T (2 ^ m)) G →
            RepresentedSampleODE.MildSolution (umesh T (2 ^ m)) T bf sol U →
            formal_classicalPropagator G (umesh T (2 ^ m)) T U →
            sol T ≠ 0 →
            Mesh.meshScale sol bf (umesh T (2 ^ m)) ≤ gbar * ‖sol T‖ →
            quadMass T m (sol 0) bs ≤ 2 * Mesh.meshScale sol bf (umesh T (2 ^ m)) →
            ‖sol T - quadSum T (2 ^ m) U (sol 0) bs‖ ≤ ζ * Mesh.meshScale sol bf (umesh T (2 ^ m)) →
            ζ + 2 * (sampleErr (umesh T (2 ^ m)) G (fun r => padLift D (x, r)) +
              2 * dissErr (umesh T (2 ^ m)) G (fun r => padLift D (x, r))) ≤
              ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (2 * gbar) ε *
                dissErr (umesh T (2 ^ m)) G (fun r => padLift D (x, r)) ≤
              TimeDependentODE.precision (2 * gbar) ε →
            HeraldedOutput (nprotocol ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε
                m).prep N (fun _ => false) loadC wpC) (2 * (2 * gbar))
                (one_le_two_mul (one_le_two_mul hg)))
              (primsTG D x) (ODEStateNormalization.unitDirection
                (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (sol T))) ε ∧
            ∀ j : ℕ, ((goodN)†) (nrun (primsTG D x)
                (trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep N
                  (fun _ => false) loadC wpC) j) sN) ≠ 0 →
              ∃ ω : ℂ, ‖ω‖ = 1 ∧
                ‖ω • ODEStateNormalization.unitDirection (((goodN)†)
                    (nrun (primsTG D x) (trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T
                      (2 * gbar) ε m).prep N (fun _ => false) loadC wpC) j) sN)) -
                  ODEStateNormalization.unitDirection
                    (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (sol T))‖ ≤ ε := by
  obtain ⟨C₀, hC₀, h⟩ := ode_thm_gates_time_general.{u}
  refine ⟨108 * C₀, by positivity, ?_⟩
  intro X N s k b bd c0 etaH etaD T gbar ε m D hm hk hF hbits hg Zs _ _ loadC wpC hloadV hwpV hH
    hD hT hε hε2
  have hg1 : 1 ≤ gbar := hg
  have hg2 : formal_gbarOne (2 * gbar) := one_le_two_mul hg
  have hε1 : ε ≤ 1 := by linarith
  have hg0 : 0 ≤ gbar := by linarith
  obtain ⟨hV, hG0, hQ0, hC0, -⟩ := h bd c0 etaH etaD T (2 * gbar) ε m D hm hk hF hbits hg2 loadC
    wpC hloadV hwpV hH hD hT hε hε2
  -- the comparisons of the shapes and the word budgets
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hQ2 := odeShape_two_le hs0 hT hH hD hg1 hε hε1
  have hQ1 : 1 ≤ odeShape s T etaH etaD gbar ε :=
    GateRemarks.ODE.one_le_qOf (s := (s : ℝ)) hT hH hD hg1 hε hε1
  have hB0 : 0 ≤ bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hQ1' : 1 ≤ odeShape s T etaH etaD (2 * gbar) ε :=
    GateRemarks.ODE.one_le_qOf (s := (s : ℝ)) hT hH hD (by linarith) hε hε1
  have hB0' : 0 ≤ bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD (2 * gbar) ε) (2 * gbar) ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) (by linarith)) hε hε1
  have hBB := bitB_two_le (bd := bd) (N := N) (M := 2 ^ m) (M' := 2 ^ m) (by linarith) hQ2
    (by linarith) hg0 hε hε1
  have hY := cube_two_le hB0 hB0' hBB
  have hY0 : 0 ≤ (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 := by
    positivity
  have hY0' : 0 ≤ (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD (2 * gbar) ε) (2 * gbar) ε +
      1) ^ 3 := by positivity
  have hZ : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
  refine ⟨hV, ?_, ?_, ?_, ?_⟩
  · -- gates
    exact hG0.trans (gates_two_le hC₀.le hg0 (by linarith) hQ2 hY0' hY (by positivity) hZ)
  · -- qubits
    have h1 := mul_le_mul_of_nonneg_left hY hC₀.le
    have h2 := mul_nonneg hC₀.le hZ
    have h3 := mul_nonneg hC₀.le hY0
    linarith
  · -- calls
    intro c
    have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
        (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    exact calls_two_le hC₀.le hg0 (by linarith) hQ2 hI0 (by positivity) (hC0 c)
  · -- the guarantees
    intro x hrH hcH hrD hcD Jl Wp G bf sol bs U ζ ζs hζs0 hload hwp hacc hJl hWl hWr hWp hinit
      hforce hacc' hreg hmild hprop hne hscale hmass hsrc hbud hbranch
    obtain ⟨hbd, -, -, -, -⟩ := hbits
    set q := odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m with hqdef
    have hqp : q.pub = odePubT (k + 1) (sbP s) ((sbP_le D.s_le_pow).trans (Nat.le_succ k)) b c0
        etaH etaD T (2 * gbar) ε m := rfl
    have hq : BTPublicOK0 q.pub := by
      rw [hqp]
      exact odePubT_ok _ hF.hb hF.hc0 hH hD hT hg2 hε hε2 hm
    have hγ := odePubT_gamma hqp hF.hb hbd
    have hζs := odePubT_zeta2 hqp hH hD hT hg1 hε hε2
    have hγ' : ¬ BTZeroCase q.pub →
        q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := by
      intro hz
      have h := hγ
      rw [if_neg hz] at h
      exact h
    have hR : MeshCertificateODE.CertRestG q D x Jl Wp G bf sol U bs gbar 2 ζ :=
      { load_unitary := hJl
        prep_left := hWl
        prep_right := hWr
        prep := fun w => by
          rw [MeshCertificateODE.srcAmp_eq_quadAmp q.pub.params hT]
          exact hWp w
        init_load := hinit
        forcing_load := hforce
        accretive := hacc'
        regular := hreg
        mild := hmild
        propagator := hprop
        target_ne := hne
        gb_pos := by linarith
        cq_nonneg := by norm_num
        scale := hscale
        mass := by
          rw [MeshCertificateODE.mass_eq_quadMass q.pub.params hT]
          exact hmass
        ratio := le_rfl
        source := hsrc
        budget := hbud
        branch := hbranch }
    -- the public data is passed literally (not as the local definition `q`), so that the
    -- outcome has the types of the statement and the final unification is syntactic
    have o := (MeshCertificateODE.general_time_cert_outcome
      (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m) hq hγ' D (fun _ => false) hF.zero
      hF.dec loadC hloadV wpC hwpV x hrH hcH hrD hcD Jl Wp G bf sol U bs gbar 2 ζ ζs hζs0 hload hwp
      (hζs ζs hacc) hR).mono (β' := ε) (by
        show ε / 100 ≤ ε
        linarith)
    rw [markEmb_eq_cleanAlong] at o
    exact ⟨⟨o.success_two_thirds, o.output_density, o.conditional_error⟩, o.trial_direction⟩

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:gates` for sparse access of general size with binary entry decoding,
time-dependent coefficients, with the manuscript's certificates**. See the module docstring. As
`ode_thm_gates_time_cert`, for a decoder that has an exact binary entry decoding `dc` of its stored
words into `b'`-bit components (`b' ≤ b_data`; `BinaryEntryDecoding`) and the protocol
`nprotocol (prepTD (odePubTG … (2ḡ) …) N dc loadC wpC) (4ḡ)`: at most
`C ḡ [q ((𝔟+1)³ + cost dc) + G_src + A_src]` elementary gates and `C (𝔟+1)³ + C A_src + C wires dc`
qubits, the calls and the guarantees of `ode_thm_gates_time_cert`. Formal restrictions:
`formal_gbarOne`, `formal_classicalPropagator`. The finite-gate-set bound with `G_src` entering
linearly is a separate result for the binary format (`N = 2^{k_x}`, `T > 0`, `η_H + η_D > 0`):
`GateSelective.binary_ode_time_budget_sel`. -/
theorem ode_thm_gates_time_decoder_cert :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b b' A : ℕ} (bd : ℕ) (c0 etaH etaD T gbar ε : ℝ) (m : ℕ)
        (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b) (dc : BinDecode b b' A),
        odeMeshG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε ≤ m →
        2 ^ k < 2 * N → BinaryEntryDecoding D dc c0 → comp_bits b' bd [c0, T, etaH, etaD] →
        ∀ (hg : formal_gbarOne gbar) {Zs : Type} [Fintype Zs] [DecidableEq Zs]
          (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
          (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)),
          (∀ i ∈ loadC, i.Valid) → (∀ i ∈ wpC, i.Valid) →
          0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 →
          (∀ j, ∀ i ∈ trialN (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N
            dc loadC wpC) j, i.Valid) ∧
          ((nprotocol (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
              loadC wpC) (2 * (2 * gbar)) (one_le_two_mul (one_le_two_mul hg))).worstCost
                wGateN : ℝ) ≤
            C * gbar * (odeShape s T etaH etaD gbar ε *
                ((bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
                  dc.cost) +
              ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
          (odeQubitsTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) dc Zs : ℝ) ≤
            C * (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
              C * Fintype.card Zs + C * dc.wires ∧
          (∀ c : Query → Bool,
            ((nprotocol (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
              loadC wpC) (2 * (2 * gbar)) (one_le_two_mul (one_le_two_mul hg))).worstCost
                (wCallN c) : ℝ) ≤
            (if T = 0 ∨ etaH + etaD = 0 then 0 else
              C * gbar * odeShape s T etaH etaD gbar ε *
                ((if c Query.rowLocation then 1 else 0) +
                  (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))) +
            C * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
          ∀ x : X,
            (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaH ^ 2) →
            (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaH ^ 2) →
            (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaD ^ 2) →
            (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaD ^ 2) →
            ∀ (Jl : Bool × (Fin m → Bool) → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
              (Wp : Matrix (Cfg (Fin (m + 1))) (Cfg (Fin (m + 1))) ℂ)
              (G : Fin (2 ^ m) → ℝ → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
              (bf : Fin (2 ^ m) → ℝ → Reg (Fin k) ℂ) (sol : ℝ → Reg (Fin k) ℂ)
              (bs : ℕ → Reg (Fin k) ℂ) (U : ℝ → Reg (Fin k) ℂ → ℝ → Reg (Fin k) ℂ) (ζ ζs : ℝ),
            0 ≤ ζs →
            ApproxOn CleanX (nrun (primsTG D x) loadC) (liftB (loadIdeal Jl)) ζs →
            ApproxOn CleanX (nrun (primsTG D x) wpC) (liftB (matOp Wp)) ζs →
            ζs ≤ ImprovedODEQueryBudget.precision gbar ε →
            (∀ c, OracleCircuit.IsUnitary (Jl c)) → Wp.conjTranspose * Wp = 1 →
            Wp * Wp.conjTranspose = 1 →
            (∀ w : Cfg (Fin (m + 1)), Wp w (fun _ => false) =
              ((quadAmp T m (sol 0) bs (w 0, Fin.tail w) : ℝ) : ℂ)) →
            (sol 0 ≠ 0 → Jl (false, fun _ => false) (seedV (S := Fin k)) =
              ODEStateNormalization.unitDirection (sol 0)) →
            (∀ w : Fin m → Bool, bs (wordValue w) ≠ 0 → Jl (true, w) (seedV (S := Fin k)) =
              ODEStateNormalization.unitDirection (bs (wordValue w))) →
            (∀ r : Fin (2 ^ m), ∀ u ∈ Set.Icc (umesh T (2 ^ m) r) (umesh T (2 ^ m) ((r : ℕ) + 1)),
              TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces (umesh T (2 ^ m)) G →
            RepresentedSampleODE.MildSolution (umesh T (2 ^ m)) T bf sol U →
            formal_classicalPropagator G (umesh T (2 ^ m)) T U →
            sol T ≠ 0 →
            Mesh.meshScale sol bf (umesh T (2 ^ m)) ≤ gbar * ‖sol T‖ →
            quadMass T m (sol 0) bs ≤ 2 * Mesh.meshScale sol bf (umesh T (2 ^ m)) →
            ‖sol T - quadSum T (2 ^ m) U (sol 0) bs‖ ≤ ζ * Mesh.meshScale sol bf (umesh T (2 ^ m)) →
            ζ + 2 * (sampleErr (umesh T (2 ^ m)) G (fun r => padLift D (x, r)) +
              2 * dissErr (umesh T (2 ^ m)) G (fun r => padLift D (x, r))) ≤
              ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (2 * gbar) ε *
                dissErr (umesh T (2 ^ m)) G (fun r => padLift D (x, r)) ≤
              TimeDependentODE.precision (2 * gbar) ε →
            HeraldedOutput (nprotocol (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar)
                ε m) N dc loadC wpC) (2 * (2 * gbar)) (one_le_two_mul (one_le_two_mul hg)))
              (primsTG D x) (ODEStateNormalization.unitDirection
                (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (sol T))) ε ∧
            ∀ j : ℕ, ((goodN)†) (nrun (primsTG D x)
                (trialN (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
                  loadC wpC) j) sN) ≠ 0 →
              ∃ ω : ℂ, ‖ω‖ = 1 ∧
                ‖ω • ODEStateNormalization.unitDirection (((goodN)†)
                    (nrun (primsTG D x) (trialN (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T
                      (2 * gbar) ε m) N dc loadC wpC) j) sN)) -
                  ODEStateNormalization.unitDirection
                    (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (sol T))‖ ≤ ε := by
  obtain ⟨C₀, hC₀, h⟩ := ode_thm_gates_time_decoder.{u}
  refine ⟨108 * C₀, by positivity, ?_⟩
  intro X N s k b b' A bd c0 etaH etaD T gbar ε m D dc hm hk hF hbits hg Zs _ _ loadC wpC hloadV
    hwpV hH hD hT hε hε2
  have hg1 : 1 ≤ gbar := hg
  have hg2 : formal_gbarOne (2 * gbar) := one_le_two_mul hg
  have hε1 : ε ≤ 1 := by linarith
  have hg0 : 0 ≤ gbar := by linarith
  obtain ⟨hV, hG0, hQ0, hC0, -⟩ := h bd c0 etaH etaD T (2 * gbar) ε m D dc hm hk hF hbits hg2
    loadC wpC hloadV hwpV hH hD hT hε hε2
  -- the comparisons of the shapes and the word budgets
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hQ2 := odeShape_two_le hs0 hT hH hD hg1 hε hε1
  have hQ1 : 1 ≤ odeShape s T etaH etaD gbar ε :=
    GateRemarks.ODE.one_le_qOf (s := (s : ℝ)) hT hH hD hg1 hε hε1
  have hB0 : 0 ≤ bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hQ1' : 1 ≤ odeShape s T etaH etaD (2 * gbar) ε :=
    GateRemarks.ODE.one_le_qOf (s := (s : ℝ)) hT hH hD (by linarith) hε hε1
  have hB0' : 0 ≤ bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD (2 * gbar) ε) (2 * gbar) ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) (by linarith)) hε hε1
  have hBB := bitB_two_le (bd := bd) (N := N) (M := 2 ^ m) (M' := 2 ^ m) (by linarith) hQ2
    (by linarith) hg0 hε hε1
  have hY := cube_two_le hB0 hB0' hBB
  have hY0 : 0 ≤ (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 := by
    positivity
  have hY0' : 0 ≤ (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD (2 * gbar) ε) (2 * gbar) ε +
      1) ^ 3 := by positivity
  have hZ : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
  have hCst : (0 : ℝ) ≤ dc.cost := Nat.cast_nonneg _
  have hWr : (0 : ℝ) ≤ dc.wires := Nat.cast_nonneg _
  refine ⟨hV, ?_, ?_, ?_, ?_⟩
  · -- gates
    exact hG0.trans (gates_two_le hC₀.le hg0 (by linarith) hQ2 (by positivity)
      (by linarith) (by positivity) hZ)
  · -- qubits
    have h1 := mul_le_mul_of_nonneg_left hY hC₀.le
    have h2 := mul_nonneg hC₀.le hZ
    have h3 := mul_nonneg hC₀.le hY0
    have h4 := mul_nonneg hC₀.le hWr
    linarith
  · -- calls
    intro c
    have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
        (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    exact calls_two_le hC₀.le hg0 (by linarith) hQ2 hI0 (by positivity) (hC0 c)
  · -- the guarantees
    intro x hrH hcH hrD hcD Jl Wp G bf sol bs U ζ ζs hζs0 hload hwp hacc hJl hWl hWr' hWp hinit
      hforce hacc' hreg hmild hprop hne hscale hmass hsrc hbud hbranch
    obtain ⟨hbd, -, -, -, -⟩ := hbits
    set q := odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m with hqdef
    have hqp : q.pub = odePubT (k + 1) (sbP s) ((sbP_le D.s_le_pow).trans (Nat.le_succ k)) b' c0
        etaH etaD T (2 * gbar) ε m := rfl
    have hq : BTPublicOK0 q.pub := by
      rw [hqp]
      exact odePubT_ok _ hF.hb hF.hc0 hH hD hT hg2 hε hε2 hm
    have hγ := odePubT_gamma hqp hF.hb hbd
    have hζs := odePubT_zeta2 hqp hH hD hT hg1 hε hε2
    have hγ' : ¬ BTZeroCase q.pub →
        q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := by
      intro hz
      have h := hγ
      rw [if_neg hz] at h
      exact h
    have hR : MeshCertificateODE.CertRestG q D x Jl Wp G bf sol U bs gbar 2 ζ :=
      { load_unitary := hJl
        prep_left := hWl
        prep_right := hWr'
        prep := fun w => by
          rw [MeshCertificateODE.srcAmp_eq_quadAmp q.pub.params hT]
          exact hWp w
        init_load := hinit
        forcing_load := hforce
        accretive := hacc'
        regular := hreg
        mild := hmild
        propagator := hprop
        target_ne := hne
        gb_pos := by linarith
        cq_nonneg := by norm_num
        scale := hscale
        mass := by
          rw [MeshCertificateODE.mass_eq_quadMass q.pub.params hT]
          exact hmass
        ratio := le_rfl
        source := hsrc
        budget := hbud
        branch := hbranch }
    -- the public data is passed literally (not as the local definition `q`), so that the
    -- outcome has the types of the statement and the final unification is syntactic
    have o := (MeshCertificateODE.decoder_time_cert_outcome
      (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) hq hγ' D dc hF.exact loadC hloadV
      wpC hwpV x hrH hcH hrD hcD Jl Wp G bf sol U bs gbar 2 ζ ζs hζs0 hload hwp
      (hζs ζs hacc) hR).mono (β' := ε) (by
        show ε / 100 ≤ ε
        linarith)
    rw [markEmb_eq_cleanAlong] at o
    exact ⟨⟨o.success_two_thirds, o.output_density, o.conditional_error⟩, o.trial_direction⟩

end

end ManuscriptConformance
