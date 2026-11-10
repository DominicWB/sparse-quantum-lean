import ManuscriptConformance.Appendix
import GateOptimalPrecision.NativeCayley
import GateOptimalPrecision.NativeSigned
import GateOptimalPrecision.ClippedTheorem
import GateOptimalPrecision.Combine
import GateOptimalBinary.ClipTransfer

/-!
# Conformance: native-model forms of `gate:prop:finite`, `gate:prop:signed`, `gate:prop:core`

The native-model forms of Propositions `gate:prop:finite`, `gate:prop:signed` and `gate:prop:core`
of Appendix `gate:sec:proof`, before finite-set synthesis, in the package's circuit model: a
released circuit is a list of instructions on qubit wires (`GateCircuit.Instr`) with elementary
gates, calls of the boundary `U_J`, and *private calls* of an abstract controlled private
operation; its native form replaces every private call by a native implementation of the private
operation, in the native gate model of `GateDefs` (one-qubit gates with at most three controls, so
arbitrary single-qubit gates).

* `gate_prop_finite` (native-model form of Proposition `gate:prop:finite`, before finite-set
  synthesis): an ideal amplified circuit with error at
  most `ε/2` and `n_P ≤ c_*R` private calls, with a native private operation whose arithmetic has
  accuracy `ξ/4`, `ξ = ε/(4 c_* R)` (each native private call then has error at most `ξ`), has a
  native form (`GateOptimalPrecision.native_transfer`) with error at most `ε`, a constant number of
  primitive calls per private call, at most `G_known + n_P G_P(ξ) ≤ G_known + c_*R G_P(ξ)` gates
  (`G_known` the known gates of the circuit, `U_J`'s elementary gates included, not the
  manuscript's `G₀` of eq. `gate:eq:budgets`;
  `G_P(ξ) = 2|V| + 2|arith| + 2b_P + b_T + 1` the gates of one native private call) and
  `|wires| + |S| + A_P` qubits (`A_P = |Z| + b_T + b_P + A + 3`). In the native gate model there is
  no synthesis term: the manuscript's `G₀ log((G₀+1)/ε)` is the cost of finite-set synthesis
  (`GateSynth.synthBudget`, which in the package multiplies every native gate, those of the private
  calls included, by the synthesis length: review item F). Synthesis is applied only end to end,
  to the whole circuit, in the finite-set theorems (`gate_thm_main`, through
  `GateOptimalBinary.gate_optimal_binary_synth`, and `gate_thm_main_decoder`).
  Review item I: every oracle call of the circuit, boundary calls included, must be controlled by
  the sector wire (`SecOK`), and the private operation must be a native operation of the package's
  compute–rotate–uncompute form with its public conditions (`NativeOp.Public`, `NativeOK`,
  `ArithOK`): the form of the bounded-regime circuit. The signed circuit, whose factor calls are
  unconditional, and the clipped circuit, whose private operation is factor-conjugated, have their
  own native forms, `gate_prop_signed_native` and `gate_prop_core_native`.
* `gate_prop_signed` (exact-gate part of the native-model form of Proposition `gate:prop:signed`,
  before finite-set synthesis; abstract factor): the signed-factor circuit uses
  `n ≤ 4·10¹⁰ (√(T_f b_f) + √(T_f r_f) + r_f)` factor calls (`R = n`) and as many boundary calls,
  at most `64·3⁸ (n+1)(a + m + r + 1)` known gates on `2a + 3m + 6r + 5` wires with
  `2^r < 2(n+2)` and `2^m ≤ 10⁷ n⁴/ε` (`m = O(log((n+1)/ε))`), and full-output error `ε`, for
  `ε ≤ 1/64`, with the success projection and the sign reflection on designated flag qubits
  `f ≠ z` of the ancillas (`wKnown`), before finite-set synthesis;
  `gate_prop_signed_native`: the native-model form of Proposition `gate:prop:signed`, before
  finite-set synthesis (`GateOptimalPrecision.signed_native_simulation`, with
  the unconditional factor calls replaced by the native factor: the package's
  compute–local-factor–uncompute macro, whose public conditions, native identity and arithmetic
  accuracy `ξ` are hypotheses, `FactorOp.Public`, `FactorNativeOK`, `FactorArithOK`), with at most
  `G_known + n G_P(ξ)` gates (`G_known = 64·3⁸ (N+1)(a + m + r + 1) + 7n|U_J|` the known gates,
  `U_J`'s elementary gates included, one boundary call per factor call, `N` the clock weights,
  `n = 2·3⁸ N` for `b_f > ε`; `G_P(ξ) = 2|W| + 2|arith| + 2b_P + b_T + 4` the gates of one native
  factor call), and error at most `ε + 3ξn`: the explicit-gates form with `R = n`.
* `gate_prop_core` (exact-gate part of the native-model form of Proposition `gate:prop:core`, before
  finite-set synthesis; abstract private operation): the clipped-transducer circuit uses exactly
  `6d` private calls and `12d` boundary calls, at most `200 (d+1)(a + m + r + 1)` known gates on
  `2a + 3m + 6r + 3` wires with `2^m < 2d²/(5ε)` (`m = O(log((d+1)/ε))`) and `2^r ≤ 4(d+1)`
  (`R = 2d` reuse steps), `d ≤ 21520 √(B r_a)` (`B = σΘ`, the package's `s τ`), and full-output
  error `ε`; `gate_prop_core_native`: the native-model form of Proposition `gate:prop:core`, before
  finite-set synthesis, with the factor-conjugated native private call
  `D = U_f† C U_f` of Section `gate:sec:native` (`GateOptimalBinary.ClipNative`: a native factor
  `U_f` of arithmetic accuracy `ξ` and a native rotation `C` of angle accuracy `ζ`, with their
  public conditions and native identities; `GateOptimalBinary.clip_transfer`), with `6d` copies of
  the primitive calls of one native private call, at most `G_known + 6d G_P` gates
  (`G_known = 200 (d+1)(a + m + r + 1) + 84d|U_J|` the known gates, `U_J`'s elementary gates
  included; `G_P` the gates of one native private call) and error at most `ε + 6d(6ξ + 4ζ)`: the
  explicit-gates form with `R = 2d`, before finite-set synthesis.

The explicit-gates forms (`gate:eq:explicit-gates`, `gate:eq:explicit-space`) are thus, in the
native gate model, `gate_prop_finite` for the bounded-regime circuit, `gate_prop_signed_native` for
the signed-factor circuit and `gate_prop_core_native` for the clipped circuit; for binary sparse
data the native private operations are constructed in `GateOptimalBinary` (used in `GateMain`). The
factor interface of `gate_prop_signed` and `gate_prop_signed_native` is the wire-defined `wKnown`
(the success projection and the sign reflection are qubits of the factor's ancillas, the form of the
stable local factor of Section `gate:sec:native`), where Section `gate:sec:signed` allows any known
success projection `Π` and sign reflection `Z` (review item H).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8192

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim SparseHamiltonian.GateNative
  GateOptimalPrecision
open LargeSparsityCore LargeSparsityCore.Parameters
open scoped InnerProduct InnerProductSpace

/-! ### Native-model form of Proposition `gate:prop:finite`, before finite-set synthesis -/

section Finite

variable {S Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **Native-model form of Proposition `gate:prop:finite` (explicit resource bound), before
finite-set synthesis: native gates.** See the module docstring. `cR` is the manuscript's `c_* R`. -/
theorem gate_prop_finite {a m r K : ℕ} (prim : J → Reg Y R →L[ℂ] Reg Y R)
    (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp Empty (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB Empty (Fin a ⊕ S) Z)) {ε cR : ℝ} (hε : 0 < ε) (hcR : 0 < cR)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec (ε / (4 * cR) / 4))
    (D : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (hD : IsUnitary D)
    (hN : NativeOK prim nd (selOp (fun _ : Cfg Empty => D)))
    (l : List (Instr (Wire a m r K))) (hv : ∀ i ∈ l, i.Valid Wire.anc)
    (hsec : ∀ i ∈ l, SecOK (wireRel a m r K) i) (hR : (nPriv l : ℝ) ≤ cR)
    (U : Reg S R →L[ℂ] Reg S R)
    (hrel : ‖run (simSem (P := Reg S R) (UJop (R := R) UJg) D) l ∘L io - io ∘L U‖ ≤ ε / 2) :
    (∀ i ∈ nativeOf UJg nd ar l, i.Valid) ∧
    (∀ p : J → Bool, nCallsN p (nativeOf UJg nd ar l) = nPriv l * (2 * nCallsN p nd.V)) ∧
    nGatesN (nativeOf UJg nd ar l) ≤ (nGates l + nUJ l * (7 * UJg.length)) +
      nPriv l * (2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)) ∧
    Fintype.card (HW (Wire a m r K) S Empty Z ar.bT ar.bP ar.A) =
      Fintype.card (Wire a m r K) + Fintype.card S +
        (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) ∧
    IsUnitary (nrun prim (nativeOf UJg nd ar l)) ∧
    ‖nrun prim (nativeOf UJg nd ar l) ∘L sysEmb (io (P := Reg S R)) -
        sysEmb (io (P := Reg S R)) ∘L U‖ ≤ ε := by
  have hξ0 : 0 ≤ ε / (4 * cR) / 4 := by positivity
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    native_transfer prim hprim UJg hUJg nd hnd ar hξ0 har D hD hN l hv hsec U hrel
  refine ⟨h1, h2, h3, h4, h5, h6.trans ?_⟩
  have hk : 0 ≤ ε / (4 * cR) := by positivity
  have e1 : (4 : ℝ) * (ε / (4 * cR) / 4) = ε / (4 * cR) := by ring
  have hcR' : cR ≠ 0 := hcR.ne'
  have e2 : cR * (ε / (4 * cR)) = ε / 4 := by
    rw [mul_div_assoc', mul_comm cR ε, mul_div_mul_right _ _ hcR']
  have h7 : (nPriv l : ℝ) * (ε / (4 * cR)) ≤ cR * (ε / (4 * cR)) :=
    mul_le_mul_of_nonneg_right hR hk
  rw [e1]
  linarith

end Finite

/-! ### Native-model form of Proposition `gate:prop:signed`, before finite-set synthesis -/

section Signed

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The factor calls of the nontrivial signed-factor circuit: `n = 2·3⁸ N`, `N` the clock
weights. -/
theorem sg_nPriv (a : ℕ) (f z : Fin a) (lam δ t ε : ℝ) (h : ε < sgB lam δ t) :
    nPriv (sgCircuit a f z lam δ t ε) = 2 * 3 ^ 8 * sigN (sgQ lam δ t ε) (sgOrd lam δ t ε) := by
  unfold sgCircuit
  rw [if_neg (not_le.mpr h)]
  split_ifs
  · exact (sig_counts a f z _ _ ε _).1
  · rw [nPriv_invList]
    exact (sig_counts a f z _ _ ε _).1

/-- **Exact-gate part of the native-model form of Proposition `gate:prop:signed` (signed-factor gate
bound), before finite-set synthesis; abstract factor.** See the module
docstring. With `T_f = λ|t|`, `b_f = T_f δ` and `r_f = L/log(e + L/b_f)` (`signedBound`, eq.
`opt:eq:signed-bound`): the circuit is valid, it is empty if `b_f ≤ ε`, and otherwise it makes
`n ≤ 4·10¹⁰ (√(T_f b_f) + √(T_f r_f) + r_f)` factor calls and as many boundary calls, at most
`64·3⁸ (n+1)(a + m + r + 1)` elementary gates on `2a + 3m + 6r + 5` wires with `2^r < 2(n+2)` and
`2^m ≤ 10⁷ n⁴/ε`, and its full output is within `ε` of `e^{-itH}`, `H = λ B†ZB`. -/
theorem gate_prop_signed [FiniteDimensional ℂ P] {a : ℕ} (UJ U : Anc a P →L[ℂ] Anc a P)
    (hUJ : IsUnitary UJ) (hU : IsUnitary U) {f z : Fin a} (hfz : f ≠ z) {lam δ : ℝ}
    (hlam : 0 < lam) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hD : (wKnown UJ (unitary_adj_comp hUJ) f z).Dop U ≤ (δ : ℂ) • (1 : P →L[ℂ] P))
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    (∀ i ∈ sgCircuit a f z lam δ t ε, i.Valid Wire.anc) ∧
    ((nPriv (sgCircuit a f z lam δ t ε) : ℝ) ≤
      4 * 10 ^ 10 * signedBound (lam * |t|) (lam * |t| * δ) ε) ∧
    (lam * |t| * δ ≤ ε → sgCircuit a f z lam δ t ε = []) ∧
    nUJ (sgCircuit a f z lam δ t ε) = nPriv (sgCircuit a f z lam δ t ε) ∧
    nGates (sgCircuit a f z lam δ t ε) ≤ 64 * 3 ^ 8 * ((nPriv (sgCircuit a f z lam δ t ε) + 1) *
      (a + sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε + sigR (sgQ lam δ t ε) (sgOrd lam δ t ε) +
        1)) ∧
    Fintype.card (SgWire a lam δ t ε) =
      2 * a + 3 * sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε +
        6 * sigR (sgQ lam δ t ε) (sgOrd lam δ t ε) + 5 ∧
    (ε < lam * |t| * δ →
      2 ^ sigR (sgQ lam δ t ε) (sgOrd lam δ t ε) < 2 * (nPriv (sgCircuit a f z lam δ t ε) + 2) ∧
      ((2 ^ sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε : ℕ) : ℝ) ≤
        10 ^ 7 * ((nPriv (sgCircuit a f z lam δ t ε) : ℕ) : ℝ) ^ 4 / ε) ∧
    ‖run (simSem (liftA UJ) (liftA U)) (sgCircuit a f z lam δ t ε) ∘L io -
        io ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) • sgHam UJ hUJ f z lam U)‖ ≤ ε := by
  obtain ⟨hv, hn, hUJn, hg, hcard, he, hm, hr⟩ :=
    signed_gate_simulation UJ U hUJ hU hfz hlam hδ hδ1 hD t hε hε1
  have hb0 : 0 ≤ lam * |t| * δ := by positivity
  refine ⟨hv, ?_, ?_, hUJn, ?_, hcard, ?_, he⟩
  · -- the factor calls
    by_cases hsmall : sgB lam δ t ≤ ε
    · rw [if_pos hsmall] at hn
      have := signedBound_nonneg (T := lam * |t|) hb0 hε (by linarith)
      linarith
    · rw [if_neg hsmall] at hn
      have hb : sgB lam δ t ≠ 0 := by
        push Not at hsmall
        exact (hε.trans hsmall).ne'
      rw [rb_eq_signedR hb] at hn
      exact hn
  · -- the identity for `b_f ≤ ε`
    intro h
    unfold sgCircuit
    rw [if_pos (show sgB lam δ t ≤ ε from h)]
  · -- the gates
    by_cases hsmall : sgB lam δ t ≤ ε
    · have h0 : sgCircuit a f z lam δ t ε = [] := by
        unfold sgCircuit
        rw [if_pos hsmall]
      rw [h0]
      simp [nGates]
    · push Not at hsmall
      rw [sg_nPriv a f z lam δ t ε hsmall]
      exact hg.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
        (Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (by norm_num)) 1)))
  · -- the label and slot widths
    intro h
    have hN := sg_nPriv a f z lam δ t ε h
    rw [hN]
    refine ⟨lt_of_lt_of_le hr (Nat.mul_le_mul_left 2
      (Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (by norm_num)) 2)), ?_⟩
    have h1 : ((sigN (sgQ lam δ t ε) (sgOrd lam δ t ε) : ℕ) : ℝ) ≤
        ((2 * 3 ^ 8 * sigN (sgQ lam δ t ε) (sgOrd lam δ t ε) : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_mul_of_pos_left _ (by norm_num) :
        sigN (sgQ lam δ t ε) (sgOrd lam δ t ε) ≤ 2 * 3 ^ 8 * sigN (sgQ lam δ t ε) (sgOrd lam δ t ε))
    have h2 := pow_le_pow_left₀ (Nat.cast_nonneg _) h1 4
    have h3 : 10 ^ 7 * ((sigN (sgQ lam δ t ε) (sgOrd lam δ t ε) : ℕ) : ℝ) ^ 4 / ε ≤
        10 ^ 7 * ((2 * 3 ^ 8 * sigN (sgQ lam δ t ε) (sgOrd lam δ t ε) : ℕ) : ℝ) ^ 4 / ε :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by norm_num)) hε.le
    exact (hm h).trans h3

end Signed

section SignedNative

variable {S Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y] {bT bP A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **Native-model form of Proposition `gate:prop:signed`, before finite-set synthesis: its
explicit-gates form with native factors.** With `U_J`
given by elementary gates `UJg` and the factor `U_B` implemented natively by `fo` (compute `W`,
the factor arithmetic of accuracy `ξ`, the local factor gates, the inverse arithmetic, `W†`; the
native identity `FactorNativeOK` and the accuracy `FactorArithOK` as hypotheses, as in
Section `gate:sec:native`), the native signed-factor circuit is valid, makes exactly
`2n` copies of the primitive calls of `W` (`n` the factor calls of `gate_prop_signed`,
`n ≤ 4·10¹⁰ (√(T_f b_f) + √(T_f r_f) + r_f)`), has at most
`64·3⁸ (N+1)(a + m + r + 1) + n (7|UJg| + 2|W| + 2|arith| + 2b_P + b_T + 4)` elementary gates
(`N` the clock weights, `n = 2·3⁸ N` unless `b_f ≤ ε`) on
`2a + 3m + 6r + 5 + |S| + |Z| + b_T + b_P + A + 3` wires, and its full output is within
`ε + 3ξn` of `e^{-itH}`. The native factor's public conditions (`FactorOp.Public`: valid
preparation, decoder independent of the three local qubits, `‖c‖ ≤ 1`) are a hypothesis; the term
`7|UJg|` per factor call is the accompanying boundary call. As in `gate_prop_signed`, `ε ≤ 1/64`
and the success projection and the sign reflection act on designated flag qubits `f ≠ z` of the
ancillas (`wKnown`); there is no finite-set synthesis. -/
theorem gate_prop_signed_native [FiniteDimensional ℂ R] {a : ℕ}
    (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (UJ U : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (hJ : UJop (R := R) UJg = UJ)
    (hUJ : IsUnitary UJ) (hU : IsUnitary U) (fo : FactorOp (Fin (a + 1) ⊕ S) Z Y J bT bP A)
    (hpub : fo.Public) {ξ : ℝ} (hξ : 0 ≤ ξ) (har : FactorArithOK fo ξ)
    (hN : FactorNativeOK prim fo (selOp (fun _ : Cfg Empty => liftA U)))
    {f z : Fin a} (hfz : f ≠ z) {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hD : (wKnown UJ (unitary_adj_comp hUJ) f z).Dop U ≤ (δ : ℂ) • (1 : Reg S R →L[ℂ] Reg S R))
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    (∀ i ∈ sgNative UJg fo f z lam δ t ε, i.Valid) ∧
    (∀ p : J → Bool, nCallsN p (sgNative UJg fo f z lam δ t ε) =
      nPriv (sgCircuit a f z lam δ t ε) * (2 * nCallsN p fo.W)) ∧
    ((nPriv (sgCircuit a f z lam δ t ε) : ℝ) ≤
      4 * 10 ^ 10 * signedBound (lam * |t|) (lam * |t| * δ) ε) ∧
    (ε < lam * |t| * δ →
      nPriv (sgCircuit a f z lam δ t ε) = 2 * 3 ^ 8 * sigN (sgQ lam δ t ε) (sgOrd lam δ t ε)) ∧
    nGatesN (sgNative UJg fo f z lam δ t ε) ≤
      64 * 3 ^ 8 * ((sigN (sgQ lam δ t ε) (sgOrd lam δ t ε) + 1) *
        (a + sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε + sigR (sgQ lam δ t ε) (sgOrd lam δ t ε) +
          1)) +
      nPriv (sgCircuit a f z lam δ t ε) * (7 * UJg.length +
        (2 * nGatesN fo.W + 2 * fo.circ.length + (2 * bP + bT + 4))) ∧
    Fintype.card (HW (SgWire a lam δ t ε) S Empty Z bT bP A) =
      2 * a + 3 * sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε +
        6 * sigR (sgQ lam δ t ε) (sgOrd lam δ t ε) + 5 + Fintype.card S +
          (Fintype.card Z + bT + bP + A + 3) ∧
    IsUnitary (nrun prim (sgNative UJg fo f z lam δ t ε)) ∧
    ‖nrun prim (sgNative UJg fo f z lam δ t ε) ∘L sysEmb (io (P := Reg S R)) -
        sysEmb (io (P := Reg S R)) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • sgHam (P := Reg S R) UJ hUJ f z lam U)‖ ≤
      ε + (nPriv (sgCircuit a f z lam δ t ε) : ℝ) * (3 * ξ) := by
  obtain ⟨hv, hc, -, hg, hcard, hu, he⟩ :=
    signed_native_simulation prim hprim UJg hUJg UJ U hJ hUJ hU fo hpub hξ har hN hfz hlam hδ
      hδ1 hD t hε hε1
  have hn := (gate_prop_signed (P := Reg S R) UJ U hUJ hU hfz hlam hδ hδ1 hD t hε hε1).2.1
  exact ⟨hv, hc, hn, fun h => sg_nPriv a f z lam δ t ε h, hg, hcard, hu, he⟩

end SignedNative

/-! ### Exact-gate part of the native-model form of Proposition `gate:prop:core`, before finite-set
synthesis -/

section Core

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **Exact-gate part of the native-model form of Proposition `gate:prop:core` (clipped-transducer
gate bound), before finite-set synthesis; abstract private operation.** See the module
docstring. In the regime `Regime s τ ε` of the clipped construction (`s ↔ σ = sμ²/η²`,
`τ ↔ Θ = η²|t|/μ`, so `sτ = B`), for unitaries `U_J`, `D` with the core data: the circuit is
valid, it makes exactly `6d` private calls and `12d` boundary calls (`d` the filter degree),
at most `200 (d+1)(a + m + r + 1)` elementary gates on `2a + 3m + 6r + 3` wires with
`2^m < 2d²/(5ε)`, `2d + 2 ≤ 2^r ≤ 4(d+1)`, `d ≤ 21520 √(sτ r)` (`r = L/h`), and its full output is
within `ε` of `e^{-i a J†KJ}`. -/
theorem gate_prop_core [FiniteDimensional ℂ P] (a : ℕ) {s τ ε : ℝ} (R : Regime s τ ε)
    (UJ D : Anc a P →L[ℂ] Anc a P) (hUJ : IsUnitary UJ) (hDu : IsUnitary D)
    {Kb Pp Pm : Anc a P →L[ℂ] Anc a P}
    (h : Core.CoreData s τ ε Kb D Pp Pm (UJ ∘L iota0)) :
    (∀ g ∈ clipCircuit a s τ ε, g.Valid Wire.anc) ∧
    nPriv (clipCircuit a s τ ε) = 6 * degree s τ ε ∧
    nUJ (clipCircuit a s τ ε) = 12 * degree s τ ε ∧
    nGates (clipCircuit a s τ ε) ≤
      200 * (degree s τ ε + 1) * (a + clipM s τ ε + clipR s τ ε + 1) ∧
    Fintype.card (ClipWire a s τ ε) = 2 * a + 3 * clipM s τ ε + 6 * clipR s τ ε + 3 ∧
    ((2 ^ clipM s τ ε : ℕ) : ℝ) < 2 * (degree s τ ε : ℝ) ^ 2 / (5 * ε) ∧
    2 * degree s τ ε + 2 ≤ 2 ^ clipR s τ ε ∧ 2 ^ clipR s τ ε ≤ 4 * (degree s τ ε + 1) ∧
    (degree s τ ε : ℝ) ≤ 21520 * Real.sqrt (s * τ * rval τ ε) ∧
    ‖run (simSem UJ D) (clipCircuit a s τ ε) ∘L io -
        io ∘L NormedSpace.exp ((-Complex.I * (aval s τ ε : ℂ)) •
          ((UJ ∘L iota0)† ∘L Kb ∘L (UJ ∘L iota0)))‖ ≤ ε := by
  obtain ⟨hv, hp, hu, hg, hc, he, -, hm2, hr1, hr2⟩ :=
    clipped_gate_simulation a R UJ D hUJ hDu h
  have hsteps := clip_steps_le R
  have hm2' : ((2 ^ clipM s τ ε : ℕ) : ℝ) < 2 * (steps s τ ε : ℝ) := by
    exact_mod_cast hm2
  have hm : ((2 ^ clipM s τ ε : ℕ) : ℝ) < 2 * (degree s τ ε : ℝ) ^ 2 / (5 * ε) := by
    have e : 2 * (degree s τ ε : ℝ) ^ 2 / (5 * ε) = 2 * ((degree s τ ε : ℝ) ^ 2 / (5 * ε)) := by
      ring
    rw [e]
    linarith
  exact ⟨hv, hp, hu, hg, hc, hm, hr1, hr2, R.degree_le_sqrt, he⟩

end Core


/-! ### Native-model form of Proposition `gate:prop:core`, before finite-set synthesis: native
private calls -/

section CoreNative

variable {S Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y] {bT bP A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

theorem secOK_clipCircuit (a : ℕ) (s τ ε : ℝ) :
    ∀ i ∈ clipCircuit a s τ ε, SecOK (wireRel _ _ _ _) i := by
  have h := secOK_clipSigned a s τ ε 0
  unfold clipSigned at h
  rwa [if_pos (le_refl (0 : ℝ))] at h

/-- **Native-model form of Proposition `gate:prop:core`, before finite-set synthesis: its
explicit-gates form with native private calls.** With `U_J`
given by elementary gates `UJg` and the private operation implemented natively in the
factor-conjugated form `D = U_f† C U_f` of Section `gate:sec:native`
(`GateOptimalBinary.ClipNative`: a native factor `U_f` with arithmetic accuracy `ξ` and a native
rotation `C` with angle accuracy `ζ`, with their public conditions and native identities as
hypotheses), the native clipped circuit
(`GateOptimalBinary.clipNativeOf`; every oracle call of the clipped circuit is sector-controlled) is
valid and unitary, makes exactly `6d` copies of the primitive calls of one native private call
(`N.calls p = 4 calls_p(W) + 2 calls_p(V)`, `ClipNative.calls_eq`: the sparse-oracle calls inside
the compute circuits of the factor and the rotation), has at most
`200 (d+1)(a + m + r + 1) + 12d · 7|UJg| + 6d G_P` elementary gates (`G_P = |N.pc|` the gates of one
native private call) on `2a + 3m + 6r + 3 + |S| + |Z| + b_T + b_P + A + 3` wires, with the slot and
degree bounds of `gate_prop_core`, and its full output is within `ε + 6d (6ξ + 4ζ)` of
`e^{-i a J†KJ}`: the explicit-gates form with `R = 2d`, in the native gate model, before finite-set
synthesis. -/
theorem gate_prop_core_native [FiniteDimensional ℂ R] (a : ℕ) {s τ ε : ℝ} (Rg : Regime s τ ε)
    (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (UJ D : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (hUJ : IsUnitary UJ) (hDu : IsUnitary D)
    {Kb Pp Pm : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)}
    (h : Core.CoreData s τ ε Kb D Pp Pm (UJ ∘L iota0)) {ξ ζ : ℝ} (hξ : 0 ≤ ξ) (hζ : 0 ≤ ζ)
    (N : GateOptimalBinary.ClipNative prim UJ D Z bT bP A ξ ζ) :
    (∀ i ∈ GateOptimalBinary.clipNativeOf N.UJg N.pc (clipCircuit a s τ ε), i.Valid) ∧
    (∀ p : J → Bool, nCallsN p (GateOptimalBinary.clipNativeOf N.UJg N.pc (clipCircuit a s τ ε)) =
      6 * degree s τ ε * N.calls p) ∧
    nGatesN (GateOptimalBinary.clipNativeOf N.UJg N.pc (clipCircuit a s τ ε)) ≤
      200 * (degree s τ ε + 1) * (a + clipM s τ ε + clipR s τ ε + 1) +
        12 * degree s τ ε * (7 * N.UJg.length) + 6 * degree s τ ε * nGatesN N.pc ∧
    Fintype.card (HW (ClipWire a s τ ε) S Empty Z bT bP A) =
      2 * a + 3 * clipM s τ ε + 6 * clipR s τ ε + 3 + Fintype.card S +
        (Fintype.card Z + bT + bP + A + 3) ∧
    ((2 ^ clipM s τ ε : ℕ) : ℝ) < 2 * (degree s τ ε : ℝ) ^ 2 / (5 * ε) ∧
    2 * degree s τ ε + 2 ≤ 2 ^ clipR s τ ε ∧ 2 ^ clipR s τ ε ≤ 4 * (degree s τ ε + 1) ∧
    (degree s τ ε : ℝ) ≤ 21520 * Real.sqrt (s * τ * rval τ ε) ∧
    IsUnitary (nrun prim (GateOptimalBinary.clipNativeOf N.UJg N.pc (clipCircuit a s τ ε))) ∧
    ‖nrun prim (GateOptimalBinary.clipNativeOf N.UJg N.pc (clipCircuit a s τ ε)) ∘L
          sysEmb (io (P := Reg S R)) -
        sysEmb (io (P := Reg S R)) ∘L NormedSpace.exp ((-Complex.I * (aval s τ ε : ℂ)) •
          ((UJ ∘L iota0)† ∘L Kb ∘L (UJ ∘L iota0)))‖ ≤
      ε + 6 * (degree s τ ε : ℝ) * (6 * ξ + 4 * ζ) := by
  obtain ⟨hv, hp, hu, hg, hc, hm, hr1, hr2, hd, he⟩ := gate_prop_core a Rg UJ D hUJ hDu h
  have hsec := secOK_clipCircuit a s τ ε
  -- an opaque circuit keeps the unifier from unfolding `clipCircuit` while it matches the
  -- instance paths of the generic `gate_prop_core` with those of `clip_transfer`
  generalize clipCircuit a s τ ε = l at hv hp hu hg he hsec ⊢
  obtain ⟨hvN, hcalls, hgates, hcard, huN, herr⟩ :=
    GateOptimalBinary.clip_transfer prim hprim hξ hζ N hDu l hv hsec _ he
  refine ⟨hvN, fun p => by rw [hcalls p, hp], ?_, by rw [hcard, hc], hm, hr1, hr2, hd, huN, ?_⟩
  · rw [hp, hu] at hgates
    exact hgates.trans (Nat.add_le_add_right (Nat.add_le_add_right hg _) _)
  · rw [hp] at herr
    push_cast at herr
    exact herr

end CoreNative

end

end ManuscriptConformance
