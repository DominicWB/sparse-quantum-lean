import GateOptimalPrecision.NativeSigned

/-!
# Theorem `gate:thm:main` and its single-norm case with native private calls

Every private call of the three regimes is replaced by its native construction (Section
`gate:sec:native`), and every boundary call by the elementary gates of `U_J` with the sector wire as
an extra control:

* the bounded regime and the clipped transducer have sector-controlled private calls; each is
  replaced by the native compute–rotate–uncompute macro of the baseline gate theorem
  (`CayleyNative`: a public compute circuit `V`, the reversible angle arithmetic `circ` with
  accuracy `ζ`, the bit-controlled edge rotation under the sector wire, the inverse arithmetic and
  `V†`; `G_C = 2|V| + 2|circ| + 2 b_P + b_T + 1` gates). The native identity `V† R V = D` on clean
  scratch enters as a hypothesis (`NativeOK`), as does the accuracy of the arithmetic (`ArithOK`);
* the signed factor has unconditional factor calls; each is replaced by the native factor of Section
  `gate:sec:native` (`FactorNative`: a public compute circuit `W`, the reversible arithmetic `circ`
  of the angle and phase words, the `2 b_P + b_T + 4` local gates of the stable factor `U(c)`, the
  inverse arithmetic and `W†`; `G_C = 2|W| + 2|circ| + 2 b_P + b_T + 4` gates). The native identity
  `W† U(c) W = U_B` on clean scratch enters as a hypothesis (`FactorNativeOK`), as does the accuracy
  of the arithmetic (`FactorArithOK`: for each configuration either `‖c‖ ≤ ζ²/16` and the angle is
  zero, or the magnitude is within `ζ²` and the phase within `ζ`).

**Theorem `gate:thm:main`, native form** (`gate_optimal_native`). The interfaces and native data of
a regime are required only in that regime. In each regime the native circuit satisfies
`NativeClaims`:

* it is valid and unitary;
* it makes at most `2·10¹¹ Q_μ` times the primitive calls of one native private call
  (`2 nCallsN V`, resp. `2 nCallsN W`);
* it has at most `10¹³ (Q_μ + 1)(a + m + r + 1) + 2·10¹¹ Q_μ G` elementary gates, where `G` is
  the gate cost of one native boundary call and one native private call (`7 C_J + G_C`);
* it uses at most `2a + 3m + 6r + 5 + |S| + |Z| + b_T + b_P + A + 3` wires: at most
  `2a + 3m + 6r + 5` wires of the released circuit, the `|S|` system qubits, the scratch, the two
  angle words, the arithmetic work wires and the three flags of the controlled `U_J` gates;
  `2^m ≤ 10³⁶ (Q_μ + 1)⁴/ε` and `2^r ≤ 10⁸ (Q_μ + 1)`;
* its full output on the system embedding is within `ε + 2·10¹¹ Q_μ ζ'` of `e^{-itH}`, with
  `ζ' = 4ζ` for an edge rotation (`ζ` the angle accuracy of `ArithOK`) and `ζ' = 3ζ` for a factor
  (`ζ` the accuracy parameter of `FactorArithOK`).

**Total error `ε`** (`gate_optimal_native_total`, `gate:eq:full`): the exact-gate construction at
accuracy `ε/2` (the ideal budget `ε/2` of Proposition `gate:prop:finite`) and arithmetic accuracy
`ζ` with `32·10¹¹ Q_μ ζ ≤ ε`, where `Q_μ` is taken at `ε`; synthesis is not part of this
library, so the private calls get the remaining `ε/2` (the paper splits it as `ε/4` for the private
calls and `ε/4` for synthesis; for binary sparse oracles,
`GateOptimalBinary.gate_optimal_binary_synth` adds a synthesis budget `ε'`). The native circuit
then satisfies `NativeClaims` at `ε/2` with the count parameter `2 Q_μ` (`Q_μ(ε/2) ≤ 2 Q_μ(ε)`,
`Qmu_half_le`) and full-output error `ε`.

**The single-norm case of Theorem `gate:thm:main`, native form** (`gate_optimal_native_single`,
`gate_optimal_native_single_total`): the same claims at `μ = η`, with `Q_μ = Q`.

The transfers from the exact-gate claims (`GateClaims`) are `cayley_claims` and `factor_claims`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace GateOptimalPrecision

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim SparseHamiltonian.GateNative
open LargeSparsityCore LargeSparsityCore.Parameters CayleyClockInterface
open Complex (I)
open scoped InnerProduct InnerProductSpace BigOperators ComplexOrder

variable {S Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Y] [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-! ### The claims and the native data -/

/-- **The conclusions of Theorem `gate:thm:main` for a native circuit** `C` on the wires of a
released circuit with `a` ancilla qubits, `2^m` slots and `2^r` labels: `calls p` primitive calls of
kind `p` and `G` elementary gates per native private call (with its boundary call), and full-output
error `δ`. -/
structure NativeClaims (prim : J → Reg Y R →L[ℂ] Reg Y R) {Z : Type*} [Fintype Z]
    [DecidableEq Z] {a m r K bT bP A : ℕ}
    (C : List (NInstr (HW (Wire a m r K) S Empty Z bT bP A) Y J))
    (H : Reg S R →L[ℂ] Reg S R) (t ε Q : ℝ) (calls : (J → Bool) → ℕ) (G : ℕ) (δ : ℝ) :
    Prop where
  valid : ∀ i ∈ C, i.Valid
  unitary : IsUnitary (nrun prim C)
  calls_le : ∀ p : J → Bool, (nCallsN p C : ℝ) ≤ 2 * 10 ^ 11 * Q * calls p
  gates : (nGatesN C : ℝ) ≤ 10 ^ 13 * (Q + 1) * (a + m + r + 1) + 2 * 10 ^ 11 * Q * G
  wires : Fintype.card (HW (Wire a m r K) S Empty Z bT bP A) ≤
    2 * a + 3 * m + 6 * r + 5 + Fintype.card S + (Fintype.card Z + bT + bP + A + 3)
  mesh : ((2 ^ m : ℕ) : ℝ) ≤ 10 ^ 36 * (Q + 1) ^ 4 / ε
  labels : ((2 ^ r : ℕ) : ℝ) ≤ 10 ^ 8 * (Q + 1)
  error : ‖nrun prim C ∘L sysEmb (io (P := Reg S R)) - sysEmb (io (P := Reg S R)) ∘L
    NormedSpace.exp ((-I * (t : ℂ)) • H)‖ ≤ δ

theorem NativeClaims.mono {prim : J → Reg Y R →L[ℂ] Reg Y R} {Z : Type*} [Fintype Z]
    [DecidableEq Z] {a m r K bT bP A : ℕ}
    {C : List (NInstr (HW (Wire a m r K) S Empty Z bT bP A) Y J)}
    {H : Reg S R →L[ℂ] Reg S R} {t ε Q : ℝ} {calls : (J → Bool) → ℕ} {G : ℕ} {δ δ' : ℝ}
    (h : NativeClaims prim C H t ε Q calls G δ) (hδ : δ ≤ δ') :
    NativeClaims prim C H t ε Q calls G δ' :=
  { h with error := h.error.trans hδ }

/-- Weakening the native claims: a larger count parameter `Q' ≥ Q ≥ 0` and a larger error. -/
theorem NativeClaims.weaken {prim : J → Reg Y R →L[ℂ] Reg Y R} {Z : Type*} [Fintype Z]
    [DecidableEq Z] {a m r K bT bP A : ℕ}
    {C : List (NInstr (HW (Wire a m r K) S Empty Z bT bP A) Y J)}
    {H : Reg S R →L[ℂ] Reg S R} {t ε Q Q' : ℝ} {calls : (J → Bool) → ℕ} {G : ℕ} {δ δ' : ℝ}
    (h : NativeClaims prim C H t ε Q calls G δ) (hε : 0 < ε) (hQ0 : 0 ≤ Q) (hQ : Q ≤ Q')
    (hδ : δ ≤ δ') : NativeClaims prim C H t ε Q' calls G δ' where
  valid := h.valid
  unitary := h.unitary
  calls_le p := (h.calls_le p).trans (by gcongr)
  gates := h.gates.trans (by gcongr)
  wires := h.wires
  mesh := h.mesh.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) 4) (by norm_num))
    hε.le)
  labels := h.labels.trans (by gcongr)
  error := h.error.trans hδ

/-- `r(ε/2) ≤ 2 r(ε)` for `θ > 0` and `0 < ε ≤ 1/2`. -/
theorem rval_half_le {θ ε : ℝ} (hθ : 0 < θ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    rval θ (ε / 2) ≤ 2 * rval θ ε := by
  unfold rval hval Lval
  have hL : Real.log 2 ≤ Real.log (1 / ε) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hε]; linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL0 : 0 ≤ Real.log (1 / ε) := le_trans hlog2 hL
  have hsplit : Real.log (1 / (ε / 2)) = Real.log 2 + Real.log (1 / ε) := by
    rw [show (1 : ℝ) / (ε / 2) = 2 * (1 / ε) by field_simp, Real.log_mul (by norm_num)
      (by positivity)]
  have hnum : Real.log (1 / (ε / 2)) ≤ 2 * Real.log (1 / ε) := by rw [hsplit]; linarith
  set d1 := Real.log (Real.exp 1 + Real.log (1 / ε) / θ) with hd1def
  set d2 := Real.log (Real.exp 1 + Real.log (1 / (ε / 2)) / θ) with hd2def
  have he : (1 : ℝ) ≤ d1 := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ Real.exp 1 + Real.log (1 / ε) / θ by
        have := div_nonneg hL0 hθ.le; linarith)
    rwa [Real.log_exp] at h
  have hden : d1 ≤ d2 := by
    apply Real.log_le_log (by have := div_nonneg hL0 hθ.le; positivity)
    have : Real.log (1 / ε) / θ ≤ Real.log (1 / (ε / 2)) / θ :=
      div_le_div_of_nonneg_right (by rw [hsplit]; linarith) hθ.le
    linarith
  have hd1 : 0 < d1 := by linarith
  have hd2 : 0 < d2 := by linarith
  rw [div_le_iff₀ hd2]
  have hq : 1 ≤ d2 / d1 := by rw [le_div_iff₀ hd1]; linarith
  calc Real.log (1 / (ε / 2)) ≤ 2 * Real.log (1 / ε) := hnum
    _ ≤ 2 * Real.log (1 / ε) * (d2 / d1) := le_mul_of_one_le_right (by linarith) hq
    _ = 2 * (Real.log (1 / ε) / d1) * d2 := by field_simp

/-- **`Q_μ(ε/2) ≤ 2 Q_μ(ε)`**: halving the accuracy at most doubles the query count. -/
theorem Qmu_half_le {s : ℕ} {η μ t ε : ℝ} (hη : 0 ≤ η) (hμ : 0 < μ)
    (hθ : 0 < η ^ 2 * |t| / μ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    Qmu s η μ t (ε / 2) ≤ 2 * Qmu s η μ t ε := by
  unfold Qmu
  set θ := η ^ 2 * |t| / μ
  have hr := rval_half_le hθ hε hε2
  have hr0 : 0 ≤ rval θ ε := by
    simp only [rval, hval, Lval]
    apply div_nonneg
    · exact Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
    · apply Real.log_nonneg
      have := Real.add_one_le_exp 1
      have : 0 ≤ Real.log (1 / ε) / θ :=
        div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)) hθ.le
      linarith
  have hA : 0 ≤ (s : ℝ) * μ * |t| := by positivity
  have h1 : Real.sqrt (s * μ * |t| * rval θ (ε / 2)) ≤
      2 * Real.sqrt (s * μ * |t| * rval θ ε) := by
    calc Real.sqrt (s * μ * |t| * rval θ (ε / 2))
        ≤ Real.sqrt (4 * (s * μ * |t| * rval θ ε)) :=
          Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_left hr hA])
      _ = 2 * Real.sqrt (s * μ * |t| * rval θ ε) := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  have h2 : 0 ≤ Real.sqrt s * η * |t| := by positivity
  linarith

/-- **Native data for a sector-controlled private operation** `D` with the boundary `U_J`: the
elementary gates `UJg` of `U_J`, the public compute circuit `nd` with the native identity
`V† R V = D` on clean scratch (`NativeOK`), and the reversible angle arithmetic `ar` with
accuracy `ζ` (`ArithOK`). -/
structure CayleyNative (prim : J → Reg Y R →L[ℂ] Reg Y R) {a : ℕ}
    (UJ D : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (Z : Type*) [Fintype Z] [DecidableEq Z]
    (ζ : ℝ) where
  /-- The elementary gates of `U_J`. -/
  UJg : List (Gate (Fin a ⊕ S))
  ok : ∀ g ∈ UJg, GateOK 3 g
  boundary : UJop (R := R) UJg = UJ
  /-- The compute circuit of the edge data. -/
  nd : NativeOp Empty (Fin a ⊕ S) Z Y J
  pub : nd.Public
  /-- The angle arithmetic. -/
  ar : Arith (NB Empty (Fin a ⊕ S) Z)
  arith : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ
  native : NativeOK prim nd (selOp (fun _ : Cfg Empty => D))

/-- The primitive calls of kind `p` of one native private call. -/
def CayleyNative.calls {prim : J → Reg Y R →L[ℂ] Reg Y R} {a : ℕ}
    {UJ D : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)} {Z : Type*} [Fintype Z] [DecidableEq Z]
    {ζ : ℝ} (N : CayleyNative prim UJ D Z ζ) (p : J → Bool) : ℕ :=
  2 * nCallsN p N.nd.V

/-- The elementary gates of one native boundary call and one native private call. -/
def CayleyNative.cost {prim : J → Reg Y R →L[ℂ] Reg Y R} {a : ℕ}
    {UJ D : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)} {Z : Type*} [Fintype Z] [DecidableEq Z]
    {ζ : ℝ} (N : CayleyNative prim UJ D Z ζ) : ℕ :=
  7 * N.UJg.length + (2 * nGatesN N.nd.V + 2 * N.ar.circ.length + (2 * N.ar.bP + N.ar.bT + 1))

/-- **Native data for the factor** `U_B` with the boundary `U_J`: the elementary gates `UJg` of
`U_J`, and the native factor `fo` on the `a + 1` ancilla wires (`factorMacro`: compute `W`, the
arithmetic, the local gates of `U(c)`, the inverse arithmetic, uncompute `W†`) with its public
conditions, the factor arithmetic of accuracy `ζ` (`FactorArithOK`) and the native identity
`W† U(c) W = U_B ⊗ I_flag` on clean scratch (`FactorNativeOK`). -/
structure FactorNative (prim : J → Reg Y R →L[ℂ] Reg Y R) {a : ℕ}
    (UJ U : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (Z : Type*) [Fintype Z] [DecidableEq Z]
    (bT bP A : ℕ) (ζ : ℝ) where
  /-- The elementary gates of `U_J`. -/
  UJg : List (Gate (Fin a ⊕ S))
  ok : ∀ g ∈ UJg, GateOK 3 g
  boundary : UJop (R := R) UJg = UJ
  /-- The native factor. -/
  fo : FactorOp (Fin (a + 1) ⊕ S) Z Y J bT bP A
  pub : fo.Public
  /-- The factor arithmetic. -/
  arith : FactorArithOK fo ζ
  native : FactorNativeOK prim fo (selOp (fun _ : Cfg Empty => liftA U))

/-- The primitive calls of kind `p` of one native factor call. -/
def FactorNative.calls {prim : J → Reg Y R →L[ℂ] Reg Y R} {a : ℕ}
    {UJ U : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)} {Z : Type*} [Fintype Z] [DecidableEq Z]
    {bT bP A : ℕ} {ζ : ℝ} (N : FactorNative prim UJ U Z bT bP A ζ) (p : J → Bool) : ℕ :=
  2 * nCallsN p N.fo.W

/-- The elementary gates of one native boundary call and one native factor call. -/
def FactorNative.cost {prim : J → Reg Y R →L[ℂ] Reg Y R} {a : ℕ}
    {UJ U : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)} {Z : Type*} [Fintype Z] [DecidableEq Z]
    {bT bP A : ℕ} {ζ : ℝ} (N : FactorNative prim UJ U Z bT bP A ζ) : ℕ :=
  7 * N.UJg.length + (2 * nGatesN N.fo.W + 2 * N.fo.circ.length + (2 * bP + bT + 4))

/-! ### The transfers -/

/-- **The native claims of a sector-controlled circuit**: from the exact-gate claims and the
native data of its private operation. -/
theorem cayley_claims (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    {a m r K : ℕ} {UJ D : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)} {Z : Type*} [Fintype Z]
    [DecidableEq Z] {ζ : ℝ} (hζ : 0 ≤ ζ) (N : CayleyNative prim UJ D Z ζ) (hD : IsUnitary D)
    (l : List (Instr (Wire a m r K))) (hsec : ∀ i ∈ l, SecOK (wireRel a m r K) i)
    {H : Reg S R →L[ℂ] Reg S R} {t ε Q : ℝ} (hG : GateClaims (P := Reg S R) UJ D l H t ε Q) :
    NativeClaims prim (nativeOf N.UJg N.nd N.ar l) H t ε Q N.calls N.cost
      (ε + 2 * 10 ^ 11 * Q * (4 * ζ)) := by
  have hrel := hG.error
  rw [← N.boundary] at hrel
  obtain ⟨hv, hcalls, hgates, hcard, hu, herr⟩ :=
    native_transfer prim hprim N.UJg N.ok N.nd N.pub N.ar hζ N.arith D hD N.native l hG.valid
      hsec _ hrel
  have hpriv := hG.priv
  refine ⟨hv, hu, fun p => ?_, ?_, ?_, hG.mesh, hG.labels, ?_⟩
  · rw [hcalls p]
    have hc : (0 : ℝ) ≤ (N.calls p : ℝ) := Nat.cast_nonneg _
    calc ((nPriv l * (2 * nCallsN p N.nd.V) : ℕ) : ℝ) = (nPriv l : ℝ) * (N.calls p : ℝ) := by
          unfold CayleyNative.calls
          push_cast
          ring
      _ ≤ 2 * 10 ^ 11 * Q * (N.calls p : ℝ) := mul_le_mul_of_nonneg_right hpriv hc
  · have h1 : (nGatesN (nativeOf N.UJg N.nd N.ar l) : ℝ) ≤ (nGates l : ℝ) +
        (nUJ l : ℝ) * ((7 * N.UJg.length : ℕ) : ℝ) + (nPriv l : ℝ) *
          ((2 * nGatesN N.nd.V + 2 * N.ar.circ.length + (2 * N.ar.bP + N.ar.bT + 1) : ℕ) : ℝ) := by
      exact_mod_cast hgates
    have h2 := mul_le_mul_of_nonneg_right hG.uj (Nat.cast_nonneg (7 * N.UJg.length))
    have h3 := mul_le_mul_of_nonneg_right hpriv
      (Nat.cast_nonneg (2 * nGatesN N.nd.V + 2 * N.ar.circ.length + (2 * N.ar.bP + N.ar.bT + 1)))
    have e : (2 : ℝ) * 10 ^ 11 * Q * (N.cost : ℝ) =
        2 * 10 ^ 11 * Q * ((7 * N.UJg.length : ℕ) : ℝ) + 2 * 10 ^ 11 * Q *
          ((2 * nGatesN N.nd.V + 2 * N.ar.circ.length + (2 * N.ar.bP + N.ar.bT + 1) : ℕ) : ℝ) := by
      unfold CayleyNative.cost
      push_cast
      ring
    rw [e]
    linarith only [h1, h2, h3, hG.gates]
  · rw [hcard]
    have := hG.wires
    omega
  · have h4 := mul_le_mul_of_nonneg_right hpriv (by linarith : (0 : ℝ) ≤ 4 * ζ)
    linarith only [herr, h4]

/-- **The native claims of a signed-factor circuit**: from the exact-gate claims and the native
data of the factor. -/
theorem factor_claims (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    {a m r K : ℕ} {UJ U : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)} {Z : Type*} [Fintype Z]
    [DecidableEq Z] {bT bP A : ℕ} {ζ : ℝ} (hζ : 0 ≤ ζ) (N : FactorNative prim UJ U Z bT bP A ζ)
    (hU : IsUnitary U) (l : List (Instr (Wire (a + 1) m r K)))
    (hunc : ∀ i ∈ l, UncOK (wireRel _ _ _ _) i) {H : Reg S R →L[ℂ] Reg S R} {t ε Q : ℝ}
    (hG : GateClaims (P := Reg S R) (liftA UJ) (liftA U) l H t ε Q) :
    NativeClaims prim (factorNativeOf N.UJg N.fo l) H t ε Q N.calls N.cost
      (ε + 2 * 10 ^ 11 * Q * (3 * ζ)) := by
  obtain ⟨hv, hcalls, hgates, hcard, hu, herr⟩ :=
    signed_transfer prim hprim N.UJg N.ok UJ U N.boundary hU N.fo N.pub hζ N.arith N.native l
      hG.valid hunc _ hG.error
  have hpriv := hG.priv
  refine ⟨hv, hu, fun p => ?_, ?_, ?_, hG.mesh, hG.labels, ?_⟩
  · rw [hcalls p]
    have hc : (0 : ℝ) ≤ (N.calls p : ℝ) := Nat.cast_nonneg _
    calc ((nPriv l * (2 * nCallsN p N.fo.W) : ℕ) : ℝ) = (nPriv l : ℝ) * (N.calls p : ℝ) := by
          unfold FactorNative.calls
          push_cast
          ring
      _ ≤ 2 * 10 ^ 11 * Q * (N.calls p : ℝ) := mul_le_mul_of_nonneg_right hpriv hc
  · have h1 : (nGatesN (factorNativeOf N.UJg N.fo l) : ℝ) ≤ (nGates l : ℝ) +
        (nUJ l : ℝ) * ((7 * N.UJg.length : ℕ) : ℝ) + (nPriv l : ℝ) *
          ((2 * nGatesN N.fo.W + 2 * N.fo.circ.length + (2 * bP + bT + 4) : ℕ) : ℝ) := by
      exact_mod_cast hgates
    have h2 := mul_le_mul_of_nonneg_right hG.uj (Nat.cast_nonneg (7 * N.UJg.length))
    have h3 := mul_le_mul_of_nonneg_right hpriv
      (Nat.cast_nonneg (2 * nGatesN N.fo.W + 2 * N.fo.circ.length + (2 * bP + bT + 4)))
    have e : (2 : ℝ) * 10 ^ 11 * Q * (N.cost : ℝ) =
        2 * 10 ^ 11 * Q * ((7 * N.UJg.length : ℕ) : ℝ) + 2 * 10 ^ 11 * Q *
          ((2 * nGatesN N.fo.W + 2 * N.fo.circ.length + (2 * bP + bT + 4) : ℕ) : ℝ) := by
      unfold FactorNative.cost
      push_cast
      ring
    rw [e]
    linarith only [h1, h2, h3, hG.gates]
  · rw [hcard]
    have := hG.wires
    omega
  · have h4 := mul_le_mul_of_nonneg_right hpriv (by linarith : (0 : ℝ) ≤ 3 * ζ)
    linarith only [herr, h4]

/-! ### Theorem `gate:thm:main` and its single-norm case -/

/-- **Theorem `gate:thm:main` (gate-efficient optimal-precision simulation), native form.** See the
module docstring. -/
theorem gate_optimal_native [FiniteDimensional ℂ R] {ZB ZS ZC : Type*} [Fintype ZB]
    [DecidableEq ZB] [Fintype ZS] [DecidableEq ZS] [Fintype ZC] [DecidableEq ZC] {bT bP A : ℕ}
    (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j)) {ζ : ℝ} (hζ : 0 ≤ ζ)
    {s : ℕ} {η μ t ε σ θ : ℝ}
    (hμη : μ ≤ η) (hηs : η ≤ Real.sqrt s * μ) (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2)
    (hθd : θ = η ^ 2 * |t| / μ) (hθ : 1 ≤ θ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    {H : Reg S R →L[ℂ] Reg S R} (hH : star H = H)
    (IB : hval θ ε < 10 ^ 4 → BoundedIface (Reg S R) σ (Real.sqrt s * η) H)
    (NB : ∀ hb : hval θ ε < 10 ^ 4, CayleyNative prim (IB hb).UJ (bdPriv (IB hb).K σ θ ε) ZB ζ)
    (IS : 10 ^ 4 ≤ hval θ ε → σ * θ < Lval ε * hval θ ε →
      SignedIface (Reg S R) (s * μ) (Real.sqrt σ)⁻¹ H)
    (NS : ∀ (h1 : 10 ^ 4 ≤ hval θ ε) (h2 : σ * θ < Lval ε * hval θ ε),
      FactorNative prim (IS h1 h2).UJ (IS h1 h2).U ZS bT bP A ζ)
    (IC : Regime σ θ ε → ClippedIface (Reg S R) σ θ ε (s * μ / qval σ θ ε) H)
    (NC : ∀ Rg : Regime σ θ ε, CayleyNative prim (IC Rg).UJ (IC Rg).D ZC ζ) :
    (∃ hb : hval θ ε < 10 ^ 4,
      NativeClaims prim (nativeOf (NB hb).UJg (NB hb).nd (NB hb).ar (bdSigned (IB hb).a σ θ ε t))
        H t ε (Qmu s η μ t ε) (NB hb).calls (NB hb).cost
        (ε + 2 * 10 ^ 11 * Qmu s η μ t ε * (4 * ζ))) ∨
    (∃ (h1 : 10 ^ 4 ≤ hval θ ε) (h2 : σ * θ < Lval ε * hval θ ε),
      NativeClaims prim
        (factorNativeOf (NS h1 h2).UJg (NS h1 h2).fo
          (sgCircuit (IS h1 h2).a (IS h1 h2).f (IS h1 h2).z (s * μ) (Real.sqrt σ)⁻¹ t ε)) H t ε
        (Qmu s η μ t ε) (NS h1 h2).calls (NS h1 h2).cost
        (ε + 2 * 10 ^ 11 * Qmu s η μ t ε * (3 * ζ))) ∨
    (∃ Rg : Regime σ θ ε,
      NativeClaims prim
        (nativeOf (NC Rg).UJg (NC Rg).nd (NC Rg).ar (clipSigned (IC Rg).a σ θ ε t)) H t ε
        (Qmu s η μ t ε) (NC Rg).calls (NC Rg).cost
        (ε + 2 * 10 ^ 11 * Qmu s η μ t ε * (4 * ζ))) := by
  rcases gate_optimal_simulation hμη hηs hσ hθd hθ hε hε1 hH IB IS IC with
    ⟨hh, hG⟩ | ⟨hh, hc, hG⟩ | ⟨Rg, hG⟩
  · exact Or.inl ⟨hh, cayley_claims prim hprim hζ (NB hh)
      (cayleyGate_isUnitary (scaled_self_adjoint (IB hh).K _ (IB hh).self)) _
      (secOK_bdSigned _ _ _ _ _) hG⟩
  · exact Or.inr (Or.inl ⟨hh, hc, factor_claims prim hprim hζ (NS hh hc) (IS hh hc).unitaryU _
      (uncOK_sgCircuit _ _ _ _ _ _ _) hG⟩)
  · exact Or.inr (Or.inr ⟨Rg, cayley_claims prim hprim hζ (NC Rg) (IC Rg).unitaryD _
      (secOK_clipSigned _ _ _ _ _) hG⟩)

/-- **Theorem `gate:thm:main`, native form, total error `ε`** (`gate:eq:full`): with the exact-gate
construction at accuracy `ε/2` and the arithmetic accuracy `ζ` with `32·10¹¹ Q_μ ζ ≤ ε` (`Q_μ` at
`ε`), the native circuit of each regime satisfies `NativeClaims` at `ε/2` with the count parameter
`2 Q_μ`, and its full output is within `ε` of `e^{-itH}`. -/
theorem gate_optimal_native_total [FiniteDimensional ℂ R] {ZB ZS ZC : Type*} [Fintype ZB]
    [DecidableEq ZB] [Fintype ZS] [DecidableEq ZS] [Fintype ZC] [DecidableEq ZC] {bT bP A : ℕ}
    (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j)) {ζ : ℝ} (hζ : 0 ≤ ζ)
    {s : ℕ} {η μ t ε σ θ : ℝ}
    (hμη : μ ≤ η) (hηs : η ≤ Real.sqrt s * μ) (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2)
    (hθd : θ = η ^ 2 * |t| / μ) (hθ : 1 ≤ θ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 32)
    (hζε : 32 * 10 ^ 11 * Qmu s η μ t ε * ζ ≤ ε)
    {H : Reg S R →L[ℂ] Reg S R} (hH : star H = H)
    (IB : hval θ (ε / 2) < 10 ^ 4 → BoundedIface (Reg S R) σ (Real.sqrt s * η) H)
    (NB : ∀ hb : hval θ (ε / 2) < 10 ^ 4,
      CayleyNative prim (IB hb).UJ (bdPriv (IB hb).K σ θ (ε / 2)) ZB ζ)
    (IS : 10 ^ 4 ≤ hval θ (ε / 2) → σ * θ < Lval (ε / 2) * hval θ (ε / 2) →
      SignedIface (Reg S R) (s * μ) (Real.sqrt σ)⁻¹ H)
    (NS : ∀ (h1 : 10 ^ 4 ≤ hval θ (ε / 2)) (h2 : σ * θ < Lval (ε / 2) * hval θ (ε / 2)),
      FactorNative prim (IS h1 h2).UJ (IS h1 h2).U ZS bT bP A ζ)
    (IC : Regime σ θ (ε / 2) →
      ClippedIface (Reg S R) σ θ (ε / 2) (s * μ / qval σ θ (ε / 2)) H)
    (NC : ∀ Rg : Regime σ θ (ε / 2), CayleyNative prim (IC Rg).UJ (IC Rg).D ZC ζ) :
    (∃ hb : hval θ (ε / 2) < 10 ^ 4,
      NativeClaims prim
        (nativeOf (NB hb).UJg (NB hb).nd (NB hb).ar (bdSigned (IB hb).a σ θ (ε / 2) t)) H t
        (ε / 2) (2 * Qmu s η μ t ε) (NB hb).calls (NB hb).cost ε) ∨
    (∃ (h1 : 10 ^ 4 ≤ hval θ (ε / 2)) (h2 : σ * θ < Lval (ε / 2) * hval θ (ε / 2)),
      NativeClaims prim
        (factorNativeOf (NS h1 h2).UJg (NS h1 h2).fo
          (sgCircuit (IS h1 h2).a (IS h1 h2).f (IS h1 h2).z (s * μ) (Real.sqrt σ)⁻¹ t (ε / 2)))
        H t (ε / 2) (2 * Qmu s η μ t ε) (NS h1 h2).calls (NS h1 h2).cost ε) ∨
    (∃ Rg : Regime σ θ (ε / 2),
      NativeClaims prim
        (nativeOf (NC Rg).UJg (NC Rg).nd (NC Rg).ar (clipSigned (IC Rg).a σ θ (ε / 2) t)) H t
        (ε / 2) (2 * Qmu s η μ t ε) (NC Rg).calls (NC Rg).cost ε) := by
  have hε' : 0 < ε / 2 := by linarith
  have hε1' : ε / 2 ≤ 1 / 64 := by linarith
  obtain ⟨hμ, hη, -, -, hST, hSq⟩ := two_norm_params hμη hηs hσ hθd hθ
  have hQ0 := Qmu_nonneg hθd hST hSq hθ hε' hε1'
  have hQle : Qmu s η μ t (ε / 2) ≤ 2 * Qmu s η μ t ε :=
    Qmu_half_le hη.le hμ (by rw [← hθd]; linarith) hε (by linarith)
  have hζQ : Qmu s η μ t (ε / 2) * ζ ≤ 2 * Qmu s η μ t ε * ζ :=
    mul_le_mul_of_nonneg_right hQle hζ
  have hQζ : 0 ≤ Qmu s η μ t (ε / 2) * ζ := mul_nonneg hQ0 hζ
  have h4 : ε / 2 + 2 * 10 ^ 11 * Qmu s η μ t (ε / 2) * (4 * ζ) ≤ ε := by nlinarith
  have h3 : ε / 2 + 2 * 10 ^ 11 * Qmu s η μ t (ε / 2) * (3 * ζ) ≤ ε := by nlinarith
  rcases gate_optimal_native prim hprim hζ hμη hηs hσ hθd hθ hε' hε1' hH IB NB IS NS IC NC with
    ⟨hh, hN⟩ | ⟨h1, h2, hN⟩ | ⟨Rg, hN⟩
  · exact Or.inl ⟨hh, hN.weaken hε' hQ0 hQle h4⟩
  · exact Or.inr (Or.inl ⟨h1, h2, hN.weaken hε' hQ0 hQle h3⟩)
  · exact Or.inr (Or.inr ⟨Rg, hN.weaken hε' hQ0 hQle h4⟩)

/-- **The single-norm case of Theorem `gate:thm:main` (single supplied norm), native form**: the
theorem at `μ = η`. -/
theorem gate_optimal_native_single [FiniteDimensional ℂ R] {ZB ZS ZC : Type*} [Fintype ZB]
    [DecidableEq ZB] [Fintype ZS] [DecidableEq ZS] [Fintype ZC] [DecidableEq ZC] {bT bP A : ℕ}
    (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j)) {ζ : ℝ} (hζ : 0 ≤ ζ)
    {s : ℕ} (hs : 1 ≤ s) {η t ε : ℝ} (hη : 0 < η) (hτ : 1 ≤ η * |t|) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64) {H : Reg S R →L[ℂ] Reg S R} (hH : star H = H)
    (IB : hval (η * |t|) ε < 10 ^ 4 → BoundedIface (Reg S R) s (Real.sqrt s * η) H)
    (NB : ∀ hb : hval (η * |t|) ε < 10 ^ 4,
      CayleyNative prim (IB hb).UJ (bdPriv (IB hb).K s (η * |t|) ε) ZB ζ)
    (IS : 10 ^ 4 ≤ hval (η * |t|) ε → (s : ℝ) * (η * |t|) < Lval ε * hval (η * |t|) ε →
      SignedIface (Reg S R) (s * η) (Real.sqrt s)⁻¹ H)
    (NS : ∀ (h1 : 10 ^ 4 ≤ hval (η * |t|) ε) (h2 : (s : ℝ) * (η * |t|) < Lval ε * hval (η * |t|) ε),
      FactorNative prim (IS h1 h2).UJ (IS h1 h2).U ZS bT bP A ζ)
    (IC : Regime s (η * |t|) ε →
      ClippedIface (Reg S R) s (η * |t|) ε (s * η / qval s (η * |t|) ε) H)
    (NC : ∀ Rg : Regime s (η * |t|) ε, CayleyNative prim (IC Rg).UJ (IC Rg).D ZC ζ) :
    (∃ hb : hval (η * |t|) ε < 10 ^ 4,
      NativeClaims prim
        (nativeOf (NB hb).UJg (NB hb).nd (NB hb).ar (bdSigned (IB hb).a s (η * |t|) ε t)) H t ε
        (Qone s η t ε) (NB hb).calls (NB hb).cost (ε + 2 * 10 ^ 11 * Qone s η t ε * (4 * ζ))) ∨
    (∃ (h1 : 10 ^ 4 ≤ hval (η * |t|) ε) (h2 : (s : ℝ) * (η * |t|) < Lval ε * hval (η * |t|) ε),
      NativeClaims prim
        (factorNativeOf (NS h1 h2).UJg (NS h1 h2).fo
          (sgCircuit (IS h1 h2).a (IS h1 h2).f (IS h1 h2).z (s * η) (Real.sqrt s)⁻¹ t ε)) H t ε
        (Qone s η t ε) (NS h1 h2).calls (NS h1 h2).cost
        (ε + 2 * 10 ^ 11 * Qone s η t ε * (3 * ζ))) ∨
    (∃ Rg : Regime s (η * |t|) ε,
      NativeClaims prim
        (nativeOf (NC Rg).UJg (NC Rg).nd (NC Rg).ar (clipSigned (IC Rg).a s (η * |t|) ε t)) H t ε
        (Qone s η t ε) (NC Rg).calls (NC Rg).cost (ε + 2 * 10 ^ 11 * Qone s η t ε * (4 * ζ))) := by
  rcases gate_optimal_simulation_single hs hη hτ hε hε1 hH IB IS IC with
    ⟨hh, hG⟩ | ⟨hh, hc, hG⟩ | ⟨Rg, hG⟩
  · exact Or.inl ⟨hh, cayley_claims prim hprim hζ (NB hh)
      (cayleyGate_isUnitary (scaled_self_adjoint (IB hh).K _ (IB hh).self)) _
      (secOK_bdSigned _ _ _ _ _) hG⟩
  · exact Or.inr (Or.inl ⟨hh, hc, factor_claims prim hprim hζ (NS hh hc) (IS hh hc).unitaryU _
      (uncOK_sgCircuit _ _ _ _ _ _ _) hG⟩)
  · exact Or.inr (Or.inr ⟨Rg, cayley_claims prim hprim hζ (NC Rg) (IC Rg).unitaryD _
      (secOK_clipSigned _ _ _ _ _) hG⟩)

/-- `Q ≥ 0`. -/
theorem Qone_nonneg {s : ℕ} {η t ε : ℝ} (hτ : 1 ≤ η * |t|) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    0 ≤ Qone s η t ε := by
  have hη : 0 < η := by
    by_contra h
    push Not at h
    nlinarith [abs_nonneg t]
  have h1 := OptimalSparseSimulation.r_pos hτ hε hε1
  have h2 : 0 ≤ Real.sqrt s * (η * |t|) := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have h3 := Real.sqrt_nonneg (s * (η * |t|) * rval (η * |t|) ε)
  unfold Qone
  linarith

/-- `Q(ε/2) ≤ 2 Q(ε)`. -/
theorem Qone_half_le {s : ℕ} {η t ε : ℝ} (hη : 0 < η) (hτ : 1 ≤ η * |t|) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) : Qone s η t (ε / 2) ≤ 2 * Qone s η t ε := by
  rw [← Qmu_self hη, ← Qmu_self hη]
  have e : η ^ 2 * |t| / η = η * |t| := by field_simp
  exact Qmu_half_le hη.le hη (by rw [e]; linarith) hε hε2

/-- **The single-norm case, native form, total error `ε`**: that case at accuracy `ε/2` with
`32·10¹¹ Q ζ ≤ ε` (`Q` at `ε`); the claims hold with the count parameter `2 Q`. -/
theorem gate_optimal_native_single_total [FiniteDimensional ℂ R] {ZB ZS ZC : Type*} [Fintype ZB]
    [DecidableEq ZB] [Fintype ZS] [DecidableEq ZS] [Fintype ZC] [DecidableEq ZC] {bT bP A : ℕ}
    (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j)) {ζ : ℝ} (hζ : 0 ≤ ζ)
    {s : ℕ} (hs : 1 ≤ s) {η t ε : ℝ} (hη : 0 < η) (hτ : 1 ≤ η * |t|) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 32) (hζε : 32 * 10 ^ 11 * Qone s η t ε * ζ ≤ ε)
    {H : Reg S R →L[ℂ] Reg S R} (hH : star H = H)
    (IB : hval (η * |t|) (ε / 2) < 10 ^ 4 → BoundedIface (Reg S R) s (Real.sqrt s * η) H)
    (NB : ∀ hb : hval (η * |t|) (ε / 2) < 10 ^ 4,
      CayleyNative prim (IB hb).UJ (bdPriv (IB hb).K s (η * |t|) (ε / 2)) ZB ζ)
    (IS : 10 ^ 4 ≤ hval (η * |t|) (ε / 2) →
      (s : ℝ) * (η * |t|) < Lval (ε / 2) * hval (η * |t|) (ε / 2) →
      SignedIface (Reg S R) (s * η) (Real.sqrt s)⁻¹ H)
    (NS : ∀ (h1 : 10 ^ 4 ≤ hval (η * |t|) (ε / 2))
      (h2 : (s : ℝ) * (η * |t|) < Lval (ε / 2) * hval (η * |t|) (ε / 2)),
      FactorNative prim (IS h1 h2).UJ (IS h1 h2).U ZS bT bP A ζ)
    (IC : Regime s (η * |t|) (ε / 2) →
      ClippedIface (Reg S R) s (η * |t|) (ε / 2) (s * η / qval s (η * |t|) (ε / 2)) H)
    (NC : ∀ Rg : Regime s (η * |t|) (ε / 2), CayleyNative prim (IC Rg).UJ (IC Rg).D ZC ζ) :
    (∃ hb : hval (η * |t|) (ε / 2) < 10 ^ 4,
      NativeClaims prim
        (nativeOf (NB hb).UJg (NB hb).nd (NB hb).ar (bdSigned (IB hb).a s (η * |t|) (ε / 2) t)) H
        t (ε / 2) (2 * Qone s η t ε) (NB hb).calls (NB hb).cost ε) ∨
    (∃ (h1 : 10 ^ 4 ≤ hval (η * |t|) (ε / 2))
      (h2 : (s : ℝ) * (η * |t|) < Lval (ε / 2) * hval (η * |t|) (ε / 2)),
      NativeClaims prim
        (factorNativeOf (NS h1 h2).UJg (NS h1 h2).fo
          (sgCircuit (IS h1 h2).a (IS h1 h2).f (IS h1 h2).z (s * η) (Real.sqrt s)⁻¹ t (ε / 2)))
        H t (ε / 2) (2 * Qone s η t ε) (NS h1 h2).calls (NS h1 h2).cost ε) ∨
    (∃ Rg : Regime s (η * |t|) (ε / 2),
      NativeClaims prim
        (nativeOf (NC Rg).UJg (NC Rg).nd (NC Rg).ar (clipSigned (IC Rg).a s (η * |t|) (ε / 2) t))
        H t (ε / 2) (2 * Qone s η t ε) (NC Rg).calls (NC Rg).cost ε) := by
  have hε' : 0 < ε / 2 := by linarith
  have hε1' : ε / 2 ≤ 1 / 64 := by linarith
  have hQ0 := Qone_nonneg (s := s) hτ hε' hε1'
  have hQle : Qone s η t (ε / 2) ≤ 2 * Qone s η t ε := Qone_half_le hη hτ hε (by linarith)
  have hζQ : Qone s η t (ε / 2) * ζ ≤ 2 * Qone s η t ε * ζ := mul_le_mul_of_nonneg_right hQle hζ
  have hQζ : 0 ≤ Qone s η t (ε / 2) * ζ := mul_nonneg hQ0 hζ
  have h4 : ε / 2 + 2 * 10 ^ 11 * Qone s η t (ε / 2) * (4 * ζ) ≤ ε := by nlinarith
  have h3 : ε / 2 + 2 * 10 ^ 11 * Qone s η t (ε / 2) * (3 * ζ) ≤ ε := by nlinarith
  rcases gate_optimal_native_single prim hprim hζ hs hη hτ hε' hε1' hH IB NB IS NS IC NC with
    ⟨hh, hN⟩ | ⟨h1, h2, hN⟩ | ⟨Rg, hN⟩
  · exact Or.inl ⟨hh, hN.weaken hε' hQ0 hQle h4⟩
  · exact Or.inr (Or.inl ⟨h1, h2, hN.weaken hε' hQ0 hQle h3⟩)
  · exact Or.inr (Or.inr ⟨Rg, hN.weaken hε' hQ0 hQle h4⟩)

end

end GateOptimalPrecision
