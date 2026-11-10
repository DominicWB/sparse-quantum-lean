import SparseGateAccounting.Accounting
import ManuscriptConformance.GateDecoder
import GeneralSparseODE.Subst
import GateEfficientSelective.HamBridge

/-!
# The constructed controlled private circuit of the sparse accounting

The accounting of `SparseGateAccounting.Accounting` holds for any supplied controlled private
circuit `pc` with the promise `PrivOK`. This file constructs such a circuit from the sparse data and
the arithmetic interface of the decoder, and derives its promise; nothing about the private Cayley
operation, the clock or the decoder's arithmetic beyond the arithmetic interface is assumed.

* `privOp D η hη γ`: the native private operation of the normalised padded data (the compute
  circuit `computeV` of the binary sparse oracles of the padded data, the orientation wire, the
  decoder `γ √s' decode / η` of the padded data with the validity decoder), with every call of a
  padded oracle replaced by its implementation `implPE N s` on the supplied oracles of `D`, the
  implementation ancillas joined to the scratch (`GeneralSparseODE.substOp`);
* `privCirc hS δ D η hη γ ar`: its native implementation `privMacro` with the arithmetic `ar` of
  the padded data on the base wires (`GeneralSparseODE.liftA`), compiled selectively once with the
  synthesis budget `δ` (`GateSelective.privSel`);
* `privCirc_privOK`: for every instance, `privCirc` is within `δ + 4 ζ` of the enable-controlled
  private Cayley operation of the normalised padded data on clean work wires, when `ar` computes
  the rotation parameters of the decoded entries within `ζ` (`GateNative.ArithOK`). The proof
  composes the native identity of the padded data (`GeneralDecoder.sparse_nativeOKD`), the
  implementation of the padded oracles (`GeneralSparseAccess.implOKE`,
  `GeneralSparseODE.nativeOK_substOp`), the native implementation (`GateNative.privMacro_approx`)
  and the selective compilation (`GateSelective.privSel_spec`);
* `privCirc_spec`: validity, gates of the set, the primitive calls (`2 |V'|_calls`, at most
  `6 (2[row] + 2[column] + [value])` of each kind) and the gates
  (`|privCirc| ≤ G_P (1 + c₁ log((G_P + 1)/δ) + c₀)` with
  `G_P = 2 |V'| + 2 |arith| + 2 bP + bT + 1`, `|V'| ≤ 28 (k+1) + 5 (30 (k+1) + 4 b)`);
* `exists_arith`: the arithmetic interface `comp_rotArith` of the decoder at the rescaling
  `γ √s' / η` gives an arithmetic `ar` of the padded data with the cost bound of
  `comp_decArith_padDataE`, fixed before the instance;
* `sparse_gate_native`, `sparse_gate_native_signed`: `sparse_gate_total` and
  `sparse_gate_total_signed` for this circuit, with `24 d (δ + 4 ζ) ≤ ε`;
* `sparse_gate_constructed`: the headline. From the arithmetic interface alone, with
  `ζ = ε/(192 d)` and `δ = ε/(48 d)`: one circuit over the gate set and the supplied sparse oracles,
  fixed before the instance, with exactly `12 d` times the primitive calls of `V'` (at most
  `36 d (2[row] + 2[column] + [value])` of each kind), the explicit private and total gate counts,
  the exact qubit count with the system wires separated, and full-output error at most `ε` on every
  admissible instance, with an untouched reference.

The schedule is that of `sparse_gate_total`: `s' = 2^⌈log₂ s⌉` in place of `s` (see the statement
guide).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.SparseGateAccounting

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim GateNative GateSynth
  GateSelective GateBinary GateSchedule GeneralSparseAccess CayleyClockInterface GeneralDecoder
open GateSynthTrials (AdjClosed)
open ManuscriptConformance (cleanAlong)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

variable {X : Type*} {N s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {Xs : Type*} [Fintype Xs] [DecidableEq Xs] {𝒢 : Set Kind} {L : ℝ → ℕ}

/-! ### The native private operation on the supplied oracles -/

/-- **The native private operation of the construction on the supplied oracles**: the native
operation of the normalised padded data with the decoder `γ √s' decode`, every call of a padded
oracle replaced by its implementation on the supplied oracles of `D`. -/
abbrev privOp (D : QData X N s k b) (η : ℝ) (hη : 0 < η) (γ : ℝ) :
    NativeOp Empty (PR (k + 1)) (SZ (k + 1) b ⊕ AW k b) (PY k b) Query :=
  GeneralSparseODE.substOp (sparseOpD (normPad D η hη) (Equiv.refl _) (γ * Real.sqrt (sP s)))
    (implPE N s)

/-- **The constructed controlled private circuit**: the native implementation of `privOp` with the
arithmetic `ar` on the base wires, compiled selectively with the synthesis budget `δ`. -/
abbrev privCirc (hS : Synthesis 𝒢 Xs L) (δ : ℝ) (D : QData X N s k b) (η : ℝ) (hη : 0 < η)
    (γ : ℝ) (ar : Arith (BW (k + 1) b)) :
    PrivC k b ((SZ (k + 1) b ⊕ AW k b) ⊕ Xs) ar.bT ar.bP ar.A :=
  privSel hS δ (privOp D η hη γ) (GeneralSparseODE.liftA (Xa := AW k b) ar)

/-- The decoder of the normalised padded data at the rescaling `κ` is the decoder of the padded
data at `κ / η`. -/
theorem normPad_dec (D : QData X N s k b) {η : ℝ} (hη : 0 < η) (κ : ℝ) :
    (sparseOpD (normPad D η hη) (Equiv.refl _) κ).dec =
      fun y => ((κ / η : ℝ) : ℂ) * D.padDataE.decode (phiE (Equiv.refl _) (eword y)) (vword y) := by
  funext y
  show (κ : ℂ) * (((η⁻¹ : ℝ) : ℂ) * D.padDataE.decode _ _) = _
  push_cast
  ring

/-- The native private operation satisfies the public conditions. -/
theorem privOp_public (D : QData X N s k b) {η : ℝ} (hη : 0 < η) (γ : ℝ) :
    (privOp D η hη γ).Public :=
  GeneralSparseODE.substOp_public (sparseOpD_public _ _ _) (valid_implPE N s)

/-- **The calls of the compute circuit**: at most `3` calls of a kind for each call of that kind of
the compute circuit of the padded data, `2` row-location, `2` column-location and `1` value call. -/
theorem privOp_calls (D : QData X N s k b) {η : ℝ} (hη : 0 < η) (γ : ℝ) (p : Query → Bool) :
    nCallsN p (privOp D η hη γ).V ≤
      3 * (2 * (if p Query.rowLocation then 1 else 0) +
        2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0)) := by
  have h := GeneralSparseODE.nCallsN_substOp_le
    (sparseOpD (normPad D η hη) (Equiv.refl _) (γ * Real.sqrt (sP s)))
    (kindOK_implPE (k := k) (b := b) N s) p
  rw [sparseOpD_V, computeV_nCalls] at h
  exact h

/-- **The gates of the compute circuit**: `28 (k + 1)` gates of the compute circuit of the padded
data and at most `implG k b = 30 (k+1) + 4 b` gates for each of its `5` calls. -/
theorem privOp_gates (D : QData X N s k b) {η : ℝ} (hη : 0 < η) (γ : ℝ) :
    nGatesN (privOp D η hη γ).V ≤ 28 * (k + 1) + implG k b * 5 := by
  have h := GeneralSparseODE.nGatesN_substOp_le
    (sparseOpD (normPad D η hη) (Equiv.refl _) (γ * Real.sqrt (sP s))) (implPE N s) (implG k b)
    (nGatesN_implPE_le N s)
  rw [sparseOpD_V, computeV_nGates, computeV_nCalls] at h
  simpa using h

/-- The all-zero index word is a slot of the normalised padded data. -/
theorem normPad_zero_slot (D : QData X N s k b) {η : ℝ} (hη : 0 < η) :
    ∃ m, (normPad D η hη).slot m = zIdx (Equiv.refl (Cfg (Fin (k + 1)))) := by
  refine (normPad_range D η hη _).2 ⟨fun _ => false, ?_⟩
  unfold zIdx
  funext i
  simp [lowWord]

/-- **The promise of the constructed circuit** (`PrivOK`), derived: for every instance, the
constructed circuit is within `δ + 4 ζ` of the enable-controlled private Cayley operation of the
normalised padded data on clean work wires, when the arithmetic `ar` computes the rotation
parameters of the decoded entries within `ζ`. -/
theorem privCirc_privOK (hS : Synthesis 𝒢 Xs L) {δ : ℝ} (hδ : 0 < δ) (D : QData X N s k b)
    {η : ℝ} (hη : 0 < η) (γ : ℝ) (ar : Arith (BW (k + 1) b)) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr (oPR (k + 1))))
      (sparseOpD (normPad D η hη) (Equiv.refl _) (γ * Real.sqrt (sP s))).dec ζ) (x : X) :
    PrivOK (R := R) D η hη x γ (δ + 4 * ζ) (privCirc hS δ D η hη γ ar) := by
  have har' := GeneralSparseODE.arithOK_liftA (Xa := AW k b) ar (oPR (k + 1)) _ ζ har
  obtain ⟨-, -, -, -, happrox⟩ := privSel_spec (R := R) hS hδ (privOp D η hη γ)
    (privOp_public D hη γ) (GeneralSparseODE.liftA (Xa := AW k b) ar) hζ har'
  obtain ⟨k0, hk0⟩ := normPad_zero_slot D hη
  have hN := sparse_nativeOKD (R := R) (normPad D η hη) (Equiv.refl _) k0 hk0 x γ
  have hN' := GeneralSparseODE.nativeOK_substOp (D.prims (R := R) x)
    (GateBinary.prims (R := R) D.padDataE (Equiv.refl _) x) (D.prims_isUnitary x)
    (GateBinary.prims_isUnitary _ _ x) (implOKE (R := R) (N := N) (s := s) D x)
    (sparseOpD (normPad D η hη) (Equiv.refl _) (γ * Real.sqrt (sP s))) (sparseOpD_public _ _ _)
    _ hN
  exact happrox (D.prims (R := R) x) (D.prims_isUnitary x) _ hN'

/-! ### The counts of the constructed circuit -/

/-- **The gates of the native implementation** before the selective compilation:
`G_P = 2 |V'| + 2 |arith| + 2 bP + bT + 1` (`GateNative.privMacro_nGates`). -/
abbrev privG (D : QData X N s k b) (η : ℝ) (hη : 0 < η) (γ : ℝ) (ar : Arith (BW (k + 1) b)) :
    ℕ :=
  2 * nGatesN (privOp D η hη γ).V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)

/-- **The gates of a selectively compiled circuit**: if the kept and the synthesised occurrences
add to `G` and each of the `K` synthesised occurrences costs `L(δ/(K+1))` gates, then there are at
most `G (1 + c₁ log((G + 1)/δ) + c₀)` gates. -/
theorem selGates_le {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {G Kp K n : ℕ} (hsum : Kp + K = G)
    (hn : n ≤ Kp + K * L (δ / (K + 1))) :
    (n : ℝ) ≤ G * (1 + c₁ * Real.log ((G + 1) / δ) + c₀) := by
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hz : 0 < δ / ((K : ℝ) + 1) := div_pos hδ hK1
  have hz1 : δ / ((K : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hK1]
    linarith
  have hKG : (K : ℝ) ≤ G := by exact_mod_cast (show K ≤ G by omega)
  have hKpG : (Kp : ℝ) + K = G := by exact_mod_cast hsum
  have hG0 : (0 : ℝ) ≤ G := Nat.cast_nonneg G
  have hlog : Real.log (1 / (δ / ((K : ℝ) + 1))) ≤ Real.log (((G : ℝ) + 1) / δ) := by
    rw [one_div_div]
    exact Real.log_le_log (div_pos hK1 hδ) (div_le_div_of_nonneg_right (by linarith) hδ.le)
  have hlog0 : 0 ≤ Real.log (((G : ℝ) + 1) / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hLK : (L (δ / ((K : ℝ) + 1)) : ℝ) ≤ c₁ * Real.log (((G : ℝ) + 1) / δ) + c₀ :=
    (hL _ hz hz1).trans (by gcongr)
  have hn' : (n : ℝ) ≤ Kp + K * (L (δ / ((K : ℝ) + 1)) : ℝ) := by exact_mod_cast hn
  have h0 : 0 ≤ c₁ * Real.log (((G : ℝ) + 1) / δ) + c₀ := by positivity
  calc (n : ℝ) ≤ Kp + K * (L (δ / ((K : ℝ) + 1)) : ℝ) := hn'
    _ ≤ Kp + K * (c₁ * Real.log (((G : ℝ) + 1) / δ) + c₀) := by gcongr
    _ ≤ G * (1 + c₁ * Real.log ((G + 1) / δ) + c₀) := by nlinarith

/-- **The constructed circuit**: valid; every gate a gate of `𝒢`; exactly `2 |V'|_calls` primitive
calls, at most `3 (2[row] + 2[column] + [value])` of each kind in `V'`; at most
`28 (k+1) + 5 (30 (k+1) + 4 b)` gates in `V'`; at most `G_P (1 + c₁ log((G_P + 1)/δ) + c₀)` gates;
and, for every instance, the promise `PrivOK` with `ξ = δ + 4 ζ`. -/
theorem privCirc_spec (hS : Synthesis 𝒢 Xs L) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (D : QData X N s k b) {η : ℝ} (hη : 0 < η) (γ : ℝ)
    (ar : Arith (BW (k + 1) b)) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr (oPR (k + 1))))
      (sparseOpD (normPad D η hη) (Equiv.refl _) (γ * Real.sqrt (sP s))).dec ζ) :
    (∀ i ∈ privCirc hS δ D η hη γ ar, i.Valid) ∧
    (∀ g, NInstr.gate g ∈ privCirc hS δ D η hη γ ar → GateOf 𝒢 g) ∧
    (∀ p : Query → Bool, nCallsN p (privCirc hS δ D η hη γ ar) =
      2 * nCallsN p (privOp D η hη γ).V) ∧
    (∀ p : Query → Bool, nCallsN p (privOp D η hη γ).V ≤
      3 * (2 * (if p Query.rowLocation then 1 else 0) +
        2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0))) ∧
    nGatesN (privOp D η hη γ).V ≤ 28 * (k + 1) + implG k b * 5 ∧
    (nGatesN (privCirc hS δ D η hη γ ar) : ℝ) ≤
      (privG D η hη γ ar : ℝ) *
        (1 + c₁ * Real.log (((privG D η hη γ ar : ℝ) + 1) / δ) + c₀) ∧
    ∀ x : X, PrivOK (R := R) D η hη x γ (δ + 4 * ζ) (privCirc hS δ D η hη γ ar) := by
  have har' := GeneralSparseODE.arithOK_liftA (Xa := AW k b) ar (oPR (k + 1)) _ ζ har
  obtain ⟨hv, hg, hgates, hc, -⟩ := privSel_spec (R := R) hS hδ (privOp D η hη γ)
    (privOp_public D hη γ) (GeneralSparseODE.liftA (Xa := AW k b) ar) hζ har'
  have hsum := nKeepN_add_nSynN 𝒢
    (privMacro (privOp D η hη γ) (GeneralSparseODE.liftA (Xa := AW k b) ar))
  rw [privMacro_nGates, GeneralSparseODE.liftA_circ_length] at hsum
  exact ⟨hv, hg, hc, privOp_calls D hη γ, privOp_gates D hη γ,
    selGates_le hc₀ hc₁ hL hδ hδ1 hsum hgates,
    fun x => privCirc_privOK hS hδ D hη γ ar hζ har x⟩

/-! ### The arithmetic of the construction from the arithmetic interface of the decoder -/

/-- **The arithmetic of the construction** from the arithmetic interface of the decoder
(`ManuscriptConformance.comp_rotArith`) at the rescaling `γ √s' / η`: an arithmetic of the padded
data computing the rotation parameters of the decoded entries `γ √s' decode / η` within `ζ`, with
the cost bound of `ManuscriptConformance.comp_decArith_padDataE`. It depends on the public data
`γ`, `η`, `ζ` only, not on the instance. -/
theorem exists_arith {cA : ℝ} {dA : ℕ} (hcA : 0 ≤ cA) (D : QData X N s k b) {bd : ℕ} {K₀ K : ℝ}
    (hrot : ManuscriptConformance.comp_rotArith cA dA bd k b D.val K₀ K) {η : ℝ} (hη : 0 < η)
    {γ : ℝ} (hγ : 0 < γ) (hK₀ : K₀ ≤ γ * Real.sqrt (sP s) / η)
    (hK : γ * Real.sqrt (sP s) / η ≤ K) {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    ∃ ar : Arith (BW (k + 1) b),
      ArithOK ar (Sum.inl (Sum.inr (oPR (k + 1))))
        (sparseOpD (normPad D η hη) (Equiv.refl _) (γ * Real.sqrt (sP s))).dec ζ ∧
      ((ar.circ.length + ar.bT + ar.bP + ar.A : ℕ) : ℝ) ≤
        (3 * cA + 18) * ((bd : ℝ) + ((k + 1 : ℕ) : ℝ) + Real.logb 2 (1 / ζ) + 1) ^ max dA 1 := by
  have hdec := ManuscriptConformance.comp_decArith_padDataE hcA D hrot
  have hs : (0 : ℝ) < Real.sqrt (sP s) := Real.sqrt_pos.2 (by exact_mod_cast sP_pos s)
  have hκ : 0 < γ * Real.sqrt (sP s) / η := div_pos (mul_pos hγ hs) hη
  obtain ⟨ar, hok, hcost⟩ := hdec _ hκ hK₀ hK ζ hζ hζ1
  refine ⟨ar, ?_, hcost⟩
  rw [normPad_dec]
  exact hok

/-! ### The accounting for the constructed circuit -/

set_option maxRecDepth 8192 in
/-- **Equations `hs:eq:gate-Gzero` and `hs:eq:gate-total` for the constructed private circuit**
(`sparse_gate_total` with `pc = privCirc hS δ D η hη γ ar`): for an arithmetic `ar` of the padded
data computing the rotation parameters of the decoded entries within `ζ` and `24 d (δ + 4 ζ) ≤ ε`,
every conclusion of `sparse_gate_total`; the promise `PrivOK` is derived (`privCirc_privOK`). -/
theorem sparse_gate_native (hS : Synthesis 𝒢 Xs L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (D : QData X N s k b) {η : ℝ} (hη : 0 < η) (ar : Arith (BW (k + 1) b)) {δ ζ : ℝ}
    (hδ : 0 < δ) (hζ : 0 ≤ ζ) (γ T τ ε : ℝ)
    (har : ArithOK ar (Sum.inl (Sum.inr (oPR (k + 1))))
      (sparseOpD (normPad D η hη) (Equiv.refl _) (γ * Real.sqrt (sP s))).dec ζ)
    (hτ : τ = clock s η T γ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hT : 0 ≤ T) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hξε : 24 * (dg s γ τ ε : ℝ) * (δ + 4 * ζ) ≤ ε) (x : X)
    (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    (∀ i ∈ finC hS D γ τ ε (privCirc hS δ D η hη γ ar), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ finC hS D γ τ ε (privCirc hS δ D η hη γ ar) → GateOf 𝒢 g) ∧
    (∀ p : Query → Bool, nCallsN p (finC hS D γ τ ε (privCirc hS δ D η hη γ ar)) =
      6 * dg s γ τ ε * nCallsN p (privCirc hS δ D η hη γ ar)) ∧
    nSynN 𝒢 (preC D γ τ ε (privCirc hS δ D η hη γ ar)) ≤ synG k s γ τ ε ∧
    (nGatesN (finC hS D γ τ ε (privCirc hS δ D η hη γ ar)) : ℝ) ≤
      6 * (dg s γ τ ε : ℝ) * nGatesN (privCirc hS δ D η hη γ ar) + (synG k s γ τ ε : ℝ) *
        (c₁ * Real.log (((synG k s γ τ ε : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
    Fintype.card (HW (SimWireMs (k + 1 + 1) (width ((sP s : ℕ) : ℝ) γ) τ (moment γ) ε) (Fin (k + 1))
        Empty ((SZ (k + 1) b ⊕ AW k b) ⊕ Xs) ar.bT ar.bP ar.A ⊕ Xs) =
      k + 1 + (2 * (k + 1 + 1) + 3 * slotMs τ ε + 6 * rg s γ τ ε + 3) +
        (Fintype.card ((SZ (k + 1) b ⊕ AW k b) ⊕ Xs) + ar.bT + ar.bP + ar.A + 3) +
        Fintype.card Xs ∧
    ‖nrun (D.prims (R := R) x) (finC hS D γ τ ε (privCirc hS δ D η hη γ ar)) ∘L
        (cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          NormedSpace.exp ((-Complex.I * (T : ℂ)) • qlift (R := R) (Equiv.refl _)
            (SparseStateOverlap.matrixOperator (D.padDataE.matrix x)))‖ ≤ ε ∧
    ‖nrun (D.prims (R := R) x) (finC hS D γ τ ε (privCirc hS δ D η hη γ ar)) ∘L
        ((cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) -
        ((cleanEmb ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) ∘L
          NormedSpace.exp ((-Complex.I * (T : ℂ)) • qlift (R := R) (Equiv.refl _)
            (SparseStateOverlap.matrixOperator (D.padMat x)))‖ ≤ ε ∧
    dg s γ τ ε = depthMs (width ((sP s : ℕ) : ℝ) γ) (τ * moment γ) ε *
      (SharpFilterSchedule.length (width ((sP s : ℕ) : ℝ) γ) - 1) ∧
    (dg s γ τ ε : ℝ) ≤ 128 * (τ * moment γ) +
      32 * width ((sP s : ℕ) : ℝ) γ * (Real.logb 2 (4096 / ε) + 1) ∧
    meshMs τ ε ≤ 2 ^ slotMs τ ε ∧ (∀ j : ℕ, meshMs τ ε ≤ 2 ^ j → slotMs τ ε ≤ j) ∧
    rg s γ τ ε = Nat.clog 2 (2 * dg s γ τ ε + 2) := by
  have har' := GeneralSparseODE.arithOK_liftA (Xa := AW k b) ar (oPR (k + 1)) _ ζ har
  obtain ⟨hv, hg, -, -, -⟩ := privSel_spec (R := R) hS hδ (privOp D η hη γ)
    (privOp_public D hη γ) (GeneralSparseODE.liftA (Xa := AW k b) ar) hζ har'
  exact sparse_gate_total hS hadj hc₀ hc₁ hL D hη (privCirc hS δ D η hη γ ar) hv hg (δ + 4 * ζ)
    (by positivity) γ T τ ε hτ hγ hγ1 hT hε hε1 hξε x hH hrow hcol
    (privCirc_privOK hS hδ D hη γ ar hζ har x)

set_option maxRecDepth 8192 in
/-- **Every real time for the constructed private circuit** (`sparse_gate_total_signed` with
`pc = privCirc hS δ D η hη γ ar`): for the signed clock `t' = η t √s' / γ`, the circuit of `|t'|`,
or its literal reverse-adjoint for `t < 0`, with `24 d (δ + 4 ζ) ≤ ε` at the clock `|t'|`. -/
theorem sparse_gate_native_signed (hS : Synthesis 𝒢 Xs L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (D : QData X N s k b) {η : ℝ} (hη : 0 < η) (ar : Arith (BW (k + 1) b)) {δ ζ : ℝ}
    (hδ : 0 < δ) (hζ : 0 ≤ ζ) (γ t t' ε : ℝ)
    (har : ArithOK ar (Sum.inl (Sum.inr (oPR (k + 1))))
      (sparseOpD (normPad D η hη) (Equiv.refl _) (γ * Real.sqrt (sP s))).dec ζ)
    (ht' : t' = clock s η t γ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hξε : 24 * (dg s γ |t'| ε : ℝ) * (δ + 4 * ζ) ≤ ε) (x : X) (hH : (D.matrix x).IsHermitian)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    (∀ i ∈ finCSigned hS D γ t' ε (privCirc hS δ D η hη γ ar), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ finCSigned hS D γ t' ε (privCirc hS δ D η hη γ ar) → GateOf 𝒢 g) ∧
    (∀ p : Query → Bool, nCallsN p (finCSigned hS D γ t' ε (privCirc hS δ D η hη γ ar)) =
      6 * dg s γ |t'| ε * nCallsN p (privCirc hS δ D η hη γ ar)) ∧
    (nGatesN (finCSigned hS D γ t' ε (privCirc hS δ D η hη γ ar)) : ℝ) ≤
      6 * (dg s γ |t'| ε : ℝ) * nGatesN (privCirc hS δ D η hη γ ar) +
        (synG k s γ |t'| ε : ℝ) *
          (c₁ * Real.log (((synG k s γ |t'| ε : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
    Fintype.card (HW (SimWireMs (k + 1 + 1) (width ((sP s : ℕ) : ℝ) γ) |t'| (moment γ) ε)
        (Fin (k + 1)) Empty ((SZ (k + 1) b ⊕ AW k b) ⊕ Xs) ar.bT ar.bP ar.A ⊕ Xs) =
      k + 1 + (2 * (k + 1 + 1) + 3 * slotMs |t'| ε + 6 * rg s γ |t'| ε + 3) +
        (Fintype.card ((SZ (k + 1) b ⊕ AW k b) ⊕ Xs) + ar.bT + ar.bP + ar.A + 3) +
        Fintype.card Xs ∧
    ‖nrun (D.prims (R := R) x) (finCSigned hS D γ t' ε (privCirc hS δ D η hη γ ar)) ∘L
        (cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
            (SparseStateOverlap.matrixOperator (D.padDataE.matrix x)))‖ ≤ ε ∧
    ‖nrun (D.prims (R := R) x) (finCSigned hS D γ t' ε (privCirc hS δ D η hη γ ar)) ∘L
        ((cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) -
        ((cleanEmb ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
            (SparseStateOverlap.matrixOperator (D.padMat x)))‖ ≤ ε := by
  have har' := GeneralSparseODE.arithOK_liftA (Xa := AW k b) ar (oPR (k + 1)) _ ζ har
  obtain ⟨hv, hg, -, -, -⟩ := privSel_spec (R := R) hS hδ (privOp D η hη γ)
    (privOp_public D hη γ) (GeneralSparseODE.liftA (Xa := AW k b) ar) hζ har'
  exact sparse_gate_total_signed hS hadj hc₀ hc₁ hL D hη (privCirc hS δ D η hη γ ar) hv hg
    (δ + 4 * ζ) (by positivity) γ t t' ε ht' hγ hγ1 hε hε1 hξε x hH hrow hcol
    (privCirc_privOK hS hδ D hη γ ar hζ har x)

/-- **The budgets of the headline**: for `d ≥ 1` and `0 < ε ≤ 1`, `ζ = ε/(192 d)` and
`δ = ε/(48 d)` lie in `(0, 1]` and `24 d (δ + 4 ζ) = ε`. -/
theorem budget_facts {ε d : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hd : 1 ≤ d) :
    0 < ε / (192 * d) ∧ ε / (192 * d) ≤ 1 ∧ 0 < ε / (48 * d) ∧ ε / (48 * d) ≤ 1 ∧
      24 * d * (ε / (48 * d) + 4 * (ε / (192 * d))) ≤ ε := by
  have hd0 : 0 < d := by linarith
  refine ⟨by positivity, ?_, by positivity, ?_, ?_⟩
  · rw [div_le_one (by positivity)]
    nlinarith
  · rw [div_le_one (by positivity)]
    nlinarith
  · have e : 24 * d * (ε / (48 * d) + 4 * (ε / (192 * d))) = ε := by
      field_simp
      ring
    exact e.le

/-! ### The headline: the construction from the arithmetic interface alone -/

set_option maxRecDepth 8192 in
/-- **Theorem `hs:thm:gates` with the explicit accounting of eqs. `hs:eq:gate-known`,
`hs:eq:gate-Gzero` and `hs:eq:gate-total`, the private circuit constructed** for sparse access of
general size with any public decoder. From the synthesis hypothesis (`L ζ ≤ c₁ log(1/ζ) + c₀`,
`𝒢` closed under adjoints) and the arithmetic interface of the decoder (`comp_rotArith` on a range
`[K₀, K]` containing the rescaling `γ √s' / η`), with `ζ = ε/(192 d)` and `δ = ε/(48 d)`: there is an
arithmetic `ar` of the padded data, fixed by the public data, with gates and work wires at most
`(3 c_A + 18)(b_data + k + 1 + log₂(192 d/ε) + 1)^{max d_A 1}`, such that the circuit
`finC hS D γ τ ε (privCirc hS (ε/(48 d)) D η hη γ ar)` over `𝒢` and the supplied sparse oracles satisfies:

* its compute circuit `V'` makes at most `3 (2[row] + 2[column] + [value])` calls of each kind and
  has at most `28 (k+1) + 5 (30 (k+1) + 4 b)` gates; the private circuit has at most
  `G_P (1 + c₁ log((G_P + 1)/δ) + c₀)` gates, `G_P = 2 |V'| + 2 |arith| + 2 bP + bT + 1`;
* on every instance whose matrix is Hermitian with row and column Euclidean norms at most `η`: the
  circuit is valid and over `𝒢`; it makes exactly `6 d` private calls, hence exactly `12 d` times the
  primitive calls of `V'`; it synthesises at most `G₀` occurrences outside the private circuit; it
  has at most `6 d |pc| + G₀ (c₁ log((G₀+1)/(ε/4)) + c₀ + 1)` gates; it has
  `k + 1` system qubits and `(2a + 3m + 6r + 3) + (|SZ| + |AW| + |X| + bT + bP + A + 3) + |X|`
  further qubits, `|SZ| = 6 (k+1) + 2b`, `|AW| = 6k + 6 + 2b`; its full output, with every other
  qubit clean and an untouched reference, is within `ε` of the evolution, on the padded index
  register and on the clean marker against `QData.padMat`; and the schedule is that of
  `sparse_gate_total` (`s'` in place of `s`). -/
theorem sparse_gate_constructed (cA : ℝ) (dA : ℕ) (hcA : 0 ≤ cA) (hS : Synthesis 𝒢 Xs L)
    (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (D : QData X N s k b) (bd : ℕ) {K₀ K : ℝ}
    (hrot : ManuscriptConformance.comp_rotArith cA dA bd k b D.val K₀ K) {η : ℝ} (hη : 0 < η)
    (γ T τ ε : ℝ) (hτ : τ = clock s η T γ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hK₀ : K₀ ≤ γ * Real.sqrt (sP s) / η) (hK : γ * Real.sqrt (sP s) / η ≤ K) (hT : 0 ≤ T)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ ar : Arith (BW (k + 1) b),
      ((ar.circ.length + ar.bT + ar.bP + ar.A : ℕ) : ℝ) ≤
        (3 * cA + 18) * ((bd : ℝ) + ((k + 1 : ℕ) : ℝ) +
          Real.logb 2 (192 * (dg s γ τ ε : ℝ) / ε) + 1) ^ max dA 1 ∧
      (∀ p : Query → Bool, nCallsN p (privOp D η hη γ).V ≤
        3 * (2 * (if p Query.rowLocation then 1 else 0) +
          2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0))) ∧
      nGatesN (privOp D η hη γ).V ≤ 28 * (k + 1) + implG k b * 5 ∧
      (nGatesN (privCirc hS (ε / (48 * (dg s γ τ ε : ℝ))) D η hη γ ar) : ℝ) ≤ (privG D η hη γ ar : ℝ) *
        (1 + c₁ * Real.log (((privG D η hη γ ar : ℝ) + 1) / (ε / (48 * (dg s γ τ ε : ℝ)))) +
          c₀) ∧
      ∀ x : X, (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
        (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
        (∀ i ∈ finC hS D γ τ ε (privCirc hS (ε / (48 * (dg s γ τ ε : ℝ))) D η hη γ ar), i.Valid) ∧
        (∀ g, NInstr.gate g ∈ finC hS D γ τ ε (privCirc hS (ε / (48 * (dg s γ τ ε : ℝ))) D η hη γ ar) → GateOf 𝒢 g) ∧
        (∀ p : Query → Bool, nCallsN p (finC hS D γ τ ε (privCirc hS (ε / (48 * (dg s γ τ ε : ℝ))) D η hη γ ar)) =
          6 * dg s γ τ ε * (2 * nCallsN p (privOp D η hη γ).V)) ∧
        nSynN 𝒢 (preC D γ τ ε (privCirc hS (ε / (48 * (dg s γ τ ε : ℝ))) D η hη γ ar)) ≤ synG k s γ τ ε ∧
        (nGatesN (finC hS D γ τ ε (privCirc hS (ε / (48 * (dg s γ τ ε : ℝ))) D η hη γ ar)) : ℝ) ≤
          6 * (dg s γ τ ε : ℝ) * nGatesN (privCirc hS (ε / (48 * (dg s γ τ ε : ℝ))) D η hη γ ar) + (synG k s γ τ ε : ℝ) *
            (c₁ * Real.log (((synG k s γ τ ε : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
        Fintype.card (HW (SimWireMs (k + 1 + 1) (width ((sP s : ℕ) : ℝ) γ) τ (moment γ) ε)
            (Fin (k + 1)) Empty ((SZ (k + 1) b ⊕ AW k b) ⊕ Xs) ar.bT ar.bP ar.A ⊕ Xs) =
          k + 1 + (2 * (k + 1 + 1) + 3 * slotMs τ ε + 6 * rg s γ τ ε + 3) +
            ((6 * (k + 1) + 2 * b) + (6 * k + 6 + 2 * b) + Fintype.card Xs + ar.bT + ar.bP +
              ar.A + 3) + Fintype.card Xs ∧
        ‖nrun (D.prims (R := R) x) (finC hS D γ τ ε (privCirc hS (ε / (48 * (dg s γ τ ε : ℝ))) D η hη γ ar)) ∘L
            (cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) -
            (cleanEmb ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
              NormedSpace.exp ((-Complex.I * (T : ℂ)) • qlift (R := R) (Equiv.refl _)
                (SparseStateOverlap.matrixOperator (D.padDataE.matrix x)))‖ ≤ ε ∧
        ‖nrun (D.prims (R := R) x) (finC hS D γ τ ε (privCirc hS (ε / (48 * (dg s γ τ ε : ℝ))) D η hη γ ar)) ∘L
            ((cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
              cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) -
            ((cleanEmb ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
              cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) ∘L
              NormedSpace.exp ((-Complex.I * (T : ℂ)) • qlift (R := R) (Equiv.refl _)
                (SparseStateOverlap.matrixOperator (D.padMat x)))‖ ≤ ε ∧
        dg s γ τ ε = depthMs (width ((sP s : ℕ) : ℝ) γ) (τ * moment γ) ε *
          (SharpFilterSchedule.length (width ((sP s : ℕ) : ℝ) γ) - 1) ∧
        (dg s γ τ ε : ℝ) ≤ 128 * (τ * moment γ) +
          32 * width ((sP s : ℕ) : ℝ) γ * (Real.logb 2 (4096 / ε) + 1) ∧
        meshMs τ ε ≤ 2 ^ slotMs τ ε ∧ (∀ j : ℕ, meshMs τ ε ≤ 2 ^ j → slotMs τ ε ≤ j) ∧
        rg s γ τ ε = Nat.clog 2 (2 * dg s γ τ ε + 2) := by
  have hτ0 : 0 ≤ τ := by
    rw [hτ]
    exact div_nonneg (mul_nonneg (mul_nonneg hη.le hT) (Real.sqrt_nonneg _)) hγ.le
  have hdR : (1 : ℝ) ≤ (dg s γ τ ε : ℝ) := by exact_mod_cast dg_pos s γ hτ0 hε hε1
  obtain ⟨hζ, hζ1, hδ, hδ1, hξ⟩ := budget_facts hε hε1 hdR
  obtain ⟨ar, hok, hcost⟩ := exists_arith hcA D hrot hη hγ hK₀ hK hζ hζ1
  obtain ⟨-, -, hcC, hcV, hgV, hgP, -⟩ := privCirc_spec (R := R) hS hc₀ hc₁ hL hδ hδ1 D hη γ ar
    hζ.le hok
  refine ⟨ar, ?_, hcV, hgV, hgP, fun x hH hrow hcol => ?_⟩
  · rw [one_div_div] at hcost
    exact hcost
  obtain ⟨hv, hg, hc, hsyn, hgates, hcard, herr1, herr2, hd, hdle, hm1, hm2, hr⟩ :=
    sparse_gate_native (R := R) hS hadj hc₀ hc₁ hL D hη ar hδ hζ.le γ T τ ε hok hτ hγ hγ1 hT hε
      hε1 hξ x hH hrow hcol
  refine ⟨hv, hg, fun p => by rw [hc p, hcC p], hsyn, hgates, ?_, herr1, herr2, hd, hdle, hm1,
    hm2, hr⟩
  rw [hcard, Fintype.card_sum, Fintype.card_sum, card_SZ, ManuscriptConformance.card_AW]

end

end SparseHamiltonian.SparseGateAccounting
