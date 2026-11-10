import GateOptimalPrecision.SignedExpand
import SignedFactorSimulation.Core

/-!
# The signed-factor gate circuit for `q ≥ 1`

Section `gate:sec:signed`: with the clock weights of Theorem `opt:thm:weights` (`n ≤ 27 a` reuse
lengths, `a = qM`, total variation at most `A_* = 3000`), a mesh of `J = 2^m` private slots with
step `v = a/J` and `c = (1 - v/2)/(1 + v/2)` (`CayleyTransfer.c v`), the signed LCU of Lemma
`gate:lem:reuse` with weights `λ_j` normalised by `A₀ = 1/s₀`, `s₀ = sin(π/(2·3⁸))`, and `3⁸`
oblivious amplification calls.

* Public parameters: `sigN q M = n`; the least admissible slot count
  `sigMeshLB = max(8an, √(768000 a³ n⁴/η))` with `η = ε²/(2·7⁸)` (the finite-mesh estimate
  `opt:eq:finite-mesh` at `A_* = 3000` gives mesh error at most `η/2`, the manuscript's
  `gate:eq:factor-mesh` with its `ε²/144` budget replaced by `η/2`); `2^m` is the least power of two
  at least `sigMeshLB` (`sigM`); the label register has `2^r ≥ n + 2` (`sigR`).
* `sigBase`: the released LCU circuit with the padded clock table; `sigAmp`: `8` rounds of
  amplification (`ampIt`); `sigCircuit`: every oracle call expanded (`expandI`): factor calls of
  `U_B` on the last `a` ancillas, three phase gates per private call, the attenuation rotation on
  ancilla `0` before every boundary call of `U_J`.
* `sig_block`: the clean block of `sigBase` is `s₀ ∑_j λ_j Ces_j(F_J)`.
* **`sig_core`**: for the attenuated factor interface `attKnown` with `D' ⪯ δ I`,
  `M ≥ 2·27² q²Mδ` and the factorial tail at most `ε²/(4·7⁸)`, the full output of the gate circuit
  is within `ε` of `e^{-i q²M C'}`.
* `sig_counts`: exactly `2·3⁸ n` factor calls (counting `U_B†`), exactly `2·3⁸ n` calls of `U_J`
  (counting `U_J†`), and at most `3⁸ (G_lcu + 2(a+1+m+2r) + 3) + 3⁸·5n` elementary gates, where
  `G_lcu` is the released LCU gate bound; `sig_valid`: every instruction is valid.
-/

set_option autoImplicit false

namespace GateOptimalPrecision

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim
open Complex (I)
open Finset (Icc)
open OptimalPrecision (ces clockLength clockWeight)
open SignedFactorSimulation (Known)
open scoped InnerProduct InnerProductSpace BigOperators ComplexOrder

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Public parameters -/

/-- The number `n` of clock weights. -/
abbrev sigN (q : ℝ) (M : ℕ) : ℕ := clockLength q M

/-- The block budget `η = ε²/(2·7⁸)`. -/
def sigEta (ε : ℝ) : ℝ := ε ^ 2 / (2 * 7 ^ 8)

/-- The least admissible number of slots, `max(8an, √(768000 a³ n⁴/η))` with `a = qM`. -/
def sigMeshLB (q : ℝ) (M : ℕ) (ε : ℝ) : ℝ :=
  max (8 * (q * M) * sigN q M)
    (Real.sqrt (768000 * (q * M) ^ 3 * (sigN q M : ℝ) ^ 4 / sigEta ε))

/-- The slot exponent: `2^m` is the least power of two at least `sigMeshLB`. -/
def sigM (q : ℝ) (M : ℕ) (ε : ℝ) : ℕ := Nat.clog 2 ⌈sigMeshLB q M ε⌉₊

/-- The pointer and label width: `2^r ≥ n + 2`. -/
def sigR (q : ℝ) (M : ℕ) : ℕ := Nat.clog 2 (sigN q M + 2)

/-- The AND-chain pool. -/
def sigK (a : ℕ) (q : ℝ) (M : ℕ) (ε : ℝ) : ℕ := (a + 1) + sigM q M ε + 2 * sigR q M

/-- The wires of the signed-factor circuit: `a + 1` ancillas (the attenuation flag and the `a`
ancillas of the factor), the sector, slot, pointer and label wires, and the work wires. -/
abbrev SigWire (a : ℕ) (q : ℝ) (M : ℕ) (ε : ℝ) :=
  Wire (a + 1) (sigM q M ε) (sigR q M) (sigK a q M ε)

/-- The amplification amplitude `s₀ = sin(π/(2·3⁸))`. -/
abbrev s0 : ℝ := SignedFactorSimulation.ampS 8 0

theorem s0_pos : 0 < s0 := by
  unfold s0 SignedFactorSimulation.ampS
  apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
  have hp := Real.pi_pos
  rw [pow_zero, one_mul, div_lt_iff₀ (by positivity)]
  nlinarith

/-- The ordinary clock weights `λ_{j+1}`. -/
def sigWt (q : ℝ) (M : ℕ) : Fin (sigN q M) → ℝ := fun j => clockWeight q M (j + 1)

/-- The reuse lengths `j + 1`. -/
def sigLen (q : ℝ) (M : ℕ) : Fin (sigN q M) → ℕ := fun j => j + 1

/-- The Cayley step `v = a/2^m`. -/
def sigStep (q : ℝ) (M : ℕ) (ε : ℝ) : ℝ := stepW (q * M) (sigM q M ε)

theorem sigR_spec (q : ℝ) (M : ℕ) :
    sigN q M + 2 ≤ 2 ^ sigR q M ∧ 0 < sigR q M ∧ 2 ^ sigR q M < 2 * (sigN q M + 2) := by
  have h1 : 1 < sigN q M + 2 := by omega
  refine ⟨Nat.le_pow_clog (by norm_num) _, Nat.clog_pos (by norm_num) h1, ?_⟩
  have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h1
  have hpos : 0 < sigR q M := Nat.clog_pos (by norm_num) h1
  unfold sigR at hpos ⊢
  have : 2 ^ Nat.clog 2 (sigN q M + 2) = 2 * 2 ^ (Nat.clog 2 (sigN q M + 2)).pred := by
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
    rw [pow_succ]; ring
  omega

theorem sigL (q : ℝ) (M : ℕ) : sigN q M + 2 ≤ 2 ^ sigR q M := (sigR_spec q M).1

theorem sigM_spec (q : ℝ) (M : ℕ) (ε : ℝ) :
    ⌈sigMeshLB q M ε⌉₊ ≤ 2 ^ sigM q M ε ∧ 2 ^ sigM q M ε ≤ 2 * ⌈sigMeshLB q M ε⌉₊ + 1 := by
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_⟩
  by_cases h1 : 1 < ⌈sigMeshLB q M ε⌉₊
  · have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h1
    have hpos : 0 < sigM q M ε := Nat.clog_pos (by norm_num) h1
    unfold sigM at hpos ⊢
    have : 2 ^ Nat.clog 2 ⌈sigMeshLB q M ε⌉₊ = 2 * 2 ^ (Nat.clog 2 ⌈sigMeshLB q M ε⌉₊).pred := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
      rw [pow_succ]; ring
    omega
  · have h0 : Nat.clog 2 ⌈sigMeshLB q M ε⌉₊ = 0 := Nat.clog_of_right_le_one (by omega) 2
    unfold sigM
    rw [h0]
    omega

/-- The clock length is at least `qM`: its initial degree is `⌈12 qM⌉`. -/
theorem qM_le_sigN {q : ℝ} (hq : 1 ≤ q) {M : ℕ} (hM : 1 ≤ M) : q * M ≤ sigN q M := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have ha : 1 ≤ q * M := by nlinarith
  have hd : 12 * (q * M) ≤ (OptimalPrecision.Gamma.d0 (q * M) : ℝ) := Nat.le_ceil _
  have hd1 : 1 ≤ OptimalPrecision.Gamma.d0 (q * M) := by
    have : (1 : ℝ) ≤ OptimalPrecision.Gamma.d0 (q * M) := by linarith
    exact_mod_cast this
  have hge : OptimalPrecision.Gamma.d0 (q * M) ≤ sigN q M := by
    unfold sigN clockLength OptimalPrecision.Gamma.Dstar
    omega
  have : (OptimalPrecision.Gamma.d0 (q * M) : ℝ) ≤ sigN q M := by exact_mod_cast hge
  linarith

theorem one_le_sigN (q : ℝ) (M : ℕ) : 1 ≤ sigN q M := by
  unfold sigN clockLength; omega

/-! ### The circuits -/

/-- The released LCU circuit with the padded clock table. -/
def sigBase (a : ℕ) (q : ℝ) (M : ℕ) (ε : ℝ) : List (Instr (SigWire a q M ε)) :=
  lcuI (sigL q M) (padLen (sigLen q M)) (padWt s0⁻¹ (sigWt q M))
    (CayleyTransfer.c (sigStep q M ε)) (CayleyTransfer.sigma (sigStep q M ε)) (sigN q M)

/-- Eight rounds of amplification. -/
def sigAmp (a : ℕ) (q : ℝ) (M : ℕ) (ε : ℝ) : List (Instr (SigWire a q M ε)) :=
  ampIt (sigBase a q M ε) 8

/-- **The signed-factor gate circuit**: the amplified circuit with every oracle call expanded
into calls of the factor `U_B` and the boundary `U_J`, phase gates and attenuation rotations. -/
def sigCircuit (a : ℕ) (f z : Fin a) (q : ℝ) (M : ℕ) (ε κ : ℝ) :
    List (Instr (SigWire a q M ε)) :=
  (sigAmp a q M ε).flatMap (expandI f z q κ)

/-! ### Validity and counts -/

theorem sigStep_nonneg {q : ℝ} (hq : 1 ≤ q) (M : ℕ) (ε : ℝ) : 0 ≤ sigStep q M ε :=
  div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

theorem sig_unit {q : ℝ} (hq : 1 ≤ q) (M : ℕ) (ε : ℝ) :
    CayleyTransfer.c (sigStep q M ε) ^ 2 + CayleyTransfer.sigma (sigStep q M ε) ^ 2 = 1 := by
  obtain ⟨-, hσ, -⟩ := SignedFactorSimulation.cayley_scalars (sigStep_nonneg hq M ε)
  linarith

theorem sigAmp_valid (a : ℕ) {q : ℝ} (hq : 1 ≤ q) (M : ℕ) (ε : ℝ) :
    ∀ i ∈ sigAmp a q M ε, i.Valid Wire.anc :=
  ampIt_valid _ (lcuI_valid _ _ _ _ _ (sig_unit hq M ε) _) 8

theorem sigAmp_secOK (a : ℕ) (q : ℝ) (M : ℕ) (ε : ℝ) :
    ∀ i ∈ sigAmp a q M ε, GateNative.SecOK (GateNative.wireRel (a + 1) _ _ _) i :=
  secOK_ampIt _ (GateNative.secOK_lcuI _ _ _ _ _ _) 8

theorem sig_valid (a : ℕ) {f z : Fin a} (hfz : f ≠ z) {q : ℝ} (hq : 1 ≤ q) (M : ℕ) (ε : ℝ)
    {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ ≤ 1) :
    ∀ i ∈ sigCircuit a f z q M ε κ, i.Valid Wire.anc :=
  expand_valid hfz q h0 h1 _ (sigAmp_valid a hq M ε)

theorem sigBase_counts (a : ℕ) (q : ℝ) (M : ℕ) (ε : ℝ) :
    nPriv (sigBase a q M ε) = sigN q M ∧ nUJ (sigBase a q M ε) = 2 * sigN q M ∧
      nGates (sigBase a q M ε) ≤ 2 * (2 ^ sigR q M * (2 * sigR q M + 1)) +
        2 * ((sigN q M + 2) * (8 * sigR q M + 2)) +
        sigN q M * (4 * (a + 1) + 8 * sigM q M ε + 7 * sigR q M + 5) := by
  have hN : sigN q M ≤ cap (sigR q M) + 1 := by
    have := cap_succ (sigR q M)
    have := sigL q M
    omega
  exact lcuI_counts (a := a + 1) (m := sigM q M ε) (K := sigK a q M ε) (sigL q M) _ _ _ _ _ hN

/-- **The counts of the signed-factor circuit**: exactly `2·3⁸ n` factor calls (`U_B` and
`U_B†`), exactly `2·3⁸ n` boundary calls (`U_J` and `U_J†`), and the elementary gates. -/
theorem sig_counts (a : ℕ) (f z : Fin a) (q : ℝ) (M : ℕ) (ε κ : ℝ) :
    nPriv (sigCircuit a f z q M ε κ) = 2 * 3 ^ 8 * sigN q M ∧
      nUJ (sigCircuit a f z q M ε κ) = 2 * 3 ^ 8 * sigN q M ∧
      nGates (sigCircuit a f z q M ε κ) ≤
        3 ^ 8 * (2 * (2 ^ sigR q M * (2 * sigR q M + 1)) +
          2 * ((sigN q M + 2) * (8 * sigR q M + 2)) +
          sigN q M * (4 * (a + 1) + 8 * sigM q M ε + 7 * sigR q M + 5) +
          2 * ((a + 1) + sigM q M ε + 2 * sigR q M) + 3 + 5 * sigN q M) := by
  obtain ⟨b1, b2, b3⟩ := sigBase_counts a q M ε
  obtain ⟨a1, a2, -⟩ := ampIt_counts (sigBase a q M ε) 8
  have a3 := ampIt_nGates_le (sigBase a q M ε) 8
  obtain ⟨e1, e2, e3⟩ := expand_counts f z q κ (sigAmp a q M ε)
  unfold sigCircuit
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; unfold sigAmp; rw [a1, b1]; ring
  · rw [e2]; unfold sigAmp; rw [a2, b2]; ring
  · rw [e3]
    unfold sigAmp
    rw [a1, a2, b1, b2]
    have : nGates (ampIt (sigBase a q M ε) 8) ≤ 3 ^ 8 * (2 * (2 ^ sigR q M * (2 * sigR q M + 1)) +
        2 * ((sigN q M + 2) * (8 * sigR q M + 2)) +
        sigN q M * (4 * (a + 1) + 8 * sigM q M ε + 7 * sigR q M + 5) +
        2 * ((a + 1) + sigM q M ε + 2 * sigR q M) + 3) := by
      refine a3.trans (Nat.mul_le_mul_left _ ?_)
      omega
    nlinarith

/-! ### The block -/

omit [CompleteSpace P] in
theorem sum_padded (q : ℝ) (M : ℕ) (F : ℕ → P →L[ℂ] P) :
    ∑ j : Fin (sigN q M), (sigWt q M j : ℂ) • F (sigLen q M j) =
      ∑ j ∈ Icc 1 (sigN q M), (clockWeight q M j : ℂ) • F j :=
  SignedFactorSimulation.sum_fin_succ_eq_Icc (fun j => (clockWeight q M j : ℂ) • F j) _

/-- **The block of the signed LCU**: `s₀ ∑_j λ_j Ces_j(F_J)` with the cascade transfer of the
chronological product of `J = 2^m` slots and the private operation `D`. -/
theorem sig_block (a : ℕ) {q : ℝ} (hq : 1 ≤ q) {M : ℕ} (hM : 1 ≤ M) (ε : ℝ)
    (UJ D : Anc (a + 1) P →L[ℂ] Anc (a + 1) P) (hUJ : UJ ∘L UJ† = 1) :
    (io (a := a + 1) (m := sigM q M ε) (r := sigR q M) (K := sigK a q M ε) (P := P))† ∘L
        (LCU (K := sigK a q M ε) (m := sigM q M ε) (sigL q M) (padLen (sigLen q M))
          (padWt s0⁻¹ (sigWt q M)) (CayleyTransfer.c (sigStep q M ε))
          (CayleyTransfer.sigma (sigStep q M ε)) UJ D (sigN q M) ∘L io) =
      (s0 : ℂ) • ∑ j ∈ Icc 1 (sigN q M), (clockWeight q M j : ℂ) •
        ces (SignedFactorSimulation.cascTransfer D (UJ ∘L iota0) (sigStep q M ε)
          (2 ^ sigM q M ε)) j := by
  obtain ⟨hr1, hr0, -⟩ := sigR_spec q M
  have hA : 0 < s0⁻¹ := inv_pos.mpr s0_pos
  have hw : ∑ j, |sigWt q M j| ≤ s0⁻¹ := by
    have h1 := OptimalPrecision.sum_abs_clockWeight_le hq hM
    have h2 : ∑ j : Fin (sigN q M), |sigWt q M j| =
        ∑ j ∈ Icc 1 (sigN q M), |clockWeight q M j| :=
      SignedFactorSimulation.sum_fin_succ_eq_Icc (fun j => |clockWeight q M j|) _
    have h3 := SignedFactorSimulation.ampS_mul_le
    have h4 : (3000 : ℝ) ≤ s0⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) s0_pos, inv_eq_one_div, le_div_iff₀ (by norm_num)]
      exact h3
    rw [h2]
    linarith
  have hN : sigN q M ≤ cap (sigR q M) := by
    have := cap_succ (sigR q M)
    omega
  rw [lcu_ces_pad (sigL q M) hA (sigWt q M) hw (sigLen q M) (sigN q M)
    (fun j => ⟨Nat.succ_pos _, Nat.succ_le_of_lt j.isLt⟩) (one_le_sigN q M) hN hr0 _ _
    (sig_unit hq M ε) UJ D hUJ]
  rw [inv_inv, netTransfer_cascade (sigStep_nonneg hq M ε), sum_padded]

/-! ### The mesh -/

theorem sigEta_pos {ε : ℝ} (hε : 0 < ε) : 0 < sigEta ε := by unfold sigEta; positivity

theorem sig_mesh {q : ℝ} (hq : 1 ≤ q) {M : ℕ} (hM : 1 ≤ M) {ε : ℝ} (hε : 0 < ε) :
    8 * (q * M) * sigN q M ≤ ((2 ^ sigM q M ε : ℕ) : ℝ) ∧
      128 * 3000 * (q * M) ^ 3 * (sigN q M : ℝ) ^ 4 / ((2 ^ sigM q M ε : ℕ) : ℝ) ^ 2 ≤
        sigEta ε / 2 := by
  have hη := sigEta_pos hε
  have hLB : sigMeshLB q M ε ≤ ((2 ^ sigM q M ε : ℕ) : ℝ) := by
    have h1 := (sigM_spec q M ε).1
    have h2 : sigMeshLB q M ε ≤ (⌈sigMeshLB q M ε⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : ((⌈sigMeshLB q M ε⌉₊ : ℕ) : ℝ) ≤ ((2 ^ sigM q M ε : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have ha : 0 ≤ q * M := by positivity
  refine ⟨(le_max_left _ _).trans hLB, ?_⟩
  set J : ℝ := ((2 ^ sigM q M ε : ℕ) : ℝ) with hJ
  have hJ0 : 0 < J := by rw [hJ]; positivity
  have hsq : Real.sqrt (768000 * (q * M) ^ 3 * (sigN q M : ℝ) ^ 4 / sigEta ε) ≤ J :=
    (le_max_right _ _).trans hLB
  have hB : 0 ≤ 768000 * (q * M) ^ 3 * (sigN q M : ℝ) ^ 4 / sigEta ε := by positivity
  have hsq2 : 768000 * (q * M) ^ 3 * (sigN q M : ℝ) ^ 4 / sigEta ε ≤ J ^ 2 := by
    calc 768000 * (q * M) ^ 3 * (sigN q M : ℝ) ^ 4 / sigEta ε =
        Real.sqrt (768000 * (q * M) ^ 3 * (sigN q M : ℝ) ^ 4 / sigEta ε) ^ 2 :=
          (Real.sq_sqrt hB).symm
      _ ≤ J ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2
  rw [div_le_iff₀ hη] at hsq2
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-! ### The error -/

/-- **The signed-factor gate circuit for `q ≥ 1`.** For the attenuated factor interface on
`a + 1` ancillas with `D' ⪯ δ I`, `M ≥ 2·27² q²Mδ` and the factorial tail of Lemma `opt:lem:tail`
at most `ε²/(4·7⁸)`, the gate circuit, run with `U_J` and `U_B` on the last `a` ancillas, has
full-output error at most `ε` for `e^{-i q²M C'}`. -/
theorem sig_core [FiniteDimensional ℂ P] {a : ℕ} (UJ U : Anc a P →L[ℂ] Anc a P)
    (hUJ : IsUnitary UJ) (hU : IsUnitary U) {f z : Fin a} (hfz : f ≠ z) {κ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) {q : ℝ} (hq : 1 ≤ q) {M : ℕ} (hM : 1 ≤ M) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hD : (attKnown UJ hUJ f z hκ0 hκ1).Dop (liftA U) ≤ (δ : ℂ) • (1 : P →L[ℂ] P))
    (hMb : 2 * 27 ^ 2 * (q ^ 2 * M * δ) ≤ M) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (htail : 2 * (3000 + 1) * (Real.exp 2 * 27 ^ 2 * (q ^ 2 * M * δ) / M) ^ M ≤
      ε ^ 2 / (4 * 7 ^ 8)) :
    ‖run (simSem (liftA UJ) (liftA U)) (sigCircuit a f z q M ε κ) ∘L io -
      io ∘L NormedSpace.exp ((-(I * ((q ^ 2 * M : ℝ) : ℂ))) •
        (attKnown UJ hUJ f z hκ0 hκ1).Cop (liftA U))‖ ≤ ε := by
  set Kn := attKnown UJ hUJ f z hκ0 hκ1 with hKn
  have hU'u : IsUnitary (liftA U) := liftA_isUnitary hU
  set D' := Kn.priv q (liftA U) with hD'
  have hD'u : IsUnitary D' := Kn.priv_isUnitary q hU'u
  set UJ' := attUJ UJ κ with hUJ'
  have hUJ'u : IsUnitary UJ' := attUJ_isUnitary hUJ hκ0 hκ1
  set n := sigN q M with hn_def
  have hn1 : 1 ≤ n := one_le_sigN q M
  have hnle : (n : ℝ) ≤ 27 * (q * M) := OptimalPrecision.clockLength_le hq hM
  have hlam : ∑ j ∈ Icc 1 n, |clockWeight q M j| ≤ 3000 :=
    OptimalPrecision.sum_abs_clockWeight_le hq hM
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have ha : 0 < q * M := by positivity
  set η := sigEta ε with hη_def
  have hη : 0 < η := sigEta_pos hε
  have hs0 : 0 ≤ s0 := s0_pos.le
  have hs1 : s0 ≤ 1 := by have := SignedFactorSimulation.ampS_mul_le; linarith
  have hsη : s0 * η ≤ η := mul_le_of_le_one_left hη.le hs1
  have hη8 : 7 ^ 8 * η = ε ^ 2 / 2 := by rw [hη_def, sigEta]; ring
  have hε2 : ε ^ 2 ≤ 1 / 4 := by
    have := pow_le_pow_left₀ hε.le hε1 2
    norm_num at this
    linarith
  have he : 7 ^ 8 * (s0 * η) ≤ 7 / 16 := by
    have := mul_le_mul_of_nonneg_left hsη (by norm_num : (0 : ℝ) ≤ 7 ^ 8)
    linarith
  have hfin : Real.sqrt (2 * (7 ^ 8 * (s0 * η))) ≤ ε := by
    rw [Real.sqrt_le_left hε.le]
    have := mul_le_mul_of_nonneg_left hsη (by norm_num : (0 : ℝ) ≤ 7 ^ 8)
    linarith
  have htailη : 2 * (3000 + 1) * (Real.exp 2 * 27 ^ 2 * (q ^ 2 * M * δ) / M) ^ M ≤ η / 2 :=
    htail.trans (le_of_eq (by rw [hη_def, sigEta]; ring))
  obtain ⟨hm8, hmesh⟩ := sig_mesh hq hM hε
  -- the ideal LCU and its block
  set X := LCU (K := sigK a q M ε) (m := sigM q M ε) (sigL q M) (padLen (sigLen q M))
    (padWt s0⁻¹ (sigWt q M)) (CayleyTransfer.c (sigStep q M ε))
    (CayleyTransfer.sigma (sigStep q M ε)) UJ' D' (sigN q M) with hX
  have hXu : IsUnitary X := LCU_isUnitary _ _ _ _ _ (sig_unit hq M ε) UJ' D' hUJ'u hD'u _
  set W := NormedSpace.exp ((-(I * ((q ^ 2 * M : ℝ) : ℂ))) • Kn.Cop (liftA U)) with hW
  have hWu : IsUnitary W := Kn.evolution_unitary (liftA U) (q ^ 2 * M)
  have hblock : ‖(io (a := a + 1) (m := sigM q M ε) (r := sigR q M) (K := sigK a q M ε)
      (P := P))† ∘L (X ∘L io) - (SignedFactorSimulation.ampS 8 0 : ℂ) • W‖ ≤ s0 * η := by
    have hb := sig_block (P := P) a hq hM ε UJ' D' (unitary_comp_adj hUJ'u)
    rw [hb]
    have hE : UJ' ∘L iota0 = Kn.E := rfl
    rw [hE]
    have hmeshx := Kn.finite_mesh (q := q) (by linarith) hU'u ha.le hn1
      (by positivity : 0 < 2 ^ sigM q M ε) hm8 hlam
    have htailx := OptimalPrecision.Tail.tail_estimate hq hM hnle hlam
      (fun k j hjk hkM => OptimalPrecision.clock_moments hq hM hjk hkM) hδ
      (Kn.Dop_nonneg (liftA U)) hD (Kn.neg_Dop_le_Cop (liftA U)) (Kn.Cop_le_Dop (liftA U)) hMb
    have hX' : ‖∑ j ∈ Icc 1 n, (clockWeight q M j : ℂ) •
        ces (SignedFactorSimulation.cascTransfer D' Kn.E (sigStep q M ε) (2 ^ sigM q M ε)) j -
        W‖ ≤ η := by
      have h1 := norm_sub_le_norm_sub_add_norm_sub
        (∑ j ∈ Icc 1 n, (clockWeight q M j : ℂ) •
          ces (SignedFactorSimulation.cascTransfer D' Kn.E (sigStep q M ε) (2 ^ sigM q M ε)) j)
        (∑ j ∈ Icc 1 n, (clockWeight q M j : ℂ) •
          ces (OptimalPrecision.Tail.Fop (q * M) q (Kn.Cop (liftA U)) (Kn.Dop (liftA U))) j)
        W
      have h2 := hmeshx.trans hmesh
      have h3 := htailx.trans htailη
      have e : sigStep q M ε = q * M / ((2 ^ sigM q M ε : ℕ) : ℝ) := rfl
      rw [e] at h1 ⊢
      linarith
    rw [← smul_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    exact mul_le_mul_of_nonneg_left hX' hs0
  have herr := ampOp_error (P := P) hXu hWu 8 hblock he
  -- the gate circuit
  have hexp : run (simSem (liftA UJ) (liftA U)) (sigCircuit a f z q M ε κ) =
      run (simSem UJ' D') (ampIt (sigBase a q M ε) 8) := by
    unfold sigCircuit
    rw [run_expand UJ U hU hfz q κ _ (sigAmp_secOK a q M ε)]
    rw [hD', attKnown_priv]
    rfl
  have hn : ∀ ℓ, padLen (sigLen q M) ℓ < 2 ^ sigR q M := by
    intro ℓ
    have h := (padLen_spec (sigLen q M) (N := sigN q M)
      (fun j => ⟨Nat.succ_pos _, Nat.succ_le_of_lt j.isLt⟩) (one_le_sigN q M) ℓ).2
    have := sigL q M
    omega
  have hagL := lcu_agrees (P := P) (a := a + 1) (m := sigM q M ε) (K := sigK a q M ε) UJ' D'
    (sigL q M) (padLen (sigLen q M)) (padWt s0⁻¹ (sigWt q M)) (CayleyTransfer.c (sigStep q M ε))
    (CayleyTransfer.sigma (sigStep q M ε)) (sigN q M) hn le_rfl
  have hag := ampIt_agrees UJ' D' hUJ'u hD'u (sigBase a q M ε)
    (lcuI_valid _ _ _ _ _ (sig_unit hq M ε) _) hXu
    (pres2_LCU (K := sigK a q M ε) (m := sigM q M ε) (P := P) _ _ _ _ _ UJ' D' _) hagL le_rfl 8
  have hio : run (simSem UJ' D') (ampIt (sigBase a q M ε) 8) ∘L io = ampOp X 8 ∘L io := by
    refine ContinuousLinearMap.ext (fun ψ => ?_)
    rw [comp_apply, comp_apply, io_apply]
    exact hag _ (supp_bas _ (fun w _ => rfl) ψ)
  rw [hexp, hio]
  exact herr.trans hfin

end

end GateOptimalPrecision
