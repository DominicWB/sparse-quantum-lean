import GateOptimalPrecision.ClippedCore
import GateOptimalPrecision.SignedTheorem

/-!
# Proposition `gate:prop:core`: the clipped-transducer gate bound

Section `gate:sec:core` at the gate level. The circuit is the released one-round amplified LCU of
the baseline gate theorem (`Sim.ampI`) with

* the branch table of the signed smoothing of the product filter `f = g_{B₀}^m g_p^k` of the
  large-sparsity core (`LargeSparsityCore.Core.coeff`, degree `d = degree s τ ε`): the released
  finite index `ReuseWeights.Index d` of `2(d+1)` branches with absolute weight two
  (`clipWt`, `clipLen`, `clipWt_mass`);
* `N = 2d` reuse steps, a label register with `2^r ≥ 2d + 2` (`clipR`);
* a mesh of `2^m ≥ N_s` slots (`clipM`, `N_s = steps s τ ε` the slot count of the query proof) with
  the Cayley scalars of the step `a/2^m` (`coreStep`).

**Proposition `gate:prop:core`** (`clipped_gate_simulation`). Let `U_J` and the private operation
`D` be unitaries on `a` ancilla qubits and the system (finite-dimensional), and let the core
hypotheses `LargeSparsityCore.Core.CoreData s τ ε K D P₊ P₋ J` hold for `J = U_J ι₀` in the regime
`Parameters.Regime s τ ε`. Then the circuit `clipCircuit a s τ ε` is valid, uses exactly `6d`
private calls and exactly `12d` calls of `U_J` or `U_J†`, at most `200(d+1)(a+m+r+1)` elementary
gates on `2a + 3m + 6r + 3` wires, and its full output is within `ε` of `e^{-i a J†KJ}`, `a = sτ/q`;
`N_s ≤ 2^m < 2 N_s` and `2d + 2 ≤ 2^r ≤ 4(d + 1)`. `clipped_gate_simulation_neg` is the statement
for the negative time (the literal inverse circuit).

The private calls are `6d` ("uses at most `6d` private calls"); `d ≤ 21520 √(sτr)` is the
degree bound of the query proof (`Parameters.Regime.degree_le_sqrt`, `opt:eq:core-degree`).
-/

set_option autoImplicit false

namespace GateOptimalPrecision

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim
open LargeSparsityCore LargeSparsityCore.Parameters
open GlobalResolvent ChronologicalResolvent GlobalColligation CoherentReuse
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Public parameters -/

/-- The branch weights of the product-filter smoothing, numbered. -/
def clipWt (s τ ε : ℝ) : Fin ((degree s τ ε + 1) + (degree s τ ε + 1)) → ℝ :=
  fun ℓ => ReuseWeights.weight (Core.coeff s τ ε) (degree s τ ε) ((labEquiv (degree s τ ε)).symm ℓ)

/-- The branch reuse lengths, numbered. -/
def clipLen (s τ ε : ℝ) : Fin ((degree s τ ε + 1) + (degree s τ ε + 1)) → ℕ :=
  fun ℓ => ReuseWeights.length (degree s τ ε) ((labEquiv (degree s τ ε)).symm ℓ)

/-- The slot exponent: `2^m ≥ N_s`. -/
def clipM (s τ ε : ℝ) : ℕ := Nat.clog 2 (steps s τ ε)

/-- The pointer and label width: `2^r ≥ 2d + 2`. -/
def clipR (s τ ε : ℝ) : ℕ := Nat.clog 2 (2 * degree s τ ε + 2)

/-- The AND-chain pool. -/
def clipK (a : ℕ) (s τ ε : ℝ) : ℕ := a + clipM s τ ε + 2 * clipR s τ ε

/-- The wires of the clipped-transducer circuit. -/
abbrev ClipWire (a : ℕ) (s τ ε : ℝ) := Wire a (clipM s τ ε) (clipR s τ ε) (clipK a s τ ε)

theorem clipM_spec (s τ ε : ℝ) :
    steps s τ ε ≤ 2 ^ clipM s τ ε ∧ 2 ^ clipM s τ ε < 2 * steps s τ ε := by
  have hS := steps_pos s τ ε
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_⟩
  by_cases h1 : 1 < steps s τ ε
  · have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h1
    have hpos : 0 < clipM s τ ε := Nat.clog_pos (by norm_num) h1
    unfold clipM at hpos ⊢
    have : 2 ^ Nat.clog 2 (steps s τ ε) = 2 * 2 ^ (Nat.clog 2 (steps s τ ε)).pred := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
      rw [pow_succ]; ring
    omega
  · have h1' : steps s τ ε = 1 := by omega
    unfold clipM
    rw [h1']
    simp

theorem clipR_spec (s τ ε : ℝ) :
    2 * degree s τ ε + 2 ≤ 2 ^ clipR s τ ε ∧ 0 < clipR s τ ε ∧
      2 ^ clipR s τ ε ≤ 4 * (degree s τ ε + 1) := by
  have h1 : 1 < 2 * degree s τ ε + 2 := by omega
  refine ⟨Nat.le_pow_clog (by norm_num) _, Nat.clog_pos (by norm_num) h1, ?_⟩
  have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h1
  have hpos : 0 < clipR s τ ε := Nat.clog_pos (by norm_num) h1
  unfold clipR at hpos ⊢
  have : 2 ^ Nat.clog 2 (2 * degree s τ ε + 2) =
      2 * 2 ^ (Nat.clog 2 (2 * degree s τ ε + 2)).pred := by
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
    rw [pow_succ]; ring
  omega

theorem clipL (s τ ε : ℝ) :
    (degree s τ ε + 1) + (degree s τ ε + 1) ≤ 2 ^ clipR s τ ε := by
  have := (clipR_spec s τ ε).1
  omega

/-- The Cayley step of the dyadic mesh. -/
abbrev clipStep (s τ ε : ℝ) : ℝ := coreStep s τ ε (2 ^ clipM s τ ε)

/-- **The clipped-transducer gate circuit**, fixed by the public data `a, s, τ, ε`. -/
def clipCircuit (a : ℕ) (s τ ε : ℝ) : List (Instr (ClipWire a s τ ε)) :=
  ampI (clipL s τ ε) (clipLen s τ ε) (clipWt s τ ε) (CayleyTransfer.c (clipStep s τ ε))
    (CayleyTransfer.sigma (clipStep s τ ε)) (2 * degree s τ ε)

/-! ### The table -/

theorem clipWt_mass {s τ ε : ℝ} (R : Regime s τ ε) : ∑ ℓ, |clipWt s τ ε ℓ| = 2 := by
  rw [← Core.mass R]
  exact Fintype.sum_equiv (labEquiv (degree s τ ε)).symm _ _ (fun ℓ => rfl)

theorem clipLen_spec {s τ ε : ℝ} (R : Regime s τ ε) (ℓ) :
    0 < clipLen s τ ε ℓ ∧ clipLen s τ ε ℓ ≤ 2 * degree s τ ε :=
  ⟨ReuseWeights.length_pos _ R.degree_pos _, ReuseWeights.length_le _ R.degree_pos _⟩

/-! ### Proposition `gate:prop:core` -/

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- **Proposition `gate:prop:core` (clipped-transducer gate bound), exact gates.** See the module
docstring. -/
theorem clipped_gate_simulation [FiniteDimensional ℂ P] (a : ℕ) {s τ ε : ℝ} (R : Regime s τ ε)
    (UJ D : Anc a P →L[ℂ] Anc a P) (hUJ : IsUnitary UJ) (hDu : IsUnitary D)
    {Kb Pp Pm : Anc a P →L[ℂ] Anc a P}
    (h : Core.CoreData s τ ε Kb D Pp Pm (UJ ∘L iota0)) :
    (∀ g ∈ clipCircuit a s τ ε, g.Valid Wire.anc) ∧
    nPriv (clipCircuit a s τ ε) = 6 * degree s τ ε ∧
    nUJ (clipCircuit a s τ ε) = 12 * degree s τ ε ∧
    nGates (clipCircuit a s τ ε) ≤
      200 * (degree s τ ε + 1) * (a + clipM s τ ε + clipR s τ ε + 1) ∧
    Fintype.card (ClipWire a s τ ε) = 2 * a + 3 * clipM s τ ε + 6 * clipR s τ ε + 3 ∧
    ‖run (simSem UJ D) (clipCircuit a s τ ε) ∘L io -
        io ∘L NormedSpace.exp ((-Complex.I * (aval s τ ε : ℂ)) •
          ((UJ ∘L iota0)† ∘L Kb ∘L (UJ ∘L iota0)))‖ ≤ ε ∧
    steps s τ ε ≤ 2 ^ clipM s τ ε ∧ 2 ^ clipM s τ ε < 2 * steps s τ ε ∧
    2 * degree s τ ε + 2 ≤ 2 ^ clipR s τ ε ∧ 2 ^ clipR s τ ε ≤ 4 * (degree s τ ε + 1) := by
  obtain ⟨hm1, hm2⟩ := clipM_spec s τ ε
  obtain ⟨hr1, hr0, hr2⟩ := clipR_spec s τ ε
  obtain ⟨hw0, hww, -, -⟩ := coreStep_spec R hm1
  have hwq : clipStep s τ ε ≤ 1 / 4 := hww.trans (w_le_quarter s τ ε)
  obtain ⟨_, _, hκc, hσc, _⟩ := CayleyTransfer.scalar_promises (clipStep s τ ε) hw0 hwq
  have hunit : CayleyTransfer.c (clipStep s τ ε) ^ 2 + CayleyTransfer.sigma (clipStep s τ ε) ^ 2 =
      1 := by linarith
  have hN : 2 * degree s τ ε ≤ cap (clipR s τ ε) + 1 := by
    have := cap_succ (clipR s τ ε); omega
  obtain ⟨hc1, hc2, hc3⟩ := ampI_counts (a := a) (m := clipM s τ ε) (K := clipK a s τ ε)
    (clipL s τ ε) (clipLen s τ ε) (clipWt s τ ε) (CayleyTransfer.c (clipStep s τ ε))
    (CayleyTransfer.sigma (clipStep s τ ε)) (2 * degree s τ ε) hN
  have hn : ∀ ℓ, clipLen s τ ε ℓ < 2 ^ clipR s τ ε := by
    intro ℓ
    have := (clipLen_spec R ℓ).2
    omega
  have hK : a + clipM s τ ε + 2 * clipR s τ ε ≤ clipK a s τ ε := le_rfl
  have hagree := amp_agrees (P := P) (a := a) (m := clipM s τ ε) (K := clipK a s τ ε) UJ D hUJ hDu
    (clipL s τ ε) (clipLen s τ ε) (clipWt s τ ε) (CayleyTransfer.c (clipStep s τ ε))
    (CayleyTransfer.sigma (clipStep s τ ε)) hunit (2 * degree s τ ε) hn hK
  have hgb := gate_bound a (clipM s τ ε) (clipR s τ ε) (degree s τ ε) (2 ^ clipR s τ ε) hr2
  refine ⟨ampI_valid _ _ _ _ _ hunit _, ?_, ?_, ?_, ?_, ?_, hm1, hm2, hr1, hr2⟩
  · unfold clipCircuit; rw [hc1]; ring
  · unfold clipCircuit; rw [hc2]; ring
  · unfold clipCircuit
    refine hc3.trans (le_of_eq_of_le ?_ hgb)
    ring
  · rw [card_wire, clipK]; ring
  -- the error
  have hD : D† ∘L D = 1 := unitary_adj_comp hDu
  have hUJc : UJ ∘L UJ† = 1 := unitary_comp_adj hUJ
  have hJ : (UJ ∘L iota0)† ∘L (UJ ∘L iota0) = 1 :=
    isometry_comp UJ iota0 (unitary_adj_comp hUJ) iota0_isometry
  obtain ⟨_hIso, hCore⟩ := core_implementation_mesh R h hm1
  set E := NormedSpace.exp ((-Complex.I * (aval s τ ε : ℂ)) •
    ((UJ ∘L iota0)† ∘L Kb ∘L (UJ ∘L iota0))) with hE
  have hEu : E† ∘L E = 1 := by
    have hSelf : star ((UJ ∘L iota0)† ∘L Kb ∘L (UJ ∘L iota0)) =
        (UJ ∘L iota0)† ∘L Kb ∘L (UJ ∘L iota0) := by
      rw [ContinuousLinearMap.star_eq_adjoint, adjoint_comp, adjoint_comp, adjoint_adjoint,
        h.spectral.self.adjoint_eq, comp_assoc]
    exact (LabeledAdjointSimulation.evolution_unitary _ hSelf (aval s τ ε)).1
  have hLCUu := LCU_isUnitary (K := clipK a s τ ε) (m := clipM s τ ε) (clipL s τ ε)
    (clipLen s τ ε) (clipWt s τ ε) (CayleyTransfer.c (clipStep s τ ε))
    (CayleyTransfer.sigma (clipStep s τ ε)) hunit UJ D hUJ hDu (2 * degree s τ ε)
  have hT' := isometry_comp (E := P) (F := Reg (ClipWire a s τ ε) P) (G := Reg (ClipWire a s τ ε) P)
    _ (io (a := a) (m := clipM s τ ε) (r := clipR s τ ε) (K := clipK a s τ ε) (P := P))
    (unitary_adj_comp hLCUu) io_isometry
  have hB := lcu_compression (K := clipK a s τ ε) (m := clipM s τ ε) (clipL s τ ε) (clipLen s τ ε)
    (2 * degree s τ ε) (clipLen_spec R) (by have := cap_succ (clipR s τ ε); omega) hr0
    (clipWt s τ ε) (clipWt_mass R) (CayleyTransfer.c (clipStep s τ ε))
    (CayleyTransfer.kappa (clipStep s τ ε)) (CayleyTransfer.sigma (clipStep s τ ε)) hunit hκc
    UJ D hUJc
  rw [blkB_net, blkC_net, blkG_net _ _ _ UJ D hUJc] at hB
  have hB' : (io (a := a) (m := clipM s τ ε) (r := clipR s τ ε) (K := clipK a s τ ε) (P := P))† ∘L
      (LCU (K := clipK a s τ ε) (m := clipM s τ ε) (clipL s τ ε) (clipLen s τ ε) (clipWt s τ ε)
        (CayleyTransfer.c (clipStep s τ ε)) (CayleyTransfer.sigma (clipStep s τ ε)) UJ D
        (2 * degree s τ ε) ∘L io) =
      (SmoothingLCU.output (P := P) (V := HV a (clipM s τ ε) P) (Core.coeff s τ ε)
        (degree s τ ε))† ∘L
        Smoothing.prepared (Core.coeff s τ ε) (degree s τ ε)
          (blkA (CayleyTransfer.c (clipStep s τ ε)) (2 ^ clipM s τ ε))
          (blkB (CayleyTransfer.c (clipStep s τ ε)) (CayleyTransfer.sigma (clipStep s τ ε))
            (UJ ∘L iota0) D (2 ^ clipM s τ ε))
          (blkC (CayleyTransfer.c (clipStep s τ ε)) (CayleyTransfer.sigma (clipStep s τ ε))
            (UJ ∘L iota0) (2 ^ clipM s τ ε))
          (blkG (CayleyTransfer.c (clipStep s τ ε)) (CayleyTransfer.kappa (clipStep s τ ε))
            (CayleyTransfer.sigma (clipStep s τ ε)) (UJ ∘L iota0) D (2 ^ clipM s τ ε)) := by
    rw [hB]
    change _ = SmoothingLCU.successfulBlock (Core.coeff s τ ε) (degree s τ ε) _ _ _ _
    rw [smoothing_block_eq]
    exact reindex_block (degree s τ ε) _ _ (fun n => successfulBlock _ _ _ _ n)
  have hJrel := SmoothingLCU.output_isometry (P := P) (V := HV a (clipM s τ ε) P)
    (Core.coeff s τ ε) (degree s τ ε) R.degree_pos (Core.mass R)
  have hTrel := Smoothing.prepared_isometry (Core.coeff s τ ε) (degree s τ ε) R.degree_pos
    (Core.mass R) _ _ _ _
    (released_step D (UJ ∘L iota0) (clipStep s τ ε) hw0 hwq hD hJ (2 ^ clipM s τ ε))
  have hAmp := GateBlockTransfer.amplified_error_le (P := P)
    (K := PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := HV a (clipM s τ ε) P) (degree s τ ε)))
    (K' := Reg (ClipWire a s τ ε) P)
    (SmoothingLCU.output (P := P) (V := HV a (clipM s τ ε) P) (Core.coeff s τ ε) (degree s τ ε))
    (Smoothing.prepared (Core.coeff s τ ε) (degree s τ ε)
      (blkA (CayleyTransfer.c (clipStep s τ ε)) (2 ^ clipM s τ ε))
      (blkB (CayleyTransfer.c (clipStep s τ ε)) (CayleyTransfer.sigma (clipStep s τ ε))
        (UJ ∘L iota0) D (2 ^ clipM s τ ε))
      (blkC (CayleyTransfer.c (clipStep s τ ε)) (CayleyTransfer.sigma (clipStep s τ ε))
        (UJ ∘L iota0) (2 ^ clipM s τ ε))
      (blkG (CayleyTransfer.c (clipStep s τ ε)) (CayleyTransfer.kappa (clipStep s τ ε))
        (CayleyTransfer.sigma (clipStep s τ ε)) (UJ ∘L iota0) D (2 ^ clipM s τ ε)))
    (io (a := a) (m := clipM s τ ε) (r := clipR s τ ε) (K := clipK a s τ ε) (P := P))
    (LCU (K := clipK a s τ ε) (m := clipM s τ ε) (clipL s τ ε) (clipLen s τ ε) (clipWt s τ ε)
        (CayleyTransfer.c (clipStep s τ ε)) (CayleyTransfer.sigma (clipStep s τ ε)) UJ D
        (2 * degree s τ ε) ∘L io)
    hJrel hTrel io_isometry hT' hB' E hEu
  have hAmp2 : ‖reflectedAmplification io (LCU (K := clipK a s τ ε) (m := clipM s τ ε)
      (clipL s τ ε) (clipLen s τ ε) (clipWt s τ ε) (CayleyTransfer.c (clipStep s τ ε))
      (CayleyTransfer.sigma (clipStep s τ ε)) UJ D (2 * degree s τ ε) ∘L io) - io ∘L E‖ ≤ ε :=
    hAmp.trans hCore
  have hio : run (simSem UJ D) (clipCircuit a s τ ε) ∘L io =
      AMP (K := clipK a s τ ε) (m := clipM s τ ε) (clipL s τ ε) (clipLen s τ ε) (clipWt s τ ε)
        (CayleyTransfer.c (clipStep s τ ε)) (CayleyTransfer.sigma (clipStep s τ ε)) UJ D
        (2 * degree s τ ε) ∘L io := by
    unfold clipCircuit
    refine ContinuousLinearMap.ext (fun ψ => ?_)
    rw [comp_apply, comp_apply, io_apply]
    exact hagree _ (supp_bas _ (fun w _ => rfl) ψ)
  rw [hio, AMP_io _ _ _ _ _ UJ D _ (unitary_comp_adj hLCUu)]
  exact hAmp2

/-- **Proposition `gate:prop:core` for both signs of the time**: the circuit for `|t|` (with
`aval s τ ε` the compressed time) or its literal inverse simulates `e^{-i (±a) J†KJ}`. -/
theorem clipped_gate_simulation_neg [FiniteDimensional ℂ P] (a : ℕ) {s τ ε : ℝ}
    (R : Regime s τ ε) (UJ D : Anc a P →L[ℂ] Anc a P) (hUJ : IsUnitary UJ) (hDu : IsUnitary D)
    {Kb Pp Pm : Anc a P →L[ℂ] Anc a P}
    (h : Core.CoreData s τ ε Kb D Pp Pm (UJ ∘L iota0)) :
    (∀ g ∈ invList (clipCircuit a s τ ε), g.Valid Wire.anc) ∧
    nPriv (invList (clipCircuit a s τ ε)) = 6 * degree s τ ε ∧
    nUJ (invList (clipCircuit a s τ ε)) = 12 * degree s τ ε ∧
    nGates (invList (clipCircuit a s τ ε)) ≤
      200 * (degree s τ ε + 1) * (a + clipM s τ ε + clipR s τ ε + 1) ∧
    ‖run (simSem UJ D) (invList (clipCircuit a s τ ε)) ∘L io -
        io ∘L NormedSpace.exp ((-Complex.I * ((-aval s τ ε : ℝ) : ℂ)) •
          ((UJ ∘L iota0)† ∘L Kb ∘L (UJ ∘L iota0)))‖ ≤ ε := by
  obtain ⟨hv, h1, h2, h3, -, herr, -⟩ := clipped_gate_simulation a R UJ D hUJ hDu h
  refine ⟨invList_valid _ hv, by rw [nPriv_invList, h1], by rw [nUJ_invList, h2],
    by rw [nGates_invList]; exact h3, ?_⟩
  have hSelf : star ((UJ ∘L iota0)† ∘L Kb ∘L (UJ ∘L iota0)) =
      (UJ ∘L iota0)† ∘L Kb ∘L (UJ ∘L iota0) := by
    rw [ContinuousLinearMap.star_eq_adjoint, adjoint_comp, adjoint_comp, adjoint_adjoint,
      h.spectral.self.adjoint_eq, comp_assoc]
  have hCu : IsUnitary (run (simSem (m := clipM s τ ε) (r := clipR s τ ε) (K := clipK a s τ ε)
      UJ D) (clipCircuit a s τ ε)) :=
    run_isUnitary (simSem (m := clipM s τ ε) (r := clipR s τ ε) (K := clipK a s τ ε) UJ D) hUJ hDu
      _ hv
  have ha := R.a_pos
  rw [run_invList]
  generalize run (simSem (m := clipM s τ ε) (r := clipR s τ ε) (K := clipK a s τ ε) UJ D)
    (clipCircuit a s τ ε) = C at hCu herr ⊢
  refine err_inverse C hCu _ _ hSelf (-aval s τ ε) ε (by linarith) ?_
  rw [abs_neg, abs_of_pos ha]
  exact herr

end

end GateOptimalPrecision
