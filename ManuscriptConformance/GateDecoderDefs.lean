import ManuscriptConformance.GateGeneralDefs
import GeneralSparseAccess.ImplE

/-!
# Sparse access of general size with a validity decoder

The transfer of `GateGeneralDefs` for the padded data with a validity decoder
(`QData.padDataE`), which needs no zero word of the decoder:

* `matOp_padForm_comp`, `exp_padForm_comp`: on the clean marker, a matrix of the padded form
  (`PadForm`) acts, and evolves, as the padded matrix `D.padMat`;
* `genCircE hS ζ N s Cc`: from a circuit `Cc` over the gate set calling the primitives of
  `padDataE`, every call replaced by its implementation (`implPE`: the padded locators and one
  supplied value call) and the gates outside the gate set synthesised at accuracy `ζ`;
* `genCircE_spec`: validity, every gate in the gate set, at most three supplied calls per call of
  `Cc`, at most `nGatesN Cc + implG k b · nCallsN (fun _ => true) Cc · (1 + L ζ)` gates;
* `genCircE_error`: the full-output error against the evolution of `D.padMat x` on the low index
  wires is at most that of `Cc` against the evolution of `padDataE`, plus `nGatesN (subst …) · ζ`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateSynth SparseHamiltonian.GateBinary SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.OracleCircuit
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

/-! ### The evolution of a matrix of the padded form on the clean marker -/

section EvolutionE

variable {X : Type*} {N s k b : ℕ} (D : QData X N s k b)
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {M : X → Matrix (Cfg (Fin (k + 1))) (Cfg (Fin (k + 1))) ℂ}

omit [CompleteSpace R] in
/-- **A matrix of the padded form on the clean marker is the padded matrix.** -/
theorem matOp_padForm_comp (hM : PadForm D M) (x : X) :
    matOp (Q := R) (M x) ∘L cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) =
      cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) ∘L matOp (D.padMat x) := by
  refine ContinuousLinearMap.ext fun ψ => PiLp.ext fun y => ?_
  simp only [comp_apply, matOp_apply, cleanAlong_castSucc_apply, hM.eq_mark]
  by_cases hy : mark y = false
  · rw [if_pos hy, ← sum_mark_false (fun d => D.padMat x (lo y) d • ψ d)]
    apply Finset.sum_congr rfl
    intro y' _
    by_cases hy' : mark y' = false
    · rw [if_pos ⟨hy, hy'⟩, if_pos hy', if_pos hy']
    · rw [if_neg (fun h => hy' h.2), if_neg hy', if_neg hy', zero_smul]
  · rw [if_neg hy]
    apply Finset.sum_eq_zero
    intro y' _
    rw [if_neg (fun h => hy h.1), zero_smul]

/-- **The evolution of a matrix of the padded form on the clean marker is the evolution of the
padded matrix.** -/
theorem exp_padForm_comp (hM : PadForm D M) (x : X) (t : ℝ) :
    NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
        (SparseStateOverlap.matrixOperator (M x))) ∘L
        cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) =
      cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) ∘L
        NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
          (SparseStateOverlap.matrixOperator (D.padMat x))) := by
  apply exp_comp_of_comp
  rw [qlift_refl_matrixOperator, qlift_refl_matrixOperator, smul_comp, comp_smul,
    matOp_padForm_comp D hM]

end EvolutionE

/-! ### The circuit of general sparse data with a validity decoder -/

section GenE

variable {𝒢 : Set Kind} {Xs : Type*} [Fintype Xs] [DecidableEq Xs] {L : ℝ → ℕ}
variable {W : Type*} [Fintype W] [DecidableEq W] {k b : ℕ}

/-- **The circuit of general sparse data** from a circuit `Cc` of the padded data with a validity
decoder: every call replaced by its implementation (`implPE`), then the gates outside the gate set
synthesised at accuracy `ζ` (`keepC`). -/
def genCircE (hS : Synthesis 𝒢 Xs L) (ζ : ℝ) (N s : ℕ)
    (Cc : List (NInstr W (PY (k + 1) b) Query)) :
    List (NInstr ((W ⊕ GeneralSparseAccess.AW k b) ⊕ Xs) (PY k b) Query) :=
  keepC hS ζ (subst (implPE N s) Cc)

/-- **Validity, gate set and counts of the circuit of general sparse data.** -/
theorem genCircE_spec {N s : ℕ} (hS : Synthesis 𝒢 Xs L) {ζ : ℝ} (hζ : 0 < ζ)
    (Cc : List (NInstr W (PY (k + 1) b) Query)) (hv : ∀ i ∈ Cc, i.Valid)
    (hg : ∀ g, NInstr.gate g ∈ Cc → GateOf 𝒢 g) :
    (∀ i ∈ genCircE hS ζ N s Cc, i.Valid) ∧
      (∀ g, NInstr.gate g ∈ genCircE hS ζ N s Cc → GateOf 𝒢 g) ∧
      nCallsN (fun _ => true) (genCircE hS ζ N s Cc) ≤ 3 * nCallsN (fun _ => true) Cc ∧
      nGatesN (genCircE hS ζ N s Cc) ≤
        nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc * (1 + L ζ) ∧
      nGatesN (subst (implPE N s) Cc) ≤ nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc := by
  have hC2v := valid_subst (valid_implPE (k := k) (b := b) N s) Cc hv
  obtain ⟨hv', hg', hgates, hcalls⟩ := keepC_spec hS hζ _ hC2v
  have hsubG := nGatesN_subst_le (implPE N s) (implG k b) (nGatesN_implPE_le N s) Cc
  have hout := nGatesOut_subst_le 𝒢 (implPE N s) (implG k b) (nGatesN_implPE_le N s) Cc hg
  have hcall := nCallsN_subst_le (kindOK_implPE (k := k) (b := b) N s) (fun _ => true) Cc
  refine ⟨hv', hg', ?_, ?_, hsubG⟩
  · unfold genCircE
    rw [hcalls]
    exact hcall
  · unfold genCircE
    calc nGatesN (keepC hS ζ (subst (implPE N s) Cc))
        ≤ nGatesN (subst (implPE N s) Cc) + nGatesOut 𝒢 (subst (implPE N s) Cc) * L ζ :=
          hgates
      _ ≤ (nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc) +
            (implG k b * nCallsN (fun _ => true) Cc) * L ζ :=
          Nat.add_le_add hsubG (Nat.mul_le_mul_right _ hout)
      _ = nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc * (1 + L ζ) := by ring

/-- **The full-output error of the circuit of general sparse data**: at most the full-output
error of `Cc` on the padded data with a validity decoder plus `nGatesN (subst …) · ζ`, against the
evolution of the padded matrix on the low index wires. -/
theorem genCircE_error {X : Type*} {N s : ℕ} (D : QData X N s k b) (hS : Synthesis 𝒢 Xs L)
    {ζ : ℝ} (hζ : 0 < ζ) (sys : Fin (k + 1) ↪ W) (Cc : List (NInstr W (PY (k + 1) b) Query))
    (hv : ∀ i ∈ Cc, i.Valid)
    {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R] (x : X)
    (t ε : ℝ) (hε : 0 ≤ ε)
    (h : FullOutputError (nrun (GateBinary.prims (R := R) D.padDataE (Equiv.refl _) x) Cc)
      (cleanAlong sys) (NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
        (SparseStateOverlap.matrixOperator (D.padDataE.matrix x)))) ε) :
    FullOutputError (nrun (D.prims (R := R) x) (genCircE hS ζ N s Cc))
      (cleanAlong (genSys Xs sys))
      (NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
        (SparseStateOverlap.matrixOperator (D.padMat x))))
      (ε + nGatesN (subst (implPE N s) Cc) * ζ) := by
  apply fullOutputError_of_norm
  have hprim : ∀ j, IsUnitary (D.prims (R := R) x j) := D.prims_isUnitary x
  have hprim' : ∀ j, IsUnitary (GateBinary.prims (R := R) D.padDataE (Equiv.refl _) x j) :=
    GateBinary.prims_isUnitary _ _ x
  have hok := implOKE (R := R) (N := N) (s := s) D x
  have hsub := nrun_subst_cleanEmb (D.prims x) _ hprim hprim' hok Cc
  have hC2v := valid_subst hok.valid Cc hv
  have hE2n : ∀ p : Reg (Fin k) R, ‖(cleanEmb (X := GeneralSparseAccess.AW k b) ∘L
      (cleanAlong sys ∘L cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)))) p‖ ≤ ‖p‖ :=
    fun p => by rw [comp_apply, comp_apply, norm_cleanEmb, norm_cleanAlong, norm_cleanAlong]
  have hkeep := keepC_error (D.prims (R := R) x) hS hζ _ hC2v hprim _ hE2n
    (NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
      (SparseStateOverlap.matrixOperator (D.padMat x))))
  rw [cleanAlong_genSys]
  unfold genCircE
  refine hkeep.trans (add_le_add ?_ le_rfl)
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro p
  have h1 := DFunLike.congr_fun hsub
    (cleanAlong sys (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) p))
  have h2 := DFunLike.congr_fun (exp_padForm_comp (R := R) D (padForm_padDataE D) x t) p
  simp only [comp_apply] at h1 h2
  simp only [sub_apply, comp_apply]
  rw [h1, ← h2, ← map_sub, norm_cleanEmb]
  calc _ ≤ ε * ‖cleanAlong (R := R) (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) p‖ :=
        fullOutputError_apply_le h hε _
    _ = ε * ‖p‖ := by rw [norm_cleanAlong]

end GenE

end

end ManuscriptConformance
