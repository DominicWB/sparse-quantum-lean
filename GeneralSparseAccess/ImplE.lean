import GeneralSparseAccess.PadE

/-!
# Implementing the padded primitives with a validity decoder

`implPE N s`: the native circuits implementing the primitives of `QData.padDataE` from the supplied
primitives: the padded locators of `implP` and, for the value oracle, one supplied value call on
the low edge wires and the value wires (`implValE`), since the stored word of `padDataE` is the
supplied word of the low index words on every pair. `implOKE`: on clean ancillas each acts as the
padded primitive; `kindOK_implPE`, `nGatesN_implPE_le`: at most three calls of the corresponding
supplied primitive and `implG k b` gates.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralSparseAccess

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary
open SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GatePointerEncoding (wordValue)
open NativeSparseBlockEncoding (Query)
open QData (lowE mw₁ mw₂ lowE_injective lowE_ne_mw₁ lowE_ne_mw₂)
open scoped InnerProduct
open IW

section ImplE

variable {k b : ℕ}

/-- **The implementation of the value oracle of `padDataE`**: one supplied value call on the low
edge wires and the value wires. -/
def implValE : List (NInstr (IW k b) (PY k b) Query) := [NInstr.call Query.value false posT]

/-- **The implementations of the primitives of `padDataE`**: the padded locators of `implP` and
the supplied value call `implValE`. -/
def implPE (N s : ℕ) : Query → List (NInstr (IW k b) (PY k b) Query)
  | .rowLocation => implLoc N s Query.rowLocation
  | .columnLocation => implLoc N s Query.columnLocation ++ nGatesOf (swapRegs k b)
  | .value => implValE

/-- **The implementations are valid circuits.** -/
theorem valid_implPE (N s : ℕ) : ∀ j, ∀ i ∈ implPE (k := k) (b := b) N s j, i.Valid := by
  intro j
  cases j with
  | rowLocation => exact valid_implLoc N s _
  | columnLocation =>
      intro i hi
      rcases List.mem_append.mp hi with h | h
      · exact valid_implLoc N s _ i h
      · exact valid_nGatesOf _ gateOK_swapRegs i h
  | value =>
      intro i hi
      change i ∈ [NInstr.call Query.value false posT] at hi
      rw [List.mem_singleton] at hi
      subst hi
      trivial

/-- **Every implementation makes at most three calls, all of the corresponding supplied
primitive.** -/
theorem kindOK_implPE (N s : ℕ) : KindOK (implPE (k := k) (b := b) N s) id 3 where
  kind_eq j := by
    cases j with
    | rowLocation => exact callsOf_implLoc N s _
    | columnLocation => exact callsOf_append (callsOf_implLoc N s _) (callsOf_nGatesOf _ _)
    | value => exact callsOf_call _ _ _
  count j := by
    cases j with
    | rowLocation =>
        simp only [implPE, implLoc, ctrlRef, nCallsN_append, nCallsN_nGatesOf, gadget_nCalls,
          nCallsN_call]
        omega
    | columnLocation =>
        simp only [implPE, implLoc, ctrlRef, nCallsN_append, nCallsN_nGatesOf, gadget_nCalls,
          nCallsN_call]
        omega
    | value =>
        simp only [implPE, implValE, nCallsN_call]
        omega

/-- **Every implementation has at most `implG k b` elementary gates.** -/
theorem nGatesN_implPE_le (N s : ℕ) (j : Query) :
    nGatesN (implPE (k := k) (b := b) N s j) ≤ implG k b := by
  have hE : Fintype.card (EW k) = 2 * k := by
    rw [Fintype.card_sum, Fintype.card_fin]
    ring
  have hM := length_maskC_le (k := k) (b := b) N s
  unfold implG
  cases j with
  | rowLocation =>
      simp only [implPE, implLoc, ctrlRef, nGatesN_append, nGatesN_nGatesOf, gadget_nGates,
        nGatesN_call, hE]
      omega
  | columnLocation =>
      simp only [implPE, implLoc, ctrlRef, nGatesN_append, nGatesN_nGatesOf, gadget_nGates,
        nGatesN_call, hE, length_swapRegs]
      omega
  | value =>
      simp only [implPE, implValE, nGatesN_call]
      omega

end ImplE

/-! ### On clean ancillas -/

section Clean

variable {X : Type*} {N s k b : ℕ} (D : QData X N s k b)
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The padded row locator of `padDataE` on the padded register**. -/
theorem prims_padE_row (x : X) :
    GateBinary.prims (R := R) D.padDataE (Equiv.refl _) x Query.rowLocation =
      localOp (Sum.inl : EW (k + 1) → PY (k + 1) b) Sum.inl_injective
        (fun _ => ctlE (qlift (R := R) (Equiv.refl _) (D.rowOracle x))) ∘L
        permOp (maskY N s) := by
  rw [GateBinary.prims_row, permOp_maskY, localOp_comp]
  congr 1
  funext _
  change qlift (phiE (Equiv.refl _)) (ofMat (phiE (Equiv.refl _)) (D.rowMat x)) = _
  rw [qlift_ofMat, QData.matOp_rowMat]
  rfl

/-- **The padded column locator of `padDataE` on the padded register**. -/
theorem prims_padE_col (x : X) :
    GateBinary.prims (R := R) D.padDataE (Equiv.refl _) x Query.columnLocation =
      permOp (swapY k b) ∘L (localOp (Sum.inl : EW (k + 1) → PY (k + 1) b) Sum.inl_injective
        (fun _ => ctlE (qlift (R := R) (Equiv.refl _) (D.columnOracle x))) ∘L
        permOp (maskY N s)) := by
  rw [GateBinary.prims_col, permOp_maskY, permOp_swapY, localOp_comp, localOp_comp]
  congr 1
  funext _
  change qlift (phiE (Equiv.refl _)) (ofMat (phiE (Equiv.refl _)) (D.colMat x)) = _
  rw [qlift_ofMat, QData.matOp_colMat]
  rfl

theorem implRowE_clean (x : X) :
    nrun (D.prims (R := R) x) (implLoc N s Query.rowLocation) ∘L cleanEmb (X := AW k b) =
      cleanEmb ∘L GateBinary.prims (R := R) D.padDataE (Equiv.refl _) x Query.rowLocation := by
  rw [prims_padE_row]
  exact maskCtrl_clean (D.rowOracle x) (D.row_unitary x) (D.rowloc x) D.N_pos D.slots_pos
    (D.row_valid x ⟨0, D.N_pos⟩ ⟨0, D.slots_pos⟩) D.N_lt_pow_succ D.s_lt_pow_succ (D.prims x)
    Query.rowLocation (D.prims_row x)

theorem implColE_clean (x : X) :
    nrun (D.prims (R := R) x) (implLoc N s Query.columnLocation ++ nGatesOf (swapRegs k b)) ∘L
        cleanEmb (X := AW k b) =
      cleanEmb ∘L GateBinary.prims (R := R) D.padDataE (Equiv.refl _) x Query.columnLocation := by
  unfold implLoc
  rw [prims_padE_col, nrun_append, nrun_nGatesOf, comp_assoc,
    maskCtrl_clean (D.columnOracle x) (D.column_unitary x) (D.colloc x) D.N_pos D.slots_pos
      (D.column_valid x ⟨0, D.N_pos⟩ ⟨0, D.slots_pos⟩) D.N_lt_pow_succ D.s_lt_pow_succ
      (D.prims x) Query.columnLocation (D.prims_col x),
    ← comp_assoc (gRun (Q := R) (swapRegs k b)), gRun_swapRegs_cleanEmb, comp_assoc]

/-- The configuration map of the supplied value call on the low edge wires and the value wires:
the stored word of the low index words XOR-ed into the value wires. -/
theorem alongEquiv_posT_cleanEmb (x : X) (y : Cfg (PY (k + 1) b)) :
    alongEquiv (posT (k := k) (b := b)) (xorEquiv (fun d => D.table x d))
        (Sum.elim y (fun _ => false)) =
      Sum.elim (xorEquiv (fun d => D.ptableE x (phiE (Equiv.refl _) d)) y) (fun _ => false) := by
  funext u
  rcases u with (w | w) | a
  · rcases QData.wire_cases k w with ⟨a, rfl⟩ | rfl | rfl
    · change alongEquiv posT _ _ (posT (Sum.inl a)) = _
      rw [alongEquiv_apply_in]
      rfl
    · rw [alongEquiv_apply_out]
      · rfl
      · rintro (a | u) h
        · exact lowE_ne_mw₁ k a (Sum.inl_injective (Sum.inl_injective h))
        · simp [posT, IW.v] at h
    · rw [alongEquiv_apply_out]
      · rfl
      · rintro (a | u) h
        · exact lowE_ne_mw₂ k a (Sum.inl_injective (Sum.inl_injective h))
        · simp [posT, IW.v] at h
  · change alongEquiv posT _ _ (posT (Sum.inr w)) = _
    rw [alongEquiv_apply_in]
    change (Sum.elim y (fun _ => false) (Sum.inl (Sum.inr w)) ^^
        D.table x (fun a => Sum.elim y (fun _ => false) (posT (Sum.inl a))) w) =
      (y (Sum.inr w) ^^ D.ptableE x (phiE (Equiv.refl _) (fun e => y (Sum.inl e))) w)
    unfold QData.ptableE
    congr 3
    funext a
    rcases a with j | j <;> rfl
  · rw [alongEquiv_apply_out]
    · rfl
    · rintro (c | u) h
      · simp [posT, IW.tl, IW.e] at h
      · simp [posT, IW.v] at h

/-- **The value oracle of `padDataE` on clean ancillas**: one supplied value call. -/
theorem implValE_clean (x : X) :
    nrun (D.prims (R := R) x) (implValE (k := k) (b := b)) ∘L cleanEmb (X := AW k b) =
      cleanEmb ∘L GateBinary.prims (R := R) D.padDataE (Equiv.refl _) x Query.value := by
  rw [GateBinary.prims_val]
  apply ext_bas_clm'
  intro y q
  rw [comp_apply, comp_apply, cleanEmb_bas, permOp_bas, cleanEmb_bas]
  unfold implValE
  rw [nrun_singleton, NInstr.eval_call]
  change localOp posT posT.injective (fun _ => D.prims x Query.value) (bas _ q) = _
  rw [D.prims_val, localOp_permOp, permOp_bas]
  congr 1
  exact alongEquiv_posT_cleanEmb D x y

/-- **The implementations act as the primitives of `padDataE` on clean ancillas**, for every
unitary extension of the supplied locators outside their valid list inputs. -/
theorem implOKE (x : X) :
    ImplOK (D.prims (R := R) x) (GateBinary.prims (R := R) D.padDataE (Equiv.refl _) x)
      (implPE N s) where
  valid := valid_implPE N s
  clean j := by
    cases j with
    | rowLocation => exact implRowE_clean D x
    | columnLocation => exact implColE_clean D x
    | value => exact implValE_clean D x

end Clean

end

end SparseHamiltonian.GeneralSparseAccess
