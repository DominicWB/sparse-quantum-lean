import GeneralSparseAccess.ImplVal

/-!
# The implementation of the padded primitives

`implP N s z₀`: the native circuits implementing the three primitive oracles of the padded data
(`QData.padData`) from the supplied primitives (`QData.prims`):

* the padded row locator (`implLoc N s Query.rowLocation`): the mask and the supplied row locator
  controlled on a clear marker of the position, with a reference (three calls);
* the padded column locator: the same with the supplied column locator, then the exchange of the
  two index registers;
* the padded value oracle (`implVal`, two calls).

On clean ancillas each circuit acts as the padded primitive (`implOK`), for every action of the
supplied locators outside their valid list inputs. Every implementation makes at most three calls,
all of the corresponding supplied primitive (`kindOK_implP`), and has at most `implG k b`
elementary gates (`nGatesN_implP_le`).
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
open QData (lowE mw₁ mw₂ evalid maskE maskF lowE_injective lowE_ne_mw₁ lowE_ne_mw₂ mw₁_ne_mw₂)
open scoped InnerProduct
open IW

/-! ### The gates of the value oracle -/

section ValueGates

variable {k b : ℕ}

theorem gateOK_vflagC (N : ℕ) : ∀ g ∈ vflagC (k := k) (b := b) N, GateOK 3 g := by
  intro g hg
  have hc := classical_vflagC (k := k) (b := b) N g hg
  refine ⟨?_, hc.2, by rw [hc.1]; exact pauliX_unitary⟩
  unfold vflagC at hg
  simp only [List.mem_append] at hg
  rcases hg with (h | h) | h
  · exact (gateOK_ltChain N layoutA g h).1
  · exact (gateOK_ltChain N layoutB g h).1
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp

theorem gateOK_copyC (z₀ : Cfg (VW b)) : ∀ g ∈ copyC (k := k) z₀, GateOK 3 g := by
  intro g hg
  have hc := classical_copyC (k := k) z₀ g hg
  refine ⟨?_, hc.2, by rw [hc.1]; exact pauliX_unitary⟩
  rcases List.mem_flatMap.mp hg with ⟨w, -, hw⟩
  unfold copyW at hw
  simp only [List.mem_cons] at hw
  rcases hw with rfl | hw
  · simp
  · split_ifs at hw
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw
      simp
    · simp at hw

theorem length_vflagC_le (N : ℕ) : (vflagC (k := k) (b := b) N).length ≤ 4 * (k + 1) + 2 := by
  unfold vflagC
  simp only [List.length_append, List.length_cons, List.length_nil]
  have h1 := length_ltChain_le N (xA (k := k) (b := b)) bA
  have h2 := length_ltChain_le N (xB (k := k) (b := b)) bB
  omega

theorem length_copyW_le (z₀ : Cfg (VW b)) (w : VW b) : (copyW (k := k) z₀ w).length ≤ 2 := by
  unfold copyW
  split_ifs <;> simp

theorem length_copyC_le (z₀ : Cfg (VW b)) : (copyC (k := k) z₀).length ≤ 4 * b := by
  unfold copyC
  rw [List.length_flatMap]
  have h := List.sum_le_card_nsmul
    (((Finset.univ : Finset (VW b)).toList).map (fun w => (copyW (k := k) z₀ w).length)) 2
    (by
      intro x hx
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp hx
      exact length_copyW_le z₀ w)
  rw [List.length_map, Finset.length_toList, Finset.card_univ, smul_eq_mul, Fintype.card_sum,
    Fintype.card_fin] at h
  omega

end ValueGates

/-! ### Circuits calling a single primitive -/

section CallsOf

variable {V Y J : Type*}

/-- Every call of the circuit `is` is a call of the primitive `j` (or of its inverse). -/
def CallsOf (j : J) (is : List (NInstr V Y J)) : Prop :=
  ∀ q ∈ is, ∀ j' adj pos, q = NInstr.call j' adj pos → j' = j

theorem callsOf_append {j : J} {is js : List (NInstr V Y J)} (h1 : CallsOf j is)
    (h2 : CallsOf j js) : CallsOf j (is ++ js) := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact h1 q h
  · exact h2 q h

theorem callsOf_nGatesOf [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] (j : J)
    (gs : List (Gate V)) : CallsOf j (nGatesOf (Y := Y) (J := J) gs) := by
  intro q hq j' adj pos h
  simp only [nGatesOf, List.mem_map] at hq
  obtain ⟨g, -, rfl⟩ := hq
  cases h

theorem callsOf_call (j : J) (adj : Bool) (pos : Y ↪ V) : CallsOf j [NInstr.call j adj pos] := by
  intro q hq j' adj' pos' h
  rw [List.mem_singleton] at hq
  subst hq
  injection h with h1
  exact h1.symm

theorem callsOf_gadget [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] {E : Type*}
    [Fintype E] [DecidableEq E] {j : J} (c : V) (pol : Bool) (T Dm Rf : E → V)
    {call : List (NInstr V Y J)} (h : CallsOf j call) : CallsOf j (gadget c pol T Dm Rf call) := by
  unfold gadget
  exact callsOf_append (callsOf_append (callsOf_append (callsOf_nGatesOf _ _) h)
    (callsOf_nGatesOf _ _)) (callsOf_nGatesOf _ _)

theorem callsOf_ctrlRef [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] {E : Type*}
    [Fintype E] [DecidableEq E] {j : J} (c : V) (pol : Bool) (T Dm Rf : E → V)
    {callT callR callR' : List (NInstr V Y J)} (hT : CallsOf j callT) (hR : CallsOf j callR)
    (hR' : CallsOf j callR') : CallsOf j (ctrlRef c pol T Dm Rf callT callR callR') :=
  callsOf_append (callsOf_append hR (callsOf_gadget c pol T Dm Rf hT)) hR'

theorem nGatesN_call (j : J) (adj : Bool) (pos : Y ↪ V) :
    nGatesN [NInstr.call j adj pos] = 0 := rfl

theorem nCallsN_call (j : J) (adj : Bool) (pos : Y ↪ V) :
    nCallsN (fun _ => true) [NInstr.call j adj pos] = 1 := rfl

end CallsOf

/-! ### The implementations -/

section Impl

variable {k b : ℕ}

/-- **The implementation of a padded locator**: the mask, then the controlled call of the supplied
locator `j` with a reference (three calls). -/
def implLoc (N s : ℕ) (j : Query) : List (NInstr (IW k b) (PY k b) Query) :=
  nGatesOf (maskC N s) ++ ctrlRef (e (mw₂ k)) false tl dm rf
    [NInstr.call j false posT] [NInstr.call j false posR] [NInstr.call j true posR]

/-- **The implementations of the padded primitives**: the padded locators (the column locator
followed by the exchange of the two index registers) and the padded value oracle. -/
def implP (N s : ℕ) (z₀ : Cfg (VW b)) : Query → List (NInstr (IW k b) (PY k b) Query)
  | .rowLocation => implLoc N s Query.rowLocation
  | .columnLocation => implLoc N s Query.columnLocation ++ nGatesOf (swapRegs k b)
  | .value => implVal N z₀

theorem valid_implLoc (N s : ℕ) (j : Query) : ∀ i ∈ implLoc (k := k) (b := b) N s j, i.Valid := by
  intro i hi
  unfold implLoc ctrlRef at hi
  simp only [List.mem_append, List.mem_singleton] at hi
  rcases hi with h | (h | h) | h
  · exact valid_nGatesOf _ (gateOK_maskC N s) i h
  · subst h
    trivial
  · refine gadget_valid _ false tl dm rf refLayout.T_ne_Dm refLayout.T_ne_Rf refLayout.T_ne_c
      refLayout.Dm_ne_c _ (fun i' hi' => ?_) i h
    rw [List.mem_singleton] at hi'
    subst hi'
    trivial
  · subst h
    trivial

theorem valid_implVal (N : ℕ) (z₀ : Cfg (VW b)) : ∀ i ∈ implVal (k := k) N z₀, i.Valid := by
  intro i hi
  unfold implVal at hi
  simp only [List.mem_append, List.mem_singleton] at hi
  rcases hi with (((h | h) | h) | h) | h
  · exact valid_nGatesOf _ (gateOK_vflagC N) i h
  · subst h
    trivial
  · exact valid_nGatesOf _ (gateOK_copyC z₀) i h
  · subst h
    trivial
  · exact valid_nGatesOf _ (fun g hg => gateOK_vflagC N g (List.mem_reverse.mp hg)) i h

/-- **The implementations are valid circuits.** -/
theorem valid_implP (N s : ℕ) (z₀ : Cfg (VW b)) :
    ∀ j, ∀ i ∈ implP (k := k) (b := b) N s z₀ j, i.Valid := by
  intro j
  cases j with
  | rowLocation => exact valid_implLoc N s _
  | columnLocation =>
      intro i hi
      rcases List.mem_append.mp hi with h | h
      · exact valid_implLoc N s _ i h
      · exact valid_nGatesOf _ gateOK_swapRegs i h
  | value => exact valid_implVal N z₀

theorem callsOf_implLoc (N s : ℕ) (j : Query) : CallsOf j (implLoc (k := k) (b := b) N s j) :=
  callsOf_append (callsOf_nGatesOf _ _)
    (callsOf_ctrlRef _ _ _ _ _ (callsOf_call _ _ _) (callsOf_call _ _ _) (callsOf_call _ _ _))

theorem callsOf_implVal (N : ℕ) (z₀ : Cfg (VW b)) :
    CallsOf Query.value (implVal (k := k) N z₀) := by
  unfold implVal
  exact callsOf_append (callsOf_append (callsOf_append (callsOf_append (callsOf_nGatesOf _ _)
    (callsOf_call _ _ _)) (callsOf_nGatesOf _ _)) (callsOf_call _ _ _)) (callsOf_nGatesOf _ _)

/-- **Every implementation makes at most three calls, all of the corresponding supplied
primitive.** -/
theorem kindOK_implP (N s : ℕ) (z₀ : Cfg (VW b)) :
    KindOK (implP (k := k) (b := b) N s z₀) id 3 where
  kind_eq j := by
    cases j with
    | rowLocation => exact callsOf_implLoc N s _
    | columnLocation => exact callsOf_append (callsOf_implLoc N s _) (callsOf_nGatesOf _ _)
    | value => exact callsOf_implVal N z₀
  count j := by
    cases j with
    | rowLocation =>
        simp only [implP, implLoc, ctrlRef, nCallsN_append, nCallsN_nGatesOf, gadget_nCalls,
          nCallsN_call]
        omega
    | columnLocation =>
        simp only [implP, implLoc, ctrlRef, nCallsN_append, nCallsN_nGatesOf, gadget_nCalls,
          nCallsN_call]
        omega
    | value =>
        simp only [implP, implVal, nCallsN_append, nCallsN_nGatesOf, nCallsN_call]
        omega

/-- The gate budget of an implementation. -/
def implG (k b : ℕ) : ℕ := 30 * (k + 1) + 4 * b

/-- **Every implementation has at most `implG k b` elementary gates.** -/
theorem nGatesN_implP_le (N s : ℕ) (z₀ : Cfg (VW b)) (j : Query) :
    nGatesN (implP (k := k) (b := b) N s z₀ j) ≤ implG k b := by
  have hE : Fintype.card (EW k) = 2 * k := by
    rw [Fintype.card_sum, Fintype.card_fin]
    ring
  have hM := length_maskC_le (k := k) (b := b) N s
  unfold implG
  cases j with
  | rowLocation =>
      simp only [implP, implLoc, ctrlRef, nGatesN_append, nGatesN_nGatesOf, gadget_nGates,
        nGatesN_call, hE]
      omega
  | columnLocation =>
      simp only [implP, implLoc, ctrlRef, nGatesN_append, nGatesN_nGatesOf, gadget_nGates,
        nGatesN_call, hE, length_swapRegs]
      omega
  | value =>
      have h1 := length_vflagC_le (k := k) (b := b) N
      have h2 := length_copyC_le (k := k) z₀
      simp only [implP, implVal, nGatesN_append, nGatesN_nGatesOf, nGatesN_call,
        List.length_reverse]
      omega

end Impl

/-! ### On clean ancillas -/

section Clean

variable {X : Type*} {N s k b : ℕ} (D : QData X N s k b)
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

theorem QData.N_lt_pow_succ (D : QData X N s k b) : N < 2 ^ (k + 1) := by
  have h1 := D.hN
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have h3 : 0 < 2 ^ k := by positivity
  omega

theorem QData.s_lt_pow_succ (D : QData X N s k b) : s < 2 ^ (k + 1) :=
  lt_of_le_of_lt D.hs D.N_lt_pow_succ

/-- The mask of the padded register as a local operation on its edge register. -/
theorem permOp_maskY (N s : ℕ) : permOp (Q := R) (maskY (k := k) (b := b) N s) =
    localOp (Sum.inl : EW (k + 1) → PY (k + 1) b) Sum.inl_injective
      (fun _ => permOp (maskE N s)) :=
  (localOp_permOp ⟨Sum.inl, Sum.inl_injective⟩ (maskE N s)).symm

/-- The exchange of the index registers as a local operation on the edge register. -/
theorem permOp_swapY : permOp (Q := R) (swapY k b) =
    localOp (Sum.inl : EW (k + 1) → PY (k + 1) b) Sum.inl_injective
      (fun _ => permOp (QData.swapE k)) :=
  (localOp_permOp ⟨Sum.inl, Sum.inl_injective⟩ (QData.swapE k)).symm

/-- **The padded row locator on the padded register**: the controlled supplied row locator after
the mask. -/
theorem prims_pad_row (z₀ : Cfg (VW b)) (hz₀ : D.val z₀ = 0) (x : X) :
    GateBinary.prims (R := R) (D.padData z₀ hz₀) (Equiv.refl _) x Query.rowLocation =
      localOp (Sum.inl : EW (k + 1) → PY (k + 1) b) Sum.inl_injective
        (fun _ => ctlE (qlift (R := R) (Equiv.refl _) (D.rowOracle x))) ∘L
        permOp (maskY N s) := by
  rw [GateBinary.prims_row, permOp_maskY, localOp_comp]
  congr 1
  funext _
  change qlift (phiE (Equiv.refl _)) (ofMat (phiE (Equiv.refl _)) (D.rowMat x)) = _
  rw [qlift_ofMat, QData.matOp_rowMat]
  rfl

/-- **The padded column locator on the padded register**. -/
theorem prims_pad_col (z₀ : Cfg (VW b)) (hz₀ : D.val z₀ = 0) (x : X) :
    GateBinary.prims (R := R) (D.padData z₀ hz₀) (Equiv.refl _) x Query.columnLocation =
      permOp (swapY k b) ∘L (localOp (Sum.inl : EW (k + 1) → PY (k + 1) b) Sum.inl_injective
        (fun _ => ctlE (qlift (R := R) (Equiv.refl _) (D.columnOracle x))) ∘L
        permOp (maskY N s)) := by
  rw [GateBinary.prims_col, permOp_maskY, permOp_swapY, localOp_comp, localOp_comp]
  congr 1
  funext _
  change qlift (phiE (Equiv.refl _)) (ofMat (phiE (Equiv.refl _)) (D.colMat x)) = _
  rw [qlift_ofMat, QData.matOp_colMat]
  rfl

theorem implRow_clean (z₀ : Cfg (VW b)) (hz₀ : D.val z₀ = 0) (x : X) :
    nrun (D.prims (R := R) x) (implLoc N s Query.rowLocation) ∘L cleanEmb (X := AW k b) =
      cleanEmb ∘L GateBinary.prims (R := R) (D.padData z₀ hz₀) (Equiv.refl _) x
        Query.rowLocation := by
  rw [prims_pad_row]
  exact maskCtrl_clean (D.rowOracle x) (D.row_unitary x) (D.rowloc x) D.N_pos D.slots_pos
    (D.row_valid x ⟨0, D.N_pos⟩ ⟨0, D.slots_pos⟩) D.N_lt_pow_succ D.s_lt_pow_succ (D.prims x)
    Query.rowLocation (D.prims_row x)

theorem implCol_clean (z₀ : Cfg (VW b)) (hz₀ : D.val z₀ = 0) (x : X) :
    nrun (D.prims (R := R) x) (implLoc N s Query.columnLocation ++ nGatesOf (swapRegs k b)) ∘L
        cleanEmb (X := AW k b) =
      cleanEmb ∘L GateBinary.prims (R := R) (D.padData z₀ hz₀) (Equiv.refl _) x
        Query.columnLocation := by
  unfold implLoc
  rw [prims_pad_col, nrun_append, nrun_nGatesOf, comp_assoc,
    maskCtrl_clean (D.columnOracle x) (D.column_unitary x) (D.colloc x) D.N_pos D.slots_pos
      (D.column_valid x ⟨0, D.N_pos⟩ ⟨0, D.slots_pos⟩) D.N_lt_pow_succ D.s_lt_pow_succ
      (D.prims x) Query.columnLocation (D.prims_col x),
    ← comp_assoc (gRun (Q := R) (swapRegs k b)), gRun_swapRegs_cleanEmb, comp_assoc]

theorem implValP_clean (z₀ : Cfg (VW b)) (hz₀ : D.val z₀ = 0) (x : X) :
    nrun (D.prims (R := R) x) (implVal N z₀) ∘L cleanEmb (X := AW k b) =
      cleanEmb ∘L GateBinary.prims (R := R) (D.padData z₀ hz₀) (Equiv.refl _) x Query.value := by
  rw [GateBinary.prims_val]
  exact implVal_clean D D.N_lt_pow_succ z₀ x

/-- **The implementations act as the padded primitives on clean ancillas**, for every action of
the supplied locators outside their valid list inputs. -/
theorem implOK (z₀ : Cfg (VW b)) (hz₀ : D.val z₀ = 0) (x : X) :
    ImplOK (D.prims (R := R) x) (GateBinary.prims (R := R) (D.padData z₀ hz₀) (Equiv.refl _) x)
      (implP N s z₀) where
  valid := valid_implP N s z₀
  clean j := by
    cases j with
    | rowLocation => exact implRow_clean D z₀ hz₀ x
    | columnLocation => exact implCol_clean D z₀ hz₀ x
    | value => exact implValP_clean D z₀ hz₀ x

end Clean

end

end SparseHamiltonian.GeneralSparseAccess
