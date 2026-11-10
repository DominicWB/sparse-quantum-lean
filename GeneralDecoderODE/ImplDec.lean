import GeneralDecoderODE.Decode
import GeneralSparseAccess.Subst

/-!
# The decoded oracles from the supplied ones

For sparse access `D : GeneralSparseAccess.QData X N s k b` with a decoder `val` and an exact binary
entry decoding `dc : BinDecode b b' A` (`val w = c₀(X + iY)` for the decoded word `dc.dw w`), the
decoded data `D.decData dc c₀ …` (module `Decode`) are sparse access in the binary format. This
module implements their primitive oracles from the supplied ones (`implDec dc`), on clean ancillas
holding a stored word, a decoded word and the work wires of the decoding:

* the row and column locators: one supplied call of the same kind on the edge wires;
* the value oracle: a supplied value call writes the stored word into the clean stored-word
  ancillas, the decoding circuit computes the decoded word into the clean decoded-word ancillas,
  controlled NOT gates copy it into the value wires, the decoding circuit runs backwards and a second
  supplied value call clears the stored-word ancillas;

`implDec_ok`: on clean ancillas these circuits act as the oracles of the decoded data
(`GeneralSparseAccess.ImplOK`); `kindOK_implDec`, `nGatesN_implDec_le`: at most two supplied calls of
the same kind and `2 |dc| + 2b'` gates per call.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralDecoderODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary
open SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateODE (overwrite_apply_ι overwrite_apply_out localOp_localOp')
open GateOptimalBinary (cfgRun_map classical_map)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

/-! ### Controlled NOT lists -/

section Cnot

variable {W : Type*} [DecidableEq W]

/-- The controlled NOT gate from the wire `s` to the wire `t`. -/
def cnotG (s t : W) : Gate W := ⟨[(s, true)], t, pauliX⟩

theorem flipCfg_cnot (s t : W) (z : Cfg W) (u : W) :
    flipCfg [(s, true)] t z u = if u = t then (z u ^^ z s) else z u := by
  unfold flipCfg ctrlOK
  by_cases hz : z s = true
  · simp only [List.all_cons, List.all_nil, Bool.and_true, hz, beq_self_eq_true, if_true]
    by_cases hu : u = t
    · subst hu
      simp
    · rw [Function.update_of_ne hu, if_neg hu]
  · have hz' : z s = false := by simpa using hz
    simp only [List.all_cons, List.all_nil, Bool.and_true, hz', beq_iff_eq, Bool.false_eq_true,
      if_false, Bool.xor_false, ite_self]

/-- **A list of controlled NOT gates** from distinct sources to distinct targets, no target a
source: every target is XOR-ed with its source, and no other wire changes. -/
theorem cfgRun_cnots {ι : Type*} (src tgt : ι → W) (htgt : Function.Injective tgt)
    (hst : ∀ i j, src i ≠ tgt j) (L : List ι) (hL : L.Nodup) (z : Cfg W) :
    (∀ i ∈ L, cfgRun (L.map (fun i => cnotG (src i) (tgt i))) z (tgt i) = (z (tgt i) ^^ z (src i))) ∧
    (∀ u, (∀ i ∈ L, tgt i ≠ u) → cfgRun (L.map (fun i => cnotG (src i) (tgt i))) z u = z u) := by
  induction L generalizing z with
  | nil => exact ⟨fun i hi => absurd hi List.not_mem_nil, fun _ _ => rfl⟩
  | cons i0 L ih =>
      rw [List.nodup_cons] at hL
      have e : cfgRun ((i0 :: L).map (fun i => cnotG (src i) (tgt i))) z =
          cfgRun (L.map (fun i => cnotG (src i) (tgt i))) (flipCfg [(src i0, true)] (tgt i0) z) :=
        rfl
      rw [e]
      obtain ⟨ha, hb⟩ := ih hL.2 (flipCfg [(src i0, true)] (tgt i0) z)
      have hz1 := flipCfg_cnot (src i0) (tgt i0) z
      refine ⟨fun i hi => ?_, fun u hu => ?_⟩
      · rcases List.mem_cons.mp hi with rfl | hi'
        · have hout : ∀ j ∈ L, tgt j ≠ tgt i := fun j hj h => hL.1 (htgt h ▸ hj)
          rw [hb _ hout, hz1, if_pos rfl]
        · have hne : i ≠ i0 := fun h => hL.1 (h ▸ hi')
          have ht : tgt i ≠ tgt i0 := fun h => hne (htgt h)
          rw [ha i hi', hz1, if_neg ht, hz1, if_neg (hst i i0)]
      · have hu0 : u ≠ tgt i0 := fun h => hu i0 List.mem_cons_self h.symm
        rw [hb u (fun j hj => hu j (List.mem_cons_of_mem i0 hj)), hz1, if_neg hu0]

omit [DecidableEq W] in
theorem classical_cnots {ι : Type*} (src tgt : ι → W) (hst : ∀ i j, src i ≠ tgt j) (L : List ι) :
    Classical (L.map (fun i => cnotG (src i) (tgt i))) := by
  intro g hg
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg
  refine ⟨rfl, ?_⟩
  intro c hc
  simp only [cnotG, List.mem_cons, List.not_mem_nil, or_false] at hc
  rw [hc]
  exact hst i i

omit [DecidableEq W] in
theorem gateOK_cnots {ι : Type*} (src tgt : ι → W) (hst : ∀ i j, src i ≠ tgt j) (L : List ι) :
    ∀ g ∈ L.map (fun i => cnotG (src i) (tgt i)), GateOK 3 g := by
  intro g hg
  have hc := classical_cnots src tgt hst L g hg
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg
  exact ⟨by simp [cnotG], hc.2, by rw [hc.1]; exact pauliX_unitary⟩

end Cnot

/-! ### The implementation -/

section Impl

variable {k b b' A : ℕ}

/-- **The wires of the implementation**: the register of the decoded oracles (the edge wires and
the decoded value wires) and, as ancillas, the wires of the decoding circuit (the stored word, the
decoded word and the work wires). -/
abbrev IDW (k b b' A : ℕ) := PY k b' ⊕ DW b b' A

theorem posD_injective : Function.Injective
    (Sum.elim (fun e => Sum.inl (Sum.inl e)) (fun v => Sum.inr (Sum.inl v)) :
      PY k b → IDW k b b' A) := by
  rintro (e | v) (e' | v') h <;> simp_all

/-- **The position of a supplied call**: the edge wires and the stored-word ancillas. -/
def posD : PY k b ↪ IDW k b b' A :=
  ⟨Sum.elim (fun e => Sum.inl (Sum.inl e)) (fun v => Sum.inr (Sum.inl v)), posD_injective⟩

/-- The decoding circuit on the ancillas. -/
def decG (dc : BinDecode b b' A) : List (Gate (IDW k b b' A)) :=
  dc.circ.map (GateODE.Gate.map Sum.inr)

/-- The decoded-word ancilla `v`. -/
abbrev tmW (v : VW b') : IDW k b b' A := Sum.inr (Sum.inr (Sum.inl v))

/-- The decoded value wire `v`. -/
abbrev vdW (v : VW b') : IDW k b b' A := Sum.inl (Sum.inr v)

/-- **The copy of the decoded word into the value wires.** -/
def outGates (k b b' A : ℕ) : List (Gate (IDW k b b' A)) :=
  (Finset.univ : Finset (VW b')).toList.map (fun v => cnotG (tmW v) (vdW v))

theorem tmW_ne_vdW (v v' : VW b') : (tmW v : IDW k b b' A) ≠ vdW v' := Sum.inr_ne_inl

theorem vdW_injective : Function.Injective (vdW : VW b' → IDW k b b' A) :=
  fun _ _ h => Sum.inr_injective (Sum.inl_injective h)

/-- **The implementation of the oracles of the decoded data** from the supplied ones: a supplied
locator call on the edge wires; for the value oracle, a supplied value call into the stored-word
ancillas, the decoding, the copy of the decoded word into the value wires, the decoding backwards
and a second supplied value call. -/
def implDec (dc : BinDecode b b' A) : Query → List (NInstr (IDW k b b' A) (PY k b) Query)
  | .rowLocation => [NInstr.call Query.rowLocation false posD]
  | .columnLocation => [NInstr.call Query.columnLocation false posD]
  | .value => [NInstr.call Query.value false posD] ++ nGatesOf (decG dc) ++
      nGatesOf (outGates k b b' A) ++ nGatesOf (decG dc).reverse ++
      [NInstr.call Query.value false posD]

/-! ### Counts -/

theorem length_outGates : (outGates k b b' A).length = 2 * b' := by
  unfold outGates
  rw [List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_sum, Fintype.card_fin]
  ring

/-- **At most `2 |dc| + 2b'` gates per call.** -/
theorem nGatesN_implDec_le (dc : BinDecode b b' A) (j : Query) :
    nGatesN (implDec (k := k) dc j) ≤ 2 * dc.circ.length + 2 * b' := by
  cases j with
  | rowLocation => simp [implDec, nGatesN, NInstr.isGate]
  | columnLocation => simp [implDec, nGatesN, NInstr.isGate]
  | value =>
      simp only [implDec, nGatesN_append, nGatesN_nGatesOf, decG, List.length_reverse,
        List.length_map, length_outGates]
      have h : nGatesN ([NInstr.call Query.value false posD] :
          List (NInstr (IDW k b b' A) (PY k b) Query)) = 0 := by
        simp [nGatesN, NInstr.isGate]
      rw [h]
      omega

/-- **At most two supplied calls, all of the kind of the call.** -/
theorem kindOK_implDec (dc : BinDecode b b' A) : KindOK (implDec (k := k) dc) id 2 where
  kind_eq j q hq j' adj pos he := by
    subst he
    cases j with
    | rowLocation =>
        simp only [implDec, List.mem_singleton] at hq
        cases hq
        rfl
    | columnLocation =>
        simp only [implDec, List.mem_singleton] at hq
        cases hq
        rfl
    | value =>
        simp only [implDec, List.mem_append, List.mem_singleton, nGatesOf, List.mem_map] at hq
        rcases hq with (((h | ⟨_, _, h⟩) | ⟨_, _, h⟩) | ⟨_, _, h⟩) | h
        · cases h
          rfl
        · cases h
        · cases h
        · cases h
        · cases h
          rfl
  count j := by
    cases j with
    | rowLocation => simp [implDec, nCallsN, NInstr.isCall]
    | columnLocation => simp [implDec, nCallsN, NInstr.isCall]
    | value =>
        simp only [implDec, nCallsN_append, nCallsN_nGatesOf]
        simp [nCallsN, NInstr.isCall]

/-! ### Validity -/

theorem classical_decG (dc : BinDecode b b' A) : Classical (decG (k := k) dc) :=
  classical_map Sum.inr_injective dc.classical

theorem classical_outGates : Classical (outGates k b b' A) :=
  classical_cnots _ _ (fun v v' => tmW_ne_vdW v v') _

theorem valid_decG (dc : BinDecode b b' A) :
    ∀ i ∈ nGatesOf (Y := PY k b) (J := Query) (decG (k := k) dc), i.Valid := by
  intro i hi
  simp only [nGatesOf, decG, List.map_map, List.mem_map, Function.comp_apply] at hi
  obtain ⟨g, hg, rfl⟩ := hi
  exact NInstr.valid_map ⟨Sum.inr, Sum.inr_injective⟩ (NInstr.gate g : NInstr (DW b b' A) (PY k b)
    Query) (dc.gateOK g hg)

theorem valid_decG_rev (dc : BinDecode b b' A) :
    ∀ i ∈ nGatesOf (Y := PY k b) (J := Query) (decG (k := k) dc).reverse, i.Valid := by
  intro i hi
  simp only [nGatesOf, List.mem_map, List.mem_reverse] at hi
  obtain ⟨g, hg, rfl⟩ := hi
  exact valid_decG dc _ (List.mem_map_of_mem hg)

theorem valid_implDec (dc : BinDecode b b' A) : ∀ j, ∀ i ∈ implDec (k := k) dc j, i.Valid := by
  intro j i hi
  cases j with
  | rowLocation =>
      simp only [implDec, List.mem_singleton] at hi
      subst hi
      trivial
  | columnLocation =>
      simp only [implDec, List.mem_singleton] at hi
      subst hi
      trivial
  | value =>
      simp only [implDec, List.mem_append, List.mem_singleton] at hi
      rcases hi with (((h | h) | h) | h) | h
      · subst h
        trivial
      · exact valid_decG dc i h
      · exact valid_nGatesOf _ (gateOK_cnots _ _ (fun v v' => tmW_ne_vdW v v') _) i h
      · exact valid_decG_rev dc i h
      · subst h
        trivial

end Impl

/-! ### The circuits on clean ancillas -/

section Clean

variable {X : Type*} {N s k b b' A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

theorem posD_inl (e : EW k) :
    (posD (k := k) (b := b) (b' := b') (A := A) (Sum.inl e)) = Sum.inl (Sum.inl e) := rfl

theorem posD_inr (w : VW b) :
    (posD (k := k) (b := b) (b' := b') (A := A) (Sum.inr w)) = Sum.inr (Sum.inl w) := rfl

/-- **A supplied locator call on clean ancillas**: an operator on the edge wires of the supplied
register acts as the same operator on the edge wires of the decoded register. -/
theorem edgeCall_clean (G : Reg (EW k) R →L[ℂ] Reg (EW k) R) :
    localOp (posD (k := k) (b := b) (b' := b') (A := A)) posD.injective
        (fun _ => localOp (Sum.inl : EW k → PY k b) Sum.inl_injective (fun _ => G)) ∘L
        cleanEmb (X := DW b b' A) =
      cleanEmb ∘L localOp (Sum.inl : EW k → PY k b') Sum.inl_injective (fun _ => G) := by
  have hρ : Function.Injective (fun e : EW k => (Sum.inl (Sum.inl e) : IDW k b b' A)) :=
    fun _ _ h => Sum.inl_injective (Sum.inl_injective h)
  rw [← liftB_cleanEmb]
  unfold liftB
  rw [localOp_localOp' posD.injective Sum.inl_injective _ hρ (fun _ => rfl),
    localOp_localOp' (Sum.inl_injective : Function.Injective
      (Sum.inl : PY k b' → IDW k b b' A)) Sum.inl_injective _ hρ (fun _ => rfl)]

variable (D : QData X N s k b) (dc : BinDecode b b' A) (c₀ : ℝ) (hc₀ : 0 < c₀)
  (hdc : dc.Exact D.val c₀)

/-- A supplied value call on a basis state. -/
theorem nrun_valCallD (x : X) (z : Cfg (IDW k b b' A)) (q : R) :
    nrun (D.prims (R := R) x) [NInstr.call Query.value false posD] (bas z q) =
      bas (alongEquiv posD (xorEquiv (fun d => D.table x d)) z) q := by
  rw [nrun_singleton, NInstr.eval_call]
  change localOp posD posD.injective (fun _ => D.prims x Query.value) (bas z q) = _
  rw [D.prims_val, localOp_permOp, permOp_bas]

/-- **The first supplied value call** writes the stored word into the clean stored-word ancillas. -/
theorem valCallD_clean (x : X) (y : Cfg (PY k b')) :
    alongEquiv (posD (b' := b') (A := A)) (xorEquiv (fun d => D.table x d))
        (Sum.elim y (fun _ => false)) =
      Sum.elim y (Sum.elim (D.table x (fun e => y (Sum.inl e))) (fun _ => false)) := by
  funext u
  rcases u with (e | v) | (w | c)
  · change alongEquiv posD _ _ (posD (Sum.inl e)) = _
    rw [alongEquiv_apply_in]
    rfl
  · rw [alongEquiv_apply_out posD _ _ (Sum.inl (Sum.inr v))
      (by rintro (e | w) h <;> simp [posD_inl, posD_inr] at h)]
    rfl
  · change alongEquiv posD _ _ (posD (Sum.inr w)) = _
    rw [alongEquiv_apply_in]
    exact Bool.false_xor _
  · rw [alongEquiv_apply_out posD _ _ (Sum.inr (Sum.inr c))
      (by rintro (e | w) h <;> simp [posD_inl, posD_inr] at h)]
    rfl

/-- **The second supplied value call** clears the stored-word ancillas. -/
theorem valCallD_restore (x : X) (y : Cfg (PY k b')) (w : Cfg (VW b))
    (hw : w = D.table x (fun e => y (Sum.inl e))) :
    alongEquiv (posD (b' := b') (A := A)) (xorEquiv (fun d => D.table x d))
        (Sum.elim y (Sum.elim w (fun _ => false))) = Sum.elim y (fun _ => false) := by
  subst hw
  funext u
  rcases u with (e | v) | (w | c)
  · change alongEquiv posD _ _ (posD (Sum.inl e)) = _
    rw [alongEquiv_apply_in]
    rfl
  · rw [alongEquiv_apply_out posD _ _ (Sum.inl (Sum.inr v))
      (by rintro (e | w) h <;> simp [posD_inl, posD_inr] at h)]
    rfl
  · change alongEquiv posD _ _ (posD (Sum.inr w)) = _
    rw [alongEquiv_apply_in]
    exact Bool.xor_self _
  · rw [alongEquiv_apply_out posD _ _ (Sum.inr (Sum.inr c))
      (by rintro (e | w) h <;> simp [posD_inl, posD_inr] at h)]
    rfl

/-- **The decoding** writes the decoded word into the clean decoded-word ancillas. -/
theorem cfgRun_decG (y : Cfg (PY k b')) (w : Cfg (VW b)) :
    cfgRun (decG (k := k) dc) (Sum.elim y (Sum.elim w (fun _ => false))) =
      Sum.elim y (Sum.elim w (Sum.elim (dc.dw w) (fun _ => false))) := by
  unfold decG
  rw [cfgRun_map Sum.inr_injective]
  have h : (fun a => (Sum.elim y (Sum.elim w (fun _ => false)) : Cfg (IDW k b b' A))
      (Sum.inr a)) = Sum.elim w (fun _ => false) := rfl
  rw [h, dc.compute]
  funext u
  rcases u with u | u
  · exact overwrite_apply_out _ _ _ _ (fun a h => by cases h)
  · exact overwrite_apply_ι Sum.inr_injective _ _ u

/-- **The decoding backwards** clears the decoded-word ancillas. -/
theorem cfgRun_decG_rev (y : Cfg (PY k b')) (w : Cfg (VW b)) :
    cfgRun (decG (k := k) dc).reverse
        (Sum.elim y (Sum.elim w (Sum.elim (dc.dw w) (fun _ => false)))) =
      Sum.elim y (Sum.elim w (fun _ => false)) := by
  rw [← cfgRun_decG dc y w]
  exact cfgRun_reverse_cancel _ (classical_decG dc) _

/-- **The copy of the decoded word** into the value wires. -/
theorem cfgRun_outGates (y : Cfg (PY k b')) (w : Cfg (VW b)) (d : Cfg (VW b')) :
    cfgRun (outGates k b b' A) (Sum.elim y (Sum.elim w (Sum.elim d (fun _ => false)))) =
      Sum.elim (Sum.elim (fun e => y (Sum.inl e)) (fun v => y (Sum.inr v) ^^ d v))
        (Sum.elim w (Sum.elim d (fun _ => false))) := by
  obtain ⟨ha, hb⟩ := cfgRun_cnots (tmW (k := k) (b := b) (A := A)) vdW vdW_injective
    (fun v v' => tmW_ne_vdW v v') (Finset.univ : Finset (VW b')).toList (Finset.nodup_toList _)
    (Sum.elim y (Sum.elim w (Sum.elim d (fun _ => false))))
  funext u
  rcases u with (e | v) | u
  · rw [outGates, hb _ (fun v _ h => by simp at h)]
    rfl
  · change cfgRun (outGates k b b' A) _ (vdW v) = _
    rw [outGates, ha v (Finset.mem_toList.mpr (Finset.mem_univ v))]
    rfl
  · rw [outGates, hb _ (fun v _ h => by simp at h)]
    rfl

theorem classical_decG_rev : Classical (decG (k := k) dc).reverse :=
  fun g hg => classical_decG dc g (List.mem_reverse.mp hg)

/-- **The value oracle of the decoded data on clean ancillas.** -/
theorem implDec_value_clean (x : X) :
    nrun (D.prims (R := R) x) (implDec (k := k) dc Query.value) ∘L cleanEmb (X := DW b b' A) =
      cleanEmb ∘L (D.decData dc c₀ hc₀ hdc).prims (R := R) x Query.value := by
  apply ext_bas_clm'
  intro y q
  rw [comp_apply, comp_apply, cleanEmb_bas, QData.prims_val, permOp_bas, cleanEmb_bas]
  simp only [implDec]
  rw [nrun_append, nrun_append, nrun_append, nrun_append, comp_apply, comp_apply, comp_apply,
    comp_apply]
  simp only [nrun_nGatesOf]
  rw [nrun_valCallD, gRun_classical_bas _ (classical_decG dc),
    gRun_classical_bas _ classical_outGates, gRun_classical_bas _ (classical_decG_rev dc),
    nrun_valCallD]
  congr 1
  rw [valCallD_clean, cfgRun_decG, cfgRun_outGates, cfgRun_decG_rev,
    valCallD_restore D x _ _ (by rfl)]
  congr 1

/-- **The decoded oracles from the supplied ones**: on clean ancillas, `implDec dc` acts as the
oracles of the decoded data. -/
theorem implDec_ok (x : X) :
    ImplOK (D.prims (R := R) x) ((D.decData dc c₀ hc₀ hdc).prims (R := R) x)
      (implDec (k := k) dc) where
  valid := valid_implDec dc
  clean j := by
    cases j with
    | rowLocation =>
        rw [show implDec (k := k) dc Query.rowLocation =
          [NInstr.call Query.rowLocation false posD] from rfl, nrun_singleton, NInstr.eval_call]
        change localOp posD posD.injective (fun _ => D.prims (R := R) x Query.rowLocation) ∘L
          cleanEmb = _
        rw [QData.prims_row, QData.prims_row, QData.decData_rowOracle]
        exact edgeCall_clean _
    | columnLocation =>
        rw [show implDec (k := k) dc Query.columnLocation =
          [NInstr.call Query.columnLocation false posD] from rfl, nrun_singleton,
          NInstr.eval_call]
        change localOp posD posD.injective (fun _ => D.prims (R := R) x Query.columnLocation) ∘L
          cleanEmb = _
        rw [QData.prims_col, QData.prims_col, QData.decData_columnOracle]
        exact edgeCall_clean _
    | value => exact implDec_value_clean D dc c₀ hc₀ hdc x

end Clean

end

end SparseHamiltonian.GeneralDecoderODE
