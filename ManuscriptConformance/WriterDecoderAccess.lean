import ManuscriptConformance.WriterGateAccess
import GeneralDecoderODE.Decoder

/-!
# The padded oracles of the decoded data from a writer (handover item B4)

The ODE gate theorems for a decoder with an exact binary entry decoding (`GeneralDecoderODE`)
implement the padded oracles of the decoded data `D.decData dc …` from the supplied ones through
the composite `implDP = implComp (implP N s z₀) (implDec dc)`: every decoded value call of the
padded value oracle `implVal` (the validity flag, two decoded value calls around the copy masked by
the flag) is implemented by a supplied value call into clean stored-word ancillas, the decoding,
the copy of the decoded word into the target, the decoding backwards and a second supplied value
call (`implDec`).

With a writer of the stored words on valid clean inputs (`GeneralSparseAccess.QData.Writer`), the
second supplied call is the inverse writer (`implDecW`; `implDPW = implComp (implP N s z₀)
(implDecW dc)`): the same gates and calls (`nGatesN_implDPW_le`, `kindOK_implDPW`). A decoded value
call through `implDecW` acts, on clean decoding ancillas and a valid pair, as the decoded XOR on any
target (`decW_valid`, `cval_valid`), but on an invalid pair the writer is unconstrained, so it is
not an implementation of the decoded oracle. It is an involution on the whole register
(`decW_invol`: writer, decoding, copy, decoding backwards, inverse writer, twice). In the padded
value oracle the two decoded calls surround the copy masked by the validity flag, which on an
invalid pair does not read their wires (`nrun_copyD_put`): there the second call undoes the first
(`cmid_invalid`; on a valid pair `cmid_valid`). So the composite acts on clean ancillas as the
padded value oracle of the decoded data (`compW_bas`, `compW_value`), and `implDPW` implements the
padded oracles of the decoded data (`implOK_implDPW`; the locators through `implDPW_eq`,
`nrun_implDP_eq`), for every unitary action of the writer outside its valid clean inputs.
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
open SparseHamiltonian.GateODE (put put_apply overwrite_apply_ι overwrite_apply_out adjIf
  localOp_put)
open GateOptimalBinary (cfgRun_map classical_map)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

/-! ### The decoded oracles from a writer -/

section ImplW

variable {k b b' A : ℕ}

/-- **The decoded oracles from a writer**: the supplied locator calls of `implDec`; for the value
oracle, the writer into the clean stored-word ancillas, the decoding, the copy of the decoded word
into the target, the decoding backwards and the inverse writer. -/
def implDecW (dc : BinDecode b b' A) : Query → List (NInstr (IDW k b b' A) (PY k b) Query)
  | .rowLocation => [NInstr.call Query.rowLocation false posD]
  | .columnLocation => [NInstr.call Query.columnLocation false posD]
  | .value => [NInstr.call Query.value false posD] ++ nGatesOf (decG dc) ++
      nGatesOf (outGates k b b' A) ++ nGatesOf (decG dc).reverse ++
      [NInstr.call Query.value true posD]

/-- **The padded oracles of the decoded data from a writer**: `implP` of the decoded data with every
decoded call implemented by `implDecW`. -/
def implDPW (N s : ℕ) (z₀ : Cfg (VW b')) (dc : BinDecode b b' A) :
    Query → List (NInstr (PY (k + 1) b' ⊕ (GeneralSparseAccess.AW k b' ⊕ DW b b' A))
      (PY k b) Query) :=
  implComp (implP (k := k) (b := b') N s z₀) (implDecW (k := k) dc)

theorem nGatesN_implDecW_le (dc : BinDecode b b' A) (j : Query) :
    nGatesN (implDecW (k := k) dc j) ≤ 2 * dc.circ.length + 2 * b' := by
  cases j with
  | rowLocation => simp [implDecW, nGatesN, NInstr.isGate]
  | columnLocation => simp [implDecW, nGatesN, NInstr.isGate]
  | value =>
      simp only [implDecW, nGatesN_append, nGatesN_nGatesOf, decG, List.length_reverse,
        List.length_map, length_outGates]
      have h : ∀ adj, nGatesN ([NInstr.call Query.value adj posD] :
          List (NInstr (IDW k b b' A) (PY k b) Query)) = 0 := fun adj => by
        simp [nGatesN, NInstr.isGate]
      rw [h, h]
      omega

theorem kindOK_implDecW (dc : BinDecode b b' A) : KindOK (implDecW (k := k) dc) id 2 where
  kind_eq j q hq j' adj pos he := by
    subst he
    cases j with
    | rowLocation =>
        simp only [implDecW, List.mem_singleton] at hq
        cases hq
        rfl
    | columnLocation =>
        simp only [implDecW, List.mem_singleton] at hq
        cases hq
        rfl
    | value =>
        simp only [implDecW, List.mem_append, List.mem_singleton, nGatesOf, List.mem_map] at hq
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
    | rowLocation => simp [implDecW, nCallsN, NInstr.isCall]
    | columnLocation => simp [implDecW, nCallsN, NInstr.isCall]
    | value =>
        simp only [implDecW, nCallsN_append, nCallsN_nGatesOf]
        simp [nCallsN, NInstr.isCall]

theorem valid_implDecW (dc : BinDecode b b' A) : ∀ j, ∀ i ∈ implDecW (k := k) dc j, i.Valid := by
  intro j i hi
  cases j with
  | rowLocation =>
      simp only [implDecW, List.mem_singleton] at hi
      subst hi
      trivial
  | columnLocation =>
      simp only [implDecW, List.mem_singleton] at hi
      subst hi
      trivial
  | value =>
      simp only [implDecW, List.mem_append, List.mem_singleton] at hi
      rcases hi with (((h | h) | h) | h) | h
      · subst h
        trivial
      · exact valid_decG dc i h
      · exact valid_nGatesOf _ (gateOK_cnots _ _ (fun v v' => tmW_ne_vdW v v') _) i h
      · exact valid_decG_rev dc i h
      · subst h
        trivial

theorem valid_implDPW (N s : ℕ) (z₀ : Cfg (VW b')) (dc : BinDecode b b' A) :
    ∀ j, ∀ i ∈ implDPW (k := k) N s z₀ dc j, i.Valid := by
  intro j i hi
  obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
  exact NInstr.valid_map assocE i'
    (valid_subst (valid_implDecW dc) _ (valid_implP N s z₀ j) i' hi')

/-- **At most `implG k b' + 3 (2 |dc| + 2b')` gates per padded call**, as for `implDP`. -/
theorem nGatesN_implDPW_le (N s : ℕ) (z₀ : Cfg (VW b')) (dc : BinDecode b b' A) (j : Query) :
    nGatesN (implDPW (k := k) N s z₀ dc j) ≤ implDG k b' dc :=
  nGatesN_implComp_le _ _ (implG k b') (2 * dc.circ.length + 2 * b') 3
    (nGatesN_implP_le N s z₀) (nGatesN_implDecW_le dc) (kindOK_implP N s z₀) j

/-- **At most six calls per padded call, all of its kind** (the writer and the inverse writer for
the value oracle), as for `implDP`. -/
theorem kindOK_implDPW (N s : ℕ) (z₀ : Cfg (VW b')) (dc : BinDecode b b' A) :
    KindOK (implDPW (k := k) N s z₀ dc) id 6 :=
  kindOK_comp_id (kindOK_implP N s z₀) (kindOK_implDecW dc)

end ImplW

/-! ### A decoded value call through the writer -/

section DecW

variable {X : Type*} {N s k b b' A : ℕ} {D : QData X N s k b} (Wr : D.Writer)
  (dc : BinDecode b b' A)
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- Two operators composing to the identity cancel inside a composition. -/
theorem comp_cancel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {U V : E →L[ℂ] E} (h : U ∘L V = 1) (W : E →L[ℂ] E) : U ∘L (V ∘L W) = W := by
  rw [← comp_assoc, h]
  rfl

/-- A classical gate list followed by its reverse is the identity. -/
theorem gRun_reverse_comp (gs : List (Gate (IDW k b b' A))) (h : Classical gs) :
    gRun (Q := R) gs.reverse ∘L gRun gs = 1 := by
  apply ext_bas_clm'
  intro z q
  rw [comp_apply, gRun_classical_bas _ h, gRun_classical_bas _ (fun g hg => h g
    (List.mem_reverse.mp hg)), cfgRun_reverse_cancel _ h]
  rfl

theorem gRun_comp_reverse (gs : List (Gate (IDW k b b' A))) (h : Classical gs) :
    gRun (Q := R) gs ∘L gRun gs.reverse = 1 := by
  have h' : Classical gs.reverse := fun g hg => h g (List.mem_reverse.mp hg)
  have := gRun_reverse_comp (R := R) gs.reverse h'
  rwa [List.reverse_reverse] at this

/-- The copy of the decoded word is an involution. -/
theorem gRun_outGates_twice :
    gRun (Q := R) (outGates k b b' A) ∘L gRun (outGates k b b' A) = 1 := by
  apply ext_bas_clm'
  intro z q
  rw [comp_apply, gRun_classical_bas _ classical_outGates,
    gRun_classical_bas _ classical_outGates]
  congr 1
  unfold outGates
  set G := (Finset.univ : Finset (VW b')).toList.map
    (fun v => cnotG (tmW (k := k) (b := b) (A := A) v) (vdW v)) with hG
  obtain ⟨ha, hb⟩ := cfgRun_cnots (tmW (k := k) (b := b) (A := A)) vdW vdW_injective
    (fun v v' => tmW_ne_vdW v v') (Finset.univ : Finset (VW b')).toList (Finset.nodup_toList _) z
  obtain ⟨ha', hb'⟩ := cfgRun_cnots (tmW (k := k) (b := b) (A := A)) vdW vdW_injective
    (fun v v' => tmW_ne_vdW v v') (Finset.univ : Finset (VW b')).toList (Finset.nodup_toList _)
    (cfgRun G z)
  rw [← hG] at ha hb ha' hb'
  funext u
  by_cases hu : ∃ v, vdW v = u
  · obtain ⟨v, rfl⟩ := hu
    have hm := Finset.mem_toList.mpr (Finset.mem_univ v)
    rw [ha' v hm, hb (tmW v) (fun v' _ h => tmW_ne_vdW v v' h.symm), ha v hm, Bool.xor_assoc,
      Bool.xor_self, Bool.xor_false]
  · have hu' : ∀ v ∈ (Finset.univ : Finset (VW b')).toList, vdW v ≠ u := fun v _ h => hu ⟨v, h⟩
    rw [hb' u hu', hb u hu']

/-- **A decoded value call through the writer is an involution** on the whole register. -/
theorem decW_invol (x : X) :
    nrun (Wr.prims (R := R) x) (implDecW (k := k) dc Query.value) ∘L
      nrun (Wr.prims (R := R) x) (implDecW (k := k) dc Query.value) = 1 := by
  set L := localOp (posD (k := k) (b := b) (b' := b') (A := A)) posD.injective
    (fun _ => qlift (R := R) (Equiv.refl (Cfg (PY k b))) (Wr.op x)) with hL
  have hW1 : nrun (Wr.prims (R := R) x) ([NInstr.call Query.value false posD] :
      List (NInstr (IDW k b b' A) (PY k b) Query)) = L := by
    rw [nrun_singleton, NInstr.eval_call]
    rfl
  have hW2 : nrun (Wr.prims (R := R) x) ([NInstr.call Query.value true posD] :
      List (NInstr (IDW k b b' A) (PY k b) Query)) = L† := by
    rw [nrun_singleton, NInstr.eval_call, hL, localOp_adjoint]
    rfl
  have hLu : IsUnitary L := localOp_isUnitary _ _ (fun _ => qlift_isUnitary _ (Wr.unitary x))
  have hLL : L ∘L L† = 1 := by
    have h := hLu.2
    rwa [star_eq_adjoint, mul_def] at h
  have hLtL : L† ∘L L = 1 := by
    have h := hLu.1
    rwa [star_eq_adjoint, mul_def] at h
  have hG1 := gRun_reverse_comp (R := R) (decG (k := k) dc) (classical_decG dc)
  have hG2 := gRun_comp_reverse (R := R) (decG (k := k) dc) (classical_decG dc)
  have hO := gRun_outGates_twice (R := R) (k := k) (b := b) (b' := b') (A := A)
  simp only [implDecW, nrun_append, nrun_nGatesOf, hW1, hW2, comp_assoc]
  rw [comp_cancel hLL, comp_cancel hG2, comp_cancel hO, comp_cancel hG1, hLtL]

theorem posD_local (z : Cfg (IDW k b b' A)) :
    (fun a => z (posD (k := k) (b := b) (b' := b') (A := A) a)) =
      Sum.elim (fun e => z (Sum.inl (Sum.inl e))) (fun w => z (Sum.inr (Sum.inl w))) := by
  funext a
  rcases a with e | w <;> rfl

/-- **A decoded value call through the writer on a valid pair**: on clean decoding ancillas, for a
valid pair of index words and any target, the XOR of the decoded word, the ancillas restored. -/
theorem decW_valid (x : X) (i j : Fin N) (y : Cfg (PY k b'))
    (hy : (fun e => y (Sum.inl e)) = edgeW k (binW k i) (binW k j)) (q : R) :
    nrun (Wr.prims (R := R) x) (implDecW (k := k) dc Query.value)
        (bas (Sum.elim y (fun _ => false)) q) =
      bas (Sum.elim (Sum.elim (fun e => y (Sum.inl e))
        (fun v => y (Sum.inr v) ^^ dc.dw (D.table x (edgeW k (binW k i) (binW k j))) v))
        (fun _ => false)) q := by
  set ad := edgeW k (binW k i) (binW k j) with had
  set w := D.table x ad with hw
  have hcc : (starRingEnd ℂ) (Wr.phase x i j) * Wr.phase x i j = 1 := by
    rw [Complex.conj_mul', Wr.norm_phase]
    norm_num
  have hcall : ∀ (adj : Bool) (z : Cfg (IDW k b b' A)) (q' : R),
      nrun (Wr.prims (R := R) x) ([NInstr.call Query.value adj posD] :
        List (NInstr (IDW k b b' A) (PY k b) Query)) (bas z q') =
      put posD posD.injective z (adjIf adj (qlift (Equiv.refl _) (Wr.op x))
        (bas (fun a => z (posD a)) q')) := fun adj z q' => by
    rw [nrun_singleton, NInstr.eval_call, localOp_bas]
    rfl
  simp only [implDecW, nrun_append, comp_apply, nrun_nGatesOf]
  -- the writer
  have hl1 : (fun a => (Sum.elim y (fun _ => false) : Cfg (IDW k b b' A)) (posD a)) =
      Sum.elim ad (fun _ => false) := by
    rw [posD_local]
    congr 1
  rw [hcall, hl1]
  rw [show adjIf false (qlift (R := R) (Equiv.refl (Cfg (PY k b))) (Wr.op x)) =
    qlift (Equiv.refl (Cfg (PY k b))) (Wr.op x) from rfl]
  rw [qlift_refl_bas _ _ _ _ (Wr.write x i j), put_bas]
  have ho1 : overwrite posD (Sum.elim y (fun _ => false) : Cfg (IDW k b b' A))
      (Sum.elim ad w) = Sum.elim y (Sum.elim w (fun _ => false)) := by
    funext u
    rcases u with (e | v) | (w' | c)
    · change overwrite posD _ _ (posD (Sum.inl e)) = _
      rw [overwrite_apply_ι posD.injective]
      exact (congrFun hy e).symm
    · rw [overwrite_apply_out posD _ _ _
        (by rintro (e | w') h <;> simp [posD_inl, posD_inr] at h)]
      rfl
    · change overwrite posD _ _ (posD (Sum.inr w')) = _
      rw [overwrite_apply_ι posD.injective]
      rfl
    · rw [overwrite_apply_out posD _ _ _
        (by rintro (e | w') h <;> simp [posD_inl, posD_inr] at h)]
      rfl
  rw [ho1]
  -- the decoding, the copy and the decoding backwards
  rw [gRun_classical_bas _ (classical_decG dc), cfgRun_decG,
    gRun_classical_bas _ classical_outGates, cfgRun_outGates,
    gRun_classical_bas _ (classical_decG_rev dc)]
  set y' : Cfg (PY k b') := Sum.elim (fun e => y (Sum.inl e)) (fun v => y (Sum.inr v) ^^ dc.dw w v)
    with hy'
  have hy'e : (fun e => y' (Sum.inl e)) = fun e => y (Sum.inl e) := rfl
  rw [show (Sum.elim (Sum.elim (fun e => y (Sum.inl e)) (fun v => y (Sum.inr v) ^^ dc.dw w v))
      (Sum.elim w (Sum.elim (dc.dw w) (fun _ => false))) : Cfg (IDW k b b' A)) =
      Sum.elim y' (Sum.elim w (Sum.elim (dc.dw w) (fun _ => false))) from rfl,
    cfgRun_decG_rev dc y' w]
  -- the inverse writer
  have hl2 : (fun a => (Sum.elim y' (Sum.elim w (fun _ => false)) : Cfg (IDW k b b' A)) (posD a)) =
      Sum.elim ad w := by
    rw [posD_local]
    congr 1
  rw [hcall, hl2]
  rw [show adjIf true (qlift (R := R) (Equiv.refl (Cfg (PY k b))) (Wr.op x)) =
    (qlift (Equiv.refl (Cfg (PY k b))) (Wr.op x))† from rfl]
  rw [← qlift_adjoint, qlift_refl_bas _ _ _ _ (Wr.adjoint_write x i j), put_bas, smul_smul, hcc,
    one_smul]
  congr 1
  funext u
  rcases u with (e | v) | (w' | c)
  · change overwrite posD _ _ (posD (Sum.inl e)) = _
    rw [overwrite_apply_ι posD.injective]
    exact (congrFun (hy'e.trans hy) e).symm
  · rw [overwrite_apply_out posD _ _ _
      (by rintro (e | w') h <;> simp [posD_inl, posD_inr] at h)]
    rfl
  · change overwrite posD _ _ (posD (Sum.inr w')) = _
    rw [overwrite_apply_ι posD.injective]
    rfl
  · rw [overwrite_apply_out posD _ _ _
      (by rintro (e | w') h <;> simp [posD_inl, posD_inr] at h)]
    rfl

end DecW

/-! ### The padded value oracle of the decoded data from a writer -/

section CompW

open SparseHamiltonian.GeneralSparseAccess.IW
open SparseHamiltonian.GatePointerEncoding (wordValue)

/-- A substituted gate list: the gates renamed onto the wires of the circuit. -/
theorem subst_nGatesOf {V Y Y' J J' A' : Type*} (impl : J' → List (NInstr (Y' ⊕ A') Y J))
    (gs : List (Gate V)) :
    subst impl (nGatesOf (Y := Y') (J := J') gs) =
      nGatesOf (gs.map (GateODE.Gate.map (Sum.inl : V → V ⊕ A'))) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      change subst impl (NInstr.gate g :: nGatesOf gs) = _
      rw [subst_cons, ih]
      rfl

/-- Substitution depends only on the implementations of the called primitives. -/
theorem subst_congr {V Y Y' J J' A' : Type*} {impl impl' : J' → List (NInstr (Y' ⊕ A') Y J)}
    (C : List (NInstr V Y' J'))
    (h : ∀ q ∈ C, ∀ j adj pos, q = NInstr.call j adj pos → impl j = impl' j) :
    subst impl C = subst impl' C := by
  induction C with
  | nil => rfl
  | cons q C ih =>
      rw [subst_cons, subst_cons, ih (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))]
      congr 1
      cases q with
      | gate g => rfl
      | call j adj pos =>
          change (implAdj impl j adj).map _ = (implAdj impl' j adj).map _
          rw [implAdj, implAdj, h _ (List.mem_cons.mpr (Or.inl rfl)) j adj pos rfl]

/-- A circuit depends only on the called primitives. -/
theorem nrun_congr {V Y J : Type*} [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y]
    {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
    {prim prim' : J → Reg Y R →L[ℂ] Reg Y R} (C : List (NInstr V Y J))
    (h : ∀ q ∈ C, ∀ j adj pos, q = NInstr.call j adj pos → prim j = prim' j) :
    nrun prim C = nrun prim' C := by
  induction C with
  | nil => rfl
  | cons q C ih =>
      rw [nrun_cons, nrun_cons, ih (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))]
      congr 1
      cases q with
      | gate g => rfl
      | call j adj pos =>
          rw [NInstr.eval_call, NInstr.eval_call,
            h _ (List.mem_cons.mpr (Or.inl rfl)) j adj pos rfl]

variable {k b b' A : ℕ}

/-- The wires of the circuit and the decoding ancillas, overwritten on the wires of a decoded
call. -/
theorem overwrite_callEmb_elim (z : Cfg (GeneralSparseAccess.IW k b')) (d : Cfg (DW b b' A))
    (c : Cfg (PY k b' ⊕ DW b b' A)) :
    overwrite (callEmb (A := DW b b' A) posV) (Sum.elim z d) c =
      Sum.elim (overwrite posV z (fun p => c (Sum.inl p))) (fun a => c (Sum.inr a)) := by
  funext u
  rcases u with u | a
  · by_cases hu : ∃ p, posV p = u
    · obtain ⟨p, rfl⟩ := hu
      exact (overwrite_apply_ι (callEmb (A := DW b b' A) posV).injective (Sum.elim z d) c
        (Sum.inl p)).trans (overwrite_apply_ι posV.injective z (fun p => c (Sum.inl p)) p).symm
    · have h1 : ∀ w, callEmb (A := DW b b' A) posV w ≠ Sum.inl u := by
        rintro (p | a) h
        · exact hu ⟨p, Sum.inl_injective h⟩
        · cases h
      rw [overwrite_apply_out _ _ _ _ h1]
      exact (overwrite_apply_out posV z (fun p => c (Sum.inl p)) u (fun p hp => hu ⟨p, hp⟩)).symm
  · exact overwrite_apply_ι (callEmb (A := DW b b' A) posV).injective (Sum.elim z d) c (Sum.inr a)

variable (dc : BinDecode b b' A)
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- A classical gate list of the circuit wires, substituted, on a basis vector: the gate list on
the circuit wires, the decoding ancillas unchanged. -/
theorem nrun_subst_gates (P : Query → Reg (PY k b) R →L[ℂ] Reg (PY k b) R)
    (gs : List (Gate (GeneralSparseAccess.IW k b'))) (h : Classical gs)
    (z : Cfg (GeneralSparseAccess.IW k b')) (d : Cfg (DW b b' A)) (q : R) :
    nrun P (subst (implDecW (k := k) dc) (nGatesOf gs)) (bas (Sum.elim z d) q) =
      bas (Sum.elim (cfgRun gs z) d) q := by
  rw [subst_nGatesOf, nrun_nGatesOf, gRun_classical_bas _ (classical_map Sum.inl_injective h),
    cfgRun_map Sum.inl_injective]
  congr 1
  funext u
  rcases u with u | a
  · exact overwrite_apply_ι Sum.inl_injective _ _ u
  · exact overwrite_apply_out _ _ _ _ (fun a' h => by cases h)

/-- The copy, substituted, on a vector placed on the wires of a decoded call, with the flag
clear. -/
theorem nrun_copyD_put (P : Query → Reg (PY k b) R →L[ℂ] Reg (PY k b) R) (z₀ : Cfg (VW b'))
    (z : Cfg (GeneralSparseAccess.IW k b')) (hg : z g₂ = false)
    (φ : Reg (PY k b' ⊕ DW b b' A) R) :
    nrun P (subst (implDecW (k := k) dc) (nGatesOf (copyC z₀)))
        (put (callEmb (A := DW b b' A) posV) (callEmb posV).injective
          (Sum.elim z (fun _ => false)) φ) =
      put (callEmb (A := DW b b' A) posV) (callEmb posV).injective
        (Sum.elim (cfgRun (copyC z₀) z) (fun _ => false)) φ := by
  rw [put_eq_sum_bas, put_eq_sum_bas, map_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  simp only [overwrite_callEmb_elim]
  rw [nrun_subst_gates dc P _ (classical_copyC z₀), cfgRun_copyC_overwrite z₀ z hg]

variable {X : Type*} {N s : ℕ} {D : QData X N s k b} (Wr : D.Writer)

/-- A decoded value call of the padded value oracle, substituted by `implDecW`. -/
theorem nrun_subst_valCall (x : X) :
    nrun (Wr.prims (R := R) x) (subst (implDecW (k := k) dc)
        ([NInstr.call Query.value false posV] :
          List (NInstr (GeneralSparseAccess.IW k b') (PY k b') Query))) =
      localOp (callEmb (A := DW b b' A) posV) (callEmb posV).injective
        (fun _ => nrun (Wr.prims (R := R) x) (implDecW (k := k) dc Query.value)) := by
  rw [subst_cons, subst_nil, List.append_nil]
  exact nrun_map _ (callEmb posV) (implDecW (k := k) dc Query.value)

/-- **A decoded value call through the writer on a valid pair** of the padded value oracle, on
clean decoding ancillas: the supplied value call of the decoded data. -/
theorem cval_valid (c₀ : ℝ) (hc₀ : 0 < c₀) (hdc : dc.Exact D.val c₀) (x : X)
    (z : Cfg (GeneralSparseAccess.IW k b')) (q : R) (i j : Fin N)
    (had : (fun a => z (tl a)) = edgeW k (binW k i) (binW k j)) :
    localOp (callEmb (A := DW b b' A) posV) (callEmb posV).injective
        (fun _ => nrun (Wr.prims (R := R) x) (implDecW (k := k) dc Query.value))
        (bas (Sum.elim z (fun _ => false)) q) =
      bas (Sum.elim (valMap (D.decData dc c₀ hc₀ hdc) x z) (fun _ => false)) q := by
  rw [localOp_bas]
  have hloc : (fun a => (Sum.elim z (fun _ => false) :
      Cfg (GeneralSparseAccess.IW k b' ⊕ DW b b' A)) (callEmb (A := DW b b' A) posV a)) =
      Sum.elim (fun p => z (posV p)) (fun _ => false) := by
    funext a
    rcases a with p | a <;> rfl
  rw [hloc, decW_valid Wr dc x i j (fun p => z (posV p)) had q, put_bas, overwrite_callEmb_elim,
    ← had]
  rfl

/-- **The decoded calls around the copy on a valid pair**: the decoded value calls through the
writer act as those of the decoded data. -/
theorem cmid_valid (c₀ : ℝ) (hc₀ : 0 < c₀) (hdc : dc.Exact D.val c₀) (x : X)
    (z₀ : Cfg (VW b')) (z : Cfg (GeneralSparseAccess.IW k b')) (q : R) (i j : Fin N)
    (had : (fun a => z (tl a)) = edgeW k (binW k i) (binW k j)) :
    localOp (callEmb (A := DW b b' A) posV) (callEmb posV).injective
        (fun _ => nrun (Wr.prims (R := R) x) (implDecW (k := k) dc Query.value))
      (nrun (Wr.prims (R := R) x) (subst (implDecW (k := k) dc) (nGatesOf (copyC z₀)))
        (localOp (callEmb (A := DW b b' A) posV) (callEmb posV).injective
          (fun _ => nrun (Wr.prims (R := R) x) (implDecW (k := k) dc Query.value))
          (bas (Sum.elim z (fun _ => false)) q))) =
      bas (Sum.elim (valMap (D.decData dc c₀ hc₀ hdc) x
        (cfgRun (copyC z₀) (valMap (D.decData dc c₀ hc₀ hdc) x z))) (fun _ => false)) q := by
  have had2 : (fun a => cfgRun (copyC z₀) (valMap (D.decData dc c₀ hc₀ hdc) x z) (tl a)) =
      edgeW k (binW k i) (binW k j) := by
    funext a
    rw [cfgRun_copyC_out z₀ _ _ (fun w => by simp [tl, e, v]),
      valMap_out (D.decData dc c₀ hc₀ hdc) x z _ (fun w => (tl_ne_sc a w).symm)]
    exact congrFun had a
  rw [cval_valid dc Wr c₀ hc₀ hdc x z q i j had, nrun_subst_gates dc _ _ (classical_copyC z₀),
    cval_valid dc Wr c₀ hc₀ hdc x _ q i j had2]

/-- **The decoded calls around the copy on an invalid pair**: with the flag clear, the copy does not
read the wires of the calls, and the second call undoes the first whatever the writer did
(`decW_invol`). -/
theorem cmid_invalid (c₀ : ℝ) (hc₀ : 0 < c₀) (hdc : dc.Exact D.val c₀) (x : X)
    (z₀ : Cfg (VW b')) (z : Cfg (GeneralSparseAccess.IW k b')) (q : R) (hg : z g₂ = false) :
    localOp (callEmb (A := DW b b' A) posV) (callEmb posV).injective
        (fun _ => nrun (Wr.prims (R := R) x) (implDecW (k := k) dc Query.value))
      (nrun (Wr.prims (R := R) x) (subst (implDecW (k := k) dc) (nGatesOf (copyC z₀)))
        (localOp (callEmb (A := DW b b' A) posV) (callEmb posV).injective
          (fun _ => nrun (Wr.prims (R := R) x) (implDecW (k := k) dc Query.value))
          (bas (Sum.elim z (fun _ => false)) q))) =
      bas (Sum.elim (valMap (D.decData dc c₀ hc₀ hdc) x
        (cfgRun (copyC z₀) (valMap (D.decData dc c₀ hc₀ hdc) x z))) (fun _ => false)) q := by
  set V := nrun (Wr.prims (R := R) x) (implDecW (k := k) dc Query.value) with hV
  have hVV : V ∘L V = 1 := decW_invol Wr dc x
  have hloc : (fun a => (Sum.elim z (fun _ => false) :
      Cfg (GeneralSparseAccess.IW k b' ⊕ DW b b' A)) (callEmb (A := DW b b' A) posV a)) =
      fun a => (Sum.elim (cfgRun (copyC z₀) z) (fun _ => false) :
        Cfg (GeneralSparseAccess.IW k b' ⊕ DW b b' A)) (callEmb (A := DW b b' A) posV a) := by
    funext a
    rcases a with p | a
    · exact (cfgRun_copyC_out z₀ z _ (fun w => posV_ne_v p w)).symm
    · rfl
  rw [localOp_bas, nrun_copyD_put dc _ z₀ z hg, localOp_put]
  change put _ _ _ (V (V _)) = _
  rw [← comp_apply V V, hVV, one_apply_eq_self, put_bas, hloc,
    overwrite_self (callEmb (A := DW b b' A) posV).injective,
    valMap_copyC_valMap (D := D.decData dc c₀ hc₀ hdc) x z₀ z hg]

/-- **The padded value oracle of the decoded data from the writer on clean basis inputs**: the
substituted circuit acts as the padded value oracle of the decoded data, the decoding ancillas
clean. -/
theorem compW_bas (c₀ : ℝ) (hc₀ : 0 < c₀) (hdc : dc.Exact D.val c₀) (z₀ : Cfg (VW b')) (x : X)
    (y : Cfg (PY (k + 1) b')) (q : R) :
    nrun (Wr.prims (R := R) x) (subst (implDecW (k := k) dc) (implVal N z₀))
        (bas (Sum.elim (Sum.elim y (fun _ => false)) (fun _ => false)) q) =
      cleanEmb (X := DW b b' A) (nrun ((D.decData dc c₀ hc₀ hdc).prims (R := R) x) (implVal N z₀)
        (bas (Sum.elim y (fun _ => false)) q)) := by
  unfold implVal
  simp only [subst_append, nrun_append, comp_apply, nrun_nGatesOf]
  rw [gRun_classical_bas _ (classical_vflagC N), nrun_valCall,
    gRun_classical_bas _ (classical_copyC z₀), nrun_valCall,
    gRun_classical_bas _ (classical_vflagC_rev N), cleanEmb_bas,
    nrun_subst_gates dc _ _ (classical_vflagC N), nrun_subst_valCall dc Wr x]
  set z : Cfg (GeneralSparseAccess.IW k b') := Sum.elim y (fun _ => false) with hz
  set z1 := cfgRun (vflagC N) z with hz1
  obtain ⟨hg2, hout⟩ := cfgRun_vflagC (k := k) (b := b') D.N_lt_pow_succ z (fun j => rfl)
    (fun j => rfl) rfl rfl
  rw [← hz1] at hg2 hout
  have hz1tl : ∀ a, z1 (tl a) = z (tl a) := fun a =>
    hout _ (fun j => by simp [bA, tl, e]) (fun j => by simp [bB, tl, e]) (by simp [g₁, tl, e])
      (by simp [g₂, tl, e])
  by_cases hv : z1 g₂ = true
  · have hvp : vpair N z = true := by rw [← hg2]; exact hv
    unfold vpair at hvp
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at hvp
    obtain ⟨⟨⟨-, h1⟩, -⟩, h2⟩ := hvp
    have had : (fun a => z1 (tl a)) =
        edgeW k (binW k (⟨_, h1⟩ : Fin N)) (binW k (⟨_, h2⟩ : Fin N)) := by
      funext a
      rw [hz1tl]
      rcases a with a | a
      · change z (xA a) = binW k (wordValue (fun i => z (xA i))) a
        rw [binW_wordValue]
      · change z (xB a) = binW k (wordValue (fun i => z (xB i))) a
        rw [binW_wordValue]
    rw [cmid_valid dc Wr c₀ hc₀ hdc x z₀ z1 q ⟨_, h1⟩ ⟨_, h2⟩ had,
      nrun_subst_gates dc _ _ (classical_vflagC_rev N)]
  · rw [Bool.not_eq_true] at hv
    rw [cmid_invalid dc Wr c₀ hc₀ hdc x z₀ z1 q hv,
      nrun_subst_gates dc _ _ (classical_vflagC_rev N)]

/-- **The padded value oracle of the decoded data from a writer** on clean ancillas. -/
theorem compW_value (c₀ : ℝ) (hc₀ : 0 < c₀) (hdc : dc.Exact D.val c₀) (z₀ : Cfg (VW b'))
    (hz₀ : (D.decData dc c₀ hc₀ hdc).val z₀ = 0) (x : X) :
    nrun (Wr.prims (R := R) x) (implDPW N s z₀ dc Query.value) ∘L
        cleanEmb (X := GeneralSparseAccess.AW k b' ⊕ DW b b' A) =
      cleanEmb ∘L GateBinary.prims (R := R) ((D.decData dc c₀ hc₀ hdc).padData z₀ hz₀)
        (Equiv.refl _) x Query.value := by
  change nrun (Wr.prims (R := R) x)
      ((subst (implDecW (k := k) dc) (implVal N z₀)).map (NInstr.map assocE)) ∘L cleanEmb = _
  rw [nrun_map]
  apply localOp_assocE_clean
  rw [comp_assoc, ← implValP_clean (D.decData dc c₀ hc₀ hdc) z₀ hz₀ x]
  apply ext_bas_clm'
  intro y q
  simp only [comp_apply, cleanEmb_bas]
  exact compW_bas dc Wr c₀ hc₀ hdc z₀ x y q

/-- The composite implementation of a locator from the writer is that from the supplied value
oracle. -/
theorem implDPW_eq (z₀ : Cfg (VW b')) (j : Query) (hj : j ≠ Query.value) :
    implDPW (k := k) N s z₀ dc j = implDP N s z₀ dc j := by
  unfold implDPW implDP implComp
  congr 1
  apply subst_congr
  intro q hq j' adj pos he
  have hk : j' = j := (kindOK_implP (k := k) (b := b') N s z₀).kind_eq j q hq j' adj pos he
  rw [hk]
  cases j with
  | rowLocation => rfl
  | columnLocation => rfl
  | value => exact absurd rfl hj

/-- A composite locator implementation calls the supplied locators only. -/
theorem nrun_implDP_eq (x : X) (z₀ : Cfg (VW b')) (j : Query) (hj : j ≠ Query.value) :
    nrun (Wr.prims (R := R) x) (implDP (k := k) N s z₀ dc j) =
      nrun (D.prims (R := R) x) (implDP N s z₀ dc j) := by
  apply nrun_congr
  intro q hq j' adj pos he
  have hk : j' = j := (kindOK_implDP (k := k) N s z₀ dc).kind_eq j q hq j' adj pos he
  rw [hk]
  cases j with
  | rowLocation => rfl
  | columnLocation => rfl
  | value => exact absurd rfl hj

/-- **The padded oracles of the decoded data from a writer**: on clean ancillas, `implDPW N s z₀ dc`
acts as the padded oracles of the decoded data, for every unitary action of the writer outside its
valid clean inputs. -/
theorem implOK_implDPW (c₀ : ℝ) (hc₀ : 0 < c₀) (hdc : dc.Exact D.val c₀) (z₀ : Cfg (VW b'))
    (hz₀ : (D.decData dc c₀ hc₀ hdc).val z₀ = 0) (x : X) :
    ImplOK (Wr.prims (R := R) x)
      (GateBinary.prims (R := R) ((D.decData dc c₀ hc₀ hdc).padData z₀ hz₀) (Equiv.refl _) x)
      (implDPW N s z₀ dc) where
  valid := valid_implDPW N s z₀ dc
  clean j := by
    cases j with
    | value => exact compW_value dc Wr c₀ hc₀ hdc z₀ hz₀ x
    | rowLocation =>
        rw [implDPW_eq dc z₀ Query.rowLocation (fun h => by cases h),
          nrun_implDP_eq dc Wr x z₀ Query.rowLocation (fun h => by cases h)]
        exact (implOK_implDP D dc c₀ hc₀ hdc z₀ hz₀ x).clean Query.rowLocation
    | columnLocation =>
        rw [implDPW_eq dc z₀ Query.columnLocation (fun h => by cases h),
          nrun_implDP_eq dc Wr x z₀ Query.columnLocation (fun h => by cases h)]
        exact (implOK_implDP D dc c₀ hc₀ hdc z₀ hz₀ x).clean Query.columnLocation

end CompW

end

end SparseHamiltonian.GeneralDecoderODE
