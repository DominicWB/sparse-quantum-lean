import GateEfficientBinaryODE.Wires

/-!
# The native identity of the four-sector private operation

For the binary sparse oracles (`prims` of `GateEfficientBinary`) the compute circuit
`computeV4` acts on clean scratch as the lifted locator `F4` (label independent) followed by a
permutation `σ4` of basis configurations (`compute4_cleanEmb`): the reference calls, the locator
block (`loc_agree`: the tag XOR turns the gadgets controlled by the tag wire into the row oracle
when orientation and tag agree), and the two value calls. If the decoder of a native private
operation with this circuit takes, after `σ4`, the value of the edgewise Cayley gate of the
label-selected four-sector operation (`DecOK`), the decoded rotation commutes past `σ4` into the
lifted edgewise action `A4` (`rdec_sigma4`), and the native identity holds for the
label-selected private operation `elift4 (act4 …)` (`nativeOK4`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateODE (overwrite_apply_ι overwrite_apply_out localOp_localOp'
  update_comp_injective Label)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### Operator lemmas -/

section Ops

variable {A W : Type*} [Fintype A] [DecidableEq A] [Fintype W] [DecidableEq W]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- A permutation of configurations that commutes with overwriting the wires `ι` conjugates an
operator on those wires into the operator selected by the permuted configuration. -/
theorem permOp_localOp_permOp {ι : A → W} (hι : Function.Injective ι) (e : Cfg W ≃ Cfg W)
    (he : ∀ z c, e (overwrite ι z c) = overwrite ι (e z) c)
    (F : Cfg W → (Reg A R →L[ℂ] Reg A R)) :
    permOp e.symm ∘L localOp ι hι F ∘L permOp e = localOp ι hι (fun z => F (e z)) := by
  ext ψ x
  simp only [comp_apply, permOp_apply, Equiv.symm_symm, localOp_apply]
  have h1 : clearCfg ι (e x) = e (clearCfg ι x) := (he x (fun _ => false)).symm
  have h2 : slice ι (permOp e ψ) (e x) = slice ι ψ x := by
    apply PiLp.ext
    intro c
    simp only [slice_apply, permOp_apply]
    rw [← he x c, Equiv.symm_apply_apply]
  have h3 : (fun a => e x (ι a)) = fun a => x (ι a) := by
    funext a
    have hx : x = overwrite ι x (fun a => x (ι a)) := (joinCfg_self hι x).symm
    have := he x (fun a => x (ι a))
    rw [← hx] at this
    rw [this, overwrite_apply_ι hι]
  rw [h1, h2, h3]

/-- An operator on the private wires selected by the label wires, which is itself a one-qubit
operation on a private wire `t`, is the one-qubit operation on `t` selected by all other
wires. -/
theorem localOp_inr_condOp {Sel P : Type*} [Fintype Sel] [DecidableEq Sel] [Fintype P]
    [DecidableEq P] (t : P) (u : Cfg Sel → Cfg P → Matrix Bool Bool ℂ) :
    localOp (Sum.inr : P → Sel ⊕ P) Sum.inr_injective
        (fun y => condOp (Q := R) t (u (fun s => y (Sum.inl s)))) =
      condOp (Sum.inr t) (fun z => u (fun s => z (Sum.inl s)) (fun w => z (Sum.inr w))) := by
  unfold condOp
  rw [localOp_localOp' Sum.inr_injective (single_injective t) (fun _ => Sum.inr t)
    (single_injective _) (fun _ => rfl)
    (fun y c => matOp (qubitMat (u (fun s => y (Sum.inl s)) c)))]
  apply localOp_congr
  intro z
  set z' := clearCfg (fun _ : Unit => (Sum.inr t : Sel ⊕ P)) z with hz'
  have h1 : (fun s => clearCfg (Sum.inr : P → Sel ⊕ P) z' (Sum.inl s)) =
      fun s => z (Sum.inl s) := by
    funext s
    rw [clearCfg_apply_out _ _ _ (fun w h => by cases h), hz',
      clearCfg_apply_out _ _ _ (fun w h => by cases h)]
  have h3 : clearCfg (fun _ : Unit => t) (fun a => z' (Sum.inr a)) =
      fun a => z' (Sum.inr a) := by
    rw [clearCfg_single]
    funext a
    by_cases ha : a = t
    · subst ha
      rw [Function.update_self, hz', clearCfg_single, Function.update_self]
    · rw [Function.update_of_ne ha]
  have h4 : (fun s => z' (Sum.inl s)) = fun s => z (Sum.inl s) := by
    funext s
    rw [hz', clearCfg_apply_out _ _ _ (fun w h => by cases h)]
  rw [h1, h3]
  show _ = matOp (qubitMat (u (fun s => z' (Sum.inl s)) fun w => z' (Sum.inr w)))
  rw [h4]

omit [CompleteSpace R] in
/-- A permutation preserves the configurations of a set invariant under it. -/
theorem preserves_permOp (S : Cfg W → Prop) (e : Cfg W ≃ Cfg W)
    (he : ∀ y, S (e.symm y) → S y) : Preserves S (permOp (Q := R) e) := by
  intro ψ hψ y hy
  rw [permOp_apply]
  exact hψ _ (fun h => hy (he y h))

end Ops

/-! ### The reference calls -/

section Refs

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b kq lq : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- A call of a primitive acting on the edge register, placed with the edge register on `T`. -/
theorem eval_call_edge4 (prim : Query → Reg (PY k b) R →L[ℂ] Reg (PY k b) R) (j : Query)
    (G : Reg (EW k) R →L[ℂ] Reg (EW k) R)
    (hj : prim j = localOp Sum.inl Sum.inl_injective (fun _ => G))
    (pos : PY k b ↪ BW4 k b kq lq) (T : EW k → BW4 k b kq lq) (hT : Function.Injective T)
    (hpos : ∀ e, pos (Sum.inl e) = T e) :
    (NInstr.call j false pos).eval prim = localOp T hT (fun _ => G) := by
  rw [NInstr.eval_call, hj]
  simp only [GateODE.adjIf, Bool.false_eq_true, if_false]
  exact localOp_localOp' pos.injective Sum.inl_injective T hT (fun e => (hpos e).symm)
    (fun _ _ => G)

/-- A configuration of the base wires is determined by its parts. -/
theorem bw4_ext {y y' : Cfg (BW4 k b kq lq)} (hp : ∀ p, y (Sum.inl p) = y' (Sum.inl p))
    (hd : ∀ e, y (dm4 e) = y' (dm4 e)) (hr : ∀ e, y (rr4 e) = y' (rr4 e))
    (hc : ∀ e, y (rc4 e) = y' (rc4 e)) (h1 : ∀ v, y (v14 v) = y' (v14 v))
    (h2 : ∀ v, y (v24 v) = y' (v24 v)) : y = y' := by
  funext w
  rcases w with p | (((e | e) | e) | (v | v))
  · exact hp p
  · exact hd e
  · exact hr e
  · exact hc e
  · exact h1 v
  · exact h2 v

/-- The scratch written by the reference calls. -/
def refCfg4 (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X) :
    Cfg (SZ4 k b) :=
  Sum.elim (Sum.elim (Sum.elim (fun _ => false) (refRow D en k0 x)) (refCol D en k0 x))
    (fun _ => false)

/-- The permutation of the reference calls: the references are XOR-ed into their registers. -/
def sigRef4 (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X) :
    Cfg (BW4 k b kq lq) ≃ Cfg (BW4 k b kq lq) :=
  xorEquiv (fun _ => refCfg4 D en k0 x)

/-- The two reference calls act on clean scratch as the permutation `sigRef4`. -/
theorem refs4_cleanEmb (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) (x : X) :
    nrun (prims (R := R) D en x)
        [NInstr.call Query.rowLocation false (posRR4 (kq := kq) (lq := lq)),
          NInstr.call Query.columnLocation false posRC4] ∘L cleanEmb (X := SZ4 k b) =
      permOp (sigRef4 D en k0 x) ∘L cleanEmb := by
  have hR := eval_call_edge4 (prims (R := R) D en x) Query.rowLocation _ (prims_row D en x)
    (posRR4 (kq := kq) (lq := lq)) rr4 rr4_injective (fun _ => rfl)
  have hC := eval_call_edge4 (prims (R := R) D en x) Query.columnLocation _
    (prims_col D en x) (posRC4 (kq := kq) (lq := lq)) rc4 rc4_injective (fun _ => rfl)
  apply ext_bas_clm'
  intro c q
  rw [nrun_cons, nrun_cons, nrun_nil, hR, hC]
  simp only [comp_apply, one_apply_eq_self, cleanEmb_bas, permOp_bas]
  rw [localOp_bas_clean rr4_injective _ _ (fun _ => rfl) _ (row_zero D en k0 hk0 x),
    localOp_bas_clean rc4_injective _ _ (fun e => by
      rw [overwrite_apply_out rr4 _ _ _ (fun e' => rr4_ne_rc4 e' e)]
      rfl) _ (col_zero D en k0 hk0 x)]
  congr 1
  apply bw4_ext
  · intro p
    rw [overwrite_apply_out rc4 _ _ _ (fun e h => by simp [rc4] at h),
      overwrite_apply_out rr4 _ _ _ (fun e h => by simp [rr4] at h)]
    rfl
  · intro e
    rw [overwrite_apply_out rc4 _ _ _ (fun e' => (dm4_ne_rc4 e e').symm),
      overwrite_apply_out rr4 _ _ _ (fun e' => (dm4_ne_rr4 e e').symm)]
    simp [sigRef4, refCfg4, dm4]
  · intro e
    rw [overwrite_apply_out rc4 _ _ _ (fun e' => (rr4_ne_rc4 e e').symm),
      overwrite_apply_ι rr4_injective]
    simp [sigRef4, refCfg4, rr4]
  · intro e
    rw [overwrite_apply_ι rc4_injective]
    simp [sigRef4, refCfg4, rc4]
  · intro v
    rw [overwrite_apply_out rc4 _ _ _ (fun e' => (rc4_ne_v14 e' v)),
      overwrite_apply_out rr4 _ _ _ (fun e' => (rr4_ne_v14 e' v))]
    simp [sigRef4, refCfg4, v14]
  · intro v
    rw [overwrite_apply_out rc4 _ _ _ (fun e' h => by simp [rc4, v24] at h),
      overwrite_apply_out rr4 _ _ _ (fun e' h => by simp [rr4, v24] at h)]
    simp [sigRef4, refCfg4, v24]

/-- Clean dummy register and reference registers holding the references. -/
def RefOK4 (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (y : Cfg (BW4 k b kq lq)) : Prop :=
  (∀ e, y (dm4 e) = false) ∧ (∀ e, y (rr4 e) = refRow D en k0 x e) ∧
    (∀ e, y (rc4 e) = refCol D en k0 x e)

omit [CompleteSpace R] in
theorem supp_sigRef4 (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (ψ : Reg (LabW kq lq ⊕ PR4 k) R) :
    Supp (RefOK4 D en k0 x) (permOp (sigRef4 D en k0 x) (cleanEmb (X := SZ4 k b) ψ)) := by
  intro y hy
  rw [permOp_apply]
  apply supp_cleanEmb ψ
  intro hc
  apply hy
  have hy' : y = sigRef4 D en k0 x ((sigRef4 D en k0 x).symm y) :=
    (Equiv.apply_symm_apply _ y).symm
  generalize (sigRef4 D en k0 x).symm y = z at hc hy'
  subst hy'
  have hz : ∀ w, z (Sum.inr w) = false := hc
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩ <;>
    simp [sigRef4, refCfg4, dm4, rr4, rc4, hz]

end Refs

/-! ### The locator block -/

section Locator

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b kq lq : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The lifted locator on the base wires: the row location oracle on the index wires when the
orientation and the tag agree, the column location oracle otherwise. -/
def Lfull4 (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    Reg (BW4 k b kq lq) R →L[ℂ] Reg (BW4 k b kq lq) R :=
  localOp xB4 xB4_injective (fun y => if y oB4 = y tB4 then qlift (phiE en) (D.rowOracle x)
    else qlift (phiE en) (D.columnOracle x))

/-- **The two gadgets** act, controlled by the tag wire, as the row and the column location
oracle on scratch holding the references. -/
theorem gadgets4_agree (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) (x : X) :
    Agrees (RefOK4 D en k0 x)
      (nrun (prims (R := R) D en x)
        (gadget tB4 false xB4 dm4 rr4
            [NInstr.call Query.rowLocation false (posT4 (kq := kq) (lq := lq))] ++
          gadget tB4 true xB4 dm4 rc4 [NInstr.call Query.columnLocation false posT4]))
      (localOp xB4 xB4_injective (fun y => if y tB4 then qlift (phiE en) (D.columnOracle x)
        else qlift (phiE en) (D.rowOracle x))) := by
  have hcR : nrun (prims (R := R) D en x)
      [NInstr.call Query.rowLocation false (posT4 (kq := kq) (lq := lq))] =
      localOp xB4 xB4_injective (fun _ => qlift (phiE en) (D.rowOracle x)) := by
    rw [nrun_singleton]
    exact eval_call_edge4 _ _ _ (prims_row D en x) posT4 xB4 xB4_injective (fun _ => rfl)
  have hcC : nrun (prims (R := R) D en x)
      [NInstr.call Query.columnLocation false (posT4 (kq := kq) (lq := lq))] =
      localOp xB4 xB4_injective (fun _ => qlift (phiE en) (D.columnOracle x)) := by
    rw [nrun_singleton]
    exact eval_call_edge4 _ _ _ (prims_col D en x) posT4 xB4 xB4_injective (fun _ => rfl)
  have h1 := gadget_agrees (prims (R := R) D en x) (qlift (phiE en) (D.rowOracle x))
    (refRow D en k0 x) (row_zero D en k0 hk0 x) tB4 false xB4 dm4 rr4 xB4_injective
    dm4_injective xB4_ne_dm4 xB4_ne_rr4 dm4_ne_rr4 xB4_ne_tB4 dm4_ne_tB4 _ hcR
  have h2 := gadget_agrees (prims (R := R) D en x) (qlift (phiE en) (D.columnOracle x))
    (refCol D en k0 x) (col_zero D en k0 hk0 x) tB4 true xB4 dm4 rc4 xB4_injective
    dm4_injective xB4_ne_dm4 xB4_ne_rc4 dm4_ne_rc4 xB4_ne_tB4 dm4_ne_tB4 _ hcC
  have hp : Preserves (RefOK4 D en k0 x) (localOp xB4 xB4_injective
      (fun y => if y tB4 = false then qlift (phiE en) (D.rowOracle x) else 1) :
        Reg (BW4 k b kq lq) R →L[ℂ] Reg (BW4 k b kq lq) R) := by
    apply preserves_localOp
    rintro y d ⟨hd, hr, hc⟩
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
    · rw [overwrite_apply_out xB4 y d _ (fun e' => xB4_ne_dm4 e' e)]
      exact hd e
    · rw [overwrite_apply_out xB4 y d _ (fun e' => xB4_ne_rr4 e' e)]
      exact hr e
    · rw [overwrite_apply_out xB4 y d _ (fun e' => xB4_ne_rc4 e' e)]
      exact hc e
  have h := Agrees.comp (Sim.Agrees.mono h1 (fun y hy => ⟨hy.1, hy.2.1⟩)) hp
    (Sim.Agrees.mono h2 (fun y hy => ⟨hy.1, hy.2.2⟩))
  have hC : (localOp xB4 xB4_injective
      (fun y => if y tB4 = true then qlift (phiE en) (D.columnOracle x) else 1) :
        Reg (BW4 k b kq lq) R →L[ℂ] Reg (BW4 k b kq lq) R) ∘L localOp xB4 xB4_injective
      (fun y => if y tB4 = false then qlift (phiE en) (D.rowOracle x) else 1) =
      localOp xB4 xB4_injective (fun y => if y tB4 then qlift (phiE en) (D.columnOracle x)
        else qlift (phiE en) (D.rowOracle x)) := by
    rw [localOp_comp]
    congr 1
    funext y
    cases y tB4 <;> simp [Sim.one_comp', Sim.comp_one']
  rw [nrun_append, ← hC]
  exact h

theorem tB4_not_mem : ∀ c ∈ [((oB4 : BW4 k b kq lq), true)], c.1 ≠ tB4 := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  exact oB4_ne_tB4

/-- The tag XOR as a permutation of configurations. -/
def flip4 : Cfg (BW4 k b kq lq) ≃ Cfg (BW4 k b kq lq) :=
  flipEquiv [(oB4, true)] tB4 tB4_not_mem

theorem flip4_symm : (flip4 (k := k) (b := b) (kq := kq) (lq := lq)).symm = flip4 :=
  Equiv.ext fun _ => rfl

theorem nrun_cnot4 (prim : Query → Reg (PY k b) R →L[ℂ] Reg (PY k b) R) :
    nrun prim [NInstr.gate (cnot4 k b kq lq)] = permOp flip4 := by
  rw [nrun_singleton, NInstr.eval_gate]
  exact gateOp_pauliX _ _ tB4_not_mem

theorem flip4_overwrite (z : Cfg (BW4 k b kq lq)) (c : Cfg (EW k)) :
    flip4 (overwrite xB4 z c) = overwrite xB4 (flip4 z) c := by
  have hctrl : ctrlOK [((oB4 : BW4 k b kq lq), true)] (overwrite xB4 z c) =
      ctrlOK [(oB4, true)] z := by
    simp only [ctrlOK, List.all_cons, List.all_nil, Bool.and_true]
    rw [overwrite_apply_out xB4 z c _ (fun e => xB4_ne_oB4 e)]
  change flipCfg _ _ (overwrite xB4 z c) = overwrite xB4 (flipCfg _ _ z) c
  unfold flipCfg
  rw [hctrl]
  split_ifs
  · rw [overwrite_apply_out xB4 z c _ (fun e => xB4_ne_tB4 e),
      overwrite_update_out xB4_injective z c tB4 _ (fun e => xB4_ne_tB4 e)]
  · rfl

theorem flip4_apply_tB4 (z : Cfg (BW4 k b kq lq)) : flip4 z tB4 = (z tB4 ^^ z oB4) := by
  change flipCfg _ _ z tB4 = _
  unfold flipCfg
  cases h : z oB4 <;> simp [ctrlOK, h]

theorem flip4_apply_out (z : Cfg (BW4 k b kq lq)) (w : BW4 k b kq lq) (hw : w ≠ tB4) :
    flip4 z w = z w := by
  change flipCfg _ _ z w = _
  unfold flipCfg
  split_ifs
  · exact Function.update_of_ne hw _ _
  · rfl

/-- **The locator block** acts as the lifted locator on scratch holding the references. -/
theorem loc_agree (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) (x : X) :
    Agrees (RefOK4 D en k0 x) (nrun (prims (R := R) D en x) (locC k b kq lq))
      (Lfull4 D en x) := by
  set G : Reg (BW4 k b kq lq) R →L[ℂ] Reg (BW4 k b kq lq) R :=
    localOp xB4 xB4_injective (fun y => if y tB4 then qlift (phiE en) (D.columnOracle x)
      else qlift (phiE en) (D.rowOracle x)) with hG
  have hg := gadgets4_agree (R := R) (kq := kq) (lq := lq) D en k0 hk0 x
  have hpres : Preserves (RefOK4 D en k0 x)
      (permOp (Q := R) (flip4 (k := k) (b := b) (kq := kq) (lq := lq))) := by
    apply preserves_permOp
    rintro y ⟨hd, hr, hc⟩
    rw [flip4_symm] at hd hr hc
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
    · rw [← hd e, flip4_apply_out _ _ (dm4_ne_tB4 e)]
    · rw [← hr e, flip4_apply_out _ _ (fun h => by simp [rr4, tB4] at h)]
    · rw [← hc e, flip4_apply_out _ _ (fun h => by simp [rc4, tB4] at h)]
  have hpG : Preserves (RefOK4 D en k0 x) G := by
    apply preserves_localOp
    rintro y d ⟨hd, hr, hc⟩
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
    · rw [overwrite_apply_out xB4 y d _ (fun e' => xB4_ne_dm4 e' e)]
      exact hd e
    · rw [overwrite_apply_out xB4 y d _ (fun e' => xB4_ne_rr4 e' e)]
      exact hr e
    · rw [overwrite_apply_out xB4 y d _ (fun e' => xB4_ne_rc4 e' e)]
      exact hc e
  have h := Agrees.comp (Agrees.comp (Agrees.refl _ _) hpres hg) (hpres.comp hpG)
    (Agrees.refl _ (permOp (Q := R) (flip4 (k := k) (b := b) (kq := kq) (lq := lq))))
  have hlocC : nrun (prims (R := R) D en x) (locC k b kq lq) =
      permOp flip4 ∘L (nrun (prims (R := R) D en x)
        (gadget tB4 false xB4 dm4 rr4
            [NInstr.call Query.rowLocation false (posT4 (kq := kq) (lq := lq))] ++
          gadget tB4 true xB4 dm4 rc4 [NInstr.call Query.columnLocation false posT4]) ∘L
        permOp flip4) := by
    simp only [locC, nrun_append, nrun_cnot4, comp_assoc]
  have hL : permOp flip4 ∘L (G ∘L permOp flip4) = Lfull4 (R := R) D en x := by
    have h' := permOp_localOp_permOp (R := R) xB4_injective
      (flip4 (k := k) (b := b) (kq := kq) (lq := lq)) flip4_overwrite
      (fun y => if y tB4 then qlift (phiE en) (D.columnOracle x)
        else qlift (phiE en) (D.rowOracle x))
    rw [flip4_symm] at h'
    rw [hG, h']
    unfold Lfull4
    congr 1
    funext z
    rw [flip4_apply_tB4]
    cases z tB4 <;> cases z oB4 <;> simp
  rw [hlocC, ← hL]
  exact h

end Locator

/-! ### The compute circuit on clean scratch -/

section Compute

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b kq lq : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The lifted locator on the label wires and the private register (label independent). -/
def F4 (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    Reg (LabW kq lq ⊕ PR4 k) R →L[ℂ] Reg (LabW kq lq ⊕ PR4 k) R :=
  localOp Sum.inr Sum.inr_injective (fun _ => qlift4 en (loc4 D x))

theorem F4_isUnitary (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    IsUnitary (F4 (R := R) (kq := kq) (lq := lq) D en x) :=
  localOp_isUnitary _ _ (fun _ => qlift4_isUnitary en (loc4_unitary D x))

theorem Lfull4_eq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    Lfull4 (R := R) (b := b) (kq := kq) (lq := lq) D en x =
      liftB (X := SZ4 k b) (F4 D en x) := by
  have hρ : Function.Injective (fun e : EW k => (Sum.inr (ix4 k e) : LabW kq lq ⊕ PR4 k)) :=
    Sum.inr_injective.comp (ix4_injective k)
  have e1 : F4 (R := R) (kq := kq) (lq := lq) D en x =
      localOp (fun e : EW k => (Sum.inr (ix4 k e) : LabW kq lq ⊕ PR4 k)) hρ
        (fun z => if z (Sum.inr (oW k)) = z (Sum.inr (tW k)) then
          qlift (phiE en) (D.rowOracle x) else qlift (phiE en) (D.columnOracle x)) := by
    unfold F4
    rw [qlift4_loc4, localOp_localOp' Sum.inr_injective (ix4_injective k) _ hρ (fun _ => rfl)
      (fun _ c => if c (oW k) = c (tW k) then qlift (R := R) (phiE en) (D.rowOracle x)
        else qlift (phiE en) (D.columnOracle x))]
    apply localOp_congr
    intro z
    rw [clearCfg_apply_out _ _ _ (fun e => ix4_ne_oW e),
      clearCfg_apply_out _ _ _ (fun e => ix4_ne_tW e)]
  have e2 : liftB (X := SZ4 k b)
      (localOp (fun e : EW k => (Sum.inr (ix4 k e) : LabW kq lq ⊕ PR4 k)) hρ
        (fun z => if z (Sum.inr (oW k)) = z (Sum.inr (tW k)) then
          qlift (R := R) (phiE en) (D.rowOracle x) else qlift (phiE en) (D.columnOracle x))) =
      Lfull4 D en x := by
    unfold liftB Lfull4
    rw [localOp_localOp' Sum.inl_injective hρ xB4 xB4_injective (fun _ => rfl)
      (fun _ z => if z (Sum.inr (oW k)) = z (Sum.inr (tW k)) then
        qlift (R := R) (phiE en) (D.rowOracle x) else qlift (phiE en) (D.columnOracle x))]
    apply localOp_congr
    intro w
    rw [clearCfg_apply_out _ _ _ (fun e h => ix4_ne_oW e (Sum.inr_injective h)),
      clearCfg_apply_out _ _ _ (fun e h => ix4_ne_tW e (Sum.inr_injective h))]
    rfl
  rw [e1, e2]

/-- The permutation written by the compute circuit: the references and the stored entries of
the located and of the transposed edge. -/
def sigma4 (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X) :
    Cfg (BW4 k b kq lq) ≃ Cfg (BW4 k b kq lq) :=
  (sigRef4 D en k0 x).trans ((alongEquiv posT4 (valPerm D en x)).trans
    (alongEquiv posS4 (valPerm D en x)))

/-- **The compute circuit on clean scratch** is the lifted locator followed by a permutation of
basis configurations. -/
theorem compute4_cleanEmb (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) (x : X) :
    nrun (prims (R := R) D en x) (computeV4 k b kq lq) ∘L cleanEmb (X := SZ4 k b) =
      permOp (sigma4 D en k0 x) ∘L cleanEmb ∘L F4 D en x := by
  have hval : nrun (prims (R := R) D en x)
      [NInstr.call Query.value false (posT4 (kq := kq) (lq := lq)),
        NInstr.call Query.value false posS4] =
      permOp (alongEquiv posS4 (valPerm D en x)) ∘L
        permOp (alongEquiv posT4 (valPerm D en x)) := by
    rw [nrun_cons, nrun_singleton, NInstr.eval_call, NInstr.eval_call, prims_val]
    simp only [GateODE.adjIf, Bool.false_eq_true, if_false]
    rw [localOp_permOp posT4 (valPerm D en x), localOp_permOp posS4 (valPerm D en x)]
  have hrefs := refs4_cleanEmb (R := R) (kq := kq) (lq := lq) D en k0 hk0 x
  have hloc := loc_agree (R := R) (kq := kq) (lq := lq) D en k0 hk0 x
  have hcomm : liftB (X := SZ4 k b) (F4 (R := R) (kq := kq) (lq := lq) D en x) ∘L
      permOp (sigRef4 D en k0 x) = permOp (sigRef4 D en k0 x) ∘L liftB (F4 D en x) :=
    liftB_comm_xor (F4 (R := R) D en x) (refCfg4 D en k0 x)
  have hlc := liftB_cleanEmb (X := SZ4 k b) (F4 (R := R) (kq := kq) (lq := lq) D en x)
  apply ContinuousLinearMap.ext
  intro ψ
  have h1 : nrun (prims (R := R) D en x)
      [NInstr.call Query.rowLocation false (posRR4 (kq := kq) (lq := lq)),
        NInstr.call Query.columnLocation false posRC4] (cleanEmb ψ) =
      permOp (sigRef4 D en k0 x) (cleanEmb ψ) := by
    rw [← comp_apply (nrun (prims (R := R) D en x)
      [NInstr.call Query.rowLocation false (posRR4 (kq := kq) (lq := lq)),
        NInstr.call Query.columnLocation false posRC4]) (cleanEmb (X := SZ4 k b)) ψ, hrefs,
      comp_apply]
  have h2 : liftB (X := SZ4 k b) (F4 D en x) (permOp (sigRef4 D en k0 x) (cleanEmb ψ)) =
      permOp (sigRef4 D en k0 x) (cleanEmb (F4 D en x ψ)) := by
    rw [← comp_apply (liftB (X := SZ4 k b) (F4 (R := R) D en x)) (permOp (sigRef4 D en k0 x)),
      hcomm, comp_apply, ← comp_apply (liftB (X := SZ4 k b) (F4 (R := R) D en x)) cleanEmb,
      hlc, comp_apply]
  rw [computeV4, nrun_append, nrun_append, comp_apply, comp_apply, comp_apply, h1,
    hloc _ (supp_sigRef4 D en k0 x ψ), Lfull4_eq, h2, hval]
  rfl

end Compute

/-! ### The decoded rotation -/

section Rdec

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s k b kq lq : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The value of the edgewise Cayley gate of the four-sector operation with LCHS node `κn` and
rescaling `γ`, on the part, the tag and the edge of a private configuration. -/
def val4 (D : Data X n Z s) (en : Cfg (Fin k) ≃ n) (x : X) (κn ρ γ : ℝ) (c : Cfg (PR4 k)) :
    ℂ :=
  ODETaggedCayley.scaledEntries (D.matrix x) (partK (D.matrix x) κn (c (pW k))) s ρ
    (Real.sqrt 2 * γ) (swapTag (te en c))

theorem val4_update_oW (D : Data X n Z s) (en : Cfg (Fin k) ≃ n) (x : X) (κn ρ γ : ℝ)
    (c : Cfg (PR4 k)) (v : Bool) :
    val4 D en x κn ρ γ (Function.update c (oW k) v) = val4 D en x κn ρ γ c := by
  have hte : te en (Function.update c (oW k) v) = te en c := by
    unfold te
    rw [Function.update_of_ne (Ne.symm oW_ne_tW)]
    have : (fun e => Function.update c (oW k) v (ix4 k e)) = fun e => c (ix4 k e) := by
      funext e
      exact Function.update_of_ne (ix4_ne_oW e) _ _
    rw [this]
  unfold val4
  rw [Function.update_of_ne (Ne.symm oW_ne_pW), hte]

/-- The lifted edgewise action of the four sectors is the one-qubit edge rotation on the
orientation wire. -/
theorem qlift4_actS4 (D : Data X n Z s) (en : Cfg (Fin k) ≃ n) (x : X) (κn ρ γ : ℝ) :
    qlift4 (R := R) en (actS4 D x κn ρ γ) =
      condOp (oW k) (fun c => edgeMat (val4 D en x κn ρ γ c)) := by
  have h := qlift4_dg_lift (R := R) en (fun p e => ExactEdgeCayley.action
    (ODETaggedCayley.scaledEntries (D.matrix x) (partK (D.matrix x) κn p) s ρ
      (Real.sqrt 2 * γ) (swapTag e)))
  rw [show actS4 D x κn ρ γ = dg (fun p => ODETaggedCayley.lift (fun e => ExactEdgeCayley.action
    (ODETaggedCayley.scaledEntries (D.matrix x) (partK (D.matrix x) κn p) s ρ
      (Real.sqrt 2 * γ) (swapTag e)))) from rfl, h]
  congr 1
  funext c
  rw [qmat_action]
  rfl

/-- The label-selected lifted edgewise action. -/
def A4 (D : Data X n Z s) (en : Cfg (Fin k) ≃ n) (x : X) (kOf γOf : Label kq lq → ℝ) (ρ : ℝ) :
    Reg (LabW kq lq ⊕ PR4 k) R →L[ℂ] Reg (LabW kq lq ⊕ PR4 k) R :=
  localOp Sum.inr Sum.inr_injective (fun y => qlift4 en (actS4 D x
    (kOf (labOfW (fun s => y (Sum.inl s)))) ρ (γOf (labOfW (fun s => y (Sum.inl s))))))

theorem A4_eq (D : Data X n Z s) (en : Cfg (Fin k) ≃ n) (x : X) (kOf γOf : Label kq lq → ℝ)
    (ρ : ℝ) : A4 (R := R) D en x kOf γOf ρ = condOp (Sum.inr (oW k)) (fun z => edgeMat
      (val4 D en x (kOf (labOfW (fun s => z (Sum.inl s)))) ρ
        (γOf (labOfW (fun s => z (Sum.inl s)))) (fun w => z (Sum.inr w)))) := by
  unfold A4
  simp only [qlift4_actS4]
  exact localOp_inr_condOp (oW k) (fun ℓ c => edgeMat (val4 D en x (kOf (labOfW ℓ)) ρ
    (γOf (labOfW ℓ)) c))

/-- **The decoder hypothesis**: after the compute circuit on clean scratch, the decoder takes the
value of the label-selected edgewise gate. -/
def DecOK (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (kOf γOf : Label kq lq → ℝ) (ρ : ℝ) (dec : Cfg (BW4 k b kq lq) → ℂ) : Prop :=
  ∀ c : Cfg (LabW kq lq ⊕ PR4 k), dec (sigma4 D en k0 x (Sum.elim c (fun _ => false))) =
    val4 D en x (kOf (labOfW (fun s => c (Sum.inl s)))) ρ
      (γOf (labOfW (fun s => c (Sum.inl s)))) (fun w => c (Sum.inr w))

theorem posT4_ne_oB4 (a : PY k b) : posT4 (kq := kq) (lq := lq) a ≠ oB4 := by
  rcases a with e | v
  · exact xB4_ne_oB4 e
  · simp [posT4, v14, oB4]

theorem posS4_ne_oB4 (a : PY k b) : posS4 (kq := kq) (lq := lq) a ≠ oB4 := by
  rcases a with e | v
  · exact xB4_ne_oB4 (swE e)
  · simp [posS4, v24, oB4]

theorem sigma4_oB4 (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (y : Cfg (BW4 k b kq lq)) : sigma4 D en k0 x y oB4 = y oB4 := by
  rw [sigma4, Equiv.trans_apply, Equiv.trans_apply,
    alongEquiv_apply_out posS4 _ _ oB4 posS4_ne_oB4,
    alongEquiv_apply_out posT4 _ _ oB4 posT4_ne_oB4]
  rfl

theorem sigma4_update_oB4 (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (x : X) (y : Cfg (BW4 k b kq lq)) (v : Bool) :
    sigma4 D en k0 x (Function.update y oB4 v) = Function.update (sigma4 D en k0 x y) oB4 v := by
  have h1 : sigRef4 D en k0 x (Function.update y oB4 v) =
      Function.update (sigRef4 D en k0 x y) oB4 v :=
    xorEquiv_update_inl _ y (Sum.inr (oW k)) v
  rw [sigma4, Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, h1,
    alongEquiv_update_out posT4 _ _ oB4 v posT4_ne_oB4,
    alongEquiv_update_out posS4 _ _ oB4 v posS4_ne_oB4]

/-- **The decoded rotation** commutes past the permutation of the compute circuit into the
label-selected lifted edgewise action. -/
theorem rdec_sigma4 (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (kOf γOf : Label kq lq → ℝ) (ρ : ℝ)
    (nd : NativeOp (LabW kq lq) (PR4 k) (SZ4 k b) (PY k b) Query) (ho : nd.o = oW k)
    (hdi : ∀ y v, nd.dec (Function.update y (Sum.inl (Sum.inr nd.o)) v) = nd.dec y)
    (hdec : DecOK D en k0 x kOf γOf ρ nd.dec) :
    Rdec (R := R) nd ∘L permOp (sigma4 D en k0 x) ∘L cleanEmb (X := SZ4 k b) =
      permOp (sigma4 D en k0 x) ∘L cleanEmb ∘L A4 D en x kOf γOf ρ := by
  have hR : Rdec (R := R) nd = condOp oB4 (fun y => edgeMat (nd.dec y)) := by
    rw [Rdec, ho]
    rfl
  have hdi' : ∀ y v, nd.dec (Function.update y oB4 v) = nd.dec y := by
    intro y v
    have := hdi y v
    rwa [ho] at this
  apply ext_bas_clm'
  intro c q
  rw [comp_apply, comp_apply, comp_apply, comp_apply, cleanEmb_bas, permOp_bas, hR, condOp_bas,
    A4_eq, condOp_bas, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [map_smul, map_smul, cleanEmb_bas, permOp_bas]
  have hcfg : (Sum.elim (Function.update c (Sum.inr (oW k)) v) (fun _ => false) :
      Cfg (BW4 k b kq lq)) = Function.update (Sum.elim c (fun _ => false)) oB4 v := by
    funext w
    rcases w with p | z
    · by_cases hp : p = Sum.inr (oW k)
      · subst hp
        simp [oB4]
      · have hne : (Sum.inl p : BW4 k b kq lq) ≠ oB4 := fun h => hp (Sum.inl_injective h)
        rw [Function.update_of_ne hne]
        simp [Function.update_of_ne hp]
    · have hne : (Sum.inr z : BW4 k b kq lq) ≠ oB4 := fun h => by cases h
      rw [Function.update_of_ne hne]
      rfl
  rw [hcfg, sigma4_update_oB4, sigma4_oB4]
  congr 2
  have hlab : (fun s => Function.update c (Sum.inr (oW k)) false (Sum.inl s)) =
      fun s => c (Sum.inl s) := by
    funext s
    exact Function.update_of_ne (fun h => by cases h) _ _
  have hpr : (fun w => Function.update c (Sum.inr (oW k)) false (Sum.inr w)) =
      Function.update (fun w => c (Sum.inr w)) (oW k) false :=
    update_comp_injective Sum.inr_injective c (oW k) false
  rw [hdi', hdec c, hlab, hpr, val4_update_oW]

/-- The selected private operation of a family of flat operations. -/
theorem selOp_unconj_fam {Sel S : Type*} [Fintype Sel] [DecidableEq Sel] [Fintype S]
    [DecidableEq S] {a : ℕ} (O : Cfg Sel → Reg (Fin a ⊕ S) R →L[ℂ] Reg (Fin a ⊕ S) R) :
    selOp (fun y => unconj (O y)) =
      localOp Sum.inr Sum.inr_injective (fun y => O (fun s => y (Sum.inl s))) := by
  unfold selOp
  congr 1
  funext y
  exact conj_unconj _

theorem labFam_false {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [CompleteSpace P] {a kq lq : ℕ} (D : Label kq lq → Anc a P →L[ℂ] Anc a P) :
    labFam D false = fun y => D (labOfW y) := rfl

/-- **The native identity** of the four-sector private operation: for a native private operation
with the compute circuit `computeV4` and a decoder satisfying `DecOK`, the native identity holds
for the label-selected private operation `elift4 (act4 D x (kOf z) ρ (γOf z))`. -/
theorem nativeOK4 (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) (x : X) (kOf γOf : Label kq lq → ℝ) (ρ : ℝ)
    (nd : NativeOp (LabW kq lq) (PR4 k) (SZ4 k b) (PY k b) Query)
    (hV : nd.V = computeV4 k b kq lq) (ho : nd.o = oW k) (hpub : nd.Public)
    (hdec : DecOK D en k0 x kOf γOf ρ nd.dec) :
    NativeOK (prims (R := R) D en x) nd
      (selOp (labFam (fun z => elift4 (R := R) en (act4 D x (kOf z) ρ (γOf z))) false)) := by
  have hK1 := compute4_cleanEmb (R := R) (kq := kq) (lq := lq) D en k0 hk0 x
  rw [← hV] at hK1
  have hK2 := rdec_sigma4 (R := R) D en k0 x kOf γOf ρ nd ho hpub.dec_indep hdec
  have hVu : IsUnitary (nrun (prims (R := R) D en x) nd.V) :=
    nrun_isUnitary _ (prims_isUnitary D en x) _ hpub.valid
  have hVV : (nrun (prims (R := R) D en x) nd.V)† ∘L nrun (prims (R := R) D en x) nd.V = 1 := by
    have h := hVu.1
    rwa [star_eq_adjoint, mul_def] at h
  have hFF : F4 (R := R) (kq := kq) (lq := lq) D en x ∘L (F4 D en x)† = 1 := by
    have h := (F4_isUnitary (R := R) (kq := kq) (lq := lq) D en x).2
    rwa [star_eq_adjoint, mul_def] at h
  have hsel : (F4 (R := R) (kq := kq) (lq := lq) D en x)† ∘L A4 D en x kOf γOf ρ ∘L
      F4 D en x = localOp (Sum.inr : PR4 k → LabW kq lq ⊕ PR4 k) Sum.inr_injective
        (fun y => qlift4 (R := R) en (act4 D x (kOf (labOfW (fun s => y (Sum.inl s)))) ρ
          (γOf (labOfW (fun s => y (Sum.inl s)))))) := by
    unfold F4 A4
    rw [localOp_adjoint, localOp_comp, localOp_comp]
    apply localOp_congr
    intro y
    rw [act4_eq_loc4, qlift4_mul, qlift4_mul, qlift4_adjoint, mul_def, mul_def, comp_assoc]
  unfold NativeOK
  rw [nativeOK_of _ _ _ _ _ hK1 hK2 hVV hFF, hsel, labFam_false, selOp_unconj_fam]

end Rdec

end

end SparseHamiltonian.GateBinaryODE
