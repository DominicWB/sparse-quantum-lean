import GateEfficientNative.Native.Lift

/-!
# The native register

A released gate-level circuit acts on qubit wires `V` (with a payload); its
oracle calls act on `a` ancilla wires `anc` and the payload, under the
sector wire `sec` (`RelW`).  For the Hamiltonian simulator `V` is
`Wire a m r K` (`wireRel`); for the ODE solver it is the solver register.

The native circuits act on the wires `HW V S X' Z bT bP A`:

* the released wires `V`;
* the system qubits `S` (the payload `R` is an untouched reference);
* the added work wires `XW`: the scratch `Z` of the compute circuit, the
  angle words and arithmetic work wires of the private implementation, and
  three clean flags for the controlled `U_J` gates;
* further work wires `X'` (none for the Hamiltonian simulator).

`ePW ρ selW` places the wires of a private implementation: the enable wire on
the sector wire, the selection wires on `selW`, the private register on the
ancilla and system wires, the scratch and arithmetic wires on the work wires.

`selOracle ρ selW Dfam` is the released form of a sector-controlled, selected
private call; its flattened lift is the lifted native ideal
(`liftB_conj_selOracle`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim
open GateODE (localOp_localOp localOp_localOp' overwrite_apply_ι overwrite_apply_out)
open scoped InnerProduct BigOperators

/-- The released register: wires `V`, `a` ancilla wires and the sector wire. -/
structure RelW (V : Type*) (a : ℕ) where
  anc : Fin a → V
  anc_inj : Function.Injective anc
  sec : V
  anc_ne_sec : ∀ i, anc i ≠ sec

/-- The register of the released Hamiltonian simulator. -/
def wireRel (a m r K : ℕ) : RelW (Wire a m r K) a :=
  ⟨Wire.anc, anc_injective, Wire.sec, fun _ h => by cases h⟩

/-- The added work wires. -/
abbrev XW (Z : Type*) (bT bP A : ℕ) := Z ⊕ (AWr bT bP A ⊕ Fin 3)

/-- The wires of a native circuit. -/
abbrev HW (V S X' Z : Type*) (bT bP A : ℕ) := (V ⊕ S) ⊕ (XW Z bT bP A ⊕ X')

section Layout

variable {V S X' Z Sel : Type*} {a : ℕ} {bT bP A : ℕ}

/-- The released wires. -/
def wEmb : V ↪ HW V S X' Z bT bP A :=
  ⟨fun w => Sum.inl (Sum.inl w), fun _ _ h => Sum.inl_injective (Sum.inl_injective h)⟩

/-- The ancilla and system wires. -/
def pEmb (ρ : RelW V a) : (Fin a ⊕ S) ↪ HW V S X' Z bT bP A :=
  ⟨fun p => Sum.inl (mapId (S := S) ρ.anc p),
    fun _ _ h => mapId_injective (S := S) ρ.anc_inj (Sum.inl_injective h)⟩

/-- The sector wire. -/
def secW (ρ : RelW V a) : HW V S X' Z bT bP A := Sum.inl (Sum.inl ρ.sec)

/-- The three flags of the controlled `U_J` gates. -/
def flagW (i : Fin 3) : HW V S X' Z bT bP A := Sum.inr (Sum.inl (Sum.inr (Sum.inr i)))

/-- The flags as a list. -/
def flagList : List (HW V S X' Z bT bP A) := [flagW 0, flagW 1, flagW 2]

theorem flagList_nodup : (flagList (V := V) (S := S) (X' := X') (Z := Z) (bT := bT) (bP := bP)
    (A := A)).Nodup := by
  simp [flagList, flagW]

/-- Selection wires of the released register, off the sector and ancilla wires. -/
structure SelWires (ρ : RelW V a) (Sel : Type*) where
  emb : Sel ↪ V
  ne_sec : ∀ s, emb s ≠ ρ.sec
  ne_anc : ∀ s i, emb s ≠ ρ.anc i

/-- The placement of the private implementation wires. -/
def ePWfun (ρ : RelW V a) (sw : SelWires ρ Sel) :
    PWr Sel (Fin a ⊕ S) Z bT bP A → HW V S X' Z bT bP A
  | Sum.inl _ => secW ρ
  | Sum.inr (Sum.inl (Sum.inl (Sum.inl s))) => Sum.inl (Sum.inl (sw.emb s))
  | Sum.inr (Sum.inl (Sum.inl (Sum.inr q))) => pEmb ρ q
  | Sum.inr (Sum.inl (Sum.inr z)) => Sum.inr (Sum.inl (Sum.inl z))
  | Sum.inr (Sum.inr w) => Sum.inr (Sum.inl (Sum.inr (Sum.inl w)))

theorem ePWfun_injective (ρ : RelW V a) (sw : SelWires ρ Sel) :
    Function.Injective (ePWfun (S := S) (X' := X') (Z := Z) (bT := bT) (bP := bP) (A := A)
      ρ sw) := by
  have h1 := sw.ne_sec
  have h2 := sw.ne_anc
  have h3 := ρ.anc_ne_sec
  have h4 := ρ.anc_inj
  intro p q h
  rcases p with ⟨⟩ | (((s | (i | x)) | z) | w) <;>
  rcases q with ⟨⟩ | (((s' | (i' | x')) | z') | w') <;>
  (try simp only [ePWfun, secW, pEmb, mapId, Function.Embedding.coeFn_mk, Sum.map_inl,
    Sum.map_inr, id, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
    EmbeddingLike.apply_eq_iff_eq] at h) <;>
  first
    | rfl
    | (subst h; rfl)
    | (obtain rfl := h4 h; rfl)
    | exact absurd h (h1 _)
    | exact absurd h.symm (h1 _)
    | exact absurd h (h2 _ _)
    | exact absurd h.symm (h2 _ _)
    | exact absurd h (h3 _)
    | exact absurd h.symm (h3 _)

/-- The placement of the private implementation wires. -/
def ePW (ρ : RelW V a) (sw : SelWires ρ Sel) :
    PWr Sel (Fin a ⊕ S) Z bT bP A ↪ HW V S X' Z bT bP A :=
  ⟨ePWfun ρ sw, ePWfun_injective ρ sw⟩

/-- No selection wires. -/
def noSel (ρ : RelW V a) : SelWires ρ Empty :=
  ⟨⟨Empty.elim, fun x => x.elim⟩, fun s => s.elim, fun s => s.elim⟩

end Layout

/-- The slot wires of the released simulator. -/
def slotSel (a m r K : ℕ) : SelWires (wireRel a m r K) (Fin m) :=
  ⟨⟨Wire.slot, fun _ _ h => by cases h; rfl⟩, (fun _ h => by cases h), (fun _ _ h => by cases h)⟩

/-! ### Selected private calls -/

section SelOracle

variable {V S X' Z Sel : Type*} [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S]
  [Fintype X'] [DecidableEq X'] [Fintype Z] [DecidableEq Z] [Fintype Sel] [DecidableEq Sel]
  {a : ℕ} {bT bP A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- A sector-controlled private call selected by the configuration of the
selection wires. -/
def selOracle (ρ : RelW V a) (sw : SelWires ρ Sel)
    (Dfam : Cfg Sel → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R))) :
    Reg V (Reg S R) →L[ℂ] Reg V (Reg S R) :=
  localOp ρ.anc ρ.anc_inj (fun x => if x ρ.sec then Dfam (fun s => x (sw.emb s)) else 1)

omit [Fintype Sel] [DecidableEq Sel] in
/-- The lifted selected call in canonical form: on the ancilla and system wires,
when the sector wire is set. -/
theorem liftB_conj_selOracle_canon (ρ : RelW V a) (sw : SelWires ρ Sel)
    (Dfam : Cfg Sel → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R))) :
    liftB (X := XW Z bT bP A ⊕ X') (conj (selOracle ρ sw Dfam)) =
      localOp (fun p => (Sum.inl (mapId (S := S) ρ.anc p) : HW V S X' Z bT bP A))
        (pEmb (S := S) (X' := X') (Z := Z) (bT := bT) (bP := bP) (A := A) ρ).injective
        (fun w => if w (secW ρ) then conj (Dfam (fun s => w (Sum.inl (Sum.inl (sw.emb s)))))
          else 1) := by
  unfold liftB selOracle
  rw [conj_localOp ρ.anc_inj]
  rw [localOp_localOp' Sum.inl_injective (mapId_injective (S := S) ρ.anc_inj)
    (fun p => (Sum.inl (mapId (S := S) ρ.anc p) : HW V S X' Z bT bP A))
    (pEmb (S := S) (X' := X') (Z := Z) (bT := bT) (bP := bP) (A := A) ρ).injective
    (fun _ => rfl)]
  apply localOp_congr
  intro z
  set z' := clearCfg (fun p => (Sum.inl (mapId (S := S) ρ.anc p) : HW V S X' Z bT bP A)) z
  have hw : ∀ w : V, (∀ i, ρ.anc i ≠ w) →
      clearCfg (mapId (S := S) ρ.anc) (fun b => z' (Sum.inl b)) (Sum.inl w) =
        z' (Sum.inl (Sum.inl w)) := by
    intro w hw
    exact clearCfg_apply_out _ _ (Sum.inl w) (fun c hc => by
      cases c with
      | inl i => exact hw i (Sum.inl_injective hc)
      | inr s => cases hc)
  have hsec := hw ρ.sec ρ.anc_ne_sec
  have hsel : ∀ s, clearCfg (mapId (S := S) ρ.anc) (fun b => z' (Sum.inl b))
        (Sum.inl (sw.emb s)) = z' (Sum.inl (Sum.inl (sw.emb s))) :=
    fun s => hw (sw.emb s) (fun i h => sw.ne_anc s i h.symm)
  beta_reduce
  simp only [hsec, hsel]
  unfold secW
  by_cases h : z' (Sum.inl (Sum.inl ρ.sec)) = true
  · simp only [h, if_true]
  · simp only [h, Bool.false_eq_true, if_false, conj_one]

/-- **The lifted selected private call is the lifted native ideal.** -/
theorem liftB_conj_selOracle (ρ : RelW V a) (sw : SelWires ρ Sel)
    (Dfam : Cfg Sel → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R))) :
    liftB (X := XW Z bT bP A ⊕ X') (conj (selOracle ρ sw Dfam)) =
      localOp (ePW (S := S) (X' := X') (Z := Z) (bT := bT) (bP := bP) (A := A) ρ sw)
        (ePW ρ sw).injective (fun _ => ctrlIdeal (selOp Dfam)) := by
  have hR : localOp (ePW (S := S) (X' := X') (Z := Z) (bT := bT) (bP := bP) (A := A) ρ sw)
      (ePW ρ sw).injective (fun _ => ctrlIdeal (selOp Dfam)) =
      localOp (fun p => (Sum.inl (mapId (S := S) ρ.anc p) : HW V S X' Z bT bP A))
        (pEmb (S := S) (X' := X') (Z := Z) (bT := bT) (bP := bP) (A := A) ρ).injective
        (fun w => if w (secW ρ) then conj (Dfam (fun s => w (Sum.inl (Sum.inl (sw.emb s)))))
          else 1) :=
    localOp_ctrlIdeal_selOp (ePW ρ sw) Dfam
  rw [hR, liftB_conj_selOracle_canon]

end SelOracle

/-! ### Wire counts -/

section Card

variable {V S X' Z : Type*} [Fintype V] [Fintype S] [Fintype X'] [Fintype Z]

theorem card_HW (bT bP A : ℕ) :
    Fintype.card (HW V S X' Z bT bP A) =
      Fintype.card V + Fintype.card S + (Fintype.card Z + bT + bP + A + 3 + Fintype.card X') := by
  simp only [HW, XW, AWr, Fintype.card_sum, Fintype.card_fin]
  ring

end Card

end

end SparseHamiltonian.GateNative
