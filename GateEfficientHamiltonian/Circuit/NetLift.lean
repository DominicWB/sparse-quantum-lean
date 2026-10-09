import GateEfficientHamiltonian.Circuit.Layout

/-!
# The boundary network on embedded reuse states

At one pointer word `j`, the public mode and the ancilla-zero components of
the private slots form a network state `(p, φ)` of the dyadic analysis.  The
ideal slot-bit rotations and the central sector rotation of the boundary
network act on embedded states exactly as the corresponding network-state
operations (`frameCond_emb`, `centralCond_emb`).
-/

namespace SparseHamiltonian.GateCircuit.Sim

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators
open GatePointerEncoding (wordValue wordEquivFin wordFin)
open ChronologicalResolvent

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Network states of one pointer word -/

theorem sum_one_update' {W Q : Type*} [DecidableEq W] [AddCommGroup Q] [Module ℂ Q]
    (f : Cfg W → Q) (x : Cfg W) (t : W) :
    (∑ b : Bool, (1 : Matrix Bool Bool ℂ) (x t) b • f (Function.update x t b)) = f x := by
  rw [Finset.sum_eq_single (x t)]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ _) h

@[simp] theorem wordEquivFin_symm_wordFin {n : ℕ} (w : Fin n → Bool) :
    (wordEquivFin n).symm (wordFin w) = w := (wordEquivFin n).symm_apply_apply w

omit [CompleteSpace P] in
theorem embVal_unclean (lw : Word r) (z : Model a m r P) (x : Cfg (Wire a m r K))
    (hc : ¬ (labOf x = lw ∧ Clean x)) : embVal lw z x = 0 := by
  simp [embVal, hc]

omit [CompleteSpace P] in
theorem embVal_private (lw : Word r) (z : Model a m r P) (x : Cfg (Wire a m r K))
    (hc : labOf x = lw ∧ Clean x) (hs : x .sec = true) :
    embVal lw z x = z.2 (ptrIdx x) (slotIdx x) (ancOf x) := by
  simp [embVal, hc, hs]

omit [CompleteSpace P] in
theorem embVal_public (lw : Word r) (z : Model a m r P) (x : Cfg (Wire a m r K))
    (hc : labOf x = lw ∧ Clean x) (hs : x .sec = false) :
    embVal lw z x = if slotOf x = zw m ∧ ancOf x = zw a then z.1 (ptrIdx x) else 0 := by
  simp [embVal, hc, hs]

/-- The ancilla-zero component of a private slot vector. -/
def rd0 (v : Vsp a P) : P := v (zw a)

/-- Replace the ancilla-zero component of a private slot vector. -/
def setAnc0 (v : Vsp a P) (q : P) : Vsp a P :=
  WithLp.toLp 2 (fun b => if b = zw a then q else v b)

omit [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P] in
@[simp] theorem rd0_setAnc0 (v : Vsp a P) (q : P) : rd0 (setAnc0 v q) = q := by
  simp [rd0, setAnc0]

omit [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P] in
theorem setAnc0_apply (v : Vsp a P) (q : P) (b : Cfg (Fin a)) :
    setAnc0 v q b = if b = zw a then q else v b := rfl

omit [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P] in
@[simp] theorem setAnc0_setAnc0 (v : Vsp a P) (q q' : P) :
    setAnc0 (setAnc0 v q) q' = setAnc0 v q' := by
  apply PiLp.ext; intro b; by_cases hb : b = zw a <;> simp [setAnc0_apply, hb]

/-- Network state: public amplitude and ancilla-zero slot amplitudes. -/
abbrev NetState (m : ℕ) (P : Type*) := P × (Dyadic.Word m → P)

def netState (j : Fin (cap r + 1)) (z : Model a m r P) : NetState m P :=
  (z.1 j, fun w => rd0 (z.2 j (wordEquivFin m w)))

def netWrite (j : Fin (cap r + 1)) (z : Model a m r P) (s : NetState m P) :
    Model a m r P :=
  (Function.update z.1 j s.1,
   Function.update z.2 j
     (WithLp.toLp 2 (fun σ => setAnc0 (z.2 j σ) (s.2 ((wordEquivFin m).symm σ)))))

/-- Apply a network-state operation at pointer word `j`. -/
def liftNet (F : NetState m P → NetState m P) (j : Fin (cap r + 1)) (z : Model a m r P) :
    Model a m r P :=
  netWrite j z (F (netState j z))

omit [CompleteSpace P] in
@[simp] theorem netState_netWrite (j : Fin (cap r + 1)) (z : Model a m r P)
    (s : NetState m P) : netState j (netWrite j z s) = s := by
  obtain ⟨p, φ⟩ := s
  simp only [netState, netWrite, Function.update_self]
  refine Prod.ext rfl ?_
  funext w
  change rd0 (setAnc0 (z.2 j _) (φ ((wordEquivFin m).symm (wordEquivFin m w)))) = φ w
  simp

omit [CompleteSpace P] in
theorem netWrite_netWrite (j : Fin (cap r + 1)) (z : Model a m r P) (s s' : NetState m P) :
    netWrite j (netWrite j z s) s' = netWrite j z s' := by
  simp only [netWrite, Function.update_idem, Function.update_self]
  congr 2
  apply PiLp.ext
  intro σ
  change setAnc0 (setAnc0 (z.2 j σ) _) _ = _
  rw [setAnc0_setAnc0]

omit [CompleteSpace P] in
theorem liftNet_liftNet (F G : NetState m P → NetState m P) (j : Fin (cap r + 1))
    (z : Model a m r P) : liftNet F j (liftNet G j z) = liftNet (F ∘ G) j z := by
  simp only [liftNet, netState_netWrite, netWrite_netWrite, Function.comp_apply]

omit [CompleteSpace P] in
theorem liftNet_id (j : Fin (cap r + 1)) (z : Model a m r P) :
    liftNet (fun s => s) j z = z := by
  simp only [liftNet, netState, netWrite]
  apply Prod.ext
  · simp
  · funext k
    by_cases hk : k = j
    · subst hk
      simp only [Function.update_self]
      apply PiLp.ext; intro σ
      apply PiLp.ext; intro b
      change setAnc0 (z.2 k σ) _ b = _
      rw [setAnc0_apply]
      split_ifs with hb
      · subst hb; simp [rd0]
      · rfl
    · simp [Function.update_of_ne hk]

omit [CompleteSpace P] in
/-- Value of an embedded state after writing a network state. -/
theorem embVal_netWrite (lw : Word r) (j : Fin (cap r + 1)) (z : Model a m r P)
    (s : NetState m P) (x : Cfg (Wire a m r K)) :
    embVal lw (netWrite j z s) x =
      if (labOf x = lw ∧ Clean x) ∧ ptrIdx x = j then
        (if x .sec then (if ancOf x = zw a then s.2 (slotOf x) else z.2 j (slotIdx x) (ancOf x))
         else if slotOf x = zw m ∧ ancOf x = zw a then s.1 else 0)
      else embVal lw z x := by
  unfold embVal
  by_cases hc : labOf x = lw ∧ Clean x
  · by_cases hj : ptrIdx x = j
    · simp only [hc, hj, and_self, if_true, netWrite, Function.update_self]
      split_ifs with hs ha
      · change setAnc0 (z.2 j (slotIdx x)) _ (ancOf x) = _
        rw [setAnc0_apply, if_pos ha]
        simp [slotIdx]
      · change setAnc0 (z.2 j (slotIdx x)) _ (ancOf x) = _
        rw [setAnc0_apply, if_neg ha]
      · rfl
      · rfl
    · simp only [hc, hj, and_false, if_false, true_and, netWrite,
        Function.update_of_ne hj]
  · simp only [hc, false_and, if_false]

/-! ### Updating one slot bit or the sector bit -/

theorem labOf_update_ne (x : Cfg (Wire a m r K)) (w : Wire a m r K) (b : Bool)
    (hw : ∀ i, Wire.lab i ≠ w) : labOf (Function.update x w b) = labOf x := by
  funext i; exact Function.update_of_ne (hw i) _ _

theorem ptrOf_update_ne (x : Cfg (Wire a m r K)) (w : Wire a m r K) (b : Bool)
    (hw : ∀ i, Wire.ptr i ≠ w) : ptrOf (Function.update x w b) = ptrOf x := by
  funext i; exact Function.update_of_ne (hw i) _ _

theorem ancOf_update_ne (x : Cfg (Wire a m r K)) (w : Wire a m r K) (b : Bool)
    (hw : ∀ i, Wire.anc i ≠ w) : ancOf (Function.update x w b) = ancOf x := by
  funext i; exact Function.update_of_ne (hw i) _ _

theorem slotOf_update_ne (x : Cfg (Wire a m r K)) (w : Wire a m r K) (b : Bool)
    (hw : ∀ i, Wire.slot i ≠ w) : slotOf (Function.update x w b) = slotOf x := by
  funext i; exact Function.update_of_ne (hw i) _ _

theorem clean_update_logical (x : Cfg (Wire a m r K)) (w : Wire a m r K) (b : Bool)
    (hw : isFlag w = false) : Clean (Function.update x w b) ↔ Clean x := by
  unfold Clean
  constructor
  · intro h v hv
    have hne : v ≠ w := by intro e; subst e; simp [hv] at hw
    have := h v hv; rwa [Function.update_of_ne hne] at this
  · intro h v hv
    have hne : v ≠ w := by intro e; subst e; simp [hv] at hw
    rw [Function.update_of_ne hne]; exact h v hv

theorem slotOf_update_slot (x : Cfg (Wire a m r K)) (i : Fin m) (b : Bool) :
    slotOf (Function.update x (Wire.slot i) b) = Function.update (slotOf x) i b := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [slotOf]
  · simp only [slotOf]
    rw [Function.update_of_ne (fun h => hk (by cases h; rfl)), Function.update_of_ne hk]
    rfl

theorem ptrIdx_update_ne (x : Cfg (Wire a m r K)) (w : Wire a m r K) (b : Bool)
    (hw : ∀ i, Wire.ptr i ≠ w) : ptrIdx (Function.update x w b) = ptrIdx x := by
  simp [ptrIdx, ptrOf_update_ne x w b hw]

/-! ### Ideal network rotations -/

/-- Ideal rotation of slot bit `i` at pointer word `j`, on the private
ancilla-zero sector, where the lower slot bits vanish. -/
def frameCond (j : Fin (cap r + 1)) (i : Fin m) (R : Matrix Bool Bool ℂ) :
    Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P :=
  condOp (Wire.slot i) (fun x => if x .sec = true ∧ ancOf x = zw a ∧ ptrIdx x = j ∧
    Dyadic.lowerZero i (slotOf x) then R else 1)

/-- The sector rotation matrix (rows: new sector, columns: old sector). -/
def rotMat (z v : ℝ) : Matrix Bool Bool ℂ := fun row col =>
  match row, col with
  | false, false => (z : ℂ)
  | false, true => -(v : ℂ)
  | true, false => (v : ℂ)
  | true, true => (z : ℂ)

/-- Ideal central rotation between the public mode and the private root. -/
def centralCond (j : Fin (cap r + 1)) (zz vv : ℝ) :
    Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P :=
  condOp Wire.sec (fun x => if ancOf x = zw a ∧ ptrIdx x = j ∧ slotOf x = zw m then
    rotMat zz vv else 1)

theorem frameCond_emb (j : Fin (cap r + 1)) (i : Fin m) (R : Matrix Bool Bool ℂ)
    (lw : Word r) (z : Model a m r P) :
    frameCond (K := K) j i R (emb lw z) =
      emb lw (liftNet (fun s => (s.1, Dyadic.bitRot i R s.2)) j z) := by
  apply PiLp.ext
  intro x
  rw [frameCond, condOp_apply, emb_apply, liftNet, embVal_netWrite]
  simp only [emb_apply]
  have hlab : ∀ b, labOf (Function.update x (Wire.slot i) b) = labOf x :=
    fun b => labOf_update_ne x _ b (fun _ h => by cases h)
  have hcl : ∀ b, Clean (Function.update x (Wire.slot i) b) ↔ Clean x :=
    fun b => clean_update_logical x _ b rfl
  have hsec : ∀ b, Function.update x (Wire.slot i) b .sec = x .sec :=
    fun b => Function.update_of_ne (fun h => by cases h) _ _
  have hanc : ∀ b, ancOf (Function.update x (Wire.slot i) b) = ancOf x :=
    fun b => ancOf_update_ne x _ b (fun _ h => by cases h)
  have hptr : ∀ b, ptrIdx (Function.update x (Wire.slot i) b) = ptrIdx x :=
    fun b => ptrIdx_update_ne x _ b (fun _ h => by cases h)
  have hlz : Dyadic.lowerZero i (slotOf (Function.update x (Wire.slot i) false)) ↔
      Dyadic.lowerZero i (slotOf x) := by
    rw [slotOf_update_slot]
    unfold Dyadic.lowerZero
    constructor
    · intro h k hk; have := h k hk; rwa [Function.update_of_ne (ne_of_lt hk)] at this
    · intro h k hk; rw [Function.update_of_ne (ne_of_lt hk)]; exact h k hk
  have hxi : x (Wire.slot i) = slotOf x i := rfl
  simp only [hsec, hanc, hptr]
  by_cases hc : labOf x = lw ∧ Clean x
  · have hc' : ∀ b, labOf (Function.update x (Wire.slot i) b) = lw ∧
        Clean (Function.update x (Wire.slot i) b) := fun b => by rw [hlab, hcl]; exact hc
    by_cases hp : x .sec = true ∧ ancOf x = zw a ∧ ptrIdx x = j ∧
        Dyadic.lowerZero i (slotOf x)
    · obtain ⟨hs, ha, hj, hl⟩ := hp
      rw [if_pos ⟨hs, ha, hj, hlz.mpr hl⟩, if_pos ⟨hc, hj⟩, if_pos hs, if_pos ha]
      simp only [Dyadic.bitRot, netState, if_pos hl, hxi]
      apply Finset.sum_congr rfl
      intro b _
      rw [embVal_private lw z _ (hc' b) (by rw [hsec]; exact hs), hptr, hanc, ha, hj,
        slotIdx, slotOf_update_slot]
      simp [rd0]
    · have hp' : ¬ (x .sec = true ∧ ancOf x = zw a ∧ ptrIdx x = j ∧
          Dyadic.lowerZero i (slotOf (Function.update x (Wire.slot i) false))) := by
        rwa [hlz]
      rw [if_neg hp', sum_one_update']
      by_cases hj : ptrIdx x = j
      · rw [if_pos ⟨hc, hj⟩]
        cases hs : x .sec
        · rw [embVal_public lw z x hc hs, hj]
          simp [netState]
        · rw [embVal_private lw z x hc hs, hj, if_pos rfl]
          by_cases ha : ancOf x = zw a
          · rw [if_pos ha]
            have hl : ¬ Dyadic.lowerZero i (slotOf x) := fun hl => hp ⟨hs, ha, hj, hl⟩
            simp only [netState, Dyadic.bitRot, if_neg hl, rd0, slotIdx, ha]
          · rw [if_neg ha]
      · rw [if_neg (fun h => hj h.2)]
  · have h0 : ∀ b, embVal lw z (Function.update x (Wire.slot i) b) = 0 := by
      intro b; apply embVal_unclean; rw [hlab, hcl]; exact hc
    simp only [h0, smul_zero, Finset.sum_const_zero]
    rw [if_neg (fun h => hc h.1), embVal_unclean lw z x hc]

theorem centralCond_emb (j : Fin (cap r + 1)) (zz vv : ℝ) (lw : Word r) (z : Model a m r P) :
    centralCond (K := K) j zz vv (emb lw z) =
      emb lw (liftNet (fun s => let q := Dyadic.rot zz vv s.1 (s.2 (Dyadic.zeroW m));
        (q.1, Dyadic.setRoot s.2 q.2)) j z) := by
  apply PiLp.ext
  intro x
  rw [centralCond, condOp_apply, emb_apply, liftNet, embVal_netWrite]
  simp only [emb_apply]
  have hlab : ∀ b, labOf (Function.update x Wire.sec b) = labOf x :=
    fun b => labOf_update_ne x _ b (fun _ h => by cases h)
  have hcl : ∀ b, Clean (Function.update x Wire.sec b) ↔ Clean x :=
    fun b => clean_update_logical x _ b rfl
  have hanc : ∀ b, ancOf (Function.update x Wire.sec b) = ancOf x :=
    fun b => ancOf_update_ne x _ b (fun _ h => by cases h)
  have hptr : ∀ b, ptrIdx (Function.update x Wire.sec b) = ptrIdx x :=
    fun b => ptrIdx_update_ne x _ b (fun _ h => by cases h)
  have hslot : ∀ b, slotOf (Function.update x Wire.sec b) = slotOf x :=
    fun b => slotOf_update_ne x _ b (fun _ h => by cases h)
  have hslotIdx : ∀ b, slotIdx (Function.update x Wire.sec b) = slotIdx x := by
    intro b; simp only [slotIdx, hslot]
  simp only [hanc, hptr, hslot]
  by_cases hc : labOf x = lw ∧ Clean x
  · have hc' : ∀ b, labOf (Function.update x Wire.sec b) = lw ∧
        Clean (Function.update x Wire.sec b) := fun b => by rw [hlab, hcl]; exact hc
    by_cases hp : ancOf x = zw a ∧ ptrIdx x = j ∧ slotOf x = zw m
    · obtain ⟨ha, hj, hz⟩ := hp
      rw [if_pos ⟨ha, hj, hz⟩, if_pos ⟨hc, hj⟩, Fintype.sum_bool]
      have e0 : embVal lw z (Function.update x Wire.sec false) = z.1 j := by
        rw [embVal_public lw z _ (hc' false) (Function.update_self ..), hslot, hanc, hptr,
          if_pos ⟨hz, ha⟩, hj]
      have e1 : embVal lw z (Function.update x Wire.sec true) =
          rd0 (z.2 j (wordEquivFin m (Dyadic.zeroW m))) := by
        rw [embVal_private lw z _ (hc' true) (Function.update_self ..), hptr, hslotIdx, hanc,
          ha, hj, slotIdx, hz]
        rfl
      rw [e0, e1]
      cases hs : x .sec
      · rw [if_neg (by simp), if_pos ⟨hz, ha⟩]
        simp only [netState, Dyadic.rot, rotMat]
        rw [neg_smul]
        abel
      · rw [if_pos rfl, if_pos ha, hz]
        show _ = Dyadic.setRoot _ _ (Dyadic.zeroW m)
        rw [Dyadic.setRoot_zero]
        simp only [netState, Dyadic.rot, rotMat]
        abel
    · rw [if_neg hp, sum_one_update']
      by_cases hj : ptrIdx x = j
      · rw [if_pos ⟨hc, hj⟩]
        cases hs : x .sec
        · rw [embVal_public lw z x hc hs]
          simp only [Bool.false_eq_true, if_false]
          by_cases hza : slotOf x = zw m ∧ ancOf x = zw a
          · exact absurd ⟨hza.2, hj, hza.1⟩ hp
          · rw [if_neg hza, if_neg hza]
        · rw [embVal_private lw z x hc hs, hj, if_pos rfl]
          by_cases ha : ancOf x = zw a
          · rw [if_pos ha]
            have hz : slotOf x ≠ Dyadic.zeroW m := fun hz => hp ⟨ha, hj, hz⟩
            simp only [Dyadic.setRoot_ne _ _ _ hz, netState, rd0, slotIdx, ha]
          · rw [if_neg ha]
      · rw [if_neg (fun h => hj h.2)]
  · have h0 : ∀ b, embVal lw z (Function.update x Wire.sec b) = 0 := by
      intro b; apply embVal_unclean; rw [hlab, hcl]; exact hc
    simp only [h0, smul_zero, Finset.sum_const_zero]
    rw [if_neg (fun h => hc h.1), embVal_unclean lw z x hc]

end

end SparseHamiltonian.GateCircuit.Sim
