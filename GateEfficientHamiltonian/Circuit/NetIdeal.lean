import GateEfficientHamiltonian.Circuit.NetLift

/-!
# The ideal boundary network, pointer increment and reuse step

`NET j` is the compressed boundary network at pointer word `j`: the ascending
inverse input frame, the central rotation by `c^(2^m)`, and the descending
output frame.  On embedded reuse states it acts as the chronological network
(`NET_emb`), whose blocks are the transducer blocks of the released analysis
with `J = ι₀` (`chron_boundary`).  Conjugating by the sector-controlled `U_J`
gives the blocks with `J = U_J ι₀` (`BNET_emb`).  The sector-controlled pointer
increment is the cyclic increment of the reuse model (`INC_emb`).
-/

namespace SparseHamiltonian.GateCircuit.Sim

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators
open GatePointerEncoding (wordValue wordEquivFin wordFin successorEquiv)
open ChronologicalResolvent GlobalColligation ChronologicalCatalyst
  FiniteChronologicalInverse GlobalResolvent
open GateDyadicBoundary (centralCosine centralSine)

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Register frames -/

/-- Rotations of slot bits `0, …, n-1` (bit `0` first) at pointer word `j`. -/
def regAscend (j : Fin (cap r + 1)) (R : ℕ → Matrix Bool Bool ℂ) :
    (n : ℕ) → n ≤ m → Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P
  | 0, _ => 1
  | n + 1, h => frameCond j ⟨n, by omega⟩ (R n) ∘L regAscend j R n (by omega)

/-- Rotations of slot bits `n-1, …, 0` (bit `n-1` first) at pointer word `j`. -/
def regDescend (j : Fin (cap r + 1)) (R : ℕ → Matrix Bool Bool ℂ) :
    (n : ℕ) → n ≤ m → Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P
  | 0, _ => 1
  | n + 1, h => regDescend j R n (by omega) ∘L frameCond j ⟨n, by omega⟩ (R n)

omit [CompleteSpace P] in
theorem liftNet_eta (j : Fin (cap r + 1)) (z : Model a m r P) :
    liftNet (fun s : NetState m P => (s.1, s.2)) j z = z := liftNet_id j z

theorem regAscend_emb (j : Fin (cap r + 1)) (R : ℕ → Matrix Bool Bool ℂ) (n : ℕ) (hn : n ≤ m)
    (lw : Word r) (z : Model a m r P) :
    regAscend (K := K) j R n hn (emb lw z) =
      emb lw (liftNet (fun s => (s.1, Dyadic.ascendR R n hn s.2)) j z) := by
  induction n with
  | zero =>
      simp only [regAscend, Dyadic.ascendR, id]
      rw [liftNet_eta]; rfl
  | succ n ih =>
      rw [regAscend, comp_apply, ih (by omega), frameCond_emb, liftNet_liftNet]
      rfl

theorem regDescend_emb (j : Fin (cap r + 1)) (R : ℕ → Matrix Bool Bool ℂ) (n : ℕ)
    (hn : n ≤ m) (lw : Word r) (z : Model a m r P) :
    regDescend (K := K) j R n hn (emb lw z) =
      emb lw (liftNet (fun s => (s.1, Dyadic.descendR R n hn s.2)) j z) := by
  induction n generalizing z with
  | zero =>
      simp only [regDescend, Dyadic.descendR, id]
      rw [liftNet_eta]; rfl
  | succ n ih =>
      rw [regDescend, comp_apply, frameCond_emb, ih (by omega), liftNet_liftNet]
      rfl

def unMats (c : ℝ) : ℕ → Matrix Bool Bool ℂ := fun j => Dyadic.unMat (centralCosine c j)
def outMats (c : ℝ) : ℕ → Matrix Bool Bool ℂ := fun j => Dyadic.outMat (centralCosine c j)

/-- The ideal compressed boundary network at pointer word `j`. -/
def NET (j : Fin (cap r + 1)) (c σ : ℝ) :
    Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P :=
  regDescend j (outMats c) m le_rfl ∘L
    centralCond j (centralCosine c m) (centralSine c σ m) ∘L regAscend j (unMats c) m le_rfl

theorem NET_emb (j : Fin (cap r + 1)) (c σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1)
    (lw : Word r) (z : Model a m r P) :
    NET (K := K) j c σ (emb lw z) = emb lw (liftNet (Dyadic.chron c σ m) j z) := by
  rw [NET, comp_apply, comp_apply, regAscend_emb, centralCond_emb, regDescend_emb,
    liftNet_liftNet, liftNet_liftNet]
  congr 2
  funext s
  rw [Dyadic.chron_eq_compressed c σ hunit]
  simp only [Function.comp_apply, Dyadic.compressed, Dyadic.central,
    Dyadic.inFrameInv_eq, Dyadic.outFrame_eq]
  rfl

/-! ### The ancilla-zero embedding and the transducer blocks -/

/-- The embedding of the system at ancilla configuration zero. -/
def iota0 : P →L[ℂ] Vsp a P :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Cfg (Fin a) => P)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun b => if b = zw a then (1 : P →L[ℂ] P) else 0)

omit [CompleteSpace P] in
theorem iota0_apply (p : P) (b : Cfg (Fin a)) :
    (iota0 (a := a) p) b = if b = zw a then p else 0 := by
  simp only [iota0, comp_apply]
  split_ifs with h <;> simp [h]

theorem iota0_adjoint_apply (v : Vsp a P) : ((iota0 (a := a) (P := P))†) v = v (zw a) := by
  apply ext_inner_right ℂ
  intro p
  rw [adjoint_inner_left, PiLp.inner_apply, Finset.sum_eq_single (zw a)]
  · rw [iota0_apply, if_pos rfl]
  · intro b _ hb; rw [iota0_apply, if_neg hb, inner_zero_right]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem iota0_isometry : (iota0 (a := a) (P := P))† ∘L iota0 = 1 := by
  ext p
  rw [comp_apply, iota0_adjoint_apply, iota0_apply, if_pos rfl]
  rfl

/-- Public block of the transducer. -/
def blkA (c : ℝ) (M : ℕ) : P →L[ℂ] P := ((c : ℂ) • (1 : P →L[ℂ] P)) ^ M

/-- Private-to-public block. -/
def blkB (c σ : ℝ) (J : P →L[ℂ] Vsp a P) (D : Vsp a P →L[ℂ] Vsp a P) (M : ℕ) :
    BlockOperator.H M (Vsp a P) →L[ℂ] P :=
  publicExit ((c : ℂ) • 1) ((-(σ : ℂ)) • (J† ∘L D)) M

/-- Public-to-private block. -/
def blkC (c σ : ℝ) (J : P →L[ℂ] Vsp a P) (M : ℕ) : P →L[ℂ] BlockOperator.H M (Vsp a P) :=
  stackedResponse ((σ : ℂ) • J) ((c : ℂ) • 1) M

/-- Private-to-private block. -/
def blkG (c κ σ : ℝ) (J : P →L[ℂ] Vsp a P) (D : Vsp a P →L[ℂ] Vsp a P) (M : ℕ) :
    BlockOperator.H M (Vsp a P) →L[ℂ] BlockOperator.H M (Vsp a P) :=
  globalPrivateBlock D J c κ σ M

omit [CompleteSpace P] in
theorem smul_one_pow_apply (c : ℂ) (n : ℕ) (p : P) :
    (((c • (1 : P →L[ℂ] P)) ^ n) p) = c ^ n • p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_apply_eq_comp]
      rw [show ((c • (1 : P →L[ℂ] P)) p) = c • p from by simp, map_smul, ih, smul_smul,
        ← pow_succ']

theorem negsig_apply (σ : ℝ) (v : Vsp a P) :
    ((-(σ : ℂ)) • ((iota0 (a := a) (P := P))† ∘L (1 : Vsp a P →L[ℂ] Vsp a P))) v =
      -((σ : ℂ) • v (zw a)) := by
  rw [smul_apply, comp_apply, one_apply_eq_self, iota0_adjoint_apply, neg_smul]

/-- The sequential public amplitude is the forced transducer recursion. -/
theorem seqPub_eq_forced (c σ : ℝ) (p : P) (y : ℕ → Vsp a P) (ψ : ℕ → P)
    (hψ : ∀ k, ψ k = y k (zw a)) (n : ℕ) :
    Dyadic.seqPub c σ p ψ n = (((c : ℂ) • (1 : P →L[ℂ] P)) ^ n) p +
      forcedPublicState ((c : ℂ) • (1 : P →L[ℂ] P))
        ((-(σ : ℂ)) • ((iota0 (a := a) (P := P))† ∘L 1)) y n := by
  induction n with
  | zero => simp [Dyadic.seqPub]
  | succ n ih =>
      rw [Dyadic.seqPub, ih, forcedPublicState_succ, smul_one_pow_apply, smul_one_pow_apply,
        negsig_apply, hψ]
      simp only [smul_apply, one_apply_eq_self, smul_add, pow_succ, smul_smul]
      rw [mul_comm]
      abel

omit [InnerProductSpace ℂ P] [CompleteSpace P] in
theorem extend_wordValue {n : ℕ} (x : BlockOperator.H (2 ^ n) (Vsp a P)) (w : Fin n → Bool) :
    extendSequence x (wordValue w) = x (wordFin w) := by
  simp only [extendSequence, dif_pos (GatePointerEncoding.wordValue_lt_pow w)]
  rfl

/-- The chronological network on one pointer word is the transducer boundary
step with `J = ι₀`. -/
theorem chron_boundary (c κ σ : ℝ) (hκ : κ = 1 - c) (j : Fin (cap r + 1))
    (z : Model a m r P) :
    liftNet (Dyadic.chron c σ m) j z =
      GateBinaryReuse.boundary (blkA c (2 ^ m)) (blkB c σ iota0 1 (2 ^ m))
        (blkC c σ iota0 (2 ^ m)) (blkG c κ σ iota0 1 (2 ^ m)) j z := by
  set y : ℕ → Vsp a P := extendSequence (z.2 j) with hy
  set ψ : ℕ → P := fun k => y k (zw a) with hψdef
  have hψ : ∀ w, ψ (wordValue w) = (netState j z).2 w := by
    intro w
    simp only [hψdef, hy, netState, rd0, extend_wordValue]
    rfl
  have hchron := Dyadic.chron_closed c σ m (z.1 j) (netState j z).2 ψ hψ
  have hforced := seqPub_eq_forced c σ (z.1 j) y ψ (fun k => rfl)
  have hrestrict : (WithLp.toLp 2 (fun k : Fin (2 ^ m) => y k) : BlockOperator.H (2 ^ m) (Vsp a P)) =
      z.2 j := restrict_extend (z.2 j)
  unfold liftNet netWrite
  rw [show netState j z = (z.1 j, (netState j z).2) from rfl, hchron]
  apply Prod.ext
  · funext k
    by_cases hk : k = j
    · subst hk
      simp only [Function.update_self, GateBinaryReuse.boundary, LinearMap.coe_mk,
        AddHom.coe_mk, if_true]
      rw [hforced, blkA, blkB, publicExit_apply]
    · simp only [Function.update_of_ne hk, GateBinaryReuse.boundary, LinearMap.coe_mk,
        AddHom.coe_mk, if_neg hk]
  · funext k
    by_cases hk : k = j
    · subst hk
      simp only [Function.update_self, GateBinaryReuse.boundary, LinearMap.coe_mk,
        AddHom.coe_mk, if_true]
      apply PiLp.ext
      intro s
      apply PiLp.ext
      intro b
      change setAnc0 (z.2 k s) _ b = _
      rw [setAnc0_apply]
      have hG := chronologicalOperator_apply
        (localPrivateBlock 1 (iota0 (a := a) (P := P)) κ) ((σ : ℂ) • iota0) ((c : ℂ) • 1)
        ((-(σ : ℂ)) • ((iota0 (a := a) (P := P))† ∘L 1)) y s
      rw [hrestrict] at hG
      rw [blkC, blkG, globalPrivateBlock]
      simp only [PiLp.add_apply]
      rw [hG, stackedResponse_apply, chronologicalPrivateState]
      have hfs : wordFin ((wordEquivFin m).symm s) = s := (wordEquivFin m).apply_symm_apply s
      have hws : wordValue ((wordEquivFin m).symm s) = s.val := by
        rw [← GatePointerEncoding.wordFin_val, hfs]
      simp only [hws, hforced, localPrivateBlock, comp_apply, sub_apply, one_apply_eq_self,
        smul_apply, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, iota0_apply,
        iota0_adjoint_apply, smul_one_pow_apply]
      have hys : y s = z.2 k s := by
        simp only [hy, extendSequence_apply]
      have hφ : (netState k z).2 ((wordEquivFin m).symm s) = z.2 k s (zw a) := by
        simp only [netState, rd0, GatePointerEncoding.wordEquivFin_apply, hfs]
      rw [hys, hφ]
      by_cases hb : b = zw a
      · subst hb
        simp only [if_true, hκ]
        rw [smul_add]
        simp only [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
        abel
      · simp only [hb, if_false, smul_zero, zero_add, add_zero, sub_zero]
    · simp only [Function.update_of_ne hk, GateBinaryReuse.boundary, LinearMap.coe_mk,
        AddHom.coe_mk, if_neg hk]

end

end SparseHamiltonian.GateCircuit.Sim
