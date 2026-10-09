import GateEfficientHamiltonian.Circuit.NetIdeal

/-!
# The reuse step and the SELECT block

One reuse step at pointer word `j` is the sector-controlled private Cayley
call, the `U_J`-conjugated boundary network at `j`, and the sector-controlled
pointer increment.  On embedded states it is exactly the step of the binary
reuse model `GateBinaryReuse` (`STEP_emb`), with effective transducer blocks
equal to those of the released analysis for `J = U_J ι₀` (`blkB_net`,
`blkC_net`, `blkG_net`).

`select_block` evaluates the SELECT circuit (all `N ≥ n` steps, independently
of the branch length `n`) between uniform pointer states of length `n`: it is
the coherent-reuse successful block of length `n`.
-/

namespace SparseHamiltonian.GateCircuit.Sim

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators
open GatePointerEncoding (wordValue wordEquivFin wordFin successorEquiv)
open ChronologicalResolvent GlobalColligation ChronologicalCatalyst
  FiniteChronologicalInverse GlobalResolvent CoherentReuse
open GateDyadicBoundary (centralCosine centralSine)

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Conjugating a boundary step by private operations -/

omit [CompleteSpace P] in
theorem pE_boundary_pE (X Y : HV a m P →L[ℂ] HV a m P) (hXY : ∀ v, X (Y v) = v)
    (A : P →L[ℂ] P) (B : HV a m P →L[ℂ] P) (C : P →L[ℂ] HV a m P) (G : HV a m P →L[ℂ] HV a m P)
    (j : Fin (cap r + 1)) (z : Model a m r P) :
    GateBinaryReuse.privateEverywhere X (cap r)
        (GateBinaryReuse.boundary A B C G j (GateBinaryReuse.privateEverywhere Y (cap r) z)) =
      GateBinaryReuse.boundary A (B ∘L Y) (X ∘L C) (X ∘L G ∘L Y) j z := by
  apply Prod.ext
  · funext k
    simp only [GateBinaryReuse.privateEverywhere, GateBinaryReuse.boundary, LinearMap.coe_mk,
      AddHom.coe_mk, comp_apply]
  · funext k
    simp only [GateBinaryReuse.privateEverywhere, GateBinaryReuse.boundary, LinearMap.coe_mk,
      AddHom.coe_mk, comp_apply]
    split_ifs
    · simp
    · exact hXY _

/-- The `U_J`-conjugated boundary network at pointer word `j`. -/
def BNET (j : Fin (cap r + 1)) (c σ : ℝ) (UJ : Vsp a P →L[ℂ] Vsp a P) :
    Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P :=
  secOracle UJ ∘L NET j c σ ∘L secOracle (UJ†)

/-- Effective network blocks before the private call. -/
def netB (c σ : ℝ) (UJ : Vsp a P →L[ℂ] Vsp a P) : HV a m P →L[ℂ] P :=
  blkB c σ iota0 1 (2 ^ m) ∘L diagV (UJ†)

def netC (c σ : ℝ) (UJ : Vsp a P →L[ℂ] Vsp a P) : P →L[ℂ] HV a m P :=
  diagV UJ ∘L blkC c σ iota0 (2 ^ m)

def netG (c κ σ : ℝ) (UJ : Vsp a P →L[ℂ] Vsp a P) : HV a m P →L[ℂ] HV a m P :=
  diagV UJ ∘L blkG c κ σ iota0 1 (2 ^ m) ∘L diagV (UJ†)

theorem BNET_emb (j : Fin (cap r + 1)) (c κ σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1)
    (hκ : κ = 1 - c) (UJ : Vsp a P →L[ℂ] Vsp a P) (hUJ : UJ ∘L UJ† = 1)
    (lw : Word r) (z : Model a m r P) :
    BNET (K := K) j c σ UJ (emb lw z) =
      emb lw (GateBinaryReuse.boundary (blkA c (2 ^ m)) (netB c σ UJ) (netC c σ UJ)
        (netG c κ σ UJ) j z) := by
  rw [BNET, comp_apply, comp_apply, secOracle_emb, NET_emb j c σ hunit, chron_boundary c κ σ hκ,
    secOracle_emb, pE_boundary_pE]
  · rfl
  · intro v
    apply PiLp.ext
    intro k
    simp only [diagV_apply]
    have := congrArg (fun F : Vsp a P →L[ℂ] Vsp a P => F (v k)) hUJ
    simpa using this

/-! ### The effective blocks are those of the released analysis -/

omit [CompleteSpace P] in
theorem diagV_comp (X Y : Vsp a P →L[ℂ] Vsp a P) :
    diagV (m := m) X ∘L diagV Y = diagV (X ∘L Y) := by
  ext v k : 2
  rfl

omit [CompleteSpace P] in
theorem publicExit_comp_diag (u : P →L[ℂ] P) (B : Vsp a P →L[ℂ] P) (O : Vsp a P →L[ℂ] Vsp a P) :
    publicExit u B (2 ^ m) ∘L diagV O = publicExit u (B ∘L O) (2 ^ m) := by
  ext v
  simp only [comp_apply, publicExit, sum_apply]
  rfl

omit [CompleteSpace P] in
theorem chronological_diag (R : Vsp a P →L[ℂ] Vsp a P) (A : P →L[ℂ] Vsp a P) (u : P →L[ℂ] P)
    (B : Vsp a P →L[ℂ] P) (X Y : Vsp a P →L[ℂ] Vsp a P) :
    diagV X ∘L chronologicalOperator R A u B (2 ^ m) ∘L diagV Y =
      chronologicalOperator (X ∘L R ∘L Y) (X ∘L A) u (B ∘L Y) (2 ^ m) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  simp only [comp_apply, diagV_apply, chronologicalOperator, BlockOperator.blocks_apply,
    map_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold chronologicalBlock
  split_ifs <;> simp [comp_apply]

theorem blkB_net (c σ : ℝ) (UJ D : Vsp a P →L[ℂ] Vsp a P) :
    netB (m := m) c σ UJ ∘L diagV D = blkB c σ (UJ ∘L iota0) D (2 ^ m) := by
  rw [netB, comp_assoc, diagV_comp, blkB, blkB, publicExit_comp_diag]
  congr 1
  ext v
  simp only [comp_apply, smul_apply, one_apply_eq_self, adjoint_comp]

omit [CompleteSpace P] in
theorem blkC_net (c σ : ℝ) (UJ : Vsp a P →L[ℂ] Vsp a P) :
    netC (m := m) c σ UJ = blkC c σ (UJ ∘L iota0) (2 ^ m) := by
  apply ContinuousLinearMap.ext
  intro p
  apply PiLp.ext
  intro k
  simp [netC, blkC, diagV_apply, stackedResponse_apply]

theorem blkG_net (c κ σ : ℝ) (UJ D : Vsp a P →L[ℂ] Vsp a P) (hUJ : UJ ∘L UJ† = 1) :
    netG (m := m) c κ σ UJ ∘L diagV D = blkG c κ σ (UJ ∘L iota0) D (2 ^ m) := by
  rw [netG, comp_assoc, comp_assoc, diagV_comp, blkG, blkG,
    globalPrivateBlock, globalPrivateBlock, chronological_diag]
  have h1 : ∀ v, UJ ((UJ†) v) = v := by
    intro v
    have := congrArg (fun F : Vsp a P →L[ℂ] Vsp a P => F v) hUJ
    simpa using this
  congr 1
  · ext v
    simp only [localPrivateBlock, comp_apply, sub_apply, one_apply_eq_self, smul_apply,
      map_sub, map_smul, h1, adjoint_comp]
  · rw [comp_smul]
  · ext v
    simp only [comp_apply, smul_apply, one_apply_eq_self, adjoint_comp]

/-! ### The sector-controlled pointer increment -/

/-- Replace the pointer word of a configuration. -/
def setPtr (x : Cfg (Wire a m r K)) (w : Word r) : Cfg (Wire a m r K)
  | .ptr i => w i
  | .anc i => x (.anc i)
  | .sec => x .sec
  | .slot i => x (.slot i)
  | .lab i => x (.lab i)
  | .hf => x .hf
  | .pf i => x (.pf i)
  | .lf => x .lf
  | .tf i => x (.tf i)
  | .cf i => x (.cf i)
  | .wk i => x (.wk i)

theorem setPtr_ne (x : Cfg (Wire a m r K)) (w : Word r) (v : Wire a m r K)
    (hv : ∀ i, v ≠ .ptr i) : setPtr x w v = x v := by
  cases v <;> first | rfl | exact absurd rfl (hv _)

@[simp] theorem ptrOf_setPtr (x : Cfg (Wire a m r K)) (w : Word r) : ptrOf (setPtr x w) = w := rfl

@[simp] theorem setPtr_sec (x : Cfg (Wire a m r K)) (w : Word r) : setPtr x w .sec = x .sec := rfl

@[simp] theorem labOf_setPtr (x : Cfg (Wire a m r K)) (w : Word r) : labOf (setPtr x w) = labOf x := rfl
@[simp] theorem slotOf_setPtr (x : Cfg (Wire a m r K)) (w : Word r) : slotOf (setPtr x w) = slotOf x := rfl
@[simp] theorem ancOf_setPtr (x : Cfg (Wire a m r K)) (w : Word r) : ancOf (setPtr x w) = ancOf x := rfl
@[simp] theorem slotIdx_setPtr (x : Cfg (Wire a m r K)) (w : Word r) : slotIdx (setPtr x w) = slotIdx x := rfl

theorem clean_setPtr (x : Cfg (Wire a m r K)) (w : Word r) : Clean (setPtr x w) ↔ Clean x := by
  unfold Clean
  constructor
  · intro h v hv
    have := h v hv
    rwa [setPtr_ne x w v (by intro i e; subst e; simp [isFlag] at hv)] at this
  · intro h v hv
    rw [setPtr_ne x w v (by intro i e; subst e; simp [isFlag] at hv)]
    exact h v hv

theorem setPtr_setPtr (x : Cfg (Wire a m r K)) (w w' : Word r) :
    setPtr (setPtr x w) w' = setPtr x w' := by
  funext v; cases v <;> rfl

theorem setPtr_self (x : Cfg (Wire a m r K)) : setPtr x (ptrOf x) = x := by
  funext v; cases v <;> rfl

/-- Apply a word map to the pointer on the private sector. -/
def incFun (f : Word r → Word r) (x : Cfg (Wire a m r K)) : Cfg (Wire a m r K) :=
  if x .sec = true then setPtr x (f (ptrOf x)) else x

theorem incFun_inv (e : Word r ≃ Word r) (x : Cfg (Wire a m r K)) :
    incFun e.symm (incFun (K := K) (m := m) (a := a) e x) = x := by
  unfold incFun
  by_cases hs : x .sec = true
  · rw [if_pos hs, setPtr_sec, if_pos hs, ptrOf_setPtr, Equiv.symm_apply_apply, setPtr_setPtr,
      setPtr_self]
  · rw [if_neg hs, if_neg hs]

/-- The sector-controlled cyclic increment of the pointer register. -/
def incEquiv : Cfg (Wire a m r K) ≃ Cfg (Wire a m r K) where
  toFun := incFun (successorEquiv r)
  invFun := incFun (successorEquiv r).symm
  left_inv x := incFun_inv (successorEquiv r) x
  right_inv x := by
    have := incFun_inv (K := K) (m := m) (a := a) (successorEquiv r).symm x
    rwa [Equiv.symm_symm] at this

/-- The ideal pointer increment on the private sector. -/
def INC : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P := permOp incEquiv

theorem cast_finRotate_symm {n n' : ℕ} (h : n = n') (i : Fin n) :
    Fin.cast h ((finRotate n).symm i) = (finRotate n').symm (Fin.cast h i) := by
  subst h; rfl

theorem ptrIdx_dec (x : Cfg (Wire a m r K)) :
    ptrIdx (setPtr x ((successorEquiv r).symm (ptrOf x))) =
      (finRotate (cap r + 1)).symm (ptrIdx x) := by
  simp only [ptrIdx, ptrOf_setPtr]
  rw [← cast_finRotate_symm]
  congr 1
  simp only [successorEquiv, Equiv.symm_trans_apply, Equiv.apply_symm_apply, Equiv.symm_symm]

omit [CompleteSpace P] in
theorem INC_emb (lw : Word r) (z : Model a m r P) :
    INC (K := K) (emb lw z) = emb lw (GateBinaryReuse.increment (cap r) z) := by
  apply PiLp.ext
  intro x
  rw [INC, permOp_apply, emb_apply, emb_apply]
  change embVal lw z (incFun (successorEquiv r).symm x) = _
  unfold incFun
  by_cases hs : x .sec = true
  · rw [if_pos hs]
    by_cases hc : labOf x = lw ∧ Clean x
    · have hc' : labOf (setPtr x ((successorEquiv r).symm (ptrOf x))) = lw ∧
          Clean (setPtr x ((successorEquiv r).symm (ptrOf x))) := by
        rw [labOf_setPtr, clean_setPtr]; exact hc
      rw [embVal_private lw z _ hc' (by rw [setPtr_sec]; exact hs),
        embVal_private lw _ x hc hs, ptrIdx_dec]
      rfl
    · rw [embVal_unclean lw z _ (by rw [labOf_setPtr, clean_setPtr]; exact hc),
        embVal_unclean lw _ x hc]
  · rw [if_neg hs]
    by_cases hc : labOf x = lw ∧ Clean x
    · have hs' : x .sec = false := by simpa using hs
      rw [embVal_public lw z x hc hs', embVal_public lw _ x hc hs']
      rfl
    · rw [embVal_unclean lw z x hc, embVal_unclean lw _ x hc]

/-! ### One reuse step and the SELECT circuit -/

/-- One reuse step at pointer word `j`. -/
def STEP (j : Fin (cap r + 1)) (c σ : ℝ) (UJ D : Vsp a P →L[ℂ] Vsp a P) :
    Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P :=
  INC ∘L BNET j c σ UJ ∘L secOracle D

theorem STEP_emb (j : Fin (cap r + 1)) (c κ σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1)
    (hκ : κ = 1 - c) (UJ D : Vsp a P →L[ℂ] Vsp a P) (hUJ : UJ ∘L UJ† = 1)
    (lw : Word r) (z : Model a m r P) :
    STEP (K := K) j c σ UJ D (emb lw z) =
      emb lw (GateBinaryReuse.step (blkA c (2 ^ m)) (netB c σ UJ) (netC c σ UJ)
        (netG c κ σ UJ) (diagV D) j z) := by
  rw [STEP, comp_apply, comp_apply, secOracle_emb, BNET_emb j c κ σ hunit hκ UJ hUJ, INC_emb]
  rfl

/-- The SELECT circuit: `n` reuse steps at pointer words `0, …, n-1`. -/
def selectN (c σ : ℝ) (UJ D : Vsp a P →L[ℂ] Vsp a P) :
    ℕ → Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P
  | 0 => 1
  | n + 1 => if h : n < cap r + 1 then STEP ⟨n, h⟩ c σ UJ D ∘L selectN c σ UJ D n
      else selectN c σ UJ D n

theorem selectN_emb (c κ σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1) (hκ : κ = 1 - c)
    (UJ D : Vsp a P →L[ℂ] Vsp a P) (hUJ : UJ ∘L UJ† = 1) (n : ℕ)
    (lw : Word r) (z : Model a m r P) :
    selectN (K := K) c σ UJ D n (emb lw z) =
      emb lw (GateBinaryReuse.run (blkA c (2 ^ m)) (netB c σ UJ) (netC c σ UJ)
        (netG c κ σ UJ) (diagV D) (cap r) n z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases h : n < cap r + 1
      · rw [selectN, dif_pos h, comp_apply, ih, STEP_emb _ c κ σ hunit hκ UJ D hUJ,
          GateBinaryReuse.run, dif_pos h]
        rfl
      · rw [selectN, dif_neg h, ih, GateBinaryReuse.run, dif_neg h]

/-! ### Inner products with public embedded states -/

/-- The public-mode configuration of label word `lw` and pointer word `k`. -/
def pubCfg (lw : Word r) (k : Fin (cap r + 1)) : Cfg (Wire a m r K)
  | .lab i => lw i
  | .ptr i => (wordEquivFin r).symm (Fin.cast (cap_succ r) k) i
  | _ => false

theorem ptrIdx_pubCfg (lw : Word r) (k : Fin (cap r + 1)) :
    ptrIdx (pubCfg (a := a) (m := m) (K := K) lw k) = k := by
  apply Fin.ext
  simp only [ptrIdx]
  have : ptrOf (pubCfg (a := a) (m := m) (K := K) lw k) =
      (wordEquivFin r).symm (Fin.cast (cap_succ r) k) := rfl
  rw [this, Equiv.apply_symm_apply]
  rfl

theorem pubCfg_injective (lw : Word r) :
    Function.Injective (pubCfg (a := a) (m := m) (K := K) lw) := by
  intro k k' h
  have := congrArg ptrIdx h
  rwa [ptrIdx_pubCfg, ptrIdx_pubCfg] at this

theorem eq_pubCfg (lw : Word r) (x : Cfg (Wire a m r K)) (hc : labOf x = lw ∧ Clean x)
    (hs : x .sec = false) (hz : slotOf x = zw m ∧ ancOf x = zw a) :
    x = pubCfg lw (ptrIdx x) := by
  funext v
  cases v with
  | anc i => exact congrFun hz.2 i
  | sec => exact hs
  | slot i => exact congrFun hz.1 i
  | ptr i =>
      change x (.ptr i) = (wordEquivFin r).symm (Fin.cast (cap_succ r) (ptrIdx x)) i
      simp only [ptrIdx, Fin.cast_cast, Fin.cast_eq_self, Equiv.symm_apply_apply]
      rfl
  | lab i => exact congrFun hc.1 i
  | hf => exact hc.2 _ rfl
  | pf i => exact hc.2 _ rfl
  | lf => exact hc.2 _ rfl
  | tf i => exact hc.2 _ rfl
  | cf i => exact hc.2 _ rfl
  | wk i => exact hc.2 _ rfl

omit [CompleteSpace P] in
theorem embVal_pubCfg (lw : Word r) (z : Model a m r P) (k : Fin (cap r + 1)) :
    embVal lw z (pubCfg (a := a) (m := m) (K := K) lw k) = z.1 k := by
  have hc : labOf (pubCfg (a := a) (m := m) (K := K) lw k) = lw ∧
      Clean (pubCfg (a := a) (m := m) (K := K) lw k) := by
    refine ⟨rfl, ?_⟩
    intro v hv
    cases v <;> simp_all [isFlag, pubCfg]
  rw [embVal_public lw z _ hc rfl, if_pos ⟨rfl, rfl⟩, ptrIdx_pubCfg]

omit [CompleteSpace P] in
/-- A public embedded state only sees public amplitudes. -/
theorem inner_emb_public (lw : Word r) (u : Fin (cap r + 1) → P) (w : Model a m r P) :
    inner ℂ (emb (K := K) lw ((u, 0) : Model a m r P)) (emb lw w) =
      ∑ k, inner ℂ (u k) (w.1 k) := by
  rw [PiLp.inner_apply]
  symm
  apply Fintype.sum_of_injective (pubCfg (a := a) (m := m) (K := K) lw) (pubCfg_injective lw)
  · intro x hx
    simp only [emb_apply]
    by_cases hc : labOf x = lw ∧ Clean x
    · cases hs : x .sec
      · rw [embVal_public lw _ x hc hs]
        by_cases hz : slotOf x = zw m ∧ ancOf x = zw a
        · exact absurd ⟨ptrIdx x, (eq_pubCfg lw x hc hs hz).symm⟩ hx
        · rw [if_neg hz, inner_zero_left]
      · rw [embVal_private lw _ x hc hs]
        simp
    · rw [embVal_unclean lw _ x hc, inner_zero_left]
  · intro k
    simp only [emb_apply, embVal_pubCfg]

/-! ### The SELECT block of one branch -/

/-- The uniform pointer state of length `n` carrying `ψ` on the public mode. -/
def uIn (n : ℕ) (ψ : P) : Model a m r P :=
  (fun k => extendSequence (uniformEmbedding n ψ) k.val, 0)

/-- Sum over the pointer words of a function vanishing from `n` on. -/
theorem sum_ptr_eq (n : ℕ) (hn : n ≤ cap r + 1) (f : ℕ → ℂ) (hf : ∀ k, n ≤ k → f k = 0) :
    (∑ k : Fin (cap r + 1), f k.val) = ∑ k : Fin n, f k.val := by
  rw [Fin.sum_univ_eq_sum_range f, Fin.sum_univ_eq_sum_range f]
  symm
  apply Finset.sum_subset (Finset.range_mono hn)
  intro k _ hk
  exact hf k (by simpa using hk)

/-- The SELECT circuit between uniform pointer states of length `n` is the
coherent-reuse successful block of length `n`, for every number `N ≥ n` of
reuse steps. -/
theorem select_block (c κ σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1) (hκ : κ = 1 - c)
    (UJ D : Vsp a P →L[ℂ] Vsp a P) (hUJ : UJ ∘L UJ† = 1) (lw : Word r)
    (n N : ℕ) (hnN : n ≤ N) (hN : N ≤ cap r) (ψ ψ' : P) :
    inner ℂ (emb (K := K) (m := m) lw (uIn n ψ'))
        (selectN (m := m) (K := K) c σ UJ D N (emb lw (uIn n ψ))) =
      inner ℂ ψ' (successfulBlock (V := HV a m P) (blkA c (2 ^ m))
        (netB (m := m) c σ UJ ∘L diagV D) (netC (m := m) c σ UJ)
        (netG (m := m) c κ σ UJ ∘L diagV D) n ψ) := by
  set y : ℕ → P := fun k => extendSequence (uniformEmbedding n ψ) k with hy
  set y' : ℕ → P := fun k => extendSequence (uniformEmbedding n ψ') k with hy'
  rw [selectN_emb c κ σ hunit hκ UJ D hUJ N lw]
  have hrun := GateBinaryReuse.run_invariant (blkA c (2 ^ m)) (netB (m := m) c σ UJ) (netC (m := m) c σ UJ)
    (netG (m := m) c κ σ UJ) (diagV (m := m) D) (cap r) y N hN
  rw [show (uIn n ψ : Model a m r P) = ((fun k => y k.val), 0) from rfl, hrun,
    show (uIn n ψ' : Model a m r P) = ((fun k => y' k.val), 0) from rfl, inner_emb_public]
  rw [successfulBlock, comp_apply, comp_apply, adjoint_inner_right, PiLp.inner_apply]
  have hz : ∀ k, n ≤ k → y' k = 0 := by
    intro k hk
    simp only [hy', extendSequence, dif_neg (by omega : ¬ k < n)]
  let f : ℕ → ℂ := fun k => inner ℂ (y' k)
    (if k < N then blkA c (2 ^ m) (y k) + netB (m := m) c σ UJ (diagV (m := m) D
      (forcedPublicState (netG (m := m) c κ σ UJ ∘L diagV (m := m) D) (netC (m := m) c σ UJ) y k)) else y k)
  have hL : ∀ k : Fin (cap r + 1), inner ℂ (y' k.val)
      (GateBinaryReuse.publicBefore (blkA c (2 ^ m)) (netB (m := m) c σ UJ) (netC (m := m) c σ UJ)
        (netG (m := m) c κ σ UJ) (diagV (m := m) D) (cap r) N y k) = f k.val := fun k => rfl
  simp only [hL]
  rw [sum_ptr_eq n (by omega) f (fun k hk => by simp only [f, hz k hk, inner_zero_left])]
  apply Finset.sum_congr rfl
  intro k _
  have hk : (k : ℕ) < N := lt_of_lt_of_le k.isLt hnN
  have hpr : publicReuse (blkA c (2 ^ m)) (netB (m := m) c σ UJ ∘L diagV (m := m) D) (netC (m := m) c σ UJ)
      (netG (m := m) c κ σ UJ ∘L diagV (m := m) D) n (uniformEmbedding n ψ) k =
        blkA c (2 ^ m) (y k) + (netB (m := m) c σ UJ ∘L diagV (m := m) D)
          (forcedPublicState (netG (m := m) c κ σ UJ ∘L diagV (m := m) D) (netC (m := m) c σ UJ) y k) := by
    have h := chronologicalOperator_apply (blkA c (2 ^ m)) (netB (m := m) c σ UJ ∘L diagV (m := m) D)
      (netG (m := m) c κ σ UJ ∘L diagV (m := m) D) (netC (m := m) c σ UJ) y k
    rw [show (WithLp.toLp 2 (fun k : Fin n => y k) : BlockOperator.H n P) =
      uniformEmbedding n ψ from restrict_extend _] at h
    rw [publicReuse, h]
    rfl
  simp only [f, if_pos hk, hpr, comp_apply]
  congr 1
  simp only [hy', extendSequence_apply]

end

end SparseHamiltonian.GateCircuit.Sim
