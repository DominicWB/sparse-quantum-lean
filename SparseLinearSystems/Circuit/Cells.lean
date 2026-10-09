import SparseLinearSystems.Circuit.Opaque
import SparseLinearSystems.Circuit.Source

/-!
# The clean cell encoding of the walk workspace

The private walk space is cut into public *cells*: the four sparse cells of
branch zero (one `OrientedSpace n` each), its appended scalar, and in each of
the three public branches the eight `ℂ^n` components `(side, reg, dil)` and the
appended scalar.  Every cell is stored in one native workspace register:

* sparse cells by the fixed clean embedding `NativeCayleyProgram.clean D`;
* `ℂ^n` cells in the source register (`Source.nEmb`);
* scalar cells as multiples of one fixed basis vector.

`Enc` is the resulting isometry from the counter register `ℂ^{T+1} ⊗ Priv`
into the native logical cell space.  The sparse factor `A_sp` of the walk acts
on the encoding exactly as the native Cayley program on the selected sparse cells
(`sparse_intertwines`), and the source factor `V` exactly as `U_b` on the one
selected source cell (`source_intertwines`).
-/

namespace SparseLinearSystems.Cells

noncomputable section
open SparseHamiltonian
open ContinuousLinearMap HilbertBlocks HilbertRegularization HilbertAugmentation
  FourBranchCompression Augmented SparseBranch LogicalWalk Source CounterFilter
open scoped InnerProduct
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- Public cells: sparse cells, the branch-zero scalar, `ℂ^n` cells
`(branch, side, reg, dil)` and the scalars of the three public branches. -/
abbrev Cell := (Bool × Bool) ⊕ (Unit ⊕ ((Fin 3 × (Bool × (Bool × Bool))) ⊕ Fin 3))

/-- The selected source cell: branch two (`T₂`), upper, register zero, dilation zero. -/
def srcCell : Cell := .inr (.inr (.inl (1, (false, (false, false)))))

/-! ### Coordinate projections -/

/-- Branch zero. -/
def br0 : Priv n →L[ℂ] P0 n := WithLp.fstL 2 ℂ _ _

/-- The three public branches. -/
def brk (k : Fin 3) : Priv n →L[ℂ] Pub V0 :=
  ![WithLp.fstL 2 ℂ _ _ ∘L WithLp.sndL 2 ℂ _ _,
    WithLp.fstL 2 ℂ _ _ ∘L WithLp.sndL 2 ℂ _ _ ∘L WithLp.sndL 2 ℂ _ _,
    WithLp.sndL 2 ℂ _ _ ∘L WithLp.sndL 2 ℂ _ _ ∘L WithLp.sndL 2 ℂ _ _] k

/-- A sparse cell of branch zero. -/
def quadL (sr : Bool × Bool) : P0 n →L[ℂ] SparseEdgeMoments.OrientedSpace n :=
  PiLp.proj (𝕜 := ℂ) 2 (fun _ : Bool × Bool => SparseEdgeMoments.OrientedSpace n) sr ∘L
    WithLp.fstL 2 ℂ _ _

/-- The scalar of branch zero. -/
def e0L : P0 n →L[ℂ] ℂ := WithLp.sndL 2 ℂ _ _

/-- A `ℂ^n` component `(side, reg, dil)` of a public vector. -/
def pubV (side reg dil : Bool) : Pub V0 →L[ℂ] V0 :=
  (if dil then WithLp.sndL 2 ℂ V0 V0 else WithLp.fstL 2 ℂ V0 V0) ∘L
    (if reg then WithLp.sndL 2 ℂ (Double V0) (Double V0) else WithLp.fstL 2 ℂ (Double V0) (Double V0)) ∘L
      (if side then WithLp.fstL 2 ℂ (Sys V0) ℂ ∘L WithLp.sndL 2 ℂ (Sys V0) (RightSpace (Sys V0))
        else WithLp.fstL 2 ℂ (Sys V0) (RightSpace (Sys V0)))

/-- The scalar of a public vector. -/
def pubE : Pub V0 →L[ℂ] ℂ := WithLp.sndL 2 ℂ _ _ ∘L WithLp.sndL 2 ℂ _ _

/-! ### The cell embeddings -/

/-- Scalars as multiples of one fixed basis vector. -/
def eEmb (a : Bas n Z) : ℂ →ₗᵢ[ℂ] EuclideanSpace ℂ (Bas n Z) :=
  LinearIsometry.toSpanSingleton ℂ _ (v := EuclideanSpace.single a 1) (by simp)

/-- The embedding of one cell into a native workspace register. -/
def cellMap (D : NativeSparseBlockEncoding.Data X n Z s) :
    Cell → (Priv n →L[ℂ] EuclideanSpace ℂ (Bas n Z))
  | .inl sr => (NativeCayleyProgram.clean D).toContinuousLinearMap ∘L quadL sr ∘L br0
  | .inr (.inl _) => (eEmb (NativeCayleyProgram.cleanBasis D)).toContinuousLinearMap ∘L e0L ∘L br0
  | .inr (.inr (.inl (k, (side, (reg, dil))))) =>
      (nEmb (NativeCayleyProgram.cleanBasis D)).toContinuousLinearMap ∘L pubV side reg dil ∘L brk k
  | .inr (.inr (.inr k)) =>
      (eEmb (NativeCayleyProgram.cleanBasis D)).toContinuousLinearMap ∘L pubE ∘L brk k

/-! ### Coordinate identities -/

omit [DecidableEq n] in
@[simp] theorem quadL_apply (sr : Bool × Bool) (p : P0 n) : quadL sr p = p.fst sr := rfl
omit [DecidableEq n] in
@[simp] theorem e0L_apply (p : P0 n) : e0L p = p.snd := rfl
omit [DecidableEq n] in
@[simp] theorem br0_apply (w : Priv n) : br0 w = w.fst := rfl
omit [DecidableEq n] in
@[simp] theorem brk_zero (w : Priv n) : brk 0 w = w.snd.fst := rfl
omit [DecidableEq n] in
@[simp] theorem brk_one (w : Priv n) : brk 1 w = w.snd.snd.fst := rfl
omit [DecidableEq n] in
@[simp] theorem brk_two (w : Priv n) : brk 2 w = w.snd.snd.snd := rfl
omit [DecidableEq n] [Fintype n] in
@[simp] theorem pubE_apply (y : Pub V0) : pubE y = y.snd.snd := rfl

omit [DecidableEq n] [Fintype n] in
theorem pubV_apply (side reg dil : Bool) (y : Pub V0) :
    pubV side reg dil y =
      (if dil then WithLp.snd else WithLp.fst)
        ((if reg then WithLp.snd else WithLp.fst) (if side then y.snd.fst else y.fst)) := by
  cases side <;> cases reg <;> cases dil <;> rfl

omit [DecidableEq n] in
theorem norm_sq_P0 (p : P0 n) : ‖p‖ ^ 2 = ∑ sr, ‖quadL sr p‖ ^ 2 + ‖e0L p‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  rfl

omit [DecidableEq n] in
theorem norm_sq_cells_pub (y : Pub V0) :
    ‖y‖ ^ 2 = ∑ c : Bool × (Bool × Bool), ‖pubV c.1 c.2.1 c.2.2 y‖ ^ 2 + ‖pubE y‖ ^ 2 := by
  rw [norm_sq_pub, WithLp.prod_norm_sq_eq_of_L2 y.fst, WithLp.prod_norm_sq_eq_of_L2 y.snd.fst,
    WithLp.prod_norm_sq_eq_of_L2 y.fst.fst, WithLp.prod_norm_sq_eq_of_L2 y.fst.snd,
    WithLp.prod_norm_sq_eq_of_L2 y.snd.fst.fst, WithLp.prod_norm_sq_eq_of_L2 y.snd.fst.snd]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, pubV_apply, pubE_apply, if_true,
    Bool.false_eq_true, if_false]
  ring

omit [DecidableEq n] in
theorem norm_sq_priv (w : Priv n) : ‖w‖ ^ 2 = ‖br0 w‖ ^ 2 + ∑ k, ‖brk k w‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2 w, WithLp.prod_norm_sq_eq_of_L2 w.snd,
    WithLp.prod_norm_sq_eq_of_L2 w.snd.snd, Fin.sum_univ_three]
  simp only [br0_apply, brk_zero, brk_one, brk_two]
  ring

theorem norm_cellMap_sq_sum (D : NativeSparseBlockEncoding.Data X n Z s) (w : Priv n) :
    ∑ cell : Cell, ‖cellMap D cell w‖ ^ 2 = ‖w‖ ^ 2 := by
  rw [norm_sq_priv, norm_sq_P0]
  simp only [norm_sq_cells_pub, Finset.sum_add_distrib, Fintype.sum_sum_type, cellMap, comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map, Fintype.univ_unit,
    Finset.sum_singleton, Fintype.sum_prod_type]
  ring

/-! ### The encoding -/

/-- The cell embeddings on the opaque copy of the walk space. -/
def cellMapO (D : NativeSparseBlockEncoding.Data X n Z s) (cell : Cell) :
    PrivO n →L[ℂ] EuclideanSpace ℂ (Bas n Z) :=
  cellMap D cell ∘L (toO (n := n)).symm.toLinearIsometry.toContinuousLinearMap

@[simp] theorem cellMapO_apply (D : NativeSparseBlockEncoding.Data X n Z s) (cell : Cell)
    (w : PrivO n) : cellMapO D cell w = cellMap D cell (toO.symm w) := rfl

theorem norm_cellMapO_sq_sum (D : NativeSparseBlockEncoding.Data X n Z s) (w : PrivO n) :
    ∑ cell : Cell, ‖cellMapO D cell w‖ ^ 2 = ‖w‖ ^ 2 := by
  simp only [cellMapO_apply]
  rw [norm_cellMap_sq_sum, LinearIsometryEquiv.norm_map]

/-- The cell encoding of the counter register `ℂ^{T+1} ⊗ Priv`, as a map. -/
def encL (D : NativeSparseBlockEncoding.Data X n Z s) (T : ℕ) :
    Ctr T (PrivO n) →L[ℂ] NativeMaskedOracle.Logical (Fin (T + 1) × Cell) (Bas n Z) :=
  (PiLp.continuousLinearEquiv 2 ℂ
    (fun _ : Fin (T + 1) × Cell => EuclideanSpace ℂ (Bas n Z))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i : Fin (T + 1) × Cell =>
      cellMapO D i.2 ∘L PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin (T + 1) => PrivO n) i.1)

@[simp] theorem encL_apply (D : NativeSparseBlockEncoding.Data X n Z s) (T : ℕ)
    (v : Ctr T (PrivO n)) (i : Fin (T + 1) × Cell) : encL D T v i = cellMapO D i.2 (v i.1) := rfl

theorem encL_norm (D : NativeSparseBlockEncoding.Data X n Z s) (T : ℕ) (v : Ctr T (PrivO n)) :
    ‖encL D T v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2 _ v, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← norm_cellMapO_sq_sum D (v c)]
  rfl

/-- The cell encoding as an isometry. -/
def Enc (D : NativeSparseBlockEncoding.Data X n Z s) (T : ℕ) :
    Ctr T (PrivO n) →ₗᵢ[ℂ] NativeMaskedOracle.Logical (Fin (T + 1) × Cell) (Bas n Z) where
  toLinearMap := (encL D T).toLinearMap
  norm_map' := encL_norm D T

@[simp] theorem Enc_apply (D : NativeSparseBlockEncoding.Data X n Z s) (T : ℕ)
    (v : Ctr T (PrivO n)) (i : Fin (T + 1) × Cell) : Enc D T v i = cellMapO D i.2 (v i.1) := rfl

/-! ### The sparse and source factors on the encoding -/

/-- The sparse cells of the active counter values. -/
def activeSparse {T : ℕ} (m : Fin (T + 1) → Bool) : Fin (T + 1) × Cell → Bool :=
  fun i => m i.1 && i.2.isLeft

/-- The source cell of the active counter values. -/
def activeSrc {T : ℕ} (m : Fin (T + 1) → Bool) : Fin (T + 1) × Cell → Bool :=
  fun i => m i.1 && decide (i.2 = srcCell)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
@[simp] theorem Asp_fst (D : NativeSparseBlockEncoding.Data X n Z s) (σ : ℝ) (x : X)
    (w : Priv n) : (Asp D σ x w).fst = sparseCells D x (w0 σ) w.fst := by
  simp [Asp, diagonal_apply]

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
@[simp] theorem Asp_snd (D : NativeSparseBlockEncoding.Data X n Z s) (σ : ℝ) (x : X)
    (w : Priv n) : (Asp D σ x w).snd = w.snd := by
  apply prodExt
  · simp [Asp, diagonal_apply]
  · apply prodExt <;> simp [Asp, diagonal_apply]

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
@[simp] theorem sparseCells_fst (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (γ : ℝ)
    (p : P0 n) (sr : Bool × Bool) :
    (sparseCells D x γ p).fst sr = FixedNativeCayleySimulation.action D x γ (p.fst sr) := by
  simp [sparseCells, blockMap_apply]

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
@[simp] theorem sparseCells_snd (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (γ : ℝ)
    (p : P0 n) : (sparseCells D x γ p).snd = p.snd := by
  simp [sparseCells, blockMap_apply]

theorem cellMap_Asp_sparse (D : NativeSparseBlockEncoding.Data X n Z s) (σ : ℝ) (x : X)
    (sr : Bool × Bool) (w : Priv n) :
    cellMap D (.inl sr) (Asp D σ x w) =
      (NativeCayleyProgram.program D (w0 σ)).eval x (cellMap D (.inl sr) w) := by
  have h := congrArg (fun A => A (w.fst.fst sr))
    (NativeCayleyProgram.program_intertwines D (w0 σ) x)
  simp only [comp_apply, LinearIsometry.coe_toContinuousLinearMap] at h
  simp only [cellMap, comp_apply, LinearIsometry.coe_toContinuousLinearMap, quadL_apply,
    br0_apply, Asp_fst, sparseCells_fst, h]

theorem cellMap_Asp_other (D : NativeSparseBlockEncoding.Data X n Z s) (σ : ℝ) (x : X)
    (cell : Unit ⊕ ((Fin 3 × (Bool × (Bool × Bool))) ⊕ Fin 3)) (w : Priv n) :
    cellMap D (.inr cell) (Asp D σ x w) = cellMap D (.inr cell) w := by
  rcases cell with _ | ⟨k, side, reg, dil⟩ | k
  · simp only [cellMap, comp_apply, e0L_apply, br0_apply, Asp_fst, sparseCells_snd]
  · fin_cases k <;> simp only [cellMap, comp_apply, brk_zero, brk_one, brk_two, Asp_snd,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · fin_cases k <;> simp only [cellMap, comp_apply, brk_zero, brk_one, brk_two, Asp_snd,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]

theorem cellMapO_Asp_sparse (D : NativeSparseBlockEncoding.Data X n Z s) (σ : ℝ) (x : X)
    (sr : Bool × Bool) (w : PrivO n) :
    cellMapO D (.inl sr) (opO (Asp D σ x) w) =
      (NativeCayleyProgram.program D (w0 σ)).eval x (cellMapO D (.inl sr) w) := by
  rw [cellMapO_apply, cellMapO_apply, opO_apply, LinearIsometryEquiv.symm_apply_apply,
    cellMap_Asp_sparse]

theorem cellMapO_Asp_other (D : NativeSparseBlockEncoding.Data X n Z s) (σ : ℝ) (x : X)
    (cell : Unit ⊕ ((Fin 3 × (Bool × (Bool × Bool))) ⊕ Fin 3)) (w : PrivO n) :
    cellMapO D (.inr cell) (opO (Asp D σ x) w) = cellMapO D (.inr cell) w := by
  rw [cellMapO_apply, cellMapO_apply, opO_apply, LinearIsometryEquiv.symm_apply_apply,
    cellMap_Asp_other]

/-- **The sparse factor on the encoding.** -/
theorem sparse_intertwines (D : NativeSparseBlockEncoding.Data X n Z s) (T : ℕ) (σ : ℝ) (x : X)
    (m : Fin (T + 1) → Bool) :
    MaskedProgram.masked (activeSparse m) ((NativeCayleyProgram.program D (w0 σ)).eval x) ∘L
        (Enc D T).toContinuousLinearMap =
      (Enc D T).toContinuousLinearMap ∘L MaskedProgram.masked m (opO (Asp D σ x)) := by
  have key := cellMapO_Asp_sparse D σ x
  have key' := cellMapO_Asp_other D σ x
  generalize (NativeCayleyProgram.program D (w0 σ)).eval x = U at key ⊢
  generalize opO (Asp D σ x) = A at key key' ⊢
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  rintro ⟨c, cell⟩
  simp only [comp_apply, LinearIsometry.coe_toContinuousLinearMap, MaskedProgram.masked_apply,
    Enc_apply, activeSparse]
  cases hm : m c
  · simp only [Bool.false_and, Bool.false_eq_true, if_false]
  · rcases cell with sr | cell
    · simp only [Bool.true_and, Sum.isLeft_inl, if_true, key]
    · simp only [Bool.true_and, Sum.isLeft_inr, Bool.false_eq_true, if_false,
        if_true, key']

omit [DecidableEq n] in
@[simp] theorem slotOp_fst_fst_fst (U : V0 →L[ℂ] V0) (y : Pub V0) :
    (slotOp U y).fst.fst.fst = U y.fst.fst.fst := by simp [slotOp, blockMap_apply]
omit [DecidableEq n] in
@[simp] theorem slotOp_fst_fst_snd (U : V0 →L[ℂ] V0) (y : Pub V0) :
    (slotOp U y).fst.fst.snd = y.fst.fst.snd := by simp [slotOp, blockMap_apply]
omit [DecidableEq n] in
@[simp] theorem slotOp_fst_snd (U : V0 →L[ℂ] V0) (y : Pub V0) :
    (slotOp U y).fst.snd = y.fst.snd := by simp [slotOp, blockMap_apply]
omit [DecidableEq n] in
@[simp] theorem slotOp_snd (U : V0 →L[ℂ] V0) (y : Pub V0) :
    (slotOp U y).snd = y.snd := by simp [slotOp, blockMap_apply]

omit [DecidableEq n] in
@[simp] theorem Vd_fst (U : V0 →L[ℂ] V0) (w : Priv n) : (Vd U w).fst = w.fst := by
  simp [Vd, diagonal_apply]
omit [DecidableEq n] in
@[simp] theorem Vd_snd_fst (U : V0 →L[ℂ] V0) (w : Priv n) : (Vd U w).snd.fst = w.snd.fst := by
  simp [Vd, diagonal_apply]
omit [DecidableEq n] in
@[simp] theorem Vd_snd_snd_fst (U : V0 →L[ℂ] V0) (w : Priv n) :
    (Vd U w).snd.snd.fst = slotOp U w.snd.snd.fst := by
  simp [Vd, diagonal_apply]
omit [DecidableEq n] in
@[simp] theorem Vd_snd_snd_snd (U : V0 →L[ℂ] V0) (w : Priv n) :
    (Vd U w).snd.snd.snd = w.snd.snd.snd := by
  simp [Vd, diagonal_apply]

theorem cellMap_Vd (D : NativeSparseBlockEncoding.Data X n Z s) (U : V0 →L[ℂ] V0) (cell : Cell)
    (w : Priv n) :
    cellMap D cell (Vd U w) =
      if cell = srcCell then srcU U (cellMap D cell w) else cellMap D cell w := by
  rcases cell with sr | _ | ⟨k, side, reg, dil⟩ | k
  · simp [cellMap, srcCell]
  · simp [cellMap, srcCell]
  · fin_cases k
    · simp [cellMap, srcCell]
    · cases side <;> cases reg <;> cases dil <;> simp [cellMap, srcCell, pubV_apply, srcU_nEmb]
    · simp [cellMap, srcCell]
  · fin_cases k <;> simp [cellMap, srcCell]

theorem cellMapO_Vd (D : NativeSparseBlockEncoding.Data X n Z s) (U : V0 →L[ℂ] V0) (cell : Cell)
    (w : PrivO n) :
    cellMapO D cell (opO (Vd U) w) =
      if cell = srcCell then srcU U (cellMapO D cell w) else cellMapO D cell w := by
  rw [cellMapO_apply, cellMapO_apply, opO_apply, LinearIsometryEquiv.symm_apply_apply, cellMap_Vd]

/-- **The source factor on the encoding.** -/
theorem source_intertwines (D : NativeSparseBlockEncoding.Data X n Z s) (T : ℕ) (U : V0 →L[ℂ] V0)
    (m : Fin (T + 1) → Bool) :
    MaskedProgram.masked (activeSrc m) (srcU U) ∘L (Enc D T).toContinuousLinearMap =
      (Enc D T).toContinuousLinearMap ∘L MaskedProgram.masked m (opO (Vd U)) := by
  have key := cellMapO_Vd D U
  generalize opO (Vd U) = A at key ⊢
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  rintro ⟨c, cell⟩
  simp only [comp_apply, LinearIsometry.coe_toContinuousLinearMap, MaskedProgram.masked_apply,
    Enc_apply, activeSrc]
  cases hm : m c
  · simp only [Bool.false_and, Bool.false_eq_true, if_false]
  · simp only [Bool.true_and, if_true, decide_eq_true_eq]
    rw [key]

end

end SparseLinearSystems.Cells
