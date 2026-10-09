import SparseLinearSystems.Sparse.SplitBoundary
import SparseLinearSystems.Spectral.CayleyAlgebra

/-!
# The sparse branch of the augmented walk (Lemma `qls:lem:entry` for `H₀`)

`H₀` is the off-diagonal lift of `Z ⊗ B`, `B = [[0, A], [A†, 0]]`.  On the
private space `P₀ = (side, reg) ⊗ OrientedSpace n ⊕ ℂ` put

* `K₀ = (1 ⊗ G) ⊕ 0`, where `G` is the locator-conjugated edge generator of `A`
  (the generator of `NativeCayleyProgram.program`);
* `J₀ x = (J_split(x_{s,r,0}, (-1)^r x_{s̄,r,1}))_{s,r} ⊕ x_e`.

The signed exchange of sides realises `X ⊗ Z` exactly, so
`J₀† K₀ J₀ = H₀ / √s`, `‖K₀ J₀ x‖ ≤ ‖x‖` and `‖K₀‖ ≤ √s`
(`branchData`).  The Cayley transform of a real multiple of `K₀` acts as the
native Cayley action on each of the four `(side, reg)` cells and as `-1` on
the appended coordinate (`cayley_K0`).
-/

namespace SparseLinearSystems.SparseBranch

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.SparseEdgeMoments
  HilbertBlocks HilbertRegularization HilbertAugmentation Augmented
open scoped InnerProduct ComplexConjugate

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- Four oriented-edge cells indexed by `(side, reg)`. -/
abbrev Quad (n : Type*) [Fintype n] := PiLp 2 (fun _ : Bool × Bool => OrientedSpace n)

/-- The private space of the sparse branch. -/
abbrev P0 (n : Type*) [Fintype n] := WithLp 2 (Quad n × ℂ)

/-- The `(side, reg)` sector of a public vector. -/
def sector (x : Pub V0) (side reg : Bool) : Double V0 :=
  (if reg then (if side then x.snd.fst else x.fst).snd else (if side then x.snd.fst else x.fst).fst)

/-- The pair fed to the split boundary in cell `(side, reg)`. -/
def pair (x : Pub V0) (side reg : Bool) : Double V0 :=
  WithLp.toLp 2 ((sector x side reg).fst,
    ((if reg then -1 else 1 : ℂ)) • (sector x (!side) reg).snd)

omit [Fintype n] [DecidableEq n] in
theorem pair_add (x y : Pub V0) (side reg : Bool) :
    pair (x + y) side reg = pair x side reg + pair y side reg := by
  cases side <;> cases reg <;>
    · simp only [pair, sector]
      apply WithLp.ofLp_injective 2
      simp [smul_add]

omit [Fintype n] [DecidableEq n] in
theorem pair_smul (c : ℂ) (x : Pub V0) (side reg : Bool) :
    pair (c • x) side reg = c • pair x side reg := by
  cases side <;> cases reg <;>
    · simp only [pair, sector]
      apply WithLp.ofLp_injective 2
      simp

omit [DecidableEq n] in
theorem sum_norm_sq_pair (x : Pub V0) :
    ∑ sr : Bool × Bool, ‖pair x sr.1 sr.2‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd.fst‖ ^ 2 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, pair, sector, WithLp.prod_norm_sq_eq_of_L2,
    ]
  simp
  ring

variable (D : NativeSparseBlockEncoding.Data X n Z s)

/-- The linear map underlying `J₀`. -/
def J0lin : Pub V0 →ₗ[ℂ] P0 n where
  toFun x := WithLp.toLp 2 (WithLp.toLp 2 (fun sr : Bool × Bool =>
    SplitBoundary.fixedSplit D.slot (pair x sr.1 sr.2)), x.snd.snd)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply PiLp.ext; intro sr; simp [pair_add]
    · simp
  map_smul' c x := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply PiLp.ext; intro sr; simp [pair_smul]
    · simp

theorem J0lin_norm (x : Pub V0) : ‖J0lin D x‖ = ‖x‖ := by
  have hiso := SplitBoundary.fixedSplit_isometry D.slot D.slots_pos
  have hn : ∀ w : Double V0, ‖SplitBoundary.fixedSplit D.slot w‖ = ‖w‖ :=
    ((SplitBoundary.fixedSplit D.slot).norm_map_iff_adjoint_comp_self.mpr hiso)
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖WithLp.toLp 2 (WithLp.toLp 2 (fun sr : Bool × Bool =>
    SplitBoundary.fixedSplit D.slot (pair x sr.1 sr.2)), x.snd.snd)‖ ^ 2 = ‖x‖ ^ 2
  rw [WithLp.prod_norm_sq_eq_of_L2, norm_sq_pub]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [hn]
  rw [sum_norm_sq_pair]

/-- The sparse-branch isometry `J₀`. -/
def J0 : Pub V0 →ₗᵢ[ℂ] P0 n where
  toLinearMap := J0lin D
  norm_map' := J0lin_norm D

theorem J0_apply_fst (x : Pub V0) (sr : Bool × Bool) :
    (J0 D x).fst sr = SplitBoundary.fixedSplit D.slot (pair x sr.1 sr.2) := rfl

theorem J0_apply_snd (x : Pub V0) : (J0 D x).snd = x.snd.snd := rfl

/-- `K₀ = (1 ⊗ G) ⊕ 0`. -/
def K0 (x : X) : P0 n →L[ℂ] P0 n :=
  blockMap (WeightedClock.diagonal (fun _ : Bool × Bool =>
    FixedNativeCayleySimulation.generator D x)) 0 0 0

theorem K0_apply (x : X) (v : P0 n) :
    K0 D x v = WithLp.toLp 2 (WithLp.toLp 2 (fun sr : Bool × Bool =>
      FixedNativeCayleySimulation.generator D x (v.fst sr)), 0) := by
  simp only [K0, blockMap_apply, zero_apply, add_zero]
  rfl

theorem generator_adjoint (x : X) :
    ((FixedNativeCayleySimulation.generator D x)†) = FixedNativeCayleySimulation.generator D x := by
  rw [← star_eq_adjoint]; exact FixedNativeCayleySimulation.generator_self_adjoint D x

omit [DecidableEq n] in
theorem quad_diagonal_adjoint (T : OrientedSpace n →L[ℂ] OrientedSpace n) (hT : (T†) = T) :
    ((WeightedClock.diagonal (fun _ : Bool × Bool => T))†) =
      WeightedClock.diagonal (fun _ : Bool × Bool => T) := by
  rw [WeightedClock.diagonal_adjoint]
  simp only [hT]

theorem K0_selfAdjoint (x : X) : ((K0 D x)†) = K0 D x := by
  rw [K0, block_adjoint, quad_diagonal_adjoint _ (generator_adjoint D x)]
  simp only [map_zero]

/-- Compression of `G` through the split boundary, pointwise. -/
theorem inner_split_G (x : X) (u w : Double V0) :
    inner ℂ (SplitBoundary.fixedSplit D.slot u)
        (FixedNativeCayleySimulation.generator D x (SplitBoundary.fixedSplit D.slot w)) =
      ((Real.sqrt (s : ℝ) : ℝ) : ℂ)⁻¹ *
        inner ℂ u (dilation (SparseStateOverlap.matrixOperator (D.matrix x)) w) := by
  have h := congrArg (fun T : Double V0 →L[ℂ] Double V0 => inner ℂ u (T w))
    (SplitBoundary.split_compression D x)
  simp only [comp_apply, adjoint_inner_right, smul_apply, inner_smul_right] at h
  exact h

/-- **Compression of the sparse branch** `J₀† K₀ J₀ = H₀/√s`. -/
theorem J0_compression (x : X) :
    ((J0 D).toContinuousLinearMap†) ∘L K0 D x ∘L (J0 D).toContinuousLinearMap =
      ((Real.sqrt (s : ℝ) : ℝ) : ℂ)⁻¹ • H0 (SparseStateOverlap.matrixOperator (D.matrix x)) := by
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_left ℂ
  intro y
  rw [comp_apply, comp_apply, adjoint_inner_right]
  simp only [LinearIsometry.coe_toContinuousLinearMap]
  rw [K0_apply, WithLp.prod_inner_apply, PiLp.inner_apply]
  simp only [WithLp.ofLp_fst, WithLp.ofLp_snd, 
    inner_zero_right, add_zero, J0_apply_fst, inner_split_G]
  rw [← Finset.mul_sum, smul_apply, inner_smul_right]
  congr 1
  rw [H0, lift_apply, inner_pub]
  simp only [mul_zero, add_zero, Fintype.sum_prod_type,
    Fintype.sum_bool, pair, sector, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    ↓reduceIte, zb_apply,
    dilation_apply, WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
    WithLp.toLp_fst, WithLp.toLp_snd, inner_smul_left, inner_smul_right, map_smul, map_neg,
    inner_neg_right, map_one]
  ring

theorem K0_J0_norm_sq (x : X) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) (u : Pub V0) :
    ‖K0 D x (J0 D u)‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [K0_apply, WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, norm_zero]
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [J0_apply_fst]
  have h : ∀ sr : Bool × Bool,
      ‖FixedNativeCayleySimulation.generator D x
        (SplitBoundary.fixedSplit D.slot (pair u sr.1 sr.2))‖ ^ 2 ≤ ‖pair u sr.1 sr.2‖ ^ 2 :=
    fun sr => SplitBoundary.split_moment D x hrow hcol _
  calc (∑ sr : Bool × Bool, ‖FixedNativeCayleySimulation.generator D x
        (SplitBoundary.fixedSplit D.slot (pair u sr.1 sr.2))‖ ^ 2) + 0 ^ 2
      ≤ ∑ sr : Bool × Bool, ‖pair u sr.1 sr.2‖ ^ 2 := by
        rw [zero_pow two_ne_zero, add_zero]; exact Finset.sum_le_sum fun sr _ => h sr
    _ = ‖u.fst‖ ^ 2 + ‖u.snd.fst‖ ^ 2 := sum_norm_sq_pair u
    _ ≤ ‖u‖ ^ 2 := by rw [norm_sq_pub]; nlinarith [sq_nonneg ‖u.snd.snd‖]

theorem K0_bound (x : X) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1) (v : P0 n) :
    ‖K0 D x v‖ ≤ Real.sqrt (s : ℝ) * ‖v‖ := by
  have hG := FixedNativeCayleySimulation.generator_norm_le D x hrow
  apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
  rw [K0_apply, WithLp.prod_norm_sq_eq_of_L2, mul_pow, WithLp.prod_norm_sq_eq_of_L2 v]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, norm_zero]
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp only
  have h : ∀ sr : Bool × Bool, ‖FixedNativeCayleySimulation.generator D x (v.fst sr)‖ ^ 2 ≤
      Real.sqrt (s : ℝ) ^ 2 * ‖v.fst sr‖ ^ 2 := by
    intro sr
    have := (FixedNativeCayleySimulation.generator D x).le_opNorm (v.fst sr)
    have h2 := mul_le_mul_of_nonneg_right hG (norm_nonneg (v.fst sr))
    have h3 := pow_le_pow_left₀ (norm_nonneg _) (this.trans h2) 2
    rwa [mul_pow] at h3
  rw [zero_pow two_ne_zero, add_zero]
  have hsum := Finset.sum_le_sum fun sr (_ : sr ∈ Finset.univ) => h sr
  rw [← Finset.mul_sum] at hsum
  nlinarith [sq_nonneg (Real.sqrt (s : ℝ)), sq_nonneg ‖v.snd‖]

/-- **Lemma `qls:lem:entry` for `H₀`.** -/
theorem branchProps (x : X) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) :
    BranchProps (SparseStateOverlap.matrixOperator (D.matrix x)) (s : ℝ) (J0 D) (K0 D x) where
  selfAdjoint := K0_selfAdjoint D x
  compression := J0_compression D x
  moment := K0_J0_norm_sq D x hrow hcol
  bound := K0_bound D x hrow

end

end SparseLinearSystems.SparseBranch
