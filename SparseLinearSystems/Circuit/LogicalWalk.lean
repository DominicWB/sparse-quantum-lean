import SparseLinearSystems.Sparse.SparseBranch

/-!
# The logical augmented walk and its query factorization

For sparse data `D`, a source circuit family `U_b` and a public seed vector,
the four-branch walk of `Augmented.Walk` is assembled for every public
regularization angle `σ` and norm guess `r`:

`W_{σ,r}(x) = (I - 2 J J†) Cayley(K_{σ,r}(x))`,

with `J = walkJ (J0 D)` and `K = walkK s (K0 D x) σ (1/r) β(x)`,
`β(x) = |0⟩|0⟩ U_b(x)|seed⟩`.  It is unitary for every unknown input `x`
(`Ww_unitary`); no promise is needed for this.

`Ww_factor` writes the walk as a product of fixed public operators,
one *sparse* factor (the native Cayley action of `NativeCayleyProgram` on the
four sparse cells) and two *source* factors (`U_b` and `U_b†` on one fixed
public slot):

`W = R · A_sp(x) · F_a · V(x) · F_b · V(x)†`.

This is the form compiled to primitive queries in `Circuit.Step`.

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/

namespace SparseLinearSystems.LogicalWalk

noncomputable section
open ContinuousLinearMap SparseHamiltonian HilbertBlocks HilbertRegularization
  HilbertAugmentation FourBranchCompression Augmented SparseBranch
open scoped InnerProduct ComplexConjugate
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- The private space of the four-branch walk. -/
abbrev Priv (n : Type*) [Fintype n] := Private (EuclideanSpace ℂ n) (P0 n)

/-! ### Cayley transforms of structured generators -/

section CayleyStructure

variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℂ (V i)] [∀ i, CompleteSpace (V i)] [∀ i, FiniteDimensional ℂ (V i)]

omit [∀ (i : ι), CompleteSpace (V i)] [∀ (i : ι), FiniteDimensional ℂ (V i)] in
theorem diagonal_sub_smul_one (K : ∀ i, V i →L[ℂ] V i) (c : ℂ) :
    WeightedClock.diagonal K - c • (1 : PiLp 2 V →L[ℂ] PiLp 2 V) =
      WeightedClock.diagonal (fun i => K i - c • 1) := by
  ext x i
  simp

omit [∀ (i : ι), CompleteSpace (V i)] [∀ (i : ι), FiniteDimensional ℂ (V i)] in
theorem diagonal_add_smul_one (K : ∀ i, V i →L[ℂ] V i) (c : ℂ) :
    WeightedClock.diagonal K + c • (1 : PiLp 2 V →L[ℂ] PiLp 2 V) =
      WeightedClock.diagonal (fun i => K i + c • 1) := by
  ext x i
  simp

omit [Fintype ι] [∀ (i : ι), CompleteSpace (V i)] [∀ (i : ι), FiniteDimensional ℂ (V i)] in
theorem diagonal_mul' (K L : ∀ i, V i →L[ℂ] V i) :
    WeightedClock.diagonal K * WeightedClock.diagonal L =
      WeightedClock.diagonal (fun i => K i * L i) :=
  WeightedClock.diagonal_comp K L

/-- The Cayley transform of a diagonal generator is diagonal. -/
theorem cayley_diagonal (K : ∀ i, V i →L[ℂ] V i) (hK : ∀ i, ((K i)†) = K i)
    (h : ((WeightedClock.diagonal K)†) = WeightedClock.diagonal K) :
    HilbertCayley.cayley (WeightedClock.diagonal K) h =
      WeightedClock.diagonal (fun i => HilbertCayley.cayley (K i) (hK i)) := by
  rw [CayleyAlgebra.cayley_eq_of_right_inverse _ h
    (WeightedClock.diagonal (fun i => HilbertCayley.denominatorInverse (K i) (hK i)))]
  · rw [diagonal_add_smul_one, diagonal_mul']
    rfl
  · rw [diagonal_sub_smul_one, diagonal_mul']
    have e : ∀ i, (K i - Complex.I • (1 : V i →L[ℂ] V i)) *
        HilbertCayley.denominatorInverse (K i) (hK i) = 1 := fun i =>
      CayleyAlgebra.cayley_mul_denominator (K i) (hK i)
    simp only [e]
    exact WeightedClock.diagonal_one

end CayleyStructure

theorem smul_blockMap {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup Q] [NormedSpace ℂ Q] (c : ℂ) (A : P →L[ℂ] P) (B : Q →L[ℂ] Q) :
    c • blockMap A 0 0 B = blockMap (c • A) 0 0 (c • B) := by
  ext x : 1
  apply prodExt <;> simp [blockMap_apply]

theorem smul_diagonal {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℂ (V i)] (c : ℂ) (K : ∀ i, V i →L[ℂ] V i) :
    c • WeightedClock.diagonal K = WeightedClock.diagonal (fun i => c • K i) := by
  ext x i
  simp

theorem cayley_congr {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] [FiniteDimensional ℂ V] (K K' : V →L[ℂ] V) (e : K = K')
    (h : (K†) = K) (h' : (K'†) = K') :
    HilbertCayley.cayley K h = HilbertCayley.cayley K' h' := by
  subst e
  rfl

/-- The four-branch Cayley transform is branchwise. -/
theorem cayley_fourDiagonal {P₀ P₁ P₂ P₃ : Type*}
    [NormedAddCommGroup P₀] [InnerProductSpace ℂ P₀] [CompleteSpace P₀] [FiniteDimensional ℂ P₀]
    [NormedAddCommGroup P₁] [InnerProductSpace ℂ P₁] [CompleteSpace P₁] [FiniteDimensional ℂ P₁]
    [NormedAddCommGroup P₂] [InnerProductSpace ℂ P₂] [CompleteSpace P₂] [FiniteDimensional ℂ P₂]
    [NormedAddCommGroup P₃] [InnerProductSpace ℂ P₃] [CompleteSpace P₃] [FiniteDimensional ℂ P₃]
    (K₀ : P₀ →L[ℂ] P₀) (K₁ : P₁ →L[ℂ] P₁) (K₂ : P₂ →L[ℂ] P₂) (K₃ : P₃ →L[ℂ] P₃)
    (h₀ : (K₀†) = K₀) (h₁ : (K₁†) = K₁) (h₂ : (K₂†) = K₂) (h₃ : (K₃†) = K₃)
    (h : ((diagonal K₀ K₁ K₂ K₃)†) = diagonal K₀ K₁ K₂ K₃) :
    HilbertCayley.cayley (diagonal K₀ K₁ K₂ K₃) h =
      diagonal (HilbertCayley.cayley K₀ h₀) (HilbertCayley.cayley K₁ h₁)
        (HilbertCayley.cayley K₂ h₂) (HilbertCayley.cayley K₃ h₃) := by
  have h23 := CayleyAlgebra.blockMap_selfAdjoint K₂ K₃ h₂ h₃
  have h123 := CayleyAlgebra.blockMap_selfAdjoint K₁ _ h₁ h23
  unfold diagonal
  rw [CayleyAlgebra.cayley_blockMap K₀ _ h₀ h123 h, CayleyAlgebra.cayley_blockMap K₁ _ h₁ h23,
    CayleyAlgebra.cayley_blockMap K₂ K₃ h₂ h₃]

/-! ### The native sparse Cayley action -/

variable [Fintype Z] [AddCommGroup Z] [DecidableEq Z]

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem generator_smul_selfAdjoint (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (γ : ℝ) : ((((γ : ℂ) • FixedNativeCayleySimulation.generator D x))†) =
      (γ : ℂ) • FixedNativeCayleySimulation.generator D x :=
  Augmented.real_smul_selfAdjoint γ _ (generator_adjoint D x)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The Cayley transform of `γ G` is the native Cayley action. -/
theorem cayley_smul_generator (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (γ : ℝ)
    (h : ((((γ : ℂ) • FixedNativeCayleySimulation.generator D x))†) =
      (γ : ℂ) • FixedNativeCayleySimulation.generator D x) :
    HilbertCayley.cayley ((γ : ℂ) • FixedNativeCayleySimulation.generator D x) h =
      FixedNativeCayleySimulation.action D x γ := by
  rw [CayleyAlgebra.cayley_eq_of_right_inverse _ h (FixedNativeCayleySimulation.inverse D x γ)
    (FixedNativeCayleySimulation.inverse_right D x γ),
    FixedNativeCayleySimulation.action_eq_cayley]
  rfl

/-- The sparse factor: the native action on the four sparse cells of branch zero. -/
def sparseCells (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (γ : ℝ) :
    P0 n →L[ℂ] P0 n :=
  blockMap (WeightedClock.diagonal (fun _ : Bool × Bool =>
    FixedNativeCayleySimulation.action D x γ)) 0 0 1

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- `Cayley(γ K₀) = (native action on the cells) ⊕ (-1)`. -/
theorem cayley_K0 (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (γ : ℝ)
    (h : ((((γ : ℂ) • K0 D x))†) = (γ : ℂ) • K0 D x) :
    HilbertCayley.cayley ((γ : ℂ) • K0 D x) h =
      sparseCells D x γ * blockMap 1 0 0 (-1) := by
  have hdiag : ((WeightedClock.diagonal (fun _ : Bool × Bool =>
      (γ : ℂ) • FixedNativeCayleySimulation.generator D x))†) =
      WeightedClock.diagonal (fun _ : Bool × Bool =>
        (γ : ℂ) • FixedNativeCayleySimulation.generator D x) :=
    quad_diagonal_adjoint _ (generator_smul_selfAdjoint D x γ)
  have h0 : ((0 : ℂ →L[ℂ] ℂ)†) = 0 := map_zero _
  have hK : (γ : ℂ) • K0 D x = blockMap (WeightedClock.diagonal (fun _ : Bool × Bool =>
      (γ : ℂ) • FixedNativeCayleySimulation.generator D x)) 0 0 0 := by
    rw [K0, smul_blockMap, smul_diagonal, smul_zero]
  have hblock : ((blockMap (WeightedClock.diagonal (fun _ : Bool × Bool =>
      (γ : ℂ) • FixedNativeCayleySimulation.generator D x)) 0 0 (0 : ℂ →L[ℂ] ℂ))†) =
      blockMap (WeightedClock.diagonal (fun _ : Bool × Bool =>
        (γ : ℂ) • FixedNativeCayleySimulation.generator D x)) 0 0 0 :=
    CayleyAlgebra.blockMap_selfAdjoint _ _ hdiag h0
  have e := cayley_congr _ _ hK h hblock
  rw [e, CayleyAlgebra.cayley_blockMap _ _ hdiag h0 hblock,
    cayley_diagonal (fun _ : Bool × Bool => (γ : ℂ) • FixedNativeCayleySimulation.generator D x)
      (fun _ => generator_smul_selfAdjoint D x γ) hdiag,
    CayleyAlgebra.cayley_zero h0, sparseCells, CayleyAlgebra.blockMap_mul_diag]
  simp only [mul_one, one_mul]
  congr 1
  congr 1
  funext _
  exact cayley_smul_generator D x γ _

/-! ### The source slot -/

/-- `U` on the upper, register-zero, dilation-zero slot of a public vector. -/
def slotOp (U : V0 →L[ℂ] V0) : Pub V0 →L[ℂ] Pub V0 :=
  blockMap (blockMap (blockMap U 0 0 1) 0 0 1) 0 0 1

omit [DecidableEq n] in
theorem slotOp_apply (U : V0 →L[ℂ] V0) (y : Pub V0) :
    slotOp U y = mk (WithLp.toLp 2 (WithLp.toLp 2 (U y.fst.fst.fst, y.fst.fst.snd), y.fst.snd))
      y.snd.fst y.snd.snd := by
  simp [slotOp, blockMap_apply]
  rfl

omit [DecidableEq n] in
theorem slotOp_adjoint (U : V0 →L[ℂ] V0) : ((slotOp U)†) = slotOp (U†) := by
  simp only [slotOp, block_adjoint, map_zero, WalkGap.adjoint_one']

theorem blockMap_isUnitary {P Q : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [CompleteSpace P] [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (A : P →L[ℂ] P) (B : Q →L[ℂ] Q) (hA : OracleCircuit.IsUnitary A)
    (hB : OracleCircuit.IsUnitary B) : OracleCircuit.IsUnitary (blockMap A 0 0 B) := by
  have hs : star (blockMap A 0 0 B) = blockMap (star A) 0 0 (star B) := by
    rw [star_eq_adjoint, block_adjoint, star_eq_adjoint, star_eq_adjoint]
    simp only [map_zero]
  constructor
  · rw [hs, CayleyAlgebra.blockMap_mul_diag, hA.1, hB.1, CayleyAlgebra.blockMap_one']
  · rw [hs, CayleyAlgebra.blockMap_mul_diag, hA.2, hB.2, CayleyAlgebra.blockMap_one']

omit [DecidableEq n] in
theorem slotOp_unitary (U : V0 →L[ℂ] V0) (hU : OracleCircuit.IsUnitary U) :
    OracleCircuit.IsUnitary (slotOp U) :=
  blockMap_isUnitary _ _ (blockMap_isUnitary _ _ (blockMap_isUnitary _ _ hU
    OracleCircuit.isUnitary_one) OracleCircuit.isUnitary_one) OracleCircuit.isUnitary_one

omit [DecidableEq n] in
theorem inner_betaOf (v : V0) (y : Sys V0) : inner ℂ (betaOf v) y = inner ℂ v y.fst.fst := by
  simp [betaOf, WithLp.prod_inner_apply]

omit [DecidableEq n] in
theorem slotOp_betaOf (U : V0 →L[ℂ] V0) (v : V0) :
    (slotOp U) (mk (betaOf v) 0 0) = mk (betaOf (U v)) 0 0 := by
  rw [slotOp_apply]
  simp [betaOf]

omit [DecidableEq n] in
/-- Conjugating `T₂` by the source slot changes `β = |0⟩|0⟩ v` into
`|0⟩|0⟩ U v`. -/
theorem T2_slot (U : V0 →L[ℂ] V0) (v : V0) :
    T2 (betaOf (U v)) = slotOp U * T2 (betaOf v) * ((slotOp U)†) := by
  ext1 y
  rw [mul_apply_eq_comp, mul_apply_eq_comp, slotOp_adjoint, slotOp_apply (U†) y, T2_apply,
    T2_apply, slotOp_apply]
  apply prodExt
  · simp only [mk_fst, mk_snd_snd]
    apply prodExt
    · apply prodExt
      · simp [betaOf, map_smul]
      · simp [betaOf]
    · simp [betaOf]
  · apply prodExt
    · simp
    · simp only [mk_snd_snd, inner_betaOf, WithLp.toLp_fst]
      rw [← adjoint_inner_right]

/-! ### The logical walk -/

/-- `β(x) = |0⟩|0⟩ U_b(x) |seed⟩`. -/
def beta (Ub : X → V0 →L[ℂ] V0) (sv : V0) (x : X) : Sys V0 := betaOf (Ub x sv)

/-- The four-branch boundary isometry. -/
def Jw (D : NativeSparseBlockEncoding.Data X n Z s) : Pub V0 →ₗᵢ[ℂ] Priv n :=
  walkJ (J0 D)

/-- The four-branch generator `K_{σ,r}(x)`. -/
def Kw (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (σ r : ℝ) (x : X) : Priv n →L[ℂ] Priv n :=
  walkK (s : ℝ) (K0 D x) σ (1 / r) (beta Ub sv x)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem Kw_selfAdjoint (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (σ r : ℝ) (x : X) : ((Kw D Ub sv σ r x)†) = Kw D Ub sv σ r x :=
  walkK_selfAdjoint (K0 D x) (K0_selfAdjoint D x) σ (1 / r) _

/-- The walk `W_{σ,r}(x) = (I - 2JJ†) Cayley(K_{σ,r}(x))`. -/
def Ww (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (σ r : ℝ) (x : X) : Priv n →L[ℂ] Priv n :=
  WalkGap.walk (Jw D).toContinuousLinearMap
    (HilbertCayley.cayley (Kw D Ub sv σ r x) (Kw_selfAdjoint D Ub sv σ r x))

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem Ww_unitary (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (σ r : ℝ) (x : X) : OracleCircuit.IsUnitary (Ww D Ub sv σ r x) :=
  WalkGap.walk_unitary _ (LinearIsometry.adjoint_comp_self _) _
    (HilbertCayley.cayley_unitary _ _)

/-! ### The query factorization -/

/-- The sparse factor `A_sp(x) = (native action on the four cells) ⊕ 1 ⊕ 1 ⊕ 1`. -/
def Asp (D : NativeSparseBlockEncoding.Data X n Z s) (σ : ℝ) (x : X) : Priv n →L[ℂ] Priv n :=
  diagonal (sparseCells D x (w0 σ)) 1 1 1

/-- The first fixed factor. -/
def Fa (s σ : ℝ) : Priv n →L[ℂ] Priv n :=
  diagonal (blockMap 1 0 0 (-1))
    (HilbertCayley.cayley ((w1 s σ : ℂ) • (T1 : Pub V0 →L[ℂ] Pub V0))
      (real_smul_selfAdjoint _ _ T1_selfAdjoint)) 1 (-1)

/-- The source factor `V(x)`. -/
def Vd (U : V0 →L[ℂ] V0) : Priv n →L[ℂ] Priv n := diagonal 1 1 (slotOp U) 1

/-- The second fixed factor, built from the public seed vector. -/
def Fb (s r : ℝ) (sv : V0) : Priv n →L[ℂ] Priv n :=
  diagonal 1 1 (HilbertCayley.cayley ((w2 s (1 / r) : ℂ) • T2 (betaOf sv))
    (real_smul_selfAdjoint _ _ (T2_selfAdjoint _))) 1

omit [DecidableEq n] in
theorem Vd_adjoint (U : V0 →L[ℂ] V0) : ((Vd (n := n) U)†) = Vd (U†) := by
  rw [Vd, diagonal_adjoint, slotOp_adjoint]
  simp only [WalkGap.adjoint_one']
  rfl

/-- Branchwise factorization of a four-branch diagonal. -/
theorem diag_product {P₀ P₁ P₂ P₃ : Type*}
    [NormedAddCommGroup P₀] [InnerProductSpace ℂ P₀] [NormedAddCommGroup P₁]
    [InnerProductSpace ℂ P₁] [NormedAddCommGroup P₂] [InnerProductSpace ℂ P₂]
    [NormedAddCommGroup P₃] [InnerProductSpace ℂ P₃]
    (a b : P₀ →L[ℂ] P₀) (c : P₁ →L[ℂ] P₁) (S C S' : P₂ →L[ℂ] P₂) (d : P₃ →L[ℂ] P₃) :
    diagonal (a * b) c (S * C * S') d =
      diagonal a 1 1 1 * (diagonal b c 1 d * (diagonal 1 1 S 1 * (diagonal 1 1 C 1 *
        diagonal 1 1 S' 1))) := by
  simp only [diagonal_mul, mul_one, one_mul, mul_assoc]

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **Query factorization of the walk.**
`W = R · (A_sp(x) · (F_a · (V(x) · (F_b · V(x)†))))`, with `V(x)† = V(U_b(x)†)`. -/
theorem Ww_factor (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (σ r : ℝ) (x : X) (hU : OracleCircuit.IsUnitary (Ub x)) :
    Ww D Ub sv σ r x =
      WalkGap.reflection (Jw D).toContinuousLinearMap *
        (Asp D σ x * (Fa (s : ℝ) σ * (Vd (Ub x) * (Fb (s : ℝ) r sv * Vd ((Ub x)†))))) := by
  have hT1 := real_smul_selfAdjoint (w1 (s : ℝ) σ) (T1 : Pub V0 →L[ℂ] Pub V0) T1_selfAdjoint
  have hT2 := real_smul_selfAdjoint (w2 (s : ℝ) (1 / r)) (T2 (beta Ub sv x)) (T2_selfAdjoint _)
  have hT2' := real_smul_selfAdjoint (w2 (s : ℝ) (1 / r)) (T2 (betaOf sv)) (T2_selfAdjoint _)
  have hK0 := real_smul_selfAdjoint (w0 σ) (K0 D x) (K0_selfAdjoint D x)
  have h0 : ((0 : Pub V0 →L[ℂ] Pub V0)†) = 0 := map_zero _
  -- Cayley of the four-branch generator
  have hC : HilbertCayley.cayley (Kw D Ub sv σ r x) (Kw_selfAdjoint D Ub sv σ r x) =
      diagonal (HilbertCayley.cayley _ hK0) (HilbertCayley.cayley _ hT1)
        (HilbertCayley.cayley _ hT2) (HilbertCayley.cayley _ h0) :=
    cayley_fourDiagonal _ _ _ _ hK0 hT1 hT2 h0 _
  -- the source conjugation
  have hU' : ((slotOp (Ub x))†) * slotOp (Ub x) = 1 ∧ slotOp (Ub x) * ((slotOp (Ub x))†) = 1 := by
    have := slotOp_unitary (Ub x) hU
    rw [← star_eq_adjoint]
    exact this
  have hconj_op : (w2 (s : ℝ) (1 / r) : ℂ) • T2 (beta Ub sv x) =
      slotOp (Ub x) * ((w2 (s : ℝ) (1 / r) : ℂ) • T2 (betaOf sv)) * ((slotOp (Ub x))†) := by
    rw [beta, T2_slot]
    ext1 y
    simp only [smul_apply, mul_apply_eq_comp, map_smul]
  have hC2 : HilbertCayley.cayley _ hT2 =
      slotOp (Ub x) * HilbertCayley.cayley _ hT2' * ((slotOp (Ub x))†) := by
    rw [cayley_congr _ _ hconj_op hT2 (hconj_op ▸ hT2)]
    exact CayleyAlgebra.cayley_conj _ hT2' _ hU' _
  have hC0 := cayley_K0 D x (w0 σ) hK0
  have hC3 := CayleyAlgebra.cayley_zero h0
  calc Ww D Ub sv σ r x
      = WalkGap.reflection (Jw D).toContinuousLinearMap *
          HilbertCayley.cayley (Kw D Ub sv σ r x) (Kw_selfAdjoint D Ub sv σ r x) := rfl
    _ = WalkGap.reflection (Jw D).toContinuousLinearMap *
          diagonal (sparseCells D x (w0 σ) * blockMap 1 0 0 (-1)) (HilbertCayley.cayley _ hT1)
            (slotOp (Ub x) * HilbertCayley.cayley _ hT2' * ((slotOp (Ub x))†)) (-1) := by
        rw [hC, hC0, hC2, hC3]
    _ = WalkGap.reflection (Jw D).toContinuousLinearMap *
          (Asp D σ x * (Fa (s : ℝ) σ * (Vd (Ub x) * (Fb (s : ℝ) r sv * Vd ((Ub x)†))))) := by
        rw [slotOp_adjoint, diag_product]
        rfl

end

end SparseLinearSystems.LogicalWalk
