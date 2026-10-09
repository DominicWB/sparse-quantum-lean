import SparseLowerBounds.Helpers.Chains.Block

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Helpers for `Hamiltonian/Chains`: the gauge computations

Generic forms of the gauge facts of `Hamiltonian/Chains`, stated over an
arbitrary family of register blocks `V : ℕ → Matrix (Fin m) (Fin m) ℂ`
(the chains module instantiates `V = gaugeBlock`):

* `cvec n m k = |k⟩ ⊗ v` (definitionally `Hamiltonian.chainVec`), its norm and
  its amplitudes under `B ⊗ I`;
* the blocks `searchBlocks` of the search-decorated chain and the per-block
  gauge identity `V_i† H_{ik} V_k = B_{ik} I` (`gauge_block`);
* block-diagonal matrices `of fun p q => if p.1 = q.1 then W p.1 p.2 q.2 else 0`
  as `Matrix.comp` of a diagonal, their adjoints, and their action on `cvec`.
-/

namespace SparseLowerBounds.Helpers.Chains

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open SparseLowerBounds.Hamiltonian

variable {n m : ℕ}

/-- `|k⟩ ⊗ v` with the alternating vector `v` on the register. -/
def cvec (n m : ℕ) (k : Fin (n + 1)) : EuclideanSpace ℂ (Fin (n + 1) × Fin m) :=
  WithLp.toLp 2 fun p => if p.1 = k then alt m p.2 else 0

theorem cvec_apply (k : Fin (n + 1)) (p : Fin (n + 1) × Fin m) :
    cvec n m k p = if p.1 = k then alt m p.2 else 0 := rfl

theorem norm_cvec (hm0 : 0 < m) (k : Fin (n + 1)) : ‖cvec n m k‖ = 1 := by
  have hA : ∑ a, ‖alt m a‖ ^ 2 = 1 := by
    have h := norm_alt hm0
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
    exact h
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fintype.sum_prod_type, Finset.sum_eq_single k]
  · simpa [cvec_apply] using hA
  · intro i _ hi
    simp [cvec_apply, hi]
  · simp

theorem inner_cvec_evolve_kronecker (hm0 : 0 < m) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (τ : ℝ) (k k' : Fin (n + 1)) :
    ⟪cvec n m k, evolve (Matrix.kronecker B (1 : Matrix (Fin m) (Fin m) ℂ)) τ (cvec n m k')⟫_ℂ =
      evolve B τ (EuclideanSpace.single k' 1) k := by
  have hcomp : ∀ p : Fin (n + 1) × Fin m,
      evolve (Matrix.kronecker B (1 : Matrix (Fin m) (Fin m) ℂ)) τ (cvec n m k') p =
        evolve B τ (EuclideanSpace.single k' 1) p.1 • alt m p.2 := by
    intro p
    rw [evolve_kronecker_one_apply]
    have hv : (WithLp.toLp 2 fun i => cvec n m k' (i, p.2) : EuclideanSpace ℂ (Fin (n + 1))) =
        alt m p.2 • EuclideanSpace.single k' 1 := by
      ext i
      by_cases h : i = k'
      · subst h
        simp [cvec_apply]
      · simp [cvec_apply, h]
    rw [hv, map_smul, PiLp.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  have hA : ∑ a, ⟪alt m a, alt m a⟫_ℂ = 1 := by
    have h := norm_alt hm0
    have h2 : ⟪(WithLp.toLp 2 (alt m) : EuclideanSpace ℂ (Fin m)),
        (WithLp.toLp 2 (alt m) : EuclideanSpace ℂ (Fin m))⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, h]
      simp
    rw [PiLp.inner_apply] at h2
    exact h2
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_eq_single k]
  · simp only [hcomp, inner_smul_right]
    rw [← Finset.mul_sum]
    have hc : ∀ a, cvec n m k (k, a) = alt m a := by
      intro a
      simp [cvec_apply]
    simp only [hc, hA, mul_one]
  · intro i _ hi
    refine Finset.sum_eq_zero fun a _ => ?_
    have hc : cvec n m k (i, a) = 0 := by
      simp [cvec_apply, hi]
    rw [hc, inner_zero_left]
  · simp

/-! ### Block-diagonal matrices on `clock × register` -/

/-- The block-diagonal matrix with register blocks `W_k` on clock `k`. -/
def blockDiag (n m : ℕ) (W : ℕ → Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin (n + 1) × Fin m) (Fin (n + 1) × Fin m) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then W p.1 p.2 q.2 else 0

theorem blockDiag_eq_comp (W : ℕ → Matrix (Fin m) (Fin m) ℂ) :
    blockDiag n m W =
      Matrix.comp _ _ _ _ ℂ (Matrix.diagonal fun i : Fin (n + 1) => W i) := by
  ext ⟨i, a⟩ ⟨k, b⟩
  simp only [blockDiag, Matrix.of_apply, Matrix.comp_apply]
  by_cases h : i = k
  · subst h
    simp
  · simp [h]

theorem conjTranspose_blockDiag (W : ℕ → Matrix (Fin m) (Fin m) ℂ) :
    (blockDiag n m W)ᴴ = blockDiag n m fun k => (W k)ᴴ := by
  ext p q
  rw [Matrix.conjTranspose_apply]
  simp only [blockDiag, Matrix.of_apply]
  by_cases h : p.1 = q.1
  · rw [if_pos h.symm, if_pos h, Matrix.conjTranspose_apply, h]
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

/-- A block-diagonal matrix with `W_k v = s_k v` acts on `|k, v⟩` as `s_k`. -/
theorem blockDiag_cvec (W : ℕ → Matrix (Fin m) (Fin m) ℂ) (s : ℕ → ℂ)
    (hW : ∀ k, W k *ᵥ alt m = s k • alt m) (k : Fin (n + 1)) :
    SparseHamiltonian.SparseStateOverlap.matrixOperator (blockDiag n m W) (cvec n m k) =
      s k • cvec n m k := by
  ext ⟨i, a⟩
  rw [SparseHamiltonian.SparseStateOverlap.matrixOperator_apply, Fintype.sum_prod_type,
    Finset.sum_eq_single i]
  · by_cases h : i = k
    · subst h
      have h1 := congrFun (hW i) a
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
      simpa [blockDiag, cvec_apply] using h1
    · simp [blockDiag, cvec_apply, h]
  · intro b _ hb
    refine Finset.sum_eq_zero fun a' _ => ?_
    simp [blockDiag, Ne.symm hb]
  · simp

/-! ### The search-decorated chain as a block matrix -/

/-- The blocks of the decorated chain on `clock × clock`. -/
def searchBlocks (n m : ℕ) (c : ℕ → ℝ) (j : Fin n → Fin m) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (Matrix (Fin m) (Fin m) ℂ) :=
  Matrix.of fun i k =>
    if h : (i : ℕ) = k + 1 then
      (c k : ℂ) • LinearSystems.gadget m (j ⟨k, by have := i.isLt; omega⟩)
    else if h' : (k : ℕ) = i + 1 then
      (c i : ℂ) • (LinearSystems.gadget m (j ⟨i, by have := k.isLt; omega⟩))ᵀ
    else 0

theorem conjTranspose_gadget_mul_gadget (j : Fin m) :
    (LinearSystems.gadget m j)ᴴ * LinearSystems.gadget m j = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff'.mp (LinearSystems.gadget_mem_unitaryGroup j)

theorem transpose_gadget (j : Fin m) :
    (LinearSystems.gadget m j)ᵀ = (LinearSystems.gadget m j)ᴴ := by
  ext a b
  rw [Matrix.transpose_apply, Matrix.conjTranspose_apply, LinearSystems.star_gadget_apply]

/-- The per-block gauge identity `V_i† H_{ik} V_k = B_{ik} I`, for register
blocks with `V_{k+1} = U_{j k} V_k` (`k < n`) and `V_k† V_k = I`. -/
theorem gauge_block (c : ℕ → ℝ) (j : Fin n → Fin m) (V : ℕ → Matrix (Fin m) (Fin m) ℂ)
    (hrec : ∀ k (hk : k < n), V (k + 1) = LinearSystems.gadget m (j ⟨k, hk⟩) * V k)
    (hunit : ∀ k, (V k)ᴴ * V k = 1) (i k : Fin (n + 1)) :
    (V i)ᴴ * searchBlocks n m c j i k * V k =
      pathMatrix n c i k • (1 : Matrix (Fin m) (Fin m) ℂ) := by
  simp only [searchBlocks, pathMatrix, Matrix.of_apply]
  split_ifs with h1 h2
  · have hk : (k : ℕ) < n := by have := i.isLt; omega
    have hV : V i = LinearSystems.gadget m (j ⟨k, hk⟩) * V k := by
      rw [h1]
      exact hrec k hk
    rw [hV]
    have hU := conjTranspose_gadget_mul_gadget (j ⟨k, hk⟩)
    calc (LinearSystems.gadget m (j ⟨k, hk⟩) * V k)ᴴ *
          ((c k : ℂ) • LinearSystems.gadget m (j ⟨k, hk⟩)) * V k
        = (c k : ℂ) • ((V k)ᴴ * ((LinearSystems.gadget m (j ⟨k, hk⟩))ᴴ *
            LinearSystems.gadget m (j ⟨k, hk⟩)) * V k) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one, hunit]
  · have hi : (i : ℕ) < n := by have := k.isLt; omega
    have hV : V k = LinearSystems.gadget m (j ⟨i, hi⟩) * V i := by
      rw [h2]
      exact hrec i hi
    rw [hV, transpose_gadget]
    have hU := conjTranspose_gadget_mul_gadget (j ⟨i, hi⟩)
    calc (V i)ᴴ * ((c i : ℂ) • (LinearSystems.gadget m (j ⟨i, hi⟩))ᴴ) *
          (LinearSystems.gadget m (j ⟨i, hi⟩) * V i)
        = (c i : ℂ) • ((V i)ᴴ * ((LinearSystems.gadget m (j ⟨i, hi⟩))ᴴ *
            LinearSystems.gadget m (j ⟨i, hi⟩)) * V i) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one, hunit]
  · simp

/-! ### Diagonal matrices and scalar identities -/

theorem mO_diagonal_apply {S : Type*} [Fintype S] [DecidableEq S] (d : S → ℂ)
    (v : EuclideanSpace ℂ S) (i : S) :
    SparseHamiltonian.SparseStateOverlap.matrixOperator (Matrix.diagonal d) v i = d i * v i := by
  rw [SparseHamiltonian.SparseStateOverlap.matrixOperator_apply]
  simp [Matrix.diagonal_apply]

theorem mO_diagonal_single {S : Type*} [Fintype S] [DecidableEq S] (d : S → ℂ) (i₀ : S)
    (h : d i₀ = 1) :
    SparseHamiltonian.SparseStateOverlap.matrixOperator (Matrix.diagonal d)
      (EuclideanSpace.single i₀ 1) = EuclideanSpace.single i₀ 1 := by
  ext i
  rw [mO_diagonal_apply]
  by_cases hi : i = i₀
  · subst hi
    rw [h, one_mul]
  · simp [hi]

/-- If `V† V = I`, `s² = 1` and `V v = s v`, then `V† v = s v`. -/
theorem conjTranspose_mulVec_of_mulVec {V : Matrix (Fin m) (Fin m) ℂ} {v : Fin m → ℂ} {s : ℂ}
    (hV : Vᴴ * V = 1) (hs : s * s = 1) (h : V *ᵥ v = s • v) : Vᴴ *ᵥ v = s • v := by
  have h1 : Vᴴ *ᵥ (V *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hV, Matrix.one_mulVec]
  rw [h, Matrix.mulVec_smul] at h1
  calc Vᴴ *ᵥ v = (s * s) • (Vᴴ *ᵥ v) := by rw [hs, one_smul]
    _ = s • v := by rw [mul_smul, h1]

/-- The path with weights `c_k` and edge signs `s_k` (the scalar chain for
`s_k = (-1)^{x_k}`). -/
def signedPath (n : ℕ) (c : ℕ → ℝ) (s : Fin n → ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun i j =>
    if h : (i : ℕ) = j + 1 then (c j : ℂ) * s ⟨j, by have := i.isLt; omega⟩
    else if h' : (j : ℕ) = i + 1 then (c i : ℂ) * s ⟨i, by have := j.isLt; omega⟩
    else 0

/-- The diagonal sign gauge: `d_{k+1} = s_k d_k` and `d_k² = 1` give
`H_s = D B D`. -/
theorem signedPath_eq_conj (c : ℕ → ℝ) (s : Fin n → ℂ) (d : ℕ → ℂ)
    (hrec : ∀ k (hk : k < n), d (k + 1) = s ⟨k, hk⟩ * d k) (hd : ∀ k, d k * d k = 1) :
    signedPath n c s =
      Matrix.diagonal (fun k : Fin (n + 1) => d k) * pathMatrix n c *
        Matrix.diagonal (fun k : Fin (n + 1) => d k) := by
  ext i k
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [signedPath, pathMatrix, Matrix.of_apply]
  split_ifs with h1 h2
  · have hk : (k : ℕ) < n := by have := i.isLt; omega
    have hdi : d i = s ⟨k, hk⟩ * d k := by
      rw [h1]
      exact hrec k hk
    rw [hdi]
    linear_combination (-(s ⟨k, hk⟩ * (c k : ℂ))) * hd k
  · have hi : (i : ℕ) < n := by have := k.isLt; omega
    have hdk : d k = s ⟨i, hi⟩ * d i := by
      rw [h2]
      exact hrec i hi
    rw [hdk]
    linear_combination (-(s ⟨i, hi⟩ * (c i : ℂ))) * hd i
  · simp

end

end SparseLowerBounds.Helpers.Chains
end
