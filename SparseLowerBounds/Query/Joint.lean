import SparseLowerBounds.Helpers.Joint.ProdMat

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The joint hidden-input and workspace space

The multiplicative adversary of `qlsl:lem:xor` and `hsl:lem:search`
(manuscript lines 5143-5210 and 2172-2203) purifies the unknown input: it
adjoins a register holding the hidden input `j : J`, so that the joint state
is `Σ_j |j⟩ ⊗ Ψ_j`. We represent `ℂ^J ⊗ K` as the finite `L²` sum
`Joint J K = PiLp 2 (fun _ : J => K)`; no tensor-product library is used, and
`K` may be any complex Hilbert space. Operators are assembled componentwise
(`Joint.mk`).

* `fiber F` is the input-controlled operator `Σ_j |j⟩⟨j| ⊗ F j`; the run of a
  program on hidden input `j` is `fiber (fun j => p.eval j)`.
* `kernel T` is `T ⊗ 1_K` for a matrix `T` on `ℂ^J`.
* For `J = Fin n → Fin m` (`n` hidden positions in `Fin m`), `onReg k A` is the
  matrix `A` acting on hidden register `k`, and `tensorPow A = A^{⊗ n}`.

Matrices carry the `L²` operator norm (`Matrix.Norms.L2Operator`), which is the
norm of `Matrix.toEuclideanCLM`.
-/

namespace SparseLowerBounds

noncomputable section
open scoped InnerProduct Matrix Matrix.Norms.L2Operator

/-- `ℂ^J ⊗ K`, as the `L²` direct sum of `J` copies of `K`. -/
abbrev Joint (J K : Type*) [NormedAddCommGroup K] : Type _ := PiLp 2 (fun _ : J => K)

namespace Joint

variable {J K : Type*} [Fintype J]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The component at hidden input `j`. -/
def proj (j : J) : Joint J K →L[ℂ] K := PiLp.proj (p := 2) (β := fun _ : J => K) j

omit [Fintype J] [CompleteSpace K] in
@[simp] theorem proj_apply (j : J) (Ψ : Joint J K) : proj j Ψ = Ψ j := rfl

/-- Assemble an operator on the joint space from its components. -/
def mk (L : J → Joint J K →L[ℂ] K) : Joint J K →L[ℂ] Joint J K :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : J => K)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi L

omit [Fintype J] [CompleteSpace K] in
@[simp] theorem mk_apply (L : J → Joint J K →L[ℂ] K) (Ψ : Joint J K) (j : J) :
    mk L Ψ j = L j Ψ := rfl

/-- The joint state that holds the same workspace vector `φ` for every input.
With the normalisation `m^{-n/2}` it is the purified initial state. -/
def const (φ : K) : Joint J K := WithLp.toLp 2 fun _ => φ

omit [Fintype J] [InnerProductSpace ℂ K] [CompleteSpace K] in
@[simp] theorem const_apply (φ : K) (j : J) : (const φ : Joint J K) j = φ := rfl

omit [InnerProductSpace ℂ K] [CompleteSpace K] in
/-- `‖Σ_j |j⟩ ⊗ φ‖² = |J| ‖φ‖²`. -/
theorem norm_const_sq (φ : K) :
    ‖(const φ : Joint J K)‖ ^ 2 = (Fintype.card J : ℝ) * ‖φ‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp

/-! ### Input-controlled operators -/

/-- The input-controlled operator `Σ_j |j⟩⟨j| ⊗ F j`. -/
def fiber (F : J → K →L[ℂ] K) : Joint J K →L[ℂ] Joint J K :=
  mk fun j => F j ∘L proj j

omit [Fintype J] [CompleteSpace K] in
@[simp] theorem fiber_apply (F : J → K →L[ℂ] K) (Ψ : Joint J K) (j : J) :
    fiber F Ψ j = F j (Ψ j) := rfl

omit [Fintype J] [CompleteSpace K] in
theorem fiber_mul (F G : J → K →L[ℂ] K) :
    fiber F * fiber G = fiber fun j => F j * G j := by
  ext Ψ j
  rfl

omit [CompleteSpace K] in
theorem fiber_add (F G : J → K →L[ℂ] K) :
    fiber F + fiber G = fiber fun j => F j + G j := by
  ext Ψ j
  rfl

omit [Fintype J] [CompleteSpace K] in
@[simp] theorem fiber_one : fiber (fun _ => (1 : K →L[ℂ] K)) = (1 : Joint J K →L[ℂ] Joint J K) := by
  ext Ψ j
  rfl

theorem star_fiber (F : J → K →L[ℂ] K) : star (fiber F) = fiber fun j => star (F j) := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [PiLp.inner_apply, fiber_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

omit [CompleteSpace K] in
/-- A controlled family has norm at most the largest norm of its branches. -/
theorem norm_fiber_le (F : J → K →L[ℂ] K) {c : ℝ} (hc : 0 ≤ c) (hF : ∀ j, ‖F j‖ ≤ c) :
    ‖fiber F‖ ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun Ψ => ?_
  have h : ‖fiber F Ψ‖ ^ 2 ≤ (c * ‖Ψ‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [fiber_apply, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ((F j).le_of_opNorm_le (hF j) _) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))
    two_ne_zero).1 h

/-- A family of isometries acts isometrically. -/
theorem norm_fiber_apply_of_isometry (F : J → K →L[ℂ] K) (hF : ∀ j, star (F j) * F j = 1)
    (Ψ : Joint J K) : ‖fiber F Ψ‖ = ‖Ψ‖ := by
  have hiso : ∀ j v, ‖F j v‖ = ‖v‖ := by
    intro j
    rw [ContinuousLinearMap.norm_map_iff_adjoint_comp_self, ← ContinuousLinearMap.star_eq_adjoint]
    exact hF j
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  simp only [fiber_apply, hiso]

/-! ### Operators on the hidden-input register -/

/-- `T ⊗ 1_K` for a matrix `T` on `ℂ^J`: `(kernel T Ψ) j = Σ_{j'} T j j' Ψ j'`. -/
def kernel (T : Matrix J J ℂ) : Joint J K →L[ℂ] Joint J K :=
  mk fun j => ∑ j', T j j' • proj j'

omit [CompleteSpace K] in
@[simp] theorem kernel_apply (T : Matrix J J ℂ) (Ψ : Joint J K) (j : J) :
    kernel T Ψ j = ∑ j', T j j' • Ψ j' := by
  rw [kernel, mk_apply, _root_.sum_apply]
  simp

omit [CompleteSpace K] in
theorem kernel_mul (T T' : Matrix J J ℂ) :
    kernel T * kernel T' = (kernel (T * T') : Joint J K →L[ℂ] Joint J K) := by
  ext Ψ j
  simp only [mul_apply_eq_comp, kernel_apply, Matrix.mul_apply, Finset.smul_sum,
    smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

omit [CompleteSpace K] in
@[simp] theorem kernel_one [DecidableEq J] :
    kernel (1 : Matrix J J ℂ) = (1 : Joint J K →L[ℂ] Joint J K) := by
  ext Ψ j
  simp [Matrix.one_apply, ite_smul]

theorem star_kernel (T : Matrix J J ℂ) :
    star (kernel T) = (kernel Tᴴ : Joint J K →L[ℂ] Joint J K) := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [PiLp.inner_apply, kernel_apply, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  simp

omit [CompleteSpace K] in
/-- `‖T ⊗ 1_K‖ ≤ ‖T‖` for the `L²` operator norm of the matrix. -/
theorem norm_kernel_le [DecidableEq J] (T : Matrix J J ℂ) :
    ‖(kernel T : Joint J K →L[ℂ] Joint J K)‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun Ψ => ?_
  have h : ‖kernel T Ψ‖ ^ 2 ≤ (‖T‖ * ‖Ψ‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2]
    simp only [kernel_apply]
    exact Helpers.Joint.sum_norm_sq_mulVec_le T fun j => Ψ j
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

omit [CompleteSpace K] in
/-- Operators on the hidden register commute with workspace operators that do
not depend on the hidden input. -/
theorem kernel_comm_fiber_const (T : Matrix J J ℂ) (A : K →L[ℂ] K) :
    kernel T * fiber (fun _ => A) = fiber (fun _ => A) * kernel T := by
  ext Ψ j
  simp [map_sum, map_smul]

omit [CompleteSpace K] in
/-- A diagonal matrix on the hidden register is an input-controlled scalar. -/
theorem kernel_diagonal [DecidableEq J] (d : J → ℂ) :
    (kernel (Matrix.diagonal d) : Joint J K →L[ℂ] Joint J K) = fiber fun j => d j • 1 := by
  ext Ψ j
  simp [Matrix.diagonal_apply, ite_smul]

/-- `kernel` as a monoid homomorphism. -/
def kernelHom [DecidableEq J] : Matrix J J ℂ →* (Joint J K →L[ℂ] Joint J K) where
  toFun := kernel
  map_one' := kernel_one
  map_mul' T T' := (kernel_mul T T').symm

/-! ### Registers of `n` hidden positions -/

variable {n m : ℕ}

/-- The matrix `A` on hidden register `k`, identity on the other registers and
on the workspace: `(onReg k A Ψ) j = Σ_b A (j k) b Ψ (update j k b)`. -/
def onReg (k : Fin n) (A : Matrix (Fin m) (Fin m) ℂ) :
    Joint (Fin n → Fin m) K →L[ℂ] Joint (Fin n → Fin m) K :=
  mk fun j => ∑ b, A (j k) b • proj (Function.update j k b)

omit [CompleteSpace K] in
@[simp] theorem onReg_apply (k : Fin n) (A : Matrix (Fin m) (Fin m) ℂ)
    (Ψ : Joint (Fin n → Fin m) K) (j : Fin n → Fin m) :
    onReg k A Ψ j = ∑ b, A (j k) b • Ψ (Function.update j k b) := by
  rw [onReg, mk_apply, _root_.sum_apply]
  simp

omit [CompleteSpace K] in
/-- `A` on register `k` is the tensor product with `A` in factor `k` and `1`
elsewhere. -/
theorem onReg_eq_kernel (k : Fin n) (A : Matrix (Fin m) (Fin m) ℂ) :
    (onReg k A : Joint (Fin n → Fin m) K →L[ℂ] _) =
      kernel (Helpers.Joint.prodMat (Function.update 1 k A)) := by
  ext Ψ j
  rw [onReg_apply, kernel_apply, Helpers.Joint.sum_prodMat_update_smul k A (fun j => Ψ j) j]

theorem update_one_mul_update_one (k : Fin n) (A B : Matrix (Fin m) (Fin m) ℂ) :
    Function.update (1 : Fin n → Matrix (Fin m) (Fin m) ℂ) k A *
      Function.update (1 : Fin n → Matrix (Fin m) (Fin m) ℂ) k B =
      Function.update (1 : Fin n → Matrix (Fin m) (Fin m) ℂ) k (A * B) := by
  funext l
  by_cases h : l = k
  · subst h
    simp
  · simp [Function.update_of_ne h]

omit [CompleteSpace K] in
theorem onReg_mul (k : Fin n) (A B : Matrix (Fin m) (Fin m) ℂ) :
    onReg k A * onReg k B = (onReg k (A * B) : Joint (Fin n → Fin m) K →L[ℂ] _) := by
  simp only [onReg_eq_kernel, kernel_mul, Helpers.Joint.prodMat_mul, update_one_mul_update_one]

omit [CompleteSpace K] in
@[simp] theorem onReg_one (k : Fin n) :
    onReg k (1 : Matrix (Fin m) (Fin m) ℂ) = (1 : Joint (Fin n → Fin m) K →L[ℂ] _) := by
  rw [onReg_eq_kernel]
  have h : Function.update (1 : Fin n → Matrix (Fin m) (Fin m) ℂ) k 1 = 1 := by
    simp
  rw [h, Helpers.Joint.prodMat_one, kernel_one]

theorem star_onReg (k : Fin n) (A : Matrix (Fin m) (Fin m) ℂ) :
    star (onReg k A) = (onReg k Aᴴ : Joint (Fin n → Fin m) K →L[ℂ] _) := by
  rw [onReg_eq_kernel, onReg_eq_kernel, star_kernel, Helpers.Joint.prodMat_conjTranspose]
  congr 2
  funext l
  by_cases h : l = k
  · subst h
    simp
  · simp [Function.update_of_ne h]

omit [CompleteSpace K] in
/-- `‖A ⊗ 1‖ ≤ ‖A‖` on one hidden register. -/
theorem norm_onReg_le (k : Fin n) (A : Matrix (Fin m) (Fin m) ℂ) :
    ‖(onReg k A : Joint (Fin n → Fin m) K →L[ℂ] _)‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun Ψ => ?_
  have h : ‖onReg k A Ψ‖ ^ 2 ≤ (‖A‖ * ‖Ψ‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2]
    simp only [onReg_apply]
    exact Helpers.Joint.sum_norm_sq_onReg_le k A fun j => Ψ j
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

omit [CompleteSpace K] in
/-- Operators on different hidden registers commute. -/
theorem onReg_comm {k l : Fin n} (hkl : k ≠ l) (A B : Matrix (Fin m) (Fin m) ℂ) :
    onReg k A * onReg l B = (onReg l B * onReg k A : Joint (Fin n → Fin m) K →L[ℂ] _) := by
  simp only [onReg_eq_kernel, kernel_mul, Helpers.Joint.prodMat_mul]
  congr 2
  funext i
  by_cases hik : i = k
  · subst hik
    simp [Function.update_of_ne hkl]
  · by_cases hil : i = l
    · subst hil
      simp [Function.update_of_ne hik]
    · simp [Function.update_of_ne hik, Function.update_of_ne hil]

omit [CompleteSpace K] in
theorem onReg_comm_fiber_const (k : Fin n) (A : Matrix (Fin m) (Fin m) ℂ) (U : K →L[ℂ] K) :
    onReg k A * fiber (fun _ => U) = fiber (fun _ => U) * onReg k A := by
  ext Ψ j
  simp [map_sum, map_smul]

omit [CompleteSpace K] in
/-- A diagonal matrix on register `k` multiplies the branch `j` by `d (j k)`. -/
theorem onReg_diagonal (k : Fin n) (d : Fin m → ℂ) :
    (onReg k (Matrix.diagonal d) : Joint (Fin n → Fin m) K →L[ℂ] _) =
      fiber fun j => d (j k) • 1 := by
  ext Ψ j
  simp [Matrix.diagonal_apply, ite_smul]

/-- The tensor power `A^{⊗ n}` on all hidden registers:
`(tensorPow A Ψ) j = Σ_{j'} (Π_k A (j k) (j' k)) Ψ j'`. -/
def tensorPow (A : Matrix (Fin m) (Fin m) ℂ) :
    Joint (Fin n → Fin m) K →L[ℂ] Joint (Fin n → Fin m) K :=
  kernel (Matrix.of fun j j' => ∏ k, A (j k) (j' k))

omit [CompleteSpace K] in
theorem tensorPow_apply (A : Matrix (Fin m) (Fin m) ℂ) (Ψ : Joint (Fin n → Fin m) K)
    (j : Fin n → Fin m) :
    tensorPow A Ψ j = ∑ j', (∏ k, A (j k) (j' k)) • Ψ j' := by
  rw [tensorPow, kernel_apply]
  rfl

omit [CompleteSpace K] in
theorem tensorPow_eq_kernel (A : Matrix (Fin m) (Fin m) ℂ) :
    (tensorPow A : Joint (Fin n → Fin m) K →L[ℂ] _) =
      kernel (Helpers.Joint.prodMat fun _ => A) := rfl

omit [CompleteSpace K] in
/-- `A^{⊗ n}` is the product of its single-register factors (in any order,
by `onReg_comm`). -/
theorem tensorPow_eq_prod_onReg (A : Matrix (Fin m) (Fin m) ℂ) :
    (tensorPow A : Joint (Fin n → Fin m) K →L[ℂ] _) = (List.ofFn fun k => onReg k A).prod := by
  have h : (List.ofFn fun k => (onReg k A : Joint (Fin n → Fin m) K →L[ℂ] _)) =
      (List.ofFn fun k => Function.update (1 : Fin n → Matrix (Fin m) (Fin m) ℂ) k A).map
        ((kernelHom (K := K)).comp Helpers.Joint.prodMatHom) := by
    rw [List.map_ofFn]
    congr 1
    funext k
    exact onReg_eq_kernel k A
  rw [h, ← map_list_prod, Helpers.Joint.ofFn_update_one_prod]
  rfl

omit [CompleteSpace K] in
theorem tensorPow_mul (A B : Matrix (Fin m) (Fin m) ℂ) :
    tensorPow A * tensorPow B = (tensorPow (A * B) : Joint (Fin n → Fin m) K →L[ℂ] _) := by
  rw [tensorPow_eq_kernel, tensorPow_eq_kernel, kernel_mul, Helpers.Joint.prodMat_mul]
  rfl

omit [CompleteSpace K] in
@[simp] theorem tensorPow_one :
    tensorPow (1 : Matrix (Fin m) (Fin m) ℂ) = (1 : Joint (Fin n → Fin m) K →L[ℂ] _) := by
  rw [tensorPow_eq_kernel]
  exact (congrArg kernel Helpers.Joint.prodMat_one).trans kernel_one

theorem star_tensorPow (A : Matrix (Fin m) (Fin m) ℂ) :
    star (tensorPow A) = (tensorPow Aᴴ : Joint (Fin n → Fin m) K →L[ℂ] _) := by
  rw [tensorPow_eq_kernel, star_kernel, Helpers.Joint.prodMat_conjTranspose]
  rfl

omit [CompleteSpace K] in
/-- `‖A^{⊗ n} ⊗ 1‖ ≤ ‖A‖ⁿ`. -/
theorem norm_tensorPow_le (A : Matrix (Fin m) (Fin m) ℂ) :
    ‖(tensorPow A : Joint (Fin n → Fin m) K →L[ℂ] _)‖ ≤ ‖A‖ ^ n := by
  have hlist : ∀ l : List (Joint (Fin n → Fin m) K →L[ℂ] Joint (Fin n → Fin m) K),
      (∀ x ∈ l, ‖x‖ ≤ ‖A‖) → ‖l.prod‖ ≤ ‖A‖ ^ l.length := by
    intro l hl
    induction l with
    | nil =>
      simp only [List.prod_nil, List.length_nil, pow_zero]
      exact ContinuousLinearMap.norm_id_le
    | cons a l ih =>
      rw [List.prod_cons, List.length_cons, pow_succ']
      calc ‖a * l.prod‖ ≤ ‖a‖ * ‖l.prod‖ := norm_mul_le a l.prod
        _ ≤ ‖A‖ * ‖A‖ ^ l.length :=
          mul_le_mul (hl a (by simp)) (ih fun x hx => hl x (by simp [hx]))
            (norm_nonneg l.prod) (norm_nonneg A)
  rw [tensorPow_eq_prod_onReg]
  have h := hlist (List.ofFn fun k => (onReg k A : Joint (Fin n → Fin m) K →L[ℂ] _))
    fun x hx => by
      obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
      exact norm_onReg_le k A
  rwa [List.length_ofFn] at h

omit [CompleteSpace K] in
/-- The weight commutes with every workspace operator independent of the
hidden input, in particular with every fixed gate of an algorithm. -/
theorem tensorPow_comm_fiber_const (A : Matrix (Fin m) (Fin m) ℂ) (U : K →L[ℂ] K) :
    tensorPow A * fiber (fun _ => U) =
      (fiber (fun _ => U) * tensorPow A : Joint (Fin n → Fin m) K →L[ℂ] _) := by
  exact kernel_comm_fiber_const _ U

omit [CompleteSpace K] in
/-- A diagonal tensor power is the input-controlled scalar `Π_k d (j k)`. -/
theorem tensorPow_diagonal (d : Fin m → ℂ) :
    (tensorPow (Matrix.diagonal d) : Joint (Fin n → Fin m) K →L[ℂ] _) =
      fiber fun j => (∏ k, d (j k)) • 1 := by
  have h := Helpers.Joint.prodMat_diagonal (n := n) fun _ => d
  rw [tensorPow_eq_kernel, h, kernel_diagonal]

omit [CompleteSpace K] in
/-- Conjugating a single-register operator by an invertible tensor power only
conjugates that register: `W (A ⊗ 1) W⁻¹ = (w A w⁻¹) ⊗ 1`. -/
theorem tensorPow_mul_onReg_mul_tensorPow_inv (w : Matrix (Fin m) (Fin m) ℂ) (hw : IsUnit w)
    (k : Fin n) (A : Matrix (Fin m) (Fin m) ℂ) :
    tensorPow w * onReg k A * tensorPow w⁻¹ =
      (onReg k (w * A * w⁻¹) : Joint (Fin n → Fin m) K →L[ℂ] _) := by
  have hw' : w * w⁻¹ = 1 := Matrix.mul_nonsing_inv w ((Matrix.isUnit_iff_isUnit_det w).1 hw)
  simp only [tensorPow_eq_kernel, onReg_eq_kernel, kernel_mul, Helpers.Joint.prodMat_mul]
  congr 2
  funext l
  by_cases h : l = k
  · subst h
    simp
  · simp [Function.update_of_ne h, hw']

omit [CompleteSpace K] in
/-- The weight acts on the input-independent joint state through the row sums
of `w`: `(W (Σ_j |j⟩ ⊗ φ)) j = (Π_k Σ_b w (j k) b) φ`. -/
theorem tensorPow_const (w : Matrix (Fin m) (Fin m) ℂ) (φ : K) (j : Fin n → Fin m) :
    (tensorPow w (const φ) : Joint (Fin n → Fin m) K) j = (∏ k, ∑ b, w (j k) b) • φ := by
  rw [tensorPow_apply, Fintype.prod_sum, Finset.sum_smul]
  rfl

end Joint

end

end SparseLowerBounds
end
