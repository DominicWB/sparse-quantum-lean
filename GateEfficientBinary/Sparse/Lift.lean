import GateEfficientNative.Native.Private

/-!
# Operators on `ℓ²(ι)` as qubit operators with an untouched payload

An identification `φ : Cfg V ≃ ι` of the configurations of the wires `V` with a finite index
set `ι` turns an operator `A` on `ℓ²(ι) = EuclideanSpace ℂ ι` into a matrix on configurations
(`toMat φ A`), and hence into the operator `matOp (toMat φ A)` on `Reg V R`, which acts on the
qubits and leaves the payload `R` untouched (`qlift φ`). The lift is a unital star algebra
homomorphism (`qlift_comp`, `qlift_one`, `qlift_adjoint`, ...), so it preserves unitarity
(`qlift_isUnitary`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinary

open SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative ContinuousLinearMap
open SparseHamiltonian.OracleCircuit
open scoped InnerProduct ComplexConjugate

noncomputable section

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- Every vector of `ℓ²(ι)` is the sum of its coordinates on the standard basis. -/
theorem euclid_eq_sum (v : EuclideanSpace ℂ ι) :
    v = ∑ d, v d • EuclideanSpace.single d (1 : ℂ) := by
  ext j
  simp [Pi.single_apply]

/-- The configuration-basis matrix of an operator on `ℓ²(ι)`, along `φ : Cfg V ≃ ι`. -/
def toMat (φ : Cfg V ≃ ι) (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    Matrix (Cfg V) (Cfg V) ℂ :=
  fun c c' => A (EuclideanSpace.single (φ c') 1) (φ c)

theorem toMat_comp (φ : Cfg V ≃ ι) (A B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    toMat φ (A ∘L B) = toMat φ A * toMat φ B := by
  funext c c'
  simp only [toMat, comp_apply, Matrix.mul_apply]
  conv_lhs => rw [euclid_eq_sum (B (EuclideanSpace.single (φ c') 1))]
  rw [map_sum]
  simp only [map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  rw [← φ.sum_comp]
  apply Finset.sum_congr rfl
  intro c'' _
  ring

omit [DecidableEq V] [Fintype ι] in
theorem toMat_one (φ : Cfg V ≃ ι) :
    toMat φ (1 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) = 1 := by
  funext c c'
  simp only [toMat, Matrix.one_apply]
  by_cases h : c = c'
  · subst h
    simp
  · simp [h, φ.injective.ne h]

omit [Fintype V] [DecidableEq V] in
theorem toMat_adjoint (φ : Cfg V ≃ ι) (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    toMat φ (A†) = (toMat φ A).conjTranspose := by
  funext c c'
  simp only [toMat, Matrix.conjTranspose_apply]
  have h1 := EuclideanSpace.inner_single_left (φ c) (1 : ℂ) ((A†) (EuclideanSpace.single (φ c') 1))
  rw [adjoint_inner_right, EuclideanSpace.inner_single_right] at h1
  simp only [map_one, one_mul] at h1
  rw [← h1]
  rfl

omit [Fintype V] [DecidableEq V] in
theorem toMat_add (φ : Cfg V ≃ ι) (A B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    toMat φ (A + B) = toMat φ A + toMat φ B := by
  funext c c'
  simp [toMat]

omit [Fintype V] [DecidableEq V] in
theorem toMat_smul (φ : Cfg V ≃ ι) (z : ℂ) (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    toMat φ (z • A) = z • toMat φ A := by
  funext c c'
  simp [toMat]

omit [CompleteSpace R] in
theorem matOp_add (M N : Matrix (Cfg V) (Cfg V) ℂ) :
    matOp (Q := R) (M + N) = matOp M + matOp N := by
  ext ψ b
  simp only [matOp_apply, add_apply, PiLp.add_apply, Matrix.add_apply, add_smul,
    Finset.sum_add_distrib]

omit [CompleteSpace R] in
theorem matOp_smul (z : ℂ) (M : Matrix (Cfg V) (Cfg V) ℂ) :
    matOp (Q := R) (z • M) = z • matOp M := by
  ext ψ b
  simp only [matOp_apply, smul_apply, PiLp.smul_apply, Matrix.smul_apply, smul_eq_mul,
    mul_smul, Finset.smul_sum]

/-- **The qubit lift** of operators on `ℓ²(ι)`, a unital star algebra homomorphism. -/
def qliftHom (φ : Cfg V ≃ ι) :
    (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) →⋆ₐ[ℂ] (Reg V R →L[ℂ] Reg V R) where
  toFun A := matOp (toMat φ A)
  map_one' := by
    rw [toMat_one, matOp_one]
  map_mul' A B := by
    change matOp (toMat φ (A ∘L B)) = matOp (toMat φ A) ∘L matOp (toMat φ B)
    rw [toMat_comp, matOp_mul]
  map_zero' := by
    have : toMat φ (0 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) = 0 := by
      funext c c'
      simp [toMat]
    rw [this]
    ext ψ b
    simp [matOp_apply]
  map_add' A B := by
    rw [toMat_add, matOp_add]
  commutes' z := by
    change matOp (toMat φ (algebraMap ℂ _ z)) = algebraMap ℂ _ z
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, toMat_smul, toMat_one,
      matOp_smul, matOp_one]
  map_star' A := by
    change matOp (Q := R) (toMat φ (A†)) = (matOp (Q := R) (toMat φ A))†
    rw [toMat_adjoint, matOp_adjoint]

/-- The qubit lift of an operator on `ℓ²(ι)`. -/
abbrev qlift (φ : Cfg V ≃ ι) (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    Reg V R →L[ℂ] Reg V R :=
  qliftHom (R := R) φ A

theorem qlift_eq (φ : Cfg V ≃ ι) (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    qlift (R := R) φ A = matOp (toMat φ A) := rfl

theorem qlift_comp (φ : Cfg V ≃ ι) (A B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    qlift (R := R) φ (A ∘L B) = qlift φ A ∘L qlift φ B :=
  map_mul (qliftHom (R := R) φ) A B

theorem qlift_one (φ : Cfg V ≃ ι) :
    qlift (R := R) φ (1 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) = 1 :=
  map_one (qliftHom (R := R) φ)

theorem qlift_adjoint (φ : Cfg V ≃ ι) (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    qlift (R := R) φ (A†) = (qlift φ A)† :=
  map_star (qliftHom (R := R) φ) A

theorem qlift_isUnitary (φ : Cfg V ≃ ι) {A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hA : IsUnitary A) : IsUnitary (qlift (R := R) φ A) := by
  have h1 : star A * A = 1 := hA.1
  have h2 : A * star A = 1 := hA.2
  constructor
  · rw [← map_star (qliftHom (R := R) φ), ← map_mul, h1, map_one]
  · rw [← map_star (qliftHom (R := R) φ), ← map_mul, h2, map_one]

/-- The lift on basis vectors. -/
theorem qlift_bas (φ : Cfg V ≃ ι) (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (c : Cfg V)
    (q : R) : qlift φ A (bas c q) = ∑ c', A (EuclideanSpace.single (φ c) 1) (φ c') • bas c' q := by
  rw [qlift_eq]
  apply PiLp.ext
  intro b'
  rw [matOp_apply, WithLp.ofLp_sum]
  simp only [Finset.sum_apply, bas_apply, PiLp.smul_apply, toMat]
  rw [Finset.sum_eq_single c, Finset.sum_eq_single b']
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

end

end SparseHamiltonian.GateBinary
