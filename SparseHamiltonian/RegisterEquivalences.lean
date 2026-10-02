import SparseHamiltonian.QueryClockStep

/-!
# Fixed changes of finite Hilbert register layout

These equivalences flatten Hilbert direct sums into computational basis registers.
Their definitions depend only on the register types, never on an oracle table.
The coordinate lemmas make this distinction explicit when transporting a query
program through a fixed layout change.
-/

namespace SparseHamiltonian.RegisterEquivalences

noncomputable section
open ContinuousLinearMap

section Dependent
variable {ι : Type*} [Fintype ι] (κ : ι → Type*) [∀ i, Fintype (κ i)]

/-- Flatten a dependent finite Hilbert direct sum into its disjoint-union basis. -/
def dependentFlatten :
    PiLp 2 (fun i => EuclideanSpace ℂ (κ i)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Sigma κ) :=
  (LinearIsometryEquiv.piLpCurry ℂ 2 (fun i (_ : κ i) => ℂ)).symm

@[simp] theorem dependentFlatten_apply
    (v : PiLp 2 (fun i => EuclideanSpace ℂ (κ i))) (i : ι) (j : κ i) :
    dependentFlatten κ v ⟨i, j⟩ = v i j := rfl

@[simp] theorem dependentFlatten_symm_apply
    (v : EuclideanSpace ℂ (Sigma κ)) (i : ι) (j : κ i) :
    (dependentFlatten κ).symm v i j = v ⟨i, j⟩ := rfl

/-- The flattened block diagonal operator acts within one branch basis. -/
theorem dependentFlatten_diagonal_apply
    (U : ∀ i, EuclideanSpace ℂ (κ i) →L[ℂ] EuclideanSpace ℂ (κ i))
    (v : EuclideanSpace ℂ (Sigma κ)) (i : ι) (j : κ i) :
    dependentFlatten κ (WeightedClock.diagonal U ((dependentFlatten κ).symm v)) ⟨i, j⟩ =
      U i ((dependentFlatten κ).symm v i) j := rfl

end Dependent

section Product
variable (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]

/-- Flatten ordinary branch and payload registers into a Cartesian basis. -/
def productFlatten :
    PiLp 2 (fun _ : A => EuclideanSpace ℂ B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B) :=
  (dependentFlatten (fun _ : A => B)).trans
    (LookupOracle.permutationUnitary (Equiv.sigmaEquivProd A B))

@[simp] theorem productFlatten_apply
    (v : PiLp 2 (fun _ : A => EuclideanSpace ℂ B)) (a : A) (b : B) :
    productFlatten A B v (a, b) = v a b := rfl

@[simp] theorem productFlatten_symm_apply
    (v : EuclideanSpace ℂ (A × B)) (a : A) (b : B) :
    (productFlatten A B).symm v a b = v (a, b) := rfl

/-- Curry a left-associated workspace, retaining the branch register separately. -/
def workspaceCurry :
    EuclideanSpace ℂ ((A × B) × C) ≃ₗᵢ[ℂ]
      PiLp 2 (fun _ : A => EuclideanSpace ℂ (B × C)) :=
  (LookupOracle.permutationUnitary (Equiv.prodAssoc A B C)).trans
    (productFlatten A (B × C)).symm

@[simp] theorem workspaceCurry_apply
    (v : EuclideanSpace ℂ ((A × B) × C)) (a : A) (b : B) (c : C) :
    workspaceCurry A B C v a (b, c) = v ((a, b), c) := rfl

@[simp] theorem workspaceCurry_symm_apply
    (v : PiLp 2 (fun _ : A => EuclideanSpace ℂ (B × C))) (a : A) (b : B) (c : C) :
    (workspaceCurry A B C).symm v ((a, b), c) = v a (b, c) := rfl

/-- The usual Cartesian flattening intertwines direct-sum branch operators. -/
theorem productFlatten_diagonal_apply
    (U : A → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (v : EuclideanSpace ℂ (A × B)) (a : A) (b : B) :
    productFlatten A B (WeightedClock.diagonal U ((productFlatten A B).symm v)) (a, b) =
      U a ((productFlatten A B).symm v a) b := rfl

end Product

section Sum
variable (A B : Type*) [Fintype A] [Fintype B]

/-- Flatten the public and private Hilbert product into a tagged basis. -/
def sumFlatten :
    WithLp 2 (EuclideanSpace ℂ A × EuclideanSpace ℂ B) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (A ⊕ B) :=
  (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℂ) 2 (fun _ : A ⊕ B => ℂ)).symm

@[simp] theorem sumFlatten_inl
    (v : WithLp 2 (EuclideanSpace ℂ A × EuclideanSpace ℂ B)) (a : A) :
    sumFlatten A B v (.inl a) = v.fst a := rfl

@[simp] theorem sumFlatten_inr
    (v : WithLp 2 (EuclideanSpace ℂ A × EuclideanSpace ℂ B)) (b : B) :
    sumFlatten A B v (.inr b) = v.snd b := rfl

@[simp] theorem sumFlatten_symm_fst
    (v : EuclideanSpace ℂ (A ⊕ B)) (a : A) :
    ((sumFlatten A B).symm v).fst a = v (.inl a) := rfl

@[simp] theorem sumFlatten_symm_snd
    (v : EuclideanSpace ℂ (A ⊕ B)) (b : B) :
    ((sumFlatten A B).symm v).snd b = v (.inr b) := rfl

end Sum

end
end SparseHamiltonian.RegisterEquivalences
