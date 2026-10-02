import SparseHamiltonian.OracleStability

/-!
# Reversible finite-table lookup oracles

A table lookup is the concrete basis permutation `(a,z) ↦ (a,z + f x a)`.
Its lift is a genuine unitary on a finite complex Hilbert space. Adding
spectator registers only reindexes this same lookup. No query-cost claim
about arbitrary input-dependent unitaries is made here.
-/

namespace SparseHamiltonian.LookupOracle

noncomputable section
open ContinuousLinearMap
open scoped InnerProduct

section Permutations
variable {X A Z : Type*} [AddCommGroup Z]

/-- Reversible addition lookup, with input instance `x` and address `a`. -/
def basisEquiv (f : X → A → Z) (x : X) : A × Z ≃ A × Z where
  toFun v := (v.1, v.2 + f x v.1)
  invFun v := (v.1, v.2 - f x v.1)
  left_inv v := by simp
  right_inv v := by simp

@[simp] theorem basisEquiv_apply (f : X → A → Z) (x : X) (a : A) (z : Z) :
    basisEquiv f x (a, z) = (a, z + f x a) := rfl

@[simp] theorem basisEquiv_symm_apply (f : X → A → Z) (x : X) (a : A) (z : Z) :
    (basisEquiv f x).symm (a, z) = (a, z - f x a) := rfl

/-- The inverse lookup is addition of the negated table. -/
theorem basisEquiv_symm (f : X → A → Z) (x : X) :
    (basisEquiv f x).symm = basisEquiv (fun x a => -f x a) x := by
  apply Equiv.ext
  intro v
  change (v.1, v.2 - f x v.1) = (v.1, v.2 + -f x v.1)
  simp only [sub_eq_add_neg]

/-- Label and workspace registers are spectators of one lookup. -/
def spectatorEquiv (S : Type*) (f : X → A → Z) (x : X) :
    S × (A × Z) ≃ S × (A × Z) :=
  Equiv.prodCongr (Equiv.refl S) (basisEquiv f x)

@[simp] theorem spectatorEquiv_apply (S : Type*) (f : X → A → Z)
    (x : X) (s : S) (a : A) (z : Z) :
    spectatorEquiv S f x (s, a, z) = (s, a, z + f x a) := rfl

@[simp] theorem spectatorEquiv_symm_apply (S : Type*) (f : X → A → Z)
    (x : X) (s : S) (a : A) (z : Z) :
    (spectatorEquiv S f x).symm (s, a, z) = (s, a, z - f x a) := rfl

end Permutations

section Hilbert
variable {B C E : Type*} [Fintype B] [Fintype C] [Fintype E]

/-- The Hilbert-space unitary induced by a finite basis permutation. -/
def permutationUnitary (e : B ≃ C) : EuclideanSpace ℂ B ≃ₗᵢ[ℂ] EuclideanSpace ℂ C :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

@[simp] theorem permutationUnitary_apply (e : B ≃ C) (v : EuclideanSpace ℂ B) (c : C) :
    permutationUnitary e v c = v (e.symm c) := rfl

@[simp] theorem permutationUnitary_single [DecidableEq B] [DecidableEq C]
    (e : B ≃ C) (b : B) (z : ℂ) :
    permutationUnitary e (EuclideanSpace.single b z) = EuclideanSpace.single (e b) z :=
  LinearIsometryEquiv.piLpCongrLeft_single e b z

/-- Sequential classical reversible operations lift in the same order. -/
theorem permutationUnitary_trans (e : B ≃ C) (g : C ≃ E) :
    permutationUnitary (e.trans g) = (permutationUnitary e).trans (permutationUnitary g) := by
  ext v i
  rfl

@[simp] theorem permutationUnitary_symm (e : B ≃ C) :
    permutationUnitary e.symm = (permutationUnitary e).symm := by
  exact (LinearIsometryEquiv.piLpCongrLeft_symm e).symm

/-- The adjoint of a basis permutation is the inverse basis permutation. -/
theorem permutationUnitary_adjoint (e : B ≃ C) :
    ((permutationUnitary e).toLinearIsometry.toContinuousLinearMap)† =
      (permutationUnitary e).symm.toLinearIsometry.toContinuousLinearMap := by
  have h := (permutationUnitary e).toLinearIsometry.adjoint_comp_self
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := (permutationUnitary e).surjective v
  have hw := congrArg (fun F : EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B => F w) h
  change (((permutationUnitary e).toLinearIsometry.toContinuousLinearMap)†)
    ((permutationUnitary e) w) = w at hw
  change (((permutationUnitary e).toLinearIsometry.toContinuousLinearMap)†)
    ((permutationUnitary e) w) = (permutationUnitary e).symm ((permutationUnitary e) w)
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact hw

/-- Both unitary identities hold for the actual permutation operator. -/
theorem permutationUnitary_unitary (e : B ≃ B) :
    let U := (permutationUnitary e).toLinearIsometry.toContinuousLinearMap
    U† ∘L U = 1 ∧ U ∘L U† = 1 := by
  dsimp
  constructor
  · exact (permutationUnitary e).toLinearIsometry.adjoint_comp_self
  · rw [permutationUnitary_adjoint]
    apply ContinuousLinearMap.ext
    intro v
    exact (permutationUnitary e).apply_symm_apply v

end Hilbert

section LookupUnitary
variable {X A Z S : Type*} [Fintype A] [Fintype Z] [Fintype S] [AddCommGroup Z]

/-- The actual complex unitary for a finite reversible lookup. -/
def unitary (f : X → A → Z) (x : X) :
    EuclideanSpace ℂ (A × Z) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × Z) :=
  permutationUnitary (basisEquiv f x)

@[simp] theorem unitary_apply (f : X → A → Z) (x : X)
    (v : EuclideanSpace ℂ (A × Z)) (a : A) (z : Z) :
    unitary f x v (a, z) = v (a, z - f x a) := rfl

/-- A superposition in arbitrary spectator registers undergoes the same lookup. -/
theorem spectator_unitary_apply (f : X → A → Z) (x : X)
    (v : EuclideanSpace ℂ (S × (A × Z))) (s : S) (a : A) (z : Z) :
    permutationUnitary (spectatorEquiv S f x) v (s, a, z) = v (s, a, z - f x a) := rfl

end LookupUnitary
end
end SparseHamiltonian.LookupOracle
