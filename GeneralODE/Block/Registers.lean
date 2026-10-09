import SparseHamiltonian.LookupFromBasisOracle
import SparseHamiltonian.OracleTransport

/-!
# Registers and factor actions

All workspaces are Euclidean spaces over finite index types.  An operator acts
on one tensor factor through a fixed reindexing `ι ≃ S × B`: it acts on the `B`
coordinate with `S` as a spectator.  These factor actions are star-algebra
homomorphisms, so they lift whole programs and preserve unitarity; they send
computational basis states to basis states whenever the factor operator does.
We also define the product states `v ⊗ φ`, their adjoints, and blocks
`⟨φ_out| U |φ_in⟩` of operators on `σ × α`.
-/

namespace SparseHamiltonian.GeneralODE.Registers

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators ComplexConjugate

/-- Unitarity is preserved by star-algebra homomorphisms. -/
theorem isUnitary_map {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (φ : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)) {U : H →L[ℂ] H} (hU : IsUnitary U) :
    IsUnitary (φ U) := by
  constructor
  · rw [← map_star, ← map_mul, hU.1, map_one]
  · rw [← map_star, ← map_mul, hU.2, map_one]

section Diagonal

variable (S : Type*) [Fintype S]
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The block-diagonal lift `U ↦ I_S ⊗ U` on a finite Hilbert sum. -/
def diagHom : (V →L[ℂ] V) →⋆ₐ[ℂ] (PiLp 2 (fun _ : S => V) →L[ℂ] PiLp 2 (fun _ : S => V)) where
  toFun U := WeightedClock.diagonal (fun _ => U)
  map_one' := WeightedClock.diagonal_one
  map_mul' U W := (WeightedClock.diagonal_comp (fun _ => U) (fun _ => W)).symm
  map_zero' := by ext x i; rfl
  map_add' U W := by ext x i; simp [WeightedClock.diagonal_apply]
  commutes' c := by
    ext x i
    simp [WeightedClock.diagonal_apply, Algebra.algebraMap_eq_smul_one]
  map_star' U := by
    show WeightedClock.diagonal (fun _ : S => star U) =
      star (WeightedClock.diagonal (fun _ : S => U))
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
      WeightedClock.diagonal_adjoint]

@[simp] theorem diagHom_apply_apply (U : V →L[ℂ] V) (x : PiLp 2 (fun _ : S => V)) (i : S) :
    diagHom S V U x i = U (x i) := rfl

end Diagonal

section Factor

variable {ι S B : Type*} [Fintype ι] [Fintype S] [Fintype B]

/-- Spectator lift `U ↦ I_S ⊗ U` on `S × B`. -/
def specHom (S B : Type*) [Fintype S] [Fintype B] :
    (EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) →⋆ₐ[ℂ]
      (EuclideanSpace ℂ (S × B) →L[ℂ] EuclideanSpace ℂ (S × B)) :=
  (RegisterEquivalences.productFlatten S B).conjStarAlgEquiv.toStarAlgHom.comp
    (diagHom S (EuclideanSpace ℂ B))

theorem specHom_eq (U : EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) :
    specHom S B U = LookupFromBasisOracle.spectator (S := S) U := rfl

theorem spectator_apply (U : EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (Z : EuclideanSpace ℂ (S × B)) (a : S) (b : B) :
    LookupFromBasisOracle.spectator (S := S) U Z (a, b) =
      U (WithLp.toLp 2 (fun b' => Z (a, b'))) b := by
  have h : (RegisterEquivalences.productFlatten S B).symm Z a =
      WithLp.toLp 2 (fun b' => Z (a, b')) := by
    ext b'; rfl
  change U ((RegisterEquivalences.productFlatten S B).symm Z a) b = _
  rw [h]

theorem permutationUnitary_symm_apply (e : ι ≃ S × B) (Y : EuclideanSpace ℂ (S × B)) (i : ι) :
    (LookupOracle.permutationUnitary e).symm Y i = Y (e i) := by
  change (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm Y i = _
  rw [LinearIsometryEquiv.piLpCongrLeft_symm]
  change LookupOracle.permutationUnitary e.symm Y i = _
  rw [LookupOracle.permutationUnitary_apply, Equiv.symm_symm]

/-- Action on the `B` factor of a reindexed register `ι ≃ S × B`. -/
def onFactor (e : ι ≃ S × B) :
    (EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) →⋆ₐ[ℂ]
      (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
  (LookupOracle.permutationUnitary e).symm.conjStarAlgEquiv.toStarAlgHom.comp (specHom S B)

theorem onFactor_apply (e : ι ≃ S × B) (U : EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (w : EuclideanSpace ℂ ι) (i : ι) :
    onFactor e U w i = U (WithLp.toLp 2 (fun b => w (e.symm ((e i).1, b)))) (e i).2 := by
  change (LookupOracle.permutationUnitary e).symm
    (LookupFromBasisOracle.spectator (S := S) U (LookupOracle.permutationUnitary e w)) i = _
  rw [permutationUnitary_symm_apply, spectator_apply]
  rfl

theorem onFactor_unitary (e : ι ≃ S × B) {U : EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B}
    (hU : IsUnitary U) : IsUnitary (onFactor e U) :=
  isUnitary_map (onFactor e) hU

/-- Basis-state transitions survive factor actions. -/
theorem onFactor_single [DecidableEq ι] [DecidableEq S] [DecidableEq B] (e : ι ≃ S × B)
    (U : EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (b c : B) (z : ℂ)
    (hU : U (EuclideanSpace.single b z) = EuclideanSpace.single c z) (s : S) :
    onFactor e U (EuclideanSpace.single (e.symm (s, b)) z) =
      EuclideanSpace.single (e.symm (s, c)) z := by
  change (LookupOracle.permutationUnitary e).symm
      (LookupFromBasisOracle.spectator (S := S) U
        (LookupOracle.permutationUnitary e (EuclideanSpace.single (e.symm (s, b)) z))) = _
  rw [LookupOracle.permutationUnitary_single, Equiv.apply_symm_apply,
    LookupFromBasisOracle.spectator_single U b c z hU s]
  change (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm _ = _
  rw [LinearIsometryEquiv.piLpCongrLeft_symm]
  exact LookupOracle.permutationUnitary_single e.symm (s, c) z

end Factor

section Kets

variable {σ α : Type*} [Fintype σ] [Fintype α]

/-- Product state `v ⊗ φ`. -/
def ketR (φ : EuclideanSpace ℂ α) : EuclideanSpace ℂ σ →L[ℂ] EuclideanSpace ℂ (σ × α) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun p => v p.1 * φ p.2)
      map_add' := by intro v w; ext p; simp [add_mul]
      map_smul' := by intro c v; ext p; simp [mul_assoc] }

@[simp] theorem ketR_apply (φ : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ σ) (p : σ × α) :
    ketR φ v p = v p.1 * φ p.2 := rfl

/-- Partial inner product with `φ` on the right factor. -/
def braR (φ : EuclideanSpace ℂ α) : EuclideanSpace ℂ (σ × α) →L[ℂ] EuclideanSpace ℂ σ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 (fun s => ∑ a, conj (φ a) * w (s, a))
      map_add' := by intro v w; ext s; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c v; ext s
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring) }

@[simp] theorem braR_apply (φ : EuclideanSpace ℂ α) (w : EuclideanSpace ℂ (σ × α)) (s : σ) :
    braR φ w s = ∑ a, conj (φ a) * w (s, a) := rfl

theorem ketR_adjoint (φ : EuclideanSpace ℂ α) :
    (ketR (σ := σ) φ)† = braR φ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro w v
  simp only [PiLp.inner_apply, braR_apply, ketR_apply, RCLike.inner_apply, Fintype.sum_prod_type,
    map_sum, map_mul, Complex.conj_conj]
  apply Finset.sum_congr rfl; intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  ring

theorem braR_ketR (φ ψ : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ σ) :
    braR φ (ketR ψ v) = (inner ℂ φ ψ) • v := by
  ext s
  simp only [braR_apply, ketR_apply, PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply,
    RCLike.inner_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro a _
  ring

theorem ketR_isometry (φ : EuclideanSpace ℂ α) (hφ : ‖φ‖ = 1) :
    (ketR (σ := σ) φ)† ∘L ketR φ = 1 := by
  rw [ketR_adjoint]
  ext v s
  rw [comp_apply, braR_ketR, inner_self_eq_norm_sq_to_K, hφ]
  simp

/-- Block `⟨φ_out| U |φ_in⟩` on the system factor. -/
def blk (φin φout : EuclideanSpace ℂ α)
    (U : EuclideanSpace ℂ (σ × α) →L[ℂ] EuclideanSpace ℂ (σ × α)) :
    EuclideanSpace ℂ σ →L[ℂ] EuclideanSpace ℂ σ :=
  braR φout ∘L U ∘L ketR φin

/-- An operator with `A† A = 1` has norm at most one. -/
theorem norm_le_one_of_isometry {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] K) (hA : A† ∘L A = 1) : ‖A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [(ContinuousLinearMap.norm_map_iff_adjoint_comp_self A).mpr hA x, one_mul]

theorem norm_unitary_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : H →L[ℂ] H) (hU : IsUnitary U) : ‖U‖ ≤ 1 := by
  apply norm_le_one_of_isometry
  have h := hU.1
  rw [ContinuousLinearMap.star_eq_adjoint] at h
  exact h

theorem norm_blk_le (φin φout : EuclideanSpace ℂ α) (hin : ‖φin‖ = 1) (hout : ‖φout‖ = 1)
    (U : EuclideanSpace ℂ (σ × α) →L[ℂ] EuclideanSpace ℂ (σ × α)) (hU : IsUnitary U) :
    ‖blk φin φout U‖ ≤ 1 := by
  have hk : ‖ketR (σ := σ) φin‖ ≤ 1 := norm_le_one_of_isometry _ (ketR_isometry φin hin)
  have hb : ‖braR (σ := σ) φout‖ ≤ 1 := by
    rw [← ketR_adjoint, ContinuousLinearMap.adjoint.norm_map]
    exact norm_le_one_of_isometry _ (ketR_isometry φout hout)
  have hu := norm_unitary_le U hU
  unfold blk
  calc ‖braR φout ∘L U ∘L ketR φin‖ ≤ ‖braR (σ := σ) φout‖ * (‖U‖ * ‖ketR (σ := σ) φin‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (1 * 1) := by gcongr
    _ = 1 := by norm_num

end Kets

end

end SparseHamiltonian.GeneralODE.Registers
