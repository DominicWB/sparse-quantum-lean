import GeneralODE.Block.Programs

/-!
# Control-selected maps

`selMap E` acts as `|c⟩ ⊗ v ↦ |c⟩ ⊗ E_c v` on a control register `C`.  It is an
isometry when every `E_c` is, its adjoint is selected by the adjoints, and the
selected maps compose and commute with spectator actions on the target.  In
particular the block of `I_C ⊗ q` between two selected isometries is the
selected family of blocks `E_out,c† q E_in,c`.
-/

namespace SparseHamiltonian.GeneralODE.Registers

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators ComplexConjugate

variable {C α β γ : Type*} [Fintype C] [Fintype α] [Fintype β] [Fintype γ]

/-- Slice of a vector on `C × α` at a control value. -/
def slice (w : EuclideanSpace ℂ (C × α)) (c : C) : EuclideanSpace ℂ α :=
  WithLp.toLp 2 (fun a => w (c, a))

omit [Fintype C] [Fintype α] in
@[simp] theorem slice_apply (w : EuclideanSpace ℂ (C × α)) (c : C) (a : α) :
    slice w c a = w (c, a) := rfl

omit [Fintype C] [Fintype α] in
theorem slice_add (w z : EuclideanSpace ℂ (C × α)) (c : C) :
    slice (w + z) c = slice w c + slice z c := by ext a; rfl

omit [Fintype C] [Fintype α] in
theorem slice_smul (z : ℂ) (w : EuclideanSpace ℂ (C × α)) (c : C) :
    slice (z • w) c = z • slice w c := by ext a; rfl

/-- Inner products split over the control register. -/
theorem inner_eq_sum_slice (w z : EuclideanSpace ℂ (C × α)) :
    inner ℂ w z = ∑ c, inner ℂ (slice w c) (slice z c) := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, slice_apply]

/-- `|c⟩ ⊗ v ↦ |c⟩ ⊗ E_c v`. -/
def selMap (E : C → (EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)) :
    EuclideanSpace ℂ (C × α) →L[ℂ] EuclideanSpace ℂ (C × β) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 (fun p => E p.1 (slice w p.1) p.2)
      map_add' := by intro v w; ext p; simp [slice_add]
      map_smul' := by intro z w; ext p; simp [slice_smul] }

theorem selMap_apply (E : C → (EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β))
    (w : EuclideanSpace ℂ (C × α)) (p : C × β) :
    selMap E w p = E p.1 (slice w p.1) p.2 := rfl

theorem slice_selMap (E : C → (EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β))
    (w : EuclideanSpace ℂ (C × α)) (c : C) :
    slice (selMap E w) c = E c (slice w c) := by
  ext b; rfl

theorem selMap_adjoint (E : C → (EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)) :
    (selMap E)† = selMap (fun c => (E c)†) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro z w
  rw [inner_eq_sum_slice, inner_eq_sum_slice]
  apply Finset.sum_congr rfl
  intro c _
  rw [slice_selMap, slice_selMap, ContinuousLinearMap.adjoint_inner_left]

theorem selMap_comp (E : C → (EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ γ))
    (F : C → (EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)) :
    selMap E ∘L selMap F = selMap (fun c => E c ∘L F c) := by
  ext1 w; ext p
  simp only [comp_apply, selMap_apply, slice_selMap]

theorem selMap_one : selMap (fun _ : C => (1 : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)) = 1 := by
  ext1 w; ext p; rfl

theorem selMap_isometry (E : C → (EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β))
    (hE : ∀ c, (E c)† ∘L E c = 1) : (selMap E)† ∘L selMap E = 1 := by
  rw [selMap_adjoint, selMap_comp]
  simp only [hE]
  exact selMap_one

/-- Spectator action on the target composes inside the selection. -/
theorem specHom_comp_selMap (q : EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ β)
    (E : C → (EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)) :
    specHom C β q ∘L selMap E = selMap (fun c => q ∘L E c) := by
  ext1 w; ext ⟨c, b⟩
  rw [comp_apply, specHom_eq, spectator_apply, selMap_apply]
  rfl

/-- Selected block of a spectator action. -/
theorem selMap_block (q : EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ β)
    (Ein Eout : C → (EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)) :
    (selMap Eout)† ∘L specHom C β q ∘L selMap Ein =
      selMap (fun c => (Eout c)† ∘L q ∘L Ein c) := by
  rw [specHom_comp_selMap, selMap_adjoint, selMap_comp]

/-- A constant selection is a spectator action. -/
theorem selMap_const (X : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α) :
    selMap (fun _ : C => X) = specHom C α X := by
  ext1 w; ext ⟨c, a⟩
  rw [selMap_apply, specHom_eq, spectator_apply]
  rfl

/-- Action of `X` on the left factor of `β × α`. -/
def actLeft (X : EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ β) :
    EuclideanSpace ℂ (β × α) →L[ℂ] EuclideanSpace ℂ (β × α) :=
  onFactor (Equiv.prodComm β α) X

theorem actLeft_apply (X : EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ β)
    (w : EuclideanSpace ℂ (β × α)) (b : β) (a : α) :
    actLeft (α := α) X w (b, a) = X (WithLp.toLp 2 (fun b' => w (b', a))) b := by
  rw [actLeft, onFactor_apply]
  rfl

theorem actLeft_ketR (X : EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ β)
    (φ : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ β) :
    actLeft X (ketR φ v) = ketR φ (X v) := by
  ext ⟨b, a⟩
  rw [actLeft_apply, ketR_apply]
  have h : (WithLp.toLp 2 (fun b' => ketR φ v (b', a)) : EuclideanSpace ℂ β) = φ a • v := by
    ext b'; simp [mul_comm]
  rw [h, map_smul]
  simp [mul_comm]

theorem braR_actLeft (X : EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ β)
    (φ : EuclideanSpace ℂ α) (w : EuclideanSpace ℂ (β × α)) :
    braR φ (actLeft X w) = X (braR φ w) := by
  ext b
  rw [braR_apply]
  simp only [actLeft_apply]
  have h : braR φ w = ∑ a, conj (φ a) • (WithLp.toLp 2 (fun b' => w (b', a)) :
      EuclideanSpace ℂ β) := by
    ext b'; simp [Finset.sum_apply]
  rw [h, map_sum]
  simp [Finset.sum_apply, map_smul]

end

end SparseHamiltonian.GeneralODE.Registers
