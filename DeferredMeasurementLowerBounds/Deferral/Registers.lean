import ODELowerBoundExtensions.Release.Registers
import SparseHamiltonian.OracleCircuit

set_option autoImplicit false

/-!
# Record registers and the dilation of an instrument

The deferral of a measured algorithm (manuscript lines 2363-2364 and 5185-5186: purification and
deferred measurement) keeps every classical outcome in a fresh record register. A record of
`k` registers of width `W` is `Rec W k = Fin k → Option (Fin W)`: the value `none` is the fresh
value and `some j` records outcome `j`. The workspace with records is `Joint (Rec W k) K`
(`ℂ^{Rec W k} ⊗ K` as an `L²` sum), and `split` separates the first register:
`Joint (Rec W (k+1)) K ≃ Joint (Option (Fin W)) (Joint (Rec W k) K)`.

An instrument with Kraus operators `A j` (`j < n ≤ W`, `∑ A j† A j = 1`) becomes one known
unitary (`halmos`): with `V φ = Σ_j |some j⟩ ⊗ A j φ` (an isometry, `krausMap`) and the fresh
injection `e₀ φ = |none⟩ ⊗ φ`,
`U = e₀ V† + V e₀† + (1 - e₀ e₀† - V V†)`
is a self-adjoint unitary with `U e₀ = V` (the Halmos dilation). It exists in every dimension, so
the deferral needs no finite-dimensionality. Unitarity needs completeness and `n ≤ W`
(`halmos_unitary`, `dilation_unitary`); the action on a fresh register, `U e₀ = V`, holds for any
operators `A j` (`halmos_fresh`, `dilation_freshInj`). `dilation` applies it to the first record
register of `Joint (Rec W (k+1)) K`, the remaining registers and the workspace acting as the
system.
-/

namespace DeferredMeasurementLowerBounds.Deferral

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open ODELowerBoundExtensions.Release (jointFlatten)
open scoped InnerProduct

/-- Records of `k` registers of width `W`; `none` is the fresh value. -/
abbrev Rec (W k : ℕ) : Type := Fin k → Option (Fin W)

/-- The fresh record. -/
def Rec.fresh (W k : ℕ) : Rec W k := fun _ => none

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Separation of the first record register. -/
def split (W k : ℕ) (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] :
    Joint (Rec W (k + 1)) K ≃ₗᵢ[ℂ] Joint (Option (Fin W)) (Joint (Rec W k) K) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ K
    (Fin.consEquiv (fun _ : Fin (k + 1) => Option (Fin W))).symm).trans
    (jointFlatten (Option (Fin W)) (Rec W k) K)

omit [CompleteSpace K] in
/-- Coordinates of the separation. -/
theorem split_apply (W k : ℕ) (Ψ : Joint (Rec W (k + 1)) K) (v : Option (Fin W))
    (r : Rec W k) : split W k K Ψ v r = Ψ (Fin.cons v r) := by
  rfl

/-- Coordinates of the adjoint of a component projection: `(proj j)† φ = |j⟩ ⊗ φ`. -/
theorem adjoint_proj_apply {J : Type*} [Fintype J] [DecidableEq J] (j : J) (φ : K) (r : J) :
    (((Joint.proj (K := K) j)†) φ) r = if r = j then φ else 0 := by
  apply ext_inner_left ℂ
  intro χ
  have h := ContinuousLinearMap.adjoint_inner_right (Joint.proj (K := K) j)
    (WithLp.toLp 2 (Pi.single r χ) : Joint J K) φ
  rw [PiLp.inner_apply] at h
  simp only [Joint.proj_apply] at h
  rw [Finset.sum_eq_single r (fun i _ hi => by simp [hi])
    (fun h => absurd (Finset.mem_univ r) h)] at h
  simp only [Pi.single_eq_same] at h
  rw [h]
  by_cases hr : r = j
  · subst hr; simp
  · simp [hr, Ne.symm hr]

/-- A component projection after its adjoint is the identity. -/
theorem proj_comp_adjoint_proj {J : Type*} [Fintype J] (j : J) :
    Joint.proj (K := K) j ∘L (Joint.proj (K := K) j)† = 1 := by
  classical
  ext φ
  simp [adjoint_proj_apply]

/-- The injection of the workspace at the fresh record. -/
def freshInj (W k : ℕ) : K →L[ℂ] Joint (Rec W k) K :=
  (Joint.proj (K := K) (Rec.fresh W k))†

/-- The fresh injection is an isometry. -/
theorem freshInj_isometry (W k : ℕ) : (freshInj (K := K) W k)† ∘L freshInj W k = 1 := by
  rw [freshInj, ContinuousLinearMap.adjoint_adjoint, proj_comp_adjoint_proj]

/-- Coordinates of the fresh injection. -/
theorem freshInj_apply (W k : ℕ) (φ : K) (r : Rec W k) :
    freshInj W k φ r = if r = Rec.fresh W k then φ else 0 := by
  rw [freshInj, adjoint_proj_apply]

/-- The fresh record at `k + 1` registers is a fresh value followed by the fresh record. -/
theorem Rec.fresh_succ (W k : ℕ) :
    Rec.fresh W (k + 1) = Fin.cons (none : Option (Fin W)) (Rec.fresh W k) := by
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

/-- The fresh injection at `k + 1` registers is the fresh injection of the first register
applied to the fresh injection at `k` registers. -/
theorem split_freshInj (W k : ℕ) (φ : K) :
    split W k K (freshInj W (k + 1) φ) =
      ((Joint.proj (K := Joint (Rec W k) K) (none : Option (Fin W)))†) (freshInj W k φ) := by
  ext v r
  rw [split_apply, adjoint_proj_apply]
  simp only [freshInj_apply, Rec.fresh_succ, Fin.cons_inj]
  by_cases hv : v = none
  · subst hv
    simp [freshInj_apply]
  · simp [hv]

/-! ### The Halmos dilation of an instrument -/

section Halmos

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Kraus operator recorded at a register value: `0` at the fresh value and at values that
are not outcomes. -/
def krausAt {W n : ℕ} (A : Fin n → H →L[ℂ] H) : Option (Fin W) → H →L[ℂ] H
  | none => 0
  | some v => if h : v.val < n then A ⟨v.val, h⟩ else 0

/-- The Stinespring isometry `φ ↦ Σ_{j < n} |some j⟩ ⊗ A j φ` into one record register. -/
def krausMap (W : ℕ) {n : ℕ} (A : Fin n → H →L[ℂ] H) : H →L[ℂ] Joint (Option (Fin W)) H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Option (Fin W) => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun v => krausAt (W := W) A v)

omit [CompleteSpace H] in
/-- The record-register component of the Stinespring map at the fresh value vanishes. -/
theorem krausMap_none (W : ℕ) {n : ℕ} (A : Fin n → H →L[ℂ] H) (φ : H) :
    krausMap W A φ none = 0 := by
  rfl

omit [CompleteSpace H] in
/-- The record-register component at outcome `j`. -/
theorem krausMap_some (W : ℕ) {n : ℕ} (A : Fin n → H →L[ℂ] H) (φ : H) (v : Fin W)
    (h : v.val < n) : krausMap W A φ (some v) = A ⟨v.val, h⟩ φ := by
  change krausAt (W := W) A (some v) φ = _
  simp only [krausAt, dif_pos h]

omit [CompleteSpace H] in
/-- Components at values that are not outcomes vanish. -/
theorem krausMap_some_of_le (W : ℕ) {n : ℕ} (A : Fin n → H →L[ℂ] H) (φ : H) (v : Fin W)
    (h : n ≤ v.val) : krausMap W A φ (some v) = 0 := by
  change krausAt (W := W) A (some v) φ = _
  simp only [krausAt, dif_neg (not_lt.mpr h), zero_apply]

/-- The Stinespring map of a complete instrument whose outcomes fit is an isometry. -/
theorem krausMap_isometry (W : ℕ) {n : ℕ} (hn : n ≤ W) {A : Fin n → H →L[ℂ] H}
    (hA : ∑ j, (A j)† ∘L A j = 1) : (krausMap W A)† ∘L krausMap W A = 1 := by
  ext φ
  apply ext_inner_left ℂ
  intro ψ
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    one_apply_eq_self]
  rw [show inner ℂ ψ φ = inner ℂ ψ ((∑ j, (A j)† ∘L A j) φ) by rw [hA, one_apply_eq_self]]
  rw [_root_.sum_apply, inner_sum, PiLp.inner_apply, Fintype.sum_option,
    krausMap_none, inner_zero_left, zero_add]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Fin.sum_univ_add]
  have h2 : ∀ i : Fin m, inner ℂ (krausMap (n + m) A ψ (some (Fin.natAdd n i)))
      (krausMap (n + m) A φ (some (Fin.natAdd n i))) = 0 := by
    intro i
    rw [krausMap_some_of_le _ _ _ _ (by simp), inner_zero_left]
  rw [Finset.sum_eq_zero (fun i _ => h2 i), add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [krausMap_some _ _ _ _ (by simp), krausMap_some _ _ _ _ (by simp)]
  rfl

/-- **Halmos form.** For any `e, V : F → E` the operator `e V† + V e† + (1 - e e† - V V†)` is
self-adjoint. -/
theorem adjoint_halmosForm {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (e V : F →L[ℂ] E) :
    (e ∘L V† + V ∘L e† + (1 - e ∘L e† - V ∘L V†))† =
      e ∘L V† + V ∘L e† + (1 - e ∘L e† - V ∘L V†) := by
  have h1 : ContinuousLinearMap.adjoint (1 : E →L[ℂ] E) = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_one]
  simp only [map_add, map_sub, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, h1]
  abel

/-- **Halmos form.** For isometries `e, V : F → E` with orthogonal ranges, the operator
`U = e V† + V e† + (1 - e e† - V V†)` satisfies `U U = 1`. -/
theorem halmosForm_mul_self {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (e V : F →L[ℂ] E) (hee : e† ∘L e = 1) (heV : e† ∘L V = 0) (hVV : V† ∘L V = 1) :
    (e ∘L V† + V ∘L e† + (1 - e ∘L e† - V ∘L V†)) *
      (e ∘L V† + V ∘L e† + (1 - e ∘L e† - V ∘L V†)) = 1 := by
  have hVe : V† ∘L e = 0 := by
    rw [← ContinuousLinearMap.adjoint_adjoint e, ← ContinuousLinearMap.adjoint_comp, heV,
      map_zero]
  have hee' : ∀ x, ContinuousLinearMap.adjoint e (e x) = x := fun x => by
    simpa using congrArg (fun T => T x) hee
  have heV' : ∀ x, ContinuousLinearMap.adjoint e (V x) = 0 := fun x => by
    simpa using congrArg (fun T => T x) heV
  have hVe' : ∀ x, ContinuousLinearMap.adjoint V (e x) = 0 := fun x => by
    simpa using congrArg (fun T => T x) hVe
  have hVV' : ∀ x, ContinuousLinearMap.adjoint V (V x) = x := fun x => by
    simpa using congrArg (fun T => T x) hVV
  ext Ψ
  simp only [mul_apply_eq_comp, add_apply,
    sub_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self,
    map_add, map_sub, hee', heV', hVe', hVV', map_zero]
  abel

/-- **The Halmos dilation** `e₀ V† + V e₀† + (1 - e₀ e₀† - V V†)` of the instrument `A`. -/
def halmos (W : ℕ) {n : ℕ} (A : Fin n → H →L[ℂ] H) :
    Joint (Option (Fin W)) H →L[ℂ] Joint (Option (Fin W)) H :=
  let e₀ : H →L[ℂ] Joint (Option (Fin W)) H := (Joint.proj (K := H) none)†
  e₀ ∘L (krausMap W A)† + krausMap W A ∘L e₀† + (1 - e₀ ∘L e₀† - krausMap W A ∘L (krausMap W A)†)

/-- The Halmos dilation of a complete instrument is unitary. -/
theorem halmos_unitary (W : ℕ) {n : ℕ} (hn : n ≤ W) {A : Fin n → H →L[ℂ] H}
    (hA : ∑ j, (A j)† ∘L A j = 1) : IsUnitary (halmos W A) := by
  have hee : ((Joint.proj (K := H) (none : Option (Fin W)))†)† ∘L
      (Joint.proj (K := H) (none : Option (Fin W)))† = 1 := by
    rw [ContinuousLinearMap.adjoint_adjoint, proj_comp_adjoint_proj]
  have heV : ((Joint.proj (K := H) (none : Option (Fin W)))†)† ∘L krausMap W A = 0 := by
    rw [ContinuousLinearMap.adjoint_adjoint]
    ext φ
    exact krausMap_none W A φ
  have hU := halmosForm_mul_self _ _ hee heV (krausMap_isometry W hn hA)
  have hs := adjoint_halmosForm (ContinuousLinearMap.adjoint
    (Joint.proj (K := H) (none : Option (Fin W)))) (krausMap W A)
  have hstar : star (halmos W A) = halmos W A := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact hs
  exact ⟨by rw [hstar]; exact hU, by rw [hstar]; exact hU⟩

/-- On a fresh register the dilation writes the outcome: `U (|none⟩ ⊗ φ) = Σ_j |some j⟩ ⊗ A j φ`. -/
theorem halmos_fresh (W : ℕ) {n : ℕ} (A : Fin n → H →L[ℂ] H) (φ : H) :
    halmos W A (((Joint.proj (K := H) (none : Option (Fin W)))†) φ) = krausMap W A φ := by
  have hee : ∀ x : H, ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint
      (Joint.proj (K := H) (none : Option (Fin W))))
      (ContinuousLinearMap.adjoint (Joint.proj (K := H) (none : Option (Fin W))) x) = x :=
    fun x => by
    rw [ContinuousLinearMap.adjoint_adjoint, ← ContinuousLinearMap.comp_apply,
      proj_comp_adjoint_proj, one_apply_eq_self]
  have hVe : ∀ x : H, ContinuousLinearMap.adjoint (krausMap W A)
      (ContinuousLinearMap.adjoint (Joint.proj (K := H) (none : Option (Fin W))) x) = 0 :=
    fun x => by
      apply ext_inner_left ℂ
      intro y
      rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
        Joint.proj_apply, krausMap_none, inner_zero_left, inner_zero_right]
  simp only [halmos, add_apply, sub_apply,
    ContinuousLinearMap.comp_apply, one_apply_eq_self, hee, hVe, map_zero]
  abel

end Halmos

/-- An instrument on `K` acts on the remaining records and the workspace blockwise. -/
theorem fiber_complete {J : Type*} [Fintype J] {n : ℕ} {A : Fin n → K →L[ℂ] K}
    (hA : ∑ j, (A j)† ∘L A j = 1) :
    ∑ j, (Joint.fiber (J := J) fun _ => A j)† ∘L Joint.fiber (fun _ => A j) = 1 := by
  ext Ψ r
  rw [one_apply_eq_self]
  change Joint.proj (K := K) r ((∑ j, (Joint.fiber (J := J) fun _ => A j)† ∘L
    Joint.fiber (fun _ => A j)) Ψ) = Ψ r
  rw [_root_.sum_apply, map_sum]
  simp only [Joint.proj_apply, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.star_eq_adjoint, Joint.star_fiber, Joint.fiber_apply]
  have h := congrArg (fun T => T (Ψ r)) hA
  simpa [_root_.sum_apply, ContinuousLinearMap.star_eq_adjoint] using h

/-- **The deferred instrument** on the first record register of `Joint (Rec W (k+1)) K`. -/
def dilation (W k : ℕ) {n : ℕ} (A : Fin n → K →L[ℂ] K) :
    Joint (Rec W (k + 1)) K →L[ℂ] Joint (Rec W (k + 1)) K :=
  (split W k K).symm.conjStarAlgEquiv
    (halmos W (fun j => Joint.fiber (J := Rec W k) fun _ => A j))

/-- The deferred instrument is a known unitary. -/
theorem dilation_unitary (W k : ℕ) {n : ℕ} (hn : n ≤ W) {A : Fin n → K →L[ℂ] K}
    (hA : ∑ j, (A j)† ∘L A j = 1) : IsUnitary (dilation W k A) :=
  (halmos_unitary W hn (fiber_complete hA)).transport _

/-- On a fresh record the deferred instrument writes the outcome into the first register. -/
theorem dilation_freshInj (W k : ℕ) {n : ℕ} (A : Fin n → K →L[ℂ] K) (φ : K)
    (v : Option (Fin W)) (r : Rec W k) :
    split W k K (dilation W k A (freshInj W (k + 1) φ)) v r =
      match v with
      | none => 0
      | some v => if h : v.val < n then freshInj W k (A ⟨v.val, h⟩ φ) r else 0 := by
  rw [dilation, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply, split_freshInj,
    halmos_fresh W _]
  rcases v with _ | v
  · rw [krausMap_none]
    rfl
  · dsimp only
    by_cases h : v.val < n
    · rw [krausMap_some _ _ _ _ h, dif_pos h, Joint.fiber_apply, freshInj_apply, freshInj_apply]
      split_ifs <;> simp
    · rw [krausMap_some_of_le _ _ _ _ (not_lt.mp h), dif_neg h]
      rfl

end

end DeferredMeasurementLowerBounds.Deferral
