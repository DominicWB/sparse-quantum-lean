import GeneralODE.Block.Registers

/-!
# Standard-form block encodings

* Two isometric embeddings into a finite-dimensional space are related by a
  unitary (`exists_unitary_comp`).
* Standardization: an isometry-encoded block `E_out† q E_in` of a unitary `q`
  on an ancilla register is the block, for one clean basis state, of the
  standard-form unitary `UNLOAD (I ⊗ q) LOAD` (`standardize`).  The fixed
  unitaries `LOAD`, `UNLOAD` depend only on the encodings.
* Fresh-ancilla products: the block of a product of two factors acting on the
  system and disjoint ancilla registers is the product of their blocks
  (`blk_mul_fresh`).
-/

namespace SparseHamiltonian.GeneralODE.Registers

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators ComplexConjugate

section Extension

variable {P V : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

/-- Two isometric embeddings of the same space are related by a unitary. -/
theorem exists_unitary_comp (A B : P →L[ℂ] V) (hA : A† ∘L A = 1) (hB : B† ∘L B = 1) :
    ∃ W : V →L[ℂ] V, IsUnitary W ∧ W ∘L A = B := by
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  have hAn : ∀ x, ‖A x‖ = ‖x‖ := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self A).mpr hA
  have hBn : ∀ x, ‖B x‖ = ‖x‖ := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self B).mpr hB
  have hinj : Function.Injective (A : P →ₗ[ℂ] V) := by
    intro x y hxy
    have h0 : ‖A (x - y)‖ = 0 := by
      rw [map_sub]; change ‖A x - A y‖ = 0
      rw [show A x = A y from hxy, sub_self, norm_zero]
    rw [hAn] at h0
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  let eA : P ≃ₗ[ℂ] LinearMap.range (A : P →ₗ[ℂ] V) := LinearEquiv.ofInjective _ hinj
  let L : LinearMap.range (A : P →ₗ[ℂ] V) →ₗᵢ[ℂ] V :=
    { toLinearMap := (B : P →ₗ[ℂ] V).comp eA.symm.toLinearMap
      norm_map' := by
        intro s
        change ‖B (eA.symm s)‖ = ‖s‖
        rw [hBn, ← hAn]
        have : (A : P →ₗ[ℂ] V) (eA.symm s) = s :=
          LinearEquiv.ofInjective_symm_apply (f := (A : P →ₗ[ℂ] V)) (h := hinj) s
        rw [Submodule.coe_norm, ← this]
        rfl }
  let We : V ≃ₗᵢ[ℂ] V := L.extend.toLinearIsometryEquiv rfl
  refine ⟨We.toContinuousLinearEquiv.toContinuousLinearMap, ?_, ?_⟩
  · have hadj : (We.toContinuousLinearEquiv.toContinuousLinearMap)† =
        We.symm.toContinuousLinearEquiv.toContinuousLinearMap :=
      LinearIsometryEquiv.adjoint_eq_symm We
    constructor
    · rw [ContinuousLinearMap.star_eq_adjoint, hadj]
      ext v; simp
    · rw [ContinuousLinearMap.star_eq_adjoint, hadj]
      ext v; simp
  · ext p
    change L.extend (A p) = B p
    have hmem : A p ∈ LinearMap.range (A : P →ₗ[ℂ] V) := ⟨p, rfl⟩
    have := LinearIsometry.extend_apply L ⟨A p, hmem⟩
    simp only at this
    rw [this]
    change B (eA.symm ⟨A p, hmem⟩) = B p
    congr 1
    apply eA.injective
    rw [LinearEquiv.apply_symm_apply]
    ext
    rfl

end Extension

section Standard

theorem one_comp_eq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (f : E →L[ℂ] F) : (1 : F →L[ℂ] F) ∘L f = f := by
  ext x; rfl

variable {σ ν : Type*} [Fintype σ] [Fintype ν] [DecidableEq σ] [DecidableEq ν]

/-- Product state `ψ ⊗ w`. -/
def ketL (ψ : EuclideanSpace ℂ σ) : EuclideanSpace ℂ ν →L[ℂ] EuclideanSpace ℂ (σ × ν) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 (fun p => ψ p.1 * w p.2)
      map_add' := by intro v w; ext p; simp [mul_add]
      map_smul' := by intro c v; ext p; simp; ring }

omit [DecidableEq σ] [DecidableEq ν] in
@[simp] theorem ketL_apply (ψ : EuclideanSpace ℂ σ) (w : EuclideanSpace ℂ ν) (p : σ × ν) :
    ketL ψ w p = ψ p.1 * w p.2 := rfl

/-- Partial inner product with `ψ` on the left factor. -/
def braL (ψ : EuclideanSpace ℂ σ) : EuclideanSpace ℂ (σ × ν) →L[ℂ] EuclideanSpace ℂ ν :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 (fun b => ∑ s, conj (ψ s) * w (s, b))
      map_add' := by intro v w; ext b; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c v; ext b
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring) }

omit [DecidableEq σ] [DecidableEq ν] in
@[simp] theorem braL_apply (ψ : EuclideanSpace ℂ σ) (w : EuclideanSpace ℂ (σ × ν)) (b : ν) :
    braL ψ w b = ∑ s, conj (ψ s) * w (s, b) := rfl

omit [DecidableEq σ] [DecidableEq ν] in
theorem ketL_adjoint (ψ : EuclideanSpace ℂ σ) :
    (ketL (ν := ν) ψ)† = braL ψ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro w v
  simp only [PiLp.inner_apply, braL_apply, ketL_apply, RCLike.inner_apply, Fintype.sum_prod_type,
    map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  ring

omit [DecidableEq σ] [DecidableEq ν] in
theorem spectator_ketL (q : EuclideanSpace ℂ ν →L[ℂ] EuclideanSpace ℂ ν)
    (ψ : EuclideanSpace ℂ σ) (w : EuclideanSpace ℂ ν) :
    specHom σ ν q (ketL ψ w) = ketL ψ (q w) := by
  ext ⟨s, b⟩
  rw [specHom_eq, spectator_apply, ketL_apply]
  have h : (WithLp.toLp 2 (fun b' => ketL ψ w (s, b')) : EuclideanSpace ℂ ν) = ψ s • w := by
    ext b'; simp
  rw [h, map_smul]
  simp

omit [DecidableEq σ] [DecidableEq ν] in
theorem ketL_isometry (ψ : EuclideanSpace ℂ σ) (hψ : ‖ψ‖ = 1) :
    (ketL (ν := ν) ψ)† ∘L ketL ψ = 1 := by
  rw [← ContinuousLinearMap.norm_map_iff_adjoint_comp_self]
  intro w
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp only [ketL_apply, norm_mul, mul_pow]
  rw [← Finset.sum_mul_sum]
  have : ∑ i, ‖ψ i‖ ^ 2 = 1 := by rw [← EuclideanSpace.norm_sq_eq, hψ, one_pow]
  rw [this, one_mul]

/-- Standard form of an isometry-encoded block. -/
theorem standardize (s0 : σ) (n0 : ν)
    (Ein Eout : EuclideanSpace ℂ σ →L[ℂ] EuclideanSpace ℂ ν)
    (hin : Ein† ∘L Ein = 1) (hout : Eout† ∘L Eout = 1) :
    ∃ LOAD UNLOAD : EuclideanSpace ℂ (σ × ν) →L[ℂ] EuclideanSpace ℂ (σ × ν),
      IsUnitary LOAD ∧ IsUnitary UNLOAD ∧
      ∀ q : EuclideanSpace ℂ ν →L[ℂ] EuclideanSpace ℂ ν,
        blk (EuclideanSpace.single n0 1) (EuclideanSpace.single n0 1)
          (UNLOAD * specHom σ ν q * LOAD) = Eout† ∘L q ∘L Ein := by
  set e0 : EuclideanSpace ℂ ν := EuclideanSpace.single n0 1
  set es : EuclideanSpace ℂ σ := EuclideanSpace.single s0 1
  have he0 : ‖e0‖ = 1 := by simp [e0]
  have hes : ‖es‖ = 1 := by simp [es]
  have hA := ketR_isometry (σ := σ) e0 he0
  have hK := ketL_isometry (ν := ν) es hes
  have hBin : (ketL es ∘L Ein)† ∘L (ketL es ∘L Ein) = 1 := by
    rw [adjoint_comp]
    calc Ein† ∘L (ketL es)† ∘L (ketL es ∘L Ein) = Ein† ∘L ((ketL es)† ∘L ketL es) ∘L Ein := by
          simp only [comp_assoc]
      _ = 1 := by rw [hK, one_comp_eq]; exact hin
  have hBout : (ketL es ∘L Eout)† ∘L (ketL es ∘L Eout) = 1 := by
    rw [adjoint_comp]
    calc Eout† ∘L (ketL es)† ∘L (ketL es ∘L Eout) = Eout† ∘L ((ketL es)† ∘L ketL es) ∘L Eout := by
          simp only [comp_assoc]
      _ = 1 := by rw [hK, one_comp_eq]; exact hout
  obtain ⟨W1, hW1, hW1A⟩ := exists_unitary_comp (P := EuclideanSpace ℂ σ)
    (V := EuclideanSpace ℂ (σ × ν)) (ketR (σ := σ) e0) (ketL es ∘L Ein) hA hBin
  obtain ⟨W2, hW2, hW2A⟩ := exists_unitary_comp (P := EuclideanSpace ℂ σ)
    (V := EuclideanSpace ℂ (σ × ν)) (ketR (σ := σ) e0) (ketL es ∘L Eout) hA hBout
  refine ⟨W1, star W2, hW1, hW2.adjoint, ?_⟩
  intro q
  unfold blk
  rw [← ketR_adjoint]
  have hspec : specHom σ ν q ∘L ketL es = ketL es ∘L q := by
    ext1 w; exact spectator_ketL q es w
  have h1 : (ketR e0)† ∘L (star W2 * specHom σ ν q * W1) ∘L ketR e0 =
      (W2 ∘L ketR e0)† ∘L specHom σ ν q ∘L (W1 ∘L ketR e0) := by
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.star_eq_adjoint, adjoint_comp,
      comp_assoc]
  rw [h1, hW1A, hW2A, adjoint_comp]
  have h2 : Eout† ∘L (ketL es)† ∘L specHom σ ν q ∘L ketL es ∘L Ein =
      Eout† ∘L ((ketL es)† ∘L ketL es) ∘L q ∘L Ein := by
    rw [← comp_assoc (specHom σ ν q) (ketL es) Ein, hspec]
    simp only [comp_assoc]
  simp only [comp_assoc] at h2 ⊢
  have hK' : ∀ X : EuclideanSpace ℂ σ →L[ℂ] EuclideanSpace ℂ ν,
      (ketL (ν := ν) es)† ∘L (ketL es ∘L X) = X := by
    intro X
    rw [← comp_assoc, hK, one_comp_eq]
  rw [h2, hK']

omit [DecidableEq σ] in
theorem load_ketR_isometry (n0 : ν) :
    (ketR (σ := σ) (EuclideanSpace.single n0 (1 : ℂ)))† ∘L
      ketR (σ := σ) (EuclideanSpace.single n0 (1 : ℂ)) = 1 :=
  ketR_isometry _ (by simp)

omit [DecidableEq ν] in
theorem load_isometry (s0 : σ) (E : EuclideanSpace ℂ σ →L[ℂ] EuclideanSpace ℂ ν)
    (hE : E† ∘L E = 1) :
    (ketL (EuclideanSpace.single s0 (1 : ℂ)) ∘L E)† ∘L
      (ketL (EuclideanSpace.single s0 (1 : ℂ)) ∘L E) = 1 := by
  have hK := ketL_isometry (ν := ν) (EuclideanSpace.single s0 (1 : ℂ)) (by simp)
  rw [adjoint_comp]
  calc E† ∘L (ketL (EuclideanSpace.single s0 1))† ∘L (ketL (EuclideanSpace.single s0 1) ∘L E)
      = E† ∘L ((ketL (ν := ν) (EuclideanSpace.single s0 1))† ∘L
          ketL (EuclideanSpace.single s0 1)) ∘L E := by simp only [comp_assoc]
    _ = 1 := by rw [hK, one_comp_eq]; exact hE

/-- A fixed unitary loading `v ⊗ |n₀⟩` into `|s₀⟩ ⊗ E v`. -/
def standardLoad (s0 : σ) (n0 : ν) (E : EuclideanSpace ℂ σ →L[ℂ] EuclideanSpace ℂ ν)
    (hE : E† ∘L E = 1) : EuclideanSpace ℂ (σ × ν) →L[ℂ] EuclideanSpace ℂ (σ × ν) :=
  Classical.choose (exists_unitary_comp (P := EuclideanSpace ℂ σ)
    (V := EuclideanSpace ℂ (σ × ν)) (ketR (σ := σ) (EuclideanSpace.single n0 1))
    (ketL (EuclideanSpace.single s0 1) ∘L E)
    (load_ketR_isometry n0) (load_isometry s0 E hE))

theorem standardLoad_spec (s0 : σ) (n0 : ν) (E : EuclideanSpace ℂ σ →L[ℂ] EuclideanSpace ℂ ν)
    (hE : E† ∘L E = 1) :
    IsUnitary (standardLoad s0 n0 E hE) ∧
      standardLoad s0 n0 E hE ∘L ketR (σ := σ) (EuclideanSpace.single n0 1) =
        ketL (EuclideanSpace.single s0 1) ∘L E :=
  Classical.choose_spec (exists_unitary_comp (P := EuclideanSpace ℂ σ)
    (V := EuclideanSpace ℂ (σ × ν)) (ketR (σ := σ) (EuclideanSpace.single n0 1))
    (ketL (EuclideanSpace.single s0 1) ∘L E)
    (load_ketR_isometry n0) (load_isometry s0 E hE))

/-- The standard form `UNLOAD (I ⊗ q) LOAD` of an isometry-encoded block. -/
def standardForm (s0 : σ) (n0 : ν) (Ein Eout : EuclideanSpace ℂ σ →L[ℂ] EuclideanSpace ℂ ν)
    (hin : Ein† ∘L Ein = 1) (hout : Eout† ∘L Eout = 1)
    (q : EuclideanSpace ℂ ν →L[ℂ] EuclideanSpace ℂ ν) :
    EuclideanSpace ℂ (σ × ν) →L[ℂ] EuclideanSpace ℂ (σ × ν) :=
  star (standardLoad s0 n0 Eout hout) * specHom σ ν q * standardLoad s0 n0 Ein hin

theorem standardForm_unitary (s0 : σ) (n0 : ν)
    (Ein Eout : EuclideanSpace ℂ σ →L[ℂ] EuclideanSpace ℂ ν)
    (hin : Ein† ∘L Ein = 1) (hout : Eout† ∘L Eout = 1)
    (q : EuclideanSpace ℂ ν →L[ℂ] EuclideanSpace ℂ ν) (hq : IsUnitary q) :
    IsUnitary (standardForm s0 n0 Ein Eout hin hout q) :=
  (((standardLoad_spec s0 n0 Eout hout).1.adjoint).mul (isUnitary_map _ hq)).mul
    (standardLoad_spec s0 n0 Ein hin).1

theorem blk_standardForm (s0 : σ) (n0 : ν)
    (Ein Eout : EuclideanSpace ℂ σ →L[ℂ] EuclideanSpace ℂ ν)
    (hin : Ein† ∘L Ein = 1) (hout : Eout† ∘L Eout = 1)
    (q : EuclideanSpace ℂ ν →L[ℂ] EuclideanSpace ℂ ν) :
    blk (EuclideanSpace.single n0 1) (EuclideanSpace.single n0 1)
      (standardForm s0 n0 Ein Eout hin hout q) = Eout† ∘L q ∘L Ein := by
  set e0 : EuclideanSpace ℂ ν := EuclideanSpace.single n0 1
  set es : EuclideanSpace ℂ σ := EuclideanSpace.single s0 1
  have hK := ketL_isometry (ν := ν) es (by simp [es])
  have hW1A := (standardLoad_spec s0 n0 Ein hin).2
  have hW2A := (standardLoad_spec s0 n0 Eout hout).2
  unfold blk standardForm
  rw [← ketR_adjoint]
  have hspec : specHom σ ν q ∘L ketL es = ketL es ∘L q := by
    ext1 w; exact spectator_ketL q es w
  have h1 : (ketR e0)† ∘L (star (standardLoad s0 n0 Eout hout) * specHom σ ν q *
      standardLoad s0 n0 Ein hin) ∘L ketR e0 =
      (standardLoad s0 n0 Eout hout ∘L ketR e0)† ∘L specHom σ ν q ∘L
        (standardLoad s0 n0 Ein hin ∘L ketR e0) := by
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.star_eq_adjoint, adjoint_comp,
      comp_assoc]
  rw [h1, hW1A, hW2A, adjoint_comp]
  have h2 : Eout† ∘L (ketL es)† ∘L specHom σ ν q ∘L ketL es ∘L Ein =
      Eout† ∘L ((ketL es)† ∘L ketL es) ∘L q ∘L Ein := by
    rw [← comp_assoc (specHom σ ν q) (ketL es) Ein, hspec]
    simp only [comp_assoc]
  simp only [comp_assoc] at h2 ⊢
  have hK' : ∀ X : EuclideanSpace ℂ σ →L[ℂ] EuclideanSpace ℂ ν,
      (ketL (ν := ν) es)† ∘L (ketL es ∘L X) = X := by
    intro X
    rw [← comp_assoc, hK, one_comp_eq]
  rw [h2, hK']

end Standard

section Fresh

variable {σ α1 α2 : Type*} [Fintype σ] [Fintype α1] [Fintype α2]

/-- Tensor product of ancilla states. -/
def tens (φ1 : EuclideanSpace ℂ α1) (φ2 : EuclideanSpace ℂ α2) : EuclideanSpace ℂ (α1 × α2) :=
  WithLp.toLp 2 (fun a => φ1 a.1 * φ2 a.2)

omit [Fintype α1] [Fintype α2] in
@[simp] theorem tens_apply (φ1 : EuclideanSpace ℂ α1) (φ2 : EuclideanSpace ℂ α2) (a : α1 × α2) :
    tens φ1 φ2 a = φ1 a.1 * φ2 a.2 := rfl

theorem norm_tens (φ1 : EuclideanSpace ℂ α1) (φ2 : EuclideanSpace ℂ α2) :
    ‖tens φ1 φ2‖ = ‖φ1‖ * ‖φ2‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  simp [mul_pow]

variable (σ α1 α2) in
/-- The first factor acts on `σ × α1`, with `α2` a spectator. -/
def firstFrame : σ × (α1 × α2) ≃ α2 × (σ × α1) where
  toFun p := (p.2.2, (p.1, p.2.1))
  invFun q := (q.2.1, (q.2.2, q.1))
  left_inv _ := rfl
  right_inv _ := rfl

variable (σ α1 α2) in
/-- The second factor acts on `σ × α2`, with `α1` a spectator. -/
def secondFrame : σ × (α1 × α2) ≃ α1 × (σ × α2) where
  toFun p := (p.2.1, (p.1, p.2.2))
  invFun q := (q.2.1, (q.1, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Fresh-ancilla products multiply blocks. -/
theorem blk_mul_fresh
    (U1 : EuclideanSpace ℂ (σ × α1) →L[ℂ] EuclideanSpace ℂ (σ × α1))
    (U2 : EuclideanSpace ℂ (σ × α2) →L[ℂ] EuclideanSpace ℂ (σ × α2))
    (φ1 ψ1 : EuclideanSpace ℂ α1) (φ2 ψ2 : EuclideanSpace ℂ α2) :
    blk (tens φ1 φ2) (tens ψ1 ψ2)
        (onFactor (secondFrame σ α1 α2) U2 * onFactor (firstFrame σ α1 α2) U1) =
      blk φ2 ψ2 U2 * blk φ1 ψ1 U1 := by
  ext1 v
  set W := U1 (ketR φ1 v) with hW
  -- slices of `W` along the first ancilla
  let Wsl : α1 → EuclideanSpace ℂ σ := fun a1 => WithLp.toLp 2 (fun s => W (s, a1))
  -- the first factor
  have h1 : onFactor (firstFrame σ α1 α2) U1 (ketR (tens φ1 φ2) v) =
      WithLp.toLp 2 (fun p : σ × (α1 × α2) => φ2 p.2.2 * W (p.1, p.2.1)) := by
    ext ⟨s, a1, a2⟩
    rw [onFactor_apply]
    have hvec : (WithLp.toLp 2 (fun b : σ × α1 =>
        ketR (tens φ1 φ2) v ((firstFrame σ α1 α2).symm
          (((firstFrame σ α1 α2) (s, a1, a2)).1, b))) : EuclideanSpace ℂ (σ × α1)) =
        φ2 a2 • ketR φ1 v := by
      ext ⟨s', a1'⟩
      simp [firstFrame]
      ring
    rw [hvec, map_smul]
    simp [firstFrame, hW]
  -- the second factor
  have h2 : onFactor (secondFrame σ α1 α2) U2
      (WithLp.toLp 2 (fun p : σ × (α1 × α2) => φ2 p.2.2 * W (p.1, p.2.1))) =
      WithLp.toLp 2 (fun p : σ × (α1 × α2) => U2 (ketR φ2 (Wsl p.2.1)) (p.1, p.2.2)) := by
    ext ⟨s, a1, a2⟩
    rw [onFactor_apply]
    have hvec : (WithLp.toLp 2 (fun b : σ × α2 =>
        (WithLp.toLp 2 (fun p : σ × (α1 × α2) => φ2 p.2.2 * W (p.1, p.2.1)) :
          EuclideanSpace ℂ (σ × (α1 × α2)))
          ((secondFrame σ α1 α2).symm (((secondFrame σ α1 α2) (s, a1, a2)).1, b))) :
          EuclideanSpace ℂ (σ × α2)) = ketR φ2 (Wsl a1) := by
      ext ⟨s', a2'⟩
      simp [secondFrame, Wsl]
      ring
    rw [hvec]
    simp [secondFrame]
  -- blocks
  have hblk1 : blk φ1 ψ1 U1 v = ∑ a1, conj (ψ1 a1) • Wsl a1 := by
    ext s
    simp [blk, Wsl, hW]
  have hrhs : (blk φ2 ψ2 U2 * blk φ1 ψ1 U1) v =
      ∑ a1, conj (ψ1 a1) • blk φ2 ψ2 U2 (Wsl a1) := by
    rw [mul_apply_eq_comp, hblk1, map_sum]
    simp [map_smul]
  rw [hrhs]
  ext s
  simp only [blk, comp_apply, mul_apply_eq_comp, h1, h2, braR_apply, tens_apply,
    Fintype.sum_prod_type, map_mul]
  rw [WithLp.ofLp_sum]
  simp only [Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl; intro a _
  rw [braR_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _
  ring

end Fresh

end

end SparseHamiltonian.GeneralODE.Registers
