import CleanWorkODE.Work
import GeneralSourceExtensions.Mesh.Oracles

/-!
# Temporary work registers of the supplied source operations

A work register with basis `W` and clean state `w₀` is adjoined to the source register of the
primitive workspace `ODESectorTensor.Physical A B`: the workspace with work registers is
`ODESectorTensor.Physical (A × W) B`.

* `workSplit`, `cleanPi`, `liftPi`, `piWork`: the embedding `ψ ↦ ψ ⊗ |w₀⟩` and the lift
  `F ↦ F ⊗ 1` of fixed gates, a `WorkEmbedding`;
* `sourcePhysical_clean`: a supplied source call enabled on the inactive matrix sector keeps the
  clean-input error of the operation on the source register;
* `liftAct`, `liftAct_clean`: an operation on active registers and the work register, with the
  remaining source registers as spectators (`Q ⊗ 1_β` through a basis change `A ≃ α × β`), keeps
  its clean-input error (the manuscript's "tensoring that difference with an identity preserves
  its norm", the paragraph after eq. `access:eq:full-output`);
* `ctrlL`: the label-controlled loader in basis coordinates; `slice_act`, `slice_loader`: the
  exact weight preparation and loader of `GeneralSourceODE` act on the label, respectively on the
  label and data registers, with the remaining registers as spectators.
-/

set_option autoImplicit false

namespace SparseHamiltonian.CleanWorkODE

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators

/-! ### The work register -/

section Split

variable {A W V : Type*} [Fintype A] [Fintype W] [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The work register split off a register of `A × W`: the `w`-th copy of the `A` register. -/
def workSplit : PiLp 2 (fun _ : A × W => V) ≃ₗᵢ[ℂ] PiLp 2 (fun _ : W => PiLp 2 (fun _ : A => V)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ V
      ((Equiv.prodComm A W).trans (Equiv.sigmaEquivProd W A).symm)).trans
    (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : W) (_ : A) => V))

@[simp] theorem workSplit_apply (f : PiLp 2 (fun _ : A × W => V)) (w : W) (a : A) :
    workSplit f w a = f (a, w) := rfl

@[simp] theorem workSplit_symm_apply (g : PiLp 2 (fun _ : W => PiLp 2 (fun _ : A => V)))
    (a : A) (w : W) : workSplit.symm g (a, w) = g w a := rfl

end Split

section Clean

variable {A W V : Type*} [Fintype A] [Fintype W] [DecidableEq W]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (w₀ : W)

/-- `ψ ↦ PiLp.single 2 w₀ ψ` as a linear isometry. -/
def singleLI : PiLp 2 (fun _ : A => V) →ₗᵢ[ℂ] PiLp 2 (fun _ : W => PiLp 2 (fun _ : A => V)) where
  toFun ψ := PiLp.single 2 w₀ ψ
  map_add' _ _ := PiLp.single_add 2 w₀
  map_smul' c ψ := by
    apply PiLp.ext
    intro w
    by_cases h : w = w₀
    · subst h
      simp
    · simp [h]
  norm_map' ψ := PiLp.norm_single 2 (fun _ : W => PiLp 2 (fun _ : A => V)) w₀ ψ

/-- **The clean work register**: `ψ ↦ ψ ⊗ |w₀⟩`. -/
def cleanPi : PiLp 2 (fun _ : A => V) →L[ℂ] PiLp 2 (fun _ : A × W => V) :=
  ((workSplit (A := A) (W := W) (V := V)).symm.toLinearIsometry.comp
    (singleLI w₀)).toContinuousLinearMap

theorem workSplit_cleanPi (ψ : PiLp 2 (fun _ : A => V)) :
    workSplit (cleanPi w₀ ψ) = PiLp.single 2 w₀ ψ := by
  change workSplit (workSplit.symm (singleLI w₀ ψ)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem cleanPi_apply (ψ : PiLp 2 (fun _ : A => V)) (a : A) (w : W) :
    cleanPi w₀ ψ (a, w) = if w = w₀ then ψ a else 0 := by
  rw [← workSplit_apply, workSplit_cleanPi]
  by_cases hw : w = w₀
  · subst hw
    simp
  · simp [hw]

theorem cleanPi_norm (ψ : PiLp 2 (fun _ : A => V)) : ‖cleanPi w₀ ψ‖ = ‖ψ‖ :=
  ((workSplit (A := A) (W := W) (V := V)).symm.toLinearIsometry.comp (singleLI w₀)).norm_map ψ

theorem cleanPi_isometry [CompleteSpace V] :
    (cleanPi (A := A) (V := V) w₀)† ∘L cleanPi (A := A) (V := V) w₀ = 1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp (cleanPi_norm w₀)

end Clean

section Lift

variable {A W V : Type*} [Fintype A] [Fintype W] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

/-- **The lift of a fixed gate**: `F ↦ F ⊗ 1` on the work register. -/
def liftPi (F : PiLp 2 (fun _ : A => V) →L[ℂ] PiLp 2 (fun _ : A => V)) :
    PiLp 2 (fun _ : A × W => V) →L[ℂ] PiLp 2 (fun _ : A × W => V) :=
  (workSplit (A := A) (W := W) (V := V)).symm.conjStarAlgEquiv
    (WeightedClock.diagonal (fun _ : W => F))

theorem liftPi_unitary {F : PiLp 2 (fun _ : A => V) →L[ℂ] PiLp 2 (fun _ : A => V)}
    (hF : IsUnitary F) : IsUnitary (liftPi (W := W) F) :=
  (CoherentQuerySchedule.diagonal_unitary _ (fun _ => hF)).transport
    (workSplit (A := A) (W := W) (V := V)).symm

theorem workSplit_liftPi (F : PiLp 2 (fun _ : A => V) →L[ℂ] PiLp 2 (fun _ : A => V))
    (f : PiLp 2 (fun _ : A × W => V)) (w : W) :
    workSplit (liftPi F f) w = F (workSplit f w) := by
  simp only [liftPi, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply,
    WeightedClock.diagonal_apply]

variable [DecidableEq W] (w₀ : W)

theorem liftPi_clean (F : PiLp 2 (fun _ : A => V) →L[ℂ] PiLp 2 (fun _ : A => V)) :
    liftPi (W := W) F ∘L cleanPi w₀ = cleanPi w₀ ∘L F := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply (workSplit (A := A) (W := W) (V := V)).injective
  apply PiLp.ext
  intro w
  rw [comp_apply, comp_apply, workSplit_liftPi, workSplit_cleanPi, workSplit_cleanPi]
  by_cases hw : w = w₀
  · subst hw
    simp
  · simp [hw]

/-- **The work embedding** of the register `A` into `A × W` with clean state `w₀`. -/
def piWork : WorkEmbedding (PiLp 2 (fun _ : A => V)) (PiLp 2 (fun _ : A × W => V)) where
  clean := cleanPi w₀
  isometry := cleanPi_isometry w₀
  lift := liftPi
  lift_unitary _ hF := liftPi_unitary hF
  lift_clean := liftPi_clean w₀

@[simp] theorem piWork_clean : (piWork (A := A) (V := V) w₀).clean = cleanPi w₀ := rfl

/-- **Implementations without a work register**: an operation within `δ` of `U` in operator norm
(the hypothesis of the released endpoints), run with the work register as a spectator, is within
`δ` of `U` on a clean work register; with `Q = U` and `δ = 0`, exact preparations meet the
clean-input hypotheses for every work register. -/
theorem CleanErr.liftPi_of_norm {Q U : PiLp 2 (fun _ : A => V) →L[ℂ] PiLp 2 (fun _ : A => V)}
    {δ : ℝ} (h : ‖Q - U‖ ≤ δ) : CleanErr (cleanPi w₀) (liftPi (W := W) Q) U δ := by
  intro ψ
  have e : liftPi (W := W) Q (cleanPi w₀ ψ) = cleanPi w₀ (Q ψ) := by
    simpa only [comp_apply] using congrArg (fun F => F ψ) (liftPi_clean w₀ Q)
  rw [e, ← map_sub, cleanPi_norm, ← sub_apply]
  exact ((Q - U).le_opNorm ψ).trans (mul_le_mul_of_nonneg_right h (norm_nonneg ψ))

end Lift

/-! ### Supplied calls on the inactive matrix sector -/

section Sector

variable {A B W : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype W] [DecidableEq W] (w₀ : W)

omit [DecidableEq A] [DecidableEq B] in
theorem transpose_cleanPi (v : ODESectorTensor.Physical A B)
    (wb : NativeControlledOracle.Workspace B) :
    ODESectorTensor.transpose (A := A × W) (B := B) (cleanPi w₀ v) wb =
      cleanPi (V := ℂ) w₀ (ODESectorTensor.transpose (A := A) (B := B) v wb) := by
  apply PiLp.ext
  rintro ⟨a, w⟩
  rw [ODESectorTensor.transpose_apply, cleanPi_apply, cleanPi_apply]
  split_ifs
  · rfl
  · rfl

omit [DecidableEq A] [DecidableEq B] in
theorem transpose_sourcePhysical (S : EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (v : ODESectorTensor.Physical A B) (wb : NativeControlledOracle.Workspace B) :
    ODESectorTensor.transpose (A := A) (B := B) (ODESectorTensor.sourcePhysical S v) wb =
      (if wb.1.1.1 then (1 : EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) else S)
        (ODESectorTensor.transpose (A := A) (B := B) v wb) := by
  simp only [ODESectorTensor.sourcePhysical, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply,
    WeightedClock.diagonal_apply]

omit [DecidableEq A] [DecidableEq B] in
/-- **An enabled supplied call keeps the clean-input error** of the operation on the source
register. -/
theorem sourcePhysical_clean (S : EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (SW : EuclideanSpace ℂ (A × W) →L[ℂ] EuclideanSpace ℂ (A × W)) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : CleanErr (cleanPi (V := ℂ) w₀) SW S δ) :
    CleanErr (cleanPi (V := EuclideanSpace ℂ (NativeControlledOracle.Workspace B)) w₀)
      (ODESectorTensor.sourcePhysical (A := A × W) (B := B) SW)
      (ODESectorTensor.sourcePhysical (A := A) (B := B) S) δ := by
  intro v
  set d := ODESectorTensor.sourcePhysical (A := A × W) (B := B) SW (cleanPi w₀ v) -
    cleanPi w₀ (ODESectorTensor.sourcePhysical (A := A) (B := B) S v) with hd
  have hb : ∀ wb, ‖ODESectorTensor.transpose (A := A × W) (B := B) d wb‖ ≤
      δ * ‖ODESectorTensor.transpose (A := A) (B := B) v wb‖ := by
    intro wb
    rw [hd, map_sub, PiLp.sub_apply, transpose_sourcePhysical, transpose_cleanPi,
      transpose_cleanPi, transpose_sourcePhysical]
    by_cases he : wb.1.1.1
    · rw [if_pos he, if_pos he, one_apply_eq_self, one_apply_eq_self, sub_self, norm_zero]
      exact mul_nonneg hδ (norm_nonneg _)
    · rw [if_neg he, if_neg he]
      exact h _
  have hsq : ‖d‖ ^ 2 ≤ (δ * ‖v‖) ^ 2 := by
    rw [← LinearIsometryEquiv.norm_map (ODESectorTensor.transpose (A := A × W) (B := B)) d,
      ← LinearIsometryEquiv.norm_map (ODESectorTensor.transpose (A := A) (B := B)) v,
      PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    exact Finset.sum_le_sum fun wb _ => by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb wb) 2
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ (norm_nonneg _))).mp hsq

end Sector

/-! ### Operations with spectator registers -/

section Act

variable {A α β W : Type*} [Fintype A] [Fintype α] [Fintype β] [Fintype W] [DecidableEq W]
  (w₀ : W)

/-- The basis change `A × W ≃ β × (α × W)` of `e : A ≃ α × β`. -/
def workPerm (e : A ≃ α × β) : A × W ≃ β × (α × W) where
  toFun p := ((e p.1).2, ((e p.1).1, p.2))
  invFun q := (e.symm (q.2.1, q.1), q.2.2)
  left_inv p := by simp
  right_inv q := by simp

/-- The register of `A × W` as a direct sum over the spectator basis `β` of active registers
`α × W`. -/
def actLayout (e : A ≃ α × β) :
    EuclideanSpace ℂ (A × W) ≃ₗᵢ[ℂ] PiLp 2 (fun _ : β => EuclideanSpace ℂ (α × W)) :=
  (LookupOracle.permutationUnitary (workPerm (W := W) e)).trans
    (RegisterEquivalences.productFlatten β (α × W)).symm

omit [DecidableEq W] in
@[simp] theorem actLayout_apply (e : A ≃ α × β) (f : EuclideanSpace ℂ (A × W)) (b : β)
    (p : α × W) : actLayout e f b p = f (e.symm (p.1, b), p.2) := rfl

/-- The register of `A` as a direct sum over `β` of active registers `α`. -/
def sliceLayout (e : A ≃ α × β) :
    EuclideanSpace ℂ A ≃ₗᵢ[ℂ] PiLp 2 (fun _ : β => EuclideanSpace ℂ α) :=
  (LookupOracle.permutationUnitary (e.trans (Equiv.prodComm α β))).trans
    (RegisterEquivalences.productFlatten β α).symm

@[simp] theorem sliceLayout_apply (e : A ≃ α × β) (u : EuclideanSpace ℂ A) (b : β) (a : α) :
    sliceLayout e u b a = u (e.symm (a, b)) := rfl

/-- **An operation on the active registers and the work register**, `Q ⊗ 1_β` through
`e : A ≃ α × β`. -/
def liftAct (e : A ≃ α × β)
    (Q : EuclideanSpace ℂ (α × W) →L[ℂ] EuclideanSpace ℂ (α × W)) :
    EuclideanSpace ℂ (A × W) →L[ℂ] EuclideanSpace ℂ (A × W) :=
  (actLayout e).symm.conjStarAlgEquiv (WeightedClock.diagonal (fun _ : β => Q))

omit [DecidableEq W] in
theorem liftAct_unitary (e : A ≃ α × β)
    {Q : EuclideanSpace ℂ (α × W) →L[ℂ] EuclideanSpace ℂ (α × W)} (hQ : IsUnitary Q) :
    IsUnitary (liftAct e Q) :=
  (CoherentQuerySchedule.diagonal_unitary _ (fun _ => hQ)).transport (actLayout e).symm

omit [DecidableEq W] in
theorem actLayout_liftAct (e : A ≃ α × β)
    (Q : EuclideanSpace ℂ (α × W) →L[ℂ] EuclideanSpace ℂ (α × W))
    (f : EuclideanSpace ℂ (A × W)) (b : β) :
    actLayout e (liftAct e Q f) b = Q (actLayout e f b) := by
  simp only [liftAct, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply,
    WeightedClock.diagonal_apply]

theorem actLayout_cleanPi (e : A ≃ α × β) (u : EuclideanSpace ℂ A) (b : β) :
    actLayout e (cleanPi (V := ℂ) w₀ u) b = cleanPi (V := ℂ) w₀ (sliceLayout e u b) := by
  apply PiLp.ext
  rintro ⟨a, w⟩
  rw [actLayout_apply, cleanPi_apply, cleanPi_apply, sliceLayout_apply]

/-- **Tensoring with spectators keeps the clean-input error**: if `Q` implements `P` within `δ`
on a clean work register and `S` acts as `P` on every slice of the spectator basis, `Q ⊗ 1_β`
implements `S` within `δ` on a clean work register. -/
theorem liftAct_clean (e : A ≃ α × β)
    (Q : EuclideanSpace ℂ (α × W) →L[ℂ] EuclideanSpace ℂ (α × W))
    (P : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)
    (S : EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (hS : ∀ u b, sliceLayout e (S u) b = P (sliceLayout e u b)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hQ : CleanErr (cleanPi (V := ℂ) w₀) Q P δ) :
    CleanErr (cleanPi (V := ℂ) w₀) (liftAct e Q) S δ := by
  intro u
  have hb : ∀ b, ‖actLayout e (liftAct e Q (cleanPi (V := ℂ) w₀ u) -
      cleanPi (V := ℂ) w₀ (S u)) b‖ ≤ δ * ‖sliceLayout e u b‖ := by
    intro b
    rw [map_sub, PiLp.sub_apply, actLayout_liftAct, actLayout_cleanPi, actLayout_cleanPi, hS]
    exact hQ _
  have hsq : ‖liftAct e Q (cleanPi (V := ℂ) w₀ u) - cleanPi (V := ℂ) w₀ (S u)‖ ^ 2 ≤
      (δ * ‖u‖) ^ 2 := by
    rw [← LinearIsometryEquiv.norm_map (actLayout e)
        (liftAct e Q (cleanPi (V := ℂ) w₀ u) - cleanPi (V := ℂ) w₀ (S u)),
      ← LinearIsometryEquiv.norm_map (sliceLayout e) u,
      PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb b) 2
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ (norm_nonneg _))).mp hsq

end Act

/-! ### The supplied source operations -/

section Source

variable {σ ι n : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype n]

/-- The weight preparation acts on the label: `((a, k), i) ↦ (a, (k, i))`. -/
def labelSplit : (σ × ι) × n ≃ σ × (ι × n) := Equiv.prodAssoc σ ι n

/-- The loader acts on the label and data registers: `((a, k), i) ↦ ((a, i), k)`. -/
def loadSplit : (σ × ι) × n ≃ (σ × n) × ι where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun q := ((q.1.1, q.2), q.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The exact label-controlled loader in basis coordinates**, `∑_a |a⟩⟨a| ⊗ L(a)` on the label
and data registers. -/
def ctrlL (L : σ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    EuclideanSpace ℂ (σ × n) →L[ℂ] EuclideanSpace ℂ (σ × n) :=
  (RegisterEquivalences.productFlatten σ n).conjStarAlgEquiv (WeightedClock.diagonal L)

omit [DecidableEq σ] in
theorem ctrlL_unitary {L : σ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n}
    (hL : ∀ a, IsUnitary (L a)) : IsUnitary (ctrlL L) :=
  (CoherentQuerySchedule.diagonal_unitary _ hL).transport _

omit [DecidableEq σ] in
theorem ctrlL_apply (L : σ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (v : EuclideanSpace ℂ (σ × n)) (a : σ) (i : n) :
    ctrlL L v (a, i) = L a ((RegisterEquivalences.productFlatten σ n).symm v a) i := rfl

omit [DecidableEq σ] in
/-- The label-controlled loaders move by at most the largest error of the loaded operations. -/
theorem norm_ctrlL_sub_le (J L : σ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) {δ : ℝ}
    (hδ : 0 ≤ δ) (h : ∀ a, ‖J a - L a‖ ≤ δ) : ‖ctrlL J - ctrlL L‖ ≤ δ := by
  have e : WeightedClock.diagonal J - WeightedClock.diagonal L =
      WeightedClock.diagonal (fun a => J a - L a) := by
    ext f a
    rfl
  rw [ctrlL, ctrlL, ← map_sub, e]
  exact (GeneralSourceExtensions.norm_conj_le _ _).trans
    (WeightedClock.norm_diagonal_le _ δ hδ h)

/-- The exact weight preparation of `GeneralSourceODE` acts on the label of every slice. -/
theorem slice_act (P : GeneralSourceODE.Weights.LabelOp σ)
    (u : EuclideanSpace ℂ ((σ × ι) × n)) (b : ι × n) :
    sliceLayout labelSplit
        ((ODEFinalNativeBasis.sourceLayout (σ := σ) (ι := ι) (n := n)).conjStarAlgEquiv
          (GeneralSourceODE.Weights.act P) u) b =
      P (sliceLayout labelSplit u b) := by
  apply PiLp.ext
  intro a
  rw [sliceLayout_apply]
  conv_rhs => rw [GeneralSourceODE.Weights.apply_eq_sum]
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  change (GeneralSourceODE.Weights.act P
      ((RegisterEquivalences.productFlatten (σ × ι) n).symm u)) (a, b.1) b.2 = _
  rw [GeneralSourceODE.Weights.act_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    RegisterEquivalences.productFlatten_symm_apply, sliceLayout_apply]
  rfl

omit [DecidableEq σ] in
/-- The exact loader of `GeneralSourceODE` acts on the label and data registers of every slice. -/
theorem slice_loader (L : σ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (u : EuclideanSpace ℂ ((σ × ι) × n)) (k : ι) :
    sliceLayout loadSplit
        ((ODEFinalNativeBasis.sourceLayout (σ := σ) (ι := ι) (n := n)).conjStarAlgEquiv
          (GeneralSourceODE.Weights.loader L) u) k =
      ctrlL L (sliceLayout loadSplit u k) := by
  apply PiLp.ext
  rintro ⟨a, i⟩
  rw [sliceLayout_apply, ctrlL_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  rfl

end Source

end

end SparseHamiltonian.CleanWorkODE
