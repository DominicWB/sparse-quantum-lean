import SparseLowerBounds.Helpers.Adaptive.Access.LiftProgram

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Boolean access certificates and their transport

The paper's Boolean reduction (proof of Theorem `qlsl:thm:main`) compiles a labelled
oracle family to Boolean one-hot queries through `EncodedOracle.ImplementsOn`
with per-label costs.
The release's linear-system algorithm does not query the native primitives
directly: its oracle family `SparseLinearSystems.Step.physOracle` wraps them in
spectator registers (`LookupFromBasisOracle.spectator`,
`NativeControlledOracle.oracle`), all-active branch masks
(`MaskedProgram.masked (fun _ => true)`, i.e. `1_ι ⊗ ·`) and fixed register
relabellings (`LinearIsometryEquiv.conjStarAlgEquiv` of
`RegisterEquivalences.productFlatten` and similar layouts), and adds the
controlled state preparation `U_b`.

This module packages a Boolean implementation of a whole labelled family as
`BooleanAccess n m O w` (a workspace, a projection family over
`Fin n × Fin m`, one isometric encoding, and `ImplementsOn` for every label
with cost `w l`) and shows that it survives the wrappers at the **same** cost:

* `implementsOn_conj`, `BooleanAccess.conj`: conjugating the logical family by
  a fixed unitary equivalence `V` (encoding `E ∘ V⁻¹`, same Boolean oracle);
* `implementsOn_spectate`, `implementsOn_spectate_oneHot`,
  `BooleanAccess.spectate`: an untouched spectator register `ℂ^Ω`
  (`1_Ω ⊗ O`, Boolean family `ProjFamily.spectate Ω`, encoding `jointMap Ω E`);
  the Boolean program is lifted gate by gate
  (`Helpers.Adaptive.Access.liftProgram`), with the same query count;
* `BooleanAccess.sumConst`: adjoining input-independent unitary labels
  (such as `U_b` for an input-independent right-hand side, Theorem `qlsl:thm:main`)
  at cost `0` (`EncodedOracle.ImplementsOn.fixed`).
-/

namespace SparseLowerBounds.Adaptive.Access

noncomputable section
set_option autoImplicit false
open SparseHamiltonian OracleCircuit
open scoped InnerProduct InnerProductSpace
open Helpers.CompileReduction Helpers.Adaptive.Access

variable {K K' K₂ : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
  [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]

/-! ### Spectator maps between different spaces -/

/-- `1_Ω ⊗ E` for a map `E : K → K'` (`Joint.fiber` is homogeneous). -/
def jointMap (Ω : Type*) [Fintype Ω] (E : K →L[ℂ] K') : Joint Ω K →L[ℂ] Joint Ω K' :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Ω => K')).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun ω => E ∘L Joint.proj ω)

omit [CompleteSpace K] [CompleteSpace K'] in
theorem jointMap_apply (Ω : Type*) [Fintype Ω] (E : K →L[ℂ] K') (Ψ : Joint Ω K) (ω : Ω) :
    jointMap Ω E Ψ ω = E (Ψ ω) := rfl

/-- `(1_Ω ⊗ E)† = 1_Ω ⊗ E†`. -/
theorem jointMap_adjoint (Ω : Type*) [Fintype Ω] (E : K →L[ℂ] K') :
    (jointMap Ω E)† = jointMap Ω (E†) := by
  rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [PiLp.inner_apply, jointMap_apply, ContinuousLinearMap.adjoint_inner_left]

/-- `1_Ω ⊗ E` is an isometry when `E` is. -/
theorem jointMap_isometry (Ω : Type*) [Fintype Ω] (E : K →L[ℂ] K') (hE : E† ∘L E = 1) :
    (jointMap Ω E)† ∘L jointMap Ω E = 1 := by
  rw [jointMap_adjoint]
  ext Ψ ω
  simpa only [ContinuousLinearMap.comp_apply, jointMap_apply,
    one_apply_eq_self] using DFunLike.congr_fun hE (Ψ ω)

omit [CompleteSpace K] [CompleteSpace K'] in
/-- A spectated gate after the spectated encoding: `(1 ⊗ A)(1 ⊗ E) = 1 ⊗ AE`. -/
theorem fiber_comp_jointMap (Ω : Type*) [Fintype Ω] (A : K' →L[ℂ] K') (E : K →L[ℂ] K') :
    Joint.fiber (fun _ : Ω => A) ∘L jointMap Ω E = jointMap Ω (A ∘L E) := by
  ext Ψ ω
  rfl

omit [CompleteSpace K] [CompleteSpace K'] in
/-- The spectated encoding after a spectated gate: `(1 ⊗ E)(1 ⊗ B) = 1 ⊗ EB`. -/
theorem jointMap_comp_fiber (Ω : Type*) [Fintype Ω] (E : K →L[ℂ] K') (B : K →L[ℂ] K) :
    jointMap Ω E ∘L Joint.fiber (fun _ : Ω => B) = jointMap Ω (E ∘L B) := by
  ext Ψ ω
  rfl

/-- The phase oracle of a spectated projection family is the spectated phase
oracle: `O_j(1_Ω ⊗ P) = 1_Ω ⊗ O_j(P)`. -/
theorem oneHotOracle_spectate {n m : ℕ} (Ω : Type*) [Fintype Ω]
    (P : ProjFamily K (Fin n × Fin m)) (j : Fin n → Fin m) :
    oneHotOracle (P.spectate Ω) j = Joint.fiber (fun _ : Ω => oneHotOracle P j) := by
  ext Ψ ω
  rw [Joint.fiber_apply, oneHotOracle_eq_hitProj, oneHotOracle_eq_hitProj]
  change Ψ ω - ((2 : ℂ) • hitProj (P.spectate Ω) j Ψ) ω = Ψ ω - (2 : ℂ) • hitProj P j (Ψ ω)
  rw [PiLp.smul_apply, hitProj_spectate_apply]

/-! ### Transport of `ImplementsOn` -/

variable {X : Type*}

/-- **Logical relabelling.** Conjugating the logical family by a fixed unitary
equivalence `V : K ≃ K₂` keeps the Boolean oracle and the cost; the encoding
becomes `E ∘ V⁻¹`. -/
theorem implementsOn_conj {Q : X → K' →L[ℂ] K'} {O : X → K →L[ℂ] K} {E : K →L[ℂ] K'} {c : ℕ}
    (V : K ≃ₗᵢ[ℂ] K₂) (h : EncodedOracle.ImplementsOn Q O E c) :
    EncodedOracle.ImplementsOn Q (fun x => V.conjStarAlgEquiv (O x))
      (E ∘L V.symm.toLinearIsometry.toContinuousLinearMap) c := by
  obtain ⟨p, hp, hc⟩ := h
  refine ⟨p, fun x => ?_, hc⟩
  ext v
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply]
  exact DFunLike.congr_fun (hp x) (V.symm v)

omit [CompleteSpace K] in
/-- **Spectator register.** A logical family acting on every copy of `ℂ^Ω`
is implemented by the spectated Boolean oracle, with the same cost, on the
encoding `1_Ω ⊗ E`. -/
theorem implementsOn_spectate (Ω : Type*) [Fintype Ω] {Q : X → K' →L[ℂ] K'}
    {O : X → K →L[ℂ] K} {E : K →L[ℂ] K'} {c : ℕ} (h : EncodedOracle.ImplementsOn Q O E c) :
    EncodedOracle.ImplementsOn (fun x => Joint.fiber (fun _ : Ω => Q x))
      (fun x => Joint.fiber (fun _ : Ω => O x)) (jointMap Ω E) c := by
  obtain ⟨p, hp, hc⟩ := h
  refine ⟨liftProgram Ω p, fun x => ?_, by rwa [count_liftProgram]⟩
  rw [eval_liftProgram, fiber_comp_jointMap, jointMap_comp_fiber, hp x]

omit [CompleteSpace K] in
/-- `implementsOn_spectate` for one-hot phase oracles, with the Boolean side
written as the phase oracle of `ProjFamily.spectate Ω`. -/
theorem implementsOn_spectate_oneHot {n m : ℕ} (Ω : Type*) [Fintype Ω]
    (P : ProjFamily K' (Fin n × Fin m)) {O : (Fin n → Fin m) → K →L[ℂ] K} {E : K →L[ℂ] K'}
    {c : ℕ} (h : EncodedOracle.ImplementsOn (oneHotOracle P) O E c) :
    EncodedOracle.ImplementsOn (oneHotOracle (P.spectate Ω))
      (fun x => Joint.fiber (fun _ : Ω => O x)) (jointMap Ω E) c := by
  have hQ : oneHotOracle (P.spectate Ω) =
      fun j => Joint.fiber (fun _ : Ω => oneHotOracle P j) :=
    funext (oneHotOracle_spectate Ω P)
  rw [hQ]
  exact implementsOn_spectate Ω h

/-! ### Boolean access certificates -/

/-- **A Boolean access certificate** for a labelled family `O` over the hidden
one-hot strings `Fin n → Fin m`: a Boolean workspace with a projection family
(phase form, `ProjFamily`), one isometric encoding of `O`'s workspace,
and an implementation of every label `l` by at most `w l` Boolean one-hot
queries. These are the hypotheses of the Boolean-cost bounds for one-hot inputs
(`Hamiltonian.time_general`, `Hamiltonian.mixed_general`). -/
structure BooleanAccess (n m : ℕ) {L : Type*} (O : L → (Fin n → Fin m) → K →L[ℂ] K)
    (w : L → ℕ) where
  /-- The Boolean workspace. -/
  Space : Type
  [instNormed : NormedAddCommGroup Space]
  [instInner : InnerProductSpace ℂ Space]
  [instComplete : CompleteSpace Space]
  /-- The Boolean one-hot oracle, in phase form. -/
  fam : ProjFamily Space (Fin n × Fin m)
  /-- The fixed isometric encoding of `O`'s workspace. -/
  enc : K →L[ℂ] Space
  enc_isometry : enc† ∘L enc = 1
  /-- Every label costs at most `w l` Boolean queries. -/
  impl : ∀ l, EncodedOracle.ImplementsOn (oneHotOracle fam) (O l) enc (w l)

attribute [instance] BooleanAccess.instNormed BooleanAccess.instInner BooleanAccess.instComplete

namespace BooleanAccess

variable {n m : ℕ} {L : Type*}

/-- A certificate from explicit data on a workspace in `Type`. -/
def ofImplementsOn {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    (P : ProjFamily B (Fin n × Fin m)) (E : K →L[ℂ] B) (hE : E† ∘L E = 1)
    {O : L → (Fin n → Fin m) → K →L[ℂ] K} {w : L → ℕ}
    (h : ∀ l, EncodedOracle.ImplementsOn (oneHotOracle P) (O l) E (w l)) : BooleanAccess n m O w where
  Space := B
  fam := P
  enc := E
  enc_isometry := hE
  impl := h

/-- Transport along a fixed unitary relabelling of the logical workspace
(`implementsOn_conj`). -/
def conj {O : L → (Fin n → Fin m) → K →L[ℂ] K} {w : L → ℕ} (A : BooleanAccess n m O w)
    (V : K ≃ₗᵢ[ℂ] K₂) :
    BooleanAccess n m (fun l x => V.conjStarAlgEquiv (O l x)) w where
  Space := A.Space
  fam := A.fam
  enc := A.enc ∘L V.symm.toLinearIsometry.toContinuousLinearMap
  enc_isometry := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc _ A.enc, A.enc_isometry, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp]
    exact LinearIsometry.adjoint_comp_self _
  impl l := implementsOn_conj V (A.impl l)

/-- Transport to an untouched spectator register `ℂ^Ω`
(`implementsOn_spectate_oneHot`). -/
def spectate {O : L → (Fin n → Fin m) → K →L[ℂ] K} {w : L → ℕ} (A : BooleanAccess n m O w)
    (Ω : Type) [Fintype Ω] :
    BooleanAccess n m (fun l x => Joint.fiber (fun _ : Ω => O l x)) w where
  Space := Joint Ω A.Space
  fam := A.fam.spectate Ω
  enc := jointMap Ω A.enc
  enc_isometry := jointMap_isometry Ω A.enc A.enc_isometry
  impl l := implementsOn_spectate_oneHot Ω A.fam (A.impl l)

/-- Adjoin input-independent unitary labels at cost `0`
(`EncodedOracle.ImplementsOn.fixed`). -/
def sumConst {O : L → (Fin n → Fin m) → K →L[ℂ] K} {w : L → ℕ} (A : BooleanAccess n m O w)
    {L' : Type*} (O' : L' → (Fin n → Fin m) → K →L[ℂ] K)
    (hconst : ∀ l' x x', O' l' x = O' l' x') (hU : ∀ l' x, IsUnitary (O' l' x)) :
    BooleanAccess n m (Sum.elim O O') (Sum.elim w fun _ => 0) where
  Space := A.Space
  fam := A.fam
  enc := A.enc
  enc_isometry := A.enc_isometry
  impl := by
    intro l
    cases l with
    | inl l => exact A.impl l
    | inr l' =>
      show EncodedOracle.ImplementsOn (oneHotOracle A.fam) (O' l') A.enc 0
      rcases isEmpty_or_nonempty (Fin n → Fin m) with hX | ⟨⟨x₀⟩⟩
      · exact ⟨Program.identity, fun x => isEmptyElim x, le_rfl⟩
      · exact (EncodedOracle.ImplementsOn.fixed A.enc_isometry (O' l' x₀) (hU l' x₀)).congr
          fun x => hconst l' x₀ x

/-- Pointwise equal families have the same certificate. -/
def congr {O O' : L → (Fin n → Fin m) → K →L[ℂ] K} {w : L → ℕ} (A : BooleanAccess n m O w)
    (h : ∀ l x, O l x = O' l x) : BooleanAccess n m O' w where
  Space := A.Space
  fam := A.fam
  enc := A.enc
  enc_isometry := A.enc_isometry
  impl l := (A.impl l).congr (h l)

/-- A certificate for larger costs. -/
def mono {O : L → (Fin n → Fin m) → K →L[ℂ] K} {w v : L → ℕ} (A : BooleanAccess n m O w)
    (h : ∀ l, w l ≤ v l) : BooleanAccess n m O v where
  Space := A.Space
  fam := A.fam
  enc := A.enc
  enc_isometry := A.enc_isometry
  impl l := (A.impl l).mono (h l)

end BooleanAccess

end

end SparseLowerBounds.Adaptive.Access
end
