import TimeDependentLowerBoundExtensions.Core.Assembly
import AdaptiveODELowerBound.Access.Control
import AdaptiveODELowerBound.Access.Admissible
import TimeDependentHamiltonianLowerBound.Adaptive

set_option autoImplicit false

/-!
# Masked calls, call forms and spectator wrappers of certified families

The manuscript's access (Section `hsl:sec:main`: the native access of Section `hs:sec:control`,
value queries and in-place locators "together with its inverse", controls by Lemma
`access:lem:control`) admits inverse and controlled calls. For Boolean certificates
(`SparseLowerBounds.Hamiltonian.HsRelease.PhaseAccess`) this module records three closure
properties, all with the **same** per-label weights:

* `implementsOn_masked`, `maskedAccess`: a call executed only in the branches of a fixed mask
  `m : ι → Bool` of a branch register (`SparseHamiltonian.MaskedProgram.masked m`), as
  `AdaptiveODELowerBound.Access.implementsOn_controlledForm` for the identity mask on `Bool`:
  the Boolean family `1_ι ⊗ |1⟩⟨1|_d ⊗ P_i` (`maskedBoolean`), the encoding
  `|c⟩ ⊗ v ↦ |c⟩ ⊗ |1⟩_d ⊗ Enc v` (`maskedEncoding`), the `d`-controlled program conjugated by
  the fixed alignment that sets `d = m c`;
* `callAccess`: all four call forms (`AdaptiveODELowerBound.Access.callFamily`: plain, inverse,
  controlled, controlled inverse), from `AdaptiveODELowerBound.Access.implementsOn_callFamily`;
* `nonempty_access_of_wrap`: spectator wrappers
  (`ODELowerBoundExtensions.Release.IsWrap`, `W A = U⁻¹ (1_Ω ⊗ A) U`).

`callFamily_conj` and `admissible_callFamily_of_normal_form` transport the call forms through
fixed layouts, for the adaptive forms.
-/

namespace TimeDependentLowerBoundExtensions.Core

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseLowerBounds SparseLowerBounds.Hamiltonian HsRelease
open AdaptiveODELowerBound.Access (callFamily CallForm formOp ctrlOp ctrlFamily activeEmbed
  callBoolean callEncoding)
open scoped InnerProduct InnerProductSpace

variable {B I : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-! ### Masked calls -/

/-- **The Boolean family of masked calls** on a branch register `ι`:
`1_ι ⊗ |1⟩⟨1|_d ⊗ P_i`. -/
def maskedBoolean (ι : Type*) [Fintype ι] (P : ProjFamily B I) :
    ProjFamily (Joint ι (Joint Bool B)) I :=
  (ctrlFamily P).spectate ι

/-- **The encoding of masked calls**: `|c⟩ ⊗ v ↦ |c⟩ ⊗ |1⟩_d ⊗ Enc v`. -/
def maskedEncoding (ι : Type*) [Fintype ι] (Enc : W →L[ℂ] B) :
    Joint ι W →L[ℂ] Joint ι (Joint Bool B) :=
  SparseLowerBounds.Adaptive.Access.jointMap ι (activeEmbed B ∘L Enc)

/-- The encoding of masked calls is isometric when `Enc` is. -/
theorem maskedEncoding_isometry (ι : Type*) [Fintype ι] (Enc : W →L[ℂ] B)
    (hEnc : Enc† ∘L Enc = 1) : (maskedEncoding ι Enc)† ∘L maskedEncoding ι Enc = 1 := by
  have hA : (activeEmbed B ∘L Enc)† ∘L (activeEmbed B ∘L Enc) = 1 := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc ((activeEmbed B)†),
      AdaptiveODELowerBound.Access.activeEmbed_isometry, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp, hEnc]
  exact SparseLowerBounds.Adaptive.Access.jointMap_isometry ι _ hA

omit [CompleteSpace W] in
/-- **Masked calls cost no more Boolean queries than the call**: if `F` is implemented on `Enc`
by at most `q` queries of `x ↦ P.phase (y x)`, then for every mask `m : ι → Bool` the masked
call `MaskedProgram.masked m (F x)` is implemented on `maskedEncoding ι Enc` by at most `q`
queries of `x ↦ (maskedBoolean ι P).phase (y x)`. -/
theorem implementsOn_masked [Fintype I] (ι : Type*) [Fintype ι] (m : ι → Bool)
    (P : ProjFamily B I) {X : Type*} (y : X → I → Bool) {Enc : W →L[ℂ] B}
    {F : X → W →L[ℂ] W} {q : ℕ}
    (h : EncodedOracle.ImplementsOn (fun x => P.phase (y x)) F Enc q) :
    EncodedOracle.ImplementsOn (fun x => (maskedBoolean ι P).phase (y x))
      (fun x => MaskedProgram.masked m (F x)) (maskedEncoding ι Enc) q := by
  have hQ : (fun x => (maskedBoolean ι P).phase (y x)) = fun x =>
      Joint.fiber fun _ : ι => MaskedProgram.masked (fun d : Bool => d) (P.phase (y x)) :=
    funext fun x => by
      rw [maskedBoolean, phase_spectate, AdaptiveODELowerBound.Access.phase_ctrlFamily]
      rfl
  rw [hQ]
  obtain ⟨p, hp, hc⟩ := h
  have hp' : ∀ x v, p.eval x (Enc v) = Enc (F x v) := fun x v =>
    DFunLike.congr_fun (hp x) v
  have hA : IsUnitary (Joint.fiber fun c : ι =>
      if m c then (1 : Joint Bool B →L[ℂ] Joint Bool B)
      else AdaptiveODELowerBound.Access.flipD B) :=
    PhaseCircuit.isUnitary_fiber _ fun c => by
      split
      · exact ⟨by simp, by simp⟩
      · exact AdaptiveODELowerBound.Access.flipD_unitary
  refine ⟨.seq (.fixed _ hA)
    (.seq (Helpers.Adaptive.Access.liftProgram ι (MaskedProgram.compile (fun d : Bool => d) p))
      (.fixed _ hA)), fun x => ?_, ?_⟩
  · rw [Program.eval_seq, Program.eval_seq, Program.eval_fixed,
      Helpers.Adaptive.Access.eval_liftProgram, MaskedProgram.compile_eval]
    ext Ψ c d
    rcases hm : m c with _ | _ <;> cases d <;>
      simp [maskedEncoding, Adaptive.Access.jointMap_apply,
        AdaptiveODELowerBound.Access.activeEmbed_apply, hp', hm,
        Joint.fiber_apply, AdaptiveODELowerBound.Access.flipD_apply]
  · simpa only [Program.count_seq, Program.count_fixed, Helpers.Adaptive.Access.count_liftProgram,
      MaskedProgram.compile_count, zero_add, add_zero] using hc

/-- **Certificate of a masked family**: the masked calls `MaskedProgram.masked m (O l x)` of a
certified family, same weights. -/
def maskedAccess [Fintype I] {X : Type*} {y : X → I → Bool} {L : Type*} {O : L → X → W →L[ℂ] W}
    {w : L → ℕ} (A : PhaseAccess I y O w) (ι : Type) [Fintype ι] (m : ι → Bool) :
    PhaseAccess I y (fun l x => MaskedProgram.masked m (O l x)) w :=
  PhaseAccess.ofImplementsOn (maskedBoolean ι A.fam) (maskedEncoding ι A.enc)
    (maskedEncoding_isometry ι A.enc A.enc_isometry)
    (fun l => implementsOn_masked ι m A.fam y (A.impl l))

/-! ### Call forms -/

/-- **Certificate of the call forms**: every call form of every label of a certified unitary
family (`callFamily O`, labels `L × CallForm`) with the weight of its label
(`AdaptiveODELowerBound.Access.implementsOn_callFamily`). -/
def callAccess [Fintype I] {X : Type*} {y : X → I → Bool} {L : Type*} {O : L → X → W →L[ℂ] W}
    {w : L → ℕ} (A : PhaseAccess I y O w) (hO : ∀ l x, IsUnitary (O l x)) :
    PhaseAccess I y (callFamily O) (fun c => w c.1) :=
  PhaseAccess.ofImplementsOn (callBoolean A.fam) (callEncoding A.enc)
    (AdaptiveODELowerBound.Access.callEncoding_isometry A.enc A.enc_isometry)
    (AdaptiveODELowerBound.Access.implementsOn_callFamily A.fam y A.enc O hO w A.impl)

/-- **Call forms commute with fixed layouts**: the call forms of `V⁻¹ O V` are the call forms
of `O` conjugated by `1_Bool ⊗ V`. -/
theorem callFamily_conj {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {L X : Type*} (O : L → X → K →L[ℂ] K) (V : W ≃ₗᵢ[ℂ] K)
    (c : L × CallForm) (x : X) :
    callFamily (fun l x => V.symm.conjStarAlgEquiv (O l x)) c x =
      (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Bool => V)).symm.conjStarAlgEquiv
        (callFamily O c x) := by
  obtain ⟨l, f⟩ := c
  have hs : star (V.symm.conjStarAlgEquiv (O l x)) = V.symm.conjStarAlgEquiv (star (O l x)) :=
    (map_star _ _).symm
  ext Ψ b
  cases f <;> cases b <;>
    simp [callFamily, formOp, ctrlOp, hs, Joint.fiber_apply, MaskedProgram.masked_apply,
      LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.piLpCongrRight_symm,
      LinearIsometryEquiv.piLpCongrRight_apply]

/-- **Admissibility of the call forms of a normal form**: if every label of `O` is
`U⁻¹ (1_Ω ⊗ oracles D l x) U`, every call form is admissible with the value-query weight of
its label (for data with input-independent locators). -/
theorem admissible_callFamily_of_normal_form {X N Z : Type} [Fintype N] [DecidableEq N]
    [Fintype Z] [AddCommGroup Z] {s : ℕ} (D : Data X N Z s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x') {O : Query → X → W →L[ℂ] W}
    (hO : ∃ (Ω : Type) (_ : Fintype Ω)
      (U : W ≃ₗᵢ[ℂ] Joint Ω (SparseFlagEmbedding.Space (N × N) Z)),
      ∀ l x, O l x = U.symm.conjStarAlgEquiv (specOracles Ω D l x))
    (c : Query × CallForm) :
    AdaptiveHamiltonianLowerBound.Access.Admissible D (callFamily O c)
      (AdaptiveHamiltonianLowerBound.Access.valueWeight c.1) := by
  obtain ⟨Ω, _, U, hU⟩ := hO
  have hO' : O = fun l x => U.symm.conjStarAlgEquiv (specOracles Ω D l x) :=
    funext fun l => funext fun x => hU l x
  have hc : callFamily O c = fun x =>
      (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Bool => U)).symm.conjStarAlgEquiv
        (callFamily (specOracles Ω D) c x) := by
    rw [hO']
    exact funext fun x => callFamily_conj (specOracles Ω D) U c x
  rw [hc]
  exact TimeDependentHamiltonianLowerBound.admissible_conj
    (AdaptiveODELowerBound.Access.admissible_callFamily_spec Ω D hrow hcol c) _

/-! ### Spectator wrappers -/

/-- **Spectator wrappers keep certificates**: if `W` is a spectator wrapper
(`W A = U⁻¹ (1_Ω ⊗ A) U`), every certificate of `F` gives one of `W ∘ F`, same weights. For
`F = oracles D` this is `Core.nonempty_access_of_normal_form`. -/
theorem nonempty_access_of_wrap {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {Wr : (W →L[ℂ] W) → (K →L[ℂ] K)}
    (hW : ODELowerBoundExtensions.Release.IsWrap Wr) [Fintype I] {X : Type*} {y : X → I → Bool}
    {L : Type*} {F : L → X → W →L[ℂ] W} {w : L → ℕ} (A : PhaseAccess I y F w) :
    Nonempty (PhaseAccess I y (fun l x => Wr (F l x)) w) := by
  obtain ⟨Ω, _, U, hU⟩ := hW
  exact ⟨((A.spectate Ω).conj U.symm).congr (fun l x => (hU _).symm)⟩

end

end TimeDependentLowerBoundExtensions.Core
