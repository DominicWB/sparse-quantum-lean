import ODELowerBoundExtensions.Release.Access
import AdaptiveODELowerBound.Access.Control

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The general-mesh physical oracle: Boolean certificates for any family

Section `odel:sec:main` (access model; public location lists and source preparation) and the
construction before Theorem `odel:thm:joint` ("A value query computes one relevant membership bit,
writes the known entry and uncomputes the bit. It therefore uses at most two membership queries,
also for inverse and controlled calls. The initial and forcing states are known, so their
preparations need no membership queries").

`implementsOn_mesh` is the generic form, for any family `F` with any number of stages, of
`ODELowerBoundExtensions.Release.implementsOn_release_joint`: a Boolean implementation of the
sampled-time access `F.access (Label ι M × Fin M)` with costs `w` on an isometric encoding gives a
Boolean implementation of the release's physical oracle `meshOracle F σ ι N d J₀ J_b` along any
public placement `σ`, with costs `matrixWeight w` (`w` on matrix labels, `0` on the public source
labels), for the spectated Boolean family. The route is that of the released lemma: the placement
isometry (`ODELowerBoundExtensions.Release.implementsOn_stage`), the normal form
(`ODELowerBoundExtensions.Release.physicalOracle_normal_form`, through
`SparseLowerBounds.Adaptive.Access.implementsOn_spectate` and `implementsOn_conj`) and
`EncodedOracle.ImplementsOn.fixed` for the input-independent source labels.

It applies to the time-dependent hard families of the package with their released certificates:
the joint family (`SparseLowerBounds.ODE.implementsOn_joint`), the homogeneous family
(`ODELowerBoundExtensions.Homogeneous.implementsOn_hom`) and the padded joint families
(`ODELowerBoundExtensions.Padding.implementsOn_jointPad`).

`implementsOn_mesh_calls` is the analogue, for the physical oracle, of
`AdaptiveODELowerBound.Access.implementsOn_callFamily`: every call form of every physical label
(`AdaptiveODELowerBound.Access.callFamily`: plain, inverse, controlled
`MaskedProgram.masked (fun c => c)` and controlled inverse) is implemented on one isometric
encoding by at most `matrixWeight w` of its label queries of one Boolean phase oracle. With the
costs `hardCost` of the hard families, a controlled or controlled-inverse value call costs at most
two Boolean queries and a controlled location or source call none.
-/

namespace PhysicalODELowerBound.Access

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit TimeDependentExtensions
open ODELowerBoundExtensions.Release (meshOracle PublicSources SysOp)
open AdaptiveODELowerBound.Access (callFamily)
open scoped InnerProduct InnerProductSpace

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

/-- The placement isometry `stageEmbed Λ σ` followed by an isometric encoding of the family's
workspace is an isometry. -/
theorem stageEncoding_isometry {N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] {K M : ℕ} (σ : Fin M → Fin K) (Λ : Type) [Fintype Λ] {B : Type}
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    (Enc : Workspace (Λ × Fin M) N Z K →L[ℂ] B) (hEnc : Enc† ∘L Enc = 1) :
    (Enc ∘L ODELowerBoundExtensions.Release.stageEmbed Λ σ)† ∘L
      (Enc ∘L ODELowerBoundExtensions.Release.stageEmbed Λ σ) = 1 :=
  ODELowerBoundExtensions.Release.comp_isometry Enc hEnc _
    (ODELowerBoundExtensions.Release.stageEmbed_isometry Λ σ)

/-- **Boolean certificates pass to the general-mesh physical oracle**: if every label of the
sampled-time access of `F` with branch register `Label ι M × Fin M` is implemented on the
isometric encoding `Enc` by at most `w q` queries of the Boolean phase oracle
`x ↦ P.phase (y x)`, then along any placement `σ`, with public source interfaces, every label of
the physical oracle is implemented on one isometric encoding by at most `matrixWeight w` queries
of one Boolean phase oracle with the same query function `y`. -/
theorem implementsOn_mesh {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] {K s : ℕ} (F : Family X N Z K s) {M : ℕ} (σ : Fin M → Fin K) (ι : Type)
    [Fintype ι] [DecidableEq ι] (Nsl d : ℕ) {J₀ : X → SysOp N} {Jb : X → Fin M → SysOp N}
    (hJ : PublicSources J₀ Jb) {I B : Type} [Fintype I] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (P : ProjFamily B I) (y : X → I → Bool)
    (Enc : Workspace (TimeDependentODE.NativeSource.Label ι M × Fin M) N Z K →L[ℂ] B)
    (hEnc : Enc† ∘L Enc = 1) (w : Query → ℕ)
    (hw : ∀ q, EncodedOracle.ImplementsOn (fun x => P.phase (y x))
      (F.access (TimeDependentODE.NativeSource.Label ι M × Fin M) q) Enc (w q)) :
    ∃ (B' : Type) (_ : NormedAddCommGroup B') (_ : InnerProductSpace ℂ B') (_ : CompleteSpace B')
      (P' : ProjFamily B' I) (Enc' : MeshSource.PhysicalSpace ι N Z M Nsl d →L[ℂ] B'),
      Enc'† ∘L Enc' = 1 ∧ ∀ l, EncodedOracle.ImplementsOn (fun x => P'.phase (y x))
        (meshOracle F σ ι Nsl d J₀ Jb l) Enc' (ODESourceQueryBudget.matrixWeight w l) := by
  obtain ⟨Ω, hΩ, U, hU⟩ := ODELowerBoundExtensions.Release.physicalOracle_normal_form
    (ODELowerBoundExtensions.Release.stageData F.data σ) ι Nsl d J₀ Jb
  have hE₀ := stageEncoding_isometry σ (TimeDependentODE.NativeSource.Label ι M) Enc hEnc
  set E₀ := Enc ∘L ODELowerBoundExtensions.Release.stageEmbed
    (TimeDependentODE.NativeSource.Label ι M) σ
  set Uc := U.symm.symm.toLinearIsometry.toContinuousLinearMap
  have hUc : Uc† ∘L Uc = 1 := by
    refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      one_apply_eq_self]
    simp [Uc]
  have hEnc' := ODELowerBoundExtensions.Release.comp_isometry _
    (SparseLowerBounds.Adaptive.Access.jointMap_isometry Ω E₀ hE₀) Uc hUc
  have hPh : (fun x : X => (P.spectate Ω).phase (y x)) =
      fun x => Joint.fiber (fun _ : Ω => P.phase (y x)) :=
    funext fun x => SparseLowerBounds.Hamiltonian.HsRelease.phase_spectate Ω _ _
  refine ⟨_, inferInstance, inferInstance, inferInstance, P.spectate Ω,
    SparseLowerBounds.Adaptive.Access.jointMap Ω E₀ ∘L Uc, hEnc', fun l => ?_⟩
  rw [hPh]
  rcases l with q | b
  · have h1 := ODELowerBoundExtensions.Release.implementsOn_stage F σ
      (TimeDependentODE.NativeSource.Label ι M) Enc q (w q) (hw q)
    have h2 := SparseLowerBounds.Adaptive.Access.implementsOn_conj U.symm
      (SparseLowerBounds.Adaptive.Access.implementsOn_spectate Ω h1)
    exact h2.congr (fun x => (hU q x).symm)
  · by_cases hX : Nonempty X
    swap
    · exact ⟨OracleCircuit.Program.identity, fun x => (hX ⟨x⟩).elim, le_rfl⟩
    · obtain ⟨x₀⟩ := hX
      have hu := MeshSource.physicalOracle_unitary (ι := ι)
        (ODELowerBoundExtensions.Release.stageData F.data σ) Nsl d J₀ Jb
        hJ.initial_unitary hJ.forcing_unitary (Sum.inr b) x₀
      exact (EncodedOracle.ImplementsOn.fixed hEnc' _ hu).congr
        (fun x => ODELowerBoundExtensions.Release.physicalOracle_inr_const
          (ODELowerBoundExtensions.Release.stageData F.data σ) ι Nsl d hJ b x₀ x)

/-- **Call forms of the general-mesh physical oracle cost no more Boolean queries than the call**
(the construction before Theorem `odel:thm:joint`): under the hypotheses of `implementsOn_mesh`,
every call form of every label of the physical oracle (`callFamily`: plain, inverse, controlled and
controlled-inverse calls) is implemented on one isometric encoding by at most `matrixWeight w` of
its label queries of one Boolean phase oracle with the query function `y`. -/
theorem implementsOn_mesh_calls {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] {K s : ℕ} (F : Family X N Z K s) {M : ℕ} (σ : Fin M → Fin K) (ι : Type)
    [Fintype ι] [DecidableEq ι] (Nsl d : ℕ) {J₀ : X → SysOp N} {Jb : X → Fin M → SysOp N}
    (hJ : PublicSources J₀ Jb) {I B : Type} [Fintype I] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (P : ProjFamily B I) (y : X → I → Bool)
    (Enc : Workspace (TimeDependentODE.NativeSource.Label ι M × Fin M) N Z K →L[ℂ] B)
    (hEnc : Enc† ∘L Enc = 1) (w : Query → ℕ)
    (hw : ∀ q, EncodedOracle.ImplementsOn (fun x => P.phase (y x))
      (F.access (TimeDependentODE.NativeSource.Label ι M × Fin M) q) Enc (w q)) :
    ∃ (B' : Type) (_ : NormedAddCommGroup B') (_ : InnerProductSpace ℂ B') (_ : CompleteSpace B')
      (P' : ProjFamily B' I)
      (Enc' : Joint Bool (MeshSource.PhysicalSpace ι N Z M Nsl d) →L[ℂ] B'),
      Enc'† ∘L Enc' = 1 ∧ ∀ c, EncodedOracle.ImplementsOn (fun x => P'.phase (y x))
        (callFamily (meshOracle F σ ι Nsl d J₀ Jb) c) Enc'
        (ODESourceQueryBudget.matrixWeight w c.1) := by
  obtain ⟨B', _, _, _, P', Enc', hEnc', hw'⟩ :=
    implementsOn_mesh F σ ι Nsl d hJ P y Enc hEnc w hw
  exact ⟨_, inferInstance, inferInstance, inferInstance,
    AdaptiveODELowerBound.Access.callBoolean P', AdaptiveODELowerBound.Access.callEncoding Enc',
    AdaptiveODELowerBound.Access.callEncoding_isometry Enc' hEnc',
    fun c => AdaptiveODELowerBound.Access.implementsOn_callFamily P' y Enc'
      (meshOracle F σ ι Nsl d J₀ Jb)
      (MeshSource.physicalOracle_unitary (ι := ι)
        (ODELowerBoundExtensions.Release.stageData F.data σ)
        Nsl d J₀ Jb hJ.initial_unitary hJ.forcing_unitary)
      (ODESourceQueryBudget.matrixWeight w) hw' c⟩

end

end PhysicalODELowerBound.Access
