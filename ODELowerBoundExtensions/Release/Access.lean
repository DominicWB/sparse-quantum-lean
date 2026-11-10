import ODELowerBoundExtensions.Release.Normal
import AdaptiveHamiltonianLowerBound.Cost
import SparseLowerBounds.Adaptive.Access
import SparseLowerBounds.Helpers.HsRelease.PhaseAccess

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The release's oracle on the hard families: certificates

Manuscript: Section `odel:sec:main` (access model; public source preparation), for the
release's physical oracle `meshOracle F σ` (`Release/Normal`) on the hard families along **any**
public placement `σ` of mesh pieces into stages (the released runs use the uniform refinement
`releaseOracle F R = meshOracle F (stageOf K R)`). Two kinds of certificates are needed, both
transported through the normal form `physicalOracle_normal_form` (`U⁻¹ (1_Ω ⊗ ·) U`, same
per-label costs):

* **`g = 1` families** (`hamFamily D`, the mixed, precision and time families): search-weight
  growth `AdaptiveHamiltonianLowerBound.SearchGrowth` with the value-query weight
  `matrixWeight valueWeight` (`valueWeight` on matrix labels, `0` on source labels)
  (`searchGrowth_release_ham`). The access of `hamFamily D` along `σ` is the spectated native
  access `specOracles (ι × Fin M) D` (`stageAccess_hamFamily`), admissible with `valueWeight`
  (`Access.admissible_specOracles`), hence of search-weight growth (`searchGrowth_admissible`);
  growth passes through fixed isometries and spectators (`searchGrowth_conj_fiber`, from
  `wgrowth_conj` and `wgrowth_diagonal`); public source labels are input-independent unitaries
  (growth `1`).
* **Joint family**: a Boolean implementation by the membership phase oracle with costs
  `matrixWeight hardCost` (`hardCost` on matrix labels, `0` on source labels)
  (`implementsOn_release_joint`), from the certificate `implementsOn_joint` of `ODE/JointCompile`,
  transported along the placement (`implementsOn_stage`), through the normal form
  (`Adaptive.Access.implementsOn_spectate`, `implementsOn_conj`, the Boolean family
  `ProjFamily.spectate`), and with `EncodedOracle.ImplementsOn.fixed` for the public source labels.
-/

namespace ODELowerBoundExtensions.Release

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit TimeDependentExtensions
open AdaptiveHamiltonianLowerBound (SearchGrowth)
open scoped InnerProduct InnerProductSpace

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

/-- **Search-weight growth passes through fixed isometries and spectators**: if `O` has growth
`w`, so has `U⁻¹ (1_Ω ⊗ O) U`. -/
theorem searchGrowth_conj_fiber {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {m : ℕ}
    {K K' L : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
    (Ω : Type*) [Fintype Ω] (U : K' ≃ₗᵢ[ℂ] Joint Ω K) (O : L → (ι' → Fin m) → K →L[ℂ] K)
    (w : L → ℕ) (h : SearchGrowth m O w) :
    SearchGrowth m (fun l j => U.symm.conjStarAlgEquiv (Joint.fiber (fun _ : Ω => O l j))) w := by
  intro a ha l
  have hd : ∀ (P : (ι' → Fin m) → K →L[ℂ] K) (C : ℝ),
      AdaptiveHamiltonianLowerBound.WGrowth (SparseLowerBounds.SearchWeight.w m a) P C →
      AdaptiveHamiltonianLowerBound.WGrowth (SparseLowerBounds.SearchWeight.w m a)
        (fun j => U.symm.conjStarAlgEquiv (Joint.fiber (fun _ : Ω => P j))) C := by
    intro P C hP
    have h1 := AdaptiveHamiltonianLowerBound.wgrowth_diagonal (S := Ω)
      (SparseLowerBounds.SearchWeight.w m a) (fun _ => P) C (fun _ => hP)
    have hfib : ∀ Q : K →L[ℂ] K, WeightedClock.diagonal (fun _ : Ω => Q) =
        Joint.fiber (fun _ : Ω => Q) := fun Q => by ext Ψ i; rfl
    simp only [hfib] at h1
    exact AdaptiveHamiltonianLowerBound.wgrowth_conj _ U.symm _ C h1
  refine ⟨hd _ _ (h a ha l).1, ?_⟩
  refine AdaptiveHamiltonianLowerBound.wgrowth_congr (hd _ _ (h a ha l).2) (fun j => ?_)
  beta_reduce
  rw [← map_star, Joint.star_fiber]

/-- **The access of a `g = 1` family along a placement is the spectated native access**: every
piece reads the same Hamiltonian data. -/
theorem stageAccess_hamFamily {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] {s : ℕ} (D : Data X N Z s) (T : ℝ) (hT : 0 ≤ T)
    (x₀ : EuclideanSpace ℂ N) {M : ℕ} (σ : Fin M → Fin 1) (ι : Type*) [Fintype ι] (l : Query)
    (x : X) :
    stageAccess (hamFamily D T hT x₀) σ ι l x = specOracles (ι × Fin M) D l x := by
  ext Ψ b : 2
  cases l <;> rfl

/-- **The release's oracle on a `g = 1` family has search-weight growth** along any placement `σ`,
with the value-query weight `matrixWeight valueWeight` (`valueWeight` on matrix labels, `0` on
public source labels), along any map `g` of one-hot inputs into the data's inputs satisfying
`Access.HardAccess` (`g = id` for the time and mixed families, `g = toBits` for the precision
family). -/
theorem searchGrowth_release_ham {n m : ℕ} (hm : Even m) {X N Z : Type} [Fintype N]
    [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (D : Data X N Z s)
    (g : (Fin n → Fin m) → X) (hD : AdaptiveHamiltonianLowerBound.Access.HardAccess D g)
    (T : ℝ) (hT : 0 ≤ T) (x₀ : EuclideanSpace ℂ N) {M : ℕ} (σ : Fin M → Fin 1) (ι : Type)
    [Fintype ι] [DecidableEq ι] (Nsl d : ℕ) {J₀ : X → SysOp N} {Jb : X → Fin M → SysOp N}
    (hJ : PublicSources J₀ Jb) :
    SearchGrowth m (fun l j => meshOracle (hamFamily D T hT x₀) σ ι Nsl d J₀ Jb l (g j))
      (ODESourceQueryBudget.matrixWeight AdaptiveHamiltonianLowerBound.Access.valueWeight) := by
  intro a ha l
  rcases l with q | b
  · obtain ⟨Ω, hΩ, U, hU⟩ :=
      physicalOracle_normal_form (stageData (hamFamily D T hT x₀).data σ) ι Nsl d J₀ Jb
    have hspec : SearchGrowth m (fun (q : Query) j =>
        specOracles (TimeDependentODE.NativeSource.Label ι M × Fin M) D q (g j))
        AdaptiveHamiltonianLowerBound.Access.valueWeight :=
      AdaptiveHamiltonianLowerBound.searchGrowth_admissible hm D g hD _ _
        (fun q => AdaptiveHamiltonianLowerBound.Access.admissible_specOracles _ D hD.row_const
          hD.column_const q)
    have hc := searchGrowth_conj_fiber Ω U _ _ hspec a ha q
    have heq : ∀ j, meshOracle (hamFamily D T hT x₀) σ ι Nsl d J₀ Jb (Sum.inl q) (g j) =
        U.symm.conjStarAlgEquiv (Joint.fiber fun _ : Ω =>
          specOracles (TimeDependentODE.NativeSource.Label ι M × Fin M) D q (g j)) := by
      intro j
      have hs := stageAccess_hamFamily D T hT x₀ σ (TimeDependentODE.NativeSource.Label ι M) q
        (g j)
      dsimp only [stageAccess] at hs
      rw [meshOracle, hU, hs]
    exact ⟨AdaptiveHamiltonianLowerBound.wgrowth_congr hc.1 (fun j => (heq j).symm),
      AdaptiveHamiltonianLowerBound.wgrowth_congr hc.2 (fun j => by beta_reduce; rw [heq j])⟩
  · have hu := MeshSource.physicalOracle_unitary (ι := ι)
      (stageData (hamFamily D T hT x₀).data σ) Nsl d J₀ Jb hJ.initial_unitary
      hJ.forcing_unitary (Sum.inr b)
    have hc := physicalOracle_inr_const (stageData (hamFamily D T hT x₀).data σ) ι Nsl d hJ b
    show AdaptiveHamiltonianLowerBound.WGrowth _ _ ((AdaptiveHamiltonianLowerBound.searchLam m a ^ 2) ^ 0) ∧
      AdaptiveHamiltonianLowerBound.WGrowth _ _ ((AdaptiveHamiltonianLowerBound.searchLam m a ^ 2) ^ 0)
    rw [pow_zero]
    refine ⟨AdaptiveHamiltonianLowerBound.Access.wgrowth_const_of_eq _ _
        (fun j j' => hc (g j) (g j'))
        (fun j v => LinearSystemLowerBound.isUnitary_norm (hu (g j)) v),
      AdaptiveHamiltonianLowerBound.Access.wgrowth_const_of_eq _ _
        (fun j j' => by simp only [meshOracle]; rw [hc (g j) (g j')])
        (fun j v => LinearSystemLowerBound.isUnitary_norm (hu (g j)).adjoint v)⟩

/-- A composition of isometries is an isometry, with each isometry hypothesis next to its map.
This restates the released `SparseHamiltonian.UnitaryDilationTransfer.comp_isometry`
(`SparseHamiltonian/UnitaryImplementation.lean`) and is proved by
`NativeSparseAttenuation.isometry_comp`. It is kept because `UnitaryImplementation` is outside
this module's import closure: importing it and calling `UnitaryDilationTransfer.comp_isometry`
at the two uses in `implementsOn_release_joint` made that theorem fail with deterministic
heartbeat timeouts (`isDefEq` and `whnf`), while this wrapper elaborates within the default
budget. -/
theorem comp_isometry {K₁ K₂ K₃ : Type*} [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁]
    [CompleteSpace K₁] [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]
    [NormedAddCommGroup K₃] [InnerProductSpace ℂ K₃] [CompleteSpace K₃] (A : K₂ →L[ℂ] K₃)
    (hA : A† ∘L A = 1) (B : K₁ →L[ℂ] K₂) (hB : B† ∘L B = 1) :
    (A ∘L B)† ∘L (A ∘L B) = 1 :=
  NativeSparseAttenuation.isometry_comp B A hB hA

/-- **The release's oracle on the joint family is implemented by membership queries** along any
placement `σ`: an isometric encoding into a Boolean workspace with a projection family over
`Fin M × Fin n × Fin 2^μ` such that every matrix label costs `hardCost` (two per value call, none
per location call) and every public source label costs `0` (`matrixWeight hardCost`). -/
theorem implementsOn_release_joint {M n μ s : ℕ} (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s) {T : ℝ}
    (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T) {M' : ℕ} (σ : Fin M' → Fin (n + 2)) (ι : Type)
    [Fintype ι] [DecidableEq ι] (Nsl d : ℕ) {J₀ : Promised M n (2 ^ μ) → SysOp (JointIndex M μ s)}
    {Jb : Promised M n (2 ^ μ) → Fin M' → SysOp (JointIndex M μ s)}
    (hJ : PublicSources J₀ Jb) :
    ∃ (B : Type) (_ : NormedAddCommGroup B) (_ : InnerProductSpace ℂ B) (_ : CompleteSpace B)
      (P : ProjFamily B (Fin M × Fin n × Fin (2 ^ μ)))
      (Enc : MeshSource.PhysicalSpace ι (JointIndex M μ s) (Hamiltonian.Word μ) M' Nsl d →L[ℂ] B),
      Enc† ∘L Enc = 1 ∧ ∀ l, EncodedOracle.ImplementsOn (fun x => P.phase (membership x))
        (meshOracle (jointFamily M n μ s hμ hμs T hT) σ ι Nsl d J₀ Jb l) Enc
        (ODESourceQueryBudget.matrixWeight hardCost l) := by
  set F := jointFamily M n μ s hμ hμs T hT
  set Λ := TimeDependentODE.NativeSource.Label ι M'
  obtain ⟨Ω, hΩ, U, hU⟩ := physicalOracle_normal_form (stageData F.data σ) ι Nsl d J₀ Jb
  set E₀ := ancillaEmbed (Workspace (Λ × Fin M') (JointIndex M μ s) (Hamiltonian.Word μ) (n + 2))
    ∘L stageEmbed Λ σ
  have hE₀ : E₀† ∘L E₀ = 1 :=
    comp_isometry _ ancillaEmbed_isometry _ (stageEmbed_isometry Λ σ)
  set Uc := U.symm.symm.toLinearIsometry.toContinuousLinearMap
  have hUc : Uc† ∘L Uc = 1 := by
    refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      one_apply_eq_self]
    simp [Uc]
  have hEnc := comp_isometry _ (SparseLowerBounds.Adaptive.Access.jointMap_isometry Ω E₀ hE₀)
    Uc hUc
  have hPh : (fun x : Promised M n (2 ^ μ) =>
      ((jointBoolean (Λ × Fin M') M n μ s).spectate Ω).phase (membership x)) =
      fun x => Joint.fiber (fun _ : Ω => (jointBoolean (Λ × Fin M') M n μ s).phase
        (membership x)) :=
    funext fun x => SparseLowerBounds.Hamiltonian.HsRelease.phase_spectate Ω _ _
  refine ⟨_, inferInstance, inferInstance, inferInstance,
    (jointBoolean (Λ × Fin M') M n μ s).spectate Ω,
    SparseLowerBounds.Adaptive.Access.jointMap Ω E₀ ∘L Uc, hEnc, fun l => ?_⟩
  rw [hPh]
  rcases l with q | b
  · have h1 := implementsOn_stage F σ Λ _ q (hardCost q)
      (implementsOn_joint (Λ × Fin M') hμ hμs T hT q)
    have h2 := SparseLowerBounds.Adaptive.Access.implementsOn_conj U.symm
      (SparseLowerBounds.Adaptive.Access.implementsOn_spectate Ω h1)
    exact h2.congr (fun x => (hU q x).symm)
  · by_cases hX : Nonempty (Promised M n (2 ^ μ))
    swap
    · exact ⟨OracleCircuit.Program.identity, fun x => (hX ⟨x⟩).elim, le_rfl⟩
    · obtain ⟨x₀⟩ := hX
      have hu := MeshSource.physicalOracle_unitary (ι := ι) (stageData F.data σ) Nsl d J₀ Jb
        hJ.initial_unitary hJ.forcing_unitary (Sum.inr b) x₀
      exact (EncodedOracle.ImplementsOn.fixed hEnc _ hu).congr
        (fun x => physicalOracle_inr_const (stageData F.data σ) ι Nsl d hJ b x₀ x)

end

end ODELowerBoundExtensions.Release
