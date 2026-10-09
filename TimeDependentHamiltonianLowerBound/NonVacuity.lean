import TimeDependentHamiltonianLowerBound.Theta
import TimeDependentHamiltonianLowerBound.Trees

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Non-vacuity: the hypotheses of the lower bounds can be met

The lower bounds of this library are implications from the guarantees of an algorithm; this
module shows that the released time-dependent simulators of Theorem `hs:thm:time` and its
generalisations meet these hypotheses on the constant hard families, so that no statement is
vacuous.

**Class statements.** The released uniform-mesh theorem `TimeDependent.simulation` chooses its
program after the path (`∀ Hpath, ∃ γ p`), while `uniform_class_max` assumes one program that
meets the guarantee for every path of the class. With `β = δ_val = 0` every path of the class
of constant data agrees with the constant path on `[0, τ]` (`uniformGuarantee_of_zero`), so the
released simulators meet that hypothesis (`uniform_class_nonvacuous`, on every admissible
number of samples). The general-mesh and integrable-path theorems choose one program for all
paths of their classes, and their simulators meet the hypotheses of `mesh_class_max` and
`integrable_class_max` on every admissible mesh (`mesh_class_nonvacuous`,
`integrable_class_nonvacuous`).

**Adaptive algorithms.** A program meeting the uniform-mesh criterion on the constant path, run
once on the encoded input (`AdaptiveHamiltonianLowerBound.Single.tree`) and read through the
released `endpointReadout`, meets the hypotheses of the tree theorems (`single_tree_hyps`; for
the released simulators, with `exists_uniformSimulates`, and with `exists_meshSimulates` and
`endpoint_of_mesh`, the hypotheses of `main_max_tree_uniform` and `main_max_tree_mesh`). A
program over the released uniform-mesh family of constant data is transported, through the
normal form `uniform_normal_form`, to a program over the bare coherent sampled-time access
`coherentAccess Ω (constData D 1)` with the same guarantee (`access_of_uniform`), and a program
over any family to one over the plain call forms of that family, with a clean control register
(`plainLift`, `calls_of_access`); so the hypotheses of `main_max_tree_access` and
`main_max_tree_calls` can be met as well.
-/

namespace TimeDependentHamiltonianLowerBound

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseLowerBounds SparseLowerBounds.Hamiltonian SparseLowerBounds.Readout
open SparseLinearSystems.Protocol
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open TimeDependentExtensions (IsMesh)
open scoped InnerProduct InnerProductSpace

/-! ### The class statements -/

section Classes

variable {τ ε : ℝ} {s : ℕ}

set_option maxRecDepth 8192 in
/-- **The hypotheses of `uniform_class_max` can be met** (with `β = δ_val = 0`): for every number
`M` of samples with the mesh conditions `4 s τ ≤ M` and `9 (√s τ)³ ≤ ε M²`, the released
uniform-mesh simulators of the constant time, mixed and precision families (Theorem
`hs:thm:time`, `TimeDependent.simulation`), with their isometric clean inputs, meet the guarantee
for every path of the class (`uniformGuarantee_of_zero`). -/
theorem uniform_class_nonvacuous (h : HSRange τ s ε) {M : ℕ} (hMesh : 4 * s * (1 * τ) ≤ M)
    (hCayley : 9 * (Real.sqrt s * (1 * τ)) ^ 3 ≤ ε * (M : ℝ) ^ 2) :
    ∃ (γT γM γP : ℝ)
      (pT : MultiOracleCircuit.Program
        (TimeDependent.oracle (constData (timeData τ s h.s_ge) M) γT 1 τ ε))
      (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
        TimeDependent.Workspace (SearchIndex (timeN τ) (hsMu s) s)
          (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s M γT 1 τ ε)
      (pM : MultiOracleCircuit.Program
        (TimeDependent.oracle (constData (mixedMainData τ ε s h.s_ge) M) γM 1 τ ε))
      (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
        TimeDependent.Workspace (SearchIndex (precN τ ε) (hsMu s) s)
          (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s M γM 1 τ ε)
      (pP : MultiOracleCircuit.Program
        (TimeDependent.oracle (constData (precisionMainData τ ε s h.s_ge) M) γP 1 τ ε))
      (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
        TimeDependent.Workspace (ScalarIndex (precN τ ε) s) (Word (scalarBits (precN τ ε) s τ)) s
          M γP 1 τ ε),
      (ιT† ∘L ιT = 1 ∧ ∀ Hpath,
        UniformHyp (constData (timeData τ s h.s_ge) M) Hpath 1 τ 0 0 ε →
          UniformGuarantee pT.eval ιT Hpath τ ε) ∧
      (ιM† ∘L ιM = 1 ∧ ∀ Hpath,
        UniformHyp (constData (mixedMainData τ ε s h.s_ge) M) Hpath 1 τ 0 0 ε →
          UniformGuarantee pM.eval ιM Hpath τ ε) ∧
      (ιP† ∘L ιP = 1 ∧ ∀ Hpath,
        UniformHyp (constData (precisionMainData τ ε s h.s_ge) M) Hpath 1 τ 0 0 ε →
          UniformGuarantee pP.eval ιP Hpath τ ε) := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  have hεHalf : ε ≤ 1 / 2 := by linarith [h.eps_le]
  have hM : 0 < M := by
    have hs : (0 : ℝ) < 4 * s * (1 * τ) := by
      have : (32 : ℝ) ≤ s := by exact_mod_cast h.s_ge
      nlinarith [h.one_le_tau]
    exact_mod_cast hs.trans_le hMesh
  obtain ⟨hTi, hMi, hPi, -⟩ := hard_instances h
  obtain ⟨γT, -, -, -, pT, hT⟩ :=
    exists_uniformSimulates hTi hM hτ h.eps_pos hεHalf hMesh hCayley
  obtain ⟨γM, -, -, -, pM, hM'⟩ :=
    exists_uniformSimulates hMi hM hτ h.eps_pos hεHalf hMesh hCayley
  obtain ⟨γP, -, -, -, pP, hP⟩ :=
    exists_uniformSimulates hPi hM hτ h.eps_pos hεHalf hMesh hCayley
  exact ⟨γT, γM, γP, pT, _, pM, _, pP, _,
    ⟨hT.2.1, fun Hp hp => uniformGuarantee_of_zero _ _ _ hT.2.2.2 Hp hp⟩,
    ⟨hM'.2.1, fun Hp hp => uniformGuarantee_of_zero _ _ _ hM'.2.2.2 Hp hp⟩,
    ⟨hP.2.1, fun Hp hp => uniformGuarantee_of_zero _ _ _ hP.2.2.2 Hp hp⟩⟩

set_option maxRecDepth 8192 in
/-- **The hypotheses of `mesh_class_max` can be met** (generalisations after Theorem
`hs:thm:time`): on every mesh `t` of `[0, τ]` with `M > 0` intervals and every admissible slot
count `N`, the released general-mesh simulators of the constant time, mixed and precision
families (`TimeDependentExtensions.Hamiltonian.simulation`), with their isometric clean inputs,
meet the general-mesh guarantee for every path of the class. -/
theorem mesh_class_nonvacuous (h : HSRange τ s ε) {M : ℕ} {t : ℕ → ℝ} {Nsl : ℕ} (hM : 0 < M)
    (hmesh : IsMesh t M τ) (hN : 0 < Nsl) (hClock : 4 * s * (1 * τ) ≤ Nsl)
    (hCayley : 9 * (Real.sqrt s * (1 * τ)) ^ 3 ≤ ε * (Nsl : ℝ) ^ 2)
    (hRefine : 9 * M * (Real.sqrt s * (1 * τ)) ≤ ε * Nsl) :
    ∃ (γT γM γP : ℝ)
      (pT : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
        (constData (timeData τ s h.s_ge) M) Nsl γT 1 τ ε))
      (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
        TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (timeN τ) (hsMu s) s)
          (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s M Nsl γT 1 τ ε)
      (pM : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
        (constData (mixedMainData τ ε s h.s_ge) M) Nsl γM 1 τ ε))
      (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
        TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (precN τ ε) (hsMu s) s)
          (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s M Nsl γM 1 τ ε)
      (pP : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
        (constData (precisionMainData τ ε s h.s_ge) M) Nsl γP 1 τ ε))
      (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
        TimeDependentExtensions.Hamiltonian.Workspace (ScalarIndex (precN τ ε) s)
          (Word (scalarBits (precN τ ε) s τ)) s M Nsl γP 1 τ ε),
      (ιT† ∘L ιT = 1 ∧ MeshGuarantee pT.eval ιT (constData (timeData τ s h.s_ge) M) t τ ε) ∧
      (ιM† ∘L ιM = 1 ∧
        MeshGuarantee pM.eval ιM (constData (mixedMainData τ ε s h.s_ge) M) t τ ε) ∧
      (ιP† ∘L ιP = 1 ∧
        MeshGuarantee pP.eval ιP (constData (precisionMainData τ ε s h.s_ge) M) t τ ε) := by
  obtain ⟨hcT, hcM, hcP⟩ := mesh_class_members h hM hmesh hN hClock hCayley hRefine
  obtain ⟨γT, -, -, -, pT, -, hiT, -, hgT⟩ := hcT.simulation
  obtain ⟨γM, -, -, -, pM, -, hiM, -, hgM⟩ := hcM.simulation
  obtain ⟨γP, -, -, -, pP, -, hiP, -, hgP⟩ := hcP.simulation
  exact ⟨γT, γM, γP, pT, _, pM, _, pP, _, ⟨hiT, hgT⟩, ⟨hiM, hgM⟩, ⟨hiP, hgP⟩⟩

set_option maxRecDepth 8192 in
/-- **The hypotheses of `integrable_class_max` can be met** (generalisations after Theorem
`hs:thm:time`): on every mesh `t` of `[0, τ]` with `M > 0` intervals and every admissible slot
count `N`, the released simulators for integrable paths of the constant time, mixed and
precision families (`IntegrablePathSimulation.Hamiltonian.simulation`), with their isometric
clean inputs, meet the guarantee for every integrable path of the class. -/
theorem integrable_class_nonvacuous (h : HSRange τ s ε) {M : ℕ} {t : ℕ → ℝ} {Nsl : ℕ}
    (hM : 0 < M) (hmesh : IsMesh t M τ) (hN : 0 < Nsl) (hClock : 4 * s * (1 * τ) ≤ Nsl)
    (hCayley : 9 * (Real.sqrt s * (1 * τ)) ^ 3 ≤ ε * (Nsl : ℝ) ^ 2)
    (hRefine : 9 * M * (Real.sqrt s * (1 * τ)) ≤ ε * Nsl) :
    ∃ (γT γM γP : ℝ)
      (pT : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
        (constData (timeData τ s h.s_ge) M) Nsl γT 1 τ ε))
      (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
        TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (timeN τ) (hsMu s) s)
          (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s M Nsl γT 1 τ ε)
      (pM : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
        (constData (mixedMainData τ ε s h.s_ge) M) Nsl γM 1 τ ε))
      (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
        TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (precN τ ε) (hsMu s) s)
          (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s M Nsl γM 1 τ ε)
      (pP : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
        (constData (precisionMainData τ ε s h.s_ge) M) Nsl γP 1 τ ε))
      (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
        TimeDependentExtensions.Hamiltonian.Workspace (ScalarIndex (precN τ ε) s)
          (Word (scalarBits (precN τ ε) s τ)) s M Nsl γP 1 τ ε),
      (ιT† ∘L ιT = 1 ∧
        IntegrableGuarantee pT.eval ιT (constData (timeData τ s h.s_ge) M) t τ ε) ∧
      (ιM† ∘L ιM = 1 ∧
        IntegrableGuarantee pM.eval ιM (constData (mixedMainData τ ε s h.s_ge) M) t τ ε) ∧
      (ιP† ∘L ιP = 1 ∧
        IntegrableGuarantee pP.eval ιP (constData (precisionMainData τ ε s h.s_ge) M) t τ ε) := by
  obtain ⟨hcT, hcM, hcP⟩ := mesh_class_members h hM hmesh hN hClock hCayley hRefine
  obtain ⟨γT, -, -, -, pT, -, hiT, -, hgT⟩ := hcT.simulation_integrable
  obtain ⟨γM, -, -, -, pM, -, hiM, -, hgM⟩ := hcM.simulation_integrable
  obtain ⟨γP, -, -, -, pP, -, hiP, -, hgP⟩ := hcP.simulation_integrable
  exact ⟨γT, γM, γP, pT, _, pM, _, pP, _, ⟨hiT, hgT⟩, ⟨hiM, hgM⟩, ⟨hiP, hgP⟩⟩

end Classes

/-! ### Adaptive algorithms: one-trial trees -/

section Single

/-- **A program meeting the uniform-mesh criterion gives a one-trial tree meeting the adaptive
hypotheses** (Theorem `hsl:thm:main` for adaptive algorithms): run once on `ι ψ`
(`AdaptiveHamiltonianLowerBound.Single.tree`, flag space `ℂ`) and read through
`endpointReadout ι i₀`, it succeeds with probability one and its conditional output is
`ε`-accurate for `U(τ) ψ` for every propagator `U` of the constant path. -/
theorem single_tree_hyps {S X L Z : Type*} [Fintype S] [DecidableEq S] {s' : ℕ}
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [FiniteDimensional ℂ K]
    {O : L → X → K →L[ℂ] K} (hO : ∀ l x, IsUnitary (O l x)) (p : MultiOracleCircuit.Program O)
    (ι : EuclideanSpace ℂ S →L[ℂ] K) (hι : ι† ∘L ι = 1) (i₀ : S) (D : Data X S Z s')
    (hH : ∀ x, (D.matrix x).IsHermitian) {ψ : EuclideanSpace ℂ S} (hψ : ‖ψ‖ = 1) {τ ε : ℝ}
    (hτ : 0 ≤ τ) (hg : UniformGuarantee p.eval ι (constPath D) τ ε) :
    ∃ hφ : ‖ι ψ‖ = 1,
      (∀ x, 2 / 3 ≤ (AdaptiveHamiltonianLowerBound.Single.tree ℂ p (ι ψ) hφ).successMass x) ∧
      ∀ x, ∀ U : ℝ → (EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S), U 0 = 1 →
        TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator (constPath D x u)) U
          0 τ →
        DensityAccurate (endpointReadout ι i₀)
          ((AdaptiveHamiltonianLowerBound.Single.tree ℂ p (ι ψ) hφ).conditionalDensity x)
          (U τ ψ) ε := by
  have hφ : ‖ι ψ‖ = 1 := by rw [Reduction.norm_encode ι hι, hψ]
  obtain ⟨-, hacc⟩ := accurate_of_endpoint_program hO p ι hι i₀ hH hψ
    ((uniform_criterion_iff D p.eval ι hτ).1 hg)
  refine ⟨hφ, fun x => ?_, (densityAccurate_propagator_iff D _ _ ψ hτ).2 fun x => ?_⟩
  · rw [AdaptiveHamiltonianLowerBound.Single.successMass_tree p _ hφ x (p.eval_unitary hO x)]
    norm_num
  · rw [AdaptiveHamiltonianLowerBound.Single.conditionalDensity_tree p _ hφ x
      (p.eval_unitary hO x), AdaptiveHamiltonianLowerBound.densityAccurate_pure_iff]
    exact hacc x

end Single

/-! ### From the released uniform-mesh family to the bare coherent access -/

section Transport

/-- Evaluation is unchanged by transporting a program along an equality of oracle families. -/
theorem eval_cast {L X K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {O₁ O₂ : L → X → K →L[ℂ] K} (h : O₁ = O₂)
    (q : MultiOracleCircuit.Program O₁) (x : X) : (h ▸ q).eval x = q.eval x := by
  subst h
  rfl

/-- The relabelling `Ω ≃ Ω × Fin 1` of a spectator register. -/
def unitSlot (Ω K : Type*) [Fintype Ω] [NormedAddCommGroup K] [InnerProductSpace ℂ K] :
    Joint Ω K ≃ₗᵢ[ℂ] Joint (Ω × Fin 1) K :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ K (Equiv.prodUnique Ω (Fin 1)).symm

/-- `unitSlot` carries the spectator form over `Ω` to that over `Ω × Fin 1`. -/
theorem unitSlot_fiber (Ω K : Type*) [Fintype Ω] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (A : K →L[ℂ] K) :
    (unitSlot Ω K).conjStarAlgEquiv (Joint.fiber fun _ : Ω => A) =
      Joint.fiber fun _ : Ω × Fin 1 => A := by
  ext Ψ j
  rcases j with ⟨ω, r⟩
  have hr : r = 0 := Subsingleton.elim _ _
  subst hr
  simp [unitSlot, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, Equiv.piCongrLeft']

/-- **A program over the released uniform-mesh family of constant data gives a program over the
bare coherent sampled-time access** (eq. `hs:eq:timeaccess`): through the normal form
`uniform_normal_form` there are a finite branch register `Ω`, a program over
`coherentAccess Ω (constData D 1)` and an isometric encoding with the same evaluation up to a
fixed isometry, so the uniform-mesh criterion on the constant path is kept. -/
theorem access_of_uniform {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (D : Data X N Z s) (M : ℕ) (γ η t ε' : ℝ)
    (p : MultiOracleCircuit.Program (TimeDependent.oracle (constData D M) γ η t ε'))
    (ι : EuclideanSpace ℂ N →L[ℂ] TimeDependent.Workspace N Z s M γ η t ε')
    (hι : ι† ∘L ι = 1) {τ ε : ℝ} (hg : UniformGuarantee p.eval ι (constPath D) τ ε) :
    ∃ (Ω : Type) (_ : Fintype Ω)
      (q : MultiOracleCircuit.Program (coherentAccess Ω (constData D 1)))
      (ι' : EuclideanSpace ℂ N →L[ℂ] Joint (Ω × Fin 1) (SparseFlagEmbedding.Space (N × N) Z)),
      ι'† ∘L ι' = 1 ∧ UniformGuarantee q.eval ι' (constPath D) τ ε := by
  obtain ⟨Ω, hΩ, U, hU⟩ := uniform_normal_form D M γ η t ε'
  let W := U.trans (unitSlot Ω (SparseFlagEmbedding.Space (N × N) Z))
  have hfam : (fun l x => W.conjStarAlgEquiv (TimeDependent.oracle (constData D M) γ η t ε' l x))
      = coherentAccess Ω (constData D 1) := by
    funext l x
    rw [hU l x, coherentAccess_constData, LinearIsometryEquiv.conjStarAlgEquiv_trans]
    simp only [StarAlgEquiv.trans_apply]
    rw [← LinearIsometryEquiv.symm_conjStarAlgEquiv, StarAlgEquiv.apply_symm_apply]
    exact unitSlot_fiber Ω _ _
  let q : MultiOracleCircuit.Program (coherentAccess Ω (constData D 1)) := hfam ▸ p.transport W
  let ι' := W.toLinearIsometry.toContinuousLinearMap ∘L ι
  have hW : (W.toLinearIsometry.toContinuousLinearMap)† ∘L
      W.toLinearIsometry.toContinuousLinearMap = 1 :=
    (W.toLinearIsometry.toContinuousLinearMap.norm_map_iff_adjoint_comp_self).mp
      (fun v => W.norm_map v)
  refine ⟨Ω, hΩ, q, ι', ?_, ?_⟩
  · show (W.toLinearIsometry.toContinuousLinearMap ∘L ι)† ∘L
      (W.toLinearIsometry.toContinuousLinearMap ∘L ι) = 1
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc _ _ ι, hW]
    rw [show (1 : TimeDependent.Workspace N Z s M γ η t ε' →L[ℂ] _) ∘L ι = ι from by
      ext v; simp]
    exact hι
  · intro x U' hU0 hU'
    have heq : q.eval x ∘L ι' - ι' ∘L U' τ =
        W.toLinearIsometry.toContinuousLinearMap ∘L (p.eval x ∘L ι - ι ∘L U' τ) := by
      ext v : 1
      simp [q, ι', eval_cast, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
    rw [heq, LinearIsometry.norm_toContinuousLinearMap_comp]
    exact hg x U' hU0 hU'

end Transport

/-! ### Plain call forms -/

section Calls

/-- The clean control encoding `v ↦ |false⟩ ⊗ v`. -/
def boolEmbed (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] :
    K →L[ℂ] Joint Bool K :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Bool => K)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun b => if b = false then ContinuousLinearMap.id ℂ K else 0)

/-- Components of the clean control encoding. -/
theorem boolEmbed_apply {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (v : K) (b : Bool) : boolEmbed K v b = if b = false then v else 0 := by
  change (if b = false then ContinuousLinearMap.id ℂ K else 0) v = _
  split_ifs <;> rfl

/-- The clean control encoding is an isometry. -/
theorem boolEmbed_isometry (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] : (boolEmbed K)† ∘L boolEmbed K = 1 := by
  ext v
  refine ext_inner_left ℂ fun w => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    PiLp.inner_apply, Fintype.sum_bool]
  simp only [boolEmbed_apply]
  simp

/-- A program over `O` as a program over the plain call forms of `O`
(`AdaptiveODELowerBound.Access.callFamily`, control register a spectator). -/
def plainLift {L X W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    {O : L → X → W →L[ℂ] W} : MultiOracleCircuit.Program O →
      MultiOracleCircuit.Program (AdaptiveODELowerBound.Access.callFamily O)
  | .fixed U hU => .fixed (Joint.fiber fun _ : Bool => U)
      (PhaseCircuit.isUnitary_fiber _ fun _ => hU)
  | .query l => .query (l, .plain)
  | .queryAdjoint l => .queryAdjoint (l, .plain)
  | .seq p q => .seq (plainLift p) (plainLift q)

/-- The lifted program acts as the original one on both control branches. -/
theorem eval_plainLift {L X W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] {O : L → X → W →L[ℂ] W} (p : MultiOracleCircuit.Program O) (x : X) :
    (plainLift p).eval x = Joint.fiber fun _ : Bool => p.eval x := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l =>
      change star (Joint.fiber fun _ : Bool => O l x) = _
      rw [Joint.star_fiber]
      rfl
  | seq p q hp hq =>
      change (plainLift p).eval x * (plainLift q).eval x = _
      rw [hp, hq, Joint.fiber_mul]
      rfl

/-- **The plain call forms keep the uniform-mesh criterion**: with the clean control encoding,
the lifted program `plainLift q` meets the criterion on the constant path whenever `q` does. -/
theorem calls_of_access {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ} (D : Data X n Z s)
    {L W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    {O : L → X → W →L[ℂ] W} (q : MultiOracleCircuit.Program O) (ι : EuclideanSpace ℂ n →L[ℂ] W)
    (hι : ι† ∘L ι = 1) {τ ε : ℝ} (hg : UniformGuarantee q.eval ι (constPath D) τ ε) :
    (boolEmbed W ∘L ι)† ∘L (boolEmbed W ∘L ι) = 1 ∧
      UniformGuarantee (plainLift q).eval (boolEmbed W ∘L ι) (constPath D) τ ε := by
  refine ⟨?_, fun x U hU0 hU => ?_⟩
  · rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc _ _ ι, boolEmbed_isometry]
    rw [show (1 : W →L[ℂ] W) ∘L ι = ι from by ext v; simp]
    exact hι
  · have heq : (plainLift q).eval x ∘L (boolEmbed W ∘L ι) - (boolEmbed W ∘L ι) ∘L U τ =
        boolEmbed W ∘L (q.eval x ∘L ι - ι ∘L U τ) := by
      ext v b
      rw [eval_plainLift]
      cases b <;> simp [boolEmbed_apply]
    rw [heq]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hJ : ‖boolEmbed W‖ ≤ 1 :=
      SparseMatrixNorm.norm_le_one_of_adjoint_comp _ (boolEmbed_isometry W)
    calc ‖boolEmbed W‖ * ‖q.eval x ∘L ι - ι ∘L U τ‖ ≤ 1 * ‖q.eval x ∘L ι - ι ∘L U τ‖ :=
          mul_le_mul_of_nonneg_right hJ (norm_nonneg _)
      _ ≤ ε := by rw [one_mul]; exact hg x U hU0 hU

end Calls

end

end TimeDependentHamiltonianLowerBound
