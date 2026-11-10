import DysonSingleProgram.Accuracy

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# A single heralded program from an amplified trial family

Manuscript: Section `odel:sec:main` (output model) and the proof of Lemma
`odel:lem:dyson`. The single-program class of the ODE lower
bounds is `SparseLowerBounds.ODE.Solver`: one program over the sampled-time access
`Family.access ι` (any branch register `ι`), a seed of norm at most one, an isometric readout
onto system ⊗ garbage, and a herald projection with success at least `2/3` and conditional
accuracy `ε` (`Readout.HeraldedAccurate`).

* `adjoint_comp_isometryEquiv_apply`, `outObs_comp_isometryEquiv_apply`,
  `comp_isometryEquiv_isometry`, `heraldedAccurate_isometryEquiv`,
  `isStarProjection_conj_isometryEquiv`: readout, herald and heralded accuracy are invariant under
  a fixed relabelling of the workspace;
* `Stage.toAccessProg`: a stage's program over the main attempt register (oracle `F.access ι`,
  spectators `I` and the cutoff label) as a program over `F.access (ι × (I × Fin M))`
  (`Register.reflatten`, `Register.toAccess`), with the fixed layout `Stage.layout`;
* `exists_solver_of_stage`: a stage with a unit seed, a herald projection, an isometric
  readout, success at least `2/3` and heralded accuracy on every solution is a `Solver` with the
  same program;
* `exists_solver_of_good`: a stage reproducing a released protocol (`Stage.Good`) with success
  mass at least `2/3` and `2ε`-accurate conditional expectations is a `Solver`;
* `fourAttempts`: the four-attempt stage with coherent cutoffs (`Coherent.trial`,
  `Parallel.Stage.four`) of a preparation;
* `exists_solver_of_shape`: for a trial family `q` with the amplification shape of a
  preparation `a` over `F.access ι` and the released complete certificate on every instance,
  the program of `fourAttempts` is the program of a `Solver` making at most
  `4 · 318504960 g' queryShape s Θ ℓ = 1274019840 g' queryShape s Θ ℓ` calls, the released
  worst-case matrix count of the four-attempt wrapper.
-/

namespace DysonSingleProgram

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE OracleCircuit Register Parallel
open ODELowerBoundExtensions.Release (jointFlatten)
open scoped InnerProduct InnerProductSpace

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {K s : ℕ}

/-- The adjoint of a readout composed with a fixed isometric equivalence `L` is
`L⁻¹ ∘ e†`. -/
theorem adjoint_comp_isometryEquiv_apply {K K' G : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
    [CompleteSpace K'] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (e : K' →L[ℂ] G) (L : K ≃ₗᵢ[ℂ] K') (w : G) :
    (e ∘L L.toLinearIsometry.toContinuousLinearMap).adjoint w = L.symm (e.adjoint w) := by
  apply ext_inner_left ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_right]
  conv_lhs => rw [← L.apply_symm_apply (e.adjoint w)]
  exact L.inner_map_map _ _

/-- The output observable of a readout composed with a fixed isometric equivalence `L`, on
`L⁻¹ v`, is `L⁻¹` of the output observable on `v`. -/
theorem outObs_comp_isometryEquiv_apply {K K' : Type*} {S G : Type*} [Fintype S]
    [DecidableEq S] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
    [CompleteSpace K'] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (e : K' →L[ℂ] SysGarb S G) (L : K ≃ₗᵢ[ℂ] K')
    (A : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) (v : K') :
    Readout.outObs (e ∘L L.toLinearIsometry.toContinuousLinearMap) A (L.symm v) =
      L.symm (Readout.outObs e A v) := by
  simp only [Readout.outObs, ContinuousLinearMap.comp_apply]
  rw [show L.toLinearIsometry.toContinuousLinearMap (L.symm v) = v from L.apply_symm_apply v,
    adjoint_comp_isometryEquiv_apply]

/-- A readout composed with a fixed isometric equivalence is isometric. -/
theorem comp_isometryEquiv_isometry {K K' G : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
    [CompleteSpace K'] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (e : K' →L[ℂ] G) (he : e.adjoint ∘L e = 1) (L : K ≃ₗᵢ[ℂ] K') :
    (e ∘L L.toLinearIsometry.toContinuousLinearMap).adjoint ∘L
      (e ∘L L.toLinearIsometry.toContinuousLinearMap) = 1 := by
  ext v
  rw [ContinuousLinearMap.comp_apply, adjoint_comp_isometryEquiv_apply,
    ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply e.adjoint e, he]
  exact L.symm_apply_apply v

/-- **Heralded accuracy is invariant under a fixed relabelling** `L`: state `L⁻¹ Φ`, herald
`L⁻¹ P L`, readout `e ∘ L`. -/
theorem heraldedAccurate_isometryEquiv {K K' : Type*} {S G : Type*} [Fintype S]
    [DecidableEq S] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
    [CompleteSpace K'] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (e : K' →L[ℂ] SysGarb S G) (P : K' →L[ℂ] K') (Φ : K') (ψ : EuclideanSpace ℂ S) (ε : ℝ)
    (L : K ≃ₗᵢ[ℂ] K') (h : Readout.HeraldedAccurate e P Φ ψ ε) :
    Readout.HeraldedAccurate (e ∘L L.toLinearIsometry.toContinuousLinearMap)
      (L.symm.conjStarAlgEquiv P) (L.symm Φ) ψ ε := by
  have hPv : ∀ v, L.symm.conjStarAlgEquiv P (L.symm v) = L.symm (P v) := by
    intro v
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_symm,
      LinearIsometryEquiv.apply_symm_apply]
  intro A hA hA1
  have key : (L.symm.conjStarAlgEquiv P ∘L
      Readout.outObs (e ∘L L.toLinearIsometry.toContinuousLinearMap) A ∘L
        L.symm.conjStarAlgEquiv P) (L.symm Φ) = L.symm ((P ∘L Readout.outObs e A ∘L P) Φ) := by
    simp only [ContinuousLinearMap.comp_apply]
    rw [hPv, outObs_comp_isometryEquiv_apply, hPv]
  rw [key, hPv, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.inner_map_map]
  exact h A hA hA1

/-- A herald projection conjugated by a fixed isometric equivalence is a herald projection
(`IsStarProjection.map`, stated over general Hilbert spaces so that it is elaborated once rather
than at the concrete workspace layout). -/
theorem isStarProjection_conj_isometryEquiv {K K' : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
    [CompleteSpace K'] (L : K ≃ₗᵢ[ℂ] K') {P : K' →L[ℂ] K'} (hP : IsStarProjection P) :
    IsStarProjection (L.symm.conjStarAlgEquiv P) :=
  hP.map _

/-- The fixed layout `Workspace (ι × (I × Fin M)) ≃ ℂ^I ⊗ (ℂ^M ⊗ Workspace ι)`. -/
def Parallel.Stage.layout (ι : Type) [Fintype ι] {M : ℕ} (I : Type) [Fintype I] :
    Workspace (ι × (I × Fin M)) N Z K ≃ₗᵢ[ℂ] Joint I (Joint (Fin M) (Workspace ι N Z K)) :=
  (accessLayout ι (I × Fin M) N Z K).trans (jointFlatten I (Fin M) (Workspace ι N Z K))

/-- **A stage's program over the class's access** with branch register `ι × (I × Fin M)`. -/
def Parallel.Stage.toAccessProg (F : Family X N Z K s) (ι : Type) [Fintype ι] {M : ℕ}
    (S : Stage (F.access ι) M N) : MultiOracleCircuit.Program (F.access (ι × (S.I × Fin M))) :=
  toAccess ι (S.I × Fin M) F (reflatten S.I (Fin M) S.prog)

/-- The program over the class's access is the stage's program in the fixed layout. -/
theorem Parallel.Stage.eval_toAccessProg (F : Family X N Z K s) (ι : Type) [Fintype ι] {M : ℕ}
    (S : Stage (F.access ι) M N) (x : X) :
    (S.toAccessProg F ι).eval x = (Stage.layout ι S.I).symm.conjStarAlgEquiv (S.prog.eval x) := by
  rw [Stage.toAccessProg, eval_toAccess, eval_reflatten]
  refine ContinuousLinearMap.ext fun y => ?_
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_symm,
    Stage.layout, LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply]

/-- The program over the class's access has the stage's calls. -/
@[simp] theorem Parallel.Stage.count_toAccessProg (F : Family X N Z K s) (ι : Type) [Fintype ι]
    {M : ℕ} (S : Stage (F.access ι) M N) : (S.toAccessProg F ι).count = S.prog.count := by
  rw [Stage.toAccessProg, count_toAccess, count_reflatten]

/-- **A stage with the solver properties is a `Solver`** with the same program, seed
`layout⁻¹ (S.seed μ)`, herald `layout⁻¹ P layout` and readout `e ∘ layout`. -/
theorem exists_solver_of_stage (F : Family X N Z K s) (ι : Type) [Fintype ι] {M : ℕ}
    (S : Stage (F.access ι) M N) (μ : Joint (Fin M) (Workspace ι N Z K)) (ε : ℝ)
    (hseed : ‖S.seed μ‖ ≤ 1) (hP : IsStarProjection S.herald)
    (he : S.out.adjoint ∘L S.out = 1)
    (hsucc : ∀ x, 2 / 3 ≤ ‖S.herald (S.prog.eval x (S.seed μ))‖ ^ 2)
    (hacc : ∀ x sol, F.Solves x sol →
      Readout.HeraldedAccurate S.out S.herald (S.prog.eval x (S.seed μ))
        (ODEStateNormalization.unitDirection (sol F.T)) ε) :
    ∃ A : Solver (ι × (S.I × Fin M)) F
      (Joint S.Γ (Joint (Fin M) (Workspace ι N Z K))) ε, A.prog = S.toAccessProg F ι := by
  have hev : ∀ x, (S.toAccessProg F ι).eval x
      ((Stage.layout (N := N) (Z := Z) (K := K) (M := M) ι S.I).symm (S.seed μ)) =
      (Stage.layout (N := N) (Z := Z) (K := K) (M := M) ι S.I).symm
        (S.prog.eval x (S.seed μ)) := by
    intro x
    rw [Stage.eval_toAccessProg, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply]
  have hPv : ∀ v, (Stage.layout (N := N) (Z := Z) (K := K) (M := M) ι S.I).symm.conjStarAlgEquiv
      S.herald ((Stage.layout (N := N) (Z := Z) (K := K) (M := M) ι S.I).symm v) =
      (Stage.layout (N := N) (Z := Z) (K := K) (M := M) ι S.I).symm (S.herald v) := by
    intro v
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_symm,
      LinearIsometryEquiv.apply_symm_apply]
  have hP' : IsStarProjection
      ((Stage.layout (N := N) (Z := Z) (K := K) (M := M) ι S.I).symm.conjStarAlgEquiv S.herald) :=
    isStarProjection_conj_isometryEquiv _ hP
  refine ⟨{
    prog := S.toAccessProg F ι
    seed := (Stage.layout (N := N) (Z := Z) (K := K) (M := M) ι S.I).symm (S.seed μ)
    seed_norm_le := by rw [LinearIsometryEquiv.norm_map]; exact hseed
    out := S.out ∘L
      (Stage.layout (N := N) (Z := Z) (K := K) (M := M) ι
        S.I).toLinearIsometry.toContinuousLinearMap
    out_isometry := comp_isometryEquiv_isometry S.out he _
    herald :=
      (Stage.layout (N := N) (Z := Z) (K := K) (M := M) ι S.I).symm.conjStarAlgEquiv S.herald
    herald_proj := hP'
    success := fun x => by rw [hev, hPv, LinearIsometryEquiv.norm_map]; exact hsucc x
    accurate := fun x sol hs => by
      rw [hev]
      exact heraldedAccurate_isometryEquiv _ _ _ _ _ _ (hacc x sol hs) }, rfl⟩

/-- **A stage reproducing a released protocol is a `Solver`**: if the stage `S` with unit main
seed `μ` reproduces a protocol `p` (`Stage.Good`) of success mass at least `2/3` on every input
whose conditional expectations are `2ε`-accurate for every solution, the stage's program is the
program of a `Solver`. -/
theorem exists_solver_of_good (F : Family X N Z K s) (ι : Type) [Fintype ι] {M : ℕ}
    (S : Stage (F.access ι) M N) (μ : Joint (Fin M) (Workspace ι N Z K)) (hμ : ‖μ‖ = 1)
    {Lt : Type*} {Ot : Lt → X → Workspace ι N Z K →L[ℂ] Workspace ι N Z K}
    (p : ODERepeatProtocol.Protocol Ot (EuclideanSpace ℂ N)) (ε : ℝ)
    (hS : S.Good μ p) (hsucc : ∀ x, (2 : ℝ) / 3 ≤ p.successMass x)
    (hacc : ∀ x sol, F.Solves x sol → ∀ A : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N,
      IsSelfAdjoint A → ‖A‖ ≤ 1 →
      |LinearSystemLowerBound.corr A (p.conditionalDensity x) -
        (⟪ODEStateNormalization.unitDirection (sol F.T),
          A (ODEStateNormalization.unitDirection (sol F.T))⟫_ℂ).re| ≤ 2 * ε) :
    ∃ A : Solver (ι × (S.I × Fin M)) F
      (Joint S.Γ (Joint (Fin M) (Workspace ι N Z K))) ε, A.prog = S.toAccessProg F ι :=
  exists_solver_of_stage F ι S μ ε (Stage.norm_seed S μ hμ hS.weight_norm).le hS.herald_proj
    hS.out_isometry (fun x => by rw [hS.success x]; exact hsucc x)
    (fun x sol hs => heraldedAccurate_of_corr p x S.out S.herald _ _ ε
      (lt_of_lt_of_le (by norm_num) (hsucc x)) (hS.success x) (hS.corr x) (hacc x sol hs))

/-- **The four-attempt stage of a preparation**: four attempts with coherent cutoffs
(`Coherent.trial` of the preparation `a` and the fixed unitaries `U₁ U₂ U₃`, label register
`Fin M`, seed `Coherent.labelSeed M ψ`), each on its own register, with the first-success herald
and readout of the output isometry `out` (`Parallel.Stage.four`). -/
def fourAttempts (F : Family X N Z K s) (ι : Type) [Fintype ι] (M : ℕ)
    (a : MultiOracleCircuit.Program (F.access ι))
    {U₁ U₂ U₃ : Workspace ι N Z K →L[ℂ] Workspace ι N Z K}
    (h₁ : IsUnitary U₁) (h₂ : IsUnitary U₂) (h₃ : IsUnitary U₃) (ψ : Workspace ι N Z K)
    (out : EuclideanSpace ℂ N →L[ℂ] Workspace ι N Z K) (i₀ : N) : Stage (F.access ι) M N :=
  Stage.four (Coherent.trial M a h₁ h₂ h₃) (Coherent.labelSeed M ψ) out i₀

/-- **The single heralded program of an amplified trial family** (proof of Lemma `odel:lem:dyson`
and Section `odel:sec:main`): for a trial family `q` over the lower-bound access (idle source
vocabulary) with the amplification shape of a preparation `a` over `F.access ι` and the released
complete certificate for every instance, provided every input has a solution, the four-attempt
program `fourAttempts` (branch register `ι × (I × Fin M)`) is the program of a single-program
`Solver` and makes at most `1274019840 g' queryShape s' Θ ℓ` calls. -/
theorem exists_solver_of_shape (F : Family X N Z K s) (ε : ℝ) (ι : Type) [Fintype ι]
    (q : ℕ → MultiOracleCircuit.Program (ODESourceQueryBudget.oracle (F.access ι) (fun _ _ => 1)))
    (M : ℕ) (ψ : Workspace ι N Z K) (out : EuclideanSpace ℂ N →L[ℂ] Workspace ι N Z K)
    (s' Θ ell g' : ℝ) (a : MultiOracleCircuit.Program (F.access ι))
    (U₁ U₂ U₃ : Workspace ι N Z K →L[ℂ] Workspace ι N Z K)
    (hshape : GroverShape q (ODESourceQueryBudget.matrixWeight (fun _ => 1)) a (fun _ => 1)
      U₁ U₂ U₃)
    (hsol : ∀ x, ∃ sol, F.Solves x sol) (x₀ : X) (i₀ : N)
    (hcert : ∀ x sol, F.Solves x sol →
      ODECompleteTrial.Certificate q M ψ out x (sol F.T) s' Θ ell g' ε) :
    ∃ A : Solver
        (ι × ((fourAttempts F ι M a hshape.unitary₁ hshape.unitary₂ hshape.unitary₃ ψ out i₀).I ×
          Fin M)) F
        (Joint (fourAttempts F ι M a hshape.unitary₁ hshape.unitary₂ hshape.unitary₃ ψ out i₀).Γ
          (Joint (Fin M) (Workspace ι N Z K))) ε,
      A.prog = (fourAttempts F ι M a hshape.unitary₁ hshape.unitary₂ hshape.unitary₃ ψ out
        i₀).toAccessProg F ι ∧
      (A.prog.count : ℝ) ≤ 1274019840 * g' * ImprovedODEQueryBudget.queryShape s' Θ ell := by
  obtain ⟨sol₀, hsol₀⟩ := hsol x₀
  have h₀ := hcert x₀ sol₀ hsol₀
  have hM : 0 < M := h₀.trial.cutoff_pos
  have hψ : ‖ψ‖ = 1 := h₀.trial.seed_unit
  have hFo : out.adjoint ∘L out = 1 := h₀.trial.output_isometry
  have hμ : ‖Coherent.labelSeed M ψ‖ = 1 := Coherent.norm_labelSeed M hM ψ hψ
  have hC : ∀ x, (Coherent.trial M a hshape.unitary₁ hshape.unitary₂ hshape.unitary₃).eval x
      (Coherent.labelSeed M ψ) = ODELowerBoundExtensions.Release.trialVec
        (ODERepeatProtocol.ofCircuits q M hM ψ hψ out hFo) x := fun x =>
    Coherent.trial_eval_labelSeed M a q _ _ hshape (F.access_unitary ι) hM ψ hψ out hFo x
  have hgood : (fourAttempts F ι M a hshape.unitary₁ hshape.unitary₂ hshape.unitary₃ ψ out
      i₀).Good (Coherent.labelSeed M ψ) (ODERepeatProtocol.fourTrials q M hM ψ hψ out hFo) :=
    Stage.good_four (F.access_unitary ι) _ _ hμ q hM ψ hψ out hFo hC i₀
  have hsucc : ∀ x, (2 : ℝ) / 3 ≤
      (ODERepeatProtocol.fourTrials q M hM ψ hψ out hFo).successMass x := by
    intro x
    obtain ⟨sol, hs⟩ := hsol x
    exact (hcert x sol hs).success_two_thirds
  obtain ⟨A, hA⟩ := exists_solver_of_good F ι _ _ hμ _ ε hgood hsucc
    (fun x sol hs B hB hB1 => certificate_observable (hcert x sol hs) B hB hB1)
  refine ⟨A, hA, ?_⟩
  have hcount : A.prog.count = 4 * ((2 * (M - 1) + 1) * a.count) := by
    rw [hA, Stage.count_toAccessProg, fourAttempts, Stage.count_four, Coherent.count_trial]
  have hq := h₀.trial.matrix_queries (M - 1) (by omega)
  rw [hshape.cost_eq (M - 1), MultiOracleCircuit.Program.cost_const] at hq
  rw [hcount]
  push_cast at hq ⊢
  linarith

end

end DysonSingleProgram
