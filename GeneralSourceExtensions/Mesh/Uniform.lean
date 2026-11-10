import GeneralSourceExtensions.Mesh.Approx
import GeneralSourceExtensions.Mesh.Corollaries

/-!
# The uniform mesh as a mesh

The released theorem `GeneralSourceODE.solver` samples one generator path `G` at the points
`t_r = r T / M`. Its instances are instances of the mesh endpoints on the uniform mesh with
`N = q M` slots, `q > 0`, with the same budget:

* `isMesh_uniform`: `t_r = r T / M` is a mesh;
* `uniform_budget_le`: for a `β_G`-Lipschitz path with sample errors `δ_G` at the mesh points,
  `ΔG + ΔR ≤ T (β_G T / M + δ_G)`, the budget term of the released theorem (the refinement term
  `ΔR` vanishes, `refinementError_uniform`, and `sampleError_le_of_lipschitz` gives
  `ΔG ≤ T (β_G T / (2M) + δ_G)`);
* `uniform_instance`: the instance hypotheses of the released theorem give those of the mesh
  endpoints for the constant pieces `G_r = G`, `b_r = b` and the node values `b(v_i)`: accretive
  and integrable pieces, piecewise solutions, the mesh propagator, the same source scale `B`, the
  certificate on the propagated source sum (Duhamel's formula) and the budget;
* `mesh_solver_uniform`: the released guarantees for every instance of `GeneralSourceODE.solver`,
  from `mesh_solver` on the uniform mesh (`UniformOutcome`, over the actual oracles of the
  `q M`-slot workspace);
* `mesh_approx_solver_nonneg_uniform`: the same from the combined endpoint
  `mesh_approx_solver_nonneg`, for every instance of `approx_solver_nonneg` (approximate
  preparations, every `T ≥ 0`; `UniformApproxBudgetOutcome`);
* `actualOracle_eq_released`, `uniformOutcome_eq`, `uniformApproxBudgetOutcome_eq`: at `q = 1`
  the `M`-slot workspace of the mesh endpoints is, definitionally, the released workspace of
  `GeneralSourceODE`, and the two outcomes are the released `GeneralSourceODE.Outcome` and
  `ApproxBudgetOutcome`;
* **`solver_of_mesh`**, **`approx_solver_nonneg_of_mesh`**: hence the mesh endpoint gives the
  released theorem `GeneralSourceODE.solver` itself, and the combined endpoint gives the statement
  of `approx_solver_nonneg` itself, each under its own hypotheses.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralSourceExtensions.Mesh

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set MeasureTheory
open TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE ratio accuracy radius precision
  lipschitz Index lchsCoefficients)
open SparseHamiltonian.GeneralSourceODE (SourceCall sources phases phases_norm IsPropagator
  sourceScale)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- The uniform mesh `t_r = r T / M`. -/
theorem isMesh_uniform (hM : 0 < M) {T : ℝ} (hT : 0 ≤ T) :
    IsMesh (fun r : ℕ => (r : ℝ) * T / M) M T := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨by simp, by field_simp, fun a b hab => ?_⟩
  apply div_le_div_of_nonneg_right _ hMR.le
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hT

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **The budget on the uniform mesh.** For a `β_G`-Lipschitz path with sample errors at most
`δ_G` at the mesh points `r T / M`, the mesh budget term on `N = q M` slots is at most the budget
term `T (β_G T / M + δ_G)` of the released uniform theorem. -/
theorem uniform_budget_le (D : Data (X × Fin M) n Z s) (x : X) (hM : 0 < M) {T : ℝ}
    (hT : 0 ≤ T) {q : ℕ} (hq : 0 < q) (G : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    {βG δG : ℝ} (hβ : 0 ≤ βG)
    (hLip : ∀ u ∈ Icc 0 T, ∀ w ∈ Icc 0 T, ‖G u - G w‖ ≤ βG * |u - w|)
    (hδ : ∀ r : Fin M, ‖G ((r : ℕ) * T / M) -
      SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δG) :
    sampleError D x (fun r : ℕ => (r : ℝ) * T / M) (fun _ => G) +
        refinementError D (fun r : ℕ => (r : ℝ) * T / M) T (q * M) ≤
      T * (βG * (T / M) + δG) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hmesh := isMesh_uniform hM hT
  have hsub : ∀ r : Fin M, Icc ((r : ℕ) * T / M) (((r : ℕ) + 1 : ℕ) * T / M) ⊆ Icc 0 T :=
    fun r => Icc_subset_Icc (hmesh.nonneg r) (hmesh.le_last (Nat.succ_le_of_lt r.isLt))
  have hS := sampleError_le_of_lipschitz D x hmesh (fun _ => G) (fun _ => βG) (fun _ => δG)
    (fun r u hu w hw => hLip u (hsub r hu) w (hsub r hw)) hδ
  have hΔ : ∀ r : ℕ, (((r + 1 : ℕ) : ℝ) * T / M - (r : ℝ) * T / M) = T / M := by
    intro r
    push_cast
    ring
  rw [refinementError_uniform D hM hT hq, add_zero]
  have hTM : 0 ≤ βG * (T / M) := mul_nonneg hβ (div_nonneg hT hMR.le)
  calc sampleError D x (fun r : ℕ => (r : ℝ) * T / M) (fun _ => G) ≤ _ := hS
    _ = (M : ℝ) * (βG * (T / M) ^ 2 / 2 + δG * (T / M)) := by
      simp only [hΔ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = T * (βG * (T / M) / 2 + δG) := by
      field_simp
    _ ≤ T * (βG * (T / M) + δG) := mul_le_mul_of_nonneg_left (by linarith) hT

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **Instances of the uniform theorem on the uniform mesh.** The instance hypotheses of the
released `GeneralSourceODE.solver` (an accretive, `β_G`-Lipschitz path with sample errors `δ_G`
at the mesh points, a continuous forcing, a solution and its propagator) give the instance
hypotheses of the mesh endpoints on the uniform mesh with `N = q M` slots, for the constant pieces
`G_r = G` and `b_r = b`: accretive interval-integrable pieces solved by `x(·)`, the mesh
propagator, the same source scale, Duhamel's formula (which turns the certificate on the
propagated vector integral into the one on the propagated source sum) and the budget. -/
theorem uniform_instance (D : Data (X × Fin M) n Z s) (x : X) (hM : 0 < M) {T : ℝ}
    (hT : 0 ≤ T) {q : ℕ} (hq : 0 < q) (G : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (b sol : ℝ → EuclideanSpace ℂ n) (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n)
    {βG δG : ℝ} (hβ : 0 ≤ βG) (hG : ∀ u ∈ Icc 0 T, Accretive (G u))
    (hLip : ∀ u ∈ Icc 0 T, ∀ w ∈ Icc 0 T, ‖G u - G w‖ ≤ βG * |u - w|)
    (hδ : ∀ r : Fin M, ‖G ((r : ℕ) * T / M) -
      SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δG)
    (hb : ContinuousOn b (Icc 0 T)) (hsol : SolvesODE G b sol 0 T) (hU : IsPropagator G U T) :
    (∀ r : Fin M, ∀ u ∈ Icc ((r : ℕ) * T / M) (((r : ℕ) + 1 : ℕ) * T / M), Accretive (G u)) ∧
    (∀ r : Fin M, IntervalIntegrable G volume ((r : ℕ) * T / M) (((r : ℕ) + 1 : ℕ) * T / M)) ∧
    (∀ r : Fin M, SolvesODE G b sol ((r : ℕ) * T / M) (((r : ℕ) + 1 : ℕ) * T / M)) ∧
    IsMeshPropagator (fun _ : Fin M => G) (fun r : ℕ => (r : ℝ) * T / M) T U ∧
    meshScale sol (fun _ : Fin M => b) (fun r : ℕ => (r : ℝ) * T / M) = sourceScale sol b T ∧
    (∫ u in (0 : ℝ)..T, U u (b u) T) = sol T - U 0 (sol 0) T ∧
    sampleError D x (fun r : ℕ => (r : ℝ) * T / M) (fun _ => G) +
        refinementError D (fun r : ℕ => (r : ℝ) * T / M) T (q * M) ≤
      T * (βG * (T / M) + δG) := by
  have hmesh := isMesh_uniform hM hT
  have hsub : ∀ r : Fin M, Icc ((r : ℕ) * T / M) (((r : ℕ) + 1 : ℕ) * T / M) ⊆ Icc 0 T :=
    fun r => Icc_subset_Icc (hmesh.nonneg r) (hmesh.le_last (Nat.succ_le_of_lt r.isLt))
  have hGc : ContinuousOn G (Icc 0 T) := TimeDependentODE.continuousOn_of_norm_sub_le G hLip
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hGc
  refine ⟨fun r u hu => hG u (hsub r hu), fun r => ?_, fun r => ?_, fun t₀ ht₀ w => ?_, ?_,
    GeneralSourceODE.duhamel hT hU hG C hC hb hsol,
    uniform_budget_le D x hM hT hq G hβ hLip hδ⟩
  · exact (hGc.mono (hsub r)).intervalIntegrable_of_Icc (hmesh.mono (Nat.le_succ r))
  · exact hsol.mono (hmesh.nonneg r) (hmesh.le_last (Nat.succ_le_of_lt r.isLt))
  · obtain ⟨hsolU, hU0⟩ := hU t₀ ht₀ w
    exact ⟨hU0, fun r _ => hsolU.mono (le_max_left _ _)
      (hmesh.le_last (Nat.succ_le_of_lt r.isLt))⟩
  · have hbn : ContinuousOn (fun u => ‖b u‖) (Icc 0 T) := hb.norm
    unfold meshScale sourceScale
    congr 1
    have hint : ∀ k < M, IntervalIntegrable (fun u => ‖b u‖) volume ((k : ℝ) * T / M)
        (((k + 1 : ℕ) : ℝ) * T / M) := fun k hk =>
      (hbn.mono (Icc_subset_Icc (hmesh.nonneg k) (hmesh.le_last (Nat.succ_le_of_lt hk)))
        ).intervalIntegrable_of_Icc (hmesh.mono (Nat.le_succ k))
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun r : ℕ => (r : ℝ) * T / M) hint
    rw [← Fin.sum_univ_eq_sum_range] at h
    rw [h, hmesh.zero, hmesh.last]

/-! ### The released theorems from the mesh endpoints -/

/-- **The released uniform outcome on `N` slots**: `GeneralSourceODE.Outcome` over the actual
oracles of the `N`-slot workspace. One public trial family, fixed before the instance; for every
instance of the released uniform theorem, four fresh trials have the released guarantees. -/
def UniformOutcome (D : Data (X × Fin M) n Z s) (N : ℕ) (etaH etaD T gbar cq ε : ℝ) {m : ℕ}
    (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (d : ℕ) (tf : ODERepeatProtocol.TrialFamily
      (MeshOracles.actualOracle (ι := Index D T (cq * gbar) ε) D m N d Pw J)
      (EuclideanSpace ℂ n)),
    tf.choices = ODEGroverAverage.chosenIterations (ratio (cq * gbar)) ∧
    (∀ j y, IsUnitary ((tf.circuit j).eval y)) ∧
    ∀ (x : X) (G : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b sol : ℝ → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (βG δG ζ : ℝ), 0 ≤ βG →
      (∀ u ∈ Icc 0 T, Accretive (G u)) →
      (∀ u ∈ Icc 0 T, ∀ w ∈ Icc 0 T, ‖G u - G w‖ ≤ βG * |u - w|) →
      (∀ r : Fin M, ‖G ((r : ℕ) * T / M) -
        SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δG) →
      ContinuousOn b (Icc 0 T) →
      SolvesODE G b sol 0 T →
      IsPropagator G U T →
      GeneralSourceODE.Compiled.WeightPrep (Pw x) (sources (sol 0) (fun i => b (v i)) ω) →
      (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → b (v i) ≠ 0 → J x (some i) seed =
        ODEStateNormalization.unitDirection (b (v i))) →
      ODESourceBranches.mass (sources (sol 0) (fun i => b (v i)) ω) ≤
        cq * sourceScale sol b T →
      ‖(∫ u in (0 : ℝ)..T, U u (b u) T) - ∑ i, ω i • U (v i) (b (v i)) T‖ ≤
        ζ * sourceScale sol b T →
      sol T ≠ 0 →
      sourceScale sol b T ≤ gbar * ‖sol T‖ →
      ζ + cq * (T * (βG * (T / M) + δG)) ≤ ε / (2000 * gbar) →
      GeneralSourceODE.Oracles.ActualCertificate
        (ODERepeatProtocol.Protocol.repeatTrials tf 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε

/-- **The released approximate outcome on `N` slots**: `ApproxBudgetOutcome` over the actual
oracles of the `N`-slot workspace. One public trial family, fixed before the instance; for every
instance of `approx_solver_nonneg`, four fresh trials satisfy `ApproxCertificate` and make at
most `Q` matrix queries in every history. -/
def UniformApproxBudgetOutcome (D : Data (X × Fin M) n Z s) (N : ℕ) (etaH etaD T gbar cq ε : ℝ)
    {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Q : ℝ) : Prop :=
  ∃ (d : ℕ) (tf : ODERepeatProtocol.TrialFamily
      (MeshOracles.actualOracle (ι := Index D T (cq * gbar) ε) D m N d Pw J)
      (EuclideanSpace ℂ n)),
    tf.choices = ODEGroverAverage.chosenIterations (ratio (cq * gbar)) ∧
    (∀ j y, IsUnitary ((tf.circuit j).eval y)) ∧
    ∀ (x : X) (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
      (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (δ : ℝ)
      (G : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b sol : ℝ → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (βG δG ζ : ℝ),
      IsUnitary P → (∀ a, IsUnitary (L a)) → 0 ≤ δ →
      ‖Pw x - P‖ ≤ δ → (∀ a, ‖J x a - L a‖ ≤ δ) →
      30 * ratio (cq * gbar) * δ ≤ 1 / 400 → 30 * ratio (cq * gbar) * δ ≤ ε / 20 →
      0 ≤ βG →
      (∀ u ∈ Icc 0 T, Accretive (G u)) →
      (∀ u ∈ Icc 0 T, ∀ w ∈ Icc 0 T, ‖G u - G w‖ ≤ βG * |u - w|) →
      (∀ r : Fin M, ‖G ((r : ℕ) * T / M) -
        SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δG) →
      ContinuousOn b (Icc 0 T) →
      SolvesODE G b sol 0 T →
      IsPropagator G U T →
      GeneralSourceODE.Compiled.WeightPrep P (sources (sol 0) (fun i => b (v i)) ω) →
      (sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → b (v i) ≠ 0 → L (some i) seed =
        ODEStateNormalization.unitDirection (b (v i))) →
      ODESourceBranches.mass (sources (sol 0) (fun i => b (v i)) ω) ≤
        cq * sourceScale sol b T →
      ‖(∫ u in (0 : ℝ)..T, U u (b u) T) - ∑ i, ω i • U (v i) (b (v i)) T‖ ≤
        ζ * sourceScale sol b T →
      sol T ≠ 0 →
      sourceScale sol b T ≤ gbar * ‖sol T‖ →
      ζ + cq * (T * (βG * (T / M) + δG)) ≤ ε / (2000 * gbar) →
      ApproxCertificate (ODERepeatProtocol.Protocol.repeatTrials tf 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε ∧
      ((ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
        GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤ Q

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The clock conditions of the released theorem on `M` give those on `N = q M` slots. -/
theorem clock_conditions_mul {q : ℕ} (hq : 0 < q) {ρT ν : ℝ} (hν : 0 ≤ ν)
    (hMesh : 8 * s * ρT ≤ M) (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) * ρT) ^ 3 ≤ ν * (M : ℝ) ^ 2) :
    8 * s * ρT ≤ ((q * M : ℕ) : ℝ) ∧
      3 * (Real.sqrt (2 * (s : ℝ)) * ρT) ^ 3 ≤ ν * ((q * M : ℕ) : ℝ) ^ 2 := by
  have hMN : (M : ℝ) ≤ ((q * M : ℕ) : ℝ) := by exact_mod_cast Nat.le_mul_of_pos_left M hq
  exact ⟨hMesh.trans hMN, hCayley.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Nat.cast_nonneg M) hMN 2) hν)⟩

set_option maxHeartbeats 4000000 in
/-- **The released theorem from the mesh endpoint.** Under the hypotheses of the released
`GeneralSourceODE.solver`, `mesh_solver` on the uniform mesh with `N = q M` slots, `q > 0`,
gives `UniformOutcome`: one public trial family over the actual oracles of the `q M`-slot
workspace (the released workspace for `q = 1`, `solver_of_mesh`) with the released guarantees for
every instance of the released theorem. -/
theorem mesh_solver_uniform (D : Data (X × Fin M) n Z s) (hM : 0 < M) {q : ℕ} (hq : 0 < q)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 < T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hρ : 0 < etaH + radius (cq * gbar) ε * etaD)
    (hMesh : 8 * s * ((etaH + radius (cq * gbar) ε * etaD) * T) ≤ M)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
        precision (cq * gbar) ε * (M : ℝ) ^ 2)
    (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    UniformOutcome D (q * M) etaH etaD T gbar cq ε v ω Pw J seed := by
  have hg' : 1 ≤ ratio (cq * gbar) := by unfold ratio; nlinarith
  have hε' : 0 < accuracy ε := by unfold accuracy; linarith
  have hν : 0 < precision (cq * gbar) ε := ImprovedODEQueryBudget.precision_pos _ _ hg' hε'
  obtain ⟨hClock, hCayley'⟩ := clock_conditions_mul hq hν.le hMesh hCayley
  obtain ⟨d, tf, hch, hU, hC⟩ := mesh_solver D hM (fun r : ℕ => (r : ℝ) * T / M)
    (Nat.mul_pos hq hM) etaH etaD T gbar cq ε v ω hH hDiss hT hg hcq hε hεOne
    (isMesh_uniform hM hT.le) hρ hClock hCayley' hv hrH hcH hrD hcD hPSD Pw hPw J hJ seed hSeed
  refine ⟨d, tf, hch, hU, fun x G b sol U βG δG ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    h15 => ?_⟩
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ :=
    uniform_instance D x hM hT.le hq G b sol U h1 h2 h3 h4 h5 h6 h7
  refine hC x (fun _ => G) (fun _ => b) sol (fun i => b (v i)) U ζ i1 i2 i3 i4 h8 h9 h10
    (by rw [i5]; exact h11) (by rw [i5, ← i6]; exact h12) h13 (by rw [i5]; exact h14) ?_
  calc _ ≤ ζ + cq * (T * (βG * (T / M) + δG)) := by
        have := mul_le_mul_of_nonneg_left i7 (by linarith : (0 : ℝ) ≤ cq)
        linarith
    _ ≤ ε / (2000 * gbar) := h15

set_option maxHeartbeats 4000000 in
/-- **The approximate released theorem from the combined mesh endpoint.** Under the hypotheses
of `approx_solver_nonneg`, the combined endpoint `mesh_approx_solver_nonneg` on the uniform mesh
with `N = q M` slots, `q > 0`, gives `UniformApproxBudgetOutcome` with the budget of
`approx_solver_nonneg`: one public trial family over the actual oracles of the `q M`-slot
workspace (the released workspace for `q = 1`, `approx_solver_nonneg_of_mesh`) for every instance
of `approx_solver_nonneg`. -/
theorem mesh_approx_solver_nonneg_uniform (D : Data (X × Fin M) n Z s) (hM : 0 < M) {q : ℕ}
    (hq : 0 < q) (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hMesh : 8 * s * ((etaH + radius (cq * gbar) ε * etaD) * T) ≤ M)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
        precision (cq * gbar) ε * (M : ℝ) ^ 2)
    (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    UniformApproxBudgetOutcome D (q * M) etaH etaD T gbar cq ε v ω Pw J seed
      (if T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0 then 0 else
        1274019840 * ratio (cq * gbar) * ImprovedODEQueryBudget.queryShape (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
          (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))) := by
  have hg' : 1 ≤ ratio (cq * gbar) := by unfold ratio; nlinarith
  have hε' : 0 < accuracy ε := by unfold accuracy; linarith
  have hν : 0 < precision (cq * gbar) ε := ImprovedODEQueryBudget.precision_pos _ _ hg' hε'
  obtain ⟨hClock, hCayley'⟩ := clock_conditions_mul hq hν.le hMesh hCayley
  obtain ⟨d, tf, hch, hU, hC⟩ := mesh_approx_solver_nonneg D hM (fun r : ℕ => (r : ℝ) * T / M)
    (Nat.mul_pos hq hM) etaH etaD T gbar cq ε v ω hH hDiss hT hg hcq hε hεOne
    (isMesh_uniform hM hT) hClock hCayley' hv hrH hcH hrD hcD hPSD Pw hPw J hJ seed hSeed
  refine ⟨d, tf, hch, hU, fun x P L δ G b sol U βG δG ζ a1 a2 a3 a4 a5 a6 a7 h1 h2 h3 h4 h5 h6
    h7 h8 h9 h10 h11 h12 h13 h14 h15 => ?_⟩
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ :=
    uniform_instance D x hM hT hq G b sol U h1 h2 h3 h4 h5 h6 h7
  refine hC x P L δ (fun _ => G) (fun _ => b) sol (fun i => b (v i)) U ζ a1 a2 a3 a4 a5 a6 a7
    i1 i2 i3 i4 h8 h9 h10 (by rw [i5]; exact h11) (by rw [i5, ← i6]; exact h12) h13
    (by rw [i5]; exact h14) ?_
  calc _ ≤ ζ + cq * (T * (βG * (T / M) + δG)) := by
        have := mul_le_mul_of_nonneg_left i7 (by linarith : (0 : ℝ) ≤ cq)
        linarith
    _ ≤ ε / (2000 * gbar) := h15

/-! ### The released statements at `q = 1` -/

omit [DecidableEq Z] in
/-- On `N = M` slots the actual oracles of the mesh workspace are, definitionally, the actual
oracles of the released general-source solver. -/
theorem actualOracle_eq_released {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    MeshOracles.actualOracle (ι := ι) D m M d Pw J =
      GeneralSourceODE.Oracles.actualOracle (ι := ι) D m d Pw J := rfl

omit [DecidableEq Z] in
/-- On `N = M` slots, `UniformOutcome` is the released `GeneralSourceODE.Outcome`. -/
theorem uniformOutcome_eq (D : Data (X × Fin M) n Z s) (etaH etaD T gbar cq ε : ℝ) {m : ℕ}
    (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) :
    UniformOutcome D M etaH etaD T gbar cq ε v ω Pw J seed =
      GeneralSourceODE.Outcome D etaH etaD T gbar cq ε v ω Pw J seed := rfl

omit [DecidableEq Z] in
/-- On `N = M` slots, `UniformApproxBudgetOutcome` is `ApproxBudgetOutcome`. -/
theorem uniformApproxBudgetOutcome_eq (D : Data (X × Fin M) n Z s)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Q : ℝ) :
    UniformApproxBudgetOutcome D M etaH etaD T gbar cq ε v ω Pw J seed Q =
      ApproxBudgetOutcome D etaH etaD T gbar cq ε v ω Pw J seed Q := rfl

set_option maxHeartbeats 4000000 in
/-- **`GeneralSourceODE.solver` from the mesh endpoint.** The released theorem itself, under its
own hypotheses, derived from `mesh_solver` on the uniform mesh with `N = M` slots
(`mesh_solver_uniform` at `q = 1` and `uniformOutcome_eq`). -/
theorem solver_of_mesh (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 < T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hρ : 0 < etaH + radius (cq * gbar) ε * etaD)
    (hMesh : 8 * s * ((etaH + radius (cq * gbar) ε * etaD) * T) ≤ M)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
        precision (cq * gbar) ε * (M : ℝ) ^ 2)
    (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    GeneralSourceODE.Outcome D etaH etaD T gbar cq ε v ω Pw J seed := by
  have h := mesh_solver_uniform D hM (q := 1) Nat.one_pos etaH etaD T gbar cq ε v ω hH hDiss hT
    hg hcq hε hεOne hρ hMesh hCayley hv hrH hcH hrD hcD hPSD Pw hPw J hJ seed hSeed
  rw [Nat.one_mul, uniformOutcome_eq] at h
  exact h

set_option maxHeartbeats 4000000 in
/-- **`approx_solver_nonneg` from the combined mesh endpoint.** The statement of
`approx_solver_nonneg` itself, under its own hypotheses, derived from
`mesh_approx_solver_nonneg` on the uniform mesh with `N = M` slots
(`mesh_approx_solver_nonneg_uniform` at `q = 1` and `uniformApproxBudgetOutcome_eq`). -/
theorem approx_solver_nonneg_of_mesh (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hMesh : 8 * s * ((etaH + radius (cq * gbar) ε * etaD) * T) ≤ M)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
        precision (cq * gbar) ε * (M : ℝ) ^ 2)
    (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    ApproxBudgetOutcome D etaH etaD T gbar cq ε v ω Pw J seed
      (if T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0 then 0 else
        1274019840 * ratio (cq * gbar) * ImprovedODEQueryBudget.queryShape (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
          (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))) := by
  have h := mesh_approx_solver_nonneg_uniform D hM (q := 1) Nat.one_pos etaH etaD T gbar cq ε v ω
    hH hDiss hT hg hcq hε hεOne hMesh hCayley hv hrH hcH hrD hcD hPSD Pw hPw J hJ seed hSeed
  rw [Nat.one_mul, uniformApproxBudgetOutcome_eq] at h
  exact h

end

end SparseHamiltonian.GeneralSourceExtensions.Mesh
