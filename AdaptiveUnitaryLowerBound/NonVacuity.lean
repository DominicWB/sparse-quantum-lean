import AdaptiveUnitaryLowerBound.Entry
import TimeDependentHamiltonianLowerBound.NonVacuity

set_option autoImplicit false
set_option synthInstance.maxSize 8192

/-!
# Non-vacuity: the released circuit as an adaptive protocol

The released constant-error circuit of `SparseHamiltonian.UnitaryImplementation.implementation`
(error `1/4`, at most `queryConstant · √N` entry-oracle calls), run once on its encoded input
and read through the endpoint readout, meets every hypothesis of `Entry.unheralded_tree` and
`Entry.heralded_tree` (`released_tree`), and, lifted to the plain call forms with a clean
control qubit, every hypothesis of `Entry.unheralded_calls_tree`, `Entry.heralded_calls_tree`
and `Entry.calls_program_of_error` (`released_calls_bounds`). So both halves of `Θ(√N)`
(Corollary `hs:cor:unitary`, last sentence) hold for adaptive protocols in one oracle model.
`single_hyps` turns operator-norm error of a unitary program into the hypotheses of the
protocol bounds (one trial, success probability one, `ε`-accuracy on the reduction input).
The plain call forms and the clean control encoding are the released
`TimeDependentHamiltonianLowerBound.plainLift` and `TimeDependentHamiltonianLowerBound.boolEmbed`.
-/

namespace AdaptiveUnitaryLowerBound.NonVacuity

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Readout SparseLowerBounds.Hamiltonian
open SparseLinearSystems.Protocol ContinuousLinearMap OracleCircuit
open UnitaryImplementationExtensions UnitaryImplementationExtensions.SearchFamily
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open TimeDependentHamiltonianLowerBound (plainLift eval_plainLift boolEmbed boolEmbed_apply
  boolEmbed_isometry)
open scoped InnerProduct InnerProductSpace

/-- **One trial of a unitary program meets the protocol hypotheses** (Corollary
`hs:cor:unitary`): a unitary program with operator-norm error `ε` on an isometric encoding `J`,
run once on `J |0⟩` and read through `endpointReadout J 0`, succeeds with probability one and is
`ε`-accurate for `U_m |0⟩`; its worst-case count is its count. -/
theorem single_hyps {L K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [FiniteDimensional ℂ K] {N : ℕ} [NeZero N] {O : L → Fin N → K →L[ℂ] K}
    (hO : ∀ l m, IsUnitary (O l m)) (q : MultiOracleCircuit.Program O)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] K) (hJ : J† ∘L J = 1) {ε : ℝ}
    (hErr : ∀ m, ‖q.eval m ∘L J - J ∘L SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤ ε) :
    ∃ hφ : ‖J (EuclideanSpace.single 0 1)‖ = 1,
      (endpointReadout J 0)† ∘L endpointReadout J 0 = 1 ∧
      (∀ m, (AdaptiveHamiltonianLowerBound.Single.tree ℂ q _ hφ).successMass m = 1) ∧
      (∀ m, DensityAccurate (endpointReadout J 0)
        ((AdaptiveHamiltonianLowerBound.Single.tree ℂ q _ hφ).conditionalDensity m)
        (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1)) ε) ∧
      (AdaptiveHamiltonianLowerBound.Single.tree ℂ q _ hφ).worstCost (fun _ => 1) = q.count := by
  have hφ : ‖J (EuclideanSpace.single 0 1)‖ = 1 := by
    rw [(J.norm_map_iff_adjoint_comp_self).mpr hJ]; simp
  have hU : ∀ m, IsUnitary (q.eval m) := fun m => q.eval_unitary hO m
  refine ⟨hφ, endpointReadout_isometry J hJ 0, fun m => ?_, fun m => ?_, ?_⟩
  · exact AdaptiveHamiltonianLowerBound.Single.successMass_tree q _ hφ m (hU m)
  · rw [AdaptiveHamiltonianLowerBound.Single.conditionalDensity_tree q _ hφ m (hU m),
      AdaptiveHamiltonianLowerBound.densityAccurate_pure_iff]
    refine accurate_of_endpoint J hJ 0 (q.eval m) (hU m).norm_le_one _ (by simp) ?_ (hErr m)
    rw [searchMatrix_single_zero]; simp
  · rw [AdaptiveHamiltonianLowerBound.Single.worstCost_tree,
      MultiOracleCircuit.Program.cost_const, mul_one]

/-! ### The released circuit over `Entry.entryOracles` -/

/-- The workspace of the released constant-error circuit. -/
abbrev Phys (N : ℕ) (γ : ℝ) :=
  UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ 1 (Real.pi / 2) (1 / 4)

/-- The released circuit as a one-label program over `Entry.entryOracles`. -/
def relProg {N : ℕ} {γ : ℝ}
    (p : OracleCircuit.Program (UnitaryImplementation.oracle (searchData N) γ)) :
    MultiOracleCircuit.Program (Entry.entryOracles N γ 1 (Real.pi / 2) (1 / 4)) :=
  MultiOracleCircuit.Program.embed () p

/-- **The released circuit over `Entry.entryOracles`** (Corollary `hs:cor:unitary` at constant
error): the circuit of `UnitaryImplementation.implementation` implements every `U_m` of the
search family with operator-norm error `1/4` on an isometric encoding with at most
`queryConstant · √N` entry-oracle calls. -/
theorem released {N : ℕ} [NeZero N] :
    ∃ (γ : ℝ) (q : MultiOracleCircuit.Program (Entry.entryOracles N γ 1 (Real.pi / 2) (1 / 4)))
      (J : EuclideanSpace ℂ (Fin N) →L[ℂ] Phys N γ), J† ∘L J = 1 ∧
      (∀ m, ‖q.eval m ∘L J - J ∘L SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤
        (1 / 4 : ℝ)) ∧
      (q.count : ℝ) ≤ UnitaryImplementation.queryConstant * Real.sqrt (N : ℝ) := by
  obtain ⟨γ, -, -, p, hcount, hinput, haction⟩ :=
    UnitaryImplementation.implementation (searchData N)
  refine ⟨γ, relProg p, UnitaryImplementation.input (searchData N) γ, hinput, fun m => ?_, ?_⟩
  · have hq : (relProg p).eval m = p.eval m := MultiOracleCircuit.Program.eval_embed _ _ _
    rw [hq]
    exact (haction m).2
  · have hc : (relProg p).count = p.count := MultiOracleCircuit.Program.count_embed _ _
    rw [hc]
    exact hcount.trans_eq (by rw [Fintype.card_fin])

/-- **The hypotheses of `Entry.unheralded_tree` and `Entry.heralded_tree` can be met**
(Corollary `hs:cor:unitary`, last sentence, both halves in one oracle model): the released
circuit, run once as an adaptive protocol with `ε₀ = 1/4`, succeeds with probability one, is
`1/4`-accurate, obeys both lower bounds and makes at most `queryConstant · √N` entry calls. -/
theorem released_tree {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    ∃ (γ : ℝ) (T : Tree (Entry.entryOracles N γ 1 (Real.pi / 2) (1 / 4)) ℂ (Phys N γ))
      (e : Phys N γ →L[ℂ] SysGarb (Fin N) (Phys N γ)),
      e† ∘L e = 1 ∧ (∀ m, T.successMass m = 1) ∧
      (∀ m, DensityAccurate e (T.conditionalDensity m)
        (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1))
          (1 / 4)) ∧
      (1 - 2 * (1 / 4 : ℝ)) ^ 2 * Real.sqrt ((N : ℝ) - 1) ≤ 4 * T.worstCost (fun _ => 1) ∧
      (1 - 2 * (1 / 4 : ℝ)) ^ 2 * Real.sqrt ((N : ℝ) - 1) ≤ 9 * T.worstCost (fun _ => 1) ∧
      ((T.worstCost (fun _ => 1) : ℕ) : ℝ) ≤
        UnitaryImplementation.queryConstant * Real.sqrt (N : ℝ) := by
  obtain ⟨γ, q, J, hJ, hErr, hcount⟩ := released (N := N)
  obtain ⟨hφ, he, hs, hacc, hT⟩ :=
    single_hyps (Entry.entryOracles_unitary N γ 1 (Real.pi / 2) (1 / 4)) q J hJ hErr
  refine ⟨γ, _, _, he, hs, hacc,
    Entry.unheralded_tree hN γ 1 (Real.pi / 2) (1 / 4) _ _ he (by norm_num) hs hacc,
    Entry.heralded_tree hN γ 1 (Real.pi / 2) (1 / 4) _ _ he (by norm_num)
      (fun m => by rw [hs m]; norm_num) hacc, ?_⟩
  rw [hT]
  exact hcount

/-! ### The call forms -/

/-- The plain call forms (`TimeDependentHamiltonianLowerBound.plainLift`) keep the number of
calls. -/
theorem count_plainLift {L X W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] {O : L → X → W →L[ℂ] W} (p : MultiOracleCircuit.Program O) :
    (plainLift p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
      change (plainLift p).count + (plainLift q).count = p.count + q.count
      rw [hp, hq]

/-- The plain call forms with the clean control encoding keep the operator-norm error. -/
theorem plain_calls {L W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] {N : ℕ} {O : L → Fin N → W →L[ℂ] W} (q : MultiOracleCircuit.Program O)
    (ι : EuclideanSpace ℂ (Fin N) →L[ℂ] W) (hι : ι† ∘L ι = 1) {ε : ℝ}
    (h : ∀ m, ‖q.eval m ∘L ι - ι ∘L SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤ ε) :
    (boolEmbed W ∘L ι)† ∘L (boolEmbed W ∘L ι) = 1 ∧
      (∀ m, ‖(plainLift q).eval m ∘L (boolEmbed W ∘L ι) -
        (boolEmbed W ∘L ι) ∘L SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤ ε) ∧
      (plainLift q).count = q.count := by
  refine ⟨?_, fun m => ?_, count_plainLift q⟩
  · rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc _ _ ι, boolEmbed_isometry]
    rw [show (1 : W →L[ℂ] W) ∘L ι = ι from by ext v; simp]
    exact hι
  · have heq : (plainLift q).eval m ∘L (boolEmbed W ∘L ι) -
        (boolEmbed W ∘L ι) ∘L SparseStateOverlap.matrixOperator (searchMatrix N m) =
        boolEmbed W ∘L (q.eval m ∘L ι - ι ∘L SparseStateOverlap.matrixOperator
          (searchMatrix N m)) := by
      ext v b
      rw [eval_plainLift]
      cases b <;> simp [boolEmbed_apply]
    rw [heq]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hJ : ‖boolEmbed W‖ ≤ 1 :=
      SparseMatrixNorm.norm_le_one_of_adjoint_comp _ (boolEmbed_isometry W)
    calc ‖boolEmbed W‖ * ‖q.eval m ∘L ι - ι ∘L SparseStateOverlap.matrixOperator
          (searchMatrix N m)‖ ≤ 1 * ‖q.eval m ∘L ι - ι ∘L SparseStateOverlap.matrixOperator
          (searchMatrix N m)‖ := mul_le_mul_of_nonneg_right hJ (norm_nonneg _)
      _ ≤ ε := by rw [one_mul]; exact h m

/-- **The released circuit over the plain call forms**, with a clean control qubit: operator-norm
error `1/4` with at most `queryConstant · √N` calls. -/
theorem released_calls {N : ℕ} [NeZero N] :
    ∃ (γ : ℝ) (p : MultiOracleCircuit.Program (AdaptiveODELowerBound.Access.callFamily
        (Entry.entryOracles N γ 1 (Real.pi / 2) (1 / 4))))
      (J : EuclideanSpace ℂ (Fin N) →L[ℂ] Joint Bool (Phys N γ)),
      J† ∘L J = 1 ∧
      (∀ m, ‖p.eval m ∘L J - J ∘L SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤
        (1 / 4 : ℝ)) ∧
      ((p.cost (fun _ => 1) : ℕ) : ℝ) ≤
        UnitaryImplementation.queryConstant * Real.sqrt (N : ℝ) := by
  obtain ⟨γ, q, ι, hι, hErr, hcount⟩ := released (N := N)
  obtain ⟨hJ, hErr', hc⟩ := plain_calls q ι hι hErr
  refine ⟨γ, plainLift q, boolEmbed (Phys N γ) ∘L ι, hJ, hErr', ?_⟩
  rw [MultiOracleCircuit.Program.cost_const, mul_one, hc]
  exact hcount

/-- **The hypotheses of `Entry.unheralded_calls_tree`, `Entry.heralded_calls_tree` and
`Entry.calls_program_of_error` can be met** (Corollary `hs:cor:unitary`, last sentence, both
halves in one oracle model with controlled and controlled-inverse calls available): the lifted
released circuit obeys the three lower bounds and makes at most `queryConstant · √N` calls. -/
theorem released_calls_bounds {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    ∃ (γ : ℝ) (p : MultiOracleCircuit.Program (AdaptiveODELowerBound.Access.callFamily
        (Entry.entryOracles N γ 1 (Real.pi / 2) (1 / 4)))),
      (1 - 2 * (1 / 4 : ℝ) * Real.sqrt (1 - (1 / 4 : ℝ) ^ 2 / 4)) * Real.sqrt ((N : ℝ) - 1) ≤
        2 * p.cost (fun _ => 1) ∧
      (1 - 2 * (1 / 4 : ℝ)) ^ 2 * Real.sqrt ((N : ℝ) - 1) ≤ 4 * p.cost (fun _ => 1) ∧
      (1 - 2 * (1 / 4 : ℝ)) ^ 2 * Real.sqrt ((N : ℝ) - 1) ≤ 9 * p.cost (fun _ => 1) ∧
      ((p.cost (fun _ => 1) : ℕ) : ℝ) ≤
        UnitaryImplementation.queryConstant * Real.sqrt (N : ℝ) := by
  obtain ⟨γ, p, J, hJ, hErr, hcost⟩ := released_calls (N := N)
  have hU := AdaptiveODELowerBound.Access.callFamily_unitary
    (Entry.entryOracles_unitary N γ 1 (Real.pi / 2) (1 / 4))
  obtain ⟨hφ, he, hs, hacc, hT⟩ := single_hyps hU p J hJ hErr
  have h1 := Entry.calls_program_of_error hN γ 1 (Real.pi / 2) (1 / 4) p J hJ (by norm_num) hErr
  have h2 := Entry.unheralded_calls_tree hN γ 1 (Real.pi / 2) (1 / 4)
    (AdaptiveHamiltonianLowerBound.Single.tree ℂ p _ hφ) (endpointReadout J 0) he (by norm_num)
    hs hacc
  have h3 := Entry.heralded_calls_tree hN γ 1 (Real.pi / 2) (1 / 4)
    (AdaptiveHamiltonianLowerBound.Single.tree ℂ p _ hφ) (endpointReadout J 0) he (by norm_num)
    (fun m => by rw [hs m]; norm_num) hacc
  have hc : p.cost (fun _ => 1) = p.count := by
    rw [MultiOracleCircuit.Program.cost_const, mul_one]
  rw [hT, ← hc] at h2 h3
  exact ⟨γ, p, h1, h2, h3, hcost⟩

end

end AdaptiveUnitaryLowerBound.NonVacuity
