import ChebyshevLinearSystem.SignedStep
import ChebyshevLinearSystem.Register
import SparseLinearSystems.Circuit.Run

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

/-!
# Chebyshev filter runs in the released run layer

The released run layer (`SparseLinearSystems/Circuit/Run.lean`) applies counter-masked
forward steps; here the counter register carries the Chebyshev LCU circuit instead. A run of
degree `d` at `(σ, r)` applies the signed steps `l = 1, …, d` with the direction registers
`dirT T d l` (`runLog`), compiled to the released physical oracle family by
`EncodedLabeledProgram.compile` with the signed step programs of `SignedStep.lean`
(`runPhys`). It costs `54 d` matrix-oracle calls and `2 d` source calls (`runPhys_cost_mat`,
`runPhys_cost_src`).

The seed is the clean encoding of `ψ_{b,d} ⊗ J e` (`seedVec`, with the coefficient seed
`seedT` of `Register.lean`); a test measures the flag `v ↦ E (ψ_{b,d} ⊗ v)` (`testFlag`), and
the final run decodes the walk boundary and the solution coordinates (`finalOutput`). For
`2d ≤ T` and `b ∈ (-1, 1)`:

* `test_amplitude`: the decoded test amplitude is `F_{b,d}(W_{σ,r}) J e`;
* `final_amplitude`: the decoded final amplitude is `S† J† F_{b,d}(W_{σ,r}) J e`.

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/

namespace ChebyshevLinearSystem

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseLinearSystems OracleCircuit LogicalWalk
  CounterFilter Step Augmented
open scoped InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-! ### Logical and physical runs -/

/-- The first `l` signed steps of the degree-`d` filter at `(σ, r)`, the first applied
first. -/
def runLog (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (T : ℕ) (σ r : ℝ) (d : ℕ) : ℕ → MultiOracleCircuit.Program (signedLog D Ub sv T)
  | 0 => .identity
  | l + 1 => .seq (.query (σ, r, dirT T d (l + 1))) (runLog D Ub sv T σ r d l)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem runLog_eval (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (T : ℕ) (σ r : ℝ) (d l : ℕ) (x : X) :
    (runLog D Ub sv T σ r d l).eval x = signedStepsT (WwO D Ub sv σ r x) T d l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [runLog, MultiOracleCircuit.Program.eval_seq, ih, MultiOracleCircuit.Program.eval_query]
    rfl

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem runLog_count (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (T : ℕ) (σ r : ℝ) (d l : ℕ) : (runLog D Ub sv T σ r d l).count = l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [runLog, MultiOracleCircuit.Program.count_seq, ih, MultiOracleCircuit.Program.count_query]
    omega

/-- **The physical Chebyshev run**: the `d` signed steps of the degree-`d` filter, every
logical signed step replaced by its implementation `signedStepProg`. -/
def runPhys (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (T : ℕ) (σ r : ℝ) (d : ℕ) : MultiOracleCircuit.Program (physOracle D Ub T) :=
  EncodedLabeledProgram.compile (E D T) (E_isometry D T) (signedStepProg D Ub sv T)
    (runLog D Ub sv T σ r d d)

theorem runPhys_intertwines (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (T : ℕ) (σ r : ℝ) (d : ℕ)
    (x : X) :
    (runPhys D Ub sv T σ r d).eval x ∘L E D T =
      E D T ∘L signedStepsT (WwO D Ub sv σ r x) T d d := by
  rw [runPhys, EncodedLabeledProgram.compile_eval (E D T) (E_isometry D T)
    (signedStepProg D Ub sv T) (physOracle_unitary D Ub hUb T) (signedLog_unitary D Ub sv T)
    (fun l y => signedStepProg_intertwines D Ub hUb sv T l y), runLog_eval]

theorem runPhys_unitary (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (T : ℕ) (σ r : ℝ) (d : ℕ)
    (x : X) : IsUnitary ((runPhys D Ub sv T σ r d).eval x) :=
  (runPhys D Ub sv T σ r d).eval_unitary (physOracle_unitary D Ub hUb T) x

theorem runPhys_cost_mat (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (T : ℕ) (σ r : ℝ) (d : ℕ) : (runPhys D Ub sv T σ r d).cost wMat = d * 54 := by
  rw [runPhys, EncodedLabeledProgram.compile_cost]
  simp only [signedStepProg_cost_mat, MultiOracleCircuit.Program.cost_const, runLog_count]

theorem runPhys_cost_src (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (T : ℕ) (σ r : ℝ) (d : ℕ) : (runPhys D Ub sv T σ r d).cost wSrc = d * 2 := by
  rw [runPhys, EncodedLabeledProgram.compile_cost]
  simp only [signedStepProg_cost_src, MultiOracleCircuit.Program.cost_const, runLog_count]

/-! ### Seeds, flags and outputs -/

omit [DecidableEq n] in
theorem seedT_norm {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) {T d : ℕ} (hT : 2 * d ≤ T)
    (v : PrivO n) : ‖seedT (V := PrivO n) b T d v‖ = ‖v‖ :=
  ((seedT (V := PrivO n) b T d).norm_map_iff_adjoint_comp_self.mpr (seedT_isometry hb hT)) v

/-- The seed `E (ψ_{b,d} ⊗ J e)`. -/
def seedVec (D : NativeSparseBlockEncoding.Data X n Z s) (b : ℝ) (T d : ℕ) : Phys n Z T :=
  E D T (seedT b T d (JwO D eVec))

theorem seedVec_norm (D : NativeSparseBlockEncoding.Data X n Z s) {b : ℝ}
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1) {T d : ℕ} (hT : 2 * d ≤ T) : ‖seedVec D b T d‖ = 1 := by
  rw [seedVec, Run.E_norm, seedT_norm hb hT, LinearIsometry.norm_map, Run.norm_eVec]

/-- The flag `v ↦ E (ψ_{b,d} ⊗ v)`. -/
def testFlag (D : NativeSparseBlockEncoding.Data X n Z s) (b : ℝ) (T d : ℕ) :
    PrivO n →L[ℂ] Phys n Z T :=
  E D T ∘L seedT b T d

theorem testFlag_isometry (D : NativeSparseBlockEncoding.Data X n Z s) {b : ℝ}
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1) {T d : ℕ} (hT : 2 * d ≤ T) :
    (testFlag D b T d)† ∘L testFlag D b T d = 1 := by
  rw [testFlag, adjoint_comp, comp_assoc, ← comp_assoc _ _ (seedT b T d), E_isometry,
    Run.one_comp', seedT_isometry hb hT]

/-- The final output isometry `y ↦ E (ψ_{b,d} ⊗ J (S y))`. -/
def finalOutput (D : NativeSparseBlockEncoding.Data X n Z s) (b : ℝ) (T d : ℕ) :
    V0 →L[ℂ] Phys n Z T :=
  testFlag D b T d ∘L ((JwO D).toContinuousLinearMap ∘L solEmb)

theorem finalOutput_isometry (D : NativeSparseBlockEncoding.Data X n Z s) {b : ℝ}
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1) {T d : ℕ} (hT : 2 * d ≤ T) :
    (finalOutput D b T d)† ∘L finalOutput D b T d = 1 := by
  rw [finalOutput, adjoint_comp, comp_assoc,
    ← comp_assoc _ _ ((JwO D).toContinuousLinearMap ∘L _), testFlag_isometry D hb hT,
    Run.one_comp', adjoint_comp, comp_assoc, ← comp_assoc _ _ (solEmb (V₀ := V0)),
    LinearIsometry.adjoint_comp_self, Run.one_comp', solEmb_isometry]

/-! ### Success block and decoded amplitudes -/

/-- **The success block of a Chebyshev run** is exactly the filter: compressed by the flag
`E (ψ_{b,d} ⊗ ·)`, the physical run of the `d` signed steps is `F_{b,d}(W_{σ,r}(x))`, for every
input. -/
theorem run_success_block (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) {T d : ℕ}
    (hT : 2 * d ≤ T) (σ r : ℝ) (x : X) :
    ((testFlag D b T d)†) ∘L ((runPhys D Ub sv T σ r d).eval x ∘L testFlag D b T d) =
      ChebyshevFilter.filterOp (WwO D Ub sv σ r x) b d := by
  ext v
  have hrun := congrArg (fun A : Ctr T (PrivO n) →L[ℂ] Phys n Z T => A (seedT b T d v))
    (runPhys_intertwines D Ub hUb sv T σ r d x)
  simp only [comp_apply] at hrun
  rw [comp_apply, comp_apply, testFlag, comp_apply, hrun, adjoint_comp, comp_apply,
    Run.E_adjoint_apply, lcuT_apply _ hb hT]

/-- **The LCU circuit of Proposition `qls:prop:chebyshev` as a physical program for the
released walk**: the flag has normalisation one, the success block of the `d` signed steps is
exactly `F_{b,d}(W_{σ,r}(x))` on every input, and the run makes `54 d` matrix-oracle calls
and `2 d` source calls. -/
theorem chebyshev_run (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) {T d : ℕ}
    (hT : 2 * d ≤ T) (σ r : ℝ) :
    (testFlag D b T d)† ∘L testFlag D b T d = 1 ∧
      (∀ x, ((testFlag D b T d)†) ∘L ((runPhys D Ub sv T σ r d).eval x ∘L testFlag D b T d) =
        ChebyshevFilter.filterOp (WwO D Ub sv σ r x) b d) ∧
      (runPhys D Ub sv T σ r d).cost wMat = d * 54 ∧
      (runPhys D Ub sv T σ r d).cost wSrc = d * 2 :=
  ⟨testFlag_isometry D hb hT, fun x => run_success_block D Ub hUb sv hb hT σ r x,
    runPhys_cost_mat D Ub sv T σ r d, runPhys_cost_src D Ub sv T σ r d⟩

/-- **The decoded test amplitude** is the Chebyshev-filtered seed `F_{b,d}(W_{σ,r}) J e`. -/
theorem test_amplitude (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) {T d : ℕ}
    (hT : 2 * d ≤ T) (σ r : ℝ) (x : X) :
    ((testFlag D b T d)†) ((runPhys D Ub sv T σ r d).eval x (seedVec D b T d)) =
      ChebyshevFilter.filterOp (WwO D Ub sv σ r x) b d ((JwO D).toContinuousLinearMap eVec) := by
  have hrun := congrArg
    (fun A : Ctr T (PrivO n) →L[ℂ] Phys n Z T => A (seedT b T d (JwO D eVec)))
    (runPhys_intertwines D Ub hUb sv T σ r d x)
  simp only [comp_apply] at hrun
  rw [seedVec, testFlag, adjoint_comp, comp_apply, hrun, Run.E_adjoint_apply,
    lcuT_apply _ hb hT, LinearIsometry.coe_toContinuousLinearMap]

/-- **The decoded final amplitude**: the solution coordinates of `J† F_{b,d}(W_{σ,r}) J e`. -/
theorem final_amplitude (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) {T d : ℕ}
    (hT : 2 * d ≤ T) (σ r : ℝ) (x : X) :
    ((finalOutput D b T d)†) ((runPhys D Ub sv T σ r d).eval x (seedVec D b T d)) =
      (solEmb†) (((JwO D).toContinuousLinearMap†)
        (ChebyshevFilter.filterOp (WwO D Ub sv σ r x) b d
          ((JwO D).toContinuousLinearMap eVec))) := by
  rw [finalOutput, adjoint_comp, comp_apply, test_amplitude D Ub hUb sv hb hT σ r x,
    adjoint_comp, comp_apply]

end

end ChebyshevLinearSystem
