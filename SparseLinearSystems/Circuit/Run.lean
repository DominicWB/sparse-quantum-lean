import SparseLinearSystems.Circuit.Step

/-!
# Filter runs: compiled circuits, seeds, flags and amplitudes

A run with parameters `(σ, r)` applies the counter-masked walk steps
`t = 1, …, t₀` (`runLog`), compiled to the physical oracle family by
`EncodedLabeledProgram.compile` (`runPhys`).  It costs `54 t₀` matrix queries
and `2 t₀` source calls (`runPhys_cost_mat`, `runPhys_cost_src`).

All runs use one workspace with `T + 1` counter values.  The seed is the clean
encoding of `ψ ⊗ J e` (`seedVec`).  A test measures the counter flag
`v ↦ E (ψ ⊗ v)` (`testFlag`); the final run additionally decodes the walk
boundary and the solution coordinates (`finalOutput`).  For `k (N - 1) ≤ t₀ ≤ T`:

* `test_amplitude`: the decoded test amplitude is `f_N(W)^k J e`;
* `final_amplitude`: the decoded final amplitude is `S† J† f_N(W)^k J e`.

Both are stated for the walk `Ww` on the original space.

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/

namespace SparseLinearSystems.Run

noncomputable section
open SparseHamiltonian
open ContinuousLinearMap OracleCircuit HilbertAugmentation Augmented SparseBranch LogicalWalk
  CounterFilter Cells Step
open scoped InnerProduct
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-! ### Logical and physical runs -/

/-- The first `t` counter-masked walk steps, the first applied first. -/
def runLog (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (T : ℕ) (σ r : ℝ) : ℕ → MultiOracleCircuit.Program (logOracle D Ub sv T)
  | 0 => .identity
  | t + 1 => .seq (.query (σ, r, stepMask T (t + 1))) (runLog D Ub sv T σ r t)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem runLog_eval (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (T : ℕ) (σ r : ℝ) (t : ℕ) (x : X) :
    (runLog D Ub sv T σ r t).eval x = steps T (WwO D Ub sv σ r x) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [runLog, MultiOracleCircuit.Program.eval_seq, ih, MultiOracleCircuit.Program.eval_query]
    rfl

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem runLog_count (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (T : ℕ) (σ r : ℝ) (t : ℕ) : (runLog D Ub sv T σ r t).count = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [runLog, MultiOracleCircuit.Program.count_seq, ih, MultiOracleCircuit.Program.count_query]
    omega

/-- **The physical run**: every logical step replaced by its primitive implementation. -/
def runPhys (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (T : ℕ) (σ r : ℝ) (t : ℕ) : MultiOracleCircuit.Program (physOracle D Ub T) :=
  EncodedLabeledProgram.compile (E D T) (E_isometry D T) (stepProg D Ub sv T)
    (runLog D Ub sv T σ r t)

theorem runPhys_intertwines (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (T : ℕ) (σ r : ℝ)
    (t : ℕ) (x : X) :
    (runPhys D Ub sv T σ r t).eval x ∘L E D T = E D T ∘L steps T (WwO D Ub sv σ r x) t := by
  rw [runPhys, EncodedLabeledProgram.compile_eval (E D T) (E_isometry D T) (stepProg D Ub sv T)
    (physOracle_unitary D Ub hUb T) (logOracle_unitary D Ub sv T)
    (fun l y => stepProg_intertwines D Ub hUb sv T l y), runLog_eval]

theorem runPhys_unitary (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (T : ℕ) (σ r : ℝ)
    (t : ℕ) (x : X) : IsUnitary ((runPhys D Ub sv T σ r t).eval x) :=
  (runPhys D Ub sv T σ r t).eval_unitary (physOracle_unitary D Ub hUb T) x

theorem runPhys_cost_mat (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (T : ℕ) (σ r : ℝ) (t : ℕ) : (runPhys D Ub sv T σ r t).cost wMat = t * 54 := by
  rw [runPhys, EncodedLabeledProgram.compile_cost]
  simp only [stepProg_cost_mat, MultiOracleCircuit.Program.cost_const, runLog_count]

theorem runPhys_cost_src (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (T : ℕ) (σ r : ℝ) (t : ℕ) : (runPhys D Ub sv T σ r t).cost wSrc = t * 2 := by
  rw [runPhys, EncodedLabeledProgram.compile_cost]
  simp only [stepProg_cost_src, MultiOracleCircuit.Program.cost_const, runLog_count]

/-! ### Transport of the filter -/

omit [DecidableEq n] in
theorem opO_avg (W : Priv n →L[ℂ] Priv n) (N : ℕ) :
    opO (UnitaryFilter.avg W N) = UnitaryFilter.avg (opO W) N := by
  rw [UnitaryFilter.avg, UnitaryFilter.avg, opO_smul, opO_sum]
  simp only [opO_pow]

omit [DecidableEq n] in
theorem opO_filter (W : Priv n →L[ℂ] Priv n) (N k : ℕ) :
    opO (UnitaryFilter.filter W N k) = UnitaryFilter.filter (opO W) N k := by
  rw [UnitaryFilter.filter, UnitaryFilter.filter, opO_pow, opO_avg]

theorem JwO_apply (D : NativeSparseBlockEncoding.Data X n Z s) (v : Pub V0) :
    JwO D v = toO (Jw D v) := rfl

/-- The filtered seed in the opaque copy is the transported filtered seed. -/
theorem filter_JwO (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (σ r : ℝ) (x : X) (N k : ℕ) (v : Pub V0) :
    UnitaryFilter.filter (WwO D Ub sv σ r x) N k (JwO D v) =
      toO (UnitaryFilter.filter (Ww D Ub sv σ r x) N k (Jw D v)) := by
  rw [WwO, ← opO_filter, opO_apply, JwO_apply, toO_symm_apply_apply]

theorem JwO_adjoint_toO (D : NativeSparseBlockEncoding.Data X n Z s) (w : Priv n) :
    ((JwO D).toContinuousLinearMap†) (toO w) = ((Jw D).toContinuousLinearMap†) w := by
  apply ext_inner_left ℂ
  intro y
  rw [adjoint_inner_right, adjoint_inner_right, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.coe_toContinuousLinearMap, JwO_apply, LinearIsometryEquiv.inner_map_map]

/-! ### Seeds, flags and outputs -/

theorem one_comp' {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (f : E →L[ℂ] F) : (1 : F →L[ℂ] F) ∘L f = f :=
  id_comp f

theorem E_norm (D : NativeSparseBlockEncoding.Data X n Z s) (T : ℕ) (v : Ctr T (PrivO n)) :
    ‖E D T v‖ = ‖v‖ :=
  ((NativeMaskedOracle.input (ι := Idx T) (NativeCayleyProgram.cleanBasis D)).comp
    (Enc D T)).norm_map v

theorem E_adjoint_apply (D : NativeSparseBlockEncoding.Data X n Z s) (T : ℕ)
    (v : Ctr T (PrivO n)) : ((E D T)†) (E D T v) = v := by
  have h := congrArg (fun A : Ctr T (PrivO n) →L[ℂ] Ctr T (PrivO n) => A v) (E_isometry D T)
  simpa only [comp_apply, one_apply_eq_self] using h

omit [DecidableEq n] in
theorem seedMap_norm (N k T : ℕ) (hN : 0 < N) (hT : k * (N - 1) ≤ T) (v : PrivO n) :
    ‖seedMap (V := PrivO n) N k T v‖ = ‖v‖ :=
  ((seedMap (V := PrivO n) N k T).norm_map_iff_adjoint_comp_self.mpr
    (seedMap_isometry N k T hN hT)) v

omit [DecidableEq n] in
theorem norm_eVec : ‖(eVec : Pub V0)‖ = 1 := by
  have h : ‖(eVec : Pub V0)‖ ^ 2 = 1 ^ 2 := by
    rw [norm_sq_pub]
    simp [eVec]
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp h

/-- The seed `E (ψ ⊗ J e)`. -/
def seedVec (D : NativeSparseBlockEncoding.Data X n Z s) (N k T : ℕ) : Phys n Z T :=
  E D T (seedMap N k T (JwO D eVec))

theorem seedVec_norm (D : NativeSparseBlockEncoding.Data X n Z s) (N k T : ℕ) (hN : 0 < N)
    (hT : k * (N - 1) ≤ T) : ‖seedVec D N k T‖ = 1 := by
  rw [seedVec, E_norm, seedMap_norm N k T hN hT, LinearIsometry.norm_map, norm_eVec]

/-- The test flag `v ↦ E (ψ ⊗ v)`. -/
def testFlag (D : NativeSparseBlockEncoding.Data X n Z s) (N k T : ℕ) :
    PrivO n →L[ℂ] Phys n Z T :=
  E D T ∘L seedMap N k T

theorem testFlag_isometry (D : NativeSparseBlockEncoding.Data X n Z s) (N k T : ℕ) (hN : 0 < N)
    (hT : k * (N - 1) ≤ T) : (testFlag D N k T)† ∘L testFlag D N k T = 1 := by
  rw [testFlag, adjoint_comp, comp_assoc, ← comp_assoc _ _ (seedMap N k T), E_isometry, one_comp',
    seedMap_isometry N k T hN hT]

/-- The final output isometry `y ↦ E (ψ ⊗ J (S y))`. -/
def finalOutput (D : NativeSparseBlockEncoding.Data X n Z s) (N k T : ℕ) : V0 →L[ℂ] Phys n Z T :=
  testFlag D N k T ∘L ((JwO D).toContinuousLinearMap ∘L solEmb)

theorem finalOutput_isometry (D : NativeSparseBlockEncoding.Data X n Z s) (N k T : ℕ)
    (hN : 0 < N) (hT : k * (N - 1) ≤ T) : (finalOutput D N k T)† ∘L finalOutput D N k T = 1 := by
  rw [finalOutput, adjoint_comp, comp_assoc, ← comp_assoc _ _ ((JwO D).toContinuousLinearMap ∘L _),
    testFlag_isometry D N k T hN hT, one_comp', adjoint_comp, comp_assoc,
    ← comp_assoc _ _ (solEmb (V₀ := V0)), LinearIsometry.adjoint_comp_self, one_comp',
    solEmb_isometry]

/-! ### Decoded amplitudes -/

/-- The decoded test amplitude is the filtered seed, in the opaque copy. -/
theorem test_amplitudeO (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (N k T t : ℕ) (ht : k * (N - 1) ≤ t)
    (htT : t ≤ T) (σ r : ℝ) (x : X) :
    ((testFlag D N k T)†) ((runPhys D Ub sv T σ r t).eval x (seedVec D N k T)) =
      UnitaryFilter.filter (WwO D Ub sv σ r x) N k (JwO D eVec) := by
  have hrun := congrArg (fun A : Ctr T (PrivO n) →L[ℂ] Phys n Z T => A (seedMap N k T (JwO D eVec)))
    (runPhys_intertwines D Ub hUb sv T σ r t x)
  simp only [comp_apply] at hrun
  have hc := congrArg (fun A : PrivO n →L[ℂ] PrivO n => A (JwO D eVec))
    (counter_compression_le (WwO D Ub sv σ r x) N k T t ht htT)
  simp only [comp_apply] at hc
  rw [seedVec, testFlag, adjoint_comp, comp_apply, hrun, E_adjoint_apply, hc]

/-- The decoded final amplitude, in the opaque copy. -/
theorem final_amplitudeO (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (N k T t : ℕ) (ht : k * (N - 1) ≤ t)
    (htT : t ≤ T) (σ r : ℝ) (x : X) :
    ((finalOutput D N k T)†) ((runPhys D Ub sv T σ r t).eval x (seedVec D N k T)) =
      (solEmb†) (((JwO D).toContinuousLinearMap†)
        (UnitaryFilter.filter (WwO D Ub sv σ r x) N k (JwO D eVec))) := by
  rw [finalOutput, adjoint_comp, comp_apply, test_amplitudeO D Ub hUb sv N k T t ht htT σ r x,
    adjoint_comp, comp_apply]

/-- The decoded test amplitude is the filtered seed. -/
theorem test_amplitude (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (N k T t : ℕ) (ht : k * (N - 1) ≤ t)
    (htT : t ≤ T) (σ r : ℝ) (x : X) :
    ((testFlag D N k T)†) ((runPhys D Ub sv T σ r t).eval x (seedVec D N k T)) =
      toO (UnitaryFilter.filter (Ww D Ub sv σ r x) N k (Jw D eVec)) := by
  have hrun := congrArg (fun A : Ctr T (PrivO n) →L[ℂ] Phys n Z T => A (seedMap N k T (JwO D eVec)))
    (runPhys_intertwines D Ub hUb sv T σ r t x)
  simp only [comp_apply] at hrun
  have hc := congrArg (fun A : PrivO n →L[ℂ] PrivO n => A (JwO D eVec))
    (counter_compression_le (WwO D Ub sv σ r x) N k T t ht htT)
  simp only [comp_apply] at hc
  rw [seedVec, testFlag, adjoint_comp, comp_apply, hrun, E_adjoint_apply, hc, filter_JwO]

/-- The test success probability is the squared norm of the filtered seed. -/
theorem test_probability (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (N k T t : ℕ) (ht : k * (N - 1) ≤ t)
    (htT : t ≤ T) (σ r : ℝ) (x : X) :
    ‖((testFlag D N k T)†) ((runPhys D Ub sv T σ r t).eval x (seedVec D N k T))‖ ^ 2 =
      ‖UnitaryFilter.filter (Ww D Ub sv σ r x) N k (Jw D eVec)‖ ^ 2 := by
  rw [test_amplitude D Ub hUb sv N k T t ht htT σ r x, norm_toO]

/-- The decoded final amplitude: solution coordinates of `J† f_N(W)^k J e`. -/
theorem final_amplitude (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (N k T t : ℕ) (ht : k * (N - 1) ≤ t)
    (htT : t ≤ T) (σ r : ℝ) (x : X) :
    ((finalOutput D N k T)†) ((runPhys D Ub sv T σ r t).eval x (seedVec D N k T)) =
      (solEmb†) (((Jw D).toContinuousLinearMap†)
        (UnitaryFilter.filter (Ww D Ub sv σ r x) N k (Jw D eVec))) := by
  rw [finalOutput, adjoint_comp, comp_apply, test_amplitude D Ub hUb sv N k T t ht htT σ r x,
    adjoint_comp, comp_apply, JwO_adjoint_toO]

end

end SparseLinearSystems.Run
