import GeneralODE.Native.LCU
import GeneralODE.Block.Programs
import GeneralODE.Analysis.Decode
import SparseODE.ODECompleteSuccess

/-!
# Damping, randomized amplification and four bounded attempts

Let `p` be a program with a unit seed `ψ` and an isometric output decoder `F`,
whose decoded output `F† p ψ` has norm at least `1/(2g)` and direction within
`η` of a target, up to a phase.  A fixed damping qubit halves the decoded
amplitude, so that it lies in `[1/(4g), 1/2]`; the released randomized
amplification (a uniform number `j < ⌈4g⌉` of Grover steps built from the
damped program, its inverse and fixed reflections) then has mean success at
least `1/4` and keeps the output direction.  The released four-attempt
wrapper turns this into success probability at least `175/256 > 2/3`, with
conditional mixed output within trace distance `η` of the target state.  In
every history, every weighted query count is at most `40 g` times that of `p`.
The damping gate is fixed and the oracles are those of `p` with the damping
qubit as a spectator.
-/

namespace SparseHamiltonian.GeneralODE.Amplify

noncomputable section
open ContinuousLinearMap OracleCircuit ODEStateNormalization LCU Registers
open scoped InnerProduct BigOperators ComplexConjugate
set_option maxHeartbeats 1000000

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
  [FiniteDimensional ℂ R]

/-- The register with one damping qubit. -/
abbrev Damped (R : Type*) [NormedAddCommGroup R] [InnerProductSpace ℂ R] :=
  PiLp 2 (fun _ : Bool => R)

/-- The tilted qubit state `(√3/2)|0⟩ + (1/2)|1⟩`. -/
def tiltVec : EuclideanSpace ℂ Bool :=
  WithLp.toLp 2 (fun b => if b then ((1 / 2 : ℝ) : ℂ) else ((Real.sqrt 3 / 2 : ℝ) : ℂ))

theorem norm_tiltVec : ‖tiltVec‖ = 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq : ‖tiltVec‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_bool]
    simp only [tiltVec, PiLp.toLp_apply, if_true, Bool.false_eq_true, if_false, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    rw [div_pow, div_pow, h3]
    norm_num
  have h0 := norm_nonneg tiltVec
  nlinarith [sq_nonneg (‖tiltVec‖ - 1)]

theorem norm_single_bool (b : Bool) : ‖(EuclideanSpace.single b (1 : ℂ) : EuclideanSpace ℂ Bool)‖ = 1 := by
  simp

/-- The fixed damping unitary: `|0⟩ ⊗ v ↦ |tilt⟩ ⊗ v`. -/
def damper (R : Type*) [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
    [FiniteDimensional ℂ R] : Damped R →L[ℂ] Damped R :=
  Classical.choose (exists_unitary_comp
    (branchState (P := R) (EuclideanSpace.single false 1)) (branchState (P := R) tiltVec)
    (branchState_isometry _ (norm_single_bool false)) (branchState_isometry _ norm_tiltVec))

theorem damper_spec : IsUnitary (damper R) ∧
    damper R ∘L branchState (P := R) (EuclideanSpace.single false 1) =
      branchState (P := R) tiltVec :=
  Classical.choose_spec (exists_unitary_comp
    (branchState (P := R) (EuclideanSpace.single false 1)) (branchState (P := R) tiltVec)
    (branchState_isometry _ (norm_single_bool false)) (branchState_isometry _ norm_tiltVec))

/-- A spectator lift commutes with a branch state. -/
theorem diag_branchState (W : R →L[ℂ] R) (a : EuclideanSpace ℂ Bool) (v : R) :
    diagHom Bool R W (branchState a v) = branchState a (W v) := by
  ext i
  simp only [diagHom_apply_apply, branchState_apply, map_smul]

/-- The `true` sector of a tilted branch state carries half the amplitude. -/
theorem true_tilt (u : R) :
    ((branchState (P := R) (EuclideanSpace.single true 1))†) (branchState tiltVec u) =
      ((1 / 2 : ℝ) : ℂ) • u := by
  rw [branchState_adjoint, branchCostate_apply, Fintype.sum_bool]
  simp [tiltVec, branchState_apply]

variable {P X L : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [FiniteDimensional ℂ P]

/-- The oracles with the damping qubit as a spectator. -/
def liftOracle (O : (L ⊕ Bool) → X → R →L[ℂ] R) :
    (L ⊕ Bool) → X → Damped R →L[ℂ] Damped R :=
  fun l x => diagHom Bool R (O l x)

omit [FiniteDimensional ℂ R] in
theorem liftOracle_unitary {O : (L ⊕ Bool) → X → R →L[ℂ] R} (hO : ∀ l x, IsUnitary (O l x)) :
    ∀ l x, IsUnitary (liftOracle O l x) :=
  fun l x => isUnitary_map _ (hO l x)

variable {O : (L ⊕ Bool) → X → R →L[ℂ] R}

/-- The damped program: run `p`, then the damping gate. -/
def damped (p : MultiOracleCircuit.Program O) : MultiOracleCircuit.Program (liftOracle O) :=
  .seq (.fixed (damper R) damper_spec.1) (MultiOracleCircuit.Program.mapHom (diagHom Bool R) id p)

theorem damped_eval (p : MultiOracleCircuit.Program O) (x : X) :
    (damped p).eval x = damper R * diagHom Bool R (p.eval x) := by
  change damper R * (MultiOracleCircuit.Program.mapHom (diagHom Bool R) id p).eval x = _
  rw [MultiOracleCircuit.Program.eval_mapHom (diagHom Bool R) id (fun l y => rfl) p x]

theorem damped_cost (p : MultiOracleCircuit.Program O) (w : (L ⊕ Bool) → ℕ) :
    (damped p).cost w = p.cost w := by
  change 0 + (MultiOracleCircuit.Program.mapHom (diagHom Bool R) id p).cost w = _
  rw [MultiOracleCircuit.Program.cost_mapHom]
  simp

/-- The damped seed `|0⟩ ⊗ ψ`. -/
def seedD (ψ : R) : Damped R := branchState (EuclideanSpace.single false 1) ψ

theorem seedD_norm (ψ : R) (hψ : ‖ψ‖ = 1) : ‖seedD ψ‖ = 1 := by
  unfold seedD
  rw [(branchState (P := R) (EuclideanSpace.single false 1)).norm_map_iff_adjoint_comp_self.mpr
    (branchState_isometry _ (norm_single_bool false)), hψ]

/-- The damped output decoder `|1⟩ ⊗ F`. -/
def outF (F : P →L[ℂ] R) : P →L[ℂ] Damped R :=
  branchState (P := R) (EuclideanSpace.single true 1) ∘L F

omit [FiniteDimensional ℂ P] in
theorem outF_isometry (F : P →L[ℂ] R) (hF : F† ∘L F = 1) : (outF F)† ∘L outF F = 1 := by
  unfold outF
  rw [adjoint_comp, comp_assoc, ← comp_assoc _ _ F, branchState_isometry _ (norm_single_bool true),
    one_comp_eq, hF]

omit [FiniteDimensional ℂ P] in
/-- The damped program decodes to half the original decoded output. -/
theorem damped_decoded (p : MultiOracleCircuit.Program O) (F : P →L[ℂ] R) (ψ : R) (x : X) :
    ((outF F)†) ((damped p).eval x (seedD ψ)) = ((1 / 2 : ℝ) : ℂ) • (F†) (p.eval x ψ) := by
  have hD := congrArg (fun T : R →L[ℂ] Damped R => T (p.eval x ψ)) damper_spec.2
  simp only [comp_apply] at hD
  rw [damped_eval, mul_apply_eq_comp, seedD, diag_branchState, hD, outF, adjoint_comp,
    comp_apply, true_tilt, map_smul]

/-- The trials: `j` Grover steps of the damped program. -/
def trials (p : MultiOracleCircuit.Program O) (F : P →L[ℂ] R) (hF : F† ∘L F = 1)
    (ψ : R) (hψ : ‖ψ‖ = 1) (j : ℕ) : MultiOracleCircuit.Program (liftOracle O) :=
  ODECountedAmplification.program (damped p) (outF F) (outF_isometry F hF) (seedD ψ)
    (seedD_norm ψ hψ) j

/-- The complete protocol: at most four attempts, each with a uniform
number `j < ⌈4g⌉` of Grover steps. -/
def protocol (p : MultiOracleCircuit.Program O) (F : P →L[ℂ] R) (hF : F† ∘L F = 1)
    (ψ : R) (hψ : ‖ψ‖ = 1) (g : ℝ) (hg : 1 ≤ g) :
    ODERepeatProtocol.Protocol (liftOracle O) P :=
  ODERepeatProtocol.fourTrials (trials p F hF ψ hψ) (ODEGroverAverage.chosenIterations g)
    (ODEGroverAverage.chosenIterations_bounds g hg).1 (seedD ψ) (seedD_norm ψ hψ) (outF F)
    (outF_isometry F hF)

omit [FiniteDimensional ℂ P] in
/-- Worst-case weighted count over every history: at most `40 g` times that of `p`. -/
theorem protocol_worstCost (p : MultiOracleCircuit.Program O) (F : P →L[ℂ] R) (hF : F† ∘L F = 1)
    (ψ : R) (hψ : ‖ψ‖ = 1) (g : ℝ) (hg : 1 ≤ g) (w : (L ⊕ Bool) → ℕ) :
    ((protocol p F hF ψ hψ g hg).worstCost w : ℝ) ≤ 40 * g * (p.cost w : ℝ) := by
  have h := ODERepeatProtocol.fourTrials_worstCost_le (trials p F hF ψ hψ)
    (ODEGroverAverage.chosenIterations g) (ODEGroverAverage.chosenIterations_bounds g hg).1
    (seedD ψ) (seedD_norm ψ hψ) (outF F) (outF_isometry F hF) w (10 * g * (p.cost w : ℝ))
    (fun j hj => by
      have := ODECountedAmplification.cost_le (damped p) (outF F) (outF_isometry F hF) (seedD ψ)
        (seedD_norm ψ hψ) g hg j hj w
      rw [damped_cost] at this
      exact this)
  unfold protocol
  linarith

/-- The guarantees of the protocol on one input. -/
structure Outcome {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {L' : Type*} {O' : L' → X → K →L[ℂ] K} (prot : ODERepeatProtocol.Protocol O' P) (x : X)
    (target : P) (η : ℝ) : Prop where
  success_lower : (175 : ℝ) / 256 ≤ prot.successMass x
  success_two_thirds : (2 : ℝ) / 3 ≤ prot.successMass x
  output_density : ODEMixedOutput.IsDensity (prot.conditionalDensity x)
  conditional_error :
    ∃ h : (prot.conditionalDensity x -
        ODEMixedOutput.pureOperator (unitDirection target)).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance (prot.conditionalDensity x)
        (ODEMixedOutput.pureOperator (unitDirection target)) h ≤ η

set_option maxHeartbeats 2000000 in
/-- **Amplification certificate.** -/
theorem outcome (p : MultiOracleCircuit.Program O) (hO : ∀ l y, IsUnitary (O l y))
    (F : P →L[ℂ] R) (hF : F† ∘L F = 1) (ψ : R) (hψ : ‖ψ‖ = 1) (g : ℝ) (hg : 1 ≤ g)
    (x : X) (target : P) (htarget : target ≠ 0) (η : ℝ)
    (hamp : 1 / (2 * g) ≤ ‖(F†) (p.eval x ψ)‖)
    (hdir : ∃ ω : ℂ, ‖ω‖ = 1 ∧
      ‖ω • unitDirection ((F†) (p.eval x ψ)) - unitDirection target‖ ≤ η) :
    Outcome (protocol p F hF ψ hψ g hg) x target η := by
  obtain ⟨ω, hω, hωη⟩ := hdir
  set F' := outF F with hF'def
  have hF' : F'† ∘L F' = 1 := outF_isometry F hF
  set ψ' := seedD ψ with hψ'def
  have hψ' : ‖ψ'‖ = 1 := seedD_norm ψ hψ
  set W' := (damped p).eval x with hW'def
  have hO' := liftOracle_unitary hO
  have hW' : IsUnitary W' := (damped p).eval_unitary hO' x
  have hdec : (F'†) (W' ψ') = ((1 / 2 : ℝ) : ℂ) • (F†) (p.eval x ψ) := damped_decoded p F ψ x
  -- amplitude
  have hWψ : ‖p.eval x ψ‖ = 1 := by
    rw [(p.eval x).norm_map_iff_adjoint_comp_self.mpr (p.eval_unitary hO x).1, hψ]
  have ha1 : ‖(F†) (p.eval x ψ)‖ ≤ 1 := by
    calc ‖(F†) (p.eval x ψ)‖ ≤ ‖F†‖ * ‖p.eval x ψ‖ := (F†).le_opNorm _
      _ ≤ 1 * 1 := by
        rw [hWψ]
        exact mul_le_mul_of_nonneg_right (Decode.norm_adjoint_le_one F hF) zero_le_one
      _ = 1 := one_mul 1
  have hamp' : ODEGroverActual.amplitude F' W' ψ' = (1 / 2) * ‖(F†) (p.eval x ψ)‖ := by
    change ‖ODEHeraldedSuccess.successfulComponent F' W' ψ'‖ = _
    rw [ODEHeraldedSuccess.successfulComponent_norm F' hF', ODEHeraldedSuccess.decoded, hdec,
      norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hg0 : 0 < g := by linarith
  have hLower : 1 / (4 * g) ≤ ODEGroverActual.amplitude F' W' ψ' := by
    rw [hamp']
    have : 1 / (4 * g) = (1 / 2) * (1 / (2 * g)) := by field_simp; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hamp (by norm_num)
  have hUpper : ODEGroverActual.amplitude F' W' ψ' ≤ 1 / 2 := by
    rw [hamp']; linarith
  -- phase-rotated target
  set c : ℂ := star ω with hc
  have hcn : ‖c‖ = 1 := by rw [hc, norm_star, hω]
  have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at hcn; norm_num at hcn
  have hcω : c * ω = 1 := by
    have h1 : ((Complex.normSq ω : ℝ) : ℂ) = (starRingEnd ℂ) ω * ω := Complex.normSq_eq_conj_mul_self
    rw [Complex.normSq_eq_norm_sq, hω] at h1
    rw [hc, ← starRingEnd_apply, ← h1]
    norm_num
  have hcdir : unitDirection (c • target) = c • unitDirection target := by
    rw [Decode.unitDirection_smul c hc0, hcn]
    simp
  have hdirdec : unitDirection ((F'†) (W' ψ')) = unitDirection ((F†) (p.eval x ψ)) := by
    rw [hdec, Complex.coe_smul]
    exact Decode.unitDirection_real_smul _ (by norm_num) _
  have hError : ‖unitDirection ((F'†) (W' ψ')) - unitDirection (c • target)‖ ≤ η := by
    rw [hdirdec, hcdir]
    have : unitDirection ((F†) (p.eval x ψ)) - c • unitDirection target =
        c • (ω • unitDirection ((F†) (p.eval x ψ)) - unitDirection target) := by
      rw [smul_sub, smul_smul, hcω, one_smul]
    rw [this, norm_smul, hcn, one_mul]
    exact hωη
  obtain ⟨hM, -, hSuccess, hDirection⟩ := ODEGroverActual.randomized_certificate F' hF' W' hW'
    ψ' hψ' g hg hLower hUpper (c • target) η hError
  -- the trial programs
  set M := ODEGroverAverage.chosenIterations g with hMdef
  set q := trials p F hF ψ hψ with hqdef
  have hState (j : ℕ) : (q j).eval x ψ' = ODEGroverActual.trial F' W' ψ' j :=
    ODECountedAmplification.state_eq (damped p) F' hF' ψ' hψ' j x hW'
  have hUq : ∀ j, IsUnitary ((q j).eval x) := fun j => (q j).eval_unitary hO' x
  have hmean : (1 : ℝ) / 4 ≤ ODERepeatProbability.mean (ODERepeatProbability.probability q M ψ' F' x) := by
    rw [ODERepeatProbability.mean_eq_projector_average q M ψ' F' x hF']
    simpa only [ODEGroverActual.meanProbability, ODEGroverActual.probability, hState] using hSuccess
  have hupper : ODERepeatProbability.mean (ODERepeatProbability.probability q M ψ' F' x) ≤ 1 :=
    ODERepeatProbability.mean_le_one _ hM
      (ODERepeatProbability.probability_le_one q M ψ' F' x hψ' hF' hUq)
  have hsucc : (protocol p F hF ψ hψ g hg).successMass x =
      ODERepeatProbability.successProbability (ODERepeatProbability.probability q M ψ' F' x) :=
    ODERepeatProtocol.fourTrials_successMass_eq q M hM ψ' hψ' F' hF' x
  have hdens : (protocol p F hF ψ hψ g hg).conditionalDensity x =
      ODEMixedOutput.ensemble
        (ODERepeatProbability.conditionalWeight (ODERepeatProbability.probability q M ψ' F' x))
        (fun a : Fin 4 × Fin M => unitDirection (ODERepeatProbability.decoded q ψ' F' x a.2.val)) :=
    ODERepeatProtocol.fourTrials_conditionalDensity_eq q M hM ψ' hψ' F' hF' x
  have hw := ODERepeatProbability.conditionalWeight_nonneg _
    (ODERepeatProbability.probability_nonneg q M ψ' F' x) hmean hupper
  have hsum := ODERepeatProbability.conditionalWeight_sum _ hmean hupper
  have hunit : ∀ a : Fin 4 × Fin M,
      ODERepeatProbability.conditionalWeight (ODERepeatProbability.probability q M ψ' F' x) a ≠ 0 →
      ‖unitDirection (ODERepeatProbability.decoded q ψ' F' x a.2.val)‖ = 1 := fun a ha =>
    unitDirection_norm _ (ODERepeatProbability.conditionalWeight_decoded_ne_zero q M ψ' F' x a ha)
  have hclose : ∀ a : Fin 4 × Fin M,
      ODERepeatProbability.conditionalWeight (ODERepeatProbability.probability q M ψ' F' x) a ≠ 0 →
      ∃ ω' : ℂ, ‖ω'‖ = 1 ∧
        ‖ω' • unitDirection (ODERepeatProbability.decoded q ψ' F' x a.2.val) -
          unitDirection target‖ ≤ η := by
    intro a ha
    have hne := ODERepeatProbability.conditionalWeight_decoded_ne_zero q M ψ' F' x a ha
    have hdq : ODERepeatProbability.decoded q ψ' F' x a.2.val =
        ODEGroverActual.decoded F' W' ψ' a.2.val := by
      unfold ODERepeatProbability.decoded ODEGroverActual.decoded
      rw [hState]
    rw [hdq] at hne ⊢
    obtain ⟨ω'', hω'', hclose''⟩ := hDirection a.2.val hne
    refine ⟨ω * ω'', by rw [norm_mul, hω, hω'', one_mul], ?_⟩
    have : (ω * ω'') • unitDirection (ODEGroverActual.decoded F' W' ψ' a.2.val) -
        unitDirection target =
        ω • (ω'' • unitDirection (ODEGroverActual.decoded F' W' ψ' a.2.val) -
          unitDirection (c • target)) := by
      rw [hcdir, smul_sub, smul_smul, smul_smul, mul_comm ω c, hcω, one_smul, mul_smul]
    rw [this, norm_smul, hω, one_mul]
    exact hclose''
  obtain ⟨hDensity, hSymm, hDistance⟩ := ODEMixedOutput.ensemble_trace_distance_le
    (ODERepeatProbability.conditionalWeight (ODERepeatProbability.probability q M ψ' F' x))
    (fun a : Fin 4 × Fin M => unitDirection (ODERepeatProbability.decoded q ψ' F' x a.2.val))
    (unitDirection target) η hw hsum hunit (unitDirection_norm target htarget) hclose
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsucc]
    exact ODERepeatProbability.successProbability_lower _ hmean hupper
  · rw [hsucc]
    exact ODERepeatProbability.successProbability_two_thirds _ hmean hupper
  · rw [hdens]
    exact hDensity
  · rw [hdens]
    exact ⟨hSymm, hDistance⟩

end

end SparseHamiltonian.GeneralODE.Amplify
