import GateEfficientHamiltonian.GateBinaryReuse
/-!
# Exact attenuation and amplification for a uniform initial segment

This module supplies the exact state and operator identities behind the
uniform-range preparation in the gate-efficient Hamiltonian construction.
It derives the initial successful amplitude `1/2` from the actual attenuated
uniform state.  A single pair of reflections yields the desired state with
its attenuation flag clean.

The final preparation-circuit identity exposes all three occurrences of a
preparation unitary.  It does not assign a gate cost to an arbitrary unitary:
the separate bit-level compiler must implement the uniform-word preparation,
the one-qubit attenuation, the initial-zero reflection, and the comparison
phase.  This module compiles with Lean/Mathlib 4.32.1.
-/

namespace SparseHamiltonian.GateUniformRange

noncomputable section
open ContinuousLinearMap InnerProductSpace ComplexAmplitudeRotation OracleCircuit
open scoped BigOperators InnerProduct ComplexConjugate

/-- `N` word positions and one attenuation flag. -/
abbrev Space (N : ℕ) := PiLp 2 (fun _ : Fin N => Qubit)

/-- Attenuation makes the *joint* success amplitude exactly one half. -/
def attenuation (n N : ℕ) : ℝ := Real.sqrt (N : ℝ) / (2 * Real.sqrt (n : ℝ))

theorem attenuation_nonneg (n N : ℕ) : 0 ≤ attenuation n N := by
  unfold attenuation
  positivity

/-- The manuscript uses `N ≤ 2*n`; the rotation only needs `N ≤ 4*n`. -/
theorem attenuation_le_one (n N : ℕ) (hn : 0 < n) (hN : N ≤ 4 * n) :
    attenuation n N ≤ 1 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hNn : (N : ℝ) ≤ 4 * (n : ℝ) := by exact_mod_cast hN
  have hsN := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hsn := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hp := Real.sqrt_pos.2 hnR
  have hb : Real.sqrt (N : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  exact (div_le_one (by positivity)).2 hb

/-- The actual known one-qubit rotation, simultaneously on every word. -/
def attenuationGate (n N : ℕ) : Space N →L[ℂ] Space N :=
  WeightedClock.diagonal (fun _ : Fin N => rotation (attenuation n N : ℂ))

theorem attenuationGate_unitary (n N : ℕ) (hn : 0 < n) (hN : N ≤ 4 * n) :
    IsUnitary (attenuationGate n N) := by
  have hz : ‖(attenuation n N : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (attenuation_nonneg n N)] using attenuation_le_one n N hn hN
  have hu := rotation_unitary (attenuation n N : ℂ) hz
  constructor
  · exact WeightedClock.diagonal_isometry _ (fun _ => hu.1)
  · change attenuationGate n N ∘L (attenuationGate n N)† = 1
    rw [attenuationGate, WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    have hright : rotation (attenuation n N : ℂ) ∘L
        (rotation (attenuation n N : ℂ))† = 1 := hu.2
    simp only [hright, WeightedClock.diagonal_one]

/-- Uniform words, followed by the single explicit attenuation rotation. -/
def initial (n N : ℕ) : Space N :=
  attenuationGate n N (CoherentReuse.uniformEmbedding N clean)

/-- The intended state has only the initial `n` words and has a clean flag. -/
def target (n N : ℕ) : Space N :=
  WithLp.toLp 2 (fun j : Fin N =>
    if j.val < n then (CoherentReuse.uniformAmplitude n : ℂ) • clean else 0)

@[simp] theorem target_true (n N : ℕ) (j : Fin N) : target n N j true = 0 := by
  by_cases h : j.val < n <;> simp [target, h]

@[simp] theorem target_false (n N : ℕ) (j : Fin N) :
    target n N j false =
      if j.val < n then (CoherentReuse.uniformAmplitude n : ℂ) else 0 := by
  by_cases h : j.val < n <;> simp [target, h]

/-- Counting the good words is an actual finite-cardinality calculation. -/
theorem sum_initial_segment (n N : ℕ) (h : n ≤ N) (c : ℝ) :
    (∑ j : Fin N, if j.val < n then c else 0) = (n : ℝ) * c := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, Fin.card_filter_val_lt, min_eq_right h]

theorem target_norm (n N : ℕ) (hn : 0 < n) (h : n ≤ N) :
    ‖target n N‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  have ha : 0 ≤ CoherentReuse.uniformAmplitude n := by
    unfold CoherentReuse.uniformAmplitude
    positivity
  have hc : ∀ j : Fin N,
      ‖target n N j‖ ^ 2 =
        if j.val < n then (n : ℝ)⁻¹ else 0 := by
    intro j
    by_cases hj : j.val < n
    · simp only [target, hj, ↓reduceIte, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ha, AmplitudePolynomialSequence.clean_norm,
        mul_one, CoherentReuse.uniformAmplitude_sq]
    · simp [target, hj]
  simp only [hc]
  rw [sum_initial_segment n N h]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [hn0]

theorem initial_norm (n N : ℕ) (hn : 0 < n) (hnN : n ≤ N) (hN : N ≤ 4 * n) :
    ‖initial n N‖ = 1 := by
  have hN0 : N ≠ 0 := by omega
  rw [initial,
    (norm_map_iff_adjoint_comp_self _).mpr (attenuationGate_unitary n N hn hN).1,
    CoherentReuse.uniformEmbedding_norm N hN0,
    AmplitudePolynomialSequence.clean_norm]

/-- Projection onto the accepted attenuation flag. -/
def cleanProjection : Qubit →L[ℂ] Qubit := matrix 1 0 0 0

@[simp] theorem cleanProjection_false (v : Qubit) : cleanProjection v false = v false := by
  simp [cleanProjection]

@[simp] theorem cleanProjection_true (v : Qubit) : cleanProjection v true = 0 := by
  simp [cleanProjection]

theorem cleanProjection_orthogonal :
    PhaseSubspaceGates.IsOrthogonalProjection cleanProjection := by
  constructor
  · change cleanProjection† = cleanProjection
    simp [cleanProjection, matrix_adjoint]
  · ext v b
    cases b <;> simp

/-- Comparison with `n`, combined with the accepted attenuation flag. -/
def goodProjection (n N : ℕ) : Space N →L[ℂ] Space N :=
  WeightedClock.diagonal (fun j : Fin N => if j.val < n then cleanProjection else 0)

theorem goodProjection_orthogonal (n N : ℕ) :
    PhaseSubspaceGates.IsOrthogonalProjection (goodProjection n N) := by
  constructor
  · change (goodProjection n N)† = goodProjection n N
    rw [goodProjection, WeightedClock.diagonal_adjoint]
    congr 1
    funext j
    have hself : cleanProjection† = cleanProjection := cleanProjection_orthogonal.1
    by_cases h : j.val < n <;> simp [h, hself]
  · change goodProjection n N ∘L goodProjection n N = goodProjection n N
    rw [goodProjection, WeightedClock.diagonal_comp]
    congr 1
    funext j
    have hidem : cleanProjection ∘L cleanProjection = cleanProjection :=
      cleanProjection_orthogonal.2
    by_cases h : j.val < n <;> simp [h, hidem]

theorem goodProjection_target (n N : ℕ) : goodProjection n N (target n N) = target n N := by
  ext j b
  cases b <;> by_cases h : j.val < n <;>
    simp [goodProjection, WeightedClock.diagonal_apply, target, h]

/-- Cancellation of the word-register normalisation against the attenuation. -/
theorem accepted_coefficient (n N : ℕ) (hN : 0 < N) :
    CoherentReuse.uniformAmplitude N * attenuation n N =
      (1 / 2 : ℝ) * CoherentReuse.uniformAmplitude n := by
  have hS : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hN))
  by_cases hn : n = 0
  · simp [hn, CoherentReuse.uniformAmplitude, attenuation]
  · have hSn : Real.sqrt (n : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hn))
    unfold CoherentReuse.uniformAmplitude attenuation
    field_simp [hS, hSn]

/-- The success amplitude is derived, rather than supplied as a hypothesis. -/
theorem goodProjection_initial (n N : ℕ) (hN : 0 < N) :
    goodProjection n N (initial n N) = (1 / 2 : ℂ) • target n N := by
  have hc : (CoherentReuse.uniformAmplitude N : ℂ) * (attenuation n N : ℂ) =
      (1 / 2 : ℂ) * (CoherentReuse.uniformAmplitude n : ℂ) := by
    have hcast := congrArg Complex.ofReal (accepted_coefficient n N hN)
    push_cast at hcast
    exact hcast
  ext j b
  cases b <;> by_cases h : j.val < n <;>
    simp [goodProjection, initial, attenuationGate, WeightedClock.diagonal_apply,
      target, h, hc]

/-- Probability `1/4` before the single amplification round. -/
theorem initial_success_probability (n N : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    ‖goodProjection n N (initial n N)‖ ^ 2 = (1 / 4 : ℝ) := by
  rw [goodProjection_initial n N (lt_of_lt_of_le hn hnN), norm_smul,
    target_norm n N hn hnN]
  norm_num

/-- Reflection fixing a known unit vector and reversing its orthogonal complement. -/
def stateReflection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : E) : E →L[ℂ] E := (2 : ℂ) • rankOne ℂ v v - 1

@[simp] theorem stateReflection_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (v w : E) :
    stateReflection v w = (2 * inner ℂ v w) • v - w := by
  simp [stateReflection, smul_smul]

/-- A rank-one state reflection is a full-space unitary. -/
theorem stateReflection_unitary {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (v : E) (hv : ‖v‖ = 1) :
    IsUnitary (stateReflection v) := by
  have hs : star (stateReflection v) = stateReflection v := by
    simp only [stateReflection, star_sub, star_smul, star_ofNat, star_one]
    simp [star_eq_adjoint]
  have hvv : inner ℂ v v = 1 := by simp [hv]
  have hi : stateReflection v ∘L stateReflection v = 1 := by
    ext w
    simp only [comp_apply, stateReflection_apply, inner_sub_right, inner_smul_right,
      hvv, mul_one, one_def, id_apply]
    module
  constructor
  · rw [hs]
    exact hi
  · rw [hs]
    exact hi

/-- The exact amplified operator on the output workspace. -/
def amplified (n N : ℕ) : Space N →L[ℂ] Space N :=
  stateReflection (initial n N) * PhaseSubspaceGates.phase (goodProjection n N) (-1)

/-- One amplitude-amplification round prepares the target *exactly*. -/
theorem amplified_initial (n N : ℕ) (hn : 0 < n) (hnN : n ≤ N) (hN : N ≤ 4 * n) :
    amplified n N (initial n N) = target n N := by
  have hv := initial_norm n N hn hnN hN
  have ht := target_norm n N hn hnN
  have hg := goodProjection_initial n N (lt_of_lt_of_le hn hnN)
  have hp := goodProjection_orthogonal n N
  have hi : inner ℂ (initial n N) (target n N) = (1 / 2 : ℂ) := by
    calc
      _ = inner ℂ (initial n N) (goodProjection n N (target n N)) := by
        rw [goodProjection_target]
      _ = inner ℂ (((goodProjection n N)†) (initial n N)) (target n N) := by
        rw [adjoint_inner_left]
      _ = (1 / 2 : ℂ) := by
        rw [show (goodProjection n N)† = goodProjection n N from hp.1, hg]
        norm_num [inner_smul_left, ht, map_ofNat]
  change stateReflection (initial n N)
    (PhaseSubspaceGates.phase (goodProjection n N) (-1) (initial n N)) = _
  rw [PhaseSubspaceGates.phase_apply, hg, smul_smul, stateReflection_apply]
  simp only [inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hv, hi]
  norm_num

/-- Both reflections are genuine unitary operators on the entire workspace. -/
theorem amplified_unitary (n N : ℕ) (hn : 0 < n) (hnN : n ≤ N) (hN : N ≤ 4 * n) :
    IsUnitary (amplified n N) :=
  (stateReflection_unitary _ (initial_norm n N hn hnN hN)).mul
    (PhaseSubspaceGates.phase_unitary _ (goodProjection_orthogonal n N) (-1) (by norm_num))

/-- Conjugating the input-state reflection exposes preparation and its inverse. -/
theorem stateReflection_conjugate {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (U : E →L[ℂ] E)
    (hU : IsUnitary U) (e : E) :
    U * stateReflection e * star U = stateReflection (U e) := by
  have hr : U ∘L rankOne ℂ e e ∘L U† = rankOne ℂ (U e) (U e) := by
    ext x
    change U ((inner ℂ e ((U†) x)) • e) = (inner ℂ (U e) x) • U e
    rw [map_smul, adjoint_inner_right]
  simp only [stateReflection, mul_sub, sub_mul, mul_smul_comm,
    smul_mul_assoc, mul_one, hU.2]
  rw [show U * rankOne ℂ e e * star U = rankOne ℂ (U e) (U e) from hr]

/-- Literal prepare, phase, inverse, zero-state reflection, prepare sequence.
The compiler of `U` remains explicit: this theorem does not regard `U` as a
single elementary gate. -/
theorem prepare_reflect_inverse_reflect_prepare (n N : ℕ)
    (hn : 0 < n) (hnN : n ≤ N) (hN : N ≤ 4 * n)
    (U : Space N →L[ℂ] Space N) (hU : IsUnitary U) (e : Space N)
    (hPrepare : U e = initial n N) :
    (U * stateReflection e * star U *
      PhaseSubspaceGates.phase (goodProjection n N) (-1) * U) e = target n N := by
  rw [stateReflection_conjugate U hU e, hPrepare]
  change amplified n N (U e) = target n N
  rw [hPrepare]
  exact amplified_initial n N hn hnN hN


/-- The explicit preparation operator separates word preparation from the
single attenuation rotation; there is no unknown postselection amplitude. -/
def prepare (n N : ℕ) (W : Space N →L[ℂ] Space N) : Space N →L[ℂ] Space N :=
  attenuationGate n N * W

theorem prepare_unitary (n N : ℕ) (hn : 0 < n) (hN : N ≤ 4 * n)
    (W : Space N →L[ℂ] Space N) (hW : IsUnitary W) : IsUnitary (prepare n N W) :=
  (attenuationGate_unitary n N hn hN).mul hW

theorem prepare_apply (n N : ℕ) (W : Space N →L[ℂ] Space N) (e : Space N)
    (hW : W e = CoherentReuse.uniformEmbedding N clean) :
    prepare n N W e = initial n N := by
  change attenuationGate n N (W e) = initial n N
  rw [hW]
  rfl

/-- Literal macro syntax.  The single oracle letter here denotes *known word
preparation*, not a sparse-matrix oracle.  Fixed comparisons and reflections
still need the separate elementary-gate compiler. -/
def preparationProgram (n N : ℕ) (hn : 0 < n) (hN : N ≤ 4 * n)
    (W : Space N →L[ℂ] Space N) :
    OracleCircuit.Program (fun _ : Unit => W) :=
  .seq (.fixed (attenuationGate n N) (attenuationGate_unitary n N hn hN)) .query

/-- Two forward and one reverse word preparations, interleaved with the
explicit attenuation and reflection operators. -/
def rangeProgram (n N : ℕ) (hn : 0 < n) (hN : N ≤ 4 * n)
    (W : Space N →L[ℂ] Space N) (e : Space N) (he : ‖e‖ = 1) :
    OracleCircuit.Program (fun _ : Unit => W) :=
  let p := preparationProgram n N hn hN W
  .seq (.seq (.seq (.seq p (.fixed (stateReflection e)
    (stateReflection_unitary e he))) p.adjoint)
    (.fixed (PhaseSubspaceGates.phase (goodProjection n N) (-1))
      (PhaseSubspaceGates.phase_unitary _ (goodProjection_orthogonal n N) (-1)
        (by norm_num)))) p

/-- This is an exact macro count, not a claimed count of elementary gates. -/
theorem rangeProgram_word_preparations (n N : ℕ) (hn : 0 < n) (hN : N ≤ 4 * n)
    (W : Space N →L[ℂ] Space N) (e : Space N) (he : ‖e‖ = 1) :
    (rangeProgram n N hn hN W e he).count = 3 := by
  simp [rangeProgram, preparationProgram]

theorem rangeProgram_eval (n N : ℕ) (hn : 0 < n) (hN : N ≤ 4 * n)
    (W : Space N →L[ℂ] Space N) (e : Space N) (he : ‖e‖ = 1) :
    (rangeProgram n N hn hN W e he).eval () =
      prepare n N W * stateReflection e * star (prepare n N W) *
        PhaseSubspaceGates.phase (goodProjection n N) (-1) * prepare n N W := by
  simp [rangeProgram, preparationProgram, prepare]

/-- All attenuation, cardinality, successful-amplitude, and amplification
obligations are discharged.  The sole preparation interface left is the
ordinary uniform-word transform on the clean zero state. -/
theorem rangeProgram_prepares (n N : ℕ) (hn : 0 < n) (hnN : n ≤ N)
    (hN : N ≤ 4 * n) (W : Space N →L[ℂ] Space N) (hW : IsUnitary W)
    (e : Space N) (he : ‖e‖ = 1)
    (hWords : W e = CoherentReuse.uniformEmbedding N clean) :
    (rangeProgram n N hn hN W e he).eval () e = target n N := by
  rw [rangeProgram_eval]
  exact prepare_reflect_inverse_reflect_prepare n N hn hnN hN
    (prepare n N W) (prepare_unitary n N hn hN W hW) e
    (prepare_apply n N W e hWords)

/-- The attenuation flag is clean in the final output, including on padded words. -/
theorem rangeProgram_flag_clean (n N : ℕ) (hn : 0 < n) (hnN : n ≤ N)
    (hN : N ≤ 4 * n) (W : Space N →L[ℂ] Space N) (hW : IsUnitary W)
    (e : Space N) (he : ‖e‖ = 1)
    (hWords : W e = CoherentReuse.uniformEmbedding N clean) (j : Fin N) :
    ((rangeProgram n N hn hN W e he).eval () e) j true = 0 := by
  rw [rangeProgram_prepares n N hn hnN hN W hW e he hWords]
  exact target_true n N j

end
end SparseHamiltonian.GateUniformRange
