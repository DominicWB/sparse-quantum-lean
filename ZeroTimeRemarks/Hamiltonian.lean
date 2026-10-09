import SparseHamiltonian.ManuscriptPrecision

/-!
# Theorem `hs:thm:main` at zero time or zero norm bound

Theorem `hs:thm:main` of the accompanying paper ends with "If `t = 0` or the available bound
is `η = 0`, the identity circuit suffices." The released endpoint
`SparseHamiltonian.ImprovedSparseHamiltonian.simulation_log_one` assumes `η > 0`, and its
query bound `995328 (√s τ + √(s τ log(1/ε)) + log(1/ε))` is positive at `t = 0`. The released
module `SparseHamiltonian/ImprovedZeroSimulation.lean` certifies the identity in the smaller
oracle family `NativeSparseAttenuation.oracles D`; this file states the remark in the oracle
family `ImprovedSparseHamiltonian.oracle D γ η t ε`, with the clean encoding
`ImprovedSparseHamiltonian.input D γ η t ε`, of the released endpoint.

* `input_isometry`: the clean encoding is an isometry for all public parameters.
* `zero_certificate`: for every rescaling `γ`, the identity program over the oracles of
  `simulation_log_one` makes no query and is exact when `t = 0` or every instance matrix
  vanishes.
* `simulation_zero`: the zero case of `hs:thm:main` (`t = 0` or `η = 0`), with zero queries
  and zero error.
* `simulation_log_one_nonneg`, `simulation_spectral_log_one_nonneg`,
  `simulation_with_reference_log_one_nonneg`: Theorem `hs:thm:main` for every `η ≥ 0` and
  every `t`, with query count at most `0` if `t = 0` or `η = 0` and the released bound
  otherwise.
-/

set_option autoImplicit false

namespace SparseHamiltonian.ZeroTimeRemarks.Hamiltonian

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- The clean input of the released normalized native simulation is an isometry for all
public parameters (`hs:thm:main`). -/
theorem native_input_isometry (D : Data X n Z s) (γ τ ε : ℝ) :
    (ImprovedNativeSimulation.input D γ τ ε)† ∘L ImprovedNativeSimulation.input D γ τ ε = 1 :=
  NativeSparseAttenuation.isometry_comp _ _
    (SharpClockQuery.input_isometry (P := EuclideanSpace ℂ n)
      (V := SparseEdgeMoments.OrientedSpace n) _ _ _ _ _
      (CayleyClockInterface.width_ge_one _ _))
    (ImprovedNativeSimulation.embedding D γ τ ε).adjoint_comp_self

/-- The clean output of the released normalized native simulation is an isometry for all
public parameters (`hs:thm:main`). -/
theorem native_output_isometry (D : Data X n Z s) (γ τ ε : ℝ) :
    (ImprovedNativeSimulation.output D γ τ ε)† ∘L ImprovedNativeSimulation.output D γ τ ε = 1 :=
  NativeSparseAttenuation.isometry_comp _ _
    (SharpClockSimulation.evolutionOutput_isometry (P := EuclideanSpace ℂ n)
      (V := SparseEdgeMoments.OrientedSpace n) _ _ _ _
      (CayleyClockInterface.width_ge_one _ _))
    (ImprovedNativeSimulation.embedding D γ τ ε).adjoint_comp_self

/-- The clean encoding `ImprovedSparseHamiltonian.input D γ η t ε` of Theorem `hs:thm:main`
is an isometry for all public parameters. -/
theorem input_isometry (D : Data X n Z s) (γ η t ε : ℝ) :
    (ImprovedSparseHamiltonian.input D γ η t ε)† ∘L
      ImprovedSparseHamiltonian.input D γ η t ε = 1 :=
  AlignedMultiOracleProgram.input_isometry _
    (LabeledAdjointSimulation.signed_isometries _ _
      (native_input_isometry D γ (η * |t|) ε) (native_output_isometry D γ (η * |t|) ε) t).1

omit [DecidableEq n] in
/-- The evolution `exp(-i t H)` is the identity when `t = 0` or `H = 0` (`hs:thm:main`). -/
theorem exp_eq_one (t : ℝ) (A : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (h : t = 0 ∨ A = 0) : NormedSpace.exp ((-Complex.I * (t : ℂ)) • A) = 1 := by
  have hz : (-Complex.I * (t : ℂ)) • A = 0 := by
    rcases h with ht | hA
    · subst ht
      ext v i
      simp only [_root_.smul_apply, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_zero,
        mul_zero, zero_mul, zero_apply, PiLp.zero_apply]
    · subst hA
      ext v i
      simp only [_root_.smul_apply, zero_apply, PiLp.smul_apply, PiLp.zero_apply,
        smul_eq_mul, mul_zero]
  rw [hz]
  exact NormedSpace.exp_zero

/-- **Zero-time and zero-matrix certificate in the oracle family of `hs:thm:main`.** For every
public rescaling `γ`, the identity program over `ImprovedSparseHamiltonian.oracle D γ η t ε`
makes no query, the clean encoding is an isometry, and the full output is exact when `t = 0`
or every instance matrix vanishes. -/
theorem zero_certificate (D : Data X n Z s) (γ η t ε : ℝ)
    (hZero : t = 0 ∨ ∀ x, D.matrix x = 0) :
    (MultiOracleCircuit.Program.identity
        (O := ImprovedSparseHamiltonian.oracle D γ η t ε)).count = 0 ∧
      (ImprovedSparseHamiltonian.input D γ η t ε)† ∘L
        ImprovedSparseHamiltonian.input D γ η t ε = 1 ∧
      ∀ x, IsUnitary ((MultiOracleCircuit.Program.identity
          (O := ImprovedSparseHamiltonian.oracle D γ η t ε)).eval x) ∧
        ‖(MultiOracleCircuit.Program.identity
            (O := ImprovedSparseHamiltonian.oracle D γ η t ε)).eval x ∘L
            ImprovedSparseHamiltonian.input D γ η t ε -
          ImprovedSparseHamiltonian.input D γ η t ε ∘L
            NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))‖ = 0 := by
  refine ⟨MultiOracleCircuit.Program.count_identity, input_isometry D γ η t ε,
    fun x => ⟨?_, ?_⟩⟩
  · rw [MultiOracleCircuit.Program.eval_identity]
    exact isUnitary_one
  · have hExp : NormedSpace.exp ((-Complex.I * (t : ℂ)) •
        SparseStateOverlap.matrixOperator (D.matrix x)) = 1 := by
      apply exp_eq_one
      rcases hZero with ht | hM
      · exact Or.inl ht
      · right
        rw [hM x]
        exact NativeZeroSimulation.matrixOperator_zero
    rw [hExp, MultiOracleCircuit.Program.eval_identity, sub_eq_zero.mpr, norm_zero]
    rfl

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The public rescaling `γ = 1` is admissible: `0 < 1 ≤ 1` and `1 ≤ √s`, since the sparse
data have at least one slot (`hs:thm:main`). -/
theorem one_admissible (D : Data X n Z s) :
    (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 ∧ 1 ≤ (1 : ℝ) * Real.sqrt (s : ℝ) := by
  have hs : (1 : ℝ) ≤ s := by exact_mod_cast D.slots_pos
  refine ⟨one_pos, le_rfl, ?_⟩
  rw [one_mul]
  calc
    (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (s : ℝ) := Real.sqrt_le_sqrt hs

/-- **Theorem `hs:thm:main`, the case `t = 0` or `η = 0`.** In the oracle family and with the
clean encoding of `simulation_log_one`, there are an admissible rescaling (in the proof `γ = 1`)
and a program (the identity circuit) that makes no primitive query, is unitary, and whose full
output equals the clean evolved state exactly. For `η = 0` the row promise forces every
instance matrix to vanish; no Hermitian or column promise is needed. -/
theorem simulation_zero (D : Data X n Z s) (η t ε : ℝ) (hZero : t = 0 ∨ η = 0)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (K := ImprovedSparseHamiltonian.Physical n Z s γ η t ε)
          (ImprovedSparseHamiltonian.oracle D γ η t ε),
        p.count = 0 ∧
        (ImprovedSparseHamiltonian.input D γ η t ε)† ∘L
          ImprovedSparseHamiltonian.input D γ η t ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L ImprovedSparseHamiltonian.input D γ η t ε -
            ImprovedSparseHamiltonian.input D γ η t ε ∘L
              NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                SparseStateOverlap.matrixOperator (D.matrix x))‖ = 0 := by
  obtain ⟨h0, h1, hs⟩ := one_admissible D
  have hZero' : t = 0 ∨ ∀ x, D.matrix x = 0 := by
    rcases hZero with ht | hη
    · exact Or.inl ht
    · right
      apply NativeZeroSimulation.matrix_zero_of_energy D
      intro x i
      simpa only [hη, zero_pow (by norm_num : 2 ≠ 0)] using hrow x i
  exact ⟨1, h0, h1, hs, MultiOracleCircuit.Program.identity,
    zero_certificate D 1 η t ε hZero'⟩

/-- **Theorem `hs:thm:main` for every `η ≥ 0` and every `t`.** Under the hypotheses of the
released `simulation_log_one` with `0 ≤ η` in place of `0 < η`, there are an admissible
rescaling and one program over the oracles of `simulation_log_one`, uniform over the
instances, with at most `0` queries if `t = 0` or `η = 0` and at most
`995328 (√s τ + √(s τ log(1/ε)) + log(1/ε))`, `τ = η |t|`, otherwise; the clean encoding is
an isometry and the full output is within `ε` of the clean evolved state. -/
theorem simulation_log_one_nonneg (D : Data X n Z s) (η t ε : ℝ)
    (hη : 0 ≤ η) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (K := ImprovedSparseHamiltonian.Physical n Z s γ η t ε)
          (ImprovedSparseHamiltonian.oracle D γ η t ε),
        (p.count : ℝ) ≤ (if t = 0 ∨ η = 0 then 0 else 995328 *
          (Real.sqrt (s : ℝ) * (η * |t|) +
            Real.sqrt ((s : ℝ) * (η * |t|) * Real.log (1 / ε)) + Real.log (1 / ε))) ∧
        (ImprovedSparseHamiltonian.input D γ η t ε)† ∘L
          ImprovedSparseHamiltonian.input D γ η t ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L ImprovedSparseHamiltonian.input D γ η t ε -
            ImprovedSparseHamiltonian.input D γ η t ε ∘L
              NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  by_cases hZero : t = 0 ∨ η = 0
  · obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hAct⟩ :=
      simulation_zero D η t ε hZero hrow
    refine ⟨γ, hγ, hγOne, hWidth, p, ?_, hIn, fun x => ⟨(hAct x).1, ?_⟩⟩
    · rw [if_pos hZero, hCount, Nat.cast_zero]
    · rw [(hAct x).2]
      exact hε.le
  · have hηpos : 0 < η := lt_of_le_of_ne hη (fun h => hZero (Or.inr h.symm))
    obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hAct⟩ :=
      ImprovedSparseHamiltonian.simulation_log_one D η t ε hηpos hε hεHalf hH hrow hcol
    refine ⟨γ, hγ, hγOne, hWidth, p, ?_, hIn, hAct⟩
    rw [if_neg hZero]
    exact hCount

/-- **Theorem `hs:thm:main` for every `η ≥ 0` under a spectral-norm bound.** The Hermitian
promise and `‖H‖ ≤ η`, `η ≥ 0`, supply both energy promises, so the conclusion of
`simulation_log_one_nonneg` holds; in particular `η = 0` uses the identity circuit. -/
theorem simulation_spectral_log_one_nonneg (D : Data X n Z s) (η t ε : ℝ)
    (hη : 0 ≤ η) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hNorm : ∀ x, ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ η) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (K := ImprovedSparseHamiltonian.Physical n Z s γ η t ε)
          (ImprovedSparseHamiltonian.oracle D γ η t ε),
        (p.count : ℝ) ≤ (if t = 0 ∨ η = 0 then 0 else 995328 *
          (Real.sqrt (s : ℝ) * (η * |t|) +
            Real.sqrt ((s : ℝ) * (η * |t|) * Real.log (1 / ε)) + Real.log (1 / ε))) ∧
        (ImprovedSparseHamiltonian.input D γ η t ε)† ∘L
          ImprovedSparseHamiltonian.input D γ η t ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L ImprovedSparseHamiltonian.input D γ η t ε -
            ImprovedSparseHamiltonian.input D γ η t ε ∘L
              NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε :=
  simulation_log_one_nonneg D η t ε hη hε hεHalf hH
    (SparseSpectralEnergy.native_energies D η hH hNorm).1
    (SparseSpectralEnergy.native_energies D η hH hNorm).2

/-- **Theorem `hs:thm:main` for every `η ≥ 0`, with an untouched reference.** The program and
clean encoding of `simulation_log_one_nonneg` obey the full-output bound on every normalized
input entangled with an untouched finite reference. -/
theorem simulation_with_reference_log_one_nonneg {R : Type*} [Fintype R]
    (D : Data X n Z s) (η t ε : ℝ)
    (hη : 0 ≤ η) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (K := ImprovedSparseHamiltonian.Physical n Z s γ η t ε)
          (ImprovedSparseHamiltonian.oracle D γ η t ε),
        (p.count : ℝ) ≤ (if t = 0 ∨ η = 0 then 0 else 995328 *
          (Real.sqrt (s : ℝ) * (η * |t|) +
            Real.sqrt ((s : ℝ) * (η * |t|) * Real.log (1 / ε)) + Real.log (1 / ε))) ∧
        (ImprovedSparseHamiltonian.input D γ η t ε)† ∘L
          ImprovedSparseHamiltonian.input D γ η t ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n), ‖ψ‖ = 1 →
            ‖FiniteReferenceLift.lift (p.eval x)
                (FiniteReferenceLift.lift (ImprovedSparseHamiltonian.input D γ η t ε) ψ) -
              FiniteReferenceLift.lift (ImprovedSparseHamiltonian.input D γ η t ε)
                (FiniteReferenceLift.lift (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                  SparseStateOverlap.matrixOperator (D.matrix x))) ψ)‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hAction⟩ :=
    simulation_log_one_nonneg D η t ε hη hε hεHalf hH hrow hcol
  refine ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, fun x => ⟨(hAction x).1, ?_⟩⟩
  intro ψ hψ
  simpa only [hψ, mul_one] using
    ImprovedSparseHamiltonian.reference_error D γ η t ε p (fun x => (hAction x).2) x ψ

end
end SparseHamiltonian.ZeroTimeRemarks.Hamiltonian
