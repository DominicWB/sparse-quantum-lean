import TimeDependentExtensions.Hamiltonian.Corollaries
import ZeroTimeRemarks.TimeUniform

/-!
# Theorem `hs:thm:time` on general meshes at zero time or zero norm bound

The released general-mesh endpoint `TimeDependentExtensions.Hamiltonian.simulation`
(nonuniform meshes, breakpoints and the integrated sample-error certificate) assumes `T > 0`
and `η > 0`; its statement file lists the degenerate cases `T = 0` and `η = 0` as not
formalised. This file treats them in the same oracle family
`TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε` with the same clean encoding
`TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε`.

* `input_isometry`: the clean encoding is an isometry for all public parameters.
* `solvesOn_zero_eq`, `piecewise_zero_eq_one`: a propagator of a path that vanishes on every
  mesh interval is the identity at the final time.
* `zero_certificate`: the identity program makes no query and is exact for `T = 0` or for
  pieces that vanish on their intervals.
* `zero_bound`: for the public bound `η = 0` every sample vanishes and the identity program
  is within the integrated certificate `∑_r ∫ ‖H_r(u) - H̃_r‖ du` of every propagator, by the
  released estimate `TimeDependentExtensions.mesh_error_integral`.
* `simulation_nonneg`: the general-mesh form of Theorem `hs:thm:time` for every `T ≥ 0` and
  `η ≥ 0`, with at most `0` queries if `T = 0` or `η = 0`;
  `simulation_with_reference_nonneg`: the same bound with an untouched finite reference.
-/

set_option autoImplicit false

namespace SparseHamiltonian.ZeroTimeRemarks.TimeMesh

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding TimeDependent Set
open TimeDependentExtensions MeasureTheory
open scoped BigOperators InnerProduct
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096

section Generic

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

omit [CompleteSpace P] in
/-- A solution of `U' = 0` on `[a, b]` is constant there (`hs:thm:time`). -/
theorem solvesOn_zero_eq (U : ℝ → P →L[ℂ] P) {a b : ℝ} (hab : a ≤ b)
    (hU : SolvesOn (fun _ => (0 : P →L[ℂ] P)) U a b) : U b = U a := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f' := fun _ => (0 : P →L[ℂ] P))
    (C := 0) (fun u hu => by simpa using hU u hu) (fun _ _ => by simp) b ⟨hab, le_rfl⟩
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  exact h

omit [CompleteSpace P] in
/-- A piecewise propagator of a path that vanishes on every mesh interval is the identity at
every mesh point, in particular at the final time (`hs:thm:time`). -/
theorem piecewise_zero_eq_one {t : ℕ → ℝ} {M : ℕ} {T : ℝ} (hmesh : IsMesh t M T)
    (U : ℝ → P →L[ℂ] P) (hU0 : U 0 = 1)
    (hU : ∀ r < M, SolvesOn (fun _ => (0 : P →L[ℂ] P)) U (t r) (t (r + 1))) :
    U T = 1 := by
  have key : ∀ r ≤ M, U (t r) = 1 := by
    intro r
    induction r with
    | zero => intro _; rw [hmesh.zero, hU0]
    | succ r ih =>
        intro hr
        rw [solvesOn_zero_eq U (hmesh.mono (Nat.le_succ r)) (hU r hr), ih (Nat.le_of_succ_le hr)]
  rw [← hmesh.last]
  exact key M le_rfl

end Generic

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- The clean encoding of the general-mesh form of Theorem `hs:thm:time` is an isometry for
all public parameters. -/
theorem input_isometry (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ)
    (γ η T ε : ℝ) :
    (TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε)† ∘L
      TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε = 1 := by
  have hE := (Refined.embedding D hM (pieceOf t T N hM) N
    (Sampled.degree (s : ℝ) γ (η * T) ε N)).adjoint_comp_self
  have hIn := SharpClockQuery.input_isometry (P := EuclideanSpace ℂ n)
    (V := SparseEdgeMoments.OrientedSpace n) (Sampled.step (s : ℝ) γ (η * T) N)
    (CayleyClockInterface.width (s : ℝ) γ) (CayleyClockInterface.moment γ) N (ε / 3)
    (CayleyClockInterface.width_ge_one _ _)
  exact AlignedMultiOracleProgram.input_isometry _ (Sampled.isometry_comp _ _ hE hIn)

/-- **Zero time or a zero path on a general mesh (`hs:thm:time`).** The identity program over
the coherent sampled-time oracles of the general-mesh theorem makes no query, the clean
encoding is an isometry, and for every instance, every family of pieces and every propagator
of the piecewise path the full output is exact when `T = 0` or every piece vanishes on its
mesh interval. -/
theorem zero_certificate (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ)
    (γ η T ε : ℝ) (hmesh : IsMesh t M T) :
    (MultiOracleCircuit.Program.identity
        (O := TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε)).count = 0 ∧
      (TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε)† ∘L
        TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε = 1 ∧
      ∀ x, IsUnitary ((MultiOracleCircuit.Program.identity
          (O := TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε)).eval x) ∧
        ∀ (Hp : Fin M → ℝ → Matrix n n ℂ)
          (U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)),
          (T = 0 ∨ ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Hp r u = 0) →
          U 0 = 1 →
          (∀ r : Fin M, SolvesOn (fun u => SparseStateOverlap.matrixOperator (Hp r u)) U
            (t r) (t ((r : ℕ) + 1))) →
          ‖(MultiOracleCircuit.Program.identity
              (O := TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε)).eval x ∘L
              TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε -
            TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε ∘L U T‖ = 0 := by
  refine ⟨MultiOracleCircuit.Program.count_identity, input_isometry D hM t N γ η T ε,
    fun x => ⟨?_, fun Hp U hZero hU0 hU => ?_⟩⟩
  · rw [MultiOracleCircuit.Program.eval_identity]
    exact isUnitary_one
  · have hUT : U T = 1 := by
      rcases hZero with hT | hpath
      · rw [hT, hU0]
      · apply piecewise_zero_eq_one hmesh U hU0
        intro r hr u hu
        have h := hU ⟨r, hr⟩ u hu
        simp only [hpath ⟨r, hr⟩ u hu, NativeZeroSimulation.matrixOperator_zero] at h
        simpa using h
    rw [hUT, MultiOracleCircuit.Program.eval_identity, sub_eq_zero.mpr, norm_zero]
    rfl

/-- **The public bound `η = 0` on a general mesh (`hs:thm:time`).** The row promise with
`η = 0` forces every represented sample to vanish. The identity program over the oracles of
the general-mesh theorem makes no query, the clean encoding is an isometry, and for every
instance, every family of Hermitian interval-integrable pieces and every propagator of the
piecewise path, the full output is within the integrated sample-error certificate
`∑_r ∫_{t_r}^{t_{r+1}} ‖H_r(u) - H̃_r‖ du` of the clean evolved state. -/
theorem zero_bound (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ)
    (γ η T ε : ℝ) (hη : η = 0) (hmesh : IsMesh t M T)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2) :
    (MultiOracleCircuit.Program.identity
        (O := TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε)).count = 0 ∧
      (TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε)† ∘L
        TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε = 1 ∧
      ∀ x, IsUnitary ((MultiOracleCircuit.Program.identity
          (O := TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε)).eval x) ∧
        ∀ (Hp : Fin M → ℝ → Matrix n n ℂ)
          (U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)),
          (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), (Hp r u).IsHermitian) →
          (∀ r : Fin M, IntervalIntegrable
            (fun u => SparseStateOverlap.matrixOperator (Hp r u)) volume
              (t r) (t ((r : ℕ) + 1))) →
          U 0 = 1 →
          (∀ r : Fin M, SolvesOn (fun u => SparseStateOverlap.matrixOperator (Hp r u)) U
            (t r) (t ((r : ℕ) + 1))) →
          ‖(MultiOracleCircuit.Program.identity
              (O := TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε)).eval x ∘L
              TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε -
            TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε ∘L U T‖ ≤
            ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
              ‖SparseStateOverlap.matrixOperator (Hp r u) -
                SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ := by
  have hZero : ∀ y, D.matrix y = 0 := by
    apply NativeZeroSimulation.matrix_zero_of_energy D
    intro y i
    simpa only [hη, zero_pow (by norm_num : 2 ≠ 0)] using hrow y i
  refine ⟨MultiOracleCircuit.Program.count_identity, input_isometry D hM t N γ η T ε,
    fun x => ⟨?_, fun Hp U hPath hInt hU0 hU => ?_⟩⟩
  · rw [MultiOracleCircuit.Program.eval_identity]
    exact isUnitary_one
  · let A : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun _ => 0
    let Hq : ℕ → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r u =>
      SparseStateOverlap.matrixOperator (Hp (Sampled.sampleIndex hM r) u)
    have hPw : IsPiecewisePropagator Hq t M U := by
      refine ⟨hU0, fun r hr => ?_⟩
      have h := hU ⟨r, hr⟩
      simp only [Hq, TimeDependentExtensions.Hamiltonian.sampleIndex_of_lt hM hr]
      exact h
    have hHq : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), star (Hq r u) = Hq r u := by
      intro r hr u hu
      simp only [Hq, TimeDependentExtensions.Hamiltonian.sampleIndex_of_lt hM hr]
      exact SparseValuePrecision.matrixOperator_star_eq _ (hPath ⟨r, hr⟩ u hu)
    have hA : ∀ r, star (A r) = A r := fun _ => by
      change star (0 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) = 0
      exact star_zero (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    have hIntq : ∀ r < M, IntervalIntegrable (Hq r) volume (t r) (t (r + 1)) := by
      intro r hr
      simp only [Hq, TimeDependentExtensions.Hamiltonian.sampleIndex_of_lt hM hr]
      exact hInt ⟨r, hr⟩
    have hErr := mesh_error_integral A hmesh hPw hHq hA hIntq
    have hOne : meshEvolution A t M = 1 := by
      unfold meshEvolution
      have h1 : ∀ r : ℕ, NormedSpace.exp ((-Complex.I * ((t (r + 1) - t r : ℝ) : ℂ)) • A r) =
          1 := fun r => Hamiltonian.exp_eq_one (t (r + 1) - t r) 0 (Or.inr rfl)
      simp only [h1]
      exact TimeUniform.evolution_one M
    rw [hOne] at hErr
    have hSum : ∑ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖Hq r u - A r‖ =
        ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
          ‖SparseStateOverlap.matrixOperator (Hp r u) -
            SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ := by
      rw [← Fin.sum_univ_eq_sum_range (fun r => ∫ u in t r..t (r + 1), ‖Hq r u - A r‖) M]
      apply Finset.sum_congr rfl
      intro r _
      simp only [Hq, A, TimeDependentExtensions.Hamiltonian.sampleIndex_val, hZero,
        NativeZeroSimulation.matrixOperator_zero]
    rw [hSum] at hErr
    rw [MultiOracleCircuit.Program.eval_identity]
    exact (TimeUniform.identity_error_le _ (input_isometry D hM t N γ η T ε) (U T)).trans hErr

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- An integrated sample-error certificate is nonnegative on a mesh (`hs:thm:time`). -/
theorem certificate_nonneg (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (T : ℝ)
    (hmesh : IsMesh t M T) (x : X) (Hp : Fin M → ℝ → Matrix n n ℂ) :
    0 ≤ ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
      ‖SparseStateOverlap.matrixOperator (Hp r u) -
        SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ :=
  Finset.sum_nonneg fun r _ =>
    intervalIntegral.integral_nonneg (hmesh.mono (Nat.le_succ r)) fun _ _ => norm_nonneg _

/-- **The general-mesh form of Theorem `hs:thm:time` for every `T ≥ 0` and `η ≥ 0`.** Under
the hypotheses of the released `TimeDependentExtensions.Hamiltonian.simulation` with `0 ≤ η`
and `0 ≤ T` in place of `0 < η` and `0 < T`, there are an admissible rescaling and one program
over `TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε`, uniform over the instances, with
at most `0` queries if `T = 0` or `η = 0` and the released bound otherwise; the clean encoding
is an isometry, and for every instance, every family of Hermitian interval-integrable pieces
whose integrated sample-error certificate is at most `ε / 9`, and every propagator of the
piecewise path, the full output is within `ε` of the clean evolved state. -/
theorem simulation_nonneg (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (η T ε : ℝ)
    (N : ℕ) (hη : 0 ≤ η) (hT : 0 ≤ T) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) (hN : 0 < N)
    (hmesh : IsMesh t M T)
    (hClock : 4 * s * (η * T) ≤ N)
    (hCayley : 9 * (Real.sqrt s * (η * T)) ^ 3 ≤ ε * (N : ℝ) ^ 2)
    (hRefine : 9 * M * (Real.sqrt s * (η * T)) ≤ ε * N)
    (hH : ∀ y, (D.matrix y).IsHermitian)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε),
        (p.count : ℝ) ≤ (if T = 0 ∨ η = 0 then 0 else 995328 *
          (Real.sqrt (s : ℝ) * (η * T) +
            Real.sqrt ((s : ℝ) * (η * T) * Real.log (1 / ε)) + Real.log (1 / ε))) ∧
        (TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε)† ∘L
          TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ (Hp : Fin M → ℝ → Matrix n n ℂ)
            (U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)),
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), (Hp r u).IsHermitian) →
            (∀ r : Fin M, IntervalIntegrable
              (fun u => SparseStateOverlap.matrixOperator (Hp r u)) volume
                (t r) (t ((r : ℕ) + 1))) →
            ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
              ‖SparseStateOverlap.matrixOperator (Hp r u) -
                SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 9 →
            U 0 = 1 →
            (∀ r : Fin M, SolvesOn (fun u => SparseStateOverlap.matrixOperator (Hp r u)) U
              (t r) (t ((r : ℕ) + 1))) →
            ‖p.eval x ∘L TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε -
              TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε ∘L U T‖ ≤ ε := by
  obtain ⟨h0, h1, hs⟩ := Hamiltonian.one_admissible (Z := Z) D
  by_cases hη0 : η = 0
  · obtain ⟨hc, hIn, hAct⟩ := zero_bound D hM t N 1 η T ε hη0 hmesh hrow
    refine ⟨1, h0, h1, hs, MultiOracleCircuit.Program.identity, ?_, hIn,
      fun x => ⟨(hAct x).1, fun Hp U hPath hInt hCert hU0 hU => ?_⟩⟩
    · rw [if_pos (Or.inr hη0), hc, Nat.cast_zero]
    · have hc0 := certificate_nonneg D t T hmesh x Hp
      exact ((hAct x).2 Hp U hPath hInt hU0 hU).trans (by linarith)
  · by_cases hT0 : T = 0
    · obtain ⟨hc, hIn, hAct⟩ := zero_certificate D hM t N 1 η T ε hmesh
      refine ⟨1, h0, h1, hs, MultiOracleCircuit.Program.identity, ?_, hIn,
        fun x => ⟨(hAct x).1, fun Hp U _ _ _ hU0 hU => ?_⟩⟩
      · rw [if_pos (Or.inl hT0), hc, Nat.cast_zero]
      · rw [(hAct x).2 Hp U (Or.inl hT0) hU0 hU]
        exact hε.le
    · have hηpos : 0 < η := lt_of_le_of_ne hη (Ne.symm hη0)
      have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
      obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hAct⟩ :=
        TimeDependentExtensions.Hamiltonian.simulation D hM t η T ε N hηpos hTpos hε hεHalf
          hN hmesh hClock hCayley hRefine hH hrow hcol
      refine ⟨γ, hγ, hγOne, hWidth, p, ?_, hIn, hAct⟩
      rw [if_neg (fun h => h.elim hT0 hη0)]
      exact hCount

/-- **The general-mesh form of Theorem `hs:thm:time` for every `T ≥ 0` and `η ≥ 0`, with an
untouched reference.** The program and clean encoding of `simulation_nonneg` obey the same
full-output bound `ε` on every normalised input entangled with an untouched finite reference
register, as in the released `TimeDependentExtensions.Hamiltonian.simulation_with_reference`. -/
theorem simulation_with_reference_nonneg {R : Type*} [Fintype R] (D : Data (X × Fin M) n Z s)
    (hM : 0 < M) (t : ℕ → ℝ) (η T ε : ℝ) (N : ℕ) (hη : 0 ≤ η) (hT : 0 ≤ T) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2) (hN : 0 < N) (hmesh : IsMesh t M T)
    (hClock : 4 * s * (η * T) ≤ N)
    (hCayley : 9 * (Real.sqrt s * (η * T)) ^ 3 ≤ ε * (N : ℝ) ^ 2)
    (hRefine : 9 * M * (Real.sqrt s * (η * T)) ≤ ε * N)
    (hH : ∀ y, (D.matrix y).IsHermitian)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε),
        (p.count : ℝ) ≤ (if T = 0 ∨ η = 0 then 0 else 995328 *
          (Real.sqrt (s : ℝ) * (η * T) +
            Real.sqrt ((s : ℝ) * (η * T) * Real.log (1 / ε)) + Real.log (1 / ε))) ∧
        (TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε)† ∘L
          TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ (Hp : Fin M → ℝ → Matrix n n ℂ)
            (U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)),
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), (Hp r u).IsHermitian) →
            (∀ r : Fin M, IntervalIntegrable
              (fun u => SparseStateOverlap.matrixOperator (Hp r u)) volume
                (t r) (t ((r : ℕ) + 1))) →
            ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
              ‖SparseStateOverlap.matrixOperator (Hp r u) -
                SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 9 →
            U 0 = 1 →
            (∀ r : Fin M, SolvesOn (fun u => SparseStateOverlap.matrixOperator (Hp r u)) U
              (t r) (t ((r : ℕ) + 1))) →
            ∀ ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n), ‖ψ‖ = 1 →
              ‖FiniteReferenceLift.lift (p.eval x)
                  (FiniteReferenceLift.lift
                    (TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε) ψ) -
                FiniteReferenceLift.lift
                  (TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε)
                  (FiniteReferenceLift.lift (U T) ψ)‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hAction⟩ :=
    simulation_nonneg D hM t η T ε N hη hT hε hεHalf hN hmesh hClock hCayley hRefine hH hrow hcol
  refine ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, fun x => ⟨(hAction x).1, ?_⟩⟩
  intro Hp U hPath hInt hCert hU0 hU ψ hψ
  simpa only [hψ, mul_one] using
    FiniteReferenceLift.same_embedding_error_le (p.eval x)
      (TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε) (U T) ε
      ((hAction x).2 Hp U hPath hInt hCert hU0 hU) ψ

end
end SparseHamiltonian.ZeroTimeRemarks.TimeMesh
