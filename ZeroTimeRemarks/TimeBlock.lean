import TimeDependentExtensions.BlockEncoding.Theorem
import ZeroTimeRemarks.TimeMesh

/-!
# Time-indexed block encodings (`hs:eq:blockadditive`) at zero time or zero normalisation

The released endpoint `TimeDependentExtensions.BlockEncoding.simulation` (equation
`hs:eq:blockadditive`, the time-indexed block-encoding special case of Theorem `hs:thm:time`)
assumes `α > 0` and `T > 0`; its statement file lists the degenerate cases `T = 0` and `α = 0`
as not formalised. With `α = 0` every represented sample `H̃_r = α J† O_r J` vanishes (a known
zero Hamiltonian). This file treats both cases in the same oracle family
`BlockEncoding.alignedOracle O N α T ε` with the same clean encoding
`BlockEncoding.alignedInput hM b₀ J hJ t N α T ε`.

* `alignedInput_isometry`: the clean encoding is an isometry for all public parameters.
* `zero_bound`: the identity program makes no query; it is exact at `T = 0` and, for `α = 0`,
  within the integrated certificate `∑_r ∫ ‖H_r(u) - H̃_r‖ du` of every propagator.
* `simulation_nonneg`: equation `hs:eq:blockadditive` for every `α ≥ 0` and `T ≥ 0`, with at
  most `0` queries if `T = 0` or `α = 0` and the released `2304 (α T + 1 + log(3/ε))` otherwise.
-/

set_option autoImplicit false

namespace SparseHamiltonian.ZeroTimeRemarks.TimeBlock

noncomputable section
open ContinuousLinearMap OracleCircuit TimeDependent Set
open TimeDependentExtensions MeasureTheory
open scoped BigOperators InnerProduct
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096

variable {X : Type*} {n B₀ : Type*} [Fintype n] [Fintype B₀] [DecidableEq B₀] {M : ℕ}

/-- The clean encoding of equation `hs:eq:blockadditive` is an isometry for all public
parameters. -/
theorem alignedInput_isometry (hM : 0 < M) (b₀ : B₀)
    (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ B₀) (hJ : J† ∘L J = 1) (t : ℕ → ℝ) (N : ℕ)
    (α T ε : ℝ) :
    (BlockEncoding.alignedInput hM b₀ J hJ t N α T ε)† ∘L
      BlockEncoding.alignedInput hM b₀ J hJ t N α T ε = 1 :=
  AlignedMultiOracleProgram.input_isometry _
    (Sampled.isometry_comp _ _
      (BlockEncoding.embedding hM b₀ J hJ (pieceOf t T N hM) N _).adjoint_comp_self
      (SharpClockQuery.input_isometry (P := EuclideanSpace ℂ n) (V := EuclideanSpace ℂ B₀)
        (α * T / N) 1 1 N (ε / 3) le_rfl))

omit [DecidableEq B₀] in
/-- With normalisation `α = 0` the represented sample vanishes (`hs:eq:blockadditive`). -/
theorem blockSample_zero (O : EuclideanSpace ℂ B₀ →L[ℂ] EuclideanSpace ℂ B₀)
    (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ B₀) :
    BlockEncoding.blockSample O J 0 = 0 := by
  unfold BlockEncoding.blockSample
  ext v i
  simp only [_root_.smul_apply, PiLp.smul_apply, Complex.ofReal_zero, smul_eq_mul, zero_mul,
    zero_apply, PiLp.zero_apply]

/-- **Zero time or zero normalisation for time-indexed block encodings
(`hs:eq:blockadditive`).** The identity program over the controlled time-indexed oracles makes
no query, the clean encoding is an isometry, and for every instance, every family of
self-adjoint interval-integrable pieces and every propagator of the piecewise path, the full
output is exact if `T = 0`, and within the integrated sample-error certificate if `α = 0`. -/
theorem zero_bound (O : X → Fin M → EuclideanSpace ℂ B₀ →L[ℂ] EuclideanSpace ℂ B₀)
    (hM : 0 < M) (b₀ : B₀) (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ B₀)
    (hJ : J† ∘L J = 1) (t : ℕ → ℝ) (α T ε : ℝ) (N : ℕ) (hmesh : IsMesh t M T) :
    (MultiOracleCircuit.Program.identity
        (O := BlockEncoding.alignedOracle O N α T ε)).count = 0 ∧
      (BlockEncoding.alignedInput hM b₀ J hJ t N α T ε)† ∘L
        BlockEncoding.alignedInput hM b₀ J hJ t N α T ε = 1 ∧
      ∀ x, IsUnitary ((MultiOracleCircuit.Program.identity
          (O := BlockEncoding.alignedOracle O N α T ε)).eval x) ∧
        ∀ (Hp : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
          (U : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
          (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), star (Hp r u) = Hp r u) →
          (∀ r : Fin M, IntervalIntegrable (Hp r) volume (t r) (t ((r : ℕ) + 1))) →
          U 0 = 1 →
          (∀ r : Fin M, SolvesOn (Hp r) U (t r) (t ((r : ℕ) + 1))) →
          (T = 0 → ‖(MultiOracleCircuit.Program.identity
              (O := BlockEncoding.alignedOracle O N α T ε)).eval x ∘L
              BlockEncoding.alignedInput hM b₀ J hJ t N α T ε -
            BlockEncoding.alignedInput hM b₀ J hJ t N α T ε ∘L U T‖ = 0) ∧
          (α = 0 → ‖(MultiOracleCircuit.Program.identity
              (O := BlockEncoding.alignedOracle O N α T ε)).eval x ∘L
              BlockEncoding.alignedInput hM b₀ J hJ t N α T ε -
            BlockEncoding.alignedInput hM b₀ J hJ t N α T ε ∘L U T‖ ≤
            ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
              ‖Hp r u - BlockEncoding.blockSample (O x r) J α‖) := by
  have hIso := alignedInput_isometry hM b₀ J hJ t N α T ε
  refine ⟨MultiOracleCircuit.Program.count_identity, hIso,
    fun x => ⟨?_, fun Hp U hPath hInt hU0 hU => ⟨fun hT0 => ?_, fun hα0 => ?_⟩⟩⟩
  · rw [MultiOracleCircuit.Program.eval_identity]
    exact isUnitary_one
  · rw [hT0, hU0, MultiOracleCircuit.Program.eval_identity, sub_eq_zero.mpr, norm_zero]
    rfl
  · let A : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun _ => 0
    let Hq : ℕ → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
      Hp (Sampled.sampleIndex hM r)
    have hPw : IsPiecewisePropagator Hq t M U := by
      refine ⟨hU0, fun r hr => ?_⟩
      have h := hU ⟨r, hr⟩
      simp only [Hq, BlockEncoding.sampleIndex_of_lt hM hr]
      exact h
    have hHq : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), star (Hq r u) = Hq r u := by
      intro r hr u hu
      simp only [Hq, BlockEncoding.sampleIndex_of_lt hM hr]
      exact hPath ⟨r, hr⟩ u hu
    have hA : ∀ r, star (A r) = A r := fun _ => by
      change star (0 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) = 0
      exact star_zero (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    have hIntq : ∀ r < M, IntervalIntegrable (Hq r) volume (t r) (t (r + 1)) := by
      intro r hr
      simp only [Hq, BlockEncoding.sampleIndex_of_lt hM hr]
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
          ‖Hp r u - BlockEncoding.blockSample (O x r) J α‖ := by
      rw [← Fin.sum_univ_eq_sum_range (fun r => ∫ u in t r..t (r + 1), ‖Hq r u - A r‖) M]
      apply Finset.sum_congr rfl
      intro r _
      have hidx : Sampled.sampleIndex hM r = r := BlockEncoding.sampleIndex_of_lt hM r.isLt
      simp only [Hq, A, hidx, hα0, blockSample_zero]
    rw [hSum] at hErr
    rw [MultiOracleCircuit.Program.eval_identity]
    exact (TimeUniform.identity_error_le _ hIso (U T)).trans hErr

/-- **Equation `hs:eq:blockadditive` for every `α ≥ 0` and `T ≥ 0`.** Under the hypotheses of
the released `BlockEncoding.simulation` with `0 ≤ α` and `0 ≤ T` in place of `0 < α` and
`0 < T`, there is one program over the controlled time-indexed oracles, uniform over the
instances, with at most `0` queries if `T = 0` or `α = 0` and at most
`2304 (α T + 1 + log(3/ε))` otherwise; the clean encoding is an isometry and, for every
instance, every family of self-adjoint interval-integrable pieces whose integrated sample-error
certificate is at most `ε / 9`, and every propagator of the piecewise path, the full output is
within `ε` of the clean evolved state. -/
theorem simulation_nonneg (O : X → Fin M → EuclideanSpace ℂ B₀ →L[ℂ] EuclideanSpace ℂ B₀)
    (hOs : ∀ x r, star (O x r) = O x r) (hOu : ∀ x r, IsUnitary (O x r)) (hM : 0 < M)
    (b₀ : B₀) (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ B₀) (hJ : J† ∘L J = 1)
    (t : ℕ → ℝ) (α T ε : ℝ) (N : ℕ) (hα : 0 ≤ α) (hT : 0 ≤ T) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hN : 0 < N) (hmesh : IsMesh t M T)
    (hClock : 4 * (α * T) ≤ N) (hCayley : 9 * (α * T) ^ 3 ≤ ε * (N : ℝ) ^ 2)
    (hRefine : 9 * M * (α * T) ≤ ε * N) :
    ∃ p : MultiOracleCircuit.Program (BlockEncoding.alignedOracle O N α T ε),
      (p.count : ℝ) ≤ (if T = 0 ∨ α = 0 then 0 else 2304 * (α * T + 1 + Real.log (3 / ε))) ∧
      (BlockEncoding.alignedInput hM b₀ J hJ t N α T ε)† ∘L
        BlockEncoding.alignedInput hM b₀ J hJ t N α T ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ∀ (Hp : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
          (U : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
          (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), star (Hp r u) = Hp r u) →
          (∀ r : Fin M, IntervalIntegrable (Hp r) volume (t r) (t ((r : ℕ) + 1))) →
          ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
            ‖Hp r u - BlockEncoding.blockSample (O x r) J α‖ ≤ ε / 9 →
          U 0 = 1 →
          (∀ r : Fin M, SolvesOn (Hp r) U (t r) (t ((r : ℕ) + 1))) →
          ‖p.eval x ∘L BlockEncoding.alignedInput hM b₀ J hJ t N α T ε -
            BlockEncoding.alignedInput hM b₀ J hJ t N α T ε ∘L U T‖ ≤ ε := by
  by_cases hZero : T = 0 ∨ α = 0
  · obtain ⟨hc, hIn, hAct⟩ := zero_bound O hM b₀ J hJ t α T ε N hmesh
    refine ⟨MultiOracleCircuit.Program.identity, ?_, hIn,
      fun x => ⟨(hAct x).1, fun Hp U hPath hInt hCert hU0 hU => ?_⟩⟩
    · rw [if_pos hZero, hc, Nat.cast_zero]
    · obtain ⟨hT0, hα0⟩ := (hAct x).2 Hp U hPath hInt hU0 hU
      rcases hZero with h | h
      · rw [hT0 h]
        exact hε.le
      · exact (hα0 h).trans (by linarith)
  · have hαpos : 0 < α := lt_of_le_of_ne hα (fun h => hZero (Or.inr h.symm))
    have hTpos : 0 < T := lt_of_le_of_ne hT (fun h => hZero (Or.inl h.symm))
    obtain ⟨p, hCount, hIn, hAct⟩ := BlockEncoding.simulation O hOs hOu hM b₀ J hJ t α T ε N
      hαpos hTpos hε hεOne hN hmesh hClock hCayley hRefine
    refine ⟨p, ?_, hIn, hAct⟩
    rw [if_neg hZero]
    exact hCount

end
end SparseHamiltonian.ZeroTimeRemarks.TimeBlock
