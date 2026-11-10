import IntegrablePathSimulation.Propagator.Duhamel
import IntegrablePathSimulation.Propagator.Classical
import TimeDependentExtensions.BlockEncoding.Theorem

set_option autoImplicit false

/-!
# Time-indexed block encodings for integrable Hermitian paths

Eqs. `hs:eq:blockspecial` and `hs:eq:blockadditive` of the manuscript (after
Theorem `hs:thm:time`): with coherent controlled access to Hermitian unitaries `O_r` with
`J† O_r J = H̃_r / α_BE`, the chronological proof gives equation `hs:eq:blockadditive`,
`𝒪(α_BE T + log(1/ε))` queries. The comparison with the continuous evolution is the one of
Theorem `hs:thm:time`, and by the paragraphs after its proof the integrated sample-error
certificate replaces the Lipschitz and representation terms, so the bound holds for integrable
Hermitian paths.

* `simulation`: a program over the released oracle family, and the released encoding, of
  `TimeDependentExtensions.BlockEncoding.simulation`, with the same slot conditions
  `4 α T ≤ N`, `9 (α T)³ ≤ ε N²`, `9 M α T ≤ ε N` and the same count
  `2304 (α T + 1 + log(3/ε))` of controlled time-indexed calls, inverses included, satisfy
  `‖𝒜 ι - ι U(T)‖ ≤ ε` for every path `H` on `[0, T]` that is self-adjoint at almost every
  time and interval integrable, whose certificate `∑_r ∫ ‖H(u) - H̃_r‖ du` against the
  represented samples `H̃_r = α J† O_r J` is at most `ε / 9`, and every propagator `U` of `H`
  in the integral sense (`Propagator.IsPropagator`).
* `simulation_piecewise`: the released `TimeDependentExtensions.BlockEncoding.simulation`
  (classical piecewise propagators), with its statement unchanged, as a corollary
  (`Propagator.isPropagator_glue`).
-/

namespace IntegrablePathSimulation.BlockEncoding

noncomputable section

open SparseHamiltonian SparseHamiltonian.TimeDependent ContinuousLinearMap OracleCircuit
open CayleyClockInterface MeasureTheory Set
open TimeDependentExtensions (IsMesh)
open TimeDependentExtensions.BlockEncoding (alignedOracle alignedInput blockSample)
open IntegrablePathSimulation.Propagator (IsPropagator)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048

variable {X n B₀ : Type*} [Fintype n] [DecidableEq n] [Fintype B₀] [DecidableEq B₀] {M : ℕ}

set_option maxRecDepth 8192 in
omit [DecidableEq n] in
/-- **Equation `hs:eq:blockadditive` for integrable Hermitian paths.** On any mesh, under
`4 α T ≤ N`, `9 (α T)³ ≤ ε N²` and `9 M α T ≤ ε N`, one input-independent unitary program
and one fixed clean encoding satisfy `‖𝒜 ι - ι U(T)‖ ≤ ε` for every instance, every path
that is self-adjoint at almost every time of `[0, T]` and interval integrable on `[0, T]`,
whose integrated sample errors `∑_r ∫ ‖H(u) - H̃_r‖ du` are at most `ε / 9`, and every
propagator of that path in the integral sense, with at most `2304 (α T + 1 + log(3/ε))`
queries, including inverse calls. -/
theorem simulation (O : X → Fin M → EuclideanSpace ℂ B₀ →L[ℂ] EuclideanSpace ℂ B₀)
    (hOs : ∀ x r, star (O x r) = O x r) (hOu : ∀ x r, IsUnitary (O x r)) (hM : 0 < M)
    (b₀ : B₀) (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ B₀) (hJ : J† ∘L J = 1)
    (t : ℕ → ℝ) (α T ε : ℝ) (N : ℕ) (hα : 0 < α) (hT : 0 < T) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hN : 0 < N) (hmesh : IsMesh t M T)
    (hClock : 4 * (α * T) ≤ N) (hCayley : 9 * (α * T) ^ 3 ≤ ε * (N : ℝ) ^ 2)
    (hRefine : 9 * M * (α * T) ≤ ε * N) :
    ∃ p : MultiOracleCircuit.Program (alignedOracle O N α T ε),
      (p.count : ℝ) ≤ 2304 * (α * T + 1 + Real.log (3 / ε)) ∧
      (alignedInput hM b₀ J hJ t N α T ε)† ∘L alignedInput hM b₀ J hJ t N α T ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ∀ (H U : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
          (∀ᵐ u, u ∈ Icc 0 T → star (H u) = H u) →
          IntervalIntegrable H volume 0 T →
          ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖H u - blockSample (O x r) J α‖ ≤
            ε / 9 →
          IsPropagator H U T →
          ‖p.eval x ∘L alignedInput hM b₀ J hJ t N α T ε -
            alignedInput hM b₀ J hJ t N α T ε ∘L U T‖ ≤ ε := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hStep : α * T / N ≤ 1 / 4 := by
    rw [div_le_iff₀ hNR]
    linarith
  let σ := TimeDependentExtensions.pieceOf t T N hM
  obtain ⟨p, hCount, hIn, hOut, hAct⟩ :=
    TimeDependentExtensions.BlockEncoding.exists_simulation O hOs hOu hM b₀ J hJ σ hN α T ε hα
      hT.le hε hεOne hStep
  let q := AlignedMultiOracleProgram.program _ _ hIn hOut p
  refine ⟨q, ?_, AlignedMultiOracleProgram.input_isometry _ hIn, fun x => ⟨?_, ?_⟩⟩
  · have hqc : q.count = p.count := AlignedMultiOracleProgram.program_count _ _ hIn hOut p
    have hW : 0 ≤ (N : ℝ) * (α * T / N) * 1 := by positivity
    have hdeg : (TimeDependentExtensions.BlockEncoding.degree N α T ε : ℝ) ≤
        128 * ((N : ℝ) * (α * T / N) * 1 +
        1 * (1 + SharpFilterSchedule.logBudget (ε / 3))) :=
      SharpFilterSchedule.degree_le 1 ((N : ℝ) * (α * T / N) * 1) (ε / 3) le_rfl hW
        (by positivity) (by linarith)
    have hWeq : (N : ℝ) * (α * T / N) * 1 = α * T := by field_simp
    have hlog : SharpFilterSchedule.logBudget (ε / 3) = Real.log (3 / ε) := by
      unfold SharpFilterSchedule.logBudget
      congr 1
      field_simp
    rw [hWeq, hlog] at hdeg
    have hpc : (p.count : ℝ) ≤
        6 * (TimeDependentExtensions.BlockEncoding.degree N α T ε : ℝ) * 3 := by
      exact_mod_cast hCount
    have hdeg' : (TimeDependentExtensions.BlockEncoding.degree N α T ε : ℝ) ≤
        128 * (α * T + 1 * (1 + Real.log (3 / ε))) := hdeg
    calc (q.count : ℝ) = (p.count : ℝ) := by exact_mod_cast hqc
      _ ≤ 6 * (TimeDependentExtensions.BlockEncoding.degree N α T ε : ℝ) * 3 := hpc
      _ ≤ 6 * (128 * (α * T + 1 * (1 + Real.log (3 / ε)))) * 3 := by nlinarith
      _ = 2304 * (α * T + 1 + Real.log (3 / ε)) := by ring
  · exact q.eval_unitary (CoherentQuerySchedule.oracle_unitary _
      (TimeDependentExtensions.BlockEncoding.oracle_unitary O hOu N _)) x
  · intro H U hPath hInt hCert hU
    have hErr := (hAct x).2
    let A : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
      blockSample (O x (Sampled.sampleIndex hM r)) J α
    have hEvol : TimeDependentExtensions.BlockEncoding.blockEvolution O J σ N α T x =
        TimeDependentExtensions.refinedEvolution A t T N M := by
      unfold TimeDependentExtensions.BlockEncoding.blockEvolution
        TimeDependentExtensions.refinedEvolution
      congr 1
      funext k
      have hk : Sampled.sampleIndex hM (TimeDependentExtensions.slotPiece t T N M k) = σ k :=
        TimeDependentExtensions.BlockEncoding.sampleIndex_of_lt hM
          (TimeDependentExtensions.slotPiece_lt hM k)
      simp only [A, hk]
    rw [hEvol] at hErr
    have hA : ∀ r, star (A r) = A r := fun r =>
      TimeDependentExtensions.BlockEncoding.blockSample_self_adjoint _ (hOs _ _) J α
    have hΛ : ∀ r, ‖A r‖ ≤ α := fun r =>
      TimeDependentExtensions.BlockEncoding.blockSample_norm_le _ (hOu _ _) J hJ hα.le
    have hRef := Propagator.IsPropagator.refined_error A hmesh hT hN hU hPath hA hΛ hInt
    have hCertR : ∑ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖H u - A r‖ ≤ ε / 9 := by
      rw [← Fin.sum_univ_eq_sum_range (fun r => ∫ u in t r..t (r + 1), ‖H u - A r‖) M]
      have hidx : ∀ r : Fin M, Sampled.sampleIndex hM r = r := fun r =>
        TimeDependentExtensions.BlockEncoding.sampleIndex_of_lt hM r.isLt
      simpa only [A, hidx] using hCert
    have hOutNorm :
        ‖TimeDependentExtensions.BlockEncoding.output hM b₀ J hJ σ N α T ε‖ ≤ 1 := by
      apply opNorm_le_bound _ zero_le_one
      intro v
      rw [(norm_map_iff_adjoint_comp_self _).mpr hOut v, one_mul]
    let S := TimeDependentExtensions.refinedEvolution A t T N M
    have hAligned := AlignedMultiOracleProgram.program_error _ _ hIn hOut p x (U T)
    change ‖q.eval x ∘L alignedInput hM b₀ J hJ t N α T ε -
      alignedInput hM b₀ J hJ t N α T ε ∘L U T‖ ≤ ε
    rw [show alignedInput hM b₀ J hJ t N α T ε = AlignedMultiOracleProgram.input
      (TimeDependentExtensions.BlockEncoding.input hM b₀ J hJ σ N α T ε) from rfl, hAligned]
    have hCay : (N : ℝ) * (α * T / N) ^ 3 ≤ ε / 9 := by
      have hNsq : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
      have heq : (N : ℝ) * (α * T / N) ^ 3 = (α * T) ^ 3 / (N : ℝ) ^ 2 := by
        field_simp
      rw [heq, div_le_iff₀ hNsq]
      linarith
    have hMis : (M : ℝ) * (T / N) * α ≤ ε / 9 := by
      have heq : (M : ℝ) * (T / N) * α = M * (α * T) / N := by
        field_simp
      rw [heq, div_le_iff₀ hNR]
      linarith
    calc
      _ ≤ ‖p.eval x ∘L TimeDependentExtensions.BlockEncoding.input hM b₀ J hJ σ N α T ε -
            TimeDependentExtensions.BlockEncoding.output hM b₀ J hJ σ N α T ε ∘L S‖ +
          ‖TimeDependentExtensions.BlockEncoding.output hM b₀ J hJ σ N α T ε ∘L S -
            TimeDependentExtensions.BlockEncoding.output hM b₀ J hJ σ N α T ε ∘L U T‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (2 * (ε / 3) + N * (α * T / N) ^ 3) + 1 * (ε / 9 + M * (T / N) * α) := by
        apply add_le_add hErr
        rw [← comp_sub]
        refine (opNorm_comp_le _ _).trans (mul_le_mul hOutNorm ?_ (norm_nonneg _) zero_le_one)
        rw [norm_sub_rev]
        exact hRef.trans (add_le_add_left hCertR _)
      _ ≤ ε := by linarith

set_option maxRecDepth 8192 in
omit [DecidableEq n] in
/-- **The released block-encoding theorem as a corollary.** The statement of
`TimeDependentExtensions.BlockEncoding.simulation` (self-adjoint, interval-integrable pieces,
one per mesh interval, and classical piecewise propagators), derived from `simulation` for
integrable paths. -/
theorem simulation_piecewise (O : X → Fin M → EuclideanSpace ℂ B₀ →L[ℂ] EuclideanSpace ℂ B₀)
    (hOs : ∀ x r, star (O x r) = O x r) (hOu : ∀ x r, IsUnitary (O x r)) (hM : 0 < M)
    (b₀ : B₀) (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ B₀) (hJ : J† ∘L J = 1)
    (t : ℕ → ℝ) (α T ε : ℝ) (N : ℕ) (hα : 0 < α) (hT : 0 < T) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hN : 0 < N) (hmesh : IsMesh t M T)
    (hClock : 4 * (α * T) ≤ N) (hCayley : 9 * (α * T) ^ 3 ≤ ε * (N : ℝ) ^ 2)
    (hRefine : 9 * M * (α * T) ≤ ε * N) :
    ∃ p : MultiOracleCircuit.Program (alignedOracle O N α T ε),
      (p.count : ℝ) ≤ 2304 * (α * T + 1 + Real.log (3 / ε)) ∧
      (alignedInput hM b₀ J hJ t N α T ε)† ∘L alignedInput hM b₀ J hJ t N α T ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ∀ (Hp : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
          (U : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
          (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), star (Hp r u) = Hp r u) →
          (∀ r : Fin M, IntervalIntegrable (Hp r) volume (t r) (t ((r : ℕ) + 1))) →
          ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖Hp r u - blockSample (O x r) J α‖ ≤
            ε / 9 →
          U 0 = 1 →
          (∀ r : Fin M, SolvesOn (Hp r) U (t r) (t ((r : ℕ) + 1))) →
          ‖p.eval x ∘L alignedInput hM b₀ J hJ t N α T ε -
            alignedInput hM b₀ J hJ t N α T ε ∘L U T‖ ≤ ε := by
  obtain ⟨p, hCount, hIn, hAction⟩ := simulation O hOs hOu hM b₀ J hJ t α T ε N hα hT hε hεOne
    hN hmesh hClock hCayley hRefine
  refine ⟨p, hCount, hIn, fun x => ⟨(hAction x).1, ?_⟩⟩
  intro Hp U hPath hInt hCert hU0 hU
  let Hq : ℕ → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
    Hp (Sampled.sampleIndex hM r)
  have hIntq : ∀ r < M, IntervalIntegrable (Hq r) volume (t r) (t (r + 1)) := by
    intro r hr
    simp only [Hq, TimeDependentExtensions.BlockEncoding.sampleIndex_of_lt hM hr]
    exact hInt ⟨r, hr⟩
  apply (hAction x).2 (Propagator.glue Hq t M) U
  · refine ae_of_all _ fun u hu => ?_
    have hmem := Propagator.mem_Icc_pieceIndex hmesh hM hu
    have hlt := Propagator.pieceIndex_lt (t := t) hM u
    change star (Hq (Propagator.pieceIndex t M u) u) = Hq (Propagator.pieceIndex t M u) u
    simp only [Hq, TimeDependentExtensions.BlockEncoding.sampleIndex_of_lt hM hlt]
    exact hPath ⟨_, hlt⟩ u hmem
  · exact Propagator.intervalIntegrable_glue hmesh hIntq
  · refine le_trans (le_of_eq ?_) hCert
    refine Finset.sum_congr rfl fun r _ => ?_
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le (hmesh.mono (Nat.le_succ r))]
    filter_upwards [Propagator.glue_ae_eq Hq hmesh r.isLt] with u hu hmem
    rw [hu hmem]
    simp only [Hq, TimeDependentExtensions.BlockEncoding.sampleIndex_of_lt hM r.isLt, Fin.eta]
  · exact Propagator.isPropagator_glue hmesh ⟨hU0, fun r hr => by
      simpa only [Hq, TimeDependentExtensions.BlockEncoding.sampleIndex_of_lt hM hr] using
        hU ⟨r, hr⟩⟩ hIntq

end

end IntegrablePathSimulation.BlockEncoding
