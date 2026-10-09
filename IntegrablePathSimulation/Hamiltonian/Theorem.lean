import IntegrablePathSimulation.Propagator.Duhamel
import IntegrablePathSimulation.Propagator.Uniqueness
import TimeDependentExtensions.Hamiltonian.Theorem

set_option autoImplicit false

/-!
# Time-dependent sparse Hamiltonian simulation for integrable Hermitian paths

The paragraph "Regularity and coherent parameters" after the proof of Theorem `hs:thm:time`
of the manuscript (lines 1618-1632), at lines 1622-1626: "More generally, for an integrable
Hermitian path it suffices to have a certified bound on the sum of the integrated sample errors
`∑_r ∫_{t_r}^{t_{r+1}} ‖H(u) - H̃_r‖ du`. All uses of regularity are confined to this
classical error certificate."

`simulation` states this with the released oracle family, clean encoding and query bound of
`TimeDependentExtensions.Hamiltonian.simulation` (the program is built as in the released
proof; `simulation_piecewise` derives the released statement with the same program): under the
public slot conditions `4 s η T ≤ N`, `9 (√s η T)³ ≤ ε N²` and `9 M √s η T ≤ ε N`, one unitary
oracle program and one clean encoding satisfy `‖𝒜 ι - ι U(T)‖ ≤ ε` for every instance `x`,
every path `H` on `[0, T]` that is Hermitian at almost every time and interval integrable,
whose certificate against the represented samples `H̃_r = D.matrix (x, r)` is at most `ε / 9`,
and every propagator `U` of `H` in the integral (Carathéodory) sense
(`Propagator.IsPropagator`; one exists and it is unique,
`Propagator.existsUnique_isPropagator`). The query count is
`995328 (√s τ + √(s τ log(1/ε)) + log(1/ε))`, `τ = η T`; neither `M`, `N`, the mesh, the path
nor the certificate enters it.

The proof is the released one with the classical refinement estimate replaced by
`Propagator.IsPropagator.refined_error`.
-/

namespace IntegrablePathSimulation.Hamiltonian

noncomputable section

open SparseHamiltonian SparseHamiltonian.TimeDependent ContinuousLinearMap OracleCircuit
open NativeSparseBlockEncoding CayleyClockInterface FixedNativeCayleySimulation
open MeasureTheory Set
open TimeDependentExtensions (IsMesh)
open IntegrablePathSimulation.Propagator (IsPropagator)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

set_option maxRecDepth 8192 in
/-- **Theorem `hs:thm:time` for integrable Hermitian paths, with the integrated certificate.**
For any mesh `0 = t_0 ≤ ⋯ ≤ t_M = T` and any slot count `N` with `4 s η T ≤ N`,
`9 (√s η T)³ ≤ ε N²` and `9 M √s η T ≤ ε N`, one oracle program over the released oracle
family, uniform over the unknown instance and unitary on every instance, and the released clean
encoding satisfy
`‖𝒜 ι - ι U(T)‖ ≤ ε` for every instance `x`, every path `H` that is Hermitian at almost every
time of `[0, T]` and interval integrable on `[0, T]`, whose integrated sample errors
`∑_r ∫_{t_r}^{t_{r+1}} ‖H(u) - H̃_r‖ du` are at most `ε / 9`, and every propagator `U` of `H`
on `[0, T]` in the integral sense. The query count is that of
`TimeDependentExtensions.Hamiltonian.simulation`. -/
theorem simulation (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (η T ε : ℝ)
    (N : ℕ) (hη : 0 < η) (hT : 0 < T) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) (hN : 0 < N)
    (hmesh : IsMesh t M T)
    (hClock : 4 * s * (η * T) ≤ N)
    (hCayley : 9 * (Real.sqrt s * (η * T)) ^ 3 ≤ ε * (N : ℝ) ^ 2)
    (hRefine : 9 * M * (Real.sqrt s * (η * T)) ≤ ε * N)
    (hH : ∀ y, (D.matrix y).IsHermitian)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * T) +
            Real.sqrt ((s : ℝ) * (η * T) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε)† ∘L
          TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ (H : ℝ → Matrix n n ℂ) (U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)),
            (∀ᵐ u, u ∈ Icc 0 T → (H u).IsHermitian) →
            IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (H u)) volume 0 T →
            ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
              ‖SparseStateOverlap.matrixOperator (H u) -
                SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 9 →
            IsPropagator (fun u => SparseStateOverlap.matrixOperator (H u)) U T →
            ‖p.eval x ∘L TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε -
              TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε ∘L U T‖ ≤ ε := by
  have hs : (1 : ℝ) ≤ s := by exact_mod_cast D.slots_pos
  have hτ : 0 ≤ η * T := mul_nonneg hη.le hT.le
  have hεOne : ε ≤ 1 := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨γ, hγ, hγOne, hWidth, hBudget⟩ :=
    ImprovedPrecisionBudget.exists_rescaling_for_precision (s : ℝ) (η * T) ε hs hτ hε hεOne
  have hStep := TimeDependent.step_le_quarter (s := s) (M := N) γ (η * T) hs hγ hWidth hτ hN
    hClock
  obtain ⟨p, hCount, hIn, hOut, hAct⟩ :=
    TimeDependentExtensions.Refined.exists_sampled_simulation
    (NativeSparseRescaling.normalize D η hη) hM (TimeDependentExtensions.pieceOf t T N hM) hN
    (fun y => NativeSparseRescaling.normalize_hermitian D η hη y (hH y))
    (fun y i => NativeSparseRescaling.normalized_row_energy D η hη y i (hrow y i))
    (fun y j => NativeSparseRescaling.normalized_column_energy D η hη y j (hcol y j))
    γ (η * T) ε hγ hγOne hτ hε hεOne hStep
  let q := AlignedMultiOracleProgram.program _ _ hIn hOut p
  refine ⟨γ, hγ, hγOne, hWidth, q, ?_, ?_, fun x => ⟨?_, ?_⟩⟩
  · have hqc : q.count = p.count := AlignedMultiOracleProgram.program_count _ _ hIn hOut p
    calc
      (q.count : ℝ) = (p.count : ℝ) := by exact_mod_cast hqc
      _ ≤ _ := ManuscriptPrecision.query_count_log_one (p.count : ℝ) (s : ℝ) (η * T) ε
        (by linarith) hτ hε hεHalf
        (TimeDependent.count_le_shape (M := N) γ (η * T) ε hγ hτ hε hεOne hN hBudget
          p.count hCount)
  · exact AlignedMultiOracleProgram.input_isometry _ hIn
  · exact q.eval_unitary (CoherentQuerySchedule.oracle_unitary _
      (Sampled.oracle_unitary (NativeSparseRescaling.normalize D η hη) N _)) x
  · intro H U hPath hInt hCert hU
    have hErr := (hAct x).2
    rw [TimeDependentExtensions.Hamiltonian.sampledEvolution_normalize D hM t N η T hη x]
      at hErr
    let A : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
      SparseStateOverlap.matrixOperator (D.matrix (x, Sampled.sampleIndex hM r))
    let Hop : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun u =>
      SparseStateOverlap.matrixOperator (H u)
    have hHop : ∀ᵐ u, u ∈ Icc 0 T → star (Hop u) = Hop u := by
      filter_upwards [hPath] with u hu hmem
      exact SparseValuePrecision.matrixOperator_star_eq _ (hu hmem)
    have hA : ∀ r, star (A r) = A r := fun r =>
      SparseValuePrecision.matrixOperator_star_eq _ (hH _)
    have hΛ : ∀ r, ‖A r‖ ≤ Real.sqrt s * η := fun r =>
      TimeDependentExtensions.Hamiltonian.sample_norm_le D η hη _ (hH _) (hrow _) (hcol _)
    have hRef := Propagator.IsPropagator.refined_error A hmesh hT hN hU hHop hA hΛ hInt
    have hCertR : ∑ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖Hop u - A r‖ ≤ ε / 9 := by
      rw [← Fin.sum_univ_eq_sum_range (fun r => ∫ u in t r..t (r + 1), ‖Hop u - A r‖) M]
      simpa only [Hop, A, TimeDependentExtensions.Hamiltonian.sampleIndex_val] using hCert
    let D' := NativeSparseRescaling.normalize D η hη
    let σ := TimeDependentExtensions.pieceOf t T N hM
    have hOutNorm : ‖TimeDependentExtensions.Refined.output D' hM σ N γ (η * T) ε‖ ≤ 1 := by
      apply opNorm_le_bound _ zero_le_one
      intro v
      rw [((TimeDependentExtensions.Refined.output D' hM σ N γ (η * T) ε
        ).norm_map_iff_adjoint_comp_self.mpr
        hOut) v, one_mul]
    let S := TimeDependentExtensions.refinedEvolution A t T N M
    have hAligned := AlignedMultiOracleProgram.program_error _ _ hIn hOut p x (U T)
    change ‖q.eval x ∘L TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε -
      TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε ∘L U T‖ ≤ ε
    rw [show TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε =
      AlignedMultiOracleProgram.input
        (TimeDependentExtensions.Refined.input D' hM σ N γ (η * T) ε) from rfl, hAligned]
    have hCay : (N : ℝ) * (Real.sqrt s * (η * T) / N) ^ 3 ≤ ε / 9 := by
      have hNsq : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
      have heq : (N : ℝ) * (Real.sqrt s * (η * T) / N) ^ 3 =
          (Real.sqrt s * (η * T)) ^ 3 / (N : ℝ) ^ 2 := by
        field_simp
      rw [heq, div_le_iff₀ hNsq]
      linarith
    have hMis : (M : ℝ) * (T / N) * (Real.sqrt s * η) ≤ ε / 9 := by
      have heq : (M : ℝ) * (T / N) * (Real.sqrt s * η) = M * (Real.sqrt s * (η * T)) / N := by
        field_simp
      rw [heq, div_le_iff₀ hNR]
      linarith
    calc
      _ ≤ ‖p.eval x ∘L TimeDependentExtensions.Refined.input D' hM σ N γ (η * T) ε -
            TimeDependentExtensions.Refined.output D' hM σ N γ (η * T) ε ∘L S‖ +
          ‖TimeDependentExtensions.Refined.output D' hM σ N γ (η * T) ε ∘L S -
            TimeDependentExtensions.Refined.output D' hM σ N γ (η * T) ε ∘L U T‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (2 * (ε / 3) + N * (Real.sqrt s * (η * T) / N) ^ 3) +
          1 * (ε / 9 + M * (T / N) * (Real.sqrt s * η)) := by
        apply add_le_add hErr
        rw [← comp_sub]
        refine (opNorm_comp_le _ _).trans (mul_le_mul hOutNorm ?_ (norm_nonneg _) zero_le_one)
        rw [norm_sub_rev]
        exact hRef.trans (add_le_add_left hCertR _)
      _ ≤ ε := by linarith

end

end IntegrablePathSimulation.Hamiltonian
