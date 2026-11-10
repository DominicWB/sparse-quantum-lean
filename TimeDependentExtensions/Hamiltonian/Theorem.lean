import TimeDependentExtensions.Hamiltonian.Native
import TimeDependentExtensions.Mesh.Duhamel
import TimeDependentHamiltonian.Theorem

set_option autoImplicit false

/-!
# Time-dependent sparse Hamiltonian simulation on general meshes

The generalisations of Theorem `hs:thm:time` stated after its proof: an arbitrary mesh
`0 = t_0 ≤ t_1 ≤ ⋯ ≤ t_M = T`, a path with breakpoints at the mesh points (one piece `H_r` per
interval, with the one-sided sample on each interval), and the integrated sample-error certificate
`∑_r ∫_{t_r}^{t_{r+1}} ‖H_r(u) - H̃_r‖ du`.

The coherent sampled-time oracle supplies one represented sample `H̃_r = D.matrix (x, r)`
per interval. The program runs the released chronological clock on `N` slots of length
`T / N`; slot `k` uses the sample of the interval containing it (`pieceOf`) through the
clean encoding, while the oracle family does not depend on the mesh
(`Refined.exists_sampled_simulation`). The
refined slot product is within `M (T / N) √s η` of the mesh product, and the mesh product is
within the certificate of every propagator of the piecewise path (`refined_error`).

`simulation`: under the public slot conditions `4 s η T ≤ N`, `9 (√s η T)³ ≤ ε N²` and
`9 M √s η T ≤ ε N`, one unitary oracle program and one clean encoding satisfy
`‖𝒜 ι - ι U(T)‖ ≤ ε` for every instance, every piecewise path whose certificate is at most
`ε / 9`, and every propagator of that path, with the released query bound
`995328 (√s τ + √(s τ log(1/ε)) + log(1/ε))`, `τ = η T`. Neither `M`, `N`, the mesh nor
the certificate enters the query count.
-/

namespace TimeDependentExtensions

namespace Hamiltonian

noncomputable section

open SparseHamiltonian SparseHamiltonian.TimeDependent ContinuousLinearMap OracleCircuit
open NativeSparseBlockEncoding CayleyClockInterface FixedNativeCayleySimulation
open MeasureTheory Set
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

theorem sampleIndex_val (hM : 0 < M) (r : Fin M) : Sampled.sampleIndex hM r = r :=
  Fin.ext (Nat.mod_eq_of_lt r.isLt)

theorem sampleIndex_of_lt (hM : 0 < M) {r : ℕ} (hr : r < M) :
    Sampled.sampleIndex hM r = ⟨r, hr⟩ :=
  Fin.ext (Nat.mod_eq_of_lt hr)

/-- The complete physical workspace on `N` slots, including the alignment spectator. -/
abbrev Workspace (n Z : Type*) [Fintype n] [Fintype Z] (s M N : ℕ) (γ η T ε : ℝ) :=
  CleanOutputAlignment.Double
    (Sampled.Physical n Z M N (Sampled.degree (s : ℝ) γ (η * T) ε N))

/-- Each query is one coherent sampled-time native primitive with untouched spectator
registers. -/
abbrev oracle (D : Data (X × Fin M) n Z s) (N : ℕ) (γ η T ε : ℝ) :
    Query → X → Workspace n Z s M N γ η T ε →L[ℂ] Workspace n Z s M N γ η T ε :=
  AlignedMultiOracleProgram.oracle (Sampled.oracle D N (Sampled.degree (s : ℝ) γ (η * T) ε N))

omit [DecidableEq Z] in
theorem oracle_unitary (D : Data (X × Fin M) n Z s) (N : ℕ) (γ η T ε : ℝ) (l : Query)
    (x : X) : IsUnitary (oracle D N γ η T ε l x) :=
  CoherentQuerySchedule.oracle_unitary _ (Sampled.oracle_unitary D N _) l x

/-- The same known clean preparation at both ends of the circuit. It depends only on public
data: the slot embedding, the mesh, the slot count, the rescaling and the precision. -/
def input (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ) (γ η T ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] Workspace n Z s M N γ η T ε :=
  AlignedMultiOracleProgram.input (Refined.input D hM (pieceOf t T N hM) N γ (η * T) ε)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The sample Hamiltonians of normalised sparse data have norm at most `√s`. -/
theorem matrixOperator_norm_le_sqrt {Y : Type*} (D : Data Y n Z s) (y : Y)
    (hH : (D.matrix y).IsHermitian)
    (hrow : ∀ i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ 1) (hcol : ∀ j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ 1) :
    ‖SparseStateOverlap.matrixOperator (D.matrix y)‖ ≤ Real.sqrt s := by
  have hsR : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.mpr (by exact_mod_cast D.slots_pos)
  have hB : ‖(boundary D)†‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact SparseMatrixNorm.norm_le_one_of_adjoint_comp _ (boundary_isometry D)
  have h1 : ‖(boundary D)† ∘L generator D y ∘L boundary D‖ ≤ 1 :=
    (opNorm_comp_le _ _).trans (by
      calc ‖(boundary D)†‖ * ‖generator D y ∘L boundary D‖ ≤ 1 * 1 :=
            mul_le_mul hB (generator_boundary_norm_le D y hrow hcol) (norm_nonneg _)
              zero_le_one
        _ = 1 := one_mul 1)
  rw [compression D y hH, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hsR.le] at h1
  rwa [inv_mul_le_iff₀ hsR, mul_one] at h1

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The samples of sparse data with row and column norms at most `η` have norm at most
`√s η`. -/
theorem sample_norm_le {Y : Type*} (D : Data Y n Z s) (η : ℝ) (hη : 0 < η) (y : Y)
    (hH : (D.matrix y).IsHermitian)
    (hrow : ∀ i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2) :
    ‖SparseStateOverlap.matrixOperator (D.matrix y)‖ ≤ Real.sqrt s * η := by
  have h := matrixOperator_norm_le_sqrt (NativeSparseRescaling.normalize D η hη) y
    (NativeSparseRescaling.normalize_hermitian D η hη y hH)
    (fun i => NativeSparseRescaling.normalized_row_energy D η hη y i (hrow i))
    (fun j => NativeSparseRescaling.normalized_column_energy D η hη y j (hcol j))
  rw [NativeSparseRescaling.matrixOperator_normalize, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr hη.le), inv_mul_le_iff₀ hη] at h
  linarith

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The slot product of the normalised samples is the refined product of the physical samples
with step `T / N`. -/
theorem sampledEvolution_normalize (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ)
    (N : ℕ) (η T : ℝ) (hη : 0 < η) (x : X) :
    Refined.sampledEvolution (NativeSparseRescaling.normalize D η hη) (pieceOf t T N hM) N
        (η * T) x =
      refinedEvolution (fun r => SparseStateOverlap.matrixOperator
        (D.matrix (x, Sampled.sampleIndex hM r))) t T N M := by
  unfold Refined.sampledEvolution refinedEvolution
  congr 1
  funext k
  have hk : Sampled.sampleIndex hM (slotPiece t T N M k) = pieceOf t T N hM k :=
    sampleIndex_of_lt hM (slotPiece_lt hM k)
  simp only [hk]
  rw [NativeSparseRescaling.matrixOperator_normalize, smul_smul]
  congr 2
  have hηC : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  push_cast
  field_simp

set_option maxRecDepth 8192 in
/-- **Theorem `hs:thm:time` on general meshes, with breakpoints and integrated
certificates.** For any mesh `0 = t_0 ≤ ⋯ ≤ t_M = T` and any slot count `N` with
`4 s η T ≤ N`, `9 (√s η T)³ ≤ ε N²` and `9 M √s η T ≤ ε N`, one oracle program, uniform over
the unknown instance and unitary on every instance, and one clean encoding built from public
data satisfy `‖𝒜 ι - ι U(T)‖ ≤ ε` for every instance `x`, every path with one Hermitian,
interval-integrable piece `H_r` per mesh interval whose integrated sample errors
`∑_r ∫_{t_r}^{t_{r+1}} ‖H_r(u) - H̃_r‖ du` are at most `ε / 9`, and every propagator of that
path (one-sided derivatives at the breakpoints). The query count is that of
`TimeDependent.simulation`. -/
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
      ∃ p : MultiOracleCircuit.Program (oracle D N γ η T ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * T) +
            Real.sqrt ((s : ℝ) * (η * T) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (input D hM t N γ η T ε)† ∘L input D hM t N γ η T ε = 1 ∧
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
            ‖p.eval x ∘L input D hM t N γ η T ε - input D hM t N γ η T ε ∘L U T‖ ≤ ε := by
  have hs : (1 : ℝ) ≤ s := by exact_mod_cast D.slots_pos
  have hτ : 0 ≤ η * T := mul_nonneg hη.le hT.le
  have hεOne : ε ≤ 1 := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨γ, hγ, hγOne, hWidth, hBudget⟩ :=
    ImprovedPrecisionBudget.exists_rescaling_for_precision (s : ℝ) (η * T) ε hs hτ hε hεOne
  have hStep := TimeDependent.step_le_quarter (s := s) (M := N) γ (η * T) hs hγ hWidth hτ hN
    hClock
  obtain ⟨p, hCount, hIn, hOut, hAct⟩ := Refined.exists_sampled_simulation
    (NativeSparseRescaling.normalize D η hη) hM (pieceOf t T N hM) hN
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
  · intro Hp U hPath hInt hCert hU0 hU
    have hErr := (hAct x).2
    rw [sampledEvolution_normalize D hM t N η T hη x] at hErr
    let A : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
      SparseStateOverlap.matrixOperator (D.matrix (x, Sampled.sampleIndex hM r))
    let Hq : ℕ → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r u =>
      SparseStateOverlap.matrixOperator (Hp (Sampled.sampleIndex hM r) u)
    have hPw : IsPiecewisePropagator Hq t M U := by
      refine ⟨hU0, fun r hr => ?_⟩
      have h := hU ⟨r, hr⟩
      simp only [Hq, sampleIndex_of_lt hM hr]
      exact h
    have hHq : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), star (Hq r u) = Hq r u := by
      intro r hr u hu
      simp only [Hq, sampleIndex_of_lt hM hr]
      exact SparseValuePrecision.matrixOperator_star_eq _ (hPath ⟨r, hr⟩ u hu)
    have hA : ∀ r, star (A r) = A r := fun r =>
      SparseValuePrecision.matrixOperator_star_eq _ (hH _)
    have hΛ : ∀ r, ‖A r‖ ≤ Real.sqrt s * η := fun r =>
      sample_norm_le D η hη _ (hH _) (hrow _) (hcol _)
    have hIntq : ∀ r < M, IntervalIntegrable (Hq r) volume (t r) (t (r + 1)) := by
      intro r hr
      simp only [Hq, sampleIndex_of_lt hM hr]
      exact hInt ⟨r, hr⟩
    have hRef := refined_error A hmesh hT hN hPw hHq hA hΛ hIntq
    have hCertR : ∑ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖Hq r u - A r‖ ≤ ε / 9 := by
      rw [← Fin.sum_univ_eq_sum_range (fun r => ∫ u in t r..t (r + 1), ‖Hq r u - A r‖) M]
      simpa only [Hq, A, sampleIndex_val] using hCert
    let D' := NativeSparseRescaling.normalize D η hη
    let σ := pieceOf t T N hM
    have hOutNorm : ‖Refined.output D' hM σ N γ (η * T) ε‖ ≤ 1 := by
      apply opNorm_le_bound _ zero_le_one
      intro v
      rw [((Refined.output D' hM σ N γ (η * T) ε).norm_map_iff_adjoint_comp_self.mpr hOut) v,
        one_mul]
    let S := refinedEvolution A t T N M
    have hAligned := AlignedMultiOracleProgram.program_error _ _ hIn hOut p x (U T)
    change ‖q.eval x ∘L input D hM t N γ η T ε - input D hM t N γ η T ε ∘L U T‖ ≤ ε
    rw [show input D hM t N γ η T ε = AlignedMultiOracleProgram.input
      (Refined.input D' hM σ N γ (η * T) ε) from rfl, hAligned]
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
      _ ≤ ‖p.eval x ∘L Refined.input D' hM σ N γ (η * T) ε -
            Refined.output D' hM σ N γ (η * T) ε ∘L S‖ +
          ‖Refined.output D' hM σ N γ (η * T) ε ∘L S -
            Refined.output D' hM σ N γ (η * T) ε ∘L U T‖ :=
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

end Hamiltonian

end TimeDependentExtensions
