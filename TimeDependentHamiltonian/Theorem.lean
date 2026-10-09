import TimeDependentHamiltonian.Native.Simulation
import TimeDependentHamiltonian.Continuous.Propagator
import SparseHamiltonian.ManuscriptPrecision

/-!
# Time-dependent sparse Hamiltonian simulation (`hs:thm:time`)

The coherent sampled-time oracles supply, for each unknown instance `x` and
each sampled time `r < M`, the represented sample `H̃_r = D.matrix (x, r)`
through the released native locator and value queries extended by a time
register (`Sampled.oracle`). For a Hermitian path `H(u)` with operator-norm
Lipschitz bound `β` and sample errors `‖H(r t / M) - H̃_r‖ ≤ δ`, one actual
unitary oracle program and one fixed clean encoding satisfy

  `‖𝒜 ι - ι U_H(t, 0)‖ ≤ ε`

for every propagator `U_H(·, 0)` of the path, with at most

  `995328 (√s τ + √(s τ log(1/ε)) + log(1/ε))`,  `τ = η t`,

coherent sampled-time queries, including inverse calls
(`simulation`). Neither the mesh size `M` nor `β` multiplies the query count;
the mesh conditions only concern the classical discretisation.
-/

namespace SparseHamiltonian.TimeDependent

noncomputable section

open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding CayleyClockInterface
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- The complete physical workspace, including the one alignment spectator. -/
abbrev Workspace (n Z : Type*) [Fintype n] [Fintype Z] (s M : ℕ) (γ η t ε : ℝ) :=
  CleanOutputAlignment.Double
    (Sampled.Physical n Z M M (Sampled.degree (s : ℝ) γ (η * t) ε M))

/-- Each query is one coherent sampled-time native primitive with untouched
spectator registers. -/
abbrev oracle (D : Data (X × Fin M) n Z s) (γ η t ε : ℝ) :
    Query → X → Workspace n Z s M γ η t ε →L[ℂ] Workspace n Z s M γ η t ε :=
  AlignedMultiOracleProgram.oracle (Sampled.oracle D M (Sampled.degree (s : ℝ) γ (η * t) ε M))

omit [DecidableEq Z] in
theorem oracle_unitary (D : Data (X × Fin M) n Z s) (γ η t ε : ℝ) (l : Query) (x : X) :
    IsUnitary (oracle D γ η t ε l x) :=
  CoherentQuerySchedule.oracle_unitary _ (Sampled.oracle_unitary D M _) l x

/-- The same known clean preparation occurs at both ends of the circuit. It
depends only on public data: slot embedding, mesh, rescaling and precision. -/
def input (D : Data (X × Fin M) n Z s) (hM : 0 < M) (γ η t ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] Workspace n Z s M γ η t ε :=
  AlignedMultiOracleProgram.input (Sampled.input D hM γ (η * t) ε)

/-- The rescaled step obeys the clock condition `w ≤ 1/4` under the public
mesh condition `4 s η t ≤ M`. -/
theorem step_le_quarter (γ τ : ℝ) (hs : (1 : ℝ) ≤ s) (hγ : 0 < γ)
    (hWidth : 1 ≤ γ * Real.sqrt s) (hτ : 0 ≤ τ) (hM : 0 < M) (hMesh : 4 * s * τ ≤ M) :
    Sampled.step (s : ℝ) γ τ M ≤ 1 / 4 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hsR : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt (by linarith)
  have hratio : Real.sqrt s / γ ≤ s := by
    rw [div_le_iff₀ hγ]
    nlinarith
  have htime : time (s : ℝ) τ γ ≤ s * τ := by
    unfold time
    rw [mul_div_assoc]
    calc
      τ * (Real.sqrt s / γ) ≤ τ * s := mul_le_mul_of_nonneg_left hratio hτ
      _ = s * τ := by ring
  unfold Sampled.step
  rw [div_le_iff₀ hMR]
  linarith

/-- The explicit query count, before conversion to the manuscript logarithm. -/
theorem count_le_shape (γ τ ε : ℝ) (hγ : 0 < γ)
    (hτ : 0 ≤ τ) (hε : 0 < ε) (hεOne : ε ≤ 1) (hM : 0 < M)
    (hBudget : τ * Real.sqrt s / γ * ((1 + γ ^ 2) / 2) +
      (⌈max 1 (γ * Real.sqrt s)⌉₊ : ℝ) * ImprovedPrecisionBudget.circuitLog ε ≤
        12 * ImprovedPrecisionBudget.shape s τ (ImprovedPrecisionBudget.targetLog ε))
    (q : ℕ) (hq : q ≤ 6 * Sampled.degree (s : ℝ) γ τ ε M * 54) :
    (q : ℝ) ≤ 497664 * ImprovedPrecisionBudget.shape s τ (ImprovedPrecisionBudget.targetLog ε) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hW : (M : ℝ) * Sampled.step (s : ℝ) γ τ M * moment γ = time (s : ℝ) τ γ * moment γ := by
    unfold Sampled.step
    field_simp
  have htime : 0 ≤ time (s : ℝ) τ γ := div_nonneg (mul_nonneg hτ (Real.sqrt_nonneg _)) hγ.le
  have hdeg0 := SharpFilterSchedule.degree_le (width (s : ℝ) γ)
    ((M : ℝ) * Sampled.step (s : ℝ) γ τ M * moment γ) (ε / 3) (width_ge_one _ _)
    (by rw [hW]; exact mul_nonneg htime (moment_nonneg γ)) (by positivity) (by linarith)
  have hlog : 1 + SharpFilterSchedule.logBudget (ε / 3) = ImprovedPrecisionBudget.circuitLog ε := by
    unfold SharpFilterSchedule.logBudget ImprovedPrecisionBudget.circuitLog
    congr 2
    field_simp
  have hdeg : (Sampled.degree (s : ℝ) γ τ ε M : ℝ) ≤ 128 * (time (s : ℝ) τ γ * moment γ +
      width (s : ℝ) γ * ImprovedPrecisionBudget.circuitLog ε) := by
    have h := hdeg0
    rw [hlog] at h
    calc
      (Sampled.degree (s : ℝ) γ τ ε M : ℝ) ≤ 128 * ((M : ℝ) * Sampled.step (s : ℝ) γ τ M *
          moment γ + width (s : ℝ) γ * ImprovedPrecisionBudget.circuitLog ε) := h
      _ = _ := by rw [hW]
  have hBudget' : time (s : ℝ) τ γ * moment γ +
      width (s : ℝ) γ * ImprovedPrecisionBudget.circuitLog ε ≤
        12 * ImprovedPrecisionBudget.shape s τ (ImprovedPrecisionBudget.targetLog ε) := hBudget
  have hqR : (q : ℝ) ≤ 6 * (Sampled.degree (s : ℝ) γ τ ε M : ℝ) * 54 := by exact_mod_cast hq
  calc
    (q : ℝ) ≤ 6 * (Sampled.degree (s : ℝ) γ τ ε M : ℝ) * 54 := hqR
    _ ≤ 6 * (128 * (time (s : ℝ) τ γ * moment γ +
        width (s : ℝ) γ * ImprovedPrecisionBudget.circuitLog ε)) * 54 := by
      nlinarith
    _ ≤ 6 * (128 * (12 * ImprovedPrecisionBudget.shape s τ
        (ImprovedPrecisionBudget.targetLog ε))) * 54 := by nlinarith
    _ = 497664 * ImprovedPrecisionBudget.shape s τ (ImprovedPrecisionBudget.targetLog ε) := by
      ring

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The ordered product of the normalized sampled exponentials is the ordered
product of the physical sampled exponentials with step `t / M`. -/
theorem sampledEvolution_normalize (D : Data (X × Fin M) n Z s) (hM : 0 < M) (η t : ℝ)
    (hη : 0 < η) (x : X) :
    Sampled.sampledEvolution (NativeSparseRescaling.normalize D η hη) hM (η * t) x =
      evolution (fun k => NormedSpace.exp ((-Complex.I * ((t / M : ℝ) : ℂ)) •
        SparseStateOverlap.matrixOperator (D.matrix (x, Sampled.sampleIndex hM k)))) M := by
  unfold Sampled.sampledEvolution
  congr 1
  funext k
  rw [NativeSparseRescaling.matrixOperator_normalize, smul_smul]
  congr 2
  have hηC : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  push_cast
  field_simp

set_option maxRecDepth 8192 in
/-- **Theorem `hs:thm:time`.** Time-dependent sparse Hamiltonian simulation
with coherent sampled-time access on a uniform mesh of `M` intervals. One
input-independent unitary oracle program and one fixed clean encoding serve
every instance; the error bound holds for every propagator of the intended
path and includes all work registers. -/
theorem simulation (D : Data (X × Fin M) n Z s) (Hpath : X → ℝ → Matrix n n ℂ)
    (η t β δ ε : ℝ) (hη : 0 < η) (ht : 0 ≤ t) (hβ : 0 ≤ β) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2) (hM : 0 < M)
    (hMesh : 4 * s * (η * t) ≤ M) (hFreeze : 9 * β * t ^ 2 ≤ ε * M)
    (hCayley : 9 * (Real.sqrt s * (η * t)) ^ 3 ≤ ε * (M : ℝ) ^ 2)
    (hH : ∀ y, (D.matrix y).IsHermitian)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hPath : ∀ x, ∀ u ∈ Set.Icc 0 t, (Hpath x u).IsHermitian)
    (hLip : ∀ x, ∀ u ∈ Set.Icc 0 t, ∀ v ∈ Set.Icc 0 t,
      ‖SparseStateOverlap.matrixOperator (Hpath x u) -
        SparseStateOverlap.matrixOperator (Hpath x v)‖ ≤ β * |u - v|)
    (hVal : ∀ x (r : Fin M), ‖SparseStateOverlap.matrixOperator (Hpath x (r * t / M)) -
      SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δ)
    (hValBudget : t * δ ≤ ε / 12) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program (oracle D γ η t ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * t) +
            Real.sqrt ((s : ℝ) * (η * t) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (input D hM γ η t ε)† ∘L input D hM γ η t ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n), U 0 = 1 →
            SolvesOn (fun u => SparseStateOverlap.matrixOperator (Hpath x u)) U 0 t →
            ‖p.eval x ∘L input D hM γ η t ε - input D hM γ η t ε ∘L U t‖ ≤ ε := by
  have hs : (1 : ℝ) ≤ s := by exact_mod_cast D.slots_pos
  have hτ : 0 ≤ η * t := mul_nonneg hη.le ht
  have hεOne : ε ≤ 1 := by linarith
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨γ, hγ, hγOne, hWidth, hBudget⟩ :=
    ImprovedPrecisionBudget.exists_rescaling_for_precision (s : ℝ) (η * t) ε hs hτ hε hεOne
  have hStep := step_le_quarter (s := s) γ (η * t) hs hγ hWidth hτ hM hMesh
  obtain ⟨p, hCount, hIn, hOut, hAct⟩ := Sampled.exists_sampled_simulation
    (NativeSparseRescaling.normalize D η hη) hM
    (fun y => NativeSparseRescaling.normalize_hermitian D η hη y (hH y))
    (fun y i => NativeSparseRescaling.normalized_row_energy D η hη y i (hrow y i))
    (fun y j => NativeSparseRescaling.normalized_column_energy D η hη y j (hcol y j))
    γ (η * t) ε hγ hγOne hτ hε hεOne hStep
  let q := AlignedMultiOracleProgram.program _ _ hIn hOut p
  refine ⟨γ, hγ, hγOne, hWidth, q, ?_, ?_, fun x => ⟨?_, ?_⟩⟩
  · have hqc : q.count = p.count := AlignedMultiOracleProgram.program_count _ _ hIn hOut p
    calc
      (q.count : ℝ) = (p.count : ℝ) := by exact_mod_cast hqc
      _ ≤ _ := ManuscriptPrecision.query_count_log_one (p.count : ℝ) (s : ℝ) (η * t) ε
        (by linarith) hτ hε hεHalf
        (count_le_shape γ (η * t) ε hγ hτ hε hεOne hM hBudget p.count hCount)
  · exact AlignedMultiOracleProgram.input_isometry _ hIn
  · exact q.eval_unitary (CoherentQuerySchedule.oracle_unitary _
      (Sampled.oracle_unitary (NativeSparseRescaling.normalize D η hη) M _)) x
  · intro U hU0 hU
    have hErr := (hAct x).2
    rw [sampledEvolution_normalize D hM η t hη x] at hErr
    -- Discretisation of the intended path.
    have hMesh' := mesh_error (H := fun u => SparseStateOverlap.matrixOperator (Hpath x u))
      (U := U) (fun k => SparseStateOverlap.matrixOperator
        (D.matrix (x, Sampled.sampleIndex hM k))) hM ht hβ hU0 hU
      (fun u hu => SparseValuePrecision.matrixOperator_star_eq _ (hPath x u hu))
      (fun k => SparseValuePrecision.matrixOperator_star_eq _ (hH _))
      (hLip x)
      (fun k hk => by
        have h := hVal x ⟨k, hk⟩
        rw [show Sampled.sampleIndex hM k = ⟨k, hk⟩ from Fin.ext (Nat.mod_eq_of_lt hk)]
        simpa using h)
    have hOutNorm : ‖Sampled.output (NativeSparseRescaling.normalize D η hη) hM γ (η * t) ε‖ ≤ 1 := by
      apply opNorm_le_bound _ zero_le_one
      intro v
      rw [((Sampled.output (NativeSparseRescaling.normalize D η hη) hM γ (η * t)
        ε).norm_map_iff_adjoint_comp_self.mpr hOut) v, one_mul]
    let S := evolution (fun k => NormedSpace.exp ((-Complex.I * ((t / M : ℝ) : ℂ)) •
      SparseStateOverlap.matrixOperator (D.matrix (x, Sampled.sampleIndex hM k)))) M
    have hAligned := AlignedMultiOracleProgram.program_error _ _ hIn hOut p x (U t)
    change ‖q.eval x ∘L input D hM γ η t ε - input D hM γ η t ε ∘L U t‖ ≤ ε
    rw [show input D hM γ η t ε = AlignedMultiOracleProgram.input
      (Sampled.input (NativeSparseRescaling.normalize D η hη) hM γ (η * t) ε) from rfl,
      hAligned]
    have hCay : (M : ℝ) * (Real.sqrt s * (η * t) / M) ^ 3 ≤ ε / 9 := by
      have hMsq : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
      have heq : (M : ℝ) * (Real.sqrt s * (η * t) / M) ^ 3 =
          (Real.sqrt s * (η * t)) ^ 3 / (M : ℝ) ^ 2 := by
        field_simp
      rw [heq, div_le_iff₀ hMsq]
      linarith
    have hFr : β * t ^ 2 / M ≤ ε / 9 := by
      rw [div_le_iff₀ hMR]
      linarith
    calc
      _ ≤ ‖p.eval x ∘L Sampled.input (NativeSparseRescaling.normalize D η hη) hM γ (η * t) ε -
            Sampled.output (NativeSparseRescaling.normalize D η hη) hM γ (η * t) ε ∘L S‖ +
          ‖Sampled.output (NativeSparseRescaling.normalize D η hη) hM γ (η * t) ε ∘L S -
            Sampled.output (NativeSparseRescaling.normalize D η hη) hM γ (η * t) ε ∘L U t‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (2 * (ε / 3) + M * (Real.sqrt s * (η * t) / M) ^ 3) +
          1 * (β * t ^ 2 / M + t * δ) := by
        apply add_le_add hErr
        rw [← comp_sub]
        refine (opNorm_comp_le _ _).trans (mul_le_mul hOutNorm ?_ (norm_nonneg _) zero_le_one)
        rw [norm_sub_rev]
        exact hMesh'
      _ ≤ ε := by linarith

end

end SparseHamiltonian.TimeDependent
