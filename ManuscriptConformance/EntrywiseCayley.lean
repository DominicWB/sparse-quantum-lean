import SparseHamiltonian.NativeCayleyProgram
import SparseHamiltonian.FixedNativeCayleySimulation
import SparseHamiltonian.SparseSpectralEnergy
import GateEfficientBinary.Sparse.Simulation
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Conformance: the sparse Cayley representation (Lemma `qls:lem:entry`)

Lemma `qls:lem:entry` for a general Hermitian `s`-sparse `H` with `‖H‖ ≤ 1`, bundled from the
arbitrary-`H` constructions of `SparseHamiltonian.FixedNativeCayleySimulation` (the edge-space
isometry and generator, conjugated by the actual locator unitary) and
`SparseHamiltonian.NativeCayleyProgram` (the eighteen-query native circuit).

* **Input.** Native sparse data `D` (value oracle and in-place row and column locators, inverses
  included, `s ≥ 1` slots; the locators list the support of every row and column of
  `H = D.matrix x`, padded to `s` entries).
* **Isometry.** `J` (`FixedNativeCayleySimulation.boundary D`) depends only on the public slot
  data: it is one operator for the whole oracle family and is implemented without matrix queries.
* **Generator.** `K` (`FixedNativeCayleySimulation.generator D x`) is self-adjoint for every
  input. For Hermitian `H` with `‖H‖ ≤ 1` (the spectral bound; the row and column energies
  `∑_j |H_ij|² ≤ 1`, `∑_i |H_ij|² ≤ 1` are derived from it, `energies_of_norm_le_one`):
  `J† K J = H/√s`, `J† K² J ≤ 1` in the Loewner order (`moment_le_one_of_norm`, from
  `‖K J‖ ≤ 1`), and `‖K‖ ≤ √s`, equation `qls:eq:moments`.
* **Cayley unitary.** For every real `γ` (the Cayley transform of the known scalar multiple
  `γK`), the private operation `FixedNativeCayleySimulation.action D x γ` is
  `(γK + i)(γK - i)⁻¹`, with an explicit two-sided inverse of `γK - i` (equation
  `qls:eq:cayley`), and it is unitary; no promise on `H` is needed for this part.
* **Circuit and counts.** `NativeCayleyProgram.program D γ` acts as this unitary on the fixed
  clean encoding of the private space, and its literal adjoint program as the inverse
  (`adjoint_program_intertwines`); both make `6` row-locator, `6` column-locator and `6` value
  calls (`18` in total), for every `γ` and every input.

The walk of the linear-system algorithm applies this lemma to the lift `H₀` of the augmented
operator (`SparseLinearSystems.SparseBranch.branchProps`).
-/

set_option autoImplicit false

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian OracleCircuit CayleyClockInterface
open scoped InnerProduct

/-- `J† K² J ≤ 1` in the Loewner order whenever `K` is self-adjoint and `‖K J‖ ≤ 1`. -/
theorem moment_le_one_of_norm {P V : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [CompleteSpace P] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (K : V →L[ℂ] V) (hK : star K = K) (J : P →L[ℂ] V) (h : ‖K ∘L J‖ ≤ 1) :
    J† ∘L (K ∘L K) ∘L J ≤ 1 := by
  have hsa : J† ∘L (K ∘L K) ∘L J = (K ∘L J)† ∘L (K ∘L J) := by
    rw [adjoint_comp, ← star_eq_adjoint K, hK]
    simp only [comp_assoc]
  rw [hsa, ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_def']
  refine ⟨(IsSelfAdjoint.one _).sub
    (ContinuousLinearMap.isPositive_adjoint_comp_self (K ∘L J)).isSelfAdjoint, fun v => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, sub_apply, one_apply_eq_self, comp_apply,
    inner_sub_left, map_sub, adjoint_inner_left, inner_self_eq_norm_sq, inner_self_eq_norm_sq]
  have h1 : ‖(K ∘L J) v‖ ≤ ‖v‖ :=
    ((K ∘L J).le_opNorm v).trans (by nlinarith [norm_nonneg v])
  have h2 := norm_nonneg ((K ∘L J) v)
  nlinarith

/-- The row and column energies from the spectral bound `‖H‖ ≤ 1` of a Hermitian `H`. -/
theorem energies_of_norm_le_one {n : Type*} [Fintype n] (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (hN : ‖SparseStateOverlap.matrixOperator H‖ ≤ 1) :
    (∀ i, ∑ j, ‖H i j‖ ^ 2 ≤ 1) ∧ (∀ j, ∑ i, ‖H i j‖ ^ 2 ≤ 1) := by
  obtain ⟨hr, hc⟩ := SparseSpectralEnergy.energies_of_spectral_bound H hH 1 hN
  exact ⟨fun i => by simpa using hr i, fun j => by simpa using hc j⟩

/-- A unitary program that intertwines an isometric encoding with a unitary operation also
intertwines it, through its adjoint, with the inverse operation. -/
theorem adjoint_program_intertwines {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (U : F →L[ℂ] F) (C : E →L[ℂ] F) (A : E →L[ℂ] E) (hU : IsUnitary U) (hA : IsUnitary A)
    (h : U ∘L C = C ∘L A) : star U ∘L C = C ∘L star A := by
  have e1 : C = C ∘L (A ∘L star A) := by
    rw [← mul_def, hA.2]
    exact (comp_id C).symm
  have e2 : (star U ∘L U) ∘L (C ∘L star A) = C ∘L star A := by
    rw [← mul_def, hU.1]
    exact id_comp _
  calc star U ∘L C = star U ∘L (C ∘L (A ∘L star A)) := by rw [← e1]
    _ = star U ∘L ((U ∘L C) ∘L star A) := by rw [h, comp_assoc]
    _ = (star U ∘L U) ∘L (C ∘L star A) := by simp only [comp_assoc]
    _ = C ∘L star A := e2

/-- **Lemma `qls:lem:entry`** (equations `qls:eq:moments`, `qls:eq:cayley`). For native sparse
data `D`: the fixed isometry `J` (no matrix query, one operator for every input) and the fixed
clean encoding of the private space; for every real `γ`, the native program and its literal
adjoint make `6` calls of each sparse primitive; and on every input `x`: the program implements
the Cayley unitary `(γK + i)(γK - i)⁻¹` of the self-adjoint generator `K` and its adjoint
program the inverse, with an explicit two-sided inverse of `γK - i`; if `H = D.matrix x` is
Hermitian with `‖H‖ ≤ 1`, then `J† K J = H/√s`, `J† K² J ≤ 1`, `‖K J‖ ≤ 1` and `‖K‖ ≤ √s`.
Formal restrictions: none. -/
theorem qls_lem_entry {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
    [DecidableEq Z] {s : ℕ} (D : NativeSparseBlockEncoding.Data X n Z s) :
    (FixedNativeCayleySimulation.boundary D)† ∘L FixedNativeCayleySimulation.boundary D = 1 ∧
      (NativeCayleyProgram.clean D).toContinuousLinearMap† ∘L
          (NativeCayleyProgram.clean D).toContinuousLinearMap = 1 ∧
      ∀ γ : ℝ,
        (NativeCayleyProgram.program D γ).labelCount .rowLocation = 6 ∧
        (NativeCayleyProgram.program D γ).labelCount .columnLocation = 6 ∧
        (NativeCayleyProgram.program D γ).labelCount .value = 6 ∧
        (NativeCayleyProgram.program D γ).adjoint.labelCount .rowLocation = 6 ∧
        (NativeCayleyProgram.program D γ).adjoint.labelCount .columnLocation = 6 ∧
        (NativeCayleyProgram.program D γ).adjoint.labelCount .value = 6 ∧
        (NativeCayleyProgram.program D γ).count = 18 ∧
        (NativeCayleyProgram.program D γ).adjoint.count = 18 ∧
        ∀ x : X,
          star (FixedNativeCayleySimulation.generator D x) =
              FixedNativeCayleySimulation.generator D x ∧
            (scaled (FixedNativeCayleySimulation.generator D x) γ - Complex.I • 1) *
                FixedNativeCayleySimulation.inverse D x γ = 1 ∧
            FixedNativeCayleySimulation.inverse D x γ *
                (scaled (FixedNativeCayleySimulation.generator D x) γ - Complex.I • 1) = 1 ∧
            FixedNativeCayleySimulation.action D x γ =
              ImprovedCayleyMoments.cayleyAction
                (scaled (FixedNativeCayleySimulation.generator D x) γ)
                (FixedNativeCayleySimulation.inverse D x γ) ∧
            IsUnitary (FixedNativeCayleySimulation.action D x γ) ∧
            (NativeCayleyProgram.program D γ).eval x ∘L
                (NativeCayleyProgram.clean D).toContinuousLinearMap =
              (NativeCayleyProgram.clean D).toContinuousLinearMap ∘L
                FixedNativeCayleySimulation.action D x γ ∧
            (NativeCayleyProgram.program D γ).adjoint.eval x ∘L
                (NativeCayleyProgram.clean D).toContinuousLinearMap =
              (NativeCayleyProgram.clean D).toContinuousLinearMap ∘L
                star (FixedNativeCayleySimulation.action D x γ) ∧
            ((D.matrix x).IsHermitian →
              ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1 →
              (FixedNativeCayleySimulation.boundary D)† ∘L
                    FixedNativeCayleySimulation.generator D x ∘L
                    FixedNativeCayleySimulation.boundary D =
                  (Real.sqrt (s : ℝ) : ℂ)⁻¹ • SparseStateOverlap.matrixOperator (D.matrix x) ∧
                (FixedNativeCayleySimulation.boundary D)† ∘L
                    (FixedNativeCayleySimulation.generator D x ∘L
                      FixedNativeCayleySimulation.generator D x) ∘L
                    FixedNativeCayleySimulation.boundary D ≤ 1 ∧
                ‖FixedNativeCayleySimulation.generator D x ∘L
                    FixedNativeCayleySimulation.boundary D‖ ≤ 1 ∧
                ‖FixedNativeCayleySimulation.generator D x‖ ≤ Real.sqrt (s : ℝ)) := by
  refine ⟨FixedNativeCayleySimulation.boundary_isometry D, NativeCayleyProgram.clean_isometry D,
    fun γ => ⟨NativeCayleyProgram.program_row_count D γ,
      NativeCayleyProgram.program_column_count D γ, NativeCayleyProgram.program_value_count D γ,
      by rw [MultiOracleCircuit.Program.labelCount_adjoint,
        NativeCayleyProgram.program_row_count],
      by rw [MultiOracleCircuit.Program.labelCount_adjoint,
        NativeCayleyProgram.program_column_count],
      by rw [MultiOracleCircuit.Program.labelCount_adjoint,
        NativeCayleyProgram.program_value_count],
      NativeCayleyProgram.program_count D γ,
      by rw [MultiOracleCircuit.Program.count_adjoint, NativeCayleyProgram.program_count],
      fun x => ?_⟩⟩
  have hA := GateBinary.fixedAction_isUnitary D x γ
  have hI := NativeCayleyProgram.program_intertwines D γ x
  refine ⟨FixedNativeCayleySimulation.generator_self_adjoint D x,
    FixedNativeCayleySimulation.inverse_right D x γ,
    FixedNativeCayleySimulation.inverse_left D x γ,
    FixedNativeCayleySimulation.action_eq_cayley D x γ, hA, hI, ?_, fun hH hN => ?_⟩
  · rw [MultiOracleCircuit.Program.eval_adjoint]
    exact adjoint_program_intertwines _ _ _ (NativeCayleyProgram.program_unitary D γ x) hA hI
  · obtain ⟨hrow, hcol⟩ := energies_of_norm_le_one (D.matrix x) hH hN
    have hKJ := FixedNativeCayleySimulation.generator_boundary_norm_le D x hrow hcol
    exact ⟨FixedNativeCayleySimulation.compression D x hH,
      moment_le_one_of_norm _ (FixedNativeCayleySimulation.generator_self_adjoint D x) _ hKJ,
      hKJ, FixedNativeCayleySimulation.generator_norm_le D x hrow⟩

end

end ManuscriptConformance
