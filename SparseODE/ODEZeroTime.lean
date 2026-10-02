import SparseODE.ODEZeroEnergy

/-!
# Exact zero-time ODE preparation

A zero horizon needs only the supplied initial-state oracle.  The counted
circuit is one initial-source query, with no matrix or forcing calls.  Its
clean output encoding is the identity, so the herald succeeds with certainty.
This is an actual circuit on the source workspace, and its certificate uses
the same TrialCertificate interface as the positive-time algorithm.

-/

namespace SparseHamiltonian.ODEZeroTime

noncomputable section
open ContinuousLinearMap OracleCircuit ODEStateNormalization
open scoped BigOperators InnerProduct

variable {P X L : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The two supplied source interfaces on their original state workspace. -/
def sourceFamily (J₀ Jb : X → P →L[ℂ] P) : Bool → X → P →L[ℂ] P
  | false => J₀
  | true => Jb

/-- A single initial-source query, with the existing matrix/source labels. -/
def program (O : L → X → P →L[ℂ] P) (J₀ Jb : X → P →L[ℂ] P) :
    MultiOracleCircuit.Program (ODESourceQueryBudget.oracle O (sourceFamily J₀ Jb)) :=
  .query (Sum.inr false)

@[simp] theorem program_eval (O : L → X → P →L[ℂ] P)
    (J₀ Jb : X → P →L[ℂ] P) (x : X) :
    (program O J₀ Jb).eval x = J₀ x := rfl

/-- Unused matrix and forcing interfaces impose no extra unitary premise. -/
theorem program_unitary (O : L → X → P →L[ℂ] P)
    (J₀ Jb : X → P →L[ℂ] P) (hJ₀ : ∀ x, IsUnitary (J₀ x)) :
    ∀ x, IsUnitary ((program O J₀ Jb).eval x) := hJ₀

/-- Exact costs in the already established disjoint-label query model. -/
theorem program_costs (O : L → X → P →L[ℂ] P)
    (J₀ Jb : X → P →L[ℂ] P) :
    (program O J₀ Jb).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = 0 ∧
    (program O J₀ Jb).cost (ODESourceQueryBudget.sourceWeight false) = 1 ∧
    (program O J₀ Jb).cost (ODESourceQueryBudget.sourceWeight true) = 0 ∧
    (program O J₀ Jb).cost ODESourceQueryBudget.sourceTotalWeight = 1 ∧
    (program O J₀ Jb).count = 1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Identity output coordinates keep the complete physical vector. -/
theorem successProjector_one :
    ODEHeraldedSuccess.successProjector (1 : P →L[ℂ] P) = 1 := by
  exact (isUnitary_one (K := P)).2

/-- The one-query circuit has deterministic heralded success. -/
theorem success_probability (O : L → X → P →L[ℂ] P)
    (J₀ Jb : X → P →L[ℂ] P) (hJ₀ : ∀ x, IsUnitary (J₀ x))
    (seed : P) (hSeed : ‖seed‖ = 1) (x : X) :
    ODEHeraldedSuccess.successProbability (1 : P →L[ℂ] P)
      ((program O J₀ Jb).eval x) seed = 1 := by
  have hNorm : ‖(J₀ x) seed‖ = 1 := by
    rw [(J₀ x).norm_map_iff_adjoint_comp_self.mpr (hJ₀ x).1, hSeed]
  rw [ODEHeraldedSuccess.successProbability,
    ODEHeraldedSuccess.successfulComponent, successProjector_one, program_eval]
  simp only [one_def, id_apply, hNorm, one_pow]

omit [CompleteSpace P] in
/-- Normalizing an already normalized nonzero target has no effect. -/
theorem unitDirection_idempotent (v : P) (hv : v ≠ 0) :
    unitDirection (unitDirection v) = unitDirection v := by
  change ‖unitDirection v‖⁻¹ • unitDirection v = unitDirection v
  rw [unitDirection_norm v hv, inv_one, one_smul]

/-- A deterministic single-query family satisfies the common trial interface.
The target is prepared exactly; the public error parameter may be zero. -/
theorem source_trial_certificate (O : L → X → P →L[ℂ] P)
    (J₀ Jb : X → P →L[ℂ] P) (hJ₀ : ∀ x, IsUnitary (J₀ x))
    (seed : P) (hSeed : ‖seed‖ = 1) (x : X) (v : P) (hv : v ≠ 0)
    (hPrepare : J₀ x seed = unitDirection v)
    (s Θ ell g η : ℝ) (hΘ : 0 ≤ Θ) (hell : 0 ≤ ell)
    (hg : 1 ≤ g) (hη : 0 ≤ η) :
    ODEPrimitiveSourceJoin.TrialCertificate
      (fun _ : ℕ => program O J₀ Jb) 1 seed (1 : P →L[ℂ] P)
      x v s Θ ell g η := by
  have hShape := ImprovedODEQueryBudget.queryShape_nonneg s Θ ell hΘ hell
  have hCosts := program_costs O J₀ Jb
  have hDecoded :
      ((1 : P →L[ℂ] P)†) ((program O J₀ Jb).eval x seed) = unitDirection v := by
    rw [adjoint_one, program_eval]
    simpa only [one_def, id_apply] using hPrepare
  have hProbability :
      ‖ODEHeraldedSuccess.successProjector (1 : P →L[ℂ] P)
        ((program O J₀ Jb).eval x seed)‖ ^ 2 = 1 :=
    success_probability O J₀ Jb hJ₀ seed hSeed x
  refine {
    cutoff_pos := by norm_num
    cutoff_le := by norm_num only [Nat.cast_one]; linarith
    seed_unit := hSeed
    output_isometry := ?_
    matrix_queries := ?_
    source_queries := ?_
    total_source_queries := ?_
    mean_success := ?_
    direction_error := ?_ }
  · exact (isUnitary_one (K := P)).1
  · intro j hj
    rw [hCosts.1, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hShape
  · intro j hj b
    cases b with
    | false =>
      rw [hCosts.2.1, Nat.cast_one]
      linarith
    | true =>
      rw [hCosts.2.2.1, Nat.cast_zero]
      linarith
  · intro j hj
    rw [hCosts.2.2.2.1, Nat.cast_one]
    linarith
  · simpa only [Finset.sum_range_one, hProbability, Nat.cast_one, div_one]
      using (by norm_num : (1 : ℝ) / 4 ≤ 1)
  · intro j hj hNonzero
    refine ⟨1, by simp, ?_⟩
    rw [hDecoded, unitDirection_idempotent v hv, one_smul, sub_self, norm_zero]
    exact hη

/-- At time zero the actual constant-forcing ODE target is exactly the initial
vector, independently of the generator and the forcing vector. -/
theorem zero_time_trial_certificate (O : L → X → P →L[ℂ] P)
    (J₀ Jb : X → P →L[ℂ] P) (hJ₀ : ∀ x, IsUnitary (J₀ x))
    (A : P →L[ℂ] P) (v b seed : P) (hSeed : ‖seed‖ = 1) (x : X)
    (hTarget : ODEConstantForcing.solution A v b 0 ≠ 0)
    (hPrepare : v ≠ 0 → J₀ x seed = unitDirection v)
    (s ell g η : ℝ) (hell : 0 ≤ ell) (hg : 1 ≤ g) (hη : 0 ≤ η) :
    (∀ y, IsUnitary ((program O J₀ Jb).eval y)) ∧
    ODEHeraldedSuccess.successProbability (1 : P →L[ℂ] P)
      ((program O J₀ Jb).eval x) seed = 1 ∧
    ODEPrimitiveSourceJoin.TrialCertificate
      (fun _ : ℕ => program O J₀ Jb) 1 seed (1 : P →L[ℂ] P)
      x (ODEConstantForcing.solution A v b 0) s 0 ell g η := by
  have hv : v ≠ 0 := by simpa only [ODEConstantForcing.solution_zero] using hTarget
  refine ⟨program_unitary O J₀ Jb hJ₀,
    success_probability O J₀ Jb hJ₀ seed hSeed x, ?_⟩
  simpa only [ODEConstantForcing.solution_zero] using
    source_trial_certificate O J₀ Jb hJ₀ seed hSeed x v hv (hPrepare hv)
      s 0 ell g η (by norm_num) hell hg hη

end
end SparseHamiltonian.ODEZeroTime
