import SparseODE.ODESourceCoefficients

/-!
# Norm-weighted source branches for constant forcing

The supplied source-preparation maps are used only on their specified seed.
Their isometry/unitarity properties belong to the actual preparation circuit;
this fragment proves the exact source normalization and target-vector algebra.
Branches of zero norm require no state-preparation promise.

-/

namespace SparseHamiltonian.ODESourceBranches

noncomputable section
open ContinuousLinearMap
open scoped BigOperators

variable {ι V : Type*} [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The sum of the norms of the unpropagated source vectors. -/
def mass (z : ι → V) : ℝ := ∑ a, ‖z a‖

/-- Classical probabilities used by the norm-weighted preparation. -/
def probability (z : ι → V) (a : ι) : ℝ := ‖z a‖ / mass z

omit [InnerProductSpace ℂ V] in
theorem mass_nonneg (z : ι → V) : 0 ≤ mass z :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

omit [InnerProductSpace ℂ V] in
theorem probability_nonneg (z : ι → V) (a : ι) :
    0 ≤ probability z a :=
  div_nonneg (norm_nonneg _) (mass_nonneg z)

omit [InnerProductSpace ℂ V] in
/-- Normalization is exact whenever the physical source budget is positive. -/
theorem sum_probability (z : ι → V) (hB : 0 < mass z) :
    ∑ a, probability z a = 1 := by
  unfold probability
  rw [← Finset.sum_div]
  change mass z / mass z = 1
  exact div_self (ne_of_gt hB)

omit [InnerProductSpace ℂ V] in
/-- Contractivity bounds for a nonzero solution give a positive source budget. -/
theorem mass_pos_of_solution (z : ι → V) (x : V) (hx : x ≠ 0)
    (hBound : ‖x‖ ≤ mass z) : 0 < mass z :=
  (norm_pos_iff.mpr hx).trans_le hBound

/-- Multiplying the total unit-direction definition by the original norm
recovers every vector, including the zero vector. -/
theorem norm_smul_unitDirection (v : V) :
    (‖v‖ : ℂ) • ODEStateNormalization.unitDirection v = v := by
  classical
  by_cases hv : v = 0
  · simp [hv, ODEStateNormalization.unitDirection]
  · have hn : ‖v‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr hv)
    rw [Complex.coe_smul]
    unfold ODEStateNormalization.unitDirection
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]

/-- Rescaling the actual source-preparation branch sum exactly recovers
the unnormalized propagated source sum. Zero branches cancel algebraically,
so they impose no condition on the supplied preparation map. -/
theorem rescaled_preparedSum (z : ι → V) (S J : ι → V →L[ℂ] V)
    (seed : V) (hB : 0 < mass z)
    (hPrep : ∀ a, z a ≠ 0 →
      J a seed = ODEStateNormalization.unitDirection (z a)) :
    (mass z : ℂ) • (∑ a, (probability z a : ℂ) • S a (J a seed)) =
      ∑ a, S a (z a) := by
  classical
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hw : mass z * probability z a = ‖z a‖ := by
    unfold probability
    field_simp [ne_of_gt hB]
  rw [smul_smul, ← Complex.ofReal_mul, hw]
  by_cases hz : z a = 0
  · simp [hz]
  · rw [hPrep a hz, ← (S a).map_smul]
    rw [norm_smul_unitDirection]

/-- Initial-state branch and uniformly weighted constant-forcing branches.
Complex scalar notation uses the canonical real action on the source space. -/
def sourceVector (v b : V) (T : ℝ) (N : ℕ) : Option (Fin N) → V
  | none => v
  | some i => (ODESourceQuadrature.weight T N i : ℂ) • b

/-- Refining the source quadrature does not change the source mass. -/
theorem mass_sourceVector (v b : V) (T : ℝ) (hT : 0 ≤ T)
    (N : ℕ) (hN : 0 < N) :
    mass (sourceVector v b T N) = ‖v‖ + T * ‖b‖ := by
  have hnorm (i : Fin N) :
      ‖sourceVector v b T N (some i)‖ =
        ODESourceQuadrature.weight T N i * ‖b‖ := by
    rw [sourceVector, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (ODESourceQuadrature.weight_nonneg T hT N i)]
  calc
    _ = ‖v‖ + ∑ i : Fin N, ODESourceQuadrature.weight T N i * ‖b‖ := by
      unfold mass
      rw [Fintype.sum_option]
      exact congrArg (fun r : ℝ => ‖v‖ + r)
        (Finset.sum_congr rfl (fun i _ => hnorm i))
    _ = ‖v‖ + T * ‖b‖ := by
      rw [← Finset.sum_mul, ODESourceQuadrature.sum_weights T N hN]

/-- The branch sum is precisely the previously certified finite-Duhamel
target, for arbitrary branch propagators. -/
theorem source_sum_eq_finiteDuhamel (v b : V) (T : ℝ) (N : ℕ)
    (S : Option (Fin N) → V →L[ℂ] V) :
    (∑ a, S a (sourceVector v b T N a)) =
      ODEErrorBudget.finiteDuhamel (S none) (fun i => S (some i))
        v (ODESourceQuadrature.weight T N) (fun _ => b) := by
  rw [Fintype.sum_option]
  simp only [sourceVector, map_smul, ODEErrorBudget.finiteDuhamel]

/-- Exact normalization of the norm-weighted constant-forcing preparation.
This is an equality, so the later simulation and quadrature error budgets
can be added without an additional source-label factor. -/
theorem prepared_source_eq_finiteDuhamel (v b : V) (T : ℝ) (hT : 0 ≤ T)
    (N : ℕ) (hN : 0 < N) (S J : Option (Fin N) → V →L[ℂ] V)
    (seed : V) (hB : 0 < ‖v‖ + T * ‖b‖)
    (hPrep : ∀ a, sourceVector v b T N a ≠ 0 →
      J a seed = ODEStateNormalization.unitDirection (sourceVector v b T N a)) :
    ((‖v‖ + T * ‖b‖ : ℝ) : ℂ) •
        (∑ a, (probability (sourceVector v b T N) a : ℂ) • S a (J a seed)) =
      ODEErrorBudget.finiteDuhamel (S none) (fun i => S (some i))
        v (ODESourceQuadrature.weight T N) (fun _ => b) := by
  have hmass := mass_sourceVector v b T hT N hN
  have hpositive : 0 < mass (sourceVector v b T N) := by rw [hmass]; exact hB
  have h := rescaled_preparedSum (sourceVector v b T N) S J seed hpositive hPrep
  rw [hmass, source_sum_eq_finiteDuhamel] at h
  exact h

/-- All source durations share the same maximum time. The initial branch
uses the full duration, while forcing branches use the certified mesh. -/
def duration (T : ℝ) (N : ℕ) : Option (Fin N) → ℝ
  | none => T
  | some i => ODESourceQuadrature.time T N i

section ConstantForcing

variable [CompleteSpace V]

/-- The exact propagator at each initial/source duration. -/
def propagation (A : V →L[ℂ] V) (T : ℝ) (N : ℕ)
    (a : Option (Fin N)) : V →L[ℂ] V :=
  NormedSpace.exp (duration T N a • A)

/-- Choose the actual finite source register from dissipativity. The source
normalization, common duration bounds, solution norm bound and vector error
are all conclusions. This reuses the proved finite-Duhamel quadrature and
leaves no source-discretization accuracy premise for the circuit interface. -/
theorem exists_constant_forcing_branches
    (A : V →L[ℂ] V) (hA : ODEDissipative.Dissipative A)
    (v b : V) (T ν : ℝ) (hT : 0 ≤ T) (hν : 0 < ν) :
    ∃ N : ℕ, 0 < N ∧
      mass (sourceVector v b T N) = ‖v‖ + T * ‖b‖ ∧
      (∀ a : Option (Fin N), 0 ≤ duration T N a ∧ duration T N a ≤ T) ∧
      ‖ODEConstantForcing.solution A v b T‖ ≤ mass (sourceVector v b T N) ∧
      ‖(∑ a, propagation A T N a (sourceVector v b T N a)) -
          ODEConstantForcing.solution A v b T‖ ≤
        ν * mass (sourceVector v b T N) := by
  obtain ⟨N, hN, _hw, ht, hB, hQuad⟩ :=
    ODESourceQuadrature.exists_finiteDuhamel_certificate A hA v b T hT ν hν
  have hmass := mass_sourceVector v b T hT N hN
  refine ⟨N, hN, hmass, ?_, ?_, ?_⟩
  · intro a
    cases a with
    | none => exact ⟨hT, le_rfl⟩
    | some i => exact ht i
  · rw [hmass]
    exact ODEConstantForcing.solution_norm_le A hA v b T hT
  · have hsum :
        (∑ a, propagation A T N a (sourceVector v b T N a)) =
          ODEErrorBudget.finiteDuhamel (NormedSpace.exp (T • A))
            (fun i : Fin N => NormedSpace.exp (ODESourceQuadrature.time T N i • A))
            v (ODESourceQuadrature.weight T N) (fun _ => b) := by
      simpa only [propagation, duration] using
        source_sum_eq_finiteDuhamel v b T N (propagation A T N)
    rw [hsum, hmass]
    simpa only [hB] using hQuad

end ConstantForcing

end
end SparseHamiltonian.ODESourceBranches
