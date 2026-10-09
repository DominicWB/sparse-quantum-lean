import MeasuredUnitaryLowerBound.OperatorNorm.CallsBound
import MeasuredUnitaryLowerBound.OperatorNorm.Programs

set_option autoImplicit false
set_option synthInstance.maxSize 8192

/-!
# Unitary programs: the operator-norm bounds through containment

Corollary `hs:cor:unitary` of the manuscript (lines 1647-1666) for the unitary circuits of its
statement, `‖A_U - U‖ ≤ ε` (eq. `hs:eq:unitaryerror`, lines 1652-1654). A unitary program over the
released entry oracle (or over its four call forms) with operator-norm error `ε₀ ≤ 1/2` on an
isometric encoding `J` is, run and output in full (`runAll`), a measured algorithm that
implements every `U_m` within operator-norm error `ε₀` (`normImplements_runAll`), so the measured
operator-norm bounds apply (over the call forms the bound also follows from
`implementation_count_ge_measured_calls_norm`, but it is proved from the pairwise bound, which is
the primary result there):

* `implementation_count_ge_program_norm`:
  `(N (1 - ε₀ √(1 - ε₀²/4)) - 1)² ≤ 4 (N - 1) √(N - 1) p.cost 1`;
* `implementation_count_ge_calls_program_norm`: the same with `32` over the call forms, derived
  from the pairwise bound through the real inequality `global_of_pairwise`.

They show that the measured notion contains unitary programs. Over the call forms the bound is
also a corollary of the pairwise program bound
`AdaptiveUnitaryLowerBound.Entry.calls_program_of_error`, `(1 - 2 s) √(N - 1) ≤ 2 Q` with `s = ε₀ √(1 - ε₀²/4)`, and it is proved from it: on
`0 ≤ ε₀ ≤ 1/2`, `0 ≤ N (1 - s) - 1 ≤ (N - 1) (1 - s)` and `(1 - s)² ≤ 16 (1 - 2 s)` since
`s ≤ √15 / 8`. The global form over the entry oracle goes through the measured operator-norm
bound and complements `AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_program_of_error`.
One checks (this comparison is not formalised) that the pairwise bound implies it at every `N`
when `(1 - s)² ≤ 2 (1 - 2 s)`, i.e. `s ≤ √2 - 1` (`ε₀` up to about `0.42`); the global form is
the sharper one near the endpoint `ε₀ = 1/2` for large `N`, where the pairwise factor
`1 - 2 s ≥ 1 - √15/4` is small.
-/

namespace MeasuredUnitaryLowerBound.OperatorNorm

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Readout ContinuousLinearMap
open UnitaryImplementationExtensions.SearchFamily
open DeferredMeasurementLowerBounds.Model
open AdaptiveODELowerBound.Access (callFamily)
open scoped InnerProduct InnerProductSpace

/-- **Unitary programs in operator norm, global form** (Corollary `hs:cor:unitary`, last
sentence). A unitary program over the released entry oracle of the search family that implements
every `U_m` on an isometric encoding `J` with operator-norm error `ε₀ ≤ 1/2` has
`(N (1 - ε₀ √(1 - ε₀²/4)) - 1)² ≤ 4 (N - 1) √(N - 1) p.cost 1`. -/
theorem implementation_count_ge_program_norm {N : ℕ} [NeZero N] (hN : 2 ≤ N) (γ η t ε : ℝ)
    (p : MultiOracleCircuit.Program (AdaptiveUnitaryLowerBound.Entry.entryOracles N γ η t ε))
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε)
    (hJ : J† ∘L J = 1) {ε₀ : ℝ} (hε₀ : ε₀ ≤ 1 / 2)
    (hErr : ∀ m, ‖p.eval m ∘L J - J ∘L
      SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤ ε₀) :
    ((N : ℝ) * (1 - ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4)) - 1) ^ 2 ≤
      4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * p.cost (fun _ => 1) := by
  have h := implementation_count_ge_measured_norm hN γ η t ε (runAll p) J hJ
    (Hamiltonian.endpointReadout J 0) (Hamiltonian.endpointReadout_isometry J hJ 0) hε₀
    (fun m => normImplements_runAll
      (AdaptiveUnitaryLowerBound.Entry.entryOracles_unitary N γ η t ε) p J hJ 0 m _ (hErr m))
  rwa [worstCost_runAll] at h

/-- **The pairwise factor controls the global one**: for `N ≥ 2`, `0 ≤ s ≤ √15 / 8` and
`(1 - 2 s) √(N - 1) ≤ 2 Q`, `(N (1 - s) - 1)² ≤ 32 (N - 1) √(N - 1) Q`. -/
theorem global_of_pairwise {N : ℕ} (hN : 2 ≤ N) {s Q : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ Real.sqrt 15 / 8) (hpair : (1 - 2 * s) * Real.sqrt ((N : ℝ) - 1) ≤ 2 * Q) :
    ((N : ℝ) * (1 - s) - 1) ^ 2 ≤ 32 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * Q := by
  have h15 : Real.sqrt 15 < 63 / 16 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have h15sq := Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num)
  have hs2 : s ^ 2 ≤ 15 / 64 := by
    have := mul_le_mul hs1 hs1 hs0 (by positivity)
    nlinarith
  have hsq : (1 - s) ^ 2 ≤ 16 * (1 - 2 * s) := by nlinarith
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hr := Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ (N : ℝ) - 1)
  have hr0 := Real.sqrt_nonneg ((N : ℝ) - 1)
  have hhalf : s ≤ 1 / 2 := by linarith
  have hlo : 0 ≤ (N : ℝ) * (1 - s) - 1 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ) - 2) (by linarith : 0 ≤ 1 / 2 - s)]
  have hhi : (N : ℝ) * (1 - s) - 1 ≤ ((N : ℝ) - 1) * (1 - s) := by nlinarith
  have hc : 0 ≤ 16 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hr0
  calc ((N : ℝ) * (1 - s) - 1) ^ 2 ≤ (((N : ℝ) - 1) * (1 - s)) ^ 2 :=
        pow_le_pow_left₀ hlo hhi 2
    _ = ((N : ℝ) - 1) * ((N : ℝ) - 1) * (1 - s) ^ 2 := by ring
    _ ≤ ((N : ℝ) - 1) * ((N : ℝ) - 1) * (16 * (1 - 2 * s)) :=
        mul_le_mul_of_nonneg_left hsq (mul_nonneg (by linarith) (by linarith))
    _ = 16 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) *
          ((1 - 2 * s) * Real.sqrt ((N : ℝ) - 1)) := by
        linear_combination (-16 * (1 - 2 * s) * ((N : ℝ) - 1)) * hr
    _ ≤ 16 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * (2 * Q) :=
        mul_le_mul_of_nonneg_left hpair hc
    _ = 32 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * Q := by ring

/-- **Unitary programs over the call forms in operator norm, global form.** A unitary program
over the four call forms of the released entry oracle that implements every `U_m` on an
isometric encoding `J` into `Joint Bool` of the oracle space with operator-norm error
`ε₀ ≤ 1/2` has `(N (1 - ε₀ √(1 - ε₀²/4)) - 1)² ≤ 32 (N - 1) √(N - 1) p.cost 1`. A corollary of
the pairwise bound `AdaptiveUnitaryLowerBound.Entry.calls_program_of_error`. -/
theorem implementation_count_ge_calls_program_norm {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (γ η t ε : ℝ)
    (p : MultiOracleCircuit.Program
      (callFamily (AdaptiveUnitaryLowerBound.Entry.entryOracles N γ η t ε)))
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ]
      Joint Bool (UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε))
    (hJ : J† ∘L J = 1) {ε₀ : ℝ} (hε₀ : ε₀ ≤ 1 / 2)
    (hErr : ∀ m, ‖p.eval m ∘L J - J ∘L
      SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤ ε₀) :
    ((N : ℝ) * (1 - ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4)) - 1) ^ 2 ≤
      32 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * p.cost (fun _ => 1) := by
  have hε0 : 0 ≤ ε₀ := (norm_nonneg _).trans (hErr 0)
  have hpair := AdaptiveUnitaryLowerBound.Entry.calls_program_of_error hN γ η t ε p J hJ
    (by linarith) hErr
  refine global_of_pairwise hN (mul_nonneg hε0 (Real.sqrt_nonneg _))
    (sharp_le_of_le_half hε0 hε₀) ?_
  rw [mul_assoc 2 ε₀] at hpair
  exact hpair

end
end MeasuredUnitaryLowerBound.OperatorNorm
