import SparseODE.ODECoherentMoments

/-!
# Exponentials on the coherent branch register

The equality is proved by bounded coordinate evaluation of the norm-convergent
exponential series. The branch spaces may vary, and no factor for the number
of branches enters the identity.

-/

namespace SparseHamiltonian.CoherentDiagonalExp

noncomputable section
open ContinuousLinearMap

/-- Cache the standard endomorphism topology before substituting a dependent
Hilbert sum. This keeps exponential elaboration from repeating that search. -/
private theorem endomorphism_topologicalRing (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] :
    IsTopologicalRing (E →L[ℂ] E) := by
  infer_instance

variable {ι : Type*} [Fintype ι]
variable {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℂ (V i)] [∀ i, CompleteSpace (V i)]

local instance diagonalEndomorphismTopologicalRing :
    IsTopologicalRing (PiLp 2 V →L[ℂ] PiLp 2 V) :=
  endomorphism_topologicalRing (PiLp 2 V)

/-- Evaluating an operator at a vector and then at one branch is bounded. -/
def evaluation (v : PiLp 2 V) (i : ι) :
    (PiLp 2 V →L[ℂ] PiLp 2 V) →L[ℂ] V i :=
  ((ContinuousLinearMap.proj i).comp
    (PiLp.continuousLinearEquiv 2 ℂ V).toContinuousLinearMap).comp
      (ContinuousLinearMap.apply ℂ (PiLp 2 V) v)

omit [∀ (i : ι), CompleteSpace (V i)] in
@[simp] theorem evaluation_apply (v : PiLp 2 V) (i : ι)
    (B : PiLp 2 V →L[ℂ] PiLp 2 V) : evaluation v i B = B v i := rfl

omit [∀ (i : ι), CompleteSpace (V i)] in
theorem diagonal_pow_apply (A : ∀ i, V i →L[ℂ] V i)
    (m : ℕ) (v : PiLp 2 V) (i : ι) :
    (WeightedClock.diagonal A ^ m) v i = (A i ^ m) (v i) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [pow_succ', mul_apply_eq_comp,
        WeightedClock.diagonal_apply, ih]

/-- The operator exponential acts separately on every coherent branch. -/
theorem exp_diagonal (A : ∀ i, V i →L[ℂ] V i) :
    NormedSpace.exp (WeightedClock.diagonal A) =
      WeightedClock.diagonal (fun i => NormedSpace.exp (A i)) := by
  ext v i
  change NormedSpace.exp (WeightedClock.diagonal A) v i =
    NormedSpace.exp (A i) (v i)
  have hbig := (evaluation v i).map_tsum
    (NormedSpace.expSeries_summable' (𝕂 := ℂ) (WeightedClock.diagonal A))
  rw [← congrFun (NormedSpace.exp_eq_tsum ℂ) (WeightedClock.diagonal A)] at hbig
  change NormedSpace.exp (WeightedClock.diagonal A) v i =
    ∑' m : ℕ, (((m.factorial : ℂ)⁻¹ • WeightedClock.diagonal A ^ m) v) i at hbig
  have hsmall := (ContinuousLinearMap.apply ℂ (V i) (v i)).map_tsum
    (NormedSpace.expSeries_summable' (𝕂 := ℂ) (A i))
  rw [← congrFun (NormedSpace.exp_eq_tsum ℂ) (A i)] at hsmall
  change NormedSpace.exp (A i) (v i) =
    ∑' m : ℕ, ((m.factorial : ℂ)⁻¹ • A i ^ m) (v i) at hsmall
  calc
    NormedSpace.exp (WeightedClock.diagonal A) v i =
        ∑' m : ℕ, (m.factorial : ℂ)⁻¹ • (A i ^ m) (v i) := by
      simpa only [smul_apply, PiLp.smul_apply, diagonal_pow_apply] using hbig
    _ = NormedSpace.exp (A i) (v i) := by
      simpa only [smul_apply] using hsmall.symm

/-- A common scalar, in particular the simulator time, can be included. -/
theorem exp_smul_diagonal (c : ℂ) (A : ∀ i, V i →L[ℂ] V i) :
    NormedSpace.exp (c • WeightedClock.diagonal A) =
      WeightedClock.diagonal (fun i => NormedSpace.exp (c • A i)) := by
  have h : c • WeightedClock.diagonal A =
      WeightedClock.diagonal (fun i => c • A i) := by
    ext v i
    rfl
  rw [h, exp_diagonal]

end
end SparseHamiltonian.CoherentDiagonalExp
