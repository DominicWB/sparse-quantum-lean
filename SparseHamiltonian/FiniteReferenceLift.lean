import SparseHamiltonian.AlignedMultiOracleProgram

/-!
# Untouched finite reference registers

An arbitrary joint state is represented by a finite Hilbert direct sum over
the reference basis.  No product-state or separability assumption is made.
Constant rectangular lifts preserve full-output error bounds. The reference
is a spectator and contributes no factor to the norm estimate.
-/

namespace SparseHamiltonian.FiniteReferenceLift

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

variable {R P K Q : Type*} [Fintype R]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]

/-- Apply the same rectangular operator in every reference sector. -/
abbrev lift (A : P →L[ℂ] K) :
    PiLp 2 (fun _ : R => P) →L[ℂ] PiLp 2 (fun _ : R => K) :=
  CoherentQuerySchedule.rectangular (fun _ : R => A)

omit [Fintype R] in
@[simp] theorem lift_apply (A : P →L[ℂ] K)
    (ψ : PiLp 2 (fun _ : R => P)) (r : R) : lift A ψ r = A (ψ r) := rfl

omit [Fintype R] in
/-- Lifting commutes with composition for rectangular operators. -/
theorem lift_comp (A : K →L[ℂ] Q) (B : P →L[ℂ] K) :
    lift (R := R) A ∘L lift B = lift (A ∘L B) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply PiLp.ext
  intro r
  rfl

/-- An untouched reference introduces no factor in the operator norm bound. -/
theorem norm_lift_le (A : P →L[ℂ] K) : ‖lift (R := R) A‖ ≤ ‖A‖ :=
  CoherentQuerySchedule.rectangular_norm_le (fun _ : R => A) ‖A‖
    (norm_nonneg A) (fun _ => le_rfl)

omit [Fintype R] in
/-- Endomorphism lifting is exactly the existing constant diagonal action. -/
theorem lift_eq_diagonal (A : P →L[ℂ] P) :
    lift (R := R) A = WeightedClock.diagonal (fun _ : R => A) := rfl

/-- Both fixed encodings may be rectangular and may differ. -/
theorem error_identity (U : K →L[ℂ] K) (EIn EOut : P →L[ℂ] K)
    (V : P →L[ℂ] P) :
    lift (R := R) U ∘L lift EIn - lift EOut ∘L lift V =
      lift (U ∘L EIn - EOut ∘L V) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply PiLp.ext
  intro r
  rfl

/-- The full-output operator error is valid with any finite untouched reference.
There is no dependence on its dimension and no restriction on entanglement. -/
theorem norm_error_le (U : K →L[ℂ] K) (EIn EOut : P →L[ℂ] K)
    (V : P →L[ℂ] P) (ε : ℝ)
    (hError : ‖U ∘L EIn - EOut ∘L V‖ ≤ ε) :
    ‖lift (R := R) U ∘L lift EIn - lift EOut ∘L lift V‖ ≤ ε := by
  rw [error_identity]
  exact (norm_lift_le (R := R) (U ∘L EIn - EOut ∘L V)).trans hError

/-- Pointwise error for every joint amplitude vector, without normalization. -/
theorem error_apply_le (U : K →L[ℂ] K) (EIn EOut : P →L[ℂ] K)
    (V : P →L[ℂ] P) (ε : ℝ)
    (hError : ‖U ∘L EIn - EOut ∘L V‖ ≤ ε)
    (ψ : PiLp 2 (fun _ : R => P)) :
    ‖lift U (lift EIn ψ) - lift EOut (lift V ψ)‖ ≤ ε * ‖ψ‖ := by
  let A : PiLp 2 (fun _ : R => P) →L[ℂ] PiLp 2 (fun _ : R => K) :=
    lift (R := R) U ∘L lift (R := R) EIn -
      lift (R := R) EOut ∘L lift (R := R) V
  have hA : ‖A‖ ≤ ε := norm_error_le (R := R) U EIn EOut V ε hError
  change ‖A ψ‖ ≤ ε * ‖ψ‖
  exact (A.le_opNorm ψ).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg ψ))

/-- A normalized, possibly entangled, input has the same absolute error. -/
theorem normalized_error_le (U : K →L[ℂ] K) (EIn EOut : P →L[ℂ] K)
    (V : P →L[ℂ] P) (ε : ℝ)
    (hError : ‖U ∘L EIn - EOut ∘L V‖ ≤ ε)
    (ψ : PiLp 2 (fun _ : R => P)) (hψ : ‖ψ‖ = 1) :
    ‖lift U (lift EIn ψ) - lift EOut (lift V ψ)‖ ≤ ε := by
  simpa only [hψ, mul_one] using error_apply_le U EIn EOut V ε hError ψ

/-- The manuscript's common clean encoding is a special case. -/
theorem same_embedding_error_le (U : K →L[ℂ] K) (E : P →L[ℂ] K)
    (V : P →L[ℂ] P) (ε : ℝ)
    (hError : ‖U ∘L E - E ∘L V‖ ≤ ε)
    (ψ : PiLp 2 (fun _ : R => P)) :
    ‖lift U (lift E ψ) - lift E (lift V ψ)‖ ≤ ε * ‖ψ‖ :=
  error_apply_le U E E V ε hError ψ

variable [CompleteSpace P] [CompleteSpace K]

/-- Fixed clean preparation remains isometric for joint reference inputs. -/
theorem lift_isometry (E : P →L[ℂ] K) (hE : E† ∘L E = 1) :
    (lift (R := R) E)† ∘L lift E = 1 :=
  CoherentQuerySchedule.rectangular_isometry (fun _ : R => E) (fun _ => hE)

/-- Lifting a full-space unitary leaves it unitary on joint states. -/
theorem lift_unitary (U : K →L[ℂ] K) (hU : IsUnitary U) :
    IsUnitary (lift (R := R) U) :=
  CoherentQuerySchedule.diagonal_unitary (fun _ : R => U) (fun _ => hU)

end
end SparseHamiltonian.FiniteReferenceLift
