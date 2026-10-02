import SparseHamiltonian.GlobalFilter

/-!
# Weighted canonical clocks with public isometric encodings

The public embeddings below need not fill a branch Hilbert space. Thus the
boundary compression is the compression of a Hermitian involution by an
isometry, as required by a block encoding. The final weighted promises are
derived from concrete clock operators and probability weights.
-/

namespace SparseHamiltonian.CanonicalWeightedClock

noncomputable section
open ContinuousLinearMap
open scoped BigOperators InnerProduct

section Branch
variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V]

/-- Public embedding into the boundary slot of a branch clock. -/
def branchBoundary (q : ℕ) (E : P →ₗᵢ[ℂ] V) : P →L[ℂ] ClockOperators.H q V :=
  ClockOperators.boundary q ∘L E.toContinuousLinearMap

/-- Public compression of a branch involution. -/
def branchGenerator (O : V →ₗ[ℂ] V) (E : P →ₗᵢ[ℂ] V) : P →L[ℂ] P :=
  E.toContinuousLinearMap† ∘L O.toContinuousLinearMap ∘L E.toContinuousLinearMap

omit [FiniteDimensional ℂ V] in
theorem branchBoundary_isometry (q : ℕ) (E : P →ₗᵢ[ℂ] V) :
    (branchBoundary q E)† ∘L branchBoundary q E = 1 := by
  apply (branchBoundary q E).norm_map_iff_adjoint_comp_self.mp
  intro x
  exact ((ClockOperators.boundaryIsometry q).norm_map (E x)).trans (E.norm_map x)

theorem branchGenerator_self_adjoint (O : V →ₗ[ℂ] V)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) (E : P →ₗᵢ[ℂ] V) :
    (branchGenerator O E)† = branchGenerator O E := by
  simp only [branchGenerator, adjoint_comp, adjoint_adjoint, comp_assoc]
  rw [← star_eq_adjoint, ClockOperators.public_self_adjoint O hHerm]

theorem branchGenerator_norm_le (O : V →ₗ[ℂ] V)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) (E : P →ₗᵢ[ℂ] V) :
    ‖branchGenerator O E‖ ≤ 1 := by
  have hE := E.norm_toContinuousLinearMap_le
  have hO' := ClockOperators.public_norm_le O hO hHerm
  calc
    ‖branchGenerator O E‖ ≤ ‖E.toContinuousLinearMap†‖ *
      (‖O.toContinuousLinearMap‖ * ‖E.toContinuousLinearMap‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (1 * 1) := by
      rw [adjoint.norm_map]
      exact mul_le_mul hE (mul_le_mul hO' hE (norm_nonneg _) zero_le_one)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
    _ = 1 := by norm_num

theorem branch_compression (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v) (E : P →ₗᵢ[ℂ] V) :
    (branchBoundary q E)† ∘L ClockOperators.resolvent O q hO ∘L branchBoundary q E =
      (2 : ℂ)⁻¹ • (1 + Complex.I • branchGenerator O E) := by
  calc
    _ = E.toContinuousLinearMap† ∘L
        ((ClockOperators.boundary q)† ∘L ClockOperators.resolvent O q hO ∘L
          ClockOperators.boundary q) ∘L E.toContinuousLinearMap := by
      simp only [branchBoundary, adjoint_comp, comp_assoc]
    _ = E.toContinuousLinearMap† ∘L
        ((2 : ℂ)⁻¹ • (1 + Complex.I • O.toContinuousLinearMap)) ∘L
          E.toContinuousLinearMap := by rw [ClockOperators.resolvent_boundary_compression]
    _ = _ := by
      simp only [smul_comp, add_comp, one_def, id_comp, comp_smul, comp_add]
      rw [E.adjoint_comp_self]
      rfl

omit [CompleteSpace P] [CompleteSpace V] in

theorem branch_endpoint_energy (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w))
    (E : P →ₗᵢ[ℂ] V) (x : P) :
    ‖ClockOperators.resolvent O q hO (branchBoundary q E x)‖ ^ 2 =
      ((q + 1 : ℕ) : ℝ) / 2 * ‖x‖ ^ 2 := by
  have h := ClockOperators.resolvent_boundary_norm_sq O q hO hHerm (E x)
  simpa only [branchBoundary, comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    E.norm_map] using h

end Branch

section Weighted
variable {ι P : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)]
  [∀ i, CompleteSpace (V i)] [∀ i, FiniteDimensional ℂ (V i)]

/-- Concrete clock branches and public isometric encodings supply all weighted
clock hypotheses, with the average length in the endpoint estimate. -/
theorem canonical_weighted_clock_promises (p : ι → ℝ) (q : ι → ℕ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (Q : ℝ) (hQ : 0 ≤ Q) (hqQ : ∀ i, ((q i + 1 : ℕ) : ℝ) ≤ Q)
    (O : ∀ i, V i →ₗ[ℂ] V i)
    (hO : ∀ i v, O i (O i v) = v)
    (hHerm : ∀ i v w, inner ℂ (O i v) w = inner ℂ v (O i w))
    (E : ∀ i, P →ₗᵢ[ℂ] V i) :
    let D := WeightedClock.diagonal (fun i => ClockOperators.clock (O i) (q i) (hO i) (hHerm i))
    let R := WeightedClock.diagonal (fun i => ClockOperators.resolvent (O i) (q i) (hO i))
    let J := WeightedClock.boundary p (fun i => branchBoundary (q i) (E i))
    let H := WeightedClock.generator p (fun i => branchGenerator (O i) (E i))
    let qbar := ∑ i, p i * ((q i + 1 : ℕ) : ℝ)
    D† ∘L D = 1 ∧ J† ∘L J = 1 ∧
    R ∘L (1 - D) = 1 ∧ (1 - D) ∘L R = 1 ∧ ‖R‖ ≤ Q ∧
    J† ∘L R ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H) ∧
    H† = H ∧ ‖H‖ ≤ 1 ∧ ‖R ∘L J‖ ≤ Real.sqrt (qbar / 2) ∧
    (Real.sqrt (qbar / 2)) ^ 2 = qbar / 2 ∧ qbar ≤ Q := by
  exact WeightedClock.weighted_clock_promises p (fun i => ((q i + 1 : ℕ) : ℝ)) hp hsum
    (fun i => Nat.cast_nonneg' _) Q hQ hqQ
    (fun i => ClockOperators.clock (O i) (q i) (hO i) (hHerm i))
    (fun i => ClockOperators.resolvent (O i) (q i) (hO i))
    (fun i => branchBoundary (q i) (E i))
    (fun i => branchGenerator (O i) (E i))
    (fun i => ClockOperators.clock_adjoint_comp (O i) (q i) (hO i) (hHerm i))
    (fun i => branchBoundary_isometry (q i) (E i))
    (fun i => ClockOperators.resolvent_left_inverse (O i) (q i) (hO i) (hHerm i))
    (fun i => ClockOperators.resolvent_right_inverse (O i) (q i) (hO i) (hHerm i))
    (fun i => ClockOperators.resolvent_norm_le (O i) (q i) (hO i) (hHerm i))
    (fun i => branch_compression (O i) (q i) (hO i) (E i))
    (fun i => branchGenerator_self_adjoint (O i) (hHerm i) (E i))
    (fun i => branchGenerator_norm_le (O i) (hO i) (hHerm i) (E i))
    (fun i x => (branch_endpoint_energy (O i) (q i) (hO i) (hHerm i) (E i) x).le)

/-- The global resolvent follows for explicit weighted canonical clocks. There
are no unproved clock-boundary or inverse-norm assumptions in this theorem. -/
theorem exists_canonical_global_resolvent (p : ι → ℝ) (q : ι → ℕ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (Q : ℝ) (hQ : 0 < Q) (hqQ : ∀ i, ((q i + 1 : ℕ) : ℝ) ≤ Q)
    (O : ∀ i, V i →ₗ[ℂ] V i)
    (hO : ∀ i v, O i (O i v) = v)
    (hHerm : ∀ i v w, inner ℂ (O i v) w = inner ℂ v (O i w))
    (E : ∀ i, P →ₗᵢ[ℂ] V i)
    (c κ σ w : ℝ) (T : ℕ) (z : ℂ)
    (hw : 0 ≤ w) (hκ : 0 ≤ κ) (hκUpper : κ ≤ 2 / 9)
    (hκc : κ = 1 - c) (hσc : σ ^ 2 = 1 - c ^ 2) (hσw : σ ^ 2 ≤ 2 * w)
    (hz : ‖z - 1‖ ≤ 1 / (4 * Q)) :
    let D := WeightedClock.diagonal (fun i => ClockOperators.clock (O i) (q i) (hO i) (hHerm i))
    let J := WeightedClock.boundary p (fun i => branchBoundary (q i) (E i))
    let qbar := ∑ i, p i * ((q i + 1 : ℕ) : ℝ)
    ∃ S : ChronologicalResolvent.BlockOperator.H T
        (PiLp 2 (fun i => ClockOperators.H (q i) (V i))) →L[ℂ]
      ChronologicalResolvent.BlockOperator.H T
        (PiLp 2 (fun i => ClockOperators.H (q i) (V i))),
      (z • 1 - GlobalResolvent.globalPrivateBlock D J c κ σ T) ∘L S = 1 ∧
      S ∘L (z • 1 - GlobalResolvent.globalPrivateBlock D J c κ σ T) = 1 ∧
      ‖S‖ ≤ 3 * (Q + (T : ℝ) * w * qbar) *
        Real.exp (3 * ((T : ℝ) * w * qbar) / (4 * Q)) := by
  obtain ⟨hDg, hJg, hLeftg, hRightg, hRnormg, hBoundaryg, hHermg, hHnormg,
    hEndpointg, hSqg, hAverageg⟩ :=
    canonical_weighted_clock_promises p q hp hsum Q hQ.le hqQ O hO hHerm E
  exact GlobalResolvent.exists_global_resolvent
    (WeightedClock.diagonal (fun i => ClockOperators.clock (O i) (q i) (hO i) (hHerm i)))
    (WeightedClock.diagonal (fun i => ClockOperators.resolvent (O i) (q i) (hO i)))
    (WeightedClock.boundary p (fun i => branchBoundary (q i) (E i)))
    (WeightedClock.generator p (fun i => branchGenerator (O i) (E i)))
    c κ σ w Q (Real.sqrt ((∑ i, p i * ((q i + 1 : ℕ) : ℝ)) / 2))
    (∑ i, p i * ((q i + 1 : ℕ) : ℝ)) T z hQ hw hκ hκUpper hκc hσc hσw
    hDg hJg hRightg hLeftg hRnormg hBoundaryg hHermg hHnormg hEndpointg
    hSqg.le hAverageg hz

/-- Explicit weighted canonical clocks admit a logarithmic-precision operator
filter. Its degree is controlled by the weighted clock budget and maximum
clock length; all analytic clock promises have been discharged. -/
theorem canonical_filter_precision (p : ι → ℝ) (q : ι → ℕ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (Q : ℝ) (hQ : 1 ≤ Q) (hqQ : ∀ i, ((q i + 1 : ℕ) : ℝ) ≤ Q)
    (O : ∀ i, V i →ₗ[ℂ] V i)
    (hO : ∀ i v, O i (O i v) = v)
    (hHerm : ∀ i v w, inner ℂ (O i v) w = inner ℂ v (O i w))
    (E : ∀ i, P →ₗᵢ[ℂ] V i)
    (c κ σ w : ℝ) (T : ℕ)
    (hw : 0 ≤ w) (hκ : 0 ≤ κ) (hκUpper : κ ≤ 2 / 9)
    (hκc : κ = 1 - c) (hσc : σ ^ 2 = 1 - c ^ 2) (hσw : σ ^ 2 ≤ 2 * w)
    (δ : ℝ) (hδ : 0 < δ) (hδOne : δ ≤ 1) :
    let D := WeightedClock.diagonal (fun i => ClockOperators.clock (O i) (q i) (hO i) (hHerm i))
    let J := WeightedClock.boundary p (fun i => branchBoundary (q i) (E i))
    let W := (T : ℝ) * w * (∑ i, p i * ((q i + 1 : ℕ) : ℝ))
    ‖averagedGeometricFilter (GlobalResolvent.globalPrivateBlock D J c κ σ T)
      (FilterSchedule.length Q) ^ FilterSchedule.depth Q W δ‖ ≤ δ ∧
    6 * W ≤ (FilterSchedule.degree Q W δ : ℝ) ∧
    (FilterSchedule.degree Q W δ : ℝ) ≤
      64 * (W + Q * (1 + Real.log ((Q + W + 2) / δ))) := by
  obtain ⟨hDg, hJg, hLeftg, hRightg, hRnormg, hBoundaryg, hHermg, hHnormg,
    hEndpointg, hSqg, hAverageg⟩ :=
    canonical_weighted_clock_promises p q hp hsum Q (zero_le_one.trans hQ) hqQ O hO hHerm E
  exact GlobalFilter.global_filter_precision
    (WeightedClock.diagonal (fun i => ClockOperators.clock (O i) (q i) (hO i) (hHerm i)))
    (WeightedClock.diagonal (fun i => ClockOperators.resolvent (O i) (q i) (hO i)))
    (WeightedClock.boundary p (fun i => branchBoundary (q i) (E i)))
    (WeightedClock.generator p (fun i => branchGenerator (O i) (E i)))
    c κ σ w Q (Real.sqrt ((∑ i, p i * ((q i + 1 : ℕ) : ℝ)) / 2))
    (∑ i, p i * ((q i + 1 : ℕ) : ℝ)) T hQ hw hκ hκUpper hκc hσc hσw
    hDg hJg hRightg hLeftg hRnormg hBoundaryg hHermg hHnormg hEndpointg
    hSqg.le hAverageg δ hδ hδOne

end Weighted

end
end SparseHamiltonian.CanonicalWeightedClock
