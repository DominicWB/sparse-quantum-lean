import SparseHamiltonian.ClockGauge

/-!
# Weighted distributed clocks

The promises required by the global resolvent and filter theorem are derived
for actual clocks with arbitrary internal unitary links. The public encodings
may occupy proper subspaces, and the branch clock lengths may differ.
-/

namespace SparseHamiltonian.DistributedWeightedClock

noncomputable section
open ContinuousLinearMap
open scoped BigOperators InnerProduct
open CanonicalWeightedClock

section Branch
variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V]

omit [CompleteSpace P] [CompleteSpace V] [FiniteDimensional ℂ V] in
/-- Slot gauges that fix zero also fix a public encoding into that slot. -/
theorem distributed_branch_fixed (q : ℕ) (E : P →ₗᵢ[ℂ] V)
    (G : Fin (q + 1) → V ≃ₗᵢ[ℂ] V)
    (hG : G 0 = LinearIsometryEquiv.refl ℂ V) (x : P) :
    ClockGauge.slotGauge q G (branchBoundary q E x) = branchBoundary q E x :=
  ClockGauge.slotGauge_fixes_boundary q G hG (E x)

/-- Public compression remains the compression of the original involution. -/
theorem distributed_branch_compression (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v) (E : P →ₗᵢ[ℂ] V)
    (G : Fin (q + 1) → V ≃ₗᵢ[ℂ] V)
    (hG : G 0 = LinearIsometryEquiv.refl ℂ V) :
    (branchBoundary q E)† ∘L ClockGauge.distributedResolvent O q hO G ∘L branchBoundary q E =
      (2 : ℂ)⁻¹ • (1 + Complex.I • branchGenerator O E) := by
  rw [ClockGauge.distributedResolvent, ClockGauge.conjugate_boundary_compression
    (ClockGauge.slotGauge q G) (ClockOperators.resolvent O q hO) (branchBoundary q E)
    (distributed_branch_fixed q E G hG)]
  exact branch_compression O q hO E

omit [CompleteSpace P] in
/-- The average-length endpoint budget survives each branch gauge exactly. -/
theorem distributed_branch_endpoint_energy (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w))
    (E : P →ₗᵢ[ℂ] V) (G : Fin (q + 1) → V ≃ₗᵢ[ℂ] V)
    (hG : G 0 = LinearIsometryEquiv.refl ℂ V) (x : P) :
    ‖ClockGauge.distributedResolvent O q hO G (branchBoundary q E x)‖ ^ 2 =
      ((q + 1 : ℕ) : ℝ) / 2 * ‖x‖ ^ 2 := by
  have h := ClockGauge.distributedResolvent_endpoint_energy O q hO hHerm G hG (E x)
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
theorem distributed_weighted_clock_promises (p : ι → ℝ) (q : ι → ℕ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (Q : ℝ) (hQ : 0 ≤ Q) (hqQ : ∀ i, ((q i + 1 : ℕ) : ℝ) ≤ Q)
    (O : ∀ i, V i →ₗ[ℂ] V i)
    (hO : ∀ i v, O i (O i v) = v)
    (hHerm : ∀ i v w, inner ℂ (O i v) w = inner ℂ v (O i w))
    (E : ∀ i, P →ₗᵢ[ℂ] V i)
    (G : ∀ i, Fin (q i + 1) → V i ≃ₗᵢ[ℂ] V i)
    (hG : ∀ i, G i 0 = LinearIsometryEquiv.refl ℂ (V i)) :
    let D := WeightedClock.diagonal (fun i => ClockGauge.distributedClock (O i) (q i) (hO i) (hHerm i) (G i))
    let R := WeightedClock.diagonal (fun i => ClockGauge.distributedResolvent (O i) (q i) (hO i) (G i))
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
    (fun i => ClockGauge.distributedClock (O i) (q i) (hO i) (hHerm i) (G i))
    (fun i => ClockGauge.distributedResolvent (O i) (q i) (hO i) (G i))
    (fun i => branchBoundary (q i) (E i))
    (fun i => branchGenerator (O i) (E i))
    (fun i => ClockGauge.distributedClock_adjoint_comp (O i) (q i) (hO i) (hHerm i) (G i))
    (fun i => branchBoundary_isometry (q i) (E i))
    (fun i => (ClockGauge.distributedResolvent_inverse (O i) (q i) (hO i) (hHerm i) (G i)).2)
    (fun i => (ClockGauge.distributedResolvent_inverse (O i) (q i) (hO i) (hHerm i) (G i)).1)
    (fun i => ClockGauge.distributedResolvent_norm_le (O i) (q i) (hO i) (hHerm i) (G i))
    (fun i => distributed_branch_compression (O i) (q i) (hO i) (E i) (G i) (hG i))
    (fun i => branchGenerator_self_adjoint (O i) (hHerm i) (E i))
    (fun i => branchGenerator_norm_le (O i) (hO i) (hHerm i) (E i))
    (fun i x => (distributed_branch_endpoint_energy (O i) (q i) (hO i) (hHerm i) (E i) (G i) (hG i) x).le)

/-- Explicit weighted distributed clocks admit a logarithmic-precision operator
filter. Its degree is controlled by the weighted clock budget and maximum
clock length; all analytic clock promises have been discharged. -/
theorem distributed_filter_precision (p : ι → ℝ) (q : ι → ℕ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (Q : ℝ) (hQ : 1 ≤ Q) (hqQ : ∀ i, ((q i + 1 : ℕ) : ℝ) ≤ Q)
    (O : ∀ i, V i →ₗ[ℂ] V i)
    (hO : ∀ i v, O i (O i v) = v)
    (hHerm : ∀ i v w, inner ℂ (O i v) w = inner ℂ v (O i w))
    (E : ∀ i, P →ₗᵢ[ℂ] V i)
    (G : ∀ i, Fin (q i + 1) → V i ≃ₗᵢ[ℂ] V i)
    (hG : ∀ i, G i 0 = LinearIsometryEquiv.refl ℂ (V i))
    (c κ σ w : ℝ) (T : ℕ)
    (hw : 0 ≤ w) (hκ : 0 ≤ κ) (hκUpper : κ ≤ 2 / 9)
    (hκc : κ = 1 - c) (hσc : σ ^ 2 = 1 - c ^ 2) (hσw : σ ^ 2 ≤ 2 * w)
    (δ : ℝ) (hδ : 0 < δ) (hδOne : δ ≤ 1) :
    let D := WeightedClock.diagonal (fun i => ClockGauge.distributedClock (O i) (q i) (hO i) (hHerm i) (G i))
    let J := WeightedClock.boundary p (fun i => branchBoundary (q i) (E i))
    let W := (T : ℝ) * w * (∑ i, p i * ((q i + 1 : ℕ) : ℝ))
    ‖averagedGeometricFilter (GlobalResolvent.globalPrivateBlock D J c κ σ T)
      (FilterSchedule.length Q) ^ FilterSchedule.depth Q W δ‖ ≤ δ ∧
    6 * W ≤ (FilterSchedule.degree Q W δ : ℝ) ∧
    (FilterSchedule.degree Q W δ : ℝ) ≤
      64 * (W + Q * (1 + Real.log ((Q + W + 2) / δ))) := by
  obtain ⟨hDg, hJg, hLeftg, hRightg, hRnormg, hBoundaryg, hHermg, hHnormg,
    hEndpointg, hSqg, hAverageg⟩ :=
    distributed_weighted_clock_promises p q hp hsum Q (zero_le_one.trans hQ) hqQ O hO hHerm E G hG
  exact GlobalFilter.global_filter_precision
    (WeightedClock.diagonal (fun i => ClockGauge.distributedClock (O i) (q i) (hO i) (hHerm i) (G i)))
    (WeightedClock.diagonal (fun i => ClockGauge.distributedResolvent (O i) (q i) (hO i) (G i)))
    (WeightedClock.boundary p (fun i => branchBoundary (q i) (E i)))
    (WeightedClock.generator p (fun i => branchGenerator (O i) (E i)))
    c κ σ w Q (Real.sqrt ((∑ i, p i * ((q i + 1 : ℕ) : ℝ)) / 2))
    (∑ i, p i * ((q i + 1 : ℕ) : ℝ)) T hQ hw hκ hκUpper hκc hσc hσw
    hDg hJg hRightg hLeftg hRnormg hBoundaryg hHermg hHnormg hEndpointg
    hSqg.le hAverageg δ hδ hδOne

end Weighted
end
end SparseHamiltonian.DistributedWeightedClock
