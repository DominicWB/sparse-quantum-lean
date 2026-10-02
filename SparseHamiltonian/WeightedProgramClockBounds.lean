import SparseHamiltonian.HeterogeneousActiveLookupClock

/-!
# Weighted analytic bounds for clocks compiled from oracle programs

Each branch is a uniform involution program over one common payload space and
oracle family. Branch clock lengths may differ, and fixed public isometries
may encode proper subspaces. The catalyst budget uses the weighted average of
the actual query-count-plus-two clock lengths.
-/

namespace SparseHamiltonian.WeightedProgramClockBounds

noncomputable section
open ContinuousLinearMap OracleCircuit QueryClockStep QueryClockLinks
open scoped BigOperators InnerProduct

variable {ι X K : Type*} [Fintype ι]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {O : X → K →L[ℂ] K}

/-- The heterogeneous direct sum retains each branch's own clock length. -/
abbrev FamilySpace (ps : ι → Program O) :=
  PiLp 2 (fun i => ClockOperators.H ((ps i).count + 1) K)

/-- The actual distributed clock on every branch. -/
def familyClock (ps : ι → Program O) (hO : ∀ x, IsUnitary (O x))
    (hInv : ∀ i x v, (ps i).eval x ((ps i).eval x v) = v) (x : X) :
    FamilySpace ps →L[ℂ] FamilySpace ps :=
  WeightedClock.diagonal (fun i => programClock (ps i) hO (hInv i) x)

/-- The weighted clock-length budget. -/
def averageLength (weights : ι → ℝ) (ps : ι → Program O) : ℝ :=
  ∑ i, weights i * (slots (ps i) : ℝ)

/-- The average budget is nonnegative for nonnegative weights. -/
theorem averageLength_nonneg (weights : ι → ℝ) (ps : ι → Program O)
    (hw : ∀ i, 0 ≤ weights i) : 0 ≤ averageLength weights ps := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (Nat.cast_nonneg _))

/-- The two fixed terminal/return slots contribute exactly two to the average. -/
theorem averageLength_eq_meanQueries_add_two (weights : ι → ℝ) (ps : ι → Program O)
    (hsum : ∑ i, weights i = 1) :
    averageLength weights ps = (∑ i, weights i * ((ps i).count : ℝ)) + 2 := by
  simp only [averageLength, slots, Nat.cast_add, Nat.cast_ofNat, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul]

/-- Normalized weights retain the minimum two-slot clock budget. -/
theorem averageLength_ge_two (weights : ι → ℝ) (ps : ι → Program O)
    (hw : ∀ i, 0 ≤ weights i) (hsum : ∑ i, weights i = 1) :
    2 ≤ averageLength weights ps := by
  rw [averageLength_eq_meanQueries_add_two weights ps hsum]
  exact le_add_of_nonneg_left
    (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (Nat.cast_nonneg _)))

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- Fixed public preparation into branch boundary slots. -/
def boundary (weights : ι → ℝ) (ps : ι → Program O) (E : ι → P →ₗᵢ[ℂ] K) :
    P →L[ℂ] FamilySpace ps :=
  WeightedClock.boundary weights (fun i =>
    CanonicalWeightedClock.branchBoundary ((ps i).count + 1) (E i))

/-- The generated Hamiltonian is the weighted sum of compressed program outputs. -/
def generator (weights : ι → ℝ) (ps : ι → Program O) (E : ι → P →ₗᵢ[ℂ] K)
    (x : X) : P →L[ℂ] P :=
  WeightedClock.generator weights (fun i =>
    (E i).toContinuousLinearMap† ∘L (ps i).eval x ∘L (E i).toContinuousLinearMap)

/-- Explicit Hamiltonian represented by the family. -/
theorem generator_eq_sum (weights : ι → ℝ) (ps : ι → Program O)
    (E : ι → P →ₗᵢ[ℂ] K) (x : X) :
    generator weights ps E x = ∑ i, (weights i : ℂ) •
      ((E i).toContinuousLinearMap† ∘L (ps i).eval x ∘L (E i).toContinuousLinearMap) := rfl

variable [FiniteDimensional ℂ K]

/-- Branchwise actual inverses give the family's actual inverse. -/
def familyResolvent (ps : ι → Program O) (hO : ∀ x, IsUnitary (O x))
    (hInv : ∀ i x v, (ps i).eval x ((ps i).eval x v) = v) (x : X) :
    FamilySpace ps →L[ℂ] FamilySpace ps :=
  WeightedClock.diagonal (fun i => programResolvent (ps i) hO (hInv i) x)

/-- Every analytic promise is derived for a fixed input from the explicit
weighted distributed clocks. No branch implementation or inverse is assumed. -/
theorem family_promises_at (weights : ι → ℝ) (ps : ι → Program O)
    (hw : ∀ i, 0 ≤ weights i) (hsum : ∑ i, weights i = 1)
    (Q : ℝ) (hQ : 1 ≤ Q) (hqQ : ∀ i, (slots (ps i) : ℝ) ≤ Q)
    (hO : ∀ x, IsUnitary (O x))
    (hInv : ∀ i x v, (ps i).eval x ((ps i).eval x v) = v)
    (E : ι → P →ₗᵢ[ℂ] K) (x : X) :
    let D := familyClock ps hO hInv x
    let R := familyResolvent ps hO hInv x
    let J := boundary weights ps E
    let H := generator weights ps E x
    let qbar := averageLength weights ps
    D† ∘L D = 1 ∧ J† ∘L J = 1 ∧
      (1 - D) ∘L R = 1 ∧ R ∘L (1 - D) = 1 ∧ ‖R‖ ≤ Q ∧
      J† ∘L R ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H) ∧
      star H = H ∧ ‖H‖ ≤ 1 ∧ ‖R ∘L J‖ ≤ Real.sqrt (qbar / 2) ∧
      Real.sqrt (qbar / 2) ^ 2 = qbar / 2 ∧ qbar ≤ Q := by
  obtain ⟨hD, hJ, hLeft, hRight, hR, hBoundary, hSelf, hH, hEndpoint, hSq, hAverage⟩ :=
    DistributedWeightedClock.distributed_weighted_clock_promises weights
      (fun i => (ps i).count + 1) hw hsum Q (zero_le_one.trans hQ) hqQ
      (fun i => ((ps i).eval x).toLinearMap) (fun i => hInv i x)
      (fun i => program_hermitian (ps i) hO (hInv i) x) E
      (fun i j => ClockGauge.prefixGauge (clockLinkEquiv (ps i) hO x) j.val)
      (fun _ => rfl)
  exact ⟨hD, hJ, hRight, hLeft, hR, hBoundary, hSelf, hH, hEndpoint, hSq, hAverage⟩

/-- Uniform analytic assumptions in evolution-certificate order. The public
boundary is fixed for every input; only the branch clocks and Hamiltonian vary. -/
theorem family_promises (weights : ι → ℝ) (ps : ι → Program O)
    (hw : ∀ i, 0 ≤ weights i) (hsum : ∑ i, weights i = 1)
    (Q : ℝ) (hQ : 1 ≤ Q) (hqQ : ∀ i, (slots (ps i) : ℝ) ≤ Q)
    (hO : ∀ x, IsUnitary (O x))
    (hInv : ∀ i x v, (ps i).eval x ((ps i).eval x v) = v)
    (E : ι → P →ₗᵢ[ℂ] K) :
    let D := familyClock ps hO hInv
    let R := familyResolvent ps hO hInv
    let J := boundary weights ps E
    let H := generator weights ps E
    let qbar := averageLength weights ps
    let b := Real.sqrt (qbar / 2)
    (∀ x, (D x)† ∘L D x = 1) ∧ J† ∘L J = 1 ∧
      (∀ x, (1 - D x) ∘L R x = 1) ∧ (∀ x, R x ∘L (1 - D x) = 1) ∧
      (∀ x, ‖R x‖ ≤ Q) ∧
      (∀ x, J† ∘L R x ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H x)) ∧
      (∀ x, star (H x) = H x) ∧ (∀ x, ‖H x‖ ≤ 1) ∧
      (∀ x, ‖R x ∘L J‖ ≤ b) ∧ b ^ 2 ≤ qbar / 2 ∧ qbar ≤ Q := by
  have h := family_promises_at weights ps hw hsum Q hQ hqQ hO hInv E
  have hJ := WeightedClock.boundary_isometry weights hw hsum
    (fun i => CanonicalWeightedClock.branchBoundary ((ps i).count + 1) (E i))
    (fun i => CanonicalWeightedClock.branchBoundary_isometry ((ps i).count + 1) (E i))
  refine ⟨fun x => (h x).1, hJ, fun x => (h x).2.2.1,
    fun x => (h x).2.2.2.1, fun x => (h x).2.2.2.2.1,
    fun x => (h x).2.2.2.2.2.1, fun x => (h x).2.2.2.2.2.2.1,
    fun x => (h x).2.2.2.2.2.2.2.1, fun x => (h x).2.2.2.2.2.2.2.2.1, ?_, ?_⟩
  · exact (Real.sq_sqrt (div_nonneg (averageLength_nonneg weights ps hw) (by norm_num))).le
  · calc
      averageLength weights ps ≤ ∑ i, weights i * Q := by
        exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hqQ i) (hw i))
      _ = Q := by rw [← Finset.sum_mul, hsum, one_mul]

end

end SparseHamiltonian.WeightedProgramClockBounds
