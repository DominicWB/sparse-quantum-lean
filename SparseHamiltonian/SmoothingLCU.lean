import SparseHamiltonian.CoherentLCU

/-!
# The actual coherent signed smoothing construction

Each branch retains its complete private output and uses a genuine uniform
preparation. The varying branch dimensions are combined in a Hilbert direct
sum, and the exact successful block is derived from the concrete SELECT and
preparations. All physical reuse lengths are positive and at most twice the
filter degree.
-/

namespace SparseHamiltonian.SmoothingLCU

noncomputable section
open scoped BigOperators InnerProduct
open ContinuousLinearMap ChronologicalResolvent CoherentReuse ReuseWeights

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The complete public and private Hilbert space of one legal reuse branch. -/
abbrev BranchSpace (d : ℕ) (i : Index d) :=
  WithLp 2 (V × BlockOperator.H (length d i) P)

/-- The actual branch circuit retains all private output. -/
def branchCircuit (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) (d : ℕ) (i : Index d) :
    BranchSpace (P := P) (V := V) d i →L[ℂ] BranchSpace (P := P) (V := V) d i :=
  fullReuse A B C D (length d i)

/-- Uniform public slots with private input zero. -/
def branchInjection (d : ℕ) (i : Index d) :
    P →L[ℂ] BranchSpace (P := P) (V := V) d i :=
  initialEmbedding (length d i)

/-- Coherent preparation with square-root absolute signed-smoothing weights. -/
def input (a : ℕ → ℝ) (d : ℕ) :
    P →L[ℂ] PiLp 2 (BranchSpace (P := P) (V := V) d) :=
  CoherentLCU.branchInput (weight a d) (branchInjection d)

/-- Coherent output preparation includes the signs of the smoothing weights. -/
def output (a : ℕ → ℝ) (d : ℕ) :
    P →L[ℂ] PiLp 2 (BranchSpace (P := P) (V := V) d) :=
  CoherentLCU.branchOutput (weight a d) (branchInjection d)

/-- The actual SELECT map applies the indicated complete reuse circuit. -/
def circuit (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) (d : ℕ) :
    PiLp 2 (BranchSpace (P := P) (V := V) d) →L[ℂ]
      PiLp 2 (BranchSpace (P := P) (V := V) d) :=
  WeightedClock.diagonal (branchCircuit A B C D d)

/-- Successful public block obtained from the concrete LCU construction. -/
def successfulBlock (a : ℕ → ℝ) (d : ℕ) (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) : P →L[ℂ] P :=
  (output a d)† ∘L circuit A B C D d ∘L input a d

theorem branchInjection_isometry (d : ℕ) (hd : 0 < d) (i : Index d) :
    (branchInjection (P := P) (V := V) d i)† ∘L branchInjection d i = 1 :=
  initialEmbedding_adjoint_comp (length d i) (Nat.ne_of_gt (length_pos d hd i))

theorem input_isometry (a : ℕ → ℝ) (d : ℕ) (hd : 0 < d)
    (ha : ∑ i : Index d, |weight a d i| = 2) :
    (input (P := P) (V := V) a d)† ∘L input a d = 1 :=
  CoherentLCU.branchInput_isometry (H := P) (V := BranchSpace (P := P) (V := V) d)
    (weight a d) ha (branchInjection d) (branchInjection_isometry d hd)

theorem output_isometry (a : ℕ → ℝ) (d : ℕ) (hd : 0 < d)
    (ha : ∑ i : Index d, |weight a d i| = 2) :
    (output (P := P) (V := V) a d)† ∘L output a d = 1 :=
  CoherentLCU.branchOutput_isometry (H := P) (V := BranchSpace (P := P) (V := V) d)
    (weight a d) ha (branchInjection d) (branchInjection_isometry d hd)

theorem circuit_isometry (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2)
    (d : ℕ) : (circuit A B C D d)† ∘L circuit A B C D d = 1 :=
  WeightedClock.diagonal_isometry (branchCircuit A B C D d)
    (fun i => fullReuse_adjoint_comp A B C D hStep (length d i))

theorem circuit_unitary [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2)
    (d : ℕ) : (circuit A B C D d)† ∘L circuit A B C D d = 1 ∧
      circuit A B C D d ∘L (circuit A B C D d)† = 1 := by
  refine ⟨circuit_isometry A B C D hStep d, ?_⟩
  unfold circuit
  rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
  have hU (i : Index d) : (branchCircuit A B C D d i).comp
      (branchCircuit A B C D d i).adjoint = 1 :=
    (fullReuse_unitary A B C D hStep (length d i)).2
  simpa only [hU] using
    (WeightedClock.diagonal_one (V := BranchSpace (P := P) (V := V) d))

/-- Actual coherent smoothing has one half of the signed public reuse sum. -/
theorem successfulBlock_eq (a : ℕ → ℝ) (d : ℕ) (hd : 0 < d)
    (A U : P →L[ℂ] P) (B : V →L[ℂ] P) (C Γ : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hPublic : A + B ∘L Γ = U) (hPrivate : C + D ∘L Γ = Γ) :
    successfulBlock a d A B C D = (2 : ℂ)⁻¹ •
      SmoothedReuse.weightedReuse a d (SmoothedReuse.reuseExpression U B Γ D) := by
  unfold successfulBlock output circuit input
  rw [CoherentLCU.branch_successful_compression]
  congr 1
  have hbranch (i : Index d) : (branchInjection (P := P) (V := V) d i)† ∘L
      branchCircuit A B C D d i ∘L branchInjection d i =
        SmoothedReuse.reuseExpression U B Γ D (length d i) :=
    fullReuse_compression_eq A U B C Γ D hPublic hPrivate (length d i)
      (Nat.ne_of_gt (length_pos d hd i))
  simp_rw [hbranch]
  simpa only [Complex.coe_smul] using
    weighted_sum_eq a d (SmoothedReuse.reuseExpression U B Γ D)

/-- The exact successful-block error is the established smoothing residual. -/
theorem successfulBlock_residual (a : ℕ → ℝ) (d : ℕ) (hd : 0 < d)
    (hmass : ∑ j ∈ Finset.range (d + 1), a j = 1)
    (A U : P →L[ℂ] P) (B : V →L[ℂ] P) (C Γ : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hPublic : A + B ∘L Γ = U) (hPrivate : C + D ∘L Γ = Γ)
    (hExit : B = U ∘L (Γ† ∘L (1 - D))) :
    (2 : ℂ)⁻¹ • U - successfulBlock a d A B C D = (2 : ℂ)⁻¹ •
      smoothedTransducerResidual U Γ (∑ j ∈ Finset.range (d + 1), a j • D ^ j) D d := by
  rw [successfulBlock_eq a d hd A U B C Γ D hPublic hPrivate, ← smul_sub,
    SmoothedReuse.weighted_expression_residual a d hd hmass U B Γ D hExit]

/-- Concrete averaging coefficients yield the filter power already bounded
in the operator filter theorem. -/
theorem concrete_successfulBlock_residual (L k : ℕ) (hL : 1 ≤ L)
    (hd : 0 < k * (L - 1))
    (A U : P →L[ℂ] P) (B : V →L[ℂ] P) (C Γ : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hPublic : A + B ∘L Γ = U) (hPrivate : C + D ∘L Γ = Γ)
    (hExit : B = U ∘L (Γ† ∘L (1 - D))) :
    (2 : ℂ)⁻¹ • U - successfulBlock (AveragingPolynomial.filter L k).coeff
      (k * (L - 1)) A B C D = (2 : ℂ)⁻¹ •
        smoothedTransducerResidual U Γ (averagedGeometricFilter D L ^ k) D (k * (L - 1)) := by
  rw [successfulBlock_eq _ _ hd A U B C Γ D hPublic hPrivate, ← smul_sub,
    SmoothedReuse.concrete_filter_residual L k hL hd U B Γ D hExit]

end
end SparseHamiltonian.SmoothingLCU
