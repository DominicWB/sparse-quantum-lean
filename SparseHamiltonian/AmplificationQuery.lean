import SparseHamiltonian.SubspaceOracle

/-!
# The three-SELECT implementation of the reflection round

The reflection about a prepared SELECT output is conjugated back to the fixed
input reflection. Thus one amplification round uses SELECT twice forward and
once backward. The input and output preparations depend only on the chosen
filter, not on any entries of the simulated operator.
-/

namespace SparseHamiltonian.AmplificationQuery

noncomputable section
open ContinuousLinearMap
open scoped InnerProduct

variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A range reflection can be moved through a surjective unitary. -/
theorem rangeReflection_conjugate (S : K →L[ℂ] K) (I : P →L[ℂ] K)
    (hSS : S ∘L S† = 1) :
    rangeReflection (S ∘L I) = S ∘L rangeReflection I ∘L S† := by
  simp only [rangeReflection, adjoint_comp, comp_sub, sub_comp,
    comp_smul, smul_comp, comp_assoc]
  simp only [one_def, id_comp] at hSS ⊢
  rw [hSS]

/-- Full-space operator for one signed amplification round. -/
def threeSelect (S : K →L[ℂ] K) (I J : P →L[ℂ] K) : K →L[ℂ] K :=
  -(S ∘L rangeReflection I ∘L S† ∘L rangeReflection J ∘L S)

/-- The previously constructed reflected output is this three-SELECT circuit
applied to the original, oracle-independent input preparation. -/
theorem reflectedAmplification_eq_threeSelect (S : K →L[ℂ] K)
    (I J : P →L[ℂ] K) (hSS : S ∘L S† = 1) :
    reflectedAmplification J (S ∘L I) = threeSelect S I J ∘L I := by
  simp only [reflectedAmplification, rangeReflection_conjugate S I hSS,
    threeSelect, neg_comp, comp_assoc]

/-- Both fixed reflections are involutions as soon as the preparations are
isometries. No SELECT data enters these two operators. -/
theorem fixed_reflections_unitary (I J : P →L[ℂ] K)
    (hI : I† ∘L I = 1) (hJ : J† ∘L J = 1) :
    (rangeReflection I)† ∘L rangeReflection I = 1 ∧
      rangeReflection I ∘L (rangeReflection I)† = 1 ∧
      (rangeReflection J)† ∘L rangeReflection J = 1 ∧
      rangeReflection J ∘L (rangeReflection J)† = 1 := by
  simpa only [rangeReflection_adjoint] using
    And.intro (rangeReflection_comp_self I hI)
      (And.intro (rangeReflection_comp_self I hI)
        (And.intro (rangeReflection_comp_self J hJ) (rangeReflection_comp_self J hJ)))

/-- A fixed range reflection is an admissible free gate in the oracle model. -/
theorem reflection_unitary (I : P →L[ℂ] K) (hI : I† ∘L I = 1) :
    OracleCircuit.IsUnitary (rangeReflection I) := by
  constructor
  · exact rangeReflection_isometry I hI
  · change rangeReflection I ∘L (rangeReflection I)† = 1
    rw [rangeReflection_adjoint]
    exact rangeReflection_comp_self I hI

/-- The global minus sign can be included in a fixed reflection gate. -/
theorem negative_reflection_unitary (I : P →L[ℂ] K) (hI : I† ∘L I = 1) :
    OracleCircuit.IsUnitary (-rangeReflection I) := by
  have hR := reflection_unitary I hI
  constructor
  · simpa only [star_neg, neg_mul_neg] using hR.1
  · simpa only [star_neg, neg_mul_neg] using hR.2

/-- A syntactic program with two forward SELECT calls and one inverse call.
Both interleaved reflections are fixed over the entire oracle family. -/
def threeSelectProgram {X : Type*} {O : X → K →L[ℂ] K}
    (p : OracleCircuit.Program O) (I J : P →L[ℂ] K)
    (hI : I† ∘L I = 1) (hJ : J† ∘L J = 1) : OracleCircuit.Program O :=
  .seq (.seq (.seq (.seq p
    (.fixed (-rangeReflection I) (negative_reflection_unitary I hI))) p.adjoint)
    (.fixed (rangeReflection J) (reflection_unitary J hJ))) p

/-- Evaluation of the syntactic program is the operator constructed above. -/
theorem threeSelectProgram_eval {X : Type*} {O : X → K →L[ℂ] K}
    (p : OracleCircuit.Program O) (I J : P →L[ℂ] K)
    (hI : I† ∘L I = 1) (hJ : J† ∘L J = 1) (x : X) :
    (threeSelectProgram p I J hI hJ).eval x = threeSelect (p.eval x) I J := by
  simp only [threeSelectProgram, OracleCircuit.Program.eval_seq,
    OracleCircuit.Program.eval_fixed, OracleCircuit.Program.eval_adjoint,
    mul_neg, neg_mul]
  rfl

/-- The exact syntactic count is three times the SELECT program count. -/
theorem threeSelectProgram_count {X : Type*} {O : X → K →L[ℂ] K}
    (p : OracleCircuit.Program O) (I J : P →L[ℂ] K)
    (hI : I† ∘L I = 1) (hJ : J† ∘L J = 1) :
    (threeSelectProgram p I J hI hJ).count = 3 * p.count := by
  simp only [threeSelectProgram, OracleCircuit.Program.count_seq,
    OracleCircuit.Program.count_fixed, OracleCircuit.Program.count_adjoint,
    add_zero]
  omega

/-- A uniform SELECT certificate yields a uniform amplification certificate
with three times the query budget, without any new oracle primitive. -/
theorem threeSelect_implements {X : Type*} {O S : X → K →L[ℂ] K} {q : ℕ}
    (I J : P →L[ℂ] K) (hI : I† ∘L I = 1) (hJ : J† ∘L J = 1)
    (hS : OracleCircuit.Implements O S q) :
    OracleCircuit.Implements O (fun x => threeSelect (S x) I J) (3 * q) := by
  obtain ⟨p, hp, hq⟩ := hS
  refine ⟨threeSelectProgram p I J hI hJ, ?_, ?_⟩
  · intro x
    rw [threeSelectProgram_eval, hp]
  · rw [threeSelectProgram_count]
    exact Nat.mul_le_mul_left 3 hq

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Specialization to the actual coherent smoothing SELECT, retaining every
public slot and every private output. -/
theorem smoothing_eq_threeSelect [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    (a : ℕ → ℝ) (d : ℕ)
    (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2) :
    reflectedAmplification (SmoothingLCU.output a d)
        (SmoothingLCU.circuit A B C D d ∘L SmoothingLCU.input a d) =
      threeSelect (SmoothingLCU.circuit A B C D d)
        (SmoothingLCU.input a d) (SmoothingLCU.output a d) ∘L
          SmoothingLCU.input a d :=
  reflectedAmplification_eq_threeSelect _ _ _
    (SmoothingLCU.circuit_unitary A B C D hStep d).2

/-- The existing precision-certified implementation is exactly the explicit
three-SELECT circuit followed by its fixed input preparation. -/
theorem implementation_eq_threeSelect [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    (L k : ℕ)
    (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2) :
    AmplifiedSmoothing.implementation L k A B C D =
      threeSelect (SmoothingLCU.circuit A B C D (k * (L - 1)))
        (SmoothingLCU.input (AveragingPolynomial.filter L k).coeff (k * (L - 1)))
        (SmoothingLCU.output (AveragingPolynomial.filter L k).coeff (k * (L - 1))) ∘L
      SmoothingLCU.input (AveragingPolynomial.filter L k).coeff (k * (L - 1)) :=
  smoothing_eq_threeSelect _ _ A B C D hStep

/-- The exact implemented smoothing output has a uniform program with at most
three times the SELECT query count. Preparation remains an explicitly fixed
input isometry; it is not counted as an oracle-dependent free operation. -/
theorem implementation_query_certificate
    [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    {X : Type*} (L k : ℕ) (hL : 1 ≤ L) (hd : 0 < k * (L - 1))
    (O : X → PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := V) (k * (L - 1))) →L[ℂ]
      PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := V) (k * (L - 1))))
    (A : X → P →L[ℂ] P) (B : X → V →L[ℂ] P)
    (C : X → P →L[ℂ] V) (D : X → V →L[ℂ] V)
    (hStep : ∀ x p v, ‖A x p + B x v‖ ^ 2 + ‖D x v + C x p‖ ^ 2 =
      ‖p‖ ^ 2 + ‖v‖ ^ 2)
    (q : ℕ)
    (hCircuit : OracleCircuit.Implements O
      (fun x => SmoothingLCU.circuit (A x) (B x) (C x) (D x) (k * (L - 1))) q) :
    ∃ p : OracleCircuit.Program O, p.count ≤ 3 * q ∧ ∀ x,
      p.eval x ∘L SmoothingLCU.input (P := P) (V := V) (AveragingPolynomial.filter L k).coeff
        (k * (L - 1)) = AmplifiedSmoothing.implementation L k (A x) (B x) (C x) (D x) := by
  have hmass := ReuseWeights.concrete_absolute_mass L k hL hd
  obtain ⟨p, hp, hq⟩ := threeSelect_implements
    (SmoothingLCU.input (P := P) (V := V) (AveragingPolynomial.filter L k).coeff (k * (L - 1)))
    (SmoothingLCU.output (P := P) (V := V) (AveragingPolynomial.filter L k).coeff (k * (L - 1)))
    (SmoothingLCU.input_isometry (P := P) (V := V) _ _ hd hmass)
    (SmoothingLCU.output_isometry (P := P) (V := V) _ _ hd hmass) hCircuit
  refine ⟨p, hq, fun x => ?_⟩
  rw [hp, implementation_eq_threeSelect L k (A x) (B x) (C x) (D x) (hStep x)]

end
end SparseHamiltonian.AmplificationQuery
