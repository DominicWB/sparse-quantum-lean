import SparseODE.ImprovedSparseODE
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Complete ODE success and conditional mixed-output guarantee

Lean / Mathlib: 4.32.1. This extends the constant-coefficient dissipative
solver with a bounded repeat-until-success protocol and mixed-output analysis.

Endpoint: SparseHamiltonian.ODECompleteEndpoint.solver

The endpoint retains the original constant-coefficient dissipative ODE
promises and constructs a protocol of at most four fresh existing trials.
It has success probability at least 175/256 (> 2/3), and its conditional mixed
output is positive, trace one, and within spectral trace distance epsilon
of the normalised actual solution. Each completed history obeys the strict
worst-case primitive-oracle budget; the wrapper multiplies the existing
bound by at most four. The source interfaces and their controls are unchanged.

The public query-free operations remain the exact operations allowed by
the released oracle model. This extension does not assert gate efficiency,
time-dependent ODE correctness, or any result for the linear-system solver.

Checked axiom dependencies are collected in `SparseODE/Audit.lean`.
-/

/-! ## ODERepeatProbability -/

/-!
# A bounded repeat-until-success protocol for the physical ODE trials

One attempt samples the existing finite trial family uniformly, applies its
actual unitary circuit to a fresh copy of its fixed seed, and measures the
clean-output projection.  The following finite probability law describes
four such fresh attempts, stopping at the first successful herald.  It is
derived from the actual projected vectors; the success probability is not
an additional promise about a different preparation.
-/

namespace SparseHamiltonian.ODERepeatProbability

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators InnerProduct

section Measurement

variable {R : Type*}
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The two measurement operators of an orthogonal herald form a complete
instrument.  They are public operators, so this measurement adds no oracle
calls. -/
theorem instrument_complete (P : R →L[ℂ] R)
    (hP : PhaseSubspaceGates.IsOrthogonalProjection P) :
    star P * P + star (1 - P) * (1 - P) = 1 := by
  simp only [star_sub, star_one, hP.1, sub_mul, mul_sub, one_mul,
    mul_one, hP.2]
  abel

/-- The Born weights of the two herald outcomes sum to the input norm
squared, including zero and unnormalised inputs. -/
theorem instrument_norm_partition (P : R →L[ℂ] R)
    (hP : PhaseSubspaceGates.IsOrthogonalProjection P) (a : R) :
    ‖P a‖ ^ 2 + ‖(1 - P) a‖ ^ 2 = ‖a‖ ^ 2 := by
  have hIdem : P (P a) = P a := by
    exact congrArg (fun Q : R →L[ℂ] R => Q a) hP.2
  have hInner : inner ℂ a (P a) = inner ℂ (P a) (P a) := by
    calc
      inner ℂ a (P a) = inner ℂ a ((P†) (P a)) := by
        rw [show P† = P from hP.1, hIdem]
      _ = inner ℂ (P a) (P a) := adjoint_inner_right P a (P a)
  have hSq := norm_sub_sq (𝕜 := ℂ) a (P a)
  rw [hInner, inner_self_eq_norm_sq] at hSq
  change ‖P a‖ ^ 2 + ‖a - P a‖ ^ 2 = ‖a‖ ^ 2
  linarith

end Measurement

section FiniteLaw

variable {M : ℕ}

/-- The actual uniform mean of the individual Born success weights. -/
def mean (p : Fin M → ℝ) : ℝ := (∑ j, p j) / (M : ℝ)

theorem mean_nonneg (p : Fin M → ℝ) (hp : ∀ j, 0 ≤ p j) :
    0 ≤ mean p := by
  exact div_nonneg (Finset.sum_nonneg (fun j _ => hp j)) (Nat.cast_nonneg M)

theorem mean_le_one (p : Fin M → ℝ) (hM : 0 < M)
    (hp : ∀ j, p j ≤ 1) : mean p ≤ 1 := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  apply (div_le_iff₀ hMr).2
  calc
    (∑ j, p j) ≤ ∑ _j : Fin M, (1 : ℝ) :=
      Finset.sum_le_sum (fun j _ => hp j)
    _ = 1 * (M : ℝ) := by simp

/-- A one-attempt outcome includes the uniformly selected trial on a
successful herald; the unsuccessful choices are combined into `none`. -/
def outcomeWeight (p : Fin M → ℝ) : Option (Fin M) → ℝ
  | none => 1 - mean p
  | some j => p j / (M : ℝ)

theorem outcomeWeight_nonneg (p : Fin M → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hMean : mean p ≤ 1) :
    ∀ o, 0 ≤ outcomeWeight p o := by
  intro o
  cases o with
  | none => exact sub_nonneg.mpr hMean
  | some j => exact div_nonneg (hp j) (Nat.cast_nonneg M)

theorem outcomeWeight_total (p : Fin M → ℝ) :
    outcomeWeight p none + ∑ j, outcomeWeight p (some j) = 1 := by
  simp only [outcomeWeight, ← Finset.sum_div, mean]
  ring

/-- Recursive probability of reaching attempt `r`.  Multiplication by the
same one-attempt failure weight expresses the fresh preparation and fresh
uniform draw at every iteration. -/
def reachWeight (p : Fin M → ℝ) : ℕ → ℝ
  | 0 => 1
  | r + 1 => reachWeight p r * outcomeWeight p none

theorem reachWeight_eq (p : Fin M → ℝ) (r : ℕ) :
    reachWeight p r = (1 - mean p) ^ r := by
  induction r with
  | zero => simp [reachWeight]
  | succ r ih => simp only [reachWeight, ih, outcomeWeight, pow_succ]

/-- Joint weight of the first successful attempt and its chosen trial. -/
def firstSuccessWeight (p : Fin M → ℝ) (r : Fin 4) (j : Fin M) : ℝ :=
  reachWeight p r.val * outcomeWeight p (some j)

theorem firstSuccessWeight_eq (p : Fin M → ℝ) (r : Fin 4) (j : Fin M) :
    firstSuccessWeight p r j = (1 - mean p) ^ r.val * p j / (M : ℝ) := by
  simp only [firstSuccessWeight, reachWeight_eq, outcomeWeight, mul_div_assoc]

/-- All four heralds fail.  A fifth attempt is never performed. -/
def failureProbability (p : Fin M → ℝ) : ℝ := reachWeight p 4

@[simp] theorem failureProbability_eq (p : Fin M → ℝ) :
    failureProbability p = (1 - mean p) ^ 4 := reachWeight_eq p 4

/-- Total successful mass of the stopped four-attempt protocol. -/
def successProbability (p : Fin M → ℝ) : ℝ :=
  ∑ r : Fin 4, ∑ j : Fin M, firstSuccessWeight p r j

theorem firstSuccessWeight_sum (p : Fin M → ℝ) (r : Fin 4) :
    (∑ j : Fin M, firstSuccessWeight p r j) =
      (1 - mean p) ^ r.val * mean p := by
  simp only [firstSuccessWeight_eq, ← Finset.sum_div, ← Finset.mul_sum,
    mul_div_assoc, mean]

theorem successProbability_eq (p : Fin M → ℝ) :
    successProbability p = 1 - (1 - mean p) ^ 4 := by
  unfold successProbability
  simp only [firstSuccessWeight_sum]
  simp [Fin.sum_univ_succ]
  ring

theorem stopped_total (p : Fin M → ℝ) :
    successProbability p + failureProbability p = 1 := by
  rw [successProbability_eq, failureProbability_eq]
  ring

theorem firstSuccessWeight_nonneg (p : Fin M → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hMean : mean p ≤ 1)
    (r : Fin 4) (j : Fin M) : 0 ≤ firstSuccessWeight p r j := by
  rw [firstSuccessWeight_eq]
  exact div_nonneg
    (mul_nonneg (pow_nonneg (sub_nonneg.mpr hMean) _) (hp j)) (Nat.cast_nonneg M)

/-- The one-quarter lower bound supplied by the existing solver becomes
the explicit four-attempt success bound `175/256`. -/
theorem successProbability_lower (p : Fin M → ℝ)
    (hLower : (1 : ℝ) / 4 ≤ mean p) (hUpper : mean p ≤ 1) :
    (175 : ℝ) / 256 ≤ successProbability p := by
  have hFailure : 0 ≤ 1 - mean p := sub_nonneg.mpr hUpper
  have hThree : 1 - mean p ≤ (3 : ℝ) / 4 := by linarith
  have hPow := pow_le_pow_left₀ hFailure hThree 4
  rw [successProbability_eq]
  norm_num at hPow ⊢
  linarith

theorem successProbability_two_thirds (p : Fin M → ℝ)
    (hLower : (1 : ℝ) / 4 ≤ mean p) (hUpper : mean p ≤ 1) :
    (2 : ℝ) / 3 ≤ successProbability p := by
  exact (by norm_num : (2 : ℝ) / 3 ≤ 175 / 256).trans
    (successProbability_lower p hLower hUpper)

theorem successProbability_pos (p : Fin M → ℝ)
    (hLower : (1 : ℝ) / 4 ≤ mean p) (hUpper : mean p ≤ 1) :
    0 < successProbability p := by
  exact (by norm_num : (0 : ℝ) < 175 / 256).trans_le
    (successProbability_lower p hLower hUpper)

/-- The classical mixture after conditioning on an actual successful herald.
The labels are retained only to define the mixture; they can be discarded. -/
def conditionalWeight (p : Fin M → ℝ) (b : Fin 4 × Fin M) : ℝ :=
  firstSuccessWeight p b.1 b.2 / successProbability p

theorem conditionalWeight_nonneg (p : Fin M → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hLower : (1 : ℝ) / 4 ≤ mean p)
    (hUpper : mean p ≤ 1) (b : Fin 4 × Fin M) :
    0 ≤ conditionalWeight p b := by
  exact div_nonneg (firstSuccessWeight_nonneg p hp hUpper b.1 b.2)
    (successProbability_pos p hLower hUpper).le

theorem conditionalWeight_sum (p : Fin M → ℝ)
    (hLower : (1 : ℝ) / 4 ≤ mean p) (hUpper : mean p ≤ 1) :
    (∑ b : Fin 4 × Fin M, conditionalWeight p b) = 1 := by
  have hS : successProbability p ≠ 0 := (successProbability_pos p hLower hUpper).ne'
  simp only [conditionalWeight, ← Finset.sum_div, Fintype.sum_prod_type]
  exact div_self hS

theorem conditionalWeight_ne_zero_implies (p : Fin M → ℝ)
    (b : Fin 4 × Fin M) (hb : conditionalWeight p b ≠ 0) : p b.2 ≠ 0 := by
  intro hz
  apply hb
  simp [conditionalWeight, firstSuccessWeight_eq, hz]

end FiniteLaw

section ActualTrials

variable {P R X L : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
  {O : (L ⊕ Bool) → X → R →L[ℂ] R}

/-- Decoded vector of the actual primitive circuit, including all its
simulation and source-preparation errors. -/
def decoded (q : ℕ → MultiOracleCircuit.Program O)
    (ψ : R) (F : P →L[ℂ] R) (x : X) (j : ℕ) : P :=
  (F†) ((q j).eval x ψ)

def probability (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ)
    (ψ : R) (F : P →L[ℂ] R) (x : X) (j : Fin M) : ℝ :=
  ‖decoded q ψ F x j.val‖ ^ 2

theorem probability_nonneg (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ)
    (ψ : R) (F : P →L[ℂ] R) (x : X) (j : Fin M) :
    0 ≤ probability q M ψ F x j := sq_nonneg _

/-- The decoded norm is exactly the Born probability of the clean-output
projection applied to the implemented circuit. -/
theorem probability_eq_projector (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ)
    (ψ : R) (F : P →L[ℂ] R) (x : X)
    (hF : F† ∘L F = 1) (j : Fin M) :
    probability q M ψ F x j =
      ‖ODEHeraldedSuccess.successProjector F ((q j.val).eval x ψ)‖ ^ 2 := by
  exact (ODEHeraldedSuccess.successProbability_eq F hF ((q j.val).eval x) ψ).symm

theorem probability_le_one (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ)
    (ψ : R) (F : P →L[ℂ] R) (x : X)
    (hψ : ‖ψ‖ = 1) (hF : F† ∘L F = 1)
    (hUnitary : ∀ j, IsUnitary ((q j).eval x)) (j : Fin M) :
    probability q M ψ F x j ≤ 1 := by
  have hNorm : ‖(q j.val).eval x ψ‖ = 1 := by
    rw [((q j.val).eval x).norm_map_iff_adjoint_comp_self.mpr
      (hUnitary j.val).1, hψ]
  have hPart := instrument_norm_partition
    (ODEHeraldedSuccess.successProjector F)
    (ODEHeraldedSuccess.successProjector_isOrthogonalProjection F hF)
    ((q j.val).eval x ψ)
  rw [hNorm] at hPart
  rw [probability_eq_projector q M ψ F x hF j]
  nlinarith [sq_nonneg ‖(1 - ODEHeraldedSuccess.successProjector F)
    ((q j.val).eval x ψ)‖]

/-- The `none` outcome is exactly the uniform mean of the complementary
Born weights.  In particular, combining the failed trial labels into one
classical outcome does not insert an assumed failure probability. -/
theorem outcomeWeight_none_eq_failure_mean
    (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ)
    (ψ : R) (F : P →L[ℂ] R) (x : X)
    (hM : 0 < M) (hψ : ‖ψ‖ = 1) (hF : F† ∘L F = 1)
    (hUnitary : ∀ j, IsUnitary ((q j).eval x)) :
    outcomeWeight (probability q M ψ F x) none =
      (∑ j : Fin M, ‖(1 - ODEHeraldedSuccess.successProjector F)
        ((q j.val).eval x ψ)‖ ^ 2) / (M : ℝ) := by
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hEach (j : Fin M) :
      ‖(1 - ODEHeraldedSuccess.successProjector F)
        ((q j.val).eval x ψ)‖ ^ 2 = 1 - probability q M ψ F x j := by
    have hNorm : ‖(q j.val).eval x ψ‖ = 1 := by
      rw [((q j.val).eval x).norm_map_iff_adjoint_comp_self.mpr
        (hUnitary j.val).1, hψ]
    have hPart := instrument_norm_partition
      (ODEHeraldedSuccess.successProjector F)
      (ODEHeraldedSuccess.successProjector_isOrthogonalProjection F hF)
      ((q j.val).eval x ψ)
    rw [hNorm, ← probability_eq_projector q M ψ F x hF j] at hPart
    linarith
  simp only [hEach, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [sub_div, div_self hMr]
  rfl

theorem mean_eq_projector_average (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ)
    (ψ : R) (F : P →L[ℂ] R) (x : X) (hF : F† ∘L F = 1) :
    mean (probability q M ψ F x) =
      (∑ j ∈ Finset.range M,
        ‖ODEHeraldedSuccess.successProjector F ((q j).eval x ψ)‖ ^ 2) / (M : ℝ) := by
  unfold mean
  congr 1
  calc
    (∑ j : Fin M, probability q M ψ F x j) =
        ∑ j : Fin M,
          ‖ODEHeraldedSuccess.successProjector F ((q j.val).eval x ψ)‖ ^ 2 := by
      exact Finset.sum_congr rfl (fun j _ => probability_eq_projector q M ψ F x hF j)
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun j => ‖ODEHeraldedSuccess.successProjector F ((q j).eval x ψ)‖ ^ 2) M

/-- All probability bounds are derived from the inherited certificate and
the actual circuit unitaries. -/
theorem certified_mean_bounds (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ)
    (ψ : R) (F : P →L[ℂ] R) (x : X) (target : P) (s Θ ell g η : ℝ)
    (hUnitary : ∀ j, IsUnitary ((q j).eval x))
    (hCert : ODEPrimitiveSourceJoin.TrialCertificate q M ψ F x target s Θ ell g η) :
    (1 : ℝ) / 4 ≤ mean (probability q M ψ F x) ∧
      mean (probability q M ψ F x) ≤ 1 := by
  constructor
  · rw [mean_eq_projector_average q M ψ F x hCert.output_isometry]
    exact hCert.mean_success
  · exact mean_le_one _ hCert.cutoff_pos
      (probability_le_one q M ψ F x hCert.seed_unit hCert.output_isometry hUnitary)

theorem conditionalWeight_decoded_ne_zero
    (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ)
    (ψ : R) (F : P →L[ℂ] R) (x : X) (b : Fin 4 × Fin M)
    (hb : conditionalWeight (probability q M ψ F x) b ≠ 0) :
    decoded q ψ F x b.2.val ≠ 0 := by
  intro hz
  have hn := conditionalWeight_ne_zero_implies (probability q M ψ F x) b hb
  apply hn
  simp [probability, hz]

end ActualTrials

end
end SparseHamiltonian.ODERepeatProbability

/-! ## ODEMixedOutput -/

/-!
# Conditional mixed outputs of the sparse ODE solver

This extension uses the ordinary finite-dimensional trace distance: one half
the sum of the absolute eigenvalues of the Hermitian difference of two density
operators.  The density operator of an ensemble is constructed as the weighted
sum of its rank-one projectors.  Its positivity, trace, and trace-distance
bound are proved below; an operator-norm estimate is not substituted for a
trace-distance estimate.

All statements in this file concern an arbitrary finite-dimensional complex
Hilbert space and therefore apply to the solver's decoded output register.
Zero-weight branches do not need a normalised vector.
-/

namespace SparseHamiltonian.ODEMixedOutput

noncomputable section
open scoped BigOperators InnerProduct ComplexOrder
open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The inner-product norm identity with the concrete complex coercion.
This avoids mixing the generic `RCLike.ofReal` coercion with
`Complex.ofReal` in subsequent simplification steps. -/
theorem inner_self_complex (u : E) : inner ℂ u u = (‖u‖ : ℂ) ^ 2 :=
  inner_self_eq_norm_sq_to_K u

/-- The rank-one positive operator associated with a possibly unnormalised
vector.  It is a pure density operator when the vector has norm one. -/
def pureOperator (u : E) : E →L[ℂ] E := rankOne ℂ u u

/-- A finite ensemble, retaining zero-weight branches without restrictions. -/
def ensemble {ι : Type*} [Fintype ι] (w : ι → ℝ) (u : ι → E) : E →L[ℂ] E :=
  ∑ i, (w i : ℂ) • pureOperator (u i)

/-- Sum of absolute diagonal entries in a specified orthonormal basis. -/
def diagonalMass {α : Type*} [Fintype α] (b : OrthonormalBasis α ℂ E)
    (A : E →L[ℂ] E) : ℝ :=
  ∑ i, ‖inner ℂ (b i) (A (b i))‖

/-- Scaling an unnormalised branch amplitude scales its positive operator
by the corresponding Born weight. -/
theorem pureOperator_smul (ω : ℂ) (u : E) :
    pureOperator (ω • u) = (‖ω‖ : ℂ) ^ 2 • pureOperator u := by
  have hc : (starRingEnd ℂ) ω * ω = (‖ω‖ : ℂ) ^ 2 := RCLike.conj_mul ω
  ext z
  simp only [pureOperator, rankOne_apply, inner_smul_left, smul_apply, smul_smul]
  rw [mul_right_comm ((starRingEnd ℂ) ω) (inner ℂ u z) ω, hc]

/-- The successful post-measurement operator is the outer product of its
unnormalised decoded amplitude.  Writing it as its Born probability times
the normalised successful projector gives exactly the same operator, even
on a zero-probability branch. -/
theorem bornWeight_pureDirection (u : E) :
    ((‖u‖ ^ 2 : ℝ) : ℂ) •
        pureOperator (ODEStateNormalization.unitDirection u) = pureOperator u := by
  by_cases hu : u = 0
  · subst u
    simp [pureOperator, ODEStateNormalization.unitDirection]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hdir : ODEStateNormalization.unitDirection u =
      ((‖u‖ : ℂ)⁻¹) • u := by
    simp only [ODEStateNormalization.unitDirection,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    change ((‖u‖⁻¹ : ℝ) : ℂ) • u = ((‖u‖ : ℂ)⁻¹) • u
    rw [Complex.ofReal_inv]
  rw [hdir, pureOperator_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg u), smul_smul]
  have hnC : (‖u‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  have hc : ((‖u‖ ^ 2 : ℝ) : ℂ) * ((‖u‖⁻¹ : ℝ) : ℂ) ^ 2 = 1 := by
    rw [Complex.ofReal_pow, Complex.ofReal_inv]
    field_simp [hnC]
  rw [hc, one_smul]

theorem pureOperator_phase (ω : ℂ) (hω : ‖ω‖ = 1) (u : E) :
    pureOperator (ω • u) = pureOperator u := by
  simp only [pureOperator_smul, hω, Complex.ofReal_one, one_pow, one_smul]

theorem pureOperator_sub (u v : E) :
    pureOperator u - pureOperator v =
      rankOne ℂ (u - v) u + rankOne ℂ v (u - v) := by
  ext z
  simp only [pureOperator, sub_apply,
    add_apply, rankOne_apply, inner_sub_left, smul_sub, sub_smul]
  exact (sub_add_sub_cancel _ _ _).symm

section DiagonalEstimates

variable {α ι : Type*} [Fintype α] [Fintype ι]

theorem diagonalMass_add_le (b : OrthonormalBasis α ℂ E)
    (A B : E →L[ℂ] E) :
    diagonalMass b (A + B) ≤ diagonalMass b A + diagonalMass b B := by
  unfold diagonalMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [add_apply, inner_add_right] using
    norm_add_le (inner ℂ (b i) (A (b i))) (inner ℂ (b i) (B (b i)))

theorem diagonalMass_smul (b : OrthonormalBasis α ℂ E)
    (c : ℂ) (A : E →L[ℂ] E) :
    diagonalMass b (c • A) = ‖c‖ * diagonalMass b A := by
  simp only [diagonalMass, smul_apply, inner_smul_right, norm_mul, Finset.mul_sum]

theorem diagonalMass_sum_le (b : OrthonormalBasis α ℂ E)
    (A : ι → E →L[ℂ] E) :
    diagonalMass b (∑ j, A j) ≤ ∑ j, diagonalMass b (A j) := by
  calc
    diagonalMass b (∑ j, A j) =
        ∑ i, ‖∑ j, inner ℂ (b i) (A j (b i))‖ := by
      simp only [diagonalMass, sum_apply, inner_sum]
    _ ≤ ∑ i, ∑ j, ‖inner ℂ (b i) (A j (b i))‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_sum_le _ _
    _ = ∑ j, diagonalMass b (A j) := by
      rw [Finset.sum_comm]
      rfl

/-- Cauchy--Schwarz and Parseval, with no factor depending on dimension. -/
theorem sum_norm_inner_mul_le (b : OrthonormalBasis α ℂ E) (x y : E) :
    (∑ i, ‖inner ℂ (b i) x‖ * ‖inner ℂ y (b i)‖) ≤ ‖x‖ * ‖y‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset α)
    (fun i => ‖inner ℂ (b i) x‖) (fun i => ‖inner ℂ y (b i)‖)
  simpa only [b.sum_sq_norm_inner_right, b.sum_sq_norm_inner_left,
    Real.sqrt_sq (norm_nonneg x), Real.sqrt_sq (norm_nonneg y)] using h

theorem diagonalMass_rankOne_le (b : OrthonormalBasis α ℂ E) (x y : E) :
    diagonalMass b (rankOne ℂ x y) ≤ ‖x‖ * ‖y‖ := by
  simpa only [diagonalMass, inner_right_rankOne_apply, norm_mul] using
    sum_norm_inner_mul_le b x y

/-- The dimension-independent pure-state trace-distance estimate, first
proved for the diagonal sum in every orthonormal basis. -/
theorem diagonalMass_pure_sub_le (b : OrthonormalBasis α ℂ E)
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    diagonalMass b (pureOperator u - pureOperator v) ≤ 2 * ‖u - v‖ := by
  rw [pureOperator_sub]
  calc
    _ ≤ diagonalMass b (rankOne ℂ (u - v) u) +
        diagonalMass b (rankOne ℂ v (u - v)) := diagonalMass_add_le b _ _
    _ ≤ ‖u - v‖ * ‖u‖ + ‖v‖ * ‖u - v‖ :=
      add_le_add (diagonalMass_rankOne_le b _ _) (diagonalMass_rankOne_le b _ _)
    _ = 2 * ‖u - v‖ := by rw [hu, hv]; ring

theorem ensemble_sub_pureOperator (w : ι → ℝ) (u : ι → E)
    (v : E) (hsum : ∑ i, w i = 1) :
    ensemble w u - pureOperator v =
      ∑ i, (w i : ℂ) • (pureOperator (u i) - pureOperator v) := by
  have hsumC : ∑ i, (w i : ℂ) = 1 := by exact_mod_cast hsum
  simp only [ensemble, smul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_smul, hsumC, one_smul]

/-- Discarding a classical branch label creates a convex mixture.  Branch
dependent global phases disappear in the density operator, and the mixture
obeys the same accuracy bound as every branch in its support. -/
theorem diagonalMass_ensemble_sub_le (b : OrthonormalBasis α ℂ E)
    (w : ι → ℝ) (u : ι → E) (v : E) (δ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hu : ∀ i, w i ≠ 0 → ‖u i‖ = 1) (hv : ‖v‖ = 1)
    (hclose : ∀ i, w i ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • u i - v‖ ≤ δ) :
    diagonalMass b (ensemble w u - pureOperator v) ≤ 2 * δ := by
  classical
  rw [ensemble_sub_pureOperator w u v hsum]
  calc
    _ ≤ ∑ i, diagonalMass b ((w i : ℂ) •
        (pureOperator (u i) - pureOperator v)) := diagonalMass_sum_le b _
    _ = ∑ i, w i * diagonalMass b (pureOperator (u i) - pureOperator v) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [diagonalMass_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
    _ ≤ ∑ i, w i * (2 * δ) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hwi : w i = 0
      · simp [hwi]
      · obtain ⟨ω, hω, herror⟩ := hclose i hwi
        apply mul_le_mul_of_nonneg_left _ (hw i)
        rw [← pureOperator_phase ω hω (u i)]
        have hn : ‖ω • u i‖ = 1 := by rw [norm_smul, hω, hu i hwi, one_mul]
        calc
          _ ≤ 2 * ‖ω • u i - v‖ := diagonalMass_pure_sub_le b _ _ hn hv
          _ ≤ 2 * δ := mul_le_mul_of_nonneg_left herror (by norm_num)
    _ = 2 * δ := by rw [← Finset.sum_mul, hsum, one_mul]

end DiagonalEstimates

section DensityOperators

variable [FiniteDimensional ℂ E]

/-- A finite-dimensional density operator is positive semidefinite and has
trace one.  Positivity here includes Hermiticity. -/
def IsDensity (A : E →L[ℂ] E) : Prop :=
  A.IsPositive ∧ LinearMap.trace ℂ E A.toLinearMap = 1

omit [FiniteDimensional ℂ E] in
theorem pureOperator_positive (u : E) : (pureOperator u).IsPositive :=
  isPositive_rankOne_self u

theorem pureOperator_isDensity (u : E) (hu : ‖u‖ = 1) :
    IsDensity (pureOperator u) := by
  refine ⟨pureOperator_positive u, ?_⟩
  simp only [pureOperator, trace_rankOne, inner_self_complex,
    hu, Complex.ofReal_one, one_pow]

omit [FiniteDimensional ℂ E] in
theorem ensemble_positive {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (u : ι → E) (hw : ∀ i, 0 ≤ w i) :
    (ensemble w u).IsPositive := by
  unfold ensemble
  apply ContinuousLinearMap.isPositive_sum
  intro i _
  exact (pureOperator_positive (u i)).smul_of_nonneg
    ((RCLike.ofReal_nonneg (K := ℂ)).2 (hw i))

/-- Zero-probability branches are ignored in the normalisation condition. -/
theorem ensemble_isDensity {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (u : ι → E) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (hu : ∀ i, w i ≠ 0 → ‖u i‖ = 1) :
    IsDensity (ensemble w u) := by
  classical
  refine ⟨ensemble_positive w u hw, ?_⟩
  calc
    LinearMap.trace ℂ E (ensemble w u).toLinearMap =
        ∑ i, (w i : ℂ) * (‖u i‖ : ℂ) ^ 2 := by
      simp only [ensemble, pureOperator, ContinuousLinearMap.toLinearMap_sum,
        map_sum, ContinuousLinearMap.toLinearMap_smul, map_smul,
        trace_rankOne, inner_self_complex, smul_eq_mul]
    _ = ∑ i, (w i : ℂ) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hwi : w i = 0
      · simp [hwi]
      · simp [hu i hwi]
    _ = 1 := by exact_mod_cast hsum

/-- The usual trace distance on Hermitian differences, defined spectrally:
one half the sum of absolute eigenvalues.  In particular, this is the trace
norm rather than the operator norm or a distance between chosen vectors. -/
def hermitianTraceDistance (A B : E →L[ℂ] E)
    (h : (A - B).toLinearMap.IsSymmetric) : ℝ :=
  (∑ i : Fin (Module.finrank ℂ E), |h.eigenvalues rfl i|) / 2

theorem hermitianTraceDistance_eq_diagonalMass (A B : E →L[ℂ] E)
    (h : (A - B).toLinearMap.IsSymmetric) :
    hermitianTraceDistance A B h =
      diagonalMass (h.eigenvectorBasis (n := Module.finrank ℂ E) rfl) (A - B) / 2 := by
  unfold hermitianTraceDistance diagonalMass
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change |h.eigenvalues rfl i| =
    ‖inner ℂ (h.eigenvectorBasis rfl i)
      ((A - B).toLinearMap (h.eigenvectorBasis rfl i))‖
  have hev : (A - B).toLinearMap (h.eigenvectorBasis rfl i) =
      (h.eigenvalues rfl i : ℂ) • h.eigenvectorBasis rfl i :=
    h.apply_eigenvectorBasis rfl i
  rw [hev]
  simp only [inner_smul_right, inner_self_complex,
    OrthonormalBasis.norm_eq_one, Complex.ofReal_one, one_pow, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

theorem hermitianTraceDistance_nonneg (A B : E →L[ℂ] E)
    (h : (A - B).toLinearMap.IsSymmetric) :
    0 ≤ hermitianTraceDistance A B h := by
  unfold hermitianTraceDistance
  positivity

/-- A complete conditional mixed-output guarantee.  The resulting operator
is positive and trace one, and its standard spectral trace distance from the
desired pure state is at most `δ`.  The proof permits branch-dependent phases
and imposes no normalisation or approximation requirement on zero-weight
branches. -/
theorem ensemble_trace_distance_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (u : ι → E) (v : E) (δ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hu : ∀ i, w i ≠ 0 → ‖u i‖ = 1) (hv : ‖v‖ = 1)
    (hclose : ∀ i, w i ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • u i - v‖ ≤ δ) :
    IsDensity (ensemble w u) ∧
      ∃ h : (ensemble w u - pureOperator v).toLinearMap.IsSymmetric,
        hermitianTraceDistance (ensemble w u) (pureOperator v) h ≤ δ := by
  have hdensity := ensemble_isDensity w u hw hsum hu
  have hherm : (ensemble w u - pureOperator v).toLinearMap.IsSymmetric :=
    hdensity.1.isSymmetric.sub (pureOperator_positive v).isSymmetric
  refine ⟨hdensity, hherm, ?_⟩
  rw [hermitianTraceDistance_eq_diagonalMass]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  have hdiag := diagonalMass_ensemble_sub_le
    (hherm.eigenvectorBasis (n := Module.finrank ℂ E) rfl)
    w u v δ hw hsum hu hv hclose
  simpa only [mul_comm δ 2] using hdiag

/-- Specialisation to the ODE solver's normalised target and accuracy
allocation.  The retained bound `ε / 500` is stronger than the required `ε`. -/
theorem ode_ensemble_trace_distance_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (u : ι → E) (target : E) (ε : ℝ)
    (htarget : target ≠ 0) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hu : ∀ i, w i ≠ 0 → ‖u i‖ = 1)
    (hclose : ∀ i, w i ≠ 0 → ∃ ω : ℂ, ‖ω‖ = 1 ∧
      ‖ω • u i - ODEStateNormalization.unitDirection target‖ ≤ ε / 500) :
    IsDensity (ensemble w u) ∧
      ∃ h : (ensemble w u - pureOperator
          (ODEStateNormalization.unitDirection target)).toLinearMap.IsSymmetric,
        hermitianTraceDistance (ensemble w u)
          (pureOperator (ODEStateNormalization.unitDirection target)) h ≤ ε / 500 := by
  exact ensemble_trace_distance_le w u (ODEStateNormalization.unitDirection target)
    (ε / 500) hw hsum hu (ODEStateNormalization.unitDirection_norm target htarget) hclose

end DensityOperators

end
end SparseHamiltonian.ODEMixedOutput



/-! ## ODERepeatProtocol -/

/-!
# A bounded fresh-trial ODE preparation protocol

This file gives a finite adaptive protocol rather than an expected-query
accounting convention. A trial draws a classical uniform label, freshly
prepares a fixed seed, executes its actual primitive-oracle circuit, and
performs the fixed clean-output herald. It returns the decoded state on
success and discards the failed workspace before continuing. Four trials
therefore have a strict worst-case bound of four times the trial bound.
-/

namespace SparseHamiltonian.ODERepeatProtocol

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators InnerProduct

variable {E K X L : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {O : L → X → K →L[ℂ] K}

/-- The known herald isometry. Append an empty output sector, then apply the
query-free Julia unitary already used for source transport. Its two sectors
are the decoded successful state and the unnormalised failed state. -/
def herald (F : E →L[ℂ] K) : K →L[ℂ] ODESourceTransport.Space E K :=
  ODESourceTransport.route F ∘L ODESourceTransport.matrixEmbedding

@[simp] theorem herald_apply (F : E →L[ℂ] K) (v : K) :
    herald F v = WithLp.toLp 2 ((F†) v, v - F ((F†) v)) := by
  simp only [herald, comp_apply, ODESourceTransport.matrixEmbedding_apply,
    ODESourceTransport.route_apply, WithLp.fst, WithLp.snd, map_zero, zero_add]

/-- The herald requires no oracle call and preserves total probability. -/
theorem herald_norm (F : E →L[ℂ] K) (hF : F† ∘L F = 1) (v : K) :
    ‖herald F v‖ = ‖v‖ := by
  change ‖ODESourceTransport.route F (ODESourceTransport.matrixEmbedding v)‖ = ‖v‖
  rw [(ODESourceTransport.route F).norm_map_iff_adjoint_comp_self.mpr
    (ODESourceTransport.route_unitary F hF).1]
  exact (ODESourceTransport.matrixEmbedding : K →L[ℂ]
    ODESourceTransport.Space E K).norm_map_iff_adjoint_comp_self.mpr
      ODESourceTransport.matrixEmbedding_isometry v

/-- Born probabilities of the two explicit herald sectors sum to the input
squared norm. This includes zero-success and unit-success cases. -/
theorem herald_probability_partition (F : E →L[ℂ] K)
    (hF : F† ∘L F = 1) (v : K) :
    ‖(F†) v‖ ^ 2 + ‖v - F ((F†) v)‖ ^ 2 = ‖v‖ ^ 2 := by
  calc
    _ = ‖herald F v‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2, herald_apply]
      rfl
    _ = ‖v‖ ^ 2 := by rw [herald_norm F hF]

/-- The success sector is precisely the original clean-output projector,
followed by its isometric decoder. -/
theorem decoded_projected (F : E →L[ℂ] K) (hF : F† ∘L F = 1) (v : K) :
    (F†) (ODEHeraldedSuccess.successProjector F v) = (F†) v := by
  have h : (F†) (F ((F†) v)) = (F†) v :=
    congrArg (fun A : E →L[ℂ] E => A ((F†) v)) hF
  exact h

/-- Every datum here is public. Unknown inputs occur only in evaluations of
the supplied primitive-oracle programs. No unitarity or correctness claim
about the unknown instance is stored as an algorithm constructor. -/
structure TrialFamily (O : L → X → K →L[ℂ] K) (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] where
  choices : ℕ
  choices_pos : 0 < choices
  circuit : Fin choices → MultiOracleCircuit.Program O
  seed : K
  seed_unit : ‖seed‖ = 1
  output : E →L[ℂ] K
  output_isometry : output† ∘L output = 1

namespace TrialFamily

variable (t : TrialFamily O E)

/-- Decoded, unnormalised successful amplitude of the actual trial. -/
def amplitude (x : X) (j : Fin t.choices) : E :=
  (t.output†) ((t.circuit j).eval x t.seed)

/-- Actual conditional-on-label Born success probability. -/
def probability (x : X) (j : Fin t.choices) : ℝ := ‖t.amplitude x j‖ ^ 2

/-- Uniform classical choice of a trial label is query-free. -/
def meanSuccess (x : X) : ℝ := (∑ j, t.probability x j) / (t.choices : ℝ)

/-- Summing the physical failed-label weights produces the single failure
branch used by the adaptive syntax. No failed label is silently dropped. -/
theorem failureChoiceWeight_sum (x : X) :
    (∑ j : Fin t.choices, (1 - t.probability x j) / (t.choices : ℝ)) =
      1 - t.meanSuccess x := by
  have hM : (t.choices : ℝ) ≠ 0 := by exact_mod_cast t.choices_pos.ne'
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [sub_div, div_self hM]
  rfl

/-- Finite maximum counts forward and inverse primitive calls identically.
The same definition accepts each individual source/matrix weight. -/
def maxCost (w : L → ℕ) : ℕ := Finset.univ.sup fun j => (t.circuit j).cost w

theorem cost_le_maxCost (w : L → ℕ) (j : Fin t.choices) :
    (t.circuit j).cost w ≤ t.maxCost w := by
  change (t.circuit j).cost w ≤
    Finset.univ.sup (fun i : Fin t.choices => (t.circuit i).cost w)
  exact Finset.le_sup (f := fun i : Fin t.choices => (t.circuit i).cost w)
    (Finset.mem_univ j)

theorem probability_bounds (x : X)
    (hUnitary : ∀ j, IsUnitary ((t.circuit j).eval x)) (j : Fin t.choices) :
    0 ≤ t.probability x j ∧ t.probability x j ≤ 1 := by
  have hPart := herald_probability_partition t.output t.output_isometry
    ((t.circuit j).eval x t.seed)
  have hNorm : ‖(t.circuit j).eval x t.seed‖ = 1 := by
    rw [((t.circuit j).eval x).norm_map_iff_adjoint_comp_self.mpr (hUnitary j).1,
      t.seed_unit]
  rw [hNorm] at hPart
  constructor
  · exact sq_nonneg _
  · dsimp [probability, amplitude]
    nlinarith [sq_nonneg (‖(t.circuit j).eval x t.seed -
      t.output ((t.output†) ((t.circuit j).eval x t.seed))‖)]

theorem probability_eq_projected (x : X) (j : Fin t.choices) :
    t.probability x j =
      ‖ODEHeraldedSuccess.successProjector t.output
        ((t.circuit j).eval x t.seed)‖ ^ 2 := by
  exact (ODEHeraldedSuccess.successProbability_eq t.output t.output_isometry
    ((t.circuit j).eval x) t.seed).symm

/-- The successful normalized output is represented by this vector. Its
phase has no operational significance; its projector is the output state. -/
def outputDirection (x : X) (j : Fin t.choices) : E :=
  ODEStateNormalization.unitDirection (t.amplitude x j)

/-- Unnormalised successful operator after one fresh uniform trial.
Failure branches contribute no successful output. -/
def oneTrialDensity (x : X) : E →L[ℂ] E :=
  ODEMixedOutput.ensemble
    (fun j => t.probability x j / (t.choices : ℝ)) (t.outputDirection x)

/-- The one-trial successful density is the uniform average of the raw
Kraus-output projectors. Thus its definition by Born weights and normalised
successful directions is exactly the physical unnormalised measurement
output, including labels whose successful amplitude is zero. -/
theorem oneTrialDensity_eq_kraus (x : X) :
    t.oneTrialDensity x = (t.choices : ℂ)⁻¹ •
      ∑ j : Fin t.choices, ODEMixedOutput.pureOperator (t.amplitude x j) := by
  simp only [oneTrialDensity, ODEMixedOutput.ensemble, Finset.smul_sum,
    probability, outputDirection, Complex.ofReal_div, Complex.ofReal_natCast]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = (t.choices : ℂ)⁻¹ •
        (((‖t.amplitude x j‖ ^ 2 : ℝ) : ℂ) •
          ODEMixedOutput.pureOperator
            (ODEStateNormalization.unitDirection (t.amplitude x j))) := by
      rw [smul_smul]
      congr 1
      ring
    _ = _ := by rw [ODEMixedOutput.bornWeight_pureDirection]

private theorem nat_sup_cast_le {A : Type*} (S : Finset A) (f : A → ℕ)
    (B : ℝ) (hB : 0 ≤ B) (h : ∀ a ∈ S, (f a : ℝ) ≤ B) :
    ((S.sup f : ℕ) : ℝ) ≤ B := by
  classical
  revert h
  induction S using Finset.induction_on with
  | empty => intro _; simpa using hB
  | @insert a S ha ih =>
      intro h
      rw [Finset.sup_insert, Nat.cast_max]
      exact max_le (h a (Finset.mem_insert_self a S))
        (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))

theorem maxCost_le (w : L → ℕ) (B : ℝ)
    (h : ∀ j, ((t.circuit j).cost w : ℝ) ≤ B) :
    (t.maxCost w : ℝ) ≤ B := by
  have hB : 0 ≤ B :=
    (Nat.cast_nonneg ((t.circuit ⟨0, t.choices_pos⟩).cost w)).trans
      (h ⟨0, t.choices_pos⟩)
  exact nat_sup_cast_le Finset.univ (fun j => (t.circuit j).cost w)
    B hB (fun j _ => h j)

end TrialFamily

/-- Finite adaptive syntax: failure is the only branch that continues.
Every `freshTrial` discards the failed workspace and reinitialises the known
seed before drawing its new classical label. Success halts immediately. -/
inductive Protocol (O : L → X → K →L[ℂ] K) (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] where
  | abort
  | freshTrial (trial : TrialFamily O E) (failure : Protocol O E)

namespace Protocol

/-- At most `r` actual trials; this recursion contains no unbounded retry. -/
def repeatTrials (t : TrialFamily O E) : ℕ → Protocol O E
  | 0 => .abort
  | r + 1 => .freshTrial t (repeatTrials t r)

/-- Worst-case weighted primitive count, including every failure branch. -/
def worstCost : Protocol O E → (L → ℕ) → ℕ
  | .abort, _ => 0
  | .freshTrial t k, w => t.maxCost w + worstCost k w

@[simp] theorem repeat_worstCost (t : TrialFamily O E) (r : ℕ) (w : L → ℕ) :
    (repeatTrials t r).worstCost w = r * t.maxCost w := by
  induction r with
  | zero => simp only [repeatTrials, worstCost, zero_mul]
  | succ r ih => simp only [repeatTrials, worstCost, ih, Nat.succ_mul]; omega

/-- A real per-trial bound controls the actual protocol maximum, not merely
its expected cost or the cost of a favourable successful history. -/
theorem repeat_worstCost_le (t : TrialFamily O E) (r : ℕ) (w : L → ℕ)
    (B : ℝ) (h : ∀ j, ((t.circuit j).cost w : ℝ) ≤ B) :
    ((repeatTrials t r).worstCost w : ℝ) ≤ (r : ℝ) * B := by
  rw [repeat_worstCost, Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left (t.maxCost_le w B h) (Nat.cast_nonneg r)

/-- Failure mass obtained by applying the complete two-outcome instrument
at each fresh trial. The `abort` leaf is the event that all allowed trials
have failed; successful branches terminate and contribute no failure mass. -/
def failureMass : Protocol O E → X → ℝ
  | .abort, _ => 1
  | .freshTrial t k, x => (1 - t.meanSuccess x) * failureMass k x

/-- The recursive failure branch is exactly the sum over the freshly drawn
labels of their failure Born weights times the continuation's failure mass. -/
theorem freshTrial_failureMass_eq (t : TrialFamily O E) (k : Protocol O E) (x : X) :
    (Protocol.freshTrial t k).failureMass x =
      ∑ j : Fin t.choices,
        ((1 - t.probability x j) / (t.choices : ℝ)) * k.failureMass x := by
  rw [← Finset.sum_mul, t.failureChoiceWeight_sum]
  rfl

/-- Total successful mass of the finite protocol. -/
def successMass (p : Protocol O E) (x : X) : ℝ := 1 - p.failureMass x

/-- A successful first trial halts. Only a failed trial proceeds to the
continuation, so no extra circuit runs on a successful output. -/
theorem freshTrial_successMass_eq (t : TrialFamily O E) (k : Protocol O E) (x : X) :
    (Protocol.freshTrial t k).successMass x =
      t.meanSuccess x + (1 - t.meanSuccess x) * k.successMass x := by
  simp only [successMass, failureMass]
  ring

theorem repeat_failureMass (t : TrialFamily O E) (r : ℕ) (x : X) :
    (repeatTrials t r).failureMass x = (1 - t.meanSuccess x) ^ r := by
  induction r with
  | zero => simp [repeatTrials, failureMass]
  | succ r ih => simp only [repeatTrials, failureMass, ih, pow_succ]; ring

theorem repeat_successMass (t : TrialFamily O E) (r : ℕ) (x : X) :
    (repeatTrials t r).successMass x = 1 - (1 - t.meanSuccess x) ^ r := by
  rw [successMass, repeat_failureMass]

/-- The protocol semantics equals the explicit sum of all first-success
branches of the four-trial law. Its failure mass is not an extra assumption. -/
theorem four_successMass_eq (t : TrialFamily O E) (x : X) :
    (repeatTrials t 4).successMass x =
      ODERepeatProbability.successProbability (t.probability x) := by
  rw [repeat_successMass, ODERepeatProbability.successProbability_eq]
  rfl

/-- Operational successful output, before conditioning. A fresh successful
branch returns immediately; a failed branch contributes the continuation's
successful operator with its actual failure weight. -/
def successDensity : Protocol O E → X → E →L[ℂ] E
  | .abort, _ => 0
  | .freshTrial t k, x => t.oneTrialDensity x +
      ((1 - t.meanSuccess x : ℝ) : ℂ) • successDensity k x

/-- Condition on an actual successful herald and discard all classical
trial labels. The definition is total even when the success mass is zero;
its density-operator interpretation is used only when success is positive. -/
def conditionalDensity (p : Protocol O E) (x : X) : E →L[ℂ] E :=
  ((p.successMass x)⁻¹ : ℂ) • p.successDensity x

private theorem firstSuccess_ensemble_factor (t : TrialFamily O E) (x : X) :
    ODEMixedOutput.ensemble
      (fun a : Fin 4 × Fin t.choices =>
        ODERepeatProbability.firstSuccessWeight (t.probability x) a.1 a.2)
      (fun a : Fin 4 × Fin t.choices => t.outputDirection x a.2) =
      ∑ r : Fin 4,
        (((1 - t.meanSuccess x) ^ r.val : ℝ) : ℂ) • t.oneTrialDensity x := by
  simp only [ODEMixedOutput.ensemble, Fintype.sum_prod_type,
    ODERepeatProbability.firstSuccessWeight_eq,
    TrialFamily.oneTrialDensity, ODEMixedOutput.ensemble, Finset.smul_sum,
    smul_smul, Complex.ofReal_div, Complex.ofReal_mul,
    TrialFamily.meanSuccess, ODERepeatProbability.mean, mul_div_assoc]

/-- The recursive operational density is exactly the sum of the actual
first-success branch projectors. This connects the finite protocol syntax
to the explicit ensemble used in the mixed-output error analysis. -/
theorem four_successDensity_eq (t : TrialFamily O E) (x : X) :
    (repeatTrials t 4).successDensity x =
      ODEMixedOutput.ensemble
        (fun a : Fin 4 × Fin t.choices =>
          ODERepeatProbability.firstSuccessWeight (t.probability x) a.1 a.2)
        (fun a : Fin 4 × Fin t.choices => t.outputDirection x a.2) := by
  rw [firstSuccess_ensemble_factor]
  simp only [repeatTrials, successDensity, smul_zero, add_zero,
    Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero,
    Complex.ofReal_pow, one_smul, Fin.sum_univ_zero,
    Nat.reduceAdd, pow_one, smul_add, smul_smul, add_zero]
  module

/-- Normalising the recursive successful operator gives precisely the
conditional ensemble. No fidelity or density-matrix claim is assumed here. -/
theorem four_conditionalDensity_eq (t : TrialFamily O E) (x : X) :
    (repeatTrials t 4).conditionalDensity x =
      ODEMixedOutput.ensemble
        (ODERepeatProbability.conditionalWeight (t.probability x))
        (fun a : Fin 4 × Fin t.choices => t.outputDirection x a.2) := by
  rw [conditionalDensity, four_successMass_eq, four_successDensity_eq]
  simp only [ODEMixedOutput.ensemble, Finset.smul_sum, smul_smul,
    ODERepeatProbability.conditionalWeight, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  change (Complex.ofReal
      (ODERepeatProbability.successProbability (t.probability x)))⁻¹ *
      Complex.ofReal (ODERepeatProbability.firstSuccessWeight
        (t.probability x) a.1 a.2) =
    Complex.ofReal (ODERepeatProbability.firstSuccessWeight
      (t.probability x) a.1 a.2 *
      (ODERepeatProbability.successProbability (t.probability x))⁻¹)
  rw [Complex.ofReal_mul, Complex.ofReal_inv]
  exact mul_comm _ _

/-- A completed classical history records each uniformly chosen label and
whether that trial succeeded or failed. Failure histories end in `abort`. -/
inductive History : Protocol O E → Type _
  | abort : History .abort
  | success (t : TrialFamily O E) (k : Protocol O E) (j : Fin t.choices) :
      History (.freshTrial t k)
  | failure (t : TrialFamily O E) (k : Protocol O E) (j : Fin t.choices)
      (tail : History k) : History (.freshTrial t k)

namespace History

/-- Exact cost along a completed history; public sampling, resets, the
known herald, and the final decode do not call any unknown oracle. -/
def cost : {p : Protocol O E} → History p → (L → ℕ) → ℕ
  | _, .abort, _ => 0
  | _, .success t _ j, w => (t.circuit j).cost w
  | _, .failure t _ j tail, w => (t.circuit j).cost w + cost tail w

/-- Product Born semantics for a fresh-trial history. All previous outcomes
are failures until the final successful label, or all trials are exhausted. -/
def weight : {p : Protocol O E} → History p → X → ℝ
  | _, .abort, _ => 1
  | _, .success t _ j, x => t.probability x j / (t.choices : ℝ)
  | _, .failure t _ j tail, x =>
      ((1 - t.probability x j) / (t.choices : ℝ)) * weight tail x

def output : {p : Protocol O E} → History p → X → Option E
  | _, .abort, _ => none
  | _, .success t _ j, x => some (t.outputDirection x j)
  | _, .failure _ _ _ tail, x => output tail x

theorem cost_le_worstCost {p : Protocol O E} (h : History p) (w : L → ℕ) :
    h.cost w ≤ p.worstCost w := by
  induction h with
  | abort => exact le_rfl
  | success t k j =>
      exact (t.cost_le_maxCost w j).trans (Nat.le_add_right _ _)
  | failure t k j tail ih =>
      exact Nat.add_le_add (t.cost_le_maxCost w j) ih

/-- Every individual outcome history respects the bounded-repeat budget. -/
theorem repeat_cost_le (t : TrialFamily O E) (r : ℕ) (w : L → ℕ)
    (B : ℝ) (hB : ∀ j, ((t.circuit j).cost w : ℝ) ≤ B)
    (h : History (Protocol.repeatTrials t r)) :
    (h.cost w : ℝ) ≤ (r : ℝ) * B := by
  exact (Nat.cast_le.mpr (h.cost_le_worstCost w)).trans
    (Protocol.repeat_worstCost_le t r w B hB)

end History
end Protocol

/-- Construct the public fresh-trial family directly from existing ODE
circuit data. Instance-specific accuracy and success are analysed separately. -/
def ofCircuits (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ) (hM : 0 < M)
    (ψ : K) (hψ : ‖ψ‖ = 1) (F : E →L[ℂ] K) (hF : F† ∘L F = 1) :
    TrialFamily O E where
  choices := M
  choices_pos := hM
  circuit j := q j.val
  seed := ψ
  seed_unit := hψ
  output := F
  output_isometry := hF

/-- The four-trial public wrapper used by the completed ODE algorithm. -/
def fourTrials (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ) (hM : 0 < M)
    (ψ : K) (hψ : ‖ψ‖ = 1) (F : E →L[ℂ] K) (hF : F† ∘L F = 1) :
    Protocol O E := Protocol.repeatTrials (ofCircuits q M hM ψ hψ F hF) 4

theorem fourTrials_worstCost_le
    (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ) (hM : 0 < M)
    (ψ : K) (hψ : ‖ψ‖ = 1) (F : E →L[ℂ] K) (hF : F† ∘L F = 1)
    (w : L → ℕ) (B : ℝ)
    (hCost : ∀ j, j < M → ((q j).cost w : ℝ) ≤ B) :
    ((fourTrials q M hM ψ hψ F hF).worstCost w : ℝ) ≤ 4 * B := by
  exact Protocol.repeat_worstCost_le (ofCircuits q M hM ψ hψ F hF) 4 w B
    (fun j => hCost j.val j.isLt)

/-- The law of the syntax-level wrapper is the law of the same actual
primitive circuits used in the inherited trial certificate. -/
theorem fourTrials_successMass_eq
    {O : (L ⊕ Bool) → X → K →L[ℂ] K}
    (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ) (hM : 0 < M)
    (ψ : K) (hψ : ‖ψ‖ = 1) (F : E →L[ℂ] K) (hF : F† ∘L F = 1) (x : X) :
    (fourTrials q M hM ψ hψ F hF).successMass x =
      ODERepeatProbability.successProbability
        (ODERepeatProbability.probability q M ψ F x) := by
  exact Protocol.four_successMass_eq (ofCircuits q M hM ψ hψ F hF) x

/-- Operational conditional output of the actual four-trial circuit wrapper,
expressed using the original decoded primitive-circuit amplitudes. -/
theorem fourTrials_conditionalDensity_eq
    {O : (L ⊕ Bool) → X → K →L[ℂ] K}
    (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ) (hM : 0 < M)
    (ψ : K) (hψ : ‖ψ‖ = 1) (F : E →L[ℂ] K) (hF : F† ∘L F = 1) (x : X) :
    (fourTrials q M hM ψ hψ F hF).conditionalDensity x =
      ODEMixedOutput.ensemble
        (ODERepeatProbability.conditionalWeight
          (ODERepeatProbability.probability q M ψ F x))
        (fun a : Fin 4 × Fin M => ODEStateNormalization.unitDirection
          (ODERepeatProbability.decoded q ψ F x a.2.val)) := by
  exact Protocol.four_conditionalDensity_eq (ofCircuits q M hM ψ hψ F hF) x

end
end SparseHamiltonian.ODERepeatProtocol

/-! ## ODECompleteTrial -/

/-!
# Complete success and mixed-output guarantee for the actual ODE trials

The trial circuits, seed and output flag are those of the released primitive
solver. The new algorithm makes at most four fresh attempts and retains the
first successful decoded state. Classical trial labels are discarded, giving
the explicitly constructed conditional density operator below. Its error is
measured by the ordinary spectral trace distance, without a dimension factor.
-/

namespace SparseHamiltonian.ODECompleteTrial

noncomputable section
open ContinuousLinearMap OracleCircuit ODEStateNormalization
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 3000000

variable {P R X L : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [FiniteDimensional ℂ P]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
  {O : (L ⊕ Bool) → X → R →L[ℂ] R}

/-- Success-conditioned weights of the actual four-attempt algorithm. -/
def outputWeights (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ)
    (ψ : R) (F : P →L[ℂ] R) (x : X) : Fin 4 × Fin M → ℝ :=
  ODERepeatProbability.conditionalWeight (ODERepeatProbability.probability q M ψ F x)

/-- Decoded branch states. Zero-probability branches are harmless: their
total definition is the zero vector and they have zero conditional weight. -/
def outputVectors (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ)
    (ψ : R) (F : P →L[ℂ] R) (x : X) (a : Fin 4 × Fin M) : P :=
  unitDirection (ODERepeatProbability.decoded q ψ F x a.2.val)

/-- The actual mixed output when both classical labels are discarded after
conditioning on a successful herald. -/
def outputDensity (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ)
    (ψ : R) (F : P →L[ℂ] R) (x : X) : P →L[ℂ] P :=
  ODEMixedOutput.ensemble (outputWeights q M ψ F x) (outputVectors q M ψ F x)

/-- Conditioning uses the proved Born weights; positive weight forces a
nonzero decoded vector. The phase in the original certificate disappears in
its rank-one density operator, so mixing successful trials loses no accuracy. -/
theorem conditional_mixed_output
    {q : ℕ → MultiOracleCircuit.Program O} {M : ℕ}
    {ψ : R} {F : P →L[ℂ] R} {x : X} {target : P}
    {s Θ ell g ε : ℝ}
    (hUnitary : ∀ j, IsUnitary ((q j).eval x))
    (hε : 0 ≤ ε) (hTarget : target ≠ 0)
    (hCert : ODEPrimitiveSourceJoin.TrialCertificate q M ψ F x target s Θ ell g
      (ε / 500)) :
    ODEMixedOutput.IsDensity (outputDensity q M ψ F x) ∧
      ∃ h : (outputDensity q M ψ F x -
          ODEMixedOutput.pureOperator (unitDirection target)).toLinearMap.IsSymmetric,
        ODEMixedOutput.hermitianTraceDistance (outputDensity q M ψ F x)
          (ODEMixedOutput.pureOperator (unitDirection target)) h ≤ ε := by
  let p := ODERepeatProbability.probability q M ψ F x
  have hMean := ODERepeatProbability.certified_mean_bounds
    q M ψ F x target s Θ ell g (ε / 500) hUnitary hCert
  have hw : ∀ a, 0 ≤ outputWeights q M ψ F x a :=
    ODERepeatProbability.conditionalWeight_nonneg p
      (ODERepeatProbability.probability_nonneg q M ψ F x) hMean.1 hMean.2
  have hsum : (∑ a, outputWeights q M ψ F x a) = 1 :=
    ODERepeatProbability.conditionalWeight_sum p hMean.1 hMean.2
  have hunit : ∀ a, outputWeights q M ψ F x a ≠ 0 →
      ‖outputVectors q M ψ F x a‖ = 1 := by
    intro a ha
    exact unitDirection_norm _
      (ODERepeatProbability.conditionalWeight_decoded_ne_zero q M ψ F x a ha)
  have hclose : ∀ a, outputWeights q M ψ F x a ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • outputVectors q M ψ F x a - unitDirection target‖ ≤ ε / 500 := by
    intro a ha
    exact hCert.direction_error a.2.val a.2.isLt
      (ODERepeatProbability.conditionalWeight_decoded_ne_zero q M ψ F x a ha)
  obtain ⟨hDensity, hSymm, hDistance⟩ :=
    ODEMixedOutput.ensemble_trace_distance_le
      (outputWeights q M ψ F x) (outputVectors q M ψ F x)
      (unitDirection target) (ε / 500) hw hsum hunit
      (unitDirection_norm target hTarget) hclose
  refine ⟨hDensity, hSymm, hDistance.trans ?_⟩
  linarith

/-- The implemented wrapper. Its circuit, cutoff, seed and decoder are all
public. The certificate argument supplies proofs that those public data are
well formed; proof irrelevance prevents it from changing the program. -/
def algorithm
    {q : ℕ → MultiOracleCircuit.Program O} {M : ℕ}
    {ψ : R} {F : P →L[ℂ] R} {x : X} {target : P}
    {s Θ ell g ε : ℝ}
    (hCert : ODEPrimitiveSourceJoin.TrialCertificate q M ψ F x target s Θ ell g
      (ε / 500)) : ODERepeatProtocol.Protocol O P :=
  ODERepeatProtocol.fourTrials q M hCert.cutoff_pos ψ hCert.seed_unit
    F hCert.output_isometry

omit [FiniteDimensional ℂ P] in
/-- Certificates for different unknown inputs and targets give the same
public protocol whenever the circuit family, cutoff, seed and flag agree.
Thus the upgrade preserves the uniform quantifier order of the solver. -/
theorem algorithm_uniform
    {q : ℕ → MultiOracleCircuit.Program O} {M : ℕ}
    {ψ : R} {F : P →L[ℂ] R} {x₁ x₂ : X} {target₁ target₂ : P}
    {s₁ Θ₁ ell₁ g₁ ε₁ s₂ Θ₂ ell₂ g₂ ε₂ : ℝ}
    (h₁ : ODEPrimitiveSourceJoin.TrialCertificate q M ψ F x₁ target₁
      s₁ Θ₁ ell₁ g₁ (ε₁ / 500))
    (h₂ : ODEPrimitiveSourceJoin.TrialCertificate q M ψ F x₂ target₂
      s₂ Θ₂ ell₂ g₂ (ε₂ / 500)) :
    algorithm h₁ = algorithm h₂ := rfl

omit [FiniteDimensional ℂ P] in
/-- The recursive instrument semantics and the explicit first-success
ensemble describe the same conditional output of the bounded algorithm. -/
theorem algorithm_output_eq
    {q : ℕ → MultiOracleCircuit.Program O} {M : ℕ}
    {ψ : R} {F : P →L[ℂ] R} {x : X} {target : P}
    {s Θ ell g ε : ℝ}
    (hCert : ODEPrimitiveSourceJoin.TrialCertificate q M ψ F x target s Θ ell g
      (ε / 500)) :
    (algorithm hCert).conditionalDensity x = outputDensity q M ψ F x := by
  exact ODERepeatProtocol.fourTrials_conditionalDensity_eq
    q M hCert.cutoff_pos ψ hCert.seed_unit F hCert.output_isometry x

/-- Complete operational guarantee for the concrete four-attempt protocol.
The count is a worst-case bound over all histories, including four failures.
The conditional output is the positive trace-one operator obtained from the
recursive herald instrument, not a selected successful vector. -/
structure Certificate (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ)
    (ψ : R) (F : P →L[ℂ] R) (x : X) (target : P)
    (s Θ ell g ε : ℝ) : Prop where
  trial : ODEPrimitiveSourceJoin.TrialCertificate q M ψ F x target s Θ ell g (ε / 500)
  unitary_trials : ∀ j, IsUnitary ((q j).eval x)
  success_lower : (175 : ℝ) / 256 ≤ (algorithm trial).successMass x
  success_two_thirds : (2 : ℝ) / 3 ≤ (algorithm trial).successMass x
  matrix_queries :
    ((algorithm trial).worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
      1274019840 * g * ImprovedODEQueryBudget.queryShape s Θ ell
  source_queries : ∀ b : Bool,
    ((algorithm trial).worstCost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤ 40 * g
  total_source_queries :
    ((algorithm trial).worstCost ODESourceQueryBudget.sourceTotalWeight : ℝ) ≤ 80 * g
  output_eq_mixture :
    (algorithm trial).conditionalDensity x = outputDensity q M ψ F x
  output_density : ODEMixedOutput.IsDensity ((algorithm trial).conditionalDensity x)
  conditional_error :
    ∃ h : ((algorithm trial).conditionalDensity x -
        ODEMixedOutput.pureOperator (unitDirection target)).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance ((algorithm trial).conditionalDensity x)
        (ODEMixedOutput.pureOperator (unitDirection target)) h ≤ ε

/-- All added obligations are proved from the released trial certificate,
the actual circuit unitaries and the nonzero target. No new algorithmic
success, approximation, or query-bound hypothesis is introduced. -/
theorem of_trialCertificate
    {q : ℕ → MultiOracleCircuit.Program O} {M : ℕ}
    {ψ : R} {F : P →L[ℂ] R} {x : X} {target : P}
    {s Θ ell g ε : ℝ}
    (hUnitary : ∀ j, IsUnitary ((q j).eval x))
    (hε : 0 ≤ ε) (hTarget : target ≠ 0)
    (hCert : ODEPrimitiveSourceJoin.TrialCertificate q M ψ F x target s Θ ell g
      (ε / 500)) :
    Certificate q M ψ F x target s Θ ell g ε := by
  have hMean := ODERepeatProbability.certified_mean_bounds
    q M ψ F x target s Θ ell g (ε / 500) hUnitary hCert
  have hSuccess : (algorithm hCert).successMass x =
      ODERepeatProbability.successProbability
        (ODERepeatProbability.probability q M ψ F x) :=
    ODERepeatProtocol.fourTrials_successMass_eq
      q M hCert.cutoff_pos ψ hCert.seed_unit F hCert.output_isometry x
  have hOutput := algorithm_output_eq hCert
  have hMixed := conditional_mixed_output hUnitary hε hTarget hCert
  have hOperational :
      ODEMixedOutput.IsDensity ((algorithm hCert).conditionalDensity x) ∧
        ∃ h : ((algorithm hCert).conditionalDensity x -
            ODEMixedOutput.pureOperator (unitDirection target)).toLinearMap.IsSymmetric,
          ODEMixedOutput.hermitianTraceDistance ((algorithm hCert).conditionalDensity x)
            (ODEMixedOutput.pureOperator (unitDirection target)) h ≤ ε := by
    rw [hOutput]
    exact hMixed
  refine
    { trial := hCert
      unitary_trials := hUnitary
      success_lower := ?_
      success_two_thirds := ?_
      matrix_queries := ?_
      source_queries := ?_
      total_source_queries := ?_
      output_eq_mixture := hOutput
      output_density := hOperational.1
      conditional_error := hOperational.2 }
  · rw [hSuccess]
    exact ODERepeatProbability.successProbability_lower _ hMean.1 hMean.2
  · rw [hSuccess]
    exact ODERepeatProbability.successProbability_two_thirds _ hMean.1 hMean.2
  · have h := ODERepeatProtocol.fourTrials_worstCost_le
      q M hCert.cutoff_pos ψ hCert.seed_unit F hCert.output_isometry
      (ODESourceQueryBudget.matrixWeight (fun _ => 1))
      (318504960 * g * ImprovedODEQueryBudget.queryShape s Θ ell) hCert.matrix_queries
    calc
      _ ≤ 4 * (318504960 * g * ImprovedODEQueryBudget.queryShape s Θ ell) := h
      _ = 1274019840 * g * ImprovedODEQueryBudget.queryShape s Θ ell := by ring
  · intro b
    have h := ODERepeatProtocol.fourTrials_worstCost_le
      q M hCert.cutoff_pos ψ hCert.seed_unit F hCert.output_isometry
      (ODESourceQueryBudget.sourceWeight b) (10 * g)
      (fun j hj => hCert.source_queries j hj b)
    calc
      _ ≤ 4 * (10 * g) := h
      _ = 40 * g := by ring
  · have h := ODERepeatProtocol.fourTrials_worstCost_le
      q M hCert.cutoff_pos ψ hCert.seed_unit F hCert.output_isometry
      ODESourceQueryBudget.sourceTotalWeight (20 * g) hCert.total_source_queries
    calc
      _ ≤ 4 * (20 * g) := h
      _ = 80 * g := by ring

/-- Every completed history obeys the matrix-query budget, regardless of
whether it terminates at a successful herald or after the fourth failure. -/
theorem history_matrix_queries
    {q : ℕ → MultiOracleCircuit.Program O} {M : ℕ}
    {ψ : R} {F : P →L[ℂ] R} {x : X} {target : P}
    {s Θ ell g ε : ℝ}
    (h : Certificate q M ψ F x target s Θ ell g ε)
    (a : ODERepeatProtocol.Protocol.History (algorithm h.trial)) :
    (a.cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
      1274019840 * g * ImprovedODEQueryBudget.queryShape s Θ ell := by
  exact (Nat.cast_le.mpr (a.cost_le_worstCost _)).trans h.matrix_queries

/-- The same history-wise bound includes both forward and inverse calls to
each supplied controlled source-preparation interface. -/
theorem history_source_queries
    {q : ℕ → MultiOracleCircuit.Program O} {M : ℕ}
    {ψ : R} {F : P →L[ℂ] R} {x : X} {target : P}
    {s Θ ell g ε : ℝ}
    (h : Certificate q M ψ F x target s Θ ell g ε)
    (a : ODERepeatProtocol.Protocol.History (algorithm h.trial)) (b : Bool) :
    (a.cost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤ 40 * g := by
  exact (Nat.cast_le.mpr (a.cost_le_worstCost _)).trans (h.source_queries b)

end
end SparseHamiltonian.ODECompleteTrial

/-! ## ODECompleteEndpoint -/

/-!
# Complete bounded-trial sparse ODE solver

The released constant-coefficient solver supplies one uniform family of
amplified trial circuits.  This extension performs four independent attempts,
retaining the first successful output, and proves the complete heralded
mixed-output guarantee.  The selected family, input seed, output flag and
query schedule depend only on the public promise data.  Matrix inputs and
both source directions remain universally quantified afterwards.

The primitive oracle interfaces and their source controls are exactly those
of the released solver.  The only new wrapper is bounded repetition: at most
four original trials are used, with no additional oracle calls for selecting
or reporting the successful output.
-/

namespace SparseHamiltonian.ODECompleteEndpoint

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- One zero-energy family, with the existential placed before every unknown
input and source vector.  The seed and output embedding use public norms. -/
def ZeroEnergyOutcome (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
    ∃ q : ℕ → MultiOracleCircuit.Program (ODEDegenerateSource.oracle (L := Query) J₀ Jb),
      (∀ j y, IsUnitary ((q j).eval y)) ∧
      (∀ j w, (q j).cost (ODESourceQueryBudget.matrixWeight w) = 0) ∧
      ∀ (x : X) (v b : EuclideanSpace ℂ n), ‖v‖ = r₀ → ‖b‖ = rb →
        (v ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection v) →
        (b ≠ 0 → Jb x seed = ODEStateNormalization.unitDirection b) →
        ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 →
        r₀ + T * rb ≤
          g * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ →
        ODECompleteTrial.Certificate q
          (ODEGroverAverage.chosenIterations g)
          (ODEDegenerateSource.publicSeed r₀ rb T seed)
          (ODEDegenerateSource.publicOutput (P := EuclideanSpace ℂ n) r₀ rb T)
          x (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T)
          (s : ℝ) (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
          (ImprovedODEQueryBudget.logBudget g ε) g ε

/-- One initial-source query family, uniformly correct for all valid zero-time
ODE targets.  This case needs no norm promise or forcing-oracle promise. -/
def ZeroTimeOutcome (D : Data X n Z s) (etaH etaD g ε : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
    ∃ q : ℕ → MultiOracleCircuit.Program (ODESourceQueryBudget.oracle
      (ODEMainEndpoint.unusedMatrixOracle (X := X) (n := n))
      (ODEZeroTime.sourceFamily J₀ Jb)),
      (∀ j y, IsUnitary ((q j).eval y)) ∧
      (∀ j, (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = 0) ∧
      (∀ j, (q j).cost (ODESourceQueryBudget.sourceWeight true) = 0) ∧
      (∀ j x, ODEHeraldedSuccess.successProbability
        (1 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) ((q j).eval x) seed = 1) ∧
      ∀ (x : X) (v b : EuclideanSpace ℂ n),
        (v ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection v) →
        ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b 0 ≠ 0 →
        ODECompleteTrial.Certificate q 1 seed
          (1 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
          x (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b 0)
          (s : ℝ) (ImprovedODEQueryBudget.theta (0 * etaH) (0 * etaD) g ε)
          (ImprovedODEQueryBudget.logBudget g ε) g ε

-- The native workspace is a nested finite direct sum.  Use the enlarged
-- elaboration limits used for the released
-- `ODEUniformPositiveEndpoint.Outcome`, with additional instance budget for
-- the complete mixed-output certificate.
set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 4096 in
set_option maxHeartbeats 3000000 in
/-- One physical schedule, encoding, seed, flag and trial family work for
every matrix input and every pair of source directions of the supplied norms.
The full primitive certificate is under the universal quantifiers. -/
def PositiveOutcome (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (Tslots d : ℕ)
    (E : ODEFinalNativeSource.SourceSpace
        (Fin (ODEPublicGaussianEndpoint.gridSize D T g ε) ⊕ Bool) n
        (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε)) →L[ℂ]
      ODEFinalNativeSource.MatrixSpace
        (Fin (ODEPublicGaussianEndpoint.gridSize D T g ε) ⊕ Bool) n Z
        (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε)) Tslots d)
    (q : ℕ → MultiOracleCircuit.Program
      (ODEFinalNativeSource.physicalOracle
        (ι := Fin (ODEPublicGaussianEndpoint.gridSize D T g ε) ⊕ Bool)
        D (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε))
        Tslots d J₀ Jb)),
    (∀ j y, IsUnitary ((q j).eval y)) ∧
      ∀ (v b : EuclideanSpace ℂ n) (x : X),
        ‖v‖ = r₀ → ‖b‖ = rb →
        (v ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection v) →
        (b ≠ 0 → Jb x seed = ODEStateNormalization.unitDirection b) →
        ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 →
        r₀ + T * rb ≤
          g * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ →
        ODECompleteTrial.Certificate q (ODEGroverAverage.chosenIterations g)
          (ODEFinalNativeSource.input D (Sum.inr false)
            (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε))
            Tslots d (ODECompiledSource.seed E
              (ODESourcePublicNorms.publicCoefficients r₀ rb T
                (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε))
                (ODECoefficientPadding.paddedCoefficient
                  (ODEPublicGaussianEndpoint.coefficients D T g ε) 3)) seed))
          (ODEFinalNativeSource.input D (Sum.inr false)
            (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε))
            Tslots d ∘L ODECompiledSource.output E
              (ODESourcePublicNorms.publicCoefficients r₀ rb T
                (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε))
                (ODECoefficientPadding.paddedCoefficient
                  (ODEPublicGaussianEndpoint.coefficients D T g ε) 3)))
          x (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T)
          (s : ℝ) (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
          (ImprovedODEQueryBudget.logBudget g ε) g ε

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- Upgrade the zero-time branch without changing its source-only circuit.
In particular its matrix and forcing counts remain zero, and every trial
already succeeds with probability one. -/
theorem of_zero_time (D : Data X n Z s) (etaH etaD g ε : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (hε : 0 ≤ ε)
    (h : ODEUniformBoundary.ZeroTimeOutcome D etaH etaD g ε J₀ Jb seed) :
    ZeroTimeOutcome D etaH etaD g ε J₀ Jb seed := by
  rcases h with ⟨q, hUnitary, hMatrix, hForcing, hSuccess, hCorrect⟩
  refine ⟨q, hUnitary, hMatrix, hForcing, hSuccess, ?_⟩
  intro x v b hInitial hTarget
  exact ODECompleteTrial.of_trialCertificate (fun j => hUnitary j x)
    hε hTarget (hCorrect x v b hInitial hTarget)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- Upgrade the zero-energy branch while retaining its zero matrix-query
cost, including the branch whose nonzero-solution promise is empty. -/
theorem of_zero_energy (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (hε : 0 ≤ ε)
    (h : ODEUniformBoundary.ZeroEnergyOutcome D etaH etaD T g ε r₀ rb J₀ Jb seed) :
    ZeroEnergyOutcome D etaH etaD T g ε r₀ rb J₀ Jb seed := by
  rcases h with ⟨q, hUnitary, hMatrix, hCorrect⟩
  refine ⟨q, hUnitary, hMatrix, ?_⟩
  intro x v b hv hb hInitial hForcing hTarget hBudget
  exact ODECompleteTrial.of_trialCertificate (fun j => hUnitary j x)
    hε hTarget (hCorrect x v b hv hb hInitial hForcing hTarget hBudget)

set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 4096 in
set_option maxHeartbeats 3000000 in
/-- Upgrade the positive-time branch using exactly the native sparse and
source oracle families supplied by the released physical construction. -/
theorem of_positive (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (hε : 0 ≤ ε)
    (h : ODEUniformPositiveEndpoint.Outcome D etaH etaD T g ε r₀ rb J₀ Jb seed) :
    PositiveOutcome D etaH etaD T g ε r₀ rb J₀ Jb seed := by
  rcases h with ⟨Tslots, d, E, q, hUnitary, hCorrect⟩
  refine ⟨Tslots, d, E, q, hUnitary, ?_⟩
  intro v b x hv hb hInitial hForcing hTarget hBudget
  exact ODECompleteTrial.of_trialCertificate (fun j => hUnitary j x)
    hε hTarget (hCorrect v b x hv hb hInitial hForcing hTarget hBudget)

/-- A concrete circuit family for each public parameter case.  Every valid
instance has heralded success probability at least `2/3`, conditional mixed
output within trace distance `ε` of its normalised actual ODE solution, and
worst-case primitive query counts at most four times the released per-trial
counts.  The circuit family is selected before the unknown input and source
vectors. -/
def Outcome (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  (T = 0 ∧ ZeroTimeOutcome D etaH etaD g ε J₀ Jb seed) ∨
    (0 < T ∧ etaH + ImprovedODEQueryBudget.radius g ε * etaD = 0 ∧
      ZeroEnergyOutcome D etaH etaD T g ε r₀ rb J₀ Jb seed) ∨
    (0 < T ∧ 0 < etaH + ImprovedODEQueryBudget.radius g ε * etaD ∧
      PositiveOutcome D etaH etaD T g ε r₀ rb J₀ Jb seed)

/-- Uniform conversion retains the public branch decision and the order of
all existential and universal quantifiers. -/
theorem of_outcome (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (hε : 0 ≤ ε)
    (h : ImprovedSparseODE.Outcome D etaH etaD T g ε r₀ rb J₀ Jb seed) :
    Outcome D etaH etaD T g ε r₀ rb J₀ Jb seed := by
  rcases h with ⟨hT, hZero⟩ | ⟨hT, hEnergy, hZero⟩ | ⟨hT, hEnergy, hPositive⟩
  · exact Or.inl ⟨hT, of_zero_time D etaH etaD g ε J₀ Jb seed hε hZero⟩
  · exact Or.inr (Or.inl ⟨hT, hEnergy,
      of_zero_energy D etaH etaD T g ε r₀ rb J₀ Jb seed hε hZero⟩)
  · exact Or.inr (Or.inr ⟨hT, hEnergy,
      of_positive D etaH etaD T g ε r₀ rb J₀ Jb seed hε hPositive⟩)

set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 2000000 in
/-- Complete constant-coefficient sparse ODE solution preparation from the
same promises as the released solver.  This theorem adds no implementation,
correctness, success or mixed-state assumptions.  Four bounded independent
attempts give success at least `2/3`; conditioning on their heralded success
and forgetting the classical attempt labels gives trace distance at most
`ε` from the normalised actual solution.  The worst-case matrix-query count
is at most `1274019840 * g * queryShape`, and each source interface is called
at most `40 * g` times. -/
theorem solver_of_nonempty_promise (D : Data X n Z s)
    (etaH etaD T g ε r₀ rb : ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T)
    (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (x : X) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1)
    (hPromise : ∃ (x : X) (v b : EuclideanSpace ℂ n),
      ‖v‖ = r₀ ∧ ‖b‖ = rb ∧
      ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 ∧
      (r₀ + T * rb) /
        ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ ≤ g) :
    Outcome D etaH etaD T g ε r₀ rb J₀ Jb seed := by
  apply of_outcome D etaH etaD T g ε r₀ rb J₀ Jb seed hε.le
  exact ImprovedSparseODE.solver_of_nonempty_promise D etaH etaD T g ε r₀ rb
    hH hDiss hT hε hεHalf hrH hcH hrD hcD hPSD J₀ Jb hJ₀ hJb seed hSeed hPromise

set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 2000000 in
/-- Manuscript-facing witness form of the complete guarantee.  The supplied
witness certifies only the nonemptiness of the public promise class; the
conclusion remains uniform over every admissible matrix and both sources. -/
theorem solver (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T)
    (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (x : X) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1)
    (x : X) (v b : EuclideanSpace ℂ n) (hv : ‖v‖ = r₀) (hb : ‖b‖ = rb)
    (hTarget : ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0)
    (hBudget : (r₀ + T * rb) /
      ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ ≤ g) :
    Outcome D etaH etaD T g ε r₀ rb J₀ Jb seed := by
  exact solver_of_nonempty_promise D etaH etaD T g ε r₀ rb
    hH hDiss hT hε hεHalf hrH hcH hrD hcD hPSD J₀ Jb hJ₀ hJb seed hSeed
    ⟨x, v, b, hv, hb, hTarget, hBudget⟩

end
end SparseHamiltonian.ODECompleteEndpoint




