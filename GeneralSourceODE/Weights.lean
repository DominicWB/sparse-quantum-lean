import SparseODE.ODEActualSourceError
import SparseODE.ODECompiledSource

/-!
# The supplied weight preparation on the source label

The general source interface supplies a weight-only preparation `P_w` on the
source label register,

  `P_w |0⟩ = √(r₀/B_q) |0⟩ + ∑_i √(|ω_i| r_{b,i}/B_q) |i⟩`
  (Eq. `ode:eq:source-interface-preparation`),

together with its actual adjoint. Its amplitudes may depend on the unknown
input. On the branch register `Option (Fin N) × ι` of the source-loaded LCU
(source label times LCHS label, with a data register `P` in each branch) the
preparation acts as `P_w ⊗ 1` (`act`): the label operator moves amplitude
between source labels and leaves the LCHS label and the data unchanged.

`act` is multiplicative, sends the adjoint to the adjoint and the identity to
the identity, so it preserves unitarity (`act_unitary`). Starting from the
public LCU state with all source weight on the initial label (`pointWeight`),
`P_w ⊗ 1` creates exactly the joint source/LCHS coefficient state of the
actual source mass (`act_coefficientInput`), and it carries the public output
encoding of the initial label to the output encoding of the actual
coefficients (`act_comp_coefficientOutput`). Hence a circuit that applies
`P_w` before loading and `P_w†` to the label alone after propagation decodes
the same vector as the source-correctness analysis with the actual
coefficients, while its seed, output encoding and reflections are public.

The coefficient phases `ω_i/|ω_i|` are applied by the public diagonal label
gate `phaseGate`.
-/

namespace SparseHamiltonian.GeneralSourceODE

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators InnerProduct ComplexConjugate

namespace Weights

variable {σ ι P : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- Label operators. -/
abbrev LabelOp (σ : Type*) [Fintype σ] :=
  EuclideanSpace ℂ σ →L[ℂ] EuclideanSpace ℂ σ

/-- The branch register: one data vector for every source and LCHS label. -/
abbrev Space (σ ι P : Type*) [Fintype σ] [Fintype ι] [NormedAddCommGroup P] :=
  PiLp 2 (fun _ : σ × ι => P)

/-- The matrix entry `⟨e_a, Q e_{a'}⟩`. -/
def amp (Q : LabelOp σ) (a a' : σ) : ℂ := Q (EuclideanSpace.single a' 1) a

omit [DecidableEq σ] in
/-- Every vector is the sum of its coordinates times basis vectors. -/
theorem sum_single [DecidableEq σ] (w : EuclideanSpace ℂ σ) :
    ∑ a', w a' • EuclideanSpace.single a' (1 : ℂ) = w := by
  ext b
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Coordinates of an image in terms of matrix entries. -/
theorem apply_eq_sum (Q : LabelOp σ) (w : EuclideanSpace ℂ σ) (a : σ) :
    Q w a = ∑ a', amp Q a a' * w a' := by
  conv_lhs => rw [← sum_single w]
  rw [map_sum, WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a' _
  rw [map_smul, PiLp.smul_apply, smul_eq_mul, mul_comm]
  rfl

theorem amp_mul (Q R : LabelOp σ) (a a'' : σ) :
    amp (Q * R) a a'' = ∑ a', amp Q a a' * amp R a' a'' := by
  change Q (R (EuclideanSpace.single a'' 1)) a = _
  rw [apply_eq_sum Q]
  rfl

theorem amp_one (a a' : σ) : amp (1 : LabelOp σ) a a' = if a = a' then 1 else 0 := by
  simp only [amp, one_apply_eq_self, PiLp.single_apply]

theorem amp_eq_inner (Q : LabelOp σ) (a a' : σ) :
    amp Q a a' = inner ℂ (EuclideanSpace.single a (1 : ℂ)) (Q (EuclideanSpace.single a' 1)) := by
  rw [EuclideanSpace.inner_single_left, map_one, one_mul]
  rfl

theorem amp_adjoint (Q : LabelOp σ) (a a' : σ) :
    amp (Q†) a a' = conj (amp Q a' a) := by
  rw [amp_eq_inner, amp_eq_inner, adjoint_inner_right, inner_conj_symm]

/-- The label operator on the branch register, `Q ⊗ 1`. -/
def act (Q : LabelOp σ) : Space σ ι P →L[ℂ] Space σ ι P :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : σ × ι => P)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun b : σ × ι =>
        ∑ a' : σ, amp Q b.1 a' •
          ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ × ι => P) (a', b.2)).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : σ × ι => P)).toContinuousLinearMap)

omit [CompleteSpace P] in
@[simp] theorem act_apply (Q : LabelOp σ) (f : Space σ ι P) (b : σ × ι) :
    act (ι := ι) Q f b = ∑ a', amp Q b.1 a' • f (a', b.2) := by
  simp [act, sum_apply]

omit [CompleteSpace P] in
theorem act_mul (Q R : LabelOp σ) :
    act (ι := ι) (P := P) (Q * R) = act Q * act R := by
  ext f b
  change act (Q * R) f b = act Q (act R f) b
  simp only [act_apply, amp_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

omit [CompleteSpace P] in
theorem act_one : act (ι := ι) (P := P) (1 : LabelOp σ) = 1 := by
  ext f b
  rw [act_apply]
  simp only [amp_one, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  rfl

theorem act_adjoint (Q : LabelOp σ) :
    (act (ι := ι) (P := P) Q)† = act (Q†) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [act_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, amp_adjoint,
    Complex.conj_conj]
  calc ∑ a, ∑ k, ∑ a', amp Q a' a * inner ℂ (f (a', k)) (g (a, k))
      = ∑ a, ∑ a', ∑ k, amp Q a' a * inner ℂ (f (a', k)) (g (a, k)) := by
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
    _ = ∑ a', ∑ a, ∑ k, amp Q a' a * inner ℂ (f (a', k)) (g (a, k)) := Finset.sum_comm
    _ = ∑ a', ∑ k, ∑ a, amp Q a' a * inner ℂ (f (a', k)) (g (a, k)) := by
        apply Finset.sum_congr rfl
        intro a' _
        exact Finset.sum_comm

/-- Label unitaries act unitarily on the branch register. -/
theorem act_unitary {Q : LabelOp σ} (hQ : IsUnitary Q) :
    IsUnitary (act (ι := ι) (P := P) Q) := by
  have hstar : star (act (ι := ι) (P := P) Q) = act (star Q) := by
    rw [star_eq_adjoint, star_eq_adjoint, act_adjoint]
  refine ⟨?_, ?_⟩
  · rw [hstar, ← act_mul, hQ.1, act_one]
  · rw [hstar, ← act_mul, hQ.2, act_one]

/-! ### Weights, loading and phases on the LCU coefficient states -/

/-- All source weight on the base label `a₀`. -/
def pointWeight (a₀ : σ) (a : σ) : ℝ := if a = a₀ then 1 else 0

omit [Fintype σ] in
theorem pointWeight_nonneg (a₀ a : σ) : 0 ≤ pointWeight a₀ a := by
  unfold pointWeight
  split_ifs <;> norm_num

omit [Fintype σ] in
@[simp] theorem pointWeight_self (a₀ : σ) : pointWeight a₀ a₀ = 1 := if_pos rfl

theorem pointWeight_sum (a₀ : σ) : ∑ a, pointWeight a₀ a = 1 := by
  simp [pointWeight]

/-- A positive real factor does not change the coefficient phase. -/
theorem coefficientPhase_real_mul (r : ℝ) (hr : 0 < r) (z : ℂ) :
    ODECoherentLCU.coefficientPhase ((r : ℂ) * z) = ODECoherentLCU.coefficientPhase z := by
  by_cases hz : z = 0
  · simp [hz]
  · have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hrz : (r : ℂ) * z ≠ 0 := mul_ne_zero hr0 hz
    have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
    simp only [ODECoherentLCU.coefficientPhase, if_neg hz, if_neg hrz, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    push_cast
    field_simp

omit [DecidableEq σ] in
/-- The coefficient probabilities of a product table with a probability
weight. -/
theorem probability_product (w : σ → ℝ) (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1)
    (c : ι → ℂ) (b : σ × ι) :
    ODECoherentLCU.coefficientProbability (ODESourceCoefficients.productCoeff w c) b =
      w b.1 * ODECoherentLCU.coefficientProbability c b.2 := by
  unfold ODECoherentLCU.coefficientProbability
  rw [ODESourceCoefficients.coefficientMass_normalized w c hw hsum]
  simp only [ODESourceCoefficients.productCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hw _)]
  ring

omit [CompleteSpace P] in
/-- `P_w ⊗ 1` turns the public coefficient state of the base label into the
coefficient state of the actual source weights. -/
theorem act_coefficientInput (Q : LabelOp σ) (a₀ : σ) (π : σ → ℝ) (hπ : ∀ a, 0 ≤ π a)
    (hπsum : ∑ a, π a = 1) (hQ : ∀ a, amp Q a a₀ = (Real.sqrt (π a) : ℂ)) (c : ι → ℂ)
    (v : P) :
    act (ι := ι) Q (ODEJointLCU.coefficientInput
        (ODESourceCoefficients.productCoeff (pointWeight a₀) c) v) =
      ODEJointLCU.coefficientInput (ODESourceCoefficients.productCoeff π c) v := by
  ext b
  rw [act_apply]
  simp only [ODEJointLCU.coefficientInput, ODECoherentLCU.inputEmbedding,
    WeightedClock.boundary_apply, one_apply_eq_self]
  simp only [probability_product (pointWeight a₀) (pointWeight_nonneg a₀)
    (pointWeight_sum a₀), probability_product π hπ hπsum, pointWeight, ite_mul, one_mul,
    zero_mul, smul_smul]
  rw [Finset.sum_eq_single a₀]
  · simp only [if_true, hQ, Real.sqrt_mul (hπ _)]
    push_cast
    ring_nf
  · intro a' _ ha'
    simp [ha']
  · simp

omit [CompleteSpace P] in
/-- `P_w ⊗ 1` carries the public output encoding of the base label to the
output encoding of the actual source weights. -/
theorem act_comp_coefficientOutput (Q : LabelOp σ) (a₀ : σ) (π : σ → ℝ)
    (hπ : ∀ a, 0 ≤ π a) (hπsum : ∑ a, π a = 1)
    (hQ : ∀ a, amp Q a a₀ = (Real.sqrt (π a) : ℂ)) (c : ι → ℂ) :
    act (ι := ι) (P := P) Q ∘L ODEJointLCU.coefficientOutput
        (ODESourceCoefficients.productCoeff (pointWeight a₀) c) =
      ODEJointLCU.coefficientOutput (ODESourceCoefficients.productCoeff π c) := by
  ext v b
  rw [comp_apply, act_apply]
  simp only [ODEJointLCU.coefficientOutput, ODECoherentLCU.outputEmbedding,
    WeightedClock.boundary_apply, smul_apply, one_apply_eq_self]
  simp only [probability_product (pointWeight a₀) (pointWeight_nonneg a₀)
    (pointWeight_sum a₀), probability_product π hπ hπsum, smul_smul]
  rw [Finset.sum_eq_single a₀]
  · simp only [pointWeight, if_true, one_mul, hQ, Real.sqrt_mul (hπ _)]
    rcases (hπ b.1).eq_or_lt with h0 | hpos
    · rw [← h0]
      simp
    · simp only [ODESourceCoefficients.productCoeff, pointWeight_self, Complex.ofReal_one,
        one_mul, coefficientPhase_real_mul (π b.1) hpos]
      push_cast
      ring_nf
  · intro a' _ ha'
    simp [pointWeight, ha']
  · simp

/-- The supplied label-controlled loader: `J a` on every branch of source label `a`. -/
def loader (J : σ → P →L[ℂ] P) : Space σ ι P →L[ℂ] Space σ ι P :=
  WeightedClock.diagonal (fun b : σ × ι => J b.1)

omit [DecidableEq σ] in
theorem loader_unitary (J : σ → P →L[ℂ] P) (hJ : ∀ a, IsUnitary (J a)) :
    IsUnitary (loader (ι := ι) J) :=
  CoherentQuerySchedule.diagonal_unitary _ (fun b => hJ b.1)

/-- Public label phases. -/
def phaseGate (φ : σ → ℂ) : Space σ ι P →L[ℂ] Space σ ι P :=
  WeightedClock.diagonal (fun b : σ × ι => φ b.1 • (1 : P →L[ℂ] P))

omit [DecidableEq σ] in
theorem phaseGate_unitary (φ : σ → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) :
    IsUnitary (phaseGate (ι := ι) (P := P) φ) := by
  apply CoherentQuerySchedule.diagonal_unitary
  intro b
  have hc : (starRingEnd ℂ) (φ b.1) * φ b.1 = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hφ]
    norm_num
  have hc' : φ b.1 * (starRingEnd ℂ) (φ b.1) = 1 := by rw [mul_comm]; exact hc
  constructor
  · rw [star_smul, star_one, smul_mul_smul_comm, mul_one]
    change (star (φ b.1) * φ b.1) • (1 : P →L[ℂ] P) = 1
    rw [show star (φ b.1) = (starRingEnd ℂ) (φ b.1) from rfl, hc, one_smul]
  · rw [star_smul, star_one, smul_mul_smul_comm, mul_one]
    change (φ b.1 * star (φ b.1)) • (1 : P →L[ℂ] P) = 1
    rw [show star (φ b.1) = (starRingEnd ℂ) (φ b.1) from rfl, hc', one_smul]

omit [DecidableEq σ] [CompleteSpace P] in
/-- Loading and phases after the weight preparation give the source-loaded
coefficient state with phased preparations. -/
theorem phase_loader_coefficientInput (φ : σ → ℂ) (J : σ → P →L[ℂ] P) (d : σ × ι → ℂ)
    (v : P) :
    phaseGate (ι := ι) φ (loader J (ODEJointLCU.coefficientInput d v)) =
      ODECoherentLCU.inputEmbedding d (fun b => φ b.1 • J b.1) v := by
  ext b
  simp only [phaseGate, loader, ODEJointLCU.coefficientInput, ODECoherentLCU.inputEmbedding,
    WeightedClock.diagonal_apply, WeightedClock.boundary_apply, smul_apply,
    one_apply_eq_self, map_smul]

end Weights

end

end SparseHamiltonian.GeneralSourceODE
