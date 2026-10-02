import SparseHamiltonian.ODEConstantForcing

/-!
# The Hermitian Hamiltonians used in the LCHS reduction for linear ODEs

For an arbitrary bounded complex operator `M`, this file constructs its
decomposition `M = L + i H` into two self-adjoint operators.  The LCHS
Hamiltonian `k L + H` is obtained by compressing a phase conjugate of the
Hermitian dilation of `M`, with normalization `sqrt (1 + k^2)`.

These are exact operator identities and norm estimates.  In particular, this
file does not assume a locator for the union of the supports of `M` and `M†`,
and makes no claim yet about implementing coherent selection with sparse
oracle queries.  The Hermitian-part identity is the one used by
Pocrnic--Johnson--Katabarwa--Wiebe and by Low--Somma for LCHS block encodings.
-/

namespace SparseHamiltonian.ODEHermitianReduction

noncomputable section
open ContinuousLinearMap OracleCircuit HermitianDilation
open scoped ComplexConjugate InnerProduct
set_option maxHeartbeats 1000000

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The self-adjoint real part of the ODE generator. -/
def dissipativePart (M : K →L[ℂ] K) : K →L[ℂ] K := hermitianPart M

/-- The self-adjoint imaginary part of the ODE generator. -/
def hamiltonianPart (M : K →L[ℂ] K) : K →L[ℂ] K :=
  (-Complex.I / 2) • (M - M†)

/-- Taking the Hermitian part always produces a self-adjoint operator. -/
theorem hermitianPart_selfAdjoint (M : K →L[ℂ] K) :
    (hermitianPart M)† = hermitianPart M := by
  simp only [hermitianPart, map_smulₛₗ, map_add, adjoint_adjoint]
  simp only [map_inv₀, map_ofNat]
  rw [add_comm]

/-- The real part is self-adjoint; positivity is a separate dissipativity promise. -/
theorem dissipativePart_selfAdjoint (M : K →L[ℂ] K) :
    (dissipativePart M)† = dissipativePart M :=
  hermitianPart_selfAdjoint M

/-- Only the self-adjoint real part contributes to real quadratic forms. -/
theorem real_inner_dissipativePart (M : K →L[ℂ] K) (v : K) :
    (inner ℂ v (dissipativePart M v)).re = (inner ℂ v (M v)).re := by
  have hs : (inner ℂ (M v) v).re = (inner ℂ v (M v)).re :=
    inner_re_symm (𝕜 := ℂ) (M v) v
  simp only [dissipativePart, hermitianPart, smul_apply, add_apply,
    inner_smul_right, inner_add_right, adjoint_inner_right]
  norm_num [Complex.mul_re, Complex.add_re, hs]
  ring

/-- Positivity of the Hermitian real part is precisely the sign needed for
contractive evolution with generator `-M`. -/
theorem negative_generator_dissipative (M : K →L[ℂ] K)
    (hM : ∀ v : K, 0 ≤ (inner ℂ v (dissipativePart M v)).re) :
    ∀ v : K, (inner ℂ v ((-M) v)).re ≤ 0 := by
  intro v
  have h := hM v
  rw [real_inner_dissipativePart] at h
  simpa only [neg_apply, inner_neg_right, Complex.neg_re] using neg_nonpos.mpr h

/-- The imaginary part is self-adjoint without any promise on `M`. -/
theorem hamiltonianPart_selfAdjoint (M : K →L[ℂ] K) :
    (hamiltonianPart M)† = hamiltonianPart M := by
  simp only [hamiltonianPart, map_smulₛₗ, map_sub, adjoint_adjoint,
    map_div₀, map_neg, Complex.conj_I, map_ofNat]
  module

/-- The decomposition recovers the original, potentially nonnormal operator. -/
theorem decomposition (M : K →L[ℂ] K) :
    dissipativePart M + Complex.I • hamiltonianPart M = M := by
  have hI : Complex.I * (-Complex.I / 2) = (2 : ℂ)⁻¹ := by
    rw [← mul_div_assoc, mul_neg, Complex.I_mul_I]
    norm_num
  simp only [dissipativePart, hermitianPart, hamiltonianPart, smul_smul, hI]
  module

/-- The Hermitian part is a contraction in the operator norm. -/
theorem norm_hermitianPart_le (M : K →L[ℂ] K) : ‖hermitianPart M‖ ≤ ‖M‖ := by
  simpa using hermitianPart_error M (0 : K →L[ℂ] K) (by simp)

theorem norm_dissipativePart_le (M : K →L[ℂ] K) :
    ‖dissipativePart M‖ ≤ ‖M‖ := norm_hermitianPart_le M

/-- Multiplication by `-i` converts the imaginary part to a Hermitian part. -/
theorem hamiltonianPart_eq_hermitianPart (M : K →L[ℂ] K) :
    hamiltonianPart M = hermitianPart (-Complex.I • M) := by
  simp only [hamiltonianPart, hermitianPart, map_smulₛₗ, map_neg, Complex.conj_I]
  module

theorem norm_hamiltonianPart_le (M : K →L[ℂ] K) :
    ‖hamiltonianPart M‖ ≤ ‖M‖ := by
  rw [hamiltonianPart_eq_hermitianPart]
  calc
    ‖hermitianPart (-Complex.I • M)‖ ≤ ‖-Complex.I • M‖ :=
      norm_hermitianPart_le _
    _ = ‖M‖ := by rw [norm_smul, norm_neg, Complex.norm_I, one_mul]

/-- The self-adjoint Hamiltonian appearing in the LCHS integral. -/
def lchsHamiltonian (M : K →L[ℂ] K) (k : ℝ) : K →L[ℂ] K :=
  (k : ℂ) • dissipativePart M + hamiltonianPart M

theorem lchsHamiltonian_selfAdjoint (M : K →L[ℂ] K) (k : ℝ) :
    (lchsHamiltonian M k)† = lchsHamiltonian M k := by
  simp only [lchsHamiltonian, map_add, map_smulₛₗ, Complex.conj_ofReal,
    dissipativePart_selfAdjoint, hamiltonianPart_selfAdjoint]

/-- The extra LCHS normalization is independent of the input oracle. -/
def phaseScale (k : ℝ) : ℝ := Real.sqrt (1 + k ^ 2)

theorem phaseScale_pos (k : ℝ) : 0 < phaseScale k := by
  exact Real.sqrt_pos.2 (by positivity)

theorem phaseScale_ne_zero (k : ℝ) : phaseScale k ≠ 0 := ne_of_gt (phaseScale_pos k)

theorem phaseScale_sq (k : ℝ) : phaseScale k ^ 2 = 1 + k ^ 2 := by
  exact Real.sq_sqrt (by positivity)

/-- A uniform truncation radius controls every branch's time rescaling. -/
theorem phaseScale_le (k R : ℝ) (hR : 0 ≤ R) (hk : |k| ≤ R) :
    phaseScale k ≤ 1 + R := by
  have hsq : k ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg k) hR).2 hk
  nlinarith [phaseScale_sq k, le_of_lt (phaseScale_pos k)]

/-- The known phase used on the outer dilation qubit. -/
def phase (k : ℝ) : ℂ := ((k : ℂ) - Complex.I) / (phaseScale k : ℂ)

theorem phase_conj (k : ℝ) :
    conj (phase k) = ((k : ℂ) + Complex.I) / (phaseScale k : ℂ) := by
  simp [phase, sub_eq_add_neg]

/-- The phase has exactly unit modulus, including at `k = 0`. -/
theorem phase_mul_conj (k : ℝ) : phase k * conj (phase k) = 1 := by
  have hn : (phaseScale k : ℂ) ≠ 0 := by exact_mod_cast phaseScale_ne_zero k
  have hs : (phaseScale k : ℂ) ^ 2 = 1 + (k : ℂ) ^ 2 := by
    exact_mod_cast phaseScale_sq k
  rw [phase_conj, phase, div_mul_div_comm]
  apply (div_eq_one_iff_eq (mul_ne_zero hn hn)).2
  calc
    ((k : ℂ) - Complex.I) * ((k : ℂ) + Complex.I) = (k : ℂ) ^ 2 + 1 := by
      calc
        _ = (k : ℂ) ^ 2 - Complex.I ^ 2 := by ring
        _ = _ := by simp
    _ = (phaseScale k : ℂ) * (phaseScale k : ℂ) := by rw [← sq, hs]; ring

theorem phase_conj_mul (k : ℝ) : conj (phase k) * phase k = 1 := by
  rw [mul_comm, phase_mul_conj]

theorem norm_phase (k : ℝ) : ‖phase k‖ = 1 := by
  have h := congrArg norm (phase_mul_conj k)
  simp only [norm_mul, Complex.norm_conj, norm_one] at h
  nlinarith [norm_nonneg (phase k)]

/-- A fixed diagonal phase on the outer Boolean register. -/
def phaseGate (z : ℂ) : Double K →L[ℂ] Double K :=
  WeightedClock.diagonal (fun b : Bool => if b then 1 else z • 1)

omit [CompleteSpace K] in
@[simp] theorem phaseGate_apply_false (z : ℂ) (x : Double K) :
    phaseGate z x false = z • x false := by simp [phaseGate]

omit [CompleteSpace K] in
@[simp] theorem phaseGate_apply_true (z : ℂ) (x : Double K) :
    phaseGate z x true = x true := by simp [phaseGate]

theorem phaseGate_adjoint (z : ℂ) :
    (phaseGate z : Double K →L[ℂ] Double K)† = phaseGate (conj z) := by
  simp only [phaseGate, WeightedClock.diagonal_adjoint]
  congr 1
  funext b
  cases b <;> simp [map_smulₛₗ]

/-- The LCHS phase conjugation uses a legal fixed unitary. -/
theorem phaseGate_unitary (k : ℝ) :
    IsUnitary (phaseGate (phase k) : Double K →L[ℂ] Double K) := by
  change (phaseGate (K := K) (phase k))† ∘L phaseGate (K := K) (phase k) = 1 ∧
    phaseGate (K := K) (phase k) ∘L (phaseGate (K := K) (phase k))† = 1
  rw [phaseGate_adjoint]
  constructor
  · ext x b
    cases b <;> simp [smul_smul, phase_conj_mul]
  · ext x b
    cases b <;> simp [smul_smul, phase_mul_conj]

/-- Phase conjugation moves the phase into the off-diagonal dilation block. -/
theorem phase_conjugation (M : K →L[ℂ] K) (z : ℂ) :
    phaseGate z ∘L dilation M ∘L (phaseGate z)† = dilation (z • M) := by
  rw [phaseGate_adjoint]
  ext x b
  cases b <;> simp [map_smulₛₗ, map_smul]

/-- The exact Hermitian-part identity underlying the ODE reduction. -/
theorem phase_hermitianPart (M : K →L[ℂ] K) (k : ℝ) :
    hermitianPart (phase k • M) =
      (phaseScale k : ℂ)⁻¹ • lchsHamiltonian M k := by
  simp only [hermitianPart, map_smulₛₗ]
  rw [phase_conj]
  simp only [phase, lchsHamiltonian, dissipativePart, hamiltonianPart, hermitianPart]
  module

/-- Compressing the phase-conjugated dilation gives the normalized LCHS Hamiltonian. -/
theorem phase_dilation_compression (M : K →L[ℂ] K) (k : ℝ) :
    (plus : K →L[ℂ] Double K)† ∘L
        (phaseGate (phase k) ∘L dilation M ∘L (phaseGate (phase k))†) ∘L plus =
      (phaseScale k : ℂ)⁻¹ • lchsHamiltonian M k := by
  rw [phase_conjugation, plus_compression, phase_hermitianPart]

/-- Undoing the normalization gives exactly the target LCHS Hamiltonian. -/
theorem lchsHamiltonian_eq_scaled_part (M : K →L[ℂ] K) (k : ℝ) :
    lchsHamiltonian M k = (phaseScale k : ℂ) • hermitianPart (phase k • M) := by
  rw [phase_hermitianPart, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast phaseScale_ne_zero k

/-- The sharper branch bound is `sqrt (1+k^2) ‖M‖`, rather than a support-union bound. -/
theorem norm_lchsHamiltonian_le (M : K →L[ℂ] K) (k : ℝ) :
    ‖lchsHamiltonian M k‖ ≤ phaseScale k * ‖M‖ := by
  rw [lchsHamiltonian_eq_scaled_part, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (phaseScale_pos k)]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (phaseScale_pos k))
  simpa only [norm_smul, norm_phase, one_mul] using
    norm_hermitianPart_le (phase k • M)

/-- The Hermitian reduction is linear in the original generator. -/
theorem lchsHamiltonian_sub (M N : K →L[ℂ] K) (k : ℝ) :
    lchsHamiltonian (M - N) k = lchsHamiltonian M k - lchsHamiltonian N k := by
  simp only [lchsHamiltonian, dissipativePart, hermitianPart, hamiltonianPart, map_sub]
  module

/-- Errors in the generator are amplified by at most the known LCHS scale. -/
theorem lchsHamiltonian_perturbation_le (M N : K →L[ℂ] K) (k : ℝ) :
    ‖lchsHamiltonian M k - lchsHamiltonian N k‖ ≤ phaseScale k * ‖M - N‖ := by
  rw [← lchsHamiltonian_sub]
  exact norm_lchsHamiltonian_le (M - N) k

/-- A common truncation radius gives one bound for all coherently indexed branches. -/
theorem norm_lchsHamiltonian_le_radius (M : K →L[ℂ] K) (k R : ℝ)
    (hR : 0 ≤ R) (hk : |k| ≤ R) :
    ‖lchsHamiltonian M k‖ ≤ (1 + R) * ‖M‖ :=
  (norm_lchsHamiltonian_le M k).trans
    (mul_le_mul_of_nonneg_right (phaseScale_le k R hR hk) (norm_nonneg M))

end
end SparseHamiltonian.ODEHermitianReduction
