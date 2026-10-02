import SparseHamiltonian.ExitIdentity

/-!
# Coisometry of the actual Cayley public action

The two-sided inverse of the Cayley denominator gives both unitary identities.
This supplies the coisometry needed for the exit identity, including in infinite
Hilbert spaces where an isometry alone would not suffice.
-/

namespace SparseHamiltonian.CayleyTransfer

noncomputable section

section StarAlgebra

variable {𝓐 : Type*} [Ring 𝓐] [StarRing 𝓐] [Algebra ℂ 𝓐] [StarModule ℂ 𝓐]

omit [StarRing 𝓐] [StarModule ℂ 𝓐] in
/-- An inverse of the Cayley denominator commutes with its numerator. -/
theorem skew_cayley_inverse_commutes (X R : 𝓐)
    (hRight : (1 - (1 / 2 : ℂ) • X) * R = 1)
    (hLeft : R * (1 - (1 / 2 : ℂ) • X) = 1) :
    R * (1 + (1 / 2 : ℂ) • X) = (1 + (1 / 2 : ℂ) • X) * R := by
  have hComm : (1 + (1 / 2 : ℂ) • X) * (1 - (1 / 2 : ℂ) • X) =
      (1 - (1 / 2 : ℂ) • X) * (1 + (1 / 2 : ℂ) • X) := by
    noncomm_ring
    module
  calc
    R * (1 + (1 / 2 : ℂ) • X) =
        R * (1 + (1 / 2 : ℂ) • X) * ((1 - (1 / 2 : ℂ) • X) * R) := by
      rw [hRight, mul_one]
    _ = R * ((1 + (1 / 2 : ℂ) • X) * (1 - (1 / 2 : ℂ) • X)) * R := by
      simp only [mul_assoc]
    _ = R * ((1 - (1 / 2 : ℂ) • X) * (1 + (1 / 2 : ℂ) • X)) * R := by rw [hComm]
    _ = (R * (1 - (1 / 2 : ℂ) • X)) * (1 + (1 / 2 : ℂ) • X) * R := by
      simp only [mul_assoc]
    _ = (1 + (1 / 2 : ℂ) • X) * R := by rw [hLeft, one_mul]

/-- The Cayley action is a coisometry when its denominator has a two-sided
inverse.  Both inverse directions are retained as explicit hypotheses. -/
theorem skew_cayley_mul_star_self (X R : 𝓐) (hX : star X = -X)
    (hRight : (1 - (1 / 2 : ℂ) • X) * R = 1)
    (hLeft : R * (1 - (1 / 2 : ℂ) • X) = 1) :
    ((1 + (1 / 2 : ℂ) • X) * R) *
      star ((1 + (1 / 2 : ℂ) • X) * R) = 1 := by
  have hh : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num
  have hNum : star (1 + (1 / 2 : ℂ) • X) = 1 - (1 / 2 : ℂ) • X := by
    simp only [star_add, star_one, star_smul, hh, hX, smul_neg, sub_eq_add_neg]
  have hDen : star (1 - (1 / 2 : ℂ) • X) = 1 + (1 / 2 : ℂ) • X := by
    simp only [star_sub, star_one, star_smul, hh, hX, smul_neg, sub_neg_eq_add]
  have hAdj : (1 + (1 / 2 : ℂ) • X) * star R = 1 := by
    simpa only [star_mul, hDen, star_one] using congrArg star hLeft
  calc
    ((1 + (1 / 2 : ℂ) • X) * R) * star ((1 + (1 / 2 : ℂ) • X) * R) =
        (R * (1 + (1 / 2 : ℂ) • X)) * (star R * (1 - (1 / 2 : ℂ) • X)) := by
      rw [star_mul, hNum, skew_cayley_inverse_commutes X R hRight hLeft]
    _ = R * ((1 + (1 / 2 : ℂ) • X) * star R) * (1 - (1 / 2 : ℂ) • X) := by
      simp only [mul_assoc]
    _ = 1 := by rw [hAdj, mul_one, hLeft]

/-- Both unitary identities for the Cayley transform. -/
theorem skew_cayley_unitary (X R : 𝓐) (hX : star X = -X)
    (hRight : (1 - (1 / 2 : ℂ) • X) * R = 1)
    (hLeft : R * (1 - (1 / 2 : ℂ) • X) = 1) :
    star ((1 + (1 / 2 : ℂ) • X) * R) * ((1 + (1 / 2 : ℂ) • X) * R) = 1 ∧
    ((1 + (1 / 2 : ℂ) • X) * R) * star ((1 + (1 / 2 : ℂ) • X) * R) = 1 :=
  ⟨skew_cayley_star_mul_self X R hX hRight,
    skew_cayley_mul_star_self X R hX hRight hLeft⟩

/-- Real-time generators of a self-adjoint Hamiltonian are skew-adjoint. -/
theorem hamiltonian_generator_skew (w : ℝ) (H : 𝓐) (hH : star H = H) :
    star ((-(Complex.I * (w : ℂ))) • H) = -((-(Complex.I * (w : ℂ))) • H) := by
  simp [star_smul, star_mul, hH, mul_comm]

/-- Both unitary identities for the actual numerator and denominator used by
clock transduction. -/
theorem cayley_unitary (w : ℝ) (H R : 𝓐) (hH : star H = H)
    (hRight : cayleyDenominator w H * R = 1)
    (hLeft : R * cayleyDenominator w H = 1) :
    star (cayleyNumerator w H * R) * (cayleyNumerator w H * R) = 1 ∧
    (cayleyNumerator w H * R) * star (cayleyNumerator w H * R) = 1 := by
  have hDen : 1 - (1 / 2 : ℂ) • ((-(Complex.I * (w : ℂ))) • H) =
      cayleyDenominator w H := by
    dsimp only [cayleyDenominator]
    module
  have hNum : 1 + (1 / 2 : ℂ) • ((-(Complex.I * (w : ℂ))) • H) =
      cayleyNumerator w H := by
    dsimp only [cayleyNumerator]
    module
  have h := skew_cayley_unitary ((-(Complex.I * (w : ℂ))) • H) R
    (hamiltonian_generator_skew w H hH)
    (by rw [hDen]; exact hRight) (by rw [hDen]; exact hLeft)
  simpa only [hNum] using h

end StarAlgebra

section Powers

variable {𝓐 : Type*} [Monoid 𝓐] [StarMul 𝓐]

/-- Powers preserve the coisometry identity in any star monoid. -/
theorem coisometry_pow (U : 𝓐) (hU : U * star U = 1) (n : ℕ) :
    U ^ n * star (U ^ n) = 1 := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [pow_succ', star_mul]
      calc
        U * U ^ n * (star (U ^ n) * star U) = U * (U ^ n * star (U ^ n)) * star U := by
          simp only [mul_assoc]
        _ = 1 := by rw [hn, mul_one, hU]

/-- Powers preserve both unitary identities. -/
theorem unitary_pow (U : 𝓐) (hIso : star U * U = 1) (hCoiso : U * star U = 1)
    (n : ℕ) : star (U ^ n) * U ^ n = 1 ∧ U ^ n * star (U ^ n) = 1 := by
  refine ⟨?_, coisometry_pow U hCoiso n⟩
  simpa only [star_pow, star_star] using coisometry_pow (star U) (by simpa only [star_star] using hIso) n

end Powers

end
end SparseHamiltonian.CayleyTransfer
