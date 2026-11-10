import GateOptimalPrecision.LocalFactor

/-!
# The compressions of the stable signed factor

For the stable signed factor `U(c)` of Section `gate:sec:native` (`GateOptimalPrecision.uMat`, on
the flag `f`, the orientation `o` and the sign `z`), the success projection `Π = [f = 1]` and the
sign `Z = (-1)^z`, the compressions of `U(c)† Π Z Π U(c)` and `U(c)† Π U(c)` to the initial
`f = z = 0` block are `E(c)` and `|c| I` on the orientation (`uMat_sign_block`,
`uMat_weight_block`): with `B_±(c) = √|c| Π_±` (`gate:eq:local-factor`) and the action
`gate:eq:factor-action` (`GateOptimalPrecision.uMat_action`) they are `B_+² - B_-² = E(c)` and
`B_+² + B_-² = |c| I`. These are the local identities behind `gate:eq:native`.

References to the manuscript use its labels.
-/

set_option autoImplicit false

namespace GateOptimalBinary

noncomputable section

open Matrix GateOptimalPrecision
open scoped Kronecker ComplexConjugate Matrix

/-- The success-and-sign weight `[f = 1] (-1)^z` on the three local qubits. -/
def sgnQ3 (q : Q3) : ℂ := if q.1 then (if q.2.2 then -1 else 1) else 0

/-- The success weight `[f = 1]` on the three local qubits. -/
def sucQ3 (q : Q3) : ℂ := if q.1 then 1 else 0

/-- The initial block `|0⟩⟨0|_f ⊗ I_o ⊗ |0⟩⟨0|_z`. -/
def pin : Matrix Q3 Q3 ℂ := eij false false ⊗ₖ ((1 : Matrix Bool Bool ℂ) ⊗ₖ eij false false)

/-- The action of `U(c)` on the initial block (`gate:eq:factor-action`). -/
abbrev xQ3 (c : ℂ) : Matrix Q3 Q3 ℂ :=
  (((Real.sqrt (1 - ‖c‖) : ℝ) : ℂ) • eij false false) ⊗ₖ
      ((1 : Matrix Bool Bool ℂ) ⊗ₖ eij false false) +
    eij true false ⊗ₖ ((((Real.sqrt ‖c‖ : ℝ) : ℂ) • piP c) ⊗ₖ eij false false +
      (((Real.sqrt ‖c‖ : ℝ) : ℂ) • piM c) ⊗ₖ eij true false)

theorem uMat_pin (c : ℂ) : uMat c * pin = xQ3 c := uMat_action c

/-- The columns of `U(c)` on the initial block are those of its action. -/
theorem uMat_col (c : ℂ) (q : Q3) (b : Bool) :
    uMat c q (false, (b, false)) = xQ3 c q (false, (b, false)) := by
  rw [← uMat_pin, Matrix.mul_apply, Finset.sum_eq_single (false, (b, false))]
  · simp [pin, Matrix.kroneckerMap_apply]
  · rintro ⟨f, o, z⟩ _ h
    simp only [pin, Matrix.kroneckerMap_apply, eij_apply, Matrix.one_apply]
    by_cases hf : f = false
    · by_cases hz : z = false
      · subst hf hz
        have ho : o ≠ b := fun ho => h (by rw [ho])
        simp [ho]
      · simp [hz]
    · simp [hf]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem piP_gram (c : ℂ) (b b' : Bool) :
    conj (piP c false b) * piP c false b' + conj (piP c true b) * piP c true b' = piP c b b' := by
  have h := congrFun (congrFun (piP_mul_piP c) b) b'
  conv_lhs at h => rw [← congrArg (fun M => M * piP c) (piP_conjTranspose c)]
  rw [Matrix.mul_apply, Fintype.sum_bool] at h
  simp only [Matrix.conjTranspose_apply, Complex.star_def] at h
  rw [← h]
  ring

theorem piM_gram (c : ℂ) (b b' : Bool) :
    conj (piM c false b) * piM c false b' + conj (piM c true b) * piM c true b' = piM c b b' := by
  have h := congrFun (congrFun (piM_mul_piM c) b) b'
  conv_lhs at h => rw [← congrArg (fun M => M * piM c) (piM_conjTranspose c)]
  rw [Matrix.mul_apply, Fintype.sum_bool] at h
  simp only [Matrix.conjTranspose_apply, Complex.star_def] at h
  rw [← h]
  ring

theorem sqrt_norm_sq (c : ℂ) :
    ((Real.sqrt ‖c‖ : ℝ) : ℂ) * ((Real.sqrt ‖c‖ : ℝ) : ℂ) = ((‖c‖ : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (norm_nonneg c)]

theorem triple_apply (U : Matrix Q3 Q3 ℂ) (d : Q3 → ℂ) (i j : Q3) :
    (Uᴴ * Matrix.diagonal d * U) i j = ∑ q, star (U q i) * d q * U q j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]

/-- **The signed compression of the local factor**: the `f = z = 0` block of
`U(c)† Π Z Π U(c)` is `E(c) = B_+(c)² - B_-(c)²`. -/
theorem uMat_sign_block (c : ℂ) (b b' : Bool) :
    ((uMat c)ᴴ * Matrix.diagonal sgnQ3 * uMat c) (false, (b, false)) (false, (b', false)) =
      eMat c b b' := by
  rw [triple_apply]
  simp only [uMat_col]
  have hE : eMat c b b' = ((‖c‖ : ℝ) : ℂ) * (piP c b b' - piM c b b') := by
    rw [eMat_eq]
    rfl
  have h1 := piP_gram c b b'
  have h2 := piM_gram c b b'
  have hs := sqrt_norm_sq c
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, sgnQ3, xQ3, Matrix.add_apply,
    Matrix.kroneckerMap_apply, Matrix.smul_apply, eij_apply, Matrix.one_apply, smul_eq_mul]
  simp
  linear_combination (((Real.sqrt ‖c‖ : ℝ) : ℂ) * ((Real.sqrt ‖c‖ : ℝ) : ℂ)) * h1 -
    (((Real.sqrt ‖c‖ : ℝ) : ℂ) * ((Real.sqrt ‖c‖ : ℝ) : ℂ)) * h2 +
    (piP c b b' - piM c b b') * hs - hE

/-- **The successful weight of the local factor**: the `f = z = 0` block of `U(c)† Π U(c)` is
`|c| I = B_+(c)² + B_-(c)²`. -/
theorem uMat_weight_block (c : ℂ) (b b' : Bool) :
    ((uMat c)ᴴ * Matrix.diagonal sucQ3 * uMat c) (false, (b, false)) (false, (b', false)) =
      ((‖c‖ : ℝ) : ℂ) * (1 : Matrix Bool Bool ℂ) b b' := by
  rw [triple_apply]
  simp only [uMat_col]
  have hA : piP c b b' + piM c b b' = (1 : Matrix Bool Bool ℂ) b b' := by
    rw [← Matrix.add_apply, piP_add_piM]
  have h1 := piP_gram c b b'
  have h2 := piM_gram c b b'
  have hs := sqrt_norm_sq c
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, sucQ3, xQ3, Matrix.add_apply,
    Matrix.kroneckerMap_apply, Matrix.smul_apply, eij_apply, Matrix.one_apply, smul_eq_mul]
  simp only [Matrix.one_apply] at hA
  have hI : (if b = b' then ((‖c‖ : ℝ) : ℂ) else 0) =
      ((‖c‖ : ℝ) : ℂ) * (if b = b' then 1 else 0) := by
    split_ifs <;> simp
  simp
  linear_combination (((Real.sqrt ‖c‖ : ℝ) : ℂ) * ((Real.sqrt ‖c‖ : ℝ) : ℂ)) * h1 +
    (((Real.sqrt ‖c‖ : ℝ) : ℂ) * ((Real.sqrt ‖c‖ : ℝ) : ℂ)) * h2 +
    (piP c b b' + piM c b b') * hs + ((‖c‖ : ℝ) : ℂ) * hA - hI

end

end GateOptimalBinary
