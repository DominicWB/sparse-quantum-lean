import SparseHamiltonian.ExactEdgeCayley
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option autoImplicit false

/-!
# The local signed factor on one edge

For a decoded entry `c` with `‖c‖ ≤ 1`, the paper's local factor
(`opt:eq:edge-factors`) sends the orientation qubit `v` to two success labels with blocks
`B_±(c) = √((‖c‖ I ± E(c))/2)` and a failure label with amplitude `√(1 - ‖c‖)`. We use a
factor with the same compressions, `B = √‖c‖ V(c)†`, where `V(c)` diagonalises
`E(c) = [[0,c],[conj c,0]]`: the success label is a qubit whose two basis states are the `+` and
`-` labels. Then `B† σ_z B = E(c)` (`facQ_sign`) and `B† B = ‖c‖ I` (`facQ_gram`).

The unitary extension acts on the orientation qubit and the three-valued flag
(`localGate`, the Kronecker product of the orientation change `orient` and the flag rotation
`flagRot`). The amplitude is clipped to the unit disk (`clip`), so every value word, including
words never produced by the oracle, gives a unitary.
-/

namespace NativeSignedFactor

noncomputable section

open ContinuousLinearMap SparseHamiltonian
open scoped ComplexConjugate Kronecker InnerProduct

/-! ### Scalars -/

/-- Radial projection to the closed unit disk. -/
def clip (w : ℂ) : ℂ := if ‖w‖ ≤ 1 then w else w / (‖w‖ : ℂ)

theorem norm_clip_le (w : ℂ) : ‖clip w‖ ≤ 1 := by
  unfold clip
  split_ifs with h
  · exact h
  · have hpos : 0 < ‖w‖ := lt_trans zero_lt_one (lt_of_not_ge h)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, div_self hpos.ne']

theorem clip_of_norm_le {w : ℂ} (h : ‖w‖ ≤ 1) : clip w = w := if_pos h

/-- Clipping never increases the modulus. -/
theorem norm_clip_le_norm (w : ℂ) : ‖clip w‖ ≤ ‖w‖ := by
  by_cases h : ‖w‖ ≤ 1
  · rw [clip_of_norm_le h]
  · exact (norm_clip_le w).trans (le_of_lt (lt_of_not_ge h))

/-- The phase of a complex number, with phase one at zero. -/
def phase (c : ℂ) : ℂ := if c = 0 then 1 else c / (‖c‖ : ℂ)

theorem norm_phase (c : ℂ) : ‖phase c‖ = 1 := by
  unfold phase
  split_ifs with h
  · simp
  · have hpos : 0 < ‖c‖ := norm_pos_iff.mpr h
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, div_self hpos.ne']

theorem norm_mul_phase (c : ℂ) : (‖c‖ : ℂ) * phase c = c := by
  unfold phase
  split_ifs with h
  · simp [h]
  · have hne : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr h).ne'
    field_simp

theorem norm_mul_conj_phase (c : ℂ) : (‖c‖ : ℂ) * conj (phase c) = conj c := by
  have h := congrArg conj (norm_mul_phase c)
  rwa [map_mul, Complex.conj_ofReal] at h

theorem phase_mul_conj_phase (c : ℂ) : phase c * conj (phase c) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_phase]
  simp

theorem conj_phase_mul_phase (c : ℂ) : conj (phase c) * phase c = 1 := by
  rw [mul_comm]
  exact phase_mul_conj_phase c

/-- The scalar `1/√2`. -/
def r2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

@[simp] theorem conj_r2 : conj r2 = r2 := Complex.conj_ofReal _

theorem r2_mul_r2 : r2 * r2 = 2⁻¹ := by
  have h : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  unfold r2
  rw [← Complex.ofReal_mul, h]
  norm_num

/-- The success amplitude `√‖c‖`. -/
def amp (c : ℂ) : ℝ := Real.sqrt ‖c‖

/-- The failure amplitude `√(1 - ‖c‖)`. -/
def fam (c : ℂ) : ℝ := Real.sqrt (1 - ‖c‖)

theorem amp_sq (c : ℂ) : (amp c : ℂ) * amp c = ‖c‖ := by
  have h : amp c * amp c = ‖c‖ := Real.mul_self_sqrt (norm_nonneg c)
  exact_mod_cast h

theorem amp_sq_add_fam_sq {c : ℂ} (hc : ‖c‖ ≤ 1) :
    (amp c : ℂ) * amp c + (fam c : ℂ) * fam c = 1 := by
  have h1 : amp c * amp c = ‖c‖ := Real.mul_self_sqrt (norm_nonneg c)
  have h2 : fam c * fam c = 1 - ‖c‖ := Real.mul_self_sqrt (by linarith)
  have h : amp c * amp c + fam c * fam c = 1 := by rw [h1, h2]; ring
  exact_mod_cast h

/-! ### The local unitary -/

/-- The orientation change `V(c)†`, with rows `(1, u)/√2` and `(1, -u)/√2`, `u` the phase of
`c`. Row and column `false` are the row orientation (or the `+` label). -/
def orient (c : ℂ) : Matrix Bool Bool ℂ :=
  Matrix.of fun b b' => r2 * (if b' then (if b then -phase c else phase c) else 1)

theorem orient_unitary (c : ℂ) :
    star (orient c) * orient c = 1 ∧ orient c * star (orient c) = 1 := by
  have hu := conj_phase_mul_phase c
  have hu' := phase_mul_conj_phase c
  have hr := r2_mul_r2
  constructor
  · ext b b'
    cases b <;> cases b' <;> simp [orient, Matrix.mul_apply, Matrix.star_apply] <;>
      first
        | linear_combination 2 * hr
        | linear_combination (2 * conj (phase c) * phase c) * hr + hu
  · ext b b'
    cases b <;> cases b' <;> simp [orient, Matrix.mul_apply, Matrix.star_apply] <;>
      first
        | linear_combination (phase c * conj (phase c) + 1) * hr + (1 / 2 : ℂ) * hu'
        | linear_combination (-(r2 * r2)) * hu'

/-- The flag rotation: flag `0` (success) keeps amplitude `√‖c‖` and flag `1` (failure)
receives `√(1 - ‖c‖)`; flag `2` is untouched. -/
def flagRot (c : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(amp c : ℂ), -(fam c : ℂ), 0; (fam c : ℂ), (amp c : ℂ), 0; 0, 0, 1]

theorem flagRot_unitary {c : ℂ} (hc : ‖c‖ ≤ 1) :
    star (flagRot c) * flagRot c = 1 ∧ flagRot c * star (flagRot c) = 1 := by
  have h := amp_sq_add_fam_sq hc
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [flagRot, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply] <;>
      first | linear_combination h | ring1
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [flagRot, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply] <;>
      first | linear_combination h | ring1

/-- The local gate on the orientation qubit and the flag. -/
def localGate (c : ℂ) : Matrix (Bool × Fin 3) (Bool × Fin 3) ℂ := orient c ⊗ₖ flagRot c

theorem localGate_unitary {c : ℂ} (hc : ‖c‖ ≤ 1) :
    star (localGate c) * localGate c = 1 ∧ localGate c * star (localGate c) = 1 := by
  obtain ⟨hO1, hO2⟩ := orient_unitary c
  obtain ⟨hR1, hR2⟩ := flagRot_unitary hc
  simp only [Matrix.star_eq_conjTranspose] at *
  constructor
  · rw [localGate, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hO1, hR1,
      Matrix.one_kronecker_one]
  · rw [localGate, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hO2, hR2,
      Matrix.one_kronecker_one]

/-- The local gate as an operator on `ℂ^{Bool × Fin 3}`. -/
def localOp (c : ℂ) : EuclideanSpace ℂ (Bool × Fin 3) →L[ℂ] EuclideanSpace ℂ (Bool × Fin 3) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (localGate c)

theorem localOp_unitary {c : ℂ} (hc : ‖c‖ ≤ 1) : OracleCircuit.IsUnitary (localOp c) := by
  obtain ⟨h1, h2⟩ := localGate_unitary hc
  constructor
  · rw [localOp, ← map_star, ← map_mul, h1, map_one]
  · rw [localOp, ← map_star, ← map_mul, h2, map_one]

theorem localOp_apply (c : ℂ) (w : EuclideanSpace ℂ (Bool × Fin 3)) (b : Bool) (f : Fin 3) :
    localOp c w (b, f) = ∑ b', ∑ f', orient c b b' * flagRot c f f' * w (b', f') := by
  change Matrix.mulVec (localGate c) (WithLp.ofLp w) (b, f) = _
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, localGate,
    Matrix.kroneckerMap_apply]

/-! ### The success factor on an edge -/

/-- The edge orientation qubit. -/
abbrev Qubit := ExactEdgeCayley.Qubit

/-- The success factor `√‖c‖ V(c)†` on one edge. -/
def facQ (c : ℂ) : Qubit →L[ℂ] Qubit :=
  ComplexAmplitudeRotation.matrix ((amp c : ℂ) * r2) ((amp c : ℂ) * r2 * phase c)
    ((amp c : ℂ) * r2) (-((amp c : ℂ) * r2 * phase c))

/-- The success reflection: `+1` on the `+` label (`false`), `-1` on the `-` label. -/
def signQ : Qubit →L[ℂ] Qubit := ComplexAmplitudeRotation.matrix 1 0 0 (-1)

@[simp] theorem facQ_false (c : ℂ) (x : Qubit) :
    facQ c x false = (amp c : ℂ) * r2 * x false + (amp c : ℂ) * r2 * phase c * x true := rfl

@[simp] theorem facQ_true (c : ℂ) (x : Qubit) :
    facQ c x true = (amp c : ℂ) * r2 * x false + -((amp c : ℂ) * r2 * phase c) * x true := rfl

theorem facQ_adjoint (c : ℂ) :
    (facQ c)† = ComplexAmplitudeRotation.matrix ((amp c : ℂ) * r2) ((amp c : ℂ) * r2)
      ((amp c : ℂ) * r2 * conj (phase c)) (-((amp c : ℂ) * r2 * conj (phase c))) := by
  rw [facQ, ComplexAmplitudeRotation.matrix_adjoint]
  simp [map_mul, map_neg, Complex.conj_ofReal]

/-- The signed compression of the local factor is the edge generator `E(c)`. -/
theorem facQ_sign (c : ℂ) :
    (facQ c)† ∘L signQ ∘L facQ c = ExactEdgeCayley.generator c := by
  have hu := conj_phase_mul_phase c
  have hr := r2_mul_r2
  have ha := amp_sq c
  have hp := norm_mul_phase c
  have hq := norm_mul_conj_phase c
  rw [facQ_adjoint]
  ext x b
  cases b
  · simp only [comp_apply, ComplexAmplitudeRotation.matrix_false,
      ComplexAmplitudeRotation.matrix_true, signQ, facQ_false, facQ_true,
      ExactEdgeCayley.generator_false]
    linear_combination (x true * phase c) * ((2 : ℂ) * (amp c : ℂ) * amp c) * hr +
      x true * hp + (x true * phase c) * ha
  · simp only [comp_apply, ComplexAmplitudeRotation.matrix_false,
      ComplexAmplitudeRotation.matrix_true, signQ, facQ_false, facQ_true,
      ExactEdgeCayley.generator_true]
    linear_combination (x false * conj (phase c)) * ((2 : ℂ) * (amp c : ℂ) * amp c) * hr +
      x false * hq + (x false * conj (phase c)) * ha

/-- The total successful weight of the local factor is `‖c‖ I`. -/
theorem facQ_gram (c : ℂ) :
    (facQ c)† ∘L facQ c = ((‖c‖ : ℝ) : ℂ) • (1 : Qubit →L[ℂ] Qubit) := by
  have hu := conj_phase_mul_phase c
  have hr := r2_mul_r2
  have ha := amp_sq c
  rw [facQ_adjoint]
  ext x b
  cases b
  · simp only [comp_apply, ComplexAmplitudeRotation.matrix_false, facQ_false, facQ_true,
      smul_apply, one_def, id_apply, PiLp.smul_apply, smul_eq_mul]
    linear_combination (x false) * ((2 : ℂ) * (amp c : ℂ) * amp c) * hr + x false * ha
  · simp only [comp_apply, ComplexAmplitudeRotation.matrix_true, facQ_false, facQ_true,
      smul_apply, one_def, id_apply, PiLp.smul_apply, smul_eq_mul]
    linear_combination (x true * conj (phase c) * phase c) * ((2 : ℂ) * (amp c : ℂ) * amp c) * hr +
      x true * ha + (x true) * ((amp c : ℂ) * amp c) * hu

/-- The flag-`0` row of the local gate applied to a flag-`0` input is the success factor. -/
theorem orient_sum (c : ℂ) (x : Qubit) (b : Bool) :
    (amp c : ℂ) * ∑ b', orient c b b' * x b' = facQ c x b := by
  cases b <;> simp [orient, facQ_false, facQ_true] <;> ring

end

end NativeSignedFactor
