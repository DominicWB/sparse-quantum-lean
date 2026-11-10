import GateOptimalBinary.FactorLocal
import GateOptimalPrecision.JointAlgebra

/-!
# The local algebra of the clipped joint private operation

The joint private operation of the clipped regime (Section `gate:sec:native`, paragraph "Sparse
preparation and the joint private operation"; `twonorm:eq:joint`) acts, at a located edge with
clipped entry `c₁` and correction entry `c₂` (of the same phase), on a branch qubit `g`, the flag
`f`, the orientation `o` and the sign `z`:

* the bulk branch `g = 0` carries the clipped edge generator `2q E(c₁)` on the orientation;
* the correction branch `g = 1` carries the stable signed factor `U(c₂)` and, on the success flag,
  the generator `2q E(e^{iφ})` on the orientation (`e^{iφ}` the phase of `c₂`), whose eigenvalues
  `±2q` label the two success labels `Π_±` of the factor; the failure flag carries `0`.

Every private operator is thus a one-qubit operation on the orientation chosen by `(g, f)` and the
edge, and the Cayley transform is the edge rotation (`edgeMat`) of the value
`y = [g = 0] 2q c₁ + [g = 1][f = 1] 2q e^{iφ}`.

* `cayley_mul_R1`, `R1_mul_cayley`: `(1 - D(y)) (1 + i E(y))/2 = 1 = (1 + i E(y))/2 (1 - D(y))`;
* `fblk`: flag-diagonal operators on `(f, o, z)`; `uMat_fblk_block`: the compression of
  `U(c)† fblk(B) U(c)` to the initial block `f = z = 0` is `(1 - |c|) B₀ + |c| (Π₊B₁Π₊ + Π₋B₁Π₋)`;
* `pinch_eMat_phase`: `Π₊ E(e^{iφ}) Π₊ + Π₋ E(e^{iφ}) Π₋ = Π₊ - Π₋`, so the success compression of
  the correction generator is `|c₂| (Π₊ - Π₋) = E(c₂)`.

References to the manuscript use its labels.
-/

set_option autoImplicit false

namespace GateOptimalBinary

noncomputable section

open Matrix GateOptimalPrecision
open SparseHamiltonian.GateNative (edgeMat)
open NativeSignedFactor (phase norm_phase norm_mul_phase norm_mul_conj_phase phase_mul_conj_phase
  conj_phase_mul_phase)
open scoped Kronecker ComplexConjugate Matrix

/-! ### Scalars and one-qubit identities -/

theorem phase_phase (c : ℂ) : phase (phase c) = phase c := by
  by_cases h : c = 0
  · subst h
    simp [phase]
  · have h1 : phase c ≠ 0 := by
      intro h0
      have := norm_phase c
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    rw [phase.eq_1 (phase c), if_neg h1, norm_phase, Complex.ofReal_one, div_one]

theorem piP_phase (c : ℂ) : piP (phase c) = piP c := by
  rw [piP_eq, piP_eq, phase_phase]

theorem piM_phase (c : ℂ) : piM (phase c) = piM c := by
  rw [piM_eq, piM_eq, phase_phase]

theorem eMat_phase (c : ℂ) : eMat (phase c) = piP c - piM c := by
  rw [eMat_eq, norm_phase, Complex.ofReal_one, one_smul, piP_phase, piM_phase]

theorem eMat_zero : eMat 0 = 0 := by
  ext b d
  cases b <;> cases d <;> simp [eMat]

theorem eMat_real_mul (r : ℝ) (z : ℂ) : eMat ((r : ℂ) * z) = (r : ℂ) • eMat z := by
  ext b d
  cases b <;> cases d <;> simp [eMat, map_mul, Complex.conj_ofReal]

theorem eMat_conjTranspose (z : ℂ) : (eMat z)ᴴ = eMat z := by
  ext b d
  cases b <;> cases d <;> simp [eMat, Matrix.conjTranspose_apply]

theorem eMat_mul_self (z : ℂ) : eMat z * eMat z = (((‖z‖ : ℝ) : ℂ) ^ 2) • 1 := by
  have h1 := mul_conj_norm z
  have h2 := conj_mul_norm z
  ext b d
  cases b <;> cases d <;> simp [eMat, Matrix.mul_apply] <;>
    linear_combination h2

theorem eMat_phase_mul_piP (c : ℂ) : eMat (phase c) * piP c = piP c := by
  rw [eMat_phase, Matrix.sub_mul, piP_mul_piP, piM_mul_piP, sub_zero]

theorem eMat_phase_mul_piM (c : ℂ) : eMat (phase c) * piM c = -piM c := by
  rw [eMat_phase, Matrix.sub_mul, piP_mul_piM, piM_mul_piM, zero_sub]

/-- The pinching of the unit generator by the success labels. -/
theorem pinch_eMat_phase (c : ℂ) :
    piP c * eMat (phase c) * piP c + piM c * eMat (phase c) * piM c = piP c - piM c := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, eMat_phase_mul_piP, eMat_phase_mul_piM, piP_mul_piP,
    Matrix.mul_neg, piM_mul_piM]
  abel

/-- The pinching of a success projection. -/
theorem pinch_piP (c : ℂ) : piP c * piP c * piP c + piM c * piP c * piM c = piP c := by
  rw [piP_mul_piP, piP_mul_piP, piM_mul_piP, Matrix.zero_mul, add_zero]

theorem pinch_piM (c : ℂ) : piP c * piM c * piP c + piM c * piM c * piM c = piM c := by
  rw [piM_mul_piM, piM_mul_piM, piP_mul_piM, Matrix.zero_mul, zero_add]

theorem pinch_one (c : ℂ) :
    piP c * (1 : Matrix Bool Bool ℂ) * piP c + piM c * 1 * piM c = 1 := by
  rw [Matrix.mul_one, Matrix.mul_one, piP_mul_piP, piM_mul_piM, piP_add_piM]

theorem pinch_zero (c : ℂ) :
    piP c * (0 : Matrix Bool Bool ℂ) * piP c + piM c * 0 * piM c = 0 := by
  simp

/-- **The Cayley relations of the edge rotation**: `(1 - D(y)) (1 + i E(y))/2 = 1`. -/
theorem cayley_mul_R1 (y : ℂ) :
    (1 - edgeMat y) * ((2 : ℂ)⁻¹ • (1 + Complex.I • eMat y)) = 1 := by
  have hy := mul_conj_norm y
  have hy' := conj_mul_norm y
  have hd := one_add_norm_sq_ne y
  ext b d
  cases b <;> cases d <;>
    simp [edgeMat, eMat, Matrix.mul_apply, Matrix.one_apply] <;>
    field_simp <;>
    (try simp only [Complex.I_sq]) <;>
    first
      | ring1
      | linear_combination (-2 : ℂ) * hy'
      | linear_combination (-2 : ℂ) * hy
      | linear_combination (2 : ℂ) * hy'

/-- `(1 + i E(y))/2 (1 - D(y)) = 1`. -/
theorem R1_mul_cayley (y : ℂ) :
    ((2 : ℂ)⁻¹ • (1 + Complex.I • eMat y)) * (1 - edgeMat y) = 1 := by
  have hy := mul_conj_norm y
  have hy' := conj_mul_norm y
  have hd := one_add_norm_sq_ne y
  ext b d
  cases b <;> cases d <;>
    simp [edgeMat, eMat, Matrix.mul_apply, Matrix.one_apply] <;>
    field_simp <;>
    (try simp only [Complex.I_sq]) <;>
    first
      | ring1
      | linear_combination (-2 : ℂ) * hy'
      | linear_combination (-2 : ℂ) * hy
      | linear_combination (2 : ℂ) * hy'

/-! ### Flag-diagonal operators on the three local qubits -/

/-- The flag-diagonal matrix with the one-qubit block `B f` on the orientation; the sign is
untouched. -/
def fblk (B : Bool → Matrix Bool Bool ℂ) : Matrix Q3 Q3 ℂ :=
  fun q q' => if q.1 = q'.1 ∧ q.2.2 = q'.2.2 then B q.1 q.2.1 q'.2.1 else 0

theorem fblk_apply (B : Bool → Matrix Bool Bool ℂ) (f o z f' o' z' : Bool) :
    fblk B (f, (o, z)) (f', (o', z')) = if f = f' ∧ z = z' then B f o o' else 0 := rfl

theorem fblk_mul (B C : Bool → Matrix Bool Bool ℂ) :
    fblk B * fblk C = fblk (fun f => B f * C f) := by
  ext ⟨f, o, z⟩ ⟨f', o', z'⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, fblk_apply]
  by_cases h : f = f' ∧ z = z'
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, if_true]
    rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    cases f <;> cases z <;> simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro o'' _
    apply Finset.sum_eq_zero
    intro z'' _
    by_cases h1 : f = a ∧ z = z''
    · obtain ⟨rfl, rfl⟩ := h1
      rw [if_neg h, mul_zero]
    · rw [if_neg h1, zero_mul]

theorem fblk_conjTranspose (B : Bool → Matrix Bool Bool ℂ) :
    (fblk B)ᴴ = fblk (fun f => (B f)ᴴ) := by
  ext ⟨f, o, z⟩ ⟨f', o', z'⟩
  simp only [Matrix.conjTranspose_apply, fblk_apply]
  by_cases h : f = f' ∧ z = z'
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · have h' : ¬(f' = f ∧ z' = z) := fun h'' => h ⟨h''.1.symm, h''.2.symm⟩
    rw [if_neg h', if_neg h, star_zero]

theorem fblk_one : fblk (fun _ => (1 : Matrix Bool Bool ℂ)) = 1 := by
  ext ⟨f, o, z⟩ ⟨f', o', z'⟩
  simp only [fblk_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases h : f = f' ∧ z = z'
  · obtain ⟨rfl, rfl⟩ := h
    by_cases ho : o = o' <;> simp [ho]
  · rw [if_neg h, if_neg]
    tauto

theorem fblk_add (B C : Bool → Matrix Bool Bool ℂ) :
    fblk B + fblk C = fblk (fun f => B f + C f) := by
  ext ⟨f, o, z⟩ ⟨f', o', z'⟩
  simp only [Matrix.add_apply, fblk_apply]
  split_ifs <;> simp

theorem fblk_sub (B C : Bool → Matrix Bool Bool ℂ) :
    fblk B - fblk C = fblk (fun f => B f - C f) := by
  ext ⟨f, o, z⟩ ⟨f', o', z'⟩
  simp only [Matrix.sub_apply, fblk_apply]
  split_ifs <;> simp

theorem fblk_smul (r : ℂ) (B : Bool → Matrix Bool Bool ℂ) :
    r • fblk B = fblk (fun f => r • B f) := by
  ext ⟨f, o, z⟩ ⟨f', o', z'⟩
  simp only [Matrix.smul_apply, fblk_apply, smul_eq_mul]
  split_ifs <;> simp

/-- The columns of the local factor on the initial block, explicitly. -/
theorem uMat_col_apply (c : ℂ) (f o z b : Bool) :
    uMat c (f, (o, z)) (false, (b, false)) =
      if f then (if z then ((Real.sqrt ‖c‖ : ℝ) : ℂ) * piM c o b
        else ((Real.sqrt ‖c‖ : ℝ) : ℂ) * piP c o b)
      else (if z then 0 else if o = b then ((Real.sqrt (1 - ‖c‖) : ℝ) : ℂ) else 0) := by
  rw [uMat_col]
  cases f <;> cases z <;>
    simp [xQ3, Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply, eij_apply,
      Matrix.one_apply]

theorem piP_conj (c : ℂ) (o b : Bool) : conj (piP c o b) = piP c b o := by
  have h := congrFun (congrFun (piP_conjTranspose c) b) o
  rw [Matrix.conjTranspose_apply] at h
  exact h

theorem piM_conj (c : ℂ) (o b : Bool) : conj (piM c o b) = piM c b o := by
  have h := congrFun (congrFun (piM_conjTranspose c) b) o
  rw [Matrix.conjTranspose_apply] at h
  exact h

theorem sqrt_one_sub_sq {c : ℂ} (hc : ‖c‖ ≤ 1) :
    ((Real.sqrt (1 - ‖c‖) : ℝ) : ℂ) * ((Real.sqrt (1 - ‖c‖) : ℝ) : ℂ) = ((1 - ‖c‖ : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]

/-- **The compression of a flag-diagonal operator by the local factor** to the initial block:
`(1 - |c|) B₀ + |c| (Π₊ B₁ Π₊ + Π₋ B₁ Π₋)`. -/
theorem uMat_fblk_block {c : ℂ} (hc : ‖c‖ ≤ 1) (B : Bool → Matrix Bool Bool ℂ) (b b' : Bool) :
    ((uMat c)ᴴ * fblk B * uMat c) (false, (b, false)) (false, (b', false)) =
      ((1 - ‖c‖ : ℝ) : ℂ) * B false b b' +
        ((‖c‖ : ℝ) : ℂ) * (piP c * B true * piP c + piM c * B true * piM c) b b' := by
  have hs := sqrt_norm_sq c
  have hs' := sqrt_one_sub_sq hc
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, fblk_apply,
    uMat_col_apply, Matrix.add_apply]
  simp only [Fintype.sum_bool]
  simp only [Bool.false_eq_true, if_false, if_true, true_and, and_true, and_false, false_and,
    Complex.star_def, map_mul, Complex.conj_ofReal, piP_conj, piM_conj, mul_zero, zero_mul,
    add_zero, zero_add, map_zero]
  rw [← hs, ← hs']
  cases b <;> cases b' <;> simp <;> ring

end

end GateOptimalBinary
