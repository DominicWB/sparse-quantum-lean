import NativeSignedFactor.Local

/-!
# A stable constant-dimensional signed factor (Section `gate:sec:native`)

For `c = u e^{iφ}` with `0 ≤ u ≤ 1` (here `u = ‖c‖` and `e^{iφ}` the phase of `c`,
`NativeSignedFactor.phase`, with phase one at zero) the manuscript puts

`E(c) = [[0, c], [c̄, 0]]`, `V_φ = diag(e^{iφ}, 1) H₂`, `Π_+ = V_φ|0⟩⟨0|V_φ†`,
`Π_- = V_φ|1⟩⟨1|V_φ†`, `T_φ = (V_φ ⊗ I_z) CNOT_{o→z} (V_φ† ⊗ I_z)`, `A_φ = diag_f(I, T_φ)`,
`R_u = [[√(1-u), -√u], [√u, √(1-u)]]` and `U(c) = A_φ (R_u ⊗ I) A_φ†` (`gate:eq:dilation`),

on the success flag `f`, the orientation qubit `o` and the sign qubit `z`. Matrices on one qubit are
indexed by `Bool` (`false` is `|0⟩`), and on the three qubits by `f × (o × z)`; `⊗ₖ` is the
Kronecker product. This module proves:

* `piP_eq`, `piM_eq`, `piP_add_piM`, `piP_mul_piP`, `piM_mul_piM`, `piP_mul_piM`, `piM_mul_piP`:
  `Π_±` are complementary orthogonal projections;
* `eMat_eq`: `E(c) = u(Π_+ - Π_-)`; `bP_sq`, `bM_sq`: `(uI ± E(c))/2 = (√u Π_±)²`, i.e.
  `B_±(c) = √u Π_±` (`gate:eq:local-factor`);
* `tMat_eq`: `T_φ = Π_+ ⊗ I + Π_- ⊗ X`; `tMat_mul_self`, `tMat_conjTranspose`:
  `T_φ = T_φ† = T_φ⁻¹`;
* `uMat_eq`: `U(c) = √(1-u) I + √u (J ⊗ T_φ)` with `J = |1⟩⟨0| - |0⟩⟨1|`, the block form
  `[[√(1-u) I, -√u T_φ], [√u T_φ, √(1-u) I]]`; `uMat_unitary`;
* `uMat_action` (`gate:eq:factor-action`): on initial `f = z = 0`,
  `ψ ↦ |0⟩_f|0⟩_z √(1-u) ψ + |1⟩_f|0⟩_z B_+(c) ψ + |1⟩_f|1⟩_z B_-(c) ψ`;
* `uMat_gates`: `U(c) = (V_φ)_o · Toffoli_{f,o→z} · (R_u)_f · Toffoli_{f,o→z} · (V_φ†)_o`, a
  constant number of local rotations and bounded-arity gates;
* `uMat_zero`: `U(0) = I`, independently of the phase convention;
* `norm_uMat_sub_one_le` (`gate:eq:small`, L2 operator norm on all inputs):
  `‖U(c) - I‖ ≤ 1 - √(1-u) + √u ≤ 2√u`; `norm_uMat_sub_zero_le`: "`u ≤ ξ²/16` may be replaced by
  zero with error at most `ξ/2`";
* `norm_uMat_sub_le`, `norm_uMat_sub_le_of_accuracy`: `‖U(c) - U(c')‖ ≤ |√(1-u) - √(1-u')| +
  |√u - √u'| + √u' |e^{iφ} - e^{iφ'}|`, so "magnitude accuracy of order `ξ²` and phase accuracy
  of order `ξ` suffice": `‖U(c) - U(c')‖ ≤ 3ξ` (`norm_kronecker_le`: `‖A ⊗ₖ B‖ ≤ ‖A‖ ‖B‖`).

The two-sided completion is what makes the last two bounds hold on all inputs; the released
query-level factor (`NativeSignedFactor.localGate`) has the same compressions with a one-sided
completion.
-/

set_option autoImplicit false

namespace GateOptimalPrecision

noncomputable section

open Matrix Complex
open NativeSignedFactor (phase norm_phase norm_mul_phase norm_mul_conj_phase phase_mul_conj_phase
  conj_phase_mul_phase)
open scoped Kronecker ComplexConjugate Matrix

/-! ### One-qubit matrices -/

/-- `|i⟩⟨j|`. -/
def eij (i j : Bool) : Matrix Bool Bool ℂ := Matrix.of fun b d => if b = i ∧ d = j then 1 else 0

@[simp] theorem eij_apply (i j b d : Bool) : eij i j b d = if b = i ∧ d = j then 1 else 0 := rfl

/-- The Hadamard gate. -/
def hMat : Matrix Bool Bool ℂ :=
  Matrix.of fun b d => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (if b && d then -1 else 1)

/-- Pauli `X`. -/
def xMat : Matrix Bool Bool ℂ := Matrix.of fun b d => if b = d then 0 else 1

/-- `E(c) = [[0, c], [c̄, 0]]`. -/
def eMat (c : ℂ) : Matrix Bool Bool ℂ :=
  Matrix.of fun b d => if b = d then 0 else if b then conj c else c

/-- `V_φ = diag(e^{iφ}, 1) H₂` with `e^{iφ}` the phase of `c`. -/
def vMat (c : ℂ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal (fun b => if b then 1 else phase c) * hMat

/-- `Π_+ = V_φ |0⟩⟨0| V_φ†`. -/
def piP (c : ℂ) : Matrix Bool Bool ℂ := vMat c * eij false false * (vMat c)ᴴ

/-- `Π_- = V_φ |1⟩⟨1| V_φ†`. -/
def piM (c : ℂ) : Matrix Bool Bool ℂ := vMat c * eij true true * (vMat c)ᴴ

/-- `R_u = [[√(1-u), -√u], [√u, √(1-u)]]` on the flag. -/
def rMat (u : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.of fun b d => if b = d then (Real.sqrt (1 - u) : ℂ)
    else if b then (Real.sqrt u : ℂ) else -(Real.sqrt u : ℂ)

/-- `J = |1⟩⟨0| - |0⟩⟨1|`. -/
def jMat : Matrix Bool Bool ℂ := eij true false - eij false true

theorem sqrt2_inv_sq_c : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 2⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem vMat_apply (c : ℂ) (b d : Bool) :
    vMat c b d = (if b then 1 else phase c) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
      (if b && d then -1 else 1)) := by
  simp [vMat, Matrix.diagonal_mul, hMat]

/-- `Π_+ = ½ [[1, e^{iφ}], [e^{-iφ}, 1]]`. -/
theorem piP_eq (c : ℂ) : piP c = Matrix.of fun b d =>
    (2⁻¹ : ℂ) * (if b = d then 1 else if b then conj (phase c) else phase c) := by
  have hu := phase_mul_conj_phase c
  have hr := sqrt2_inv_sq_c
  ext b d
  cases b <;> cases d <;>
    simp [piP, Matrix.mul_apply, vMat_apply, Matrix.conjTranspose_apply] <;>
    first
      | linear_combination (phase c * conj (phase c)) * hr + (2⁻¹ : ℂ) * hu
      | linear_combination (phase c) * hr
      | linear_combination (conj (phase c)) * hr
      | linear_combination hr

/-- `Π_- = ½ [[1, -e^{iφ}], [-e^{-iφ}, 1]]`. -/
theorem piM_eq (c : ℂ) : piM c = Matrix.of fun b d =>
    (2⁻¹ : ℂ) * (if b = d then 1 else if b then -conj (phase c) else -phase c) := by
  have hu := phase_mul_conj_phase c
  have hr := sqrt2_inv_sq_c
  ext b d
  cases b <;> cases d <;>
    simp [piM, Matrix.mul_apply, vMat_apply, Matrix.conjTranspose_apply] <;>
    first
      | linear_combination (phase c * conj (phase c)) * hr + (2⁻¹ : ℂ) * hu
      | linear_combination (-phase c) * hr
      | linear_combination (-conj (phase c)) * hr
      | linear_combination (phase c) * hr
      | linear_combination (conj (phase c)) * hr
      | linear_combination hr

theorem piP_add_piM (c : ℂ) : piP c + piM c = 1 := by
  rw [piP_eq, piM_eq]
  ext b d
  cases b <;> cases d <;> simp <;> ring

theorem piP_mul_piP (c : ℂ) : piP c * piP c = piP c := by
  have hu := phase_mul_conj_phase c
  have hu' := conj_phase_mul_phase c
  rw [piP_eq]
  ext b d
  cases b <;> cases d <;> simp [Matrix.mul_apply] <;>
    first
      | ring1
      | linear_combination (4⁻¹ : ℂ) * hu'

theorem piM_mul_piM (c : ℂ) : piM c * piM c = piM c := by
  have hu := phase_mul_conj_phase c
  have hu' := conj_phase_mul_phase c
  rw [piM_eq]
  ext b d
  cases b <;> cases d <;> simp [Matrix.mul_apply] <;>
    first
      | ring1
      | linear_combination (4⁻¹ : ℂ) * hu'

theorem piP_mul_piM (c : ℂ) : piP c * piM c = 0 := by
  have hu := phase_mul_conj_phase c
  have hu' := conj_phase_mul_phase c
  rw [piP_eq, piM_eq]
  ext b d
  cases b <;> cases d <;> simp [Matrix.mul_apply] <;>
    first
      | ring1
      | linear_combination (4⁻¹ : ℂ) * hu'
      | linear_combination (-(4⁻¹ : ℂ)) * hu'

theorem piM_mul_piP (c : ℂ) : piM c * piP c = 0 := by
  have hu := phase_mul_conj_phase c
  have hu' := conj_phase_mul_phase c
  rw [piP_eq, piM_eq]
  ext b d
  cases b <;> cases d <;> simp [Matrix.mul_apply] <;>
    first
      | ring1
      | linear_combination (4⁻¹ : ℂ) * hu'
      | linear_combination (-(4⁻¹ : ℂ)) * hu'

theorem piP_conjTranspose (c : ℂ) : (piP c)ᴴ = piP c := by
  rw [piP_eq]
  ext b d
  cases b <;> cases d <;> simp [Matrix.conjTranspose_apply]

theorem piM_conjTranspose (c : ℂ) : (piM c)ᴴ = piM c := by
  rw [piM_eq]
  ext b d
  cases b <;> cases d <;> simp [Matrix.conjTranspose_apply]

/-- `E(c) = u (Π_+ - Π_-)`. -/
theorem eMat_eq (c : ℂ) : eMat c = ((‖c‖ : ℝ) : ℂ) • (piP c - piM c) := by
  have hp := norm_mul_phase c
  have hq := norm_mul_conj_phase c
  rw [piP_eq, piM_eq]
  ext b d
  cases b <;> cases d <;> simp [eMat] <;>
    first
      | linear_combination -hp
      | linear_combination -hq

/-- `B_+(c) = √u Π_+`: `(uI + E(c))/2 = (√u Π_+)²`. -/
theorem bP_sq (c : ℂ) :
    (2⁻¹ : ℂ) • (((‖c‖ : ℝ) : ℂ) • (1 : Matrix Bool Bool ℂ) + eMat c) =
      ((Real.sqrt ‖c‖ : ℝ) : ℂ) • piP c * (((Real.sqrt ‖c‖ : ℝ) : ℂ) • piP c) := by
  have hs : ((Real.sqrt ‖c‖ : ℝ) : ℂ) * ((Real.sqrt ‖c‖ : ℝ) : ℂ) = ((‖c‖ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (norm_nonneg c)]
  rw [smul_mul_smul_comm, hs, piP_mul_piP, eMat_eq, ← piP_add_piM c]
  rw [show (piP c + piM c) = piP c + piM c from rfl]
  module

/-- `B_-(c) = √u Π_-`: `(uI - E(c))/2 = (√u Π_-)²`. -/
theorem bM_sq (c : ℂ) :
    (2⁻¹ : ℂ) • (((‖c‖ : ℝ) : ℂ) • (1 : Matrix Bool Bool ℂ) - eMat c) =
      ((Real.sqrt ‖c‖ : ℝ) : ℂ) • piM c * (((Real.sqrt ‖c‖ : ℝ) : ℂ) • piM c) := by
  have hs : ((Real.sqrt ‖c‖ : ℝ) : ℂ) * ((Real.sqrt ‖c‖ : ℝ) : ℂ) = ((‖c‖ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (norm_nonneg c)]
  rw [smul_mul_smul_comm, hs, piM_mul_piM, eMat_eq, ← piP_add_piM c]
  module

/-! ### Small matrix identities -/

theorem eij_conjTranspose (i j : Bool) : (eij i j)ᴴ = eij j i := by
  ext b d
  cases i <;> cases j <;> cases b <;> cases d <;> simp [Matrix.conjTranspose_apply]

theorem eij_add_eij : eij false false + eij true true = 1 := by
  ext b d
  cases b <;> cases d <;> simp

theorem xMat_mul_self : xMat * xMat = 1 := by
  ext b d
  cases b <;> cases d <;> simp [xMat, Matrix.mul_apply]

theorem xMat_conjTranspose : xMatᴴ = xMat := by
  ext b d
  cases b <;> cases d <;> simp [xMat, Matrix.conjTranspose_apply]

theorem xMat_mul_eij : xMat * eij false false = eij true false := by
  ext b d
  cases b <;> cases d <;> simp [xMat, Matrix.mul_apply]

theorem jMat_mul_eij : jMat * eij false false = eij true false := by
  ext b d
  cases b <;> cases d <;> simp [jMat, Matrix.mul_apply]

theorem jMat_conjTranspose_mul_self : jMatᴴ * jMat = 1 := by
  ext b d
  cases b <;> cases d <;>
    simp [jMat, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem jMat_mul_conjTranspose : jMat * jMatᴴ = 1 := by
  ext b d
  cases b <;> cases d <;>
    simp [jMat, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem vMat_mul_conjTranspose (c : ℂ) : vMat c * (vMat c)ᴴ = 1 := by
  have hu := phase_mul_conj_phase c
  have hr := sqrt2_inv_sq_c
  ext b d
  cases b <;> cases d <;>
    simp [Matrix.mul_apply, vMat_apply, Matrix.conjTranspose_apply,
      ] <;>
    first
      | linear_combination (2 * phase c * conj (phase c)) * hr + (1 : ℂ) * hu
      | linear_combination 2 * hr

theorem vMat_conjTranspose_mul (c : ℂ) : (vMat c)ᴴ * vMat c = 1 := by
  have hu := phase_mul_conj_phase c
  have hu' := conj_phase_mul_phase c
  have hr := sqrt2_inv_sq_c
  ext b d
  cases b <;> cases d <;>
    simp [Matrix.mul_apply, vMat_apply, Matrix.conjTranspose_apply,
      ] <;>
    first
      | linear_combination (conj (phase c) * phase c + 1) * hr + (2⁻¹ : ℂ) * hu'
      | linear_combination (conj (phase c) * phase c - 1) * hr + (2⁻¹ : ℂ) * hu'

theorem sub_kronecker' {l m n p : Type*} (A B : Matrix l m ℂ) (C : Matrix n p ℂ) :
    (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext i j
  simp [Matrix.kroneckerMap_apply, sub_mul]

/-! ### The two-qubit reflection `T_φ` -/

/-- `CNOT_{o→z} = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ X`. -/
def cnotMat : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  eij false false ⊗ₖ (1 : Matrix Bool Bool ℂ) + eij true true ⊗ₖ xMat

/-- `T_φ = (V_φ ⊗ I) CNOT_{o→z} (V_φ† ⊗ I)` on the orientation and sign qubits. -/
def tMat (c : ℂ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (vMat c ⊗ₖ (1 : Matrix Bool Bool ℂ)) * cnotMat * ((vMat c)ᴴ ⊗ₖ (1 : Matrix Bool Bool ℂ))

/-- `T_φ = Π_+ ⊗ I + Π_- ⊗ X`. -/
theorem tMat_eq (c : ℂ) : tMat c = piP c ⊗ₖ (1 : Matrix Bool Bool ℂ) + piM c ⊗ₖ xMat := by
  unfold tMat cnotMat
  simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    Matrix.one_mul]
  rfl

theorem tMat_mul_self (c : ℂ) : tMat c * tMat c = 1 := by
  rw [tMat_eq]
  simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_kronecker_mul, piP_mul_piP, piM_mul_piM,
    piP_mul_piM, piM_mul_piP, Matrix.zero_kronecker, add_zero, zero_add, Matrix.one_mul,
    Matrix.mul_one, xMat_mul_self]
  rw [← Matrix.add_kronecker, piP_add_piM, Matrix.one_kronecker_one]

theorem tMat_conjTranspose (c : ℂ) : (tMat c)ᴴ = tMat c := by
  rw [tMat_eq, Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_kronecker, piP_conjTranspose, piM_conjTranspose,
    Matrix.conjTranspose_one, xMat_conjTranspose]

/-! ### The three-qubit factor `U(c)` -/

/-- The three-qubit index: flag `f`, orientation `o`, sign `z`. -/
abbrev Q3 := Bool × (Bool × Bool)

/-- `A_φ = diag_f(I, T_φ)`. -/
def aMat (c : ℂ) : Matrix Q3 Q3 ℂ :=
  eij false false ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) + eij true true ⊗ₖ tMat c

/-- **The stable signed factor** `U(c) = A_φ (R_u ⊗ I) A_φ†` with `u = ‖c‖` (`gate:eq:dilation`). -/
def uMat (c : ℂ) : Matrix Q3 Q3 ℂ :=
  aMat c * (rMat ‖c‖ ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)) * (aMat c)ᴴ

theorem aMat_conjTranspose (c : ℂ) : (aMat c)ᴴ = aMat c := by
  rw [aMat, Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_kronecker, eij_conjTranspose, eij_conjTranspose,
    Matrix.conjTranspose_one, tMat_conjTranspose]

theorem eR_ff (u : ℝ) : eij false false * rMat u * eij false false =
    ((Real.sqrt (1 - u) : ℝ) : ℂ) • eij false false := by
  ext b d
  cases b <;> cases d <;> simp [rMat, Matrix.mul_apply]

theorem eR_ft (u : ℝ) : eij false false * rMat u * eij true true =
    (-((Real.sqrt u : ℝ) : ℂ)) • eij false true := by
  ext b d
  cases b <;> cases d <;> simp [rMat, Matrix.mul_apply]

theorem eR_tf (u : ℝ) : eij true true * rMat u * eij false false =
    ((Real.sqrt u : ℝ) : ℂ) • eij true false := by
  ext b d
  cases b <;> cases d <;> simp [rMat, Matrix.mul_apply]

theorem eR_tt (u : ℝ) : eij true true * rMat u * eij true true =
    ((Real.sqrt (1 - u) : ℝ) : ℂ) • eij true true := by
  ext b d
  cases b <;> cases d <;> simp [rMat, Matrix.mul_apply]

/-- **The block form** `U(c) = [[√(1-u) I, -√u T_φ], [√u T_φ, √(1-u) I]]`, i.e.
`U(c) = √(1-u) I + √u (J ⊗ T_φ)`. -/
theorem uMat_eq (c : ℂ) :
    uMat c = ((Real.sqrt (1 - ‖c‖) : ℝ) : ℂ) • (1 : Matrix Q3 Q3 ℂ) +
      ((Real.sqrt ‖c‖ : ℝ) : ℂ) • (jMat ⊗ₖ tMat c) := by
  unfold uMat
  rw [aMat_conjTranspose]
  unfold aMat
  simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    Matrix.one_mul, tMat_mul_self]
  rw [eR_ff, eR_ft, eR_tf, eR_tt]
  have h1 : (1 : Matrix Q3 Q3 ℂ) = eij false false ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) +
      eij true true ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
    rw [← Matrix.add_kronecker, eij_add_eij, Matrix.one_kronecker_one]
  have h2 : jMat ⊗ₖ tMat c = eij true false ⊗ₖ tMat c - eij false true ⊗ₖ tMat c := by
    rw [jMat, sub_kronecker']
  rw [h1, h2]
  simp only [Matrix.smul_kronecker]
  module

theorem rMat_unitary {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    (rMat u)ᴴ * rMat u = 1 ∧ rMat u * (rMat u)ᴴ = 1 := by
  have hs : ((Real.sqrt (1 - u) : ℝ) : ℂ) * ((Real.sqrt (1 - u) : ℝ) : ℂ) +
      ((Real.sqrt u : ℝ) : ℂ) * ((Real.sqrt u : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith),
      Real.mul_self_sqrt h0]
    push_cast; ring
  constructor
  · ext b d
    cases b <;> cases d <;>
      simp [rMat, Matrix.mul_apply, Matrix.conjTranspose_apply,
        ] <;>
      first | linear_combination hs | ring1
  · ext b d
    cases b <;> cases d <;>
      simp [rMat, Matrix.mul_apply, Matrix.conjTranspose_apply,
        ] <;>
      first | linear_combination hs | ring1

theorem aMat_mul_self (c : ℂ) : aMat c * aMat c = 1 := by
  unfold aMat
  simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, tMat_mul_self]
  have e1 : eij false false * eij false false = eij false false := by
    ext b d; cases b <;> cases d <;> simp [Matrix.mul_apply]
  have e2 : eij true true * eij true true = eij true true := by
    ext b d; cases b <;> cases d <;> simp [Matrix.mul_apply]
  have e3 : eij false false * eij true true = 0 := by
    ext b d; cases b <;> cases d <;> simp [Matrix.mul_apply]
  have e4 : eij true true * eij false false = 0 := by
    ext b d; cases b <;> cases d <;> simp [Matrix.mul_apply]
  rw [e1, e2, e3, e4]
  simp only [Matrix.zero_kronecker, add_zero, zero_add]
  rw [← Matrix.add_kronecker, eij_add_eij, Matrix.one_kronecker_one]

/-- `U(c)` is unitary for `‖c‖ ≤ 1`. -/
theorem uMat_unitary {c : ℂ} (hc : ‖c‖ ≤ 1) :
    (uMat c)ᴴ * uMat c = 1 ∧ uMat c * (uMat c)ᴴ = 1 := by
  obtain ⟨hr1, hr2⟩ := rMat_unitary (norm_nonneg c) hc
  have hR1 : (rMat ‖c‖ ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ))ᴴ *
      (rMat ‖c‖ ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)) = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hr1, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.one_kronecker_one]
  have hR2 : (rMat ‖c‖ ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)) *
      (rMat ‖c‖ ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ))ᴴ = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hr2, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.one_kronecker_one]
  have hA := aMat_mul_self c
  have hAh := aMat_conjTranspose c
  unfold uMat
  constructor
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hAh]
    calc _ = aMat c * ((rMat ‖c‖ ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ))ᴴ * (aMat c * aMat c) *
          (rMat ‖c‖ ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ))) * aMat c := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA, Matrix.mul_one, hR1, Matrix.mul_one, hA]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hAh]
    calc _ = aMat c * ((rMat ‖c‖ ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)) * (aMat c * aMat c) *
          (rMat ‖c‖ ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ))ᴴ) * aMat c := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA, Matrix.mul_one, hR2, Matrix.mul_one, hA]

/-- **The action on initial `f = z = 0`** (`gate:eq:factor-action`):
`U(c) (|0⟩⟨0|_f ⊗ I_o ⊗ |0⟩⟨0|_z) = √(1-u) |0⟩⟨0|_f ⊗ I_o ⊗ |0⟩⟨0|_z +
|1⟩⟨0|_f ⊗ (B_+(c) ⊗ |0⟩⟨0|_z + B_-(c) ⊗ |1⟩⟨0|_z)` with `B_± = √u Π_±`. -/
theorem uMat_action (c : ℂ) :
    uMat c * (eij false false ⊗ₖ ((1 : Matrix Bool Bool ℂ) ⊗ₖ eij false false)) =
      (((Real.sqrt (1 - ‖c‖) : ℝ) : ℂ) • eij false false) ⊗ₖ
          ((1 : Matrix Bool Bool ℂ) ⊗ₖ eij false false) +
        eij true false ⊗ₖ ((((Real.sqrt ‖c‖ : ℝ) : ℂ) • piP c) ⊗ₖ eij false false +
          (((Real.sqrt ‖c‖ : ℝ) : ℂ) • piM c) ⊗ₖ eij true false) := by
  rw [uMat_eq, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
    ← Matrix.mul_kronecker_mul, jMat_mul_eij, tMat_eq, Matrix.add_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.mul_one,
    Matrix.one_mul, xMat_mul_eij]
  simp only [Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.kronecker_add]
  module

/-- `U(0) = I`, independently of the phase convention at zero. -/
theorem uMat_zero : uMat 0 = 1 := by
  rw [uMat_eq]
  simp

/-- The Toffoli gate `f, o → z`. -/
def tofMat : Matrix Q3 Q3 ℂ :=
  eij false false ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) + eij true true ⊗ₖ cnotMat

theorem tofMat_conjTranspose : tofMatᴴ = tofMat := by
  rw [tofMat, Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_kronecker, eij_conjTranspose, eij_conjTranspose,
    Matrix.conjTranspose_one, cnotMat, Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_kronecker, eij_conjTranspose, eij_conjTranspose,
    Matrix.conjTranspose_one, xMat_conjTranspose]

/-- **The gate form**: `U(c) = (V_φ)_o · Toffoli_{f,o→z} · (R_u)_f · Toffoli_{f,o→z} · (V_φ†)_o`.
-/
theorem uMat_gates (c : ℂ) :
    uMat c = ((1 : Matrix Bool Bool ℂ) ⊗ₖ (vMat c ⊗ₖ (1 : Matrix Bool Bool ℂ))) * tofMat *
      (rMat ‖c‖ ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)) * tofMat *
      ((1 : Matrix Bool Bool ℂ) ⊗ₖ ((vMat c)ᴴ ⊗ₖ (1 : Matrix Bool Bool ℂ))) := by
  set W : Matrix Q3 Q3 ℂ := (1 : Matrix Bool Bool ℂ) ⊗ₖ (vMat c ⊗ₖ (1 : Matrix Bool Bool ℂ))
    with hW
  set Wh : Matrix Q3 Q3 ℂ := (1 : Matrix Bool Bool ℂ) ⊗ₖ ((vMat c)ᴴ ⊗ₖ (1 : Matrix Bool Bool ℂ))
    with hWh
  have hA : aMat c = W * tofMat * Wh := by
    rw [hW, hWh, tofMat, cnotMat]
    simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
      Matrix.mul_one]
    rw [vMat_mul_conjTranspose, Matrix.one_kronecker_one, aMat, tMat_eq]
    rfl
  have hWR : Wh * (rMat ‖c‖ ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)) * W =
      rMat ‖c‖ ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
    rw [hW, hWh, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_one, ← Matrix.mul_kronecker_mul, vMat_conjTranspose_mul,
      Matrix.mul_one, Matrix.one_kronecker_one]
  have hAh : (aMat c)ᴴ = W * tofMat * Wh := by rw [aMat_conjTranspose, hA]
  unfold uMat
  rw [hAh, hA]
  calc W * tofMat * Wh * (rMat ‖c‖ ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)) *
        (W * tofMat * Wh)
      = W * tofMat * (Wh * (rMat ‖c‖ ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)) * W) *
          tofMat * Wh := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hWR]

/-! ### Stability on all inputs -/

section Norm

open scoped Matrix.Norms.L2Operator

/-- The L2 operator norm of a Kronecker product. -/
theorem norm_one_kronecker_le {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (M : Matrix n n ℂ) : ‖(1 : Matrix m m ℂ) ⊗ₖ M‖ ≤ ‖M‖ := by
  rw [Matrix.cstar_norm_def, Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun x => ?_)
  set xb : m → EuclideanSpace ℂ n := fun b => WithLp.toLp 2 (fun j => x (b, j)) with hxb
  have happ : ∀ b i, (toEuclideanCLM (n := m × n) (𝕜 := ℂ) ((1 : Matrix m m ℂ) ⊗ₖ M) x) (b, i) =
      (toEuclideanCLM (n := n) (𝕜 := ℂ) M (xb b)) i := by
    intro b i
    change ((1 : Matrix m m ℂ) ⊗ₖ M *ᵥ WithLp.ofLp x) (b, i) = (M *ᵥ WithLp.ofLp (xb b)) i
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply, hxb]
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'
      simp [Ne.symm hb']
    · intro h; exact absurd (Finset.mem_univ b) h
  have hx : ‖x‖ ^ 2 = ∑ b, ‖xb b‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    congr 1
    funext b
    rw [EuclideanSpace.norm_sq_eq]
  have hy : ‖toEuclideanCLM (n := m × n) (𝕜 := ℂ) ((1 : Matrix m m ℂ) ⊗ₖ M) x‖ ^ 2 =
      ∑ b, ‖toEuclideanCLM (n := n) (𝕜 := ℂ) M (xb b)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    congr 1
    funext b
    rw [EuclideanSpace.norm_sq_eq]
    congr 1
    funext i
    rw [happ]
  have hle : ‖toEuclideanCLM (n := m × n) (𝕜 := ℂ) ((1 : Matrix m m ℂ) ⊗ₖ M) x‖ ^ 2 ≤
      (‖toEuclideanCLM (n := n) (𝕜 := ℂ) M‖ * ‖x‖) ^ 2 := by
    rw [hy, mul_pow, hx, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ((toEuclideanCLM (n := n) (𝕜 := ℂ) M).le_opNorm _) 2
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hle

theorem norm_kronecker_one_le {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (M : Matrix n n ℂ) : ‖M ⊗ₖ (1 : Matrix m m ℂ)‖ ≤ ‖M‖ := by
  rw [Matrix.cstar_norm_def, Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun x => ?_)
  set xb : m → EuclideanSpace ℂ n := fun b => WithLp.toLp 2 (fun j => x (j, b)) with hxb
  have happ : ∀ i b, (toEuclideanCLM (n := n × m) (𝕜 := ℂ) (M ⊗ₖ (1 : Matrix m m ℂ)) x) (i, b) =
      (toEuclideanCLM (n := n) (𝕜 := ℂ) M (xb b)) i := by
    intro i b
    change (M ⊗ₖ (1 : Matrix m m ℂ) *ᵥ WithLp.ofLp x) (i, b) = (M *ᵥ WithLp.ofLp (xb b)) i
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply, hxb]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'
      simp [Ne.symm hb']
    · intro h; exact absurd (Finset.mem_univ b) h
  have hx : ‖x‖ ^ 2 = ∑ b, ‖xb b‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
    congr 1
    funext b
    rw [EuclideanSpace.norm_sq_eq]
  have hy : ‖toEuclideanCLM (n := n × m) (𝕜 := ℂ) (M ⊗ₖ (1 : Matrix m m ℂ)) x‖ ^ 2 =
      ∑ b, ‖toEuclideanCLM (n := n) (𝕜 := ℂ) M (xb b)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
    congr 1
    funext b
    rw [EuclideanSpace.norm_sq_eq]
    congr 1
    funext i
    rw [happ]
  have hle : ‖toEuclideanCLM (n := n × m) (𝕜 := ℂ) (M ⊗ₖ (1 : Matrix m m ℂ)) x‖ ^ 2 ≤
      (‖toEuclideanCLM (n := n) (𝕜 := ℂ) M‖ * ‖x‖) ^ 2 := by
    rw [hy, mul_pow, hx, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ((toEuclideanCLM (n := n) (𝕜 := ℂ) M).le_opNorm _) 2
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hle

theorem norm_kronecker_le {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (A : Matrix m m ℂ) (B : Matrix n n ℂ) : ‖A ⊗ₖ B‖ ≤ ‖A‖ * ‖B‖ := by
  have e : A ⊗ₖ B = (A ⊗ₖ (1 : Matrix n n ℂ)) * ((1 : Matrix m m ℂ) ⊗ₖ B) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [e]
  exact (norm_mul_le _ _).trans (mul_le_mul (norm_kronecker_one_le A) (norm_one_kronecker_le B)
    (norm_nonneg _) (norm_nonneg _))

theorem jMat_kron_unitary (c : ℂ) : jMat ⊗ₖ tMat c ∈ unitary (Matrix Q3 Q3 ℂ) := by
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    tMat_conjTranspose, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    jMat_conjTranspose_mul_self, jMat_mul_conjTranspose, tMat_mul_self, Matrix.one_kronecker_one]
  exact ⟨rfl, rfl⟩

theorem self_le_sqrt_of_le_one {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : x ≤ Real.sqrt x := by
  rw [Real.le_sqrt h0 h0]
  nlinarith

/-- **`‖U(c) - I‖ ≤ 1 - √(1-u) + √u ≤ 2√u` on all inputs** (`gate:eq:small`, L2 operator norm). -/
theorem norm_uMat_sub_one_le {c : ℂ} (hc : ‖c‖ ≤ 1) :
    ‖uMat c - 1‖ ≤ 1 - Real.sqrt (1 - ‖c‖) + Real.sqrt ‖c‖ ∧
      1 - Real.sqrt (1 - ‖c‖) + Real.sqrt ‖c‖ ≤ 2 * Real.sqrt ‖c‖ := by
  have hu0 := norm_nonneg c
  have hs1 : Real.sqrt (1 - ‖c‖) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hJ : ‖jMat ⊗ₖ tMat c‖ = 1 := CStarRing.norm_of_mem_unitary (jMat_kron_unitary c)
  have e : uMat c - 1 = (((Real.sqrt (1 - ‖c‖) - 1 : ℝ)) : ℂ) • (1 : Matrix Q3 Q3 ℂ) +
      ((Real.sqrt ‖c‖ : ℝ) : ℂ) • (jMat ⊗ₖ tMat c) := by
    rw [uMat_eq, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    abel
  constructor
  · rw [e]
    calc ‖(((Real.sqrt (1 - ‖c‖) - 1 : ℝ)) : ℂ) • (1 : Matrix Q3 Q3 ℂ) +
          ((Real.sqrt ‖c‖ : ℝ) : ℂ) • (jMat ⊗ₖ tMat c)‖
        ≤ ‖(((Real.sqrt (1 - ‖c‖) - 1 : ℝ)) : ℂ) • (1 : Matrix Q3 Q3 ℂ)‖ +
          ‖((Real.sqrt ‖c‖ : ℝ) : ℂ) • (jMat ⊗ₖ tMat c)‖ := norm_add_le _ _
      _ = |Real.sqrt (1 - ‖c‖) - 1| * 1 + |Real.sqrt ‖c‖| * 1 := by
          rw [norm_smul, norm_smul, norm_one, hJ, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
      _ = 1 - Real.sqrt (1 - ‖c‖) + Real.sqrt ‖c‖ := by
          rw [abs_of_nonpos (by linarith), abs_of_nonneg (Real.sqrt_nonneg _)]
          ring
  · have h1 := self_le_sqrt_of_le_one (show 0 ≤ 1 - ‖c‖ by linarith) (by linarith)
    have h2 := self_le_sqrt_of_le_one hu0 hc
    linarith

theorem kronecker_sub' {l m n p : Type*} (A : Matrix l m ℂ) (B C : Matrix n p ℂ) :
    A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by
  ext i j
  simp [Matrix.kroneckerMap_apply, mul_sub]

theorem piP_sub_piP (c c' : ℂ) : piP c - piP c' = (2⁻¹ : ℂ) • eMat (phase c - phase c') := by
  rw [piP_eq, piP_eq]
  ext b d
  cases b <;> cases d <;> simp [eMat] <;> ring

theorem piPM_unitary (z : ℂ) : piP z - piM z ∈ unitary (Matrix Bool Bool ℂ) := by
  have hh : (piP z - piM z)ᴴ = piP z - piM z := by
    rw [Matrix.conjTranspose_sub, piP_conjTranspose, piM_conjTranspose]
  have hsq : (piP z - piM z) * (piP z - piM z) = 1 := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, piP_mul_piP, piM_mul_piM, piP_mul_piM,
      piM_mul_piP, ← piP_add_piM z]
    abel
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose, hh]
  exact ⟨hsq, hsq⟩

theorem norm_eMat (z : ℂ) : ‖eMat z‖ = ‖z‖ := by
  rw [eMat_eq, norm_smul, CStarRing.norm_of_mem_unitary (piPM_unitary z), mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]

theorem norm_xMat : ‖xMat‖ = 1 := by
  refine CStarRing.norm_of_mem_unitary ?_
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose, xMat_conjTranspose, xMat_mul_self]
  exact ⟨rfl, rfl⟩

theorem norm_jMat : ‖jMat‖ = 1 := by
  refine CStarRing.norm_of_mem_unitary ?_
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
  exact ⟨jMat_conjTranspose_mul_self, jMat_mul_conjTranspose⟩

/-- `‖T_φ - T_φ'‖ ≤ |e^{iφ} - e^{iφ'}|`. -/
theorem norm_tMat_sub_le (c c' : ℂ) : ‖tMat c - tMat c'‖ ≤ ‖phase c - phase c'‖ := by
  have hM : ∀ z : ℂ, piM z = 1 - piP z := fun z => by rw [← piP_add_piM z]; abel
  have e : tMat c - tMat c' = (piP c - piP c') ⊗ₖ ((1 : Matrix Bool Bool ℂ) - xMat) := by
    rw [tMat_eq, tMat_eq, hM c, hM c', kronecker_sub', sub_kronecker', sub_kronecker',
      sub_kronecker', sub_kronecker']
    abel
  rw [e]
  calc ‖(piP c - piP c') ⊗ₖ ((1 : Matrix Bool Bool ℂ) - xMat)‖
      ≤ ‖piP c - piP c'‖ * ‖(1 : Matrix Bool Bool ℂ) - xMat‖ := norm_kronecker_le _ _
    _ ≤ ‖piP c - piP c'‖ * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ‖(1 : Matrix Bool Bool ℂ) - xMat‖ ≤ ‖(1 : Matrix Bool Bool ℂ)‖ + ‖xMat‖ :=
              norm_sub_le _ _
          _ = 2 := by rw [norm_one, norm_xMat]; norm_num
    _ = ‖phase c - phase c'‖ := by
        rw [piP_sub_piP, norm_smul, norm_eMat, norm_inv, Complex.norm_ofNat]
        ring

/-- **Stability of the factor in its parameters**: `‖U(c) - U(c')‖ ≤ |√(1-u) - √(1-u')| +
|√u - √u'| + √u' |e^{iφ} - e^{iφ'}|`. -/
theorem norm_uMat_sub_le (c c' : ℂ) :
    ‖uMat c - uMat c'‖ ≤ |Real.sqrt (1 - ‖c‖) - Real.sqrt (1 - ‖c'‖)| +
      |Real.sqrt ‖c‖ - Real.sqrt ‖c'‖| + Real.sqrt ‖c'‖ * ‖phase c - phase c'‖ := by
  have hJ : ‖jMat ⊗ₖ tMat c‖ = 1 := CStarRing.norm_of_mem_unitary (jMat_kron_unitary c)
  have e : uMat c - uMat c' =
      (((Real.sqrt (1 - ‖c‖) - Real.sqrt (1 - ‖c'‖) : ℝ)) : ℂ) • (1 : Matrix Q3 Q3 ℂ) +
      (((Real.sqrt ‖c‖ - Real.sqrt ‖c'‖ : ℝ)) : ℂ) • (jMat ⊗ₖ tMat c) +
      ((Real.sqrt ‖c'‖ : ℝ) : ℂ) • (jMat ⊗ₖ (tMat c - tMat c')) := by
    rw [uMat_eq, uMat_eq, kronecker_sub', Complex.ofReal_sub, Complex.ofReal_sub, sub_smul,
      sub_smul, smul_sub]
    abel
  rw [e]
  have h3 : ‖jMat ⊗ₖ (tMat c - tMat c')‖ ≤ ‖phase c - phase c'‖ :=
    (norm_kronecker_le _ _).trans (by rw [norm_jMat, one_mul]; exact norm_tMat_sub_le c c')
  calc _ ≤ ‖(((Real.sqrt (1 - ‖c‖) - Real.sqrt (1 - ‖c'‖) : ℝ)) : ℂ) • (1 : Matrix Q3 Q3 ℂ)‖ +
        ‖(((Real.sqrt ‖c‖ - Real.sqrt ‖c'‖ : ℝ)) : ℂ) • (jMat ⊗ₖ tMat c)‖ +
        ‖((Real.sqrt ‖c'‖ : ℝ) : ℂ) • (jMat ⊗ₖ (tMat c - tMat c'))‖ := norm_add₃_le
    _ = |Real.sqrt (1 - ‖c‖) - Real.sqrt (1 - ‖c'‖)| + |Real.sqrt ‖c‖ - Real.sqrt ‖c'‖| +
        Real.sqrt ‖c'‖ * ‖jMat ⊗ₖ (tMat c - tMat c')‖ := by
        rw [norm_smul, norm_smul, norm_smul, norm_one, hJ, Complex.norm_real, Complex.norm_real,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), mul_one, mul_one]
    _ ≤ _ := by gcongr

/-- `|√x - √y| ≤ √|x - y|`. -/
theorem abs_sqrt_sub_sqrt_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y| := by
  have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → b ≤ a →
      Real.sqrt a - Real.sqrt b ≤ Real.sqrt (a - b) := by
    intro a b ha hb hab
    have h1 : Real.sqrt a ≤ Real.sqrt b + Real.sqrt (a - b) := by
      rw [Real.sqrt_le_left (by positivity)]
      have := Real.sq_sqrt hb
      have := Real.sq_sqrt (show 0 ≤ a - b by linarith)
      nlinarith [Real.sqrt_nonneg b, Real.sqrt_nonneg (a - b),
        mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg (a - b))]
    linarith
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt h)), abs_of_nonneg (by linarith)]
    exact key x y hx hy h
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.sqrt_le_sqrt h)), abs_of_nonpos (by linarith)]
    have := key y x hy hx h
    rw [show -(x - y) = y - x by ring]
    linarith

/-- **Magnitude accuracy `ξ²` and phase accuracy `ξ` suffice**: for `‖c'‖ ≤ 1`, if
`|‖c‖ - ‖c'‖| ≤ ξ²` and `|e^{iφ} - e^{iφ'}| ≤ ξ`, then `‖U(c) - U(c')‖ ≤ 3ξ`. -/
theorem norm_uMat_sub_le_of_accuracy {c c' : ℂ} (hc : ‖c‖ ≤ 1) (hc' : ‖c'‖ ≤ 1) {ξ : ℝ}
    (hξ : 0 ≤ ξ) (hu : |‖c‖ - ‖c'‖| ≤ ξ ^ 2) (hp : ‖phase c - phase c'‖ ≤ ξ) :
    ‖uMat c - uMat c'‖ ≤ 3 * ξ := by
  have h0 := norm_uMat_sub_le c c'
  have hξ2 : Real.sqrt (ξ ^ 2) = ξ := Real.sqrt_sq hξ
  have h1 : |Real.sqrt (1 - ‖c‖) - Real.sqrt (1 - ‖c'‖)| ≤ ξ := by
    refine (abs_sqrt_sub_sqrt_le _ _ (by linarith) (by linarith)).trans ?_
    rw [← hξ2]
    apply Real.sqrt_le_sqrt
    rw [show 1 - ‖c‖ - (1 - ‖c'‖) = -(‖c‖ - ‖c'‖) by ring, abs_neg]
    exact hu
  have h2 : |Real.sqrt ‖c‖ - Real.sqrt ‖c'‖| ≤ ξ := by
    refine (abs_sqrt_sub_sqrt_le _ _ (norm_nonneg _) (norm_nonneg _)).trans ?_
    rw [← hξ2]
    exact Real.sqrt_le_sqrt hu
  have h3 : Real.sqrt ‖c'‖ * ‖phase c - phase c'‖ ≤ ξ := by
    have hs : Real.sqrt ‖c'‖ ≤ 1 := Real.sqrt_le_one.mpr hc'
    calc Real.sqrt ‖c'‖ * ‖phase c - phase c'‖ ≤ 1 * ‖phase c - phase c'‖ :=
          mul_le_mul_of_nonneg_right hs (norm_nonneg _)
      _ ≤ ξ := by rw [one_mul]; exact hp
  linarith

/-- **The threshold**: for `u ≤ ξ²/16`, replacing `c` by zero costs at most `ξ/2`. -/
theorem norm_uMat_sub_zero_le {c : ℂ} (hc : ‖c‖ ≤ 1) {ξ : ℝ} (hξ : 0 ≤ ξ)
    (hu : ‖c‖ ≤ ξ ^ 2 / 16) : ‖uMat c - uMat 0‖ ≤ ξ / 2 := by
  rw [uMat_zero]
  obtain ⟨h1, h2⟩ := norm_uMat_sub_one_le hc
  have h3 : Real.sqrt ‖c‖ ≤ ξ / 4 := by
    rw [show ξ / 4 = Real.sqrt ((ξ / 4) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  linarith

end Norm

end

end GateOptimalPrecision
