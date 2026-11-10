import GateOptimalPrecision.BlockOp
import GateOptimalPrecision.JointAlgebra

/-!
# The gates of the local factor

The stable signed factor `U(c)` of the paragraph "A stable constant-dimensional signed factor" of
Section `gate:sec:native` (`uMat`) is implemented from two binary words held on wires outside its
three qubits: an angle word for the magnitude and a phase word.

* `alphaVal`: the `b_T`-bit word `w` encodes `α(w) = Σ_j w_j π / 2^(j+2) ∈ [0, π/2]`; the phase word
  is `phiVal` of the baseline, `φ(v) = Σ_j v_j 2π / 2^(j+1)`.
* `phMat φ = diag(e^{iφ}, 1)` and `rot2 α = [[cos α, -sin α], [sin α, cos α]]`, the rotation
  `R_y(2α)`; `rot2_eq_rMat`: `rot2 α = R_u` with `u = sin² α` for `0 ≤ α ≤ π/2`.
* `uImpl α φ`, the product of the gate matrices below, and `uImpl_eq_uMat`:
  `uImpl α φ = U(sin² α · e^{iφ})` for `0 ≤ α ≤ π/2`.
* `norm_uImpl_sub_le`: "`u ≤ ξ²/16` may be replaced by zero with error at most `ξ/2`. Above that
  threshold, magnitude accuracy of order `ξ²` and phase accuracy of order `ξ` suffice." If either
  `‖c‖ ≤ ξ²/16` and `α = 0`, or `|sin² α - ‖c‖| ≤ ξ²` and `|e^{iφ} - c/|c|| ≤ ξ`, then
  `‖uImpl α φ - U(c)‖ ≤ 3ξ` for `‖c‖ ≤ 1` (L2 operator norm).
* `locGates e tw pw` on the flag `f = e 0`, the orientation `o = e 1` and the sign `z = e 2`:
  the phase gates `diag(e^{-iφ_j}, 1)` on `o`, one per bit of the phase word and controlled by
  it; `H` on `o`; the Toffoli gate `f, o → z`; the rotations `rot2(π/2^(j+2))` on `f`, one per bit
  of the angle word and controlled by it; the Toffoli gate; `H` on `o`; the phase gates
  `diag(e^{iφ_j}, 1)`. That is `U(c) = (V_φ)_o · Toffoli · (R_u)_f · Toffoli · (V_φ†)_o`
  (`uMat_gates`) with `V_φ = diag(e^{iφ}, 1) H`. There are `2 b_P + b_T + 4` gates with at most
  two controls each (`locGates_length`, `locGates_ok`).
* `gRun_locGates`: the gates act on the three qubits as the block `uImpl α φ`, with `α` and `φ`
  read from the words.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace GateOptimalPrecision

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open NativeSignedFactor (phase)
open scoped InnerProduct InnerProductSpace BigOperators ComplexConjugate Kronecker Matrix

/-! ### The angle word -/

/-- The angle `α ∈ [0, π/2]` encoded by a binary word. -/
def alphaVal {n : ℕ} (w : Fin n → Bool) : ℝ :=
  ∑ j : Fin n, if w j then Real.pi / 2 ^ (j.val + 2) else 0

theorem alphaVal_nonneg {n : ℕ} (w : Fin n → Bool) : 0 ≤ alphaVal w := by
  unfold alphaVal
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · positivity
  · exact le_refl 0

theorem alphaVal_le {n : ℕ} (w : Fin n → Bool) : alphaVal w ≤ Real.pi / 2 := by
  unfold alphaVal
  have h1 : (∑ j : Fin n, if w j then Real.pi / 2 ^ (j.val + 2) else 0) ≤
      ∑ j : Fin n, Real.pi / 2 ^ (j.val + 2) := by
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · exact le_refl _
    · positivity
  have h2 : ∑ j : Fin n, Real.pi / 2 ^ (j.val + 2) =
      Real.pi / 4 * ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j := by
    rw [Fin.sum_univ_eq_sum_range (fun j => Real.pi / 2 ^ (j + 2)) n, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [one_div_pow, pow_add]
    ring
  have h3 : ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j ≤ 2 := sum_geometric_two_le n
  have h4 : Real.pi / 4 * ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j ≤ Real.pi / 4 * 2 :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  linarith

/-! ### One-qubit gates -/

/-- The phase gate `diag(e^{iφ}, 1)`. -/
def phMat (φ : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal (fun b => if b then 1 else Complex.exp (φ * Complex.I))

theorem phMat_mul (φ ψ : ℝ) : phMat φ * phMat ψ = phMat (φ + ψ) := by
  unfold phMat
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext b
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [← Complex.exp_add, Complex.ofReal_add, add_mul]
  · simp

theorem phMat_zero : phMat 0 = 1 := by
  unfold phMat
  rw [← Matrix.diagonal_one]
  congr 1
  funext b
  cases b <;> simp

theorem phMat_conjTranspose (φ : ℝ) : (phMat φ)ᴴ = phMat (-φ) := by
  unfold phMat
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext b
  cases b
  · simp only [Pi.star_apply, Bool.false_eq_true, if_false, RCLike.star_def, ← Complex.exp_conj,
      map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
    ring_nf
  · simp

theorem phMat_unitary (φ : ℝ) : UnitaryMat (phMat φ) := by
  constructor
  · rw [phMat_conjTranspose, phMat_mul, neg_add_cancel, phMat_zero]
  · rw [phMat_conjTranspose, phMat_mul, add_neg_cancel, phMat_zero]

/-- The real rotation `R_y(2α) = [[cos α, -sin α], [sin α, cos α]]`. -/
def rot2 (α : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.of fun b d => if b = d then (Real.cos α : ℂ)
    else if b then (Real.sin α : ℂ) else -(Real.sin α : ℂ)

theorem rot2_mul (α β : ℝ) : rot2 α * rot2 β = rot2 (α + β) := by
  ext b d
  cases b <;> cases d <;>
    simp [rot2, Matrix.mul_apply, Real.cos_add, Real.sin_add] <;> ring

theorem rot2_zero : rot2 0 = 1 := by
  ext b d
  cases b <;> cases d <;> simp [rot2]

theorem rot2_conjTranspose (α : ℝ) : (rot2 α)ᴴ = rot2 (-α) := by
  ext b d
  cases b <;> cases d <;>
    simp [rot2, Matrix.conjTranspose_apply, -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem rot2_unitary (α : ℝ) : UnitaryMat (rot2 α) := by
  constructor
  · rw [rot2_conjTranspose, rot2_mul, neg_add_cancel, rot2_zero]
  · rw [rot2_conjTranspose, rot2_mul, add_neg_cancel, rot2_zero]

/-- For `0 ≤ α ≤ π/2`, `rot2 α` is `R_u` with `u = sin² α`. -/
theorem rot2_eq_rMat {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ Real.pi / 2) :
    rot2 α = rMat (Real.sin α ^ 2) := by
  have hc : 0 ≤ Real.cos α := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h1⟩
  have hs : 0 ≤ Real.sin α := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have e1 : Real.sqrt (1 - Real.sin α ^ 2) = Real.cos α := by
    rw [← Real.cos_sq', Real.sqrt_sq hc]
  have e2 : Real.sqrt (Real.sin α ^ 2) = Real.sin α := Real.sqrt_sq hs
  unfold rot2 rMat
  rw [e1, e2]

theorem hMat_conjTranspose : hMatᴴ = hMat := by
  ext b d
  cases b <;> cases d <;> simp [hMat, Matrix.conjTranspose_apply]

theorem hMat_unitary : UnitaryMat hMat := by
  constructor <;> rw [hMat_conjTranspose, hMat_mul_self]

/-! ### Three-qubit identities -/

theorem eij_ff_mul_ff : eij false false * eij false false = eij false false := by
  ext b d; cases b <;> cases d <;> simp [Matrix.mul_apply]

theorem eij_tt_mul_tt : eij true true * eij true true = eij true true := by
  ext b d; cases b <;> cases d <;> simp [Matrix.mul_apply]

theorem eij_ff_mul_tt : eij false false * eij true true = 0 := by
  ext b d; cases b <;> cases d <;> simp [Matrix.mul_apply]

theorem eij_tt_mul_ff : eij true true * eij false false = 0 := by
  ext b d; cases b <;> cases d <;> simp [Matrix.mul_apply]

theorem cnotMat_mul_self : cnotMat * cnotMat = 1 := by
  unfold cnotMat
  simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, xMat_mul_self, eij_ff_mul_ff, eij_tt_mul_tt, eij_ff_mul_tt, eij_tt_mul_ff,
    Matrix.zero_kronecker, add_zero, zero_add]
  rw [← Matrix.add_kronecker, eij_add_eij, Matrix.one_kronecker_one]

theorem tofMat_mul_self : tofMat * tofMat = 1 := by
  unfold tofMat
  simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, cnotMat_mul_self, eij_ff_mul_ff, eij_tt_mul_tt, eij_ff_mul_tt, eij_tt_mul_ff,
    Matrix.zero_kronecker, add_zero, zero_add]
  rw [← Matrix.add_kronecker, eij_add_eij, Matrix.one_kronecker_one]

/-- `1 ⊗ (A B ⊗ 1) = (1 ⊗ (A ⊗ 1)) (1 ⊗ (B ⊗ 1))`. -/
theorem kron_mid_mul (A B : Matrix Bool Bool ℂ) :
    (1 : Matrix Bool Bool ℂ) ⊗ₖ ((A * B) ⊗ₖ (1 : Matrix Bool Bool ℂ)) =
      ((1 : Matrix Bool Bool ℂ) ⊗ₖ (A ⊗ₖ (1 : Matrix Bool Bool ℂ))) *
        ((1 : Matrix Bool Bool ℂ) ⊗ₖ (B ⊗ₖ (1 : Matrix Bool Bool ℂ))) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one]

/-- **The matrix of the local factor gates** (last gate leftmost):
`diag(e^{iφ},1)_o H_o Toffoli (rot2 α)_f Toffoli H_o diag(e^{-iφ},1)_o`. -/
def uImpl (α φ : ℝ) : Matrix Q3 Q3 ℂ :=
  ((1 : Matrix Bool Bool ℂ) ⊗ₖ (phMat φ ⊗ₖ (1 : Matrix Bool Bool ℂ))) *
    ((1 : Matrix Bool Bool ℂ) ⊗ₖ (hMat ⊗ₖ (1 : Matrix Bool Bool ℂ))) * tofMat *
    (rot2 α ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)) * tofMat *
    ((1 : Matrix Bool Bool ℂ) ⊗ₖ (hMat ⊗ₖ (1 : Matrix Bool Bool ℂ))) *
    ((1 : Matrix Bool Bool ℂ) ⊗ₖ (phMat (-φ) ⊗ₖ (1 : Matrix Bool Bool ℂ)))

/-- The entry implemented by the words, `sin² α · e^{iφ}`. -/
def cImpl (α φ : ℝ) : ℂ := ((Real.sin α ^ 2 : ℝ) : ℂ) * Complex.exp (φ * Complex.I)

theorem norm_cImpl (α φ : ℝ) : ‖cImpl α φ‖ = Real.sin α ^ 2 := by
  rw [cImpl, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]

theorem phase_cImpl {α : ℝ} (φ : ℝ) (hs : Real.sin α ≠ 0) :
    phase (cImpl α φ) = Complex.exp (φ * Complex.I) := by
  have h2 : ((Real.sin α ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 hs
  have hne : cImpl α φ ≠ 0 := mul_ne_zero h2 (Complex.exp_ne_zero _)
  unfold phase
  rw [if_neg hne, norm_cImpl, cImpl, mul_div_cancel_left₀ _ h2]

theorem cImpl_zero (φ : ℝ) : cImpl 0 φ = 0 := by
  simp [cImpl]

/-- **The gates implement the factor**: `uImpl α φ = U(sin² α · e^{iφ})` for `0 ≤ α ≤ π/2`. -/
theorem uImpl_eq_uMat {α : ℝ} (φ : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ Real.pi / 2) :
    uImpl α φ = uMat (cImpl α φ) := by
  by_cases hs : Real.sin α = 0
  · have hα : α = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])).mp hs
    subst hα
    rw [cImpl_zero, uMat_zero, uImpl, rot2_zero, Matrix.one_kronecker_one, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc tofMat tofMat, tofMat_mul_self, Matrix.one_mul,
      ← Matrix.mul_assoc ((1 : Matrix Bool Bool ℂ) ⊗ₖ (hMat ⊗ₖ (1 : Matrix Bool Bool ℂ))),
      ← kron_mid_mul hMat hMat, hMat_mul_self, Matrix.one_kronecker_one,
      Matrix.one_kronecker_one, Matrix.one_mul, ← kron_mid_mul, phMat_mul, add_neg_cancel,
      phMat_zero, Matrix.one_kronecker_one, Matrix.one_kronecker_one]
  · have hv : vMat (cImpl α φ) = phMat φ * hMat := by
      unfold vMat phMat
      rw [phase_cImpl φ hs]
    rw [uMat_gates, norm_cImpl, ← rot2_eq_rMat h0 h1, hv, Matrix.conjTranspose_mul,
      hMat_conjTranspose, phMat_conjTranspose, kron_mid_mul, kron_mid_mul, uImpl]
    simp only [Matrix.mul_assoc]

/-! ### Accuracy -/

section Norm

open scoped Matrix.Norms.L2Operator

/-- `norm_uMat_sub_le_of_accuracy` with the phase of `c'` needed only for `c' ≠ 0`. -/
theorem norm_uMat_sub_le_of_accuracy' {c c' : ℂ} (hc : ‖c‖ ≤ 1) (hc' : ‖c'‖ ≤ 1) {ξ : ℝ}
    (hξ : 0 ≤ ξ) (hu : |‖c‖ - ‖c'‖| ≤ ξ ^ 2) (hp : c' ≠ 0 → ‖phase c - phase c'‖ ≤ ξ) :
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
    by_cases h : c' = 0
    · rw [h, norm_zero, Real.sqrt_zero, zero_mul]
      exact hξ
    · have hs : Real.sqrt ‖c'‖ ≤ 1 := Real.sqrt_le_one.mpr hc'
      calc Real.sqrt ‖c'‖ * ‖phase c - phase c'‖ ≤ 1 * ‖phase c - phase c'‖ :=
            mul_le_mul_of_nonneg_right hs (norm_nonneg _)
        _ ≤ ξ := by rw [one_mul]; exact hp h
  linarith

/-- **The accuracy of the local factor gates** (L2 operator norm): for `‖c‖ ≤ 1` and
`0 ≤ α ≤ π/2`, if either `‖c‖ ≤ ξ²/16` and `α = 0` (the threshold), or `|sin² α - ‖c‖| ≤ ξ²` and
`|e^{iφ} - c/|c|| ≤ ξ`, then `‖uImpl α φ - U(c)‖ ≤ 3ξ`. -/
theorem norm_uImpl_sub_le {c : ℂ} (hc : ‖c‖ ≤ 1) {α φ ξ : ℝ} (h0 : 0 ≤ α)
    (h1 : α ≤ Real.pi / 2) (hξ : 0 ≤ ξ)
    (hacc : (‖c‖ ≤ ξ ^ 2 / 16 ∧ α = 0) ∨
      (|Real.sin α ^ 2 - ‖c‖| ≤ ξ ^ 2 ∧ ‖Complex.exp (φ * Complex.I) - phase c‖ ≤ ξ)) :
    ‖uImpl α φ - uMat c‖ ≤ 3 * ξ := by
  rw [uImpl_eq_uMat φ h0 h1, norm_sub_rev]
  rcases hacc with ⟨hsmall, hα⟩ | ⟨hu, hp⟩
  · subst hα
    rw [cImpl_zero]
    have := norm_uMat_sub_zero_le hc hξ hsmall
    linarith
  · have hc' : ‖cImpl α φ‖ ≤ 1 := by
      rw [norm_cImpl]
      exact Real.sin_sq_le_one α
    refine norm_uMat_sub_le_of_accuracy' hc hc' hξ ?_ ?_
    · rw [norm_cImpl, abs_sub_comm]
      exact hu
    · intro hne
      have hs : Real.sin α ≠ 0 := by
        intro h
        apply hne
        simp [cImpl, h]
      rw [phase_cImpl φ hs, norm_sub_rev]
      exact hp

end Norm

/-! ### The gates -/

section Gates

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- The phase gates `diag(e^{i s φ_j}, 1)` on `o`, one per bit `j` of the phase word. -/
def phGates {n : ℕ} (o : W) (pw : Fin n → W) (s : ℝ) : List (Gate W) :=
  (List.finRange n).map (fun j =>
    ⟨[(pw j, true)], o, phMat (s * (2 * Real.pi / 2 ^ (j.val + 1)))⟩)

/-- The rotations `rot2(π/2^(j+2))` on `f`, one per bit `j` of the angle word. -/
def ryGates {n : ℕ} (f : W) (tw : Fin n → W) : List (Gate W) :=
  (List.finRange n).map (fun j => ⟨[(tw j, true)], f, rot2 (Real.pi / 2 ^ (j.val + 2))⟩)

/-- The Hadamard gate on `o`. -/
def hGate (o : W) : Gate W := ⟨[], o, hMat⟩

/-- The Toffoli gate `f, o → z`. -/
def tofGate (f o z : W) : Gate W := ⟨[(f, true), (o, true)], z, pauliX⟩

/-- **The local factor gates** on the flag `e 0`, the orientation `e 1` and the sign `e 2`, with
the angle word on the wires `tw` and the phase word on the wires `pw`. -/
def locGates {bT bP : ℕ} (e : Fin 3 → W) (tw : Fin bT → W) (pw : Fin bP → W) : List (Gate W) :=
  phGates (e 1) pw (-1) ++ [hGate (e 1)] ++ [tofGate (e 0) (e 1) (e 2)] ++ ryGates (e 0) tw ++
    [tofGate (e 0) (e 1) (e 2)] ++ [hGate (e 1)] ++ phGates (e 1) pw 1

omit [Fintype W] [DecidableEq W] in
theorem locGates_length {bT bP : ℕ} (e : Fin 3 → W) (tw : Fin bT → W) (pw : Fin bP → W) :
    (locGates e tw pw).length = 2 * bP + bT + 4 := by
  simp only [locGates, phGates, ryGates, List.length_append, List.length_map,
    List.length_finRange, List.length_cons, List.length_nil]
  omega

omit [Fintype W] [DecidableEq W] in
/-- The local factor gates are elementary: at most two controls, all off the target. -/
theorem locGates_ok {bT bP : ℕ} {e : Fin 3 → W} (he : Function.Injective e) {tw : Fin bT → W}
    {pw : Fin bP → W} (htw : ∀ j a, e a ≠ tw j) (hpw : ∀ j a, e a ≠ pw j) :
    ∀ g ∈ locGates e tw pw, GateOK 2 g := by
  have hph : ∀ s : ℝ, ∀ g ∈ phGates (e 1) pw s, GateOK 2 g := by
    intro s g hg
    simp only [phGates, List.mem_map] at hg
    obtain ⟨j, _, rfl⟩ := hg
    refine ⟨by simp, ?_, phMat_unitary _⟩
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rw [hc]
    exact fun h => hpw j 1 h.symm
  have hry : ∀ g ∈ ryGates (e 0) tw, GateOK 2 g := by
    intro g hg
    simp only [ryGates, List.mem_map] at hg
    obtain ⟨j, _, rfl⟩ := hg
    refine ⟨by simp, ?_, rot2_unitary _⟩
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rw [hc]
    exact fun h => htw j 0 h.symm
  have hH : GateOK 2 (hGate (e 1)) := ⟨by simp [hGate], by simp [hGate], hMat_unitary⟩
  have hT : GateOK 2 (tofGate (e 0) (e 1) (e 2)) := by
    refine ⟨by simp [tofGate], ?_, pauliX_unitary⟩
    intro c hc
    simp only [tofGate, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact fun h => absurd (he h) (by decide)
    · exact fun h => absurd (he h) (by decide)
  intro g hg
  simp only [locGates, List.mem_append, List.mem_singleton] at hg
  rcases hg with (((((h | h) | h) | h) | h) | h) | h
  · exact hph (-1) g h
  · rw [h]; exact hH
  · rw [h]; exact hT
  · exact hry g h
  · rw [h]; exact hT
  · rw [h]; exact hH
  · exact hph 1 g h

omit [Fintype W] [DecidableEq W] in
theorem selProd_ph {n : ℕ} (o : W) (pw : Fin n → W) (s : ℝ) (x : Cfg W) :
    selProd (phGates o pw s) x = phMat (s * phiVal (fun j => x (pw j))) := by
  have key : ∀ l : List (Fin n), selProd (l.map (fun j =>
      (⟨[(pw j, true)], o, phMat (s * (2 * Real.pi / 2 ^ (j.val + 1)))⟩ : Gate W))) x =
      phMat (s * (l.map (fun j => if x (pw j) then 2 * Real.pi / 2 ^ (j.val + 1)
        else 0)).sum) := by
    intro l
    induction l with
    | nil => simp only [List.map_nil, selProd, List.sum_nil, mul_zero, phMat_zero]
    | cons j l ih =>
        simp only [List.map_cons, selProd, ih, List.sum_cons, ctrlOK_cons, ctrlOK_nil,
          Bool.and_true]
        cases hp : x (pw j) <;> simp [phMat_mul, mul_add, add_comm]
  unfold phGates phiVal
  rw [key, Fin.sum_univ_def]

omit [Fintype W] [DecidableEq W] in
theorem selProd_ry {n : ℕ} (f : W) (tw : Fin n → W) (x : Cfg W) :
    selProd (ryGates f tw) x = rot2 (alphaVal (fun j => x (tw j))) := by
  have key : ∀ l : List (Fin n), selProd (l.map (fun j =>
      (⟨[(tw j, true)], f, rot2 (Real.pi / 2 ^ (j.val + 2))⟩ : Gate W))) x =
      rot2 ((l.map (fun j => if x (tw j) then Real.pi / 2 ^ (j.val + 2) else 0)).sum) := by
    intro l
    induction l with
    | nil => simp only [List.map_nil, selProd, List.sum_nil, rot2_zero]
    | cons j l ih =>
        simp only [List.map_cons, selProd, ih, List.sum_cons, ctrlOK_cons, ctrlOK_nil,
          Bool.and_true]
        cases hp : x (tw j) <;> simp [rot2_mul, add_comm]
  unfold ryGates alphaVal
  rw [key, Fin.sum_univ_def]

/-- The phase gates on `o` form the phase `diag(e^{i s φ}, 1)` of the word. -/
theorem gRun_phGates {n : ℕ} (o : W) (pw : Fin n → W) (s : ℝ) :
    gRun (Q := Q) (phGates o pw s) =
      condOp o (fun x => phMat (s * phiVal (fun j => x (pw j)))) := by
  have ht : ∀ g ∈ phGates o pw s, g.t = o := by
    intro g hg
    simp only [phGates, List.mem_map] at hg
    obtain ⟨j, _, rfl⟩ := hg
    rfl
  rw [gRun_same_target o _ ht]
  congr 1
  funext x
  exact selProd_ph o pw s x

/-- The rotations on `f` form the rotation `rot2 α` of the word. -/
theorem gRun_ryGates {n : ℕ} (f : W) (tw : Fin n → W) :
    gRun (Q := Q) (ryGates f tw) = condOp f (fun x => rot2 (alphaVal (fun j => x (tw j)))) := by
  have ht : ∀ g ∈ ryGates f tw, g.t = f := by
    intro g hg
    simp only [ryGates, List.mem_map] at hg
    obtain ⟨j, _, rfl⟩ := hg
    rfl
  rw [gRun_same_target f _ ht]
  congr 1
  funext x
  exact selProd_ry f tw x

/-- The phase gates on the orientation qubit of a block. -/
theorem gRun_phGates_blk {n : ℕ} {e : Fin 3 → W} (he : Function.Injective e) (pw : Fin n → W)
    (hpw : ∀ j a, e a ≠ pw j) (s : ℝ) :
    gRun (Q := Q) (phGates (e 1) pw s) = localOp e he (fun x => matOp (blk
      ((1 : Matrix Bool Bool ℂ) ⊗ₖ (phMat (s * phiVal (fun j => x (pw j))) ⊗ₖ
        (1 : Matrix Bool Bool ℂ))))) := by
  have hu : ∀ x x' : Cfg W, (∀ w, (∀ a, e a ≠ w) → x w = x' w) →
      phMat (s * phiVal (fun j => x (pw j))) = phMat (s * phiVal (fun j => x' (pw j))) := by
    intro x x' hx
    have h : (fun j => x (pw j)) = (fun j => x' (pw j)) :=
      funext fun j => hx (pw j) (fun a => hpw j a)
    rw [h]
  rw [gRun_phGates, condOp_outer he 1 _ hu]
  congr 1
  funext x
  exact condOp_one_eq_blk _

/-- The rotations on the flag of a block. -/
theorem gRun_ryGates_blk {n : ℕ} {e : Fin 3 → W} (he : Function.Injective e) (tw : Fin n → W)
    (htw : ∀ j a, e a ≠ tw j) :
    gRun (Q := Q) (ryGates (e 0) tw) = localOp e he (fun x => matOp (blk
      (rot2 (alphaVal (fun j => x (tw j))) ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)))) := by
  have hu : ∀ x x' : Cfg W, (∀ w, (∀ a, e a ≠ w) → x w = x' w) →
      rot2 (alphaVal (fun j => x (tw j))) = rot2 (alphaVal (fun j => x' (tw j))) := by
    intro x x' hx
    have h : (fun j => x (tw j)) = (fun j => x' (tw j)) :=
      funext fun j => hx (tw j) (fun a => htw j a)
    rw [h]
  rw [gRun_ryGates, condOp_outer he 0 _ hu]
  congr 1
  funext x
  exact condOp_zero_eq_blk _

/-- The Hadamard gate on the orientation qubit of a block. -/
theorem hGate_op_blk {e : Fin 3 → W} (he : Function.Injective e) :
    (hGate (e 1)).op (Q := Q) = localOp e he (fun _ => matOp (blk
      ((1 : Matrix Bool Bool ℂ) ⊗ₖ (hMat ⊗ₖ (1 : Matrix Bool Bool ℂ))))) := by
  have h1 : (hGate (e 1)).op (Q := Q) = condOp (e 1) (fun _ => hMat) := by
    simp only [Gate.op, hGate, gateOp, ctrlOK_nil, if_true]
  rw [h1, condOp_outer he 1 _ (fun _ _ _ => rfl)]
  congr 1
  funext x
  exact condOp_one_eq_blk _

/-- The Toffoli gate on a block. -/
theorem tofGate_op_blk {e : Fin 3 → W} (he : Function.Injective e) :
    (tofGate (e 0) (e 1) (e 2)).op (Q := Q) = localOp e he (fun _ => matOp (blk tofMat)) := by
  rw [← gateOp_tof_eq_blk, GateODE.localOp_gateOp he]
  rfl

/-- **The local factor gates act as the block `uImpl α φ`**, with `α` and `φ` read from the
words. -/
theorem gRun_locGates {bT bP : ℕ} {e : Fin 3 → W} (he : Function.Injective e) (tw : Fin bT → W)
    (pw : Fin bP → W) (htw : ∀ j a, e a ≠ tw j) (hpw : ∀ j a, e a ≠ pw j) :
    gRun (Q := Q) (locGates e tw pw) = localOp e he (fun x => matOp (blk
      (uImpl (alphaVal (fun j => x (tw j))) (phiVal (fun j => x (pw j)))))) := by
  unfold locGates
  simp only [gRun_append, gRun_singleton]
  rw [gRun_phGates_blk he pw hpw (-1), gRun_phGates_blk he pw hpw 1, hGate_op_blk he,
    tofGate_op_blk he, gRun_ryGates_blk he tw htw]
  simp only [localOp_comp, matOp_mul, ← blk_mul]
  congr 1
  funext x
  simp only [uImpl, Matrix.mul_assoc, neg_one_mul, one_mul]

end Gates

end

end GateOptimalPrecision
