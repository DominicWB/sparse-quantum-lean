import GateEfficientSigned.Binary
import GateEfficientBitBudget.NonVacuity

/-!
# The signed endpoints are not vacuous at a negative time

The hypotheses of the signed endpoints are those of the released binary-data endpoints for the
time `|t|`. This file checks that they hold together at the negative time `t = -1` for a
Hamiltonian that is not zero, and that there the released circuit for `|t|` does not meet the
error bound against `exp(-itĤ)`, while the signed circuit does:

* `wordData`: one-point binary data on the index register `Cfg (Fin 0)` (one index, one slot,
  `b` stored bits per component, the decoder `c₀ · gauss`, every stored entry the word `w`, the
  identity oracles), the released `GateBitBudget.pointData` with an arbitrary stored word;
* `oneWord`, `gauss_oneWord`, `wordData_matrix`, `wordData_hamiltonian`: with two-bit components,
  the word `oneWord` decodes to `1`, so the matrix of `wordData Y 2 1 oneWord` is the identity
  and the simulated Hamiltonian `Ĥ` is the identity on the system register;
* `exp_smul_one_reg`, `one_lt_norm_exp_sub`: on that register `exp(-itĤ) = e^{-it} · 1`, and
  `|e^{i} - e^{-i}| = 2 sin 1 > 1`;
* `error_sep`, `binarySim_error_ge`: a circuit within `ε` of `ι U₂` on an isometric embedding is
  at least `‖U₁ ψ - U₂ ψ‖ - ε` from `ι U₁` for every unit vector `ψ`; so, under the hypotheses of
  the released `GateBinary.binary_simulation` for `|t|`, the released circuit for `|t|` is at
  least `‖e^{-itĤ} ψ - e^{-i|t|Ĥ} ψ‖ - ε` from `exp(-itĤ)`;
* `hs_signed_all_hyps`: for `s = 1 = 2^0` slot, `t = -1` and `ε = 1/2`, the data
  `wordData Unit 2 1 oneWord`, some `b_data ≥ 2`, `ζ = ε/(442368 q)` and a rescaling
  `γ ∈ (0, 1]` (in the proof, that of the released `GateBitBudget.binary_simulation_bits` for
  `|t|`) satisfy every hypothesis of `binary_simulation_bits_signed` and of `binarySim_error_ge`
  (with `48 d ζ ≤ ε`); the circuit `binarySimSigned` has the gate bound `10¹⁵ q (𝔟_H + 1)³` and is
  within `ε` of `exp(-itĤ)`, and the two evolutions differ by more than `2ε = 1` on a unit vector
  (by `2 sin 1`). With `binarySim_error_ge`, the released circuit for `|t|` is therefore farther
  than `ε` from `exp(-itĤ)`. On this one-dimensional system the two evolutions differ by the
  global phase `e^{2i}`, to which the full-output error is sensitive.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000

namespace SparseHamiltonian.GateSigned

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.OracleCircuit CayleyClockInterface
open SparseHamiltonian.GateBitBudget
open SparseHamiltonian.GateCircuit.Sim (fDeg simM simR SimWire io io_apply)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### One-point binary data with a stored word -/

/-- **One-point binary data storing the word `w`**: the index register `Cfg (Fin 0)` (one index),
one slot, `b` stored bits per component, the decoder `c₀ · gauss`, every stored entry the word
`w`, and the identity row and column oracles; the inputs `Y` are arbitrary. -/
def wordData (Y : Type) (b : ℕ) (c0 : ℝ) (w : Cfg (VW b)) : Data Y (Cfg (Fin 0)) (Cfg (VW b)) 1
    where
  slot := ⟨fun _ => default, fun _ _ _ => Subsingleton.elim _ _⟩
  slots_pos := one_pos
  scale := 1 + ∑ z : Cfg (VW b), ‖(c0 : ℂ) * gauss z‖
  scale_pos := by positivity
  matrix := fun _ _ _ => (c0 : ℂ) * gauss w
  table := fun _ _ => w
  decode := fun _ z => (c0 : ℂ) * gauss z
  decode_bound := fun _ z => by
    have h := Finset.single_le_sum (f := fun z : Cfg (VW b) => ‖(c0 : ℂ) * gauss z‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ z)
    linarith
  decoded := fun _ _ _ => rfl
  rowloc := fun _ _ _ => default
  colloc := fun _ _ _ => default
  row_injective := fun _ _ _ _ _ => Subsingleton.elim _ _
  column_injective := fun _ _ _ _ _ => Subsingleton.elim _ _
  row_covers := fun _ _ _ _ => by
    unfold SparseSlotStates.selected
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, Subsingleton.elim _ _⟩
  column_covers := fun _ _ _ _ => by
    unfold SparseSlotStates.selected
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, Subsingleton.elim _ _⟩
  rowOracle := fun _ => 1
  columnOracle := fun _ => 1
  row_unitary := fun _ => by simp [IsUnitary]
  column_unitary := fun _ => by simp [IsUnitary]
  row_valid := fun _ _ _ => by
    change EuclideanSpace.single _ 1 = _
    rfl
  column_valid := fun _ j k => by
    change EuclideanSpace.single _ 1 = _
    have : ((j, (⟨fun _ => default, fun _ _ _ => Subsingleton.elim _ _⟩ : Fin 1 ↪ Cfg (Fin 0)) k)
        : Cfg (Fin 0) × Cfg (Fin 0)) = (default, j) := Prod.ext (Subsingleton.elim _ _)
      (Subsingleton.elim _ _)
    rw [this]

/-- The word of two-bit components with real part `1` and imaginary part `0`. -/
def oneWord : Cfg (VW 2) := fun v => decide (v = Sum.inl 0)

/-- The two's complement value of the first component of `oneWord` is `1`. -/
theorem twos_inl_oneWord : twos (B := VW 2) Sum.inl oneWord = 1 := by decide

/-- The two's complement value of the second component of `oneWord` is `0`. -/
theorem twos_inr_oneWord : twos (B := VW 2) Sum.inr oneWord = 0 := by decide

/-- The word `oneWord` decodes to `1`. -/
theorem gauss_oneWord : gauss oneWord = 1 := by
  simp [gauss, twos_inl_oneWord, twos_inr_oneWord]

/-- **The matrix of the one-point data storing `oneWord`** with decoder scale `1` is the
identity, for every input. -/
theorem wordData_matrix (Y : Type) (y : Y) : (wordData Y 2 1 oneWord).matrix y = 1 := by
  funext i j
  have hij : i = j := Subsingleton.elim i j
  subst hij
  simp [wordData, gauss_oneWord]

/-- The slot range of the one-point data with the identity equivalence: the one slot is the one
index, the image of the empty low word. -/
theorem wordData_range (Y : Type) (b : ℕ) (c0 : ℝ) (w : Cfg (VW b)) :
    ∀ j : Cfg (Fin 0), (∃ m, (wordData Y b c0 w).slot m = j) ↔
      ∃ u : Fin 0 → Bool, j = Equiv.refl (Cfg (Fin 0)) (lowWord 0 u) := fun _ =>
  ⟨fun _ => ⟨fun i => i.elim0, Subsingleton.elim _ _⟩, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

/-- The operator of the identity matrix is the identity. -/
theorem matrixOperator_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    SparseStateOverlap.matrixOperator (1 : Matrix ι ι ℂ) = 1 := by
  refine ContinuousLinearMap.ext fun v => ?_
  ext i
  simp [SparseStateOverlap.matrixOperator_apply, Matrix.one_apply]

/-- **The simulated Hamiltonian of the one-point data storing `oneWord` is the identity** on the
system register (`k = 0` qubits) with the payload `R`. -/
theorem wordData_hamiltonian {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R]
    [CompleteSpace R] (Y : Type) (y : Y) :
    qlift (R := R) (Equiv.refl (Cfg (Fin 0)))
      (SparseStateOverlap.matrixOperator ((wordData Y 2 1 oneWord).matrix y)) = 1 := by
  rw [wordData_matrix, matrixOperator_one, qlift_one]

/-! ### The evolution of the identity and a lower bound on the error -/

/-- On the system register with `k = 0` qubits and the payload `ℂ`,
`exp(-it · 1) = e^{-it} · 1`. -/
theorem exp_smul_one_reg (t : ℝ) :
    NormedSpace.exp ((-Complex.I * (t : ℂ)) • (1 : Reg (Fin 0) ℂ →L[ℂ] Reg (Fin 0) ℂ)) =
      Complex.exp (-Complex.I * (t : ℂ)) • (1 : Reg (Fin 0) ℂ →L[ℂ] Reg (Fin 0) ℂ) := by
  rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one,
    ← NormedSpace.algebraMap_exp_comm, Complex.exp_eq_exp_ℂ]

/-- **An error lower bound.** If `C ι` is within `ε` of `ι U₂` for an isometric embedding `ι` of
a system register, then `C ι` is at least `‖U₁ ψ - U₂ ψ‖ - ε` from `ι U₁`, for every unit vector
`ψ`. -/
theorem error_sep {V S : Type*} [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S]
    {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
    (C : Reg V R →L[ℂ] Reg V R) (ι : Reg S R →L[ℂ] Reg V R) (hι : ∀ φ, ‖ι φ‖ = ‖φ‖)
    (U₁ U₂ : Reg S R →L[ℂ] Reg S R) (ψ : Reg S R) (hψ : ‖ψ‖ = 1) (ε : ℝ)
    (h : ‖C ∘L ι - ι ∘L U₂‖ ≤ ε) :
    ‖U₁ ψ - U₂ ψ‖ - ε ≤ ‖C ∘L ι - ι ∘L U₁‖ := by
  have hX := (C ∘L ι - ι ∘L U₂).le_opNorm ψ
  have hY := (C ∘L ι - ι ∘L U₁).le_opNorm ψ
  have hdiff : (C ∘L ι - ι ∘L U₂) ψ - (C ∘L ι - ι ∘L U₁) ψ = ι (U₁ ψ - U₂ ψ) := by
    simp only [sub_apply, ContinuousLinearMap.comp_apply, map_sub]
    abel
  have htri := norm_sub_le ((C ∘L ι - ι ∘L U₂) ψ) ((C ∘L ι - ι ∘L U₁) ψ)
  rw [hdiff, hι] at htri
  rw [hψ, mul_one] at hX hY
  linarith

/-- `|e^{-i} - e^{i}| = 2 sin 1 > 1`. -/
theorem one_lt_norm_exp_sub : 1 < ‖Complex.exp (-Complex.I * ((|(-1 : ℝ)| : ℝ) : ℂ)) -
    Complex.exp (-Complex.I * ((-1 : ℝ) : ℂ))‖ := by
  have h1 : -Complex.I * ((|(-1 : ℝ)| : ℝ) : ℂ) = ((-1 : ℝ) : ℂ) * Complex.I := by
    rw [abs_neg, abs_one]
    push_cast
    ring
  have h2 : -Complex.I * ((-1 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h1, h2]
  have him := Complex.abs_im_le_norm (Complex.exp (((-1 : ℝ) : ℂ) * Complex.I) -
    Complex.exp (((1 : ℝ) : ℂ) * Complex.I))
  rw [Complex.sub_im, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_im,
    Real.sin_neg] at him
  have hs := Real.sin_gt_sub_cube (x := 1) one_pos
  have hs1 : 0 < Real.sin 1 := by linarith
  rw [show -Real.sin 1 - Real.sin 1 = -(2 * Real.sin 1) by ring, abs_neg,
    abs_of_pos (by linarith)] at him
  linarith

/-! ### The released circuit for `|t|` at a negative time -/

section Released

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

set_option maxHeartbeats 1000000 in
/-- **The released circuit for `|t|` is at least the distance of the two evolutions, minus `ε`,
from `exp(-itĤ)`.** Under the hypotheses of the released `GateBinary.binary_simulation` for the
time `|t|`, for every unit vector `ψ` of the system register the released circuit
`GateBinary.binarySim` for `|t|` is at least `‖e^{-itĤ} ψ - e^{-i|t|Ĥ} ψ‖ - ε` from `exp(-itĤ)` in
full-output error. -/
theorem binarySim_error_ge (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (σ : ℕ)
    (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (hb : 0 < b) (c0 : ℝ) (hc0 : 0 < c0) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z)
    (x : X) (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) (γ t ε ζ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hζε : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℝ) * ζ ≤ ε)
    (ψ : Reg (Fin k) R) (hψ : ‖ψ‖ = 1) :
    ‖NormedSpace.exp ((-Complex.I * (t : ℂ)) •
          qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x))) ψ -
        NormedSpace.exp ((-Complex.I * ((|t| : ℝ) : ℂ)) •
          qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x))) ψ‖ - ε ≤
      ‖nrun (prims (R := R) D en x) (binarySim k b σ hσ s γ c0 |t| ε ζ) ∘L
          sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L
            NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ := by
  obtain ⟨-, -, -, -, herr, -⟩ := binary_simulation (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x
    hH hrow hcol γ |t| ε ζ hγ hγ1 (abs_nonneg t) hε hε1 hζ hζ1 hζε
  exact error_sep _ _ (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas])) _ _ ψ hψ ε herr

end Released

/-! ### The witness -/

/-- **Every hypothesis of `binary_simulation_bits_signed` holds at a negative time for a nonzero
Hamiltonian** (Theorem `hs:thm:gates` for every real time; the signed endpoints are not vacuous):
for `s = 1 = 2^0` slot, `t = -1` and `ε = 1/2`, the one-point binary data
`wordData Unit 2 1 oneWord` (`k = 0` index bits, `b = 2` stored bits, decoder scale `c₀ = 1`,
the identity matrix, so `Ĥ = 1`) with the identity equivalence, some `b_data ≥ 2` with
`HasBits b_data 1` and `ζ = ε/(442368 q)` satisfy the slot range, the decoder, the Hermitian, row
and column norm hypotheses, the bit-length hypotheses and the accuracy window of
`binary_simulation_bits_signed`. For some rescaling `γ ∈ (0, 1]` (in the proof, that of the
released `GateBitBudget.binary_simulation_bits` for `|t| = 1`) also `48 d ζ ≤ ε` holds, the signed
circuit `binarySimSigned` has the gate bound `10¹⁵ q (𝔟_H + 1)³` and it is within `ε` of
`exp(-itĤ)` (payload `R = ℂ`). The two evolutions differ by more than `1 = 2ε` on the unit vector
`ψ = bas default 1` (by `2 sin 1`). Every hypothesis of `binarySim_error_ge` thus holds for these
data, `γ`, `ζ` and `ψ`, and with it the released circuit `GateBinary.binarySim` for `|t|` is farther
than `ε` from `exp(-itĤ)`; here the two evolutions differ by the global phase `e^{2i}`. -/
theorem hs_signed_all_hyps : ∃ (D : Data Unit (Cfg (Fin 0)) (Cfg (VW 2)) 1)
    (en : Cfg (Fin 0) ≃ Cfg (Fin 0)) (c0 : ℝ) (bd : ℕ) (ζ : ℝ),
    (∀ j, (∃ m, D.slot m = j) ↔ ∃ u : Fin 0 → Bool, j = en (lowWord 0 u)) ∧ 0 < c0 ∧
    (∀ e z, D.decode e z = (c0 : ℂ) * gauss z) ∧ (D.matrix ()).IsHermitian ∧
    (∀ i, ∑ j, ‖D.matrix () i j‖ ^ 2 ≤ 1) ∧ (∀ j, ∑ i, ‖D.matrix () i j‖ ^ 2 ≤ 1) ∧
    2 ≤ bd ∧ HasBits bd c0 ∧ 0 < ζ ∧ ζ ≤ 1 ∧
    221184 * ImprovedPrecisionBudget.shape ((1 : ℕ) : ℝ) |(-1 : ℝ)| (Real.log (1 / (1 / 2))) *
      ζ ≤ 1 / 2 ∧
    1 / 2 ≤ 442368 * ImprovedPrecisionBudget.shape ((1 : ℕ) : ℝ) |(-1 : ℝ)|
      (Real.log (1 / (1 / 2))) * ζ ∧
    qlift (R := ℂ) en (SparseStateOverlap.matrixOperator (D.matrix ())) = 1 ∧
    ‖(bas default (1 : ℂ) : Reg (Fin 0) ℂ)‖ = 1 ∧
    1 < ‖NormedSpace.exp ((-Complex.I * ((-1 : ℝ) : ℂ)) •
          qlift (R := ℂ) en (SparseStateOverlap.matrixOperator (D.matrix ())))
          (bas default (1 : ℂ)) -
        NormedSpace.exp ((-Complex.I * ((|(-1 : ℝ)| : ℝ) : ℂ)) •
          qlift (R := ℂ) en (SparseStateOverlap.matrixOperator (D.matrix ())))
          (bas default (1 : ℂ))‖ ∧
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      48 * (fDeg (width ((1 : ℕ) : ℝ) γ) (time ((1 : ℕ) : ℝ) |(-1 : ℝ)| γ) (moment γ)
        (1 / 2 / 2) : ℝ) * ζ ≤ 1 / 2 ∧
      (nGatesN (binarySimSigned 0 2 0 le_rfl 1 γ c0 (-1) (1 / 2) ζ) : ℝ) ≤
        10 ^ 15 * ImprovedPrecisionBudget.shape ((1 : ℕ) : ℝ) |(-1 : ℝ)|
            (Real.log (1 / (1 / 2))) *
          (bitH bd (2 ^ 0) (ImprovedPrecisionBudget.shape ((1 : ℕ) : ℝ) |(-1 : ℝ)|
            (Real.log (1 / (1 / 2)))) (1 / 2) + 1) ^ 3 ∧
      ‖nrun (prims (R := ℂ) D en ()) (binarySimSigned 0 2 0 le_rfl 1 γ c0 (-1) (1 / 2) ζ) ∘L
          sysEmb (io (P := Reg (Fin 0) ℂ)) - sysEmb (io (P := Reg (Fin 0) ℂ)) ∘L
            NormedSpace.exp ((-Complex.I * ((-1 : ℝ) : ℂ)) •
              qlift (R := ℂ) en (SparseStateOverlap.matrixOperator (D.matrix ())))‖ ≤ 1 / 2 := by
  obtain ⟨γ, hγ, hγ1, -, hdeg, -, -, -, hall⟩ :=
    binary_simulation_bits.{0, 0, 0} 1 le_rfl |(-1 : ℝ)| (1 / 2) (abs_nonneg _) (by norm_num)
      (by norm_num)
  obtain ⟨bd, hb, hbits⟩ := exists_common_bits 2 [1] (by
    intro x hx
    simp only [List.mem_singleton] at hx
    exact ⟨1, 0, by rw [hx]; norm_num⟩)
  obtain ⟨hz0, hz1, hz2, hz3⟩ :=
    hs_zeta_shape_spec 1 (abs_nonneg (-1 : ℝ)) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hdec : ∀ e z, (wordData Unit 2 1 oneWord).decode e z = ((1 : ℝ) : ℂ) * gauss z :=
    fun _ _ => rfl
  have hH : ((wordData Unit 2 1 oneWord).matrix ()).IsHermitian := by
    rw [wordData_matrix]
    exact Matrix.isHermitian_one
  have hrow : ∀ i, ∑ j, ‖(wordData Unit 2 1 oneWord).matrix () i j‖ ^ 2 ≤ 1 := fun i => by
    rw [wordData_matrix, Fintype.sum_subsingleton _ i, Matrix.one_apply_eq, norm_one, one_pow]
  have hcol : ∀ j, ∑ i, ‖(wordData Unit 2 1 oneWord).matrix () i j‖ ^ 2 ≤ 1 := fun j => by
    rw [wordData_matrix, Fintype.sum_subsingleton _ j, Matrix.one_apply_eq, norm_one, one_pow]
  have h1 := hbits 1 (by simp)
  obtain ⟨hG, -⟩ := hall (X := Unit) (n := Cfg (Fin 0)) (k := 0) (b := 2) (R := ℂ)
    (wordData Unit 2 1 oneWord) (Equiv.refl _) 0 le_rfl rfl (wordData_range Unit 2 1 oneWord)
    two_pos 1 one_pos hdec () hH hrow hcol bd hb h1 _ hz0 hz1 hz2 hz3
  have hζε : 48 * (fDeg (width ((1 : ℕ) : ℝ) γ) (time ((1 : ℕ) : ℝ) |(-1 : ℝ)| γ) (moment γ)
      (1 / 2 / 2) : ℝ) * (1 / 2 / (442368 * ImprovedPrecisionBudget.shape ((1 : ℕ) : ℝ)
        |(-1 : ℝ)| (Real.log (1 / (1 / 2))))) ≤ 1 / 2 := by
    nlinarith [hdeg, hz0, hz2]
  obtain ⟨-, -, -, -, herrS, -⟩ := binary_simulation_signed (R := ℂ) (wordData Unit 2 1 oneWord)
    (Equiv.refl _) 0 le_rfl rfl (wordData_range Unit 2 1 oneWord) two_pos 1 one_pos hdec () hH
    hrow hcol γ (-1) (1 / 2) _ hγ hγ1 (by norm_num) (by norm_num) hz0 hz1 hζε
  have hψ : ‖(bas default (1 : ℂ) : Reg (Fin 0) ℂ)‖ = 1 := by rw [norm_bas, norm_one]
  refine ⟨wordData Unit 2 1 oneWord, Equiv.refl _, 1, bd, _, wordData_range Unit 2 1 oneWord,
    one_pos, hdec, hH, hrow, hcol, hb, h1, hz0, hz1, hz2, hz3, wordData_hamiltonian Unit (), hψ,
    ?_, γ, hγ, hγ1, hζε, ?_, herrS⟩
  · rw [wordData_hamiltonian, exp_smul_one_reg, exp_smul_one_reg, smul_apply, smul_apply,
      one_apply_eq_self, ← sub_smul, norm_smul, hψ, mul_one, norm_sub_rev]
    exact one_lt_norm_exp_sub
  · rw [nGatesN_binarySimSigned]
    exact hG

end

end SparseHamiltonian.GateSigned
