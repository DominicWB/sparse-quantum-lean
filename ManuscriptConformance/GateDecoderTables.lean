import ManuscriptConformance.GateMainDecoder
import GeneralDecoder.Tables

/-!
# Conformance: the arithmetic assumptions of the general-decoder theorems can be met

The computational assumptions of `hs_thm_gates_decoder` and `gate_thm_main_decoder`
(`comp_rotArith`, `comp_signedArithV`, `comp_clipArithV`) ask for reversible word arithmetic of the
decoder `val` with gates and work wires at most `c_A (b_data + k + log₂(1/ξ) + 1)^{d_A}` at
accuracy `ξ`, the constants `c_A`, `d_A` fixed before the instance. For every decoder of `2b`-bit
stored words they hold with `c_A = tableConst b = 2^{2b+8} (b + 1)` and `d_A = 1`, by the lookup
tables of `GeneralDecoder.Tables` (`comp_rotArith_tables`, `comp_signedArithV_tables`,
`comp_clipArithV_tables`), and they hold for every larger `c_A` (`comp_rotArith_cmono`,
`comp_signedArithV_cmono`, `comp_clipArithV_cmono`). So the form and the accuracy of the assumptions
can be met for every decoder, and for stored words of bounded width `b ≤ b₀` the general-decoder
theorems hold with no arithmetic hypothesis (`hs_thm_gates_decoder_tables`,
`gate_thm_main_decoder_tables`: the theorems at `c_A = tableConst b₀`, `d_A = 1`, with constants
`C` exponential in `b₀`). What the assumptions add is the polynomial gate bound with constants
independent of `b`; for the decoder `c₀(X + iY)` the tables play the same role for the factor
arithmetic (`GateOptimalBinary.gate_optimal_binary_tables`), and the CORDIC arithmetic meets the
polynomial bound for the angles (`comp_rotArith_binary`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateSynth SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget
  SparseHamiltonian.GeneralSparseAccess SparseHamiltonian.GeneralDecoder
open GateOptimalBinary (bitsFor clipBT clipBP)
open scoped InnerProduct

/-! ### Larger constants -/

/-- The rotation arithmetic assumption holds for every larger constant `c_A`. -/
theorem comp_rotArith_cmono {cA cA' : ℝ} {dA bd k b : ℕ} {val : Cfg (VW b) → ℂ} {K₀ K : ℝ}
    (hc : cA ≤ cA') (h : comp_rotArith cA dA bd k b val K₀ K) :
    comp_rotArith cA' dA bd k b val K₀ K := by
  intro κ hκ hκm hκK ζ hζ hζ1
  obtain ⟨bT, bP, A, ar, hcost⟩ := h κ hκ hκm hκK ζ hζ hζ1
  refine ⟨bT, bP, A, ar, hcost.trans ?_⟩
  have hlog : 0 ≤ Real.logb 2 (1 / ζ) :=
    Real.logb_nonneg one_lt_two (by rw [le_div_iff₀ hζ]; linarith)
  have : 0 ≤ ((bd : ℝ) + k + Real.logb 2 (1 / ζ) + 1) ^ dA := by positivity
  exact mul_le_mul_of_nonneg_right hc this

/-- The factor arithmetic assumption of the signed-factor regime holds for every larger
constant `c_A`. -/
theorem comp_signedArithV_cmono {cA cA' : ℝ} {dA bd k b : ℕ} {val : Cfg (VW b) → ℂ} {μ : ℝ}
    (hc : cA ≤ cA') (h : comp_signedArithV cA dA bd k b val μ) :
    comp_signedArithV cA' dA bd k b val μ := by
  intro ξ hξ hξ1
  obtain ⟨bT, bP, A, ar, hacc, hcost⟩ := h ξ hξ hξ1
  refine ⟨bT, bP, A, ar, hacc, hcost.trans ?_⟩
  have hlog : 0 ≤ Real.logb 2 (1 / ξ) :=
    Real.logb_nonneg one_lt_two (by rw [le_div_iff₀ hξ]; linarith)
  have : 0 ≤ ((bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) ^ dA := by positivity
  exact mul_le_mul_of_nonneg_right hc this

/-- The arithmetic assumption of the clipped regime holds for every larger constant `c_A`. -/
theorem comp_clipArithV_cmono {cA cA' : ℝ} {dA bd k b : ℕ} {val : Cfg (VW b) → ℂ} {μ β q : ℝ}
    (hc : cA ≤ cA') (h : comp_clipArithV cA dA bd k b val μ β q) :
    comp_clipArithV cA' dA bd k b val μ β q := by
  intro ξ hξ hξ1
  obtain ⟨bT, bP, A, af, aa, haf, haa, hcost⟩ := h ξ hξ hξ1
  refine ⟨bT, bP, A, af, aa, haf, haa, hcost.trans ?_⟩
  have hlog : 0 ≤ Real.logb 2 (1 / ξ) :=
    Real.logb_nonneg one_lt_two (by rw [le_div_iff₀ hξ]; linarith)
  have : 0 ≤ ((bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) ^ dA := by positivity
  exact mul_le_mul_of_nonneg_right hc this

/-! ### The assumptions from lookup tables -/

/-- **The constant of the table arithmetic**: `c_A = 2^{2b+8} (b + 1)` for stored words of `2b`
bits. -/
def tableConst (b : ℕ) : ℝ := 2 ^ (2 * b + 8) * ((b : ℝ) + 1)

theorem tableConst_nonneg (b : ℕ) : 0 ≤ tableConst b := by
  unfold tableConst
  positivity

theorem tableConst_eq (b : ℕ) : tableConst b = 256 * (2 : ℝ) ^ (2 * b) * ((b : ℝ) + 1) := by
  unfold tableConst
  rw [pow_add]
  ring

/-- The constant of the table arithmetic is monotone in the width of the stored words. -/
theorem tableConst_mono {b b' : ℕ} (h : b ≤ b') : tableConst b ≤ tableConst b' := by
  unfold tableConst
  have h1 : (2 : ℝ) ^ (2 * b + 8) ≤ 2 ^ (2 * b' + 8) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (b : ℝ) + 1 ≤ b' + 1 := by
    have : (b : ℝ) ≤ b' := by exact_mod_cast h
    linarith
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- The cost of a table in the form of the assumptions: a count
`x ≤ 2^{2b} T (24b + 26) + T + 2b + 1` with words of total length `T ≤ 3 log₂(1/ξ) + 7` is at
most `tableConst b (b_data + k + log₂(1/ξ) + 1)`. -/
theorem table_bound {bd k b : ℕ} {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) {T x : ℝ}
    (hT : T ≤ 3 * Real.logb 2 (1 / ξ) + 7)
    (hx : x ≤ 2 ^ (2 * b) * T * (24 * b + 26) + T + 2 * b + 1) :
    x ≤ tableConst b * ((bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) ^ 1 := by
  have hL : 0 ≤ Real.logb 2 (1 / ξ) :=
    Real.logb_nonneg one_lt_two (by rw [le_div_iff₀ hξ]; linarith)
  have hbd : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have h := table_cost_le (P := 2 ^ (2 * b)) (M := Real.logb 2 (1 / ξ) + 1)
    (w := (bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) b (one_le_pow₀ (by norm_num)) (by linarith)
    (by linarith) (by linarith) hx
  rw [pow_one, tableConst_eq]
  exact h

/-- **The rotation arithmetic assumption holds for every decoder** (`comp_rotArith`, the angles of
the bounded regime of `gate:thm:main` and of `hs:thm:gates`), with `c_A = tableConst b` and
`d_A = 1`, by lookup tables. -/
theorem comp_rotArith_tables (bd k b : ℕ) (val : Cfg (VW b) → ℂ) (K₀ K : ℝ) :
    comp_rotArith (tableConst b) 1 bd k b val K₀ K := by
  intro κ _ _ _ ζ hζ hζ1
  obtain ⟨ar, hlen⟩ := rotWordArith_exists (fun z => (κ : ℂ) * val z) hζ
  refine ⟨_, _, _, ar, ?_⟩
  obtain ⟨h1, -, h3⟩ := bitsFor_words hζ hζ1
  have hL : 0 ≤ Real.logb 2 (1 / ζ) :=
    Real.logb_nonneg one_lt_two (by rw [le_div_iff₀ hζ]; linarith)
  apply table_bound (T := (bitsFor Real.pi ζ : ℝ) + bitsFor (2 * Real.pi) ζ) hζ hζ1
    (by linarith)
  have hlen' : (ar.circ.length : ℝ) ≤ 2 ^ (2 * b) *
      ((bitsFor Real.pi ζ : ℝ) + bitsFor (2 * Real.pi) ζ) * (4 * b + 1) := by exact_mod_cast hlen
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have h4 : (2 : ℝ) ^ (2 * b) * ((bitsFor Real.pi ζ : ℝ) + bitsFor (2 * Real.pi) ζ) * (4 * b + 1) ≤
      2 ^ (2 * b) * ((bitsFor Real.pi ζ : ℝ) + bitsFor (2 * Real.pi) ζ) * (24 * b + 26) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  push_cast
  linarith

/-- **The factor arithmetic assumption of the signed-factor regime holds for every decoder**
(`comp_signedArithV`), with `c_A = tableConst b` and `d_A = 1`, by lookup tables. -/
theorem comp_signedArithV_tables (bd k b : ℕ) (val : Cfg (VW b) → ℂ) (μ : ℝ) :
    comp_signedArithV (tableConst b) 1 bd k b val μ := by
  intro ξ hξ hξ1
  obtain ⟨ar, hacc, hlen⟩ := sgWordArith_exists val μ hξ
  refine ⟨_, _, _, ar, hacc, ?_⟩
  obtain ⟨-, h2, h3⟩ := bitsFor_words hξ hξ1
  have hL : 0 ≤ Real.logb 2 (1 / ξ) :=
    Real.logb_nonneg one_lt_two (by rw [le_div_iff₀ hξ]; linarith)
  apply table_bound (T := (bitsFor Real.pi (ξ ^ 2) : ℝ) + bitsFor (2 * Real.pi) ξ) hξ hξ1
    (by linarith)
  have hlen' : (ar.circ.length : ℝ) ≤ 2 ^ (2 * b) *
      ((bitsFor Real.pi (ξ ^ 2) : ℝ) + bitsFor (2 * Real.pi) ξ) * (4 * b + 1) := by
    exact_mod_cast hlen
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have h4 : (2 : ℝ) ^ (2 * b) * ((bitsFor Real.pi (ξ ^ 2) : ℝ) + bitsFor (2 * Real.pi) ξ) *
      (4 * b + 1) ≤
      2 ^ (2 * b) * ((bitsFor Real.pi (ξ ^ 2) : ℝ) + bitsFor (2 * Real.pi) ξ) * (24 * b + 26) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  push_cast
  linarith

/-- **The arithmetic assumption of the clipped regime holds for every decoder**
(`comp_clipArithV`, the factor and the rotation on common work wires), with `c_A = tableConst b`
and `d_A = 1`, by lookup tables. -/
theorem comp_clipArithV_tables (bd k b : ℕ) (val : Cfg (VW b) → ℂ) (μ β q : ℝ) :
    comp_clipArithV (tableConst b) 1 bd k b val μ β q := by
  intro ξ hξ hξ1
  obtain ⟨af, aa, haf, haa, hlf, hla⟩ := clipWordArith_exists val μ β q hξ
  refine ⟨_, _, _, af, aa, haf, haa, ?_⟩
  obtain ⟨h1, h2, h3⟩ := bitsFor_words hξ hξ1
  have hL : 0 ≤ Real.logb 2 (1 / ξ) :=
    Real.logb_nonneg one_lt_two (by rw [le_div_iff₀ hξ]; linarith)
  have hBT : (clipBT ξ ξ : ℝ) ≤ 2 * Real.logb 2 (1 / ξ) + 3 := by
    unfold clipBT
    rw [Nat.cast_max]
    exact max_le h2 (by linarith)
  have hBP : (clipBP ξ ξ : ℝ) ≤ Real.logb 2 (1 / ξ) + 4 := by
    unfold clipBP
    rw [max_self]
    exact h3
  apply table_bound (T := (clipBT ξ ξ : ℝ) + clipBP ξ ξ) hξ hξ1 (by linarith)
  have e1 : (2 : ℝ) ^ (2 * b + 1) = 2 * 2 ^ (2 * b) := by rw [pow_succ]; ring
  have e2 : (2 : ℝ) ^ (2 * b + 2) = 4 * 2 ^ (2 * b) := by rw [pow_add]; ring
  have hlf' : (af.circ.length : ℝ) ≤ 2 ^ (2 * b + 1) *
      ((clipBT ξ ξ : ℝ) + clipBP ξ ξ) * (4 * b + 3) := by exact_mod_cast hlf
  have hla' : (aa.circ.length : ℝ) ≤ 2 ^ (2 * b + 2) *
      ((clipBT ξ ξ : ℝ) + clipBP ξ ξ) * (4 * b + 5) := by exact_mod_cast hla
  rw [e1] at hlf'
  rw [e2] at hla'
  push_cast
  linarith

universe u v w

/-! ### The general-decoder theorems for stored words of bounded width -/

set_option maxHeartbeats 4000000 in
/-- **Fixed-width variant of Theorem `hs:thm:gates`, eq. `hs:eq:gate-binary`, for sparse access of
general size and every decoder of stored words of bounded width, with no arithmetic hypothesis.**
For a finite gate set
admitting single-qubit synthesis of length at most `c₁ log(1/ζ) + c₀` and an exact decomposition
of its controlled one-qubit gates, and every bound `b₀`, there are constants `C` and `K` such
that the conclusion of `hs_thm_gates_decoder` holds for every sparse data of general size with any
public decoder of stored words of `2b` bits, `b ≤ b₀`: `hs_thm_gates_decoder` at
`c_A = tableConst b₀`, `d_A = 1`, with the lookup tables of `comp_rotArith_tables`. The constant
`C` grows exponentially with `b₀`, so this is not the polynomial form of eq. `hs:eq:gate-binary`. -/
theorem hs_thm_gates_decoder_tables (b₀ : ℕ) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (Kd : ℕ) {𝒢 : Set Kind}
    {X₁ X₂ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ}
    (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b) (bd : ℕ)
        (η t ε : ℝ),
        b ≤ b₀ → 2 ^ k < 2 * N → b ≤ bd → 0 < η → 0 < ε → ε ≤ 1 / 2 →
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (sys : Fin k ↪ W)
          (Cc : List (NInstr W (PY k b) NativeSparseBlockEncoding.Query)),
          (∀ i ∈ Cc, i.Valid) ∧ (∀ g, NInstr.gate g ∈ Cc → GateOf 𝒢 g) ∧
          (nCallsN (fun _ => true) Cc : ℝ) ≤ 6635520 * mainBound s (η * |t|) ε ∧
          (nGatesN Cc : ℝ) ≤ C * mainBound s (η * |t|) ε *
            (bitH bd N (mainBound s (η * |t|) ε) ε + 1) ^ K ∧
          ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
            (x : X),
            (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            FullOutputError (nrun (D.prims (R := R) x) Cc) (cleanAlong sys)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) (Equiv.refl _) (SparseStateOverlap.matrixOperator (D.padMat x)))) ε := by
  obtain ⟨C, K, hC, h⟩ := hs_thm_gates_decoder.{u, w} (tableConst b₀) 1 (tableConst_nonneg b₀)
    hc₀ hc₁ Kd ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  refine ⟨C, K, hC, ?_⟩
  intro X N s k b D bd η t ε hb hk hbd hη hε hε2
  exact h D bd η t ε hk hbd
    (comp_rotArith_cmono (tableConst_mono hb) (comp_rotArith_tables _ _ _ _ _ _)) hη hε hε2

set_option maxHeartbeats 4000000 in
/-- **Fixed-width variant of Theorem `gate:thm:main` for sparse access of general size and every
decoder of stored words
of bounded width, with no arithmetic hypothesis.** For a finite gate set admitting single-qubit
synthesis of length at most `c₁ log(1/ζ) + c₀` and an exact decomposition of its controlled
one-qubit gates, and every bound `b₀`, there are constants `C` and `K` such that the conclusion of
`gate_thm_main_decoder` holds for every sparse data of general size with any public decoder of
stored words of `2b` bits, `b ≤ b₀`: `gate_thm_main_decoder` at `c_A = tableConst b₀`, `d_A = 1`,
with the lookup tables of `comp_rotArith_tables`, `comp_signedArithV_tables` and
`comp_clipArithV_tables`. The query count `288·10¹² Q_μ` is unchanged; the constant `C` grows
exponentially with `b₀`, so this is not the polynomial form of eq. `gate:eq:main-gates`. -/
theorem gate_thm_main_decoder_tables (b₀ : ℕ) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (Kd : ℕ) {𝒢 : Set Kind} {X₁ X₂ : Type} [Fintype X₁] [DecidableEq X₁]
    [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ}
    (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b) (bd : ℕ)
        (η μ t ε : ℝ),
        b ≤ b₀ → 2 ^ k < 2 * N → b ≤ bd →
        μ ≤ η → η ≤ Real.sqrt s * μ → 1 ≤ η ^ 2 * |t| / μ → 0 < ε → ε ≤ 1 / 64 →
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (sys : Fin k ↪ W)
          (Cc : List (NInstr W (PY k b) NativeSparseBlockEncoding.Query)),
          (∀ i ∈ Cc, i.Valid) ∧ (∀ g, NInstr.gate g ∈ Cc → GateOf 𝒢 g) ∧
          (nCallsN (fun _ => true) Cc : ℝ) ≤ 288 * 10 ^ 12 * twoNormBound s η μ t ε ∧
          (nGatesN Cc : ℝ) ≤ C * twoNormBound s η μ t ε *
            (gateWord bd N s (twoNormBound s η μ t ε) ε + 1) ^ K ∧
          (Fintype.card W : ℝ) ≤
            k + C * (gateWord bd N s (twoNormBound s η μ t ε) ε + 1) ^ K ∧
          ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
            [FiniteDimensional ℂ R] (x : X),
            (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) → (∀ i j, ‖D.matrix x i j‖ ≤ μ) →
            FullOutputError (nrun (D.prims (R := R) x) Cc) (cleanAlong sys)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) (Equiv.refl _) (SparseStateOverlap.matrixOperator (D.padMat x)))) ε := by
  obtain ⟨C, K, hC, h⟩ := gate_thm_main_decoder.{u, w} (tableConst b₀) 1 (tableConst_nonneg b₀)
    hc₀ hc₁ Kd ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  refine ⟨C, K, hC, ?_⟩
  intro X N s k b D bd η μ t ε hb hk hbd hμη hηs hθ hε hε64
  exact h D bd η μ t ε hk hbd
    (comp_rotArith_cmono (tableConst_mono hb) (comp_rotArith_tables _ _ _ _ _ _))
    (comp_signedArithV_cmono (tableConst_mono hb) (comp_signedArithV_tables _ _ _ _ _))
    (comp_clipArithV_cmono (tableConst_mono hb) (comp_clipArithV_tables _ _ _ _ _ _ _))
    hμη hηs hθ hε hε64

end

end ManuscriptConformance
