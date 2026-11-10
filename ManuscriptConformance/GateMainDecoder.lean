import ManuscriptConformance.GateDecoder
import ManuscriptConformance.GateMain
import GeneralDecoder.MainEndpoint

/-!
# Conformance: Theorem `gate:thm:main` for general decoders

Theorem `gate:thm:main` assumes (in the paragraph before it, Section `gate:sec:result`) that "the
decoder and reversible scalar arithmetic must evaluate the normalised entries, elementary real
functions and local rotation parameters specified in Section `gate:sec:native` to accuracy `ξ`
using gates and clean work polynomial in `b_data`, the index widths and `log(1/ξ)`". This file
states it for every public decoder of the stored words, with that assumption for the local
rotation parameters of the three regimes of the construction:

* `gate_main_dataDec`: binary sizes (`BinarySizes`) and the decoder of the data, which may depend
  on the edge, with the arithmetic on the base wires of the native operations (`comp_decArith` for
  the bounded regime, `comp_signedArithD`, `comp_clipArithD`);
* `comp_signedArithD_padDataE`, `comp_clipArithD_padDataE`: the arithmetic assumptions of the
  padded data with a validity decoder, from the arithmetic of the decoder on the value word
  (`comp_signedArithV`, `comp_clipArithV`; `GeneralDecoder.WordArith.flagLiftG`);
* `gate_thm_main_decoder`: general sizes and general decoders.
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
open GateOptimalPrecision (FactorArithOK)
open scoped InnerProduct

/-! ### The arithmetic assumptions -/

section Assumptions

variable {X n : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- **The factor arithmetic of the decoder of the data in the signed-factor regime** (computational
assumption, on the base wires): for every accuracy `ξ ∈ (0, 1]`, a reversible arithmetic on the
base wires of the native factor writing the angle and phase words of `clip(decode(e, w)/μ)`
(`GateOptimalPrecision.FactorArithOK` of `GeneralDecoder.sgFOD`), with gates and work wires at
most `c_A (b_data + k + log₂(1/ξ) + 1)^{d_A}`. -/
def comp_signedArithD (cA : ℝ) (dA : ℕ) (bd k b : ℕ)
    (D : NativeSparseBlockEncoding.Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) :
    Prop :=
  ∀ ξ : ℝ, 0 < ξ → ξ ≤ 1 → ∃ (bT bP A : ℕ)
    (circ : List (Gate (NB Empty (GateOptimalBinary.PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (tw : Cfg (NB Empty (GateOptimalBinary.PRf k) (SZ k b)) → Fin bT → Bool)
    (pw : Cfg (NB Empty (GateOptimalBinary.PRf k) (SZ k b)) → Fin bP → Bool),
    FactorArithOK (sgFOD D en μ circ tw pw) ξ ∧
    ((circ.length + bT + bP + A : ℕ) : ℝ) ≤ cA * ((bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) ^ dA

/-- **The factor and angle arithmetic of the decoder of the data in the clipped regime**
(computational assumption, on the base wires): for every accuracy `ξ ∈ (0, 1]`, on common work
wires, a reversible arithmetic writing the angle and phase words of the correction entry `[g] c₂`
(`FactorArithOK` of `GeneralDecoder.clFOD`) and one writing the angle words of
`y(g, f, c₁, c₂)` (`GateNative.ArithOK` of `GeneralDecoder.clNDD`), `c₁`, `c₂` the clipped and
correction entries of `decode(e, w)`, with gates and work wires at most
`c_A (b_data + k + log₂(1/ξ) + 1)^{d_A}`. -/
def comp_clipArithD (cA : ℝ) (dA : ℕ) (bd k b : ℕ)
    (D : NativeSparseBlockEncoding.Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) :
    Prop :=
  ∀ ξ : ℝ, 0 < ξ → ξ ≤ 1 → ∃ (bT bP A : ℕ)
    (fcirc : List (Gate (NB Empty (GateOptimalBinary.PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (ftw : Cfg (NB Empty (GateOptimalBinary.PRf k) (SZ k b)) → Fin bT → Bool)
    (fpw : Cfg (NB Empty (GateOptimalBinary.PRf k) (SZ k b)) → Fin bP → Bool)
    (acirc : List (Gate (NB Empty (GateOptimalBinary.PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (atw : Cfg (NB Empty (GateOptimalBinary.PRf k) (SZ k b)) → Fin bT → Bool)
    (apw : Cfg (NB Empty (GateOptimalBinary.PRf k) (SZ k b)) → Fin bP → Bool),
    FactorArithOK (clFOD D en μ β fcirc ftw fpw) ξ ∧
    ArithOK (⟨bT, bP, A, acirc, atw, apw⟩ : Arith (NB Empty (GateOptimalBinary.PRf k) (SZ k b)))
      (Sum.inl (Sum.inr (GateOptimalBinary.locF k 1))) (ckdecD D en μ β q) ξ ∧
    ((fcirc.length + acirc.length + bT + bP + A : ℕ) : ℝ) ≤
      cA * ((bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) ^ dA

end Assumptions

/-- **The factor arithmetic of a decoder in the signed-factor regime** (computational assumption of
`gate:thm:main`, stated before the theorem, on the value word): for every accuracy `ξ ∈ (0, 1]`, a
reversible word arithmetic on the value word (`GeneralDecoder.WordArith`) writing the angle and
phase words of `clip(val w/μ)` to the accuracy of the native factor (`GeneralDecoder.FactorAcc`),
with gates and work wires at most `c_A (b_data + k + log₂(1/ξ) + 1)^{d_A}`. -/
def comp_signedArithV (cA : ℝ) (dA : ℕ) (bd k b : ℕ) (val : Cfg (VW b) → ℂ) (μ : ℝ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ → ξ ≤ 1 → ∃ (bT bP A : ℕ) (ar : WordArith (VW b) bT bP A),
    FactorAcc (sgVal val μ) ξ ar.tw ar.pw ∧
    ((ar.circ.length + bT + bP + A : ℕ) : ℝ) ≤ cA * ((bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) ^ dA

/-- **The factor and angle arithmetic of a decoder in the clipped regime** (computational
assumption of `gate:thm:main`, on the branch, the flag and the value word): for every accuracy
`ξ ∈ (0, 1]`, on common work wires, a word arithmetic writing the angle and phase words of the
correction entry `[g] c₂(val w)` (`GeneralDecoder.cfVal`, `FactorAcc`) and one writing the angle
words of `y(g, f, c₁(val w), c₂(val w))` (`GeneralDecoder.ckVal`, `RotAcc`), with gates and work
wires at most `c_A (b_data + k + log₂(1/ξ) + 1)^{d_A}`. -/
def comp_clipArithV (cA : ℝ) (dA : ℕ) (bd k b : ℕ) (val : Cfg (VW b) → ℂ) (μ β q : ℝ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ → ξ ≤ 1 → ∃ (bT bP A : ℕ) (af : WordArith (Unit ⊕ VW b) bT bP A)
    (aa : WordArith ((Unit ⊕ Unit) ⊕ VW b) bT bP A),
    FactorAcc (cfVal val μ β) ξ af.tw af.pw ∧ RotAcc (ckVal val μ β q) ξ aa.tw aa.pw ∧
    ((af.circ.length + aa.circ.length + bT + bP + A : ℕ) : ℝ) ≤
      cA * ((bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) ^ dA

/-! ### The arithmetic of the padded data -/

section Pad

/-- The arithmetic assumption of the bounded regime holds for every larger constant. -/
theorem comp_decArith_mono {X n : Type*} [Fintype n] [DecidableEq n] {s : ℕ} {cA cA' : ℝ}
    {dA bd k b : ℕ} {D : NativeSparseBlockEncoding.Data X n (Cfg (VW b)) s} {en : Cfg (Fin k) ≃ n}
    {K₀ K : ℝ} (hc : cA ≤ cA') (h : comp_decArith cA dA bd k b D en K₀ K) :
    comp_decArith cA' dA bd k b D en K₀ K := by
  intro κ hκ hκm hκK ζ hζ hζ1
  obtain ⟨ar, har, hcost⟩ := h κ hκ hκm hκK ζ hζ hζ1
  refine ⟨ar, har, hcost.trans ?_⟩
  have hlog : 0 ≤ Real.logb 2 (1 / ζ) :=
    Real.logb_nonneg one_lt_two (by rw [le_div_iff₀ hζ]; linarith)
  have : 0 ≤ ((bd : ℝ) + k + Real.logb 2 (1 / ζ) + 1) ^ dA := by positivity
  exact mul_le_mul_of_nonneg_right hc this

/-- The cost of a wrapped arithmetic: `m c + d ≤ (4 c_A + 40) w'^{max(d_A, 1)}` for `m ≤ 4`,
`d ≤ 18k + 39` and `c ≤ c_A w^{d_A}`, `w' = b_data + (k + 1) + log₂(1/ξ) + 1` the word at the
index width `k + 1` (used with `3c + 10k + 23` and `4c + 18k + 39`). -/
theorem wrap_bound_le {cA : ℝ} {dA bd k : ℕ} (hcA : 0 ≤ cA) {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    {c : ℝ} (hc : c ≤ cA * ((bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) ^ dA) (m : ℝ) (hm : m ≤ 4)
    (hm0 : 0 ≤ m) (d : ℝ) (hd : d ≤ 18 * k + 39) :
    m * c + d ≤ (4 * cA + 40) * ((bd : ℝ) + ((k + 1 : ℕ) : ℝ) + Real.logb 2 (1 / ξ) + 1) ^
      max dA 1 := by
  have hlog : 0 ≤ Real.logb 2 (1 / ξ) :=
    Real.logb_nonneg one_lt_two (by rw [le_div_iff₀ hξ]; linarith)
  have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  set w : ℝ := (bd : ℝ) + ((k + 1 : ℕ) : ℝ) + Real.logb 2 (1 / ξ) + 1 with hw
  have hwk : (k : ℝ) + 2 ≤ w := by rw [hw]; push_cast; linarith
  have hw1 : 1 ≤ w := by linarith
  have hw0 : (bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1 ≤ w := by rw [hw]; push_cast; linarith
  have hw00 : 0 ≤ (bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1 := by linarith
  have h1 : ((bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) ^ dA ≤ w ^ max dA 1 :=
    (pow_le_pow_left₀ hw00 hw0 dA).trans (pow_le_pow_right₀ hw1 (le_max_left _ _))
  have h2 : w ≤ w ^ max dA 1 := le_self_pow₀ hw1 (by omega)
  have hcw : c ≤ cA * w ^ max dA 1 := hc.trans (mul_le_mul_of_nonneg_left h1 hcA)
  have hwm : 0 ≤ w ^ max dA 1 := by positivity
  have hc0 : m * c ≤ m * (cA * w ^ max dA 1) := mul_le_mul_of_nonneg_left hcw hm0
  have hc1 : m * (cA * w ^ max dA 1) ≤ 4 * (cA * w ^ max dA 1) :=
    mul_le_mul_of_nonneg_right hm (by positivity)
  have hd' : d ≤ 40 * w ^ max dA 1 := by nlinarith
  nlinarith

/-- **The factor arithmetic of the signed regime for the padded data with a validity decoder**,
from the factor arithmetic of the decoder on the value word. -/
theorem comp_signedArithD_padDataE {cA : ℝ} {dA : ℕ} (hcA : 0 ≤ cA) {X : Type*}
    {N s k b bd : ℕ} (D : QData X N s k b) {μ : ℝ} (h : comp_signedArithV cA dA bd k b D.val μ) :
    comp_signedArithD (4 * cA + 40) (max dA 1) bd (k + 1) b D.padDataE (Equiv.refl _) μ := by
  intro ξ hξ hξ1
  obtain ⟨bT, bP, A, ar, hacc, hcost⟩ := h ξ hξ hξ1
  refine ⟨bT, bP, flagA k bT bP A + 1,
    (ar.flagLiftG N (ιEF (k + 1) b) (GateOptimalBinary.vF (k + 1) b) none).circ,
    (ar.flagLiftG N (ιEF (k + 1) b) (GateOptimalBinary.vF (k + 1) b) none).tw,
    (ar.flagLiftG N (ιEF (k + 1) b) (GateOptimalBinary.vF (k + 1) b) none).pw,
    sgFOD_padDataE_ok D μ ar hacc, ?_⟩
  have hw := wrap_cost_le N (ιEF (k + 1) b) (GateOptimalBinary.vF (k + 1) b) none ar
  have hw' : (((ar.flagLiftG N (ιEF (k + 1) b) (GateOptimalBinary.vF (k + 1) b) none).circ.length +
      bT + bP + (flagA k bT bP A + 1) : ℕ) : ℝ) ≤
      3 * ((ar.circ.length + bT + bP + A : ℕ) : ℝ) + (10 * k + 23) := by
    exact_mod_cast hw
  have hb := wrap_bound_le (dA := dA) (bd := bd) (k := k) hcA hξ hξ1 hcost 3 (by norm_num)
    (by norm_num) (10 * k + 23) (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg _; linarith)
  exact hw'.trans hb

/-- **The factor and angle arithmetic of the clipped regime for the padded data with a validity
decoder**, from the arithmetic of the decoder on the value word, for `q ≥ 0`. -/
theorem comp_clipArithD_padDataE {cA : ℝ} {dA : ℕ} (hcA : 0 ≤ cA) {X : Type*}
    {N s k b bd : ℕ} (D : QData X N s k b) {μ β q : ℝ} (hq : 0 ≤ q)
    (h : comp_clipArithV cA dA bd k b D.val μ β q) :
    comp_clipArithD (4 * cA + 40) (max dA 1) bd (k + 1) b D.padDataE (Equiv.refl _) μ β q := by
  intro ξ hξ hξ1
  obtain ⟨bT, bP, A, af, aa, haf, haa, hcost⟩ := h ξ hξ hξ1
  refine ⟨bT, bP, flagA k bT bP A + 1,
    (af.flagLiftG N (ιEF (k + 1) b) (GateOptimalBinary.ιFin (k + 1) b) none).circ,
    (af.flagLiftG N (ιEF (k + 1) b) (GateOptimalBinary.ιFin (k + 1) b) none).tw,
    (af.flagLiftG N (ιEF (k + 1) b) (GateOptimalBinary.ιFin (k + 1) b) none).pw,
    (aa.flagLiftG N (ιEF (k + 1) b) (GateOptimalBinary.ιCin (k + 1) b)
      (some (Sum.inl (Sum.inl ())))).circ,
    (aa.flagLiftG N (ιEF (k + 1) b) (GateOptimalBinary.ιCin (k + 1) b)
      (some (Sum.inl (Sum.inl ())))).tw,
    (aa.flagLiftG N (ιEF (k + 1) b) (GateOptimalBinary.ιCin (k + 1) b)
      (some (Sum.inl (Sum.inl ())))).pw,
    clFOD_padDataE_ok D μ β af haf, clNDD_padDataE_ok D μ β q hq aa haa, ?_⟩
  have h1 := af.flagLiftG_length N (ιEF (k + 1) b) (GateOptimalBinary.ιFin (k + 1) b) none
  have h2 := aa.flagLiftG_length N (ιEF (k + 1) b) (GateOptimalBinary.ιCin (k + 1) b)
    (some (Sum.inl (Sum.inl ())))
  have hV := length_validC_le (k := k) N
  have hA : flagA k bT bP A = bT + bP + A + (2 * k + 6) := by rw [flagA, card_FW]
  have hn : (af.flagLiftG N (ιEF (k + 1) b) (GateOptimalBinary.ιFin (k + 1) b) none).circ.length +
      (aa.flagLiftG N (ιEF (k + 1) b) (GateOptimalBinary.ιCin (k + 1) b)
        (some (Sum.inl (Sum.inl ())))).circ.length + bT + bP + (flagA k bT bP A + 1) ≤
      4 * (af.circ.length + aa.circ.length + bT + bP + A) + (18 * k + 39) := by
    omega
  have hn' : (((af.flagLiftG N (ιEF (k + 1) b) (GateOptimalBinary.ιFin (k + 1) b) none).circ.length +
      (aa.flagLiftG N (ιEF (k + 1) b) (GateOptimalBinary.ιCin (k + 1) b)
        (some (Sum.inl (Sum.inl ())))).circ.length + bT + bP + (flagA k bT bP A + 1) : ℕ) : ℝ) ≤
      4 * ((af.circ.length + aa.circ.length + bT + bP + A : ℕ) : ℝ) + (18 * k + 39) := by
    exact_mod_cast hn
  have hb := wrap_bound_le (dA := dA) (bd := bd) (k := k) hcA hξ hξ1 hcost 4 le_rfl
    (by norm_num) (18 * k + 39) le_rfl
  exact hn'.trans hb

/-- The Cayley scale of the clipped construction is nonnegative: `q = cot(π/p)/2` with an even
`p ≥ 2`. -/
theorem qval_nonneg (s τ ε : ℝ) : 0 ≤ LargeSparsityCore.Parameters.qval s τ ε := by
  unfold LargeSparsityCore.Parameters.qval LargeSparsityCore.Parameters.theta
  have hq : 0 ≤ LargeSparsityCore.Parameters.qstar s τ ε := Real.sqrt_nonneg _
  have hc : 0 < ⌈Real.pi * LargeSparsityCore.Parameters.qstar s τ ε + 1⌉₊ :=
    Nat.ceil_pos.mpr (by positivity)
  have hp : (2 : ℝ) ≤ (LargeSparsityCore.Parameters.pval s τ ε : ℝ) := by
    unfold LargeSparsityCore.Parameters.pval
    push_cast
    have : (1 : ℝ) ≤ (⌈Real.pi * LargeSparsityCore.Parameters.qstar s τ ε + 1⌉₊ : ℝ) := by
      exact_mod_cast hc
    linarith
  have hθ0 : 0 < Real.pi / (LargeSparsityCore.Parameters.pval s τ ε : ℝ) :=
    div_pos Real.pi_pos (by linarith)
  have hθ1 : Real.pi / (LargeSparsityCore.Parameters.pval s τ ε : ℝ) ≤ Real.pi / 2 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hp
  rw [Real.cot_eq_cos_div_sin]
  apply div_nonneg _ (by norm_num)
  apply div_nonneg
  · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ1⟩
  · exact (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])).le

end Pad

/-! ### Per-call costs with supplied arithmetic -/

section Costs

/-- **The per-call gates of the bounded regime** for a supplied arithmetic with
`|circ| + b_T + b_P + A ≤ P`: `bdNativeCostD ≤ 74 B + 5 P`. -/
theorem bd_cost_leD {k sb b : ℕ} (ar : Arith (BW k b)) {B P : ℝ} (hsb : (sb : ℝ) ≤ B)
    (hk : (k : ℝ) ≤ B) (hB1 : 1 ≤ B)
    (hP : ((ar.circ.length + ar.bT + ar.bP + ar.A : ℕ) : ℝ) ≤ P) :
    (bdNativeCostD k sb ar : ℝ) ≤ 74 * B + 5 * P := by
  have e : bdNativeCostD k sb ar =
      7 * (sb + 1) + (2 * (28 * k) + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)) := rfl
  rw [e]
  have h1 : 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1) ≤
      5 * (ar.circ.length + ar.bT + ar.bP + ar.A) + 1 := by omega
  have h1' : ((2 * ar.circ.length + (2 * ar.bP + ar.bT + 1) : ℕ) : ℝ) ≤
      5 * ((ar.circ.length + ar.bT + ar.bP + ar.A : ℕ) : ℝ) + 1 := by exact_mod_cast h1
  push_cast at h1' hP ⊢
  linarith

/-- **The per-call gates of the signed-factor regime** for a supplied arithmetic with
`|circ| + b_T + b_P + A ≤ P`: `sgNativeCostD ≤ 74 B + 5 P`. -/
theorem sg_cost_leD {k sb b bT bP A : ℕ}
    (circ : List (Gate (NB Empty (GateOptimalBinary.PRf k) (SZ k b) ⊕ AWr bT bP A))) {B P : ℝ}
    (hsb : (sb : ℝ) ≤ B) (hk : (k : ℝ) ≤ B) (hB1 : 1 ≤ B)
    (hP : ((circ.length + bT + bP + A : ℕ) : ℝ) ≤ P) :
    (sgNativeCostD k sb circ : ℝ) ≤ 74 * B + 5 * P := by
  have e : sgNativeCostD k sb circ =
      7 * (sb + 1) + (2 * (28 * k) + 2 * circ.length + (2 * bP + bT + 4)) := rfl
  rw [e]
  have h1 : 2 * circ.length + (2 * bP + bT + 4) ≤ 5 * (circ.length + bT + bP + A) + 4 := by
    omega
  have h1' : ((2 * circ.length + (2 * bP + bT + 4) : ℕ) : ℝ) ≤
      5 * ((circ.length + bT + bP + A : ℕ) : ℝ) + 4 := by exact_mod_cast h1
  push_cast at h1' hP ⊢
  linarith

/-- **The per-call gates of the clipped regime** for supplied arithmetic with
`|circ_f| + |circ_a| + b_T + b_P + A ≤ P`: `clNativeCostD ≤ 198 B + 15 P`. -/
theorem cl_cost_leD {k sb b bT bP A : ℕ}
    (fcirc acirc : List (Gate (NB Empty (GateOptimalBinary.PRf k) (SZ k b) ⊕ AWr bT bP A)))
    {B P : ℝ} (hsb : (sb : ℝ) ≤ B) (hk : (k : ℝ) ≤ B) (hB1 : 1 ≤ B)
    (hP : ((fcirc.length + acirc.length + bT + bP + A : ℕ) : ℝ) ≤ P) :
    (clNativeCostD k sb fcirc acirc : ℝ) ≤ 198 * B + 15 * P := by
  have e : clNativeCostD k sb fcirc acirc =
      7 * (sb + 2) + (2 * (2 * (28 * k) + 2 * fcirc.length + (2 * bP + bT + 4)) +
        (2 * (28 * k) + 2 * acirc.length + (2 * bP + bT + 1))) := rfl
  rw [e]
  have h1 : 2 * (2 * fcirc.length + (2 * bP + bT + 4)) + (2 * acirc.length + (2 * bP + bT + 1))
      ≤ 15 * (fcirc.length + acirc.length + bT + bP + A) + 9 := by omega
  have h1' : ((2 * (2 * fcirc.length + (2 * bP + bT + 4)) +
      (2 * acirc.length + (2 * bP + bT + 1)) : ℕ) : ℝ) ≤
      15 * ((fcirc.length + acirc.length + bT + bP + A : ℕ) : ℝ) + 9 := by exact_mod_cast h1
  push_cast at h1' hP ⊢
  linarith

end Costs

universe u v w

/-! ### Theorem `gate:thm:main` for the decoder of the data -/

set_option maxHeartbeats 12000000 in
/-- **Theorem `gate:thm:main` for the decoder of the data** (binary sizes). Fix the computational
assumptions on the base wires of the native operations (`comp_decArith` for the angles of the
bounded regime at the rescalings `κ ∈ [1/η, √s/η]`, `comp_signedArithD`, `comp_clipArithD` at the public
scales of the construction, with gates and work at most `c_A (b_data + k + log₂(1/ξ) + 1)^{d_A}` at
accuracy `ξ`) and a finite gate set admitting single-qubit synthesis of length at most
`c₁ log(1/ζ) + c₀` at accuracy `ζ`, with an exact decomposition of its controlled one-qubit gates.
There are constants `C` and `K = max(3, d_A) + 1` such that: for sparse data with binary sizes
(`BinarySizes`) and any public decoder of the stored words, stored words of `2b` bits with
`b ≤ b_data`, `μ ≤ η ≤ √s μ`, `η²|t|/μ ≥ 1` and `0 < ε ≤ 1/64`, one circuit over the gate set and
the primitive sparse oracles, fixed before the instance, uses at most `24·10¹² Q_μ` primitive
sparse queries, at most `C Q_μ (𝔟 + 1)^K` gates with `𝔟 = gateWord b_data N s Q_μ ε`, `N = |n|`,
at most `k + C (𝔟 + 1)^K` qubits, and on every instance whose matrix is Hermitian with row and
column Euclidean norms at most `η` and entries of modulus at most `μ` has full-output error at most
`ε` on the clean embedding, with an untouched reference of any finite dimension. -/
theorem gate_main_dataDec (cA : ℝ) (dA : ℕ) (hcA : 0 ≤ cA) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (Kd : ℕ) {𝒢 : Set Kind} {X₁ X₂ : Type} [Fintype X₁] [DecidableEq X₁]
    [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ}
    (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ {X : Type u} {n : Type v} [Fintype n] [DecidableEq n] {s k b : ℕ}
        (D : NativeSparseBlockEncoding.Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n)
        (sb bd : ℕ) (η μ t ε : ℝ),
        BinarySizes D en sb → b ≤ bd → comp_decArith cA dA bd k b D en (1 / η) (Real.sqrt s / η) →
        comp_signedArithD cA dA bd k b D en μ →
        comp_clipArithD cA dA bd k b D en μ (clipBeta η μ t ε) (clipScale s η μ t ε) →
        μ ≤ η → η ≤ Real.sqrt s * μ → 1 ≤ η ^ 2 * |t| / μ → 0 < ε → ε ≤ 1 / 64 →
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (sys : Fin k ↪ W)
          (Cc : List (NInstr W (PY k b) NativeSparseBlockEncoding.Query)),
          (∀ i ∈ Cc, i.Valid) ∧ (∀ g, NInstr.gate g ∈ Cc → GateOf 𝒢 g) ∧
          (nCallsN (fun _ => true) Cc : ℝ) ≤ 24 * 10 ^ 12 * twoNormBound s η μ t ε ∧
          (nGatesN Cc : ℝ) ≤ C * twoNormBound s η μ t ε *
            (gateWord bd (Fintype.card n) s (twoNormBound s η μ t ε) ε + 1) ^ K ∧
          (Fintype.card W : ℝ) ≤
            k + C * (gateWord bd (Fintype.card n) s (twoNormBound s η μ t ε) ε + 1) ^ K ∧
          ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
            [FiniteDimensional ℂ R] (x : X),
            (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) → (∀ i j, ‖D.matrix x i j‖ ≤ μ) →
            FullOutputError (nrun (prims (R := R) D en x) Cc) (cleanAlong sys)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))) ε := by
  obtain ⟨L', c₀', c₁', hc₀', hc₁', hS, hL'⟩ := synthesis_of_parts hc₀ hc₁
    ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  -- the constants
  set KG := max 3 dA with hKG
  set PA := cA * 52 ^ dA with hPA
  have hPA0 : 0 ≤ PA := by positivity
  set cG : ℝ := 198 + 15 * PA with hcG
  set cW : ℝ := 8 + PA with hcW
  set cN : ℝ := 9 * 10 ^ 15 + 8 * 10 ^ 11 * cG with hcN
  set Cg : ℝ := cN * (c₁' * (Real.log (4 * cN) + KG + 2) + c₀') with hCg
  have hcG0 : 0 ≤ cG := by positivity
  have hcW0 : 0 ≤ cW := by positivity
  have hcN1 : 1 ≤ cN := by rw [hcN]; nlinarith
  have hCg0 : 0 ≤ Cg := by
    have : 0 ≤ Real.log (4 * cN) := Real.log_nonneg (by linarith)
    positivity
  set C : ℝ := 24 * 10 ^ 12 + Cg + 630 + cW + Fintype.card (X₂ ⊕ X₁) with hC
  refine ⟨C, KG + 1, by positivity, ?_⟩
  intro X n _ _ s k b D en sb bd η μ t ε hF hbd hdec hsa hca hμη hηs hθ hε hε1
  -- the parameters
  have hμ0 : 0 < μ := by
    by_contra h
    have h' : μ ≤ 0 := not_lt.mp h
    have : η ^ 2 * |t| / μ ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg η) (abs_nonneg t)) h'
    linarith
  have hη0 : 0 < η := lt_of_lt_of_le hμ0 hμη
  set σ : ℝ := (s : ℝ) * μ ^ 2 / η ^ 2 with hσdef
  set θ : ℝ := η ^ 2 * |t| / μ with hθdef
  have hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2 := by rw [hσdef]; field_simp
  obtain ⟨-, -, hs0, hσ1, hST, hSq⟩ := GateOptimalPrecision.two_norm_params hμη hηs hσ rfl hθ
  set Q := twoNormBound s η μ t ε with hQdef
  have hQmu : GateOptimalPrecision.Qmu s η μ t ε = Q := qmu_eq s η μ t ε
  have hQ1 : 1 ≤ Q := by
    rw [← hQmu, GateOptimalPrecision.Qmu_eq rfl hST hSq]
    have h1 : 1 ≤ Real.sqrt σ := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hσ1
    have h2 : 1 ≤ Real.sqrt σ * θ := one_le_mul_of_one_le_of_one_le h1 hθ
    have h3 := OptimalSparseSimulation.r_pos hθ hε hε1
    have h4 := Real.sqrt_nonneg (σ * θ * LargeSparsityCore.Parameters.rval θ ε)
    linarith
  have hε1' : ε ≤ 1 := by linarith
  have hε2 : 0 < ε / 2 := by positivity
  -- the budget word
  set B := gateWord bd (Fintype.card n) s Q ε + 1 with hBdef
  have hcard : Fintype.card n = 2 ^ k := card_eq_two_pow en
  have hY1 : 1 ≤ (Q + 1) / ε := one_le_div_of_le (by linarith) hε hε1'
  have hlogN : (k : ℝ) ≤ Real.logb 2 ((Fintype.card n : ℝ) + 1) := by
    rw [hcard]; exact nat_le_logb k
  have hlogs : 0 ≤ Real.logb 2 ((s : ℝ) + 1) :=
    logb_nonneg_of_one_le (by have := Nat.cast_nonneg (α := ℝ) s; linarith)
  have hlogY : 0 ≤ Real.logb 2 ((Q + 1) / ε) := logb_nonneg_of_one_le hY1
  have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hB1 : 1 ≤ B := by rw [hBdef]; unfold gateWord; linarith
  have hBk : (k : ℝ) ≤ B := by rw [hBdef]; unfold gateWord; linarith
  have hBd : (bd : ℝ) ≤ B := by rw [hBdef]; unfold gateWord; linarith
  have hBY : Real.logb 2 ((Q + 1) / ε) ≤ B := by rw [hBdef]; unfold gateWord; linarith
  have hsbB : (sb : ℝ) ≤ B := by
    have : (sb : ℝ) ≤ k := by exact_mod_cast hF.hsb
    linarith
  have hBK : 1 ≤ B ^ KG := one_le_pow₀ hB1
  have hBdK : B ^ dA ≤ B ^ KG := pow_le_pow_right₀ hB1 (le_max_right 3 dA)
  have hB1K : B ≤ B ^ KG := le_self_pow₀ hB1 (by omega)
  have hKK : B ^ KG ≤ B ^ (KG + 1) := pow_le_pow_right₀ hB1 (by omega)
  -- the arithmetic accuracy
  set ξ : ℝ := ε / (2 * 10 ^ 14 * Q) with hξdef
  have hξ0 : 0 < ξ := by positivity
  have hξ1 : ξ ≤ 1 := by
    rw [hξdef, div_le_one (by positivity)]; nlinarith
  have hlogξ : Real.logb 2 (1 / ξ) ≤ 49 * B := logb_inv_xi_le hQ1 hε hε1' hB1 hBY
  have hPb : cA * ((bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) ^ dA ≤ PA * B ^ KG := by
    have h1 : 0 ≤ (bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1 := by
      have : 0 ≤ Real.logb 2 (1 / ξ) :=
        logb_nonneg_of_one_le (by rw [le_div_iff₀ hξ0]; linarith)
      linarith
    have h2 : (bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1 ≤ 52 * B := by linarith
    have h3 : ((bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) ^ dA ≤ (52 * B) ^ dA :=
      pow_le_pow_left₀ h1 h2 dA
    rw [mul_pow] at h3
    have h4 : cA * ((bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) ^ dA ≤ cA * (52 ^ dA * B ^ dA) :=
      mul_le_mul_of_nonneg_left h3 hcA
    have h5 : cA * (52 ^ dA * B ^ dA) ≤ PA * B ^ KG := by
      rw [hPA, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBdK (by positivity)) hcA
    linarith
  -- the internal accuracy and the error budget
  have hP : GateOptimalBinary.MainParams s η μ t (ε / 2 / 2) σ θ :=
    ⟨hμη, hηs, hσ, rfl, hθ, by positivity, by linarith⟩
  have hQh : GateOptimalPrecision.Qmu s η μ t (ε / 2) ≤ 2 * Q := by
    rw [← hQmu]
    exact GateOptimalPrecision.Qmu_half_le hη0.le hμ0 (by linarith) hε (by linarith)
  have hQh0 : 0 ≤ GateOptimalPrecision.Qmu s η μ t (ε / 2) :=
    GateOptimalPrecision.Qmu_nonneg rfl hST hSq hθ hε2 (by linarith)
  have hδε : 8 * 10 ^ 11 * GateOptimalPrecision.Qmu s η μ t (ε / 2) * (6 * ξ + 4 * ξ) ≤ ε / 2 := by
    have e : 6 * ξ + 4 * ξ = 10 * ε / (2 * 10 ^ 14 * Q) := by rw [hξdef]; ring
    rw [e]
    have hQ0 : 0 < Q := by linarith
    have h1 : 8 * 10 ^ 11 * GateOptimalPrecision.Qmu s η μ t (ε / 2) * (10 * ε / (2 * 10 ^ 14 * Q))
        ≤ 8 * 10 ^ 11 * (2 * Q) * (10 * ε / (2 * 10 ^ 14 * Q)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQh (by norm_num)) (by positivity)
    have e2 : 8 * 10 ^ 11 * (2 * Q) * (10 * ε / (2 * 10 ^ 14 * Q)) = 8 * ε / 100 := by
      field_simp; ring
    linarith
  -- the arithmetic of the three regimes
  have hs1 : (1 : ℝ) ≤ s := by rw [hF.hs]; exact_mod_cast Nat.one_le_two_pow
  have hsq0 : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 (by linarith)
  obtain ⟨hγ0, hγ1, hγσ, -⟩ := GateOptimalPrecision.bdGamma_spec (σ := σ) (θ := θ)
    (ε := ε / 2 / 2) ⟨hσ1, by linarith, by positivity, by linarith⟩
  have hκ0 : 0 < GateOptimalPrecision.bdGamma σ θ (ε / 2 / 2) * Real.sqrt s / η := by positivity
  have hκK : GateOptimalPrecision.bdGamma σ θ (ε / 2 / 2) * Real.sqrt s / η ≤ Real.sqrt s / η := by
    apply div_le_div_of_nonneg_right _ hη0.le
    nlinarith
  have hκm : 1 / η ≤ GateOptimalPrecision.bdGamma σ θ (ε / 2 / 2) * Real.sqrt s / η := by
    apply div_le_div_of_nonneg_right _ hη0.le
    have hμη2 : μ ^ 2 / η ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact pow_le_pow_left₀ hμ0.le hμη 2
    have hσs : σ ≤ s := by
      have e : σ = (s : ℝ) * (μ ^ 2 / η ^ 2) := by rw [hσdef]; ring
      rw [e]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) hμη2
    have hsq : Real.sqrt σ ≤ Real.sqrt s := Real.sqrt_le_sqrt hσs
    calc (1 : ℝ) ≤ GateOptimalPrecision.bdGamma σ θ (ε / 2 / 2) * Real.sqrt σ := hγσ
      _ ≤ GateOptimalPrecision.bdGamma σ θ (ε / 2 / 2) * Real.sqrt s :=
          mul_le_mul_of_nonneg_left hsq hγ0.le
  obtain ⟨arB, harB, hcostB⟩ := hdec _ hκ0 hκm hκK ξ hξ0 hξ1
  obtain ⟨bT, bP, A, scirc, stw, spw, hsaok, hcostS⟩ := hsa ξ hξ0 hξ1
  obtain ⟨bT', bP', A', fcirc, ftw, fpw, acirc, atw, apw, hafok, haaok, hcostC⟩ := hca ξ hξ0 hξ1
  -- the promises
  let Prom : X → Prop := fun x => (D.matrix x).IsHermitian ∧
    (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) ∧ (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) ∧
    (∀ i j, ‖D.matrix x i j‖ ≤ μ)
  have hI : ∀ x, Prom x → BinaryInputD D en sb x η μ := fun x hx =>
    ⟨hF.hsb, hF.hs, hF.range, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2⟩
  have hQ'0 : 0 ≤ 2 * GateOptimalPrecision.Qmu s η μ t (ε / 2) := by linarith
  have hQ'4 : 2 * GateOptimalPrecision.Qmu s η μ t (ε / 2) ≤ 4 * Q := by linarith
  have hε₄ : ε / 2 / 2 = ε / 4 := by ring
  have hεε : ε / 2 + ε / 2 = ε := by ring
  have hS' : (Fintype.card (Fin k) : ℝ) ≤ B := by rw [Fintype.card_fin]; exact hBk
  by_cases hx : ∃ x, Prom x
  swap
  · -- no admissible instance: the empty circuit
    refine ⟨Fin k, inferInstance, inferInstance, Function.Embedding.refl _, [], by simp, by simp,
      ?_, ?_, ?_, fun x hH hrow hcol hent => absurd ⟨x, hH, hrow, hcol, hent⟩ hx⟩
    · simp only [nCallsN, List.countP_nil, Nat.cast_zero]; positivity
    · simp only [nGatesN, List.countP_nil, Nat.cast_zero]; positivity
    · rw [Fintype.card_fin]
      have : 0 ≤ C * B ^ (KG + 1) := by positivity
      linarith
  obtain ⟨x₀, hx₀⟩ := hx
  have hcalls5 := GateOptimalBinary.computeV_calls_total k b
  by_cases hbd' : LargeSparsityCore.Parameters.hval θ (ε / 2 / 2) < 10 ^ 4
  · -- the bounded regime
    have key : ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
        [FiniteDimensional ℂ R] (x : X), Prom x →
        GateOptimalBinary.SynthClaims (prims (R := R) D en x) 𝒢 (X₂ ⊕ X₁) L' (ε / 2)
          (synthBudget hS (ε / 2) (bdNativeCircuitD D en sb hF.hsb hη0 σ θ (ε / 2 / 2) t arB))
          (GateOptimalBinary.sysH (R := R) D en x) t (ε / 2 / 2)
          (2 * GateOptimalPrecision.Qmu s η μ t (ε / 2)) (fun p => 2 * nCallsN p (computeV k b))
          (nGatesN (bdNativeCircuitD D en sb hF.hsb hη0 σ θ (ε / 2 / 2) t arB))
          (bdNativeCostD k sb arB) (ε / 2 + ε / 2) := by
      intro R _ _ _ _ x hxp
      rcases gate_optimal_binaryD_synth (R := R) (hI x hxp) hP hξ0.le hξ0.le hδε arB harB scirc
          stw spw hsaok fcirc ftw fpw acirc atw apw hafok haaok hS hε2 with
        ⟨-, h⟩ | ⟨h1, -, -⟩ | ⟨Rg, -⟩
      · exact h
      · exact absurd h1 (not_le.mpr hbd')
      · exact absurd Rg.h_large (not_le.mpr hbd')
    have hG : (bdNativeCostD k sb arB : ℝ) ≤ cG * B ^ KG := by
      have h1 := bd_cost_leD arB hsbB hBk hB1 (hcostB.trans hPb)
      have h3 : (74 + 5 * PA) * B ^ KG ≤ cG * B ^ KG :=
        mul_le_mul_of_nonneg_right (by rw [hcG]; linarith) (by positivity)
      have e : (74 + 5 * PA) * B ^ KG = 74 * B ^ KG + 5 * (PA * B ^ KG) := by ring
      linarith
    have hW : ((Fintype.card (SZ k b) + arB.bT + arB.bP + arB.A : ℕ) : ℝ) ≤ cW * B ^ KG := by
      have h1 : ((Fintype.card (SZ k b) + arB.bT + arB.bP + arB.A : ℕ) : ℝ) ≤
          8 * B + PA * B ^ KG := by
        rw [card_SZ]
        have h2 := hcostB.trans hPb
        have hb' : (b : ℝ) ≤ bd := by exact_mod_cast hbd
        push_cast at h2 ⊢
        have : (0 : ℝ) ≤ arB.circ.length := Nat.cast_nonneg _
        linarith
      have h3 : (8 + PA) * B ^ KG ≤ cW * B ^ KG :=
        mul_le_mul_of_nonneg_right (by rw [hcW]) (by positivity)
      have e : (8 + PA) * B ^ KG = 8 * B ^ KG + PA * B ^ KG := by ring
      linarith
    obtain ⟨hgates, hcardW, hcalls⟩ := claims_poly
      (key (R := EuclideanSpace ℂ (ULift.{w} (Fin 1))) x₀ hx₀) (KG := KG) (cG := cG)
      (cW := cW) hQ1 hQ'0 hQ'4 hε hε1' hε₄ rfl hB1 hBY hS'
      (by rw [Fintype.card_fin]; push_cast; linarith) (by omega) hcG0 hG hW hc₀' hc₁' hL'
    refine ⟨_, inferInstance, inferInstance, sysWire _ _ _ _ _ _ _ _,
      synthBudget hS (ε / 2) (bdNativeCircuitD D en sb hF.hsb hη0 σ θ (ε / 2 / 2) t arB),
      (key (R := EuclideanSpace ℂ (ULift.{w} (Fin 1))) x₀ hx₀).valid,
      (key (R := EuclideanSpace ℂ (ULift.{w} (Fin 1))) x₀ hx₀).gateset, ?_, ?_, ?_, ?_⟩
    · have h1 := hcalls (fun _ => true)
      rw [hcalls5] at h1
      push_cast at h1
      have : 0 ≤ Q := by linarith
      nlinarith
    · have : Q * cN * (c₁' * (Real.log (4 * cN) + KG + 2) + c₀') * B ^ (KG + 1) ≤
          C * Q * B ^ (KG + 1) := by
        have hle : Cg ≤ C := by
          rw [hC]; have := Nat.cast_nonneg (α := ℝ) (Fintype.card (X₂ ⊕ X₁)); linarith
        have e : Q * cN * (c₁' * (Real.log (4 * cN) + KG + 2) + c₀') * B ^ (KG + 1) =
            Cg * (Q * B ^ (KG + 1)) := by rw [hCg]; ring
        rw [e]
        have : 0 ≤ Q * B ^ (KG + 1) := by positivity
        nlinarith
      exact hgates.trans this
    · rw [Fintype.card_fin] at hcardW
      have hle : 630 + cW + Fintype.card (X₂ ⊕ X₁) ≤ C := by rw [hC]; linarith
      have hX0 : (0 : ℝ) ≤ Fintype.card (X₂ ⊕ X₁) := Nat.cast_nonneg _
      have h1 : (630 + cW) * B ^ KG + Fintype.card (X₂ ⊕ X₁) ≤
          (630 + cW + Fintype.card (X₂ ⊕ X₁)) * B ^ (KG + 1) := by
        have h2 : (630 + cW) * B ^ KG ≤ (630 + cW) * B ^ (KG + 1) :=
          mul_le_mul_of_nonneg_left hKK (by linarith)
        have h3 : (Fintype.card (X₂ ⊕ X₁) : ℝ) ≤ Fintype.card (X₂ ⊕ X₁) * B ^ (KG + 1) :=
          le_mul_of_one_le_right hX0 (one_le_pow₀ hB1)
        nlinarith
      have h4 : (630 + cW + Fintype.card (X₂ ⊕ X₁)) * B ^ (KG + 1) ≤ C * B ^ (KG + 1) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      linarith
    · intro R _ _ _ _ x hH hrow hcol hent
      have h := (key (R := R) x ⟨hH, hrow, hcol, hent⟩).error
      rw [cleanEmb_sysEmb_io, hεε] at h
      exact fullOutputError_of_norm h
  by_cases hsg : σ * θ < LargeSparsityCore.Parameters.Lval (ε / 2 / 2) *
      LargeSparsityCore.Parameters.hval θ (ε / 2 / 2)
  · -- the signed-factor regime
    have hh : 10 ^ 4 ≤ LargeSparsityCore.Parameters.hval θ (ε / 2 / 2) := not_lt.mp hbd'
    have key : ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
        [FiniteDimensional ℂ R] (x : X), Prom x →
        GateOptimalBinary.SynthClaims (prims (R := R) D en x) 𝒢 (X₂ ⊕ X₁) L' (ε / 2)
          (synthBudget hS (ε / 2)
            (sgNativeCircuitD D en sb hF.hsb μ σ t (ε / 2 / 2) scirc stw spw))
          (GateOptimalBinary.sysH (R := R) D en x) t (ε / 2 / 2)
          (2 * GateOptimalPrecision.Qmu s η μ t (ε / 2)) (fun p => 2 * nCallsN p (computeV k b))
          (nGatesN (sgNativeCircuitD D en sb hF.hsb μ σ t (ε / 2 / 2) scirc stw spw))
          (sgNativeCostD k sb scirc) (ε / 2 + ε / 2) := by
      intro R _ _ _ _ x hxp
      rcases gate_optimal_binaryD_synth (R := R) (hI x hxp) hP hξ0.le hξ0.le hδε arB harB scirc
          stw spw hsaok fcirc ftw fpw acirc atw apw hafok haaok hS hε2 with
        ⟨h0, -⟩ | ⟨-, -, h⟩ | ⟨Rg, -⟩
      · exact absurd h0 (not_lt.mpr hh)
      · exact h
      · exact absurd Rg.core (not_le.mpr hsg)
    have hG : (sgNativeCostD k sb scirc : ℝ) ≤ cG * B ^ KG := by
      have h1 := sg_cost_leD scirc hsbB hBk hB1 (hcostS.trans hPb)
      have h3 : (74 + 5 * PA) * B ^ KG ≤ cG * B ^ KG :=
        mul_le_mul_of_nonneg_right (by rw [hcG]; linarith) (by positivity)
      have e : (74 + 5 * PA) * B ^ KG = 74 * B ^ KG + 5 * (PA * B ^ KG) := by ring
      linarith
    have hW : ((Fintype.card (SZ k b) + bT + bP + A : ℕ) : ℝ) ≤ cW * B ^ KG := by
      have h1 : ((Fintype.card (SZ k b) + bT + bP + A : ℕ) : ℝ) ≤ 8 * B + PA * B ^ KG := by
        rw [card_SZ]
        have h2 := hcostS.trans hPb
        have hb' : (b : ℝ) ≤ bd := by exact_mod_cast hbd
        push_cast at h2 ⊢
        have : (0 : ℝ) ≤ scirc.length := Nat.cast_nonneg _
        linarith
      have h3 : (8 + PA) * B ^ KG ≤ cW * B ^ KG :=
        mul_le_mul_of_nonneg_right (by rw [hcW]) (by positivity)
      have e : (8 + PA) * B ^ KG = 8 * B ^ KG + PA * B ^ KG := by ring
      linarith
    obtain ⟨hgates, hcardW, hcalls⟩ := claims_poly
      (key (R := EuclideanSpace ℂ (ULift.{w} (Fin 1))) x₀ hx₀) (KG := KG) (cG := cG)
      (cW := cW) hQ1 hQ'0 hQ'4 hε hε1' hε₄ rfl hB1 hBY hS'
      (by rw [Fintype.card_fin]; push_cast; linarith) (by omega) hcG0 hG hW hc₀' hc₁' hL'
    refine ⟨_, inferInstance, inferInstance, sysWire _ _ _ _ _ _ _ _,
      synthBudget hS (ε / 2) (sgNativeCircuitD D en sb hF.hsb μ σ t (ε / 2 / 2) scirc stw spw),
      (key (R := EuclideanSpace ℂ (ULift.{w} (Fin 1))) x₀ hx₀).valid,
      (key (R := EuclideanSpace ℂ (ULift.{w} (Fin 1))) x₀ hx₀).gateset, ?_, ?_, ?_, ?_⟩
    · have h1 := hcalls (fun _ => true)
      rw [hcalls5] at h1
      push_cast at h1
      have : 0 ≤ Q := by linarith
      nlinarith
    · have : Q * cN * (c₁' * (Real.log (4 * cN) + KG + 2) + c₀') * B ^ (KG + 1) ≤
          C * Q * B ^ (KG + 1) := by
        have hle : Cg ≤ C := by
          rw [hC]; have := Nat.cast_nonneg (α := ℝ) (Fintype.card (X₂ ⊕ X₁)); linarith
        have e : Q * cN * (c₁' * (Real.log (4 * cN) + KG + 2) + c₀') * B ^ (KG + 1) =
            Cg * (Q * B ^ (KG + 1)) := by rw [hCg]; ring
        rw [e]
        have : 0 ≤ Q * B ^ (KG + 1) := by positivity
        nlinarith
      exact hgates.trans this
    · rw [Fintype.card_fin] at hcardW
      have hle : 630 + cW + Fintype.card (X₂ ⊕ X₁) ≤ C := by rw [hC]; linarith
      have hX0 : (0 : ℝ) ≤ Fintype.card (X₂ ⊕ X₁) := Nat.cast_nonneg _
      have h1 : (630 + cW) * B ^ KG + Fintype.card (X₂ ⊕ X₁) ≤
          (630 + cW + Fintype.card (X₂ ⊕ X₁)) * B ^ (KG + 1) := by
        have h2 : (630 + cW) * B ^ KG ≤ (630 + cW) * B ^ (KG + 1) :=
          mul_le_mul_of_nonneg_left hKK (by linarith)
        have h3 : (Fintype.card (X₂ ⊕ X₁) : ℝ) ≤ Fintype.card (X₂ ⊕ X₁) * B ^ (KG + 1) :=
          le_mul_of_one_le_right hX0 (one_le_pow₀ hB1)
        nlinarith
      have h4 : (630 + cW + Fintype.card (X₂ ⊕ X₁)) * B ^ (KG + 1) ≤ C * B ^ (KG + 1) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      linarith
    · intro R _ _ _ _ x hH hrow hcol hent
      have h := (key (R := R) x ⟨hH, hrow, hcol, hent⟩).error
      rw [cleanEmb_sysEmb_io, hεε] at h
      exact fullOutputError_of_norm h
  · -- the clipped regime
    have Rg : LargeSparsityCore.Parameters.Regime σ θ (ε / 2 / 2) :=
      ⟨hσ1, hθ, by positivity, by linarith, not_lt.mp hbd', not_lt.mp hsg⟩
    have key : ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
        [FiniteDimensional ℂ R] (x : X), Prom x →
        GateOptimalBinary.SynthClaims (prims (R := R) D en x) 𝒢 (X₂ ⊕ X₁) L' (ε / 2)
          (synthBudget hS (ε / 2)
            (clNativeCircuitD D en sb hF.hsb σ θ (ε / 2 / 2) t μ fcirc ftw fpw acirc atw apw))
          (GateOptimalBinary.sysH (R := R) D en x) t (ε / 2 / 2)
          (2 * GateOptimalPrecision.Qmu s η μ t (ε / 2)) (fun p => 6 * nCallsN p (computeV k b))
          (nGatesN (clNativeCircuitD D en sb hF.hsb σ θ (ε / 2 / 2) t μ fcirc ftw fpw acirc atw
            apw))
          (clNativeCostD k sb fcirc acirc) (ε / 2 + ε / 2) := by
      intro R _ _ _ _ x hxp
      rcases gate_optimal_binaryD_synth (R := R) (hI x hxp) hP hξ0.le hξ0.le hδε arB harB scirc
          stw spw hsaok fcirc ftw fpw acirc atw apw hafok haaok hS hε2 with
        ⟨h0, -⟩ | ⟨-, h2, -⟩ | ⟨-, h⟩
      · exact absurd h0 (not_lt.mpr Rg.h_large)
      · exact absurd h2 hsg
      · exact h
    have hG : (clNativeCostD k sb fcirc acirc : ℝ) ≤ cG * B ^ KG := by
      have h1 := cl_cost_leD fcirc acirc hsbB hBk hB1 (hcostC.trans hPb)
      have e : (198 + 15 * PA) * B ^ KG = 198 * B ^ KG + 15 * (PA * B ^ KG) := by ring
      have h3 : 198 * B ≤ 198 * B ^ KG := mul_le_mul_of_nonneg_left hB1K (by norm_num)
      rw [hcG]
      linarith
    have hW : ((Fintype.card (SZ k b) + bT' + bP' + A' : ℕ) : ℝ) ≤ cW * B ^ KG := by
      have h1 : ((Fintype.card (SZ k b) + bT' + bP' + A' : ℕ) : ℝ) ≤ 8 * B + PA * B ^ KG := by
        rw [card_SZ]
        have h2 := hcostC.trans hPb
        have hb' : (b : ℝ) ≤ bd := by exact_mod_cast hbd
        push_cast at h2 ⊢
        have : (0 : ℝ) ≤ fcirc.length := Nat.cast_nonneg _
        have : (0 : ℝ) ≤ acirc.length := Nat.cast_nonneg _
        linarith
      have h3 : (8 + PA) * B ^ KG ≤ cW * B ^ KG :=
        mul_le_mul_of_nonneg_right (by rw [hcW]) (by positivity)
      have e : (8 + PA) * B ^ KG = 8 * B ^ KG + PA * B ^ KG := by ring
      linarith
    obtain ⟨hgates, hcardW, hcalls⟩ := claims_poly
      (key (R := EuclideanSpace ℂ (ULift.{w} (Fin 1))) x₀ hx₀) (KG := KG) (cG := cG)
      (cW := cW) hQ1 hQ'0 hQ'4 hε hε1' hε₄ rfl hB1 hBY hS'
      (by rw [Fintype.card_fin]; push_cast; linarith) (by omega) hcG0 hG hW hc₀' hc₁' hL'
    refine ⟨_, inferInstance, inferInstance, sysWire _ _ _ _ _ _ _ _,
      synthBudget hS (ε / 2)
        (clNativeCircuitD D en sb hF.hsb σ θ (ε / 2 / 2) t μ fcirc ftw fpw acirc atw apw),
      (key (R := EuclideanSpace ℂ (ULift.{w} (Fin 1))) x₀ hx₀).valid,
      (key (R := EuclideanSpace ℂ (ULift.{w} (Fin 1))) x₀ hx₀).gateset, ?_, ?_, ?_, ?_⟩
    · have h1 := hcalls (fun _ => true)
      rw [hcalls5] at h1
      push_cast at h1
      have : 0 ≤ Q := by linarith
      nlinarith
    · have : Q * cN * (c₁' * (Real.log (4 * cN) + KG + 2) + c₀') * B ^ (KG + 1) ≤
          C * Q * B ^ (KG + 1) := by
        have hle : Cg ≤ C := by
          rw [hC]; have := Nat.cast_nonneg (α := ℝ) (Fintype.card (X₂ ⊕ X₁)); linarith
        have e : Q * cN * (c₁' * (Real.log (4 * cN) + KG + 2) + c₀') * B ^ (KG + 1) =
            Cg * (Q * B ^ (KG + 1)) := by rw [hCg]; ring
        rw [e]
        have : 0 ≤ Q * B ^ (KG + 1) := by positivity
        nlinarith
      exact hgates.trans this
    · rw [Fintype.card_fin] at hcardW
      have hle : 630 + cW + Fintype.card (X₂ ⊕ X₁) ≤ C := by rw [hC]; linarith
      have hX0 : (0 : ℝ) ≤ Fintype.card (X₂ ⊕ X₁) := Nat.cast_nonneg _
      have h1 : (630 + cW) * B ^ KG + Fintype.card (X₂ ⊕ X₁) ≤
          (630 + cW + Fintype.card (X₂ ⊕ X₁)) * B ^ (KG + 1) := by
        have h2 : (630 + cW) * B ^ KG ≤ (630 + cW) * B ^ (KG + 1) :=
          mul_le_mul_of_nonneg_left hKK (by linarith)
        have h3 : (Fintype.card (X₂ ⊕ X₁) : ℝ) ≤ Fintype.card (X₂ ⊕ X₁) * B ^ (KG + 1) :=
          le_mul_of_one_le_right hX0 (one_le_pow₀ hB1)
        nlinarith
      have h4 : (630 + cW + Fintype.card (X₂ ⊕ X₁)) * B ^ (KG + 1) ≤ C * B ^ (KG + 1) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      linarith
    · intro R _ _ _ _ x hH hrow hcol hent
      have h := (key (R := R) x ⟨hH, hrow, hcol, hent⟩).error
      rw [cleanEmb_sysEmb_io, hεε] at h
      exact fullOutputError_of_norm h

/-! ### Theorem `gate:thm:main` for general sizes and general decoders -/

set_option maxHeartbeats 8000000 in
/-- **Theorem `gate:thm:main` for sparse access of general size and general
decoders.** Fix the computational assumptions of `gate:thm:main` for the decoder `val` of the
stored words (the arithmetic of the local rotation parameters of the three regimes on the value
word: `comp_rotArith` for the angles of the bounded regime at the rescalings `κ ∈ [1/η, √(2s)/η]`,
`comp_signedArithV`, `comp_clipArithV` at the public scales of the construction, with gates and
work at most `c_A (b_data + k + log₂(1/ξ) + 1)^{d_A}` at accuracy `ξ`) and a finite gate set
admitting single-qubit synthesis of length at most `c₁ log(1/ζ) + c₀` at accuracy `ζ`, with an exact
decomposition of its controlled one-qubit gates. There are constants `C` and `K` such that: for
sparse data of general size (`GeneralSparseAccess.QData`: an `N × N` matrix with `s`-sparse lists,
`1 ≤ s ≤ N`, on `k = ⌈log₂ N⌉`-qubit index registers, locators prescribed on valid list inputs only,
the value oracle XOR-writing a stored word on every pair of index words) with any public decoder
`val` of its stored words, stored words of `2b` bits with `b ≤ b_data`, `μ ≤ η ≤ √s μ`,
`η²|t|/μ ≥ 1` and `0 < ε ≤ 1/64`, one circuit over the gate set and the supplied sparse oracles,
fixed before the instance, uses at most `288·10¹² Q_μ` primitive sparse queries (an absolute
constant), at most `C Q_μ (𝔟 + 1)^K` gates with
`𝔟 = b_data + log₂(N+1) + log₂(s+1) + log₂((Q_μ+1)/ε)`, at most `k + C (𝔟 + 1)^K` qubits, and on
every instance whose matrix is Hermitian with row and column Euclidean norms at most `η` and entries
of modulus at most `μ` has full-output error at most `ε` on the clean embedding of the index
register, against the evolution of the matrix extended by zero to the index words `≥ N`, with an
untouched reference of any finite dimension. On an invalid index pair the local operations are
selected by the validity of the pair (the paragraph after the proof of Lemma `hs:lem:boundary`: "a
known fixed action independently of the returned value word"): the factors and the rotation of
the bounded regime, and the phase of the clipped rotation, are those of the zero entry
independently of the returned word; with the
branch bit `g` set, the angle word of the clipped rotation is the word of the arithmetic for the
returned word, within the accuracy `ξ` of the angle `2 arctan(2q [f])` of the zero entry (as
`|y(1, f, c₁, c₂)| = 2q [f]` for every entry), so that action is fixed up to `ξ`. -/
theorem gate_thm_main_decoder (cA : ℝ) (dA : ℕ) (hcA : 0 ≤ cA) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (Kd : ℕ) {𝒢 : Set Kind} {X₁ X₂ : Type} [Fintype X₁] [DecidableEq X₁]
    [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ}
    (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b) (bd : ℕ)
        (η μ t ε : ℝ),
        2 ^ k < 2 * N → b ≤ bd →
        comp_rotArith cA dA bd k b D.val (1 / η) (Real.sqrt (2 * s) / η) →
        comp_signedArithV cA dA bd k b D.val μ →
        comp_clipArithV cA dA bd k b D.val μ (genClipBeta η μ t ε) (genClipScale s η μ t ε) →
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
  obtain ⟨L', c₀', c₁', hc₀', hc₁', hS, hL'⟩ := synthesis_of_parts hc₀ hc₁
    ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  obtain ⟨C₀', K, hC₀', hbin⟩ := gate_main_dataDec.{u, 0, w} (4 * cA + 40) (max dA 1)
    (by positivity) hc₀ hc₁ Kd ext_singleQubitSynthesis ext_singleQubitLength
    ext_controlDecomposition
  -- one constant for the gates, the qubits and the calls of the circuit of the padded data
  set C₀ : ℝ := C₀' + 24 * 10 ^ 12 with hC₀def
  have hC₀ : 0 < C₀ := by rw [hC₀def]; linarith
  have hC₀le : C₀' ≤ C₀ := by rw [hC₀def]; linarith
  have hC₀c : (24 * 10 ^ 12 : ℝ) ≤ C₀ := by rw [hC₀def]; linarith
  set K' := max K 2 with hK'
  set a : ℝ := 4 * 7 ^ K' with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  set cG : ℝ := (a + 256 * (1 + (c₁' * (Real.log (2 * ((a + 256) * C₀ + 2)) + (K' : ℝ) + 1) +
    c₀'))) * C₀ with hcG
  have hcG0 : 0 ≤ cG := by
    have h0 : 0 ≤ (a + 256) * C₀ := by positivity
    have : 0 ≤ Real.log (2 * ((a + 256) * C₀ + 2)) := Real.log_nonneg (by linarith)
    positivity
  set C : ℝ := cG + 7 ^ K' * C₀ + 16 + Fintype.card (X₂ ⊕ X₁) with hC
  have hX0 : (0 : ℝ) ≤ Fintype.card (X₂ ⊕ X₁) := Nat.cast_nonneg _
  have h7C : 0 ≤ 7 ^ K' * C₀ := by positivity
  refine ⟨C, K', by rw [hC]; linarith, ?_⟩
  intro X N s k b D bd η μ t ε hk hbd hrot hsa hca hμη hηs hθ hε hε64
  have hεh : 0 < ε / 2 := by positivity
  have hε1 : ε ≤ 1 := by linarith
  have hε2 : ε ≤ 1 / 2 := by linarith
  -- the parameters
  have hμ0 : 0 < μ := by
    by_contra h
    have h' : μ ≤ 0 := not_lt.mp h
    have : η ^ 2 * |t| / μ ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg η) (abs_nonneg t)) h'
    linarith
  have hη0 : 0 < η := lt_of_lt_of_le hμ0 hμη
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hsP : ((sP s : ℕ) : ℝ) ≤ 2 * (s : ℝ) := by
    have h' : ((sP s : ℕ) : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast (sP_lt D.slots_pos).le
    push_cast at h'
    exact h'
  have hηs' : η ≤ Real.sqrt (sP s) * μ := by
    have h1 : Real.sqrt s ≤ Real.sqrt (sP s) :=
      Real.sqrt_le_sqrt (by exact_mod_cast le_sP s)
    have := mul_le_mul_of_nonneg_right h1 hμ0.le
    linarith
  -- the arithmetic of the padded data
  have hsP2 : Real.sqrt ((sP s : ℕ) : ℝ) / η ≤ Real.sqrt (2 * s) / η := by
    apply div_le_div_of_nonneg_right _ hη0.le
    exact Real.sqrt_le_sqrt hsP
  have hdecP := comp_decArith_mono (by linarith : 3 * cA + 18 ≤ 4 * cA + 40)
    (comp_decArith_padDataE hcA D (comp_rotArith_mono hrot hsP2))
  have hsaP := comp_signedArithD_padDataE hcA D hsa
  have hcaP := comp_clipArithD_padDataE hcA D (qval_nonneg _ _ _) hca
  have hsizes : BinarySizes D.padDataE (Equiv.refl _) (sbP s) :=
    ⟨(sbP_le D.s_le_pow).trans (Nat.le_succ k), rfl, fun j => pslot_range D.s_le_pow j⟩
  obtain ⟨W, _, _, sys, Cc, hv, hg, hcalls, hgates, hwires, herr⟩ :=
    hbin D.padDataE (Equiv.refl _) (sbP s) bd η μ t (ε / 2) hsizes hbd hdecP hsaP hcaP hμη hηs'
      hθ hεh (by linarith)
  set Q := twoNormBound s η μ t ε with hQdef
  set Q' := twoNormBound (sP s) η μ t (ε / 2) with hQ'def
  have hQ1 : 1 ≤ Q := by
    have h1 : η / μ ≤ Real.sqrt s := by rw [div_le_iff₀ hμ0]; linarith
    have h2 : η ^ 2 * |t| / μ = η / μ * (η * |t|) := by field_simp
    have h3 : η / μ * (η * |t|) ≤ Real.sqrt s * (η * |t|) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h4 := le_twoNormBound (s := s) (t := t) hs0 hη0.le hμ0.le hε hε1
    nlinarith
  have hQ'0 : 0 ≤ Q' := by
    have := le_twoNormBound (s := sP s) (t := t) (Nat.cast_nonneg _) hη0.le hμ0.le hεh
      (by linarith)
    have : 0 ≤ Real.sqrt (sP s) * η * |t| := by positivity
    linarith
  have hQ'Q : Q' ≤ 4 * Q := by
    have h1 := twoNormBound_le_of_le (t := t) hs0 (Nat.cast_nonneg _) hsP hη0.le hμ0.le hεh
      (by linarith)
    have h2 : twoNormBound s η μ t (ε / 2) ≤ 2 * twoNormBound s η μ t ε := by
      rw [← qmu_eq, ← qmu_eq]
      exact GateOptimalPrecision.Qmu_half_le hη0.le hμ0 (by linarith) hε hε2
    linarith
  -- the budget word
  set B := gateWord bd N s Q ε + 1 with hBdef
  have hY1 : 1 ≤ (Q + 1) / ε := by rw [le_div_iff₀ hε]; linarith
  have hlogY : 0 ≤ Real.logb 2 ((Q + 1) / ε) := Real.logb_nonneg one_lt_two hY1
  have hlogN : 0 ≤ Real.logb 2 ((N : ℝ) + 1) :=
    Real.logb_nonneg one_lt_two (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hlogs : 0 ≤ Real.logb 2 ((s : ℝ) + 1) := Real.logb_nonneg one_lt_two (by linarith)
  have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  have hB1 : 1 ≤ B := by rw [hBdef]; unfold gateWord; linarith
  have hBY : Real.logb 2 ((Q + 1) / ε) ≤ B := by rw [hBdef]; unfold gateWord; linarith
  have hBk : (k : ℝ) ≤ B := by
    have := k_le_logb hk
    rw [hBdef]; unfold gateWord; linarith
  have hBb : (b : ℝ) ≤ B := by
    have : (b : ℝ) ≤ bd := by exact_mod_cast hbd
    rw [hBdef]; unfold gateWord; linarith
  have hBK : 1 ≤ B ^ K' := one_le_pow₀ hB1
  have hB1K : B ≤ B ^ K' := le_self_pow₀ hB1 (by omega)
  -- the word of the padded data
  have hcard : Fintype.card (Cfg (Fin (k + 1))) = 2 ^ (k + 1) := card_eq_two_pow (Equiv.refl _)
  have hB' : gateWord bd (Fintype.card (Cfg (Fin (k + 1)))) (sP s) Q' (ε / 2) + 1 ≤ 7 * B := by
    rw [hcard]
    have h1 := logb_pow_succ_le hk
    have h2 := logb_scale_le hQ'0 hQ'Q hε
    have h3 := logb_sP_le D.slots_pos
    rw [hBdef]
    unfold gateWord
    linarith
  have hB'0 : 0 ≤ gateWord bd (Fintype.card (Cfg (Fin (k + 1)))) (sP s) Q' (ε / 2) + 1 := by
    have hY' : 1 ≤ (Q' + 1) / (ε / 2) := by rw [le_div_iff₀ hεh]; linarith
    have h1 := Real.logb_nonneg one_lt_two hY'
    have hc0 : (0 : ℝ) ≤ ((Fintype.card (Cfg (Fin (k + 1))) : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : 0 ≤ Real.logb 2 (((Fintype.card (Cfg (Fin (k + 1))) : ℕ) : ℝ) + 1) :=
      Real.logb_nonneg one_lt_two (by linarith)
    have hs0' : (0 : ℝ) ≤ ((sP s : ℕ) : ℝ) := Nat.cast_nonneg _
    have h3 : 0 ≤ Real.logb 2 (((sP s : ℕ) : ℝ) + 1) :=
      Real.logb_nonneg one_lt_two (by linarith)
    unfold gateWord
    linarith
  have hpow : (gateWord bd (Fintype.card (Cfg (Fin (k + 1)))) (sP s) Q' (ε / 2) + 1) ^ K ≤
      7 ^ K' * B ^ K' := by
    calc (gateWord bd (Fintype.card (Cfg (Fin (k + 1)))) (sP s) Q' (ε / 2) + 1) ^ K
        ≤ (7 * B) ^ K := pow_le_pow_left₀ hB'0 hB' K
      _ = 7 ^ K * B ^ K := mul_pow _ _ _
      _ ≤ 7 ^ K' * B ^ K' :=
          mul_le_mul (pow_le_pow_right₀ (by norm_num) (le_max_left K 2))
            (pow_le_pow_right₀ hB1 (le_max_left K 2)) (by positivity) (by positivity)
  -- the counts of the circuit of the padded data
  have hQ'c : (24 * 10 ^ 12 : ℝ) * Q' ≤ 24 * 10 ^ 12 * (4 * Q) :=
    mul_le_mul_of_nonneg_left hQ'Q (by norm_num)
  have hnC : (nCallsN (fun _ => true) Cc : ℝ) ≤ 4 * C₀ * Q := by
    have h1 : (24 * 10 ^ 12 : ℝ) * (4 * Q) ≤ C₀ * (4 * Q) :=
      mul_le_mul_of_nonneg_right hC₀c (by linarith)
    linarith
  have hnG : (nGatesN Cc : ℝ) ≤ a * C₀ * Q * B ^ K' := by
    have h2 : C₀' * Q' * (gateWord bd (Fintype.card (Cfg (Fin (k + 1)))) (sP s) Q' (ε / 2) + 1) ^ K ≤
        C₀ * (4 * Q) * (7 ^ K' * B ^ K') :=
      mul_le_mul (mul_le_mul hC₀le hQ'Q hQ'0 hC₀.le) hpow (by positivity) (by positivity)
    have e : C₀ * (4 * Q) * (7 ^ K' * B ^ K') = a * C₀ * Q * B ^ K' := by rw [ha]; ring
    linarith
  have hG : (implG k b : ℝ) ≤ 64 * B := by
    unfold implG
    push_cast
    linarith
  -- the accuracy of the synthesis
  set n := nGatesN (subst (implPE N s) Cc) with hn
  set ζ : ℝ := ε / 2 / ((n : ℝ) + 1) with hζ
  have hζ0 : 0 < ζ := by positivity
  obtain ⟨hv', hg', hcalls', hgates', hn'⟩ :=
    genCircE_spec (N := N) (s := s) hS hζ0 Cc hv hg
  refine ⟨(W ⊕ GeneralSparseAccess.AW k b) ⊕ (X₂ ⊕ X₁), inferInstance, inferInstance,
    genSys (X₂ ⊕ X₁) sys, genCircE hS ζ N s Cc, hv', hg', ?_, ?_, ?_, ?_⟩
  · -- the calls
    have h1 : (nCallsN (fun _ => true) (genCircE hS ζ N s Cc) : ℝ) ≤
        3 * nCallsN (fun _ => true) Cc := by exact_mod_cast hcalls'
    linarith
  · -- the gates
    have h1 : (nGatesN (genCircE hS ζ N s Cc) : ℝ) ≤
        ((nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc * (1 + L' ζ) : ℕ) : ℝ) := by
      exact_mod_cast hgates'
    have h2 : ((nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc * (1 + L' ζ) : ℕ) : ℝ) ≤
        (a + 256 * (1 + (c₁' * (Real.log (2 * ((a + 256) * C₀ + 2)) + (K' : ℝ) + 1) +
          c₀'))) * C₀ * Q * B ^ K' :=
      gen_gates_le (K := K') (le_max_right K 2) (by linarith) hB1 hC₀.le (by positivity) hc₀'
        hc₁' hε hε1 hBY hnG hnC hG hn' hL'
    have h3 : cG * Q * B ^ K' ≤ C * Q * B ^ K' := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      linarith
    have e : (a + 256 * (1 + (c₁' * (Real.log (2 * ((a + 256) * C₀ + 2)) + (K' : ℝ) + 1) +
        c₀'))) * C₀ * Q * B ^ K' = cG * Q * B ^ K' := by rw [hcG]
    linarith
  · -- the qubits
    have hcW : Fintype.card ((W ⊕ GeneralSparseAccess.AW k b) ⊕ (X₂ ⊕ X₁)) =
        Fintype.card W + (6 * k + 6 + 2 * b) + Fintype.card (X₂ ⊕ X₁) := by
      rw [Fintype.card_sum, Fintype.card_sum, card_AW]
    rw [hcW]
    push_cast
    have h1 : (Fintype.card W : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + C₀ * (7 ^ K' * B ^ K') := by
      have h1a := mul_le_mul_of_nonneg_left hpow hC₀'.le
      have h1b : C₀' * (7 ^ K' * B ^ K') ≤ C₀ * (7 ^ K' * B ^ K') :=
        mul_le_mul_of_nonneg_right hC₀le (by positivity)
      linarith
    push_cast at h1
    have h2 : 6 * (k : ℝ) + 7 + 2 * b ≤ 15 * B ^ K' := by nlinarith
    have h3 : (Fintype.card (X₂ ⊕ X₁) : ℝ) ≤ Fintype.card (X₂ ⊕ X₁) * B ^ K' :=
      le_mul_of_one_le_right hX0 hBK
    have h4 : C₀ * (7 ^ K' * B ^ K') + 15 * B ^ K' + Fintype.card (X₂ ⊕ X₁) * B ^ K' ≤
        C * B ^ K' := by
      have e : C₀ * (7 ^ K' * B ^ K') + 15 * B ^ K' + Fintype.card (X₂ ⊕ X₁) * B ^ K' =
          (7 ^ K' * C₀ + 15 + Fintype.card (X₂ ⊕ X₁)) * B ^ K' := by ring
      rw [e]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    linarith
  · -- the error
    intro R _ _ _ _ x hH hrow hcol hent
    have hM := padForm_padDataE D
    have h1 := herr (R := R) x (hM.isHermitian x hH) (hM.row_le x hrow) (hM.col_le x hcol)
      (hM.entry_le x hμ0.le hent)
    have h2 := genCircE_error D hS hζ0 sys Cc hv x t (ε / 2) hεh.le h1
    intro ψ hψ
    refine (h2 ψ hψ).trans ?_
    have h3 : (n : ℝ) * ζ ≤ ε / 2 := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      rw [hζ, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith

end

end ManuscriptConformance
