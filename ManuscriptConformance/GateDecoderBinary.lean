import ManuscriptConformance.GateDecoderTables
import GateEfficientBitBudget.Hamiltonian

/-!
# Conformance: the binary decoder meets the assumptions of the general-decoder theorems

`hs_thm_gates_decoder` and `gate_thm_main_decoder` replace the decoder `c₀(X + iY)` of
`hs_thm_gates_general` and `gate_thm_main_general` (`formal_binaryDecoder`) by any public decoder,
with the arithmetic of the decoder as computational assumption. For the binary decoder these
assumptions follow from the hypotheses of the general-size theorems, so the general-decoder
theorems extend them (with other constants):

* `rotWordArith_cordic`: for `b > 0` and `κ > 0`, the package's CORDIC arithmetic
  (`GateBinary.cordicArith`) placed on the value word is a rotation arithmetic of `κ (X + iY)` at
  every accuracy `ζ ∈ (0, 1]`, with at most `29600 (W + 1)³` gates and work wires for its words
  `W = GateBitBudget.cordicWords 0 b κ ζ`;
* **`comp_rotArith_binary`**: `comp_rotArith` with `c_A = 2·10⁷` and `d_A = 3` at the rescalings
  `κ ∈ [1/η, √(2s)/η]` for the decoder `c₀(X + iY)` with `c₀`, `η` of bit length `b_data`
  (`comp_bits b b_data [c₀, η]`, as in `hs_thm_gates_general`);
* **`comp_signedArithV_binary`**, **`comp_clipArithV_binary`**: `comp_signedArithV` and
  `comp_clipArithV` from the binary assumptions `comp_signedArith` (at `c₀/μ`) and
  `comp_clipArith` of `gate_thm_main_general`, with the same constants;
* `comp_rotArith_dmono`, `comp_signedArithV_dmono`, `comp_clipArithV_dmono`: the assumptions for
  every larger exponent `d_A` (with `comp_rotArith_cmono`, `comp_signedArithV_cmono` and
  `comp_clipArithV_cmono` for larger `c_A`, one pair `c_A`, `d_A` serves all three);
* **`hs_thm_gates_general_of_decoder`**, **`gate_thm_main_general_of_decoder`**: under the
  hypotheses of `hs_thm_gates_general` and `gate_thm_main_general` the conclusions of the decoder
  theorems hold, with other constants `C` and `K` (`hs_thm_gates_decoder` at `c_A = 2·10⁷`,
  `d_A = 3`; `gate_thm_main_decoder` at `max(c_A, 2·10⁷)`, `max(d_A, 3)`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace ManuscriptConformance

noncomputable section
open SparseHamiltonian SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget SparseHamiltonian.GeneralDecoder

/-! ### The CORDIC arithmetic on the value word -/

section Cordic

/-- **The rotation properties of the CORDIC arithmetic** (the fields of `GateNative.ArithOK` but
the independence of an orientation wire, which a value word does not have): for `b > 0`, `κ > 0`
and distinct input wires, the CORDIC arithmetic writes the angle words of `2 arctan |κ (X + iY)|` and `arg (X + iY)`
within `ζ` and restores its work wires (the proof of `GateBinary.cordicArith_ok`). -/
theorem cordicArith_rot {B : Type*} [DecidableEq B] (b : ℕ) (hb : 0 < b) (xw yw : Fin b → B)
    (hxy : Function.Injective (Sum.elim xw yw)) (κ ζ : ℝ) (hκ : 0 < κ) (hζ : 0 < ζ)
    (hζ1 : ζ ≤ 1) :
    (∀ g ∈ (cordicArith b xw yw κ ζ).circ, g.cs.length ≤ 3) ∧
    Classical (cordicArith b xw yw κ ζ).circ ∧
    (∀ x : Cfg B, cfgRun (cordicArith b xw yw κ ζ).circ (Sum.elim x (fun _ => false)) =
      Sum.elim x (Sum.elim (Sum.elim ((cordicArith b xw yw κ ζ).tw x)
        ((cordicArith b xw yw κ ζ).pw x)) (fun _ => false))) ∧
    (∀ x, |thetaVal ((cordicArith b xw yw κ ζ).tw x) -
      2 * Real.arctan ‖binDec xw yw κ x‖| ≤ ζ) ∧
    (∀ x, binDec xw yw κ x ≠ 0 → ∃ m : ℤ, |phiVal ((cordicArith b xw yw κ ζ).pw x) -
      Complex.arg (binDec xw yw κ x) - 2 * Real.pi * m| ≤ ζ) := by
  have hP := Cordic.params_OK b hb κ ζ hκ
  have hnorm : ∀ x : Cfg B,
      ‖binDec xw yw κ x‖ = κ * ‖Cordic.zIn (P := Cordic.params b κ ζ) (x ∘ Sum.elim xw yw)‖ := by
    intro x
    rw [binDec_eq b xw yw κ ζ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', hgg⟩ := List.mem_map.1 hg
    rw [← hgg]
    exact circW_cs (Cordic.params b κ ζ) xw yw g' hg'
  · exact classical_map_toGate _ (circW_proper hP hxy)
  · intro x
    have h := cfgRun_map_toGate (circW (Cordic.params b κ ζ) xw yw) (Sum.elim x (fun _ => false))
    rw [circW_run hP hxy x] at h
    exact h
  · intro x
    have hU2 : (2 : ℝ) ≤ (Cordic.params b κ ζ).U := by
      have h := Cordic.params_U_ge b κ ζ hκ
      have : (2 : ℝ) ≤ 2 ^ ((Cordic.params b κ ζ).n + 4) :=
        le_self_pow₀ (by norm_num) (by omega)
      linarith
    have h := Cordic.theta_error hP (x ∘ Sum.elim xw yw) κ hκ (Cordic.params_c2 b κ ζ)
      (Cordic.params_U b κ ζ hκ) hU2
    rw [hnorm]
    exact h.trans (Cordic.params_theta b κ ζ hκ hζ hζ1)
  · intro x hx
    have hz : Cordic.zIn (P := Cordic.params b κ ζ) (x ∘ Sum.elim xw yw) ≠ 0 := by
      intro hz
      apply hx
      rw [binDec_eq b xw yw κ ζ, hz, mul_zero]
    obtain ⟨m, hm⟩ := Cordic.phi_error hP (x ∘ Sum.elim xw yw) hz (Cordic.params_c1 b κ ζ)
    refine ⟨m, ?_⟩
    rw [binDec_eq b xw yw κ ζ, Complex.arg_real_mul _ hκ]
    exact hm.trans (Cordic.params_phi b κ ζ hζ)

/-- **The gates and work wires of the CORDIC arithmetic**: at most `29600 (W + 1)³`,
`W = GateBitBudget.cordicWords 0 b κ ζ` (the counts of `GateBitBudget.cordic_words`, with the work
wires). -/
theorem cordicArith_cost_le {B : Type*} [DecidableEq B] (b : ℕ) (xw yw : Fin b → B) (κ ζ : ℝ) :
    (cordicArith b xw yw κ ζ).circ.length + (cordicArith b xw yw κ ζ).bT +
      (cordicArith b xw yw κ ζ).bP + (cordicArith b xw yw κ ζ).A ≤
        29600 * (cordicWords 0 b κ ζ + 1) ^ 3 := by
  obtain ⟨hc, hA, hT, hP'⟩ := cordicArith_counts b xw yw κ ζ
  obtain ⟨hn, hbT, hbP, hw⟩ := params_fields b κ ζ
  have hu : cordicWords 0 b κ ζ = 0 + b + Cordic.nOf ζ + Nat.clog 2 ⌈κ⌉₊ +
      Nat.clog 2 ⌈1 / κ⌉₊ := rfl
  have hW := GateODEBudget.wordOf_le (Cordic.nOf ζ)
  have hg2 : Cordic.g2Of (Cordic.nOf ζ) κ = Nat.clog 2 ⌈κ⌉₊ + Cordic.nOf ζ + 5 := by
    unfold Cordic.g2Of
    rfl
  have hlk : Cordic.lkOf κ = Nat.clog 2 ⌈1 / κ⌉₊ := by
    unfold Cordic.lkOf
    rfl
  have hnu : Cordic.nOf ζ ≤ cordicWords 0 b κ ζ := by
    rw [hu]
    omega
  have hNN : Cordic.nOf ζ * Cordic.nOf ζ ≤ cordicWords 0 b κ ζ * cordicWords 0 b κ ζ :=
    Nat.mul_le_mul hnu hnu
  have hWc : (Cordic.params b κ ζ).w ≤
      37 * ((cordicWords 0 b κ ζ + 1) * (cordicWords 0 b κ ζ + 1)) := by
    rw [hw, hg2, hlk]
    have e : (cordicWords 0 b κ ζ + 1) * (cordicWords 0 b κ ζ + 1) =
        cordicWords 0 b κ ζ * cordicWords 0 b κ ζ + 2 * cordicWords 0 b κ ζ + 1 := by ring
    rw [e]
    have h1 : Nat.clog 2 ⌈κ⌉₊ + Nat.clog 2 ⌈1 / κ⌉₊ + b ≤ cordicWords 0 b κ ζ := by
      rw [hu]
      omega
    omega
  obtain ⟨h1, h2⟩ := GateODEBudget.arith_poly 0 0 (Cordic.params b κ ζ).w
    (Cordic.params b κ ζ).n (Cordic.wordOf (Cordic.nOf ζ)) (cordicWords 0 b κ ζ) (by omega)
    (by omega) hWc (by rw [hn]; exact hnu) (by omega)
  rw [hbP, hbT] at hc
  have hT' : (cordicArith b xw yw κ ζ).bT = Cordic.wordOf (Cordic.nOf ζ) := hT.trans hbT
  have hP'' : (cordicArith b xw yw κ ζ).bP = Cordic.wordOf (Cordic.nOf ζ) := hP'.trans hbP
  have hp1 : cordicWords 0 b κ ζ + 1 ≤ (cordicWords 0 b κ ζ + 1) ^ 3 :=
    le_self_pow₀ (by omega) (by norm_num)
  omega

variable {b : ℕ}

theorem sumElim_inl_inr_injective (b : ℕ) :
    Function.Injective (Sum.elim (Sum.inl : Fin b → VW b) Sum.inr) := by
  rw [Sum.elim_inl_inr]
  exact Function.injective_id

/-- **The CORDIC arithmetic on the value word** (`GateBinary.cordicArith` with the components on
the two halves of the value word): for `b > 0` and `κ > 0`, a rotation arithmetic of every decoder
`dec = κ (X + iY)` at every accuracy `ζ ∈ (0, 1]`, with at most `29600 (W + 1)³` gates and work wires,
`W = GateBitBudget.cordicWords 0 b κ ζ`. -/
theorem rotWordArith_cordic (hb : 0 < b) {κ ζ : ℝ} (hκ : 0 < κ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (dec : Cfg (VW b) → ℂ) (hdec : ∀ z, dec z = (κ : ℂ) * gauss z) :
    ∃ (bT bP A : ℕ) (ar : RotWordArith b dec ζ bT bP A),
      ar.circ.length + bT + bP + A ≤ 29600 * (cordicWords 0 b κ ζ + 1) ^ 3 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := cordicArith_rot b hb (Sum.inl : Fin b → VW b) Sum.inr
    (sumElim_inl_inr_injective b) κ ζ hκ hζ hζ1
  have hdec' : ∀ z, dec z = binDec (Sum.inl : Fin b → VW b) Sum.inr κ z := hdec
  refine ⟨_, _, _, ⟨(cordicArith b (Sum.inl : Fin b → VW b) Sum.inr κ ζ).circ,
    (cordicArith b (Sum.inl : Fin b → VW b) Sum.inr κ ζ).tw,
    (cordicArith b (Sum.inl : Fin b → VW b) Sum.inr κ ζ).pw, h1, h2, h3, ?_, ?_⟩,
    cordicArith_cost_le b Sum.inl Sum.inr κ ζ⟩
  · intro x
    rw [hdec' x]
    exact h4 x
  · intro x hx
    rw [hdec' x] at hx ⊢
    exact h5 x hx

end Cordic

/-! ### The binary decoder meets the assumptions -/

section Binary

variable {X : Type*} {N s k b : ℕ}

/-- **The binary decoder meets the rotation arithmetic assumption** of `hs_thm_gates_decoder` and
`gate_thm_main_decoder`: for the decoder `c₀(X + iY)` (`BinaryDecoder`) with `c₀` and `η > 0` of
bit length `b_data` and `b ≤ b_data` (`comp_bits b b_data [c₀, η]`, the hypothesis of
`hs_thm_gates_general`), `comp_rotArith` holds with `c_A = 2·10⁷`, `d_A = 3` at the rescalings
`κ ∈ [1/η, √(2s)/η]`, by the CORDIC arithmetic at the scale `κ c₀`. -/
theorem comp_rotArith_binary (D : GeneralSparseAccess.QData X N s k b) {bd : ℕ} {c0 η : ℝ}
    (hF : BinaryDecoder D c0) (hbits : comp_bits b bd [c0, η]) (hη : 0 < η) :
    comp_rotArith (2 * 10 ^ 7) 3 bd k b D.val (1 / η) (Real.sqrt (2 * s) / η) := by
  obtain ⟨hbd, hc0b, hηb⟩ := hbits
  have hc0 := hF.hc0
  intro κ hκ hκm hκK ζ hζ hζ1
  have hκ' : 0 < κ * c0 := mul_pos hκ hc0
  have hdec : ∀ z, (κ : ℂ) * D.val z = ((κ * c0 : ℝ) : ℂ) * gauss z := by
    intro z
    rw [hF.dec z]
    push_cast
    ring
  obtain ⟨bT, bP, A, ar, hcost⟩ :=
    rotWordArith_cordic hF.hb hκ' hζ hζ1 (fun z => (κ : ℂ) * D.val z) hdec
  refine ⟨bT, bP, A, ar, ?_⟩
  -- the bit lengths of the CORDIC scale `κ c₀`
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast D.slots_pos
  have hsk : (s : ℝ) ≤ 2 ^ k := by exact_mod_cast D.s_le_pow
  have hsq : Real.sqrt (2 * s) ≤ 2 ^ (k + 1) := by
    have h1 : Real.sqrt (2 * (s : ℝ)) ≤ 2 * s := sqrt_le_self_of_one_le (by linarith)
    have h2 : (2 : ℝ) * s ≤ 2 ^ (k + 1) := by rw [pow_succ]; linarith
    linarith
  have hc0' : c0 ≤ 2 ^ bd := hc0b.lt.le
  have hη' : η ≤ 2 ^ bd := hηb.lt.le
  have hηi : 1 / η ≤ 2 ^ bd := by
    rw [div_le_iff₀ hη]
    have := hηb.one_le_mul hη
    linarith
  have hc0i : 1 / c0 ≤ 2 ^ bd := by
    rw [div_le_iff₀ hc0]
    have := hc0b.one_le_mul hc0
    linarith
  have hκu : κ * c0 ≤ 2 ^ (k + 1 + 2 * bd) := by
    have h1 : κ ≤ 2 ^ (k + 1) * 2 ^ bd := by
      calc κ ≤ Real.sqrt (2 * s) / η := hκK
        _ = Real.sqrt (2 * s) * (1 / η) := by ring
        _ ≤ 2 ^ (k + 1) * 2 ^ bd :=
            mul_le_mul hsq hηi (by positivity) (by positivity)
    calc κ * c0 ≤ 2 ^ (k + 1) * 2 ^ bd * 2 ^ bd :=
          mul_le_mul h1 hc0' hc0.le (by positivity)
      _ = 2 ^ (k + 1 + 2 * bd) := by ring
  have hκi : 1 / (κ * c0) ≤ 2 ^ (2 * bd) := by
    have h1 : 1 / (κ * c0) ≤ η * (1 / c0) := by
      rw [div_le_iff₀ hκ']
      have h2 : 1 ≤ κ * η := by
        have := mul_le_mul_of_nonneg_right hκm hη.le
        rwa [one_div, inv_mul_cancel₀ hη.ne'] at this
      have e : η * (1 / c0) * (κ * c0) = κ * η := by
        calc η * (1 / c0) * (κ * c0) = κ * η * (c0 * (1 / c0)) := by ring
          _ = κ * η := by rw [mul_one_div_cancel hc0.ne', mul_one]
      rw [e]
      exact h2
    calc 1 / (κ * c0) ≤ η * (1 / c0) := h1
      _ ≤ 2 ^ bd * 2 ^ bd := mul_le_mul hη' hc0i (by positivity) (by positivity)
      _ = 2 ^ (2 * bd) := by ring
  have wκ : (Nat.clog 2 ⌈κ * c0⌉₊ : ℝ) ≤ k + 1 + 2 * bd := by
    have := clog_ceil_le_nat _ _ hκu
    exact_mod_cast this
  have wκi : (Nat.clog 2 ⌈1 / (κ * c0)⌉₊ : ℝ) ≤ 2 * bd := by
    have := clog_ceil_le_nat _ _ hκi
    exact_mod_cast this
  -- the CORDIC steps
  have hX1 : 1 ≤ 1 / ζ := by rw [le_div_iff₀ hζ]; linarith
  have hz : 8 / ζ ≤ 2 ^ 3 * (1 / ζ) ^ 1 := by
    rw [pow_one]
    have e : (2 : ℝ) ^ 3 * (1 / ζ) = 8 / ζ := by ring
    rw [e]
  have wn : (Cordic.nOf ζ : ℝ) ≤ Real.logb 2 (1 / ζ) + 6 := by
    have h := clog_le_mul_pow _ (2 ^ 3) (1 / ζ) 3 1 hX1 le_rfl hz
    unfold Cordic.nOf
    push_cast at h ⊢
    linarith
  have hu : (cordicWords 0 b (κ * c0) ζ : ℝ) = b + (Cordic.nOf ζ : ℝ) +
      (Nat.clog 2 ⌈κ * c0⌉₊ : ℝ) + (Nat.clog 2 ⌈1 / (κ * c0)⌉₊ : ℝ) := by
    unfold cordicWords
    push_cast
    ring
  -- the bound
  have hb' : (b : ℝ) ≤ bd := by exact_mod_cast hbd
  have hL : 0 ≤ Real.logb 2 (1 / ζ) := Real.logb_nonneg one_lt_two hX1
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  set Y : ℝ := (bd : ℝ) + k + Real.logb 2 (1 / ζ) + 1 with hY
  have hY1 : 1 ≤ Y := by
    have : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
    rw [hY]
    linarith
  have hU : (cordicWords 0 b (κ * c0) ζ : ℝ) + 1 ≤ 8 * Y := by
    rw [hu, hY]
    linarith
  have hU0 : (0 : ℝ) ≤ (cordicWords 0 b (κ * c0) ζ : ℝ) + 1 := by positivity
  have hcost' : ((ar.circ.length + bT + bP + A : ℕ) : ℝ) ≤
      29600 * ((cordicWords 0 b (κ * c0) ζ : ℝ) + 1) ^ 3 := by
    exact_mod_cast hcost
  have hcube : ((cordicWords 0 b (κ * c0) ζ : ℝ) + 1) ^ 3 ≤ (8 * Y) ^ 3 :=
    pow_le_pow_left₀ hU0 hU 3
  have e : (8 * Y) ^ 3 = 512 * Y ^ 3 := by ring
  have hY3 : 0 ≤ Y ^ 3 := by positivity
  calc ((ar.circ.length + bT + bP + A : ℕ) : ℝ)
      ≤ 29600 * ((cordicWords 0 b (κ * c0) ζ : ℝ) + 1) ^ 3 := hcost'
    _ ≤ 29600 * (512 * Y ^ 3) := by rw [← e]; exact mul_le_mul_of_nonneg_left hcube (by norm_num)
    _ ≤ 2 * 10 ^ 7 * Y ^ 3 := by nlinarith

/-- **The binary decoder meets the factor arithmetic assumption of the signed-factor regime**:
`comp_signedArithV` from the binary assumption `comp_signedArith` at the scale `c₀/μ` (of
`gate_thm_main_general`), with the same constants. -/
theorem comp_signedArithV_binary (D : GeneralSparseAccess.QData X N s k b) {bd : ℕ} {cA c0 μ : ℝ}
    {dA : ℕ} (hF : BinaryDecoder D c0) (h : comp_signedArith cA dA bd k b (c0 / μ)) :
    comp_signedArithV cA dA bd k b D.val μ := by
  intro ξ hξ hξ1
  obtain ⟨bT, bP, A, ar, hcost⟩ := h ξ hξ hξ1
  refine ⟨bT, bP, A, ⟨ar.circ, ar.tw, ar.pw, ar.elem, ar.classical, ar.compute⟩, ?_, hcost⟩
  intro w
  have e : sgVal D.val μ w = GateOptimalBinary.wdec (c0 / μ) w := by
    unfold sgVal GateOptimalBinary.wdec
    rw [hF.dec w]
    congr 1
    push_cast
    ring
  rw [e]
  exact ar.acc w

/-- **The binary decoder meets the arithmetic assumption of the clipped regime**:
`comp_clipArithV` from the binary assumption `comp_clipArith` (of `gate_thm_main_general`), with
the same constants. -/
theorem comp_clipArithV_binary (D : GeneralSparseAccess.QData X N s k b) {bd : ℕ}
    {cA c0 μ β q : ℝ} {dA : ℕ} (hF : BinaryDecoder D c0)
    (h : comp_clipArith cA dA bd k b μ β q c0) : comp_clipArithV cA dA bd k b D.val μ β q := by
  intro ξ hξ hξ1
  obtain ⟨bT, bP, A, af, aa, hcost⟩ := h ξ hξ hξ1
  have ef : cfVal D.val μ β = GateOptimalBinary.cfdec μ β c0 := by
    funext w
    unfold cfVal GateOptimalBinary.cfdec
    rw [hF.dec]
  have ek : ckVal D.val μ β q = GateOptimalBinary.ckdec μ β q c0 := by
    funext w
    unfold ckVal GateOptimalBinary.ckdec
    rw [hF.dec]
  refine ⟨bT, bP, A, ⟨af.circ, af.tw, af.pw, af.elem, af.classical, af.compute⟩,
    ⟨aa.circ, aa.tw, aa.pw, aa.elem, aa.classical, aa.compute⟩, ?_, ?_, hcost⟩
  · rw [ef]
    exact af.acc
  · rw [ek]
    exact ⟨aa.theta, aa.phi⟩

end Binary

/-! ### Larger exponents -/

theorem pow_le_pow_of_word {bd k : ℕ} {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) {dA dA' : ℕ}
    (hd : dA ≤ dA') :
    ((bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) ^ dA ≤
      ((bd : ℝ) + k + Real.logb 2 (1 / ξ) + 1) ^ dA' := by
  have hL : 0 ≤ Real.logb 2 (1 / ξ) :=
    Real.logb_nonneg one_lt_two (by rw [le_div_iff₀ hξ]; linarith)
  have hbd : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  exact pow_le_pow_right₀ (by linarith) hd

/-- The rotation arithmetic assumption holds for every larger exponent `d_A` (`c_A ≥ 0`). -/
theorem comp_rotArith_dmono {cA : ℝ} {dA dA' bd k b : ℕ} {val : Cfg (VW b) → ℂ} {K₀ K : ℝ}
    (hcA : 0 ≤ cA) (hd : dA ≤ dA') (h : comp_rotArith cA dA bd k b val K₀ K) :
    comp_rotArith cA dA' bd k b val K₀ K := by
  intro κ hκ hκm hκK ζ hζ hζ1
  obtain ⟨bT, bP, A, ar, hcost⟩ := h κ hκ hκm hκK ζ hζ hζ1
  exact ⟨bT, bP, A, ar, hcost.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_word hζ hζ1 hd) hcA)⟩

/-- The factor arithmetic assumption of the signed-factor regime holds for every larger exponent
`d_A` (`c_A ≥ 0`). -/
theorem comp_signedArithV_dmono {cA : ℝ} {dA dA' bd k b : ℕ} {val : Cfg (VW b) → ℂ} {μ : ℝ}
    (hcA : 0 ≤ cA) (hd : dA ≤ dA') (h : comp_signedArithV cA dA bd k b val μ) :
    comp_signedArithV cA dA' bd k b val μ := by
  intro ξ hξ hξ1
  obtain ⟨bT, bP, A, ar, hacc, hcost⟩ := h ξ hξ hξ1
  exact ⟨bT, bP, A, ar, hacc, hcost.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_word hξ hξ1 hd) hcA)⟩

/-- The arithmetic assumption of the clipped regime holds for every larger exponent `d_A`
(`c_A ≥ 0`). -/
theorem comp_clipArithV_dmono {cA : ℝ} {dA dA' bd k b : ℕ} {val : Cfg (VW b) → ℂ} {μ β q : ℝ}
    (hcA : 0 ≤ cA) (hd : dA ≤ dA') (h : comp_clipArithV cA dA bd k b val μ β q) :
    comp_clipArithV cA dA' bd k b val μ β q := by
  intro ξ hξ hξ1
  obtain ⟨bT, bP, A, af, aa, haf, haa, hcost⟩ := h ξ hξ hξ1
  exact ⟨bT, bP, A, af, aa, haf, haa, hcost.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_word hξ hξ1 hd) hcA)⟩

/-! ### The general-size hypotheses give the conclusions of the decoder theorems -/

universe u v w

section General

open ContinuousLinearMap SparseHamiltonian.GateSynth
open scoped InnerProduct

set_option maxHeartbeats 4000000 in
/-- **`hs_thm_gates_decoder` under the hypotheses of `hs_thm_gates_general`**: for sparse access of
general size with the decoder `c₀(X + iY)` (`formal_binaryDecoder`), `comp_bits b b_data [c₀, η]`
and `η > 0`, the conclusion of `hs_thm_gates_decoder` holds (`hs_thm_gates_decoder` at
`c_A = 2·10⁷`, `d_A = 3`, with `comp_rotArith_binary`). The gate exponent `K` is existential here,
where `hs_thm_gates_general` fixes it at `4`. -/
theorem hs_thm_gates_general_of_decoder {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (Kd : ℕ)
    {𝒢 : Set Kind} {X₁ X₂ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂]
    {L : ℝ → ℕ} (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b) (bd : ℕ)
        (c0 η t ε : ℝ),
        2 ^ k < 2 * N → formal_binaryDecoder D c0 → comp_bits b bd [c0, η] →
        0 < η → 0 < ε → ε ≤ 1 / 2 →
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
  obtain ⟨C, K, hC, h⟩ := hs_thm_gates_decoder.{u, w} (2 * 10 ^ 7) 3 (by norm_num) hc₀ hc₁ Kd
    ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  refine ⟨C, K, hC, ?_⟩
  intro X N s k b D bd c0 η t ε hk hF hbits hη hε hε2
  have hrot := comp_rotArith_binary D hF hbits hη
  obtain ⟨hbd, -, -⟩ := hbits
  exact h D bd η t ε hk hbd hrot hη hε hε2

set_option maxHeartbeats 4000000 in
/-- **`gate_thm_main_decoder` under the hypotheses of `gate_thm_main_general`**: for sparse access
of general size with the decoder `c₀(X + iY)` (`formal_binaryDecoder`), `comp_bits b b_data
[c₀, η, μ]` and the binary arithmetic assumptions `comp_signedArith`, `comp_clipArith` with
constants `c_A`, `d_A`, the conclusion of `gate_thm_main_decoder` holds (`gate_thm_main_decoder`
at `max(c_A, 2·10⁷)`, `max(d_A, 3)`, with `comp_rotArith_binary`, `comp_signedArithV_binary`,
`comp_clipArithV_binary`), with other constants `C` and `K`. -/
theorem gate_thm_main_general_of_decoder (cA : ℝ) (dA : ℕ) (hcA : 0 ≤ cA) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (Kd : ℕ) {𝒢 : Set Kind} {X₁ X₂ : Type} [Fintype X₁]
    [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ}
    (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b) (bd : ℕ)
        (c0 η μ t ε : ℝ),
        2 ^ k < 2 * N → formal_binaryDecoder D c0 → comp_bits b bd [c0, η, μ] →
        comp_signedArith cA dA bd k b (c0 / μ) →
        comp_clipArith cA dA bd k b μ (genClipBeta η μ t ε) (genClipScale s η μ t ε) c0 →
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
  obtain ⟨C, K, hC, h⟩ := gate_thm_main_decoder.{u, w} (max cA (2 * 10 ^ 7)) (max dA 3)
    (le_max_of_le_left hcA) hc₀ hc₁ Kd ext_singleQubitSynthesis ext_singleQubitLength
    ext_controlDecomposition
  refine ⟨C, K, hC, ?_⟩
  intro X N s k b D bd c0 η μ t ε hk hF hbits hsa hca hμη hηs hθ hε hε64
  have hμ0 : 0 < μ := by
    by_contra hμ
    have h' : μ ≤ 0 := not_lt.mp hμ
    have : η ^ 2 * |t| / μ ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg η) (abs_nonneg t)) h'
    linarith
  have hη : 0 < η := lt_of_lt_of_le hμ0 hμη
  obtain ⟨hbd, hc0b, hηb, -⟩ := hbits
  have hbits' : comp_bits b bd [c0, η] := ⟨hbd, hc0b, hηb⟩
  exact h D bd η μ t ε hk hbd
    (comp_rotArith_cmono (le_max_right _ _)
      (comp_rotArith_dmono (by norm_num) (le_max_right _ _) (comp_rotArith_binary D hF hbits' hη)))
    (comp_signedArithV_cmono (le_max_left _ _)
      (comp_signedArithV_dmono hcA (le_max_left _ _) (comp_signedArithV_binary D hF hsa)))
    (comp_clipArithV_cmono (le_max_left _ _)
      (comp_clipArithV_dmono hcA (le_max_left _ _) (comp_clipArithV_binary D hF hca)))
    hμη hηs hθ hε hε64

end General

end

end ManuscriptConformance
