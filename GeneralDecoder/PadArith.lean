import GeneralDecoder.FlagGen
import GeneralSparseAccess.PadE

/-!
# The arithmetic of the padded data with a validity decoder

The padded data with a validity decoder (`QData.padDataE`) decode a stored word `w` of a pair of
index words as `val w` on a valid pair and as `0` otherwise (`pdecode_flag`). From a word
arithmetic on the value word for the decoder `val` of the data, the wrappers of
`GeneralDecoder.FlagGen` give the arithmetic hypotheses of the native operations of Theorem
`gate:thm:main` for the padded data:

* signed-factor regime: `sgFOD_padDataE_ok`, from a factor arithmetic of `clip(val w/μ)`
  (`sgVal`);
* clipped regime: `clFOD_padDataE_ok`, from a factor arithmetic of `[g] c₂(val w)` (`cfVal`), and
  `clNDD_padDataE_ok`, from an angle arithmetic of `y(g, f, c₁(val w), c₂(val w))` (`ckVal`), for
  `q ≥ 0`: on an invalid pair the clipped rotation is that of the zero entry,
  `y(g, f, 0, 0) = 2q [g][f]`, whose angle is the angle of the arithmetic when `g` is set and zero
  otherwise, and whose phase is zero.

`wrap_cost_le`: the gates and work wires of a wrapper.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralDecoder

noncomputable section
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative SparseHamiltonian.GateBinary
  GateOptimalPrecision
open SparseHamiltonian.GeneralSparseAccess
open GateOptimalBinary (PRf locF vF vF_injective valF locBF gBF ιFin ιCin ιFin_injective
  ιCin_injective locBF_ne_vF locBF_ne_ιFin locBF1_ne_ιCin edge_ne_locF ιS_ne_gW yC)
open LargeSparsityCore.Native (cclip ccorr)

/-! ### The validity of the pair of index words -/

theorem evalidW_iff {k N : ℕ} (ew : Cfg (EW (k + 1))) :
    evalidW N ew = true ↔
      PValid N (fun j => ew (Sum.inl j)) ∧ PValid N (fun j => ew (Sum.inr j)) := by
  unfold evalidW PValid mark lo
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]

/-- The validity decoder on a pair of index words: the decoder of the data on a valid pair, zero
otherwise. -/
theorem pdecode_flag {X : Type*} {N s k b : ℕ} (D : QData X N s k b) (ew : Cfg (EW (k + 1)))
    (w : Cfg (VW b)) :
    D.pdecode (phiE (Equiv.refl _) ew) w = if evalidW N ew then D.val w else 0 := by
  have he : phiE (Equiv.refl (Cfg (Fin (k + 1)))) ew =
      ((fun j => ew (Sum.inl j)), (fun j => ew (Sum.inr j))) := rfl
  rw [he]
  unfold QData.pdecode
  by_cases hv : evalidW N ew = true
  · rw [if_pos hv, if_pos ((evalidW_iff ew).mp hv)]
  · rw [if_neg hv, if_neg (fun h => hv ((evalidW_iff ew).mpr h))]

/-! ### The decoded entries of a decoder of the stored words -/

/-- The signed factor entry `clip(val w/μ)` of a decoder of the stored words. -/
def sgVal {b : ℕ} (val : Cfg (VW b) → ℂ) (μ : ℝ) (w : Cfg (VW b)) : ℂ :=
  NativeSignedFactor.clip (val w / (μ : ℂ))

/-- The clipped correction entry `[g] c₂` of the branch `g` and a stored word, with
`c₂ = ccorr_{μ,β}(val w)`. -/
def cfVal {b : ℕ} (val : Cfg (VW b) → ℂ) (μ β : ℝ) (w : Cfg (Unit ⊕ VW b)) : ℂ :=
  if w (Sum.inl ()) then ccorr μ β (val (fun v => w (Sum.inr v))) else 0

/-- The clipped value `y(g, f, c₁, c₂)` of the branch `g`, the flag `f` and a stored word, with
`c₁ = cclip_{μ,β}(val w)` and `c₂ = ccorr_{μ,β}(val w)`. -/
def ckVal {b : ℕ} (val : Cfg (VW b) → ℂ) (μ β q : ℝ) (w : Cfg ((Unit ⊕ Unit) ⊕ VW b)) : ℂ :=
  yC q (w (Sum.inl (Sum.inl ()))) (w (Sum.inl (Sum.inr ())))
    (cclip μ β (val (fun v => w (Sum.inr v)))) (ccorr μ β (val (fun v => w (Sum.inr v))))

theorem clip_zero : NativeSignedFactor.clip 0 = 0 := by
  simp [NativeSignedFactor.clip]

theorem cclip_zero (μ β : ℝ) : cclip μ β 0 = 0 := by
  simp [LargeSparsityCore.Native.cclip]

theorem ccorr_zero (μ β : ℝ) : ccorr μ β 0 = 0 := by
  simp [LargeSparsityCore.Native.ccorr, cclip_zero, clip_zero]

/-! ### The index wires of the native factor -/

/-- The index wires among the base wires of the native factor. -/
def ιEF (k b : ℕ) (e : EW k) : NB Empty (PRf k) (SZ k b) :=
  Sum.inl (Sum.inr (GateOptimalBinary.ιF k (ixPR k e)))

theorem ιEF_injective (k b : ℕ) : Function.Injective (ιEF k b) :=
  fun _ _ h => ixPR_injective k
    (GateOptimalBinary.ιF_injective k (Sum.inr_injective (Sum.inl_injective h)))

theorem ιEF_ne_vF (k b : ℕ) (e : EW k) (v : VW b) : ιEF k b e ≠ vF k b v := by
  simp [ιEF, vF]

theorem ιEF_ne_gBF (k b : ℕ) (e : EW k) : ιEF k b e ≠ gBF k b :=
  fun h => ιS_ne_gW k _ (Sum.inr_injective (Sum.inl_injective h))

theorem ιEF_ne_locBF (k b : ℕ) (e : EW k) (i : Fin 3) : ιEF k b e ≠ locBF k i :=
  fun h => edge_ne_locF k i e (Sum.inr_injective (Sum.inl_injective h)).symm

theorem ιEF_ne_ιFin (k b : ℕ) (e : EW k) (a : Unit ⊕ VW b) : ιEF k b e ≠ ιFin k b a := by
  rcases a with u | v
  · exact ιEF_ne_gBF k b e
  · exact ιEF_ne_vF k b e v

theorem ιEF_ne_ιCin (k b : ℕ) (e : EW k) (a : (Unit ⊕ Unit) ⊕ VW b) : ιEF k b e ≠ ιCin k b a := by
  rcases a with (u | u) | v
  · exact ιEF_ne_gBF k b e
  · exact ιEF_ne_locBF k b e 0
  · exact ιEF_ne_vF k b e v

/-! ### The decoded entries of the padded data -/

section Padded

variable {X : Type*} {N s k b : ℕ} (D : QData X N s k b)

/-- The entry of the padded data on the base wires of the native factor. -/
theorem entD_padDataE (y : Cfg (NB Empty (PRf (k + 1)) (SZ (k + 1) b))) :
    entD D.padDataE (Equiv.refl _) y =
      if evalidW N (fun e => y (ιEF (k + 1) b e)) then D.val (valF y) else 0 := by
  unfold entD
  rw [QData.padDataE_decode]
  exact pdecode_flag D (fun e => y (ιEF (k + 1) b e)) (valF y)

theorem sgDec_padDataE (μ : ℝ) (y : Cfg (NB Empty (PRf (k + 1)) (SZ (k + 1) b))) :
    sgDec D.padDataE (Equiv.refl _) μ y =
      if evalidW N (fun e => y (ιEF (k + 1) b e)) then
        sgVal D.val μ (fun v => y (vF (k + 1) b v)) else 0 := by
  have h : sgDec D.padDataE (Equiv.refl _) μ y =
      NativeSignedFactor.clip (entD D.padDataE (Equiv.refl _) y / (μ : ℂ)) := rfl
  rw [h, entD_padDataE]
  split_ifs
  · rfl
  · rw [zero_div, clip_zero]

theorem cfdecD_padDataE (μ β : ℝ) (y : Cfg (NB Empty (PRf (k + 1)) (SZ (k + 1) b))) :
    cfdecD D.padDataE (Equiv.refl _) μ β y =
      if evalidW N (fun e => y (ιEF (k + 1) b e)) then
        cfVal D.val μ β (fun a => y (ιFin (k + 1) b a)) else 0 := by
  unfold cfdecD cfVal
  rw [entD_padDataE]
  by_cases hv : evalidW N (fun e => y (ιEF (k + 1) b e)) = true
  · rw [if_pos hv, if_pos hv]
    rfl
  · rw [if_neg hv, if_neg hv, ccorr_zero, ite_self]

theorem ckdecD_padDataE (μ β q : ℝ) (y : Cfg (NB Empty (PRf (k + 1)) (SZ (k + 1) b))) :
    ckdecD D.padDataE (Equiv.refl _) μ β q y =
      if evalidW N (fun e => y (ιEF (k + 1) b e)) then
        ckVal D.val μ β q (fun a => y (ιCin (k + 1) b a))
      else (fun w : Cfg ((Unit ⊕ Unit) ⊕ VW b) =>
        yC q (w (Sum.inl (Sum.inl ()))) (w (Sum.inl (Sum.inr ()))) 0 0)
          (fun a => y (ιCin (k + 1) b a)) := by
  unfold ckdecD ckVal
  rw [entD_padDataE]
  by_cases hv : evalidW N (fun e => y (ιEF (k + 1) b e)) = true
  · rw [if_pos hv, if_pos hv]
    rfl
  · rw [if_neg hv, if_neg hv, cclip_zero, ccorr_zero]
    rfl

end Padded

/-! ### The arithmetic hypotheses of the padded data -/

section Lifts

variable {X : Type*} {N s k b : ℕ} (D : QData X N s k b)

/-- **The factor arithmetic of the signed regime for the padded data**, from a word arithmetic of
the signed entry `clip(val w/μ)` on the value word. -/
theorem sgFOD_padDataE_ok (μ : ℝ) {ξ : ℝ} {bT bP A : ℕ} (ar : WordArith (VW b) bT bP A)
    (hacc : FactorAcc (sgVal D.val μ) ξ ar.tw ar.pw) :
    FactorArithOK (sgFOD (bT := bT) (bP := bP) (A := flagA k bT bP A + 1) D.padDataE
      (Equiv.refl _) μ (ar.flagLiftG N (ιEF (k + 1) b) (vF (k + 1) b) none).circ
      (ar.flagLiftG N (ιEF (k + 1) b) (vF (k + 1) b) none).tw
      (ar.flagLiftG N (ιEF (k + 1) b) (vF (k + 1) b) none).pw) ξ :=
  flagLiftG_factorOK N D.N_lt_pow_succ (ιEF_injective _ _) (vF_injective _ _)
    (fun e v => ιEF_ne_vF _ _ e v) ar hacc _ (locF (k + 1)) _ (sgDec_padDataE D μ)
    (fun i e h => ιEF_ne_locBF _ _ e i h.symm) (fun i j => locBF_ne_vF i j)

/-- **The factor arithmetic of the clipped regime for the padded data**, from a word arithmetic of
the correction entry `[g] c₂(val w)` on the branch and the value word. -/
theorem clFOD_padDataE_ok (μ β : ℝ) {ξ : ℝ} {bT bP A : ℕ} (ar : WordArith (Unit ⊕ VW b) bT bP A)
    (hacc : FactorAcc (cfVal D.val μ β) ξ ar.tw ar.pw) :
    FactorArithOK (clFOD (bT := bT) (bP := bP) (A := flagA k bT bP A + 1) D.padDataE
      (Equiv.refl _) μ β (ar.flagLiftG N (ιEF (k + 1) b) (ιFin (k + 1) b) none).circ
      (ar.flagLiftG N (ιEF (k + 1) b) (ιFin (k + 1) b) none).tw
      (ar.flagLiftG N (ιEF (k + 1) b) (ιFin (k + 1) b) none).pw) ξ :=
  flagLiftG_factorOK N D.N_lt_pow_succ (ιEF_injective _ _) ιFin_injective
    (fun e a => ιEF_ne_ιFin _ _ e a) ar hacc _ (locF (k + 1)) _ (cfdecD_padDataE D μ β)
    (fun i e h => ιEF_ne_locBF _ _ e i h.symm) (fun i j => locBF_ne_ιFin i j)

/-- **The angle arithmetic of the clipped regime for the padded data**, from a word arithmetic of
the clipped value `y(g, f, c₁(val w), c₂(val w))` on the branch, the flag and the value word, for
`q ≥ 0`: on an invalid pair the rotation of the zero entry `y(g, f, 0, 0) = 2q [g][f]`. -/
theorem clNDD_padDataE_ok (μ β q : ℝ) (hq : 0 ≤ q) {ζ : ℝ} {bT bP A : ℕ}
    (ar : WordArith ((Unit ⊕ Unit) ⊕ VW b) bT bP A)
    (hacc : RotAcc (ckVal D.val μ β q) ζ ar.tw ar.pw) :
    ArithOK (ar.flagLiftG N (ιEF (k + 1) b) (ιCin (k + 1) b) (some (Sum.inl (Sum.inl ()))))
      (Sum.inl (Sum.inr (locF (k + 1) 1))) (ckdecD D.padDataE (Equiv.refl _) μ β q) ζ := by
  refine flagLiftG_rotOK (dec0 := fun w : Cfg ((Unit ⊕ Unit) ⊕ VW b) =>
      yC q (w (Sum.inl (Sum.inl ()))) (w (Sum.inl (Sum.inr ()))) 0 0)
    N D.N_lt_pow_succ (ιEF_injective _ _) ιCin_injective
    (fun e a => ιEF_ne_ιCin _ _ e a) (Sum.inl (Sum.inl ())) ar hacc _
    (fun e => ιEF_ne_locBF _ _ e 1) (fun a h => locBF1_ne_ιCin a h.symm) _
    (ckdecD_padDataE D μ β q) ?_ ?_ ?_
  · intro w hg
    show ‖yC q (w (Sum.inl (Sum.inl ()))) (w (Sum.inl (Sum.inr ()))) 0 0‖ =
      ‖ckVal D.val μ β q w‖
    unfold ckVal yC
    rw [hg]
    cases w (Sum.inl (Sum.inr ())) <;> simp [NativeSignedFactor.norm_phase]
  · intro w hg
    show yC q (w (Sum.inl (Sum.inl ()))) (w (Sum.inl (Sum.inr ()))) 0 0 = 0
    rw [hg]
    simp [yC]
  · intro w hw
    change yC q (w (Sum.inl (Sum.inl ()))) (w (Sum.inl (Sum.inr ()))) 0 0 ≠ 0 at hw
    show Complex.arg (yC q (w (Sum.inl (Sum.inl ()))) (w (Sum.inl (Sum.inr ()))) 0 0) = 0
    revert hw
    cases w (Sum.inl (Sum.inl ())) <;> cases w (Sum.inl (Sum.inr ()))
    · intro hw
      exact absurd (by simp [yC]) hw
    · intro hw
      exact absurd (by simp [yC]) hw
    · intro hw
      exact absurd (by simp [yC]) hw
    · intro _
      have h1 : NativeSignedFactor.phase 0 = 1 := by simp [NativeSignedFactor.phase]
      simp only [yC, ↓reduceIte, h1, mul_one]
      exact Complex.arg_ofReal_of_nonneg (by linarith)

end Lifts

/-! ### The gates and work wires of a wrapper -/

/-- **The gates and work wires of a wrapper**: `flagLiftG` of a word arithmetic of cost
`c = |circ| + b_T + b_P + A` has at most `3c + 10k + 23` gates and work wires (at most
`2 (4(k + 1) + 2) + 2 |circ| + 4 + b_T + b_P` gates and `b_T + b_P + A + 2k + 7` work wires). -/
theorem wrap_cost_le {B I : Type*} [DecidableEq I] {k bT bP A : ℕ} (N : ℕ)
    (ιE : EW (k + 1) → B) (ιI : I → B) (gT : Option I) (ar : WordArith I bT bP A) :
    (ar.flagLiftG N ιE ιI gT).circ.length + bT + bP + (flagA k bT bP A + 1) ≤
      3 * (ar.circ.length + bT + bP + A) + 10 * k + 23 := by
  have h1 := ar.flagLiftG_length N ιE ιI gT
  have h2 := length_validC_le (k := k) N
  have h3 : flagA k bT bP A = bT + bP + A + (2 * k + 6) := by
    rw [flagA, card_FW]
  omega

end

end SparseHamiltonian.GeneralDecoder
