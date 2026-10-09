import GateEfficientBinary.Cordic.Semantics
import Mathlib.Algebra.BigOperators.Field

/-!
# The angle errors of the CORDIC program

The output words are binary fractions (`sum_rev_bits`): the `φ` word is the stage-1 angle
modulo `2^bP` in units of `2π / 2^bP`, and the `θ` word is twice the clamped stage-2 angle in
units of `π / 2^(bT+1)`.

* `phi_error`: for a nonzero entry `z = X + i Y`, the `φ` word is `arg z` modulo `2π` up to the
  CORDIC residual `α_(n-1)` and the rounding `n u₁ / 2` of the angle constants.
* `theta_error`: for every entry, the `θ` word is `2 arctan (κ |z|)` up to twice the residual,
  the rounding and the clamp, and the relative error `1/(2U) + α_(n-1)² / 2` of the stage-2
  input `x_n 2^S₂ / (U 2^T)` as an approximation of `κ |z|`, given that `U` rounds
  `g_n 2^S₂ / κ`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinary.Cordic

noncomputable section

/-- A word whose bit `j` (most significant first) is bit `m - 1 - j` of `f` is the binary
fraction of the number with bits `f`. -/
theorem sum_rev_bits (f : ℕ → Bool) (m : ℕ) (c : ℝ) :
    (∑ j : Fin m, if f (m - 1 - j) then c / 2 ^ (j.val + 1) else 0) =
      c * ((∑ i ∈ Finset.range m, if f i then 2 ^ i else 0 : ℕ) : ℝ) / 2 ^ m := by
  have h1 : (∑ j : Fin m, if f (m - 1 - j) then c / 2 ^ (j.val + 1) else 0) =
      ∑ i : Fin m, if f i then c / 2 ^ (m - i.val) else 0 := by
    apply Fintype.sum_equiv Fin.revPerm
    intro j
    simp only [Fin.revPerm_apply, Fin.val_rev]
    have h2 : m - 1 - j.val = m - (j.val + 1) := by omega
    have h3 : m - (m - (j.val + 1)) = j.val + 1 := by omega
    rw [h2, h3]
  rw [h1, Fin.sum_univ_eq_sum_range (fun i => if f i then c / 2 ^ (m - i) else 0) m]
  push_cast
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.1 hi
  split_ifs
  · rw [show (2 : ℝ) ^ m = 2 ^ (m - i) * 2 ^ i by rw [← pow_add]; congr 1; omega]
    field_simp
  · simp

/-- Clamping to `[0, 2^m)` costs at most one unit for targets in `[0, π/2)`. -/
theorem clamp_error (a : ℤ) (m : ℕ) (u h : ℝ) (hu : u = Real.pi / 2 ^ (m + 1)) (h0 : 0 ≤ h)
    (h1 : h < Real.pi / 2) : |(clampN a m : ℝ) * u - h| ≤ |a * u - h| + u := by
  have hu0 : 0 < u := by rw [hu]; positivity
  have htop : ((2 ^ m - 1 : ℕ) : ℝ) * u = Real.pi / 2 - u := by
    rw [Nat.cast_sub (Nat.one_le_two_pow), hu]
    push_cast
    field_simp
    ring
  unfold clampN
  by_cases ha : a < 0
  · rw [if_pos ha]
    have : (a : ℝ) * u < 0 := mul_neg_of_neg_of_pos (by exact_mod_cast ha) hu0
    rw [abs_of_nonpos (by push_cast; linarith), abs_of_neg (by linarith)]
    push_cast
    linarith
  · rw [if_neg ha]
    by_cases hb : a < 2 ^ m
    · rw [if_pos hb]
      have hc : ((a.toNat : ℕ) : ℝ) = (a : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (not_lt.1 ha)]
      rw [hc]
      linarith [abs_nonneg ((a : ℝ) * u - h)]
    · rw [if_neg hb, htop]
      have hau : Real.pi / 2 ≤ (a : ℝ) * u := by
        have : ((2 ^ m : ℤ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast not_lt.1 hb
        rw [hu]
        push_cast at this
        calc Real.pi / 2 = (2 : ℝ) ^ m * (Real.pi / 2 ^ (m + 1)) := by
              field_simp
              ring
          _ ≤ (a : ℝ) * (Real.pi / 2 ^ (m + 1)) :=
              mul_le_mul_of_nonneg_right this (by positivity)
      rw [abs_le]
      constructor
      · rw [abs_of_nonneg (by linarith)]
        linarith
      · rw [abs_of_nonneg (by linarith)]
        linarith

variable {P : CParams}

/-- The entry `X + i Y` of the input bits. -/
def zIn (v : Fin P.b ⊕ Fin P.b → Bool) : ℂ := toC (inX v, inY v)

theorem toC_p1 (v : Fin P.b ⊕ Fin P.b → Bool) :
    toC (p1 v) = ((2 ^ P.T : ℝ) : ℂ) * (if inX v < 0 then -zIn v else zIn v) := by
  unfold p1 zIn toC
  split_ifs with h
  · rw [abs_of_neg h]
    push_cast
    ring
  · rw [abs_of_nonneg (not_lt.1 h)]
    push_cast
    ring

theorem norm_toC_p1 (v : Fin P.b ⊕ Fin P.b → Bool) : ‖toC (p1 v)‖ = 2 ^ P.T * ‖zIn v‖ := by
  rw [toC_p1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  split_ifs <;> simp

theorem toC_p1_ne_zero (v : Fin P.b ⊕ Fin P.b → Bool) (hz : zIn v ≠ 0) : toC (p1 v) ≠ 0 := by
  rw [toC_p1]
  apply mul_ne_zero (by exact_mod_cast (by positivity : (2 : ℝ) ^ P.T ≠ 0))
  split_ifs
  · exact neg_ne_zero.2 hz
  · exact hz

theorem re_toC_p1_nonneg (v : Fin P.b ⊕ Fin P.b → Bool) : 0 ≤ (toC (p1 v)).re := by
  rw [toC_re]
  simp only [p1]
  positivity

/-- **The `φ` error.** For a nonzero entry the `φ` word is `arg z` modulo `2π`, up to the
CORDIC residual and the rounding of the angle constants. -/
theorem phi_error (hP : P.OK) (v : Fin P.b ⊕ Fin P.b → Bool) (hz : zIn v ≠ 0)
    (hc1 : ∀ k, |(c1Z P k : ℝ) * (2 * Real.pi / 2 ^ P.bP) - alpha k| ≤
      (2 * Real.pi / 2 ^ P.bP) / 2) :
    ∃ m : ℤ, |(∑ j : Fin P.bP, if phiBits v j then 2 * Real.pi / 2 ^ (j.val + 1) else 0) -
      Complex.arg (zIn v) - 2 * Real.pi * m| ≤
        alpha (P.n - 1) + P.n * (2 * Real.pi / 2 ^ P.bP) / 2 := by
  set u1 : ℝ := 2 * Real.pi / 2 ^ P.bP with hu1
  have hsum := sum_rev_bits (regs P v (.a1 (ix P P.n))).getLsbD P.bP (2 * Real.pi)
  have hphi : (∑ j : Fin P.bP, if phiBits v j then 2 * Real.pi / 2 ^ (j.val + 1) else 0) =
      ((∑ i ∈ Finset.range P.bP, if (regs P v (.a1 (ix P P.n))).getLsbD i then 2 ^ i else 0 :
        ℕ) : ℝ) * u1 := by
    rw [show (fun j : Fin P.bP => if phiBits v j then 2 * Real.pi / 2 ^ (j.val + 1) else 0) =
      fun j : Fin P.bP => if (regs P v (.a1 (ix P P.n))).getLsbD (P.bP - 1 - j) then
        2 * Real.pi / 2 ^ (j.val + 1) else 0 from rfl, hsum, hu1]
    ring
  have hword := phi_word hP v
  set N := (∑ i ∈ Finset.range P.bP,
    if (regs P v (.a1 (ix P P.n))).getLsbD i then 2 ^ i else 0 : ℕ) with hN
  set Q := (a0 v + cacc (p1 v) (c1Z P) P.n) / 2 ^ P.bP with hQ
  have hNQ : (N : ℤ) = a0 v + cacc (p1 v) (c1Z P) P.n - 2 ^ P.bP * Q := by
    rw [hword, Int.emod_def]
  have hNr : (N : ℝ) * u1 = (a0 v : ℝ) * u1 + (cacc (p1 v) (c1Z P) P.n : ℝ) * u1 -
      2 * Real.pi * Q := by
    have : ((N : ℤ) : ℝ) = (a0 v : ℝ) + (cacc (p1 v) (c1Z P) P.n : ℝ) - 2 ^ P.bP * Q := by
      rw [hNQ]
      push_cast
      ring
    rw [show ((N : ℕ) : ℝ) = ((N : ℤ) : ℝ) by push_cast; rfl, this, hu1]
    field_simp
  obtain ⟨d1, d2⟩ := dvd_p1 (P := P) v
  have he := cacc_error (p1 v) P.n P.T hP.T d1 d2 (c1Z P) u1 hc1 P.n le_rfl
  obtain ⟨hconv, hres⟩ := converge (toC (p1 v)) (toC_p1_ne_zero v hz) (re_toC_p1_nonneg v) P.n
    hP.n2
  have harg : Complex.arg (toC (p1 v)) =
      Complex.arg (if inX v < 0 then -zIn v else zIn v) := by
    rw [toC_p1, Complex.arg_real_mul _ (by positivity)]
  have hpi : (2 : ℝ) ^ (P.bP - 1) * u1 = Real.pi := by
    rw [hu1]
    have h2 : (2 : ℝ) ^ P.bP = 2 ^ (P.bP - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      have := hP.bP1
      omega
    rw [h2]
    field_simp
  rw [hphi, hNr]
  by_cases hx : inX v < 0
  · rw [if_pos hx] at harg
    obtain ⟨m', hm'⟩ := arg_neg_eq (zIn v) hz
    refine ⟨1 + m' - Q, ?_⟩
    have ha0 : (a0 v : ℝ) * u1 = Real.pi := by
      rw [a0, if_pos hx]
      push_cast
      exact hpi
    rw [ha0]
    have : (Real.pi + (cacc (p1 v) (c1Z P) P.n : ℝ) * u1 - 2 * Real.pi * Q) -
        Complex.arg (zIn v) - 2 * Real.pi * ((1 + m' - Q : ℤ) : ℝ) =
        ((cacc (p1 v) (c1Z P) P.n : ℝ) * u1 - acc (toC (p1 v)) P.n) -
          Complex.arg (iter (toC (p1 v)) P.n) := by
      push_cast
      rw [hconv] at harg
      rw [hm'] at harg
      linarith
    rw [this]
    calc |((cacc (p1 v) (c1Z P) P.n : ℝ) * u1 - acc (toC (p1 v)) P.n) -
          Complex.arg (iter (toC (p1 v)) P.n)|
        ≤ |(cacc (p1 v) (c1Z P) P.n : ℝ) * u1 - acc (toC (p1 v)) P.n| +
          |Complex.arg (iter (toC (p1 v)) P.n)| := abs_sub _ _
      _ ≤ P.n * u1 / 2 + alpha (P.n - 1) := add_le_add he hres
      _ = alpha (P.n - 1) + P.n * u1 / 2 := by ring
  · rw [if_neg hx] at harg
    refine ⟨-Q, ?_⟩
    have ha0 : (a0 v : ℝ) * u1 = 0 := by
      rw [a0, if_neg hx]
      simp
    rw [ha0]
    have : (0 + (cacc (p1 v) (c1Z P) P.n : ℝ) * u1 - 2 * Real.pi * Q) -
        Complex.arg (zIn v) - 2 * Real.pi * ((-Q : ℤ) : ℝ) =
        ((cacc (p1 v) (c1Z P) P.n : ℝ) * u1 - acc (toC (p1 v)) P.n) -
          Complex.arg (iter (toC (p1 v)) P.n) := by
      push_cast
      rw [hconv] at harg
      linarith
    rw [this]
    calc |((cacc (p1 v) (c1Z P) P.n : ℝ) * u1 - acc (toC (p1 v)) P.n) -
          Complex.arg (iter (toC (p1 v)) P.n)|
        ≤ |(cacc (p1 v) (c1Z P) P.n : ℝ) * u1 - acc (toC (p1 v)) P.n| +
          |Complex.arg (iter (toC (p1 v)) P.n)| := abs_sub _ _
      _ ≤ P.n * u1 / 2 + alpha (P.n - 1) := add_le_add he hres
      _ = alpha (P.n - 1) + P.n * u1 / 2 := by ring

theorem citer_zero_point (k : ℕ) : citer (0, 0) k = (0, 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [citer_succ, ih]
      simp [cstep]

theorem p1_eq_zero (v : Fin P.b ⊕ Fin P.b → Bool) (hz : zIn v = 0) : p1 v = (0, 0) := by
  have h1 : inX v = 0 := by
    have := congrArg Complex.re hz
    simpa [zIn, toC_re] using this
  have h2 : inY v = 0 := by
    have := congrArg Complex.im hz
    simpa [zIn, toC_im] using this
  simp [p1, h1, h2]

/-- The stage-2 input ratio: the argument of the initial stage-2 point. -/
theorem arg_toC_p2 (hP : P.OK) (v : Fin P.b ⊕ Fin P.b → Bool) :
    Complex.arg (toC (p2 v)) = Real.arctan ((xOut v : ℝ) * 2 ^ P.S2 / (P.U * 2 ^ P.T)) := by
  have hU : (0 : ℝ) < P.U * 2 ^ P.T := by
    have := hP.U1
    positivity
  have h := arg_ofReal_add_mul_I ((P.U : ℝ) * 2 ^ P.T) ((xOut v : ℝ) * 2 ^ P.S2) hU
  rw [← h]
  congr 1
  simp only [toC, p2]
  push_cast
  ring

/-- **The `θ` error.** For every entry the `θ` word is `2 arctan (κ |z|)` up to twice the
residual, the rounding of the angle constants, the relative error of the stage-2 input and
the clamp. -/
theorem theta_error (hP : P.OK) (v : Fin P.b ⊕ Fin P.b → Bool) (κ : ℝ) (hκ : 0 < κ)
    (hc2 : ∀ k, |(c2Z P k : ℝ) * (Real.pi / 2 ^ (P.bT + 1)) - alpha k| ≤
      (Real.pi / 2 ^ (P.bT + 1)) / 2)
    (hU : |(P.U : ℝ) - gain P.n * 2 ^ P.S2 / κ| ≤ 1 / 2) (hU2 : (2 : ℝ) ≤ P.U) :
    |(∑ j : Fin P.bT, if thetaBits v j then Real.pi / 2 ^ (j.val + 1) else 0) -
      2 * Real.arctan (κ * ‖zIn v‖)| ≤
        2 * (alpha (P.n - 1) + P.n * (Real.pi / 2 ^ (P.bT + 1)) / 2 +
          (1 / (2 * P.U) + alpha (P.n - 1) ^ 2 / 2) + Real.pi / 2 ^ (P.bT + 1)) := by
  set u2 : ℝ := Real.pi / 2 ^ (P.bT + 1) with hu2
  set r := ‖zIn v‖ with hr
  set hs := Real.arctan (κ * r) with hhs
  have hs0 : 0 ≤ hs := Real.arctan_nonneg.2 (by positivity)
  have hs1 : hs < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  -- the word as a clamped angle
  have hsum := sum_rev_bits (tBit v) P.bT Real.pi
  have hword : (∑ j : Fin P.bT, if thetaBits v j then Real.pi / 2 ^ (j.val + 1) else 0) =
      2 * ((clampN (ang2 v) P.bT : ℝ) * u2) := by
    rw [show (fun j : Fin P.bT => if thetaBits v j then Real.pi / 2 ^ (j.val + 1) else 0) =
      fun j : Fin P.bT => if tBit v (P.bT - 1 - j) then Real.pi / 2 ^ (j.val + 1) else 0
      from rfl, hsum, theta_word hP v, hu2, pow_succ]
    field_simp
  rw [hword, show 2 * ((clampN (ang2 v) P.bT : ℝ) * u2) - 2 * hs =
    2 * ((clampN (ang2 v) P.bT : ℝ) * u2 - hs) by ring, abs_mul, abs_two]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  refine (clamp_error (ang2 v) P.bT u2 hs hu2 hs0 hs1).trans ?_
  refine add_le_add ?_ le_rfl
  -- the stage-2 angle
  obtain ⟨d1, d2⟩ := dvd_p2 hP v
  have he := cacc_error (p2 v) P.n P.T hP.T d1 d2 (c2Z P) u2 hc2 P.n le_rfl
  have hp2 : toC (p2 v) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [toC_re] at this
    simp only [p2, Complex.zero_re] at this
    have hU1 := hP.U1
    have : (P.U : ℤ) * 2 ^ P.T ≠ 0 := by positivity
    exact this (by exact_mod_cast ‹((P.U * 2 ^ P.T : ℤ) : ℝ) = 0›)
  have hre2 : 0 ≤ (toC (p2 v)).re := by
    rw [toC_re]
    simp only [p2]
    positivity
  obtain ⟨hconv, hres⟩ := converge (toC (p2 v)) hp2 hre2 P.n hP.n2
  rw [arg_toC_p2 hP v] at hconv
  -- the relative error of the stage-2 input
  have hrho : |Real.arctan ((xOut v : ℝ) * 2 ^ P.S2 / (P.U * 2 ^ P.T)) - hs| ≤
      1 / (2 * P.U) + alpha (P.n - 1) ^ 2 / 2 := by
    by_cases hz : zIn v = 0
    · have hx : xOut v = 0 := by
        rw [xOut, p1_eq_zero v hz, citer_zero_point]
      rw [hx, hhs, hr, hz]
      simp only [Int.cast_zero, zero_mul, zero_div, Real.arctan_zero, norm_zero, mul_zero,
        sub_self, abs_zero]
      positivity
    · obtain ⟨d1', d2'⟩ := dvd_p1 (P := P) v
      have hfst := citer_fst (p1 v) P.n P.T hP.T d1' d2'
      obtain ⟨_, hres1⟩ := converge (toC (p1 v)) (toC_p1_ne_zero v hz) (re_toC_p1_nonneg v)
        P.n hP.n2
      set ψ := Complex.arg (iter (toC (p1 v)) P.n) with hψ
      set Ue := gain P.n * 2 ^ P.S2 / κ with hUe
      have hUpos : (0 : ℝ) < P.U := by linarith
      set ρ := Ue / P.U * Real.cos ψ - 1 with hρ
      have hratio : (xOut v : ℝ) * 2 ^ P.S2 / (P.U * 2 ^ P.T) = (1 + ρ) * (κ * r) := by
        rw [xOut, hfst, norm_toC_p1, hρ, hUe]
        field_simp
        ring
      have hcos1 : 1 - Real.cos ψ ≤ alpha (P.n - 1) ^ 2 / 2 := by
        have h1 := Real.one_sub_sq_div_two_le_cos (x := ψ)
        have h2 : ψ ^ 2 ≤ alpha (P.n - 1) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hres1 2
        linarith
      have hcos2 : Real.cos ψ ≤ 1 := Real.cos_le_one ψ
      have hcos0 : 0 ≤ Real.cos ψ := by
        apply Real.cos_nonneg_of_mem_Icc
        have := alpha_le_pi_div_four (P.n - 1)
        constructor <;> linarith [abs_le.1 hres1]
      have hq : |Ue / P.U - 1| ≤ 1 / (2 * P.U) := by
        rw [show Ue / P.U - 1 = (Ue - P.U) / P.U by field_simp, abs_div,
          abs_of_pos hUpos, abs_sub_comm]
        rw [div_le_div_iff₀ hUpos (by positivity)]
        nlinarith
      have hρb : |ρ| ≤ 1 / (2 * P.U) + alpha (P.n - 1) ^ 2 / 2 := by
        have : ρ = (Ue / P.U - 1) * Real.cos ψ + (Real.cos ψ - 1) := by rw [hρ]; ring
        rw [this]
        calc |(Ue / P.U - 1) * Real.cos ψ + (Real.cos ψ - 1)|
            ≤ |(Ue / P.U - 1) * Real.cos ψ| + |Real.cos ψ - 1| := abs_add_le _ _
          _ ≤ |Ue / P.U - 1| + (1 - Real.cos ψ) := by
              rw [abs_mul, abs_of_nonneg hcos0,
                abs_of_nonpos (show Real.cos ψ - 1 ≤ 0 by linarith)]
              nlinarith [abs_nonneg (Ue / P.U - 1)]
          _ ≤ 1 / (2 * P.U) + alpha (P.n - 1) ^ 2 / 2 := add_le_add hq hcos1
      have hρhalf : |ρ| ≤ 1 / 2 := by
        have h1 : 1 / (2 * (P.U : ℝ)) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
        have h2 : alpha (P.n - 1) ≤ 1 / 2 := by
          have := alpha_le (P.n - 1)
          have h3 : (1 / 2 : ℝ) ^ (P.n - 1) ≤ 1 / 2 := by
            have := hP.n2
            calc (1 / 2 : ℝ) ^ (P.n - 1) ≤ (1 / 2) ^ 1 :=
                  pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
              _ = 1 / 2 := by norm_num
          linarith
        have h4 : alpha (P.n - 1) ^ 2 / 2 ≤ 1 / 8 := by
          have := alpha_nonneg (P.n - 1)
          nlinarith
        linarith
      rw [hratio]
      exact (abs_arctan_sub_le (κ * r) ρ (by positivity) hρhalf).trans hρb
  calc |(ang2 v : ℝ) * u2 - hs|
      = |((cacc (p2 v) (c2Z P) P.n : ℝ) * u2 - acc (toC (p2 v)) P.n) -
          Complex.arg (iter (toC (p2 v)) P.n) +
          (Real.arctan ((xOut v : ℝ) * 2 ^ P.S2 / (P.U * 2 ^ P.T)) - hs)| := by
        congr 1
        rw [ang2]
        linarith
    _ ≤ |(cacc (p2 v) (c2Z P) P.n : ℝ) * u2 - acc (toC (p2 v)) P.n| +
          |Complex.arg (iter (toC (p2 v)) P.n)| +
          |Real.arctan ((xOut v : ℝ) * 2 ^ P.S2 / (P.U * 2 ^ P.T)) - hs| := by
        refine (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ P.n * u2 / 2 + alpha (P.n - 1) + (1 / (2 * P.U) + alpha (P.n - 1) ^ 2 / 2) :=
        add_le_add (add_le_add he hres) hrho
    _ = alpha (P.n - 1) + P.n * u2 / 2 + (1 / (2 * P.U) + alpha (P.n - 1) ^ 2 / 2) := by ring

end

end SparseHamiltonian.GateBinary.Cordic
