import OptimalPrecision.Weights.Operator

/-!
# The dual evaluation on rational functions of `x = -∂`

In the exact moment construction of Theorem `opt:thm:weights`, every inverse
operator is a rational function of `x = 1 - D` (the operator `-∂` on
exponential polynomials), and the extraction rule becomes a linear functional
`L` on `ℂ⟦X⟧`. This file proves, for an arbitrary linear functional `L` with

* `L(x^{-2}) = 1`, `L(x^{-1}) = 0` (equal masses, mean difference),
* `L(x^j) = 0` for `0 ≤ j < d₀` (vanishing of the extraction function at the delay),
* `L((x ∓ c)^{-b}) = 0` for `1 ≤ b ≤ M` (oscillator moments),

that `L(x^{-2} (x-c)^{-b} (x+c)^{-e}) = (-c)^{-b} c^{-e}` and that
`L(x^a (x-c)^{-b} (x+c)^{-e}) = 0` for `-1 ≤ a < d₀` and `b, e ≤ M`. These are
the partial-fraction identities behind `opt:eq:dual-pairing`; they are proved
by the resolvent identities `x^{-1}(x-c)^{-1} = c^{-1}((x-c)^{-1} - x^{-1})` etc.
-/

namespace OptimalPrecision.Resolvent

noncomputable section

open PowerSeries

/-- `x = 1 - X`, the operator `-∂` on exponential polynomials. -/
abbrev u : PowerSeries ℂ := ExpPoly.xs

/-- `x - c`. -/
def v (c : ℂ) : PowerSeries ℂ := u - C c

/-- `x + c`. -/
def v' (c : ℂ) : PowerSeries ℂ := u + C c

theorem constantCoeff_u : constantCoeff u = 1 := ExpPoly.constantCoeff_xs

theorem constantCoeff_v (c : ℂ) : constantCoeff (v c) = 1 - c := by
  rw [v, map_sub, constantCoeff_u, constantCoeff_C]

theorem constantCoeff_v' (c : ℂ) : constantCoeff (v' c) = 1 + c := by
  rw [v', map_add, constantCoeff_u, constantCoeff_C]

theorem u_mul_inv : u * u⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel u (by rw [constantCoeff_u]; exact one_ne_zero)

variable {c : ℂ}

theorem v_mul_inv (hc : 1 - c ≠ 0) : v c * (v c)⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel (v c) (by rw [constantCoeff_v]; exact hc)

theorem v'_mul_inv (hc : 1 + c ≠ 0) : v' c * (v' c)⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel (v' c) (by rw [constantCoeff_v']; exact hc)

/-- `x^{-1}(x-c)^{-1} = c^{-1}((x-c)^{-1} - x^{-1})`. -/
theorem ui_mul_vi (hc0 : c ≠ 0) (hc : 1 - c ≠ 0) :
    u⁻¹ * (v c)⁻¹ = C c⁻¹ * ((v c)⁻¹ - u⁻¹) := by
  have h1 := u_mul_inv
  have h2 := v_mul_inv hc
  have hcc : C c * C c⁻¹ = (1 : PowerSeries ℂ) := by rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
  have huv : u = v c + C c := by simp [v]
  calc u⁻¹ * (v c)⁻¹ = (C c * C c⁻¹) * (u⁻¹ * (v c)⁻¹) := by rw [hcc, one_mul]
    _ = C c⁻¹ * ((u - v c) * (u⁻¹ * (v c)⁻¹)) := by
        rw [show u - v c = C c by rw [huv]; ring]; ring
    _ = C c⁻¹ * ((u * u⁻¹) * (v c)⁻¹ - (v c * (v c)⁻¹) * u⁻¹) := by ring
    _ = C c⁻¹ * ((v c)⁻¹ - u⁻¹) := by rw [h1, h2]; ring

/-- `x^{-1}(x+c)^{-1} = (-c)^{-1}((x+c)^{-1} - x^{-1})`. -/
theorem ui_mul_wi (hc0 : c ≠ 0) (hc : 1 + c ≠ 0) :
    u⁻¹ * (v' c)⁻¹ = C (-c)⁻¹ * ((v' c)⁻¹ - u⁻¹) := by
  have h1 := u_mul_inv
  have h2 := v'_mul_inv hc
  have hc' : -c ≠ 0 := neg_ne_zero.mpr hc0
  have hcc : C (-c) * C (-c)⁻¹ = (1 : PowerSeries ℂ) := by
    rw [← map_mul, mul_inv_cancel₀ hc', map_one]
  have huv : u = v' c - C c := by simp [v']
  calc u⁻¹ * (v' c)⁻¹ = (C (-c) * C (-c)⁻¹) * (u⁻¹ * (v' c)⁻¹) := by rw [hcc, one_mul]
    _ = C (-c)⁻¹ * ((u - v' c) * (u⁻¹ * (v' c)⁻¹)) := by
        rw [show u - v' c = C (-c) by rw [huv, map_neg]; ring]; ring
    _ = C (-c)⁻¹ * ((u * u⁻¹) * (v' c)⁻¹ - (v' c * (v' c)⁻¹) * u⁻¹) := by ring
    _ = C (-c)⁻¹ * ((v' c)⁻¹ - u⁻¹) := by rw [h1, h2]; ring

/-- `(x-c)^{-1}(x+c)^{-1} = (2c)^{-1}((x-c)^{-1} - (x+c)^{-1})`. -/
theorem vi_mul_wi (hc0 : c ≠ 0) (hc : 1 - c ≠ 0) (hc' : 1 + c ≠ 0) :
    (v c)⁻¹ * (v' c)⁻¹ = C (2 * c)⁻¹ * ((v c)⁻¹ - (v' c)⁻¹) := by
  have h1 := v_mul_inv hc
  have h2 := v'_mul_inv hc'
  have h2c : (2 : ℂ) * c ≠ 0 := mul_ne_zero two_ne_zero hc0
  have hcc : C (2 * c) * C (2 * c)⁻¹ = (1 : PowerSeries ℂ) := by
    rw [← map_mul, mul_inv_cancel₀ h2c, map_one]
  have hd : v' c - v c = C (2 * c) := by simp [v, v', map_mul, map_ofNat]; ring
  calc (v c)⁻¹ * (v' c)⁻¹ = (C (2 * c) * C (2 * c)⁻¹) * ((v c)⁻¹ * (v' c)⁻¹) := by
        rw [hcc, one_mul]
    _ = C (2 * c)⁻¹ * ((v' c - v c) * ((v c)⁻¹ * (v' c)⁻¹)) := by rw [hd]; ring
    _ = C (2 * c)⁻¹ * ((v' c * (v' c)⁻¹) * (v c)⁻¹ - (v c * (v c)⁻¹) * (v' c)⁻¹) := by ring
    _ = C (2 * c)⁻¹ * ((v c)⁻¹ - (v' c)⁻¹) := by rw [h1, h2]; ring

/-- `x (x-c)^{-1} = 1 + c (x-c)^{-1}`. -/
theorem u_mul_vi (hc : 1 - c ≠ 0) : u * (v c)⁻¹ = 1 + C c * (v c)⁻¹ := by
  have h := v_mul_inv hc
  have huv : u = v c + C c := by simp [v]
  rw [huv, add_mul, h]

/-- `x (x+c)^{-1} = 1 - c (x+c)^{-1}`. -/
theorem u_mul_wi (hc : 1 + c ≠ 0) : u * (v' c)⁻¹ = 1 - C c * (v' c)⁻¹ := by
  have h := v'_mul_inv hc
  have huv : u = v' c - C c := by simp [v']
  rw [huv, sub_mul, h]

/-! ### The dual evaluation -/

section Dual

variable (L : PowerSeries ℂ →ₗ[ℂ] ℂ) (c : ℂ) (M d₀ : ℕ)

/-- The hypotheses on the dual evaluation. -/
structure Hyp : Prop where
  c_ne : c ≠ 0
  one_sub_ne : 1 - c ≠ 0
  one_add_ne : 1 + c ≠ 0
  ui_sq : L (u⁻¹ ^ 2) = 1
  ui : L u⁻¹ = 0
  u_pow : ∀ j, j < d₀ → L (u ^ j) = 0
  vi_pow : ∀ b, 1 ≤ b → b ≤ M → L ((v c)⁻¹ ^ b) = 0
  wi_pow : ∀ e, 1 ≤ e → e ≤ M → L ((v' c)⁻¹ ^ e) = 0

variable {L c M d₀}

/-- `a = 0`. -/
theorem vanish_zero (h : Hyp L c M d₀) (hd₀ : 0 < d₀) :
    ∀ n b e, b + e = n → b ≤ M → e ≤ M → L ((v c)⁻¹ ^ b * (v' c)⁻¹ ^ e) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b e hn hb he
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · rcases Nat.eq_zero_or_pos e with rfl | he0
      · simpa using h.u_pow 0 hd₀
      · simpa using h.wi_pow e he0 he
    · rcases Nat.eq_zero_or_pos e with rfl | he0
      · simpa using h.vi_pow b hb0 hb
      · obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb0.ne'
        obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he0.ne'
        have key : (v c)⁻¹ ^ (b' + 1) * (v' c)⁻¹ ^ (e' + 1) =
            C (2 * c)⁻¹ * ((v c)⁻¹ ^ (b' + 1) * (v' c)⁻¹ ^ e' -
              (v c)⁻¹ ^ b' * (v' c)⁻¹ ^ (e' + 1)) := by
          have := vi_mul_wi h.c_ne h.one_sub_ne h.one_add_ne
          calc (v c)⁻¹ ^ (b' + 1) * (v' c)⁻¹ ^ (e' + 1) =
              (v c)⁻¹ ^ b' * (v' c)⁻¹ ^ e' * ((v c)⁻¹ * (v' c)⁻¹) := by ring
            _ = _ := by rw [this]; ring
        rw [key, ← PowerSeries.smul_eq_C_mul, map_smul, map_sub,
          ih (b' + 1 + e') (by omega) (b' + 1) e' rfl hb (by omega),
          ih (b' + (e' + 1)) (by omega) b' (e' + 1) rfl (by omega) he, sub_zero, smul_zero]

/-- `0 ≤ a < d₀`: the polynomial and pole parts both vanish. -/
theorem vanish_nonneg (h : Hyp L c M d₀) :
    ∀ a b e, a < d₀ → b ≤ M → e ≤ M → L (u ^ a * (v c)⁻¹ ^ b * (v' c)⁻¹ ^ e) = 0 := by
  intro a
  induction a with
  | zero =>
    intro b e ha hb he
    simpa using vanish_zero h ha (b + e) b e rfl hb he
  | succ a ih =>
    intro b e ha hb he
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · rcases Nat.eq_zero_or_pos e with rfl | he0
      · simpa using h.u_pow (a + 1) ha
      · obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he0.ne'
        have key : u ^ (a + 1) * (v c)⁻¹ ^ 0 * (v' c)⁻¹ ^ (e' + 1) =
            u ^ a * (v c)⁻¹ ^ 0 * (v' c)⁻¹ ^ e' -
              C c * (u ^ a * (v c)⁻¹ ^ 0 * (v' c)⁻¹ ^ (e' + 1)) := by
          have := u_mul_wi h.one_add_ne
          calc u ^ (a + 1) * (v c)⁻¹ ^ 0 * (v' c)⁻¹ ^ (e' + 1) =
              u ^ a * (v' c)⁻¹ ^ e' * (u * (v' c)⁻¹) := by ring
            _ = _ := by rw [this]; ring
        rw [key, map_sub, ← PowerSeries.smul_eq_C_mul, map_smul,
          ih 0 e' (by omega) (by omega) (by omega), ih 0 (e' + 1) (by omega) (by omega) he,
          smul_zero, sub_zero]
    · obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb0.ne'
      have key : u ^ (a + 1) * (v c)⁻¹ ^ (b' + 1) * (v' c)⁻¹ ^ e =
          u ^ a * (v c)⁻¹ ^ b' * (v' c)⁻¹ ^ e +
            C c * (u ^ a * (v c)⁻¹ ^ (b' + 1) * (v' c)⁻¹ ^ e) := by
        have := u_mul_vi h.one_sub_ne
        calc u ^ (a + 1) * (v c)⁻¹ ^ (b' + 1) * (v' c)⁻¹ ^ e =
            u ^ a * (v c)⁻¹ ^ b' * (v' c)⁻¹ ^ e * (u * (v c)⁻¹) := by ring
          _ = _ := by rw [this]; ring
      rw [key, map_add, ← PowerSeries.smul_eq_C_mul, map_smul,
        ih b' e (by omega) (by omega) he, ih (b' + 1) e (by omega) hb he, smul_zero, add_zero]

/-- `a = -1`. -/
theorem vanish_neg_one (h : Hyp L c M d₀) (hd₀ : 0 < d₀) :
    ∀ n b e, b + e = n → b ≤ M → e ≤ M → L (u⁻¹ * (v c)⁻¹ ^ b * (v' c)⁻¹ ^ e) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b e hn hb he
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · rcases Nat.eq_zero_or_pos e with rfl | he0
      · simpa using h.ui
      · obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he0.ne'
        have key : u⁻¹ * (v c)⁻¹ ^ 0 * (v' c)⁻¹ ^ (e' + 1) =
            C (-c)⁻¹ * ((v c)⁻¹ ^ 0 * (v' c)⁻¹ ^ (e' + 1) - u⁻¹ * (v c)⁻¹ ^ 0 * (v' c)⁻¹ ^ e') := by
          have := ui_mul_wi h.c_ne h.one_add_ne
          calc u⁻¹ * (v c)⁻¹ ^ 0 * (v' c)⁻¹ ^ (e' + 1) =
              (v' c)⁻¹ ^ e' * (u⁻¹ * (v' c)⁻¹) := by ring
            _ = _ := by rw [this]; ring
        rw [key, ← PowerSeries.smul_eq_C_mul, map_smul, map_sub,
          vanish_zero h hd₀ (0 + (e' + 1)) 0 (e' + 1) rfl (by omega) he,
          ih (0 + e') (by omega) 0 e' rfl (by omega) (by omega), sub_zero, smul_zero]
    · obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb0.ne'
      have key : u⁻¹ * (v c)⁻¹ ^ (b' + 1) * (v' c)⁻¹ ^ e =
          C c⁻¹ * ((v c)⁻¹ ^ (b' + 1) * (v' c)⁻¹ ^ e - u⁻¹ * (v c)⁻¹ ^ b' * (v' c)⁻¹ ^ e) := by
        have := ui_mul_vi h.c_ne h.one_sub_ne
        calc u⁻¹ * (v c)⁻¹ ^ (b' + 1) * (v' c)⁻¹ ^ e =
            (v c)⁻¹ ^ b' * (v' c)⁻¹ ^ e * (u⁻¹ * (v c)⁻¹) := by ring
          _ = _ := by rw [this]; ring
      rw [key, ← PowerSeries.smul_eq_C_mul, map_smul, map_sub,
        vanish_zero h hd₀ ((b' + 1) + e) (b' + 1) e rfl hb he,
        ih (b' + e) (by omega) b' e rfl (by omega) he, sub_zero, smul_zero]

/-- `a = -2`: the extracted value `(-c)^{-b} c^{-e}`. -/
theorem value_neg_two (h : Hyp L c M d₀) (hd₀ : 0 < d₀) :
    ∀ n b e, b + e = n → b ≤ M → e ≤ M →
      L (u⁻¹ ^ 2 * (v c)⁻¹ ^ b * (v' c)⁻¹ ^ e) = (-c)⁻¹ ^ b * c⁻¹ ^ e := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b e hn hb he
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · rcases Nat.eq_zero_or_pos e with rfl | he0
      · simpa using h.ui_sq
      · obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he0.ne'
        have key : u⁻¹ ^ 2 * (v c)⁻¹ ^ 0 * (v' c)⁻¹ ^ (e' + 1) =
            C (-c)⁻¹ * (u⁻¹ * (v c)⁻¹ ^ 0 * (v' c)⁻¹ ^ (e' + 1) -
              u⁻¹ ^ 2 * (v c)⁻¹ ^ 0 * (v' c)⁻¹ ^ e') := by
          have := ui_mul_wi h.c_ne h.one_add_ne
          calc u⁻¹ ^ 2 * (v c)⁻¹ ^ 0 * (v' c)⁻¹ ^ (e' + 1) =
              u⁻¹ * (v' c)⁻¹ ^ e' * (u⁻¹ * (v' c)⁻¹) := by ring
            _ = _ := by rw [this]; ring
        rw [key, ← PowerSeries.smul_eq_C_mul, map_smul, map_sub,
          vanish_neg_one h hd₀ (0 + (e' + 1)) 0 (e' + 1) rfl (by omega) he,
          ih (0 + e') (by omega) 0 e' rfl (by omega) (by omega), smul_eq_mul]
        simp only [← neg_inv, Nat.succ_eq_add_one]
        ring
    · obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb0.ne'
      have key : u⁻¹ ^ 2 * (v c)⁻¹ ^ (b' + 1) * (v' c)⁻¹ ^ e =
          C c⁻¹ * (u⁻¹ * (v c)⁻¹ ^ (b' + 1) * (v' c)⁻¹ ^ e -
            u⁻¹ ^ 2 * (v c)⁻¹ ^ b' * (v' c)⁻¹ ^ e) := by
        have := ui_mul_vi h.c_ne h.one_sub_ne
        calc u⁻¹ ^ 2 * (v c)⁻¹ ^ (b' + 1) * (v' c)⁻¹ ^ e =
            u⁻¹ * (v c)⁻¹ ^ b' * (v' c)⁻¹ ^ e * (u⁻¹ * (v c)⁻¹) := by ring
          _ = _ := by rw [this]; ring
      rw [key, ← PowerSeries.smul_eq_C_mul, map_smul, map_sub,
        vanish_neg_one h hd₀ ((b' + 1) + e) (b' + 1) e rfl hb he,
        ih (b' + e) (by omega) b' e rfl (by omega) he, smul_eq_mul]
      simp only [← neg_inv, Nat.succ_eq_add_one]
      ring

end Dual

end

end OptimalPrecision.Resolvent
