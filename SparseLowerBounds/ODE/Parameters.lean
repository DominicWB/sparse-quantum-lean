import SparseLowerBounds.ODE.Model

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Parameters of Theorem `odel:thm:joint`

Manuscript: Theorem `odel:thm:joint` and its proof: for `s ≥ 4`, `τ ≥ 4`, `ḡ ≥ 2`, `0 < ε ≤ 1/64`
(`JointRange`, Theorem `odel:thm:joint`) choose (proof of Theorem `odel:thm:joint`)

* `M = 2⌊ḡ²/2⌋` (`jointM`): even, `M ≥ 4`, `ḡ/√2 ≤ √M ≤ ḡ`;
* `m = 2^⌊log₂ s⌋` (`2 ^ jointMu s`): `4 ≤ m`, `s/2 < m ≤ s`;
* `n = ⌊2(τ - 1)/π⌋` (`jointN`): `n ≥ 1`, `n > τ/5`, and the hidden stages fit
  before the unit source stage, `n π/2 + 1 ≤ τ`.

The elementary bound `⌊x⌋ ≥ x/2` for `x ≥ 1` is
`Hamiltonian.half_le_floor`.
-/

namespace SparseLowerBounds.ODE

noncomputable section

/-- The parameter range of Theorem `odel:thm:joint`. -/
structure JointRange (s : ℕ) (τ gbar ε : ℝ) : Prop where
  s_ge : 4 ≤ s
  tau_ge : 4 ≤ τ
  gbar_ge : 2 ≤ gbar
  eps_pos : 0 < ε
  eps_le : ε ≤ 1 / 64

/-- `M = 2⌊ḡ²/2⌋` (proof of Theorem `odel:thm:joint`). -/
def jointM (gbar : ℝ) : ℕ := 2 * ⌊gbar ^ 2 / 2⌋₊

/-- `μ = ⌊log₂ s⌋`, so `m = 2^μ` (proof of Theorem `odel:thm:joint`). -/
def jointMu (s : ℕ) : ℕ := Nat.log 2 s

/-- `n = ⌊2(τ - 1)/π⌋` (proof of Theorem `odel:thm:joint`). -/
def jointN (τ : ℝ) : ℕ := ⌊2 * (τ - 1) / Real.pi⌋₊

variable {s : ℕ} {τ gbar : ℝ}

/-! ### `m = 2^μ` (proof of Theorem `odel:thm:joint`) -/

/-- `μ ≥ 1` once `s ≥ 2`. -/
theorem one_le_jointMu (hs : 2 ≤ s) : 1 ≤ jointMu s :=
  Nat.le_log_of_pow_le (by norm_num) (by simpa using hs)

/-- `μ ≥ 2`, i.e. `m = 2^μ ≥ 4`, once `s ≥ 4` (Section `odel:sec:main` and proof of Theorem
`odel:thm:joint`). -/
theorem two_le_jointMu (hs : 4 ≤ s) : 2 ≤ jointMu s :=
  Nat.le_log_of_pow_le (by norm_num) (by simpa using hs)

/-- `m = 2^μ ≤ s` (proof of Theorem `odel:thm:joint`). -/
theorem two_pow_jointMu_le (hs : 1 ≤ s) : 2 ^ jointMu s ≤ s :=
  Nat.pow_log_le_self 2 (by omega)

/-- `s < 2m`, i.e. `m > s/2` (proof of Theorem `odel:thm:joint`). -/
theorem lt_two_mul_two_pow_jointMu (s : ℕ) : s < 2 * 2 ^ jointMu s := by
  have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) s
  rw [Nat.succ_eq_add_one, pow_succ] at h
  unfold jointMu
  omega

/-- **The `m` of the Hamiltonian lower bound**: for `s ≥ 2`,
`μ = ⌊log₂ s⌋ = hsMu s + 1`, i.e. `m = 2 · hsM s` (`Hamiltonian.hsMu_add_one`).
The two bounds `m ≤ s < 2m` above are `Hamiltonian.two_pow_hsMu_succ_le` and
`Hamiltonian.lt_two_pow_hsMu_add_two` in this form; they are stated for
`Nat.log` directly (Mathlib one-liners) because `lt_two_mul_two_pow_jointMu`
needs no hypothesis `s ≥ 2`. -/
theorem jointMu_eq_hsMu_add_one (hs : 2 ≤ s) : jointMu s = Hamiltonian.hsMu s + 1 :=
  (Hamiltonian.hsMu_add_one hs).symm

/-- `s/2 < m` over `ℝ`. -/
theorem half_lt_two_pow_jointMu (s : ℕ) : (s : ℝ) / 2 < 2 ^ jointMu s := by
  have h : (s : ℝ) < 2 * 2 ^ jointMu s := by exact_mod_cast lt_two_mul_two_pow_jointMu s
  linarith

/-- `2 ≤ m = 2^μ` once `μ ≥ 1`. -/
theorem two_le_two_pow {μ : ℕ} (hμ : 1 ≤ μ) : 2 ≤ 2 ^ μ :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ μ := Nat.pow_le_pow_right (by norm_num) hμ

/-- `m = 2^μ` is even once `μ ≥ 1`. -/
theorem even_two_pow {μ : ℕ} (hμ : 1 ≤ μ) : Even (2 ^ μ) :=
  Nat.even_pow.mpr ⟨even_two, by omega⟩

/-! ### `n = ⌊2(τ-1)/π⌋` (proof of Theorem `odel:thm:joint`) -/

/-- The hidden stages and the unit source stage fit in `[0, τ]`. -/
theorem jointN_time (hτ : 1 ≤ τ) : (jointN τ : ℝ) * (Real.pi / 2) + 1 ≤ τ := by
  have hx : 0 ≤ 2 * (τ - 1) / Real.pi := div_nonneg (by linarith) Real.pi_pos.le
  have h := Nat.floor_le hx
  have h2 : (jointN τ : ℝ) * Real.pi ≤ 2 * (τ - 1) := (le_div_iff₀ Real.pi_pos).mp h
  nlinarith

/-- `n ≥ (τ - 1)/π` for `τ ≥ 4` (`⌊x⌋ ≥ x/2` for `x ≥ 1`). -/
theorem le_jointN (hτ : 4 ≤ τ) : (τ - 1) / Real.pi ≤ jointN τ := by
  have hx : 1 ≤ 2 * (τ - 1) / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    linarith [Real.pi_lt_four]
  have h := Hamiltonian.half_le_floor hx
  have he : 2 * (τ - 1) / Real.pi / 2 = (τ - 1) / Real.pi := by ring
  rw [he] at h
  exact h

/-- `n > τ/5` for `τ ≥ 4` (proof of Theorem `odel:thm:joint`): `n ≥ (τ-1)/π ≥ 3τ/(4π) > τ/5`. -/
theorem fifth_lt_jointN (hτ : 4 ≤ τ) : τ / 5 < jointN τ := by
  have h := le_jointN hτ
  have hlt : τ / 5 < (τ - 1) / Real.pi := by
    rw [lt_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_lt_d2]
  linarith

/-- `n ≥ 1` for `τ ≥ 4`. -/
theorem one_le_jointN (hτ : 4 ≤ τ) : 1 ≤ jointN τ := by
  have h := fifth_lt_jointN hτ
  have h0 : (0 : ℝ) < jointN τ := by linarith
  have : 0 < jointN τ := by exact_mod_cast h0
  omega

/-! ### `M = 2⌊ḡ²/2⌋` (proof of Theorem `odel:thm:joint`) -/

/-- `M` is even. -/
theorem even_jointM (gbar : ℝ) : Even (jointM gbar) := even_two_mul _

/-- `M ≥ 4` for `ḡ ≥ 2`. -/
theorem four_le_jointM (hg : 2 ≤ gbar) : 4 ≤ jointM gbar := by
  have h : 2 ≤ ⌊gbar ^ 2 / 2⌋₊ := Nat.le_floor (by push_cast; nlinarith [hg])
  unfold jointM
  omega

/-- `M ≤ ḡ²`. -/
theorem jointM_le (gbar : ℝ) : (jointM gbar : ℝ) ≤ gbar ^ 2 := by
  have h := Nat.floor_le (div_nonneg (sq_nonneg gbar) (by norm_num : (0 : ℝ) ≤ 2))
  unfold jointM
  push_cast
  linarith

/-- `M ≥ ḡ²/2` for `ḡ ≥ 2`. -/
theorem half_sq_le_jointM (hg : 2 ≤ gbar) : gbar ^ 2 / 2 ≤ jointM gbar := by
  have h := Hamiltonian.half_le_floor (x := gbar ^ 2 / 2) (by nlinarith)
  unfold jointM
  push_cast
  linarith

/-- `g = √M ≤ ḡ` (proof of Theorem `odel:thm:joint`). -/
theorem sqrt_jointM_le (hg : 0 ≤ gbar) : Real.sqrt (jointM gbar) ≤ gbar :=
  (Real.sqrt_le_left hg).mpr (jointM_le gbar)

/-- `g = √M ≥ ḡ/√2` for `ḡ ≥ 2` (proof of Theorem `odel:thm:joint`). -/
theorem div_sqrt_two_le_sqrt_jointM (hg : 2 ≤ gbar) :
    gbar / Real.sqrt 2 ≤ Real.sqrt (jointM gbar) := by
  have h0 : 0 ≤ gbar / Real.sqrt 2 := div_nonneg (by linarith) (Real.sqrt_nonneg 2)
  rw [Real.le_sqrt h0 (Nat.cast_nonneg _), div_pow, Real.sq_sqrt (by norm_num)]
  exact half_sq_le_jointM hg

/-- `√(M m) ≥ ḡ √s / 2` for `ḡ ≥ 2` (`M ≥ ḡ²/2`, `m > s/2`). -/
theorem sqrt_jointM_mul_ge (hg : 2 ≤ gbar) :
    gbar * Real.sqrt s / 2 ≤ Real.sqrt ((jointM gbar : ℝ) * 2 ^ jointMu s) := by
  have hM := half_sq_le_jointM hg
  have hm := half_lt_two_pow_jointMu s
  have h0 : 0 ≤ gbar * Real.sqrt s / 2 :=
    div_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) (by norm_num)
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  rw [Real.le_sqrt h0 (by positivity), div_pow, mul_pow, Real.sq_sqrt hs]
  have h1 : gbar ^ 2 / 2 * ((s : ℝ) / 2) ≤ (jointM gbar : ℝ) * 2 ^ jointMu s :=
    mul_le_mul hM hm.le (by positivity) (Nat.cast_nonneg _)
  linarith

/-! ### The constant `c_J = 1/400` (proof of Theorem `odel:thm:joint`) -/

/-- `β = (2/3)(1 - 2ε) ≥ 31/48` for `ε ≤ 1/64`. -/
theorem corr_ge {ε : ℝ} (hε : ε ≤ 1 / 64) : 31 / 48 ≤ 2 / 3 * (1 - 2 * ε) := by
  linarith

/-- **The numeric chain of Theorem `odel:thm:joint`** (proof of Theorem `odel:thm:joint`): for
`τ ≥ 4`, `ḡ ≥ 2` and `β ≥ 31/48`, `ḡ √s τ / 400 ≤ β² n √(M m) / 16`, since
`n > τ/5`, `√(Mm) ≥ ḡ√s/2` and `(31/48)²/160 = 961/368640 ≥ 1/400`. -/
theorem joint_numeric (hτ : 4 ≤ τ) (hg : 2 ≤ gbar) {β : ℝ} (hβ : 31 / 48 ≤ β) :
    1 / 400 * gbar * Real.sqrt s * τ ≤
      β ^ 2 * jointN τ * Real.sqrt ((jointM gbar : ℝ) * 2 ^ jointMu s) / 16 := by
  have hn := (fifth_lt_jointN hτ).le
  have hr := sqrt_jointM_mul_ge (s := s) hg
  have hβ2 : (31 / 48 : ℝ) ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ (by norm_num) hβ 2
  have hg0 : 0 ≤ gbar := by linarith
  have hgs : 0 ≤ gbar * Real.sqrt s := mul_nonneg hg0 (Real.sqrt_nonneg _)
  have h1 : (31 / 48 : ℝ) ^ 2 * (τ / 5) ≤ β ^ 2 * jointN τ :=
    mul_le_mul hβ2 hn (by linarith) (sq_nonneg β)
  have h2 : (31 / 48 : ℝ) ^ 2 * (τ / 5) * (gbar * Real.sqrt s / 2) ≤
      β ^ 2 * jointN τ * Real.sqrt ((jointM gbar : ℝ) * 2 ^ jointMu s) :=
    mul_le_mul h1 hr (by linarith) (mul_nonneg (sq_nonneg β) (Nat.cast_nonneg _))
  have hX : 0 ≤ gbar * Real.sqrt s * τ := mul_nonneg hgs (by linarith)
  nlinarith

end

end SparseLowerBounds.ODE
end
