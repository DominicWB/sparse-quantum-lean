import SparseLowerBounds.ODE.JointTheorem

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

/-!
# Remark `odel:rem:homogeneous`: parameters and numerics

Manuscript lines 3907-3952 (Remark `odel:rem:homogeneous`, "A homogeneous variant"). The
source of the joint family of Theorem `odel:thm:joint` (lines 3860-3905) is removed when
`τ ≥ 20(1 + log ḡ)`. The parameters are `M = jointM ḡ = 2⌊ḡ²/2⌋`, `m = 2^{jointMu s}` as in
Theorem `odel:thm:joint` (`SparseLowerBounds.ODE.Parameters`), `n = ⌊τ/π⌋` (`homN`) and the
dissipation time `d = log(4√M)` (`homD`).

**Known stages** (`ODELowerBoundExtensions.Homogeneous.Defs`): after the `n` hidden stages of
length `π/2`, one phase pulse `-|1⟩⟨1|` of length `((n+2) mod 4)·π/2` (`pulseLen`; it merges
the paper's phase pulse of length `(n mod 4)π/2` with its `Z` pulse of length `π/2`, which is
`-|1⟩⟨1|` for time `π` up to the global phase `-i`), the `Y` pulse of length `π/4`, the
dissipation `-P_reject` of length `d`, and a known idle stage up to `T = τ`. The busy time is
`homBusy M n = nπ/2 + pulseLen n + π/4 + d`.

**Why the pulses are merged (a formalization choice).** We merge the paper's phase pulse with
its `Z` pulse (`e^{-iπZ/2} = -i e^{iπ|1⟩⟨1|}`, the same unitary up to the global phase `-i`).
This keeps the uniform decode `homPhase · wordDecode` of
`ODELowerBoundExtensions.Homogeneous.Table` (the real-word decode of `jointData` times one
fixed unit phase per address) and a single unit word on every known-stage address: with that
decode the flag-zero diagonal address, which carries `+1` for `P_reject`, cannot also carry the
`Z` entry `±i`. The literal three-pulse family is also realisable in
`NativeSparseBlockEncoding.Data`, whose `decode` is an arbitrary bounded map per address, by a
decode that sends a second known word to `i` at the flag-zero diagonal addresses (not
constructed here); it would only put a factor `-i` on `homEnd`. With the `Y` pulse the merged pulse gives exactly the Hadamard (no global phase), so
the family is the paper's up to the global phase `-i` of the final state: normalised targets
and readout correlations are unchanged. The known pulses take at most `7π/4 ≤ 9π/4`, so the
paper's time budget holds.

**Numerics** (lines 3939-3947): `nπ/2 ≤ τ/2`, the known stages take at most
`7π/4 + log 4 + log ḡ < 10(1 + log ḡ) ≤ τ/2` (`homN_time`), and `n ≥ τ/π - 1 ≥ τ/5`
(`fifth_le_homN`). The decision correlation is `β = (2/3)(15/17 - 2ε)` (`homCorr`: the
paper's success probability `(2/3)(16/17 - ε) + 1/6` is `(1 + β)/2`), `β ≥ 463/816` for
`ε ≤ 1/64`, and with `√(Mm) ≥ ḡ√s/2` (`sqrt_jointM_mul_ge`) the explicit constant of the
remark's eq. `odel:eq:joint` is `c_H = 1/500` (`hom_numeric`).
-/

namespace ODELowerBoundExtensions.Homogeneous

noncomputable section
open SparseLowerBounds.ODE

/-- **The parameter range of Remark `odel:rem:homogeneous`** (lines 3907-3908 with the range
of Theorem `odel:thm:joint`, lines 3861-3862): `s ≥ 4`, `ḡ ≥ 2`, `τ ≥ 20(1 + log ḡ)` and
`0 < ε ≤ 1/64`. (`τ ≥ 20` follows, `twenty_le_tau`.) -/
structure HomRange (s : ℕ) (τ gbar ε : ℝ) : Prop where
  s_ge : 4 ≤ s
  gbar_ge : 2 ≤ gbar
  tau_ge : 20 * (1 + Real.log gbar) ≤ τ
  eps_pos : 0 < ε
  eps_le : ε ≤ 1 / 64

/-- The number of hidden stages `n = ⌊τ/π⌋` (line 3910). -/
def homN (τ : ℝ) : ℕ := ⌊τ / Real.pi⌋₊

/-- The length `((n+2) mod 4)·π/2` of the merged phase pulse `-|1⟩⟨1|` (lines 3911-3914:
the phase pulse of length `(n mod 4)π/2` followed by the `Z` pulse of length `π/2`, the
latter replaced by `-|1⟩⟨1|` for time `π`). -/
def pulseLen (n : ℕ) : ℝ := (((n + 2) % 4 : ℕ) : ℝ) * (Real.pi / 2)

/-- The dissipation time `d = log(4√M)` (line 3927). -/
def homD (M : ℕ) : ℝ := Real.log (4 * Real.sqrt M)

/-- The busy time `nπ/2 + pulseLen n + π/4 + d`: hidden stages, merged phase pulse, `Y` pulse
and dissipation; the remaining time up to `T` is a known idle stage (line 3946). -/
def homBusy (M n : ℕ) : ℝ := n * (Real.pi / 2) + pulseLen n + Real.pi / 4 + homD M

/-- The decision correlation `β = (2/3)(15/17 - 2ε)` (lines 3936-3937: success probability
`(2/3)(16/17 - ε) + 1/6 = (1 + β)/2`). -/
def homCorr (ε : ℝ) : ℝ := 2 / 3 * (15 / 17 - 2 * ε)

/-- The explicit constant `c_H = 1/500` of eq. `odel:eq:joint` for the homogeneous variant. -/
def homConst : ℝ := 1 / 500

/-- The merged pulse has nonnegative length. -/
theorem pulseLen_nonneg (n : ℕ) : 0 ≤ pulseLen n := by
  unfold pulseLen
  have hp := Real.pi_pos
  positivity

/-- The merged pulse lasts at most `3π/2`. -/
theorem pulseLen_le (n : ℕ) : pulseLen n ≤ 3 * Real.pi / 2 := by
  unfold pulseLen
  have h : (n + 2) % 4 ≤ 3 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by norm_num))
  have h' : (((n + 2) % 4 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast h
  have hp := Real.pi_pos
  nlinarith

/-- `d = log(4√M) ≥ 0` (`4√M` is `0` or at least `4`). -/
theorem homD_nonneg (M : ℕ) : 0 ≤ homD M := by
  unfold homD
  rcases Nat.eq_zero_or_pos M with h | h
  · subst h; simp
  · apply Real.log_nonneg
    have : (1 : ℝ) ≤ Real.sqrt M := by
      simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ M by exact_mod_cast h)
    linarith

/-- `e^{-d} = 1/(4√M)` for `M ≥ 1`. -/
theorem exp_neg_homD {M : ℕ} (hM : 1 ≤ M) : Real.exp (-homD M) = 1 / (4 * Real.sqrt M) := by
  unfold homD
  have hs : 0 < Real.sqrt M := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  rw [Real.exp_neg, Real.exp_log (by positivity), one_div]

/-- `d ≤ log 4 + log ḡ` at `M = jointM ḡ` (`√M ≤ ḡ`, line 3933; line 3943). -/
theorem homD_le {gbar : ℝ} (hg : 2 ≤ gbar) : homD (jointM gbar) ≤ Real.log 4 + Real.log gbar := by
  unfold homD
  have hM := four_le_jointM hg
  have hs : 0 < Real.sqrt (jointM gbar) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  rw [Real.log_mul (by norm_num) hs.ne']
  have := Real.log_le_log hs (sqrt_jointM_le (by linarith : (0 : ℝ) ≤ gbar))
  linarith

/-- `τ ≥ 20` on the range (`log ḡ ≥ 0`). -/
theorem twenty_le_tau {s : ℕ} {τ gbar ε : ℝ} (h : HomRange s τ gbar ε) : 20 ≤ τ := by
  have := Real.log_nonneg (by linarith [h.gbar_ge] : (1 : ℝ) ≤ gbar)
  linarith [h.tau_ge]

/-- **The time budget** (lines 3939-3945): `nπ/2 ≤ τ/2` and the known stages take at most
`7π/4 + log 4 + log ḡ < 10(1 + log ḡ) ≤ τ/2`, so the busy time fits in `[0, τ]`. -/
theorem homN_time {τ gbar : ℝ} (hg : 2 ≤ gbar) (hτ : 20 * (1 + Real.log gbar) ≤ τ) :
    homBusy (jointM gbar) (homN τ) ≤ τ := by
  have hlg := Real.log_nonneg (by linarith : (1 : ℝ) ≤ gbar)
  have hτ0 : 0 ≤ τ := by linarith
  have hp := Real.pi_pos
  have hn : (homN τ : ℝ) ≤ τ / Real.pi := Nat.floor_le (div_nonneg hτ0 hp.le)
  have hn' : (homN τ : ℝ) * (Real.pi / 2) ≤ τ / 2 := by
    have h1 := mul_le_mul_of_nonneg_right hn (by positivity : (0 : ℝ) ≤ Real.pi / 2)
    have h2 : τ / Real.pi * (Real.pi / 2) = τ / 2 := by field_simp
    linarith
  have hpl := pulseLen_le (homN τ)
  have hd := homD_le hg
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl2 := Real.log_two_lt_d9
  have hpi := Real.pi_lt_d2
  unfold homBusy
  linarith

/-- `n = ⌊τ/π⌋ ≥ τ/π - 1 ≥ τ/5` for `τ ≥ 10` (line 3947). -/
theorem fifth_le_homN {τ : ℝ} (hτ : 10 ≤ τ) : τ / 5 ≤ homN τ := by
  have hp := Real.pi_pos
  have hpi := Real.pi_lt_d2
  have h1 := Nat.lt_floor_add_one (τ / Real.pi)
  have h2 : τ / 5 + 1 ≤ τ / Real.pi := by
    rw [le_div_iff₀ hp]
    nlinarith [mul_lt_mul_of_pos_left hpi (by linarith : (0 : ℝ) < τ / 5 + 1)]
  unfold homN
  linarith

/-- At least one hidden stage for `τ ≥ 10`. -/
theorem one_le_homN {τ : ℝ} (hτ : 10 ≤ τ) : 1 ≤ homN τ := by
  have h := fifth_le_homN hτ
  have h0 : (0 : ℝ) < homN τ := by linarith
  exact Nat.succ_le_of_lt (by exact_mod_cast h0)

/-- `2ε ≤ 15/17` for `ε ≤ 1/64`, the hypothesis `2ε ≤ a` of `Readout.heralded_correlation`. -/
theorem two_eps_le {ε : ℝ} (hε : ε ≤ 1 / 64) : 2 * ε ≤ 15 / 17 := by
  linarith

/-- `β = (2/3)(15/17 - 2ε) ≥ 463/816` for `ε ≤ 1/64`. -/
theorem homCorr_ge {ε : ℝ} (hε : ε ≤ 1 / 64) : 463 / 816 ≤ homCorr ε := by
  unfold homCorr
  linarith

/-- **The numeric chain of the remark** (lines 3947-3949 with lines 3895-3897): for `τ ≥ 10`,
`ḡ ≥ 2` and `β ≥ 463/816`, `ḡ √s τ / 500 ≤ β² n √(M m) / 16`, since `n ≥ τ/5`,
`√(Mm) ≥ ḡ√s/2` and `(463/816)²/160 ≥ 1/500`. -/
theorem hom_numeric {s : ℕ} {τ gbar : ℝ} (hτ : 10 ≤ τ) (hg : 2 ≤ gbar) {β : ℝ}
    (hβ : 463 / 816 ≤ β) :
    homConst * gbar * Real.sqrt s * τ ≤
      β ^ 2 * homN τ * Real.sqrt ((jointM gbar : ℝ) * 2 ^ jointMu s) / 16 := by
  have hn := fifth_le_homN hτ
  have hr := sqrt_jointM_mul_ge (s := s) hg
  have hβ2 : (463 / 816 : ℝ) ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ (by norm_num) hβ 2
  have hg0 : 0 ≤ gbar := by linarith
  have hgs : 0 ≤ gbar * Real.sqrt s := mul_nonneg hg0 (Real.sqrt_nonneg _)
  have h1 : (463 / 816 : ℝ) ^ 2 * (τ / 5) ≤ β ^ 2 * homN τ :=
    mul_le_mul hβ2 hn (by linarith) (sq_nonneg β)
  have h2 : (463 / 816 : ℝ) ^ 2 * (τ / 5) * (gbar * Real.sqrt s / 2) ≤
      β ^ 2 * homN τ * Real.sqrt ((jointM gbar : ℝ) * 2 ^ jointMu s) :=
    mul_le_mul h1 hr (by positivity) (mul_nonneg (sq_nonneg β) (Nat.cast_nonneg _))
  have hX : 0 ≤ gbar * Real.sqrt s * τ := mul_nonneg hgs (by linarith)
  unfold homConst
  nlinarith

end

end ODELowerBoundExtensions.Homogeneous
