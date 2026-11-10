import SparseLowerBounds.Hamiltonian.Theorem

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Corollary `hsl:cor:power`: no `O(√s L^p + L)` bound at fixed time

Manuscript: Corollary `hsl:cor:power` and eq. `hsl:eq:fixedtime`. At `τ = 1`, Theorem `hsl:thm:main`
gives `Ω(√s + √(sL/log(e+L)) + L/log(e+L))` (eq. `hsl:eq:fixedtime`, `fixedtime_sum`). The
corollary: for any fixed `p < 1/2`, a uniform bound `O(√s L^p + L)` at `τ = 1` is impossible, even
with any fixed extra polylogarithmic factor in `s`.

* `power_separation` (the proof of the corollary, proof of Corollary `hsl:cor:power`): for every
  constant `C` and all thresholds `L₀` and `s₀` there are `s, ε` in the range
  of the theorem with `L ≥ max(64, L₀)`, `s ≥ s₀`, `s ≥ 64 n` (so the mixed
  family applies at `τ = 1`) and
  `C (√s L^p + L) (log s)^k < (log 2/(384√2)) √(s r)`. Route: `L = N`,
  `s = N²` (`power_params`), `N → ∞` (`power_asymptotic`, real analysis);
  the right side is `Ω(N^{3/2}/√(log N))`, the left side
  `O(N^{1+max(p,0)} (log N)^k)`.
* `cor_power`: hence, at such a point with `L` and `s` beyond any thresholds
  (the proof sends both to infinity, `s = ⌈L²⌉`), on the
  mixed family `mixedMainData 1 ε s` every `ε`-accurate algorithm (spectator
  form, any spectator and garbage type) makes more than
  `C (√s L^p + L) (log s)^k` value queries (the ratio diverges as `L → ∞`);
* `cor_power_not_uniform`: equivalently, no constant `C` and no thresholds
  `L₀`, `s₀` admit, for all `s, ε` in range with `L ≥ L₀` and `s ≥ s₀`, an
  `ε`-accurate algorithm with `Q ≤ C (√s L^p + L) (log s)^k` (so not even an
  eventual `O(√s L^p + L)` bound, with thresholds on both `L` and `s`, holds).
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Readout
open scoped InnerProduct InnerProductSpace

-- The nested spectator spaces over the search index exceed the default instance size.
set_option synthInstance.maxSize 1024

universe u v

/-- The parameters of the corollary's proof (proof of Corollary `hsl:cor:power`) along integers:
`L = N` (`ε = e^{-N}`), `s = N²`. For `N ≥ 64` they lie in the range of the theorem and the mixed
family applies at `τ = 1` (`64 n ≤ s`, as `n ≤ r/4 ≤ N/4`). -/
theorem power_params {N : ℕ} (hN : 64 ≤ N) :
    HSRange 1 (N ^ 2) (Real.exp (-N)) ∧ hsL (Real.exp (-N)) = N ∧
      64 * (precN 1 (Real.exp (-N)) : ℝ) ≤ ((N ^ 2 : ℕ) : ℝ) := by
  have hN' : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : hsL (Real.exp (-N)) = N := by
    rw [hsL, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hε : Real.exp (-(N : ℝ)) ≤ 1 / 64 := by
    have h1 := Real.add_one_le_exp (N : ℝ)
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) (by linarith)
  have hR : HSRange 1 (N ^ 2) (Real.exp (-N)) :=
    ⟨le_rfl, le_trans (by norm_num) (Nat.pow_le_pow_left hN 2), Real.exp_pos _, hε⟩
  refine ⟨hR, hL, ?_⟩
  have h1 := hR.precN_le_quarter
  have h2 := hR.hsR_le_hsL
  rw [hL] at h2
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hN' (Nat.cast_nonneg (α := ℝ) N)]

/-- **The asymptotic separation** (proof of Corollary `hsl:cor:power`), at `L = N`, `s = N²`,
`r = N/log(e + N)`: for `p < 1/2`, every `k`, every `C` and every `N₀` there
is `N ≥ max(64, N₀)` with
`C (N · N^p + N) (log N²)^k < (log 2/(384√2)) √(N² · N/log(e+N))`; the right
side is `Ω(N^{3/2}/√(log N))`, the left side `O(N^{1+max(p,0)} (log N)^k)`.
Real analysis only: with `a = max(p, 0)`, `θ = 1/2 - a`, `δ = θ/(2k+1)`,
`log x ≤ x^δ/δ` bounds the logarithms, and the claim holds once `x^θ` exceeds
an explicit constant. -/
theorem power_asymptotic {pw : ℝ} (hp : pw < 1 / 2) (k : ℕ) (C : ℝ) (N₀ : ℕ) :
    ∃ N : ℕ, 64 ≤ N ∧ N₀ ≤ N ∧ C * ((N : ℝ) * (N : ℝ) ^ pw + N) * Real.log ((N : ℝ) ^ 2) ^ k <
      Real.log 2 / (384 * Real.sqrt 2) *
        Real.sqrt ((N : ℝ) ^ 2 * (N / Real.log (Real.exp 1 + N))) := by
  -- Exponents: `a = max(p, 0) < 1/2`, gap `θ = 1/2 - a`, `δ = θ/(2k+1) ≤ 1`.
  obtain ⟨a, ha0, hpa, ha⟩ : ∃ a : ℝ, 0 ≤ a ∧ pw ≤ a ∧ a < 1 / 2 :=
    ⟨max pw 0, le_max_right _ _, le_max_left _ _, max_lt hp (by norm_num)⟩
  obtain ⟨θ, hθ, hθa⟩ : ∃ θ : ℝ, 0 < θ ∧ 2 * a + 2 * θ = 1 := ⟨1 / 2 - a, by linarith, by ring⟩
  obtain ⟨δ, hδ, hδk⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * (2 * k + 1) = θ :=
    ⟨θ / (2 * k + 1), by positivity, div_mul_cancel₀ θ (by positivity)⟩
  have hδ1 : δ ≤ 1 := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [mul_nonneg hδ.le hk]
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = Real.log 2 / (384 * Real.sqrt 2) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hc_def]; exact div_pos (Real.log_pos one_lt_two) (by positivity)
  obtain ⟨C', hCC', hC'0⟩ : ∃ C' : ℝ, C ≤ C' ∧ 0 ≤ C' :=
    ⟨max C 0, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨K, hK_def⟩ : ∃ K : ℝ, K = 4 * C' ^ 2 * (2 / δ) ^ (2 * k + 1) / c ^ 2 := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hK_def]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max (max 64 (N₀ : ℝ)) ((K + 1) ^ (1 / θ)))
  have hx64 : (64 : ℝ) ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN.le
  have hxN₀ : (N₀ : ℝ) ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN.le
  have hxK : (K + 1) ^ (1 / θ) < N := (le_max_right _ _).trans_lt hN
  refine ⟨N, by exact_mod_cast hx64, by exact_mod_cast hxN₀, ?_⟩
  rw [← hc_def]
  suffices H : ∀ x : ℝ, 64 ≤ x → (K + 1) ^ (1 / θ) < x →
      C * (x * x ^ pw + x) * Real.log (x ^ 2) ^ k <
        c * Real.sqrt (x ^ 2 * (x / Real.log (Real.exp 1 + x))) from H N hx64 hxK
  intro x hx64 hxK
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  -- `x^θ > K`.
  have hθx : K < x ^ θ := by
    have h2 := Real.rpow_lt_rpow (Real.rpow_nonneg (by linarith) _) hxK hθ
    rw [← Real.rpow_mul (by linarith), one_div_mul_cancel hθ.ne', Real.rpow_one] at h2
    linarith
  have hxa := Real.rpow_le_rpow_of_exponent_le hx1 hpa
  have hxa1 := Real.one_le_rpow hx1 ha0
  have hxpw0 := Real.rpow_nonneg hx0.le pw
  have hQ0 : 0 < x ^ δ := Real.rpow_pos_of_pos hx0 δ
  have hQ1 := Real.one_le_rpow hx1 hδ.le
  have hR0 : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 θ
  -- The three factor bounds.
  have hA : x * x ^ pw + x ≤ 2 * (x * x ^ a) := by
    have h1 := mul_le_mul_of_nonneg_left hxa hx0.le
    have h2 := le_mul_of_one_le_right hx0.le hxa1
    linarith
  have hA0 : 0 ≤ x * x ^ pw + x := add_nonneg (mul_nonneg hx0.le hxpw0) hx0.le
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlogx : Real.log x ≤ x ^ δ / δ := by
    have h1 := Real.log_le_sub_one_of_pos hQ0
    rw [Real.log_rpow hx0] at h1
    rw [le_div_iff₀ hδ]
    linarith
  have hB0 : 0 ≤ Real.log (x ^ 2) := by rw [Real.log_pow]; push_cast; linarith
  have hB : Real.log (x ^ 2) ^ k ≤ (2 / δ) ^ k * (x ^ δ) ^ k := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ hB0 ?_ k
    rw [Real.log_pow]
    push_cast
    have : 2 * (x ^ δ / δ) = 2 / δ * x ^ δ := by ring
    linarith
  have hD0 : 0 < Real.log (Real.exp 1 + x) := Real.log_pos (by linarith [Real.exp_pos 1])
  have hD : Real.log (Real.exp 1 + x) ≤ 2 / δ * x ^ δ := by
    have he2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hmul : Real.exp 1 + x ≤ Real.exp 1 * x := by
      linarith [mul_nonneg (sub_nonneg.2 he2) (sub_nonneg.2 hx64)]
    have h1 : Real.log (Real.exp 1 + x) ≤ 1 + Real.log x := by
      calc Real.log (Real.exp 1 + x) ≤ Real.log (Real.exp 1 * x) :=
            Real.log_le_log (by linarith [Real.exp_pos 1]) hmul
        _ = 1 + Real.log x := by rw [Real.log_mul (Real.exp_pos 1).ne' hx0.ne', Real.log_exp]
    have h2 : 1 ≤ x ^ δ / δ := by rw [le_div_iff₀ hδ]; linarith
    have : 2 / δ * x ^ δ = x ^ δ / δ + x ^ δ / δ := by ring
    linarith
  -- The exponent identity `x^{2a} x^{(2k+1)δ} x^θ = x`.
  have hPQR : (x ^ a) ^ 2 * (x ^ δ) ^ (2 * k + 1) * x ^ θ = x := by
    rw [← Real.rpow_natCast (x ^ a) 2, ← Real.rpow_natCast (x ^ δ) (2 * k + 1),
      ← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    have he : a * ((2 : ℕ) : ℝ) + δ * ((2 * k + 1 : ℕ) : ℝ) + θ = 1 := by
      push_cast
      linarith
    rw [he, Real.rpow_one]
  -- The left side is at most `U = C' · 2x^{1+a} · (2/δ)^k x^{kδ}`.
  obtain ⟨U, hU_def⟩ : ∃ U : ℝ, U = C' * (2 * (x * x ^ a)) * ((2 / δ) ^ k * (x ^ δ) ^ k) :=
    ⟨_, rfl⟩
  have hδ2 : 0 ≤ 2 / δ := (div_pos two_pos hδ).le
  have hxxa : 0 ≤ 2 * (x * x ^ a) := by
    have := mul_nonneg hx0.le (by linarith : (0 : ℝ) ≤ x ^ a)
    linarith
  have hU : C * (x * x ^ pw + x) * Real.log (x ^ 2) ^ k ≤ U := by
    rw [hU_def]
    calc C * (x * x ^ pw + x) * Real.log (x ^ 2) ^ k
        ≤ C' * (x * x ^ pw + x) * Real.log (x ^ 2) ^ k :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC' hA0) (pow_nonneg hB0 k)
      _ ≤ C' * (2 * (x * x ^ a)) * ((2 / δ) ^ k * (x ^ δ) ^ k) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hA hC'0) hB (pow_nonneg hB0 k)
            (mul_nonneg hC'0 hxxa)
  have hU0 : 0 ≤ U := by
    rw [hU_def]
    exact mul_nonneg (mul_nonneg hC'0 hxxa)
      (mul_nonneg (pow_nonneg hδ2 k) (pow_nonneg hQ0.le k))
  refine lt_of_le_of_lt hU ?_
  -- `(U/c)² (2/δ) x^δ x^θ = K x³`, and `K < x^θ`.
  have hkey : (U / c) ^ 2 * (2 / δ * x ^ δ) * x ^ θ =
      K * x ^ 2 * ((x ^ a) ^ 2 * (x ^ δ) ^ (2 * k + 1) * x ^ θ) := by
    rw [hU_def, hK_def]
    ring
  rw [hPQR] at hkey
  have h2 : (U / c) ^ 2 * (2 / δ * x ^ δ) < x ^ 3 := by
    have hx3 : 0 < x ^ 3 := pow_pos hx0 3
    by_contra hcon
    push Not at hcon
    have h3 := mul_le_mul_of_nonneg_right hcon hR0.le
    rw [hkey] at h3
    have h4 : K * x ^ 2 * x = x ^ 3 * K := by ring
    linarith [mul_lt_mul_of_pos_left hθx hx3]
  have h4 : (U / c) ^ 2 < x ^ 2 * (x / Real.log (Real.exp 1 + x)) := by
    have h5 : (U / c) ^ 2 * Real.log (Real.exp 1 + x) < x ^ 3 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hD (sq_nonneg _)) h2
    rw [← mul_div_assoc, lt_div_iff₀ hD0, show x ^ 2 * x = x ^ 3 by ring]
    exact h5
  have h6 : U / c < Real.sqrt (x ^ 2 * (x / Real.log (Real.exp 1 + x))) :=
    (Real.lt_sqrt (div_nonneg hU0 hc.le)).mpr h4
  calc U = c * (U / c) := by have := hc.ne'; field_simp
    _ < c * Real.sqrt (x ^ 2 * (x / Real.log (Real.exp 1 + x))) := mul_lt_mul_of_pos_left h6 hc

/-- **Separation of the mixed bound from `√s L^p + L`** (proof of Corollary
`hsl:cor:power`): for `p < 1/2`, every `k`, every `C` and
all thresholds `L₀`, `s₀` there are `s, ε` with `HSRange 1 s ε`, `L ≥ 64`,
`L ≥ L₀`, `s ≥ s₀`, `64 n ≤ s` (`n = ⌊r/4⌋`) and
`C (√s L^p + L) (log s)^k < (log 2/(384√2)) √(s · 1 · r)`. -/
theorem power_separation {pw : ℝ} (hp : pw < 1 / 2) (k : ℕ) (C L₀ : ℝ) (s₀ : ℕ) :
    ∃ s : ℕ, ∃ ε : ℝ, HSRange 1 s ε ∧ 64 ≤ hsL ε ∧ L₀ ≤ hsL ε ∧ s₀ ≤ s ∧
      64 * (precN 1 ε : ℝ) ≤ s ∧
      C * (Real.sqrt s * hsL ε ^ pw + hsL ε) * Real.log s ^ k <
        Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * 1 * hsR 1 ε) := by
  obtain ⟨N, hN, hN₀, hlt⟩ := power_asymptotic hp k C (max ⌈L₀⌉₊ s₀)
  obtain ⟨hR, hLN, hn⟩ := power_params hN
  refine ⟨N ^ 2, Real.exp (-N), hR, ?_, ?_, ?_, hn, ?_⟩
  · rw [hLN]
    exact_mod_cast hN
  · rw [hLN]
    exact (Nat.le_ceil L₀).trans (by exact_mod_cast (le_max_left _ _).trans hN₀)
  · exact ((le_max_right _ _).trans hN₀).trans (Nat.le_self_pow two_ne_zero N)
  · have hr : hsR 1 (Real.exp (-N)) = N / Real.log (Real.exp 1 + N / 1) := by
      rw [hsR, hsH, hLN]
    rw [hr, hLN]
    push_cast
    rw [Real.sqrt_sq (Nat.cast_nonneg N)]
    simp only [mul_one, div_one]
    exact hlt

/-- **Corollary `hsl:cor:power`** (Corollary `hsl:cor:power`): a uniform `O(√s L^p + L)` bound at
`τ = 1`, even with a fixed `polylog(s)` factor, is impossible. For `p < 1/2`, every `k`, every `C`
and all thresholds `L₀`, `s₀` there is a point `(s, ε)` of the theorem's range (with `τ = 1`) with
`L = log(1/ε) ≥ L₀` and `s ≥ s₀` (the proof takes `L → ∞` and `s = ⌈L²⌉`, proof of Corollary
`hsl:cor:power`) at which every `ε`-accurate algorithm on the mixed family, with any spectator `Ω`
and any garbage `G`, makes more than `C (√s L^p + L) (log s)^k` value queries. -/
theorem cor_power {pw : ℝ} (hp : pw < 1 / 2) (k : ℕ) (C L₀ : ℝ) (s₀ : ℕ) :
    ∃ s : ℕ, ∃ ε : ℝ, ∃ h : HSRange 1 s ε, L₀ ≤ hsL ε ∧ s₀ ≤ s ∧
      ∀ (Ω : Type u) [Fintype Ω] (G : Type v) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
        [CompleteSpace G]
        (p : MultiOracleCircuit.Program (specOracles Ω (mixedMainData 1 ε s h.s_ge)))
        (φ₀ : Joint Ω (SearchSpace (precN 1 ε) (hsMu s) s 1 1)) (_ : ‖φ₀‖ ≤ 1)
        (e : Joint Ω (SearchSpace (precN 1 ε) (hsMu s) s 1 1) →L[ℂ]
          SysGarb (SearchIndex (precN 1 ε) (hsMu s) s) G) (_ : e† ∘L e = 1),
        (∀ j, Accurate e (p.eval j φ₀)
          (evolve ((mixedMainData 1 ε s h.s_ge).matrix j) 1
            (searchInput (precN 1 ε) (hsMu s) s)) ε) →
        C * (Real.sqrt s * hsL ε ^ pw + hsL ε) * Real.log s ^ k < p.labelCount .value := by
  obtain ⟨s, ε, h, hL, hL₀, hs₀, hs, hlt⟩ := power_separation hp k C L₀ s₀
  refine ⟨s, ε, h, hL₀, hs₀, fun Ω _ G _ _ _ p φ₀ hφ₀ e he hacc => ?_⟩
  have hm := mixed_main h (by linarith) (by rw [div_one]; exact hs) Ω p φ₀ hφ₀ e he hacc
  exact lt_of_lt_of_le hlt hm.1

/-- **Corollary `hsl:cor:power`, negated-upper-bound form**: for `p < 1/2`
and every `k`, there is no constant `C` and no thresholds `L₀`, `s₀` such that
for all `s, ε` in the range of Theorem `hsl:thm:main` at `τ = 1` with
`L ≥ L₀` and `s ≥ s₀` some `ε`-accurate algorithm (spectator form) on the
mixed family makes at most `C (√s L^p + L) (log s)^k` value queries. -/
theorem cor_power_not_uniform {pw : ℝ} (hp : pw < 1 / 2) (k : ℕ) :
    ¬ ∃ (C L₀ : ℝ) (s₀ : ℕ), ∀ (s : ℕ) (ε : ℝ) (h : HSRange 1 s ε), s₀ ≤ s → L₀ ≤ hsL ε →
      ∃ (Ω : Type u) (_ : Fintype Ω) (G : Type v) (_ : NormedAddCommGroup G)
        (_ : InnerProductSpace ℂ G) (_ : CompleteSpace G)
        (p : MultiOracleCircuit.Program (specOracles Ω (mixedMainData 1 ε s h.s_ge)))
        (φ₀ : Joint Ω (SearchSpace (precN 1 ε) (hsMu s) s 1 1)) (_ : ‖φ₀‖ ≤ 1)
        (e : Joint Ω (SearchSpace (precN 1 ε) (hsMu s) s 1 1) →L[ℂ]
          SysGarb (SearchIndex (precN 1 ε) (hsMu s) s) G) (_ : e† ∘L e = 1),
        (∀ j, Accurate e (p.eval j φ₀)
          (evolve ((mixedMainData 1 ε s h.s_ge).matrix j) 1
            (searchInput (precN 1 ε) (hsMu s) s)) ε) ∧
        (p.labelCount .value : ℝ) ≤ C * (Real.sqrt s * hsL ε ^ pw + hsL ε) * Real.log s ^ k := by
  rintro ⟨C, L₀, s₀, hC⟩
  obtain ⟨s, ε, h, hL₀, hs₀, hcor⟩ := cor_power.{u, v} hp k C L₀ s₀
  obtain ⟨Ω, _, G, _, _, _, p, φ₀, hφ₀, e, he, hacc, hle⟩ := hC s ε h hs₀ hL₀
  exact absurd hle (not_le.mpr (hcor Ω G p φ₀ hφ₀ e he hacc))

end

end SparseLowerBounds.Hamiltonian
end
