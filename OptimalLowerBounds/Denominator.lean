import OptimalLowerBounds.TwoNorm

set_option synthInstance.maxHeartbeats 400000

/-!
# Why the logarithmic denominator must also change

The paragraphs after the proof of Proposition `hsl:prop:two-norm`, in paraphrase: the precision
denominator of the enlarged family must contain its time scale `θ`, rather than `η|t|`. To make
that necessity explicit, enlarge the two-sparse signed chain of Lemma `hsl:lem:precision`, let `m`
tend to infinity through powers of four, and choose `s = 2m`, `η = t = 1`, `μ = m^{-1/2}`,
`L = √m log m` (eq. `twonorml:eq:counterexample-parameters`); the construction retains exact dyadic
entries. Keeping the old precision parameter would give `r̃ := L/log(e + L/(η|t|)) = Θ(√m)`,
`√s η|t| + √(sμ|t| r̃) + r̃ = O(√m)` (eq. `twonorml:eq:wrong-denominator`). On the uniform
added-register state, however, the original chain evolves for time `θ = √m`. For sufficiently large
`m`, `n = ⌊r_μ/4⌋` satisfies the scalar-chain hypotheses and requires
`Ω(r_μ) = Ω(√m log m/log log m)` queries (eq. `twonorml:eq:necessary-denominator`). Hence changing
only the mixed-term coefficient from `η` to `μ`, while keeping the old precision parameter
throughout, cannot be a uniform upper bound.

With `m = 4^k`:

* `denomData k`: the signed scalar chain of `hsl:lem:precision` (`scalarHam n 2 θ`, sparsity two
  with its padding) of length `n = ⌊r_μ/4⌋` at time `θ = 2^k = √m`, enlarged by `m` with
  coefficient `μ = 2^{-k} = m^{-1/2}` (`scalarTwo`): sparsity exactly `2m`, entries at most `μ`
  (attained), row and column norms at most `μ√m = 1` (attained), exact words
  (`denom_instance`, `denom_params`);
* `wrongShape s η μ t ε = √s η|t| + √(sμ|t| r̃) + r̃`, `r̃ = hsR (η|t|) ε`, the bound with only
  the mixed term changed; at the parameters, `2^k/2 ≤ r̃ ≤ 2^{k+1}` (`wrong_r_bounds`, `r̃ = Θ(√m)`)
  and `wrongShape ≤ 6·2^k` (`wrongShape_le`, `O(√m)`);
* `denom_rmu`: `r_μ = 2^k log(4^k)/log(e + log(4^k)) = √m log m/log(e + log m)`;
* `precision_scalar_of_access`, `denom_lower`: for `k ≥ 47` every program over a certified
  family, `ε`-accurate on `denomData k` for `e^{-it H_x}(ψ_in ⊗ u_m)`, `t = 1`, makes at least
  `r_μ/32` value queries (Lemma `hsl:lem:precision` with `n = ⌊r_μ/4⌋`);
* **`wrong_denominator`** (spectator form) and **`wrong_denominator_simulates`** (the common
  query form of the upper bounds): for every constant `C` and every
  `k ≥ max(47, ⌈(384 C)² + 3⌉)` every accurate algorithm makes more than `C · wrongShape`
  queries (`wrong_lt_of_lower`); so no bound `O(√s η|t| + √(sμ|t| r̃) + r̃)` holds uniformly;
* `denom_simulates`: for `k ≥ 2` the families are simulated by `hs:thm:two-norm` with the
  corrected precision parameter (`two_on_aligned_of`), so the lower bounds are not vacuous.
-/

namespace OptimalLowerBounds

noncomputable section
set_option autoImplicit false
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit SparseLowerBounds
open SparseLowerBounds.Hamiltonian SparseLowerBounds.Hamiltonian.HsRelease Readout
open scoped InnerProduct InnerProductSpace
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

/-! ### Lemma `hsl:lem:precision` for the scalar chain at any sparsity -/

section Precision

variable {θ ε : ℝ} {K G : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **Lemma `hsl:lem:precision` at the main parameters, any sparsity** (eqs. `hsl:eq:nrange`,
`hsl:eq:precisionchoice`, `hsl:eq:rbound`): for `θ ≥ 1`, `0 < ε ≤ 1/64`, `L ≥ 64θ` and every
sparsity parameter `s₀`, every program over a certified family that is `ε`-accurate on the signed
scalar chain
of length `n = ⌊r/4⌋` (`scalarHam n s₀ θ`) makes at least `r/32` value queries. The range
`HSRange θ 32 ε` only carries `θ ≥ 1` and `ε ≤ 1/64` here (the numerics do not involve the
sparsity). -/
theorem precision_scalar_of_access (h : HSRange θ 32 ε) (hL : 64 * θ ≤ hsL ε) {s₀ : ℕ}
    {O : Query → (Fin (precN θ ε) → Bool) → K →L[ℂ] K} (hO : ∀ l x, IsUnitary (O l x))
    (A : PhaseAccess (Fin (precN θ ε)) bitPattern O hardCost)
    (p : MultiOracleCircuit.Program O) (φ₀ : K)
    (e : K →L[ℂ] SysGarb (ScalarIndex (precN θ ε) s₀) G)
    (hacc : ∀ x, Accurate e (p.eval x φ₀)
      (evolve (scalarHam (precN θ ε) s₀ θ x) θ (scalarInput (precN θ ε) s₀)) ε) :
    hsR θ ε / 32 ≤ p.labelCount .value ∧ hsR θ ε / 32 ≤ p.count := by
  obtain ⟨hn, hrn, hτr, -⟩ := precN_range h hL
  have h16 := sixteen_eps_le h hL
  have hb := precision_general (n := precN θ ε) (s := s₀) (τ := θ) (ε := ε) (by omega)
    (by linarith [h.one_le_tau]) (by linarith) (by linarith [h.eps_pos])
    A.fam A.enc A.enc_isometry O hO hardCost A.implementsOn_bit p φ₀ e hacc
  have hrb := rbound h hL
  exact native_bound_of_cost p (by linarith)

end Precision

/-! ### The parameters -/

/-- `m = 4^k`. -/
def denomM (k : ℕ) : ℕ := 4 ^ k

theorem denomM_pos (k : ℕ) : 0 < denomM k := by
  unfold denomM; positivity

/-- `μ = m^{-1/2} = 2^{-k}`. -/
def denomMu (k : ℕ) : ℝ := ((2 : ℝ) ^ k)⁻¹

theorem denomMu_pos (k : ℕ) : 0 < denomMu k := by
  unfold denomMu; positivity

/-- `θ = μ m |t| = √m = 2^k` at `t = 1`. -/
def denomTheta (k : ℕ) : ℝ := (2 : ℝ) ^ k

/-- `L = √m log m = 2^k log(4^k)`. -/
def denomL (k : ℕ) : ℝ := (2 : ℝ) ^ k * Real.log ((4 : ℝ) ^ k)

/-- `ε = e^{-L}`. -/
def denomEps (k : ℕ) : ℝ := Real.exp (-denomL k)

/-- **The counterexample family**: the signed scalar chain of length `n = ⌊r_μ/4⌋` at sparsity
two and time `θ = 2^k`, enlarged by `m = 4^k` with coefficient `μ = 2^{-k}`. -/
def denomData (k : ℕ) :
    Data (Fin (precN (denomTheta k) (denomEps k)) → Bool)
      (ScalarIndex (precN (denomTheta k) (denomEps k)) 2 × Fin (denomM k))
      (Word (scalarBits (precN (denomTheta k) (denomEps k)) 2 (denomTheta k))) (2 * denomM k) :=
  scalarTwo (precN (denomTheta k) (denomEps k)) 2 (denomTheta k) le_rfl (denomM k) (denomM_pos k)
    (denomMu k) (denomMu_pos k).ne'

/-- `(4 : ℝ)^k = (2^k)²`. -/
theorem four_pow_eq (k : ℕ) : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- `log(4^k) = 2 k log 2`. -/
theorem log_four_pow (k : ℕ) : Real.log ((4 : ℝ) ^ k) = 2 * k * Real.log 2 := by
  rw [Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

/-- **The parameters of eq. `twonorml:eq:counterexample-parameters`**: `c m t = θ` with `t = 1`
(`μ m = 2^k`), `η = μ√m = 1`, `θ = √m`, `L = √m log m`, and `log(1/ε) = L`. -/
theorem denom_params (k : ℕ) :
    denomMu k * (denomM k : ℝ) * 1 = denomTheta k ∧
      |denomMu k| * Real.sqrt (denomM k) = 1 ∧ denomTheta k = Real.sqrt (denomM k) ∧
      denomL k = Real.sqrt (denomM k) * Real.log (denomM k) ∧ hsL (denomEps k) = denomL k := by
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have hm : (denomM k : ℝ) = ((2 : ℝ) ^ k) ^ 2 := by
    rw [denomM, Nat.cast_pow, Nat.cast_ofNat, four_pow_eq]
  have hsq : Real.sqrt (denomM k) = 2 ^ k := by rw [hm, Real.sqrt_sq h2.le]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [denomMu, denomTheta, hm]; field_simp
  · rw [abs_of_pos (denomMu_pos k), hsq, denomMu, inv_mul_cancel₀ h2.ne']
  · rw [denomTheta, hsq]
  · rw [denomL, hsq, denomM, Nat.cast_pow, Nat.cast_ofNat]
  · rw [hsL, denomEps, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]

/-- **The counterexample family satisfies `TwoNormInstance`** with `μ = 2^{-k}` and `η = μ√m = 1`:
real symmetric, sparsity exactly `2m`, entries of modulus at most `μ` (attained), row and column
Euclidean norms at most one (attained), exact words, public locators. -/
theorem denom_instance (k : ℕ) : TwoNormInstance (denomData k) (denomMu k) (denomM k) :=
  scalarTwo_twoNormInstance le_rfl (denomM_pos k) (denomMu_pos k).ne'

/-- `L ≥ 64θ` for `k ≥ 47` (`k log 4 ≥ 64`). -/
theorem denom_L_ge {k : ℕ} (hk : 47 ≤ k) : 64 * denomTheta k ≤ hsL (denomEps k) := by
  rw [(denom_params k).2.2.2.2, denomL, denomTheta, log_four_pow]
  have hl2 := Real.log_two_gt_d9
  have hk' : (47 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have : (64 : ℝ) ≤ 2 * k * Real.log 2 := by nlinarith
  nlinarith

/-- The range of `hsl:thm:main` (at the dummy sparsity `32`) for `k ≥ 2`. -/
theorem denom_range {k : ℕ} (hk : 2 ≤ k) : HSRange (denomTheta k) 32 (denomEps k) := by
  have hl2 := Real.log_two_gt_d9
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : (4 : ℝ) ≤ 2 ^ k := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  refine ⟨?_, le_rfl, Real.exp_pos _, ?_⟩
  · rw [denomTheta]; exact one_le_pow₀ (by norm_num)
  · rw [denomEps, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num
    have hL : (8 : ℝ) ≤ denomL k := by
      rw [denomL, log_four_pow]
      have : (2 : ℝ) ≤ 2 * k * Real.log 2 := by nlinarith
      nlinarith
    calc (64 : ℝ) ≤ Real.exp 8 := by
          have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
          have h4 : Real.exp 8 = Real.exp 2 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
          rw [h4]
          calc (64 : ℝ) ≤ 3 ^ 4 := by norm_num
            _ ≤ Real.exp 2 ^ 4 := pow_le_pow_left₀ (by norm_num) h3 4
      _ ≤ Real.exp (denomL k) := Real.exp_le_exp.mpr hL

/-- **`r_μ = √m log m/log(e + log m)`** (eq. `twonorml:eq:necessary-denominator`):
`L/θ = log(4^k)`. -/
theorem denom_rmu (k : ℕ) :
    hsR (denomTheta k) (denomEps k) =
      denomL k / Real.log (Real.exp 1 + Real.log ((4 : ℝ) ^ k)) := by
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  rw [hsR, hsH, (denom_params k).2.2.2.2, denomL, denomTheta]
  congr 3
  field_simp

/-! ### The bound with the old precision parameter -/

/-- **The bound with only the mixed term changed**: `√s η|t| + √(sμ|t| r̃) + r̃` with the old
precision parameter `r̃ = L/log(e + L/(η|t|))` (eq. `twonorml:eq:wrong-denominator`). -/
def wrongShape (s : ℕ) (η μ t ε : ℝ) : ℝ :=
  Real.sqrt s * η * |t| + Real.sqrt (s * μ * |t| * hsR (η * |t|) ε) + hsR (η * |t|) ε

/-- **`r̃ = Θ(√m)`** (eq. `twonorml:eq:wrong-denominator`): at `η = t = 1`,
`2^k/2 ≤ r̃ ≤ 2^{k+1}` for `k ≥ 1`. -/
theorem wrong_r_bounds {k : ℕ} (hk : 1 ≤ k) :
    (2 : ℝ) ^ k / 2 ≤ hsR (1 * |1|) (denomEps k) ∧ hsR (1 * |1|) (denomEps k) ≤ 2 * 2 ^ k := by
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : (2 : ℝ) ≤ 2 ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have h20 : (0 : ℝ) < 2 ^ k := by positivity
  set x : ℝ := 2 * k * Real.log 2 with hx
  have hx1 : 1 ≤ x := by rw [hx]; nlinarith
  have hL : hsL (denomEps k) = 2 ^ k * x := by
    rw [(denom_params k).2.2.2.2, denomL, log_four_pow]
  have hr : hsR (1 * |1|) (denomEps k) = 2 ^ k * x / Real.log (Real.exp 1 + 2 ^ k * x) := by
    rw [hsR, hsH, hL]; norm_num
  have hLpos : 0 < 2 ^ k * x := by positivity
  -- `log(e + L) ≥ log(2^k) = k log 2 > 0`
  have hlog_lo : k * Real.log 2 ≤ Real.log (Real.exp 1 + 2 ^ k * x) := by
    have : Real.log ((2 : ℝ) ^ k) = k * Real.log 2 := by rw [Real.log_pow]
    rw [← this]
    refine Real.log_le_log h20 ?_
    have : (2 : ℝ) ^ k ≤ 2 ^ k * x := le_mul_of_one_le_right h20.le hx1
    linarith [Real.exp_pos 1]
  have hkl : 0 < k * Real.log 2 := by positivity
  -- `log(e + L) ≤ log(4 · 2^k x) ≤ 2 log 2 + k log 2 + (x - 1)`
  have hlog_hi : Real.log (Real.exp 1 + 2 ^ k * x) ≤ 2 * Real.log 2 + k * Real.log 2 + (x - 1) := by
    have he : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; linarith
    have hle : Real.exp 1 + 2 ^ k * x ≤ 4 * (2 ^ k * x) := by nlinarith
    calc Real.log (Real.exp 1 + 2 ^ k * x) ≤ Real.log (4 * (2 ^ k * x)) :=
          Real.log_le_log (by positivity) hle
      _ = Real.log 4 + Real.log ((2 : ℝ) ^ k) + Real.log x := by
          rw [Real.log_mul (by norm_num) hLpos.ne', Real.log_mul h20.ne' (by linarith)]; ring
      _ ≤ 2 * Real.log 2 + k * Real.log 2 + (x - 1) := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, Real.log_pow]
          push_cast
          linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < x)]
  have hlogpos : 0 < Real.log (Real.exp 1 + 2 ^ k * x) := lt_of_lt_of_le hkl hlog_lo
  rw [hr]
  constructor
  · rw [le_div_iff₀ hlogpos]
    have : 2 * Real.log 2 + k * Real.log 2 + (x - 1) ≤ 2 * x := by rw [hx]; nlinarith
    nlinarith
  · rw [div_le_iff₀ hlogpos]
    have e : 2 ^ k * x = 2 * 2 ^ k * (k * Real.log 2) := by rw [hx]; ring
    calc 2 ^ k * x = 2 * 2 ^ k * (k * Real.log 2) := e
      _ ≤ 2 * 2 ^ k * Real.log (Real.exp 1 + 2 ^ k * x) :=
          mul_le_mul_of_nonneg_left hlog_lo (by positivity)

/-- **`√s η|t| + √(sμ|t| r̃) + r̃ = O(√m)`** (eq. `twonorml:eq:wrong-denominator`): at the
parameters, the bound with the old precision parameter is at most `6·2^k = 6√m` for `k ≥ 1`. -/
theorem wrongShape_le {k : ℕ} (hk : 1 ≤ k) :
    wrongShape (2 * denomM k) 1 (denomMu k) 1 (denomEps k) ≤ 6 * 2 ^ k := by
  obtain ⟨-, hr⟩ := wrong_r_bounds hk
  have h20 : (0 : ℝ) < 2 ^ k := by positivity
  have hm : ((2 * denomM k : ℕ) : ℝ) = 2 * ((2 : ℝ) ^ k) ^ 2 := by
    rw [Nat.cast_mul, denomM, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat, four_pow_eq]
  have hr0 : 0 ≤ hsR (1 * |1|) (denomEps k) :=
    le_trans (by positivity) (wrong_r_bounds hk).1
  unfold wrongShape
  rw [hm]
  have h1 : Real.sqrt (2 * ((2 : ℝ) ^ k) ^ 2) ≤ 2 * 2 ^ k := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq h20.le]
    have : Real.sqrt 2 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith
  have h2 : Real.sqrt (2 * ((2 : ℝ) ^ k) ^ 2 * denomMu k * |1| * hsR (1 * |1|) (denomEps k)) ≤
      2 * 2 ^ k := by
    have e : 2 * ((2 : ℝ) ^ k) ^ 2 * denomMu k * |1| = 2 * 2 ^ k := by
      rw [denomMu, abs_one]; field_simp
    rw [e]
    calc Real.sqrt (2 * 2 ^ k * hsR (1 * |1|) (denomEps k))
        ≤ Real.sqrt (2 * 2 ^ k * (2 * 2 ^ k)) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hr (by positivity))
      _ = 2 * 2 ^ k := Real.sqrt_mul_self (by positivity)
  simp only [abs_one, mul_one] at h2 hr ⊢
  linarith

/-! ### The impossibility -/

/-- **The required queries** (eq. `twonorml:eq:necessary-denominator`): for `k ≥ 47` every
program over a certified family that is `ε`-accurate on `denomData k` for
`e^{-it H_x}(ψ_in ⊗ u_m)` at `t = 1` makes at least `r_μ/32` value queries. -/
theorem denom_lower {k : ℕ} (hk : 47 ≤ k) {K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {O : Query → (Fin (precN (denomTheta k) (denomEps k)) → Bool) → K →L[ℂ] K}
    (hO : ∀ l x, IsUnitary (O l x))
    (A : PhaseAccess (Fin (precN (denomTheta k) (denomEps k))) bitPattern O hardCost)
    (p : MultiOracleCircuit.Program O) (φ₀ : K)
    (e : K →L[ℂ] SysGarb (ScalarIndex (precN (denomTheta k) (denomEps k)) 2 × Fin (denomM k)) G)
    (hacc : ∀ x, Accurate e (p.eval x φ₀) (evolve ((denomData k).matrix x) 1
      (embedU (denomM k) (scalarInput (precN (denomTheta k) (denomEps k)) 2))) (denomEps k)) :
    hsR (denomTheta k) (denomEps k) / 32 ≤ p.labelCount .value ∧
      hsR (denomTheta k) (denomEps k) / 32 ≤ p.count :=
  precision_scalar_of_access (denom_range (by omega)) (denom_L_ge hk) hO A p φ₀ _
    fun x => accurate_scalar_of_two le_rfl (denomM_pos k) (denomMu_pos k).ne'
      (denom_params k).1 e _ x (hacc x)

/-- The ratio: for `k ≥ max(47, ⌈(384 C)² + 3⌉)`, `C · 6·2^k < r_μ/32`. -/
theorem wrong_lt_rmu (C : ℝ) {k : ℕ} (hk : 47 ≤ k) (hkC : (384 * C) ^ 2 + 3 ≤ k) :
    C * (6 * 2 ^ k) < hsR (denomTheta k) (denomEps k) / 32 := by
  have hl2 := Real.log_two_gt_d9
  have h20 : (0 : ℝ) < 2 ^ k := by positivity
  set x : ℝ := Real.log ((4 : ℝ) ^ k) with hx
  have hxk : (k : ℝ) ≤ x := by rw [hx, log_four_pow]; nlinarith
  have hk' : (47 : ℝ) ≤ k := by exact_mod_cast hk
  have hx0 : 0 < x := by linarith
  have hlogpos : 0 < Real.log (Real.exp 1 + x) :=
    Real.log_pos (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have hr : hsR (denomTheta k) (denomEps k) = 2 ^ k * x / Real.log (Real.exp 1 + x) := by
    rw [denom_rmu, denomL]
  rw [hr]
  rcases le_or_gt C 0 with hC | hC
  · have : C * (6 * 2 ^ k) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC (by positivity)
    have : 0 < 2 ^ k * x / Real.log (Real.exp 1 + x) / 32 := by positivity
    linarith
  · -- `log(e + x) ≤ 2 √(e + x)` and `384 C √(e + x) ≤ x`
    have he3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    set y : ℝ := Real.exp 1 + x with hy
    have hy0 : 0 < y := by positivity
    have hlog_sqrt : Real.log y ≤ 2 * Real.sqrt y - 2 := by
      have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hy0)
      rw [Real.log_sqrt hy0.le] at h
      linarith
    set a : ℝ := (384 * C) ^ 2 with ha
    have hxa : a + 3 ≤ x := by linarith
    have hsq : 384 * C * Real.sqrt y ≤ x := by
      have hlhs : 0 ≤ 384 * C * Real.sqrt y := by positivity
      rw [← Real.sqrt_sq hx0.le, show 384 * C * Real.sqrt y = Real.sqrt ((384 * C) ^ 2 * y) by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]]
      apply Real.sqrt_le_sqrt
      rw [← ha, hy]
      nlinarith
    have hkey : 192 * C * Real.log y < x := by
      have h1 : 192 * C * Real.log y ≤ 192 * C * (2 * Real.sqrt y - 2) :=
        mul_le_mul_of_nonneg_left hlog_sqrt (by positivity)
      linarith
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 32), lt_div_iff₀ hlogpos]
    calc C * (6 * 2 ^ k) * 32 * Real.log y = 2 ^ k * (192 * C * Real.log y) := by ring
      _ < 2 ^ k * x := mul_lt_mul_of_pos_left hkey h20

/-- From the required queries to the impossibility: for `k ≥ max(47, ⌈(384 C)² + 3⌉)`, any count
of at least `r_μ/32` exceeds `C · wrongShape` (`wrongShape_le`, `wrong_lt_rmu`). -/
theorem wrong_lt_of_lower (C : ℝ) {k : ℕ} (hk47 : 47 ≤ k) (hkC : (384 * C) ^ 2 + 3 ≤ k)
    {Q : ℝ} (hQ : hsR (denomTheta k) (denomEps k) / 32 ≤ Q) :
    C * wrongShape (2 * denomM k) 1 (denomMu k) 1 (denomEps k) < Q := by
  have hW := wrongShape_le (k := k) (by omega)
  have hr := wrong_lt_rmu C hk47 hkC
  rcases le_or_gt C 0 with hC | hC
  · have hW0 : 0 ≤ wrongShape (2 * denomM k) 1 (denomMu k) 1 (denomEps k) := by
      unfold wrongShape
      have hr' := (wrong_r_bounds (k := k) (by omega)).1
      exact add_nonneg (add_nonneg (by positivity) (Real.sqrt_nonneg _))
        (le_trans (by positivity) hr')
    have h1 : C * wrongShape (2 * denomM k) 1 (denomMu k) 1 (denomEps k) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hC hW0
    have h2 : 0 < hsR (denomTheta k) (denomEps k) / 32 :=
      div_pos ((denom_range (k := k) (by omega)).hsR_pos) (by norm_num)
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 hQ)
  · have h1 := mul_le_mul_of_nonneg_left hW hC.le
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le hr hQ)

/-- **The logarithmic denominator must change** (eqs. `twonorml:eq:counterexample-parameters`,
`twonorml:eq:wrong-denominator`, `twonorml:eq:necessary-denominator`), spectator form: for every
constant `C` and every `k ≥ max(47, ⌈(384 C)² + 3⌉)`, every program over the native primitives
of `denomData k` with any untouched spectator register, `ε`-accurate in trace distance for
`e^{-iH_x}(ψ_in ⊗ u_m)` (`t = 1`, `ε = e^{-L}`), makes more than
`C (√s η|t| + √(sμ|t| r̃) + r̃)` value queries, at `s = 2m`, `η = 1`, `μ = m^{-1/2}`. So no
bound `O(√s η|t| + √(sμ|t| r̃) + r̃)` with the old precision parameter holds uniformly. -/
theorem wrong_denominator (C : ℝ) :
    ∀ k, max 47 ⌈(384 * C) ^ 2 + 3⌉₊ ≤ k → ∀ (Ω : Type) [Fintype Ω] {G : Type*}
      [NormedAddCommGroup G]
      [InnerProductSpace ℂ G] [CompleteSpace G]
      (p : MultiOracleCircuit.Program (specOracles Ω (denomData k)))
      (φ₀ : Joint Ω (ScalarTwoSpace (precN (denomTheta k) (denomEps k)) 2 (denomTheta k)
        (denomM k)))
      (e : Joint Ω (ScalarTwoSpace (precN (denomTheta k) (denomEps k)) 2 (denomTheta k)
          (denomM k)) →L[ℂ]
        SysGarb (ScalarIndex (precN (denomTheta k) (denomEps k)) 2 × Fin (denomM k)) G),
      (∀ x, Accurate e (p.eval x φ₀) (evolve ((denomData k).matrix x) 1
        (embedU (denomM k) (scalarInput (precN (denomTheta k) (denomEps k)) 2))) (denomEps k)) →
      C * wrongShape (2 * denomM k) 1 (denomMu k) 1 (denomEps k) < p.labelCount .value := by
  intro k hk Ω _ G _ _ _ p φ₀ e hacc
  have hk47 : 47 ≤ k := le_of_max_le_left hk
  have hkC : (384 * C) ^ 2 + 3 ≤ k :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hk)
  exact wrong_lt_of_lower C hk47 hkC (denom_lower hk47 (specOracles_unitary Ω _)
    ((scalarTwoAccess le_rfl (denomM_pos k) (denomMu_pos k).ne').spectate Ω) p φ₀ e hacc).1

/-- **The logarithmic denominator must change, common form**: for every constant `C` and every
`k ≥ max(47, ⌈(384 C)² + 3⌉)`, no common-form simulation (`NativeSignedFactor.Simulates`, the query
model of `hs:thm:optimal` and `hs:thm:two-norm`) of `denomData k` at `t = 1` within `ε = e^{-L}`
has a query bound at most `C (√s η|t| + √(sμ|t| r̃) + r̃)`. -/
theorem wrong_denominator_simulates (C : ℝ) :
    ∀ k, max 47 ⌈(384 * C) ^ 2 + 3⌉₊ ≤ k → ∀ q : ℝ,
      NativeSignedFactor.Simulates (NativeSignedFactor.physOracle (denomData k))
        (fun x => SparseStateOverlap.matrixOperator ((denomData k).matrix x)) 1 (denomEps k) q →
      C * wrongShape (2 * denomM k) 1 (denomMu k) 1 (denomEps k) < q := by
  intro k hk q hq
  have hk47 : 47 ≤ k := le_of_max_le_left hk
  have hkC : (384 * C) ^ 2 + 3 ≤ k :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hk)
  obtain ⟨ι, _, inp, p, hinp, hcount, hsim⟩ := hq
  obtain ⟨-, hacc⟩ := accurate_of_endpoint_program (common_unitary _ ι) p inp hinp
    (refZero, ⟨0, denomM_pos k⟩) (denom_instance k).isHermitian
    (norm_embedU_scalarInput _ _ (denomM_pos k)) fun x => (hsim x).2
  have hlow := (denom_lower hk47 (common_unitary _ ι)
    (commonAccess _ (scalarTwoAccess le_rfl (denomM_pos k) (denomMu_pos k).ne') ι) p _ _
    hacc).2
  exact wrong_lt_of_lower C hk47 hkC (hlow.trans hcount)

/-- **The counterexample family is simulable with the corrected denominator** (non-vacuity of
`wrong_denominator_simulates`): for `k ≥ 2`, `hs:thm:two-norm` simulates `denomData k` at `t = 1`
within `ε = e^{-L}` with at most `2·10¹² (√s η|t| + √(sμ|t| r_μ) + r_μ)` queries in the common
form, `s = 2m`, `η = μ√m = 1`, `μ = 2^{-k}`, `r_μ = L/log(e + L/θ)`: the bound with the corrected
precision parameter holds where the one with the old parameter fails. -/
theorem denom_simulates {k : ℕ} (hk : 2 ≤ k) :
    NativeSignedFactor.Simulates (NativeSignedFactor.physOracle (denomData k))
      (fun x => SparseStateOverlap.matrixOperator ((denomData k).matrix x)) 1 (denomEps k)
      (2 * 10 ^ 12 * (Real.sqrt ((2 * denomM k : ℕ) : ℝ) * (|denomMu k| *
        Real.sqrt (denomM k)) * |1| + Real.sqrt ((2 * denomM k : ℕ) * |denomMu k| * |1| *
          hsR (denomTheta k) (denomEps k)) + hsR (denomTheta k) (denomEps k))) := by
  have h := denom_range hk
  exact two_on_aligned_of (denomData k) (denom_instance k) h.one_le_tau (by norm_num) h.eps_pos
    h.eps_le (denomM_pos k) (denomMu_pos k).ne' (denom_params k).1

end

end OptimalLowerBounds
