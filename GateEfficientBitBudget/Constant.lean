import GateEfficientBitBudget.Sizes
import GateEfficientODEBudget.Words

/-!
# Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟`, constant coefficients

For the public data `q : GateBinaryODE.Pub` of the dissipative solver from binary sparse data
with the public rescaling `γ = gammaOf T η_H η_D g ε` of `GateODEBudget.binary_ode_budget`, put
`q* = qOf s T η_H η_D g ε`, `ℓ = log(1/ν)`, and let the word budget of equation
`ode:eq:gate-word-budget` be

`𝔟 = bitB b_data (2^k_x) (2^m) (2^k) q* g ε
   = b_data + log₂(N+1) + log₂(M+1) + log₂(m_src+1) + log₂((q* g + 1)/ε)`

with the dimension `N = 2^k_x`, the time mesh `M = 2^m` of the released simulator and the
`m_src = 2^k` source nodes of the quadrature register. The bit-length hypotheses are on exactly
the public parameters that enter the register words: the stored bits `b ≤ b_data` and the bit
lengths (`HasBits`) of the decoder scale `c₀`, the time `T` and the energy bounds `η_H`, `η_D`;
the arithmetic accuracy is at least `ζ ≥ ν/(196608 q*)` (the explicit public choice
`ζ = zetaOf ν q* = ν/(196608 q*)` meets it with equality and leaves `ζs ≤ ν/4` in the released
budget `98304 q* ζ + 2 ζs ≤ ν`: `zetaOf_spec`).

* `words_le` (the key lemma): `𝔴 + ℓ ≤ 300 (𝔟₀ + 1)` for the register words
  `𝔴 = GateODEBudget.words q`, with `𝔟₀ = bitB b_data (2^k_x) 0 0 q* g ε ≤ 𝔟` (without the mesh
  and source-node terms, which are themselves logarithmic for constant coefficients);
  `words_le_bitB`: the same with `𝔟`.
* `binary_ode_budget_bits`: in every history the native protocol uses at most
  `10²⁰ g [q* (𝔟+1)³ + G_src + |Zs|]` elementary gates and its register has at most
  `3·10¹¹ (𝔟+1)³ + 2 |Zs|` qubits, together with every conclusion of the released
  `binary_ode_budget_words` and `binary_ode_budget` (the word budget, the explicit gate count,
  the calls, the register size and the guarantees `GateNative.NOutcome`).
* `zetaOf`, `zetaOf_spec`, `withChoice`, `withChoice_spec`: the public choices of `γ` and `ζ`
  are compatible with the released public conditions `Pub.OK` for every admissible public data.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBitBudget

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open GateODEBudget (gammaOf qOf words binary_ode_sizes binary_ode_budget binary_ode_budget_words
  pub_shapeOK gammaOf_le_one)
open ImprovedODEQueryBudget (precision logBudget radius)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### The public arithmetic accuracy -/

/-- **The public arithmetic accuracy** `ζ = ν/(196608 q*)`. -/
def zetaOf (ν Q : ℝ) : ℝ := ν / (196608 * Q)

/-- **The public arithmetic accuracy is admissible**: for `0 < ν ≤ 1` and `q* ≥ 1`,
`ζ = zetaOf ν q*` has `0 < ζ ≤ 1`, meets the lower bound `ν ≤ 196608 q* ζ` of the word budget
with equality, and `98304 q* ζ = ν/2`, so that the released arithmetic budget
`98304 q* ζ + 2 ζs ≤ ν` (respectively `+ 3 ζs` for time-dependent coefficients) holds exactly
for `ζs ≤ ν/4` (respectively `ζs ≤ ν/6`). -/
theorem zetaOf_spec {ν Q : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hQ : 1 ≤ Q) :
    0 < zetaOf ν Q ∧ zetaOf ν Q ≤ 1 ∧ ν ≤ 196608 * Q * zetaOf ν Q ∧
      98304 * Q * zetaOf ν Q = ν / 2 := by
  have hQ0 : 0 < Q := by linarith
  have e : 196608 * Q * zetaOf ν Q = ν := by
    unfold zetaOf
    field_simp
  refine ⟨by unfold zetaOf; positivity, ?_, le_of_eq e.symm, by linarith⟩
  unfold zetaOf
  rw [div_le_one (by positivity)]
  linarith

/-! ### The key lemma -/

/-- **The register words in the word budget** (constant coefficients; the key lemma of
equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟`). For the public data `q` with the
public rescaling `γ = gammaOf T η_H η_D g ε`, an arithmetic accuracy `ζ ≥ ν/(196608 q*)`, stored
bits `b ≤ b_data` and `c₀`, `T`, `η_H`, `η_D` of bit length `b_data`, the register words
`𝔴 = words q = k_x + b + m + r + k + l + F + n_c + ⌈log₂ ⌈κ⌉⌉ + ⌈log₂ ⌈1/κ⌉⌉` and
`ℓ = log(1/ν)` satisfy `𝔴 + ℓ ≤ 300 (b_data + log₂(N+1) + log₂((q* g + 1)/ε) + 1)`,
`N = 2^k_x`. -/
theorem words_le (bd : ℕ) (q : Pub) (hq : q.OK) (hγ : q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε)
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ) (hb : q.b ≤ bd)
    (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) :
    (words q : ℝ) + logBudget q.g q.ε ≤
      300 * (bitB bd (2 ^ q.kx) 0 0 (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) := by
  have h := pub_shapeOK q hq
  obtain ⟨-, -, hm, hr, hJ, hl, hk⟩ := binary_ode_sizes q hq hγ
  have hQ1 := h.one_le_q
  have hX := shape_one_le_X h
  have hQX := shape_q_le_X h
  have hνX : 1 / q.params.nu ≤
      10000 * ((qOf q.s q.T q.etaH q.etaD q.g q.ε * q.g + 1) / q.ε) :=
    shape_inv_precision_le h
  have hℓX := shape_ell_le_X h
  have hℓL := shape_ell_le_logb h
  have hν : 0 < q.params.nu := (q.params_ok hq).nu_pos
  have hℓ1 := h.ell_ge
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have wkx := nat_le_logb q.kx
  have wb : (q.b : ℝ) ≤ bd := by exact_mod_cast hb
  have wm := m_word q.params.m hQ1 hQX hν hνX hm
  have wr := r_word q.params.r hQ1 hQX hr
  have wk := k_word q.params.k hQ1 hQX hν hνX hk
  have wl := l_word q.params.l hQ1 hQX (by linarith) hℓX hl
  have wF : (q.F : ℝ) ≤ 54 + 4 * Real.logb 2
      ((qOf q.s q.T q.etaH q.etaD q.g q.ε * q.g + 1) / q.ε) :=
    F_word q.params hq.g_ge hq.ε_pos hε1 (q.TD_nonneg hq) hq.ζ_pos hQ1 hQX hJ hℓX hνX hζ
  have wn := nOf_word hq.ζ_pos hν hQ1 hQX hνX hζ
  obtain ⟨wκ, wκi⟩ := kap_words bd q.kx q.s (q.params.k + q.F + 10) h
    (Nat.pow_le_pow_right (by norm_num) q.hσ) hc0 hq.c0_pos hT hH hD
  have hkap : q.kap = gammaOf q.T q.etaH q.etaD q.g q.ε * Real.sqrt (4 * (q.s : ℝ)) * q.c0 /
      (2 ^ (q.params.k + q.F + 10) * (q.etaH + radius q.g q.ε * q.etaD)) := by
    rw [← hγ]
    rfl
  rw [← hkap] at wκ wκi
  simp only [Nat.cast_add, Nat.cast_ofNat] at wκi
  have hw : (words q : ℝ) = q.kx + q.b + q.params.m + q.params.r + q.params.k + q.params.l +
      q.F + (Cordic.nOf (q.ζ / 2) : ℝ) + (Nat.clog 2 ⌈q.kap⌉₊ : ℝ) +
      (Nat.clog 2 ⌈1 / q.kap⌉₊ : ℝ) := by
    unfold words
    push_cast
    ring
  have hb0 : bitB bd (2 ^ q.kx) 0 0 (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε =
      bd + Real.logb 2 (((2 ^ q.kx : ℕ) : ℝ) + 1) +
        Real.logb 2 ((qOf q.s q.T q.etaH q.etaD q.g q.ε * q.g + 1) / q.ε) := by
    unfold bitB
    simp only [Nat.cast_zero, zero_add, Real.logb_one, add_zero]
  rw [hw, hb0]
  have hL0 := Real.logb_nonneg one_lt_two hX
  have hN0 := logb_succ_nonneg (2 ^ q.kx)
  have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  linarith

/-- **The register words in the paper's `𝔟`** (constant coefficients):
`𝔴 + ℓ ≤ 300 (𝔟 + 1)` with `𝔟 = bitB b_data (2^k_x) (2^m) (2^k) q* g ε`, under the hypotheses of
`words_le`. -/
theorem words_le_bitB (bd : ℕ) (q : Pub) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε)
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ) (hb : q.b ≤ bd)
    (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) :
    (words q : ℝ) + logBudget q.g q.ε ≤
      300 * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) := by
  have h1 := words_le bd q hq hγ hζ hb hc0 hT hH hD
  have h2 := bitB_mono bd (2 ^ q.kx) 0 0 (2 ^ q.params.m) (2 ^ q.params.k)
    (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε (Nat.zero_le _) (Nat.zero_le _)
  linarith

/-! ### The budget in `𝔟` -/

section Budget

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in the word budget `𝔟`, constant
coefficients** (Theorem `ode:thm:gates`, equation `ode:eq:gate-word-budget`). Let the public
data `q` have the public rescaling `γ = gammaOf T η_H η_D g ε` and an arithmetic accuracy
`ζ ≥ ν/(196608 q*)` (`q* = qOf s T η_H η_D g ε`, `ν = ε/(10000 g)`, `ℓ = log(1/ν)`), let the
stored bits be `b ≤ b_data` and `c₀`, `T`, `η_H`, `η_D` have bit length `b_data` (`HasBits`), and
put `𝔟 = bitB b_data (2^k_x) (2^m) (2^k) q* g ε = b_data + log₂(N+1) + log₂(M+1) +
log₂(m_src+1) + log₂((q* g + 1)/ε)` for `N = 2^k_x`, the time mesh `M = 2^m` and `m_src = 2^k`
source nodes. For the binary data and the valid source circuits `srcC` of `binary_ode_solver`,
in every history the native protocol `nprotocol (q.prep srcC) g` uses at most
`10²⁰ g [q* (𝔟+1)³ + G_src + |Zs|]` elementary gates (`G_src = |srcC 0| + |srcC 1|`, `|Zs|` the
source scratch), and its register has at most `3·10¹¹ (𝔟+1)³ + 2 |Zs|` qubits: equations
`ode:eq:gate-main` and `ode:eq:gate-space` with `P(x) = 3·10¹¹ (x+1)³`, `C = 10²⁰` and
`A_src = |Zs|`. The register words satisfy `𝔴 + ℓ ≤ 300 (𝔟 + 1)` (`𝔴 = words q`), and every
conclusion of `GateODEBudget.binary_ode_budget_words` and `GateODEBudget.binary_ode_budget` is
kept: at most `3·10¹² g [q* (𝔴 + ℓ + 1)³ + G_src + |Zs|]` gates and `10000 (𝔴+1)³ + 2 |Zs|`
qubits; at most `36873000 g [q* (G_C + k_x + σ + m + r + k + ℓ (l+1) + 8) + G_src + A]` gates;
at most `3932160 g q*` calls of each matrix oracle besides `40 g` times the calls of the source
circuits; the register size; and, for every input and instance as in `binary_ode_solver` with
`98304 q* ζ + 2 ζs ≤ ν`, the guarantees `NOutcome` (success probability at least `2/3`,
conditional output within trace distance `ε`, every successful trial within `ε/500` of
`x(T)/‖x(T)‖` up to a global phase). -/
theorem binary_ode_budget_bits (bd : ℕ) (q : Pub) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε)
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ) (hb : q.b ≤ bd)
    (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD)
    (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    ((nprotocol (q.prep srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      10 ^ 20 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
            (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ∧
    (Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℝ) ≤
      3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
          (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 + 2 * Fintype.card Zs ∧
    (words q : ℝ) + logBudget q.g q.ε ≤
      300 * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ∧
    ((nprotocol (q.prep srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      3 * 10 ^ 12 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          ((words q : ℝ) + logBudget q.g q.ε + 1) ^ 3 +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ∧
    Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) ≤
      10000 * (words q + 1) ^ 3 + 2 * Fintype.card Zs ∧
    ((nprotocol (q.prep srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      36873000 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) : ℕ) : ℝ) +
            q.kx + q.σ + q.params.m + q.params.r + q.params.k +
            logBudget q.g q.ε * ((q.params.l : ℝ) + 1) + 8) +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
        ((q.kx : ℝ) + Fintype.card Zs + ((6 * q.kx + 4 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP +
          q.ar.A)) ∧
    (∀ c : Query → Bool, ((nprotocol (q.prep srcC) q.g hq.g_ge).worstCost (wCallN c) : ℝ) ≤
      3932160 * q.g * qOf q.s q.T q.etaH q.etaD q.g q.ε *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) +
        40 * q.g * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true))) ∧
    Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
      22 * q.kx + 12 * q.params.m + 24 * q.params.r + 4 * q.params.k + 4 * q.params.l +
        8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs + 47 ∧
    ∀ x : X,
      (∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re) →
      ∀ (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (x0 v : Reg (Fin q.kx) ℂ)
        (ζs : ℝ),
      (∀ c, IsUnitary (Jsrc c)) →
      0 ≤ ζs →
      (∀ c, ApproxOn CleanX (nrun (prims (R := ℂ) D en x) (srcC c))
        (liftB (srcIdeal c (Jsrc c))) ζs) →
      98304 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ + 2 * ζs ≤ q.params.nu →
      ‖x0‖ = q.r₀ → ‖v‖ = q.rb →
      (x0 ≠ 0 → Jsrc false (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection x0) →
      (v ≠ 0 → Jsrc true (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection v) →
      ODEConstantForcing.solution (-mLift D en x) x0 v q.T ≠ 0 →
      q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-mLift D en x) x0 v q.T‖ →
      NOutcome (q.prep srcC) q.g q.ε hq.g_ge (prims (R := ℂ) D en x)
        (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
  have h := pub_shapeOK q hq
  have hw := words_le_bitB bd q hq hγ hζ hb hc0 hT hH hD
  obtain ⟨hWg, hWc⟩ := binary_ode_budget_words q hq hγ D en hrange hdec srcC hsrcV
  obtain ⟨hG, hC, hcard, hout⟩ := binary_ode_budget q hq hγ D en hrange hdec srcC hsrcV
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hQ1 := h.one_le_q
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hB0 : 0 ≤ bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
      (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hq.ε_pos hε1
  have hℓ := h.ell_ge
  have hw0 : (0 : ℝ) ≤ words q := Nat.cast_nonneg _
  refine ⟨?_, ?_, hw, hWg, hWc, hG, hC, hcard, hout⟩
  · -- gates
    have hcube := cube_le (by linarith) hB0 hw
    refine hWg.trans (budget_mono (by norm_num) hg0 (by linarith) (by positivity)
      (by positivity) (by positivity) (by norm_num) hcube (by norm_num))
  · -- qubits
    have hcube := cube_le hw0 hB0 (c := 300) (by linarith)
    have hc : ((Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) :
        ℕ) : ℝ) ≤ 10000 * ((words q : ℝ) + 1) ^ 3 + 2 * Fintype.card Zs := by
      exact_mod_cast hWc
    have hY : 0 ≤ (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 := by positivity
    nlinarith

end Budget

/-! ### Compatibility of the public choices -/

/-- **The public choices** of the rescaling and of the arithmetic accuracy:
`γ = gammaOf T η_H η_D g ε` and `ζ = zetaOf ν q* = ν/(196608 q*)`, the other public data
unchanged. -/
def withChoice (q : Pub) : Pub :=
  { q with
    γ := gammaOf q.T q.etaH q.etaD q.g q.ε
    ζ := zetaOf (precision q.g q.ε) (qOf q.s q.T q.etaH q.etaD q.g q.ε) }

/-- **The public choices are admissible**: for public data satisfying the released conditions
`Pub.OK`, the data `withChoice q` with `γ = gammaOf T η_H η_D g ε` and `ζ = ν/(196608 q*)`
satisfy `Pub.OK`, the rescaling hypothesis of `binary_ode_budget_bits` and its accuracy
hypothesis `ν ≤ 196608 q* ζ`, and the released arithmetic budget `98304 q* ζ + 2 ζs ≤ ν` holds
exactly for `ζs ≤ ν/4`. The bit-length hypotheses concern `b`, `c₀`, `T`, `η_H`, `η_D`, which
are unchanged. -/
theorem withChoice_spec (q : Pub) (hq : q.OK) :
    (withChoice q).OK ∧
    (withChoice q).γ = gammaOf (withChoice q).T (withChoice q).etaH (withChoice q).etaD
      (withChoice q).g (withChoice q).ε ∧
    (withChoice q).params.nu ≤ 196608 * qOf (withChoice q).s (withChoice q).T
      (withChoice q).etaH (withChoice q).etaD (withChoice q).g (withChoice q).ε *
        (withChoice q).ζ ∧
    ∀ ζs : ℝ, 98304 * qOf (withChoice q).s (withChoice q).T (withChoice q).etaH
        (withChoice q).etaD (withChoice q).g (withChoice q).ε * (withChoice q).ζ + 2 * ζs ≤
          (withChoice q).params.nu ↔ ζs ≤ (withChoice q).params.nu / 4 := by
  have h := pub_shapeOK q hq
  have hν : 0 < precision q.g q.ε := (q.params_ok hq).nu_pos
  have hν1 : precision q.g q.ε ≤ 1 :=
    (ImprovedODEQueryBudget.precision_le_one_ten_thousandth q.g q.ε hq.g_ge
      (hq.ε_half.trans (by norm_num))).trans (by norm_num)
  obtain ⟨hz0, hz1, hzν, hz2⟩ := zetaOf_spec hν hν1 h.one_le_q
  refine ⟨?_, rfl, hzν, fun ζs => ?_⟩
  · exact ⟨hq.b_pos, hq.c0_pos, hq.etaH_nonneg, hq.etaD_nonneg, hq.eta_pos, h.gammaOf_pos,
      gammaOf_le_one _ _ _ _ _, hq.T_pos, hq.g_ge, hq.ε_pos, hq.ε_half, hq.r₀_nonneg,
      hq.rb_nonneg, hq.B_pos, hz0, hz1⟩
  · change 98304 * qOf q.s q.T q.etaH q.etaD q.g q.ε *
        zetaOf (precision q.g q.ε) (qOf q.s q.T q.etaH q.etaD q.g q.ε) + 2 * ζs ≤
      precision q.g q.ε ↔ ζs ≤ precision q.g q.ε / 4
    rw [hz2]
    constructor <;> intro h' <;> linarith

end

end SparseHamiltonian.GateBitBudget
