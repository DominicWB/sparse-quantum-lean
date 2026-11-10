import ManuscriptConformance.GateDefs
import ManuscriptConformance.ODEUpper
import GateEfficientRemarks.ODE.ZeroReleased
import GateEfficientRemarks.ODE.MinRegister
import SourceAccuracyODE.Constant

/-!
# Conformance: Theorem `ode:thm:gates` (gate-efficient dissipative equations), constant coefficients

Theorem `ode:thm:gates` for the constant-coefficient problem of
`ode:thm:main`, every `T ≥ 0` (its remark on zero time and a known zero generator included), in the
native gate model (`GateDefs`: elementary gates are one-qubit unitaries with at most three
controls, so arbitrary single-qubit gates are allowed; primitive matrix calls are counted
separately):

* **Input.** Binary sparse data `D` (`formal_binaryInput`, review item B) for the generator
  `G = -A = D + iH` with row and column Euclidean norms of `H`, `D` at most `η_H`, `η_D`, `D ⪰ 0`;
  `x(T) ≠ 0` and `B = r₀ + T r_b ≤ ḡ ‖x(T)‖`; entry words and the public parameters `c₀`, `T`,
  `η_H`, `η_D` of at most `b_data` bits (`comp_bits`; the decoding and the reversible public
  arithmetic are the package's CORDIC circuits, whose polynomial cost is proved).
* **Source circuits.** Two native circuits `srcC false`, `srcC true` (gates `G_src`, scratch
  `A_src = |Zs|`) within `ζ_s ≤ ν = ε/(10⁴ ḡ)` of the controlled preparations of `x₀/‖x₀‖` and
  `b/‖b‖` on clean scratch (`ApproxOn CleanX`): each within `ν`, which the manuscript's combined
  implementation error `ν` of the source circuits implies (`G_src(ν)`, before Theorem
  `ode:thm:gates`; for constant forcing `G_src(ν) = G_{x₀}(cν) + G_b(cν) + …`, eq.
  `ode:eq:gate-constant-source`). The released analysis asks each within `ν/4`; `SourceAccuracyODE`
  certifies the same protocol for circuits within `ν` (every successful trial within `ε/250`; the
  formal vector error `18 ν B` is within the vector error `19 ν B` of the manuscript's proof, eq.
  `ode:eq:gate-vector-error`).
* **Protocol.** The package's four-attempt protocol `nprotocol (bprepC P srcC) ḡ` for the public
  data `P = odePub …` (the public rescaling `γ`, and `γ = 1` in the zero case, and the arithmetic
  accuracy `ζ = ν/(196608 q)` are chosen inside), fixed before the instance: it depends only on the
  public data and the source circuits.
  Review item K: the source circuits are native circuits that may call only the matrix
  primitives, and the native model has no separate source-preparation oracle; one protocol
  therefore serves the instances whose sources these circuits prepare, and the manuscript's
  supplied source-preparation calls (before Theorem `ode:thm:gates`) are not modelled.
* **Conclusions.** Every trial is a valid native circuit; in every history at most
  `C ḡ [q P(𝔟) + G_src + A_src]` elementary gates (eq. `ode:eq:gate-main`) and a register of at
  most `P(𝔟) + C A_src` qubits (eq. `ode:eq:gate-space`), with `P(x) = C (x+1)³`; at most
  `C ḡ q` calls of each matrix oracle (none in the zero case) besides `C ḡ` times the calls made
  inside the source circuits; heralded success at least `2/3`, conditional output within trace
  distance `ε` of `x(T)/‖x(T)‖` (`HeraldedOutput`), and every successful trial within Euclidean
  distance `ε` of it up to a global phase. The source preparations are native circuits, charged by
  their gates and the calls inside them; the number of their executions (the manuscript's `O(ḡ)`
  source-preparation calls) is counted on the annotated macro expansion of the protocol by
  `ode_thm_gates_sources` (`SourceExecutions`: at most `40 ḡ` executions of each circuit in every
  history, the calls and gates split into propagation and source parts). Here `q` is eq.
  `ode:eq:gate-q` (`odeShape`)
  and the
  word budget is `𝔟 = b_data + log₂(N+1) + log₂((q ḡ + 1)/ε)`, which is at most the `𝔟` of eq.
  `ode:eq:gate-word-budget` for every time mesh `M` and source-node count `m` (base-2 logarithms; a
  change of base changes only the constants).

**Formal restrictions.** `formal_binaryInput` (review item B); `formal_nondegenerate`
(`ḡ ≥ 1` and `B > 0`, which hold for every admissible instance: contractivity gives
`g = B/‖x(T)‖ ≥ 1`, and `x(T) ≠ 0` forces `B > 0`; it excludes only public data without any
admissible instance). Review item E (source circuits within `ν/4`) is resolved: each source circuit
within `ν` suffices (`SourceAccuracyODE.binary_ode_outcome_nonneg`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget
open SparseHamiltonian.GateBinaryODE (Pub mLift SZ4)
open SparseHamiltonian.ZeroTimeGateODE (bprepC BPublicOK0 BZeroCase)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

universe u v

/-! ### The manuscript's quantities -/

/-- **Eq. `ode:eq:gate-q`**: `q = √s Θ + √(s Θ ℓ) + ℓ`, `Θ = T η_H + T η_D ℓ`,
`ℓ = log(1/ν) = log(10⁴ ḡ/ε)`. -/
def odeShape (s T etaH etaD gbar ε : ℝ) : ℝ :=
  Real.sqrt s * (T * etaH + T * etaD * Real.log (10000 * gbar / ε)) +
    Real.sqrt (s * (T * etaH + T * etaD * Real.log (10000 * gbar / ε)) *
      Real.log (10000 * gbar / ε)) +
    Real.log (10000 * gbar / ε)

/-- The package's query shape is eq. `ode:eq:gate-q`. -/
theorem odeShape_eq (s T etaH etaD gbar ε : ℝ) :
    odeShape s T etaH etaD gbar ε = GateODEBudget.qOf s T etaH etaD gbar ε := rfl

/-! ### The public data of the solver -/

/-- **The public data of the constant-coefficient gate solver**, from the manuscript's public
inputs: `N = 2^k` (`k` index bits), `s = 2^{s_b}` slots, `b` stored bits, the decoder scale `c₀`,
`η_H`, `η_D`, `T`, `ḡ`, `ε`, `r₀ = ‖x₀‖`, `r_b = ‖b‖`, with the package's public choices: the
rescaling `γ = gammaOf T η_H η_D ḡ ε` (`γ = 1` in the zero case `T = 0 ∨ η_H + η_D = 0`) and the
arithmetic accuracy `ζ = ν/(196608 q)` (`GateBitBudget.zetaOf`). -/
def odePub (k sb : ℕ) (hsb : sb ≤ k) (b : ℕ) (c0 etaH etaD T gbar ε r₀ rb : ℝ) : Pub where
  kx := k
  σ := sb
  hσ := hsb
  b := b
  c0 := c0
  etaH := etaH
  etaD := etaD
  γ := if T = 0 ∨ etaH + etaD = 0 then 1 else GateODEBudget.gammaOf T etaH etaD gbar ε
  T := T
  g := gbar
  ε := ε
  r₀ := r₀
  rb := rb
  ζ := zetaOf (ImprovedODEQueryBudget.precision gbar ε)
    (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε)

/-- The qubits of the solver's register for the public data `q` and the source scratch `Zs`. -/
abbrev odeQubits (q : Pub) (Zs : Type) [Fintype Zs] : ℕ :=
  Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)

theorem hasBits_one {bd : ℕ} (h : 1 ≤ bd) : HasBits bd 1 := by
  rw [hasBits_iff]
  refine ⟨⟨2 ^ bd, ?_⟩, ?_⟩
  · push_cast
    rw [div_self (by positivity)]
  · rw [abs_one]
    exact one_lt_pow₀ (by norm_num) (by omega)

/-- The public conditions of the package (`BPublicOK0`, every `T ≥ 0`) hold for `odePub`. -/
theorem odePub_ok {k sb : ℕ} (hsb : sb ≤ k) {b : ℕ} {c0 etaH etaD T gbar ε r₀ rb : ℝ}
    (hb : 0 < b) (hc0 : 0 < c0) (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hT : 0 ≤ T) (hg : 1 ≤ gbar)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hr0 : 0 ≤ r₀) (hrb : 0 ≤ rb) (hB : 0 < r₀ + T * rb) :
    BPublicOK0 (odePub k sb hsb b c0 etaH etaD T gbar ε r₀ rb) := by
  have hε1 : ε ≤ 1 := by linarith
  have hν : 0 < ImprovedODEQueryBudget.precision gbar ε :=
    ImprovedODEQueryBudget.precision_pos gbar ε hg hε
  have hν1 : ImprovedODEQueryBudget.precision gbar ε ≤ 1 :=
    (ImprovedODEQueryBudget.precision_le_one_ten_thousandth gbar ε hg hε1).trans (by norm_num)
  have hQ1 : 1 ≤ GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε :=
    GateRemarks.ODE.one_le_qOf hT hH hD hg hε hε1
  obtain ⟨hz0, hz1, -, -⟩ := zetaOf_spec hν hν1 hQ1
  have hγ : 0 < (if T = 0 ∨ etaH + etaD = 0 then (1 : ℝ) else
        GateODEBudget.gammaOf T etaH etaD gbar ε) ∧
      (if T = 0 ∨ etaH + etaD = 0 then (1 : ℝ) else GateODEBudget.gammaOf T etaH etaD gbar ε) ≤
        1 := by
    split_ifs with hz
    · exact ⟨one_pos, le_rfl⟩
    · push Not at hz
      have hT' : 0 < T := lt_of_le_of_ne hT (Ne.symm hz.1)
      have hE : 0 < etaH + etaD := lt_of_le_of_ne (by linarith) (Ne.symm hz.2)
      have hS : GateODEBudget.ShapeOK 1 T etaH etaD gbar ε :=
        ⟨le_rfl, hT', hH, hD, hE, hg, hε, hε1⟩
      exact ⟨hS.gammaOf_pos, GateODEBudget.gammaOf_le_one _ _ _ _ _⟩
  exact ⟨hb, hc0, hH, hD, hγ.1, hγ.2, hT, hg, hε, hε2, hr0, hrb, hB, hz0, hz1⟩

/-- The rescaling hypothesis of the package for `odePub`: `γ = 1` has `b_data` bits in the zero
case, and `γ` is the public rescaling otherwise. -/
theorem odePub_gamma {q : Pub} {k sb : ℕ} {hsb : sb ≤ k} {b bd : ℕ}
    {c0 etaH etaD T gbar ε r₀ rb : ℝ} (hq : q = odePub k sb hsb b c0 etaH etaD T gbar ε r₀ rb)
    (hb : 0 < b) (hbd : b ≤ bd) :
    if BZeroCase q then HasBits bd q.γ
    else q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD q.g q.ε := by
  subst hq
  by_cases hz : BZeroCase (odePub k sb hsb b c0 etaH etaD T gbar ε r₀ rb)
  · rw [if_pos hz]
    have hz' : T = 0 ∨ etaH + etaD = 0 := hz
    show HasBits bd (if T = 0 ∨ etaH + etaD = 0 then (1 : ℝ) else
      GateODEBudget.gammaOf T etaH etaD gbar ε)
    rw [if_pos hz']
    exact hasBits_one (by omega)
  · rw [if_neg hz]
    have hz' : ¬ (T = 0 ∨ etaH + etaD = 0) := hz
    show (if T = 0 ∨ etaH + etaD = 0 then (1 : ℝ) else
      GateODEBudget.gammaOf T etaH etaD gbar ε) = GateODEBudget.gammaOf T etaH etaD gbar ε
    rw [if_neg hz']

/-- The arithmetic-accuracy hypotheses of the package for `odePub`: `ν ≤ 196608 q ζ`, and the
budget `98304 q ζ + 2 ζ_s ≤ 4 ν` of `SourceAccuracyODE` for every source accuracy `ζ_s ≤ ν`. -/
theorem odePub_zeta {q : Pub} {k sb : ℕ} {hsb : sb ≤ k} {b : ℕ}
    {c0 etaH etaD T gbar ε r₀ rb : ℝ} (hq : q = odePub k sb hsb b c0 etaH etaD T gbar ε r₀ rb)
    (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hT : 0 ≤ T) (hg : 1 ≤ gbar) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    q.params.nu ≤ 196608 * GateODEBudget.qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ ∧
    ∀ ζs : ℝ, ζs ≤ ImprovedODEQueryBudget.precision gbar ε →
      98304 * GateODEBudget.qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ + 2 * ζs ≤
        4 * q.params.nu := by
  subst hq
  have hν : 0 < ImprovedODEQueryBudget.precision gbar ε :=
    ImprovedODEQueryBudget.precision_pos gbar ε hg hε
  have hν1 : ImprovedODEQueryBudget.precision gbar ε ≤ 1 :=
    (ImprovedODEQueryBudget.precision_le_one_ten_thousandth gbar ε hg hε1).trans (by norm_num)
  have hQ1 : 1 ≤ GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε :=
    GateRemarks.ODE.one_le_qOf hT hH hD hg hε hε1
  obtain ⟨-, -, hzν, hz2⟩ := zetaOf_spec hν hν1 hQ1
  refine ⟨hzν, fun ζs h => ?_⟩
  show 98304 * GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε *
      zetaOf (ImprovedODEQueryBudget.precision gbar ε)
        (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε) + 2 * ζs ≤
    4 * ImprovedODEQueryBudget.precision gbar ε
  linarith

/-! ### Theorem `ode:thm:gates`, constant coefficients -/

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:gates`, constant coefficients** (eqs.
`ode:eq:gate-word-budget`, `ode:eq:gate-main`, `ode:eq:gate-space`, with its remark on zero time
and a known zero generator). See the module docstring. With `C = 10²⁰`: in the native gate model,
for binary sparse data and public parameters of at most `b_data` bits, every `T ≥ 0`, `ḡ`,
`0 < ε ≤ 1/2`, and valid source circuits, the protocol `nprotocol (bprepC (odePub …) srcC) ḡ`
(fixed before the instance) has valid trials, at most `C ḡ [q (𝔟+1)³ + G_src + A_src]` elementary
gates in every history, at most `C (𝔟+1)³ + C A_src` qubits, at most `C ḡ q` calls of each matrix
oracle (none if `T = 0` or `η_H + η_D = 0`) besides `C ḡ` times the calls inside the source
circuits, and on every admissible instance with source circuits within `ν = ε/(10⁴ ḡ)` of the
controlled source preparations: success at least `2/3`, conditional output within trace distance
`ε`, and every successful trial within `ε` of `x(T)/‖x(T)‖` up to a global phase. Formal
restrictions: `formal_binaryInput`, `formal_nondegenerate`. The finite-gate-set bound with `G_src`
entering linearly is a separate result for the binary format (`N = 2^{k_x}`, `T > 0`,
`η_H + η_D > 0`): `GateSelective.binary_ode_budget_sel`. -/
theorem ode_thm_gates :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} [Fintype n] [DecidableEq n] {s k b : ℕ}
        (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb bd : ℕ)
        (c0 etaH etaD T gbar ε r₀ rb : ℝ)
        (hF : formal_binaryInput D en sb c0) (_ : comp_bits b bd [c0, T, etaH, etaD])
        (hnd : formal_nondegenerate gbar (r₀ + T * rb))
        {Zs : Type} [Fintype Zs] [DecidableEq Zs]
        (srcC : Bool → List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)),
        (∀ c, ∀ i ∈ srcC c, i.Valid) →
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 → 0 ≤ r₀ → 0 ≤ rb →
        (∀ j, ∀ i ∈ trialN (bprepC (odePub k sb hF.hsb b c0 etaH etaD T gbar ε
          r₀ rb) srcC) j, i.Valid) ∧
        ((nprotocol (bprepC (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb)
            srcC) gbar hnd.1).worstCost wGateN : ℝ) ≤
          C * gbar * (odeShape s T etaH etaD gbar ε *
              (bitB bd (Fintype.card n) 0 0 (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
            ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ∧
        (odeQubits (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) Zs : ℝ) ≤
          C * (bitB bd (Fintype.card n) 0 0 (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
            C * Fintype.card Zs ∧
        (∀ c : Query → Bool,
          ((nprotocol (bprepC (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb)
            srcC) gbar hnd.1).worstCost (wCallN c) : ℝ) ≤
          (if T = 0 ∨ etaH + etaD = 0 then 0 else
            C * gbar * odeShape s T etaH etaD gbar ε *
              ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
                (if c Query.value then 1 else 0))) +
          C * gbar * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true))) ∧
        ∀ x : X,
          (∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2) →
          (∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2) →
          (∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) →
          (∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) →
          (∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
            (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re) →
          ∀ (Jsrc : Bool → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) (x0 v : Reg (Fin k) ℂ) (ζs : ℝ),
          (∀ c, OracleCircuit.IsUnitary (Jsrc c)) → 0 ≤ ζs →
          (∀ c, ApproxOn CleanX (nrun (prims (R := ℂ) D en x) (srcC c))
            (liftB (srcIdeal c (Jsrc c))) ζs) →
          ζs ≤ ImprovedODEQueryBudget.precision gbar ε →
          ‖x0‖ = r₀ → ‖v‖ = rb →
          (x0 ≠ 0 → Jsrc false (seedV (S := Fin k)) = ODEStateNormalization.unitDirection x0) →
          (v ≠ 0 → Jsrc true (seedV (S := Fin k)) = ODEStateNormalization.unitDirection v) →
          ODEConstantForcing.solution (-mLift D en x) x0 v T ≠ 0 →
          r₀ + T * rb ≤ gbar * ‖ODEConstantForcing.solution (-mLift D en x) x0 v T‖ →
          HeraldedOutput (nprotocol (bprepC (odePub k sb hF.hsb b c0 etaH etaD T
              gbar ε r₀ rb) srcC) gbar hnd.1) (prims (R := ℂ) D en x)
            (ODEStateNormalization.unitDirection
              (ODEConstantForcing.solution (-mLift D en x) x0 v T)) ε ∧
          ∀ j : ℕ, ((goodN (S := Fin k))†) (nrun (prims (R := ℂ) D en x)
              (trialN (bprepC (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb)
                srcC) j) sN) ≠ 0 →
            ∃ ω : ℂ, ‖ω‖ = 1 ∧
              ‖ω • ODEStateNormalization.unitDirection (((goodN (S := Fin k))†)
                  (nrun (prims (R := ℂ) D en x) (trialN (bprepC (odePub k sb
                    hF.hsb b c0 etaH etaD T gbar ε r₀ rb) srcC) j) sN)) -
                ODEStateNormalization.unitDirection
                  (ODEConstantForcing.solution (-mLift D en x) x0 v T)‖ ≤ ε := by
  refine ⟨10 ^ 20, by norm_num, ?_⟩
  intro X n _ _ s k b D en sb bd c0 etaH etaD T gbar ε r₀ rb hF hbits hnd Zs _ _ srcC hsrcV
    hH hD hT hε hε2 hr0 hrb
  obtain ⟨hbd, hc0b, hTb, hHb, hDb⟩ := hbits
  have hg := hnd.1
  have hB := hnd.2
  have hcard : Fintype.card n = 2 ^ k := card_eq_two_pow en
  rw [hcard]
  have hs := hF.hs
  subst hs
  have hε1 : ε ≤ 1 := by linarith
  have hg0 : 0 ≤ gbar := by linarith
  have hq := odePub_ok hF.hsb hF.hb hF.hc0 hH hD hT hg hε hε2 hr0 hrb hB
  have hγ := odePub_gamma (q := odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) rfl hF.hb hbd
  obtain ⟨hζ, hζs⟩ := odePub_zeta (q := odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) rfl
    hH hD hT hg hε hε1
  obtain ⟨-, -, -, hWg', hWc', -, hWC, -, hV, -⟩ :=
    GateRemarks.ODE.binary_ode_budget_bits_nonneg bd
      (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) hq hγ hζ hbd hc0b hTb hHb hDb D en
      hF.range hF.dec srcC hsrcV
  -- the abbreviations of the bounds
  have hQ1 : 1 ≤ GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε :=
    GateRemarks.ODE.one_le_qOf hT hH hD hg hε hε1
  have hB0 : 0 ≤ bitB bd (2 ^ k) 0 0 (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε)
      gbar ε := bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hS0 : (0 : ℝ) ≤ (nGatesN (srcC false) : ℝ) + nGatesN (srcC true) := by positivity
  have hZ0 : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
  -- the gate and qubit bounds in `𝔟` without the mesh and source-node terms
  have hbounds : ((nprotocol (bprepC (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) srcC)
        gbar hg).worstCost wGateN : ℝ) ≤
        10 ^ 20 * gbar * (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε *
          (bitB bd (2 ^ k) 0 0 (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε +
            1) ^ 3 + ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ∧
      (odeQubits (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) Zs : ℝ) ≤
        3 * 10 ^ 11 * (bitB bd (2 ^ k) 0 0
          (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
        2 * Fintype.card Zs := by
    by_cases hz : BZeroCase (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb)
    · have hγb : HasBits bd (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb).γ := by
        have h := hγ
        rw [if_pos hz] at h
        exact h
      obtain ⟨h1, h2, -⟩ := GateRemarks.ODE.binary_ode_budget_bits_zero_released bd
        (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) hq hz hγb hζ hbd hc0b hHb hDb D en
        srcC hsrcV 0 0
      exact ⟨h1, h2⟩
    · have hP := ZeroTimeGateODE.bpublicOK_of hq hz
      have hγ' : (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb).γ =
          GateODEBudget.gammaOf T etaH etaD gbar ε := by
        have h := hγ
        rw [if_neg hz] at h
        exact h
      have hw : (GateODEBudget.words (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) : ℝ) +
          ImprovedODEQueryBudget.logBudget gbar ε ≤
          300 * (bitB bd (2 ^ k) 0 0 (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε)
            gbar ε + 1) :=
        GateBitBudget.words_le bd (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) hP hγ' hζ
          hbd hc0b hTb hHb hDb
      have hℓ : 1 ≤ ImprovedODEQueryBudget.logBudget gbar ε :=
        ImprovedODEQueryBudget.logBudget_ge_one gbar ε hg hε hε1
      have hw0 : (0 : ℝ) ≤
          GateODEBudget.words (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) :=
        Nat.cast_nonneg _
      have hWg : ((nprotocol (bprepC (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) srcC)
          gbar hg).worstCost wGateN : ℝ) ≤
          3 * 10 ^ 12 * gbar * (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε *
            ((GateODEBudget.words (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) : ℝ) +
              ImprovedODEQueryBudget.logBudget gbar ε + 1) ^ 3 +
            ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) := hWg'
      have hWc : (odeQubits (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) Zs : ℝ) ≤
          10000 * ((GateODEBudget.words (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) :
            ℝ) + 1) ^ 3 + 2 * Fintype.card Zs := by exact_mod_cast hWc'
      have hY : 0 ≤ (bitB bd (2 ^ k) 0 0
          (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε + 1) ^ 3 :=
        pow_nonneg (by linarith) 3
      constructor
      · have hcube := cube_le (by linarith) hB0 hw
        exact hWg.trans (budget_mono (by norm_num) hg0 (by linarith) hY hS0 hZ0
          (by norm_num) hcube (by norm_num))
      · have hcube := cube_le hw0 hB0 (c := 300) (by linarith)
        have h1 := mul_le_mul_of_nonneg_left hcube (by norm_num : (0 : ℝ) ≤ 10000)
        linarith
  obtain ⟨hG0, hQ0⟩ := hbounds
  refine ⟨hV, ?_, ?_, ?_, ?_⟩
  · -- gates
    rw [odeShape_eq]
    exact hG0
  · -- qubits
    rw [odeShape_eq]
    have hY : 0 ≤ (bitB bd (2 ^ k) 0 0
        (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε + 1) ^ 3 :=
      pow_nonneg (by linarith) 3
    have h1 : 3 * 10 ^ 11 * (bitB bd (2 ^ k) 0 0
        (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε + 1) ^ 3 ≤
        10 ^ 20 * (bitB bd (2 ^ k) 0 0
          (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε + 1) ^ 3 :=
      mul_le_mul_of_nonneg_right (by norm_num) hY
    have h2 : 2 * (Fintype.card Zs : ℝ) ≤ 10 ^ 20 * Fintype.card Zs :=
      mul_le_mul_of_nonneg_right (by norm_num) hZ0
    linarith
  · -- calls
    intro c
    rw [odeShape_eq]
    have h := hWC c
    have hc : ((nprotocol (bprepC (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) srcC)
        gbar hg).worstCost (wCallN c) : ℝ) ≤
        (if T = 0 ∨ etaH + etaD = 0 then 0 else 3932160 * gbar *
          GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε *
            ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
              (if c Query.value then 1 else 0))) +
        40 * gbar * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true)) := h
    have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
        (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    have hN0 : (0 : ℝ) ≤ (nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true) := by positivity
    have h2 : 40 * gbar * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true)) ≤
        10 ^ 20 * gbar * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hg0) hN0
    by_cases hz : T = 0 ∨ etaH + etaD = 0
    · rw [if_pos hz] at hc ⊢
      linarith
    · rw [if_neg hz] at hc ⊢
      have h1 : 3932160 * gbar * GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) ≤
          10 ^ 20 * gbar * GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) := by
        apply mul_le_mul_of_nonneg_right _ hI0
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_right (by norm_num) hg0
      linarith
  · -- the guarantees, source circuits within `ν` (`SourceAccuracyODE`)
    intro x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs0 hsrc hacc hx0 hv hpx hpv hne hBnd
    have hγ' : ¬ BZeroCase (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) →
        (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb).γ = GateODEBudget.gammaOf
          (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb).T
          (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb).etaH
          (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb).etaD
          (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb).g
          (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb).ε := by
      intro hz
      have h := hγ
      rw [if_neg hz] at h
      exact h
    have o := (SourceAccuracyODE.binary_ode_outcome_nonneg
      (odePub k sb hF.hsb b c0 etaH etaD T gbar ε r₀ rb) hq hγ' D en hF.range hF.dec srcC hsrcV x
      hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs0 hsrc (hζs ζs hacc) hx0 hv hpx hpv hne
      hBnd).mono (show ε / 250 ≤ ε by linarith)
    exact ⟨⟨o.success_two_thirds, o.output_density, o.conditional_error⟩, o.trial_direction⟩

end

end ManuscriptConformance
