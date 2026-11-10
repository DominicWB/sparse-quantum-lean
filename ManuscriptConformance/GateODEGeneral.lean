import ManuscriptConformance.GateODE
import ManuscriptConformance.GateGeneral
import GeneralSparseODE.ConstantBudget
import GeneralSparseODE.Valid

/-!
# Conformance: Theorem `ode:thm:gates` for sparse access of general size, constant coefficients

Theorem `ode:thm:gates` for the constant-coefficient problem of
`ode:thm:main`, every `T ≥ 0`, as `ode_thm_gates` (`GateODE`), for the sparse access of the
manuscript in general sizes (`SparseHamiltonian.GeneralSparseAccess.QData`, Section
`hs:sec:control`: an `N × N` generator with `s`-sparse lists, `1 ≤ s ≤ N`, index registers of
`k = ⌈log₂ N⌉` qubits, locators prescribed on the valid list inputs only):

* **Input.** The generator `G = -A` of the general sparse access `D` with row and column Euclidean
  norms of the Hamiltonian and dissipative parts of its matrix at most `η_H`, `η_D` and an accretive
  dissipative part on `ℂ^N`; the stored words decoded as `c₀(X + iY)` (`formal_binaryDecoder`);
  public parameters of at most `b_data` bits (`comp_bits`).
* **Source circuits.** Two native circuits on the control, the `k` qubits of the index register and
  scratch `Zs`, calling the supplied oracles `D.prims x`, within `ν = ε/(10⁴ ḡ)` of the controlled
  preparations of `x₀/‖x₀‖` and `b/‖b‖` for vectors `x₀`, `b` of the index register.
* **Protocol.** The package's four-attempt protocol for the padded problem
  (`SparseHamiltonian.GeneralSparseODE.GPub.prep`, public data `odePubG …`): in the zero case
  (`T = 0` or `η_H + η_D = 0`) the direct source assembly, as in `ode_thm_gates`, otherwise the
  native preparation of the released solver from binary data on the padded data `D.padData`
  (`k + 1`-bit index words, `2^⌈log₂ s⌉` slots), with every call of the padded oracles in its
  private operation replaced by the implementation from the supplied oracles
  (`GeneralSparseAccess.implP`: at most three supplied calls and `implG k b` gates, on clean
  ancillas in the private scratch); the source circuits run on the low wires of the padded system
  register. It depends only on the public data and the source circuits. As in `ode_thm_gates`
  (review item K), the source circuits are native circuits charged by their gates and the calls
  inside them; the number of their executions is not a separate count here (it is for
  `ode_thm_gates` and `ode_thm_gates_decoder`: `SourceExecutions`), and no source-preparation
  oracle is modelled.
* **Conclusions.** Valid trials; at most `C ḡ [q P(𝔟) + G_src + A_src]` gates in every history and
  `P(𝔟) + C A_src` qubits, `P(x) = C (x+1)³`, with `q` of eq. `ode:eq:gate-q` for the sparsity `s`
  and `𝔟 = b_data + log₂(N+1) + log₂((q ḡ + 1)/ε)` for the dimension `N`; at most `C ḡ q` calls of
  each supplied matrix oracle (none in the zero case) besides `C ḡ` times the calls inside the source
  circuits; heralded success at least `2/3`, conditional output within trace distance `ε` of the
  normalised solution `x(T)/‖x(T)‖` of `x' = -A x + b` on the index register with the marker qubit
  clean (the unit direction of `cleanAlong Fin.castSuccEmb (x(T))`, the output register being the
  `k + 1`-qubit padded index register), and every successful trial within `ε` of it up to a global
  phase. Here `A` is the matrix extended by zero to the index words `≥ N` (`QData.padMat`, lifted
  by `padLift`).

**The problem on `ℂ^N`.** `padLift D x` is the matrix of `D` on the valid index words and zero
elsewhere (`GeneralSparseODE.padLift_eq`). For sources `x₀ = validEmb y₀`, `b = validEmb c` of
vectors `y₀`, `c` on `ℂ^N` (`GeneralSparseODE.validEmb`: the basis vector of `i` to that of the
index word `binW k i`, an isometry) the solution is `validEmb ∘ y` for the solution `y` of the
manuscript's problem `y' = -M y + c`, `y(0) = y₀`, on `ℂ^N`
(`GeneralSparseODE.solution_padLift_validEmb`), so the target is the clean embedding of
`validEmb (y(T)/‖y(T)‖)` (`GeneralSparseODE.unitDirection_validEmb`).
A source component on an invalid index word is decoupled from the matrix and evolves by
`x_j(T) = x₀_j + T b_j` (`GeneralSparseODE.solution_padLift_invalid`), so the theorem also covers
sources with such components.

**Formal restrictions.** `formal_binaryDecoder` (review item B2) and `formal_nondegenerate`; the
sizes `N`, `s` and the locator lists are general (review item B).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GeneralSparseODE (GPub markEmb padLift)
open SparseHamiltonian.GateBinaryODE (Pub SZ4)
open SparseHamiltonian.ZeroTimeGateODE (BPublicOK0 BZeroCase)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

universe u

/-! ### The public data -/

/-- **The public data of the general constant-coefficient solver**: the index bits `k`, the
sparsity `s ≤ 2^k`, `b` stored bits and the manuscript's public inputs, with the package's public
choices for the padded problem (`2^⌈log₂ s⌉` slots): the rescaling `γ = gammaOf T η_H η_D ḡ ε`
(`γ = 1` in the zero case) and the arithmetic accuracy `ζ = ν/(196608 q')`, `q'` the query shape of
the padded slot count. -/
def odePubG (k s : ℕ) (hs : s ≤ 2 ^ k) (b : ℕ) (c0 etaH etaD T gbar ε r₀ rb : ℝ) : GPub where
  k := k
  s := s
  hs := hs
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
    (GateODEBudget.qOf ((2 ^ sbP s : ℕ) : ℝ) T etaH etaD gbar ε)

/-- The padded problem of `odePubG` is the released public data `odePub` of `k + 1` index bits and
`⌈log₂ s⌉` slot bits. -/
theorem odePubG_pub (k s : ℕ) (hs : s ≤ 2 ^ k) (b : ℕ) (c0 etaH etaD T gbar ε r₀ rb : ℝ) :
    (odePubG k s hs b c0 etaH etaD T gbar ε r₀ rb).pub =
      odePub (k + 1) (sbP s) ((sbP_le hs).trans (Nat.le_succ k)) b c0 etaH etaD T gbar ε r₀ rb :=
  rfl

/-- The qubits of the general solver's register. -/
abbrev odeQubitsG (q : GPub) (Zs : Type) [Fintype Zs] : ℕ := Fintype.card (q.reg Zs)

/-- The marker embedding is the clean embedding along the low index wires. -/
theorem markEmb_eq_cleanAlong (k : ℕ) :
    (markEmb k : Reg (Fin k) ℂ →L[ℂ] Reg (Fin (k + 1)) ℂ) =
      cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) := by
  refine ContinuousLinearMap.ext fun ψ => PiLp.ext fun y => ?_
  rw [GeneralSparseODE.markEmb_apply, cleanAlong_castSucc_apply]

/-! ### Real estimates -/

/-- The query shape of eq. `ode:eq:gate-q` at most doubles when the sparsity at most doubles. -/
theorem qOf_le_of_le {s s' T ηH ηD g ε : ℝ} (hs : 0 ≤ s) (hss : s' ≤ 2 * s) (hT : 0 ≤ T)
    (hH : 0 ≤ ηH) (hD : 0 ≤ ηD) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    GateODEBudget.qOf s' T ηH ηD g ε ≤ 2 * GateODEBudget.qOf s T ηH ηD g ε := by
  have hℓ := ImprovedODEQueryBudget.logBudget_ge_one g ε hg hε hε1
  have hΘ : 0 ≤ GateODEBudget.thetaOf T ηH ηD g ε := by
    unfold GateODEBudget.thetaOf ImprovedODEQueryBudget.theta
    have h1 := mul_nonneg hT hH
    have h2 := mul_nonneg (mul_nonneg hT hD)
      (by linarith : (0 : ℝ) ≤ ImprovedODEQueryBudget.logBudget g ε)
    linarith
  unfold GateODEBudget.qOf ImprovedODEQueryBudget.queryShape
  generalize GateODEBudget.thetaOf T ηH ηD g ε = Θ at hΘ
  generalize ImprovedODEQueryBudget.logBudget g ε = ℓ at hℓ
  have h1 : Real.sqrt s' ≤ 2 * Real.sqrt s := sqrt_le_two_mul_sqrt hs (by linarith)
  have h2 : Real.sqrt (s' * Θ * ℓ) ≤ 2 * Real.sqrt (s * Θ * ℓ) := by
    apply sqrt_le_two_mul_sqrt (by positivity)
    have hΘℓ : 0 ≤ Θ * ℓ := mul_nonneg hΘ (by linarith)
    have : s' * (Θ * ℓ) ≤ 4 * s * (Θ * ℓ) := mul_le_mul_of_nonneg_right (by linarith) hΘℓ
    nlinarith
  have h3 : Real.sqrt s' * Θ ≤ 2 * Real.sqrt s * Θ := mul_le_mul_of_nonneg_right h1 hΘ
  have h4 : 0 ≤ Real.sqrt (s * Θ * ℓ) := Real.sqrt_nonneg _
  have h5 : 0 ≤ Real.sqrt s * Θ := mul_nonneg (Real.sqrt_nonneg _) hΘ
  nlinarith

/-- The word budget of the padded problem: `𝔟' ≤ 𝔟 + 3` for `2^k < 2N` and `q' ≤ 2 q`. -/
theorem bitB_pad_le {bd k N : ℕ} (hk : 2 ^ k < 2 * N) {Q Q' g ε : ℝ} (hQ : 0 ≤ Q) (hQQ : Q' ≤ 2 * Q)
    (hQ' : 0 ≤ Q') (hg : 0 ≤ g) (hε : 0 < ε) :
    bitB bd (2 ^ (k + 1)) 0 0 Q' g ε ≤ bitB bd N 0 0 Q g ε + 3 := by
  unfold bitB
  have h1 := logb_pow_succ_le hk
  have h2 : (Q' * g + 1) / ε ≤ 2 * ((Q * g + 1) / ε) := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hε]
    have := mul_le_mul_of_nonneg_right hQQ hg
    nlinarith
  have h3 : Real.logb 2 ((Q' * g + 1) / ε) ≤ Real.logb 2 ((Q * g + 1) / ε) + 1 := by
    have hpos : 0 < (Q' * g + 1) / ε := by
      apply div_pos _ hε
      have := mul_nonneg hQ' hg
      linarith
    have h4 := Real.logb_le_logb_of_le one_lt_two hpos h2
    rw [Real.logb_mul (by norm_num) (by
      apply ne_of_gt
      apply div_pos _ hε
      have := mul_nonneg hQ hg
      linarith), Real.logb_self_eq_one one_lt_two] at h4
    linarith
  simp only [Nat.cast_zero, zero_add, Real.logb_one, add_zero]
  linarith

/-- `(𝔟' + 1)³ ≤ 64 (𝔟 + 1)³` for `𝔟' ≤ 𝔟 + 3`, `𝔟 ≥ 0`. -/
theorem cube_pad_le {B B' : ℝ} (hB : 0 ≤ B) (hB' : 0 ≤ B') (h : B' ≤ B + 3) :
    (B' + 1) ^ 3 ≤ 64 * (B + 1) ^ 3 := by
  have h1 : B' + 1 ≤ 4 * (B + 1) := by linarith
  have h2 : (B' + 1) ^ 3 ≤ (4 * (B + 1)) ^ 3 := pow_le_pow_left₀ (by linarith) h1 3
  have e : (4 * (B + 1)) ^ 3 = 64 * (B + 1) ^ 3 := by ring
  linarith

/-! ### Theorem `ode:thm:gates` for sparse access of general size, constant coefficients -/

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:gates` for sparse access of general size, constant coefficients** (eqs.
`ode:eq:gate-word-budget`, `ode:eq:gate-main`, `ode:eq:gate-space`, with its closing sentence on
zero time and a known zero generator). See the module docstring. With `C = 10²³`: for
the general sparse access `D` (`2^{k-1} < N ≤ 2^k`) with the decoder `c₀(X + iY)`, public
parameters of at most `b_data` bits, every `T ≥ 0`, `ḡ`, `0 < ε ≤ 1/2` and valid source circuits
calling the supplied oracles, the protocol `nprotocol ((odePubG …).prep N 0 srcC) ḡ` (fixed before
the instance) has valid trials, at most `C ḡ [q (𝔟+1)³ + G_src + A_src]` elementary gates in every
history (`q` for the sparsity `s`, `𝔟 = b_data + log₂(N+1) + log₂((q ḡ + 1)/ε)`), at most
`C (𝔟+1)³ + C A_src` qubits, at most `C ḡ q` calls of each supplied matrix oracle (none if `T = 0`
or `η_H + η_D = 0`) besides `C ḡ` times the calls inside the source circuits, and on every
admissible instance with source circuits within `ν = ε/(10⁴ ḡ)` of the controlled source
preparations: success at least `2/3`, conditional output within trace distance `ε` of the
normalised solution of `x' = -A x + b` on the index register (marker clean), and every successful
trial within `ε` of it up to a global phase. Formal restrictions: `formal_binaryDecoder`,
`formal_nondegenerate`. The finite-gate-set bound with `G_src` entering linearly is a separate
result for the binary format (`N = 2^{k_x}`, `T > 0`, `η_H + η_D > 0`):
`GateSelective.binary_ode_budget_sel`. -/
theorem ode_thm_gates_general :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b) (bd : ℕ)
        (c0 etaH etaD T gbar ε r₀ rb : ℝ),
        2 ^ k < 2 * N → formal_binaryDecoder D c0 → comp_bits b bd [c0, T, etaH, etaD] →
        ∀ (hnd : formal_nondegenerate gbar (r₀ + T * rb))
        {Zs : Type} [Fintype Zs] [DecidableEq Zs]
        (srcC : Bool → List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)),
        (∀ c, ∀ i ∈ srcC c, i.Valid) →
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 → 0 ≤ r₀ → 0 ≤ rb →
        (∀ j, ∀ i ∈ trialN ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).prep N
          (fun _ => false) srcC) j, i.Valid) ∧
        ((nprotocol ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).prep N
            (fun _ => false) srcC) gbar hnd.1).worstCost wGateN : ℝ) ≤
          C * gbar * (odeShape s T etaH etaD gbar ε *
              (bitB bd N 0 0 (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
            ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ∧
        (odeQubitsG (odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb) Zs : ℝ) ≤
          C * (bitB bd N 0 0 (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
            C * Fintype.card Zs ∧
        (∀ c : Query → Bool,
          ((nprotocol ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).prep N
            (fun _ => false) srcC) gbar hnd.1).worstCost (wCallN c) : ℝ) ≤
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
          (∀ w : EuclideanSpace ℂ (Fin N), 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
            (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re) →
          ∀ (Jsrc : Bool → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) (x0 v : Reg (Fin k) ℂ) (ζs : ℝ),
          (∀ c, OracleCircuit.IsUnitary (Jsrc c)) → 0 ≤ ζs →
          (∀ c, ApproxOn CleanX (nrun (D.prims (R := ℂ) x) (srcC c))
            (liftB (srcIdeal c (Jsrc c))) ζs) →
          ζs ≤ ImprovedODEQueryBudget.precision gbar ε →
          ‖x0‖ = r₀ → ‖v‖ = rb →
          (x0 ≠ 0 → Jsrc false (seedV (S := Fin k)) = ODEStateNormalization.unitDirection x0) →
          (v ≠ 0 → Jsrc true (seedV (S := Fin k)) = ODEStateNormalization.unitDirection v) →
          ODEConstantForcing.solution (-padLift D x) x0 v T ≠ 0 →
          r₀ + T * rb ≤ gbar * ‖ODEConstantForcing.solution (-padLift D x) x0 v T‖ →
          HeraldedOutput (nprotocol ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).prep N
              (fun _ => false) srcC) gbar hnd.1) (D.prims (R := ℂ) x)
            (ODEStateNormalization.unitDirection
              (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))
                (ODEConstantForcing.solution (-padLift D x) x0 v T))) ε ∧
          ∀ j : ℕ, ((goodN (S := Fin (k + 1)))†) (nrun (D.prims (R := ℂ) x)
              (trialN ((odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb).prep N
                (fun _ => false) srcC) j) sN) ≠ 0 →
            ∃ ω : ℂ, ‖ω‖ = 1 ∧
              ‖ω • ODEStateNormalization.unitDirection (((goodN (S := Fin (k + 1)))†)
                  (nrun (D.prims (R := ℂ) x) (trialN ((odePubG k s D.s_le_pow b c0 etaH etaD T
                    gbar ε r₀ rb).prep N (fun _ => false) srcC) j) sN)) -
                ODEStateNormalization.unitDirection
                  (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))
                    (ODEConstantForcing.solution (-padLift D x) x0 v T))‖ ≤ ε := by
  refine ⟨10 ^ 23, by norm_num, ?_⟩
  intro X N s k b D bd c0 etaH etaD T gbar ε r₀ rb hk hF hbits hnd Zs _ _ srcC hsrcV hH hD hT hε
    hε2 hr0 hrb
  obtain ⟨hbd, hc0b, hTb, hHb, hDb⟩ := hbits
  have hg := hnd.1
  have hB := hnd.2
  have hε1 : ε ≤ 1 := by linarith
  have hg0 : 0 ≤ gbar := by linarith
  set q := odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb with hqdef
  have hqp : q.pub = odePub (k + 1) (sbP s) ((sbP_le D.s_le_pow).trans (Nat.le_succ k)) b c0
      etaH etaD T gbar ε r₀ rb := rfl
  have hq : BPublicOK0 q.pub := by
    rw [hqp]
    exact odePub_ok _ hF.hb hF.hc0 hH hD hT hg hε hε2 hr0 hrb hB
  have hγ := odePub_gamma hqp hF.hb hbd
  obtain ⟨hζ, hζs⟩ := odePub_zeta hqp hH hD hT hg hε hε1
  obtain ⟨hV, hWg0, hWq0, hWc0⟩ := GeneralSparseODE.general_ode_budget bd q hq hγ hζ hbd hc0b hTb
    hHb hDb N (fun _ => false) srcC hsrcV
  have hWg : ((nprotocol (q.prep N (fun _ => false) srcC) gbar hnd.1).worstCost wGateN : ℝ) ≤
      10 ^ 20 * gbar * (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε *
        (bitB bd (2 ^ (k + 1)) 0 0 (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε +
          1) ^ 3 + ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) := hWg0
  have hWq : (Fintype.card (q.reg Zs) : ℝ) ≤ 3 * 10 ^ 11 * (bitB bd (2 ^ (k + 1)) 0 0
      (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
      2 * Fintype.card Zs := hWq0
  have hWc : ∀ c : Query → Bool, ((nprotocol (q.prep N (fun _ => false) srcC) gbar
      hnd.1).worstCost (wCallN c) : ℝ) ≤ (if T = 0 ∨ etaH + etaD = 0 then 0 else
        11796480 * gbar * GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0))) +
        40 * gbar * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true)) := hWc0
  -- the query shapes and the word budgets
  have hsP : (((sP s : ℕ) : ℝ)) ≤ 2 * (s : ℝ) := by
    have h' : ((sP s : ℕ) : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast (sP_lt D.slots_pos).le
    push_cast at h'
    exact h'
  have hQQ : GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε ≤
      2 * GateODEBudget.qOf s T etaH etaD gbar ε :=
    qOf_le_of_le (Nat.cast_nonneg _) hsP hT hH hD hg hε hε1
  have hQ1 : 1 ≤ GateODEBudget.qOf s T etaH etaD gbar ε :=
    GateRemarks.ODE.one_le_qOf hT hH hD hg hε hε1
  have hQ1' : 1 ≤ GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε :=
    GateRemarks.ODE.one_le_qOf hT hH hD hg hε hε1
  have hB0 : 0 ≤ bitB bd N 0 0 (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hB0' : 0 ≤ bitB bd (2 ^ (k + 1)) 0 0 (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε)
      gbar ε := bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hBB := bitB_pad_le (bd := bd) hk (by linarith) hQQ (by linarith) hg0 hε
  have hcube := cube_pad_le hB0 hB0' hBB
  have hY : 0 ≤ (bitB bd N 0 0 (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε + 1) ^ 3 := by
    positivity
  have hY' : 0 ≤ (bitB bd (2 ^ (k + 1)) 0 0 (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε)
      gbar ε + 1) ^ 3 := by positivity
  have hZ0 : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
  rw [odeShape_eq]
  refine ⟨hV, ?_, ?_, ?_, ?_⟩
  · -- gates
    refine hWg.trans ?_
    generalize GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε = Q' at hQQ hQ1' hcube hY' ⊢
    generalize GateODEBudget.qOf s T etaH etaD gbar ε = Q at hQQ hQ1 hcube hB0 hY ⊢
    generalize (bitB bd (2 ^ (k + 1)) 0 0 Q' gbar ε + 1) ^ 3 = Y' at hcube hY' ⊢
    generalize (bitB bd N 0 0 Q gbar ε + 1) ^ 3 = Y at hcube hY ⊢
    have hG0 : (0 : ℝ) ≤ (nGatesN (srcC false) : ℝ) + nGatesN (srcC true) := by positivity
    have h1 : Q' * Y' ≤ 128 * (Q * Y) := by
      have h2 : Q' * Y' ≤ (2 * Q) * Y' := mul_le_mul_of_nonneg_right hQQ hY'
      have h3 : (2 * Q) * Y' ≤ (2 * Q) * (64 * Y) := mul_le_mul_of_nonneg_left hcube (by linarith)
      nlinarith
    have hQY : 0 ≤ Q * Y := mul_nonneg (by linarith) hY
    have h4 : (10 : ℝ) ^ 20 * gbar * (Q' * Y' + ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
        Fintype.card Zs) ≤ 10 ^ 20 * gbar * (128 * (Q * Y) + ((nGatesN (srcC false) : ℝ) +
          nGatesN (srcC true)) + Fintype.card Zs) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h5 : (10 : ℝ) ^ 20 * gbar * (128 * (Q * Y) + ((nGatesN (srcC false) : ℝ) +
          nGatesN (srcC true)) + Fintype.card Zs) ≤ 10 ^ 23 * gbar * (Q * Y +
          ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) := by
      have h6 : (10 : ℝ) ^ 20 * (128 * (Q * Y) + ((nGatesN (srcC false) : ℝ) +
          nGatesN (srcC true)) + Fintype.card Zs) ≤ 10 ^ 23 * (Q * Y +
          ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) := by
        nlinarith
      have := mul_le_mul_of_nonneg_left h6 hg0
      linarith
    linarith
  · -- qubits
    have h1 := mul_le_mul_of_nonneg_left hcube (by norm_num : (0 : ℝ) ≤ 3 * 10 ^ 11)
    have h2 : (2 : ℝ) * Fintype.card Zs ≤ 10 ^ 23 * Fintype.card Zs :=
      mul_le_mul_of_nonneg_right (by norm_num) hZ0
    have h3 : (3 * 10 ^ 11 : ℝ) * (64 * (bitB bd N 0 0 (GateODEBudget.qOf s T etaH etaD gbar ε)
        gbar ε + 1) ^ 3) ≤ 10 ^ 23 * (bitB bd N 0 0 (GateODEBudget.qOf s T etaH etaD gbar ε)
        gbar ε + 1) ^ 3 := by nlinarith
    have hq' : (odeQubitsG q Zs : ℝ) = (Fintype.card (q.reg Zs) : ℝ) := rfl
    rw [hq']
    linarith
  · -- calls
    intro c
    have hW := hWc c
    have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
        (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    have hS0 : (0 : ℝ) ≤ (nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true) := by positivity
    have hS : 40 * gbar * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true)) ≤
        10 ^ 23 * gbar * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hg0) hS0
    by_cases hz : T = 0 ∨ etaH + etaD = 0
    · rw [if_pos hz] at hW
      rw [if_pos hz]
      linarith
    · rw [if_neg hz] at hW
      rw [if_neg hz]
      generalize hId : ((if c Query.rowLocation then 1 else 0) +
          (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) : ℝ) = I
        at hI0 hW ⊢
      generalize GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε = Q' at hQQ hW
      have h1 : 11796480 * gbar * Q' * I ≤ 10 ^ 23 * gbar * GateODEBudget.qOf s T etaH etaD gbar ε *
          I := by
        have h2 : Q' * I ≤ (2 * GateODEBudget.qOf s T etaH etaD gbar ε) * I :=
          mul_le_mul_of_nonneg_right hQQ hI0
        have h3 : 0 ≤ GateODEBudget.qOf s T etaH etaD gbar ε * I :=
          mul_nonneg (by linarith) hI0
        have h4 : 11796480 * (Q' * I) ≤ 10 ^ 23 * (GateODEBudget.qOf s T etaH etaD gbar ε * I) := by
          nlinarith
        have h5 := mul_le_mul_of_nonneg_left h4 hg0
        nlinarith
      linarith
  · -- the guarantees
    intro x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs0 hsrc hacc hx0 hv hpx hpv hne hBud
    have hγ' : ¬ BZeroCase q.pub → q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD q.g q.ε := by
      intro hz
      have h := hγ
      rw [if_neg hz] at h
      exact h
    -- the public data is passed literally (not as the local definition `q`), so that the
    -- outcome has the types of the statement and the final unification is syntactic
    have o := (GeneralSparseODE.general_ode_outcome
      (odePubG k s D.s_le_pow b c0 etaH etaD T gbar ε r₀ rb) hq hγ' D (fun _ => false) hF.zero
      hF.dec srcC hsrcV x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs0 hsrc (hζs ζs hacc) hx0 hv hpx
      hpv hne hBud).mono (β' := ε) (by
        show ε / 250 ≤ ε
        linarith)
    rw [markEmb_eq_cleanAlong] at o
    exact ⟨⟨o.success_two_thirds, o.output_density, o.conditional_error⟩, o.trial_direction⟩

end

end ManuscriptConformance
