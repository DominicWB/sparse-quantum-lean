import ManuscriptConformance.GateODETime
import ManuscriptConformance.GateODEGeneral
import GeneralSparseODE.TimeBudget

/-!
# Conformance: Theorem `ode:thm:gates` for sparse access of general size, time-dependent

Theorem `ode:thm:gates` for the time-dependent dissipative problem of
`ode:thm:time`, every `T ≥ 0`, as `ode_thm_gates_time` (`GateODETime`), for the sparse access of
the manuscript in general sizes (`SparseHamiltonian.GeneralSparseAccess.QData`, Section
`hs:sec:control`, time-indexed: the sample of slot `r` on input `x` is `D.matrix (x, r)`, an `N × N`
matrix with `s`-sparse lists, `1 ≤ s ≤ N`, index registers of `k = ⌈log₂ N⌉` qubits, locators
prescribed on the valid list inputs only):

* **Input.** Time-indexed general sparse access `D` on a power-of-two mesh of `M = 2^m` slots,
  every sample with row and column Euclidean norms of its Hamiltonian and dissipative parts at
  most `η_H`, `η_D`; the stored words decoded as `c₀(X + iY)` (`formal_binaryDecoder`); public
  parameters of at most `b_data` bits (`comp_bits`). The mesh is every power of two at least the
  coarsest admissible one of the padded problem, `m ≥ odeMeshG …` (`odeMesh` of `GateODETime` for
  `k + 1` index bits and `⌈log₂ s⌉` slot bits).
* **Source circuits.** The loading circuit `loadC` (the controlled loading `U_load` on the `k`
  qubits of the index register) and the weight-preparation circuit `wpC` (`P_w`), calling the
  coherent sampled-time supplied oracles `primsTG D x`, within `ζ_s ≤ ν = ε/(10⁴ ḡ)` of their ideal
  forms on clean scratch; `G_src = |loadC| + 2 |wpC|` and `A_src = |Zs|`, as in
  `ode_thm_gates_time`.
* **Protocol.** The package's four-attempt protocol for the padded problem
  (`SparseHamiltonian.GeneralSparseODE.GPubT.prep`, public data `odePubTG …`): in the zero case
  (`T = 0` or `η_H + η_D = 0`) the direct source assembly, as in `ode_thm_gates_time`, otherwise
  the native preparation of the released time-dependent solver from binary data on the padded data
  `D.padData` (`k + 1`-bit index words, `2^⌈log₂ s⌉` slots), with every call of the padded oracles
  in its private operation replaced by the implementation from the supplied oracles
  (`GeneralSparseAccess.implP`: at most three supplied calls and `implG k b` gates, on clean
  ancillas in the private scratch; every call also reads the slot wires); the source circuits run
  on the low wires of the padded system register. It depends only on the public data and the
  source circuits. As in `ode_thm_gates_time` (review item K), the source circuits are native
  circuits charged by their gates and the calls inside them; the number of their executions is not
  a separate count here (it is for the certificate endpoints: `SourceExecutions`), and no
  source-preparation oracle is modelled.
* **Conclusions.** Valid trials; at most `C ḡ [q P(𝔟) + G_src + A_src]` gates in every history and
  `P(𝔟) + C A_src` qubits, `P(x) = C (x+1)³`, with `q` of eq. `ode:eq:gate-q` for the sparsity `s`
  and `𝔟 = b_data + log₂(N+1) + log₂(M+1) + log₂(m_src+1) + log₂((q ḡ + 1)/ε)` for the
  dimension `N`, the time mesh `M = 2^m` and the `m_src = 2^m` source nodes (the manuscript's `m`; eq.
  `ode:eq:gate-word-budget`); at most `C ḡ q` calls of each coherent sampled-time supplied matrix
  oracle (none in the zero case) besides `C ḡ` times the calls inside the source circuits; heralded
  success at least `2/3`, conditional output within trace distance `ε` of `x(T)/‖x(T)‖` on the
  index register with the marker qubit clean (the unit direction of
  `cleanAlong Fin.castSuccEmb (x(T))`, the output register being the `k + 1`-qubit padded index
  register), and every successful trial within `ε` of it up to a global phase.

**Represented samples of any sign** and the uniform-mesh conditions are those of
`ode_thm_gates_time` on the index register, for the released public parameters of the padded
problem (`formal_uniformMeshG`: the conditions `GeneralSparseODE.RobustRestG`, with the generator
path within `δ_G` of the lifts `GeneralSparseODE.padLift D (x, r)` of the samples extended by zero
to the index words `≥ N`). As for the mesh `odeMeshG`, the parameters `λ_H`, `λ_D` of their
discretisation condition are those of the `2^⌈log₂ s⌉` padded slots, so for `s` not a power of
two its `λ` term is up to `√2` larger than for `s` slots; the other parameters do not depend on
the sparsity.

**The problem on `ℂ^N`.** `padLift D (x, r)` is the sample on the valid index words and zero
elsewhere (`GeneralSparseODE.padLift_eq`). For a generator path `G'`, a forcing `c` and a
solution `y` of `y' = -G'(t) y + c(t)` on `ℂ^N`, the lifted path `validLift ∘ G'` and the
embedded forcing and solution `validEmb ∘ c`, `validEmb ∘ y` (`GeneralSparseODE.validEmb`: the
basis vector of `i` to that of the index word `binW k i`, an isometry) satisfy the conditions of
`RobustRestG` on the solution, the accretivity, the Lipschitz bound and the sample distances
whenever `G'`, `y` and the samples on `ℂ^N` do (`GeneralSparseODE.solves_validLift`,
`GeneralSparseODE.accretive_validLift`, `GeneralSparseODE.norm_validLift_sub_le`,
`GeneralSparseODE.norm_validLift_sub_padLift_le`); the target is then the clean embedding of
`validEmb (y(T)/‖y(T)‖)` (`GeneralSparseODE.unitDirection_validEmb`).

**Special case.** `ode_thm_gates_time_general` is the special case of Theorem `ode:thm:gates` under
the package's uniform-mesh conditions (`formal_uniformMeshG`); the conformance forms of the theorem
are `ode_thm_gates_time_cert` and `ode_thm_gates_time_decoder_cert` (`GateODETimeCert`).

**Formal restrictions.** `formal_binaryDecoder` (review item B2), `formal_gbarOne` and
`formal_uniformMeshG`; the sizes `N`, `s` and the locator lists are general (review item B).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GeneralSparseODE (GPubT markEmb padLift primsTG)
open SparseHamiltonian.GateBinaryODETime (PubT)
open SparseHamiltonian.ZeroTimeGateODE (BTPublicOK0 BTZeroCase)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

universe u

/-! ### The public data -/

/-- **The public data of the general time-dependent solver**: the index bits `k`, the sparsity
`s ≤ 2^k`, `b` stored bits, the manuscript's public inputs and the mesh exponent `m`, with the
package's public choices for the padded problem (`2^⌈log₂ s⌉` slots): the rescaling
`γ = gammaOf T η_H η_D (2ḡ) (ε/2)` (`γ = 1` in the zero case) and the arithmetic accuracy
`ζ = ν'/(196608 q')` of the internal ratio `2ḡ` and accuracy `ε/2`, `q'` the query shape of the
padded slot count. Reducible, so that its fields are those of the inputs up to reducible
unfolding (the system register `Fin ((odePubTG …).k + 1)` of the protocol is `Fin (k + 1)`). -/
abbrev odePubTG (k s : ℕ) (hs : s ≤ 2 ^ k) (b : ℕ) (c0 etaH etaD T gbar ε : ℝ) (m : ℕ) : GPubT where
  k := k
  s := s
  hs := hs
  b := b
  c0 := c0
  etaH := etaH
  etaD := etaD
  γ := if T = 0 ∨ etaH + etaD = 0 then 1
    else GateODEBudget.gammaOf T etaH etaD (2 * gbar) (ε / 2)
  T := T
  g := gbar
  ε := ε
  m := m
  ζ := zetaOf (ImprovedODEQueryBudget.precision (2 * gbar) (ε / 2))
    (GateODEBudget.qOf ((2 ^ sbP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2))

/-- The padded problem of `odePubTG` is the released public data `odePubT` of `k + 1` index bits
and `⌈log₂ s⌉` slot bits. -/
theorem odePubTG_pub (k s : ℕ) (hs : s ≤ 2 ^ k) (b : ℕ) (c0 etaH etaD T gbar ε : ℝ) (m : ℕ) :
    (odePubTG k s hs b c0 etaH etaD T gbar ε m).pub =
      odePubT (k + 1) (sbP s) ((sbP_le hs).trans (Nat.le_succ k)) b c0 etaH etaD T gbar ε m :=
  rfl

/-- **The coarsest admissible mesh exponent of the padded problem** (`odeMesh` for `k + 1` index
bits and `⌈log₂ s⌉` slot bits; the package's own mesh condition). -/
def odeMeshG (k s : ℕ) (hs : s ≤ 2 ^ k) (b : ℕ) (c0 etaH etaD T gbar ε : ℝ) : ℕ :=
  odeMesh (k + 1) (sbP s) ((sbP_le hs).trans (Nat.le_succ k)) b c0 etaH etaD T gbar ε

/-- The qubits of the general time-dependent solver's register. -/
abbrev odeQubitsTG (q : GPubT) (Zs : Type) [Fintype Zs] : ℕ := Fintype.card (q.reg Zs)

/-- **`formal_uniformMeshG`**: the instance conditions `GeneralSparseODE.RobustRestG` of the
uniform-mesh time-dependent solver on the index register (those of `formal_uniformMesh` with the
generator path within `δ_G` of the lifts `padLift D (x, r)` of the samples extended by zero to the
`2^k` index words; for sparse access of any stored bits `b`). -/
abbrev formal_uniformMeshG {X : Type*} {N : ℕ} (q : GPubT) {b : ℕ}
    (D : GeneralSparseAccess.QData (X × Fin (2 ^ q.m)) N q.s q.k b) (x : X)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : ℝ → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ) (bf xs : ℝ → Reg (Fin q.k) ℂ)
    (bs : ℕ → Reg (Fin q.k) ℂ) (βG δG βb δb bmax : ℝ) : Prop :=
  GeneralSparseODE.RobustRestG q D x Jl Wp G bf xs bs βG δG βb δb bmax

/-! ### Real estimates -/

/-- **The query shape of the internal ratio and accuracy** for every `T ≥ 0`:
`q*(2g, ε/2) ≤ 3 q*(g, ε)`. -/
theorem qOf_two_le0 {s T ηH ηD g ε : ℝ} (hs : 0 ≤ s) (hT : 0 ≤ T) (hH : 0 ≤ ηH) (hD : 0 ≤ ηD)
    (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    GateODEBudget.qOf s T ηH ηD (2 * g) (ε / 2) ≤ 3 * GateODEBudget.qOf s T ηH ηD g ε := by
  have hg0 : 0 < g := lt_of_lt_of_le one_pos hg
  have hℓ := ImprovedODEQueryBudget.logBudget_ge_one g ε hg hε hε1
  have e := logBudget_two g ε hg0 hε
  have hlog4 : Real.log 4 ≤ 2 := by
    have h1 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have := Real.log_two_lt_d9
    norm_num at this
    linarith
  have hlog40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hℓ' : ImprovedODEQueryBudget.logBudget (2 * g) (ε / 2) ≤
      3 * ImprovedODEQueryBudget.logBudget g ε := by
    rw [e]
    linarith
  have hℓ'0 : 0 ≤ ImprovedODEQueryBudget.logBudget (2 * g) (ε / 2) := by
    rw [e]
    linarith
  have hTH : 0 ≤ T * ηH := mul_nonneg hT hH
  have hTD : 0 ≤ T * ηD := mul_nonneg hT hD
  have hΘ : GateODEBudget.thetaOf T ηH ηD (2 * g) (ε / 2) ≤
      3 * GateODEBudget.thetaOf T ηH ηD g ε := by
    unfold GateODEBudget.thetaOf ImprovedODEQueryBudget.theta
    have := mul_le_mul_of_nonneg_left hℓ' hTD
    nlinarith
  have hΘ0 : 0 ≤ GateODEBudget.thetaOf T ηH ηD (2 * g) (ε / 2) := by
    unfold GateODEBudget.thetaOf ImprovedODEQueryBudget.theta
    positivity
  unfold GateODEBudget.qOf ImprovedODEQueryBudget.queryShape
  have h1 : Real.sqrt s * GateODEBudget.thetaOf T ηH ηD (2 * g) (ε / 2) ≤
      3 * (Real.sqrt s * GateODEBudget.thetaOf T ηH ηD g ε) := by
    have := mul_le_mul_of_nonneg_left hΘ (Real.sqrt_nonneg s)
    linarith
  have h2 : Real.sqrt (s * GateODEBudget.thetaOf T ηH ηD (2 * g) (ε / 2) *
      ImprovedODEQueryBudget.logBudget (2 * g) (ε / 2)) ≤
      3 * Real.sqrt (s * GateODEBudget.thetaOf T ηH ηD g ε *
        ImprovedODEQueryBudget.logBudget g ε) := by
    have h3 : s * GateODEBudget.thetaOf T ηH ηD (2 * g) (ε / 2) *
        ImprovedODEQueryBudget.logBudget (2 * g) (ε / 2) ≤
        9 * (s * GateODEBudget.thetaOf T ηH ηD g ε * ImprovedODEQueryBudget.logBudget g ε) := by
      have h4 := mul_le_mul hΘ hℓ' hℓ'0 (by
        have : 0 ≤ GateODEBudget.thetaOf T ηH ηD g ε := by
          unfold GateODEBudget.thetaOf ImprovedODEQueryBudget.theta
          have := mul_nonneg hTD (by linarith : (0 : ℝ) ≤ ImprovedODEQueryBudget.logBudget g ε)
          linarith
        linarith)
      have h5 := mul_le_mul_of_nonneg_left h4 hs
      nlinarith
    have h6 := Real.sqrt_le_sqrt h3
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9),
      show Real.sqrt 9 = 3 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      at h6
    exact h6
  linarith

/-- The word budget of the padded problem with the internal ratio and accuracy: `𝔟' ≤ 𝔟 + 5` for
`2^k < 2N` and `q' ≤ 6 q`. -/
theorem bitB_padT_le {bd k N M : ℕ} (hk : 2 ^ k < 2 * N) {Q Q' g ε : ℝ} (hQ : 0 ≤ Q)
    (hQQ : Q' ≤ 6 * Q) (hQ' : 0 ≤ Q') (hg : 0 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    bitB bd (2 ^ (k + 1)) M M Q' g ε ≤ bitB bd N M M Q g ε + 5 := by
  unfold bitB
  have h1 := logb_pow_succ_le hk
  have hX : 1 ≤ (Q * g + 1) / ε := by
    rw [le_div_iff₀ hε]
    have := mul_nonneg hQ hg
    linarith
  have hpos : 0 < (Q' * g + 1) / ε := by
    apply div_pos _ hε
    have := mul_nonneg hQ' hg
    linarith
  have h2 : (Q' * g + 1) / ε ≤ 8 * ((Q * g + 1) / ε) ^ 1 := by
    rw [pow_one, mul_div_assoc', div_le_div_iff_of_pos_right hε]
    have := mul_le_mul_of_nonneg_right hQQ hg
    have := mul_nonneg hQ hg
    nlinarith
  have h3 := logb_le_mul_pow _ 8 _ 3 1 hpos hX (by norm_num) h2
  push_cast at h3
  linarith

/-- `(𝔟' + 1)³ ≤ 216 (𝔟 + 1)³` for `𝔟' ≤ 𝔟 + 5`, `𝔟, 𝔟' ≥ 0`. -/
theorem cube_padT_le {B B' : ℝ} (hB : 0 ≤ B) (hB' : 0 ≤ B') (h : B' ≤ B + 5) :
    (B' + 1) ^ 3 ≤ 216 * (B + 1) ^ 3 := by
  have h1 : B' + 1 ≤ 6 * (B + 1) := by linarith
  have h2 : (B' + 1) ^ 3 ≤ (6 * (B + 1)) ^ 3 := pow_le_pow_left₀ (by linarith) h1 3
  have e : (6 * (B + 1)) ^ 3 = 216 * (B + 1) ^ 3 := by ring
  linarith

/-! ### Theorem `ode:thm:gates` for sparse access of general size, time-dependent coefficients -/

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:gates` for sparse access of general size, time-dependent coefficients,
special case under the package's uniform-mesh conditions**. See the module docstring. With
`C = 10²⁴`: for the time-indexed general sparse access `D` (`2^{k-1} < N ≤ 2^k`) with the decoder
`c₀(X + iY)` on a mesh `M = 2^m` at least the coarsest admissible one of the padded problem, public
parameters of at most `b_data` bits, every `T ≥ 0`, `ḡ ≥ 1`, `0 < ε ≤ 1/2` and valid loading and
weight-preparation circuits calling the coherent sampled-time supplied oracles, the protocol
`nprotocol ((odePubTG …).prep N 0 loadC wpC) (2ḡ)` (fixed before the instance) has valid trials, at
most `C ḡ [q (𝔟+1)³ + G_src + A_src]` elementary gates in every history (`q` for the sparsity `s`,
`𝔟 = b_data + log₂(N+1) + 2 log₂(M+1) + log₂((q ḡ + 1)/ε)`), at most `C (𝔟+1)³ + C A_src` qubits,
at most `C ḡ q` calls of each supplied matrix oracle (none if `T = 0` or `η_H + η_D = 0`) besides
`C ḡ` times the calls inside the source circuits, and on every instance with the uniform-mesh
conditions on the index register (for the public parameters of the padded problem) and source
circuits within `ν = ε/(10⁴ ḡ)`: success at least
`2/3`, conditional output within trace distance `ε` of `x(T)/‖x(T)‖` on the index register
(marker clean), and every successful trial within `ε` of it up to a global phase. The represented
samples may have dissipative parts of any sign. Formal restrictions: `formal_binaryDecoder`,
`formal_gbarOne`, `formal_uniformMeshG`. The finite-gate-set bound with `G_src` entering linearly is
a separate result for the binary format (`N = 2^{k_x}`, `T > 0`, `η_H + η_D > 0`):
`GateSelective.binary_ode_time_budget_sel`. -/
theorem ode_thm_gates_time_general :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (bd : ℕ) (c0 etaH etaD T gbar ε : ℝ) (m : ℕ)
        (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b),
        odeMeshG k s D.s_le_pow b c0 etaH etaD T gbar ε ≤ m →
        2 ^ k < 2 * N → formal_binaryDecoder D c0 → comp_bits b bd [c0, T, etaH, etaD] →
        ∀ (hg : formal_gbarOne gbar) {Zs : Type} [Fintype Zs] [DecidableEq Zs]
          (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
          (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)),
          (∀ i ∈ loadC, i.Valid) → (∀ i ∈ wpC, i.Valid) →
          0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 →
          (∀ j, ∀ i ∈ trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m).prep N
            (fun _ => false) loadC wpC) j, i.Valid) ∧
          ((nprotocol ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m).prep N
              (fun _ => false) loadC wpC) (2 * gbar) (one_le_two_mul hg)).worstCost wGateN : ℝ) ≤
            C * gbar * (odeShape s T etaH etaD gbar ε *
                (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
              ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
          (odeQubitsTG (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m) Zs : ℝ) ≤
            C * (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
              C * Fintype.card Zs ∧
          (∀ c : Query → Bool,
            ((nprotocol ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m).prep N
              (fun _ => false) loadC wpC) (2 * gbar) (one_le_two_mul hg)).worstCost
                (wCallN c) : ℝ) ≤
            (if T = 0 ∨ etaH + etaD = 0 then 0 else
              C * gbar * odeShape s T etaH etaD gbar ε *
                ((if c Query.rowLocation then 1 else 0) +
                  (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))) +
            C * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
          ∀ x : X,
            (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaH ^ 2) →
            (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaH ^ 2) →
            (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaD ^ 2) →
            (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaD ^ 2) →
            ∀ (Jl : Bool × (Fin m → Bool) → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
              (Wp : Matrix (Cfg (Fin (m + 1))) (Cfg (Fin (m + 1))) ℂ)
              (G : ℝ → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) (bf xs : ℝ → Reg (Fin k) ℂ)
              (bs : ℕ → Reg (Fin k) ℂ) (βG δG βb δb bmax ζs : ℝ),
            0 ≤ ζs →
            ApproxOn CleanX (nrun (primsTG D x) loadC) (liftB (loadIdeal Jl)) ζs →
            ApproxOn CleanX (nrun (primsTG D x) wpC) (liftB (matOp Wp)) ζs →
            ζs ≤ ImprovedODEQueryBudget.precision gbar ε →
            formal_uniformMeshG (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m) D x Jl Wp G
              bf xs bs βG δG βb δb bmax →
            HeraldedOutput (nprotocol ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m).prep N
                (fun _ => false) loadC wpC) (2 * gbar) (one_le_two_mul hg))
              (primsTG D x) (ODEStateNormalization.unitDirection
                (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (xs T))) ε ∧
            ∀ j : ℕ, ((goodN)†) (nrun (primsTG D x)
                (trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m).prep N
                  (fun _ => false) loadC wpC) j) sN) ≠ 0 →
              ∃ ω : ℂ, ‖ω‖ = 1 ∧
                ‖ω • ODEStateNormalization.unitDirection (((goodN)†)
                    (nrun (primsTG D x) (trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T gbar
                      ε m).prep N (fun _ => false) loadC wpC) j) sN)) -
                  ODEStateNormalization.unitDirection
                    (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (xs T))‖ ≤ ε := by
  refine ⟨10 ^ 24, by norm_num, ?_⟩
  intro X N s k b bd c0 etaH etaD T gbar ε m D hm hk hF hbits hg Zs _ _ loadC wpC hloadV hwpV hH
    hD hT hε hε2
  obtain ⟨hbd, hc0b, hTb, hHb, hDb⟩ := hbits
  have hg1 : 1 ≤ gbar := hg
  have hε1 : ε ≤ 1 := by linarith
  have hg0 : 0 ≤ gbar := by linarith
  set q := odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m with hqdef
  have hqp : q.pub = odePubT (k + 1) (sbP s) ((sbP_le D.s_le_pow).trans (Nat.le_succ k)) b c0
      etaH etaD T gbar ε m := rfl
  have hq : BTPublicOK0 q.pub := by
    rw [hqp]
    exact odePubT_ok _ hF.hb hF.hc0 hH hD hT hg hε hε2 hm
  have hγ := odePubT_gamma hqp hF.hb hbd
  obtain ⟨hζ, hζs⟩ := odePubT_zeta hqp hH hD hT hg hε hε2
  obtain ⟨hV, hWg0, hWq0, hWc0⟩ := GeneralSparseODE.general_time_budget bd q hq hγ hζ hbd hc0b
    hTb hHb hDb N (fun _ => false) loadC hloadV wpC hwpV
  have hWg : ((nprotocol (q.prep N (fun _ => false) loadC wpC) (2 * gbar)
      (one_le_two_mul hg)).worstCost wGateN : ℝ) ≤
      2 * 10 ^ 20 * gbar * (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) *
        (bitB bd (2 ^ (k + 1)) (2 ^ m) (2 ^ m)
          (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2)) gbar ε + 1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) := hWg0
  have hWq : (Fintype.card (q.reg Zs) : ℝ) ≤ 3 * 10 ^ 11 * (bitB bd (2 ^ (k + 1)) (2 ^ m) (2 ^ m)
      (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2)) gbar ε + 1) ^ 3 +
      2 * Fintype.card Zs := hWq0
  have hWc : ∀ c : Query → Bool, ((nprotocol (q.prep N (fun _ => false) loadC wpC) (2 * gbar)
      (one_le_two_mul hg)).worstCost (wCallN c) : ℝ) ≤ (if T = 0 ∨ etaH + etaD = 0 then 0 else
        23592960 * gbar * GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0))) +
        80 * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) := hWc0
  -- the query shapes and the word budgets
  have hsP : (((sP s : ℕ) : ℝ)) ≤ 2 * (s : ℝ) := by
    have h' : ((sP s : ℕ) : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast (sP_lt D.slots_pos).le
    push_cast at h'
    exact h'
  have hQQ1 : GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε ≤
      2 * GateODEBudget.qOf s T etaH etaD gbar ε :=
    qOf_le_of_le (Nat.cast_nonneg _) hsP hT hH hD hg hε hε1
  have hQQ2 : GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) ≤
      3 * GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε :=
    qOf_two_le0 (Nat.cast_nonneg _) hT hH hD hg hε hε1
  have hQQ : GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) ≤
      6 * GateODEBudget.qOf s T etaH etaD gbar ε := by linarith
  have hQ1 : 1 ≤ GateODEBudget.qOf s T etaH etaD gbar ε :=
    GateRemarks.ODE.one_le_qOf hT hH hD hg hε hε1
  have hQ1' : 1 ≤ GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) :=
    GateRemarks.ODE.one_le_qOf hT hH hD (by linarith) (by linarith) (by linarith)
  have hB0 : 0 ≤ bitB bd N (2 ^ m) (2 ^ m) (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hB0' : 0 ≤ bitB bd (2 ^ (k + 1)) (2 ^ m) (2 ^ m)
      (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2)) gbar ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hBB := bitB_padT_le (bd := bd) (M := 2 ^ m) hk (by linarith) hQQ (by linarith) hg0 hε hε1
  have hcube := cube_padT_le hB0 hB0' hBB
  have hY : 0 ≤ (bitB bd N (2 ^ m) (2 ^ m) (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε + 1) ^ 3 :=
    by positivity
  have hY' : 0 ≤ (bitB bd (2 ^ (k + 1)) (2 ^ m) (2 ^ m)
      (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2)) gbar ε + 1) ^ 3 := by
    positivity
  have hZ0 : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
  rw [odeShape_eq]
  refine ⟨hV, ?_, ?_, ?_, ?_⟩
  · -- gates
    refine hWg.trans ?_
    generalize GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) = Q'
      at hQQ hQ1' hcube hY' ⊢
    generalize GateODEBudget.qOf s T etaH etaD gbar ε = Q at hQQ hQ1 hcube hB0 hY ⊢
    generalize (bitB bd (2 ^ (k + 1)) (2 ^ m) (2 ^ m) Q' gbar ε + 1) ^ 3 = Y' at hcube hY' ⊢
    generalize (bitB bd N (2 ^ m) (2 ^ m) Q gbar ε + 1) ^ 3 = Y at hcube hY ⊢
    have hG0 : (0 : ℝ) ≤ (nGatesN loadC : ℝ) + 2 * nGatesN wpC := by positivity
    have h1 : Q' * Y' ≤ 1296 * (Q * Y) := by
      have h2 : Q' * Y' ≤ (6 * Q) * Y' := mul_le_mul_of_nonneg_right hQQ hY'
      have h3 : (6 * Q) * Y' ≤ (6 * Q) * (216 * Y) := mul_le_mul_of_nonneg_left hcube (by linarith)
      nlinarith
    have hQY : 0 ≤ Q * Y := mul_nonneg (by linarith) hY
    have h4 : (2 * 10 ^ 20 : ℝ) * gbar * (Q' * Y' + ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
        Fintype.card Zs) ≤ 2 * 10 ^ 20 * gbar * (1296 * (Q * Y) + ((nGatesN loadC : ℝ) +
          2 * nGatesN wpC) + Fintype.card Zs) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h5 : (2 * 10 ^ 20 : ℝ) * gbar * (1296 * (Q * Y) + ((nGatesN loadC : ℝ) +
          2 * nGatesN wpC) + Fintype.card Zs) ≤ 10 ^ 24 * gbar * (Q * Y +
          ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) := by
      have h6 : (2 * 10 ^ 20 : ℝ) * (1296 * (Q * Y) + ((nGatesN loadC : ℝ) +
          2 * nGatesN wpC) + Fintype.card Zs) ≤ 10 ^ 24 * (Q * Y +
          ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) := by
        nlinarith
      have := mul_le_mul_of_nonneg_left h6 hg0
      linarith
    exact h4.trans h5
  · -- qubits
    have h1 := mul_le_mul_of_nonneg_left hcube (by norm_num : (0 : ℝ) ≤ 3 * 10 ^ 11)
    have h2 : (2 : ℝ) * Fintype.card Zs ≤ 10 ^ 24 * Fintype.card Zs :=
      mul_le_mul_of_nonneg_right (by norm_num) hZ0
    have h3 : (3 * 10 ^ 11 : ℝ) * (216 * (bitB bd N (2 ^ m) (2 ^ m)
        (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε + 1) ^ 3) ≤ 10 ^ 24 * (bitB bd N (2 ^ m)
          (2 ^ m) (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε + 1) ^ 3 := by nlinarith
    have hq' : (odeQubitsTG q Zs : ℝ) = (Fintype.card (q.reg Zs) : ℝ) := rfl
    rw [hq']
    exact hWq.trans (add_le_add (h1.trans h3) h2)
  · -- calls
    intro c
    have hW := hWc c
    have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
        (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    have hS0 : (0 : ℝ) ≤ (nCallsN c loadC : ℝ) + 2 * nCallsN c wpC := by positivity
    have hS : 80 * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) ≤
        10 ^ 24 * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hg0) hS0
    by_cases hz : T = 0 ∨ etaH + etaD = 0
    · rw [if_pos hz] at hW
      rw [if_pos hz]
      exact hW.trans (add_le_add le_rfl hS)
    · rw [if_neg hz] at hW
      rw [if_neg hz]
      generalize hId : ((if c Query.rowLocation then 1 else 0) +
          (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) : ℝ) = I
        at hI0 hW ⊢
      generalize GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) = Q' at hQQ hW
      have h1 : 23592960 * gbar * Q' * I ≤ 10 ^ 24 * gbar * GateODEBudget.qOf s T etaH etaD gbar ε *
          I := by
        have h2 : Q' * I ≤ (6 * GateODEBudget.qOf s T etaH etaD gbar ε) * I :=
          mul_le_mul_of_nonneg_right hQQ hI0
        have h3 : 0 ≤ GateODEBudget.qOf s T etaH etaD gbar ε * I :=
          mul_nonneg (by linarith) hI0
        have h4 : 23592960 * (Q' * I) ≤ 10 ^ 24 * (GateODEBudget.qOf s T etaH etaD gbar ε * I) := by
          nlinarith
        have h5 := mul_le_mul_of_nonneg_left h4 hg0
        nlinarith
      exact hW.trans (add_le_add h1 hS)
  · -- the guarantees
    intro x hrH hcH hrD hcD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs0 hload hwp hacc hR
    have hγ' : ¬ BTZeroCase q.pub →
        q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := by
      intro hz
      have h := hγ
      rw [if_neg hz] at h
      exact h
    -- the public data is passed literally (not as the local definition `q`), so that the
    -- outcome has the types of the statement and the final unification is syntactic
    have o := (GeneralSparseODE.general_time_outcome
      (odePubTG k s D.s_le_pow b c0 etaH etaD T gbar ε m) hq hγ' D (fun _ => false) hF.zero
      hF.dec loadC hloadV wpC hwpV x hrH hcH hrD hcD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs0
      hload hwp (hζs ζs hacc) hR).mono (β' := ε) (by
        show ε / 100 ≤ ε
        linarith)
    rw [markEmb_eq_cleanAlong] at o
    exact ⟨⟨o.success_two_thirds, o.output_density, o.conditional_error⟩, o.trial_direction⟩

end

end ManuscriptConformance
