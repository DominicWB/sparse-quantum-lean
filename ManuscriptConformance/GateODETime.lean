import ManuscriptConformance.GateODE
import GateEfficientRemarks.ODE.ZeroReleasedTime
import RepresentedSampleODE.Gate.Binary
import SourceAccuracyODE.Time

/-!
# Conformance: Theorem `ode:thm:gates` (gate-efficient dissipative equations), time-dependent

Theorem `ode:thm:gates` for the time-dependent dissipative problem of
`ode:thm:time`, every `T ≥ 0`, in the native gate model of `GateDefs`, from the package's
uniform-mesh solver (`GateBitBudget.binary_ode_time_budget_bits`,
`GateRemarks.ODE.binary_ode_time_budget_bits_nonneg`; for represented samples of any sign and
source circuits within `ν`, `SourceAccuracyODE.binary_time_outcome_nonneg`):

* **Input.** Time-indexed binary sparse data `D` on a power-of-two mesh of `M = 2^m` slots
  (`D.matrix (x, r)` the represented sample at `t_r = r T/M`; `formal_binaryInput`, review item B),
  every sample with row and column Euclidean norms of its Hamiltonian and dissipative parts at most
  `η_H`, `η_D`; public parameters of at most `b_data` bits (`comp_bits`). The mesh is every
  power of two at least the coarsest admissible one, `2^m ≥ 2^{odeMesh …}` (`odeMesh`: the least
  exponent with `steps(τ, ν'/3) ≤ 2^m`, the package's own mesh condition; Theorem `ode:thm:gates`
  has "choose the common degree `d` and a power-of-two time mesh `M` from that lemma with `δ = ν`",
  the lemma being `ode:lem:gate-select`).
* **Source circuits.** The loading circuit `loadC` (the controlled loading `U_load` of the
  normalised data states) and the weight-preparation circuit `wpC` (`P_w`), within
  `ζ_s ≤ ν = ε/(10⁴ ḡ)` of their ideal forms on clean scratch; `G_src = |loadC| + 2 |wpC|` (`P_w`,
  the loading and `P_w†`) and `A_src = |Zs|`. Each circuit within `ν` is implied by the
  manuscript's combined implementation error `ν` of `P_w`, the loading and `P_w†` (`G_src(ν)`,
  before Theorem `ode:thm:gates`); the released analysis asks each within `ν'/6 = ν/24`, and
  `SourceAccuracyODE` certifies the same protocol for circuits within `ν` (every successful trial
  within `ε/100`).
* **Protocol.** The package's four-attempt protocol for the public data `odePubT …` (internal ratio
  `2ḡ`, accuracy `ε/2`; the public rescaling and arithmetic accuracy chosen inside), fixed before
  the instance: it depends only on the public data and the source circuits.
  Review item K: the source circuits are native circuits that may call only the matrix
  primitives, and the native model has no separate source-preparation oracle; one protocol
  therefore serves the instances whose sources these circuits prepare, and the manuscript's
  supplied source-preparation calls (before Theorem `ode:thm:gates`) are not modelled.
* **Conclusions.** Valid trials; at most `C ḡ [q P(𝔟) + G_src + A_src]` gates in every history and
  `P(𝔟) + C A_src` qubits, `P(x) = C (x+1)³`, with `q` of eq. `ode:eq:gate-q` and
  `𝔟 = b_data + log₂(N+1) + log₂(M+1) + log₂(m_src+1) + log₂((q ḡ + 1)/ε)` for the time mesh
  `M = 2^m` and the `m_src = 2^m` source nodes (the manuscript's `m`; eq.
  `ode:eq:gate-word-budget`); at most `C ḡ q` calls of each coherent sampled-time matrix oracle
  (none in the zero case) besides `C ḡ` times the calls inside the source circuits; heralded success
  at least `2/3`, conditional output within trace distance `ε` of `x(T)/‖x(T)‖`, and every
  successful trial within `ε` of it up to a global phase. The source
  preparations are native circuits, charged by their gates and the calls inside them; the number of
  their executions (the manuscript's `O(ḡ)` source-preparation calls) is not a separate count
  here; for the certificate endpoints it is counted by `ode_thm_gates_time_cert_sources` and
  `ode_thm_gates_time_decoder_cert_sources` (`SourceExecutions`).

**Represented samples of any sign.** Only the generator path is dissipative: the represented
samples need not have positive semidefinite dissipative parts (`RepresentedSampleODE.GateTime`: the
analysis runs on their positive repairs, the circuits on the samples), as in the manuscript.

**Special case.** `ode_thm_gates_time` is the special case of Theorem `ode:thm:gates` under the
package's uniform-mesh conditions (`formal_uniformMesh`); the conformance forms of the theorem are
`ode_thm_gates_time_cert` and `ode_thm_gates_time_decoder_cert` (`GateODETimeCert`).

**Formal restrictions** (in addition to `formal_binaryInput` and `formal_gbarOne`, `ḡ ≥ 1`):
`formal_uniformMesh`, the package's instance conditions `RepresentedSampleODE.GateTime.RobustRest`
(the released `PubT.Rest` with the certificate below):

* manuscript assumptions: unitary loading `U_load` (`load_unitary`) with the phase-consistent
  loading of the normalised initial state and forcing samples (`init_load`, `forcing_load`), a
  unitary weight preparation (`prep_left`, `prep_right`), the solution `x` of `ẋ = -G(t)x + b(t)`
  (`solves`) with a dissipative generator path (`accretive`), the generator's Lipschitz bound `β_G`
  (`lipG`; Lemma `ode:lem:gate-select`), `x(T) ≠ 0` (`target_ne`);
* restrictions of the package's model: the source quadrature is the left-point rule on the same
  uniform mesh (nodes `r T/M`, weights `T/M`), with the weight preparation's amplitudes
  `√(‖x₀‖/B_m)`, `√((T/M)‖b_r‖/B_m)` (`prep`); the amplification bound is taken on the discrete
  mass, `B_m ≤ ḡ ‖x(T)‖` (`budget`; the manuscript has `B ≤ ḡ ‖x(T)‖` and `B_m ≤ 2B`); and the
  certificate is the package's explicit discretisation bound `≤ ε B_m/(2000 ḡ)` at the sample error
  `3 δ_G` (`disc`) with the branch budget `6 R' T δ_G ≤ ν'` (`branch`, `R' = 4 log(8·10⁴ ḡ/ε)`; it
  bounds the dissipative part `R' T δ_G` of the represented-sample contribution
  `∑_r h_r ‖K̃_{k,r} - K_k(t_r)‖`, `|k| ≤ R'`, to the manuscript's branch certificate in the proof
  of Theorem `ode:thm:time`, after eq. `ode:eq:timedisc`) in place of the manuscript's source and
  sample certificates, with its inputs: a uniform bound `δ_G` on the represented generator samples
  at the slot times (`sampleG`; the lemma asks for an integrated error at the branch addresses), and
  for the forcing a Lipschitz bound `β_b`, the sample errors `δ_b` of the loaded forcing samples and
  a bound `b_max` on `‖b‖` (`lipb`, `sampleb`, `boundb`), where the manuscript asks of the forcing
  only the source certificates.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget
open SparseHamiltonian.GateBinaryODE (SZ4)
open SparseHamiltonian.GateBinaryODETime (PubT)
open SparseHamiltonian.ZeroTimeGateODE (btprepC BTPublicOK0 BTZeroCase)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

universe u v

/-! ### The public data of the time-dependent solver -/

/-- **The public data of the time-dependent gate solver** from the manuscript's public inputs and
the mesh exponent `m`, with the package's public choices: the rescaling
`γ = gammaOf T η_H η_D (2ḡ) (ε/2)` (`γ = 1` in the zero case) and the arithmetic accuracy
`ζ = ν'/(196608 q')` of the internal ratio `2ḡ` and accuracy `ε/2`. -/
def odePubT (k sb : ℕ) (hsb : sb ≤ k) (b : ℕ) (c0 etaH etaD T gbar ε : ℝ) (m : ℕ) : PubT where
  kx := k
  σ := sb
  hσ := hsb
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
    (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2))

/-- **The coarsest admissible mesh exponent** (the package's own mesh condition): the least `m₀`
with `steps τ (ν'/3) ≤ 2^m₀` for the common simulation time `τ` of the public rescaling (which does
not depend on the mesh). -/
def odeMesh (k sb : ℕ) (hsb : sb ≤ k) (b : ℕ) (c0 etaH etaD T gbar ε : ℝ) : ℕ :=
  Sim.simM (odePubT k sb hsb b c0 etaH etaD T gbar ε 0).params.tau
    (odePubT k sb hsb b c0 etaH etaD T gbar ε 0).params.nu

/-- The qubits of the time-dependent solver's register. -/
abbrev odeQubitsT (q : PubT) (Zs : Type) [Fintype Zs] : ℕ :=
  Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)

/-- **`formal_uniformMesh`**: the package's instance conditions `RobustRest` of the uniform-mesh
time-dependent solver with represented samples of any sign (the released `PubT.Rest` with the
discretisation budget at the sample error `3 δ_G` and the branch budget `6 R' T δ_G ≤ ν'`; see the
module docstring for the manuscript's assumptions it contains and its three restrictions: the
left-point source quadrature on the data mesh, the amplification bound on the discrete mass, and
the explicit discretisation certificate). -/
abbrev formal_uniformMesh {X n : Type*} [Fintype n] [DecidableEq n] (q : PubT)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n) (x : X)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf xs : ℝ → Reg (Fin q.kx) ℂ)
    (bs : ℕ → Reg (Fin q.kx) ℂ) (βG δG βb δb bmax : ℝ) : Prop :=
  RepresentedSampleODE.GateTime.RobustRest q D en x Jl Wp G bf xs bs βG δG βb δb bmax

theorem one_le_two_mul {g : ℝ} (h : 1 ≤ g) : 1 ≤ 2 * g := by linarith

/-- The public conditions of the package (`BTPublicOK0`, every `T ≥ 0`) hold for `odePubT` on
every mesh at least the coarsest admissible one. -/
theorem odePubT_ok {k sb : ℕ} (hsb : sb ≤ k) {b : ℕ} {c0 etaH etaD T gbar ε : ℝ} {m : ℕ}
    (hb : 0 < b) (hc0 : 0 < c0) (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hT : 0 ≤ T) (hg : 1 ≤ gbar)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hm : odeMesh k sb hsb b c0 etaH etaD T gbar ε ≤ m) :
    BTPublicOK0 (odePubT k sb hsb b c0 etaH etaD T gbar ε m) := by
  have hg2 : 1 ≤ 2 * gbar := by linarith
  have hε' : 0 < ε / 2 := by linarith
  have hε1' : ε / 2 ≤ 1 := by linarith
  have hν : 0 < ImprovedODEQueryBudget.precision (2 * gbar) (ε / 2) :=
    ImprovedODEQueryBudget.precision_pos _ _ hg2 hε'
  have hν1 : ImprovedODEQueryBudget.precision (2 * gbar) (ε / 2) ≤ 1 :=
    (ImprovedODEQueryBudget.precision_le_one_ten_thousandth _ _ hg2 hε1').trans (by norm_num)
  have hQ1 : 1 ≤ GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) :=
    GateRemarks.ODE.one_le_qOf hT hH hD hg2 hε' hε1'
  obtain ⟨hz0, hz1, -, -⟩ := zetaOf_spec hν hν1 hQ1
  have hγ : 0 < (if T = 0 ∨ etaH + etaD = 0 then (1 : ℝ) else
        GateODEBudget.gammaOf T etaH etaD (2 * gbar) (ε / 2)) ∧
      (if T = 0 ∨ etaH + etaD = 0 then (1 : ℝ) else
        GateODEBudget.gammaOf T etaH etaD (2 * gbar) (ε / 2)) ≤ 1 := by
    split_ifs with hz
    · exact ⟨one_pos, le_rfl⟩
    · push Not at hz
      have hT' : 0 < T := lt_of_le_of_ne hT (Ne.symm hz.1)
      have hE : 0 < etaH + etaD := lt_of_le_of_ne (by linarith) (Ne.symm hz.2)
      have hS : GateODEBudget.ShapeOK 1 T etaH etaD (2 * gbar) (ε / 2) :=
        ⟨le_rfl, hT', hH, hD, hE, hg2, hε', hε1'⟩
      exact ⟨hS.gammaOf_pos, GateODEBudget.gammaOf_le_one _ _ _ _ _⟩
  have hmesh : TimeSchedule.steps (odePubT k sb hsb b c0 etaH etaD T gbar ε m).params.tau
      ((odePubT k sb hsb b c0 etaH etaD T gbar ε m).params.nu / 3) ≤
      2 ^ (odePubT k sb hsb b c0 etaH etaD T gbar ε m).m := by
    have h1 := (Sim.simM_spec (odePubT k sb hsb b c0 etaH etaD T gbar ε 0).params.tau
      (odePubT k sb hsb b c0 etaH etaD T gbar ε 0).params.nu).1
    have h2 : 2 ^ odeMesh k sb hsb b c0 etaH etaD T gbar ε ≤ 2 ^ m :=
      Nat.pow_le_pow_right (by norm_num) hm
    exact h1.trans h2
  exact ⟨hb, hc0, hH, hD, hγ.1, hγ.2, hT, hg, hε, hε2, hz0, hz1, hmesh⟩

/-- The rescaling hypothesis of the package for `odePubT`. -/
theorem odePubT_gamma {q : PubT} {k sb : ℕ} {hsb : sb ≤ k} {b bd : ℕ}
    {c0 etaH etaD T gbar ε : ℝ} {m : ℕ} (hq : q = odePubT k sb hsb b c0 etaH etaD T gbar ε m)
    (hb : 0 < b) (hbd : b ≤ bd) :
    if BTZeroCase q then HasBits bd q.γ
    else q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := by
  subst hq
  by_cases hz : BTZeroCase (odePubT k sb hsb b c0 etaH etaD T gbar ε m)
  · rw [if_pos hz]
    have hz' : T = 0 ∨ etaH + etaD = 0 := hz
    show HasBits bd (if T = 0 ∨ etaH + etaD = 0 then (1 : ℝ) else
      GateODEBudget.gammaOf T etaH etaD (2 * gbar) (ε / 2))
    rw [if_pos hz']
    exact hasBits_one (by omega)
  · rw [if_neg hz]
    have hz' : ¬ (T = 0 ∨ etaH + etaD = 0) := hz
    show (if T = 0 ∨ etaH + etaD = 0 then (1 : ℝ) else
      GateODEBudget.gammaOf T etaH etaD (2 * gbar) (ε / 2)) =
      GateODEBudget.gammaOf T etaH etaD (2 * gbar) (ε / 2)
    rw [if_neg hz']

/-- The arithmetic-accuracy hypotheses of the package for `odePubT`: `ν' ≤ 196608 q' ζ`, and the
budget `98304 q' ζ + 3 ζ_s ≤ 13 ν'` of `SourceAccuracyODE` for every source accuracy
`ζ_s ≤ ν = 4 ν'`. -/
theorem odePubT_zeta {q : PubT} {k sb : ℕ} {hsb : sb ≤ k} {b : ℕ}
    {c0 etaH etaD T gbar ε : ℝ} {m : ℕ} (hq : q = odePubT k sb hsb b c0 etaH etaD T gbar ε m)
    (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hT : 0 ≤ T) (hg : 1 ≤ gbar) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    q.params.nu ≤ 196608 * GateODEBudget.qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ ∧
    ∀ ζs : ℝ, ζs ≤ ImprovedODEQueryBudget.precision gbar ε →
      98304 * GateODEBudget.qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ + 3 * ζs ≤
        13 * q.params.nu := by
  subst hq
  have hg2 : 1 ≤ 2 * gbar := by linarith
  have hε' : 0 < ε / 2 := by linarith
  have hε1' : ε / 2 ≤ 1 := by linarith
  have hν : 0 < ImprovedODEQueryBudget.precision (2 * gbar) (ε / 2) :=
    ImprovedODEQueryBudget.precision_pos _ _ hg2 hε'
  have hν1 : ImprovedODEQueryBudget.precision (2 * gbar) (ε / 2) ≤ 1 :=
    (ImprovedODEQueryBudget.precision_le_one_ten_thousandth _ _ hg2 hε1').trans (by norm_num)
  have hQ1 : 1 ≤ GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) :=
    GateRemarks.ODE.one_le_qOf hT hH hD hg2 hε' hε1'
  obtain ⟨-, -, hzν, hz2⟩ := zetaOf_spec hν hν1 hQ1
  refine ⟨hzν, fun ζs h => ?_⟩
  have hg0 : gbar ≠ 0 := (by linarith : (0 : ℝ) < gbar).ne'
  have e4 : ImprovedODEQueryBudget.precision gbar ε =
      4 * ImprovedODEQueryBudget.precision (2 * gbar) (ε / 2) := by
    rw [show ImprovedODEQueryBudget.precision gbar ε = ε / (10000 * gbar) from rfl,
      show ImprovedODEQueryBudget.precision (2 * gbar) (ε / 2) = ε / 2 / (10000 * (2 * gbar))
        from rfl]
    field_simp
    ring
  rw [e4] at h
  show 98304 * GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) *
      zetaOf (ImprovedODEQueryBudget.precision (2 * gbar) (ε / 2))
        (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2)) + 3 * ζs ≤
    13 * ImprovedODEQueryBudget.precision (2 * gbar) (ε / 2)
  linarith

/-! ### Theorem `ode:thm:gates`, time-dependent coefficients -/

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:gates`, time-dependent coefficients, special case under the package's
uniform-mesh conditions**. See the module docstring. With `C = 2·10²³`: for public data of at most
`b_data` bits, every `T ≥ 0`, `ḡ ≥ 1` and `0 < ε ≤ 1/2`, for every mesh `M = 2^m` at least the
coarsest admissible one (`odeMesh … ≤ m`), time-indexed binary sparse data on the mesh and valid
source circuits, the protocol `nprotocol (btprepC (odePubT …) loadC wpC) (2ḡ)` (fixed before the
instance) has
valid trials, at most `C ḡ [q (𝔟+1)³ + G_src + A_src]` elementary gates in every history, at most
`C (𝔟+1)³ + C A_src` qubits, at most `C ḡ q` calls of each matrix oracle (none if `T = 0` or
`η_H + η_D = 0`) besides `C ḡ` times the calls inside the source circuits, and on every
instance with the package's uniform-mesh conditions and source circuits within `ν = ε/(10⁴ ḡ)`:
success at least `2/3`, conditional output within trace distance `ε`, and every successful trial
within `ε` of `x(T)/‖x(T)‖` up to a global phase. The represented samples may have dissipative
parts of any sign. Formal restrictions: `formal_binaryInput`, `formal_gbarOne`,
`formal_uniformMesh`. The finite-gate-set bound with `G_src` entering linearly is a separate result
for the binary format (`N = 2^{k_x}`, `T > 0`, `η_H + η_D > 0`):
`GateSelective.binary_ode_time_budget_sel`. -/
theorem ode_thm_gates_time :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} [Fintype n] [DecidableEq n] {k b : ℕ} (sb bd : ℕ)
        (hsb : sb ≤ k) (c0 etaH etaD T gbar ε : ℝ),
        ∀ m : ℕ, odeMesh k sb hsb b c0 etaH etaD T gbar ε ≤ m →
        ∀ (D : Data (X × Fin (2 ^ m)) n (Cfg (VW b)) (2 ^ sb)) (en : Cfg (Fin k) ≃ n)
          (_ : formal_binaryInput D en sb c0) (_ : comp_bits b bd [c0, T, etaH, etaD])
          (hg : formal_gbarOne gbar)
          {Zs : Type} [Fintype Zs] [DecidableEq Zs]
          (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
          (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)),
          (∀ i ∈ loadC, i.Valid) → (∀ i ∈ wpC, i.Valid) →
          0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 →
          (∀ j, ∀ i ∈ trialN (btprepC (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC) j,
            i.Valid) ∧
          ((nprotocol (btprepC (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC) (2 * gbar)
              (one_le_two_mul hg)).worstCost wGateN : ℝ) ≤
            C * gbar * (odeShape ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε *
                (bitB bd (Fintype.card n) (2 ^ m) (2 ^ m)
                  (odeShape ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
              ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
          (odeQubitsT (odePubT k sb hsb b c0 etaH etaD T gbar ε m) Zs : ℝ) ≤
            C * (bitB bd (Fintype.card n) (2 ^ m) (2 ^ m)
              (odeShape ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
              C * Fintype.card Zs ∧
          (∀ c : Query → Bool,
            ((nprotocol (btprepC (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC)
              (2 * gbar) (one_le_two_mul hg)).worstCost (wCallN c) : ℝ) ≤
            (if T = 0 ∨ etaH + etaD = 0 then 0 else
              C * gbar * odeShape ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε *
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
            ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) loadC) (liftB (loadIdeal Jl)) ζs →
            ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) wpC) (liftB (matOp Wp)) ζs →
            ζs ≤ ImprovedODEQueryBudget.precision gbar ε →
            formal_uniformMesh (odePubT k sb hsb b c0 etaH etaD T gbar ε m) D en x Jl Wp G bf xs
              bs βG δG βb δb bmax →
            HeraldedOutput (nprotocol (btprepC (odePubT k sb hsb b c0 etaH etaD T gbar ε m)
                loadC wpC) (2 * gbar) (one_le_two_mul hg))
              (primsT (R := ℂ) D en x) (ODEStateNormalization.unitDirection (xs T)) ε ∧
            ∀ j : ℕ, ((goodN (S := Fin k))†) (nrun (primsT (R := ℂ) D en x)
                (trialN (btprepC (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC) j)
                  sN) ≠ 0 →
              ∃ ω : ℂ, ‖ω‖ = 1 ∧
                ‖ω • ODEStateNormalization.unitDirection (((goodN (S := Fin k))†)
                    (nrun (primsT (R := ℂ) D en x) (trialN (btprepC
                      (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC) j) sN)) -
                  ODEStateNormalization.unitDirection (xs T)‖ ≤ ε := by
  refine ⟨2 * 10 ^ 23, by norm_num, ?_⟩
  intro X n _ _ k b sb bd hsb c0 etaH etaD T gbar ε m hm D en hF hbits hg Zs _ _ loadC wpC hloadV
    hwpV hH hD hT hε hε2
  obtain ⟨hbd, hc0b, hTb, hHb, hDb⟩ := hbits
  have hg1 : 1 ≤ gbar := hg
  have hcard : Fintype.card n = 2 ^ k := card_eq_two_pow en
  rw [hcard]
  have hε1 : ε ≤ 1 := by linarith
  have hg0 : 0 ≤ gbar := by linarith
  have hq := odePubT_ok hsb hF.hb hF.hc0 hH hD hT hg hε hε2 hm
  have hγ := odePubT_gamma (q := odePubT k sb hsb b c0 etaH etaD T gbar ε m) rfl hF.hb hbd
  obtain ⟨hζ, hζs⟩ := odePubT_zeta (q := odePubT k sb hsb b c0 etaH etaD T gbar ε m) rfl
    hH hD hT hg hε hε2
  obtain ⟨-, -, -, -, -, -, hWC, -, hUg, hUq, hV, -⟩ :=
    GateRemarks.ODE.binary_ode_time_budget_bits_nonneg bd
      (odePubT k sb hsb b c0 etaH etaD T gbar ε m) hq hγ hζ hbd hc0b hTb hHb hDb D en
      hF.range hF.dec loadC hloadV wpC hwpV
  have hZ0 : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
  have hQ1 : 1 ≤ GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε :=
    GateRemarks.ODE.one_le_qOf hT hH hD hg hε hε1
  have hB0 : 0 ≤ bitB bd (2 ^ k) (2 ^ m) (2 ^ m)
      (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hY : 0 ≤ (bitB bd (2 ^ k) (2 ^ m) (2 ^ m)
      (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε + 1) ^ 3 :=
    pow_nonneg (by linarith) 3
  refine ⟨hV, ?_, ?_, ?_, ?_⟩
  · -- gates
    rw [odeShape_eq]
    have h : ((nprotocol (btprepC (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC)
        (2 * gbar) (one_le_two_mul hg)).worstCost wGateN : ℝ) ≤
        2 * 10 ^ 22 * gbar * (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε *
          (bitB bd (2 ^ k) (2 ^ m) (2 ^ m)
            (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
          ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) := hUg
    have hS0 : 0 ≤ GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε *
        (bitB bd (2 ^ k) (2 ^ m) (2 ^ m)
          (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs := by
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH
        etaD gbar ε) hY
      positivity
    have h2 : 2 * 10 ^ 22 * gbar * (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε *
          (bitB bd (2 ^ k) (2 ^ m) (2 ^ m)
            (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
          ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ≤
        2 * 10 ^ 23 * gbar * (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε *
          (bitB bd (2 ^ k) (2 ^ m) (2 ^ m)
            (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
          ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hg0) hS0
    exact h.trans h2
  · -- qubits
    rw [odeShape_eq]
    have h : (odeQubitsT (odePubT k sb hsb b c0 etaH etaD T gbar ε m) Zs : ℝ) ≤
        9 * 10 ^ 12 * (bitB bd (2 ^ k) (2 ^ m) (2 ^ m)
          (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
        2 * Fintype.card Zs := hUq
    have h1 : 9 * 10 ^ 12 * (bitB bd (2 ^ k) (2 ^ m) (2 ^ m)
        (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε + 1) ^ 3 ≤
        2 * 10 ^ 23 * (bitB bd (2 ^ k) (2 ^ m) (2 ^ m)
          (GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε + 1) ^ 3 :=
      mul_le_mul_of_nonneg_right (by norm_num) hY
    have h2 : 2 * (Fintype.card Zs : ℝ) ≤ 2 * 10 ^ 23 * Fintype.card Zs :=
      mul_le_mul_of_nonneg_right (by norm_num) hZ0
    linarith
  · -- calls
    intro c
    rw [odeShape_eq]
    have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
        (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    have hN0 : (0 : ℝ) ≤ (nCallsN c loadC : ℝ) + 2 * nCallsN c wpC := by positivity
    have h2 : 80 * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) ≤
        2 * 10 ^ 23 * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hg0) hN0
    have hc : ((nprotocol (btprepC (odePubT k sb hsb b c0 etaH etaD T gbar ε m) loadC wpC)
        (2 * gbar) (one_le_two_mul hg)).worstCost (wCallN c) : ℝ) ≤
        (if T = 0 ∨ etaH + etaD = 0 then 0 else 7864320 * gbar *
          GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) *
            ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
              (if c Query.value then 1 else 0))) +
        80 * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) := hWC c
    by_cases hz : T = 0 ∨ etaH + etaD = 0
    · rw [if_pos hz] at hc ⊢
      linarith
    · rw [if_neg hz] at hc ⊢
      push Not at hz
      have hT' : 0 < T := lt_of_le_of_ne hT (Ne.symm hz.1)
      have hE : 0 < etaH + etaD := lt_of_le_of_ne (by linarith) (Ne.symm hz.2)
      have hS : GateODEBudget.ShapeOK ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε :=
        ⟨by exact_mod_cast Nat.one_le_two_pow, hT', hH, hD, hE, hg, hε, hε1⟩
      have hq3 := qOf_two_le hS
      have hQ'0 : 0 ≤ GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) := by
        have hS2 : GateODEBudget.ShapeOK ((2 ^ sb : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) :=
          ⟨by exact_mod_cast Nat.one_le_two_pow, hT', hH, hD, hE, by linarith, by linarith,
            by linarith⟩
        linarith [hS2.one_le_q]
      have h1 : 7864320 * gbar *
          GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) *
            ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
              (if c Query.value then 1 else 0)) ≤
          2 * 10 ^ 23 * gbar * GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε *
            ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
              (if c Query.value then 1 else 0)) := by
        apply mul_le_mul_of_nonneg_right _ hI0
        have h3 : 7864320 * GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) ≤
            2 * 10 ^ 23 * GateODEBudget.qOf ((2 ^ sb : ℕ) : ℝ) T etaH etaD gbar ε := by
          nlinarith
        have h4 := mul_le_mul_of_nonneg_left h3 hg0
        linarith
      linarith
  · -- the guarantees
    intro x hrH hcH hrD hcD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs0 hload hwp hacc hR
    have hγ' : ¬ BTZeroCase (odePubT k sb hsb b c0 etaH etaD T gbar ε m) →
        (odePubT k sb hsb b c0 etaH etaD T gbar ε m).γ = GateODEBudget.gammaOf
          (odePubT k sb hsb b c0 etaH etaD T gbar ε m).T
          (odePubT k sb hsb b c0 etaH etaD T gbar ε m).etaH
          (odePubT k sb hsb b c0 etaH etaD T gbar ε m).etaD
          (2 * (odePubT k sb hsb b c0 etaH etaD T gbar ε m).g)
          ((odePubT k sb hsb b c0 etaH etaD T gbar ε m).ε / 2) := by
      intro hz
      have h := hγ
      rw [if_neg hz] at h
      exact h
    have o := (SourceAccuracyODE.binary_time_outcome_nonneg
      (odePubT k sb hsb b c0 etaH etaD T gbar ε m) hq hγ' D en hF.range hF.dec loadC hloadV wpC
      hwpV x hrH hcH hrD hcD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs0 hload hwp (hζs ζs hacc)
      hR).mono (show ε / 100 ≤ ε by linarith)
    exact ⟨⟨o.success_two_thirds, o.output_density, o.conditional_error⟩, o.trial_direction⟩

end

end ManuscriptConformance
