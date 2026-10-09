import GateEfficientODE.Time.Protocol
import GateEfficientODE.Theorem

/-!
# Gate-efficient dissipative ODE solver: time-dependent coefficients, exact gates

This is the time-dependent, exact-gate part of Theorem `ode:thm:gates` of
the manuscript: the problem `x' = -G(u) x + b(u)` on `[0, T]` with an
accretive, Lipschitz generator path, solved by an explicit circuit of
elementary gates and counted calls on a uniform time mesh of `2^m` slots.

**Access model.** The system is an abstract finite-dimensional Hilbert space
`P`.  The generator enters through represented slot samples
`G_r = L_r + i H_r` (`r < 2^m`, `L_r ≥ 0`, `‖H_r‖ ≤ λH`, `‖L_r‖ ≤ λD`) with
certified sample errors `‖G(rT/2^m) - G_r‖ ≤ δG`, and only through `U_J` and
the label- and slot-selected private Cayley operation: one call applies
`D z r` on every configuration whose solver wires carry the joint label `z`
and whose slot wires carry the slot `r`, where `D z r` satisfies the clock
promise of the released gate-level simulator for the normalised slot
Hamiltonian of the branch `z` (`TOracles`, `SelectHypT`).  The forcing
enters through samples `b_r` with `‖b(rT/2^m) - b_r‖ ≤ δb`.  The coherent
source loading `J s` (initial state on the label `(false, 0)`, the forcing
sample `b_q` on `(true, q)`) and the weight preparation `Wp` of the
source-label register (amplitudes `sqrt (‖z_s‖ / B)`, `B` the source mass)
are supplied unitaries whose calls are counted; the public payload
reflection about the seed vector is a separate counted instruction.  All
other operations are elementary gates: one-qubit unitaries with at most
three literal controls.

**The circuit.** Every branch is masked on the common mesh: the source
label `(ini, q)` starts its evolution at slot `0` (initial state) or at
slot `q` (forcing sample `b_q`, weight `T / 2^m`), and the LCHS label `w`
selects the frequency `k_w`.  The selected simulator runs the slot-selected
released simulator (`SlotSim.simCircuitT`) of the normalised slot
Hamiltonians `(T mask / τ) (H_r + k_w L_r)`, `τ = T (λH + R λD)`, with
step `τ / 2^m` per slot.  `TParams.prepC` is
`Wp · LCHS · LOAD · SELECT · PHASE · LCHS⁻¹ · Wp⁻¹`, one amplification step
is `R_good · prepC⁻¹ · R_seed · prepC · (-1)`, and the trial with `j` steps
is `trialC j = prepC · step^j`.  Internally the solver works with the ratio
`2 g` and the accuracy `ε / 2`; half of the direction error and half of the
normalisation are reserved for the time discretisation.  The LCHS register
holds the analytic Gaussian grid with growth constant `T λD`, padded to
`J + 2` labels of total coefficient mass three on `l = ⌈log₂ (J + 2)⌉`
wires.  The complete protocol (`TParams.protocol`) is the released bounded
four-attempt wrapper with a uniform trial count `j < chosenIterations (2g)`.

**Main theorem** (`solver`).  For public data satisfying `PublicOK`
(including the mesh condition `steps τ (ν/3) ≤ 2^m` of the simulator, see
`mesh_of_le`) and a unit seed `v`, the protocol, chosen before every unknown
instance:

* consists of valid elementary instructions only;
* uses, in every history including four failures, at most
  `80 g · prepGates + 40 g · reflGates` elementary gates, where
  `prepGates = 200 (d+1)(a+m+r+1) + 3 · 2^l (2l+1)` and
  `reflGates = 6 (2a + 4m + 6r + 4 + l) + 4`; at most `480 g d` private
  calls and `960 g d` calls of `U_J` or `U_J†`; at most `80 g` loading calls,
  `160 g` weight-preparation calls and `40 g` seed reflections;
* acts on `4a + 8m + 12r + 2l + 8` qubit wires and the system;
* has filter degree `d ≤ 128 (τ qbar + Q (1 + log (3/ν)))` with
  `ν = ε / (40000 g)`, `2^r ≤ 4 (d+1)`, `J + 2 ≤ 2^l < 2 (J + 2)` and
  `J ≤ R (T λD + 2 log (512/ν)) / π + 3`, where `R = 4 log (80000 g/ε)` and
  `512/ν = 20480000 g/ε` (`J_le_log`), so `J = O(ℓ (T λD + ℓ))`;
* for every instance satisfying `InstanceOK` (unitary oracles with the clock
  promises at every label and slot, the loading and weight-preparation
  promises, the represented and sampled data, a solution `x` with
  `x(T) ≠ 0`, the budget `B ≤ g ‖x(T)‖` and the discretisation budget
  `discretisation ≤ ε B / (2000 g)`) satisfies `Outcome`: success
  probability at least `175/256 > 2/3`, every successful trial within
  `ε / 500` of `x(T)/‖x(T)‖` up to a global phase, and a conditional output
  density operator within trace distance `ε` of `x(T) / ‖x(T)‖`.

`gate_count` simplifies the gate bound to
`18000 g ((d+1)(a+m+r+1) + (J+2)(l+1))`.  With exact samples
(`δG = δb = 0`) the discretisation error is
`T² / 2^m · (βG (‖x(0)‖ + bmax T) + βb + (λH + λD) bmax)`
(`discretisation_exact_samples`), so the discretisation budget is a lower
bound on the public mesh size `2^m`.

Not formalised here: synthesis of the rotation angles over a finite gate
set, entry decoding and arithmetic inside the matrix oracles, and the gate
costs of the supplied loading and weight-preparation unitaries.
-/

namespace SparseHamiltonian.GateODE.Time

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire simM simR fDeg simM_spec simR_spec)
open scoped InnerProduct BigOperators Real

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

namespace TParams

variable (p : TParams)

/-! ### Public sizes -/

theorem card_simWires :
    Fintype.card (Wire p.a p.m p.r p.K) = 2 * p.a + 3 * p.m + 6 * p.r + 3 := by
  have hK : p.K = p.a + p.m + 2 * p.r := rfl
  rw [GateCircuit.Sim.card_wire, hK]
  ring

/-- The number of qubit wires of the solver. -/
theorem card_W : Fintype.card p.W = 4 * p.a + 8 * p.m + 12 * p.r + 2 * p.l + 8 := by
  have h1 := p.card_simWires
  have h2 := card_oWire p.m p.l p.f
  have h3 : Fintype.card p.W =
      Fintype.card (Wire p.a p.m p.r p.K) + Fintype.card (OWire p.m p.l p.f) :=
    Fintype.card_sum
  have h4 : p.f = Fintype.card (Wire p.a p.m p.r p.K) + p.m + p.l := rfl
  omega

/-- The released degree bound of the filter. -/
theorem degree_bound (hp : p.PublicOK) :
    (p.d : ℝ) ≤ 128 * (p.tau * p.qbar + p.Q * (1 + Real.log (3 / p.nu))) := by
  have hν := hp.nu_pos
  have hν1 : p.nu ≤ 1 / 10000 :=
    ImprovedODEQueryBudget.precision_le_one_ten_thousandth p.ratio p.acc (p.ratio_ge hp.g_ge)
      (p.acc_le_one hp.eps_le_one)
  have h := SharpFilterSchedule.degree_le p.Q (p.tau * p.qbar) (p.nu / 3) hp.Q_ge
    (mul_nonneg hp.tau_pos.le hp.qbar_nonneg) (div_pos hν (by norm_num)) (by linarith)
  have e1 : (p.d : ℝ) = (SharpFilterSchedule.degree p.Q (p.tau * p.qbar) (p.nu / 3) : ℝ) := rfl
  have e2 : Real.log (3 / p.nu) = SharpFilterSchedule.logBudget (p.nu / 3) := by
    unfold SharpFilterSchedule.logBudget
    rw [one_div_div]
  rw [e1, e2]
  exact h

/-- The reuse-pointer and label registers of the simulator. -/
theorem r_bounds : 2 * p.d + 2 ≤ 2 ^ p.r ∧ 2 ^ p.r ≤ 4 * (p.d + 1) := by
  obtain ⟨h1, _, h2⟩ := simR_spec p.Q p.tau p.qbar p.nu
  exact ⟨h1, h2⟩

/-- The mesh condition holds for every mesh at least as fine as the
released simulator's schedule `2^(simM τ ν)`; `τ` and `ν` do not depend on
the mesh exponent. -/
theorem mesh_of_le (h : simM p.tau p.nu ≤ p.m) :
    TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m :=
  (simM_spec p.tau p.nu).1.trans (Nat.pow_le_pow_right (by norm_num) h)

/-- The LCHS label register holds the `J + 2` padded labels with less than
a factor two to spare. -/
theorem l_bounds : p.J + 2 ≤ 2 ^ p.l ∧ 2 ^ p.l < 2 * (p.J + 2) :=
  ⟨p.J_add_two_le, pow_clog_lt _ (by omega)⟩

/-- The analytic LCHS grid has `O(R (T λD + log (1/ν)))` labels. -/
theorem J_le (hp : p.PublicOK) :
    (p.J : ℝ) ≤ p.R * (p.T * p.lamD + 2 * Real.log (512 / p.nu)) / π + 3 :=
  AnalyticLCHS.gridSize_le hp.TD_nonneg (p.ratio_ge hp.g_ge) (p.acc_pos hp.ε_pos)
    (p.acc_le_one hp.eps_le_one)

/-- The grid bound in the public parameters: with `ℓ = log (g / ε)`,
`J = O(ℓ (T λD + ℓ))`. -/
theorem J_le_log (hp : p.PublicOK) :
    (p.J : ℝ) ≤ 4 * Real.log (80000 * p.g / p.ε) *
      (p.T * p.lamD + 2 * Real.log (20480000 * p.g / p.ε)) / π + 3 := by
  have h := p.J_le hp
  have h1 := hp.ε_pos
  have h2 : 0 < p.g := lt_of_lt_of_le one_pos hp.g_ge
  have e1 : p.R = 4 * Real.log (80000 * p.g / p.ε) := by
    show 4 * Real.log (20000 * (2 * p.g) / (p.ε / 2)) = _
    congr 2
    field_simp
    ring
  have e2 : 512 / p.nu = 20480000 * p.g / p.ε := by
    show 512 / ImprovedODEQueryBudget.precision (2 * p.g) (p.ε / 2) = _
    unfold ImprovedODEQueryBudget.precision
    field_simp
    ring
  rwa [e1, e2] at h

/-- The gate budget of one preparation, explicitly. -/
theorem prepGates_eq : p.prepGates =
    200 * (p.d + 1) * (p.a + p.m + p.r + 1) + 3 * (2 ^ p.l * (2 * p.l + 1)) :=
  rfl

/-- The gate budget of the reflections and the sign of one step, explicitly. -/
theorem reflGates_eq : p.reflGates = 6 * (2 * p.a + 4 * p.m + 6 * p.r + 4 + p.l) + 4 := by
  have h := p.card_simWires
  unfold reflGates nz
  omega

/-- With exact samples the certified discretisation error decays like
`T² / 2^m`. -/
theorem discretisation_exact_samples (βG βb bmax r₀ : ℝ) :
    p.discretisation βG 0 βb 0 bmax r₀ =
      p.T ^ 2 / p.M * (βG * (r₀ + bmax * p.T) + βb + (p.lamH + p.lamD) * bmax) := by
  unfold discretisation
  ring

/-- **A simplified worst-case gate count.** -/
theorem gate_count (hp : p.PublicOK) (v : P) (hv : ‖v‖ = 1) :
    ((p.protocol v hv hp.g_ge).worstCost p.wGate : ℝ) ≤
      18000 * p.g * (((p.d : ℝ) + 1) * ((p.a : ℝ) + p.m + p.r + 1) +
        ((p.J : ℝ) + 2) * ((p.l : ℝ) + 1)) := by
  have h := (p.protocol_worst hp v hv).1
  have hl := p.l_bounds.2
  have hg := hp.g_ge
  rw [p.prepGates_eq, p.reflGates_eq] at h
  generalize (p.protocol v hv hp.g_ge).worstCost p.wGate = W at h ⊢
  generalize p.d = D at h ⊢
  generalize p.a = A at h ⊢
  generalize p.m = M at h ⊢
  generalize p.r = R at h ⊢
  generalize p.l = L at h hl ⊢
  generalize p.J = J at h hl ⊢
  generalize p.g = g at h hg ⊢
  have hX : ((2 : ℝ) ^ L) ≤ 2 * ((J : ℝ) + 2) := by exact_mod_cast hl.le
  push_cast at h
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have h1 : (2 : ℝ) ^ L * (2 * L + 1) ≤ 2 * ((J : ℝ) + 2) * (2 * L + 1) :=
    mul_le_mul_of_nonneg_right hX (by positivity)
  have h2 : (0 : ℝ) ≤ D * (A + M + R + 1) := by positivity
  have h3 : (0 : ℝ) ≤ J * L := by positivity
  have hin : 80 * (200 * ((D : ℝ) + 1) * (A + M + R + 1) + 3 * (2 ^ L * (2 * L + 1))) +
        40 * (6 * (2 * (A : ℝ) + 4 * M + 6 * R + 4 + L) + 4) ≤
      18000 * (((D : ℝ) + 1) * (A + M + R + 1) + (J + 2) * (L + 1)) := by
    nlinarith
  calc (W : ℝ) ≤ g * (80 * (200 * ((D : ℝ) + 1) * (A + M + R + 1) + 3 * (2 ^ L * (2 * L + 1))) +
        40 * (6 * (2 * (A : ℝ) + 4 * M + 6 * R + 4 + L) + 4)) := by
        linarith
    _ ≤ g * (18000 * (((D : ℝ) + 1) * (A + M + R + 1) + (J + 2) * (L + 1))) :=
        mul_le_mul_of_nonneg_left hin (by linarith)
    _ = _ := by ring

/-- **The gate count with the analytic grid**: with
`J ≤ R (T λD + 2 log (512/ν)) / π + 3` substituted, every history uses at most
`18000 g ((d+1)(a+m+r+1) + (R (T λD + 2 log (512/ν)) / π + 5)(l+1))` gates. -/
theorem gate_count_grid (hp : p.PublicOK) (v : P) (hv : ‖v‖ = 1) :
    ((p.protocol v hv hp.g_ge).worstCost p.wGate : ℝ) ≤
      18000 * p.g * (((p.d : ℝ) + 1) * ((p.a : ℝ) + p.m + p.r + 1) +
        (p.R * (p.T * p.lamD + 2 * Real.log (512 / p.nu)) / π + 5) * ((p.l : ℝ) + 1)) := by
  have h := p.gate_count hp v hv
  have hJ := p.J_le hp
  have hl : (0 : ℝ) ≤ (p.l : ℝ) + 1 := by positivity
  have hg : 0 ≤ 18000 * p.g := by have := hp.g_ge; linarith
  have h1 : ((p.J : ℝ) + 2) * ((p.l : ℝ) + 1) ≤
      (p.R * (p.T * p.lamD + 2 * Real.log (512 / p.nu)) / π + 5) * ((p.l : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hl
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hg)
  linarith

end TParams

/-! ### The main theorem -/

/-- **Gate-efficient dissipative ODE solver, time-dependent coefficients,
exact gates.**  The protocol depends only on the public data `p` (including
the mesh exponent `m`) and the seed `v`; the instance
`(σ, H_r, L_r, G, b, x, b_r)` is quantified afterwards. -/
theorem solver [FiniteDimensional ℂ P] (p : TParams) (hp : p.PublicOK) (v : P)
    (hv : ‖v‖ = 1) :
    (∀ j, ∀ g ∈ p.trialC j, g.Valid Wire.anc) ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wGate : ℝ) ≤
      80 * p.g * p.prepGates + 40 * p.g * p.reflGates ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wPriv : ℝ) ≤ 480 * p.g * p.d ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wUJ : ℝ) ≤ 960 * p.g * p.d ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wLoad : ℝ) ≤ 80 * p.g ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wPrep : ℝ) ≤ 160 * p.g ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wSeed : ℝ) ≤ 40 * p.g ∧
    p.prepGates = 200 * (p.d + 1) * (p.a + p.m + p.r + 1) + 3 * (2 ^ p.l * (2 * p.l + 1)) ∧
    p.reflGates = 6 * (2 * p.a + 4 * p.m + 6 * p.r + 4 + p.l) + 4 ∧
    Fintype.card p.W = 4 * p.a + 8 * p.m + 12 * p.r + 2 * p.l + 8 ∧
    (p.d : ℝ) ≤ 128 * (p.tau * p.qbar + p.Q * (1 + Real.log (3 / p.nu))) ∧
    2 * p.d + 2 ≤ 2 ^ p.r ∧ 2 ^ p.r ≤ 4 * (p.d + 1) ∧
    p.J + 2 ≤ 2 ^ p.l ∧ 2 ^ p.l < 2 * (p.J + 2) ∧
    (p.J : ℝ) ≤ p.R * (p.T * p.lamD + 2 * Real.log (512 / p.nu)) / π + 3 ∧
    ∀ (σ : TOracles p.a p.m p.l P) (Hs Ls : ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P)
      (b x : ℝ → P) (bs : ℕ → P) (βG δG βb δb bmax : ℝ),
      p.InstanceOK v σ Hs Ls G b x bs βG δG βb δb bmax →
        p.Outcome v hv hp.g_ge σ (x p.T) := by
  obtain ⟨wG, wP, wU, wL, wW, wE⟩ := p.protocol_worst hp v hv
  obtain ⟨r1, r2⟩ := p.r_bounds
  obtain ⟨l1, l2⟩ := p.l_bounds
  exact ⟨p.trialC_valid hp.tau_pos.le hp.nu_pos hp.mesh, wG, wP, wU, wL, wW, wE,
    p.prepGates_eq, p.reflGates_eq, p.card_W, p.degree_bound hp, r1, r2, l1, l2, p.J_le hp,
    fun σ Hs Ls G b x bs βG δG βb δb bmax hI =>
      p.outcome hp v hv σ Hs Ls G b x bs βG δG βb δb bmax hI⟩

end

end SparseHamiltonian.GateODE.Time
