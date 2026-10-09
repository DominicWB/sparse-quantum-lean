import ZeroTimeGateODE.Exact
import ZeroTimeGateODE.ExactTimeSolver

/-!
# The exact-gate solvers for every `T ≥ 0`

The released exact-gate solvers `GateODE.solver` and `GateODE.Time.solver` take public data
with `T > 0` and `λ_H + R λ_D > 0`.  For every `T ≥ 0` (`PublicOK0`, `TPublicOK0`), the trial
circuits are the zero-case trials in the zero case and the released trials otherwise
(`ctrialE`, `ctrialET`), with the corresponding four-attempt protocols (`cprotocolE`,
`cprotocolET`):

* `exact_ode_solver_nonneg`: valid trials; worst-case counts
  `if ZeroCase p then 40 g · 2 + 20 g · reflGates else 40 g · prepGates + 20 g · reflGates`
  gates, `if ZeroCase p then 0 else 240 g d` private calls, `if ZeroCase p then 0 else 480 g d`
  calls of `U_J`, `40 g` calls of each source interface and `20 g` seed reflections; every size
  conclusion of the released `GateODE.solver` (`sizes_of_publicOK0`: the gate budgets, the
  degree bound, the mesh, register, grid and node bounds, all for every `T ≥ 0`); the
  guarantees `COutcome` under `ZInstanceOK` in the zero case and the released `InstanceOK`
  otherwise;
* `exact_ode_time_solver_nonneg`: the same for time-dependent coefficients (ratio `2g`, the
  size conclusions of the released `GateODE.Time.solver`, `tsizes_of_publicOK0`), with
  `TZInstanceOK` in the zero case.

In the zero case the size conclusions concern the released circuit, which the protocol does not
use; they make the positive case carry every conclusion of the released theorems.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.ZeroTimeGateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire)
open GateODE (Params Label Oracles wiring run seedState goodF)
open GateODE.Time (TParams TOracles trun)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Constant coefficients -/

section Constant

variable (p : Params)

/-- **The exact-gate trials for every `T ≥ 0`**: the zero-case trials in the zero case, the
released trials otherwise. -/
def ctrialE (j : ℕ) : List p.Ins := if ZeroCase p then ztrialE p j else p.trialC j

/-- **The exact-gate protocol for every `T ≥ 0`.** -/
def cprotocolE (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) :
    ODERepeatProtocol.Protocol (GateODE.family (wiring (a := p.a) (m := p.m) (r := p.r)
      (K := p.K) (k := p.k) (l := p.l) (f := p.f) v)) P :=
  if ZeroCase p then zprotocol p v hv hg else p.protocol v hv hg

/-- **The released size conclusions of `GateODE.solver` for every `T ≥ 0`**: under
`PublicOK0 p`, the explicit gate budget `prepGates` of the released preparation, the degree
bound of the released filter, the bounds on the mesh, reuse-pointer and label registers of the
released simulator, on the LCHS label register and grid size, and on the quadrature-node
register (the released proofs, with `0 ≤ τ` in place of `0 < τ`). -/
theorem sizes_of_publicOK0 (hp : PublicOK0 p) :
    p.prepGates =
      200 * (p.d + 1) * (p.a + p.m + p.r + 1) + 2 * (p.k + 1) + 3 * (2 ^ p.l * (2 * p.l + 1)) ∧
    (p.d : ℝ) ≤ 128 * (p.tau * p.qbar + p.Q * (1 + Real.log (3 / p.nu))) ∧
    TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m ∧
    2 ^ p.m < 2 * TimeSchedule.steps p.tau (p.nu / 3) ∧
    2 * p.d + 2 ≤ 2 ^ p.r ∧ 2 ^ p.r ≤ 4 * (p.d + 1) ∧
    p.J + 2 ≤ 2 ^ p.l ∧ 2 ^ p.l < 2 * (p.J + 2) ∧
    (p.J : ℝ) ≤ p.R * (p.T * p.lamD + 2 * Real.log (512 / p.nu)) / Real.pi + 3 ∧
    p.T * (p.lamH + p.lamD) ≤ p.nu * 2 ^ p.k ∧
    2 ^ p.k < 2 * (⌈p.T * (p.lamH + p.lamD) / p.nu⌉₊ + 1) := by
  have hν : 0 < p.nu := ImprovedODEQueryBudget.precision_pos p.g p.ε hp.g_ge hp.ε_pos
  have hν1 : p.nu ≤ 1 / 10000 := ImprovedODEQueryBudget.precision_le_one_ten_thousandth p.g p.ε
    hp.g_ge (hp.ε_half.trans (by norm_num))
  have hR : 0 < p.R := GateODE.AnalyticLCHS.radius_pos hp.g_ge hp.ε_pos
    (hp.ε_half.trans (by norm_num))
  have hτ : 0 ≤ p.tau :=
    mul_nonneg hp.T_nonneg (add_nonneg hp.lamH_nonneg (mul_nonneg hR.le hp.lamD_nonneg))
  have hdeg : (p.d : ℝ) ≤ 128 * (p.tau * p.qbar + p.Q * (1 + Real.log (3 / p.nu))) := by
    have h := SharpFilterSchedule.degree_le p.Q (p.tau * p.qbar) (p.nu / 3) hp.Q_ge
      (mul_nonneg hτ hp.qbar_nonneg) (by positivity) (by linarith)
    have e1 : (p.d : ℝ) = (SharpFilterSchedule.degree p.Q (p.tau * p.qbar) (p.nu / 3) : ℝ) :=
      rfl
    have e2 : Real.log (3 / p.nu) = SharpFilterSchedule.logBudget (p.nu / 3) := by
      unfold SharpFilterSchedule.logBudget
      rw [one_div_div]
    rw [e1, e2]
    exact h
  obtain ⟨s1, s2, s3, s4⟩ := p.sim_sizes
  obtain ⟨l1, l2⟩ := p.l_bounds
  obtain ⟨k1, k2⟩ := p.k_bounds hν
  exact ⟨p.prepGates_eq, hdeg, s1, s2, s3, s4, l1, l2,
    GateODE.AnalyticLCHS.gridSize_le (mul_nonneg hp.T_nonneg hp.lamD_nonneg) hp.g_ge hp.ε_pos
      (hp.ε_half.trans (by norm_num)), k1, k2⟩

variable [FiniteDimensional ℂ P]

/-- The guarantees of the exact-gate protocol for every `T ≥ 0` for one instance (the fields of
the released `GateODE.Params.Outcome` for `ctrialE` and `cprotocolE`). -/
structure COutcome (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) (σ : Oracles p.a (Label p.k p.l) P)
    (x : P) : Prop where
  unitary_trials : ∀ j, IsUnitary (run (wiring v) σ (ctrialE p j))
  mean_success : (1 : ℝ) / 4 ≤
    (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations p.g),
      ‖ODEHeraldedSuccess.successProjector goodF
        (run (wiring v) σ (ctrialE p j) (seedState v))‖ ^ 2) /
      (ODEGroverAverage.chosenIterations p.g : ℝ)
  trial_direction : ∀ j : ℕ, (goodF†) (run (wiring v) σ (ctrialE p j) (seedState v)) ≠ 0 →
    ∃ ω : ℂ, ‖ω‖ = 1 ∧
      ‖ω • unitDirection ((goodF†) (run (wiring v) σ (ctrialE p j) (seedState v))) -
        unitDirection x‖ ≤ p.ε / 500
  success_lower : (175 : ℝ) / 256 ≤ (cprotocolE p v hv hg).successMass σ
  success_two_thirds : (2 : ℝ) / 3 ≤ (cprotocolE p v hv hg).successMass σ
  output_density : ODEMixedOutput.IsDensity ((cprotocolE p v hv hg).conditionalDensity σ)
  conditional_error :
    ∃ h : ((cprotocolE p v hv hg).conditionalDensity σ -
        ODEMixedOutput.pureOperator (unitDirection x)).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance ((cprotocolE p v hv hg).conditionalDensity σ)
        (ODEMixedOutput.pureOperator (unitDirection x)) h ≤ p.ε

/-- **Gate-efficient dissipative ODE solver with exact gates for every `T ≥ 0`, constant
coefficients** (Theorem `ode:thm:gates`, exact gates, with its remark on zero time and a known
zero generator).

For public data `p` with `PublicOK0 p` and a unit seed `v`, the protocol `cprotocolE p v` on the
released wires has valid trials and, in every history, at most
`if ZeroCase p then 40 g · 2 + 20 g · reflGates else 40 g · prepGates + 20 g · reflGates`
elementary gates, `if ZeroCase p then 0 else 240 g d` private calls,
`if ZeroCase p then 0 else 480 g d` calls of `U_J` or `U_J†`, at most `40 g` calls of each source
interface and `20 g` seed reflections; every size conclusion of the released `GateODE.solver`
holds (`prepGates`, `reflGates` and the number of wires explicitly, the degree bound, the mesh,
reuse-pointer, label and node registers and the grid size; `sizes_of_publicOK0`).  For every
instance satisfying `ZInstanceOK` in the zero case and the released `GateODE.Params.InstanceOK`
otherwise, it has the guarantees `COutcome` against the released target `x(T)`. -/
theorem exact_ode_solver_nonneg (hp : PublicOK0 p) (v : P) (hv : ‖v‖ = 1) :
    (∀ j, ∀ g ∈ ctrialE p j, g.Valid Wire.anc) ∧
    ((cprotocolE p v hv hp.g_ge).worstCost p.wGate : ℝ) ≤
      (if ZeroCase p then 40 * p.g * 2 + 20 * p.g * p.reflGates
      else 40 * p.g * p.prepGates + 20 * p.g * p.reflGates) ∧
    ((cprotocolE p v hv hp.g_ge).worstCost p.wPriv : ℝ) ≤
      (if ZeroCase p then 0 else 240 * p.g * p.d) ∧
    ((cprotocolE p v hv hp.g_ge).worstCost p.wUJ : ℝ) ≤
      (if ZeroCase p then 0 else 480 * p.g * p.d) ∧
    (∀ c, ((cprotocolE p v hv hp.g_ge).worstCost (p.wSrc c) : ℝ) ≤ 40 * p.g) ∧
    ((cprotocolE p v hv hp.g_ge).worstCost p.wSeed : ℝ) ≤ 20 * p.g ∧
    p.prepGates =
      200 * (p.d + 1) * (p.a + p.m + p.r + 1) + 2 * (p.k + 1) + 3 * (2 ^ p.l * (2 * p.l + 1)) ∧
    p.reflGates = 6 * (2 * p.a + 3 * p.m + 6 * p.r + 4 + p.k + p.l) + 4 ∧
    Fintype.card p.W = 4 * p.a + 6 * p.m + 12 * p.r + 2 * p.k + 2 * p.l + 8 ∧
    (p.d : ℝ) ≤ 128 * (p.tau * p.qbar + p.Q * (1 + Real.log (3 / p.nu))) ∧
    TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m ∧
    2 ^ p.m < 2 * TimeSchedule.steps p.tau (p.nu / 3) ∧
    2 * p.d + 2 ≤ 2 ^ p.r ∧ 2 ^ p.r ≤ 4 * (p.d + 1) ∧
    p.J + 2 ≤ 2 ^ p.l ∧ 2 ^ p.l < 2 * (p.J + 2) ∧
    (p.J : ℝ) ≤ p.R * (p.T * p.lamD + 2 * Real.log (512 / p.nu)) / Real.pi + 3 ∧
    p.T * (p.lamH + p.lamD) ≤ p.nu * 2 ^ p.k ∧
    2 ^ p.k < 2 * (⌈p.T * (p.lamH + p.lamD) / p.nu⌉₊ + 1) ∧
    ∀ (σ : Oracles p.a (Label p.k p.l) P) (H L : P →L[ℂ] P) (x0 b : P),
      (if ZeroCase p then ZInstanceOK p v σ.J H L x0 b else p.InstanceOK v σ H L x0 b) →
        COutcome p v hv hp.g_ge σ (p.target H L x0 b) := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11⟩ := sizes_of_publicOK0 p hp
  by_cases hz : ZeroCase p
  · obtain ⟨hV, wG, wP, wU, wS, wE, hR, hC, hout⟩ := exact_ode_solver_zero p hp hz v hv
    have e1 : ∀ j, ctrialE p j = ztrialE p j := fun j => if_pos hz
    have e2 : cprotocolE p v hv hp.g_ge = zprotocol p v hv hp.g_ge := if_pos hz
    refine ⟨fun j => ?_, ?_, ?_, ?_, fun c => ?_, ?_, z1, hR, hC, z2, z3, z4, z5, z6, z7, z8,
      z9, z10, z11, ?_⟩
    · rw [e1]
      exact hV j
    · rw [e2, if_pos hz]
      exact wG
    · rw [e2, if_pos hz, wP]
      simp
    · rw [e2, if_pos hz, wU]
      simp
    · rw [e2]
      exact wS c
    · rw [e2]
      exact wE
    · intro σ H L x0 b hI
      rw [if_pos hz] at hI
      have h := hout σ H L x0 b hI
      refine ⟨fun j => ?_, ?_, fun j => ?_, ?_, ?_, ?_, ?_⟩
      · rw [e1]
        exact h.unitary_trials j
      · simp only [e1]
        exact h.mean_success
      · rw [e1]
        exact h.trial_direction j
      · rw [e2]
        exact h.success_lower
      · rw [e2]
        exact h.success_two_thirds
      · rw [e2]
        exact h.output_density
      · rw [e2]
        exact h.conditional_error
  · have hP := publicOK_of hp hz
    obtain ⟨wG, wP, wU, wS, wE⟩ := p.protocol_worst hP v hv
    have e1 : ∀ j, ctrialE p j = p.trialC j := fun j => if_neg hz
    have e2 : cprotocolE p v hv hp.g_ge = p.protocol v hv hP.g_ge := if_neg hz
    refine ⟨fun j => ?_, ?_, ?_, ?_, fun c => ?_, ?_, z1, p.reflGates_eq, p.card_W, z2, z3, z4,
      z5, z6, z7, z8, z9, z10, z11, ?_⟩
    · rw [e1]
      exact p.trialC_valid hP.tau_pos.le hP.nu_pos hP.r₀_nonneg hP.rb_nonneg hP.T_pos.le hP.B_pos
        j
    · rw [e2, if_neg hz]
      exact wG
    · rw [e2, if_neg hz]
      exact wP
    · rw [e2, if_neg hz]
      exact wU
    · rw [e2]
      exact wS c
    · rw [e2]
      exact wE
    · intro σ H L x0 b hI
      rw [if_neg hz] at hI
      have h := p.outcome hP v hv σ H L x0 b hI
      refine ⟨fun j => ?_, ?_, fun j => ?_, ?_, ?_, ?_, ?_⟩
      · rw [e1]
        exact h.unitary_trials j
      · simp only [e1]
        exact h.mean_success
      · rw [e1]
        exact h.trial_direction j
      · rw [e2]
        exact h.success_lower
      · rw [e2]
        exact h.success_two_thirds
      · rw [e2]
        exact h.output_density
      · rw [e2]
        exact h.conditional_error

end Constant

/-! ### Time-dependent coefficients -/

section Time

variable (p : TParams)

/-- **The exact-gate time-dependent trials for every `T ≥ 0`.** -/
def ctrialET (j : ℕ) : List p.Ins := if TZeroCase p then tztrialE p j else p.trialC j

/-- **The exact-gate time-dependent protocol for every `T ≥ 0`.** -/
def cprotocolET (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) :
    ODERepeatProtocol.Protocol (GateODE.Time.tfamily (a := p.a) (m := p.m) (r := p.r)
      (K := p.K) (k := p.m) (l := p.l) (f := p.f) v) P :=
  if TZeroCase p then tzprotocol p v hv hg else p.protocol v hv hg

/-- **The released size conclusions of `GateODE.Time.solver` for every `T ≥ 0`**: under
`TPublicOK0 p`, the explicit gate budget `prepGates` of the released preparation, the degree
bound of the released filter, the bounds on the reuse-pointer and label registers of the
released simulator, and on the LCHS label register and grid size (ratio `2g`, accuracy `ε/2`;
the released proofs, with `0 ≤ τ` in place of `0 < τ`). -/
theorem tsizes_of_publicOK0 (hp : TPublicOK0 p) :
    p.prepGates = 200 * (p.d + 1) * (p.a + p.m + p.r + 1) + 3 * (2 ^ p.l * (2 * p.l + 1)) ∧
    (p.d : ℝ) ≤ 128 * (p.tau * p.qbar + p.Q * (1 + Real.log (3 / p.nu))) ∧
    2 * p.d + 2 ≤ 2 ^ p.r ∧ 2 ^ p.r ≤ 4 * (p.d + 1) ∧
    p.J + 2 ≤ 2 ^ p.l ∧ 2 ^ p.l < 2 * (p.J + 2) ∧
    (p.J : ℝ) ≤ p.R * (p.T * p.lamD + 2 * Real.log (512 / p.nu)) / Real.pi + 3 := by
  have hεOne : p.ε ≤ 1 := hp.ε_half.trans (by norm_num)
  have hν : 0 < p.nu := p.nu_pos hp.g_ge hp.ε_pos
  have hν1 : p.nu ≤ 1 / 10000 :=
    ImprovedODEQueryBudget.precision_le_one_ten_thousandth p.ratio p.acc (p.ratio_ge hp.g_ge)
      (p.acc_le_one hεOne)
  have hR : 0 < p.R := GateODE.AnalyticLCHS.radius_pos (p.ratio_ge hp.g_ge) (p.acc_pos hp.ε_pos)
    (p.acc_le_one hεOne)
  have hτ : 0 ≤ p.tau :=
    mul_nonneg hp.T_nonneg (add_nonneg hp.lamH_nonneg (mul_nonneg hR.le hp.lamD_nonneg))
  have hdeg : (p.d : ℝ) ≤ 128 * (p.tau * p.qbar + p.Q * (1 + Real.log (3 / p.nu))) := by
    have h := SharpFilterSchedule.degree_le p.Q (p.tau * p.qbar) (p.nu / 3) hp.Q_ge
      (mul_nonneg hτ hp.qbar_nonneg) (by positivity) (by linarith)
    have e1 : (p.d : ℝ) = (SharpFilterSchedule.degree p.Q (p.tau * p.qbar) (p.nu / 3) : ℝ) :=
      rfl
    have e2 : Real.log (3 / p.nu) = SharpFilterSchedule.logBudget (p.nu / 3) := by
      unfold SharpFilterSchedule.logBudget
      rw [one_div_div]
    rw [e1, e2]
    exact h
  obtain ⟨r1, r2⟩ := p.r_bounds
  obtain ⟨l1, l2⟩ := p.l_bounds
  exact ⟨p.prepGates_eq, hdeg, r1, r2, l1, l2,
    GateODE.AnalyticLCHS.gridSize_le (mul_nonneg hp.T_nonneg hp.lamD_nonneg) (p.ratio_ge hp.g_ge)
      (p.acc_pos hp.ε_pos) (p.acc_le_one hεOne)⟩

variable [FiniteDimensional ℂ P]

/-- The guarantees of the exact-gate time-dependent protocol for every `T ≥ 0` for one instance
(the fields of the released `GateODE.Time.TParams.Outcome` for `ctrialET` and
`cprotocolET`). -/
structure CTOutcome (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) (σ : TOracles p.a p.m p.l P)
    (x : P) : Prop where
  unitary_trials : ∀ j, IsUnitary (trun v σ (ctrialET p j))
  mean_success : (1 : ℝ) / 4 ≤
    (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations p.ratio),
      ‖ODEHeraldedSuccess.successProjector goodF (trun v σ (ctrialET p j) (seedState v))‖ ^ 2) /
      (ODEGroverAverage.chosenIterations p.ratio : ℝ)
  trial_direction : ∀ j : ℕ, (goodF†) (trun v σ (ctrialET p j) (seedState v)) ≠ 0 →
    ∃ ω : ℂ, ‖ω‖ = 1 ∧
      ‖ω • unitDirection ((goodF†) (trun v σ (ctrialET p j) (seedState v))) -
        unitDirection x‖ ≤ p.ε / 500
  success_lower : (175 : ℝ) / 256 ≤ (cprotocolET p v hv hg).successMass σ
  success_two_thirds : (2 : ℝ) / 3 ≤ (cprotocolET p v hv hg).successMass σ
  output_density : ODEMixedOutput.IsDensity ((cprotocolET p v hv hg).conditionalDensity σ)
  conditional_error :
    ∃ h : ((cprotocolET p v hv hg).conditionalDensity σ -
        ODEMixedOutput.pureOperator (unitDirection x)).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance ((cprotocolET p v hv hg).conditionalDensity σ)
        (ODEMixedOutput.pureOperator (unitDirection x)) h ≤ p.ε

/-- **Gate-efficient dissipative ODE solver with exact gates for every `T ≥ 0`, time-dependent
coefficients** (Theorem `ode:thm:gates`, exact gates, time-dependent part, with its remark on
zero time and a known zero generator).

For public data `p` with `TPublicOK0 p` and a unit seed `v`, the protocol `cprotocolET p v`
(ratio `2g`) on the released wires has valid trials and, in every history, at most
`if TZeroCase p then 40 g · reflGates else 80 g · prepGates + 40 g · reflGates` elementary
gates, `if TZeroCase p then 0 else 480 g d` private calls, `if TZeroCase p then 0 else 960 g d`
calls of `U_J`, at most `80 g` loading calls, `160 g` weight-preparation calls and `40 g` seed
reflections; every size conclusion of the released `GateODE.Time.solver` holds (`prepGates`,
`reflGates` and the number of wires explicitly, the degree bound, the reuse-pointer and label
registers and the grid size; `tsizes_of_publicOK0`).  For every instance satisfying
`TZInstanceOK` in the zero case and the released `GateODE.Time.TParams.InstanceOK` otherwise, it
has the guarantees `CTOutcome` against `x(T)`. -/
theorem exact_ode_time_solver_nonneg (hp : TPublicOK0 p) (v : P) (hv : ‖v‖ = 1) :
    (∀ j, ∀ g ∈ ctrialET p j, g.Valid Wire.anc) ∧
    ((cprotocolET p v hv hp.g_ge).worstCost p.wGate : ℝ) ≤
      (if TZeroCase p then 40 * p.g * p.reflGates
      else 80 * p.g * p.prepGates + 40 * p.g * p.reflGates) ∧
    ((cprotocolET p v hv hp.g_ge).worstCost p.wPriv : ℝ) ≤
      (if TZeroCase p then 0 else 480 * p.g * p.d) ∧
    ((cprotocolET p v hv hp.g_ge).worstCost p.wUJ : ℝ) ≤
      (if TZeroCase p then 0 else 960 * p.g * p.d) ∧
    ((cprotocolET p v hv hp.g_ge).worstCost p.wLoad : ℝ) ≤ 80 * p.g ∧
    ((cprotocolET p v hv hp.g_ge).worstCost p.wPrep : ℝ) ≤ 160 * p.g ∧
    ((cprotocolET p v hv hp.g_ge).worstCost p.wSeed : ℝ) ≤ 40 * p.g ∧
    p.prepGates = 200 * (p.d + 1) * (p.a + p.m + p.r + 1) + 3 * (2 ^ p.l * (2 * p.l + 1)) ∧
    p.reflGates = 6 * (2 * p.a + 4 * p.m + 6 * p.r + 4 + p.l) + 4 ∧
    Fintype.card p.W = 4 * p.a + 8 * p.m + 12 * p.r + 2 * p.l + 8 ∧
    (p.d : ℝ) ≤ 128 * (p.tau * p.qbar + p.Q * (1 + Real.log (3 / p.nu))) ∧
    2 * p.d + 2 ≤ 2 ^ p.r ∧ 2 ^ p.r ≤ 4 * (p.d + 1) ∧
    p.J + 2 ≤ 2 ^ p.l ∧ 2 ^ p.l < 2 * (p.J + 2) ∧
    (p.J : ℝ) ≤ p.R * (p.T * p.lamD + 2 * Real.log (512 / p.nu)) / Real.pi + 3 ∧
    ∀ (σ : TOracles p.a p.m p.l P) (Hs Ls : ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P)
      (b x : ℝ → P) (bs : ℕ → P) (βG δG βb δb bmax : ℝ),
      (if TZeroCase p then TZInstanceOK p v σ.J σ.Wp Hs Ls G b x bs βG δG βb δb bmax
      else p.InstanceOK v σ Hs Ls G b x bs βG δG βb δb bmax) →
        CTOutcome p v hv hp.g_ge σ (x p.T) := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7⟩ := tsizes_of_publicOK0 p hp
  by_cases hz : TZeroCase p
  · obtain ⟨hV, wG, wP, wU, wL, wW, wE, hR, hC, hout⟩ :=
      exact_ode_time_solver_zero p hp hz v hv
    have e1 : ∀ j, ctrialET p j = tztrialE p j := fun j => if_pos hz
    have e2 : cprotocolET p v hv hp.g_ge = tzprotocol p v hv hp.g_ge := if_pos hz
    refine ⟨fun j => ?_, ?_, ?_, ?_, ?_, ?_, ?_, z1, hR, hC, z2, z3, z4, z5, z6, z7, ?_⟩
    · rw [e1]
      exact hV j
    · rw [e2, if_pos hz]
      exact wG
    · rw [e2, if_pos hz, wP]
      simp
    · rw [e2, if_pos hz, wU]
      simp
    · rw [e2]
      exact wL
    · rw [e2]
      exact wW
    · rw [e2]
      exact wE
    · intro σ Hs Ls G b x bs βG δG βb δb bmax hI
      rw [if_pos hz] at hI
      have h := hout σ Hs Ls G b x bs βG δG βb δb bmax hI
      refine ⟨fun j => ?_, ?_, fun j => ?_, ?_, ?_, ?_, ?_⟩
      · rw [e1]
        exact h.unitary_trials j
      · simp only [e1]
        exact h.mean_success
      · rw [e1]
        exact h.trial_direction j
      · rw [e2]
        exact h.success_lower
      · rw [e2]
        exact h.success_two_thirds
      · rw [e2]
        exact h.output_density
      · rw [e2]
        exact h.conditional_error
  · have hP := tpublicOK_of hp hz
    obtain ⟨wG, wP, wU, wL, wW, wE⟩ := p.protocol_worst hP v hv
    have e1 : ∀ j, ctrialET p j = p.trialC j := fun j => if_neg hz
    have e2 : cprotocolET p v hv hp.g_ge = p.protocol v hv hP.g_ge := if_neg hz
    refine ⟨fun j => ?_, ?_, ?_, ?_, ?_, ?_, ?_, z1, p.reflGates_eq, p.card_W, z2, z3, z4, z5, z6,
      z7, ?_⟩
    · rw [e1]
      exact p.trialC_valid hP.tau_pos.le hP.nu_pos hP.mesh j
    · rw [e2, if_neg hz]
      exact wG
    · rw [e2, if_neg hz]
      exact wP
    · rw [e2, if_neg hz]
      exact wU
    · rw [e2]
      exact wL
    · rw [e2]
      exact wW
    · rw [e2]
      exact wE
    · intro σ Hs Ls G b x bs βG δG βb δb bmax hI
      rw [if_neg hz] at hI
      have h := p.outcome hP v hv σ Hs Ls G b x bs βG δG βb δb bmax hI
      refine ⟨fun j => ?_, ?_, fun j => ?_, ?_, ?_, ?_, ?_⟩
      · rw [e1]
        exact h.unitary_trials j
      · simp only [e1]
        exact h.mean_success
      · rw [e1]
        exact h.trial_direction j
      · rw [e2]
        exact h.success_lower
      · rw [e2]
        exact h.success_two_thirds
      · rw [e2]
        exact h.output_density
      · rw [e2]
        exact h.conditional_error

end Time

end

end SparseHamiltonian.ZeroTimeGateODE
