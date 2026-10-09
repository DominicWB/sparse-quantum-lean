import GateEfficientODE.Time.Model
import GateEfficientODE.Circuit.Trial

/-!
# The time-dependent gate-level trial circuits

The public data `TParams` are those of the constant-coefficient solver
without source norms, together with the mesh exponent `m`: the time interval
`[0, T]` is divided into `2^m` slots of length `T / 2^m`, which are also the
left-endpoint quadrature nodes of the forcing.  Internally the solver works
with the ratio `2 g` and the accuracy `ε / 2` (`ratio`, `acc`): half of the
direction error and half of the normalisation are reserved for the
discretisation of the time-dependent problem.  Derived:

* `nu = ε / (40000 g)`, the frequency radius `R = radius (2g) (ε/2)` and the
  common simulation time `tau = T (λH + R λD)`;
* the slot-selected simulator `SlotSim.simCircuitT a tau Q qbar nu m` with
  `2^m` slots and filter degree `d`;
* the analytic Gaussian LCHS grid with growth constant `T λD`, padded to
  coefficient mass three on `l = ⌈log₂ (J + 2)⌉` wires;
* the source label `(ini, q)` on `1 + m` wires and a pool of
  `f = card (Wire a m r K) + m + l` clean flags.

The preparation circuit is

`Wp · LCHS · LOAD · SELECT · PHASE · LCHS⁻¹ · Wp⁻¹`,

where `Wp` is one call of the supplied weight preparation on the source
label, `LCHS` the rotation tree of the amplitudes `sqrt(|c_w| / 3)`, `LOAD`
one coherent call of the source loading, `SELECT` the embedded
slot-selected simulator and `PHASE` the coefficient phases.  One
amplification step and the trials are as in the constant-coefficient solver:
`stepC = R_good · prepC⁻¹ · R_seed · prepC · (-1)`,
`trialC j = prepC · stepC^j`.
-/

namespace SparseHamiltonian.GateODE.Time

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire anc_injective simR fDeg zMat zMat_unitary negOne_unitary)
open GatePointerEncoding (wordValue wordValue_lt_pow)
open scoped InnerProduct BigOperators

/-- The public data of the time-dependent solver. -/
structure TParams where
  a : ℕ
  Q : ℝ
  qbar : ℝ
  T : ℝ
  lamH : ℝ
  lamD : ℝ
  g : ℝ
  ε : ℝ
  m : ℕ

namespace TParams

variable (p : TParams)

/-- The internal normalisation ratio `2 g`. -/
abbrev ratio : ℝ := 2 * p.g

/-- The internal accuracy `ε / 2`. -/
abbrev acc : ℝ := p.ε / 2

/-- The precision unit `ν = (ε / 2) / (10000 · 2 g)`. -/
abbrev nu : ℝ := ImprovedODEQueryBudget.precision p.ratio p.acc

/-- The frequency radius of the LCHS table. -/
abbrev R : ℝ := ImprovedODEQueryBudget.radius p.ratio p.acc

/-- The common simulation time of every branch. -/
abbrev tau : ℝ := p.T * (p.lamH + p.R * p.lamD)

/-- The number of time slots. -/
abbrev M : ℕ := 2 ^ p.m

abbrev r : ℕ := simR p.Q p.tau p.qbar p.nu
abbrev K : ℕ := p.a + p.m + 2 * p.r

/-- The filter degree of the simulator. -/
abbrev d : ℕ := fDeg p.Q p.tau p.qbar p.nu

/-- The size of the analytic Gaussian LCHS grid. -/
abbrev J : ℕ := AnalyticLCHS.gridSize (p.T * p.lamD) p.ratio p.acc

/-- LCHS label wires: `2^l ≥ J + 2`. -/
abbrev l : ℕ := Nat.clog 2 (p.J + 2)

/-- The pool size. -/
abbrev f : ℕ := Fintype.card (Wire p.a p.m p.r p.K) + p.m + p.l

/-- All wires of the solver. -/
abbrev W := AW p.a p.m p.r p.K p.m p.l p.f

/-- The instructions of the solver. -/
abbrev Ins := OInstr (Wire p.a p.m p.r p.K) (OWire p.m p.l p.f)

theorem l_pos : 0 < p.l := Nat.clog_pos (by norm_num) (by omega)

theorem J_add_two_le : p.J + 2 ≤ 2 ^ p.l := Nat.le_pow_clog (by norm_num) _

theorem l_le_pool : p.l ≤ p.f + 1 := by
  unfold f; omega

theorem zero_test_le : Fintype.card (Wire p.a p.m p.r p.K) + p.m + p.l ≤ p.f := le_rfl

theorem M_pos : 0 < p.M := Nat.two_pow_pos _

/-! ### Padded LCHS labels on words -/

/-- The padded Gaussian coefficient of an LCHS word (zero beyond `J + 2`). -/
def coeffW (w : Fin p.l → Bool) : ℂ :=
  (padIdx p.J (wordValue w)).elim 0 (fun i => ODECoefficientPadding.paddedCoefficient
    (AnalyticLCHS.coefficients (p.T * p.lamD) p.ratio p.acc) 3 i)

/-- The padded Gaussian node of an LCHS word (zero beyond `J + 2`). -/
def nodeW (w : Fin p.l → Bool) : ℝ :=
  (padIdx p.J (wordValue w)).elim 0 (fun i => ODECoefficientPadding.paddedNodes
    (AnalyticLCHS.nodes (p.T * p.lamD) p.ratio p.acc) i)

/-! ### The circuits -/

/-- Amplitudes of the LCHS label register. -/
def lchAmp (w : Fin p.l → Bool) : ℝ := Real.sqrt (‖p.coeffW w‖ / 3)

/-- Gates of the LCHS label preparation. -/
def lchPrep : List (Gate p.W) := prepT lchTree p.lchAmp p.l

/-- Gates of the coefficient phases. -/
def lchPhase : List (Gate p.W) :=
  phaseT lchTree p.l_pos (fun w => ODECoherentLCU.coefficientPhase (p.coeffW w))

/-- The coherent source loading. -/
def load : List p.Ins := [.src false false]

/-- The supplied weight preparation of the source label. -/
def wprepC : List p.Ins := [.src true false]

/-- The slot-selected simulator, embedded with the label-selected private
operation. -/
def select : List p.Ins :=
  List.map (embI (S := Wire p.a p.m p.r p.K) (O := OWire p.m p.l p.f))
    (SlotSim.simCircuitT p.a p.tau p.Q p.qbar p.nu p.m)

/-- The preparation circuit. -/
def prepC : List p.Ins :=
  p.wprepC ++ ofGates p.lchPrep ++ p.load ++ p.select ++
    (ofGates p.lchPhase ++ invList (ofGates p.lchPrep) ++ invList p.wprepC)

/-- The global sign `-1`. -/
def negGate : Gate p.W := ⟨[], Sum.inr OWire.ini, -1⟩

/-- One amplification step. -/
def stepC : List p.Ins :=
  ofGates rgoodG ++ invList p.prepC ++ rseedC ++ p.prepC ++ [.gate p.negGate]

/-- The trial with `j` amplification steps. -/
def trialC (j : ℕ) : List p.Ins := p.prepC ++ (List.replicate j p.stepC).flatten

end TParams

end

end SparseHamiltonian.GateODE.Time
