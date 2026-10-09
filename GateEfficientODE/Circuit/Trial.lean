import GateEfficientODE.Circuit.Reflect
import GateEfficientODE.Grid.Table

/-!
# The gate-level trial circuits

All public data are collected in `Params`: the number `a` of ancillas of the
supplied `U_J`, the clock constants `Q, qbar`, the final time `T`, the norm
bounds `lamH, lamD` of the Hamiltonian and dissipative parts, the normalisation
bound `g`, the precision `ε`, and the source norms `r₀, rb`.  Derived:

* `nu = ε / (10000 g)`, `R = radius g ε`, the common simulation time
  `tau = T (lamH + R lamD)`, and the released simulator `simCircuit a tau Q qbar nu`
  with filter degree `d` on `Wire a m r K`;
* the analytic Gaussian LCHS grid `AnalyticLCHS` with growth constant
  `T lamD`: `J = 2K + 1` nodes `n h`, `|n| ≤ K`, `h ≤ π / (T lamD / 2 + log (512 / nu))`,
  padded to coefficient mass three (`J + 2` labels on `l = ⌈log₂ (J + 2)⌉`
  wires: `coeffW`, `nodeW`);
* `2^k` left-endpoint quadrature nodes, `k = ⌈log₂ ⌈T (lamH + lamD) / nu⌉⌉`;
* a pool of `f = card (Wire a m r K) + k + l` clean flags.

The preparation circuit `prepC` is

`SRC · LCHS · LOAD · SELECT · PHASE · LCHS⁻¹ · SRC⁻¹`

where `SRC` is one rotation on `ini` and Hadamards on the node word, `LCHS`
is the rotation tree of the amplitudes `sqrt(|c_w| / 3)`, `LOAD` calls the
two source interfaces under `ini`, `SELECT` is the released simulator with
the label-selected private operation, and `PHASE` applies the coefficient
phases.  One amplification step is

`stepC = R_good · prepC⁻¹ · R_seed · prepC · (-1)`,

and the trial with `j` steps is `trialC j = prepC · stepC^j`.
-/

namespace SparseHamiltonian.GateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire anc_injective simCircuit simM simR simK fDeg zMat zMat_unitary
  negOne_unitary)
open GatePointerEncoding (wordValue wordValue_lt_pow)
open scoped InnerProduct BigOperators

/-- The public data of the solver. -/
structure Params where
  a : ℕ
  Q : ℝ
  qbar : ℝ
  T : ℝ
  lamH : ℝ
  lamD : ℝ
  g : ℝ
  ε : ℝ
  r₀ : ℝ
  rb : ℝ

namespace Params

variable (p : Params)

/-- The precision unit `ν = ε / (10000 g)`. -/
abbrev nu : ℝ := ImprovedODEQueryBudget.precision p.g p.ε

/-- The frequency radius of the LCHS table. -/
abbrev R : ℝ := ImprovedODEQueryBudget.radius p.g p.ε

/-- The common simulation time of every branch. -/
abbrev tau : ℝ := p.T * (p.lamH + p.R * p.lamD)

abbrev m : ℕ := simM p.tau p.nu
abbrev r : ℕ := simR p.Q p.tau p.qbar p.nu
abbrev K : ℕ := simK p.a p.Q p.tau p.qbar p.nu

/-- The filter degree of the released simulator. -/
abbrev d : ℕ := fDeg p.Q p.tau p.qbar p.nu

/-- The size of the analytic Gaussian LCHS grid. -/
abbrev J : ℕ := AnalyticLCHS.gridSize (p.T * p.lamD) p.g p.ε

/-- LCHS label wires: `2^l ≥ J + 2`. -/
abbrev l : ℕ := Nat.clog 2 (p.J + 2)

/-- Quadrature node wires: `2^k ≥ T (lamH + lamD) / ν`. -/
abbrev k : ℕ := Nat.clog 2 ⌈p.T * (p.lamH + p.lamD) / p.nu⌉₊

/-- The pool size. -/
abbrev f : ℕ := Fintype.card (Wire p.a p.m p.r p.K) + p.k + p.l

/-- The source mass `B = r₀ + T rb`. -/
abbrev B : ℝ := p.r₀ + p.T * p.rb

/-- All wires of the solver. -/
abbrev W := AW p.a p.m p.r p.K p.k p.l p.f

/-- The instructions of the solver. -/
abbrev Ins := OInstr (Wire p.a p.m p.r p.K) (OWire p.k p.l p.f)

theorem l_pos : 0 < p.l := Nat.clog_pos (by norm_num) (by omega)

theorem J_add_two_le : p.J + 2 ≤ 2 ^ p.l := Nat.le_pow_clog (by norm_num) _

theorem l_le_pool : p.l ≤ p.f + 1 := by
  unfold f; omega

theorem zero_test_le : Fintype.card (Wire p.a p.m p.r p.K) + p.k + p.l ≤ p.f := le_rfl

end Params

/-! ### Padded LCHS labels on words -/

/-- The padded label of an index: the `J` table labels, then the two padding
labels. -/
def padIdx (J n : ℕ) : Option (Fin J ⊕ Bool) :=
  if h : n < J then some (Sum.inl ⟨n, h⟩)
  else if n = J then some (Sum.inr false)
  else if n = J + 1 then some (Sum.inr true) else none

namespace Params

variable (p : Params)

/-- The padded Gaussian coefficient of an LCHS word (zero beyond `J + 2`). -/
def coeffW (w : Fin p.l → Bool) : ℂ :=
  (padIdx p.J (wordValue w)).elim 0 (fun i => ODECoefficientPadding.paddedCoefficient
    (AnalyticLCHS.coefficients (p.T * p.lamD) p.g p.ε) 3 i)

/-- The padded Gaussian node of an LCHS word (zero beyond `J + 2`). -/
def nodeW (w : Fin p.l → Bool) : ℝ :=
  (padIdx p.J (wordValue w)).elim 0 (fun i => ODECoefficientPadding.paddedNodes
    (AnalyticLCHS.nodes (p.T * p.lamD) p.g p.ε) i)

/-- Branch durations: `T` for the initial sector, `i T / 2^k` for node `i`. -/
def dur (s : Bool × (Fin p.k → Bool)) : ℝ :=
  if s.1 then (wordValue s.2 : ℝ) * (p.T / 2 ^ p.k) else p.T

/-! ### The gates of the preparation -/

/-- The source-label rotations: `ini` first entry, then Hadamards. -/
def srcMat : Fin (p.k + 1) → Matrix Bool Bool ℂ :=
  Fin.cases (rotC (Real.sqrt (p.r₀ / p.B)) (Real.sqrt (p.T * p.rb / p.B))) (fun _ => hadC)

/-- Gates of the source-label preparation. -/
def srcPrep : List (Gate p.W) := constT srcTS p.srcMat (p.k + 1)

/-- Amplitudes of the LCHS label register. -/
def lchAmp (w : Fin p.l → Bool) : ℝ := Real.sqrt (‖p.coeffW w‖ / 3)

/-- Gates of the LCHS label preparation. -/
def lchPrep : List (Gate p.W) := prepT lchTree p.lchAmp p.l

/-- Gates of the coefficient phases. -/
def lchPhase : List (Gate p.W) :=
  phaseT lchTree p.l_pos (fun w => ODECoherentLCU.coefficientPhase (p.coeffW w))

/-- The two controlled source-interface calls. -/
def load : List p.Ins := [.src false false, .src true false]

/-- The released simulator with the label-selected private operation. -/
def select : List p.Ins := (simCircuit p.a p.tau p.Q p.qbar p.nu).map embI

/-- The preparation circuit. -/
def prepC : List p.Ins :=
  ofGates p.srcPrep ++ ofGates p.lchPrep ++ p.load ++ p.select ++
    (ofGates p.lchPhase ++ invList (ofGates p.lchPrep) ++ invList (ofGates p.srcPrep))

/-- The global sign `-1`. -/
def negGate : Gate p.W := ⟨[], Sum.inr OWire.ini, -1⟩

/-- One amplification step. -/
def stepC : List p.Ins :=
  ofGates rgoodG ++ invList p.prepC ++ rseedC ++ p.prepC ++ [.gate p.negGate]

/-- The trial with `j` amplification steps. -/
def trialC (j : ℕ) : List p.Ins := p.prepC ++ (List.replicate j p.stepC).flatten

end Params

end

end SparseHamiltonian.GateODE
