import GateEfficientTimeDependent.SlotError
import TimeDependentHamiltonian.Continuous.Existence
import SparseHamiltonian.ImprovedPrecisionBudget
import SparseHamiltonian.CayleyClockInterface

/-!
# Gate-efficient time-dependent Hamiltonian simulation, exact gates

The gate-level circuit of `hs:thm:gates` with a *slot-selected* private
Cayley operation simulates a time-dependent Hamiltonian on a uniform mesh of
`2^m` slots, as in the chronological construction of `hs:thm:time`.  The
manuscript states `hs:thm:gates` for time-independent Hamiltonians only; the
time-dependent circuit is the single-label case of the coherent selection
`ode:lem:gate-select`.

**Access model.** As in the released gate-level simulator, `U_J` and the
private operations are supplied unitaries on `a` ancilla qubits and the
system `P`.  The private operation is slot-selected: one call applies `D k`
to the ancilla slice of every configuration whose slot wires carry the slot
`k` (`slotOracle`, `runT`); one call is one instruction.  `D k` satisfies the
clock promise of the released simulator, for the common boundary isometry
`J = U_J ι₀`, with respect to the normalised sample `H̃_k / α`, where `H̃_k`
is the represented sample of slot `k`, `‖H̃_k‖ ≤ α`.

**The circuit.** `simCircuitT a (α t) Q qbar (ε/2) m` is the released circuit
`ampI` with `2^m` time slots: it depends only on the public numbers
`a, α t, Q, qbar, ε, m`, not on the oracles, the path or the samples.

**Main theorem** (`gate_efficient_time_simulation`).  For a Hermitian path
`H(u)`, `0 ≤ u ≤ t`, with operator-norm Lipschitz bound `β` and represented
samples with `‖H(k t / 2^m) - H̃_k‖ ≤ δ`, under the public mesh conditions
`steps (α t) (ε/6) ≤ 2^m` (subdivision of the Cayley steps) and
`4 β t² ≤ ε 2^m` (freezing), and the sample budget `4 t δ ≤ ε`:

* every instruction is a valid elementary instruction;
* exactly `6d` slot-selected private calls and exactly `12d` calls of `U_J`
  or `U_J†`, and at most `200 (d+1)(a+m+r+1)` elementary gates on
  `2a + 3m + 6r + 3` qubits besides the system;
* `d ≤ 128 (α t qbar + Q (1 + log (6/ε)))` and `2d + 2 ≤ 2^r ≤ 4 (d+1)`;
* the path has a propagator, and for *every* propagator `U` with `U(0) = 1`,
  the full output on clean inputs, including every work register, is within
  `ε` of `U(t)`: `‖runT ∘ io - io ∘ U(t)‖ ≤ ε`.

The error splits as `ε/2` (simulation of the ordered product of the slot
exponentials) plus `β t²/2^m` (freezing) plus `t δ` (samples)
(`propagator_error`).  `meshExp` is an explicit mesh exponent meeting both
mesh conditions with `2^m < 2 max (steps (α t) (ε/6), ⌈4 β t² / ε⌉)`.

**Sparse parameters** (`sparse_counts`).  With the rescaling of
`hs:thm:time` (`α = η √s / γ`, `Q = ⌈max (1, γ √s)⌉`, `qbar = (1 + γ²)/2`,
`γ` from the released precision budget), the degree is
`d ≤ 4608 (√s τ + √(s τ log(1/ε)) + log(1/ε))`, `τ = η t`, so the circuit
makes `O(√s τ + √(s τ ℓ) + ℓ)` private and `U_J` calls and uses
`O((√s τ + √(s τ ℓ) + ℓ)(a + m + r + 1))` elementary gates; neither the mesh
size `2^m` nor `β` multiplies the number of calls, and they enter the gate
count only through `m`.
-/

namespace SparseHamiltonian.GateCircuit.SlotSim

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Public counts -/

/-- Validity and counts of the simulator with `2^m` slots follow from the
public data and the mesh condition alone. -/
theorem simCircuitT_public (a m : ℕ) (τ Q qbar ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε)
    (hm : TimeSchedule.steps τ (ε / 3) ≤ 2 ^ m) :
    (∀ g ∈ simCircuitT a τ Q qbar ε m, g.Valid Wire.anc) ∧
    nPriv (simCircuitT a τ Q qbar ε m) = 6 * fDeg Q τ qbar ε ∧
    nUJ (simCircuitT a τ Q qbar ε m) = 12 * fDeg Q τ qbar ε ∧
    nGates (simCircuitT a τ Q qbar ε m) ≤
      200 * (fDeg Q τ qbar ε + 1) * (a + m + simR Q τ qbar ε + 1) := by
  obtain ⟨_, _, hr2⟩ := simR_spec Q τ qbar ε
  have hw0 : 0 ≤ stepW τ m := div_nonneg hτ (Nat.cast_nonneg _)
  have hwq : stepW τ m ≤ 1 / 4 := (schedule_ge τ (ε / 3) hτ (by positivity) (2 ^ m) hm).2.1
  obtain ⟨_, _, _, hσc, _⟩ := CayleyTransfer.scalar_promises (stepW τ m) hw0 hwq
  have hunit : CayleyTransfer.c (stepW τ m) ^ 2 + CayleyTransfer.sigma (stepW τ m) ^ 2 = 1 := by
    linarith
  have hN : 2 * fDeg Q τ qbar ε ≤ cap (simR Q τ qbar ε) + 1 := by
    have := cap_succ (simR Q τ qbar ε)
    have h1 := (simR_spec Q τ qbar ε).1
    omega
  obtain ⟨hc1, hc2, hc3⟩ := ampI_counts (a := a) (m := m) (K := a + m + 2 * simR Q τ qbar ε)
    (simL Q τ qbar ε) (labLen Q τ qbar ε) (labWt Q τ qbar ε) (CayleyTransfer.c (stepW τ m))
    (CayleyTransfer.sigma (stepW τ m)) (2 * fDeg Q τ qbar ε) hN
  have hgb := gate_bound a m (simR Q τ qbar ε) (fDeg Q τ qbar ε) (2 ^ simR Q τ qbar ε) hr2
  refine ⟨ampI_valid _ _ _ _ _ hunit _, ?_, ?_, ?_⟩
  · unfold simCircuitT; rw [hc1]; ring
  · unfold simCircuitT; rw [hc2]; ring
  · unfold simCircuitT
    refine hc3.trans (le_of_eq_of_le ?_ hgb)
    ring

/-! ### The mesh -/

/-- `2 ^ ⌈log₂ n⌉ < 2 n` for `n ≥ 1`. -/
theorem two_pow_clog_lt (n : ℕ) (hn : 1 ≤ n) : 2 ^ Nat.clog 2 n < 2 * n := by
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h1
    have hpos : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) h1
    have e : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n).pred := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
      rw [pow_succ]
      ring
    omega
  · have : n = 1 := by omega
    subst this
    simp

/-- An explicit mesh exponent: `2^m` is the least power of two that is at
least the subdivision count `steps (α t) (ε/6)` of the Cayley steps and the
freezing count `⌈4 β t² / ε⌉`. -/
def meshExp (α t β ε : ℝ) : ℕ :=
  Nat.clog 2 (max (TimeSchedule.steps (α * t) (ε / 6)) ⌈4 * β * t ^ 2 / ε⌉₊)

/-- The explicit mesh meets both mesh conditions, with less than a factor two
to spare. -/
theorem meshExp_spec (α t β ε : ℝ) (hε : 0 < ε) :
    TimeSchedule.steps (α * t) (ε / 6) ≤ 2 ^ meshExp α t β ε ∧
    4 * β * t ^ 2 ≤ ε * 2 ^ meshExp α t β ε ∧
    2 ^ meshExp α t β ε <
      2 * max (TimeSchedule.steps (α * t) (ε / 6)) ⌈4 * β * t ^ 2 / ε⌉₊ := by
  have h1 : TimeSchedule.steps (α * t) (ε / 6) ≤
      max (TimeSchedule.steps (α * t) (ε / 6)) ⌈4 * β * t ^ 2 / ε⌉₊ := le_max_left _ _
  have h2 : ⌈4 * β * t ^ 2 / ε⌉₊ ≤
      max (TimeSchedule.steps (α * t) (ε / 6)) ⌈4 * β * t ^ 2 / ε⌉₊ := le_max_right _ _
  have hpos : 1 ≤ max (TimeSchedule.steps (α * t) (ε / 6)) ⌈4 * β * t ^ 2 / ε⌉₊ :=
    le_trans (TimeSchedule.steps_pos _ _) h1
  have hle : max (TimeSchedule.steps (α * t) (ε / 6)) ⌈4 * β * t ^ 2 / ε⌉₊ ≤
      2 ^ meshExp α t β ε := Nat.le_pow_clog (by norm_num) _
  refine ⟨h1.trans hle, ?_, two_pow_clog_lt _ hpos⟩
  have h3 : 4 * β * t ^ 2 / ε ≤ (2 : ℝ) ^ meshExp α t β ε := by
    have hc := Nat.le_ceil (4 * β * t ^ 2 / ε)
    have h4 : ((⌈4 * β * t ^ 2 / ε⌉₊ : ℕ) : ℝ) ≤ ((2 ^ meshExp α t β ε : ℕ) : ℝ) := by
      exact_mod_cast h2.trans hle
    push_cast at h4
    linarith
  rw [div_le_iff₀ hε] at h3
  linarith

/-! ### The error against every propagator -/

/-- **The error against every propagator.**  The slot-selected simulator with
accuracy parameter `ε` and `2^m ≥ steps (α t) (ε/3)` slots is within
`ε + β t² / 2^m + t δ` of every propagator of a `β`-Lipschitz Hermitian path
whose samples at the left endpoints `k t / 2^m` are within `δ` of the
represented samples `H̃_k`; `D k` carries the clock promise for `H̃_k / α`. -/
theorem propagator_error (a m : ℕ) (UJ : Vsp a P →L[ℂ] Vsp a P)
    (D R1 : ℕ → Vsp a P →L[ℂ] Vsp a P) (Hpath U : ℝ → P →L[ℂ] P) (Hs : ℕ → P →L[ℂ] P)
    (t α β δ Q b qbar ε : ℝ) (ht : 0 ≤ t) (hα : 0 < α) (hβ : 0 ≤ β) (hQ : 1 ≤ Q)
    (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hm : TimeSchedule.steps (α * t) (ε / 3) ≤ 2 ^ m)
    (hUJ : IsUnitary UJ) (hD : ∀ k < 2 ^ m, IsUnitary (D k))
    (hRight : ∀ k < 2 ^ m, (1 - D k) ∘L R1 k = 1)
    (hLeft : ∀ k < 2 ^ m, R1 k ∘L (1 - D k) = 1) (hR1 : ∀ k < 2 ^ m, ‖R1 k‖ ≤ Q)
    (hBoundary : ∀ k < 2 ^ m, (UJ ∘L iota0)† ∘L R1 k ∘L (UJ ∘L iota0) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • ((α : ℂ)⁻¹ • Hs k)))
    (hEndpoint : ∀ k < 2 ^ m, ‖R1 k ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2)
    (hSelf : ∀ k < 2 ^ m, star (Hs k) = Hs k) (hHs : ∀ k < 2 ^ m, ‖Hs k‖ ≤ α)
    (hPath : ∀ u ∈ Set.Icc 0 t, star (Hpath u) = Hpath u)
    (hLip : ∀ u ∈ Set.Icc 0 t, ∀ v ∈ Set.Icc 0 t, ‖Hpath u - Hpath v‖ ≤ β * |u - v|)
    (hVal : ∀ k : ℕ, k < 2 ^ m → ‖Hpath (k * t / 2 ^ m) - Hs k‖ ≤ δ)
    (hU0 : U 0 = 1) (hU : TimeDependent.SolvesOn Hpath U 0 t) :
    ‖runT UJ D (simCircuitT a (α * t) Q qbar ε m) ∘L io - io ∘L U t‖ ≤
      ε + β * t ^ 2 / 2 ^ m + t * δ := by
  have hMpos : 0 < 2 ^ m := Nat.two_pow_pos m
  have hMR : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast hMpos
  have hαC : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  -- the normalised samples
  have hnSelf : ∀ k < 2 ^ m, star ((α : ℂ)⁻¹ • Hs k) = (α : ℂ)⁻¹ • Hs k := by
    intro k hk
    rw [star_smul, hSelf k hk, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hnNorm : ∀ k < 2 ^ m, ‖(α : ℂ)⁻¹ • Hs k‖ ≤ 1 := by
    intro k hk
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hα.le,
      inv_mul_le_iff₀ hα, mul_one]
    exact hHs k hk
  obtain ⟨-, -, -, -, -, hsim, -⟩ := simulationT (P := P) a m UJ D R1
    (fun k => (α : ℂ)⁻¹ • Hs k) hUJ hD (α * t) Q b qbar ε (mul_nonneg hα.le ht) hQ hRight hLeft
    hR1 hBoundary hnSelf hnNorm hEndpoint hbq hqQ hε hε1 hm
  -- one normalised Cayley step is one physical step `t / 2^m`
  have hexp : (fun k => NormedSpace.exp ((-Complex.I * (stepW (α * t) m : ℂ)) •
      ((α : ℂ)⁻¹ • Hs k))) =
      fun k => NormedSpace.exp ((-Complex.I * ((t / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • Hs k) := by
    funext k
    congr 1
    rw [smul_smul]
    congr 1
    unfold stepW
    push_cast
    field_simp
  rw [hexp] at hsim
  -- the mesh error of the path, with samples clamped to the mesh
  have hcl := min_pred_lt hMpos
  have hmesh := TimeDependent.mesh_error (H := Hpath) (U := U) (δ := δ) (clampAt (2 ^ m) Hs) hMpos
    ht hβ hU0 hU hPath (fun k => hSelf _ (hcl k)) hLip (fun k hk => by
      rw [clampAt_of_lt _ _ hk]
      have h := hVal k hk
      push_cast
      exact h)
  have hev : TimeDependent.evolution (fun k => NormedSpace.exp
        ((-Complex.I * ((t / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • clampAt (2 ^ m) Hs k)) (2 ^ m) =
      TimeDependent.evolution (fun k => NormedSpace.exp
        ((-Complex.I * ((t / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • Hs k)) (2 ^ m) :=
    evolution_eq_of_lt _ _ _ (fun k hk => by rw [clampAt_of_lt _ _ hk])
  rw [hev] at hmesh
  have hio : ‖(io : P →L[ℂ] Reg (Wire a m (simR Q (α * t) qbar ε)
      (a + m + 2 * simR Q (α * t) qbar ε)) P)‖ ≤ 1 :=
    opNorm_le_bound _ zero_le_one (fun v => by
      rw [GateBlockTransfer.norm_apply_of_isometry _ io_isometry v, one_mul])
  have h2 : ‖(io : P →L[ℂ] Reg (Wire a m (simR Q (α * t) qbar ε)
      (a + m + 2 * simR Q (α * t) qbar ε)) P) ∘L TimeDependent.evolution (fun k => NormedSpace.exp
        ((-Complex.I * ((t / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • Hs k)) (2 ^ m) - io ∘L U t‖ ≤
      β * t ^ 2 / 2 ^ m + t * δ := by
    rw [← comp_sub]
    refine (opNorm_comp_le _ _).trans ?_
    have h3 : ‖TimeDependent.evolution (fun k => NormedSpace.exp
        ((-Complex.I * ((t / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • Hs k)) (2 ^ m) - U t‖ ≤
        β * t ^ 2 / 2 ^ m + t * δ := by
      rw [norm_sub_rev]
      have hpow : (((2 ^ m : ℕ) : ℝ)) = (2 : ℝ) ^ m := by norm_num
      rw [← hpow]
      exact hmesh
    calc _ ≤ 1 * (β * t ^ 2 / 2 ^ m + t * δ) :=
          mul_le_mul hio h3 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have key := norm_sub_le_norm_sub_add_norm_sub
    (runT UJ D (simCircuitT a (α * t) Q qbar ε m) ∘L io)
    ((io : P →L[ℂ] Reg (Wire a m (simR Q (α * t) qbar ε)
      (a + m + 2 * simR Q (α * t) qbar ε)) P) ∘L TimeDependent.evolution (fun k => NormedSpace.exp
        ((-Complex.I * ((t / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • Hs k)) (2 ^ m))
    ((io : P →L[ℂ] Reg (Wire a m (simR Q (α * t) qbar ε)
      (a + m + 2 * simR Q (α * t) qbar ε)) P) ∘L U t)
  linarith

/-! ### The main theorem -/

/-- **Gate-efficient time-dependent Hamiltonian simulation, exact gates.**

The circuit `simCircuitT a (α t) Q qbar (ε/2) m` is fixed by the public
numbers before the oracles.  Let `U_J` and the slot-selected private
operations `D k` be unitaries such that, for the boundary isometry
`J = U_J ι₀`, every `D k` (`k < 2^m`) carries the clock promise of the
released analysis for the normalised represented sample `H̃_k / α`
(`‖H̃_k‖ ≤ α`).  For a Hermitian path `H(u)` with Lipschitz bound `β` and
`‖H(k t / 2^m) - H̃_k‖ ≤ δ`, under the mesh conditions
`steps (α t) (ε/6) ≤ 2^m` and `4 β t² ≤ ε 2^m` and the sample budget
`4 t δ ≤ ε`, the circuit consists of valid elementary instructions, makes
exactly `6d` private calls and `12d` calls of `U_J` or `U_J†`, uses at most
`200 (d+1)(a+m+r+1)` elementary gates on `2a + 3m + 6r + 3` qubits, and its
full output on clean inputs is within `ε` of `U(t)` for every propagator `U`
of the path; a propagator exists. -/
theorem gate_efficient_time_simulation (a m : ℕ) (UJ : Vsp a P →L[ℂ] Vsp a P)
    (D R1 : ℕ → Vsp a P →L[ℂ] Vsp a P) (Hpath : ℝ → P →L[ℂ] P) (Hs : ℕ → P →L[ℂ] P)
    (t α β δ Q b qbar ε : ℝ) (ht : 0 ≤ t) (hα : 0 < α) (hβ : 0 ≤ β) (hQ : 1 ≤ Q)
    (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hCayley : TimeSchedule.steps (α * t) (ε / 6) ≤ 2 ^ m)
    (hFreeze : 4 * β * t ^ 2 ≤ ε * 2 ^ m)
    (hUJ : IsUnitary UJ) (hD : ∀ k < 2 ^ m, IsUnitary (D k))
    (hRight : ∀ k < 2 ^ m, (1 - D k) ∘L R1 k = 1)
    (hLeft : ∀ k < 2 ^ m, R1 k ∘L (1 - D k) = 1) (hR1 : ∀ k < 2 ^ m, ‖R1 k‖ ≤ Q)
    (hBoundary : ∀ k < 2 ^ m, (UJ ∘L iota0)† ∘L R1 k ∘L (UJ ∘L iota0) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • ((α : ℂ)⁻¹ • Hs k)))
    (hEndpoint : ∀ k < 2 ^ m, ‖R1 k ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2)
    (hSelf : ∀ k < 2 ^ m, star (Hs k) = Hs k) (hHs : ∀ k < 2 ^ m, ‖Hs k‖ ≤ α)
    (hPath : ∀ u ∈ Set.Icc 0 t, star (Hpath u) = Hpath u)
    (hLip : ∀ u ∈ Set.Icc 0 t, ∀ v ∈ Set.Icc 0 t, ‖Hpath u - Hpath v‖ ≤ β * |u - v|)
    (hVal : ∀ k : ℕ, k < 2 ^ m → ‖Hpath (k * t / 2 ^ m) - Hs k‖ ≤ δ)
    (hValBudget : 4 * t * δ ≤ ε) :
    (∀ g ∈ simCircuitT a (α * t) Q qbar (ε / 2) m, g.Valid Wire.anc) ∧
    nPriv (simCircuitT a (α * t) Q qbar (ε / 2) m) = 6 * fDeg Q (α * t) qbar (ε / 2) ∧
    nUJ (simCircuitT a (α * t) Q qbar (ε / 2) m) = 12 * fDeg Q (α * t) qbar (ε / 2) ∧
    nGates (simCircuitT a (α * t) Q qbar (ε / 2) m) ≤
      200 * (fDeg Q (α * t) qbar (ε / 2) + 1) * (a + m + simR Q (α * t) qbar (ε / 2) + 1) ∧
    Fintype.card (Wire a m (simR Q (α * t) qbar (ε / 2))
        (a + m + 2 * simR Q (α * t) qbar (ε / 2))) =
      2 * a + 3 * m + 6 * simR Q (α * t) qbar (ε / 2) + 3 ∧
    (fDeg Q (α * t) qbar (ε / 2) : ℝ) ≤ 128 * (α * t * qbar + Q * (1 + Real.log (6 / ε))) ∧
    2 * fDeg Q (α * t) qbar (ε / 2) + 2 ≤ 2 ^ simR Q (α * t) qbar (ε / 2) ∧
    2 ^ simR Q (α * t) qbar (ε / 2) ≤ 4 * (fDeg Q (α * t) qbar (ε / 2) + 1) ∧
    (∃ U : ℝ → P →L[ℂ] P, U 0 = 1 ∧ TimeDependent.SolvesOn Hpath U 0 t) ∧
    ∀ U : ℝ → P →L[ℂ] P, U 0 = 1 → TimeDependent.SolvesOn Hpath U 0 t →
      ‖runT UJ D (simCircuitT a (α * t) Q qbar (ε / 2) m) ∘L io - io ∘L U t‖ ≤ ε := by
  have hε2 : 0 < ε / 2 := by linarith
  have hε21 : ε / 2 ≤ 1 := by linarith
  have hm : TimeSchedule.steps (α * t) (ε / 2 / 3) ≤ 2 ^ m := by
    rw [show ε / 2 / 3 = ε / 6 by ring]
    exact hCayley
  have hnSelf : ∀ k < 2 ^ m, star ((α : ℂ)⁻¹ • Hs k) = (α : ℂ)⁻¹ • Hs k := by
    intro k hk
    rw [star_smul, hSelf k hk, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hnNorm : ∀ k < 2 ^ m, ‖(α : ℂ)⁻¹ • Hs k‖ ≤ 1 := by
    intro k hk
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hα.le,
      inv_mul_le_iff₀ hα, mul_one]
    exact hHs k hk
  obtain ⟨hvalid, hP, hJ, hG, hW, -, hdeg⟩ := simulationT (P := P) a m UJ D R1
    (fun k => (α : ℂ)⁻¹ • Hs k) hUJ hD (α * t) Q b qbar (ε / 2) (mul_nonneg hα.le ht) hQ hRight
    hLeft hR1 hBoundary hnSelf hnNorm hEndpoint hbq hqQ hε2 hε21 hm
  obtain ⟨hr1, _, hr2⟩ := simR_spec Q (α * t) qbar (ε / 2)
  have hlog : (1 : ℝ) / (ε / 2 / 3) = 6 / ε := by
    field_simp
    ring
  rw [hlog] at hdeg
  refine ⟨hvalid, hP, hJ, hG, hW, hdeg, hr1, hr2,
    TimeDependent.exists_solvesOn_of_lipschitz Hpath ht hLip, fun U hU0 hU => ?_⟩
  have herr := propagator_error a m UJ D R1 Hpath U Hs t α β δ Q b qbar (ε / 2) ht hα hβ hQ hqQ
    hε2 hε21 hm hUJ hD hRight hLeft hR1 hBoundary hEndpoint hbq hSelf hHs hPath hLip hVal hU0 hU
  have hM : (0 : ℝ) < 2 ^ m := by positivity
  have hfr : β * t ^ 2 / 2 ^ m ≤ ε / 4 := by
    rw [div_le_iff₀ hM]
    linarith
  linarith

/-! ### The rescaled sparse parameters -/

/-- **Counts for the rescaled sparse parameters of `hs:thm:time`.**  For
sparsity `s ≥ 1`, row and column norm bound `η` and time `t`, with
`τ = η t` and `q = √s τ + √(s τ log(1/ε)) + log(1/ε)`, the released precision
budget chooses `γ ∈ (0, 1]` with `γ √s ≥ 1`.  For `α = η √s / γ`,
`Q = ⌈max (1, γ √s)⌉` and `qbar = (1 + γ²)/2` (which satisfy `Q ≥ 1` and
`qbar ≤ Q`), the filter degree is at most `4608 q`; on any mesh meeting the
subdivision condition, the circuit makes at most `27648 q` private calls and
`55296 q` calls of `U_J` or `U_J†`, and uses at most
`200 (4608 q + 1)(a + m + r + 1)` elementary gates with `2^r ≤ 4 (4608 q + 1)`. -/
theorem sparse_counts (a : ℕ) (s η t ε : ℝ) (hs : 1 ≤ s) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt s ∧
      1 ≤ CayleyClockInterface.width s γ ∧
      CayleyClockInterface.moment γ ≤ CayleyClockInterface.width s γ ∧
      (fDeg (CayleyClockInterface.width s γ) (η * Real.sqrt s / γ * t)
          (CayleyClockInterface.moment γ) (ε / 2) : ℝ) ≤
        4608 * ImprovedPrecisionBudget.shape s (η * t) (Real.log (1 / ε)) ∧
      ∀ m : ℕ, TimeSchedule.steps (η * Real.sqrt s / γ * t) (ε / 6) ≤ 2 ^ m →
        (nPriv (simCircuitT a (η * Real.sqrt s / γ * t) (CayleyClockInterface.width s γ)
            (CayleyClockInterface.moment γ) (ε / 2) m) : ℝ) ≤
          27648 * ImprovedPrecisionBudget.shape s (η * t) (Real.log (1 / ε)) ∧
        (nUJ (simCircuitT a (η * Real.sqrt s / γ * t) (CayleyClockInterface.width s γ)
            (CayleyClockInterface.moment γ) (ε / 2) m) : ℝ) ≤
          55296 * ImprovedPrecisionBudget.shape s (η * t) (Real.log (1 / ε)) ∧
        (nGates (simCircuitT a (η * Real.sqrt s / γ * t) (CayleyClockInterface.width s γ)
            (CayleyClockInterface.moment γ) (ε / 2) m) : ℝ) ≤
          200 * (4608 * ImprovedPrecisionBudget.shape s (η * t) (Real.log (1 / ε)) + 1) *
            (a + m + simR (CayleyClockInterface.width s γ) (η * Real.sqrt s / γ * t)
              (CayleyClockInterface.moment γ) (ε / 2) + 1) ∧
        ((2 ^ simR (CayleyClockInterface.width s γ) (η * Real.sqrt s / γ * t)
            (CayleyClockInterface.moment γ) (ε / 2) : ℕ) : ℝ) ≤
          4 * (4608 * ImprovedPrecisionBudget.shape s (η * t) (Real.log (1 / ε)) + 1) := by
  have hτ : 0 ≤ η * t := mul_nonneg hη ht
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨γ, hγ, hγ1, hw, hbud⟩ :=
    ImprovedPrecisionBudget.exists_rescaling_for_precision s (η * t) (ε / 2) hs hτ hε2 (by linarith)
  have hsq0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hW1 := CayleyClockInterface.width_ge_one s γ
  have hmom0 : 0 ≤ CayleyClockInterface.moment γ := by
    unfold CayleyClockInterface.moment
    positivity
  have hmom1 : CayleyClockInterface.moment γ ≤ 1 := by
    unfold CayleyClockInterface.moment
    nlinarith
  have hτ' : 0 ≤ η * Real.sqrt s / γ * t := mul_nonneg (div_nonneg (mul_nonneg hη hsq0) hγ.le) ht
  -- the logarithms
  have hℓ2 : Real.log 2 ≤ Real.log (1 / ε) := Real.log_le_log (by norm_num) (by
    rw [le_div_iff₀ hε]
    linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hℓ0 : 0 ≤ Real.log (1 / ε) := hlog2.le.trans hℓ2
  have htarget : ImprovedPrecisionBudget.targetLog (ε / 2) ≤ 3 * Real.log (1 / ε) := by
    unfold ImprovedPrecisionBudget.targetLog
    have e : 2 / (ε / 2) = 2 * 2 * (1 / ε) := by
      field_simp
    rw [e, Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) (by norm_num)]
    linarith
  -- the shape with `log (4/ε)` is at most three times the shape with `log (1/ε)`
  have hshape : ImprovedPrecisionBudget.shape s (η * t) (ImprovedPrecisionBudget.targetLog (ε / 2)) ≤
      3 * ImprovedPrecisionBudget.shape s (η * t) (Real.log (1 / ε)) := by
    unfold ImprovedPrecisionBudget.shape
    have hx : 0 ≤ s * (η * t) := mul_nonneg (by linarith) hτ
    have h0 : s * (η * t) * ImprovedPrecisionBudget.targetLog (ε / 2) ≤
        4 * (s * (η * t) * Real.log (1 / ε)) := by
      have h5 := mul_le_mul_of_nonneg_left htarget hx
      have h6 := mul_nonneg hx hℓ0
      nlinarith
    have h1 : Real.sqrt (s * (η * t) * ImprovedPrecisionBudget.targetLog (ε / 2)) ≤
        Real.sqrt (4 * (s * (η * t) * Real.log (1 / ε))) := Real.sqrt_le_sqrt h0
    have h2 : Real.sqrt (4 * (s * (η * t) * Real.log (1 / ε))) =
        2 * Real.sqrt (s * (η * t) * Real.log (1 / ε)) := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    have h3 : 0 ≤ Real.sqrt s * (η * t) := mul_nonneg hsq0 hτ
    have h4 : 0 ≤ Real.sqrt (s * (η * t) * Real.log (1 / ε)) := Real.sqrt_nonneg _
    linarith
  -- the degree
  have hdegree : (fDeg (CayleyClockInterface.width s γ) (η * Real.sqrt s / γ * t)
      (CayleyClockInterface.moment γ) (ε / 2) : ℝ) ≤
      4608 * ImprovedPrecisionBudget.shape s (η * t) (Real.log (1 / ε)) := by
    have h := SharpFilterSchedule.degree_le (CayleyClockInterface.width s γ)
      (η * Real.sqrt s / γ * t * CayleyClockInterface.moment γ) (ε / 2 / 3) hW1
      (mul_nonneg hτ' hmom0) (by positivity) (by linarith)
    have e1 : (fDeg (CayleyClockInterface.width s γ) (η * Real.sqrt s / γ * t)
        (CayleyClockInterface.moment γ) (ε / 2) : ℝ) =
        (SharpFilterSchedule.degree (CayleyClockInterface.width s γ)
          (η * Real.sqrt s / γ * t * CayleyClockInterface.moment γ) (ε / 2 / 3) : ℝ) := rfl
    have e2 : 1 + SharpFilterSchedule.logBudget (ε / 2 / 3) =
        ImprovedPrecisionBudget.circuitLog (ε / 2) := by
      unfold SharpFilterSchedule.logBudget ImprovedPrecisionBudget.circuitLog
      congr 2
      ring
    have hb : η * Real.sqrt s / γ * t * CayleyClockInterface.moment γ +
        CayleyClockInterface.width s γ * ImprovedPrecisionBudget.circuitLog (ε / 2) ≤
        12 * ImprovedPrecisionBudget.shape s (η * t) (ImprovedPrecisionBudget.targetLog (ε / 2)) := by
      have e3 : η * Real.sqrt s / γ * t * CayleyClockInterface.moment γ =
          η * t * Real.sqrt s / γ * ((1 + γ ^ 2) / 2) := by
        unfold CayleyClockInterface.moment
        ring
      have e4 : CayleyClockInterface.width s γ = (⌈max 1 (γ * Real.sqrt s)⌉₊ : ℝ) := rfl
      rw [e3, e4]
      exact hbud
    rw [e1]
    refine h.trans ?_
    rw [e2]
    linarith
  refine ⟨γ, hγ, hγ1, hw, hW1, hmom1.trans hW1, hdegree, fun m hm => ?_⟩
  have hm' : TimeSchedule.steps (η * Real.sqrt s / γ * t) (ε / 2 / 3) ≤ 2 ^ m := by
    rw [show ε / 2 / 3 = ε / 6 by ring]
    exact hm
  obtain ⟨-, hP, hJ, hG⟩ := simCircuitT_public a m (η * Real.sqrt s / γ * t)
    (CayleyClockInterface.width s γ) (CayleyClockInterface.moment γ) (ε / 2) hτ' hε2 hm'
  obtain ⟨-, -, hr2⟩ := simR_spec (CayleyClockInterface.width s γ) (η * Real.sqrt s / γ * t)
    (CayleyClockInterface.moment γ) (ε / 2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hP, Nat.cast_mul, Nat.cast_ofNat]
    linarith
  · rw [hJ, Nat.cast_mul, Nat.cast_ofNat]
    linarith
  · have hGR : (nGates (simCircuitT a (η * Real.sqrt s / γ * t) (CayleyClockInterface.width s γ)
        (CayleyClockInterface.moment γ) (ε / 2) m) : ℝ) ≤
        200 * ((fDeg (CayleyClockInterface.width s γ) (η * Real.sqrt s / γ * t)
          (CayleyClockInterface.moment γ) (ε / 2) : ℝ) + 1) *
          ((a : ℝ) + m + simR (CayleyClockInterface.width s γ) (η * Real.sqrt s / γ * t)
            (CayleyClockInterface.moment γ) (ε / 2) + 1) := by
      exact_mod_cast hG
    have hamr : (0 : ℝ) ≤ (a : ℝ) + m + simR (CayleyClockInterface.width s γ)
        (η * Real.sqrt s / γ * t) (CayleyClockInterface.moment γ) (ε / 2) + 1 :=
      add_nonneg (add_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)) zero_le_one
    refine hGR.trans (mul_le_mul_of_nonneg_right (by linarith) hamr)
  · have h := (Nat.cast_le (α := ℝ)).mpr hr2
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h
    linarith

end

end SparseHamiltonian.GateCircuit.SlotSim
