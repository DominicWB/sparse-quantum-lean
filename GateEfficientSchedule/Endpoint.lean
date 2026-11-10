import GateEfficientSchedule.Circuit
import GateEfficientSchedule.Manuscript

/-!
# Theorem `hs:thm:gates` with the manuscript's schedule (exact gates)

The manuscript's schedule (equations `hs:eq:gate-schedule` and `hs:eq:gate-clocks`):

* `W = αTν` (here `τ q̄`, with `τ = αT` and `q̄ = ν`), `b_av = 32Q`,
  `k = ⌈4W/Q + log₂(4096/ε)⌉`, `d = k (b_av - 1)`;
* `M = 2^{m_slot}` the least power of two at least `max{2, 4αT, (αT)^{3/2}/√(3ε)}`;
* `r = r_reuse = ⌈log₂(2d+2)⌉`.

`simCircuitMs a τ Q q̄ ε` is the released gate-level circuit with exactly this filter depth
(`depthMs`), this slot count (`slotMs`) and this reuse register (`simRK`). Its error budget is the
manuscript's: filter accuracy `δ = ε/8` (amplified error `2δ = ε/4`, by `depthMs_admissible`) and
Cayley discretisation `ε/4` (by the sharp local error `w³/12`,
`hamiltonian_cayley_error_sharp`), so the full output error before gate approximation is `ε/2`.

* `meshMs`, `slotMs`: the threshold `max{2, 4τ, √(τ³/(3ε))}` (`√(τ³/(3ε)) = τ^{3/2}/√(3ε)`) and
  `m = m_slot = log₂ M` (`slotMs_spec`: `M ≥` the threshold and `M` is the least such power of two);
* `mesh_budget`: such an `M` has step `w = τ/M ≤ 1/4` and Cayley error `M w³/12 ≤ ε/4`;
* `gate_efficient_simulation_ms`: valid elementary instructions, exactly `6d` private Cayley
  calls and `12d` calls of `U_J` or `U_J†`, at most `200 (d+1)(a+m+r+1)` elementary gates on
  `2a + 3m + 6r + 3` qubits, full-output error at most `ε/2` against `exp(-iτH)` on clean inputs,
  and `d ≤ 128 W + 32 Q (log₂(4096/ε) + 1)`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSchedule

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim
open scoped InnerProduct

/-! ### The slot count -/

/-- The manuscript's slot threshold `max{2, 4τ, τ^{3/2}/√(3ε)}` (equation `hs:eq:gate-clocks`),
written with `τ^{3/2}/√(3ε) = √(τ³/(3ε))`. -/
def meshMs (τ ε : ℝ) : ℝ := max 2 (max (4 * τ) (Real.sqrt (τ ^ 3 / (3 * ε))))

/-- `m = log₂ M` for the least power of two `M` at least `meshMs τ ε`. -/
def slotMs (τ ε : ℝ) : ℕ := Nat.clog 2 ⌈meshMs τ ε⌉₊

/-- **The manuscript's slot count**: `M = 2^m` is at least the threshold, and it is the least
power of two with this property; `m ≥ 1`. -/
theorem slotMs_spec (τ ε : ℝ) :
    meshMs τ ε ≤ 2 ^ slotMs τ ε ∧ (∀ j : ℕ, meshMs τ ε ≤ 2 ^ j → slotMs τ ε ≤ j) ∧
      1 ≤ slotMs τ ε := by
  have h2 : (2 : ℝ) ≤ meshMs τ ε := le_max_left _ _
  refine ⟨?_, fun j hj => ?_, ?_⟩
  · have h1 : meshMs τ ε ≤ (⌈meshMs τ ε⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : ((⌈meshMs τ ε⌉₊ : ℕ) : ℝ) ≤ ((2 ^ slotMs τ ε : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_pow_clog (by norm_num) _
    push_cast at h3
    linarith
  · apply Nat.clog_le_of_le_pow
    apply Nat.ceil_le.mpr
    exact_mod_cast hj
  · apply Nat.clog_pos (by norm_num)
    have : (1 : ℝ) < (⌈meshMs τ ε⌉₊ : ℝ) := by
      have := Nat.le_ceil (meshMs τ ε)
      linarith
    exact_mod_cast this

/-- **The slot budget**: `2^m ≥ max{2, 4τ, √(τ³/(3ε))}` gives the step `w = τ/2^m ≤ 1/4` and the
sharp Cayley error `2^m w³/12 ≤ ε/4`. -/
theorem mesh_budget (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε) (m : ℕ)
    (hm : meshMs τ ε ≤ 2 ^ m) :
    stepW τ m ≤ 1 / 4 ∧ ((2 ^ m : ℕ) : ℝ) * stepW τ m ^ 3 / 12 ≤ ε / 4 := by
  have hTm : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := by push_cast; rfl
  have hTp : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have h4 : 4 * τ ≤ (2 : ℝ) ^ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hs : Real.sqrt (τ ^ 3 / (3 * ε)) ≤ (2 : ℝ) ^ m :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  unfold stepW
  rw [hTm]
  constructor
  · rw [div_le_iff₀ hTp]
    linarith
  · have hratio : 0 ≤ τ ^ 3 / (3 * ε) := by positivity
    have h1 : τ ^ 3 / (3 * ε) ≤ ((2 : ℝ) ^ m) ^ 2 := by
      calc τ ^ 3 / (3 * ε) = (Real.sqrt (τ ^ 3 / (3 * ε))) ^ 2 := (Real.sq_sqrt hratio).symm
        _ ≤ ((2 : ℝ) ^ m) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
    have h2 : τ ^ 3 ≤ 3 * ε * ((2 : ℝ) ^ m) ^ 2 := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * ε)).mp h1
      linarith
    have e : (2 : ℝ) ^ m * (τ / (2 : ℝ) ^ m) ^ 3 / 12 = τ ^ 3 / (12 * ((2 : ℝ) ^ m) ^ 2) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith

/-! ### The circuit with the manuscript's schedule -/

/-- The manuscript's filter repetitions for the clock budget `W = τ q̄`. -/
abbrev kMs (Q τ qbar ε : ℝ) : ℕ := depthMs Q (τ * qbar) ε

/-- The reuse register size `r = ⌈log₂(2d+2)⌉`. -/
abbrev rMs (Q τ qbar ε : ℝ) : ℕ := simRK Q (kMs Q τ qbar ε)

/-- The wires of the simulator with the manuscript's schedule. -/
abbrev SimWireMs (a : ℕ) (Q τ qbar ε : ℝ) := SimWireK a (slotMs τ ε) Q (kMs Q τ qbar ε)

/-- **The gate-level circuit with the manuscript's schedule.** -/
def simCircuitMs (a : ℕ) (τ Q qbar ε : ℝ) : List (Instr (SimWireMs a Q τ qbar ε)) :=
  simCircuitK a (slotMs τ ε) τ Q (kMs Q τ qbar ε)

/-- The degree of the circuit is the manuscript's `d = k (⌈32Q⌉ - 1)`. -/
theorem fDegK_kMs (Q τ qbar ε : ℝ) :
    fDegK Q (kMs Q τ qbar ε) = degreeMs Q (τ * qbar) ε := rfl

set_option maxRecDepth 8192 in
/-- **Gate-efficient sparse Hamiltonian simulation with the manuscript's schedule, exact gates**
(Theorem `hs:thm:gates`, before finite-set synthesis). Under the clock hypotheses of the
released analysis for the private Cayley operation `D` and `J = U_J ι₀`, with
`k = ⌈4τq̄/Q + log₂(4096/ε)⌉`, `d = k (⌈32Q⌉ - 1)`, `2^m` the least power of two at least
`max{2, 4τ, √(τ³/(3ε))}` and `r = ⌈log₂(2d+2)⌉`, the circuit `simCircuitMs a τ Q q̄ ε` consists
of valid elementary instructions, makes exactly `6d` private Cayley calls and `12d` calls of `U_J`
or `U_J†`, has at most `200 (d+1)(a+m+r+1)` elementary gates on `2a + 3m + 6r + 3` qubits, and its
full output on clean inputs (every work register included) is within `ε/2` of `exp(-iτH)`
(filter `2 · ε/8`, Cayley discretisation `ε/4`). -/
theorem gate_efficient_simulation_ms (a : ℕ) {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℂ P] [CompleteSpace P]
    (UJ D R1 : Anc a P →L[ℂ] Anc a P) (H : P →L[ℂ] P)
    (hUJ : IsUnitary UJ) (hD : IsUnitary D)
    (τ Q b qbar ε : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : (UJ ∘L iota0)† ∘L R1 ∘L (UJ ∘L iota0) = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ g ∈ simCircuitMs a τ Q qbar ε, g.Valid Wire.anc) ∧
    nPriv (simCircuitMs a τ Q qbar ε) = 6 * degreeMs Q (τ * qbar) ε ∧
    nUJ (simCircuitMs a τ Q qbar ε) = 12 * degreeMs Q (τ * qbar) ε ∧
    nGates (simCircuitMs a τ Q qbar ε) ≤
      200 * (degreeMs Q (τ * qbar) ε + 1) * (a + slotMs τ ε + rMs Q τ qbar ε + 1) ∧
    Fintype.card (SimWireMs a Q τ qbar ε) = 2 * a + 3 * slotMs τ ε + 6 * rMs Q τ qbar ε + 3 ∧
    ‖run (simSem UJ D) (simCircuitMs a τ Q qbar ε) ∘L io -
        io ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤ ε / 2 ∧
    (degreeMs Q (τ * qbar) ε : ℝ) ≤ 128 * (τ * qbar) + 32 * Q * (Real.logb 2 (4096 / ε) + 1) ∧
    meshMs τ ε ≤ 2 ^ slotMs τ ε ∧ (∀ j : ℕ, meshMs τ ε ≤ 2 ^ j → slotMs τ ε ≤ j) ∧
    2 * degreeMs Q (τ * qbar) ε + 2 ≤ 2 ^ rMs Q τ qbar ε ∧
    2 ^ rMs Q τ qbar ε ≤ 4 * (degreeMs Q (τ * qbar) ε + 1) := by
  have hq : 0 ≤ qbar := by nlinarith [sq_nonneg b]
  have hW : 0 ≤ τ * qbar := mul_nonneg hτ hq
  obtain ⟨hmesh, hleast, -⟩ := slotMs_spec τ ε
  obtain ⟨hwq, hcub⟩ := mesh_budget τ ε hτ hε (slotMs τ ε) hmesh
  have hk := depthMs_admissible Q (τ * qbar) ε hQ hW hε hε1
  have hδf : 0 < ε / 8 := by positivity
  have hδf1 : ε / 8 ≤ 1 := by linarith
  obtain ⟨hvalid, hP, hJ, hG, hcard, herr, hr1, hr2⟩ :=
    gate_efficient_simulation_k a (slotMs τ ε) UJ D R1 H hUJ hD τ Q b qbar hτ hQ hRight hLeft
      hR1 hBoundary hSelf hH hEndpoint hbq hqQ (ε / 8) (ε / 4) hδf hδf1 (kMs Q τ qbar ε) hk hwq
      hcub
  have hdeg := degreeMs_le Q (τ * qbar) ε hQ hW hε hε1
  rw [show simCircuitMs a τ Q qbar ε = simCircuitK a (slotMs τ ε) τ Q (kMs Q τ qbar ε) from rfl,
    ← fDegK_kMs]
  rw [← fDegK_kMs] at hdeg
  refine ⟨hvalid, hP, hJ, hG, hcard, ?_, hdeg, hmesh, hleast, hr1, hr2⟩
  refine herr.trans (le_of_eq ?_)
  ring

end

end SparseHamiltonian.GateSchedule
