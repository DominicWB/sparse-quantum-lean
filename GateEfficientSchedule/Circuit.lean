import GateEfficientHamiltonian.Circuit.Theorem
import GateEfficientSchedule.Depth
import GateEfficientSchedule.Cayley

/-!
# The exact-gate simulation circuit for every admissible filter depth and slot count

The released gate-level circuit (`GateCircuit.Sim.simCircuit`) fixes the filter depth
`SharpFilterSchedule.depth Q (τ q̄) (ε/3)` and the slot count `2^m ≥ steps τ (ε/3)`. Here both are
parameters: `simCircuitK a m τ Q k` is the same released circuit (`ampI`) with `2^m` time slots
and the filter of depth `k`, degree `d = k (⌈32Q⌉ - 1)`. It depends only on the public data.

* `amp_error_k`: for an admissible depth `k` at the filter accuracy `δf`
  (`GateSchedule.Admissible Q (τ q̄) δf k`) and a slot count with step `w = τ/2^m ≤ 1/4` and
  sharp Cayley budget `2^m w³/12 ≤ δc` (`hamiltonian_cayley_error_sharp`), the ideal amplified
  circuit is within `2 δf + δc` of `exp(-iτH)` on clean inputs.
* `gate_efficient_simulation_k`: the circuit consists of valid elementary instructions, makes
  exactly `6d` private Cayley calls and `12d` calls of `U_J` or `U_J†`, has at most
  `200 (d+1)(a+m+r+1)` elementary gates on `2a + 3m + 6r + 3` qubit wires, and its full output
  on clean inputs (every work register included) is within `2 δf + δc` of `exp(-iτH)`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSchedule

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim
open scoped InnerProduct BigOperators
open ChronologicalResolvent GlobalColligation ChronologicalCatalyst GlobalResolvent
  CoherentReuse

/-! ### The filter of depth `k` -/

/-- The filter degree `d = k (⌈32Q⌉ - 1)` of depth `k`. -/
abbrev fDegK (Q : ℝ) (k : ℕ) : ℕ := k * (SharpFilterSchedule.length Q - 1)

/-- The smoothing coefficients of depth `k`. -/
abbrev fCoefK (Q : ℝ) (k : ℕ) : ℕ → ℝ :=
  (AveragingPolynomial.filter (SharpFilterSchedule.length Q) k).coeff

/-- Signed branch weights of depth `k`, numbered. -/
def labWtK (Q : ℝ) (k : ℕ) : Fin ((fDegK Q k + 1) + (fDegK Q k + 1)) → ℝ :=
  fun ℓ => ReuseWeights.weight (fCoefK Q k) (fDegK Q k) ((labEquiv (fDegK Q k)).symm ℓ)

/-- Branch reuse lengths of depth `k`, numbered. -/
def labLenK (Q : ℝ) (k : ℕ) : Fin ((fDegK Q k + 1) + (fDegK Q k + 1)) → ℕ :=
  fun ℓ => ReuseWeights.length (fDegK Q k) ((labEquiv (fDegK Q k)).symm ℓ)

/-- The released filter is the depth `SharpFilterSchedule.depth`. -/
theorem fDeg_eq_fDegK (Q τ qbar ε : ℝ) :
    fDeg Q τ qbar ε = fDegK Q (SharpFilterSchedule.depth Q (τ * qbar) (ε / 3)) := rfl

theorem length_ge_one (Q : ℝ) (hQ : 1 ≤ Q) : 1 ≤ SharpFilterSchedule.length Q := by
  apply Nat.one_le_ceil_iff.mpr
  have := SharpFilterSchedule.length_ge Q
  linarith

theorem fDegK_pos (Q : ℝ) (k : ℕ) (hQ : 1 ≤ Q) (hk : 1 ≤ k) : 0 < fDegK Q k := by
  have hL : (1 : ℝ) ≤ ((SharpFilterSchedule.length Q - 1 : ℕ) : ℝ) :=
    hQ.trans (SharpFilterSchedule.length_sub_one_bounds Q hQ).1
  have hLnat : 1 ≤ SharpFilterSchedule.length Q - 1 := by exact_mod_cast hL
  exact Nat.mul_pos hk hLnat

theorem labLenK_spec (Q : ℝ) (k : ℕ) (hQ : 1 ≤ Q) (hk : 1 ≤ k) (ℓ) :
    0 < labLenK Q k ℓ ∧ labLenK Q k ℓ ≤ 2 * fDegK Q k :=
  ⟨ReuseWeights.length_pos _ (fDegK_pos Q k hQ hk) _,
    ReuseWeights.length_le _ (fDegK_pos Q k hQ hk) _⟩

theorem labWtK_mass (Q : ℝ) (k : ℕ) (hQ : 1 ≤ Q) (hk : 1 ≤ k) :
    ∑ ℓ, |labWtK Q k ℓ| = 2 := by
  have h := ReuseWeights.concrete_absolute_mass (SharpFilterSchedule.length Q) k
    (length_ge_one Q hQ) (fDegK_pos Q k hQ hk)
  rw [← h]
  exact Fintype.sum_equiv (labEquiv (fDegK Q k)).symm _ _ (fun ℓ => rfl)

/-! ### The error of the ideal circuit -/

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

theorem stepW_mul (τ : ℝ) (m : ℕ) : ((2 ^ m : ℕ) : ℝ) * stepW τ m = τ := by
  have hpos : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast Nat.two_pow_pos m
  unfold stepW
  field_simp

theorem stepW_nonneg (τ : ℝ) (m : ℕ) (hτ : 0 ≤ τ) : 0 ≤ stepW τ m :=
  div_nonneg hτ (Nat.cast_nonneg _)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- **Error of the ideal amplified circuit with an admissible depth and a sharp slot budget.**
With an admissible filter depth `k` at accuracy `δf` for the clock budget `τ q̄`, `2^m` slots of
step `w = τ/2^m ≤ 1/4` with `2^m w³/12 ≤ δc`, a reuse register with `2d + 2 ≤ 2^r`, and the clock
hypotheses of the released analysis for `J = U_J ι₀`, the ideal amplified circuit approximates the
exact evolution on clean inputs within `2 δf + δc`. -/
theorem amp_error_k (UJ D R1 : Vsp a P →L[ℂ] Vsp a P) (H : P →L[ℂ] P)
    (hUJ : IsUnitary UJ) (hDu : IsUnitary D)
    (τ Q b qbar : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : (UJ ∘L iota0)† ∘L R1 ∘L (UJ ∘L iota0) = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (δf δc : ℝ) (hδf : 0 < δf) (hδf1 : δf ≤ 1) (k : ℕ) (hk : Admissible Q (τ * qbar) δf k)
    (hwq : stepW τ m ≤ 1 / 4) (hcub : ((2 ^ m : ℕ) : ℝ) * stepW τ m ^ 3 / 12 ≤ δc)
    (hr : 0 < r) (hL : (fDegK Q k + 1) + (fDegK Q k + 1) ≤ 2 ^ r) :
    ‖AMP (K := K) (m := m) hL (labLenK Q k) (labWtK Q k)
        (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) UJ D
        (2 * fDegK Q k) ∘L io -
      io ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤ 2 * δf + δc := by
  have hw0 : 0 ≤ stepW τ m := stepW_nonneg τ m hτ
  have hTw := stepW_mul τ m
  have hD : D† ∘L D = 1 := unitary_adj_comp hDu
  have hUJc : UJ ∘L UJ† = 1 := unitary_comp_adj hUJ
  have hJ : (UJ ∘L iota0)† ∘L (UJ ∘L iota0) = 1 :=
    isometry_comp UJ iota0 (unitary_adj_comp hUJ) iota0_isometry
  have hk' : Admissible Q (((2 ^ m : ℕ) : ℝ) * stepW τ m * qbar) δf k := by
    rw [hTw]
    exact hk
  obtain ⟨U, R, hRR, -, hCay, hUi, -, -, hImpl⟩ :=
    exists_precise_implementation_k D R1 (UJ ∘L iota0) H (stepW τ m) Q b qbar (2 ^ m) hQ hw0
      hwq hD hJ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ δf hδf hδf1 k hk'
  obtain ⟨_, _, hκc, hσc, _⟩ := CayleyTransfer.scalar_promises (stepW τ m) hw0 hwq
  have hunit : CayleyTransfer.c (stepW τ m) ^ 2 + CayleyTransfer.sigma (stepW τ m) ^ 2 = 1 := by
    linarith
  have hLf : 1 ≤ SharpFilterSchedule.length Q := length_ge_one Q hQ
  have hd0 : 0 < fDegK Q k := fDegK_pos Q k hQ hk.pos
  have hJrel := SmoothingLCU.output_isometry (P := P) (V := HV a m P) (fCoefK Q k)
    (fDegK Q k) hd0 (ReuseWeights.concrete_absolute_mass _ _ hLf hd0)
  have hTrel := AmplifiedSmoothing.prepared_isometry (SharpFilterSchedule.length Q) k hLf hd0
    _ _ _ _ (released_step D (UJ ∘L iota0) (stepW τ m) hw0 hwq hD hJ (2 ^ m))
  -- the ideal LCU circuit
  have hn : ∀ ℓ, 0 < labLenK Q k ℓ ∧ labLenK Q k ℓ ≤ 2 * fDegK Q k :=
    labLenK_spec Q k hQ hk.pos
  have hN : 2 * fDegK Q k ≤ cap r := by
    have := cap_succ r
    omega
  have hLCUu := LCU_isUnitary (K := K) (m := m) hL (labLenK Q k) (labWtK Q k)
    (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) hunit UJ D hUJ hDu
    (2 * fDegK Q k)
  have hT' := isometry_comp (E := P) (F := Reg (Wire a m r K) P) (G := Reg (Wire a m r K) P) _
    (io (a := a) (m := m) (r := r) (K := K) (P := P)) (unitary_adj_comp hLCUu) io_isometry
  have hB := lcu_compression (K := K) (m := m) hL (labLenK Q k) (2 * fDegK Q k) hn hN
    hr (labWtK Q k) (labWtK_mass Q k hQ hk.pos) (CayleyTransfer.c (stepW τ m))
    (CayleyTransfer.kappa (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) hunit hκc UJ D hUJc
  rw [blkB_net, blkC_net, blkG_net _ _ _ UJ D hUJc] at hB
  have hB' : (io (a := a) (m := m) (r := r) (K := K) (P := P))† ∘L
      (LCU (K := K) (m := m) hL (labLenK Q k) (labWtK Q k)
        (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) UJ D
        (2 * fDegK Q k) ∘L io) =
      (SmoothingLCU.output (P := P) (V := HV a m P) (fCoefK Q k) (fDegK Q k))† ∘L
        AmplifiedSmoothing.prepared (SharpFilterSchedule.length Q) k
          (blkA (CayleyTransfer.c (stepW τ m)) (2 ^ m))
          (blkB (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m))
            (UJ ∘L iota0) D (2 ^ m))
          (blkC (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m))
            (UJ ∘L iota0) (2 ^ m))
          (blkG (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.kappa (stepW τ m))
            (CayleyTransfer.sigma (stepW τ m)) (UJ ∘L iota0) D (2 ^ m)) := by
    rw [hB]
    change _ = SmoothingLCU.successfulBlock (fCoefK Q k) (fDegK Q k) _ _ _ _
    rw [smoothing_block_eq]
    exact reindex_block (fDegK Q k) _ _ (fun n => successfulBlock _ _ _ _ n)
  have hAmp := GateBlockTransfer.amplified_error_le (P := P)
    (K := PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := HV a m P) (fDegK Q k)))
    (K' := Reg (Wire a m r K) P)
    (SmoothingLCU.output (P := P) (V := HV a m P) (fCoefK Q k) (fDegK Q k))
    (AmplifiedSmoothing.prepared (SharpFilterSchedule.length Q) k
      (blkA (CayleyTransfer.c (stepW τ m)) (2 ^ m))
      (blkB (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m))
        (UJ ∘L iota0) D (2 ^ m))
      (blkC (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m))
        (UJ ∘L iota0) (2 ^ m))
      (blkG (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.kappa (stepW τ m))
        (CayleyTransfer.sigma (stepW τ m)) (UJ ∘L iota0) D (2 ^ m)))
    (io (a := a) (m := m) (r := r) (K := K) (P := P))
    (LCU (K := K) (m := m) hL (labLenK Q k) (labWtK Q k)
        (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) UJ D
        (2 * fDegK Q k) ∘L io)
    hJrel hTrel io_isometry hT' hB' (U ^ (2 ^ m)) hUi
  have hAmp2 := hAmp.trans hImpl
  -- Cayley powers against the exponential, with the sharp constant
  have hRR' : CayleyTransfer.cayleyDenominator (stepW τ m) H * R = 1 := by
    rw [mul_def]; exact hRR
  have hCayErr := hamiltonian_cayley_error_sharp H R (stepW τ m) hw0 hSelf hH hRR' (2 ^ m)
  have hTwC : ((2 ^ m : ℕ) : ℂ) * (stepW τ m : ℂ) = (τ : ℂ) := by exact_mod_cast hTw
  have hScalar : -Complex.I * ((2 ^ m : ℕ) : ℂ) * (stepW τ m : ℂ) = -Complex.I * (τ : ℂ) := by
    rw [mul_assoc, hTwC]
  have hUT : (CayleyTransfer.cayleyNumerator (stepW τ m) H * R) ^ (2 ^ m) = U ^ (2 ^ m) := by
    rw [hCay, mul_def]
  rw [hUT, hScalar] at hCayErr
  have hTarget : ‖U ^ (2 ^ m) - NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤ δc :=
    hCayErr.trans hcub
  -- assemble
  rw [AMP_io hL _ _ _ _ UJ D _ (unitary_comp_adj hLCUu)]
  calc _ ≤ ‖reflectedAmplification io (LCU (K := K) (m := m) hL (labLenK Q k)
          (labWtK Q k) (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m))
          UJ D (2 * fDegK Q k) ∘L io) - io ∘L U ^ (2 ^ m)‖ +
          ‖io ∘L U ^ (2 ^ m) - io ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * δf + δc := by
        apply add_le_add hAmp2
        rw [← comp_sub]
        calc ‖io ∘L (U ^ (2 ^ m) - NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H))‖
            ≤ ‖(io (a := a) (m := m) (r := r) (K := K) (P := P))‖ *
                ‖U ^ (2 ^ m) - NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ :=
              opNorm_comp_le _ _
          _ ≤ 1 * δc := mul_le_mul io_norm_le hTarget (norm_nonneg _) zero_le_one
          _ = δc := one_mul _

/-! ### The circuit -/

/-- Size of the reuse pointer and label registers for the filter of depth `k`. -/
def simRK (Q : ℝ) (k : ℕ) : ℕ := Nat.clog 2 (2 * fDegK Q k + 2)

/-- Size of the AND-chain pool. -/
def simKK (a m : ℕ) (Q : ℝ) (k : ℕ) : ℕ := a + m + 2 * simRK Q k

/-- The wires of the simulator with `2^m` slots and the filter of depth `k`. -/
abbrev SimWireK (a m : ℕ) (Q : ℝ) (k : ℕ) := Wire a m (simRK Q k) (simKK a m Q k)

theorem simRK_spec (Q : ℝ) (k : ℕ) :
    2 * fDegK Q k + 2 ≤ 2 ^ simRK Q k ∧ 0 < simRK Q k ∧
      2 ^ simRK Q k ≤ 4 * (fDegK Q k + 1) := by
  have h1 : 1 < 2 * fDegK Q k + 2 := by omega
  refine ⟨Nat.le_pow_clog (by norm_num) _, Nat.clog_pos (by norm_num) h1, ?_⟩
  have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h1
  have hpos : 0 < simRK Q k := Nat.clog_pos (by norm_num) h1
  unfold simRK at hpos ⊢
  have : 2 ^ Nat.clog 2 (2 * fDegK Q k + 2) =
      2 * 2 ^ (Nat.clog 2 (2 * fDegK Q k + 2)).pred := by
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
    rw [pow_succ]; ring
  omega

theorem simLK (Q : ℝ) (k : ℕ) : (fDegK Q k + 1) + (fDegK Q k + 1) ≤ 2 ^ simRK Q k := by
  have := (simRK_spec Q k).1
  omega

/-- **The gate-level simulation circuit with `2^m` slots and the filter of depth `k`.** It is
the released circuit `ampI`; it is fixed by the public data `a, m, τ, Q, k`. -/
def simCircuitK (a m : ℕ) (τ Q : ℝ) (k : ℕ) : List (Instr (SimWireK a m Q k)) :=
  ampI (simLK Q k) (labLenK Q k) (labWtK Q k)
    (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) (2 * fDegK Q k)

theorem card_simWireK (a m : ℕ) (Q : ℝ) (k : ℕ) :
    Fintype.card (SimWireK a m Q k) = 2 * a + 3 * m + 6 * simRK Q k + 3 := by
  rw [card_wire, simKK]
  ring

set_option maxRecDepth 8192 in
/-- **Gate-efficient sparse Hamiltonian simulation with exact gates, for every admissible filter
depth and slot count.** Under the clock hypotheses of the released analysis for the private
Cayley operation `D` and `J = U_J ι₀`, an admissible depth `k` at the filter accuracy `δf`, and
`2^m` slots of step `w = τ/2^m ≤ 1/4` with `2^m w³/12 ≤ δc`, the circuit `simCircuitK a m τ Q k`
consists of valid elementary instructions, makes exactly `6d` private Cayley calls and `12d` calls
of `U_J` or `U_J†` (`d = k (⌈32Q⌉ - 1)`), has at most `200 (d+1)(a+m+r+1)` elementary gates on
`2a + 3m + 6r + 3` qubits with `2d + 2 ≤ 2^r ≤ 4(d+1)`, and its full output on clean inputs is
within `2 δf + δc` of `exp(-iτH)`. -/
theorem gate_efficient_simulation_k (a m : ℕ) {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℂ P] [CompleteSpace P]
    (UJ D R1 : Anc a P →L[ℂ] Anc a P) (H : P →L[ℂ] P)
    (hUJ : IsUnitary UJ) (hD : IsUnitary D)
    (τ Q b qbar : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : (UJ ∘L iota0)† ∘L R1 ∘L (UJ ∘L iota0) = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (δf δc : ℝ) (hδf : 0 < δf) (hδf1 : δf ≤ 1) (k : ℕ) (hk : Admissible Q (τ * qbar) δf k)
    (hwq : stepW τ m ≤ 1 / 4) (hcub : ((2 ^ m : ℕ) : ℝ) * stepW τ m ^ 3 / 12 ≤ δc) :
    (∀ g ∈ simCircuitK a m τ Q k, g.Valid Wire.anc) ∧
    nPriv (simCircuitK a m τ Q k) = 6 * fDegK Q k ∧
    nUJ (simCircuitK a m τ Q k) = 12 * fDegK Q k ∧
    nGates (simCircuitK a m τ Q k) ≤ 200 * (fDegK Q k + 1) * (a + m + simRK Q k + 1) ∧
    Fintype.card (SimWireK a m Q k) = 2 * a + 3 * m + 6 * simRK Q k + 3 ∧
    ‖run (simSem UJ D) (simCircuitK a m τ Q k) ∘L io -
        io ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤ 2 * δf + δc ∧
    2 * fDegK Q k + 2 ≤ 2 ^ simRK Q k ∧ 2 ^ simRK Q k ≤ 4 * (fDegK Q k + 1) := by
  obtain ⟨hr1, hr0, hr2⟩ := simRK_spec Q k
  have hw0 : 0 ≤ stepW τ m := stepW_nonneg τ m hτ
  obtain ⟨_, _, _, hσc, _⟩ := CayleyTransfer.scalar_promises (stepW τ m) hw0 hwq
  have hunit : CayleyTransfer.c (stepW τ m) ^ 2 + CayleyTransfer.sigma (stepW τ m) ^ 2 = 1 := by
    linarith
  have hN : 2 * fDegK Q k ≤ cap (simRK Q k) + 1 := by
    have := cap_succ (simRK Q k)
    omega
  obtain ⟨hc1, hc2, hc3⟩ := ampI_counts (a := a) (m := m) (K := simKK a m Q k)
    (simLK Q k) (labLenK Q k) (labWtK Q k) (CayleyTransfer.c (stepW τ m))
    (CayleyTransfer.sigma (stepW τ m)) (2 * fDegK Q k) hN
  have hn : ∀ ℓ, labLenK Q k ℓ < 2 ^ simRK Q k := by
    intro ℓ
    have := (labLenK_spec Q k hQ hk.pos ℓ).2
    omega
  have hK : a + m + 2 * simRK Q k ≤ simKK a m Q k := le_rfl
  have hagree := amp_agrees (P := P) (a := a) (m := m) (K := simKK a m Q k) UJ D hUJ hD
    (simLK Q k) (labLenK Q k) (labWtK Q k)
    (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) hunit
    (2 * fDegK Q k) hn hK
  have herr := amp_error_k (K := simKK a m Q k) (m := m) UJ D R1 H hUJ hD τ Q b
    qbar hτ hQ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ δf δc hδf hδf1 k hk hwq hcub
    hr0 (simLK Q k)
  have hgb := gate_bound a m (simRK Q k) (fDegK Q k) (2 ^ simRK Q k) hr2
  refine ⟨ampI_valid _ _ _ _ _ hunit _, ?_, ?_, ?_, card_simWireK a m Q k, ?_, hr1, hr2⟩
  · unfold simCircuitK; rw [hc1]; ring
  · unfold simCircuitK; rw [hc2]; ring
  · unfold simCircuitK
    refine hc3.trans (le_of_eq_of_le ?_ hgb)
    ring
  · have hio : run (simSem UJ D) (simCircuitK a m τ Q k) ∘L io =
        AMP (K := simKK a m Q k) (m := m) (simLK Q k) (labLenK Q k)
          (labWtK Q k) (CayleyTransfer.c (stepW τ m))
          (CayleyTransfer.sigma (stepW τ m)) UJ D (2 * fDegK Q k) ∘L io := by
      unfold simCircuitK
      refine ContinuousLinearMap.ext (fun ψ => ?_)
      rw [comp_apply, comp_apply, io_apply]
      exact hagree _ (supp_bas _ (fun w _ => rfl) ψ)
    rw [hio]
    exact herr

end

end SparseHamiltonian.GateSchedule
