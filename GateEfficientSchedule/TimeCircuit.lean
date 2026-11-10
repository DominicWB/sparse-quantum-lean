import GateEfficientSchedule.Circuit
import GateEfficientSchedule.TimeClock
import GateEfficientSchedule.TimeMesh
import GateEfficientSchedule.Manuscript
import GateEfficientTimeDependent.Theorem

/-!
# The time-dependent gate-level simulation (Theorem `hs:thm:time` with the circuit of `hs:thm:gates`) with the manuscript's schedule (exact gates)

A package extension, Theorem `hs:thm:time` with the circuit of `hs:thm:gates`, states that, for the
time-dependent setting of `hs:thm:time` on a uniform mesh of `M = 2^m ≥ 2` slots satisfying
`hs:eq:timegrid`, *the same circuit* with slot-selected private Cayley operations has full-output
error at most `ε` relative to `U_H(T, 0)`; in the manuscript Theorem `hs:thm:gates` is "a
time-independent result", and a circuit of this kind is the single-label case of Lemma
`ode:lem:gate-select`. The released formal version
(`SlotSim.gate_efficient_time_simulation`) uses the released filter depth and the released constants
of the discretisation estimate. Here:

* `simCircuitTK a m τ Q k`: the released slot circuit (`ampI`) with `2^m` slots and the filter of
  depth `k`;
* `ampT_error_k`, `simulationT_k`: for an admissible depth at the filter accuracy `δf` and a slot
  count with `w = τ/2^m ≤ 1/4` and sharp Cayley budget `2^m (wλ)³/12 ≤ δc` (`‖H̃_k/α‖ ≤ λ`), the
  circuit is within `2 δf + δc` of the ordered product of the slot exponentials;
* `propagator_error_k`: against every propagator of a `β`-Lipschitz Hermitian path with samples
  within `δ`, the error is at most `2 δf + δc + β t²/(2·2^m) + t δ` (`mesh_error_sharp`);
* `timegridMs`: the threshold `max{1, 4αT, 6βT²/ε, (ΛT)^{3/2}/√ε}` of equation
  `hs:eq:timegrid`, written `max{1, 4αT, 6βT²/ε, √((ΛT)³/ε)}`, where `Λ ≤ α` bounds the
  represented samples; `timegrid_budget`: it gives `w ≤ 1/4`, Cayley error at most `ε/12` and
  freezing error at most `ε/12`;
* `gate_efficient_time_simulation_ms`: with the manuscript's depth `k = ⌈4αTq̄/Q +
  log₂(4096/ε)⌉` (filter accuracy `ε/8`), `2^m ≥ timegridMs` and the sample budget
  `T δ ≤ ε/12`, the circuit has exactly `6d` slot-selected private calls and `12d` calls of `U_J`
  or `U_J†`, at most `200 (d+1)(a+m+r+1)` elementary gates on `2a + 3m + 6r + 3` qubits, and full
  output within `ε/2` of `U(t)` for every propagator `U` (filter `ε/4`, Cayley `ε/12`, freezing
  `ε/12`, samples `ε/12`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSchedule

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim GateCircuit.SlotSim
open scoped InnerProduct BigOperators
open ChronologicalResolvent GlobalColligation ChronologicalCatalyst GlobalResolvent
  CoherentReuse

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- **Error of the ideal amplified slot-selected circuit with an admissible depth and a sharp
slot budget**: within `2 δf + δc` of the ordered product of the slot exponentials. -/
theorem ampT_error_k (UJ : Vsp a P →L[ℂ] Vsp a P) (D R1 : ℕ → Vsp a P →L[ℂ] Vsp a P)
    (H : ℕ → P →L[ℂ] P) (hUJ : IsUnitary UJ) (hDu : ∀ j, IsUnitary (D j))
    (τ Q b qbar lam : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hRight : ∀ j, (1 - D j) ∘L R1 j = 1) (hLeft : ∀ j, R1 j ∘L (1 - D j) = 1)
    (hR1 : ∀ j, ‖R1 j‖ ≤ Q)
    (hBoundary : ∀ j, (UJ ∘L iota0)† ∘L R1 j ∘L (UJ ∘L iota0) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • H j))
    (hSelf : ∀ j, star (H j) = H j) (hH : ∀ j, ‖H j‖ ≤ 1) (hHlam : ∀ j, ‖H j‖ ≤ lam)
    (hEndpoint : ∀ j, ‖R1 j ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (δf δc : ℝ) (hδf : 0 < δf) (hδf1 : δf ≤ 1) (k : ℕ) (hk : Admissible Q (τ * qbar) δf k)
    (hwq : stepW τ m ≤ 1 / 4)
    (hcub : ((2 ^ m : ℕ) : ℝ) * ((stepW τ m * lam) ^ 3 / 12) ≤ δc)
    (hr : 0 < r) (hL : (fDegK Q k + 1) + (fDegK Q k + 1) ≤ 2 ^ r) :
    ‖AMPT (K := K) (m := m) hL (labLenK Q k) (labWtK Q k)
        (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) UJ D
        (2 * fDegK Q k) ∘L io -
      io ∘L TimeDependent.evolution
        (fun j => NormedSpace.exp ((-Complex.I * (stepW τ m : ℂ)) • H j)) (2 ^ m)‖ ≤
      2 * δf + δc := by
  have hw0 : 0 ≤ stepW τ m := stepW_nonneg τ m hτ
  have hTw := stepW_mul τ m
  have hD : ∀ j, (D j)† ∘L D j = 1 := fun j => unitary_adj_comp (hDu j)
  have hUJc : UJ ∘L UJ† = 1 := unitary_comp_adj hUJ
  have hJ : (UJ ∘L iota0)† ∘L (UJ ∘L iota0) = 1 :=
    isometry_comp UJ iota0 (unitary_adj_comp hUJ) iota0_isometry
  have hk' : Admissible Q (((2 ^ m : ℕ) : ℝ) * stepW τ m * qbar) δf k := by
    rw [hTw]
    exact hk
  obtain ⟨U, R, hRR, -, hCay, -, hImpl⟩ :=
    exists_precise_implementationV_k D R1 (UJ ∘L iota0) H (stepW τ m) Q b qbar (2 ^ m) hQ hw0
      hwq hD hJ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ δf hδf hδf1 k hk'
  obtain ⟨_, _, hκc, hσc, _⟩ := CayleyTransfer.scalar_promises (stepW τ m) hw0 hwq
  have hunit : CayleyTransfer.c (stepW τ m) ^ 2 + CayleyTransfer.sigma (stepW τ m) ^ 2 = 1 := by
    linarith
  have hLf : 1 ≤ SharpFilterSchedule.length Q := length_ge_one Q hQ
  have hd0 : 0 < fDegK Q k := fDegK_pos Q k hQ hk.pos
  have hJrel := SmoothingLCU.output_isometry (P := P) (V := HV a m P) (fCoefK Q k)
    (fDegK Q k) hd0 (ReuseWeights.concrete_absolute_mass _ _ hLf hd0)
  have hTrel := AmplifiedSmoothing.prepared_isometry (SharpFilterSchedule.length Q) k hLf hd0
    _ _ _ _ (TimeDependent.step_energy D (UJ ∘L iota0) hJ hD (stepW τ m) hw0 hwq (2 ^ m))
  have hn : ∀ ℓ, 0 < labLenK Q k ℓ ∧ labLenK Q k ℓ ≤ 2 * fDegK Q k :=
    labLenK_spec Q k hQ hk.pos
  have hN : 2 * fDegK Q k ≤ cap r := by
    have := cap_succ r
    omega
  have hLCUu := LCUT_isUnitary (K := K) (m := m) hL (labLenK Q k) (labWtK Q k)
    (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) hunit UJ D hUJ
    (fun j _ => hDu j) (2 * fDegK Q k)
  have hT' := isometry_comp (E := P) (F := Reg (Wire a m r K) P) (G := Reg (Wire a m r K) P) _
    (io (a := a) (m := m) (r := r) (K := K) (P := P)) (unitary_adj_comp hLCUu) io_isometry
  have hB := lcu_compressionT (K := K) (m := m) hL (labLenK Q k) (2 * fDegK Q k) hn
    hN hr (labWtK Q k) (labWtK_mass Q k hQ hk.pos) (CayleyTransfer.c (stepW τ m))
    (CayleyTransfer.kappa (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) hunit hκc UJ D hUJc
  rw [netB_slot, blkC_net, netG_slot _ _ _ UJ D hUJc] at hB
  have hB' : (io (a := a) (m := m) (r := r) (K := K) (P := P))† ∘L
      (LCUT (K := K) (m := m) hL (labLenK Q k) (labWtK Q k)
        (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) UJ D
        (2 * fDegK Q k) ∘L io) =
      (SmoothingLCU.output (P := P) (V := HV a m P) (fCoefK Q k) (fDegK Q k))† ∘L
        AmplifiedSmoothing.prepared (SharpFilterSchedule.length Q) k
          (blkA (CayleyTransfer.c (stepW τ m)) (2 ^ m))
          (TimeDependent.exitV D (UJ ∘L iota0) (CayleyTransfer.c (stepW τ m))
            (CayleyTransfer.sigma (stepW τ m)) (2 ^ m))
          (blkC (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m))
            (UJ ∘L iota0) (2 ^ m))
          (TimeDependent.privateV D (UJ ∘L iota0) (CayleyTransfer.c (stepW τ m))
            (CayleyTransfer.kappa (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) (2 ^ m)) := by
    rw [hB]
    change _ = SmoothingLCU.successfulBlock (fCoefK Q k) (fDegK Q k) _ _ _ _
    rw [smoothing_block_eq]
    exact reindex_block (fDegK Q k) _ _ (fun n => successfulBlock _ _ _ _ n)
  have hUk : ∀ j, (U j)† ∘L U j = 1 := by
    intro j
    rw [hCay j]
    exact cayley_isometry (H j) (R j) _ (hSelf j) (hRR j)
  have hUiso : (TimeDependent.evolution U (2 ^ m))† ∘L TimeDependent.evolution U (2 ^ m) = 1 :=
    evolution_isometry U hUk (2 ^ m)
  have hAmp := GateBlockTransfer.amplified_error_le (P := P)
    (K := PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := HV a m P) (fDegK Q k)))
    (K' := Reg (Wire a m r K) P)
    (SmoothingLCU.output (P := P) (V := HV a m P) (fCoefK Q k) (fDegK Q k))
    (AmplifiedSmoothing.prepared (SharpFilterSchedule.length Q) k
      (blkA (CayleyTransfer.c (stepW τ m)) (2 ^ m))
      (TimeDependent.exitV D (UJ ∘L iota0) (CayleyTransfer.c (stepW τ m))
        (CayleyTransfer.sigma (stepW τ m)) (2 ^ m))
      (blkC (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m))
        (UJ ∘L iota0) (2 ^ m))
      (TimeDependent.privateV D (UJ ∘L iota0) (CayleyTransfer.c (stepW τ m))
        (CayleyTransfer.kappa (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) (2 ^ m)))
    (io (a := a) (m := m) (r := r) (K := K) (P := P))
    (LCUT (K := K) (m := m) hL (labLenK Q k) (labWtK Q k)
        (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) UJ D
        (2 * fDegK Q k) ∘L io)
    hJrel hTrel io_isometry hT' hB' (TimeDependent.evolution U (2 ^ m)) hUiso
  have hAmp2 := hAmp.trans hImpl
  have hCayErr := cayley_evolution_error_sharp H R U (stepW τ m) lam hw0 hSelf hHlam hRR hCay
    (2 ^ m)
  have hTarget : ‖TimeDependent.evolution U (2 ^ m) - TimeDependent.evolution
      (fun j => NormedSpace.exp ((-Complex.I * (stepW τ m : ℂ)) • H j)) (2 ^ m)‖ ≤ δc :=
    hCayErr.trans hcub
  rw [AMPT_io hL _ _ _ _ UJ D _ (unitary_comp_adj hLCUu)]
  calc _ ≤ ‖reflectedAmplification io (LCUT (K := K) (m := m) hL (labLenK Q k)
          (labWtK Q k) (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m))
          UJ D (2 * fDegK Q k) ∘L io) - io ∘L TimeDependent.evolution U (2 ^ m)‖ +
          ‖io ∘L TimeDependent.evolution U (2 ^ m) - io ∘L TimeDependent.evolution
            (fun j => NormedSpace.exp ((-Complex.I * (stepW τ m : ℂ)) • H j)) (2 ^ m)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * δf + δc := by
        apply add_le_add hAmp2
        rw [← comp_sub]
        calc _ ≤ ‖(io (a := a) (m := m) (r := r) (K := K) (P := P))‖ *
                ‖TimeDependent.evolution U (2 ^ m) - TimeDependent.evolution
                  (fun j => NormedSpace.exp ((-Complex.I * (stepW τ m : ℂ)) • H j)) (2 ^ m)‖ :=
              opNorm_comp_le _ _
          _ ≤ 1 * δc := mul_le_mul io_norm_le hTarget (norm_nonneg _) zero_le_one
          _ = δc := one_mul _

/-! ### The gate-level statement -/

/-- **The slot circuit with `2^m` slots and the filter of depth `k`**: the released circuit
`ampI`, fixed by the public data `a, m, τ, Q, k`. -/
def simCircuitTK (a m : ℕ) (τ Q : ℝ) (k : ℕ) : List (Instr (SimWireK a m Q k)) :=
  ampI (simLK Q k) (labLenK Q k) (labWtK Q k)
    (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) (2 * fDegK Q k)

set_option maxRecDepth 8192 in
/-- **Gate-efficient slot-selected simulation with exact gates, for every admissible depth.**
For the slot-selected private Cayley operations `D j` with the clock promises at every slot
`j < 2^m` for the normalised samples `H j` (`‖H j‖ ≤ 1`, `‖H j‖ ≤ λ`), an admissible depth `k` at
the filter accuracy `δf` and `2^m` slots with `w = τ/2^m ≤ 1/4` and `2^m (wλ)³/12 ≤ δc`: valid
elementary instructions, exactly `6d` slot-selected private calls and `12d` calls of `U_J` or
`U_J†`, at most `200 (d+1)(a+m+r+1)` elementary gates on `2a + 3m + 6r + 3` qubits, and full output
on clean inputs within `2 δf + δc` of `exp(-iwH(2^m-1)) ⋯ exp(-iwH(0))`. -/
theorem simulationT_k (a m : ℕ) (UJ : Vsp a P →L[ℂ] Vsp a P) (D R1 : ℕ → Vsp a P →L[ℂ] Vsp a P)
    (H : ℕ → P →L[ℂ] P) (hUJ : IsUnitary UJ) (hD : ∀ j < 2 ^ m, IsUnitary (D j))
    (τ Q b qbar lam : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hRight : ∀ j < 2 ^ m, (1 - D j) ∘L R1 j = 1)
    (hLeft : ∀ j < 2 ^ m, R1 j ∘L (1 - D j) = 1) (hR1 : ∀ j < 2 ^ m, ‖R1 j‖ ≤ Q)
    (hBoundary : ∀ j < 2 ^ m, (UJ ∘L iota0)† ∘L R1 j ∘L (UJ ∘L iota0) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • H j))
    (hSelf : ∀ j < 2 ^ m, star (H j) = H j) (hH : ∀ j < 2 ^ m, ‖H j‖ ≤ 1)
    (hHlam : ∀ j < 2 ^ m, ‖H j‖ ≤ lam)
    (hEndpoint : ∀ j < 2 ^ m, ‖R1 j ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2)
    (hqQ : qbar ≤ Q) (δf δc : ℝ) (hδf : 0 < δf) (hδf1 : δf ≤ 1) (k : ℕ)
    (hk : Admissible Q (τ * qbar) δf k) (hwq : stepW τ m ≤ 1 / 4)
    (hcub : ((2 ^ m : ℕ) : ℝ) * ((stepW τ m * lam) ^ 3 / 12) ≤ δc) :
    (∀ g ∈ simCircuitTK a m τ Q k, g.Valid Wire.anc) ∧
    nPriv (simCircuitTK a m τ Q k) = 6 * fDegK Q k ∧
    nUJ (simCircuitTK a m τ Q k) = 12 * fDegK Q k ∧
    nGates (simCircuitTK a m τ Q k) ≤ 200 * (fDegK Q k + 1) * (a + m + simRK Q k + 1) ∧
    Fintype.card (SimWireK a m Q k) = 2 * a + 3 * m + 6 * simRK Q k + 3 ∧
    ‖runT UJ D (simCircuitTK a m τ Q k) ∘L io -
        io ∘L TimeDependent.evolution
          (fun j => NormedSpace.exp ((-Complex.I * (stepW τ m : ℂ)) • H j)) (2 ^ m)‖ ≤
      2 * δf + δc ∧
    2 * fDegK Q k + 2 ≤ 2 ^ simRK Q k ∧ 2 ^ simRK Q k ≤ 4 * (fDegK Q k + 1) := by
  obtain ⟨hr1, hr0, hr2⟩ := simRK_spec Q k
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  have hcl := min_pred_lt hpos
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
  have hDc : ∀ j, IsUnitary (clampAt (2 ^ m) D j) := fun j => hD _ (hcl j)
  have hagree := ampT_agrees (P := P) (a := a) (m := m) (K := simKK a m Q k) UJ
    (clampAt (2 ^ m) D) hUJ (fun j _ => hDc j) (simLK Q k) (labLenK Q k) (labWtK Q k)
    (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) hunit
    (2 * fDegK Q k) hn le_rfl
  have herr := ampT_error_k (K := simKK a m Q k) (m := m) UJ
    (clampAt (2 ^ m) D) (clampAt (2 ^ m) R1) (clampAt (2 ^ m) H) hUJ hDc τ Q b qbar lam hτ hQ
    (fun j => hRight _ (hcl j)) (fun j => hLeft _ (hcl j)) (fun j => hR1 _ (hcl j))
    (fun j => hBoundary _ (hcl j)) (fun j => hSelf _ (hcl j)) (fun j => hH _ (hcl j))
    (fun j => hHlam _ (hcl j)) (fun j => hEndpoint _ (hcl j)) hbq hqQ δf δc hδf hδf1 k hk hwq
    hcub hr0 (simLK Q k)
  have hgb := gate_bound a m (simRK Q k) (fDegK Q k) (2 ^ simRK Q k) hr2
  have hrunD : runT UJ D (simCircuitTK a m τ Q k) =
      runT UJ (clampAt (2 ^ m) D) (simCircuitTK a m τ Q k) :=
    runT_congr UJ D _ (fun j hj => (clampAt_of_lt (2 ^ m) D hj).symm) _
  have hevol : TimeDependent.evolution
      (fun j => NormedSpace.exp ((-Complex.I * (stepW τ m : ℂ)) • H j)) (2 ^ m) =
      TimeDependent.evolution
      (fun j => NormedSpace.exp ((-Complex.I * (stepW τ m : ℂ)) • clampAt (2 ^ m) H j)) (2 ^ m) :=
    evolution_eq_of_lt _ _ (2 ^ m) (fun j hj => by rw [clampAt_of_lt (2 ^ m) H hj])
  refine ⟨ampI_valid _ _ _ _ _ hunit _, ?_, ?_, ?_, card_simWireK a m Q k, ?_, hr1, hr2⟩
  · unfold simCircuitTK; rw [hc1]; ring
  · unfold simCircuitTK; rw [hc2]; ring
  · unfold simCircuitTK
    refine hc3.trans (le_of_eq_of_le ?_ hgb)
    ring
  · have hio : runT UJ (clampAt (2 ^ m) D) (simCircuitTK a m τ Q k) ∘L io =
        AMPT (K := simKK a m Q k) (m := m) (simLK Q k) (labLenK Q k)
          (labWtK Q k) (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m))
          UJ (clampAt (2 ^ m) D) (2 * fDegK Q k) ∘L io := by
      unfold simCircuitTK
      refine ContinuousLinearMap.ext (fun ψ => ?_)
      rw [comp_apply, comp_apply, io_apply]
      exact hagree _ (supp_bas _ (fun w _ => rfl) ψ)
    rw [hrunD, hio, hevol]
    exact herr

/-! ### The error against every propagator -/

/-- **The error against every propagator, with the manuscript's constants.** The slot-selected
circuit with an admissible depth at accuracy `δf` (budget `τ q̄`, `τ = α t`) and `2^m` slots with
`w = α t/2^m ≤ 1/4` and `2^m (Λt/2^m)³/12 ≤ δc` is within `2 δf + δc + β t²/(2·2^m) + t δ` of every
propagator of a `β`-Lipschitz Hermitian path whose samples at `j t/2^m` are within `δ` of the
represented samples `H̃_j`, `‖H̃_j‖ ≤ Λ ≤ α`; `D j` carries the clock promise for `H̃_j/α`. -/
theorem propagator_error_k (a m : ℕ) (UJ : Vsp a P →L[ℂ] Vsp a P)
    (D R1 : ℕ → Vsp a P →L[ℂ] Vsp a P) (Hpath U : ℝ → P →L[ℂ] P) (Hs : ℕ → P →L[ℂ] P)
    (t α Λ β δ Q b qbar : ℝ) (ht : 0 ≤ t) (hα : 0 < α) (hΛα : Λ ≤ α) (hQ : 1 ≤ Q)
    (hqQ : qbar ≤ Q) (δf δc : ℝ) (hδf : 0 < δf) (hδf1 : δf ≤ 1) (k : ℕ)
    (hk : Admissible Q (α * t * qbar) δf k) (hwq : stepW (α * t) m ≤ 1 / 4)
    (hcub : ((2 ^ m : ℕ) : ℝ) * ((Λ * t / 2 ^ m) ^ 3 / 12) ≤ δc)
    (hUJ : IsUnitary UJ) (hD : ∀ j < 2 ^ m, IsUnitary (D j))
    (hRight : ∀ j < 2 ^ m, (1 - D j) ∘L R1 j = 1)
    (hLeft : ∀ j < 2 ^ m, R1 j ∘L (1 - D j) = 1) (hR1 : ∀ j < 2 ^ m, ‖R1 j‖ ≤ Q)
    (hBoundary : ∀ j < 2 ^ m, (UJ ∘L iota0)† ∘L R1 j ∘L (UJ ∘L iota0) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • ((α : ℂ)⁻¹ • Hs j)))
    (hEndpoint : ∀ j < 2 ^ m, ‖R1 j ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2)
    (hSelf : ∀ j < 2 ^ m, star (Hs j) = Hs j) (hHs : ∀ j < 2 ^ m, ‖Hs j‖ ≤ Λ)
    (hPath : ∀ u ∈ Set.Icc 0 t, star (Hpath u) = Hpath u)
    (hLip : ∀ u ∈ Set.Icc 0 t, ∀ v ∈ Set.Icc 0 t, ‖Hpath u - Hpath v‖ ≤ β * |u - v|)
    (hVal : ∀ j : ℕ, j < 2 ^ m → ‖Hpath (j * t / 2 ^ m) - Hs j‖ ≤ δ)
    (hU0 : U 0 = 1) (hU : TimeDependent.SolvesOn Hpath U 0 t) :
    ‖runT UJ D (simCircuitTK a m (α * t) Q k) ∘L io - io ∘L U t‖ ≤
      2 * δf + δc + β * t ^ 2 / (2 * 2 ^ m) + t * δ := by
  have hMpos : 0 < 2 ^ m := Nat.two_pow_pos m
  have hMR : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast hMpos
  have hpow : (((2 ^ m : ℕ) : ℝ)) = (2 : ℝ) ^ m := by norm_num
  have hαC : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  -- the normalised samples
  have hnSelf : ∀ j < 2 ^ m, star ((α : ℂ)⁻¹ • Hs j) = (α : ℂ)⁻¹ • Hs j := by
    intro j hj
    rw [star_smul, hSelf j hj, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hnNormΛ : ∀ j < 2 ^ m, ‖(α : ℂ)⁻¹ • Hs j‖ ≤ Λ / α := by
    intro j hj
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hα.le, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (hHs j hj) hα.le
  have hΛα1 : Λ / α ≤ 1 := (div_le_one hα).mpr hΛα
  have hnNorm : ∀ j < 2 ^ m, ‖(α : ℂ)⁻¹ • Hs j‖ ≤ 1 := fun j hj => (hnNormΛ j hj).trans hΛα1
  have hwl : stepW (α * t) m * (Λ / α) = Λ * t / 2 ^ m := by
    unfold stepW
    rw [hpow]
    field_simp
  have hcub' : ((2 ^ m : ℕ) : ℝ) * ((stepW (α * t) m * (Λ / α)) ^ 3 / 12) ≤ δc := by
    rw [hwl]
    exact hcub
  obtain ⟨-, -, -, -, -, hsim, -⟩ := simulationT_k (P := P) a m UJ D R1
    (fun j => (α : ℂ)⁻¹ • Hs j) hUJ hD (α * t) Q b qbar (Λ / α) (mul_nonneg hα.le ht) hQ hRight
    hLeft hR1 hBoundary hnSelf hnNorm hnNormΛ hEndpoint hbq hqQ δf δc hδf hδf1 k hk hwq hcub'
  -- one normalised Cayley step is one physical step `t / 2^m`
  have hexp : (fun j => NormedSpace.exp ((-Complex.I * (stepW (α * t) m : ℂ)) •
      ((α : ℂ)⁻¹ • Hs j))) =
      fun j => NormedSpace.exp ((-Complex.I * ((t / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • Hs j) := by
    funext j
    congr 1
    rw [smul_smul]
    congr 1
    unfold stepW
    push_cast
    field_simp
  rw [hexp] at hsim
  -- the mesh error of the path, with samples clamped to the mesh
  have hcl := min_pred_lt hMpos
  have hmesh := mesh_error_sharp (H := Hpath) (U := U) (δ := δ) (clampAt (2 ^ m) Hs) hMpos
    ht hU0 hU hPath (fun j => hSelf _ (hcl j)) hLip (fun j hj => by
      rw [clampAt_of_lt _ _ hj]
      have h := hVal j hj
      push_cast
      exact h)
  have hev : TimeDependent.evolution (fun j => NormedSpace.exp
        ((-Complex.I * ((t / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • clampAt (2 ^ m) Hs j)) (2 ^ m) =
      TimeDependent.evolution (fun j => NormedSpace.exp
        ((-Complex.I * ((t / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • Hs j)) (2 ^ m) :=
    evolution_eq_of_lt _ _ _ (fun j hj => by rw [clampAt_of_lt _ _ hj])
  rw [hev] at hmesh
  have hio : ‖(io : P →L[ℂ] Reg (SimWireK a m Q k) P)‖ ≤ 1 :=
    opNorm_le_bound _ zero_le_one (fun v => by
      rw [GateBlockTransfer.norm_apply_of_isometry _ io_isometry v, one_mul])
  have h2 : ‖(io : P →L[ℂ] Reg (SimWireK a m Q k) P) ∘L TimeDependent.evolution
      (fun j => NormedSpace.exp
        ((-Complex.I * ((t / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • Hs j)) (2 ^ m) - io ∘L U t‖ ≤
      β * t ^ 2 / (2 * 2 ^ m) + t * δ := by
    rw [← comp_sub]
    refine (opNorm_comp_le _ _).trans ?_
    have h3 : ‖TimeDependent.evolution (fun j => NormedSpace.exp
        ((-Complex.I * ((t / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • Hs j)) (2 ^ m) - U t‖ ≤
        β * t ^ 2 / (2 * 2 ^ m) + t * δ := by
      rw [norm_sub_rev, ← hpow]
      exact hmesh
    calc _ ≤ 1 * (β * t ^ 2 / (2 * 2 ^ m) + t * δ) :=
          mul_le_mul hio h3 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have key := norm_sub_le_norm_sub_add_norm_sub
    (runT UJ D (simCircuitTK a m (α * t) Q k) ∘L io)
    ((io : P →L[ℂ] Reg (SimWireK a m Q k) P) ∘L TimeDependent.evolution
      (fun j => NormedSpace.exp
        ((-Complex.I * ((t / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • Hs j)) (2 ^ m))
    ((io : P →L[ℂ] Reg (SimWireK a m Q k) P) ∘L U t)
  linarith

/-! ### The manuscript's mesh and schedule -/

/-- The manuscript's time-grid threshold `max{1, 4αT, 6βT²/ε, (ΛT)^{3/2}/√ε}` (equation
`hs:eq:timegrid`), written with `(ΛT)^{3/2}/√ε = √((ΛT)³/ε)`. -/
def timegridMs (α Λ β t ε : ℝ) : ℝ :=
  max 1 (max (4 * (α * t)) (max (6 * β * t ^ 2 / ε) (Real.sqrt ((Λ * t) ^ 3 / ε))))

/-- **The manuscript's time grid** gives the step `w = αt/2^m ≤ 1/4`, the sharp Cayley error
`2^m (Λt/2^m)³/12 ≤ ε/12` and the freezing error `β t²/(2·2^m) ≤ ε/12`. -/
theorem timegrid_budget (α Λ β t ε : ℝ) (hΛ : 0 ≤ Λ) (ht : 0 ≤ t)
    (hε : 0 < ε) (m : ℕ) (hm : timegridMs α Λ β t ε ≤ 2 ^ m) :
    stepW (α * t) m ≤ 1 / 4 ∧
    ((2 ^ m : ℕ) : ℝ) * ((Λ * t / 2 ^ m) ^ 3 / 12) ≤ ε / 12 ∧
    β * t ^ 2 / (2 * 2 ^ m) ≤ ε / 12 := by
  have hTm : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := by push_cast; rfl
  have hTp : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have h4 : 4 * (α * t) ≤ (2 : ℝ) ^ m :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have h6 : 6 * β * t ^ 2 / ε ≤ (2 : ℝ) ^ m :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hm))
  have hs : Real.sqrt ((Λ * t) ^ 3 / ε) ≤ (2 : ℝ) ^ m :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hm))
  refine ⟨?_, ?_, ?_⟩
  · unfold stepW
    rw [hTm, div_le_iff₀ hTp]
    linarith
  · rw [hTm]
    have hratio : 0 ≤ (Λ * t) ^ 3 / ε := by positivity
    have h1 : (Λ * t) ^ 3 / ε ≤ ((2 : ℝ) ^ m) ^ 2 := by
      calc (Λ * t) ^ 3 / ε = (Real.sqrt ((Λ * t) ^ 3 / ε)) ^ 2 := (Real.sq_sqrt hratio).symm
        _ ≤ ((2 : ℝ) ^ m) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
    have h2 : (Λ * t) ^ 3 ≤ ε * ((2 : ℝ) ^ m) ^ 2 := by
      have := (div_le_iff₀ hε).mp h1
      linarith
    have e : (2 : ℝ) ^ m * ((Λ * t / (2 : ℝ) ^ m) ^ 3 / 12) =
        (Λ * t) ^ 3 / (12 * ((2 : ℝ) ^ m) ^ 2) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  · have h6' : 6 * β * t ^ 2 ≤ ε * (2 : ℝ) ^ m := by
      have := (div_le_iff₀ hε).mp h6
      linarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith

/-- **The slot circuit with the manuscript's schedule**: depth `k = ⌈4αtq̄/Q + log₂(4096/ε)⌉`
and `2^m` slots. -/
def simCircuitTMs (a m : ℕ) (α t Q qbar ε : ℝ) :
    List (Instr (SimWireK a m Q (depthMs Q (α * t * qbar) ε))) :=
  simCircuitTK a m (α * t) Q (depthMs Q (α * t * qbar) ε)

set_option maxRecDepth 8192 in
/-- **Gate-efficient time-dependent simulation with the manuscript's schedule, exact gates**
(Theorem `hs:thm:time` with the circuit of `hs:thm:gates`). The circuit
`simCircuitTMs a m α t Q q̄ ε` is fixed by the public data. Let `U_J` and the slot-selected private
operations `D j` be unitaries such that every `D j` (`j < 2^m`) carries the clock promise for
`H̃_j/α` and `J = U_J ι₀`, with `‖H̃_j‖ ≤ Λ ≤ α`. For a Hermitian path `H(u)` with Lipschitz bound
`β` and `‖H(j t/2^m) - H̃_j‖ ≤ δ`, under the manuscript's mesh condition
`2^m ≥ max{1, 4αt, 6βt²/ε, √((Λt)³/ε)}` and the sample budget `12 t δ ≤ ε`: the circuit consists of
valid elementary instructions, makes exactly `6d` private calls and `12d` calls of `U_J` or `U_J†`
(`d = k (⌈32Q⌉ - 1)`, `k = ⌈4αtq̄/Q + log₂(4096/ε)⌉`), uses at most `200 (d+1)(a+m+r+1)` elementary
gates on `2a + 3m + 6r + 3` qubits, `d ≤ 128 αtq̄ + 32 Q (log₂(4096/ε) + 1)`, a propagator exists,
and the full output on clean inputs is within `ε/2` of `U(t)` for every propagator `U` (filter
`ε/4`, Cayley `ε/12`, freezing `ε/12`, samples `ε/12`). -/
theorem gate_efficient_time_simulation_ms (a m : ℕ) (UJ : Vsp a P →L[ℂ] Vsp a P)
    (D R1 : ℕ → Vsp a P →L[ℂ] Vsp a P) (Hpath : ℝ → P →L[ℂ] P) (Hs : ℕ → P →L[ℂ] P)
    (t α Λ β δ Q b qbar ε : ℝ) (ht : 0 ≤ t) (hα : 0 < α) (hΛ : 0 ≤ Λ) (hΛα : Λ ≤ α)
    (hQ : 1 ≤ Q) (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hgrid : timegridMs α Λ β t ε ≤ 2 ^ m)
    (hUJ : IsUnitary UJ) (hD : ∀ j < 2 ^ m, IsUnitary (D j))
    (hRight : ∀ j < 2 ^ m, (1 - D j) ∘L R1 j = 1)
    (hLeft : ∀ j < 2 ^ m, R1 j ∘L (1 - D j) = 1) (hR1 : ∀ j < 2 ^ m, ‖R1 j‖ ≤ Q)
    (hBoundary : ∀ j < 2 ^ m, (UJ ∘L iota0)† ∘L R1 j ∘L (UJ ∘L iota0) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • ((α : ℂ)⁻¹ • Hs j)))
    (hEndpoint : ∀ j < 2 ^ m, ‖R1 j ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2)
    (hSelf : ∀ j < 2 ^ m, star (Hs j) = Hs j) (hHs : ∀ j < 2 ^ m, ‖Hs j‖ ≤ Λ)
    (hPath : ∀ u ∈ Set.Icc 0 t, star (Hpath u) = Hpath u)
    (hLip : ∀ u ∈ Set.Icc 0 t, ∀ v ∈ Set.Icc 0 t, ‖Hpath u - Hpath v‖ ≤ β * |u - v|)
    (hVal : ∀ j : ℕ, j < 2 ^ m → ‖Hpath (j * t / 2 ^ m) - Hs j‖ ≤ δ)
    (hValBudget : 12 * t * δ ≤ ε) :
    (∀ g ∈ simCircuitTMs a m α t Q qbar ε, g.Valid Wire.anc) ∧
    nPriv (simCircuitTMs a m α t Q qbar ε) = 6 * degreeMs Q (α * t * qbar) ε ∧
    nUJ (simCircuitTMs a m α t Q qbar ε) = 12 * degreeMs Q (α * t * qbar) ε ∧
    nGates (simCircuitTMs a m α t Q qbar ε) ≤
      200 * (degreeMs Q (α * t * qbar) ε + 1) *
        (a + m + simRK Q (depthMs Q (α * t * qbar) ε) + 1) ∧
    Fintype.card (SimWireK a m Q (depthMs Q (α * t * qbar) ε)) =
      2 * a + 3 * m + 6 * simRK Q (depthMs Q (α * t * qbar) ε) + 3 ∧
    (degreeMs Q (α * t * qbar) ε : ℝ) ≤
      128 * (α * t * qbar) + 32 * Q * (Real.logb 2 (4096 / ε) + 1) ∧
    2 * degreeMs Q (α * t * qbar) ε + 2 ≤ 2 ^ simRK Q (depthMs Q (α * t * qbar) ε) ∧
    2 ^ simRK Q (depthMs Q (α * t * qbar) ε) ≤ 4 * (degreeMs Q (α * t * qbar) ε + 1) ∧
    (∃ U : ℝ → P →L[ℂ] P, U 0 = 1 ∧ TimeDependent.SolvesOn Hpath U 0 t) ∧
    ∀ U : ℝ → P →L[ℂ] P, U 0 = 1 → TimeDependent.SolvesOn Hpath U 0 t →
      ‖runT UJ D (simCircuitTMs a m α t Q qbar ε) ∘L io - io ∘L U t‖ ≤ ε / 2 := by
  have hq : 0 ≤ qbar := by nlinarith [sq_nonneg b]
  have hW : 0 ≤ α * t * qbar := mul_nonneg (mul_nonneg hα.le ht) hq
  have hdeg := degreeMs_le Q (α * t * qbar) ε hQ hW hε hε1
  obtain ⟨hwq, hcub, hfr⟩ := timegrid_budget α Λ β t ε hΛ ht hε m hgrid
  have hk := depthMs_admissible Q (α * t * qbar) ε hQ hW hε hε1
  have hδf : 0 < ε / 8 := by positivity
  have hδf1 : ε / 8 ≤ 1 := by linarith
  have hk' : Admissible Q (α * t * qbar) (ε / 8) (depthMs Q (α * t * qbar) ε) := hk
  have hnSelf : ∀ j < 2 ^ m, star ((α : ℂ)⁻¹ • Hs j) = (α : ℂ)⁻¹ • Hs j := by
    intro j hj
    rw [star_smul, hSelf j hj, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hnNormΛ : ∀ j < 2 ^ m, ‖(α : ℂ)⁻¹ • Hs j‖ ≤ Λ / α := by
    intro j hj
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hα.le, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (hHs j hj) hα.le
  have hΛα1 : Λ / α ≤ 1 := (div_le_one hα).mpr hΛα
  have hnNorm : ∀ j < 2 ^ m, ‖(α : ℂ)⁻¹ • Hs j‖ ≤ 1 := fun j hj => (hnNormΛ j hj).trans hΛα1
  have hwl : stepW (α * t) m * (Λ / α) = Λ * t / 2 ^ m := by
    have hpow : (((2 ^ m : ℕ) : ℝ)) = (2 : ℝ) ^ m := by norm_num
    unfold stepW
    rw [hpow]
    field_simp
  have hcub' : ((2 ^ m : ℕ) : ℝ) * ((stepW (α * t) m * (Λ / α)) ^ 3 / 12) ≤ ε / 12 := by
    rw [hwl]
    exact hcub
  obtain ⟨hvalid, hP, hJ, hG, hcard, -, hr1, hr2⟩ := simulationT_k (P := P) a m UJ D R1
    (fun j => (α : ℂ)⁻¹ • Hs j) hUJ hD (α * t) Q b qbar (Λ / α) (mul_nonneg hα.le ht) hQ
    hRight hLeft hR1 hBoundary hnSelf hnNorm hnNormΛ hEndpoint hbq hqQ (ε / 8) (ε / 12) hδf hδf1
    _ hk' hwq hcub'
  have e1 : simCircuitTMs a m α t Q qbar ε =
      simCircuitTK a m (α * t) Q (depthMs Q (α * t * qbar) ε) := rfl
  have e2 : degreeMs Q (α * t * qbar) ε = fDegK Q (depthMs Q (α * t * qbar) ε) := rfl
  rw [e1, e2]
  rw [e2] at hdeg
  refine ⟨hvalid, hP, hJ, hG, hcard, hdeg, hr1, hr2,
    TimeDependent.exists_solvesOn_of_lipschitz Hpath ht hLip, fun U hU0 hU => ?_⟩
  have herr := propagator_error_k a m UJ D R1 Hpath U Hs t α Λ β δ Q b qbar ht hα hΛα hQ hqQ
    (ε / 8) (ε / 12) hδf hδf1 _ hk' hwq hcub hUJ hD hRight hLeft hR1 hBoundary hEndpoint hbq
    hSelf hHs hPath hLip hVal hU0 hU
  have htδ : t * δ ≤ ε / 12 := by linarith
  calc _ ≤ 2 * (ε / 8) + ε / 12 + β * t ^ 2 / (2 * 2 ^ m) + t * δ := herr
    _ ≤ ε / 2 := by linarith

end

end SparseHamiltonian.GateSchedule
