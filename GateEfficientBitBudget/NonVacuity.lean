import GateEfficientBitBudget.Witness
import GateEfficientBitBudget.HamiltonianBudget

/-!
# The endpoints in `𝔟` are not vacuous

Every hypothesis of the four endpoints of equations `ode:eq:gate-main`, `ode:eq:gate-space`
(Theorem `ode:thm:gates`, in the word budget of equation `ode:eq:gate-word-budget`) and
`hs:eq:gate-binary` (Theorem `hs:thm:gates`) holds at once for explicit data, the binary data and
the source circuits included, and the endpoint then applies to these data:

* `pointData`: one-point binary data on the index register `Cfg (Fin 0)` (one index, one slot,
  `b` stored bits per component, the decoder `c₀ · gauss`, every stored entry the zero word, the
  identity oracles); `twos_inl_zero`, `twos_inr_zero`, `gauss_zero_word`, `pointData_matrix`:
  for one-bit components the zero word decodes to `0`, so the matrix of `pointData Y 1 1` is zero
  (Hermitian, with row and column norms `0`);
* `ode_all_hyps`, `ode_time_all_hyps`: the public data `withChoice pointPub`
  (respectively `withChoiceT pointPubT`), the data `pointData`, the identity equivalence and
  empty source circuits on the empty source scratch satisfy every hypothesis of
  `binary_ode_budget_bits` (respectively `binary_ode_time_budget_bits`) for some `b_data`, and its
  gate bound in `𝔟` holds for them;
* `hs_all_hyps`, `hsT_all_hyps`: for `s = 1`, `τ = 0` (respectively `t = 0`) and `ε = 1/2`, the
  data `pointData` with `b = 1` and `c₀ = 1`, some `b_data ≥ 1`, the accuracy
  `ζ = ε/(442368 q)` (`hs_zeta_shape_spec`, `hs_zeta_shape_specT`) and, for time-dependent
  Hamiltonians, the zero path with `β = δ = 0` and the least admissible mesh satisfy every
  hypothesis of `binary_simulation_bits` (respectively `binary_time_simulation_bits`) after its
  rescaling `γ`, and its gate bound in `𝔟_H` holds for them.

The forms over a finite gate set add only the released hypotheses `GateSynth.Synthesis`,
`AdjClosed` and `zeroTestKinds ⊆ 𝒢`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBitBudget

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE
open SparseHamiltonian.GateBinaryODETime SparseHamiltonian.OracleCircuit CayleyClockInterface
open GateODEBudget (gammaOf qOf)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### One-point binary data -/

/-- **One-point binary data**: the index register `Cfg (Fin 0)` (one index), one slot, `b` stored
bits per component, the decoder `c₀ · gauss`, every stored entry the zero word, and the identity
row and column oracles; the inputs `Y` are arbitrary. -/
def pointData (Y : Type) (b : ℕ) (c0 : ℝ) : Data Y (Cfg (Fin 0)) (Cfg (VW b)) 1 where
  slot := ⟨fun _ => default, fun _ _ _ => Subsingleton.elim _ _⟩
  slots_pos := one_pos
  scale := 1 + ∑ z : Cfg (VW b), ‖(c0 : ℂ) * gauss z‖
  scale_pos := by positivity
  matrix := fun _ _ _ => (c0 : ℂ) * gauss (fun _ => false)
  table := fun _ _ _ => false
  decode := fun _ z => (c0 : ℂ) * gauss z
  decode_bound := fun _ z => by
    have h := Finset.single_le_sum (f := fun z : Cfg (VW b) => ‖(c0 : ℂ) * gauss z‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ z)
    linarith
  decoded := fun _ _ _ => rfl
  rowloc := fun _ _ _ => default
  colloc := fun _ _ _ => default
  row_injective := fun _ _ _ _ _ => Subsingleton.elim _ _
  column_injective := fun _ _ _ _ _ => Subsingleton.elim _ _
  row_covers := fun _ _ _ _ => by
    unfold SparseSlotStates.selected
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, Subsingleton.elim _ _⟩
  column_covers := fun _ _ _ _ => by
    unfold SparseSlotStates.selected
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, Subsingleton.elim _ _⟩
  rowOracle := fun _ => 1
  columnOracle := fun _ => 1
  row_unitary := fun _ => by simp [IsUnitary]
  column_unitary := fun _ => by simp [IsUnitary]
  row_valid := fun _ _ _ => by
    change EuclideanSpace.single _ 1 = _
    rfl
  column_valid := fun _ j k => by
    change EuclideanSpace.single _ 1 = _
    have : ((j, (⟨fun _ => default, fun _ _ _ => Subsingleton.elim _ _⟩ : Fin 1 ↪ Cfg (Fin 0)) k)
        : Cfg (Fin 0) × Cfg (Fin 0)) = (default, j) := Prod.ext (Subsingleton.elim _ _)
      (Subsingleton.elim _ _)
    rw [this]

/-- The two's complement value of the first component of the zero word of one bit is `0`. -/
theorem twos_inl_zero : twos (B := VW 1) Sum.inl (fun _ => false) = 0 := by decide

/-- The two's complement value of the second component of the zero word of one bit is `0`. -/
theorem twos_inr_zero : twos (B := VW 1) Sum.inr (fun _ => false) = 0 := by decide

/-- The zero word of one-bit components decodes to `0`. -/
theorem gauss_zero_word : gauss (b := 1) (fun _ => false) = 0 := by
  simp [gauss, twos_inl_zero, twos_inr_zero]

/-- **The matrix of the one-point data** with one-bit components and decoder scale `1` is zero,
for every input. -/
theorem pointData_matrix (Y : Type) (x : Y) : (pointData Y 1 1).matrix x = 0 := by
  funext i j
  simp [pointData, gauss_zero_word]

/-- The slot range of the one-point data with the identity equivalence: the one slot is the one
index, the image of the empty low word. -/
theorem pointData_range (Y : Type) (b : ℕ) (c0 : ℝ) :
    ∀ j : Cfg (Fin 0), (∃ m, (pointData Y b c0).slot m = j) ↔
      ∃ u : Fin 0 → Bool, j = Equiv.refl (Cfg (Fin 0)) (lowWord 0 u) := fun _ =>
  ⟨fun _ => ⟨fun i => i.elim0, Subsingleton.elim _ _⟩, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

/-! ### The dissipative solvers -/

/-- **Every hypothesis of `binary_ode_budget_bits` holds at once** (equations `ode:eq:gate-main`,
`ode:eq:gate-space` in `𝔟`, constant coefficients; the endpoint is not vacuous): the public data
`withChoice pointPub`, the one-point binary data `pointData Unit 1 1`, the identity equivalence and
empty source circuits on the empty source scratch satisfy, for some `b_data`, `Pub.OK`, the public
rescaling, the accuracy bound `ν ≤ 196608 q* ζ`, `b ≤ b_data`, the four bit-length hypotheses,
the slot range, the decoder and the validity of the source circuits, and the gate bound
`10²⁰ g [q* (𝔟+1)³ + G_src + |Zs|]` of the endpoint holds for them. -/
theorem ode_all_hyps : ∃ (q : Pub) (bd : ℕ) (hq : q.OK)
    (D : Data Unit (Cfg (Fin 0)) (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ Cfg (Fin 0))
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Empty) (PY q.kx q.b) Query)),
    q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε ∧
    q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ ∧ q.b ≤ bd ∧
    HasBits bd q.c0 ∧ HasBits bd q.T ∧ HasBits bd q.etaH ∧ HasBits bd q.etaD ∧
    (∀ j, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u)) ∧
    (∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z) ∧ (∀ c, ∀ i ∈ srcC c, i.Valid) ∧
    ((nprotocol (q.prep srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      10 ^ 20 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
            (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Empty) := by
  obtain ⟨bd, hok, hγ, hζ, hb, hc0, hT, hH, hD⟩ :=
    withChoice_bits pointPub pointPub_ok ⟨1, 0, by norm_num [pointPub]⟩
      ⟨1, 0, by norm_num [pointPub]⟩ ⟨1, 0, by norm_num [pointPub]⟩ ⟨0, 0, by norm_num [pointPub]⟩
  have hdec : ∀ e z, (pointData Unit 1 1).decode e z =
      ((withChoice pointPub).c0 : ℂ) * gauss z := fun _ _ => by
    simp [pointData, withChoice, pointPub]
  refine ⟨withChoice pointPub, bd, hok, pointData Unit 1 1, Equiv.refl _, fun _ => [], hγ, hζ, hb,
    hc0, hT, hH, hD, pointData_range Unit 1 1, hdec, fun _ _ hi => by simp at hi, ?_⟩
  exact (binary_ode_budget_bits (X := Unit) (Zs := Empty) bd (withChoice pointPub) hok hγ hζ hb
    hc0 hT hH hD (pointData Unit 1 1) (Equiv.refl _) (pointData_range Unit 1 1) hdec
    (fun _ => []) (fun _ _ hi => by simp at hi)).1

/-- **Every hypothesis of `binary_ode_time_budget_bits` holds at once** (equations
`ode:eq:gate-main`, `ode:eq:gate-space` in `𝔟`, time-dependent coefficients; the endpoint is not
vacuous): the public data `withChoiceT pointPubT` (the coarsest admissible mesh), the one-point
time-indexed binary data `pointData (Unit × Fin (2^m)) 1 1`, the identity equivalence and empty
circuits `loadC`, `wpC` on the empty source scratch satisfy, for some `b_data`, `PubT.OK` (the mesh
condition included), the public rescaling, the accuracy bound, `b ≤ b_data`, the four bit-length
hypotheses, the slot range, the decoder and the validity of the circuits, and the gate bound
`2·10²⁰ g [q* (𝔟+1)³ + G_src + |Zs|]` of the endpoint holds for them. -/
theorem ode_time_all_hyps : ∃ (q : PubT) (bd : ℕ) (hq : q.OK)
    (D : Data (Unit × Fin (2 ^ q.m)) (Cfg (Fin 0)) (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ Cfg (Fin 0))
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Empty) (Fin q.m ⊕ PY q.kx q.b)
      Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Empty) (Fin q.m ⊕ PY q.kx q.b) Query)),
    q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) ∧
    q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ ∧ q.b ≤ bd ∧
    HasBits bd q.c0 ∧ HasBits bd q.T ∧ HasBits bd q.etaH ∧ HasBits bd q.etaD ∧
    (∀ j, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u)) ∧
    (∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z) ∧ (∀ i ∈ loadC, i.Valid) ∧
    (∀ i ∈ wpC, i.Valid) ∧
    ((nprotocol (q.prep loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      2 * 10 ^ 20 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Empty) := by
  obtain ⟨bd, hok, hγ, hζ, hb, hc0, hT, hH, hD⟩ :=
    withChoiceT_bits pointPubT pointPubT_ok
      ⟨1, 0, by norm_num [pointPubT, pointPubT₀]⟩ ⟨1, 0, by norm_num [pointPubT, pointPubT₀]⟩
      ⟨1, 0, by norm_num [pointPubT, pointPubT₀]⟩ ⟨0, 0, by norm_num [pointPubT, pointPubT₀]⟩
  have hdec : ∀ e z, (pointData (Unit × Fin (2 ^ (withChoiceT pointPubT).m)) 1 1).decode e z =
      ((withChoiceT pointPubT).c0 : ℂ) * gauss z := fun _ _ => by
    simp [pointData, withChoiceT, withChoiceT₀, pointPubT, pointPubT₀]
  refine ⟨withChoiceT pointPubT, bd, hok, pointData _ 1 1, Equiv.refl _, [], [], hγ, hζ, hb, hc0,
    hT, hH, hD, pointData_range _ 1 1, hdec, fun _ hi => by simp at hi,
    fun _ hi => by simp at hi, ?_⟩
  exact (binary_ode_time_budget_bits (X := Unit) (Zs := Empty) bd (withChoiceT pointPubT) hok hγ
    hζ hb hc0 hT hH hD (pointData _ 1 1) (Equiv.refl _) (pointData_range _ 1 1) hdec []
    (fun _ hi => by simp at hi) [] (fun _ hi => by simp at hi)).1

/-! ### The binary simulations -/

/-- **Every hypothesis of `binary_simulation_bits` holds at once** (equation `hs:eq:gate-binary`;
the endpoint is not vacuous): for `s = 1 = 2^0` slot, `τ = 0` and `ε = 1/2`, the one-point binary
data `pointData Unit 1 1` (`k = 0` index bits, `b = 1` stored bit, decoder scale `c₀ = 1`, zero
matrix) with the identity equivalence, some `b_data ≥ 1` with `HasBits b_data 1` and
`ζ = ε/(442368 q)` satisfy the slot range, the decoder, the Hermitian, row and column norm
hypotheses, the bit-length hypotheses and the accuracy window `0 < ζ ≤ 1`,
`ε/(442368 q) ≤ ζ ≤ ε/(221184 q)`; for the rescaling `γ` of the endpoint its gate bound
`10¹⁵ q (𝔟_H + 1)³` holds for them. -/
theorem hs_all_hyps : ∃ (D : Data Unit (Cfg (Fin 0)) (Cfg (VW 1)) 1)
    (en : Cfg (Fin 0) ≃ Cfg (Fin 0)) (c0 : ℝ) (bd : ℕ) (ζ : ℝ),
    (∀ j, (∃ m, D.slot m = j) ↔ ∃ u : Fin 0 → Bool, j = en (lowWord 0 u)) ∧ 0 < c0 ∧
    (∀ e z, D.decode e z = (c0 : ℂ) * gauss z) ∧ (D.matrix ()).IsHermitian ∧
    (∀ i, ∑ j, ‖D.matrix () i j‖ ^ 2 ≤ 1) ∧ (∀ j, ∑ i, ‖D.matrix () i j‖ ^ 2 ≤ 1) ∧
    1 ≤ bd ∧ HasBits bd c0 ∧ 0 < ζ ∧ ζ ≤ 1 ∧
    221184 * ImprovedPrecisionBudget.shape ((1 : ℕ) : ℝ) 0 (Real.log (1 / (1 / 2))) * ζ ≤
      1 / 2 ∧
    1 / 2 ≤ 442368 * ImprovedPrecisionBudget.shape ((1 : ℕ) : ℝ) 0 (Real.log (1 / (1 / 2))) * ζ ∧
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      (nGatesN (binarySim 0 1 0 le_rfl 1 γ c0 0 (1 / 2) ζ) : ℝ) ≤
        10 ^ 15 * ImprovedPrecisionBudget.shape ((1 : ℕ) : ℝ) 0 (Real.log (1 / (1 / 2))) *
          (bitH bd (2 ^ 0) (ImprovedPrecisionBudget.shape ((1 : ℕ) : ℝ) 0
            (Real.log (1 / (1 / 2)))) (1 / 2) + 1) ^ 3 := by
  obtain ⟨γ, hγ, hγ1, -, -, -, -, -, hall⟩ :=
    binary_simulation_bits.{0, 0, 0} 1 le_rfl 0 (1 / 2) le_rfl (by norm_num) (by norm_num)
  obtain ⟨bd, hb, hbits⟩ := exists_common_bits 1 [1] (by
    intro x hx
    simp only [List.mem_singleton] at hx
    exact ⟨1, 0, by rw [hx]; norm_num⟩)
  obtain ⟨hz0, hz1, hz2, hz3⟩ :=
    hs_zeta_shape_spec 1 (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hdec : ∀ e z, (pointData Unit 1 1).decode e z = ((1 : ℝ) : ℂ) * gauss z := fun _ _ => rfl
  have hH : ((pointData Unit 1 1).matrix ()).IsHermitian := by
    rw [pointData_matrix]
    exact Matrix.isHermitian_zero
  have hrow : ∀ i, ∑ j, ‖(pointData Unit 1 1).matrix () i j‖ ^ 2 ≤ 1 := fun _ => by
    simp [pointData_matrix]
  have hcol : ∀ j, ∑ i, ‖(pointData Unit 1 1).matrix () i j‖ ^ 2 ≤ 1 := fun _ => by
    simp [pointData_matrix]
  have h1 := hbits 1 (by simp)
  have h := hall (X := Unit) (n := Cfg (Fin 0)) (k := 0) (b := 1) (R := ℂ) (pointData Unit 1 1)
    (Equiv.refl _) 0 le_rfl rfl (pointData_range Unit 1 1) one_pos 1 one_pos hdec () hH hrow hcol
    bd hb h1 _ hz0 hz1 hz2 hz3
  exact ⟨pointData Unit 1 1, Equiv.refl _, 1, bd, _, pointData_range Unit 1 1, one_pos, hdec, hH,
    hrow, hcol, hb, h1, hz0, hz1, hz2, hz3, γ, hγ, hγ1, h.1⟩

/-- **Every hypothesis of `binary_time_simulation_bits` holds at once** (the time-dependent part
of equation `hs:eq:gate-binary`; the endpoint is not vacuous): for `s = 1 = 2^0` slot, `t = 0`,
`ε = 1/2` and the rescaling `γ` of the endpoint, the least mesh exponent `m` with
`steps τ' (ε/12) ≤ 2^m`, the one-point time-indexed binary data `pointData (Unit × Fin (2^m)) 1 1`
(`b = 1`, `c₀ = 1`, zero samples) with the identity equivalence, the zero path with `β = δ = 0`,
some `b_data ≥ 1` with `HasBits b_data 1` and `ζ = ε/(442368 q)` satisfy the slot range, the
decoder, the Hermitian, row and column norm hypotheses of the samples, the path, Lipschitz,
sampling and mesh hypotheses, the bit-length hypotheses and the accuracy window, and the gate
bound `10¹⁵ q (𝔟_H + log₂(M+1) + 1)³` of the endpoint holds for them. -/
theorem hsT_all_hyps : ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ ∃ (m : ℕ)
    (D : Data (Unit × Fin (2 ^ m)) (Cfg (Fin 0)) (Cfg (VW 1)) 1)
    (en : Cfg (Fin 0) ≃ Cfg (Fin 0)) (c0 : ℝ) (H : ℝ → Matrix (Cfg (Fin 0)) (Cfg (Fin 0)) ℂ)
    (β δ : ℝ) (bd : ℕ) (ζ : ℝ),
    (∀ j, (∃ r, D.slot r = j) ↔ ∃ u : Fin 0 → Bool, j = en (lowWord 0 u)) ∧ 0 < c0 ∧
    (∀ e z, D.decode e z = (c0 : ℂ) * gauss z) ∧ (∀ r, (D.matrix ((), r)).IsHermitian) ∧
    (∀ r i, ∑ j, ‖D.matrix ((), r) i j‖ ^ 2 ≤ 1) ∧
    (∀ r j, ∑ i, ‖D.matrix ((), r) i j‖ ^ 2 ≤ 1) ∧
    0 ≤ β ∧ (∀ u ∈ Set.Icc (0 : ℝ) 0, (H u).IsHermitian) ∧
    (∀ u ∈ Set.Icc (0 : ℝ) 0, ∀ v ∈ Set.Icc (0 : ℝ) 0,
      ‖SparseStateOverlap.matrixOperator (H u) - SparseStateOverlap.matrixOperator (H v)‖ ≤
        β * |u - v|) ∧
    (∀ r : Fin (2 ^ m),
      ‖SparseStateOverlap.matrixOperator (H (((r : ℕ) : ℝ) * 0 / 2 ^ m)) -
        SparseStateOverlap.matrixOperator (D.matrix ((), r))‖ ≤ δ) ∧
    8 * 0 * δ ≤ (1 / 2 : ℝ) ∧
    TimeSchedule.steps (time ((1 : ℕ) : ℝ) 0 γ) ((1 / 2 : ℝ) / 12) ≤ 2 ^ m ∧
    8 * β * (0 : ℝ) ^ 2 ≤ 1 / 2 * 2 ^ m ∧
    1 ≤ bd ∧ HasBits bd c0 ∧ 0 < ζ ∧ ζ ≤ 1 ∧
    221184 * ImprovedPrecisionBudget.shape ((1 : ℕ) : ℝ) 0 (Real.log (2 / (1 / 2))) * ζ ≤
      1 / 2 ∧
    1 / 2 ≤ 442368 * ImprovedPrecisionBudget.shape ((1 : ℕ) : ℝ) 0 (Real.log (2 / (1 / 2))) * ζ ∧
    (nGatesN (binaryTimeSim 0 1 m 0 le_rfl 1 γ c0 0 (1 / 2) ζ) : ℝ) ≤
      10 ^ 15 * ImprovedPrecisionBudget.shape ((1 : ℕ) : ℝ) 0 (Real.log (2 / (1 / 2))) *
        (bitH bd (2 ^ 0) (ImprovedPrecisionBudget.shape ((1 : ℕ) : ℝ) 0
          (Real.log (2 / (1 / 2)))) (1 / 2) + Real.logb 2 (((2 ^ m : ℕ) : ℝ) + 1) + 1) ^ 3 := by
  obtain ⟨γ, hγ, hγ1, -, -, hall⟩ :=
    binary_time_simulation_bits.{0, 0, 0} 1 le_rfl 0 (1 / 2) le_rfl (by norm_num) (by norm_num)
  obtain ⟨bd, hb, hbits⟩ := exists_common_bits 1 [1] (by
    intro x hx
    simp only [List.mem_singleton] at hx
    exact ⟨1, 0, by rw [hx]; norm_num⟩)
  obtain ⟨hz0, hz1, hz2, hz3⟩ :=
    hs_zeta_shape_specT 1 (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  obtain ⟨m, hm⟩ : ∃ m : ℕ,
      TimeSchedule.steps (time ((1 : ℕ) : ℝ) 0 γ) ((1 / 2 : ℝ) / 12) ≤ 2 ^ m :=
    ⟨_, Nat.le_pow_clog (by norm_num) _⟩
  have hdec : ∀ e z, (pointData (Unit × Fin (2 ^ m)) 1 1).decode e z =
      ((1 : ℝ) : ℂ) * gauss z := fun _ _ => rfl
  have hH : ∀ r, ((pointData (Unit × Fin (2 ^ m)) 1 1).matrix ((), r)).IsHermitian := fun _ => by
    rw [pointData_matrix]
    exact Matrix.isHermitian_zero
  have hrow : ∀ r i, ∑ j, ‖(pointData (Unit × Fin (2 ^ m)) 1 1).matrix ((), r) i j‖ ^ 2 ≤ 1 :=
    fun _ _ => by simp [pointData_matrix]
  have hcol : ∀ r j, ∑ i, ‖(pointData (Unit × Fin (2 ^ m)) 1 1).matrix ((), r) i j‖ ^ 2 ≤ 1 :=
    fun _ _ => by simp [pointData_matrix]
  have hpath : ∀ u ∈ Set.Icc (0 : ℝ) 0,
      ((fun _ => 0 : ℝ → Matrix (Cfg (Fin 0)) (Cfg (Fin 0)) ℂ) u).IsHermitian := fun _ _ =>
    Matrix.isHermitian_zero
  have hlip : ∀ u ∈ Set.Icc (0 : ℝ) 0, ∀ v ∈ Set.Icc (0 : ℝ) 0,
      ‖SparseStateOverlap.matrixOperator
          ((fun _ => 0 : ℝ → Matrix (Cfg (Fin 0)) (Cfg (Fin 0)) ℂ) u) -
        SparseStateOverlap.matrixOperator
          ((fun _ => 0 : ℝ → Matrix (Cfg (Fin 0)) (Cfg (Fin 0)) ℂ) v)‖ ≤ 0 * |u - v| :=
    fun _ _ _ _ => by simp
  have hsamp : ∀ r : Fin (2 ^ m),
      ‖SparseStateOverlap.matrixOperator
          ((fun _ => 0 : ℝ → Matrix (Cfg (Fin 0)) (Cfg (Fin 0)) ℂ) (((r : ℕ) : ℝ) * 0 / 2 ^ m)) -
        SparseStateOverlap.matrixOperator ((pointData (Unit × Fin (2 ^ m)) 1 1).matrix ((), r))‖ ≤
        0 := fun _ => by simp [pointData_matrix]
  have hδ : 8 * 0 * (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hβ : 8 * (0 : ℝ) * 0 ^ 2 ≤ 1 / 2 * 2 ^ m := by
    rw [show (8 : ℝ) * 0 * 0 ^ 2 = 0 by norm_num]
    positivity
  have h1 := hbits 1 (by simp)
  have h := hall (X := Unit) (n := Cfg (Fin 0)) (k := 0) (b := 1) (m := m) (R := ℂ)
    (pointData (Unit × Fin (2 ^ m)) 1 1) (Equiv.refl _) 0 le_rfl rfl (pointData_range _ 1 1)
    one_pos 1 one_pos hdec () hH hrow hcol (fun _ => 0) 0 0 le_rfl hpath hlip hsamp hδ hm hβ bd hb
    h1 _ hz0 hz1 hz2 hz3
  exact ⟨γ, hγ, hγ1, m, pointData _ 1 1, Equiv.refl _, 1, fun _ => 0, 0, 0, bd, _,
    pointData_range _ 1 1, one_pos, hdec, hH, hrow, hcol, le_rfl, hpath, hlip, hsamp, hδ, hm, hβ,
    hb, h1, hz0, hz1, hz2, hz3, h.1⟩

end

end SparseHamiltonian.GateBitBudget
