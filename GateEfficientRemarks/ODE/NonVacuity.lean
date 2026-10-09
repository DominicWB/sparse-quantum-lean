import GateEfficientRemarks.ODE.ZeroBudget
import GateEfficientRemarks.ODE.ZeroReleased
import GateEfficientRemarks.ODE.ZeroReleasedTime
import GateEfficientBitBudget.NonVacuity

/-!
# The zero-case endpoints are not vacuous

Every hypothesis of the zero-case and every-`T ≥ 0` endpoints of equations `ode:eq:gate-main` and
`ode:eq:gate-space` (Theorem `ode:thm:gates` with its remark on zero time and a known zero
generator, in the word budget of equation `ode:eq:gate-word-budget`) holds at once for explicit
data, and the endpoints then apply (the released library `ZeroTimeGateODE` has no such
witnesses; the released `GateBitBudget.ode_all_hyps` witnesses the positive case):

* `zeroPub`, `zeroPubT`: zero-time public data (`T = 0`, `k_x = σ = 0`, `b = 1`,
  `c₀ = η_H = γ = g = 1`, `η_D = 0`, `ε = ζ = 1/2`, and `r₀ = 1`, `r_b = 0`, respectively the
  mesh exponent `m = 0`) with `BPublicOK0`, `BTPublicOK0` (`zeroPub_ok0`, `zeroPubT_ok0`,
  `zeroPubT_mesh`), in the zero case (`zeroPub_zero`, `zeroPubT_zero`);
* `zero_all_hyps`, `zero_time_all_hyps`: with `b_data = 1` (`γ = 1` has bit length `1`,
  `hasBits_one`), the one-point binary data `GateBitBudget.pointData`, the identity equivalence
  and empty circuits on the empty source scratch, every hypothesis of
  `binary_ode_budget_bits_zero_released` and `binary_ode_budget_bits_nonneg` (zero branch of the
  hypothesis on `γ`), respectively of `binary_ode_time_budget_bits_nonneg`, holds, and the gate
  bound of the every-`T ≥ 0` form holds for these data;
* `zeroPubZ` (`zeroPubZ_q`, `zeroPubZ_nu`, `zeroPubZ_spec`, `zeroPubZ_ok0`): the zero-time public
  data with the public arithmetic accuracy `ζ = ν/(196608 q*)` (`GateBitBudget.zetaOf`);
  `approx_empty`: the empty source circuit implements the controlled identity exactly;
* `zero_instance_all_hyps`: every hypothesis of `binary_ode_budget_bits_zero`,
  `binary_ode_budget_bits_zero_released` and `binary_ode_budget_bits_nonneg` (zero branch), the
  antecedents of the guarantee `NOutcome` included, holds at once (`T = 0`, `γ = 1`,
  `ζ = ν/(196608 q*)`, the one-point data, empty source circuits, `J_src = 1`, `x₀ = seedV`,
  `v = 0`, `ζs = 0`); `zero_instance_outcome`: the guarantees `NOutcome` of
  `binary_ode_budget_bits_zero` (minimal register) and `binary_ode_budget_bits_nonneg` (released
  register; the same as that of `binary_ode_budget_bits_zero_released`) hold for these data.

The finite-gate-set forms add only the released synthesis hypotheses (`GateSynth.Synthesis`,
`len ζ ≤ c₁ log(1/ζ) + c₀` with `c₀, c₁ ≥ 0`, `AdjClosed`, `zeroTestKinds ⊆ 𝒢`). The remaining
instance conditions `PubT.Rest` of the time-dependent guarantees are not witnessed (the released
libraries do not witness them either).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateRemarks.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateBinary GateBinaryODE
open GateBinaryODETime
open SparseHamiltonian.GateBitBudget (bitB HasBits pointData pointData_range pointData_matrix
  hasBits_zero zetaOf zetaOf_spec)
open GateODEBudget (gammaOf qOf)
open NativeSparseBlockEncoding (Data Query)
open ZeroTimeGateODE (BPublicOK0 BZeroCase BTPublicOK0 BTZeroCase bprepC btprepC zprepC srcRot)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-! ### Zero-time public data -/

/-- **Zero-time public data, constant coefficients**: `k_x = σ = 0`, `b = 1`,
`c₀ = η_H = γ = g = r₀ = 1`, `T = η_D = r_b = 0`, `ε = ζ = 1/2` (the zero case of the remark of
Theorem `ode:thm:gates`). -/
def zeroPub : Pub := ⟨0, 0, le_rfl, 1, 1, 1, 0, 1, 0, 1, 1 / 2, 1, 0, 1 / 2⟩

/-- `zeroPub` satisfies the public conditions `BPublicOK0` of every `T ≥ 0`. -/
theorem zeroPub_ok0 : BPublicOK0 zeroPub := by
  constructor <;> norm_num [zeroPub]

/-- `zeroPub` is in the zero case (`T = 0`). -/
theorem zeroPub_zero : BZeroCase zeroPub := Or.inl rfl

/-- **Zero-time public data, time-dependent coefficients**: as `zeroPub`, with the mesh exponent
`m = 0` (one time slot) and without the norms `r₀`, `r_b`. -/
def zeroPubT : PubT := ⟨0, 0, le_rfl, 1, 1, 1, 0, 1, 0, 1, 1 / 2, 0, 1 / 2⟩

/-- The one time slot of `zeroPubT` suffices: the simulation time vanishes, so the time schedule
has at most one step. -/
theorem zeroPubT_mesh :
    TimeSchedule.steps zeroPubT.params.tau (zeroPubT.params.nu / 3) ≤ 2 ^ zeroPubT.m := by
  have hτ : zeroPubT.params.tau = 0 := by
    show zeroPubT.T * _ = 0
    simp [zeroPubT]
  rw [hτ]
  simp [TimeSchedule.steps, TimeSchedule.threshold, zeroPubT]

/-- `zeroPubT` satisfies the public conditions `BTPublicOK0` of every `T ≥ 0`. -/
theorem zeroPubT_ok0 : BTPublicOK0 zeroPubT := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, zeroPubT_mesh⟩ <;> norm_num [zeroPubT]

/-- `zeroPubT` is in the zero case (`T = 0`). -/
theorem zeroPubT_zero : BTZeroCase zeroPubT := Or.inl rfl

/-! ### The released-register budgets -/

/-- **The zero case of the released-register budgets is not vacuous, constant coefficients**
(equations `ode:eq:gate-main`, `ode:eq:gate-space` of Theorem `ode:thm:gates`): `zeroPub`
(`T = 0`), `b_data = 1`, the one-point data, the identity equivalence and empty source circuits
satisfy every hypothesis of `binary_ode_budget_bits_zero_released` (`BZeroCase`, `HasBits 1 γ`)
and of `binary_ode_budget_bits_nonneg` (the zero branch of its hypothesis on `γ`), and the gate
bound of `binary_ode_budget_bits_nonneg` holds for them. -/
theorem zero_all_hyps : ∃ (q : Pub) (bd : ℕ) (hq : BPublicOK0 q)
    (D : Data Unit (Cfg (Fin 0)) (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ Cfg (Fin 0))
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Empty) (PY q.kx q.b) Query)),
    BZeroCase q ∧ HasBits bd q.γ ∧
    (if BZeroCase q then HasBits bd q.γ else q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε) ∧
    q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ ∧ q.b ≤ bd ∧
    HasBits bd q.c0 ∧ HasBits bd q.T ∧ HasBits bd q.etaH ∧ HasBits bd q.etaD ∧
    (∀ j, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u)) ∧
    (∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z) ∧ (∀ c, ∀ i ∈ srcC c, i.Valid) ∧
    ((nprotocol (bprepC q srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      10 ^ 20 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
            (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Empty) := by
  have hγ : HasBits 1 zeroPub.γ := by simpa [zeroPub] using hasBits_one (bd := 1) le_rfl
  have hγ' : (if BZeroCase zeroPub then HasBits 1 zeroPub.γ
      else zeroPub.γ = gammaOf zeroPub.T zeroPub.etaH zeroPub.etaD zeroPub.g zeroPub.ε) := by
    rw [if_pos zeroPub_zero]
    exact hγ
  have hQ : 1 ≤ qOf zeroPub.s zeroPub.T zeroPub.etaH zeroPub.etaD zeroPub.g zeroPub.ε :=
    one_le_qOf (by norm_num [zeroPub]) (by norm_num [zeroPub]) (by norm_num [zeroPub])
      (by norm_num [zeroPub]) (by norm_num [zeroPub]) (by norm_num [zeroPub])
  have hζ : zeroPub.params.nu ≤
      196608 * qOf zeroPub.s zeroPub.T zeroPub.etaH zeroPub.etaD zeroPub.g zeroPub.ε *
        zeroPub.ζ := by
    show ImprovedODEQueryBudget.precision zeroPub.g zeroPub.ε ≤ _
    have e : ImprovedODEQueryBudget.precision zeroPub.g zeroPub.ε = 1 / 20000 := by
      unfold ImprovedODEQueryBudget.precision
      norm_num [zeroPub]
    have hz : zeroPub.ζ = 1 / 2 := rfl
    rw [e, hz]
    nlinarith
  have hc0 : HasBits 1 zeroPub.c0 := by simpa [zeroPub] using hasBits_one (bd := 1) le_rfl
  have hT : HasBits 1 zeroPub.T := by simpa [zeroPub] using hasBits_zero 1
  have hH : HasBits 1 zeroPub.etaH := by simpa [zeroPub] using hasBits_one (bd := 1) le_rfl
  have hD : HasBits 1 zeroPub.etaD := by simpa [zeroPub] using hasBits_zero 1
  have hdec : ∀ e z, (pointData Unit 1 1).decode e z = (zeroPub.c0 : ℂ) * gauss z :=
    fun _ _ => by simp [pointData, zeroPub]
  refine ⟨zeroPub, 1, zeroPub_ok0, pointData Unit 1 1, Equiv.refl _, fun _ => [], zeroPub_zero,
    hγ, hγ', hζ, le_rfl, hc0, hT, hH, hD, pointData_range Unit 1 1, hdec,
    fun _ _ hi => by simp at hi, ?_⟩
  exact (binary_ode_budget_bits_nonneg (X := Unit) (Zs := Empty) 1 zeroPub zeroPub_ok0 hγ' hζ
    le_rfl hc0 hT hH hD (pointData Unit 1 1) (Equiv.refl _) (pointData_range Unit 1 1) hdec
    (fun _ => []) (fun _ _ hi => by simp at hi)).1

/-- **The zero case of the time-dependent released-register budgets is not vacuous**
(equations `ode:eq:gate-main`, `ode:eq:gate-space`, time-dependent part): `zeroPubT` (`T = 0`,
`m = 0`), `b_data = 1`, the one-point time-indexed data, the identity equivalence and empty
loading and weight-preparation circuits satisfy every hypothesis of
`binary_ode_time_budget_bits_nonneg` (zero branch of its hypothesis on `γ`), and its gate bound
holds for them. -/
theorem zero_time_all_hyps : ∃ (q : PubT) (bd : ℕ) (hq : BTPublicOK0 q)
    (D : Data (Unit × Fin (2 ^ q.m)) (Cfg (Fin 0)) (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ Cfg (Fin 0))
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Empty) (Fin q.m ⊕ PY q.kx q.b)
      Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Empty) (Fin q.m ⊕ PY q.kx q.b) Query)),
    BTZeroCase q ∧
    (if BTZeroCase q then HasBits bd q.γ
      else q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) ∧
    q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ ∧ q.b ≤ bd ∧
    HasBits bd q.c0 ∧ HasBits bd q.T ∧ HasBits bd q.etaH ∧ HasBits bd q.etaD ∧
    (∀ j, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u)) ∧
    (∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z) ∧ (∀ i ∈ loadC, i.Valid) ∧
    (∀ i ∈ wpC, i.Valid) ∧
    ((nprotocol (btprepC q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      2 * 10 ^ 20 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Empty) := by
  have hγ' : (if BTZeroCase zeroPubT then HasBits 1 zeroPubT.γ
      else zeroPubT.γ = gammaOf zeroPubT.T zeroPubT.etaH zeroPubT.etaD (2 * zeroPubT.g)
        (zeroPubT.ε / 2)) := by
    rw [if_pos zeroPubT_zero]
    simpa [zeroPubT] using hasBits_one (bd := 1) le_rfl
  have hQ : 1 ≤ qOf zeroPubT.s zeroPubT.T zeroPubT.etaH zeroPubT.etaD (2 * zeroPubT.g)
      (zeroPubT.ε / 2) :=
    one_le_qOf (by norm_num [zeroPubT]) (by norm_num [zeroPubT]) (by norm_num [zeroPubT])
      (by norm_num [zeroPubT]) (by norm_num [zeroPubT]) (by norm_num [zeroPubT])
  have hζ : zeroPubT.params.nu ≤
      196608 * qOf zeroPubT.s zeroPubT.T zeroPubT.etaH zeroPubT.etaD (2 * zeroPubT.g)
        (zeroPubT.ε / 2) * zeroPubT.ζ := by
    show ImprovedODEQueryBudget.precision (2 * zeroPubT.g) (zeroPubT.ε / 2) ≤ _
    have e : ImprovedODEQueryBudget.precision (2 * zeroPubT.g) (zeroPubT.ε / 2) = 1 / 80000 := by
      unfold ImprovedODEQueryBudget.precision
      norm_num [zeroPubT]
    have hz : zeroPubT.ζ = 1 / 2 := rfl
    rw [e, hz]
    nlinarith
  have hc0 : HasBits 1 zeroPubT.c0 := by simpa [zeroPubT] using hasBits_one (bd := 1) le_rfl
  have hT : HasBits 1 zeroPubT.T := by simpa [zeroPubT] using hasBits_zero 1
  have hH : HasBits 1 zeroPubT.etaH := by simpa [zeroPubT] using hasBits_one (bd := 1) le_rfl
  have hD : HasBits 1 zeroPubT.etaD := by simpa [zeroPubT] using hasBits_zero 1
  have hdec : ∀ e z, (pointData (Unit × Fin (2 ^ zeroPubT.m)) 1 1).decode e z =
      (zeroPubT.c0 : ℂ) * gauss z := fun _ _ => by simp [pointData, zeroPubT]
  refine ⟨zeroPubT, 1, zeroPubT_ok0, pointData _ 1 1, Equiv.refl _, [], [], zeroPubT_zero, hγ',
    hζ, le_rfl, hc0, hT, hH, hD, pointData_range _ 1 1, hdec, fun _ hi => by simp at hi,
    fun _ hi => by simp at hi, ?_⟩
  exact (binary_ode_time_budget_bits_nonneg (X := Unit) (Zs := Empty) 1 zeroPubT zeroPubT_ok0
    hγ' hζ le_rfl hc0 hT hH hD (pointData _ 1 1) (Equiv.refl _) (pointData_range _ 1 1) hdec []
    (fun _ hi => by simp at hi) [] (fun _ hi => by simp at hi)).1

/-! ### The guarantees -/

/-- **Zero-time public data with the public arithmetic accuracy**: `zeroPub` with
`ζ = ν/(196608 q*)` (`GateBitBudget.zetaOf`, `ν = precision 1 (1/2)`, `q* = qOf 1 0 1 0 1 (1/2)`),
for the guarantees of the zero-case endpoints. -/
def zeroPubZ : Pub :=
  ⟨0, 0, le_rfl, 1, 1, 1, 0, 1, 0, 1, 1 / 2, 1, 0,
    zetaOf (ImprovedODEQueryBudget.precision 1 (1 / 2)) (qOf ((2 ^ 0 : ℕ) : ℝ) 0 1 0 1 (1 / 2))⟩

/-- The query shape of `zeroPubZ` is at least one. -/
theorem zeroPubZ_q : 1 ≤ qOf ((2 ^ 0 : ℕ) : ℝ) 0 1 0 1 (1 / 2) :=
  one_le_qOf le_rfl zero_le_one le_rfl le_rfl (by norm_num) (by norm_num)

/-- The precision `ν = ε/(10⁴ g)` of `zeroPubZ` (here `1/20000`) lies in `(0, 1]`. -/
theorem zeroPubZ_nu : 0 < ImprovedODEQueryBudget.precision 1 (1 / 2) ∧
    ImprovedODEQueryBudget.precision 1 (1 / 2) ≤ 1 := by
  unfold ImprovedODEQueryBudget.precision
  constructor <;> norm_num

/-- The arithmetic accuracy of `zeroPubZ` lies in `(0, 1]`, meets `ν ≤ 196608 q* ζ`, and
`98304 q* ζ = ν/2` (`GateBitBudget.zetaOf_spec`). -/
theorem zeroPubZ_spec :
    0 < zetaOf (ImprovedODEQueryBudget.precision 1 (1 / 2))
        (qOf ((2 ^ 0 : ℕ) : ℝ) 0 1 0 1 (1 / 2)) ∧
      zetaOf (ImprovedODEQueryBudget.precision 1 (1 / 2))
        (qOf ((2 ^ 0 : ℕ) : ℝ) 0 1 0 1 (1 / 2)) ≤ 1 ∧
      ImprovedODEQueryBudget.precision 1 (1 / 2) ≤
        196608 * qOf ((2 ^ 0 : ℕ) : ℝ) 0 1 0 1 (1 / 2) *
          zetaOf (ImprovedODEQueryBudget.precision 1 (1 / 2))
            (qOf ((2 ^ 0 : ℕ) : ℝ) 0 1 0 1 (1 / 2)) ∧
      98304 * qOf ((2 ^ 0 : ℕ) : ℝ) 0 1 0 1 (1 / 2) *
          zetaOf (ImprovedODEQueryBudget.precision 1 (1 / 2))
            (qOf ((2 ^ 0 : ℕ) : ℝ) 0 1 0 1 (1 / 2)) =
        ImprovedODEQueryBudget.precision 1 (1 / 2) / 2 :=
  zetaOf_spec zeroPubZ_nu.1 zeroPubZ_nu.2 zeroPubZ_q

/-- `zeroPubZ` satisfies the public conditions `BPublicOK0` of every `T ≥ 0`. -/
theorem zeroPubZ_ok0 : BPublicOK0 zeroPubZ := by
  obtain ⟨h1, h2, -, -⟩ := zeroPubZ_spec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h1, h2⟩ <;> norm_num [zeroPubZ]

/-- **The empty source circuit implements the controlled identity exactly**: on the one-point
data, the empty circuit is within `0` of the lifted source interface `J_src = 1`. -/
theorem approx_empty (c : Bool) :
    ApproxOn CleanX
      (nrun (prims (R := ℂ) (pointData Unit 1 1) (Equiv.refl (Cfg (Fin 0))) ())
        ([] : List (NInstr ((Unit ⊕ Fin 0) ⊕ Empty) (PY 0 1) Query)))
      (liftB (srcIdeal c (1 : Reg (Fin 0) ℂ →L[ℂ] Reg (Fin 0) ℂ))) 0 := by
  have h1 : srcIdeal c (1 : Reg (Fin 0) ℂ →L[ℂ] Reg (Fin 0) ℂ) = 1 := by
    unfold srcIdeal
    simp only [ite_self]
    exact localOp_one _
  rw [h1, liftB_one, nrun_nil]
  intro ψ _
  simp

/-- **Every hypothesis of the zero-case endpoints holds at once, the antecedents of the guarantee
included** (equations `ode:eq:gate-main`, `ode:eq:gate-space` with the remark on zero time and a
known zero generator): for `zeroPubZ` (`T = 0`, `γ = 1`, `ζ = ν/(196608 q*)`), `b_data = 1`, the
one-point data, the identity equivalence, empty source circuits, `J_src = 1`, `x₀ = seedV`,
`v = 0` and `ζs = 0`, every hypothesis of `binary_ode_budget_bits_zero`,
`binary_ode_budget_bits_zero_released` and `binary_ode_budget_bits_nonneg` (zero branch) and every
antecedent of their guarantees `NOutcome` hold (with `2 ζs ≤ ν` and `98304 q* ζ + 2 ζs ≤ ν`). -/
theorem zero_instance_all_hyps :
    ∃ (q : Pub) (bd : ℕ) (D : Data Unit (Cfg (Fin 0)) (Cfg (VW q.b)) q.s)
      (en : Cfg (Fin q.kx) ≃ Cfg (Fin 0))
      (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Empty) (PY q.kx q.b) Query))
      (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (x0 v : Reg (Fin q.kx) ℂ),
    BPublicOK0 q ∧ BZeroCase q ∧
    (if BZeroCase q then HasBits bd q.γ else q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε) ∧
    q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ ∧ q.b ≤ bd ∧
    HasBits bd q.c0 ∧ HasBits bd q.T ∧ HasBits bd q.etaH ∧ HasBits bd q.etaD ∧
    (∀ j, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u)) ∧
    (∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z) ∧ (∀ c, ∀ i ∈ srcC c, i.Valid) ∧
    (∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix ()) i j‖ ^ 2 ≤ q.etaH ^ 2) ∧
    (∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix ()) i j‖ ^ 2 ≤ q.etaH ^ 2) ∧
    (∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix ()) i j‖ ^ 2 ≤ q.etaD ^ 2) ∧
    (∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix ()) i j‖ ^ 2 ≤ q.etaD ^ 2) ∧
    (∀ w : EuclideanSpace ℂ (Cfg (Fin 0)), 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.dissipativePart (D.matrix ())) w)).re) ∧
    (∀ c, IsUnitary (Jsrc c)) ∧
    (∀ c, ApproxOn CleanX (nrun (prims (R := ℂ) D en ()) (srcC c))
      (liftB (srcIdeal c (Jsrc c))) 0) ∧
    98304 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ + 2 * 0 ≤ q.params.nu ∧
    2 * (0 : ℝ) ≤ q.params.nu ∧
    ‖x0‖ = q.r₀ ∧ ‖v‖ = q.rb ∧
    (x0 ≠ 0 → Jsrc false (seedV (S := Fin q.kx)) = unitDirection x0) ∧
    (v ≠ 0 → Jsrc true (seedV (S := Fin q.kx)) = unitDirection v) ∧
    ODEConstantForcing.solution (-mLift D en ()) x0 v q.T ≠ 0 ∧
    q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-mLift D en ()) x0 v q.T‖ := by
  obtain ⟨-, -, hζ, hhalf⟩ := zeroPubZ_spec
  have hz : BZeroCase zeroPubZ := Or.inl rfl
  have hγ' : (if BZeroCase zeroPubZ then HasBits 1 zeroPubZ.γ
      else zeroPubZ.γ = gammaOf zeroPubZ.T zeroPubZ.etaH zeroPubZ.etaD zeroPubZ.g zeroPubZ.ε) := by
    rw [if_pos hz]
    simpa [zeroPubZ] using hasBits_one (bd := 1) le_rfl
  have hdec : ∀ e z, (pointData Unit 1 1).decode e z = (zeroPubZ.c0 : ℂ) * gauss z :=
    fun _ _ => by simp [pointData, zeroPubZ]
  have hM : (pointData Unit 1 1).matrix () = 0 := pointData_matrix Unit ()
  have hν : 0 < ImprovedODEQueryBudget.precision 1 (1 / 2) := zeroPubZ_nu.1
  refine ⟨zeroPubZ, 1, pointData Unit 1 1, Equiv.refl _, fun _ => [],
    fun _ => 1, seedV, 0, zeroPubZ_ok0, hz, hγ', hζ, le_rfl,
    by simpa [zeroPubZ] using hasBits_one (bd := 1) le_rfl,
    by simpa [zeroPubZ] using hasBits_zero 1,
    by simpa [zeroPubZ] using hasBits_one (bd := 1) le_rfl,
    by simpa [zeroPubZ] using hasBits_zero 1, pointData_range Unit 1 1, hdec,
    fun _ _ hi => by simp at hi, ?_, ?_, ?_, ?_, ?_, fun _ => isUnitary_one,
    fun c => approx_empty c, ?_, ?_, ?_, ?_, fun _ => ?_,
    fun h => absurd rfl h, ?_, ?_⟩
  · intro i
    rw [hM]
    simp [zeroPubZ]
  · intro j
    rw [hM]
    simp [zeroPubZ]
  · intro i
    rw [hM]
    simp [zeroPubZ]
  · intro j
    rw [hM]
    simp [zeroPubZ]
  · intro w
    have h0 : ODEMatrixEnergy.dissipativePart (0 : Matrix (Cfg (Fin 0)) (Cfg (Fin 0)) ℂ) = 0 := by
      funext i j
      simp
    rw [hM, h0, NativeZeroSimulation.matrixOperator_zero]
    simp
  · show 98304 * qOf ((2 ^ 0 : ℕ) : ℝ) 0 1 0 1 (1 / 2) *
        zetaOf (ImprovedODEQueryBudget.precision 1 (1 / 2))
          (qOf ((2 ^ 0 : ℕ) : ℝ) 0 1 0 1 (1 / 2)) + 2 * 0 ≤
      ImprovedODEQueryBudget.precision 1 (1 / 2)
    linarith
  · show 2 * (0 : ℝ) ≤ ImprovedODEQueryBudget.precision 1 (1 / 2)
    linarith
  · show ‖(seedV : Reg (Fin 0) ℂ)‖ = 1
    exact norm_seedV
  · show ‖(0 : Reg (Fin 0) ℂ)‖ = 0
    exact norm_zero
  · show (1 : Reg (Fin 0) ℂ →L[ℂ] Reg (Fin 0) ℂ) seedV = unitDirection seedV
    rw [unitDirection, norm_seedV, inv_one, one_smul]
    rfl
  · show ODEConstantForcing.solution _ _ _ (0 : ℝ) ≠ 0
    rw [ODEConstantForcing.solution_zero]
    intro h
    have := norm_seedV (S := Fin zeroPubZ.kx)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  · show (1 : ℝ) + 0 * 0 ≤ 1 * ‖ODEConstantForcing.solution _ _ _ (0 : ℝ)‖
    rw [ODEConstantForcing.solution_zero, norm_seedV]
    norm_num

/-- **The guarantees of the zero-case endpoints hold for explicit data** (equations
`ode:eq:gate-main`, `ode:eq:gate-space` with the remark on zero time and a known zero generator):
for the data of `zero_instance_all_hyps`, the guarantee `NOutcome` of `binary_ode_budget_bits_zero`
on the minimal register and that of `binary_ode_budget_bits_nonneg` on the released register (the
guarantee of `binary_ode_budget_bits_zero_released` too) hold against the solution `x(T)`. -/
theorem zero_instance_outcome :
    ∃ (q : Pub) (hq : BPublicOK0 q) (D : Data Unit (Cfg (Fin 0)) (Cfg (VW q.b)) q.s)
      (en : Cfg (Fin q.kx) ≃ Cfg (Fin 0))
      (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Empty) (PY q.kx q.b) Query))
      (x0 v : Reg (Fin q.kx) ℂ),
    BZeroCase q ∧
    NOutcome (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (MinW 0 q.kx Empty) (PY q.kx q.b) Query)) q.g q.ε hq.g_ge
      (prims (R := ℂ) D en ()) (ODEConstantForcing.solution (-mLift D en ()) x0 v q.T) ∧
    NOutcome (bprepC q srcC) q.g q.ε hq.g_ge (prims (R := ℂ) D en ())
      (ODEConstantForcing.solution (-mLift D en ()) x0 v q.T) := by
  obtain ⟨q, bd, D, en, srcC, Jsrc, x0, v, hq, hz, hγ, hζ, hb, hc0, hT, hH, hD, hr, hdec, hV,
    hrH, hcH, hrD, hcD, hPSD, hJ, hsrc, hbud, hbud0, h0, hv, hpx, hpv, hne, hB⟩ :=
    zero_instance_all_hyps
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h1⟩ :=
    binary_ode_budget_bits_zero (X := Unit) (Zs := Empty) bd q hq hz D en srcC hV 0 0
  obtain ⟨-, -, -, -, -, -, -, -, -, h3⟩ := binary_ode_budget_bits_nonneg (X := Unit)
    (Zs := Empty) bd q hq hγ hζ hb hc0 hT hH hD D en hr hdec srcC hV
  exact ⟨q, hq, D, en, srcC, x0, v, hz,
    h1 () hrH hrD Jsrc x0 v 0 hJ le_rfl hsrc hbud0 h0 hv hpx hpv hne hB,
    h3 () hrH hcH hrD hcD hPSD Jsrc x0 v 0 hJ le_rfl hsrc hbud h0 hv hpx hpv hne hB⟩

end

end SparseHamiltonian.GateRemarks.ODE
