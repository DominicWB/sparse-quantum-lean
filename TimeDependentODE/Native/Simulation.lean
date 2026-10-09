import TimeDependentODE.Native.Layer
import TimeDependentHamiltonian.Chronology.Products
import SparseHamiltonian.ManuscriptPrecision

/-!
# Coherent sampled-time ODE SELECT

On a uniform mesh with `M` intervals, every coherent branch `i` evolves under
the tagged LCHS Hamiltonian of the samples, with its own nonnegative duration
`u i r ≤ T` on the interval of sample `r` (`selectEvolution`). The released
joint Cayley analysis supplies the clock promises for each slot
(`ODEJointCayley`), the time-dependent chronological clock of
`TimeDependentHamiltonian` amplifies and reuses them, and the native layer
implements each active layer with `72` coherent sampled-time queries.

`Select.select` gives one program and one aligned clean encoding, chosen
before the branch parameters, with at most
`663552 * shape (2 s) (ρ T) (log (2/ε))` queries and full-output error at most
`ε` against the ordered branch products, under the public mesh conditions
`8 s ρ T ≤ M` and `3 (√(2s) ρ T)³ ≤ ε M²`.
-/

namespace SparseHamiltonian.TimeDependentODE

namespace Select

noncomputable section

open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding CayleyClockInterface
open ImprovedCayleyMoments
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

/-! ### Ordered products of diagonal families -/

section Products

variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℂ (V i)]

/-- Ordered products of diagonal families are diagonal. -/
theorem evolution_diagonal (A : ℕ → ∀ i, V i →L[ℂ] V i) (m : ℕ) :
    TimeDependent.evolution (fun t => WeightedClock.diagonal (A t)) m =
      WeightedClock.diagonal (fun i => TimeDependent.evolution (fun t => A t i) m) := by
  induction m with
  | zero =>
    rw [TimeDependent.evolution_zero]
    simp only [TimeDependent.evolution_zero]
    exact WeightedClock.diagonal_one.symm
  | succ m ih =>
    rw [TimeDependent.evolution_succ, ih]
    simp only [TimeDependent.evolution_succ]
    exact WeightedClock.diagonal_comp _ _

end Products

/-- Ordered products depend only on the factors used. -/
theorem evolution_congr {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    (U U' : ℕ → P →L[ℂ] P) (m : ℕ) (h : ∀ t < m, U t = U' t) :
    TimeDependent.evolution U m = TimeDependent.evolution U' m := by
  induction m with
  | zero => rw [TimeDependent.evolution_zero, TimeDependent.evolution_zero]
  | succ m ih =>
    rw [TimeDependent.evolution_succ, TimeDependent.evolution_succ, h m (Nat.lt_succ_self m),
      ih (fun t ht => h t (Nat.lt_succ_of_lt ht))]

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s M : ℕ}

/-- Rescaled Cayley step of the sampled ODE clock. -/
def step (s γ ρ T : ℝ) (M : ℕ) : ℝ := time (2 * s) (ρ * T) γ / M

/-- Filter degree of the slot-dependent ODE clock. -/
def degree (s γ ρ T ε : ℝ) (M : ℕ) : ℕ :=
  SharpFilterSchedule.degree (width (2 * s) γ) ((M : ℝ) * step s γ ρ T M * moment γ) (ε / 3)

/-- Per-branch public rescaling at each sample, with the duration fraction. -/
def rescaling (γ T : ℝ) (u : ι → Fin M → ℝ) (i : ι) (r : Fin M) : ℝ := γ * (u i r / T)

/-- The private slot action at chronological slot `t`. -/
def actions (D : Data (X × Fin M) n Z s) (hM : 0 < M) (k : ι → ℝ) (u : ι → Fin M → ℝ)
    (ρ T γ : ℝ) (x : X) (t : ℕ) : ODEJointNative.Private ι n →L[ℂ] ODEJointNative.Private ι n :=
  slotAction D k (rescaling γ T u) ρ x (TimeDependent.Sampled.sampleIndex hM t)

omit [DecidableEq ι] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The slot action is the released joint Cayley action of the sample. -/
theorem actions_eq (D : Data (X × Fin M) n Z s) (hM : 0 < M) (k : ι → ℝ)
    (u : ι → Fin M → ℝ) (ρ T γ : ℝ) (x : X) (t : ℕ) :
    actions D hM k u ρ T γ x t =
      ODEJointCayley.action D (x, TimeDependent.Sampled.sampleIndex hM t) k
        (fun i => u i (TimeDependent.Sampled.sampleIndex hM t)) ρ T γ := rfl

/-- The clean input: smoothing preparation followed by the native encoding. -/
def input (D : Data (X × Fin M) n Z s) (hM : 0 < M) (b0 : ι × Fin M) (γ ρ T ε : ℝ) :
    ODEJointNative.Public ι n →L[ℂ]
      Physical ι n Z M M (degree (s : ℝ) γ ρ T ε M) :=
  (embedding D hM b0 M (degree (s : ℝ) γ ρ T ε M)).toContinuousLinearMap ∘L
    SharpClockQuery.input (P := ODEJointNative.Public ι n) (V := ODEJointNative.Private ι n)
      (step (s : ℝ) γ ρ T M) (width (2 * (s : ℝ)) γ) (moment γ) M (ε / 3)

/-- The clean output embedding. -/
def output (D : Data (X × Fin M) n Z s) (hM : 0 < M) (b0 : ι × Fin M) (γ ρ T ε : ℝ) :
    ODEJointNative.Public ι n →L[ℂ]
      Physical ι n Z M M (degree (s : ℝ) γ ρ T ε M) :=
  (embedding D hM b0 M (degree (s : ℝ) γ ρ T ε M)).toContinuousLinearMap ∘L
    SharpClockSimulation.output (P := ODEJointNative.Public ι n)
      (V := ODEJointNative.Private ι n)
      (step (s : ℝ) γ ρ T M) (width (2 * (s : ℝ)) γ) (moment γ) M (ε / 3)

/-- The ordered branch evolution: branch `i` uses duration `u i r` on the
interval of sample `r`. -/
def branchEvolution (D : Data (X × Fin M) n Z s) (hM : 0 < M) (k : ι → ℝ)
    (u : ι → Fin M → ℝ) (x : X) (i : ι) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  TimeDependent.evolution (fun t => NormedSpace.exp
    ((-Complex.I * ((u i (TimeDependent.Sampled.sampleIndex hM t) / M : ℝ) : ℂ)) •
      SparseStateOverlap.matrixOperator (ODEMatrixEnergy.lchsHamiltonian
        (D.matrix (x, TimeDependent.Sampled.sampleIndex hM t)) (k i)))) M

/-- The SELECT target on the joint branch register. -/
def selectEvolution (D : Data (X × Fin M) n Z s) (hM : 0 < M) (k : ι → ℝ)
    (u : ι → Fin M → ℝ) (x : X) : ODEJointNative.Public ι n →L[ℂ] ODEJointNative.Public ι n :=
  WeightedClock.diagonal (fun i => branchEvolution D hM k u x i)

variable {Label K : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [DecidableEq ι] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
set_option maxRecDepth 8192 in
/-- The coherent sampled-time ODE construction on any fixed isometric
encoding of the clock workspace whose active layers are implemented at cost
`q`. -/
theorem select_core (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD R T : ℝ) (k : ι → ℝ) (u : ι → Fin M → ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hρ : 0 < etaH + R * etaD)
    (hT : 0 < T) (hk : ∀ i, |k i| ≤ R)
    (hu : ∀ i r, 0 ≤ u i r) (huT : ∀ i r, u i r ≤ T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (γ ε : ℝ) (hγ : 0 < γ) (hγOne : γ ≤ 1) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hStep : step (s : ℝ) γ (etaH + R * etaD) T M ≤ 1 / 4)
    (O : Label → X → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (E : SharpClockQuery.Space (P := ODEJointNative.Public ι n)
      (V := ODEJointNative.Private ι n)
      (step (s : ℝ) γ (etaH + R * etaD) T M) (width (2 * (s : ℝ)) γ) (moment γ) M (ε / 3)
        →L[ℂ] K)
    (hE : E† ∘L E = 1) (q : ℕ)
    (hQuery : ∀ r < 2 * SharpFilterSchedule.degree (width (2 * (s : ℝ)) γ)
        ((M : ℝ) * step (s : ℝ) γ (etaH + R * etaD) T M * moment γ) (ε / 3),
      LabeledEncodedOracle.ImplementsOn O
        (fun x => TimeDependent.activeClockV (P := ODEJointNative.Public ι n)
          (actions D hM k u (etaH + R * etaD) T γ x) M
          (SharpFilterSchedule.degree (width (2 * (s : ℝ)) γ)
            ((M : ℝ) * step (s : ℝ) γ (etaH + R * etaD) T M * moment γ) (ε / 3)) r) E q) :
    ∃ p : MultiOracleCircuit.Program O,
      p.count ≤ 6 * SharpFilterSchedule.degree (width (2 * (s : ℝ)) γ)
        ((M : ℝ) * step (s : ℝ) γ (etaH + R * etaD) T M * moment γ) (ε / 3) * q ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L (E ∘L SharpClockQuery.input (step (s : ℝ) γ (etaH + R * etaD) T M)
            (width (2 * (s : ℝ)) γ) (moment γ) M (ε / 3)) -
          (E ∘L SharpClockSimulation.output (step (s : ℝ) γ (etaH + R * etaD) T M)
            (width (2 * (s : ℝ)) γ) (moment γ) M (ε / 3)) ∘L selectEvolution D hM k u x‖ ≤
          2 * (ε / 3) +
            M * (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / M) ^ 3 := by
  classical
  let J := ODEJointCayley.boundary (ι := ι) D
  let w := step (s : ℝ) γ (etaH + R * etaD) T M
  let slot : ℕ → Fin M := TimeDependent.Sampled.sampleIndex hM
  let G : X → ℕ → _ := fun x t =>
    ODEJointCayley.generator D (x, slot t) k (fun i => u i (slot t)) (etaH + R * etaD) T
  let S : X → ℕ → _ := fun x t =>
    ODEJointCayley.inverse D (x, slot t) k (fun i => u i (slot t)) (etaH + R * etaD) T γ
  have hs : 0 < s := D.slots_pos
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hw : 0 ≤ w := by
    have ht : 0 ≤ time (2 * (s : ℝ)) ((etaH + R * etaD) * T) γ :=
      div_nonneg (mul_nonneg (mul_nonneg hρ.le hT.le) (Real.sqrt_nonneg _)) hγ.le
    exact div_nonneg ht hMR.le
  have hJ : J† ∘L J = 1 := ODEJointCayley.boundary_isometry D
  have hMom : ∀ x t, ‖G x t‖ ≤ Real.sqrt (2 * (s : ℝ)) ∧ ‖G x t ∘L J‖ ≤ 1 := fun x t =>
    ODEJointCayley.moment_certificate D (x, slot t) etaH etaD R T k (fun i => u i (slot t))
      hH hDiss hρ hT hk (fun i => hu i _) (fun i => huT i _)
      (hrH _) (hcH _) (hrD _) (hcD _)
  have hSelf : ∀ x t, star (G x t) = G x t := fun x t =>
    ODEJointCayley.generator_adjoint D (x, slot t) k (fun i => u i (slot t)) (etaH + R * etaD) T
  have hAct : ∀ x t, actions D hM k u (etaH + R * etaD) T γ x t = cayleyAction (scaled (G x t) γ) (S x t) :=
    fun x t => ODEJointCayley.action_eq_cayley D (x, slot t) k (fun i => u i (slot t)) (etaH + R * etaD) T γ
  have hD : ∀ x t, (actions D hM k u (etaH + R * etaD) T γ x t)† ∘L actions D hM k u (etaH + R * etaD) T γ x t = 1 :=
    fun x t => (ODEJointCayley.action_unitary D (x, slot t) k (fun i => u i (slot t)) (etaH + R * etaD) T γ).1
  have hRight : ∀ x t, (1 - actions D hM k u (etaH + R * etaD) T γ x t) ∘L
      resolventAtOne (scaled (G x t) γ) = 1 := by
    intro x t
    change (1 - actions D hM k u (etaH + R * etaD) T γ x t) * resolventAtOne (scaled (G x t) γ) = 1
    rw [hAct]
    exact one_sub_cayleyAction_mul_resolventAtOne
      (A := ODEJointNative.Private ι n →L[ℂ] ODEJointNative.Private ι n)
      (scaled (G x t) γ) (S x t)
      (ODEJointCayley.inverse_right D (x, slot t) k (fun i => u i (slot t)) (etaH + R * etaD) T γ)
      (ODEJointCayley.inverse_left D (x, slot t) k (fun i => u i (slot t)) (etaH + R * etaD) T γ)
  have hLeft : ∀ x t, resolventAtOne (scaled (G x t) γ) ∘L
      (1 - actions D hM k u (etaH + R * etaD) T γ x t) = 1 := by
    intro x t
    change resolventAtOne (scaled (G x t) γ) * (1 - actions D hM k u (etaH + R * etaD) T γ x t) = 1
    rw [hAct]
    exact resolventAtOne_mul_one_sub_cayleyAction
      (A := ODEJointNative.Private ι n →L[ℂ] ODEJointNative.Private ι n)
      (scaled (G x t) γ) (S x t)
      (ODEJointCayley.inverse_right D (x, slot t) k (fun i => u i (slot t)) (etaH + R * etaD) T γ)
  obtain ⟨p, hCount, hEval⟩ := TimeDependent.implementationV_query_certificate
    (fun x => actions D hM k u (etaH + R * etaD) T γ x) J w (width (2 * (s : ℝ)) γ) (moment γ) M (ε / 3)
    (width_ge_one _ _) hw hStep hD hJ O hO E hE q hQuery
  have hOutIso := SharpClockSimulation.output_isometry (P := ODEJointNative.Public ι n)
    (V := ODEJointNative.Private ι n) w (width (2 * (s : ℝ)) γ) (moment γ) M (ε / 3)
    (width_ge_one _ _)
  refine ⟨p, hCount, fun x => ⟨p.eval_unitary hO x, ?_⟩⟩
  obtain ⟨U, Rs, hRRight, _hRLeft, hCayley, _hIso, hImpl, _hDeg⟩ :=
    TimeDependent.exists_precise_implementationV (actions D hM k u (etaH + R * etaD) T γ x)
      (fun t => resolventAtOne (scaled (G x t) γ)) J
      (fun t => compressed (G x t) J γ) w (width (2 * (s : ℝ)) γ) (endpoint γ) (moment γ) M
      (width_ge_one _ _) hw hStep (hD x) hJ (hRight x) (hLeft x)
      (fun t => resolvent_norm (G x t) (2 * (s : ℝ)) γ hγ.le (hMom x t).1)
      (fun t => resolventAtOne_compression (scaled (G x t) γ) J hJ)
      (fun t => compressed_self_adjoint (G x t) J γ (hSelf x t))
      (fun t => (compressed_norm (G x t) J γ hγ.le hJ (hMom x t).2).trans hγOne)
      (fun t => endpoint_norm (G x t) J γ (hSelf x t) hJ hγ.le (hMom x t).2)
      (endpoint_sq γ).le (moment_le_width (2 * (s : ℝ)) γ hγ.le hγOne) (ε / 3)
      (by positivity) (by linarith)
  -- Each Cayley step is within `(√(2s) (etaH + R * etaD) T / M)^3` of the sampled exponential.
  let Xs : ℕ → ODEJointNative.Public ι n →L[ℂ] ODEJointNative.Public ι n := fun t =>
    (-Complex.I * (w : ℂ)) • compressed (G x t) J γ
  have hXdiag : ∀ t, Xs t = WeightedClock.diagonal (fun i =>
      (-Complex.I * ((u i (slot t) / M : ℝ) : ℂ)) •
        SparseStateOverlap.matrixOperator
          (ODEMatrixEnergy.lchsHamiltonian (D.matrix (x, slot t)) (k i))) := by
    intro t
    have h := ODEJointCayley.physical_exponent D (x, slot t) k (fun i => u i (slot t)) (etaH + R * etaD) T γ
      hρ.ne' hT hγ.ne'
    have hsplit : (-Complex.I * (w : ℂ)) =
        ((M : ℂ)⁻¹) * (-Complex.I * (time (2 * (s : ℝ)) ((etaH + R * etaD) * T) γ : ℂ)) := by
      simp only [w, step]
      push_cast
      field_simp
    change (-Complex.I * (w : ℂ)) • compressed (G x t) J γ = _
    rw [hsplit, mul_smul, h, CoherentQuerySchedule.smul_diagonal]
    congr 1
    funext i
    rw [smul_smul]
    congr 1
    push_cast
    field_simp
  have hSkew : ∀ t, star (Xs t) = -Xs t := by
    intro t
    change star ((-Complex.I * (w : ℂ)) • compressed (G x t) J γ) =
      -((-Complex.I * (w : ℂ)) • compressed (G x t) J γ)
    rw [star_smul, compressed_self_adjoint (G x t) J γ (hSelf x t)]
    rw [← neg_smul]
    congr 1
    simp [Complex.conj_ofReal]
  have hwγ : w * γ = Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / M := by
    simp only [w, step, time]
    field_simp
  have hXnorm : ∀ t, ‖Xs t‖ ≤ Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / M := by
    intro t
    have hHk := compressed_norm (G x t) J γ hγ.le hJ (hMom x t).2
    calc
      ‖Xs t‖ = w * ‖compressed (G x t) J γ‖ := by
        change ‖(-Complex.I * (w : ℂ)) • compressed (G x t) J γ‖ = _
        rw [norm_smul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_of_nonneg hw]
      _ ≤ w * γ := mul_le_mul_of_nonneg_left hHk hw
      _ = Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / M := hwγ
  have hXone : ∀ t, ‖Xs t‖ ≤ 1 := by
    intro t
    have hle : Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / M ≤ w := by
      rw [← hwγ]
      exact mul_le_of_le_one_right hw hγOne
    linarith [hXnorm t]
  have hnum : ∀ t, CayleyTransfer.cayleyNumerator w (compressed (G x t) J γ) =
      1 + (1 / 2 : ℂ) • Xs t := by
    intro t
    simp only [CayleyTransfer.cayleyNumerator, Xs, smul_smul]
    rw [sub_eq_add_neg, ← neg_smul]
    congr 2
    ring
  have hden : ∀ t, CayleyTransfer.cayleyDenominator w (compressed (G x t) J γ) =
      1 - (1 / 2 : ℂ) • Xs t := by
    intro t
    simp only [CayleyTransfer.cayleyDenominator, Xs, smul_smul]
    rw [sub_eq_add_neg, ← neg_smul]
    congr 2
    ring
  have hUform : ∀ t, U t = (1 + (1 / 2 : ℂ) • Xs t) * Rs t := by
    intro t
    rw [hCayley t, hnum t]
    rfl
  have hRform : ∀ t, (1 - (1 / 2 : ℂ) • Xs t) * Rs t = 1 := by
    intro t
    rw [← hden t]
    exact hRRight t
  have hStepErr : ∀ t, ‖U t - NormedSpace.exp (Xs t)‖ ≤
      (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / M) ^ 3 := by
    intro t
    have h := CayleyApproximation.cayley_power_exp_error_of_inverse (Xs t) (Rs t)
      (hXone t) (hSkew t) (hRform t) 1
    rw [pow_one, one_smul, Nat.cast_one, one_mul, ← hUform t] at h
    exact h.trans (pow_le_pow_left₀ (norm_nonneg _) (hXnorm t) 3)
  have hUnorm : ∀ t, ‖U t‖ ≤ 1 := by
    intro t
    rw [hUform t]
    exact CayleyTransfer.skew_cayley_norm_le_one (Xs t) (Rs t) (hSkew t) (hRform t)
  have hExpNorm : ∀ t, ‖NormedSpace.exp (Xs t)‖ ≤ 1 := fun t =>
    CayleyApproximation.skew_exp_norm_le (Xs t) (hSkew t)
  have hProd : ‖TimeDependent.evolution U M - selectEvolution D hM k u x‖ ≤
      M * (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / M) ^ 3 := by
    have hEq : selectEvolution D hM k u x =
        TimeDependent.evolution (fun t => NormedSpace.exp (Xs t)) M := by
      have hExp : ∀ t, NormedSpace.exp (Xs t) = WeightedClock.diagonal (fun i =>
          NormedSpace.exp ((-Complex.I * ((u i (slot t) / M : ℝ) : ℂ)) •
            SparseStateOverlap.matrixOperator
              (ODEMatrixEnergy.lchsHamiltonian (D.matrix (x, slot t)) (k i)))) := by
        intro t
        rw [hXdiag t]
        exact CoherentDiagonalExp.exp_diagonal
          (V := fun _ : ι => EuclideanSpace ℂ n) _
      simp only [hExp]
      rw [evolution_diagonal]
      rfl
    rw [hEq]
    exact TimeDependent.evolution_sub_norm_le_mul U _ hUnorm hExpNorm hStepErr M
  have hOutNorm : ‖SharpClockSimulation.output (P := ODEJointNative.Public ι n)
      (V := ODEJointNative.Private ι n) w (width (2 * (s : ℝ)) γ) (moment γ) M (ε / 3)‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro v
    have h := ((SharpClockSimulation.output (P := ODEJointNative.Public ι n)
      (V := ODEJointNative.Private ι n) w (width (2 * (s : ℝ)) γ) (moment γ) M
        (ε / 3)).norm_map_iff_adjoint_comp_self.mpr hOutIso) v
    rw [h, one_mul]
  have hMain : ‖p.eval x ∘L (E ∘L SharpClockQuery.input w (width (2 * (s : ℝ)) γ)
        (moment γ) M (ε / 3)) -
      (E ∘L SharpClockSimulation.output w (width (2 * (s : ℝ)) γ) (moment γ) M (ε / 3)) ∘L
        TimeDependent.evolution U M‖ ≤ 2 * (ε / 3) := by
    rw [hEval x, comp_assoc, ← comp_sub, EncodedOracle.norm_comp_eq E hE]
    exact hImpl
  calc
    _ ≤ ‖p.eval x ∘L (E ∘L SharpClockQuery.input w (width (2 * (s : ℝ)) γ) (moment γ) M
            (ε / 3)) -
          (E ∘L SharpClockSimulation.output w (width (2 * (s : ℝ)) γ) (moment γ) M (ε / 3)) ∘L
            TimeDependent.evolution U M‖ +
        ‖(E ∘L SharpClockSimulation.output w (width (2 * (s : ℝ)) γ) (moment γ) M (ε / 3)) ∘L
            TimeDependent.evolution U M -
          (E ∘L SharpClockSimulation.output w (width (2 * (s : ℝ)) γ) (moment γ) M (ε / 3)) ∘L
            selectEvolution D hM k u x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * (ε / 3) + M * (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / M) ^ 3 := by
      apply add_le_add hMain
      rw [← comp_sub, comp_assoc, EncodedOracle.norm_comp_eq E hE]
      calc
        _ ≤ ‖SharpClockSimulation.output (P := ODEJointNative.Public ι n)
            (V := ODEJointNative.Private ι n) w (width (2 * (s : ℝ)) γ) (moment γ) M (ε / 3)‖ *
            ‖TimeDependent.evolution U M - selectEvolution D hM k u x‖ := opNorm_comp_le _ _
        _ ≤ 1 * (M * (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / M) ^ 3) :=
          mul_le_mul hOutNorm hProd (norm_nonneg _) zero_le_one
        _ = M * (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / M) ^ 3 := one_mul _

end

end Select

end SparseHamiltonian.TimeDependentODE
