import TimeDependentODE.Native.Select

set_option autoImplicit false

/-!
# The coherent sampled-time ODE SELECT with an arbitrary slot-to-sample map

The released ODE SELECT (`SparseHamiltonian.TimeDependentODE.Select`) runs the chronological
clock with `M` slots and lets slot `t` use the sample `t mod M`; only the clean encoding of the
private cells depends on that choice (`TimeDependentODE.privateEmbedding`). Here slot `t` of
`N` slots uses an arbitrary public sample `σ t` (`privateEmbedding`, `embedding`): the
queries, the native program and its count are the released ones, every slot-dependent active
layer is still implemented with `72` coherent sampled-time queries (`implementsOn`), and the
SELECT approximates, on every branch `i`, the ordered product over the `N` slots of
`exp(-i (u_i(σ t) / N) K_{k_i}(σ t))` (`branchEvolution`), with the released error
`2 (ε/3) + N (√(2s) ρ T / N)³` (`exists_native_select`) and the released query bound
`663552 · shape (2s) (ρ T) (log (2/ε))`, independent of `M`, `N` and `σ` (`select`).

Durations stay tables indexed by branch and sample, `0 ≤ u_i(r) ≤ T`; a branch can therefore
start, stop or pause at any sample, coherently in the branch label (coherent start times and
durations), and with `σ` the slot of the refinement of a nonuniform mesh, at any mesh point.
-/

namespace TimeDependentExtensions

namespace MeshSelect

noncomputable section

open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open CayleyClockInterface ImprovedCayleyMoments
open SparseHamiltonian.TimeDependentODE (slotAction cleanSlot cleanBasis image valid
  cayleyOracle cayleyOracle_unitary cayleyProgram cayleyProgram_intertwines cayleyProgram_count
  publicEmbedding Physical Basis oracle oracle_unitary)
open SparseHamiltonian.TimeDependentODE.Select (step degree rescaling evolution_diagonal
  step_le_quarter count_le_shape)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s M : ℕ}

/-! ### The clean encoding with slot samples `σ` -/

/-- The private cells of slot `t` carry the time address `σ t`. -/
def privateEmbedding (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (t : ℕ) :
    ODEJointNative.Private ι n →ₗᵢ[ℂ]
      NativeMaskedOracle.Logical PUnit.{1} (Basis ι n Z M) :=
  FlatMaskedAccess.singleton (cleanSlot D (σ t))

/-- The fixed logical-to-physical encoding with slot samples `σ`. -/
def embedding (D : Data (X × Fin M) n Z s) (hM : 0 < M) (σ : ℕ → Fin M) (b0 : ι × Fin M)
    (T d : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := ODEJointNative.Public ι n)
      (V := ChronologicalResolvent.BlockOperator.H T (ODEJointNative.Private ι n)) d)
      →ₗᵢ[ℂ] Physical ι n Z M T d :=
  TimeDependent.cleanInputV (C := PUnit.{1}) (publicEmbedding D ⟨0, hM⟩)
    (privateEmbedding D σ) (cleanBasis D b0) T d

/-- Every slot-dependent active layer has an exact clean implementation with the released
seventy-two coherent sampled-time queries. -/
theorem implementsOn (D : Data (X × Fin M) n Z s) (hM : 0 < M) (σ : ℕ → Fin M)
    (b0 : ι × Fin M) (k : ι → ℝ) (γ : ι → Fin M → ℝ) (ρ : ℝ) (T d r : ℕ) :
    LabeledEncodedOracle.ImplementsOn (oracle (ι := ι) D T d)
      (fun x => TimeDependent.activeClockV (P := ODEJointNative.Public ι n)
        (fun t => slotAction D k γ ρ x (σ t)) T d r)
      (embedding D hM σ b0 T d).toContinuousLinearMap 72 := by
  have h := TimeDependent.clean_implementsOnV (C := PUnit.{1}) (cayleyOracle (ι := ι) D)
    (cayleyOracle_unitary D) (cleanBasis D b0) (image D b0) (valid D b0)
    (cayleyProgram D k γ ρ) (publicEmbedding D ⟨0, hM⟩) (privateEmbedding D σ)
    (fun x t => slotAction D k γ ρ x (σ t))
    (fun x t => FlatMaskedAccess.singleton_intertwines _ _ _
      (cayleyProgram_intertwines D k γ ρ x (σ t))) T d r
  have h72 : 3 * (cayleyProgram (ι := ι) D k γ ρ).count = 72 := by simp
  rw [h72] at h
  exact h

/-! ### The SELECT on `N` slots -/

/-- The private slot action at slot `t`: the joint Cayley action of the sample `σ t`. -/
def actions (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (k : ι → ℝ) (u : ι → Fin M → ℝ)
    (ρ T γ : ℝ) (x : X) (t : ℕ) :
    ODEJointNative.Private ι n →L[ℂ] ODEJointNative.Private ι n :=
  slotAction D k (rescaling γ T u) ρ x (σ t)

/-- The clean input on `N` slots: smoothing preparation followed by the native encoding. -/
def input (D : Data (X × Fin M) n Z s) (hM : 0 < M) (σ : ℕ → Fin M) (b0 : ι × Fin M)
    (N : ℕ) (γ ρ T ε : ℝ) :
    ODEJointNative.Public ι n →L[ℂ] Physical ι n Z M N (degree (s : ℝ) γ ρ T ε N) :=
  (embedding D hM σ b0 N (degree (s : ℝ) γ ρ T ε N)).toContinuousLinearMap ∘L
    SharpClockQuery.input (P := ODEJointNative.Public ι n) (V := ODEJointNative.Private ι n)
      (step (s : ℝ) γ ρ T N) (width (2 * (s : ℝ)) γ) (moment γ) N (ε / 3)

/-- The clean output embedding on `N` slots. -/
def output (D : Data (X × Fin M) n Z s) (hM : 0 < M) (σ : ℕ → Fin M) (b0 : ι × Fin M)
    (N : ℕ) (γ ρ T ε : ℝ) :
    ODEJointNative.Public ι n →L[ℂ] Physical ι n Z M N (degree (s : ℝ) γ ρ T ε N) :=
  (embedding D hM σ b0 N (degree (s : ℝ) γ ρ T ε N)).toContinuousLinearMap ∘L
    SharpClockSimulation.output (P := ODEJointNative.Public ι n)
      (V := ODEJointNative.Private ι n)
      (step (s : ℝ) γ ρ T N) (width (2 * (s : ℝ)) γ) (moment γ) N (ε / 3)

/-- The ordered branch evolution: branch `i` uses duration `u i (σ t) / N` at slot `t`. -/
def branchEvolution (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (N : ℕ) (k : ι → ℝ)
    (u : ι → Fin M → ℝ) (x : X) (i : ι) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  TimeDependent.evolution (fun t => NormedSpace.exp
    ((-Complex.I * ((u i (σ t) / N : ℝ) : ℂ)) •
      SparseStateOverlap.matrixOperator (ODEMatrixEnergy.lchsHamiltonian
        (D.matrix (x, σ t)) (k i)))) N

/-- The SELECT target on the joint branch register. -/
def selectEvolution (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (N : ℕ) (k : ι → ℝ)
    (u : ι → Fin M → ℝ) (x : X) :
    ODEJointNative.Public ι n →L[ℂ] ODEJointNative.Public ι n :=
  WeightedClock.diagonal (fun i => branchEvolution D σ N k u x i)

variable {Label K : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [DecidableEq ι] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
set_option maxRecDepth 8192 in
/-- The coherent sampled-time ODE construction on any fixed isometric
encoding of the clock workspace whose active layers are implemented at cost
`q`. -/
theorem select_core (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) {N : ℕ} (hN : 0 < N)
    (etaH etaD R T : ℝ) (k : ι → ℝ) (u : ι → Fin M → ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hρ : 0 < etaH + R * etaD)
    (hT : 0 < T) (hk : ∀ i, |k i| ≤ R)
    (hu : ∀ i r, 0 ≤ u i r) (huT : ∀ i r, u i r ≤ T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (γ ε : ℝ) (hγ : 0 < γ) (hγOne : γ ≤ 1) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hStep : step (s : ℝ) γ (etaH + R * etaD) T N ≤ 1 / 4)
    (O : Label → X → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (E : SharpClockQuery.Space (P := ODEJointNative.Public ι n)
      (V := ODEJointNative.Private ι n)
      (step (s : ℝ) γ (etaH + R * etaD) T N) (width (2 * (s : ℝ)) γ) (moment γ) N (ε / 3)
        →L[ℂ] K)
    (hE : E† ∘L E = 1) (q : ℕ)
    (hQuery : ∀ r < 2 * SharpFilterSchedule.degree (width (2 * (s : ℝ)) γ)
        ((N : ℝ) * step (s : ℝ) γ (etaH + R * etaD) T N * moment γ) (ε / 3),
      LabeledEncodedOracle.ImplementsOn O
        (fun x => TimeDependent.activeClockV (P := ODEJointNative.Public ι n)
          (actions D σ k u (etaH + R * etaD) T γ x) N
          (SharpFilterSchedule.degree (width (2 * (s : ℝ)) γ)
            ((N : ℝ) * step (s : ℝ) γ (etaH + R * etaD) T N * moment γ) (ε / 3)) r) E q) :
    ∃ p : MultiOracleCircuit.Program O,
      p.count ≤ 6 * SharpFilterSchedule.degree (width (2 * (s : ℝ)) γ)
        ((N : ℝ) * step (s : ℝ) γ (etaH + R * etaD) T N * moment γ) (ε / 3) * q ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L (E ∘L SharpClockQuery.input (step (s : ℝ) γ (etaH + R * etaD) T N)
            (width (2 * (s : ℝ)) γ) (moment γ) N (ε / 3)) -
          (E ∘L SharpClockSimulation.output (step (s : ℝ) γ (etaH + R * etaD) T N)
            (width (2 * (s : ℝ)) γ) (moment γ) N (ε / 3)) ∘L selectEvolution D σ N k u x‖ ≤
          2 * (ε / 3) +
            N * (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / N) ^ 3 := by
  classical
  let J := ODEJointCayley.boundary (ι := ι) D
  let w := step (s : ℝ) γ (etaH + R * etaD) T N
  let slot : ℕ → Fin M := σ
  let G : X → ℕ → _ := fun x t =>
    ODEJointCayley.generator D (x, slot t) k (fun i => u i (slot t)) (etaH + R * etaD) T
  let S : X → ℕ → _ := fun x t =>
    ODEJointCayley.inverse D (x, slot t) k (fun i => u i (slot t)) (etaH + R * etaD) T γ
  have hs : 0 < s := D.slots_pos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 ≤ w := by
    have ht : 0 ≤ time (2 * (s : ℝ)) ((etaH + R * etaD) * T) γ :=
      div_nonneg (mul_nonneg (mul_nonneg hρ.le hT.le) (Real.sqrt_nonneg _)) hγ.le
    exact div_nonneg ht hNR.le
  have hJ : J† ∘L J = 1 := ODEJointCayley.boundary_isometry D
  have hMom : ∀ x t, ‖G x t‖ ≤ Real.sqrt (2 * (s : ℝ)) ∧ ‖G x t ∘L J‖ ≤ 1 := fun x t =>
    ODEJointCayley.moment_certificate D (x, slot t) etaH etaD R T k (fun i => u i (slot t))
      hH hDiss hρ hT hk (fun i => hu i _) (fun i => huT i _)
      (hrH _) (hcH _) (hrD _) (hcD _)
  have hSelf : ∀ x t, star (G x t) = G x t := fun x t =>
    ODEJointCayley.generator_adjoint D (x, slot t) k (fun i => u i (slot t)) (etaH + R * etaD) T
  have hAct : ∀ x t, actions D σ k u (etaH + R * etaD) T γ x t =
      cayleyAction (scaled (G x t) γ) (S x t) :=
    fun x t => ODEJointCayley.action_eq_cayley D (x, slot t) k (fun i => u i (slot t))
      (etaH + R * etaD) T γ
  have hD : ∀ x t, (actions D σ k u (etaH + R * etaD) T γ x t)† ∘L
      actions D σ k u (etaH + R * etaD) T γ x t = 1 :=
    fun x t => (ODEJointCayley.action_unitary D (x, slot t) k (fun i => u i (slot t))
      (etaH + R * etaD) T γ).1
  have hRight : ∀ x t, (1 - actions D σ k u (etaH + R * etaD) T γ x t) ∘L
      resolventAtOne (scaled (G x t) γ) = 1 := by
    intro x t
    change (1 - actions D σ k u (etaH + R * etaD) T γ x t) * resolventAtOne (scaled (G x t) γ) = 1
    rw [hAct]
    exact one_sub_cayleyAction_mul_resolventAtOne
      (A := ODEJointNative.Private ι n →L[ℂ] ODEJointNative.Private ι n)
      (scaled (G x t) γ) (S x t)
      (ODEJointCayley.inverse_right D (x, slot t) k (fun i => u i (slot t)) (etaH + R * etaD) T γ)
      (ODEJointCayley.inverse_left D (x, slot t) k (fun i => u i (slot t)) (etaH + R * etaD) T γ)
  have hLeft : ∀ x t, resolventAtOne (scaled (G x t) γ) ∘L
      (1 - actions D σ k u (etaH + R * etaD) T γ x t) = 1 := by
    intro x t
    change resolventAtOne (scaled (G x t) γ) * (1 - actions D σ k u (etaH + R * etaD) T γ x t) = 1
    rw [hAct]
    exact resolventAtOne_mul_one_sub_cayleyAction
      (A := ODEJointNative.Private ι n →L[ℂ] ODEJointNative.Private ι n)
      (scaled (G x t) γ) (S x t)
      (ODEJointCayley.inverse_right D (x, slot t) k (fun i => u i (slot t)) (etaH + R * etaD) T γ)
  obtain ⟨p, hCount, hEval⟩ := TimeDependent.implementationV_query_certificate
    (fun x => actions D σ k u (etaH + R * etaD) T γ x) J w (width (2 * (s : ℝ)) γ) (moment γ) N
    (ε / 3)
    (width_ge_one _ _) hw hStep hD hJ O hO E hE q hQuery
  have hOutIso := SharpClockSimulation.output_isometry (P := ODEJointNative.Public ι n)
    (V := ODEJointNative.Private ι n) w (width (2 * (s : ℝ)) γ) (moment γ) N (ε / 3)
    (width_ge_one _ _)
  refine ⟨p, hCount, fun x => ⟨p.eval_unitary hO x, ?_⟩⟩
  obtain ⟨U, Rs, hRRight, _hRLeft, hCayley, _hIso, hImpl, _hDeg⟩ :=
    TimeDependent.exists_precise_implementationV (actions D σ k u (etaH + R * etaD) T γ x)
      (fun t => resolventAtOne (scaled (G x t) γ)) J
      (fun t => compressed (G x t) J γ) w (width (2 * (s : ℝ)) γ) (endpoint γ) (moment γ) N
      (width_ge_one _ _) hw hStep (hD x) hJ (hRight x) (hLeft x)
      (fun t => resolvent_norm (G x t) (2 * (s : ℝ)) γ hγ.le (hMom x t).1)
      (fun t => resolventAtOne_compression (scaled (G x t) γ) J hJ)
      (fun t => compressed_self_adjoint (G x t) J γ (hSelf x t))
      (fun t => (compressed_norm (G x t) J γ hγ.le hJ (hMom x t).2).trans hγOne)
      (fun t => endpoint_norm (G x t) J γ (hSelf x t) hJ hγ.le (hMom x t).2)
      (endpoint_sq γ).le (moment_le_width (2 * (s : ℝ)) γ hγ.le hγOne) (ε / 3)
      (by positivity) (by linarith)
  -- Each Cayley step is within `(√(2s) (etaH + R * etaD) T / N)^3` of the sampled exponential.
  let Xs : ℕ → ODEJointNative.Public ι n →L[ℂ] ODEJointNative.Public ι n := fun t =>
    (-Complex.I * (w : ℂ)) • compressed (G x t) J γ
  have hXdiag : ∀ t, Xs t = WeightedClock.diagonal (fun i =>
      (-Complex.I * ((u i (slot t) / N : ℝ) : ℂ)) •
        SparseStateOverlap.matrixOperator
          (ODEMatrixEnergy.lchsHamiltonian (D.matrix (x, slot t)) (k i))) := by
    intro t
    have h := ODEJointCayley.physical_exponent D (x, slot t) k (fun i => u i (slot t))
      (etaH + R * etaD) T γ hρ.ne' hT hγ.ne'
    have hsplit : (-Complex.I * (w : ℂ)) =
        ((N : ℂ)⁻¹) * (-Complex.I * (time (2 * (s : ℝ)) ((etaH + R * etaD) * T) γ : ℂ)) := by
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
  have hwγ : w * γ = Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / N := by
    simp only [w, step, time]
    field_simp
  have hXnorm : ∀ t, ‖Xs t‖ ≤ Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / N := by
    intro t
    have hHk := compressed_norm (G x t) J γ hγ.le hJ (hMom x t).2
    calc
      ‖Xs t‖ = w * ‖compressed (G x t) J γ‖ := by
        change ‖(-Complex.I * (w : ℂ)) • compressed (G x t) J γ‖ = _
        rw [norm_smul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_of_nonneg hw]
      _ ≤ w * γ := mul_le_mul_of_nonneg_left hHk hw
      _ = Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / N := hwγ
  have hXone : ∀ t, ‖Xs t‖ ≤ 1 := by
    intro t
    have hle : Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / N ≤ w := by
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
      (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / N) ^ 3 := by
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
  have hProd : ‖TimeDependent.evolution U N - selectEvolution D σ N k u x‖ ≤
      N * (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / N) ^ 3 := by
    have hEq : selectEvolution D σ N k u x =
        TimeDependent.evolution (fun t => NormedSpace.exp (Xs t)) N := by
      have hExp : ∀ t, NormedSpace.exp (Xs t) = WeightedClock.diagonal (fun i =>
          NormedSpace.exp ((-Complex.I * ((u i (slot t) / N : ℝ) : ℂ)) •
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
    exact TimeDependent.evolution_sub_norm_le_mul U _ hUnorm hExpNorm hStepErr N
  have hOutNorm : ‖SharpClockSimulation.output (P := ODEJointNative.Public ι n)
      (V := ODEJointNative.Private ι n) w (width (2 * (s : ℝ)) γ) (moment γ) N (ε / 3)‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro v
    have h := ((SharpClockSimulation.output (P := ODEJointNative.Public ι n)
      (V := ODEJointNative.Private ι n) w (width (2 * (s : ℝ)) γ) (moment γ) N
        (ε / 3)).norm_map_iff_adjoint_comp_self.mpr hOutIso) v
    rw [h, one_mul]
  have hMain : ‖p.eval x ∘L (E ∘L SharpClockQuery.input w (width (2 * (s : ℝ)) γ)
        (moment γ) N (ε / 3)) -
      (E ∘L SharpClockSimulation.output w (width (2 * (s : ℝ)) γ) (moment γ) N (ε / 3)) ∘L
        TimeDependent.evolution U N‖ ≤ 2 * (ε / 3) := by
    rw [hEval x, comp_assoc, ← comp_sub, EncodedOracle.norm_comp_eq E hE]
    exact hImpl
  calc
    _ ≤ ‖p.eval x ∘L (E ∘L SharpClockQuery.input w (width (2 * (s : ℝ)) γ) (moment γ) N
            (ε / 3)) -
          (E ∘L SharpClockSimulation.output w (width (2 * (s : ℝ)) γ) (moment γ) N (ε / 3)) ∘L
            TimeDependent.evolution U N‖ +
        ‖(E ∘L SharpClockSimulation.output w (width (2 * (s : ℝ)) γ) (moment γ) N (ε / 3)) ∘L
            TimeDependent.evolution U N -
          (E ∘L SharpClockSimulation.output w (width (2 * (s : ℝ)) γ) (moment γ) N (ε / 3)) ∘L
            selectEvolution D σ N k u x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * (ε / 3) + N * (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / N) ^ 3 := by
      apply add_le_add hMain
      rw [← comp_sub, comp_assoc, EncodedOracle.norm_comp_eq E hE]
      calc
        _ ≤ ‖SharpClockSimulation.output (P := ODEJointNative.Public ι n)
            (V := ODEJointNative.Private ι n) w (width (2 * (s : ℝ)) γ) (moment γ) N (ε / 3)‖ *
            ‖TimeDependent.evolution U N - selectEvolution D σ N k u x‖ := opNorm_comp_le _ _
        _ ≤ 1 * (N * (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / N) ^ 3) :=
          mul_le_mul hOutNorm hProd (norm_nonneg _) zero_le_one
        _ = N * (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / N) ^ 3 := one_mul _

set_option maxRecDepth 8192 in
/-- The native coherent sampled-time ODE program on `N` slots with slot samples `σ`. -/
theorem exists_native_select (D : Data (X × Fin M) n Z s) (hM : 0 < M) (σ : ℕ → Fin M)
    {N : ℕ} (hN : 0 < N) (b0 : ι × Fin M)
    (etaH etaD R T : ℝ) (k : ι → ℝ) (u : ι → Fin M → ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hρ : 0 < etaH + R * etaD)
    (hT : 0 < T) (hk : ∀ i, |k i| ≤ R)
    (hu : ∀ i r, 0 ≤ u i r) (huT : ∀ i r, u i r ≤ T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (γ ε : ℝ) (hγ : 0 < γ) (hγOne : γ ≤ 1) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hStep : step (s : ℝ) γ (etaH + R * etaD) T N ≤ 1 / 4) :
    ∃ p : MultiOracleCircuit.Program
        (oracle (ι := ι) D N (degree (s : ℝ) γ (etaH + R * etaD) T ε N)),
      p.count ≤ 6 * degree (s : ℝ) γ (etaH + R * etaD) T ε N * 72 ∧
      (input D hM σ b0 N γ (etaH + R * etaD) T ε)† ∘L
        input D hM σ b0 N γ (etaH + R * etaD) T ε = 1 ∧
      (output D hM σ b0 N γ (etaH + R * etaD) T ε)† ∘L
        output D hM σ b0 N γ (etaH + R * etaD) T ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L input D hM σ b0 N γ (etaH + R * etaD) T ε -
          output D hM σ b0 N γ (etaH + R * etaD) T ε ∘L selectEvolution D σ N k u x‖ ≤
          2 * (ε / 3) + N * (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / N) ^ 3 := by
  let O := oracle (ι := ι) D N (degree (s : ℝ) γ (etaH + R * etaD) T ε N)
  have hO : ∀ l x, IsUnitary (O l x) := oracle_unitary D N _
  let E : SharpClockQuery.Space (P := ODEJointNative.Public ι n)
      (V := ODEJointNative.Private ι n)
      (step (s : ℝ) γ (etaH + R * etaD) T N) (width (2 * (s : ℝ)) γ) (moment γ) N (ε / 3)
        →L[ℂ] Physical ι n Z M N (degree (s : ℝ) γ (etaH + R * etaD) T ε N) :=
    (embedding D hM σ b0 N (degree (s : ℝ) γ (etaH + R * etaD) T ε N)).toContinuousLinearMap
  have hE : E† ∘L E = 1 :=
    (embedding D hM σ b0 N (degree (s : ℝ) γ (etaH + R * etaD) T ε N)).adjoint_comp_self
  have hQ : ∀ r < 2 * SharpFilterSchedule.degree (width (2 * (s : ℝ)) γ)
        ((N : ℝ) * step (s : ℝ) γ (etaH + R * etaD) T N * moment γ) (ε / 3),
      LabeledEncodedOracle.ImplementsOn O
        (fun x => TimeDependent.activeClockV (P := ODEJointNative.Public ι n)
          (actions D σ k u (etaH + R * etaD) T γ x) N
          (SharpFilterSchedule.degree (width (2 * (s : ℝ)) γ)
            ((N : ℝ) * step (s : ℝ) γ (etaH + R * etaD) T N * moment γ) (ε / 3)) r) E 72 :=
    fun r _ => implementsOn D hM σ b0 k (rescaling γ T u) (etaH + R * etaD) N _ r
  have hCore := select_core D σ hN etaH etaD R T k u hH hDiss hρ hT hk hu huT
    hrH hcH hrD hcD γ ε hγ hγOne hε hεOne hStep O hO E hE 72
  obtain ⟨p, hCount, hAction⟩ := hCore hQ
  have hInIso := SharpClockQuery.input_isometry (P := ODEJointNative.Public ι n)
    (V := ODEJointNative.Private ι n) (step (s : ℝ) γ (etaH + R * etaD) T N)
    (width (2 * (s : ℝ)) γ) (moment γ) N (ε / 3) (width_ge_one _ _)
  have hOutIso := SharpClockSimulation.output_isometry (P := ODEJointNative.Public ι n)
    (V := ODEJointNative.Private ι n) (step (s : ℝ) γ (etaH + R * etaD) T N)
    (width (2 * (s : ℝ)) γ) (moment γ) N (ε / 3) (width_ge_one _ _)
  exact ⟨p, hCount, NativeSparseAttenuation.isometry_comp _ _ hInIso hE,
    NativeSparseAttenuation.isometry_comp _ _ hOutIso hE, hAction⟩

/-- The complete workspace on `N` slots, including the alignment spectator. -/
abbrev Workspace (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z] (s M N : ℕ)
    (γ ρ T ε : ℝ) :=
  CleanOutputAlignment.Double (Physical ι n Z M N (degree (s : ℝ) γ ρ T ε N))

/-- Each query is one coherent sampled-time native primitive, with untouched spectator
registers. -/
abbrev alignedOracle (D : Data (X × Fin M) n Z s) (N : ℕ) (γ ρ T ε : ℝ) :
    Query → X → Workspace ι n Z s M N γ ρ T ε →L[ℂ] Workspace ι n Z s M N γ ρ T ε :=
  AlignedMultiOracleProgram.oracle (oracle (ι := ι) D N (degree (s : ℝ) γ ρ T ε N))

omit [DecidableEq ι] [DecidableEq Z] in
theorem alignedOracle_unitary (D : Data (X × Fin M) n Z s) (N : ℕ) (γ ρ T ε : ℝ) (l : Query)
    (x : X) : IsUnitary (alignedOracle (ι := ι) D N γ ρ T ε l x) :=
  CoherentQuerySchedule.oracle_unitary _ (oracle_unitary D N _) l x

/-- The same known clean preparation at both ends of the SELECT circuit. -/
def alignedInput (D : Data (X × Fin M) n Z s) (hM : 0 < M) (σ : ℕ → Fin M) (b0 : ι × Fin M)
    (N : ℕ) (γ ρ T ε : ℝ) : ODEJointNative.Public ι n →L[ℂ] Workspace ι n Z s M N γ ρ T ε :=
  AlignedMultiOracleProgram.input (input D hM σ b0 N γ ρ T ε)

set_option maxRecDepth 8192 in
/-- **Coherent sampled-time ODE SELECT on `N` slots with slot samples `σ`.** One public
rescaling and one clean encoding serve every table of branch nodes `|k i| ≤ R` and durations
`0 ≤ u i r ≤ T`. The full output is within `ε` of the ordered branch products, uniformly over
the unknown instance, with at most `663552 * shape (2 s) (ρ T) (log (2/ε))` queries, under
the slot conditions `8 s ρ T ≤ N` and `3 (√(2s) ρ T)³ ≤ ε N²`. -/
theorem select (D : Data (X × Fin M) n Z s) (hM : 0 < M) (σ : ℕ → Fin M) {N : ℕ}
    (hN : 0 < N) (b0 : ι × Fin M)
    (etaH etaD R T ε : ℝ) (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD)
    (hρ : 0 < etaH + R * etaD) (hT : 0 < T) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hClock : 8 * s * ((etaH + R * etaD) * T) ≤ N)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T)) ^ 3 ≤
      ε * (N : ℝ) ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (2 * (s : ℝ)) ∧
      ∀ (k : ι → ℝ) (u : ι → Fin M → ℝ), (∀ i, |k i| ≤ R) →
        (∀ i r, 0 ≤ u i r) → (∀ i r, u i r ≤ T) →
        ∃ p : MultiOracleCircuit.Program
            (alignedOracle (ι := ι) D N γ (etaH + R * etaD) T ε),
          (p.count : ℝ) ≤ 663552 * ImprovedPrecisionBudget.shape (2 * (s : ℝ))
            ((etaH + R * etaD) * T) (ImprovedPrecisionBudget.targetLog ε) ∧
          (alignedInput D hM σ b0 N γ (etaH + R * etaD) T ε)† ∘L
            alignedInput D hM σ b0 N γ (etaH + R * etaD) T ε = 1 ∧
          ∀ x, IsUnitary (p.eval x) ∧
            ‖p.eval x ∘L alignedInput D hM σ b0 N γ (etaH + R * etaD) T ε -
              alignedInput D hM σ b0 N γ (etaH + R * etaD) T ε ∘L
                selectEvolution D σ N k u x‖ ≤ ε := by
  have hs : (1 : ℝ) ≤ s := by exact_mod_cast D.slots_pos
  have hsTwo : (1 : ℝ) ≤ 2 * (s : ℝ) := by linarith
  have hρT : 0 ≤ (etaH + R * etaD) * T := mul_nonneg hρ.le hT.le
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨γ, hγ, hγOne, hWidth, hBudget⟩ :=
    ImprovedPrecisionBudget.exists_rescaling_for_precision (2 * (s : ℝ))
      ((etaH + R * etaD) * T) ε hsTwo hρT hε hεOne
  have hStep := step_le_quarter (s := s) (M := N) γ (etaH + R * etaD) T hs hγ hWidth hρT hN
    hClock
  refine ⟨γ, hγ, hγOne, hWidth, ?_⟩
  intro k u hk hu huT
  obtain ⟨p, hCount, hIn, hOut, hAct⟩ := exists_native_select D hM σ hN b0 etaH etaD R T k u
    hH hDiss hρ hT hk hu huT hrH hcH hrD hcD γ ε hγ hγOne hε hεOne hStep
  let q := AlignedMultiOracleProgram.program _ _ hIn hOut p
  refine ⟨q, ?_, AlignedMultiOracleProgram.input_isometry _ hIn, fun x => ⟨?_, ?_⟩⟩
  · have hqc : q.count = p.count := AlignedMultiOracleProgram.program_count _ _ hIn hOut p
    calc
      (q.count : ℝ) = (p.count : ℝ) := by exact_mod_cast hqc
      _ ≤ _ := count_le_shape (M := N) γ (etaH + R * etaD) T ε hγ hρT hε hεOne hN hBudget
        p.count hCount
  · exact q.eval_unitary (CoherentQuerySchedule.oracle_unitary _ (oracle_unitary D N _)) x
  · have hAligned := AlignedMultiOracleProgram.program_error _ _ hIn hOut p x
      (selectEvolution D σ N k u x)
    change ‖q.eval x ∘L alignedInput D hM σ b0 N γ (etaH + R * etaD) T ε -
      alignedInput D hM σ b0 N γ (etaH + R * etaD) T ε ∘L selectEvolution D σ N k u x‖ ≤ ε
    rw [show alignedInput D hM σ b0 N γ (etaH + R * etaD) T ε =
      AlignedMultiOracleProgram.input (input D hM σ b0 N γ (etaH + R * etaD) T ε) from rfl,
      hAligned]
    have hCay : (N : ℝ) * (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / N) ^ 3 ≤
        ε / 3 := by
      have hNsq : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
      have heq : (N : ℝ) * (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / N) ^ 3 =
          (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T)) ^ 3 / (N : ℝ) ^ 2 := by
        field_simp
      rw [heq, div_le_iff₀ hNsq]
      linarith
    linarith [(hAct x).2]

end

end MeshSelect

end TimeDependentExtensions
