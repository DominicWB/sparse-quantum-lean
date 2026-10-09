import TimeDependentHamiltonian.Native.Simulation

set_option autoImplicit false

/-!
# The sampled native simulation with an arbitrary slot-to-sample map

The released native layer (`SparseHamiltonian.TimeDependent.Sampled`) runs the chronological
clock with `T` slots and a coherent sampled-time oracle with `M` samples, and lets slot `k`
use the sample `k mod M`: the clean encoding writes `|k mod M⟩` into the time register of
every private cell of slot `k` (`Sampled.privateEmbedding`). Nothing else depends on this
choice. Here slot `k` uses an arbitrary public sample `σ k` (`privateEmbedding`, `embedding`):
the queries, the program and its count are those of the released layer, the private Cayley
action of slot `k` is that of the sample `σ k` (`implementsOn`, still `54` coherent
sampled-time queries per active layer), and the complete construction approximates the
ordered product of the slot exponentials `exp(-i (τ/N) Ĥ_{σ k})` on `N` slots
(`exists_sampled_simulation`) with the released error `2 (ε/3) + N (√s τ / N)³` and count
`6 · 54 · d`, independently of `N`, `M` and `σ`.

The manuscript uses such a "known map from each new time label to its original sample label"
in the proof of `hs:cor:hybrid`; here it is realised in the fixed clean encoding.
-/

namespace TimeDependentExtensions

namespace Refined

noncomputable section

open SparseHamiltonian SparseHamiltonian.TimeDependent ContinuousLinearMap OracleCircuit
open NativeSparseBlockEncoding CayleyClockInterface ImprovedCayleyMoments
open FixedNativeCayleySimulation
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- The private Cayley action of slot `k`: that of the sample `σ k`. -/
def actions (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (γ : ℝ) (x : X) (k : ℕ) :
    SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n :=
  FixedNativeCayleySimulation.action D (x, σ k) γ

/-- The private cells of slot `k` carry the time register `|σ k⟩`. -/
def privateEmbedding (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (k : ℕ) :
    SparseEdgeMoments.OrientedSpace n →ₗᵢ[ℂ]
      NativeMaskedOracle.Logical PUnit.{1} (Fin M × NativeCayleyProgram.Basis n Z) :=
  FlatMaskedAccess.singleton (sampledClean D (σ k))

/-- The fixed logical-to-physical encoding with slot samples `σ`. -/
def embedding (D : Data (X × Fin M) n Z s) (hM : 0 < M) (σ : ℕ → Fin M) (T d : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := EuclideanSpace ℂ n)
      (V := ChronologicalResolvent.BlockOperator.H T (SparseEdgeMoments.OrientedSpace n)) d)
      →ₗᵢ[ℂ] Sampled.Physical n Z M T d :=
  cleanInputV (Sampled.publicEmbedding D hM) (privateEmbedding D σ)
    (sampledBasis D ⟨0, hM⟩) T d

/-- Each slot-dependent active layer has an exact clean implementation with the released
fifty-four coherent sampled-time queries. -/
theorem implementsOn (D : Data (X × Fin M) n Z s) (hM : 0 < M) (σ : ℕ → Fin M) (γ : ℝ)
    (T d r : ℕ) :
    LabeledEncodedOracle.ImplementsOn (Sampled.oracle D T d)
      (fun x => activeClockV (P := EuclideanSpace ℂ n) (actions D σ γ x) T d r)
      (embedding D hM σ T d).toContinuousLinearMap 54 := by
  have h := clean_implementsOnV (C := PUnit.{1}) (sampledOracle D)
    (fun l x => sampledOracle_unitary D l x) (sampledBasis D ⟨0, hM⟩)
    (fun l x => ((⟨0, hM⟩ : Fin M), NativeCayleyProgram.image D l (x, ⟨0, hM⟩)))
    (fun l x => sampledOracle_valid D ⟨0, hM⟩ l x) (sampledProgram D γ)
    (Sampled.publicEmbedding D hM) (privateEmbedding D σ) (actions D σ γ)
    (fun x t => FlatMaskedAccess.singleton_intertwines _ _ _
      (sampledProgram_intertwines D γ x (σ t))) T d r
  have h54 : 3 * (sampledProgram D γ).count = 54 := by simp
  rw [h54] at h
  exact h

/-- The fixed clean input on `N` slots. -/
def input (D : Data (X × Fin M) n Z s) (hM : 0 < M) (σ : ℕ → Fin M) (N : ℕ) (γ τ ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] Sampled.Physical n Z M N (Sampled.degree (s : ℝ) γ τ ε N) :=
  (embedding D hM σ N (Sampled.degree (s : ℝ) γ τ ε N)).toContinuousLinearMap ∘L
    SharpClockQuery.input (P := EuclideanSpace ℂ n) (V := SparseEdgeMoments.OrientedSpace n)
      (Sampled.step (s : ℝ) γ τ N) (width (s : ℝ) γ) (moment γ) N (ε / 3)

/-- The fixed clean output on `N` slots. -/
def output (D : Data (X × Fin M) n Z s) (hM : 0 < M) (σ : ℕ → Fin M) (N : ℕ) (γ τ ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] Sampled.Physical n Z M N (Sampled.degree (s : ℝ) γ τ ε N) :=
  (embedding D hM σ N (Sampled.degree (s : ℝ) γ τ ε N)).toContinuousLinearMap ∘L
    SharpClockSimulation.output (P := EuclideanSpace ℂ n)
      (V := SparseEdgeMoments.OrientedSpace n)
      (Sampled.step (s : ℝ) γ τ N) (width (s : ℝ) γ) (moment γ) N (ε / 3)

/-- The ordered product of the slot exponentials `exp(-i (τ/N) Ĥ_{σ k})`. -/
def sampledEvolution (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (N : ℕ) (τ : ℝ) (x : X) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  evolution (fun k => NormedSpace.exp ((-Complex.I * ((τ / N : ℝ) : ℂ)) •
    SparseStateOverlap.matrixOperator (D.matrix (x, σ k)))) N

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- One rescaled Cayley step on `N` slots is the sample Hamiltonian times `τ / N`. -/
theorem step_smul_compressed (D : Data (X × Fin M) n Z s) (y : X × Fin M)
    (hH : (D.matrix y).IsHermitian) (γ τ : ℝ) (N : ℕ) (hγ : γ ≠ 0) (hs : 0 < s) :
    ((Sampled.step (s : ℝ) γ τ N : ℝ) : ℂ) • compressed (generator D y) (boundary D) γ =
      ((τ / N : ℝ) : ℂ) • SparseStateOverlap.matrixOperator (D.matrix y) := by
  have hcomp : compressed (generator D y) (boundary D) γ =
      (γ : ℂ) • ((boundary D)† ∘L generator D y ∘L boundary D) := by
    simp only [compressed, scaled, smul_comp, comp_smul]
  rw [hcomp, compression D y hH, smul_smul, smul_smul]
  congr 1
  have hsR : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.mpr (by exact_mod_cast hs)
  have hγC : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  have hsC : ((Real.sqrt s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsR.ne'
  simp only [Sampled.step, time, Complex.ofReal_div, Complex.ofReal_mul]
  field_simp

variable {Label K : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
set_option maxRecDepth 8192 in
/-- The coherent sampled-time construction with slot samples `σ`, on any fixed isometric
encoding of the clock workspace whose active layers are implemented at cost `q`. -/
theorem sampled_core (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) {N : ℕ} (hN : 0 < N)
    (hH : ∀ y, (D.matrix y).IsHermitian)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ 1)
    (hcol : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ 1)
    (γ τ ε : ℝ) (hγ : 0 < γ) (hγOne : γ ≤ 1) (hτ : 0 ≤ τ) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hStep : Sampled.step (s : ℝ) γ τ N ≤ 1 / 4)
    (O : Label → X → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (E : SharpClockQuery.Space (P := EuclideanSpace ℂ n) (V := SparseEdgeMoments.OrientedSpace n)
      (Sampled.step (s : ℝ) γ τ N) (width (s : ℝ) γ) (moment γ) N (ε / 3) →L[ℂ] K)
    (hE : E† ∘L E = 1) (q : ℕ)
    (hQuery : ∀ r < 2 * SharpFilterSchedule.degree (width (s : ℝ) γ)
        ((N : ℝ) * Sampled.step (s : ℝ) γ τ N * moment γ) (ε / 3),
      LabeledEncodedOracle.ImplementsOn O
        (fun x => activeClockV (P := EuclideanSpace ℂ n) (actions D σ γ x) N
          (SharpFilterSchedule.degree (width (s : ℝ) γ)
            ((N : ℝ) * Sampled.step (s : ℝ) γ τ N * moment γ) (ε / 3)) r) E q) :
    ∃ p : MultiOracleCircuit.Program O,
      p.count ≤ 6 * SharpFilterSchedule.degree (width (s : ℝ) γ)
        ((N : ℝ) * Sampled.step (s : ℝ) γ τ N * moment γ) (ε / 3) * q ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L (E ∘L SharpClockQuery.input (Sampled.step (s : ℝ) γ τ N)
            (width (s : ℝ) γ) (moment γ) N (ε / 3)) -
          (E ∘L SharpClockSimulation.output (Sampled.step (s : ℝ) γ τ N) (width (s : ℝ) γ)
            (moment γ) N (ε / 3)) ∘L sampledEvolution D σ N τ x‖ ≤
          2 * (ε / 3) + N * (Real.sqrt s * τ / N) ^ 3 := by
  classical
  let J := boundary D
  let w := Sampled.step (s : ℝ) γ τ N
  let K : X → ℕ → _ := fun x k => generator D (x, σ k)
  let S : X → ℕ → _ := fun x k => inverse D (x, σ k) γ
  have hs : 0 < s := D.slots_pos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 ≤ w := by
    have ht : 0 ≤ time (s : ℝ) τ γ := div_nonneg (mul_nonneg hτ (Real.sqrt_nonneg _)) hγ.le
    exact div_nonneg ht hNR.le
  have hJ : J† ∘L J = 1 := boundary_isometry D
  have hSelf : ∀ x k, star (K x k) = K x k := fun x k => generator_self_adjoint D _
  have hKJ : ∀ x k, ‖K x k ∘L J‖ ≤ 1 := fun x k =>
    generator_boundary_norm_le D _ (hrow _) (hcol _)
  have hAct : ∀ x k, actions D σ γ x k = cayleyAction (scaled (K x k) γ) (S x k) :=
    fun x k => action_eq_cayley D _ γ
  have hD : ∀ x k, (actions D σ γ x k)† ∘L actions D σ γ x k = 1 := by
    intro x k
    change star (actions D σ γ x k) * actions D σ γ x k = 1
    rw [hAct]
    exact cayleyAction_star_mul_self
      (A := SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n)
      (scaled (K x k) γ) (S x k) (scaled_self_adjoint (K x k) γ (hSelf x k))
      (inverse_right D _ γ)
  have hRight : ∀ x k, (1 - actions D σ γ x k) ∘L resolventAtOne (scaled (K x k) γ) = 1 := by
    intro x k
    change (1 - actions D σ γ x k) * resolventAtOne (scaled (K x k) γ) = 1
    rw [hAct]
    exact one_sub_cayleyAction_mul_resolventAtOne
      (A := SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n)
      (scaled (K x k) γ) (S x k) (inverse_right D _ γ) (inverse_left D _ γ)
  have hLeft : ∀ x k, resolventAtOne (scaled (K x k) γ) ∘L (1 - actions D σ γ x k) = 1 := by
    intro x k
    change resolventAtOne (scaled (K x k) γ) * (1 - actions D σ γ x k) = 1
    rw [hAct]
    exact resolventAtOne_mul_one_sub_cayleyAction
      (A := SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n)
      (scaled (K x k) γ) (S x k) (inverse_right D _ γ)
  obtain ⟨p, hCount, hEval⟩ := implementationV_query_certificate
    (fun x => actions D σ γ x) J w (width (s : ℝ) γ) (moment γ) N (ε / 3)
    (width_ge_one _ _) hw hStep hD hJ O hO E hE q hQuery
  have hOutIso := SharpClockSimulation.output_isometry (P := EuclideanSpace ℂ n)
    (V := SparseEdgeMoments.OrientedSpace n) w (width (s : ℝ) γ) (moment γ) N (ε / 3)
    (width_ge_one _ _)
  refine ⟨p, hCount, fun x => ⟨p.eval_unitary hO x, ?_⟩⟩
  obtain ⟨U, R, hRRight, _hRLeft, hCayley, _hIso, hImpl, _hDeg⟩ :=
    exists_precise_implementationV (actions D σ γ x)
      (fun k => resolventAtOne (scaled (K x k) γ)) J
      (fun k => compressed (K x k) J γ) w (width (s : ℝ) γ) (endpoint γ) (moment γ) N
      (width_ge_one _ _) hw hStep (hD x) hJ (hRight x) (hLeft x)
      (fun k => resolvent_norm (K x k) (s : ℝ) γ hγ.le (generator_norm_le D _ (hrow _)))
      (fun k => resolventAtOne_compression (scaled (K x k) γ) J hJ)
      (fun k => compressed_self_adjoint (K x k) J γ (hSelf x k))
      (fun k => (compressed_norm (K x k) J γ hγ.le hJ (hKJ x k)).trans hγOne)
      (fun k => endpoint_norm (K x k) J γ (hSelf x k) hJ hγ.le (hKJ x k))
      (endpoint_sq γ).le (moment_le_width (s : ℝ) γ hγ.le hγOne) (ε / 3)
      (by positivity) (by linarith)
  -- Each Cayley step is within `(√s τ / N)^3` of the sampled exponential.
  let A : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun k =>
    SparseStateOverlap.matrixOperator (D.matrix (x, σ k))
  let Xs : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun k =>
    (-Complex.I * (w : ℂ)) • compressed (K x k) J γ
  have hXA : ∀ k, Xs k = (-Complex.I * ((τ / N : ℝ) : ℂ)) • A k := by
    intro k
    have h := step_smul_compressed D (x, σ k) (hH _) γ τ N hγ.ne' hs
    change (-Complex.I * (w : ℂ)) • compressed (K x k) J γ = _
    rw [mul_smul, h, ← mul_smul]
  have hSkew : ∀ k, star (Xs k) = -Xs k := by
    intro k
    change star ((-Complex.I * (w : ℂ)) • compressed (K x k) J γ) =
      -((-Complex.I * (w : ℂ)) • compressed (K x k) J γ)
    rw [star_smul, compressed_self_adjoint (K x k) J γ (hSelf x k)]
    rw [← neg_smul]
    congr 1
    simp [Complex.conj_ofReal]
  have hwγ : w * γ = Real.sqrt s * τ / N := by
    simp only [w, Sampled.step, time]
    field_simp
  have hXnorm : ∀ k, ‖Xs k‖ ≤ Real.sqrt s * τ / N := by
    intro k
    have hHk := (compressed_norm (K x k) J γ hγ.le hJ (hKJ x k))
    calc
      ‖Xs k‖ = w * ‖compressed (K x k) J γ‖ := by
        change ‖(-Complex.I * (w : ℂ)) • compressed (K x k) J γ‖ = _
        rw [norm_smul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_of_nonneg hw]
      _ ≤ w * γ := mul_le_mul_of_nonneg_left hHk hw
      _ = Real.sqrt s * τ / N := hwγ
  have hXone : ∀ k, ‖Xs k‖ ≤ 1 := by
    intro k
    have hle : Real.sqrt s * τ / N ≤ w := by
      rw [← hwγ]
      exact mul_le_of_le_one_right hw hγOne
    linarith [hXnorm k]
  have hnum : ∀ k, CayleyTransfer.cayleyNumerator w (compressed (K x k) J γ) =
      1 + (1 / 2 : ℂ) • Xs k := by
    intro k
    simp only [CayleyTransfer.cayleyNumerator, Xs, smul_smul]
    rw [sub_eq_add_neg, ← neg_smul]
    congr 2
    ring
  have hden : ∀ k, CayleyTransfer.cayleyDenominator w (compressed (K x k) J γ) =
      1 - (1 / 2 : ℂ) • Xs k := by
    intro k
    simp only [CayleyTransfer.cayleyDenominator, Xs, smul_smul]
    rw [sub_eq_add_neg, ← neg_smul]
    congr 2
    ring
  have hUform : ∀ k, U k = (1 + (1 / 2 : ℂ) • Xs k) * R k := by
    intro k
    rw [hCayley k, hnum k]
    rfl
  have hRform : ∀ k, (1 - (1 / 2 : ℂ) • Xs k) * R k = 1 := by
    intro k
    rw [← hden k]
    exact hRRight k
  have hStepErr : ∀ k, ‖U k - NormedSpace.exp (Xs k)‖ ≤ (Real.sqrt s * τ / N) ^ 3 := by
    intro k
    have h := CayleyApproximation.cayley_power_exp_error_of_inverse (Xs k) (R k)
      (hXone k) (hSkew k) (hRform k) 1
    rw [pow_one, one_smul, Nat.cast_one, one_mul, ← hUform k] at h
    exact h.trans (pow_le_pow_left₀ (norm_nonneg _) (hXnorm k) 3)
  have hUnorm : ∀ k, ‖U k‖ ≤ 1 := by
    intro k
    rw [hUform k]
    exact CayleyTransfer.skew_cayley_norm_le_one (Xs k) (R k) (hSkew k) (hRform k)
  have hExpNorm : ∀ k, ‖NormedSpace.exp (Xs k)‖ ≤ 1 := fun k =>
    CayleyApproximation.skew_exp_norm_le (Xs k) (hSkew k)
  have hProd : ‖evolution U N - sampledEvolution D σ N τ x‖ ≤
      N * (Real.sqrt s * τ / N) ^ 3 := by
    have hEq : sampledEvolution D σ N τ x = evolution (fun k => NormedSpace.exp (Xs k)) N := by
      simp only [sampledEvolution, hXA, A]
    rw [hEq]
    exact evolution_sub_norm_le_mul U _ hUnorm hExpNorm hStepErr N
  have hOutNorm : ‖SharpClockSimulation.output (P := EuclideanSpace ℂ n)
      (V := SparseEdgeMoments.OrientedSpace n) w (width (s : ℝ) γ) (moment γ) N (ε / 3)‖ ≤
        1 := by
    apply opNorm_le_bound _ zero_le_one
    intro v
    have h := ((SharpClockSimulation.output (P := EuclideanSpace ℂ n)
      (V := SparseEdgeMoments.OrientedSpace n) w (width (s : ℝ) γ) (moment γ) N
        (ε / 3)).norm_map_iff_adjoint_comp_self.mpr hOutIso) v
    rw [h, one_mul]
  have hMain : ‖p.eval x ∘L (E ∘L SharpClockQuery.input w (width (s : ℝ) γ) (moment γ) N
      (ε / 3)) - (E ∘L SharpClockSimulation.output w (width (s : ℝ) γ) (moment γ) N
        (ε / 3)) ∘L evolution U N‖ ≤ 2 * (ε / 3) := by
    rw [hEval x, comp_assoc, ← comp_sub, EncodedOracle.norm_comp_eq E hE]
    exact hImpl
  calc
    _ ≤ ‖p.eval x ∘L (E ∘L SharpClockQuery.input w (width (s : ℝ) γ) (moment γ) N (ε / 3)) -
          (E ∘L SharpClockSimulation.output w (width (s : ℝ) γ) (moment γ) N (ε / 3)) ∘L
            evolution U N‖ +
        ‖(E ∘L SharpClockSimulation.output w (width (s : ℝ) γ) (moment γ) N (ε / 3)) ∘L
            evolution U N -
          (E ∘L SharpClockSimulation.output w (width (s : ℝ) γ) (moment γ) N (ε / 3)) ∘L
            sampledEvolution D σ N τ x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * (ε / 3) + N * (Real.sqrt s * τ / N) ^ 3 := by
      apply add_le_add hMain
      rw [← comp_sub, comp_assoc, EncodedOracle.norm_comp_eq E hE]
      calc
        _ ≤ ‖SharpClockSimulation.output (P := EuclideanSpace ℂ n)
            (V := SparseEdgeMoments.OrientedSpace n) w (width (s : ℝ) γ) (moment γ) N
              (ε / 3)‖ * ‖evolution U N - sampledEvolution D σ N τ x‖ := opNorm_comp_le _ _
        _ ≤ 1 * (N * (Real.sqrt s * τ / N) ^ 3) :=
          mul_le_mul hOutNorm hProd (norm_nonneg _) zero_le_one
        _ = N * (Real.sqrt s * τ / N) ^ 3 := one_mul _

set_option maxRecDepth 8192 in
/-- An actual coherent sampled-time program with slot samples `σ` approximates the ordered
product of the slot exponentials, uniformly over the unknown instance. -/
theorem exists_sampled_simulation (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (σ : ℕ → Fin M) {N : ℕ} (hN : 0 < N)
    (hH : ∀ y, (D.matrix y).IsHermitian)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ 1)
    (hcol : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ 1)
    (γ τ ε : ℝ) (hγ : 0 < γ) (hγOne : γ ≤ 1) (hτ : 0 ≤ τ) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hStep : Sampled.step (s : ℝ) γ τ N ≤ 1 / 4) :
    ∃ p : MultiOracleCircuit.Program (Sampled.oracle D N (Sampled.degree (s : ℝ) γ τ ε N)),
      p.count ≤ 6 * Sampled.degree (s : ℝ) γ τ ε N * 54 ∧
      (input D hM σ N γ τ ε)† ∘L input D hM σ N γ τ ε = 1 ∧
      (output D hM σ N γ τ ε)† ∘L output D hM σ N γ τ ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L input D hM σ N γ τ ε -
            output D hM σ N γ τ ε ∘L sampledEvolution D σ N τ x‖ ≤
          2 * (ε / 3) + N * (Real.sqrt s * τ / N) ^ 3 := by
  have hE := (embedding D hM σ N (Sampled.degree (s : ℝ) γ τ ε N)).adjoint_comp_self
  have hInIso := SharpClockQuery.input_isometry (P := EuclideanSpace ℂ n)
    (V := SparseEdgeMoments.OrientedSpace n) (Sampled.step (s : ℝ) γ τ N) (width (s : ℝ) γ)
    (moment γ) N (ε / 3) (width_ge_one _ _)
  have hOutIso := SharpClockSimulation.output_isometry (P := EuclideanSpace ℂ n)
    (V := SparseEdgeMoments.OrientedSpace n) (Sampled.step (s : ℝ) γ τ N) (width (s : ℝ) γ)
    (moment γ) N (ε / 3) (width_ge_one _ _)
  obtain ⟨p, hCount, hAction⟩ := sampled_core D σ hN hH hrow hcol γ τ ε hγ hγOne hτ hε hεOne
    hStep (Sampled.oracle D N (Sampled.degree (s : ℝ) γ τ ε N)) (Sampled.oracle_unitary D N _)
    (embedding D hM σ N (Sampled.degree (s : ℝ) γ τ ε N)).toContinuousLinearMap hE 54
    (fun r _ => implementsOn D hM σ γ N _ r)
  exact ⟨p, hCount, Sampled.isometry_comp _ _ hE hInIso, Sampled.isometry_comp _ _ hE hOutIso,
    hAction⟩

end

end Refined

end TimeDependentExtensions
