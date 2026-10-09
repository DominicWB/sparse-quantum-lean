import TimeDependentHamiltonian.Native.Encoding
import TimeDependentHamiltonian.Chronology.Products

/-!
# Native simulation of the ordered sampled evolution

For normalized sparse samples on a uniform mesh with `M` intervals, one public
rescaling `γ` and the sharp filter schedule give an actual coherent
sampled-time oracle program whose complete output approximates the ordered
product of the sampled exponentials `exp (-i (τ/M) Ĥ_k)`
(`exists_sampled_simulation`). The error is the amplified filter error plus
the accumulated Cayley error `M (√s τ / M)³`; the query count is at most
`6 · 54 · d`, with `d` the filter degree, independently of `M`.

All clock promises are proved for every sample from the released exact
sparse Cayley construction; the boundary preparation is common to all
samples because it depends only on the public slot embedding.
-/

namespace SparseHamiltonian.TimeDependent

namespace Sampled

noncomputable section

open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding CayleyClockInterface
open ImprovedCayleyMoments FixedNativeCayleySimulation
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- The Cayley step in rescaled units on a uniform mesh with `M` intervals. -/
def step (s γ τ : ℝ) (M : ℕ) : ℝ := time s τ γ / M

/-- The filter degree, with the unreduced chronological budget in its argument
so that it agrees with the workspace of the slot-dependent simulation. -/
def degree (s γ τ ε : ℝ) (M : ℕ) : ℕ :=
  SharpFilterSchedule.degree (width s γ) ((M : ℝ) * step s γ τ M * moment γ) (ε / 3)

/-- The fixed clean input: the smoothing preparation followed by the sampled
physical encoding. -/
def input (D : Data (X × Fin M) n Z s) (hM : 0 < M) (γ τ ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] Physical n Z M M (degree (s : ℝ) γ τ ε M) :=
  (embedding D hM M (degree (s : ℝ) γ τ ε M)).toContinuousLinearMap ∘L
    SharpClockQuery.input (P := EuclideanSpace ℂ n) (V := SparseEdgeMoments.OrientedSpace n)
      (step (s : ℝ) γ τ M) (width (s : ℝ) γ) (moment γ) M (ε / 3)

/-- The fixed clean output embedding. -/
def output (D : Data (X × Fin M) n Z s) (hM : 0 < M) (γ τ ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] Physical n Z M M (degree (s : ℝ) γ τ ε M) :=
  (embedding D hM M (degree (s : ℝ) γ τ ε M)).toContinuousLinearMap ∘L
    SharpClockSimulation.output (P := EuclideanSpace ℂ n)
      (V := SparseEdgeMoments.OrientedSpace n)
      (step (s : ℝ) γ τ M) (width (s : ℝ) γ) (moment γ) M (ε / 3)

/-- The ordered product of the sampled exponentials on the uniform mesh. -/
def sampledEvolution (D : Data (X × Fin M) n Z s) (hM : 0 < M) (τ : ℝ) (x : X) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  evolution (fun k => NormedSpace.exp ((-Complex.I * ((τ / M : ℝ) : ℂ)) •
    SparseStateOverlap.matrixOperator (D.matrix (x, sampleIndex hM k)))) M

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The scalar identity behind the uniform mesh: one rescaled Cayley step of
the compressed generator is the sampled Hamiltonian times `τ / M`. -/
theorem step_smul_compressed (D : Data (X × Fin M) n Z s) (y : X × Fin M)
    (hH : (D.matrix y).IsHermitian) (γ τ : ℝ) (hγ : γ ≠ 0) (hs : 0 < s) :
    ((step (s : ℝ) γ τ M : ℝ) : ℂ) • compressed (generator D y) (boundary D) γ =
      ((τ / M : ℝ) : ℂ) • SparseStateOverlap.matrixOperator (D.matrix y) := by
  have hcomp : compressed (generator D y) (boundary D) γ =
      (γ : ℂ) • ((boundary D)† ∘L generator D y ∘L boundary D) := by
    simp only [compressed, scaled, smul_comp, comp_smul]
  rw [hcomp, compression D y hH, smul_smul, smul_smul]
  congr 1
  have hsR : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.mpr (by exact_mod_cast hs)
  have hγC : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  have hsC : ((Real.sqrt s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsR.ne'
  simp only [step, time, Complex.ofReal_div, Complex.ofReal_mul]
  field_simp

omit [Fintype n] [DecidableEq n] in
/-- Composition of isometries is an isometry. -/
theorem isometry_comp {A B C : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    [NormedAddCommGroup C] [InnerProductSpace ℂ C] [CompleteSpace C]
    (E : B →L[ℂ] C) (F : A →L[ℂ] B) (hE : E† ∘L E = 1) (hF : F† ∘L F = 1) :
    (E ∘L F)† ∘L (E ∘L F) = 1 := by
  rw [adjoint_comp, comp_assoc, ← comp_assoc (ContinuousLinearMap.adjoint E) E F, hE, one_def,
    id_comp]
  exact hF

variable {Label K : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
set_option maxRecDepth 8192 in
/-- The coherent sampled-time construction on any fixed isometric encoding
of the clock workspace whose active layers are implemented at cost `q`. -/
theorem sampled_core (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (hH : ∀ y, (D.matrix y).IsHermitian)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ 1)
    (hcol : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ 1)
    (γ τ ε : ℝ) (hγ : 0 < γ) (hγOne : γ ≤ 1) (hτ : 0 ≤ τ) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hStep : step (s : ℝ) γ τ M ≤ 1 / 4)
    (O : Label → X → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (E : SharpClockQuery.Space (P := EuclideanSpace ℂ n) (V := SparseEdgeMoments.OrientedSpace n)
      (step (s : ℝ) γ τ M) (width (s : ℝ) γ) (moment γ) M (ε / 3) →L[ℂ] K)
    (hE : E† ∘L E = 1) (q : ℕ)
    (hQuery : ∀ r < 2 * SharpFilterSchedule.degree (width (s : ℝ) γ)
        ((M : ℝ) * step (s : ℝ) γ τ M * moment γ) (ε / 3),
      LabeledEncodedOracle.ImplementsOn O
        (fun x => activeClockV (P := EuclideanSpace ℂ n) (actions D hM γ x) M
          (SharpFilterSchedule.degree (width (s : ℝ) γ)
            ((M : ℝ) * step (s : ℝ) γ τ M * moment γ) (ε / 3)) r) E q) :
    ∃ p : MultiOracleCircuit.Program O,
      p.count ≤ 6 * SharpFilterSchedule.degree (width (s : ℝ) γ)
        ((M : ℝ) * step (s : ℝ) γ τ M * moment γ) (ε / 3) * q ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L (E ∘L SharpClockQuery.input (step (s : ℝ) γ τ M) (width (s : ℝ) γ)
            (moment γ) M (ε / 3)) -
          (E ∘L SharpClockSimulation.output (step (s : ℝ) γ τ M) (width (s : ℝ) γ)
            (moment γ) M (ε / 3)) ∘L sampledEvolution D hM τ x‖ ≤
          2 * (ε / 3) + M * (Real.sqrt s * τ / M) ^ 3 := by
  classical
  let J := boundary D
  let w := step (s : ℝ) γ τ M
  let K : X → ℕ → _ := fun x k => generator D (x, sampleIndex hM k)
  let S : X → ℕ → _ := fun x k => inverse D (x, sampleIndex hM k) γ
  have hs : 0 < s := D.slots_pos
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hw : 0 ≤ w := by
    have ht : 0 ≤ time (s : ℝ) τ γ := div_nonneg (mul_nonneg hτ (Real.sqrt_nonneg _)) hγ.le
    exact div_nonneg ht hMR.le
  have hJ : J† ∘L J = 1 := boundary_isometry D
  have hSelf : ∀ x k, star (K x k) = K x k := fun x k => generator_self_adjoint D _
  have hKJ : ∀ x k, ‖K x k ∘L J‖ ≤ 1 := fun x k =>
    generator_boundary_norm_le D _ (hrow _) (hcol _)
  have hAct : ∀ x k, actions D hM γ x k = cayleyAction (scaled (K x k) γ) (S x k) :=
    fun x k => action_eq_cayley D _ γ
  have hD : ∀ x k, (actions D hM γ x k)† ∘L actions D hM γ x k = 1 := by
    intro x k
    change star (actions D hM γ x k) * actions D hM γ x k = 1
    rw [hAct]
    exact cayleyAction_star_mul_self
      (A := SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n)
      (scaled (K x k) γ) (S x k) (scaled_self_adjoint (K x k) γ (hSelf x k))
      (inverse_right D _ γ)
  have hRight : ∀ x k, (1 - actions D hM γ x k) ∘L resolventAtOne (scaled (K x k) γ) = 1 := by
    intro x k
    change (1 - actions D hM γ x k) * resolventAtOne (scaled (K x k) γ) = 1
    rw [hAct]
    exact one_sub_cayleyAction_mul_resolventAtOne
      (A := SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n)
      (scaled (K x k) γ) (S x k) (inverse_right D _ γ) (inverse_left D _ γ)
  have hLeft : ∀ x k, resolventAtOne (scaled (K x k) γ) ∘L (1 - actions D hM γ x k) = 1 := by
    intro x k
    change resolventAtOne (scaled (K x k) γ) * (1 - actions D hM γ x k) = 1
    rw [hAct]
    exact resolventAtOne_mul_one_sub_cayleyAction
      (A := SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n)
      (scaled (K x k) γ) (S x k) (inverse_right D _ γ)
  obtain ⟨p, hCount, hEval⟩ := implementationV_query_certificate
    (fun x => actions D hM γ x) J w (width (s : ℝ) γ) (moment γ) M (ε / 3)
    (width_ge_one _ _) hw hStep hD hJ O hO E hE q hQuery
  have hOutIso := SharpClockSimulation.output_isometry (P := EuclideanSpace ℂ n)
    (V := SparseEdgeMoments.OrientedSpace n) w (width (s : ℝ) γ) (moment γ) M (ε / 3)
    (width_ge_one _ _)
  refine ⟨p, hCount, fun x => ⟨p.eval_unitary hO x, ?_⟩⟩
  obtain ⟨U, R, hRRight, _hRLeft, hCayley, _hIso, hImpl, _hDeg⟩ :=
    exists_precise_implementationV (actions D hM γ x)
      (fun k => resolventAtOne (scaled (K x k) γ)) J
      (fun k => compressed (K x k) J γ) w (width (s : ℝ) γ) (endpoint γ) (moment γ) M
      (width_ge_one _ _) hw hStep (hD x) hJ (hRight x) (hLeft x)
      (fun k => resolvent_norm (K x k) (s : ℝ) γ hγ.le (generator_norm_le D _ (hrow _)))
      (fun k => resolventAtOne_compression (scaled (K x k) γ) J hJ)
      (fun k => compressed_self_adjoint (K x k) J γ (hSelf x k))
      (fun k => (compressed_norm (K x k) J γ hγ.le hJ (hKJ x k)).trans hγOne)
      (fun k => endpoint_norm (K x k) J γ (hSelf x k) hJ hγ.le (hKJ x k))
      (endpoint_sq γ).le (moment_le_width (s : ℝ) γ hγ.le hγOne) (ε / 3)
      (by positivity) (by linarith)
  -- Each Cayley step is within `(√s τ / M)^3` of the sampled exponential.
  let A : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun k =>
    SparseStateOverlap.matrixOperator (D.matrix (x, sampleIndex hM k))
  let Xs : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun k =>
    (-Complex.I * (w : ℂ)) • compressed (K x k) J γ
  have hXA : ∀ k, Xs k = (-Complex.I * ((τ / M : ℝ) : ℂ)) • A k := by
    intro k
    have h := step_smul_compressed D (x, sampleIndex hM k) (hH _) γ τ hγ.ne' hs
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
  have hwγ : w * γ = Real.sqrt s * τ / M := by
    simp only [w, step, time]
    field_simp
  have hXnorm : ∀ k, ‖Xs k‖ ≤ Real.sqrt s * τ / M := by
    intro k
    have hHk := (compressed_norm (K x k) J γ hγ.le hJ (hKJ x k))
    calc
      ‖Xs k‖ = w * ‖compressed (K x k) J γ‖ := by
        change ‖(-Complex.I * (w : ℂ)) • compressed (K x k) J γ‖ = _
        rw [norm_smul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_of_nonneg hw]
      _ ≤ w * γ := mul_le_mul_of_nonneg_left hHk hw
      _ = Real.sqrt s * τ / M := hwγ
  have hXone : ∀ k, ‖Xs k‖ ≤ 1 := by
    intro k
    have hle : Real.sqrt s * τ / M ≤ w := by
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
  have hStepErr : ∀ k, ‖U k - NormedSpace.exp (Xs k)‖ ≤ (Real.sqrt s * τ / M) ^ 3 := by
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
  have hProd : ‖evolution U M - sampledEvolution D hM τ x‖ ≤
      M * (Real.sqrt s * τ / M) ^ 3 := by
    have hEq : sampledEvolution D hM τ x = evolution (fun k => NormedSpace.exp (Xs k)) M := by
      simp only [sampledEvolution, hXA, A]
    rw [hEq]
    exact evolution_sub_norm_le_mul U _ hUnorm hExpNorm hStepErr M
  have hOutNorm : ‖SharpClockSimulation.output (P := EuclideanSpace ℂ n)
      (V := SparseEdgeMoments.OrientedSpace n) w (width (s : ℝ) γ) (moment γ) M (ε / 3)‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro v
    have h := ((SharpClockSimulation.output (P := EuclideanSpace ℂ n)
      (V := SparseEdgeMoments.OrientedSpace n) w (width (s : ℝ) γ) (moment γ) M
        (ε / 3)).norm_map_iff_adjoint_comp_self.mpr hOutIso) v
    rw [h, one_mul]
  have hMain : ‖p.eval x ∘L (E ∘L SharpClockQuery.input w (width (s : ℝ) γ) (moment γ) M (ε / 3)) -
      (E ∘L SharpClockSimulation.output w (width (s : ℝ) γ) (moment γ) M (ε / 3)) ∘L
        evolution U M‖ ≤ 2 * (ε / 3) := by
    rw [hEval x, comp_assoc, ← comp_sub, EncodedOracle.norm_comp_eq E hE]
    exact hImpl
  calc
    _ ≤ ‖p.eval x ∘L (E ∘L SharpClockQuery.input w (width (s : ℝ) γ) (moment γ) M (ε / 3)) -
          (E ∘L SharpClockSimulation.output w (width (s : ℝ) γ) (moment γ) M (ε / 3)) ∘L
            evolution U M‖ +
        ‖(E ∘L SharpClockSimulation.output w (width (s : ℝ) γ) (moment γ) M (ε / 3)) ∘L
            evolution U M -
          (E ∘L SharpClockSimulation.output w (width (s : ℝ) γ) (moment γ) M (ε / 3)) ∘L
            sampledEvolution D hM τ x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * (ε / 3) + M * (Real.sqrt s * τ / M) ^ 3 := by
      apply add_le_add hMain
      rw [← comp_sub, comp_assoc, EncodedOracle.norm_comp_eq E hE]
      calc
        _ ≤ ‖SharpClockSimulation.output (P := EuclideanSpace ℂ n)
            (V := SparseEdgeMoments.OrientedSpace n) w (width (s : ℝ) γ) (moment γ) M (ε / 3)‖ *
            ‖evolution U M - sampledEvolution D hM τ x‖ := opNorm_comp_le _ _
        _ ≤ 1 * (M * (Real.sqrt s * τ / M) ^ 3) :=
          mul_le_mul hOutNorm hProd (norm_nonneg _) zero_le_one
        _ = M * (Real.sqrt s * τ / M) ^ 3 := one_mul _

set_option maxRecDepth 8192 in
/-- An actual coherent sampled-time program approximates the ordered product
of the sampled exponentials, uniformly over the unknown instance. -/
theorem exists_sampled_simulation (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (hH : ∀ y, (D.matrix y).IsHermitian)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ 1)
    (hcol : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ 1)
    (γ τ ε : ℝ) (hγ : 0 < γ) (hγOne : γ ≤ 1) (hτ : 0 ≤ τ) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hStep : step (s : ℝ) γ τ M ≤ 1 / 4) :
    ∃ p : MultiOracleCircuit.Program (oracle D M (degree (s : ℝ) γ τ ε M)),
      p.count ≤ 6 * degree (s : ℝ) γ τ ε M * 54 ∧
      (input D hM γ τ ε)† ∘L input D hM γ τ ε = 1 ∧
      (output D hM γ τ ε)† ∘L output D hM γ τ ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L input D hM γ τ ε - output D hM γ τ ε ∘L sampledEvolution D hM τ x‖ ≤
          2 * (ε / 3) + M * (Real.sqrt s * τ / M) ^ 3 := by
  have hE := (embedding D hM M (degree (s : ℝ) γ τ ε M)).adjoint_comp_self
  have hInIso := SharpClockQuery.input_isometry (P := EuclideanSpace ℂ n)
    (V := SparseEdgeMoments.OrientedSpace n) (step (s : ℝ) γ τ M) (width (s : ℝ) γ)
    (moment γ) M (ε / 3) (width_ge_one _ _)
  have hOutIso := SharpClockSimulation.output_isometry (P := EuclideanSpace ℂ n)
    (V := SparseEdgeMoments.OrientedSpace n) (step (s : ℝ) γ τ M) (width (s : ℝ) γ)
    (moment γ) M (ε / 3) (width_ge_one _ _)
  obtain ⟨p, hCount, hAction⟩ := sampled_core D hM hH hrow hcol γ τ ε hγ hγOne hτ hε hεOne hStep
    (oracle D M (degree (s : ℝ) γ τ ε M)) (oracle_unitary D M _)
    (embedding D hM M (degree (s : ℝ) γ τ ε M)).toContinuousLinearMap hE 54
    (fun r _ => implementsOn D hM γ M _ r)
  exact ⟨p, hCount, isometry_comp _ _ hE hInIso, isometry_comp _ _ hE hOutIso, hAction⟩

end

end Sampled

end SparseHamiltonian.TimeDependent
