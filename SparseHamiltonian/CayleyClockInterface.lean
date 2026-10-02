import SparseHamiltonian.ExactEdgeValueQuery

/-!
# From sparse boundary moments to the improved simulation schedule

This module discharges the analytic clock promises from the two distinct
bounds `‖K‖ ≤ sqrt s` and `‖K J‖ ≤ 1`.  The boundary isometry, self-adjoint
generator, and a two-sided Cayley denominator inverse remain explicit data.
The exact edge construction provides that inverse locally; assembling it
on the full sparse workspace and proving the native layer cost are separate
implementation obligations.

The final theorem applies the proved rescaling optimiser to the actual
amplified simulation isometry and its filter degree.  It is not yet a native
sparse-oracle query theorem.
-/

namespace SparseHamiltonian.CayleyClockInterface

noncomputable section
open ContinuousLinearMap ImprovedCayleyMoments
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Rescaling the generator changes the first and second moments differently. -/
def scaled (K : V →L[ℂ] V) (γ : ℝ) : V →L[ℂ] V := (γ : ℂ) • K

/-- Public Hamiltonian represented by the rescaled boundary compression. -/
def compressed (K : V →L[ℂ] V) (J : P →L[ℂ] V) (γ : ℝ) : P →L[ℂ] P :=
  J† ∘L scaled K γ ∘L J

/-- Integer resolvent width, with the same convention as the scalar optimiser. -/
def width (s γ : ℝ) : ℝ := (⌈max 1 (γ * Real.sqrt s)⌉₊ : ℝ)

/-- Quadratic boundary budget, rather than a full-operator norm budget. -/
def moment (γ : ℝ) : ℝ := (1 + γ ^ 2) / 2

def endpoint (γ : ℝ) : ℝ := Real.sqrt ((1 + γ ^ 2) / 4)

/-- Effective time compensates exactly for the compressed generator scale. -/
def time (s τ γ : ℝ) : ℝ := τ * Real.sqrt s / γ

theorem width_ge_one (s γ : ℝ) : 1 ≤ width s γ :=
  (le_max_left _ _).trans (Nat.le_ceil _)

theorem width_ge_scaled_sqrt (s γ : ℝ) : γ * Real.sqrt s ≤ width s γ :=
  (le_max_right _ _).trans (Nat.le_ceil _)

theorem moment_nonneg (γ : ℝ) : 0 ≤ moment γ := by
  unfold moment
  positivity

theorem moment_le_one (γ : ℝ) (hγ : 0 ≤ γ) (hγOne : γ ≤ 1) : moment γ ≤ 1 := by
  unfold moment
  nlinarith

theorem moment_le_width (s γ : ℝ) (hγ : 0 ≤ γ) (hγOne : γ ≤ 1) :
    moment γ ≤ width s γ :=
  (moment_le_one γ hγ hγOne).trans (width_ge_one s γ)

theorem endpoint_sq (γ : ℝ) : (endpoint γ) ^ 2 = moment γ / 2 := by
  rw [endpoint, Real.sq_sqrt (by positivity : 0 ≤ (1 + γ ^ 2) / 4)]
  unfold moment
  ring

theorem scaled_self_adjoint (K : V →L[ℂ] V) (γ : ℝ) (hK : star K = K) :
    star (scaled K γ) = scaled K γ := by
  simp only [scaled, star_smul, hK, Complex.star_def, Complex.conj_ofReal]

omit [CompleteSpace P] [CompleteSpace V] in
theorem scaled_boundary_norm (K : V →L[ℂ] V) (J : P →L[ℂ] V)
    (γ : ℝ) (hγ : 0 ≤ γ) (hKJ : ‖K ∘L J‖ ≤ 1) :
    ‖scaled K γ ∘L J‖ ≤ γ := by
  rw [scaled, smul_comp, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hγ]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hKJ hγ

omit [CompleteSpace V] in
theorem scaled_norm (K : V →L[ℂ] V) (s γ : ℝ)
    (hγ : 0 ≤ γ) (hK : ‖K‖ ≤ Real.sqrt s) :
    ‖scaled K γ‖ ≤ γ * Real.sqrt s := by
  rw [scaled, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hγ]
  exact mul_le_mul_of_nonneg_left hK hγ

theorem compressed_self_adjoint (K : V →L[ℂ] V) (J : P →L[ℂ] V)
    (γ : ℝ) (hK : star K = K) : star (compressed K J γ) = compressed K J γ := by
  have hScaled : (scaled K γ)† = scaled K γ := scaled_self_adjoint K γ hK
  change (J† ∘L scaled K γ ∘L J)† = J† ∘L scaled K γ ∘L J
  simp only [adjoint_comp, adjoint_adjoint, hScaled, comp_assoc]

/-- Compression is controlled by the boundary moment, even when `‖K‖` is large. -/
theorem compressed_norm (K : V →L[ℂ] V) (J : P →L[ℂ] V)
    (γ : ℝ) (hγ : 0 ≤ γ) (hJ : J† ∘L J = 1) (hKJ : ‖K ∘L J‖ ≤ 1) :
    ‖compressed K J γ‖ ≤ γ := by
  have hAdj : ‖J†‖ ≤ 1 := by
    rw [adjoint.norm_map]
    exact SparseMatrixNorm.norm_le_one_of_adjoint_comp J hJ
  calc
    ‖compressed K J γ‖ ≤ ‖J†‖ * ‖scaled K γ ∘L J‖ := opNorm_comp_le _ _
    _ ≤ 1 * γ := mul_le_mul hAdj (scaled_boundary_norm K J γ hγ hKJ)
      (norm_nonneg _) zero_le_one
    _ = γ := one_mul γ

omit [CompleteSpace V] in
theorem resolvent_norm (K : V →L[ℂ] V) (s γ : ℝ)
    (hγ : 0 ≤ γ) (hK : ‖K‖ ≤ Real.sqrt s) :
    ‖resolventAtOne (scaled K γ)‖ ≤ width s γ := by
  have hBase := resolventAtOne_norm_le (scaled K γ)
  have hScaled := scaled_norm K s γ hγ hK
  have hOne := width_ge_one s γ
  have hWidth := width_ge_scaled_sqrt s γ
  linarith

theorem endpoint_norm (K : V →L[ℂ] V) (J : P →L[ℂ] V)
    (γ : ℝ) (hSelf : star K = K) (hJ : J† ∘L J = 1)
    (hγ : 0 ≤ γ) (hKJ : ‖K ∘L J‖ ≤ 1) :
    ‖resolventAtOne (scaled K γ) ∘L J‖ ≤ endpoint γ := by
  have hSq := rescaled_boundary_norm_sq_le K J γ hSelf hJ hγ hKJ
  have hRoot := Real.sq_sqrt (by positivity : 0 ≤ (1 + γ ^ 2) / 4)
  have hNonneg := Real.sqrt_nonneg ((1 + γ ^ 2) / 4)
  change ‖resolventAtOne ((γ : ℂ) • K) ∘L J‖ ≤ Real.sqrt ((1 + γ ^ 2) / 4)
  nlinarith [norm_nonneg (resolventAtOne ((γ : ℂ) • K) ∘L J)]

set_option maxRecDepth 4096 in
/-- All analytic promises needed by the sharp continuous-time simulator are
proved from generator moments.  Only inverse existence is supplied here. -/
theorem evolution_error (K S : V →L[ℂ] V) (J : P →L[ℂ] V)
    (s γ τ ε : ℝ) (hγ : 0 ≤ γ) (hγOne : γ ≤ 1)
    (hSelf : star K = K) (hJ : J† ∘L J = 1)
    (hK : ‖K‖ ≤ Real.sqrt s) (hKJ : ‖K ∘L J‖ ≤ 1)
    (hRight : (scaled K γ - Complex.I • (1 : V →L[ℂ] V)) * S = 1)
    (hLeft : S * (scaled K γ - Complex.I • (1 : V →L[ℂ] V)) = 1)
    (hτ : 0 ≤ τ) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    let D := cayleyAction (scaled K γ) S
    (SharpClockSimulation.evolutionImplementation D J τ (width s γ) (moment γ) ε)† ∘L
      SharpClockSimulation.evolutionImplementation D J τ (width s γ) (moment γ) ε = 1 ∧
    ‖SharpClockSimulation.evolutionImplementation D J τ (width s γ) (moment γ) ε -
      SharpClockSimulation.evolutionOutput (P := P) (V := V) τ (width s γ) (moment γ) ε ∘L
        NormedSpace.exp ((-Complex.I * (τ : ℂ)) • compressed K J γ)‖ ≤ ε ∧
    (SharpFilterSchedule.degree (width s γ) (τ * moment γ) (ε / 3) : ℝ) ≤
      128 * (τ * moment γ + width s γ * (1 + Real.log (1 / (ε / 3)))) := by
  exact SharpClockSimulation.evolution_error
    (cayleyAction (scaled K γ) S) (resolventAtOne (scaled K γ)) J (compressed K J γ)
    τ (width s γ) (endpoint γ) (moment γ) ε hτ (width_ge_one s γ)
    (cayleyAction_star_mul_self _ S (scaled_self_adjoint K γ hSelf) hRight) hJ
    (one_sub_cayleyAction_mul_resolventAtOne _ S hRight hLeft)
    (resolventAtOne_mul_one_sub_cayleyAction _ S hRight)
    (resolvent_norm K s γ hγ hK) (resolventAtOne_compression _ J hJ)
    (compressed_self_adjoint K J γ hSelf)
    ((compressed_norm K J γ hγ hJ hKJ).trans hγOne)
    (endpoint_norm K J γ hSelf hJ hγ hKJ) (endpoint_sq γ).le
    (moment_le_width s γ hγ hγOne) hε hεOne

/-- Rescaling cancels exactly in the exponential's generator; this is an
operator equality, not just a comparison of complexity parameters. -/
theorem rescaled_exponent (K : V →L[ℂ] V) (J : P →L[ℂ] V)
    (s τ γ : ℝ) (hγ : γ ≠ 0) :
    (-Complex.I * (time s τ γ : ℂ)) • compressed K J γ =
      (-Complex.I * ((τ * Real.sqrt s : ℝ) : ℂ)) • (J† ∘L K ∘L J) := by
  have hγC : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  have hScalar : (-Complex.I * (time s τ γ : ℂ)) * (γ : ℂ) =
      -Complex.I * ((τ * Real.sqrt s : ℝ) : ℂ) := by
    simp only [time, Complex.ofReal_div, Complex.ofReal_mul]
    field_simp [hγC]
  simp only [compressed, scaled, smul_comp, comp_smul, smul_smul, hScalar]

set_option maxRecDepth 4096 in
/-- Optimisation now controls a concrete simulation isometry and its filter
degree.  The target evolution is independent of the selected rescaling.
The remaining inverse and native-workspace obligations are explicit. -/
theorem exists_optimized_implementation
    (K : V →L[ℂ] V) (J : P →L[ℂ] V) (S : ℝ → V →L[ℂ] V)
    (s τ ε : ℝ) (hs : 1 ≤ s) (hτ : 0 ≤ τ) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hSelf : star K = K) (hJ : J† ∘L J = 1)
    (hK : ‖K‖ ≤ Real.sqrt s) (hKJ : ‖K ∘L J‖ ≤ 1)
    (hRight : ∀ γ, 0 < γ → γ ≤ 1 →
      (scaled K γ - Complex.I • (1 : V →L[ℂ] V)) * S γ = 1)
    (hLeft : ∀ γ, 0 < γ → γ ≤ 1 →
      S γ * (scaled K γ - Complex.I • (1 : V →L[ℂ] V)) = 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt s ∧
      let D := cayleyAction (scaled K γ) (S γ)
      let t := time s τ γ
      (SharpClockSimulation.evolutionImplementation D J t (width s γ) (moment γ) ε)† ∘L
        SharpClockSimulation.evolutionImplementation D J t (width s γ) (moment γ) ε = 1 ∧
      ‖SharpClockSimulation.evolutionImplementation D J t (width s γ) (moment γ) ε -
        SharpClockSimulation.evolutionOutput (P := P) (V := V) t (width s γ) (moment γ) ε ∘L
          NormedSpace.exp ((-Complex.I * ((τ * Real.sqrt s : ℝ) : ℂ)) •
            (J† ∘L K ∘L J))‖ ≤ ε ∧
      (SharpFilterSchedule.degree (width s γ) (t * moment γ) (ε / 3) : ℝ) ≤
        1536 * ImprovedPrecisionBudget.shape s τ (ImprovedPrecisionBudget.targetLog ε) := by
  obtain ⟨γ, hγ, hγOne, hWidth, hBudget⟩ :=
    ImprovedPrecisionBudget.exists_rescaling_for_precision s τ ε hs hτ hε hεOne
  have ht : 0 ≤ time s τ γ := div_nonneg (mul_nonneg hτ (Real.sqrt_nonneg s)) hγ.le
  obtain ⟨hIso, hError, hDegree⟩ := evolution_error K (S γ) J s γ (time s τ γ) ε
    hγ.le hγOne hSelf hJ hK hKJ (hRight γ hγ hγOne) (hLeft γ hγ hγOne)
    ht hε hεOne
  rw [rescaled_exponent K J s τ γ hγ.ne'] at hError
  refine ⟨γ, hγ, hγOne, hWidth, hIso, hError, ?_⟩
  have hArg : 1 / (ε / 3) = 3 / ε := by ring
  rw [hArg] at hDegree
  change time s τ γ * moment γ + width s γ *
    (1 + Real.log (3 / ε)) ≤
      12 * ImprovedPrecisionBudget.shape s τ (ImprovedPrecisionBudget.targetLog ε) at hBudget
  linarith

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Analytic and scalar parts of the improved query bound, for a family with
a fixed boundary preparation.  The sole circuit-level premise is still the
implementation of each complete coherent reuse layer, at cost `q`.

The scalar budget is supplied by `exists_rescaling_for_precision`.  This
formulation keeps the oracle workspace fixed after choosing that rescaling. -/
theorem query_certificate_of_moments
    [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    {X : Type*} (K S : X → V →L[ℂ] V) (J : P →L[ℂ] V)
    (s γ τ ε : ℝ) (hγ : 0 < γ) (hγOne : γ ≤ 1)
    (hτ : 0 ≤ τ) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hSelf : ∀ x, star (K x) = K x) (hJ : J† ∘L J = 1)
    (hK : ∀ x, ‖K x‖ ≤ Real.sqrt s) (hKJ : ∀ x, ‖K x ∘L J‖ ≤ 1)
    (hRight : ∀ x, (scaled (K x) γ - Complex.I • (1 : V →L[ℂ] V)) * S x = 1)
    (hLeft : ∀ x, S x * (scaled (K x) γ - Complex.I • (1 : V →L[ℂ] V)) = 1)
    (hBudget : time s τ γ * moment γ + width s γ * ImprovedPrecisionBudget.circuitLog ε ≤
      12 * ImprovedPrecisionBudget.shape s τ (ImprovedPrecisionBudget.targetLog ε))
    (O : X → SharpClockQuery.EvolutionSpace (P := P) (V := V)
        (time s τ γ) (width s γ) (moment γ) ε →L[ℂ]
      SharpClockQuery.EvolutionSpace (P := P) (V := V)
        (time s τ γ) (width s γ) (moment γ) ε)
    (hO : ∀ x, OracleCircuit.IsUnitary (O x)) (q : ℕ)
    (hLayer : ∀ r < 2 * SharpFilterSchedule.degree (width s γ)
        (time s τ γ * moment γ) (ε / 3),
      OracleCircuit.Implements O (fun x => SharpClockQuery.evolutionLayer
        (cayleyAction (scaled (K x) γ) (S x)) J
        (time s τ γ) (width s γ) (moment γ) ε r) q) :
    ∃ p : OracleCircuit.Program O,
      (p.count : ℝ) ≤ 9216 * (q : ℝ) *
        ImprovedPrecisionBudget.shape s τ (ImprovedPrecisionBudget.targetLog ε) ∧
      (SharpClockQuery.evolutionInput (P := P) (V := V)
        (time s τ γ) (width s γ) (moment γ) ε)† ∘L
        SharpClockQuery.evolutionInput (time s τ γ) (width s γ) (moment γ) ε = 1 ∧
      (SharpClockSimulation.evolutionOutput (P := P) (V := V)
        (time s τ γ) (width s γ) (moment γ) ε)† ∘L
        SharpClockSimulation.evolutionOutput (time s τ γ) (width s γ) (moment γ) ε = 1 ∧
      ∀ x, OracleCircuit.IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L SharpClockQuery.evolutionInput (P := P) (V := V)
            (time s τ γ) (width s γ) (moment γ) ε -
          SharpClockSimulation.evolutionOutput (P := P) (V := V)
            (time s τ γ) (width s γ) (moment γ) ε ∘L
          NormedSpace.exp ((-Complex.I * ((τ * Real.sqrt s : ℝ) : ℂ)) •
            (J† ∘L K x ∘L J))‖ ≤ ε := by
  have ht : 0 ≤ time s τ γ := div_nonneg (mul_nonneg hτ (Real.sqrt_nonneg s)) hγ.le
  obtain ⟨p, _hNat, hCount, hIn, hOut, hAction⟩ :=
    SharpClockQuery.evolution_query_certificate
      (fun x => cayleyAction (scaled (K x) γ) (S x))
      (fun x => resolventAtOne (scaled (K x) γ)) J (fun x => compressed (K x) J γ)
      (time s τ γ) (width s γ) (endpoint γ) (moment γ) ε ht (width_ge_one s γ)
      (fun x => cayleyAction_star_mul_self _ _ (scaled_self_adjoint _ γ (hSelf x)) (hRight x))
      hJ
      (fun x => one_sub_cayleyAction_mul_resolventAtOne _ _ (hRight x) (hLeft x))
      (fun x => resolventAtOne_mul_one_sub_cayleyAction _ _ (hRight x))
      (fun x => resolvent_norm _ s γ hγ.le (hK x))
      (fun x => resolventAtOne_compression _ J hJ)
      (fun x => compressed_self_adjoint _ J γ (hSelf x))
      (fun x => (compressed_norm _ J γ hγ.le hJ (hKJ x)).trans hγOne)
      (fun x => endpoint_norm _ J γ (hSelf x) hJ hγ.le (hKJ x))
      (endpoint_sq γ).le (moment_le_width s γ hγ.le hγOne)
      hε hεOne O hO q hLayer
  refine ⟨p, ?_, hIn, hOut, fun x => ?_⟩
  · change time s τ γ * moment γ + width s γ * (1 + Real.log (3 / ε)) ≤
      12 * ImprovedPrecisionBudget.shape s τ (ImprovedPrecisionBudget.targetLog ε) at hBudget
    have hMul := mul_le_mul_of_nonneg_left hBudget
      (show (0 : ℝ) ≤ 768 * (q : ℝ) by positivity)
    calc
      (p.count : ℝ) ≤ 768 * (q : ℝ) *
          (time s τ γ * moment γ + width s γ * (1 + Real.log (3 / ε))) := hCount
      _ ≤ (768 * (q : ℝ)) *
          (12 * ImprovedPrecisionBudget.shape s τ (ImprovedPrecisionBudget.targetLog ε)) := hMul
      _ = 9216 * (q : ℝ) *
          ImprovedPrecisionBudget.shape s τ (ImprovedPrecisionBudget.targetLog ε) := by ring
  · obtain ⟨hUnitary, hError⟩ := hAction x
    rw [rescaled_exponent (K x) J s τ γ hγ.ne'] at hError
    exact ⟨hUnitary, hError⟩

end
end SparseHamiltonian.CayleyClockInterface
