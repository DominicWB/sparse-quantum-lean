import OptimalSparseSimulation.Forms

set_option autoImplicit false

/-!
# The bounded-logarithm regime of Theorem `hs:thm:two-norm`

Appendix B (the proof of Theorem `hs:thm:two-norm`, paragraph "Bounded `h`: the baseline"): with a
supplied entry bound `‖H‖_max ≤ μ` besides the row and column Euclidean norm bound `η`, the baseline
generator `K₀` (`hs:eq:JK`, built from `H/η`) has norm at most `√s μ/η = √σ`, `σ = sμ²/η²`, while
its boundary moments are unchanged. The baseline Cayley-transducer simulation with rescaling `γ`
then has the clock width `⌈max{1, γ√σ}⌉` in place of `⌈max{1, γ√s}⌉`, and the public optimisation of
`γ` gives `O(√σ θ + √(σθ ℓ) + ℓ)` native queries with `θ = η²|t|/μ` and `ℓ = log(2/ε)`
(`√σ θ = √s η|t|`, `σθ = sμ|t|`).

This module repeats the final steps of the baseline simulation (`FixedNativeCayleyQuery`,
`ImprovedNativeSimulation`, `ScaledNativeSimulation`, `ImprovedSparseHamiltonian`) with the
analytic schedule parameters `(σ, θ)` in place of `(s, η|t|)`; the native circuit, the boundary
and the oracle family are those of the baseline simulation.

* `generator_norm_le_entry`: `‖K₀‖ ≤ √s m` when every entry has modulus at most `m`.
* `query_certificate_sigma`: the query certificate with schedule `(σ, θ)`.
* `bounded_simulation`: the simulation for every real `t` with one known isometric input and the
  native oracles with spectators, at most `497664 (√σ θ + √(σθ ℓ) + ℓ)` calls.
-/

namespace TwoNormSimulation

noncomputable section

open ContinuousLinearMap SparseHamiltonian OracleCircuit NativeSparseBlockEncoding
open ImprovedCayleyMoments CayleyClockInterface FixedNativeCayleySimulation
open scoped InnerProduct
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096

variable {X : Type*} {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The baseline generator has norm at most `√s m` when every entry has modulus at
most `m`. -/
theorem generator_norm_le_entry (D : Data X n Z s) (x : X) {m : ℝ} (hm : 0 ≤ m)
    (hent : ∀ i j, ‖D.matrix x i j‖ ≤ m) :
    ‖FixedNativeCayleySimulation.generator D x‖ ≤ Real.sqrt s * m := by
  refine (UnitaryCayleyTransport.conjugate_norm_le _
    (FixedLocatorConjugation.locator_unitary D x) _).trans ?_
  rw [SparseEdgeMoments.generator, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (SparseEdgeMoments.entryGenerator_norm_le _ m hm hent)
    (Real.sqrt_nonneg _)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The physical exponent with the schedule `(σ, θ)`: rescaling cancels, and the sparse
normalization leaves `θ√σ/√s`. -/
theorem physical_exponent_sigma (D : Data X n Z s) (x : X) (hH : (D.matrix x).IsHermitian)
    (σ θ γ : ℝ) (hγ : γ ≠ 0) :
    (-Complex.I * (time σ θ γ : ℂ)) • compressed (generator D x) (boundary D) γ =
      (-Complex.I * ((θ * Real.sqrt σ / Real.sqrt s : ℝ) : ℂ)) •
        SparseStateOverlap.matrixOperator (D.matrix x) := by
  rw [rescaled_exponent _ _ _ _ _ hγ]
  have hComp : (boundary D)† ∘L generator D x ∘L boundary D =
      (SparseEdgeMoments.boundary (D.rowloc x) (D.colloc x))† ∘L
        SparseEdgeMoments.generator (D.matrix x) s ∘L
        SparseEdgeMoments.boundary (D.rowloc x) (D.colloc x) := by
    unfold generator boundary
    rw [UnitaryCayleyTransport.compression, FixedLocatorConjugation.locator_boundary D x]
  rw [hComp]
  have h := NativeCayleySimulation.physical_exponent D x hH (θ * Real.sqrt σ / Real.sqrt s)
  have hs : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.mpr (by exact_mod_cast D.slots_pos)
  have he : θ * Real.sqrt σ / Real.sqrt s * Real.sqrt s = θ * Real.sqrt σ := by
    field_simp
  rw [he] at h
  exact h

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
set_option maxHeartbeats 2000000 in
/-- **The query certificate with schedule `(σ, θ)`.** For normalized data (row and column
Euclidean norms at most one) whose generator has norm at most `√σ`, and a rescaling `γ` with the
public budget of `(σ, θ)`, every implementation of the active layers at cost `q` gives a program
with at most `9216 q (√σ θ + √(σθ ℓ) + ℓ)` calls and error at most `ε` for
`exp(-i (θ√σ/√s) H)`, from the known input `E ∘ evolutionInput` to the known output
`E ∘ evolutionOutput` (aligned later, in `bounded_simulation`). -/
theorem query_certificate_sigma {Label K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (D : Data X n Z s) (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (σ θ γ ε : ℝ) (hK : ∀ x, ‖generator D x‖ ≤ Real.sqrt σ)
    (hγ : 0 < γ) (hγOne : γ ≤ 1) (hθ : 0 ≤ θ) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hBudget : time σ θ γ * moment γ + width σ γ * ImprovedPrecisionBudget.circuitLog ε ≤
      12 * ImprovedPrecisionBudget.shape σ θ (ImprovedPrecisionBudget.targetLog ε))
    (O : Label → X → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (E : SharpClockQuery.EvolutionSpace (P := EuclideanSpace ℂ n)
      (V := SparseEdgeMoments.OrientedSpace n) (time σ θ γ) (width σ γ) (moment γ) ε →L[ℂ] K)
    (hE : E† ∘L E = 1) (q : ℕ)
    (hQuery : ∀ r < 2 * SharpFilterSchedule.degree (width σ γ) (time σ θ γ * moment γ) (ε / 3),
      LabeledEncodedOracle.ImplementsOn O
        (fun x => SharpLabeledActiveClockQuery.evolutionActiveClock
          (P := EuclideanSpace ℂ n) (action D x γ) (time σ θ γ) (width σ γ) (moment γ) ε r)
        E q) :
    ∃ p : MultiOracleCircuit.Program O,
      (p.count : ℝ) ≤ 9216 * (q : ℝ) *
        ImprovedPrecisionBudget.shape σ θ (ImprovedPrecisionBudget.targetLog ε) ∧
      (E ∘L SharpClockQuery.evolutionInput (P := EuclideanSpace ℂ n)
        (V := SparseEdgeMoments.OrientedSpace n) (time σ θ γ) (width σ γ) (moment γ) ε)† ∘L
        (E ∘L SharpClockQuery.evolutionInput (time σ θ γ) (width σ γ) (moment γ) ε) = 1 ∧
      (E ∘L SharpClockSimulation.evolutionOutput (P := EuclideanSpace ℂ n)
        (V := SparseEdgeMoments.OrientedSpace n) (time σ θ γ) (width σ γ) (moment γ) ε)† ∘L
        (E ∘L SharpClockSimulation.evolutionOutput (P := EuclideanSpace ℂ n)
          (V := SparseEdgeMoments.OrientedSpace n) (time σ θ γ) (width σ γ) (moment γ) ε) = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L (E ∘L SharpClockQuery.evolutionInput (P := EuclideanSpace ℂ n)
            (V := SparseEdgeMoments.OrientedSpace n) (time σ θ γ) (width σ γ) (moment γ) ε) -
          (E ∘L SharpClockSimulation.evolutionOutput (P := EuclideanSpace ℂ n)
            (V := SparseEdgeMoments.OrientedSpace n) (time σ θ γ) (width σ γ) (moment γ) ε) ∘L
            NormedSpace.exp ((-Complex.I * ((θ * Real.sqrt σ / Real.sqrt s : ℝ) : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  have ht : 0 ≤ time σ θ γ := div_nonneg (mul_nonneg hθ (Real.sqrt_nonneg _)) hγ.le
  have hJ := boundary_isometry D
  have hSelf := generator_self_adjoint D
  have hD : ∀ x, (action D x γ)† ∘L action D x γ = 1 := by
    intro x
    change star (action D x γ) * action D x γ = 1
    rw [FixedNativeCayleySimulation.action_eq_cayley D x γ]
    exact ImprovedCayleyMoments.cayleyAction_star_mul_self
      (A := SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n)
      (scaled (generator D x) γ) (inverse D x γ)
      (CayleyClockInterface.scaled_self_adjoint (generator D x) γ (hSelf x))
      (FixedNativeCayleySimulation.inverse_right D x γ)
  have hRight : ∀ x, (1 - action D x γ) ∘L resolventAtOne (scaled (generator D x) γ) = 1 := by
    intro x
    change (1 - action D x γ) * resolventAtOne (scaled (generator D x) γ) = 1
    rw [FixedNativeCayleySimulation.action_eq_cayley D x γ]
    exact ImprovedCayleyMoments.one_sub_cayleyAction_mul_resolventAtOne
      (A := SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n)
      (scaled (generator D x) γ) (inverse D x γ)
      (FixedNativeCayleySimulation.inverse_right D x γ)
      (FixedNativeCayleySimulation.inverse_left D x γ)
  have hLeft : ∀ x, resolventAtOne (scaled (generator D x) γ) ∘L (1 - action D x γ) = 1 := by
    intro x
    change resolventAtOne (scaled (generator D x) γ) * (1 - action D x γ) = 1
    rw [FixedNativeCayleySimulation.action_eq_cayley D x γ]
    exact ImprovedCayleyMoments.resolventAtOne_mul_one_sub_cayleyAction
      (A := SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n)
      (scaled (generator D x) γ) (inverse D x γ)
      (FixedNativeCayleySimulation.inverse_right D x γ)
  obtain ⟨p, _hNat, hCount, hIn, hOut, hAction⟩ :=
    SharpLabeledActiveClockQuery.evolution_query_certificate
      (fun x => action D x γ) (fun x => resolventAtOne (scaled (generator D x) γ))
      (boundary D) (fun x => compressed (generator D x) (boundary D) γ)
      (time σ θ γ) (width σ γ) (endpoint γ) (moment γ) ε
      ht (width_ge_one σ γ) hD hJ hRight hLeft
      (fun x => resolvent_norm (generator D x) σ γ hγ.le (hK x))
      (fun x => resolventAtOne_compression (scaled (generator D x) γ) (boundary D) hJ)
      (fun x => compressed_self_adjoint (generator D x) (boundary D) γ (hSelf x))
      (fun x => (compressed_norm (generator D x) (boundary D) γ hγ.le hJ
        (generator_boundary_norm_le D x (hrow x) (hcol x))).trans hγOne)
      (fun x => endpoint_norm (generator D x) (boundary D) γ (hSelf x) hJ hγ.le
        (generator_boundary_norm_le D x (hrow x) (hcol x)))
      (endpoint_sq γ).le (moment_le_width σ γ hγ.le hγOne)
      hε hεOne O hO E hE q hQuery
  refine ⟨p, ?_, hIn, hOut, fun x => ?_⟩
  · change time σ θ γ * moment γ + width σ γ * (1 + Real.log (3 / ε)) ≤
        12 * ImprovedPrecisionBudget.shape σ θ (ImprovedPrecisionBudget.targetLog ε) at hBudget
    have hMul := mul_le_mul_of_nonneg_left hBudget (show (0 : ℝ) ≤ 768 * (q : ℝ) by positivity)
    calc
      (p.count : ℝ) ≤ 768 * (q : ℝ) * (time σ θ γ * moment γ +
          width σ γ * (1 + Real.log (3 / ε))) := hCount
      _ ≤ (768 * (q : ℝ)) * (12 * ImprovedPrecisionBudget.shape σ θ
          (ImprovedPrecisionBudget.targetLog ε)) := hMul
      _ = _ := by ring
  · obtain ⟨hUnitary, hError⟩ := hAction x
    rw [physical_exponent_sigma D x (hH x) σ θ γ hγ.ne'] at hError
    exact ⟨hUnitary, hError⟩

/-! ### The simulation with schedule `(σ, θ)` -/

/-- The moment parameter `σ = sμ²/η²`. -/
def sigma (s : ℕ) (η μ : ℝ) : ℝ := s * μ ^ 2 / η ^ 2

/-- The time scale `θ = η²|t|/μ`. -/
def thetaT (η μ t : ℝ) : ℝ := η ^ 2 * |t| / μ

/-- The oracle family of the active layers with schedule `(σ, θ)`. -/
abbrev oracleS (D : Data X n Z s) (σ γ θ ε : ℝ) :=
  NativeCayleyActive.oracle D (ImprovedNativeSimulation.slots σ γ θ ε)
    (ImprovedNativeSimulation.degree σ γ θ ε)

/-- The fixed physical encoding with schedule `(σ, θ)`. -/
def embeddingS (D : Data X n Z s) (σ γ θ ε : ℝ) :=
  NativeCayleyActive.embedding D (ImprovedNativeSimulation.slots σ γ θ ε)
    (ImprovedNativeSimulation.degree σ γ θ ε)

/-- The known input with schedule `(σ, θ)`. -/
def inputS (D : Data X n Z s) (σ γ θ ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] NativeCayleyActive.Physical n Z
      (ImprovedNativeSimulation.slots σ γ θ ε) (ImprovedNativeSimulation.degree σ γ θ ε) :=
  (embeddingS D σ γ θ ε).toContinuousLinearMap ∘L
    SharpClockQuery.evolutionInput (P := EuclideanSpace ℂ n)
      (V := SparseEdgeMoments.OrientedSpace n) (time σ θ γ) (width σ γ) (moment γ) ε

/-- The known output with schedule `(σ, θ)`. -/
def outputS (D : Data X n Z s) (σ γ θ ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] NativeCayleyActive.Physical n Z
      (ImprovedNativeSimulation.slots σ γ θ ε) (ImprovedNativeSimulation.degree σ γ θ ε) :=
  (embeddingS D σ γ θ ε).toContinuousLinearMap ∘L
    SharpClockSimulation.evolutionOutput (P := EuclideanSpace ℂ n)
      (V := SparseEdgeMoments.OrientedSpace n) (time σ θ γ) (width σ γ) (moment γ) ε

/-- Every active layer with schedule `(σ, θ)` costs `54` native calls. -/
theorem active_implementsOn_sigma (D : Data X n Z s) (σ γ θ ε : ℝ) (r : ℕ) :
    LabeledEncodedOracle.ImplementsOn (oracleS D σ γ θ ε)
      (fun x => SharpLabeledActiveClockQuery.evolutionActiveClock
        (P := EuclideanSpace ℂ n) (action D x γ) (time σ θ γ) (width σ γ) (moment γ) ε r)
      (embeddingS D σ γ θ ε).toContinuousLinearMap 54 :=
  NativeCayleyActive.implementsOn D γ (ImprovedNativeSimulation.slots σ γ θ ε)
    (ImprovedNativeSimulation.degree σ γ θ ε) r

set_option maxHeartbeats 3000000 in
/-- **Normalized simulation with schedule `(σ, θ)`.** For normalized data whose generator has
norm at most `√σ`, `σ ≥ 1` and `θ ≥ 0`, there are a rescaling `γ` and a program over the native
oracles with at most `497664 (√σ θ + √(σθ ℓ) + ℓ)` calls, `ℓ = log(2/ε)`, with error at most
`ε` for `exp(-i (θ√σ/√s) H)` from the known input `inputS` to the known output `outputS`. -/
theorem exists_normalized_simulation (D : Data X n Z s) (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (σ θ ε : ℝ) (hσ : 1 ≤ σ) (hK : ∀ x, ‖generator D x‖ ≤ Real.sqrt σ) (hθ : 0 ≤ θ)
    (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ p : MultiOracleCircuit.Program
          (K := NativeCayleyActive.Physical n Z (ImprovedNativeSimulation.slots σ γ θ ε)
            (ImprovedNativeSimulation.degree σ γ θ ε)) (oracleS D σ γ θ ε),
        (p.count : ℝ) ≤ 497664 * ImprovedPrecisionBudget.shape σ θ
          (ImprovedPrecisionBudget.targetLog ε) ∧
        (inputS D σ γ θ ε)† ∘L inputS D σ γ θ ε = 1 ∧
        (outputS D σ γ θ ε)† ∘L outputS D σ γ θ ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L inputS D σ γ θ ε - outputS D σ γ θ ε ∘L
            NormedSpace.exp ((-Complex.I * ((θ * Real.sqrt σ / Real.sqrt s : ℝ) : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, -, hBudget⟩ :=
    ImprovedPrecisionBudget.exists_rescaling_for_precision σ θ ε hσ hθ hε hεOne
  obtain ⟨p, hCount, hIn, hOut, hAction⟩ :=
    query_certificate_sigma (Label := Query)
      (K := NativeCayleyActive.Physical n Z (ImprovedNativeSimulation.slots σ γ θ ε)
        (ImprovedNativeSimulation.degree σ γ θ ε))
      D hH hrow hcol σ θ γ ε hK hγ hγOne hθ hε hεOne hBudget (oracleS D σ γ θ ε)
      (NativeCayleyActive.oracle_unitary D _ _)
      (embeddingS D σ γ θ ε).toContinuousLinearMap (embeddingS D σ γ θ ε).adjoint_comp_self
      54 (fun r _ => active_implementsOn_sigma D σ γ θ ε r)
  refine ⟨γ, hγ, hγOne, p, ?_, hIn, hOut, hAction⟩
  calc (p.count : ℝ) ≤ 9216 * (54 : ℝ) * ImprovedPrecisionBudget.shape σ θ
        (ImprovedPrecisionBudget.targetLog ε) := hCount
    _ = 497664 * ImprovedPrecisionBudget.shape σ θ (ImprovedPrecisionBudget.targetLog ε) := by
        ring

/-! ### General normalization, signed time and the common form -/

theorem sqrt_sigma (s : ℕ) {η μ : ℝ} (hη : 0 < η) (hμ : 0 ≤ μ) :
    Real.sqrt (sigma s η μ) = Real.sqrt s * (μ / η) := by
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  unfold sigma
  rw [show (s : ℝ) * μ ^ 2 / η ^ 2 = s * (μ / η) ^ 2 by ring, Real.sqrt_mul hs0,
    Real.sqrt_sq (div_nonneg hμ hη.le)]

theorem one_le_sigma (s : ℕ) {η μ : ℝ} (hη : 0 < η) (hηs : η ≤ Real.sqrt s * μ) :
    1 ≤ sigma s η μ := by
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  unfold sigma
  rw [le_div_iff₀ (by positivity)]
  have h1 : η * η ≤ (Real.sqrt s * μ) * (Real.sqrt s * μ) := mul_self_le_mul_self hη.le hηs
  have h2 : (Real.sqrt s * μ) * (Real.sqrt s * μ) = s * μ ^ 2 := by
    rw [show (Real.sqrt s * μ) * (Real.sqrt s * μ) = Real.sqrt s ^ 2 * μ ^ 2 by ring,
      Real.sq_sqrt hs0]
  nlinarith

theorem theta_sqrt_sigma (s : ℕ) (hs : 0 < s) {η μ : ℝ} (hη : 0 < η) (hμ : 0 < μ) (t : ℝ) :
    thetaT η μ t * Real.sqrt (sigma s η μ) / Real.sqrt s = η * |t| := by
  have hs0 : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.mpr (by exact_mod_cast hs)
  rw [sqrt_sigma s hη hμ.le]
  unfold thetaT
  field_simp

set_option maxHeartbeats 4000000 in
/-- **The bounded-logarithm regime of Theorem `hs:thm:two-norm`.** Let `H = D.matrix x` be
Hermitian with row and column Euclidean norms at most `η` and entries of modulus at most `μ`,
`0 < μ ≤ η ≤ √s μ`, and `0 < ε ≤ 1`. For every real `t`, `e^{-itH}` is simulated in the common
form `Simulates (physOracle D)` with at most `497664 (√σ θ + √(σθ ℓ) + ℓ)` native calls,
`σ = sμ²/η²`, `θ = η²|t|/μ` and `ℓ = log(2/ε)`. -/
theorem bounded_simulation (D : Data X n Z s) {η μ t ε : ℝ} (hμ : 0 < μ) (hμη : μ ≤ η)
    (hηs : η ≤ Real.sqrt s * μ) (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hent : ∀ x i j, ‖D.matrix x i j‖ ≤ μ) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    NativeSignedFactor.Simulates (NativeSignedFactor.physOracle D)
      (fun x => SparseStateOverlap.matrixOperator (D.matrix x)) t ε
      (497664 * ImprovedPrecisionBudget.shape (sigma s η μ) (thetaT η μ t)
        (ImprovedPrecisionBudget.targetLog ε)) := by
  have hη : 0 < η := lt_of_lt_of_le hμ hμη
  have hσ1 := one_le_sigma s hη hηs
  have hθ : 0 ≤ thetaT η μ t := by
    unfold thetaT
    positivity
  have hK : ∀ x, ‖generator (NativeSparseRescaling.normalize D η hη) x‖ ≤
      Real.sqrt (sigma s η μ) := by
    intro x
    rw [sqrt_sigma s hη hμ.le]
    apply generator_norm_le_entry _ x (div_nonneg hμ.le hη.le)
    intro i j
    rw [NativeSparseRescaling.normalize_matrix, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hη), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hent x i j) (inv_nonneg.mpr hη.le)
  obtain ⟨γ, -, -, p, hCount, hIn, hOut, hAction⟩ :=
    exists_normalized_simulation (NativeSparseRescaling.normalize D η hη)
      (fun x => NativeSparseRescaling.normalize_hermitian D η hη x (hH x))
      (fun x i => NativeSparseRescaling.normalized_row_energy D η hη x i (hrow x i))
      (fun x j => NativeSparseRescaling.normalized_column_energy D η hη x j (hcol x j))
      (sigma s η μ) (thetaT η μ t) ε hσ1 hK hθ hε hεOne
  change MultiOracleCircuit.Program
    (K := NativeCayleyActive.Physical n Z
      (ImprovedNativeSimulation.slots (sigma s η μ) γ (thetaT η μ t) ε)
      (ImprovedNativeSimulation.degree (sigma s η μ) γ (thetaT η μ t) ε))
    (oracleS D (sigma s η μ) γ (thetaT η μ t) ε) at p
  change (inputS D (sigma s η μ) γ (thetaT η μ t) ε)† ∘L
    inputS D (sigma s η μ) γ (thetaT η μ t) ε = 1 at hIn
  change (outputS D (sigma s η μ) γ (thetaT η μ t) ε)† ∘L
    outputS D (sigma s η μ) γ (thetaT η μ t) ε = 1 at hOut
  have hAbs : ∀ x, ‖p.eval x ∘L inputS D (sigma s η μ) γ (thetaT η μ t) ε -
      outputS D (sigma s η μ) γ (thetaT η μ t) ε ∘L
        NormedSpace.exp ((-Complex.I * ((|t| : ℝ) : ℂ)) •
          SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
    intro x
    have h := (hAction x).2
    rw [theta_sqrt_sigma s D.slots_pos hη hμ, NativeSparseRescaling.exponent_cancel D η hη x |t|]
      at h
    exact h
  have hIso := LabeledAdjointSimulation.signed_isometries
    (inputS D (sigma s η μ) γ (thetaT η μ t) ε) (outputS D (sigma s η μ) γ (thetaT η μ t) ε)
    hIn hOut t
  have hSigned := LabeledAdjointSimulation.signed_program_error p
    (NativeCayleyActive.oracle_unitary D _ _)
    (inputS D (sigma s η μ) γ (thetaT η μ t) ε) (outputS D (sigma s η μ) γ (thetaT η μ t) ε)
    (fun x => SparseStateOverlap.matrixOperator (D.matrix x))
    (fun x => SparseValuePrecision.matrixOperator_star_eq _ (hH x)) t ε hAbs
  obtain ⟨q, hqCount, -, hqIn, hq⟩ :=
    AlignedMultiOracleProgram.exists_aligned_program (oracleS D (sigma s η μ) γ (thetaT η μ t) ε)
      (NativeCayleyActive.oracle_unitary D _ _) _ _ hIso.1 hIso.2
      (LabeledAdjointSimulation.signedProgram p t)
      (fun x => NormedSpace.exp ((-Complex.I * (t : ℂ)) •
        SparseStateOverlap.matrixOperator (D.matrix x))) ε hSigned
  refine OptimalSparseSimulation.simulates_of_spectatorForm
    (K := CleanOutputAlignment.Double (NativeCayleyActive.Physical n Z
      (ImprovedNativeSimulation.slots (sigma s η μ) γ (thetaT η μ t) ε)
      (ImprovedNativeSimulation.degree (sigma s η μ) γ (thetaT η μ t) ε)))
    ((OptimalSparseSimulation.cayleyActive_form D _ _).diagonal Bool) _ t ε _ _ hqIn q ?_ hq
  rw [hqCount, LabeledAdjointSimulation.signedProgram_count]
  exact hCount

end

end TwoNormSimulation
