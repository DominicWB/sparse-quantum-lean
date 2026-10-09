import ODELowerBoundExtensions.Dyson.Theorem
import ODELowerBoundExtensions.Dyson.Fixed
import TimeDependentExtensions.ODE.Theorem

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Corollaries of Lemma `odel:lem:dyson`: the released input class and `Q_A` at fixed parameters

Manuscript lines 4150-4152 ("covers the entire time-dependent class under the coherent access,
regularity, and source-preparation assumptions of Theorem `ode:thm:time`") and lines 4256-4261
(eq. `odel:eq:fixed`).

* `dyson_release_class`: every instance accepted by the released solver
  `TimeDependentExtensions.ODE.solver` (its `Outcome` premises, for any slot count `N`) is
  accepted by the Dyson solver. The release's public PSD promise on the sampled dissipative parts
  makes every used sample accretive (`MeshSampling.generator_accretive`), and the release's
  certified error contains the Dyson error, since its `publicError` adds the nonnegative
  slot-refinement term `s Λ M (T/N) B`. Only `dyson`'s hypotheses and the PSD promise are
  assumed: none of the release's energy bounds or slot conditions.
* `certificate_queries_le`: every released complete certificate with the Dyson parameters
  (`Θ = 0`, `ℓ = shapeLength`, `g' = ampFactor`) has worst-case matrix-query count at most
  `dysonBound z ḡ ε` once `Outcome` holds (its first conjunct and `Certificate.matrix_queries`).
* `queries_fixed`: eq. `odel:eq:fixed` for `Q_A` on the general time-dependent class: at fixed
  `z = s Λ T` and `ḡ`, there are `C` and `ε₀ ∈ (0, 1)` such that for every `ε ≤ ε₀`, every input
  with `Outcome` (supplied by `dyson`) and every such certificate, the worst-case matrix queries
  are at most `C log(1/ε)/log log(1/ε)`.
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set
open MeasureTheory TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE)
open scoped InnerProduct BigOperators

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The release's certified error dominates the Dyson certified error: `publicError` adds the
nonnegative slot-refinement term `s Λ M (T/N) B` to the source quadrature `s Λ ∑ Δ_q² rb_q/2`. -/
theorem quadrature_le_publicError (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (T : ℝ) (N : ℕ)
    (r₀ : ℝ) (rb : Fin M → ℝ) (hT : 0 ≤ T) (hB : 0 ≤ MeshSampling.mass r₀ t rb) :
    (s : ℝ) * D.scale * (∑ q : Fin M, (t ((q : ℕ) + 1) - t q) ^ 2 * rb q) / 2 ≤
      TimeDependentExtensions.ODE.publicError D t T N r₀ rb := by
  unfold TimeDependentExtensions.ODE.publicError
  have hsΛ : 0 ≤ (s : ℝ) * D.scale := mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le
  have hR : 0 ≤ (M : ℝ) * (T / N) * MeshSampling.mass r₀ t rb :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg M) (div_nonneg hT (Nat.cast_nonneg N))) hB
  have hprod := mul_nonneg hsΛ hR
  have heq : (s : ℝ) * D.scale * ((∑ q : Fin M, (t ((q : ℕ) + 1) - t q) ^ 2 * rb q) / 2 +
      M * (T / N) * MeshSampling.mass r₀ t rb) =
      (s : ℝ) * D.scale * (∑ q : Fin M, (t ((q : ℕ) + 1) - t q) ^ 2 * rb q) / 2 +
        (s : ℝ) * D.scale * (M * (T / N) * MeshSampling.mass r₀ t rb) := by ring
  rw [heq]
  linarith

set_option maxHeartbeats 1000000 in
/-- **The Dyson solver covers the released time-dependent class** (lines 4150-4152): for the
data shape of `TimeDependentExtensions.ODE.solver` (`Ks = M`, `σ = id`), under `dyson`'s
hypotheses and the release's public PSD promise on the sampled dissipative parts, the Dyson
solver's bound holds and one public trial family satisfies the released complete certificate
(`Θ = 0`, `ℓ = shapeLength`, `g' = ampFactor`) for every instance satisfying the premises of the
released `TimeDependentExtensions.ODE.Outcome`, verbatim, at any slot count `N`. -/
theorem dyson_release_class (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ)
    (T g ε r₀ : ℝ) (rb : Fin M → ℝ) (hmesh : IsMesh t M T) (hT : 0 < T) (hg : 1 ≤ g)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (h₀ : 0 ≤ r₀) (hb : ∀ r, 0 ≤ rb r)
    (hB : 0 < MeshSampling.mass r₀ t rb)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x r, IsUnitary (Jb x r))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    1274019840 * ampFactor D t T g ε r₀ rb *
        ImprovedODEQueryBudget.queryShape (s : ℝ) 0 (shapeLength D T g ε) ≤
      dysonBound (rate D * T) g ε ∧
    ∃ (q : ℕ → MultiOracleCircuit.Program (oracle D (dysonDegree D T g ε) M J₀ Jb))
      (ψ : DysonSpace M n Z (dysonDegree D T g ε) M)
      (F : EuclideanSpace ℂ n →L[ℂ] DysonSpace M n Z (dysonDegree D T g ε) M),
      (∀ j x, IsUnitary ((q j).eval x)) ∧
      ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
        (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
        (bs : Fin M → EuclideanSpace ℂ n) (bmax : ℝ),
        (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
        (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) →
        (∀ r : Fin M, IntervalIntegrable (b r) volume (t r) (t ((r : ℕ) + 1))) →
        (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ‖b r u‖ ≤ bmax) →
        (∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) →
        ‖sol 0‖ = r₀ → (∀ r, ‖bs r‖ = rb r) →
        (sol 0 ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection (sol 0)) →
        (∀ r, bs r ≠ 0 → Jb x r seed = ODEStateNormalization.unitDirection (bs r)) →
        sol T ≠ 0 →
        MeshSampling.mass r₀ t rb ≤ g * ‖sol T‖ →
        (r₀ + bmax * T) * (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
            ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, r))‖) +
          (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖b r u - bs r‖) +
            TimeDependentExtensions.ODE.publicError D t T N r₀ rb ≤
              ε * MeshSampling.mass r₀ t rb / (2000 * g) →
        ODECompleteTrial.Certificate q
          (ODEGroverAverage.chosenIterations (ampFactor D t T g ε r₀ rb)) ψ F x (sol T)
          (s : ℝ) 0 (shapeLength D T g ε) (ampFactor D t T g ε r₀ rb) ε := by
  obtain ⟨hbound, q, ψ, F, hU, h⟩ :=
    dyson D hM id t T g ε r₀ rb hmesh hT hg hε hε1 h₀ hb hB J₀ Jb hJ₀ hJb seed hSeed
  refine ⟨hbound, q, ψ, F, hU, ?_⟩
  intro x G b sol bs bmax hG hGint hbint hbmax hsol hs0 hbs hJ0 hJb' _ hmass hcert
  have hAcc : ∀ r : Fin M,
      Accretive (SparseStateOverlap.matrixOperator (D.matrix (x, id r))) := fun r =>
    MeshSampling.generator_accretive D (fun _ => r) hPSD x 0
  have hq := quadrature_le_publicError D t T N r₀ rb hT.le hB.le
  refine h x G b sol bs bmax hG hAcc hGint hbint hbmax hsol hs0 hbs hJ0 hJb' hmass
    (le_trans ?_ hcert)
  try simp only [id]
  linarith

omit [DecidableEq Z] in
/-- **The worst-case matrix queries of the Dyson solver** (eq. `odel:eq:dyson`): once `Outcome`
holds (`dyson`), every released complete certificate with the Dyson parameters `Θ = 0`,
`ℓ = shapeLength`, `g' = ampFactor`, over any trial family, has
`worstCost (matrixWeight 1) ≤ dysonBound z ḡ ε`, `z = s Λ T`. -/
theorem certificate_queries_le {Ks : ℕ}
    {D : Data (X × Fin Ks) n Z s} {σ : Fin M → Fin Ks} {t : ℕ → ℝ} {T g ε r₀ : ℝ}
    {rb : Fin M → ℝ} {J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n}
    {Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n} {seed : EuclideanSpace ℂ n}
    (hO : Outcome D σ t T g ε r₀ rb J₀ Jb seed)
    {P R Y L : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    [FiniteDimensional ℂ P] [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
    {O : (L ⊕ Bool) → Y → R →L[ℂ] R} {q : ℕ → MultiOracleCircuit.Program O} {m : ℕ} {ψ : R}
    {F : P →L[ℂ] R} {x : Y} {y : P}
    (c : ODECompleteTrial.Certificate q m ψ F x y (s : ℝ) 0 (shapeLength D T g ε)
      (ampFactor D t T g ε r₀ rb) ε) :
    ((ODECompleteTrial.algorithm c.trial).worstCost
        (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
      dysonBound (rate D * T) g ε :=
  c.matrix_queries.trans hO.1

/-- **Eq. `odel:eq:fixed` for `Q_A` on the general time-dependent class** (lines 4256-4261): at
fixed `z = s Λ T > 0` and `ḡ ≥ 1` there are `C` and `ε₀ ∈ (0, 1)` such that, for every
`ε ≤ ε₀`, every input with `rate D * T = z` satisfying `Outcome` (as `dyson` provides for every
valid input) and every released complete certificate with the Dyson parameters, the worst-case
matrix queries are at most `C log(1/ε)/log log(1/ε)`. -/
theorem queries_fixed (z g : ℝ) (hz : 0 < z) (hg : 1 ≤ g) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ {X n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
        {s Ks M : ℕ} (D : Data (X × Fin Ks) n Z s) (σ : Fin M → Fin Ks) (t : ℕ → ℝ)
        (T r₀ : ℝ) (rb : Fin M → ℝ) (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
        (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
        (seed : EuclideanSpace ℂ n),
        rate D * T = z → Outcome D σ t T g ε r₀ rb J₀ Jb seed →
        ∀ {P R Y L : Type} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
          [FiniteDimensional ℂ P] [NormedAddCommGroup R] [InnerProductSpace ℂ R]
          [CompleteSpace R] {O : (L ⊕ Bool) → Y → R →L[ℂ] R}
          {q : ℕ → MultiOracleCircuit.Program O} {m : ℕ} {ψ : R} {F : P →L[ℂ] R} {x : Y} {y : P}
          (c : ODECompleteTrial.Certificate q m ψ F x y (s : ℝ) 0 (shapeLength D T g ε)
            (ampFactor D t T g ε r₀ rb) ε),
          ((ODECompleteTrial.algorithm c.trial).worstCost
              (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
            C * (Real.log (1 / ε) / Real.log (Real.log (1 / ε))) := by
  obtain ⟨C, ε₀, hε₀, hε₀1, hC⟩ := dyson_fixed z g hz hg
  refine ⟨C, ε₀, hε₀, hε₀1, ?_⟩
  intro ε hε hεle X n Z _ _ _ _ _ s Ks M D σ t T r₀ rb J₀ Jb seed hz' hO
    P R Y L _ _ _ _ _ _ _ O q m ψ F x y c
  have h := certificate_queries_le hO c
  rw [hz'] at h
  exact h.trans (hC ε hε hεle)

end

end ODELowerBoundExtensions.Dyson
