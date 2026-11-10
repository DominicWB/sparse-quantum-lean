import DysonGeneralAccess.Theorem
import ODELowerBoundExtensions.Dyson.Corollaries

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Consequences of the single-program form of Lemma `odel:lem:dyson`

Manuscript: the paragraph before Lemma `odel:lem:dyson` ("The comparison must cover the whole
time-dependent input class [...] the following lemma uses the coherent access, certified
discretisation and source-preparation assumptions of Theorem `ode:thm:time`"), eq. `odel:eq:fixed`
and the consequence after it ("a uniform worst-case lower bound proportional to
`ḡ √s τ log(ḡ/ε)` is false under these access assumptions").

* `ReleaseValid`, `releaseValid_valid`, `single_release_class`: every instance accepted by the
  released solver `TimeDependentExtensions.ODE.solver` (the premises of its `Outcome`, at any slot
  count, under its public PSD promise) is solved by the single program (as in
  `ODELowerBoundExtensions.Dyson.dyson_release_class`);
* `single_fixed`: eq. `odel:eq:fixed` for single programs over the general access: at fixed
  `z = s Λ T` and `ḡ` the matrix queries are `O(log(1/ε)/log log(1/ε))`;
* `single_no_uniform`: for fixed `s, τ, ḡ` and every `c > 0`, single programs over the general
  access make fewer than `c ḡ √s τ log(ḡ/ε)` matrix queries for all small `ε`.
-/

namespace DysonGeneralAccess.Dyson

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set
open MeasureTheory TimeDependentExtensions ODELowerBoundExtensions.Dyson
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE)
open DysonSingleProgram DysonSingleProgram.Register Model
open scoped InnerProduct BigOperators

section Release

variable {X n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- **The instances accepted by the released solver**: `y = x(T)` for an instance meeting the
premises of `TimeDependentExtensions.ODE.Outcome` at slot count `N` (data shape `Ks = M`,
`σ = id`), as listed in `ODELowerBoundExtensions.Dyson.dyson_release_class`. -/
def ReleaseValid (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (N : ℕ) (T g ε r₀ : ℝ)
    (rb : Fin M → ℝ) (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (x : X) (y : EuclideanSpace ℂ n) : Prop :=
  ∃ (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
    (bs : Fin M → EuclideanSpace ℂ n) (bmax : ℝ),
    (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) ∧
    (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) ∧
    (∀ r : Fin M, IntervalIntegrable (b r) volume (t r) (t ((r : ℕ) + 1))) ∧
    (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ‖b r u‖ ≤ bmax) ∧
    (∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) ∧
    ‖sol 0‖ = r₀ ∧ (∀ r, ‖bs r‖ = rb r) ∧
    (sol 0 ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection (sol 0)) ∧
    (∀ r, bs r ≠ 0 → Jb x r seed = ODEStateNormalization.unitDirection (bs r)) ∧
    sol T ≠ 0 ∧
    MeshSampling.mass r₀ t rb ≤ g * ‖sol T‖ ∧
    (r₀ + bmax * T) * (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
        ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, r))‖) +
      (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖b r u - bs r‖) +
        TimeDependentExtensions.ODE.publicError D t T N r₀ rb ≤
          ε * MeshSampling.mass r₀ t rb / (2000 * g) ∧
    sol T = y

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **The released instances are valid instances** (`σ = id`): under the release's public PSD
promise on the sampled dissipative parts, with `T ≥ 0` and nonnegative mass. -/
theorem releaseValid_valid (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (N : ℕ) (T g ε r₀ : ℝ)
    (rb : Fin M → ℝ) (hT : 0 ≤ T) (hB : 0 ≤ MeshSampling.mass r₀ t rb)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (x : X) (y : EuclideanSpace ℂ n)
    (h : ReleaseValid D t N T g ε r₀ rb J₀ Jb seed x y) :
    Valid D id t T g ε r₀ rb J₀ Jb seed x y := by
  obtain ⟨G, b, sol, bs, bmax, hG, hGint, hbint, hbmax, hsol, hs0, hbs, hJ0, hJb, _, hmass,
    hcert, hy⟩ := h
  have hAcc : ∀ r : Fin M,
      Accretive (SparseStateOverlap.matrixOperator (D.matrix (x, id r))) := fun r =>
    MeshSampling.generator_accretive D (fun _ => r) hPSD x 0
  have hq := quadrature_le_publicError D t T N r₀ rb hT hB
  refine ⟨G, b, sol, bs, bmax, hG, hAcc, hGint, hbint, hbmax, hsol, hs0, hbs, hJ0, hJb, hmass,
    le_trans ?_ hcert, hy⟩
  simp only [id]
  linarith

/-- **The single program covers the released time-dependent class** (the sentence before Lemma
`odel:lem:dyson`): under the hypotheses of `ODELowerBoundExtensions.Dyson.dyson_release_class`,
one heralded program over the general access (`σ = id`) solves every instance accepted by the
released solver, at any slot count `N`, with at most `dysonBound (s Λ T) ḡ ε` matrix queries. -/
theorem single_release_class (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ)
    (T g ε r₀ : ℝ) (rb : Fin M → ℝ) (hmesh : IsMesh t M T) (hT : 0 < T) (hg : 1 ≤ g)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (h₀ : 0 ≤ r₀) (hb : ∀ r, 0 ≤ rb r)
    (hB : 0 < MeshSampling.mass r₀ t rb)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x r, IsUnitary (Jb x r))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    ∃ (J : Type) (_ : Fintype J) (G : Type) (_ : NormedAddCommGroup G)
      (_ : InnerProductSpace ℂ G) (_ : CompleteSpace G)
      (A : HeraldedSolver (fiberOracle J (oracle D (dysonDegree D T g ε) M J₀ Jb))
        (ReleaseValid D t N T g ε r₀ rb J₀ Jb seed) G ε),
      (A.prog.cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
        dysonBound (rate D * T) g ε := by
  obtain ⟨J, hJ, G, i1, i2, i3, A, hA⟩ :=
    single_dyson D hM id t T g ε r₀ rb hmesh hT hg hε hε1 h₀ hb hB J₀ Jb hJ₀ hJb seed hSeed
  exact ⟨J, hJ, G, i1, i2, i3,
    A.mono (fun x y h => releaseValid_valid D t N T g ε r₀ rb hT.le hB.le hPSD J₀ Jb seed x y h),
    hA⟩

end Release

/-- **Eq. `odel:eq:fixed` for single programs over the general access**: at fixed `z = s Λ T > 0`
and `ḡ ≥ 1` there are `C` and `ε₀ ∈ (0, 1)` such that for every `ε ∈ (0, ε₀]` and every input
satisfying the hypotheses of `ODELowerBoundExtensions.Dyson.dyson` with `rate D * T = z`, one
heralded program over the general access solves every valid instance with at most
`C log(1/ε)/log log(1/ε)` matrix queries. -/
theorem single_fixed (z g : ℝ) (hz : 0 < z) (hg : 1 ≤ g) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ {X n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
        {s Ks M : ℕ} (D : Data (X × Fin Ks) n Z s) (_ : 0 < M) (σ : Fin M → Fin Ks)
        (t : ℕ → ℝ) (T r₀ : ℝ) (rb : Fin M → ℝ) (_ : IsMesh t M T) (_ : 0 < T) (_ : 0 ≤ r₀)
        (_ : ∀ r, 0 ≤ rb r) (_ : 0 < MeshSampling.mass r₀ t rb)
        (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
        (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
        (_ : ∀ x, IsUnitary (J₀ x)) (_ : ∀ x r, IsUnitary (Jb x r))
        (seed : EuclideanSpace ℂ n) (_ : ‖seed‖ = 1), rate D * T = z →
        ∃ (J : Type) (_ : Fintype J) (G : Type) (_ : NormedAddCommGroup G)
          (_ : InnerProductSpace ℂ G) (_ : CompleteSpace G)
          (A : HeraldedSolver (fiberOracle J (oracle D (dysonDegree D T g ε) M J₀ Jb))
            (Valid D σ t T g ε r₀ rb J₀ Jb seed) G ε),
          (A.prog.cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
            C * (Real.log (1 / ε) / Real.log (Real.log (1 / ε))) := by
  obtain ⟨C, ε₀, h0, h1, hC⟩ := ODELowerBoundExtensions.Dyson.dyson_fixed z g hz hg
  refine ⟨C, ε₀, h0, h1, ?_⟩
  intro ε hε hεle X n Z _ _ _ _ _ s Ks M D hM σ t T r₀ rb hmesh hT h₀ hb hB J₀ Jb hJ₀ hJb seed
    hSeed hz'
  obtain ⟨J, hJ, G, i1, i2, i3, A, hA⟩ :=
    single_dyson D hM σ t T g ε r₀ rb hmesh hT hg hε (hεle.trans h1.le) h₀ hb hB J₀ Jb hJ₀ hJb
      seed hSeed
  rw [hz'] at hA
  exact ⟨J, hJ, G, i1, i2, i3, A, hA.trans (hC ε hε hεle)⟩

/-- **No uniform lower bound over the general access** (the consequence of eq.
`odel:eq:fixed`): for fixed sparsity `s` (every input has `s > 0`), `τ > 0`, `ḡ ≥ 1` and every
`c > 0` there is `ε₀ > 0` such that for every `ε ∈ (0, ε₀]` and every input satisfying the
hypotheses of `ODELowerBoundExtensions.Dyson.dyson` with `Λ T = τ`, one heralded program over the
general access solves every valid instance with fewer than `c ḡ √s τ log(ḡ/ε)` matrix queries. -/
theorem single_no_uniform (s : ℕ) (τ g c : ℝ) (hτ : 0 < τ) (hg : 1 ≤ g)
    (hc : 0 < c) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ {X n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
        {Ks M : ℕ} (D : Data (X × Fin Ks) n Z s) (_ : 0 < M) (σ : Fin M → Fin Ks)
        (t : ℕ → ℝ) (T r₀ : ℝ) (rb : Fin M → ℝ) (_ : IsMesh t M T) (_ : 0 < T) (_ : 0 ≤ r₀)
        (_ : ∀ r, 0 ≤ rb r) (_ : 0 < MeshSampling.mass r₀ t rb)
        (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
        (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
        (_ : ∀ x, IsUnitary (J₀ x)) (_ : ∀ x r, IsUnitary (Jb x r))
        (seed : EuclideanSpace ℂ n) (_ : ‖seed‖ = 1), D.scale * T = τ →
        ∃ (J : Type) (_ : Fintype J) (G : Type) (_ : NormedAddCommGroup G)
          (_ : InnerProductSpace ℂ G) (_ : CompleteSpace G)
          (A : HeraldedSolver (fiberOracle J (oracle D (dysonDegree D T g ε) M J₀ Jb))
            (Valid D σ t T g ε r₀ rb J₀ Jb seed) G ε),
          (A.prog.cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) <
            c * g * Real.sqrt s * τ * Real.log (g / ε) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · refine ⟨1 / 2, by norm_num, ?_⟩
    intro ε _ _ X n Z _ _ _ _ _ Ks M D
    exact absurd D.slots_pos (lt_irrefl 0)
  · obtain ⟨ε₁, hε₁, h₁⟩ := ODELowerBoundExtensions.Dyson.eventually_lt (s : ℝ) τ g c
      (Nat.cast_pos.mpr hs) hτ hg hc
    refine ⟨min ε₁ 1, lt_min hε₁ one_pos, ?_⟩
    intro ε hε hεle X n Z _ _ _ _ _ Ks M D hM σ t T r₀ rb hmesh hT h₀ hb hB J₀ Jb hJ₀ hJb seed
      hSeed hτT
    have hz : rate D * T = s * τ := by unfold rate; rw [← hτT]; ring
    obtain ⟨J, hJ, G, i1, i2, i3, A, hA⟩ :=
      single_dyson D hM σ t T g ε r₀ rb hmesh hT hg hε (hεle.trans (min_le_right _ _)) h₀ hb hB
        J₀ Jb hJ₀ hJb seed hSeed
    rw [hz] at hA
    exact ⟨J, hJ, G, i1, i2, i3, A,
      lt_of_le_of_lt hA (h₁ ε hε (hεle.trans (min_le_left _ _)))⟩

end

end DysonGeneralAccess.Dyson
