import DysonGeneralAccess.Core
import DysonSingleProgram.Explicit.Dyson

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The valid instances of the general access of Lemma `odel:lem:dyson`

Manuscript, Lemma `odel:lem:dyson` (lines 4156-4159: coherent time queries, certified time
discretisation, the source quadrature/preparation access of Theorem `ode:thm:time`, coherent
matrix access on every finite mesh selected from the public regularity certificate) and its
proof (lines 4178-4196: mesh chosen from the certificate, Duhamel bound, public cell-to-sample
map; lines 4230-4232: supplied source quadrature preparation). The
released access is `ODELowerBoundExtensions.Dyson.oracle D K M J₀ Jb` (masked coherent
sampled-time native calls and the two supplied source interfaces) for a public time-indexed
native input `D`, mesh `t` with `M` cells, cell-to-sample map `σ`, source norms `r₀`, `rb`,
interfaces `J₀`, `Jb` and seed; an instance is valid when it meets the premises of
`ODELowerBoundExtensions.Dyson.Outcome`.

* `Valid`: `y = x(T)` for an instance on input `x` meeting the premises of `Dyson.Outcome`
  verbatim (accretive generator pieces and used samples, integrability, bounded forcing, solution
  on every cell, source norms and directions, `B ≤ ḡ ‖x(T)‖`, certified error);
* `oracle_unitary`: the access is unitary for unitary source interfaces;
* `exists_shape`: the `Valid` form of `DysonSingleProgram.Explicit.dyson_grover`: under the
  hypotheses of `Dyson.dyson`, the released Dyson trial family has the amplification shape of a
  preparation over the same access, and every valid instance carries the released complete
  certificate with target `y`.
-/

namespace DysonGeneralAccess.Dyson

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set
open MeasureTheory TimeDependentExtensions ODELowerBoundExtensions.Dyson
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE)
open DysonSingleProgram
open scoped InnerProduct BigOperators

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s Ks : ℕ}

/-- **The valid instances of the general access**: `y = x(T)` for generator pieces `G`, forcing
pieces `b`, a solution `sol`, sampled sources `bs` and a forcing bound `bmax` on input `x`
meeting the premises of `ODELowerBoundExtensions.Dyson.Outcome`. -/
def Valid (D : Data (X × Fin Ks) n Z s) {M : ℕ} (σ : Fin M → Fin Ks) (t : ℕ → ℝ)
    (T g ε r₀ : ℝ) (rb : Fin M → ℝ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (x : X) (y : EuclideanSpace ℂ n) : Prop :=
  ∃ (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
    (bs : Fin M → EuclideanSpace ℂ n) (bmax : ℝ),
    (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) ∧
    (∀ r : Fin M, Accretive (SparseStateOverlap.matrixOperator (D.matrix (x, σ r)))) ∧
    (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) ∧
    (∀ r : Fin M, IntervalIntegrable (b r) volume (t r) (t ((r : ℕ) + 1))) ∧
    (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ‖b r u‖ ≤ bmax) ∧
    (∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) ∧
    ‖sol 0‖ = r₀ ∧ (∀ r, ‖bs r‖ = rb r) ∧
    (sol 0 ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection (sol 0)) ∧
    (∀ r, bs r ≠ 0 → Jb x r seed = ODEStateNormalization.unitDirection (bs r)) ∧
    MeshSampling.mass r₀ t rb ≤ g * ‖sol T‖ ∧
    (r₀ + bmax * T) * (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
        ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, σ r))‖) +
      (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖b r u - bs r‖) +
      (s : ℝ) * D.scale * (∑ q : Fin M, (t ((q : ℕ) + 1) - t q) ^ 2 * rb q) / 2 ≤
        ε * MeshSampling.mass r₀ t rb / (2000 * g) ∧
    sol T = y

omit [DecidableEq Z] in
/-- **The general access is unitary** for unitary source interfaces. -/
theorem oracle_unitary (D : Data (X × Fin Ks) n Z s) (K M : ℕ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x r, IsUnitary (Jb x r)) :
    ∀ l x, IsUnitary (oracle D K M J₀ Jb l x) :=
  fun l x => ODECoordinateNativeControl.physicalOracle_unitary _ _ _ _
    (ODELowerBoundExtensions.Dyson.matrixOracle_unitary (Omega K M) D)
    (TimeDependentODE.SourceTD.sourceFamily_unitary J₀ Jb hJ₀ hJb) l x

/-- **The released Dyson trials with their shape, on the valid instances** (the `Valid` form of
`DysonSingleProgram.Explicit.dyson_grover`): under the hypotheses
of `ODELowerBoundExtensions.Dyson.dyson`, there are a trial family `q`, seed `ψ` and output `F`
over the general access with the amplification shape of a preparation `a` over the same access
(matrix counts), and every valid instance `(x, y)` carries the released complete certificate
with cutoff `chosenIterations g'`, `g' = ampFactor`, `Θ = 0`, `ℓ = shapeLength` and target `y`. -/
theorem exists_shape (D : Data (X × Fin Ks) n Z s) {M : ℕ} (hM : 0 < M) (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T g ε r₀ : ℝ) (rb : Fin M → ℝ) (hmesh : IsMesh t M T) (hT : 0 < T)
    (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) (h₀ : 0 ≤ r₀) (hb : ∀ r, 0 ≤ rb r)
    (hB : 0 < MeshSampling.mass r₀ t rb)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x r, IsUnitary (Jb x r))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    ∃ (q : ℕ → MultiOracleCircuit.Program (oracle D (dysonDegree D T g ε) M J₀ Jb))
      (ψ : DysonSpace Ks n Z (dysonDegree D T g ε) M)
      (F : EuclideanSpace ℂ n →L[ℂ] DysonSpace Ks n Z (dysonDegree D T g ε) M)
      (a : MultiOracleCircuit.Program (oracle D (dysonDegree D T g ε) M J₀ Jb))
      (U₁ U₂ U₃ : DysonSpace Ks n Z (dysonDegree D T g ε) M →L[ℂ]
        DysonSpace Ks n Z (dysonDegree D T g ε) M),
      GroverShape q (ODESourceQueryBudget.matrixWeight (fun _ => 1)) a
        (ODESourceQueryBudget.matrixWeight (fun _ => 1)) U₁ U₂ U₃ ∧
      ∀ x y, Valid D σ t T g ε r₀ rb J₀ Jb seed x y →
        ODECompleteTrial.Certificate q
          (ODEGroverAverage.chosenIterations (ampFactor D t T g ε r₀ rb)) ψ F x y
          (s : ℝ) 0 (shapeLength D T g ε) (ampFactor D t T g ε r₀ rb) ε := by
  obtain ⟨q, ψ, F, a, U₁, U₂, U₃, hshape, -, hcert⟩ :=
    DysonSingleProgram.Explicit.dyson_grover D hM σ t T g ε r₀ rb hmesh hT hg hε hε1 h₀ hb hB
      J₀ Jb hJ₀ hJb seed hSeed
  refine ⟨q, ψ, F, a, U₁, U₂, U₃, hshape, ?_⟩
  rintro x y ⟨G, b, sol, bs, bmax, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, rfl⟩
  exact hcert x G b sol bs bmax h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

end

end DysonGeneralAccess.Dyson
