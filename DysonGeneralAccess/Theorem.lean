import DysonGeneralAccess.Valid
import ODELowerBoundExtensions.Dyson.Family.Mesh

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Lemma `odel:lem:dyson` as one heralded program over its general access

Manuscript, Lemma `odel:lem:dyson` and eq. `odel:eq:dyson`: "Assume the coherent time queries,
attainable sample accuracy and source access of Theorem `ode:thm:time`, including coherent matrix
access on every finite mesh selected from the public error certificate. Assume a supplied common
row and column Euclidean-norm bound `η` for `A(t)`." Then there is a generic sparse-oracle solver
with `Q_A = O(ḡ e^z [1 + z + L_g/log(e + L_g/z)])`, `z = s η T`, `L_g = log(C ḡ/ε)`; only matrix
queries are counted. This package assumes, as its own hypotheses, interval-integrable generator
and forcing pieces on each closed mesh cell and a classical solution on each closed cell
(`SolvesODE`: a derivative at every point of the cell, one-sided at its ends), so a generator jump
inside a cell that leaves the solution without a derivative there is not covered. The released
`ODELowerBoundExtensions.Dyson.dyson` gives the
solver as a public trial family with the complete certificate of the four-attempt retry wrapper.
Here the solver is one heralded program (`Model.HeraldedSolver`) over the same access with
spectator registers, `fiberOracle J (Dyson.oracle D K M J₀ Jb)`.

* `SingleOutcome`: one heralded single program over the general access, for the valid instances
  `Dyson.Valid` (the premises of `Dyson.Outcome`), with at most `dysonBound z ḡ ε` matrix
  queries (`cost (matrixWeight 1)`: row, column and value calls, inverses included; source
  calls are not counted; the controls of the access, Section `odel:sec:main`, are built into
  `Dyson.oracle` through its controlled workspace `NativeControlledOracle.Workspace`, and the
  program has no further controlled call);
* `single_dyson`: `SingleOutcome` under the hypotheses of `Dyson.dyson`.
-/

namespace DysonGeneralAccess.Dyson

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set
open MeasureTheory TimeDependentExtensions ODELowerBoundExtensions.Dyson
open DysonSingleProgram DysonSingleProgram.Register Model

variable {X n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s Ks : ℕ}

/-- **The outcome of Lemma `odel:lem:dyson` for one heralded program**: a spectator register
`J`, a garbage space `G` and a heralded single program over `fiberOracle J (oracle D K M J₀ Jb)`
(`K = dysonDegree`), with success at least `2/3` and conditional accuracy `ε` on every valid
instance, making at most `dysonBound (s Λ T) ḡ ε = 16000 ḡ e^z (1 + z + L_g/log(e + L_g/z))`
matrix queries, `z = s Λ T`, `L_g = log(4000 ḡ/ε)` (eq. `odel:eq:dyson`). -/
def SingleOutcome (D : Data (X × Fin Ks) n Z s) {M : ℕ} (σ : Fin M → Fin Ks) (t : ℕ → ℝ)
    (T g ε r₀ : ℝ) (rb : Fin M → ℝ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (G : Type) (_ : NormedAddCommGroup G)
    (_ : InnerProductSpace ℂ G) (_ : CompleteSpace G)
    (A : HeraldedSolver (fiberOracle J (oracle D (dysonDegree D T g ε) M J₀ Jb))
      (Valid D σ t T g ε r₀ rb J₀ Jb seed) G ε),
    (A.prog.cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
      dysonBound (rate D * T) g ε

/-- **Lemma `odel:lem:dyson`, single-program form**: for every public time-indexed native input
on a mesh with a public cell-to-sample map, every `T > 0`, `ḡ ≥ 1`, `0 < ε ≤ 1`, nonnegative
public source norms with positive mass, unitary source interfaces and a unit seed (the
hypotheses of `ODELowerBoundExtensions.Dyson.dyson`), one heralded program over the general
access solves every valid instance with at most `dysonBound (s Λ T) ḡ ε` matrix queries. -/
theorem single_dyson (D : Data (X × Fin Ks) n Z s) {M : ℕ} (hM : 0 < M) (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T g ε r₀ : ℝ) (rb : Fin M → ℝ) (hmesh : IsMesh t M T) (hT : 0 < T)
    (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) (h₀ : 0 ≤ r₀) (hb : ∀ r, 0 ≤ rb r)
    (hB : 0 < MeshSampling.mass r₀ t rb)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x r, IsUnitary (Jb x r))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    SingleOutcome D σ t T g ε r₀ rb J₀ Jb seed := by
  classical
  obtain ⟨i₀⟩ : Nonempty n := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have h0 : seed = 0 := by
      ext i
      exact isEmptyElim i
    rw [h0, norm_zero] at hSeed
    exact zero_ne_one hSeed
  have hO := oracle_unitary D (dysonDegree D T g ε) M J₀ Jb hJ₀ hJb
  by_cases hV : ∃ x y, Valid D σ t T g ε r₀ rb J₀ Jb seed x y
  · obtain ⟨x₀, y₀, hv₀⟩ := hV
    obtain ⟨q, ψ, F, a, U₁, U₂, U₃, hshape, hcert⟩ :=
      exists_shape D hM σ t T g ε r₀ rb hmesh hT hg hε hε1 h₀ hb hB J₀ Jb hJ₀ hJb seed hSeed
    have c := hcert x₀ y₀ hv₀
    refine ⟨_, _, _, _, _, _, Core.single hO q _ c.trial.cutoff_pos ψ c.trial.seed_unit F
      c.trial.output_isometry i₀ a (ODESourceQueryBudget.matrixWeight (fun _ => 1)) hshape
      (Valid D σ t T g ε r₀ rb J₀ Jb seed) (s : ℝ) 0 (shapeLength D T g ε)
      (ampFactor D t T g ε r₀ rb) ε hcert, ?_⟩
    exact (Core.single_matrix_le hO q _ c.trial.cutoff_pos ψ c.trial.seed_unit F
      c.trial.output_isometry i₀ a _ hshape _ _ _ _ _ _ hcert x₀ y₀ hv₀).trans
      (DysonSingleProgram.Explicit.bound_le_dysonBound D t T g ε r₀ rb hmesh hT hg hε hε1 h₀
        hb hB)
  · push Not at hV
    refine ⟨Unit, inferInstance,
      SparseLowerBounds.Joint Unit (DysonSpace Ks n Z (dysonDegree D T g ε) M),
      inferInstance, inferInstance, inferInstance, HeraldedSolver.trivial i₀ hV, ?_⟩
    rw [HeraldedSolver.trivial_prog, MultiOracleCircuit.Program.cost_identity, Nat.cast_zero]
    have hrate : 0 < rate D := mul_pos (Nat.cast_pos.mpr D.slots_pos) D.scale_pos
    exact ODELowerBoundExtensions.Dyson.dysonBound_nonneg (mul_pos hrate hT).le hg hε hε1

end

end DysonGeneralAccess.Dyson
