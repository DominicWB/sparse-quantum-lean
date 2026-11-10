import DysonSingleProgram.Solver

set_option autoImplicit false

/-!
# Heralded single programs over a general access

Manuscript, Section `odel:sec:main` (output model, one heralded run with success
at least `2/3` and conditional accuracy `ε`) and Lemma `odel:lem:dyson` (a generic
sparse-oracle solver under the coherent access of Theorem `ode:thm:time`). The single-program class
of the ODE lower bounds, `SparseLowerBounds.ODE.Solver`, is tied to the sampled-time access
`Family.access ι` and to the solutions of a family. `HeraldedSolver O Valid G ε` is the same class
over an arbitrary oracle family `O` and a relation `Valid x y` ("`y` is the target of a valid
instance on input `x`"): one program over `O`, an input-independent seed of norm at most one, an
isometric readout onto system ⊗ garbage `G`, an input-independent herald projection, success at
least `2/3` and conditional accuracy `ε` (`Readout.HeraldedAccurate`) for `y/‖y‖` on every valid
instance.

* `familyValid`, `ofSolver`, `toSolver`: `SparseLowerBounds.ODE.Solver ι F G ε` is the class at
  the access `F.access ι` and the relation "`y = x(T)` for a solution", when every input has a
  solution;
* `HeraldedSolver.mono`: fewer valid instances keep a solver;
* `HeraldedSolver.map`: a program map conjugating evaluations by a fixed isometric equivalence
  transports a solver, with the transported program;
* `HeraldedSolver.trivial`: without valid instances the identity program is a solver.
-/

namespace DysonGeneralAccess.Model

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE OracleCircuit
open scoped InnerProduct InnerProductSpace

/-- **A heralded single program over the access `O`** at accuracy `ε` for the valid instances
`Valid`: one program, a seed of norm at most one, an isometric readout onto system `ℂ^N` ⊗
garbage `G`, a herald projection; on every valid instance `(x, y)` success probability at least
`2/3` and conditional accuracy `ε` for `y/‖y‖` (`Readout.HeraldedAccurate`). -/
structure HeraldedSolver {X L W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] (O : L → X → W →L[ℂ] W) {N : Type*} [Fintype N] [DecidableEq N]
    (Valid : X → EuclideanSpace ℂ N → Prop) (G : Type*) [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] (ε : ℝ) where
  /-- The query algorithm. -/
  prog : MultiOracleCircuit.Program O
  /-- The input-independent seed. -/
  seed : W
  seed_norm_le : ‖seed‖ ≤ 1
  /-- The readout isometry onto system ⊗ garbage. -/
  out : W →L[ℂ] SysGarb N G
  out_isometry : out† ∘L out = 1
  /-- The input-independent success flag. -/
  herald : W →L[ℂ] W
  herald_proj : IsStarProjection herald
  success : ∀ x y, Valid x y → 2 / 3 ≤ ‖herald (prog.eval x seed)‖ ^ 2
  accurate : ∀ x y, Valid x y →
    Readout.HeraldedAccurate out herald (prog.eval x seed)
      (ODEStateNormalization.unitDirection y) ε

variable {X L W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  {O : L → X → W →L[ℂ] W} {N : Type*} [Fintype N] [DecidableEq N]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] {ε : ℝ}

/-- **Fewer valid instances**: a solver for `Valid` is a solver for every `Valid' ⊆ Valid`, with
the same program. -/
def HeraldedSolver.mono {Valid Valid' : X → EuclideanSpace ℂ N → Prop}
    (A : HeraldedSolver O Valid G ε) (h : ∀ x y, Valid' x y → Valid x y) :
    HeraldedSolver O Valid' G ε where
  prog := A.prog
  seed := A.seed
  seed_norm_le := A.seed_norm_le
  out := A.out
  out_isometry := A.out_isometry
  herald := A.herald
  herald_proj := A.herald_proj
  success := fun x y hv => A.success x y (h x y hv)
  accurate := fun x y hv => A.accurate x y (h x y hv)

/-- **Transport along a program map**: if `f` maps programs over `O` to programs over `O'` whose
evaluations are the `Φ`-conjugates, a solver over `O` gives a solver over `O'` with program
`f A.prog`, seed `Φ A.seed`, herald `Φ P Φ⁻¹` and readout `e ∘ Φ⁻¹`. -/
def HeraldedSolver.map {L' W' : Type*} [NormedAddCommGroup W'] [InnerProductSpace ℂ W']
    [CompleteSpace W'] {O' : L' → X → W' →L[ℂ] W'} {Valid : X → EuclideanSpace ℂ N → Prop}
    (A : HeraldedSolver O Valid G ε) (Φ : W ≃ₗᵢ[ℂ] W')
    (f : MultiOracleCircuit.Program O → MultiOracleCircuit.Program O')
    (hf : ∀ p x, (f p).eval x = Φ.conjStarAlgEquiv (p.eval x)) :
    HeraldedSolver O' Valid G ε where
  prog := f A.prog
  seed := Φ A.seed
  seed_norm_le := by rw [LinearIsometryEquiv.norm_map]; exact A.seed_norm_le
  out := A.out ∘L Φ.symm.toLinearIsometry.toContinuousLinearMap
  out_isometry := DysonSingleProgram.comp_isometryEquiv_isometry A.out A.out_isometry Φ.symm
  herald := Φ.conjStarAlgEquiv A.herald
  herald_proj := by
    have h := DysonSingleProgram.isStarProjection_conj_isometryEquiv Φ.symm A.herald_proj
    rwa [LinearIsometryEquiv.symm_symm] at h
  success := fun x y hv => by
    rw [hf, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.norm_map]
    exact A.success x y hv
  accurate := fun x y hv => by
    have key : (f A.prog).eval x (Φ A.seed) = Φ (A.prog.eval x A.seed) := by
      rw [hf, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
        LinearIsometryEquiv.symm_apply_apply]
    rw [key]
    have h := DysonSingleProgram.heraldedAccurate_isometryEquiv A.out A.herald
      (A.prog.eval x A.seed) _ ε Φ.symm (A.accurate x y hv)
    rwa [LinearIsometryEquiv.symm_symm] at h

/-- The transported solver runs the mapped program. -/
@[simp] theorem HeraldedSolver.map_prog {L' W' : Type*} [NormedAddCommGroup W']
    [InnerProductSpace ℂ W'] [CompleteSpace W'] {O' : L' → X → W' →L[ℂ] W'}
    {Valid : X → EuclideanSpace ℂ N → Prop} (A : HeraldedSolver O Valid G ε) (Φ : W ≃ₗᵢ[ℂ] W')
    (f : MultiOracleCircuit.Program O → MultiOracleCircuit.Program O')
    (hf : ∀ p x, (f p).eval x = Φ.conjStarAlgEquiv (p.eval x)) :
    (A.map Φ f hf).prog = f A.prog := rfl

/-- **Without valid instances** the identity program (seed `0`, herald `0`, readout onto the
system index `i₀` with garbage `W`) is a solver. -/
def HeraldedSolver.trivial {Valid : X → EuclideanSpace ℂ N → Prop} (i₀ : N)
    (hV : ∀ x y, ¬ Valid x y) : HeraldedSolver O Valid W ε where
  prog := MultiOracleCircuit.Program.identity
  seed := 0
  seed_norm_le := by simp
  out := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : N => W)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun i => if i = i₀ then 1 else 0
  out_isometry := by
    ext1 v
    refine ext_inner_left ℂ fun w => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      PiLp.inner_apply, Finset.sum_eq_single i₀ (fun b _ hb => by simp [hb]) (by simp)]
    simp
  herald := 0
  herald_proj := IsStarProjection.zero _
  success := fun x y h => (hV x y h).elim
  accurate := fun x y h => (hV x y h).elim

/-- The trivial solver runs the identity program. -/
@[simp] theorem HeraldedSolver.trivial_prog {Valid : X → EuclideanSpace ℂ N → Prop} (i₀ : N)
    (hV : ∀ x y, ¬ Valid x y) :
    (HeraldedSolver.trivial (O := O) (ε := ε) i₀ hV).prog =
      MultiOracleCircuit.Program.identity := rfl

section Family

variable {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {K s : ℕ}

/-- **The valid instances of a family**: `y = x(T)` for a solution on input `x`. -/
def familyValid (F : Family X N Z K s) (x : X) (y : EuclideanSpace ℂ N) : Prop :=
  ∃ sol, F.Solves x sol ∧ sol F.T = y

/-- **The class of the ODE lower bounds is contained**: a `SparseLowerBounds.ODE.Solver` is a
heralded single program over `F.access ι` for the family's valid instances. -/
def ofSolver {ι : Type*} [Fintype ι] {F : Family X N Z K s} (A : Solver ι F G ε) :
    HeraldedSolver (F.access ι) (familyValid F) G ε where
  prog := A.prog
  seed := A.seed
  seed_norm_le := A.seed_norm_le
  out := A.out
  out_isometry := A.out_isometry
  herald := A.herald
  herald_proj := A.herald_proj
  success := fun x _ _ => A.success x
  accurate := fun x _ ⟨sol, hs, hy⟩ => hy ▸ A.accurate x sol hs

/-- **The converse specialisation**: when every input has a solution, a heralded single program
over `F.access ι` for the family's valid instances is a `SparseLowerBounds.ODE.Solver` with the
same program. -/
def toSolver {ι : Type*} [Fintype ι] {F : Family X N Z K s}
    (A : HeraldedSolver (F.access ι) (familyValid F) G ε) (hsol : ∀ x, ∃ sol, F.Solves x sol) :
    Solver ι F G ε where
  prog := A.prog
  seed := A.seed
  seed_norm_le := A.seed_norm_le
  out := A.out
  out_isometry := A.out_isometry
  herald := A.herald
  herald_proj := A.herald_proj
  success := fun x => (hsol x).elim fun sol hs => A.success x _ ⟨sol, hs, rfl⟩
  accurate := fun x sol hs => A.accurate x _ ⟨sol, hs, rfl⟩

/-- `toSolver` keeps the program. -/
@[simp] theorem toSolver_prog {ι : Type*} [Fintype ι] {F : Family X N Z K s}
    (A : HeraldedSolver (F.access ι) (familyValid F) G ε) (hsol : ∀ x, ∃ sol, F.Solves x sol) :
    (toSolver A hsol).prog = A.prog := rfl

end Family

end

end DysonGeneralAccess.Model
