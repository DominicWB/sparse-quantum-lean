import DysonGeneralAccess.Core
import DysonSingleProgram.Theorem

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The ODE lower-bound class as a specialisation

Manuscript, Lemma `odel:lem:dyson` on the class of the ODE lower bounds
(sampled-time access `Family.access ι`, Section `odel:sec:main`). The general-access construction of
`Core` contains the single-program form of `DysonSingleProgram`:

* `fourAttempts_eq`: `DysonSingleProgram.fourAttempts` is `Core.attempts` at the access
  `F.access ι`;
* `solver_dyson_of_core`: the conclusion of `DysonSingleProgram.solver_dyson`, obtained from
  `Core.single` at `O = F.access ι` and the relation `Model.familyValid F`, the spectator map
  `Register.toAccess` (`Model.HeraldedSolver.map`) and `Model.toSolver`, without
  `DysonSingleProgram.exists_solver_of_shape`. It restates that theorem on purpose: it checks
  that the general construction contains the class of the ODE lower bounds;
* `heralded_dyson_family`: every family of the class has a heralded single program over its own
  access within the bound of eq. `odel:eq:dyson` (from `DysonSingleProgram.solver_dyson` and
  `Model.ofSolver`, which keeps the program).
-/

namespace DysonGeneralAccess.Family

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE OracleCircuit Model
open DysonSingleProgram DysonSingleProgram.Register DysonSingleProgram.Parallel

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {K s : ℕ}

/-- `DysonSingleProgram.fourAttempts` is the general four-attempt stage at the access
`F.access ι`. -/
theorem fourAttempts_eq (F : Family X N Z K s) (ι : Type) [Fintype ι] (M : ℕ)
    (a : MultiOracleCircuit.Program (F.access ι))
    {U₁ U₂ U₃ : Workspace ι N Z K →L[ℂ] Workspace ι N Z K}
    (h₁ : IsUnitary U₁) (h₂ : IsUnitary U₂) (h₃ : IsUnitary U₃) (ψ : Workspace ι N Z K)
    (out : EuclideanSpace ℂ N →L[ℂ] Workspace ι N Z K) (i₀ : N) :
    fourAttempts F ι M a h₁ h₂ h₃ ψ out i₀ = Core.attempts M a h₁ h₂ h₃ ψ out i₀ :=
  rfl

/-- **`DysonSingleProgram.solver_dyson` from the general construction**: every family of the
class `InClass η ḡ` with `η > 0` and `T > 0` has, for `ḡ ≥ 1` and `0 < ε ≤ 1`, a single-program
solver (`SparseLowerBounds.ODE.Solver`) over its own access making at most
`dysonBound (s η T) ḡ ε` calls; proved through `Core.single`, `HeraldedSolver.map` and
`toSolver`. This restates `DysonSingleProgram.solver_dyson` to check that the general
construction contains the class of the ODE lower bounds. -/
theorem solver_dyson_of_core (F : Family X N Z K s) (η gbar ε : ℝ) (hF : F.InClass η gbar)
    (hη : 0 < η) (hT : 0 < F.T) (hg : 1 ≤ gbar) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (ι : Type) (_ : Fintype ι) (G : Type) (_ : NormedAddCommGroup G)
      (_ : InnerProductSpace ℂ G) (_ : CompleteSpace G) (A : Solver ι F G ε),
      (A.prog.count : ℝ) ≤ ODELowerBoundExtensions.Dyson.dysonBound ((s : ℝ) * η * F.T) gbar ε := by
  classical
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · obtain ⟨G, i1, i2, i3, A, hA⟩ := exists_solver_of_isEmpty F ε
    refine ⟨Unit, inferInstance, G, i1, i2, i3, A, ?_⟩
    rw [hA, Nat.cast_zero]
    have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    exact ODELowerBoundExtensions.Dyson.dysonBound_nonneg
      (mul_nonneg (mul_nonneg hs hη.le) hT.le) hg hε hε1
  · obtain ⟨sol₀, hs₀, hne₀, -⟩ := hF.solution x₀
    obtain ⟨i₀, -⟩ : ∃ i, sol₀ F.T i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne₀ (by ext i; simpa using hcon i)
    obtain ⟨ι, hι, q, M, ψ, out, g', ell, a, U₁, U₂, U₃, hbound, hshape, hcert⟩ :=
      Explicit.family_dyson_grover F η gbar ε hF hη hT hg hε hε1
    have h₀ := hcert x₀ sol₀ hs₀
    have hV : ∀ x y, Model.familyValid F x y →
        ODECompleteTrial.Certificate q M ψ out x y (s : ℝ) 0 ell g' ε :=
      fun x y ⟨sol, hs, hy⟩ => hy ▸ hcert x sol hs
    let A₀ := Core.single (F.access_unitary ι) q M h₀.trial.cutoff_pos ψ h₀.trial.seed_unit out
      h₀.trial.output_isometry i₀ a (fun _ => 1) hshape (Model.familyValid F) (s : ℝ) 0 ell g' ε
      hV
    let J := (Core.attempts M a hshape.unitary₁ hshape.unitary₂ hshape.unitary₃ ψ out i₀).I ×
      Fin M
    let A₁ := A₀.map (accessLayout ι J N Z K).symm (toAccess ι J F)
      (fun p x => eval_toAccess ι J F p x)
    let A := toSolver A₁ (fun x => (hF.solution x).imp fun _ h => h.1)
    refine ⟨_, inferInstance, _, inferInstance, inferInstance, inferInstance, A, ?_⟩
    have hprog : A.prog = toAccess ι J F A₀.prog := rfl
    have hle := Core.single_matrix_le (F.access_unitary ι) q M h₀.trial.cutoff_pos ψ
      h₀.trial.seed_unit out h₀.trial.output_isometry i₀ a (fun _ => 1) hshape
      (Model.familyValid F) (s : ℝ) 0 ell g' ε hV x₀ (sol₀ F.T) ⟨sol₀, hs₀, rfl⟩
    rw [MultiOracleCircuit.Program.cost_const, mul_one] at hle
    rw [hprog, count_toAccess]
    exact hle.trans hbound

/-- **The class of the ODE lower bounds inside the general class**: every family of the class
has a heralded single program over its own access, for its valid instances, within the bound of
eq. `odel:eq:dyson`. -/
theorem heralded_dyson_family (F : Family X N Z K s) (η gbar ε : ℝ) (hF : F.InClass η gbar)
    (hη : 0 < η) (hT : 0 < F.T) (hg : 1 ≤ gbar) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (ι : Type) (_ : Fintype ι) (G : Type) (_ : NormedAddCommGroup G)
      (_ : InnerProductSpace ℂ G) (_ : CompleteSpace G)
      (A : HeraldedSolver (F.access ι) (familyValid F) G ε),
      (A.prog.count : ℝ) ≤ ODELowerBoundExtensions.Dyson.dysonBound ((s : ℝ) * η * F.T) gbar ε := by
  obtain ⟨ι, hι, G, i1, i2, i3, A, hA⟩ :=
    DysonSingleProgram.solver_dyson F η gbar ε hF hη hT hg hε hε1
  exact ⟨ι, hι, G, i1, i2, i3, Model.ofSolver A, hA⟩

end

end DysonGeneralAccess.Family
