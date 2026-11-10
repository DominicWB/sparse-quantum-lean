import SparseLowerBounds.ODE.JointAdversary

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The piecewise-constant dissipative ODE class with sampled-time access

Manuscript: Section `odel:sec:main`. The equation is
`ẋ = A(t) x + b(t)`, `x(0) = x₀`, `0 ≤ t ≤ T`, with `-A = D + iH`, `D ⪰ 0`.
In the release's convention (`TimeDependentODE.SolvesODE`) this is
`ẋ = -G(t) x + b(t)` with the **generator** `G = -A`, and `D ⪰ 0` is
`TimeDependentODE.Accretive G` (`0 ≤ Re ⟪v, G v⟫`).

**The class (`Family`, `Family.InClass`).** A family of instances indexed by
the hidden input `x : X` is given by

* `K` stages with public durations `len k ≥ 0`; stage `k` occupies `[start k, start (k+1)]`,
  `start k = Σ_{i<k} len i`, and `T = start K` ("The time-dependent examples are piecewise constant
  with known breakpoints", Section `odel:sec:main`);
* the **sampled-time sparse input** `data : NativeSparseBlockEncoding.Data (X × Fin K) N Z s`,
  whose matrix `data.matrix (x, k)` is the generator `G_k(x)` of stage `k`
  (the convention `G̃_r = D.matrix (x, r)` of the released solvers
  `TimeDependentODE.solver` and `TimeDependentExtensions.ODE.solver`, with the
  time address being the stage index);
  row/column sparsity at most `s` is built into `Data` (`row_sparsity_le`,
  `col_sparsity_le`); all unknown information is in the exact finite-word
  table (Section `odel:sec:main`);
* public stage sources `src k` and a public initial state `init` ("Initial and source preparations
  contain no hidden information", Section `odel:sec:main`; known state preparations are free,
  Section `odel:sec:main`).

`sol` solves instance `x` (`Solves`) if `sol 0 = init` and, on every closed
stage interval, `sol` satisfies the release's `SolvesODE` with the stage's
constant generator and source. The promises of the class (`InClass η ḡ`):
accretive generators (`D ⪰ 0`), row and column Euclidean norms at most `η`
(`τ = T η`), and a nonzero solution with `B ≤ ḡ ‖x(T)‖`, `B = ‖x₀‖ + ∫‖b‖`
(`mass`), i.e. `g = B/‖x(T)‖ ≤ ḡ` (eq. `odel:eq:params`). The general-mesh
solver `TimeDependentExtensions.ODE.solver` states the same promise as
`MeshSampling.mass r₀ t rb ≤ g * ‖sol T‖`, which is `mass` for the breakpoints
`t = start`, `r₀ = ‖init‖` and `rb k = ‖src k‖` (the uniform-mesh
`PublicSource.mass` is a quadrature of `B`).

**Access (`access`).** One call of label `l : Query` on input `x` is the
coherent sampled-time oracle `Σ_{(i,k)} |i,k⟩⟨i,k| ⊗ O_l(x, k)` (the release's
`TimeDependentODE.labelOracle` of the native primitives
`NativeSparseBlockEncoding.oracles` with `TimeDependentODE.sample`), the branch
register `ι` being an untouched spectator; inverses are `queryAdjoint` and all
calls are counted (Section `odel:sec:main`). The released solvers query the same
primitives through other fixed flattenings (`ODENativeCayley.oracle`) with
spectator registers; there is no Lean transport between the two forms.

**Controlled calls** (Section `odel:sec:main`, "including inverses, controls and coherent time
addresses where needed"; the construction before Theorem `odel:thm:joint`).
`MultiOracleCircuit.Program` has no controlled primitive; controlled calls are
covered by reduction, as for the Hamiltonian lower bound
(`Hamiltonian/Statements`, `Hamiltonian/Theorem`).
A controlled locator call is a fixed gate: the hard families have input- and
stage-independent locators (`jointData_locators_const`; `hamData` keeps the
input-independent locators of the Hamiltonian lower bound), so it costs `0`. A
controlled value call is one value call between fixed controlled swaps that, on
the inactive branch, route the word register to a dummy word register held in
the uniform superposition `Σ_z |z⟩/√|Z|`, which every shift `z ↦ z - w` of the
value oracle leaves invariant (including the zero shift of the idle and source
stages, see `access_value_apply`; the release's
`NativeControlledOracle.referenceSwap` pattern). Because `Family.Forces`
quantifies over every branch register `ι : Type`, all bounds of `ODE/*` apply to
solvers with controlled calls, with spectator `ι × Fin 2 × Z`, at cost `1` per
controlled value call. There is no Lean lemma for this step (as for the
Hamiltonian lower bound).

**Solvers (`Solver`, `Forces`).** The output model is the heralded readout model
of the Hamiltonian lower bound (`Readout.HeraldedAccurate`, `Query/Readout`): a
program over `access ι F`, a seed of norm at most one, an isometric readout
`e : W → ℂ^N ⊗ G`, a herald projection with success probability at least `2/3`
on every input, and conditional accuracy `ε` (observable form of trace distance)
for the normalised solution `x(T)/‖x(T)‖` of every solution (Section `odel:sec:main`).
As in the release's `TimeDependentODE.Outcome`, accuracy is required for every
solution; the promise `InClass` gives one, and `ODE/Uniqueness` shows there is
only one endpoint, so this is the paper's requirement.
-/

namespace SparseLowerBounds.ODE

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open scoped InnerProduct InnerProductSpace

/-- **A piecewise-constant family of the dissipative ODE class with sampled-time
sparse access** (Section `odel:sec:main`): `K` public stages, the sampled-time native
input whose matrix `data.matrix (x, k)` is the generator `G_k(x) = -A_k(x)`,
public stage sources and a public initial state. -/
structure Family (X N Z : Type*) [Fintype N] [DecidableEq N] (K s : ℕ) where
  /-- The sampled-time sparse input: `data.matrix (x, k)` is `G_k(x)`. -/
  data : Data (X × Fin K) N Z s
  /-- Public stage durations. -/
  len : Fin K → ℝ
  len_nonneg : ∀ k, 0 ≤ len k
  /-- Public stage sources `b_k`. -/
  src : Fin K → EuclideanSpace ℂ N
  /-- Public initial state `x₀`. -/
  init : EuclideanSpace ℂ N

namespace Family

variable {X N Z : Type*} [Fintype N] [DecidableEq N] {K s : ℕ} (F : Family X N Z K s)

/-- The duration of stage `i`, extended by `0` beyond the last stage. -/
def lenNat (i : ℕ) : ℝ := if h : i < K then F.len ⟨i, h⟩ else 0

/-- The breakpoint `t_k = Σ_{i<k} len i` (stage `k` is `[start k, start (k+1)]`). -/
def start (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, F.lenNat i

/-- The final time `T = t_K`. -/
def T : ℝ := F.start K

/-- The generator `G_k(x) = -A_k(x)` of stage `k` on input `x`: the operator of
the matrix the oracle encodes. -/
def gen (x : X) (k : Fin K) : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N :=
  SparseStateOverlap.matrixOperator (F.data.matrix (x, k))

/-- The source mass `B = ‖x₀‖ + ∫₀ᵀ ‖b‖` (eq. `odel:eq:params`). -/
def mass : ℝ := ‖F.init‖ + ∑ k, F.len k * ‖F.src k‖

/-- **`sol` solves instance `x`**: `sol 0 = x₀` and, on every closed stage
interval `[t_k, t_{k+1}]`, the release's `SolvesODE` with the stage's constant
generator and source. -/
def Solves (x : X) (sol : ℝ → EuclideanSpace ℂ N) : Prop :=
  sol 0 = F.init ∧ ∀ k : Fin K, TimeDependentODE.SolvesODE (fun _ => F.gen x k)
    (fun _ => F.src k) sol (F.start k) (F.start ((k : ℕ) + 1))

theorem lenNat_of_lt (k : Fin K) : F.lenNat k = F.len k := by
  rw [lenNat, dif_pos k.2]

theorem lenNat_nonneg (i : ℕ) : 0 ≤ F.lenNat i := by
  unfold lenNat; split_ifs with h
  · exact F.len_nonneg _
  · exact le_rfl

@[simp] theorem start_zero : F.start 0 = 0 := by simp [start]

theorem start_succ (k : ℕ) : F.start (k + 1) = F.start k + F.lenNat k := by
  rw [start, start, Finset.sum_range_succ]

/-- `t_{k+1} = t_k + len k` for a stage `k`. -/
theorem start_succ_fin (k : Fin K) : F.start ((k : ℕ) + 1) = F.start k + F.len k := by
  rw [start_succ, lenNat_of_lt]

theorem start_le_start_succ (k : ℕ) : F.start k ≤ F.start (k + 1) := by
  rw [start_succ]; linarith [F.lenNat_nonneg k]

theorem start_mono {k k' : ℕ} (h : k ≤ k') : F.start k ≤ F.start k' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (F.start_le_start_succ _)

theorem start_nonneg (k : ℕ) : 0 ≤ F.start k := by
  simpa using F.start_mono (Nat.zero_le k)

theorem T_eq_start : F.T = F.start K := rfl

/-- `T = Σ_k len k`. -/
theorem T_eq_sum : F.T = ∑ k, F.len k := by
  rw [T, start, Finset.sum_range]
  exact Finset.sum_congr rfl fun k _ => F.lenNat_of_lt k

theorem T_nonneg : 0 ≤ F.T := F.start_nonneg K

/-- **Row sparsity at most `s`** (Section `odel:sec:main`): the nonzeros of a row lie in its
`s`-slot location list. -/
theorem row_sparsity_le (y : X × Fin K) (i : N) :
    (Finset.univ.filter fun j => F.data.matrix y i j ≠ 0).card ≤ s := by
  classical
  calc (Finset.univ.filter fun j => F.data.matrix y i j ≠ 0).card
      ≤ (Finset.univ.image (F.data.rowloc y i)).card :=
        Finset.card_le_card fun j hj => F.data.row_covers y i j (Finset.mem_filter.mp hj).2
    _ ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_image_le
    _ = s := by simp

/-- **Column sparsity at most `s`** (Section `odel:sec:main`). -/
theorem col_sparsity_le (y : X × Fin K) (j : N) :
    (Finset.univ.filter fun i => F.data.matrix y i j ≠ 0).card ≤ s := by
  classical
  calc (Finset.univ.filter fun i => F.data.matrix y i j ≠ 0).card
      ≤ (Finset.univ.image (F.data.colloc y j)).card :=
        Finset.card_le_card fun i hi => F.data.column_covers y i j (Finset.mem_filter.mp hi).2
    _ ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_image_le
    _ = s := by simp

end Family

/-- **The promises of the class** (Section `odel:sec:main`) with row/column Euclidean
norm bound `η` and normalisation bound `ḡ`: every stage generator is accretive
(`-A = D + iH`, `D ⪰ 0`), every row and column of every sampled matrix has
Euclidean norm at most `η`, and every instance has a solution with
`x(T) ≠ 0` and `B ≤ ḡ ‖x(T)‖` (`g = B/‖x(T)‖ ≤ ḡ`). -/
structure Family.InClass {X N Z : Type*} [Fintype N] [DecidableEq N] {K s : ℕ}
    (F : Family X N Z K s) (η gbar : ℝ) : Prop where
  accretive : ∀ x k, TimeDependentODE.Accretive (F.gen x k)
  row_norm : ∀ x k i, ∑ j, ‖F.data.matrix (x, k) i j‖ ^ 2 ≤ η ^ 2
  col_norm : ∀ x k j, ∑ i, ‖F.data.matrix (x, k) i j‖ ^ 2 ≤ η ^ 2
  solution : ∀ x, ∃ sol, F.Solves x sol ∧ sol F.T ≠ 0 ∧ F.mass ≤ gbar * ‖sol F.T‖

/-- The workspace of the sampled-time access: branch register `ι`, time address
`Fin K`, and the release's native address/value/flag space. -/
abbrev Workspace (ι N Z : Type*) [Fintype N] [Fintype Z] (K : ℕ) : Type _ :=
  Joint (ι × Fin K) (SparseFlagEmbedding.Space (N × N) Z)

namespace Family

variable {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {K s : ℕ}

/-- **The sampled-time matrix oracle** (Section `odel:sec:main`): label `l` on input `x`
is the release's coherent query `Σ_{(i,k)} |i,k⟩⟨i,k| ⊗ O_l(x, k)`
(`TimeDependentODE.labelOracle` with `TimeDependentODE.sample`), branch `ι` a
spectator. -/
abbrev access (ι : Type*) (F : Family X N Z K s) :
    Query → X → Workspace ι N Z K →L[ℂ] Workspace ι N Z K :=
  TimeDependentODE.labelOracle (oracles F.data) (TimeDependentODE.sample (ι := ι) (M := K))

theorem access_unitary (ι : Type*) [Fintype ι] (F : Family X N Z K s) (l : Query) (x : X) :
    IsUnitary (F.access ι l x) :=
  TimeDependentODE.labelOracle_unitary _ (oracles_unitary F.data) _ l x

end Family

/-- **A solver for the family `F` at accuracy `ε`** (Section `odel:sec:main`): a program
over the sampled-time access with branch register `ι`, a seed of norm at most
one, an isometric readout onto system `ℂ^N` ⊗ garbage `G`, and a herald
projection; success probability at least `2/3` on every input and, for every
solution, conditional accuracy `ε` (observable form of trace distance,
`Readout.HeraldedAccurate`) for `x(T)/‖x(T)‖`. -/
structure Solver {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
    {K s : ℕ} (ι : Type*) [Fintype ι] (F : Family X N Z K s) (G : Type*)
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (ε : ℝ) where
  /-- The query algorithm. -/
  prog : MultiOracleCircuit.Program (F.access ι)
  /-- The input-independent seed. -/
  seed : Workspace ι N Z K
  seed_norm_le : ‖seed‖ ≤ 1
  /-- The readout isometry onto system ⊗ garbage. -/
  out : Workspace ι N Z K →L[ℂ] SysGarb N G
  out_isometry : out† ∘L out = 1
  /-- The input-independent success flag. -/
  herald : Workspace ι N Z K →L[ℂ] Workspace ι N Z K
  herald_proj : IsStarProjection herald
  success : ∀ x, 2 / 3 ≤ ‖herald (prog.eval x seed)‖ ^ 2
  accurate : ∀ x sol, F.Solves x sol →
    Readout.HeraldedAccurate out herald (prog.eval x seed)
      (ODEStateNormalization.unitDirection (sol F.T)) ε

/-- **`F` forces `b` matrix queries at accuracy `ε`**: every solver, with any
branch register and any garbage space, makes at least `b` value queries, hence
at least `b` matrix queries in total. -/
def Family.Forces {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
    {K s : ℕ} (F : Family X N Z K s) (ε b : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : Type) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (A : Solver ι F G ε),
    b ≤ A.prog.labelCount .value ∧ b ≤ A.prog.count

/-- **`F` witnesses the bound `b`** for the parameters `(τ, ḡ, ε)` of the class:
`F` is in the class with `η = 1` and `T = τ` (so `τ = T η`) and `g ≤ ḡ`, and
forces `b` matrix queries at accuracy `ε`. -/
structure Family.Witnesses {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] {K s : ℕ} (F : Family X N Z K s) (τ gbar ε b : ℝ) : Prop where
  inClass : F.InClass 1 gbar
  time_eq : F.T = τ
  forces : F.Forces ε b

/-- A witness of `b` witnesses every smaller bound `b' ≤ b`. -/
theorem Family.Witnesses.mono {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] {K s : ℕ} {F : Family X N Z K s} {τ gbar ε b b' : ℝ}
    (hW : F.Witnesses τ gbar ε b) (hb : b' ≤ b) : F.Witnesses τ gbar ε b' :=
  ⟨hW.inClass, hW.time_eq, fun ι _ G _ _ _ A =>
    ⟨hb.trans (hW.forces ι G A).1, hb.trans (hW.forces ι G A).2⟩⟩

/-- `G = iH` as an operator: `matrixOperator (i • H) = i • matrixOperator H`. -/
theorem matrixOperator_I_smul {N : Type*} [Fintype N] [DecidableEq N] (H : Matrix N N ℂ) :
    SparseStateOverlap.matrixOperator (Complex.I • H) =
      Complex.I • SparseStateOverlap.matrixOperator H := by
  rw [Hamiltonian.matrixOperator_eq_toEuclideanCLM, Hamiltonian.matrixOperator_eq_toEuclideanCLM,
    map_smul]

/-- `iH` is accretive for Hermitian `H` (`D = 0`, Section `odel:sec:main`): `Re ⟪v, iHv⟫ = 0`. -/
theorem accretive_I_smul {N : Type*} [Fintype N] [DecidableEq N] {H : Matrix N N ℂ}
    (hH : H.IsHermitian) :
    TimeDependentODE.Accretive (SparseStateOverlap.matrixOperator (Complex.I • H)) := by
  intro v
  have hsa : IsSelfAdjoint (SparseStateOverlap.matrixOperator H) :=
    Hamiltonian.star_matrixOperator_of_isHermitian hH
  have him : (⟪v, SparseStateOverlap.matrixOperator H v⟫_ℂ).im = 0 :=
    hsa.isSymmetric.im_inner_self_apply v
  rw [matrixOperator_I_smul]
  show 0 ≤ (⟪v, Complex.I • SparseStateOverlap.matrixOperator H v⟫_ℂ).re
  rw [inner_smul_right, Complex.mul_re, Complex.I_re, Complex.I_im, him]
  simp

end

end SparseLowerBounds.ODE
end
