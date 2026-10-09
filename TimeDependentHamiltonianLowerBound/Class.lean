import TimeDependentHamiltonianLowerBound.Constant
import IntegrablePathSimulation.Hamiltonian.Theorem
import SparseLowerBounds.Hamiltonian.ReleaseForm

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The time-dependent classes and the constant hard paths

The hypotheses and guarantees of the three released time-dependent Hamiltonian theorems,
bundled as predicates, and the membership of constant data with constant paths in these
classes with `β = δ_val = 0` (the remark after Theorem `hs:thm:time`, paragraph "Regularity and
coherent parameters": "its time-independent hard instances satisfy the new assumptions with
`β = δ_val = 0`").

* Uniform mesh, `SparseHamiltonian.TimeDependent.simulation` (Theorem `hs:thm:time`):
  `UniformHyp D Hpath η t β δ ε` collects its sixteen hypotheses on the samples, the path and
  the public parameters; `UniformGuarantee run ι Hpath t ε` is its error criterion for an
  evaluation family `run` (for a program, `p.eval`) and an encoding `ι`: for every instance and
  every propagator `U` of the path (`U 0 = 1`, `TimeDependent.SolvesOn` on `[0, t]`),
  `‖run x ∘ ι - ι ∘ U(t)‖ ≤ ε`. `UniformHyp.simulation` is the released theorem in these terms.
* General meshes, `TimeDependentExtensions.Hamiltonian.simulation` (generalisations after
  `hs:thm:time`): `MeshHyp D t η T ε N` (mesh, slot conditions, sample promises), `MeshPath`
  (one Hermitian, interval-integrable piece per interval, integrated certificate at most
  `ε/9`) and `MeshGuarantee`; `MeshHyp.simulation`.
* Integrable paths, `IntegrablePathSimulation.Hamiltonian.simulation`: the same `MeshHyp`,
  `IntegrablePath` (Hermitian almost everywhere, interval integrable, certificate at most
  `ε/9`) and `IntegrableGuarantee` (every integral-sense propagator);
  `MeshHyp.simulation_integrable`.

**Membership.** For data with Hermitian instances and row and column norms at most `η`, the
constant data `constData D M` with the constant path `constPath D` satisfy `UniformHyp` for all
`β, δ ≥ 0` under the public mesh conditions (`uniformHyp_const`; `β = δ = 0` in
`uniformHyp_const_zero`), `MeshHyp` on every admissible mesh (`meshHyp_const`), and the constant
pieces and the constant path satisfy `MeshPath` and `IntegrablePath` with certificate `0`
(`meshPath_const`, `integrablePath_const`): every Lipschitz bound, sample error and integrated
sample error vanishes. For the hard families (`SparseLowerBounds.Hamiltonian.HardInstance`) with
`η = 1`: `uniformHyp_hard`, `meshHyp_hard`.

**Criteria on one path.** `UniformGuarantee run ι Hpath t ε` is already a criterion for one
path; `MeshCriterion run ι Hpath t M T ε` (every piecewise propagator of the path on the mesh
intervals) and `IntegrableCriterion run ι Hpath T ε` (every integral-sense propagator) are
the general-mesh and integrable criteria for one path. On the constant path each of the three
criteria is equivalent to the endpoint error against `exp(-iτH_x)` used by the released lower
bounds (`uniform_criterion_iff`, `mesh_criterion_iff` on a mesh, `integrable_criterion_iff`;
`endpoint_of_mesh` on any `t`), since every propagator of a constant path is `constProp`
(`propagator_constPath_eq`, `isPropagator_constPath_eq`, and the released gluing
`IntegrablePathSimulation.Propagator.isPropagator_glue` for piecewise propagators).

**Class membership used.** A guarantee for every path of a class gives the criterion on the
constant path, through the membership lemmas (`uniformGuarantee_const`,
`MeshGuarantee.criterion_const`, `IntegrableGuarantee.criterion_const`).
-/

namespace TimeDependentHamiltonianLowerBound

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open MeasureTheory Set
open TimeDependentExtensions (IsMesh)
open IntegrablePathSimulation.Propagator (IsPropagator)
open scoped InnerProduct InnerProductSpace

section Defs

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s M : ℕ}

/-! ### Uniform meshes -/

/-- **The hypotheses of Theorem `hs:thm:time` on a uniform mesh**
(`TimeDependent.simulation`): positive norm bound `η`, time `t ≥ 0`, Lipschitz constant
`β ≥ 0`, precision `0 < ε ≤ 1/2`, `M > 0` slots with the mesh conditions `4 s η t ≤ M`,
`9 β t² ≤ ε M` and `9 (√s η t)³ ≤ ε M²`; Hermitian samples with row and column norms at most
`η`; a Hermitian path on `[0, t]` with operator-norm Lipschitz bound `β`; sample errors
`‖H(r t/M) - H̃_r‖ ≤ δ` with `t δ ≤ ε/12`. -/
structure UniformHyp (D : Data (X × Fin M) n Z s) (Hpath : X → ℝ → Matrix n n ℂ)
    (η t β δ ε : ℝ) : Prop where
  eta_pos : 0 < η
  time_nonneg : 0 ≤ t
  beta_nonneg : 0 ≤ β
  eps_pos : 0 < ε
  eps_le_half : ε ≤ 1 / 2
  slots_pos : 0 < M
  mesh : 4 * s * (η * t) ≤ M
  freeze : 9 * β * t ^ 2 ≤ ε * M
  cayley : 9 * (Real.sqrt s * (η * t)) ^ 3 ≤ ε * (M : ℝ) ^ 2
  hermitian : ∀ y, (D.matrix y).IsHermitian
  row : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2
  col : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2
  path_hermitian : ∀ x, ∀ u ∈ Icc 0 t, (Hpath x u).IsHermitian
  lipschitz : ∀ x, ∀ u ∈ Icc 0 t, ∀ v ∈ Icc 0 t,
    ‖SparseStateOverlap.matrixOperator (Hpath x u) -
      SparseStateOverlap.matrixOperator (Hpath x v)‖ ≤ β * |u - v|
  sample : ∀ x (r : Fin M), ‖SparseStateOverlap.matrixOperator (Hpath x (r * t / M)) -
    SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δ
  budget : t * δ ≤ ε / 12

/-- **The error criterion of Theorem `hs:thm:time`** (equation `hs:eq:timeerror`, complete
output) for an evaluation family `run` and an encoding `ι`: for every instance `x` and every
propagator `U` of the path (`U 0 = 1`, `U' = -iH(u)U` on `[0, t]`),
`‖run x ∘ ι - ι ∘ U(t)‖ ≤ ε`. -/
def UniformGuarantee {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (run : X → K →L[ℂ] K) (ι : EuclideanSpace ℂ n →L[ℂ] K) (Hpath : X → ℝ → Matrix n n ℂ)
    (t ε : ℝ) : Prop :=
  ∀ x, ∀ U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n), U 0 = 1 →
    TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator (Hpath x u)) U 0 t →
    ‖run x ∘L ι - ι ∘L U t‖ ≤ ε

set_option maxRecDepth 8192 in
/-- **The released Theorem `hs:thm:time`** (`TimeDependent.simulation`) in terms of
`UniformHyp` and `UniformGuarantee`. -/
theorem UniformHyp.simulation [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
    {D : Data (X × Fin M) n Z s} {Hpath : X → ℝ → Matrix n n ℂ} {η t β δ ε : ℝ}
    (h : UniformHyp D Hpath η t β δ ε) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program (TimeDependent.oracle D γ η t ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * t) +
            Real.sqrt ((s : ℝ) * (η * t) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (TimeDependent.input D h.slots_pos γ η t ε)† ∘L
          TimeDependent.input D h.slots_pos γ η t ε = 1 ∧
        (∀ x, IsUnitary (p.eval x)) ∧
        UniformGuarantee p.eval (TimeDependent.input D h.slots_pos γ η t ε) Hpath t ε := by
  obtain ⟨γ, hγ, hγ1, hw, p, hc, hi, hp⟩ := TimeDependent.simulation D Hpath η t β δ ε
    h.eta_pos h.time_nonneg h.beta_nonneg h.eps_pos h.eps_le_half h.slots_pos h.mesh h.freeze
    h.cayley h.hermitian h.row h.col h.path_hermitian h.lipschitz h.sample h.budget
  exact ⟨γ, hγ, hγ1, hw, p, hc, hi, fun x => (hp x).1, fun x => (hp x).2⟩

/-! ### General meshes and integrable paths -/

/-- **The hypotheses of the general-mesh theorem** (generalisations after Theorem `hs:thm:time`;
`TimeDependentExtensions.Hamiltonian.simulation` and
`IntegrablePathSimulation.Hamiltonian.simulation`) on the samples and the public data:
`M > 0` mesh intervals, `η > 0`, `T > 0`, `0 < ε ≤ 1/2`, `N > 0` slots, a mesh
`0 = t_0 ≤ ⋯ ≤ t_M = T`, the slot conditions `4 s η T ≤ N`, `9 (√s η T)³ ≤ ε N²` and
`9 M √s η T ≤ ε N`, and Hermitian samples with row and column norms at most `η`. -/
structure MeshHyp (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (η T ε : ℝ) (N : ℕ) : Prop where
  intervals_pos : 0 < M
  eta_pos : 0 < η
  time_pos : 0 < T
  eps_pos : 0 < ε
  eps_le_half : ε ≤ 1 / 2
  slots_pos : 0 < N
  isMesh : IsMesh t M T
  clock : 4 * s * (η * T) ≤ N
  cayley : 9 * (Real.sqrt s * (η * T)) ^ 3 ≤ ε * (N : ℝ) ^ 2
  refine : 9 * M * (Real.sqrt s * (η * T)) ≤ ε * N
  hermitian : ∀ y, (D.matrix y).IsHermitian
  row : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2
  col : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2

/-- **A path of the general-mesh class** for instance `x`: one piece `H_r` per mesh interval,
Hermitian and interval integrable on `[t_r, t_{r+1}]`, with integrated sample errors
`∑_r ∫_{t_r}^{t_{r+1}} ‖H_r(u) - H̃_r‖ du ≤ ε/9`. -/
structure MeshPath (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (ε : ℝ) (x : X)
    (Hp : Fin M → ℝ → Matrix n n ℂ) : Prop where
  hermitian : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), (Hp r u).IsHermitian
  integrable : ∀ r : Fin M, IntervalIntegrable
    (fun u => SparseStateOverlap.matrixOperator (Hp r u)) volume (t r) (t ((r : ℕ) + 1))
  certificate : ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
    ‖SparseStateOverlap.matrixOperator (Hp r u) -
      SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 9

/-- **The error criterion of the general-mesh theorem**: for every instance, every path of the
class (`MeshPath`) and every piecewise propagator (`U 0 = 1`, `U' = -iH_r U` on every closed
mesh interval), `‖run x ∘ ι - ι ∘ U(T)‖ ≤ ε`. -/
def MeshGuarantee {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (run : X → K →L[ℂ] K) (ι : EuclideanSpace ℂ n →L[ℂ] K) (D : Data (X × Fin M) n Z s)
    (t : ℕ → ℝ) (T ε : ℝ) : Prop :=
  ∀ x (Hp : Fin M → ℝ → Matrix n n ℂ) (U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)),
    MeshPath D t ε x Hp → U 0 = 1 →
    (∀ r : Fin M, TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator (Hp r u)) U
      (t r) (t ((r : ℕ) + 1))) →
    ‖run x ∘L ι - ι ∘L U T‖ ≤ ε

/-- **A path of the integrable class** for instance `x`: Hermitian at almost every time of
`[0, T]`, interval integrable on `[0, T]`, with integrated sample errors at most `ε/9`. -/
structure IntegrablePath (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (T ε : ℝ) (x : X)
    (H : ℝ → Matrix n n ℂ) : Prop where
  hermitian : ∀ᵐ u, u ∈ Icc 0 T → (H u).IsHermitian
  integrable : IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (H u)) volume 0 T
  certificate : ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
    ‖SparseStateOverlap.matrixOperator (H u) -
      SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 9

/-- **The error criterion for integrable paths**: for every instance, every path of the class
(`IntegrablePath`) and every integral-sense propagator `U` of it on `[0, T]`,
`‖run x ∘ ι - ι ∘ U(T)‖ ≤ ε`. -/
def IntegrableGuarantee {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (run : X → K →L[ℂ] K) (ι : EuclideanSpace ℂ n →L[ℂ] K)
    (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (T ε : ℝ) : Prop :=
  ∀ x (H : ℝ → Matrix n n ℂ) (U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)),
    IntegrablePath D t T ε x H →
    IsPropagator (fun u => SparseStateOverlap.matrixOperator (H u)) U T →
    ‖run x ∘L ι - ι ∘L U T‖ ≤ ε

set_option maxRecDepth 8192 in
/-- **The released general-mesh theorem** (`TimeDependentExtensions.Hamiltonian.simulation`)
in terms of `MeshHyp` and `MeshGuarantee`. -/
theorem MeshHyp.simulation [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
    {D : Data (X × Fin M) n Z s} {t : ℕ → ℝ} {η T ε : ℝ} {N : ℕ} (h : MeshHyp D t η T ε N) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * T) +
            Real.sqrt ((s : ℝ) * (η * T) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (TimeDependentExtensions.Hamiltonian.input D h.intervals_pos t N γ η T ε)† ∘L
          TimeDependentExtensions.Hamiltonian.input D h.intervals_pos t N γ η T ε = 1 ∧
        (∀ x, IsUnitary (p.eval x)) ∧
        MeshGuarantee p.eval
          (TimeDependentExtensions.Hamiltonian.input D h.intervals_pos t N γ η T ε) D t T ε := by
  obtain ⟨γ, hγ, hγ1, hw, p, hc, hi, hp⟩ := TimeDependentExtensions.Hamiltonian.simulation D
    h.intervals_pos t η T ε N h.eta_pos h.time_pos h.eps_pos h.eps_le_half h.slots_pos
    h.isMesh h.clock h.cayley h.refine h.hermitian h.row h.col
  exact ⟨γ, hγ, hγ1, hw, p, hc, hi, fun x => (hp x).1,
    fun x Hp U hP hU0 hU => (hp x).2 Hp U hP.hermitian hP.integrable hP.certificate hU0 hU⟩

set_option maxRecDepth 8192 in
/-- **The released theorem for integrable paths**
(`IntegrablePathSimulation.Hamiltonian.simulation`) in terms of `MeshHyp` and
`IntegrableGuarantee`. -/
theorem MeshHyp.simulation_integrable [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
    {D : Data (X × Fin M) n Z s} {t : ℕ → ℝ} {η T ε : ℝ} {N : ℕ} (h : MeshHyp D t η T ε N) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * T) +
            Real.sqrt ((s : ℝ) * (η * T) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (TimeDependentExtensions.Hamiltonian.input D h.intervals_pos t N γ η T ε)† ∘L
          TimeDependentExtensions.Hamiltonian.input D h.intervals_pos t N γ η T ε = 1 ∧
        (∀ x, IsUnitary (p.eval x)) ∧
        IntegrableGuarantee p.eval
          (TimeDependentExtensions.Hamiltonian.input D h.intervals_pos t N γ η T ε) D t T ε := by
  obtain ⟨γ, hγ, hγ1, hw, p, hc, hi, hp⟩ := IntegrablePathSimulation.Hamiltonian.simulation D
    h.intervals_pos t η T ε N h.eta_pos h.time_pos h.eps_pos h.eps_le_half h.slots_pos
    h.isMesh h.clock h.cayley h.refine h.hermitian h.row h.col
  exact ⟨γ, hγ, hγ1, hw, p, hc, hi, fun x => (hp x).1,
    fun x H U hP hU => (hp x).2 H U hP.hermitian hP.integrable hP.certificate hU⟩

/-! ### One path on every mesh interval -/

/-- **The general-mesh criterion for one path** `Hpath` (the same piece on every mesh
interval): for every instance and every piecewise propagator (`U 0 = 1`,
`U' = -iH(u)U` on every closed mesh interval `[t_r, t_{r+1}]`, `r < M`),
`‖run x ∘ ι - ι ∘ U(T)‖ ≤ ε`. -/
def MeshCriterion {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (run : X → K →L[ℂ] K) (ι : EuclideanSpace ℂ n →L[ℂ] K) (Hpath : X → ℝ → Matrix n n ℂ)
    (t : ℕ → ℝ) (M : ℕ) (T ε : ℝ) : Prop :=
  ∀ x, ∀ U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n), U 0 = 1 →
    (∀ r : Fin M, TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator (Hpath x u))
      U (t r) (t ((r : ℕ) + 1))) →
    ‖run x ∘L ι - ι ∘L U T‖ ≤ ε

/-- **The integrable-path criterion for one path** `Hpath`: for every instance and every
integral-sense propagator `U` of the path on `[0, T]`, `‖run x ∘ ι - ι ∘ U(T)‖ ≤ ε`. -/
def IntegrableCriterion {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (run : X → K →L[ℂ] K) (ι : EuclideanSpace ℂ n →L[ℂ] K)
    (Hpath : X → ℝ → Matrix n n ℂ) (T ε : ℝ) : Prop :=
  ∀ x, ∀ U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
    IsPropagator (fun u => SparseStateOverlap.matrixOperator (Hpath x u)) U T →
    ‖run x ∘L ι - ι ∘L U T‖ ≤ ε

end Defs

/-! ### Membership of constant data and constant paths -/

section Membership

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- **Constant data with the constant path are in the uniform-mesh class** for every `β, δ ≥ 0`
satisfying the public mesh conditions: the path is Hermitian, its Lipschitz bound and sample
errors vanish. -/
theorem uniformHyp_const (D : Data X n Z s) (hH : ∀ x, (D.matrix x).IsHermitian) {η : ℝ}
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) {M : ℕ} {t β δ ε : ℝ} (hη : 0 < η)
    (ht : 0 ≤ t) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) (hM : 0 < M)
    (hMesh : 4 * s * (η * t) ≤ M) (hFreeze : 9 * β * t ^ 2 ≤ ε * M)
    (hCayley : 9 * (Real.sqrt s * (η * t)) ^ 3 ≤ ε * (M : ℝ) ^ 2) (hBudget : t * δ ≤ ε / 12) :
    UniformHyp (constData D M) (constPath D) η t β δ ε where
  eta_pos := hη
  time_nonneg := ht
  beta_nonneg := hβ
  eps_pos := hε
  eps_le_half := hεHalf
  slots_pos := hM
  mesh := hMesh
  freeze := hFreeze
  cayley := hCayley
  hermitian := constData_hermitian D M hH
  row := constData_row D M hrow
  col := constData_col D M hcol
  path_hermitian x _ _ := hH x
  lipschitz x u _ v _ := by
    rw [constPath_apply, constPath_apply, sub_self, norm_zero]
    exact mul_nonneg hβ (abs_nonneg _)
  sample x r := by
    rw [constPath_apply, constData_matrix, sub_self, norm_zero]
    exact hδ
  budget := hBudget

/-- **With `β = δ_val = 0`** (the remark after Theorem `hs:thm:time`): constant data and the
constant path satisfy the hypotheses of `TimeDependent.simulation` under the two remaining
mesh conditions `4 s η t ≤ M` and `9 (√s η t)³ ≤ ε M²`. -/
theorem uniformHyp_const_zero (D : Data X n Z s) (hH : ∀ x, (D.matrix x).IsHermitian) {η : ℝ}
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) {M : ℕ} {t ε : ℝ} (hη : 0 < η)
    (ht : 0 ≤ t) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) (hM : 0 < M)
    (hMesh : 4 * s * (η * t) ≤ M)
    (hCayley : 9 * (Real.sqrt s * (η * t)) ^ 3 ≤ ε * (M : ℝ) ^ 2) :
    UniformHyp (constData D M) (constPath D) η t 0 0 ε :=
  uniformHyp_const D hH hrow hcol hη ht le_rfl le_rfl hε hεHalf hM hMesh
    (by rw [mul_zero, zero_mul]; exact mul_nonneg hε.le (Nat.cast_nonneg M)) hCayley
    (by rw [mul_zero]; positivity)

/-- **Constant data are in the general-mesh class** on every admissible mesh. -/
theorem meshHyp_const (D : Data X n Z s) (hH : ∀ x, (D.matrix x).IsHermitian) {η : ℝ}
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) {M : ℕ} {t : ℕ → ℝ} {T ε : ℝ} {N : ℕ}
    (hM : 0 < M) (hη : 0 < η) (hT : 0 < T) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) (hN : 0 < N)
    (hmesh : IsMesh t M T) (hClock : 4 * s * (η * T) ≤ N)
    (hCayley : 9 * (Real.sqrt s * (η * T)) ^ 3 ≤ ε * (N : ℝ) ^ 2)
    (hRefine : 9 * M * (Real.sqrt s * (η * T)) ≤ ε * N) :
    MeshHyp (constData D M) t η T ε N where
  intervals_pos := hM
  eta_pos := hη
  time_pos := hT
  eps_pos := hε
  eps_le_half := hεHalf
  slots_pos := hN
  isMesh := hmesh
  clock := hClock
  cayley := hCayley
  refine := hRefine
  hermitian := constData_hermitian D M hH
  row := constData_row D M hrow
  col := constData_col D M hcol

/-- **The constant pieces are a path of the general-mesh class** for every instance, with
certificate `0`. -/
theorem meshPath_const (D : Data X n Z s) (hH : ∀ x, (D.matrix x).IsHermitian) {M : ℕ}
    (t : ℕ → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (x : X) :
    MeshPath (constData D M) t ε x (fun _ => constPath D x) where
  hermitian _ _ _ := hH x
  integrable _ := (intervalIntegrable_const : IntervalIntegrable
    (fun _ => SparseStateOverlap.matrixOperator (D.matrix x)) volume _ _)
  certificate := by
    simp only [constPath_apply, constData_matrix, sub_self, norm_zero,
      intervalIntegral.integral_zero, Finset.sum_const_zero]
    positivity

/-- **The constant path is a path of the integrable class** for every instance, with
certificate `0`. -/
theorem integrablePath_const (D : Data X n Z s) (hH : ∀ x, (D.matrix x).IsHermitian) {M : ℕ}
    (t : ℕ → ℝ) {T ε : ℝ} (hε : 0 ≤ ε) (x : X) :
    IntegrablePath (constData D M) t T ε x (constPath D x) where
  hermitian := Filter.Eventually.of_forall fun _ _ => hH x
  integrable := (intervalIntegrable_const : IntervalIntegrable
    (fun _ => SparseStateOverlap.matrixOperator (D.matrix x)) volume _ _)
  certificate := by
    simp only [constPath_apply, constData_matrix, sub_self, norm_zero,
      intervalIntegral.integral_zero, Finset.sum_const_zero]
    positivity

/-- **The hard instances with `η = 1`**: data with the properties of Theorem `hsl:thm:main`
(`HardInstance`) give the uniform-mesh class with the constant path for every `β, δ ≥ 0`
satisfying the mesh conditions. -/
theorem uniformHyp_hard {B : ℕ} {D : Data X n (SparseLowerBounds.Hamiltonian.Word B) s}
    (hD : SparseLowerBounds.Hamiltonian.HardInstance D) {M : ℕ} {t β δ ε : ℝ} (ht : 0 ≤ t)
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) (hM : 0 < M)
    (hMesh : 4 * s * (1 * t) ≤ M) (hFreeze : 9 * β * t ^ 2 ≤ ε * M)
    (hCayley : 9 * (Real.sqrt s * (1 * t)) ^ 3 ≤ ε * (M : ℝ) ^ 2) (hBudget : t * δ ≤ ε / 12) :
    UniformHyp (constData D M) (constPath D) 1 t β δ ε :=
  uniformHyp_const D hD.isHermitian (by simpa only [one_pow] using hD.row_norm_le)
    (by simpa only [one_pow] using hD.col_norm_le) one_pos ht hβ hδ hε hεHalf hM hMesh hFreeze
    hCayley hBudget

/-- **The hard instances with `η = 1`** are in the general-mesh class on every admissible
mesh. -/
theorem meshHyp_hard {B : ℕ} {D : Data X n (SparseLowerBounds.Hamiltonian.Word B) s}
    (hD : SparseLowerBounds.Hamiltonian.HardInstance D) {M : ℕ} {t : ℕ → ℝ} {T ε : ℝ} {N : ℕ}
    (hM : 0 < M) (hT : 0 < T) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) (hN : 0 < N)
    (hmesh : IsMesh t M T) (hClock : 4 * s * (1 * T) ≤ N)
    (hCayley : 9 * (Real.sqrt s * (1 * T)) ^ 3 ≤ ε * (N : ℝ) ^ 2)
    (hRefine : 9 * M * (Real.sqrt s * (1 * T)) ≤ ε * N) :
    MeshHyp (constData D M) t 1 T ε N :=
  meshHyp_const D hD.isHermitian (by simpa only [one_pow] using hD.row_norm_le)
    (by simpa only [one_pow] using hD.col_norm_le) hM one_pos hT hε hεHalf hN hmesh hClock
    hCayley hRefine

end Membership

/-! ### The criteria on the constant path -/

section Criteria

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **The uniform-mesh criterion on the constant path is the endpoint error**: error at most
`ε` against every propagator of the constant path is error at most `ε` against
`exp(-iτH_x)`. -/
theorem uniform_criterion_iff (D : Data X n Z s) (run : X → K →L[ℂ] K)
    (ι : EuclideanSpace ℂ n →L[ℂ] K) {τ ε : ℝ} (hτ : 0 ≤ τ) :
    UniformGuarantee run ι (constPath D) τ ε ↔
    ∀ x, ‖run x ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  constructor
  · intro h x
    exact h x (constProp (SparseStateOverlap.matrixOperator (D.matrix x))) (constProp_zero _)
      (solvesOn_constPath D x 0 τ)
  · intro h x U hU0 hU
    rw [propagator_constPath_eq D x hτ hU0 hU]
    exact h x

/-- **The integrable criterion on the constant path is the endpoint error**. -/
theorem integrable_criterion_iff (D : Data X n Z s) (run : X → K →L[ℂ] K)
    (ι : EuclideanSpace ℂ n →L[ℂ] K) {τ ε : ℝ} (hτ : 0 ≤ τ) :
    IntegrableCriterion run ι (constPath D) τ ε ↔
    ∀ x, ‖run x ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  constructor
  · intro h x
    exact h x (constProp (SparseStateOverlap.matrixOperator (D.matrix x)))
      (isPropagator_constPath D x hτ)
  · intro h x U hU
    rw [isPropagator_constPath_eq D x hτ hU]
    exact h x

/-- The general-mesh criterion on the constant path gives the endpoint error (on any `t`). -/
theorem endpoint_of_mesh (D : Data X n Z s) (run : X → K →L[ℂ] K)
    (ι : EuclideanSpace ℂ n →L[ℂ] K) {M : ℕ} {t : ℕ → ℝ} {τ ε : ℝ}
    (h : MeshCriterion run ι (constPath D) t M τ ε) (x : X) :
    ‖run x ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε :=
  h x (constProp (SparseStateOverlap.matrixOperator (D.matrix x))) (constProp_zero _)
    (fun _ => solvesOn_constPath D x _ _)

/-- **The general-mesh criterion on the constant path is the endpoint error**, on every mesh
(a piecewise propagator of the constant pieces is a propagator of the constant path, by the
released `IntegrablePathSimulation.Propagator.isPropagator_glue`). -/
theorem mesh_criterion_iff (D : Data X n Z s) (run : X → K →L[ℂ] K)
    (ι : EuclideanSpace ℂ n →L[ℂ] K) {M : ℕ} {t : ℕ → ℝ} {τ ε : ℝ} (hmesh : IsMesh t M τ) :
    MeshCriterion run ι (constPath D) t M τ ε ↔
    ∀ x, ‖run x ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  have hτ : 0 ≤ τ := by
    have h0 := hmesh.mono (Nat.zero_le M)
    rw [hmesh.zero, hmesh.last] at h0
    exact h0
  refine ⟨endpoint_of_mesh D run ι, fun h x U hU0 hU => ?_⟩
  have hP : IsPropagator (fun u => SparseStateOverlap.matrixOperator (constPath D x u)) U τ :=
    IntegrablePathSimulation.Propagator.isPropagator_glue
      (Hp := fun _ u => SparseStateOverlap.matrixOperator (constPath D x u)) hmesh
      ⟨hU0, fun r hr => hU ⟨r, hr⟩⟩ (fun _ _ => (intervalIntegrable_const : IntervalIntegrable
        (fun _ => SparseStateOverlap.matrixOperator (D.matrix x)) volume _ _))
  rw [isPropagator_constPath_eq D x hτ hP]
  exact h x

/-! ### The class guarantees give the criteria on the constant hard paths -/

/-- **Class membership used**: an evaluation family that meets the uniform-mesh guarantee for
every path of the class of the constant data (`UniformHyp`) meets it on the constant path,
which belongs to the class (`uniformHyp_const`). -/
theorem uniformGuarantee_const (D : Data X n Z s) (hH : ∀ x, (D.matrix x).IsHermitian) {η : ℝ}
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) {M : ℕ} {t β δ ε : ℝ} (hη : 0 < η)
    (ht : 0 ≤ t) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) (hM : 0 < M)
    (hMesh : 4 * s * (η * t) ≤ M) (hFreeze : 9 * β * t ^ 2 ≤ ε * M)
    (hCayley : 9 * (Real.sqrt s * (η * t)) ^ 3 ≤ ε * (M : ℝ) ^ 2) (hBudget : t * δ ≤ ε / 12)
    (run : X → K →L[ℂ] K) (ι : EuclideanSpace ℂ n →L[ℂ] K)
    (hguar : ∀ Hpath, UniformHyp (constData D M) Hpath η t β δ ε →
      UniformGuarantee run ι Hpath t ε) :
    UniformGuarantee run ι (constPath D) t ε :=
  hguar _ (uniformHyp_const D hH hrow hcol hη ht hβ hδ hε hεHalf hM hMesh hFreeze hCayley
    hBudget)

/-- **Class membership used**: the general-mesh guarantee on the constant data gives the
criterion on the constant path, whose constant pieces belong to the class with certificate
`0` (`meshPath_const`). -/
theorem MeshGuarantee.criterion_const {D : Data X n Z s} (hH : ∀ x, (D.matrix x).IsHermitian)
    {M : ℕ} {t : ℕ → ℝ} {T ε : ℝ} (hε : 0 ≤ ε) {run : X → K →L[ℂ] K}
    {ι : EuclideanSpace ℂ n →L[ℂ] K} (h : MeshGuarantee run ι (constData D M) t T ε) :
    MeshCriterion run ι (constPath D) t M T ε :=
  fun x U hU0 hU => h x (fun _ => constPath D x) U (meshPath_const D hH t hε x) hU0 hU

/-- **Class membership used**: the integrable-path guarantee on the constant data gives the
criterion on the constant path, which belongs to the class with certificate `0`
(`integrablePath_const`). -/
theorem IntegrableGuarantee.criterion_const {D : Data X n Z s}
    (hH : ∀ x, (D.matrix x).IsHermitian) {M : ℕ} {t : ℕ → ℝ} {T ε : ℝ} (hε : 0 ≤ ε)
    {run : X → K →L[ℂ] K} {ι : EuclideanSpace ℂ n →L[ℂ] K}
    (h : IntegrableGuarantee run ι (constData D M) t T ε) :
    IntegrableCriterion run ι (constPath D) T ε :=
  fun x U hU => h x (constPath D x) U (integrablePath_const D hH t hε x) hU

/-- **With `β = δ_val = 0` the uniform-mesh class of constant data is the constant path**:
every path with `UniformHyp (constData D M) Hpath η t 0 0 ε` agrees with the constant path on
`[0, t]` (its sample at `0` is exact and its Lipschitz constant vanishes), so the guarantee on
the constant path is the guarantee for every path of the class. The released Theorem
`hs:thm:time` (`TimeDependent.simulation`) chooses its program after the path; with this
lemma its simulators meet the path-uniform hypothesis of `uniform_class_max`. -/
theorem uniformGuarantee_of_zero (D : Data X n Z s) {M : ℕ} {η t ε : ℝ} (run : X → K →L[ℂ] K)
    (ι : EuclideanSpace ℂ n →L[ℂ] K) (hg : UniformGuarantee run ι (constPath D) t ε)
    (Hpath : X → ℝ → Matrix n n ℂ) (hH : UniformHyp (constData D M) Hpath η t 0 0 ε) :
    UniformGuarantee run ι Hpath t ε := by
  intro x U hU0 hU
  refine hg x U hU0 fun u hu => ?_
  have h0 : SparseStateOverlap.matrixOperator (Hpath x 0) =
      SparseStateOverlap.matrixOperator (D.matrix x) := by
    have hs := hH.sample x ⟨0, hH.slots_pos⟩
    simp only [Nat.cast_zero, zero_mul, zero_div, constData_matrix] at hs
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hs)
  have hl := hH.lipschitz x u hu 0 ⟨le_rfl, hH.time_nonneg⟩
  rw [zero_mul, h0] at hl
  have hd := hU u hu
  simp only [sub_eq_zero.mp (norm_le_zero_iff.mp hl)] at hd
  exact hd

end Criteria

end

end TimeDependentHamiltonianLowerBound
