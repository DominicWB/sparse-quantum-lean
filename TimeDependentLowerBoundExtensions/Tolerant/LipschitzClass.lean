import TimeDependentHamiltonianLowerBound.Class
import TimeDependentExtensions.Hamiltonian.Corollaries

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The class of piecewise Lipschitz paths with breakpoints

The paragraph "Regularity and coherent parameters" after Theorem `hs:thm:time` (the manuscript,
lines 1497-1500): "The same proof covers piecewise Lipschitz paths when all breakpoints are
supplied: include them in the mesh, take the appropriate one-sided sample on each interval, and
use its Lipschitz bound" (likewise line 2916, in the time-dependent ODE argument; the class and
the lower bounds of this directory are those of the Hamiltonian simulation theorem, and the ODE
form is not stated here). The package's statement is
`TimeDependentExtensions.Hamiltonian.simulation_lipschitz`: on a mesh `t` whose points contain
the breakpoints, every path with `β_r`-Lipschitz Hermitian pieces on the mesh intervals and
one-sided sample errors `‖H_r(t_r) - H̃_r‖ ≤ δ_r`, with `∑_r (β_r Δ_r² / 2 + δ_r Δ_r) ≤ ε/9`, is
simulated within `ε` against every piecewise propagator. This module names that class and that
guarantee, in the style of `TimeDependentHamiltonianLowerBound.MeshPath` and `MeshGuarantee`.

* `LipschitzPath`, `LipschitzGuarantee`: the class of piecewise Lipschitz paths for given
  samples and mesh, and the error criterion of `simulation_lipschitz`;
* `LipschitzPath.meshPath`, `lipschitzGuarantee_of_meshGuarantee`: on nondecreasing mesh
  points (`t_r ≤ t_{r+1}`), every piecewise Lipschitz path is a path of the general-mesh class
  (integrated certificate bounded by the Lipschitz certificate), so the general-mesh guarantee
  gives the Lipschitz guarantee;
* `lipschitzPath_const`: the constant pieces of constant data are a piecewise Lipschitz path with
  `β = δ = 0`, on every mesh (any breakpoints);
* `LipschitzGuarantee.criterion_const`: the Lipschitz guarantee on constant data gives the
  general-mesh criterion on the constant path;
* `simulation_lipschitz_guarantee`: the conclusion of `simulation_lipschitz`, under its own
  hypotheses, is exactly `LipschitzGuarantee` for its program and encoding;
* `meshHyp_simulation_lipschitz`: the released theorem
  (`TimeDependentExtensions.Hamiltonian.simulation`) under `MeshHyp` meets `LipschitzGuarantee`.
-/

namespace TimeDependentLowerBoundExtensions.Tolerant

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open MeasureTheory Set
open TimeDependentExtensions (IsMesh)
open TimeDependentHamiltonianLowerBound (MeshHyp MeshPath MeshGuarantee MeshCriterion constData
  constPath)
open scoped InnerProduct InnerProductSpace

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s M : ℕ}

/-- **A piecewise Lipschitz path with breakpoints at the mesh points** for instance `x`: one
piece `H_r` per mesh interval, Hermitian and `β_r`-Lipschitz in operator norm on
`[t_r, t_{r+1}]`, with one-sided sample errors `‖H_r(t_r) - H̃_r‖ ≤ δ_r` and certificate
`∑_r (β_r Δ_r² / 2 + δ_r Δ_r) ≤ ε/9` (`Δ_r = t_{r+1} - t_r`), the hypotheses of
`TimeDependentExtensions.Hamiltonian.simulation_lipschitz`. -/
structure LipschitzPath (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (ε : ℝ) (x : X)
    (Hp : Fin M → ℝ → Matrix n n ℂ) (β δ : Fin M → ℝ) : Prop where
  hermitian : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), (Hp r u).IsHermitian
  lipschitz : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)),
    ∀ v ∈ Icc (t r) (t ((r : ℕ) + 1)),
      ‖SparseStateOverlap.matrixOperator (Hp r u) -
        SparseStateOverlap.matrixOperator (Hp r v)‖ ≤ β r * |u - v|
  sample : ∀ r : Fin M, ‖SparseStateOverlap.matrixOperator (Hp r (t r)) -
    SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δ r
  certificate : ∑ r : Fin M, (β r * (t ((r : ℕ) + 1) - t r) ^ 2 / 2 +
    δ r * (t ((r : ℕ) + 1) - t r)) ≤ ε / 9

/-- **The error criterion for piecewise Lipschitz paths** (the conclusion of
`TimeDependentExtensions.Hamiltonian.simulation_lipschitz`): for every instance, every piecewise
Lipschitz path of the class (`LipschitzPath`, any `β_r`, `δ_r`) and every piecewise propagator
(`U 0 = 1`, `U' = -iH_r U` on every closed mesh interval), `‖run x ∘ ι - ι ∘ U(T)‖ ≤ ε`. -/
def LipschitzGuarantee {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (run : X → K →L[ℂ] K) (ι : EuclideanSpace ℂ n →L[ℂ] K)
    (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (T ε : ℝ) : Prop :=
  ∀ x (Hp : Fin M → ℝ → Matrix n n ℂ) (β δ : Fin M → ℝ)
    (U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)),
    LipschitzPath D t ε x Hp β δ → U 0 = 1 →
    (∀ r : Fin M, TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator (Hp r u)) U
      (t r) (t ((r : ℕ) + 1))) →
    ‖run x ∘L ι - ι ∘L U T‖ ≤ ε

/-- **Piecewise Lipschitz paths are paths of the general-mesh class**: on nondecreasing mesh
points, a piecewise Lipschitz path (`LipschitzPath`) is a `MeshPath`, its pieces being
continuous, hence interval integrable, with integrated sample errors bounded by the Lipschitz
certificate. -/
theorem LipschitzPath.meshPath {D : Data (X × Fin M) n Z s} {t : ℕ → ℝ} {ε : ℝ} {x : X}
    {Hp : Fin M → ℝ → Matrix n n ℂ} {β δ : Fin M → ℝ}
    (hmono : ∀ r : Fin M, t r ≤ t ((r : ℕ) + 1))
    (h : LipschitzPath D t ε x Hp β δ) : MeshPath D t ε x Hp where
  hermitian := h.hermitian
  integrable r := (TimeDependentExtensions.continuousOn_of_lipschitz _
    (h.lipschitz r)).intervalIntegrable_of_Icc (hmono r)
  certificate := (Finset.sum_le_sum fun r _ =>
    TimeDependentExtensions.integral_le_of_lipschitz' _ _ (hmono r) (h.lipschitz r)
      (h.sample r)).trans h.certificate

/-- **The general-mesh guarantee gives the Lipschitz guarantee**: on nondecreasing mesh points,
an evaluation family meeting `MeshGuarantee` meets `LipschitzGuarantee`
(`LipschitzPath.meshPath`). Every mesh in the sense of `TimeDependentExtensions.IsMesh` has
nondecreasing points (`IsMesh.mono`). On a reversed interval the Lipschitz hypothesis is vacuous
and does not give the interval integrability required by `MeshPath`. -/
theorem lipschitzGuarantee_of_meshGuarantee {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] {run : X → K →L[ℂ] K}
    {ι : EuclideanSpace ℂ n →L[ℂ] K} {D : Data (X × Fin M) n Z s} {t : ℕ → ℝ} {T ε : ℝ}
    (hmono : ∀ r : Fin M, t r ≤ t ((r : ℕ) + 1)) (h : MeshGuarantee run ι D t T ε) :
    LipschitzGuarantee run ι D t T ε :=
  fun x Hp _ _ U hP hU0 hU => h x Hp U (hP.meshPath hmono) hU0 hU

/-- **The constant pieces are a piecewise Lipschitz path with `β = δ = 0`**: for constant data
with Hermitian instances, on every mesh `t` (any breakpoints) and every `ε ≥ 0`. -/
theorem lipschitzPath_const (D : Data X n Z s) (hH : ∀ x, (D.matrix x).IsHermitian)
    (t : ℕ → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (x : X) :
    LipschitzPath (constData D M) t ε x (fun _ => constPath D x) 0 0 where
  hermitian _ _ _ := hH x
  lipschitz _ _ _ _ _ := by simp [TimeDependentHamiltonianLowerBound.constPath_apply]
  sample _ := by simp [TimeDependentHamiltonianLowerBound.constPath_apply,
    TimeDependentHamiltonianLowerBound.constData_matrix]
  certificate := by
    simp only [Pi.zero_apply, zero_mul, zero_div, zero_add, Finset.sum_const_zero]
    linarith

/-- **Class membership used**: the Lipschitz guarantee on the constant data gives the
general-mesh criterion on the constant path, whose constant pieces belong to the class with
`β = δ = 0` (`lipschitzPath_const`). -/
theorem LipschitzGuarantee.criterion_const {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] {D : Data X n Z s}
    (hH : ∀ x, (D.matrix x).IsHermitian) {t : ℕ → ℝ} {T ε : ℝ} (hε : 0 ≤ ε)
    {run : X → K →L[ℂ] K} {ι : EuclideanSpace ℂ n →L[ℂ] K}
    (h : LipschitzGuarantee run ι (constData D M) t T ε) :
    MeshCriterion run ι (constPath D) t M T ε :=
  fun x U hU0 hU => h x (fun _ => constPath D x) 0 0 U (lipschitzPath_const D hH t hε x) hU0 hU

set_option maxRecDepth 8192 in
/-- **`LipschitzGuarantee` is the guarantee of `simulation_lipschitz`**: under the hypotheses of
`TimeDependentExtensions.Hamiltonian.simulation_lipschitz`, its program and encoding satisfy
`LipschitzGuarantee`, with its count bound; the proof unpacks the conclusion of
`simulation_lipschitz` along the fields of `LipschitzPath`. -/
theorem simulation_lipschitz_guarantee [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
    (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ)
    (η T ε : ℝ) (N : ℕ) (hη : 0 < η) (hT : 0 < T) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hN : 0 < N) (hmesh : IsMesh t M T)
    (hClock : 4 * s * (η * T) ≤ N)
    (hCayley : 9 * (Real.sqrt s * (η * T)) ^ 3 ≤ ε * (N : ℝ) ^ 2)
    (hRefine : 9 * M * (Real.sqrt s * (η * T)) ≤ ε * N)
    (hH : ∀ y, (D.matrix y).IsHermitian)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * T) +
            Real.sqrt ((s : ℝ) * (η * T) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε)† ∘L
          TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε = 1 ∧
        (∀ x, IsUnitary (p.eval x)) ∧
        LipschitzGuarantee p.eval (TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε)
          D t T ε := by
  obtain ⟨γ, hγ, hγ1, hw, p, hc, hi, hA⟩ :=
    TimeDependentExtensions.Hamiltonian.simulation_lipschitz D hM t η T ε N hη hT hε hεHalf hN
      hmesh hClock hCayley hRefine hH hrow hcol
  exact ⟨γ, hγ, hγ1, hw, p, hc, hi, fun x => (hA x).1, fun x Hp β δ U hP hU0 hU =>
    ((hA x).2 Hp β δ hP.hermitian hP.lipschitz hP.sample hP.certificate).2 U hU0 hU⟩

set_option maxRecDepth 8192 in
/-- **The released general-mesh theorem meets the Lipschitz guarantee**: under `MeshHyp`, the
program and encoding of `TimeDependentExtensions.Hamiltonian.simulation` (the program of
`simulation_lipschitz`) satisfy `LipschitzGuarantee`, with the released count bound (a corollary
of `TimeDependentHamiltonianLowerBound.MeshHyp.simulation` and
`lipschitzGuarantee_of_meshGuarantee`). -/
theorem meshHyp_simulation_lipschitz [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
    {D : Data (X × Fin M) n Z s} {t : ℕ → ℝ} {η T ε : ℝ} {N : ℕ} (h : MeshHyp D t η T ε N) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * T) +
            Real.sqrt ((s : ℝ) * (η * T) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (TimeDependentExtensions.Hamiltonian.input D h.intervals_pos t N γ η T ε)† ∘L
          TimeDependentExtensions.Hamiltonian.input D h.intervals_pos t N γ η T ε = 1 ∧
        (∀ x, IsUnitary (p.eval x)) ∧
        LipschitzGuarantee p.eval
          (TimeDependentExtensions.Hamiltonian.input D h.intervals_pos t N γ η T ε) D t T ε := by
  obtain ⟨γ, hγ, hγ1, hw, p, hc, hi, hu, hg⟩ := h.simulation
  exact ⟨γ, hγ, hγ1, hw, p, hc, hi, hu,
    lipschitzGuarantee_of_meshGuarantee (fun _ => h.isMesh.mono (Nat.le_succ _)) hg⟩

end

end TimeDependentLowerBoundExtensions.Tolerant
