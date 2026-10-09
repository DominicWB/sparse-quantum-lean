import SparseLowerBounds.Hamiltonian.Herald
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Data.Real.Basic
import TimeDependentODE.Continuous.Solution
import TimeDependentODE.Native.Layer
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Real.Pi.Bounds

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Inner products under phase oracles

Helper for `SparseLowerBounds.Query.PositiveAdversary` (manuscript lines
3743-3797, the positive spectral adversary in the proof of Lemma
`odel:lem:outer`). For a projection family `P` (Query/PhaseOracle) with
remainder `R = P.rest`:

* unitaries preserve inner products and norms (`inner_map_map_of_isUnitary`,
  `norm_map_of_isUnitary`);
* the polarized resolution of the identity
  `⟪u, v⟫ = ⟪R u, R v⟫ + Σ_i ⟪P_i u, P_i v⟫` (`inner_eq_rest_add_sum`);
* a phase oracle multiplies the block `P_i` by `±1` and fixes `R`
  (`proj_phase_apply`, `rest_phase_apply`), so two phase oracles change an inner
  product exactly on the blocks where their strings differ:
  `Re⟪O_y u, O_{y'} v⟫ - Re⟪u, v⟫ = Σ_{i : y i ≠ y' i} (-2) Re⟪P_i u, P_i v⟫`
  (`re_inner_phase_sub`);
* Bessel's inequality `Σ_i ‖P_i v‖² ≤ ‖v‖²` (`sum_norm_proj_sq_le`).
-/

namespace SparseLowerBounds.PositiveAdversary

noncomputable section
open SparseHamiltonian OracleCircuit
open scoped InnerProductSpace

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Unitaries preserve inner products. -/
theorem inner_map_map_of_isUnitary {U : K →L[ℂ] K} (hU : IsUnitary U) (a b : K) :
    ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint]
  show ⟪a, (star U * U) b⟫_ℂ = _
  rw [hU.1]
  rfl

/-- Unitaries preserve norms. -/
theorem norm_map_of_isUnitary {U : K →L[ℂ] K} (hU : IsUnitary U) (v : K) : ‖U v‖ = ‖v‖ :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self U).mpr hU.1 v

/-- For a star projection `Q`, `⟪u, Q v⟫ = ⟪Q u, Q v⟫`. -/
theorem inner_apply_eq_of_isStarProjection {Q : K →L[ℂ] K} (hQ : IsStarProjection Q)
    (u v : K) : ⟪u, Q v⟫_ℂ = ⟪Q u, Q v⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    hQ.isSelfAdjoint.star_eq]
  show _ = ⟪u, (Q * Q) v⟫_ℂ
  rw [hQ.isIdempotentElem.eq]

variable {I : Type*}

/-- `P_i P_j v = [i = j] P_i v`. -/
theorem proj_apply_proj [DecidableEq I] (P : ProjFamily K I) (i j : I) (v : K) :
    P.proj i (P.proj j v) = if i = j then P.proj i v else 0 := by
  split_ifs with h
  · subst h
    exact congrArg (fun T : K →L[ℂ] K => T v) (P.isStarProjection i).isIdempotentElem.eq
  · exact congrArg (fun T : K →L[ℂ] K => T v) (P.orthogonal i j h)

variable [Fintype I]

/-- The phase oracle on a vector: `O_y v = v - 2 Σ_{i, y i} P_i v`. -/
theorem phase_apply (P : ProjFamily K I) (y : I → Bool) (v : K) :
    P.phase y v = v - (2 : ℂ) • ∑ i ∈ Finset.univ.filter (fun i => y i = true), P.proj i v := by
  rw [PhaseCircuit.phase_eq_hitProj, ← PhaseCircuit.hitProj_apply]
  rfl

/-- The phase oracle multiplies the block `P_i` by `(-1)^{y i}`. -/
theorem proj_phase_apply (P : ProjFamily K I) (y : I → Bool) (i : I) (v : K) :
    P.proj i (P.phase y v) = (if y i then (-1 : ℂ) else 1) • P.proj i v := by
  classical
  rw [phase_apply, map_sub, map_smul, map_sum]
  simp_rw [proj_apply_proj P i]
  rw [Finset.sum_ite_eq]
  cases hy : y i
  · simp [hy]
  · simp only [hy, Finset.mem_filter, Finset.mem_univ, and_self, if_true, neg_one_smul, two_smul]
    abel

/-- The phase oracle fixes the remainder block. -/
theorem rest_phase_apply (P : ProjFamily K I) (y : I → Bool) (v : K) :
    P.rest (P.phase y v) = P.rest v := by
  rw [phase_apply, map_sub, map_smul, map_sum]
  have h0 : ∀ i, P.rest (P.proj i v) = 0 := fun i =>
    congrArg (fun T : K →L[ℂ] K => T v) (P.rest_mul_proj i)
  simp [h0]

/-- The resolution of the identity, polarized:
`⟪u, v⟫ = ⟪R u, R v⟫ + Σ_i ⟪P_i u, P_i v⟫`. -/
theorem inner_eq_rest_add_sum (P : ProjFamily K I) (u v : K) :
    ⟪u, v⟫_ℂ = ⟪P.rest u, P.rest v⟫_ℂ + ∑ i, ⟪P.proj i u, P.proj i v⟫_ℂ := by
  have hv : v = P.rest v + ∑ i, P.proj i v := by
    have h : P.rest + ∑ i, P.proj i = 1 := by rw [ProjFamily.rest, sub_add_cancel]
    have h' := congrArg (fun T : K →L[ℂ] K => T v) h
    simpa using h'.symm
  conv_lhs => rw [hv]
  rw [inner_add_right, inner_sum, inner_apply_eq_of_isStarProjection P.isStarProjection_rest]
  congr 1
  exact Finset.sum_congr rfl fun i _ =>
    inner_apply_eq_of_isStarProjection (P.isStarProjection i) u v

/-- **Bit-flip identity.** Two phase oracles change the real inner product only on
the blocks where their strings differ, by `-2 Re⟪P_i u, P_i v⟫` each. -/
theorem re_inner_phase_sub (P : ProjFamily K I) (y y' : I → Bool) (u v : K) :
    (⟪P.phase y u, P.phase y' v⟫_ℂ).re - (⟪u, v⟫_ℂ).re =
      ∑ i, (if y i = y' i then 0 else -2) * (⟪P.proj i u, P.proj i v⟫_ℂ).re := by
  rw [inner_eq_rest_add_sum P (P.phase y u), inner_eq_rest_add_sum P u v, rest_phase_apply,
    rest_phase_apply]
  simp only [proj_phase_apply, inner_smul_left, inner_smul_right, Complex.add_re,
    Complex.re_sum]
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases y i <;> cases y' i <;> simp <;> ring

/-- **Bessel's inequality** for a projection family: `Σ_i ‖P_i v‖² ≤ ‖v‖²`. -/
theorem sum_norm_proj_sq_le (P : ProjFamily K I) (v : K) :
    ∑ i, ‖P.proj i v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [Helpers.Adversary.norm_sq_eq_add_sum P.rest P.proj P.isStarProjection_rest
    P.isStarProjection (by rw [ProjFamily.rest, sub_add_cancel]) v]
  exact le_add_of_nonneg_left (sq_nonneg _)

end

end SparseLowerBounds.PositiveAdversary
end
