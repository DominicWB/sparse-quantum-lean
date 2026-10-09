import IntegrablePathSimulation.Propagator.Basic
import TimeDependentExtensions.Mesh.Duhamel

set_option autoImplicit false

/-!
# Classical and piecewise propagators are propagators

The released time-dependent theorems use classical propagators: `SolvesOn` (a derivative at
every point of a closed interval) and, for paths with breakpoints at the mesh points,
`TimeDependentExtensions.IsPiecewisePropagator` (`U 0 = 1` and `SolvesOn` of the piece `H_r`
on every mesh interval). This module shows that both are propagators in the integral sense of
`Propagator.Basic`, provided the generators are interval integrable.

* `solvesIntegralOn_of_solvesOn`: a classical solution with an interval-integrable generator
  is an integral-sense solution; `isPropagator_of_solvesOn` on `[0, T]`.
* `pieceIndex t M u`: the last `r ≤ M - 1` with `t r ≤ u`, the mesh interval used at time `u`;
  `glue Hp t M u = Hp (pieceIndex t M u) u` is the single path glued from the pieces. It
  agrees with the piece `Hp r` on `[t_r, t_{r+1})` (`glue_eq_of_mem_Ico`), hence almost
  everywhere on `[t_r, t_{r+1}]` (`glue_ae_eq`).
* `solvesIntegralOn_glue`: a classical solution of the pieces `a, …, b - 1` with
  interval-integrable pieces solves the integral equation of the glued path on the window
  `[t_a, t_b]`; `isPropagator_glue`: every piecewise propagator with interval-integrable pieces
  is a propagator of the glued path.

Integrability cannot be dropped: in one dimension `U(u) = exp(-i φ(u))` with
`φ(u) = u² sin(1/u²)` solves `U' = -i φ' U` at every point, but `φ'` is not Lebesgue integrable
near `0`, so `U` does not solve the integral equation.
-/

namespace IntegrablePathSimulation.Propagator

noncomputable section

open MeasureTheory Set Filter
open SparseHamiltonian.TimeDependent (SolvesOn)
open TimeDependentExtensions (IsMesh IsPiecewisePropagator)
open scoped Topology

/-! ### Classical solutions -/

section Classical

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

variable {H U : ℝ → P →L[ℂ] P} {a b T : ℝ}

/-- A classical solution of `U' = -i H U` on `[a, b]` with an interval-integrable generator
solves the integral equation on `[a, b]`. -/
theorem solvesIntegralOn_of_solvesOn (hab : a ≤ b) (hU : SolvesOn H U a b)
    (hint : IntervalIntegrable H volume a b) : SolvesIntegralOn H U a b := by
  have hUc : ContinuousOn U (Icc a b) := fun u hu => (hU u hu).continuousWithinAt
  have hHU : IntervalIntegrable (fun u => H u * U u) volume a b :=
    hint.mul_continuousOn (by rwa [uIcc_of_le hab])
  refine ⟨hHU, fun s hs => ?_⟩
  have hint' : IntervalIntegrable (fun u => (-Complex.I) • (H u * U u)) volume a s :=
    (hHU.smul (-Complex.I)).mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le hs.1]
      exact Icc_subset_Icc le_rfl hs.2)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1
    (hUc.mono (Icc_subset_Icc le_rfl hs.2))
    (fun u hu => (hU u ⟨hu.1.le, hu.2.le.trans hs.2⟩).hasDerivAt
      (Icc_mem_nhds hu.1 (hu.2.trans_le hs.2))) hint'
  rw [hftc]
  abel

/-- A classical propagator from the identity on `[0, T]` with an interval-integrable generator
is a propagator. -/
theorem isPropagator_of_solvesOn (hT : 0 ≤ T) (hU0 : U 0 = 1) (hU : SolvesOn H U 0 T)
    (hint : IntervalIntegrable H volume 0 T) : IsPropagator H U T :=
  ⟨hU0, solvesIntegralOn_of_solvesOn hT hU hint⟩

end Classical

/-! ### Gluing the pieces of a piecewise path -/

section Glue

/-- The mesh interval used at time `u`: the last `r ≤ M - 1` with `t r ≤ u` (and `0` if there
is none). -/
def pieceIndex (t : ℕ → ℝ) (M : ℕ) (u : ℝ) : ℕ := by
  classical exact Nat.findGreatest (fun r => t r ≤ u) (M - 1)

/-- The single path glued from the pieces `Hp r`: at time `u` it is the piece of the mesh
interval `pieceIndex t M u`. -/
def glue {E : Type*} (Hp : ℕ → ℝ → E) (t : ℕ → ℝ) (M : ℕ) (u : ℝ) : E :=
  Hp (pieceIndex t M u) u

variable {t : ℕ → ℝ} {M : ℕ} {T : ℝ}

/-- The glued index is a mesh interval. -/
theorem pieceIndex_lt (hM : 0 < M) (u : ℝ) : pieceIndex t M u < M := by
  unfold pieceIndex
  exact lt_of_le_of_lt (Nat.findGreatest_le _) (by omega)

/-- On `[t_r, t_{r+1})` the glued index is `r`. -/
theorem pieceIndex_eq (h : IsMesh t M T) {r : ℕ} (hr : r < M) {u : ℝ}
    (hu : u ∈ Ico (t r) (t (r + 1))) : pieceIndex t M u = r := by
  unfold pieceIndex
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by omega, fun _ => hu.1, fun n hn _ hle => ?_⟩
  exact lt_irrefl u ((hu.2.trans_le (h.mono (Nat.succ_le_of_lt hn))).trans_le hle)

/-- Every time of `[0, T]` lies in the mesh interval of its glued index. -/
theorem mem_Icc_pieceIndex (h : IsMesh t M T) (hM : 0 < M) {u : ℝ} (hu : u ∈ Icc 0 T) :
    u ∈ Icc (t (pieceIndex t M u)) (t (pieceIndex t M u + 1)) := by
  have hlow : t (pieceIndex t M u) ≤ u := by
    unfold pieceIndex
    exact Nat.findGreatest_spec (P := fun r => t r ≤ u) (m := 0) (Nat.zero_le _)
      (show t 0 ≤ u by rw [h.zero]; exact hu.1)
  have hjlt := pieceIndex_lt (t := t) hM u
  refine ⟨hlow, ?_⟩
  by_cases hj : pieceIndex t M u + 1 ≤ M - 1
  · unfold pieceIndex at hj ⊢
    exact le_of_lt (not_le.1 (Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hj))
  · have hlast : pieceIndex t M u + 1 = M := by omega
    rw [hlast, h.last]
    exact hu.2

/-- On `[t_r, t_{r+1})` the glued path is the piece `Hp r`. -/
theorem glue_eq_of_mem_Ico {E : Type*} (Hp : ℕ → ℝ → E) (h : IsMesh t M T) {r : ℕ}
    (hr : r < M) {u : ℝ} (hu : u ∈ Ico (t r) (t (r + 1))) : glue Hp t M u = Hp r u := by
  rw [glue, pieceIndex_eq h hr hu]

/-- The glued path agrees with the piece `Hp r` almost everywhere on `(t_r, t_{r+1}]`. -/
theorem glue_ae_eq {E : Type*} (Hp : ℕ → ℝ → E) (h : IsMesh t M T) {r : ℕ} (hr : r < M) :
    ∀ᵐ u, u ∈ Ioc (t r) (t (r + 1)) → glue Hp t M u = Hp r u := by
  have hnull : ∀ᵐ u : ℝ, u ≠ t (r + 1) := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hnull] with u hu hmem
  exact glue_eq_of_mem_Ico Hp h hr ⟨hmem.1.le, lt_of_le_of_ne hmem.2 hu⟩

/-- The glued path of interval-integrable pieces is interval integrable on `[0, T]`. -/
theorem intervalIntegrable_glue {E : Type*} [NormedAddCommGroup E] {Hp : ℕ → ℝ → E}
    (h : IsMesh t M T)
    (hint : ∀ r < M, IntervalIntegrable (Hp r) volume (t r) (t (r + 1))) :
    IntervalIntegrable (glue Hp t M) volume 0 T := by
  have key : ∀ k < M, IntervalIntegrable (glue Hp t M) volume (t k) (t (k + 1)) := by
    intro k hk
    have hle : t k ≤ t (k + 1) := h.mono (Nat.le_succ k)
    have hk' := hint k hk
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle] at hk' ⊢
    refine hk'.congr_fun_ae ?_
    exact (ae_restrict_iff' measurableSet_Ioc).2
      ((glue_ae_eq Hp h hk).mono fun u hu hmem => (hu hmem).symm)
  have hall := IntervalIntegrable.trans_iterate key
  rwa [h.zero, h.last] at hall

/-- **Containment on a window**: a classical solution of the pieces `a, …, b - 1` on their
intervals, with interval-integrable pieces, solves the integral equation of the glued path on
`[t_a, t_b]`. -/
theorem solvesIntegralOn_glue {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [CompleteSpace P] {Hp : ℕ → ℝ → P →L[ℂ] P} {U : ℝ → P →L[ℂ] P} (h : IsMesh t M T)
    {a b : ℕ} (hab : a ≤ b) (hbM : b ≤ M)
    (hU : ∀ r, a ≤ r → r < b → SolvesOn (Hp r) U (t r) (t (r + 1)))
    (hint : ∀ r, a ≤ r → r < b → IntervalIntegrable (Hp r) volume (t r) (t (r + 1))) :
    SolvesIntegralOn (glue Hp t M) U (t a) (t b) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero =>
    refine ⟨IntervalIntegrable.refl, fun s hs => ?_⟩
    have hs' : s = t (a + 0) := le_antisymm hs.2 hs.1
    subst hs'
    simp
  | succ d ih =>
    have hr : a + d < M := by omega
    have h1 := ih (by omega) (by omega) (fun r h1 h2 => hU r h1 (by omega))
      (fun r h1 h2 => hint r h1 (by omega))
    have hle : t (a + d) ≤ t (a + d + 1) := h.mono (Nat.le_succ (a + d))
    have h2 := (solvesIntegralOn_of_solvesOn hle (hU (a + d) (by omega) (by omega))
      (hint (a + d) (by omega) (by omega))).congr_ae hle
      ((glue_ae_eq Hp h hr).mono fun u hu hmem => (hu hmem).symm)
    exact h1.trans (h.mono (by omega)) hle h2

/-- **Containment**: a piecewise propagator with interval-integrable pieces is a propagator of
the glued path. -/
theorem isPropagator_glue {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [CompleteSpace P] {Hp : ℕ → ℝ → P →L[ℂ] P} {U : ℝ → P →L[ℂ] P} (h : IsMesh t M T)
    (hU : IsPiecewisePropagator Hp t M U)
    (hint : ∀ r < M, IntervalIntegrable (Hp r) volume (t r) (t (r + 1))) :
    IsPropagator (glue Hp t M) U T := by
  have hglue := solvesIntegralOn_glue h (Nat.zero_le M) le_rfl
    (fun r _ hr => hU.2 r hr) (fun r _ hr => hint r hr)
  rw [h.zero, h.last] at hglue
  exact ⟨hU.1, hglue⟩

end Glue

end

end IntegrablePathSimulation.Propagator
