import ODELowerBoundExtensions.Dyson.Family.Theorem
import ODELowerBoundExtensions.Release.Strip
import ODELowerBoundExtensions.Dyson.Fixed
import ODELowerBoundExtensions.Release.Model

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Eq. `odel:eq:fixed` and its consequence for the ODE lower-bound class

Manuscript lines 4256-4268: "At fixed positive `s, τ, ḡ`, this gives
`Q_A = O(log(1/ε)/log log(1/ε))` (`ε → 0`). Consequently a uniform worst-case lower bound
proportional to `ḡ √s τ log(ḡ/ε)` is false under these access assumptions: fixing any admissible
positive `s, τ, ḡ` makes the auxiliary upper bound sublinear in `log(1/ε)`."

The statements use the vocabulary of the retry-protocol lower bound
(`ODELowerBoundExtensions.Release`): a `RetrySolver F (F.access ι) E G ε` is a release-style
bounded retry protocol (`ODERepeatProtocol.Protocol`) over the class's own sampled-time access
`F.access ι` with an isometric readout, success at least `2/3` on every input and conditional
output `ε`-close in trace distance (observable form `DensityAccurate`); `RetryForces` and
`RetryWitnesses` are the lower-bound predicates of that class. The Dyson protocols of
`family_dyson` (Certificate layer, idle source vocabulary) become retry solvers by removing the
idle vocabulary (`Release.stripIdle`, `Release.mapProtocol`, `Release/Strip`) and reading the
released output through the clean readout `endpointReadout 1 i₀`
(`Release.certificate_densityAccurate`).

* `retrySolver_dyson`: every family of the class (`InClass η ḡ`, `T > 0`) has a retry solver
  over `F.access ι` with worst-case query count at most `dysonBound (s η T) ḡ ε`
  (eq. `odel:eq:dyson`). A family without inputs is solved by the zero-query protocol.
* `retry_fixed`: eq. `odel:eq:fixed` for `Q_A`, at fixed `s, τ, ḡ` and uniformly in `η` (every
  family of `InClass η ḡ` with `T η = τ`, for every `η > 0`): worst-case queries at most
  `C log(1/ε)/log log(1/ε)` for all small `ε`, with `C` and the threshold depending on `s, τ, ḡ`
  only.
* `no_uniform_lower_bound`: for every `c > 0` and all small `ε` (threshold depending on
  `s, τ, ḡ, c` only), every family of the class `InClass η ḡ` with `T η = τ`, for every `η > 0`,
  has a retry solver with fewer than `c ḡ √s τ log(ḡ/ε)` queries.
* `no_retry_witnesses`: the consequence in the package vocabulary (`η = 1`, as in
  `RetryWitnesses` and `SparseLowerBounds.ODE.Family.Witnesses`): for all small `ε` no family
  retry-witnesses the bound `c ḡ √s τ log(ḡ/ε)`.

**Scope.** The refutation concerns the retry class (which contains every single-program
`SparseLowerBounds.ODE.Solver`, `Release/Embed`, and the released solvers). It does not refute a
uniform bound for the single-program class `SparseLowerBounds.ODE.Family.Forces` alone: the Dyson
solver uses randomized amplification cutoffs and four attempts, and `RetryForces → Forces` holds
in one direction only. No positivity of `s` or of the source mass is assumed: a family has
`s > 0` (`Data.slots_pos`), and a family of the class with an input has `B > 0`, since zero data
force `x(T) = 0`.
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators

/-- The system space `ℂ^N` has an isometric readout onto system ⊗ garbage `ℂ^N`: the clean
readout `endpointReadout 1 i₀` when `N` is nonempty, and `0` on the zero space otherwise. -/
theorem retry_exists_isometric_readout (N : Type) [Fintype N] [DecidableEq N] :
    ∃ e : EuclideanSpace ℂ N →L[ℂ] SysGarb N (EuclideanSpace ℂ N), e† ∘L e = 1 := by
  by_cases hN : Nonempty N
  · obtain ⟨i₀⟩ := hN
    exact ⟨_, Hamiltonian.endpointReadout_isometry 1 (by ext; simp) i₀⟩
  · refine ⟨0, ContinuousLinearMap.ext fun v => ?_⟩
    have hv : v = 0 := by
      ext i
      exact (hN ⟨i⟩).elim
    subst hv
    simp

set_option maxHeartbeats 4000000 in
/-- **The Dyson solver as a retry solver of the ODE lower-bound class** (Lemma `odel:lem:dyson`,
lines 4155-4168): every family in the class `InClass η ḡ` with `T > 0` has, for `0 < ε ≤ 1`, a
release-style retry solver over its own access `F.access ι` whose worst-case query count (all
labels, inverse calls included) is at most `dysonBound (s η T) ḡ ε`. -/
theorem retrySolver_dyson {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
    {K s : ℕ} (F : Family X N Z K s) (η gbar ε : ℝ) (hF : F.InClass η gbar) (hη : 0 < η)
    (hT : 0 < F.T) (hg : 1 ≤ gbar) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (ι : Type) (_ : Fintype ι)
      (A : Release.RetrySolver F (F.access ι) (EuclideanSpace ℂ N) (EuclideanSpace ℂ N) ε),
      (A.prot.worstCost (fun _ => 1) : ℝ) ≤ dysonBound ((s : ℝ) * η * F.T) gbar ε := by
  classical
  have hs : (0 : ℝ) < s := Nat.cast_pos.mpr F.data.slots_pos
  have hB := dysonBound_pos (mul_pos (mul_pos hs hη) hT) hg hε hε1
  by_cases hX : Nonempty X
  swap
  · obtain ⟨e, he⟩ := retry_exists_isometric_readout N
    refine ⟨Unit, inferInstance, ⟨.abort, e, he, fun x => (hX ⟨x⟩).elim,
      fun x _ _ => (hX ⟨x⟩).elim⟩, ?_⟩
    simpa [ODERepeatProtocol.Protocol.worstCost] using hB.le
  obtain ⟨x₀⟩ := hX
  obtain ⟨sol₀, hs₀, hne₀, -⟩ := hF.solution x₀
  obtain ⟨i₀, -⟩ : ∃ i, sol₀ F.T i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne₀ (by ext i; simpa using hcon i)
  obtain ⟨ι, hι, q, M, ψ, out, g', ell, hbound, cert⟩ :=
    family_dyson F η gbar ε hF hη hT hg hε hε1
  have h₀ := cert x₀ sol₀ hs₀
  refine ⟨ι, hι, ⟨Release.mapProtocol Release.stripIdle (ODECompleteTrial.algorithm h₀.trial),
    Hamiltonian.endpointReadout 1 i₀, Hamiltonian.endpointReadout_isometry 1 (by ext; simp) i₀,
    ?_, ?_⟩, ?_⟩
  · intro x
    obtain ⟨sol, hsol, -⟩ := hF.solution x
    rw [Release.mapProtocol_successMass Release.stripIdle Release.stripIdle_eval]
    exact (cert x sol hsol).success_two_thirds
  · intro x sol hsol
    rw [Release.mapProtocol_conditionalDensity Release.stripIdle Release.stripIdle_eval]
    exact Release.certificate_densityAccurate (cert x sol hsol) i₀
  · rw [Release.mapProtocol_worstCost Release.stripIdle (fun _ => 1)
      (ODESourceQueryBudget.matrixWeight (fun _ => 1)) (fun p => Release.stripIdle_cost p _)]
    exact h₀.matrix_queries.trans hbound

/-- A family of the class with `T η = τ`, `η > 0` and `τ > 0` has `T > 0`. -/
theorem retry_time_pos_of_mul_eq {X N Z : Type} [Fintype N] [DecidableEq N] {K s : ℕ}
    (F : Family X N Z K s) {η τ : ℝ} (hη : 0 < η) (hτ : 0 < τ) (hTη : F.T * η = τ) :
    0 < F.T := by
  by_contra h
  push Not at h
  nlinarith

/-- **Eq. `odel:eq:fixed` for the ODE lower-bound class** (lines 4256-4261): at fixed `s`,
`τ` and `ḡ`, there are `C` and `ε₀ ∈ (0, 1)` such that for every `ε ≤ ε₀`, uniformly in `η > 0`,
every family of the class `InClass η ḡ` with `T η = τ` has a retry solver over its own access with
at most `C log(1/ε)/log log(1/ε)` queries in the worst case. -/
theorem retry_fixed (s : ℕ) (τ gbar : ℝ) (hτ : 0 < τ) (hg : 1 ≤ gbar) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ η : ℝ, 0 < η →
      ∀ {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {K : ℕ}
        (F : Family X N Z K s), F.InClass η gbar → F.T * η = τ →
        ∃ (ι : Type) (_ : Fintype ι)
          (A : Release.RetrySolver F (F.access ι) (EuclideanSpace ℂ N) (EuclideanSpace ℂ N) ε),
          (A.prot.worstCost (fun _ => 1) : ℝ) ≤
            C * (Real.log (1 / ε) / Real.log (Real.log (1 / ε))) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · refine ⟨0, 1 / 2, by norm_num, by norm_num, ?_⟩
    intro ε _ _ η _ X N Z _ _ _ _ K F
    exact absurd F.data.slots_pos (lt_irrefl 0)
  · have hsτ : 0 < (s : ℝ) * τ := mul_pos (Nat.cast_pos.mpr hs) hτ
    obtain ⟨C, ε₀, hε₀, hε₀1, hC⟩ := dyson_fixed _ gbar hsτ hg
    refine ⟨C, ε₀, hε₀, hε₀1, ?_⟩
    intro ε hε hεle η hη X N Z _ _ _ _ K F hF hTη
    have hT := retry_time_pos_of_mul_eq F hη hτ hTη
    have hz : (s : ℝ) * η * F.T = s * τ := by rw [← hTη]; ring
    obtain ⟨ι, hι, A, hA⟩ :=
      retrySolver_dyson F η gbar ε hF hη hT hg hε (hεle.trans hε₀1.le)
    rw [hz] at hA
    exact ⟨ι, hι, A, hA.trans (hC ε hε hεle)⟩

/-- **No uniform `ḡ √s τ log(ḡ/ε)` lower bound for retry protocols** (lines 4262-4265): at fixed
`s, τ, ḡ`, for every `c > 0` and all sufficiently small `ε` (threshold independent of `η`), every
family of the class `InClass η ḡ` with `T η = τ`, for every `η > 0`, has a release-style retry
solver over its own access `F.access ι` with fewer than `c ḡ √s τ log(ḡ/ε)` queries in the worst
case. -/
theorem no_uniform_lower_bound (s : ℕ) (τ gbar c : ℝ) (hτ : 0 < τ) (hg : 1 ≤ gbar)
    (hc : 0 < c) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ η : ℝ, 0 < η →
      ∀ {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {K : ℕ}
        (F : Family X N Z K s), F.InClass η gbar → F.T * η = τ →
        ∃ (ι : Type) (_ : Fintype ι)
          (A : Release.RetrySolver F (F.access ι) (EuclideanSpace ℂ N) (EuclideanSpace ℂ N) ε),
          (A.prot.worstCost (fun _ => 1) : ℝ) <
            c * gbar * Real.sqrt s * τ * Real.log (gbar / ε) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · refine ⟨1 / 2, by norm_num, ?_⟩
    intro ε _ _ η _ X N Z _ _ _ _ K F
    exact absurd F.data.slots_pos (lt_irrefl 0)
  · obtain ⟨ε₁, hε₁, h₁⟩ := eventually_lt (s : ℝ) τ gbar c (Nat.cast_pos.mpr hs) hτ hg hc
    refine ⟨min ε₁ 1, lt_min hε₁ one_pos, ?_⟩
    intro ε hε hεle η hη X N Z _ _ _ _ K F hF hTη
    have hT := retry_time_pos_of_mul_eq F hη hτ hTη
    have hz : (s : ℝ) * η * F.T = s * τ := by rw [← hTη]; ring
    obtain ⟨ι, hι, A, hA⟩ :=
      retrySolver_dyson F η gbar ε hF hη hT hg hε (hεle.trans (min_le_right _ _))
    rw [hz] at hA
    exact ⟨ι, hι, A, hA.trans_lt (h₁ ε hε (hεle.trans (min_le_left _ _)))⟩

/-- **The consequence of Lemma `odel:lem:dyson` in the package vocabulary** (lines 4262-4265):
for fixed `s`, `τ > 0`, `ḡ ≥ 1` and every `c > 0`, for all sufficiently small `ε` no family
retry-witnesses the bound `c ḡ √s τ log(ḡ/ε)` (`Release.RetryWitnesses`: in the class with
`η = 1`, `T = τ`, `g ≤ ḡ`, and every retry solver over `F.access ι` needs that many queries). -/
theorem no_retry_witnesses (s : ℕ) (τ gbar c : ℝ) (hτ : 0 < τ) (hg : 1 ≤ gbar) (hc : 0 < c) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {K : ℕ}
        (F : Family X N Z K s),
        ¬ Release.RetryWitnesses F τ gbar ε (c * gbar * Real.sqrt s * τ * Real.log (gbar / ε)) := by
  obtain ⟨ε₀, hε₀, h⟩ := no_uniform_lower_bound s τ gbar c hτ hg hc
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεle X N Z _ _ _ _ K F hW
  obtain ⟨ι, hι, A, hA⟩ :=
    h ε hε hεle 1 one_pos F hW.inClass (by rw [hW.time_eq, mul_one])
  have hb := (hW.forces ι (EuclideanSpace ℂ N) (EuclideanSpace ℂ N) A).2
  linarith

end

end ODELowerBoundExtensions.Dyson
