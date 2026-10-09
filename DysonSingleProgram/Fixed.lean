import DysonSingleProgram.Theorem
import ODELowerBoundExtensions.Dyson.Fixed
import ODELowerBoundExtensions.Dyson.Family.Retry
import ODELowerBoundExtensions.Release.Embed
import AdaptiveODELowerBound.Model.Solver

set_option autoImplicit false

/-!
# Eq. `odel:eq:fixed` and its consequence for single heralded programs

Manuscript lines 4692-4701: "At fixed positive `s, τ, ḡ`, this gives
`Q_A = O(log(1/ε)/log log(1/ε))` (`ε → 0`). Consequently a uniform worst-case lower bound
proportional to `ḡ √s τ log(ḡ/ε)` is false under these access assumptions: fixing any admissible
positive `s, τ, ḡ` makes the auxiliary upper bound sublinear in `log(1/ε)`."

In the single-program class of the ODE lower bounds (`SparseLowerBounds.ODE.Solver`,
`Family.Forces`, `Family.Witnesses`), with the single heralded Dyson program of `solver_dyson`:

* `solver_fixed`: eq. `odel:eq:fixed`, at fixed `s, τ, ḡ` and uniformly in `η` (every family of
  `InClass η ḡ` with `T η = τ`, every `η > 0`): a single-program solver with at most
  `C log(1/ε)/log log(1/ε)` calls for all small `ε`, `C` and the threshold depending on
  `s, τ, ḡ` only;
* `no_uniform_lower_bound`: for every `c > 0` and all small `ε` (threshold depending on
  `s, τ, ḡ, c`), a single-program solver with fewer than `c ḡ √s τ log(ḡ/ε)` calls;
* `no_witnesses`: for all small `ε` no family witnesses the bound `c ḡ √s τ log(ḡ/ε)`
  (`Family.Witnesses`: in the class with `η = 1`, `T = τ`, `g ≤ ḡ`, and every single-program
  solver needs that many calls). Through `Release.retryWitnesses_witnesses`
  (`Release.RetryWitnesses → Family.Witnesses`) it implies the statement of
  `ODELowerBoundExtensions.Dyson.no_retry_witnesses`;
* `no_tree_witnesses`: the same for adaptive-tree witnesses
  (`AdaptiveODELowerBound.Model.TreeWitnesses`, via
  `AdaptiveODELowerBound.Model.treeWitnesses_witnesses`): for all small `ε` no family is, at
  once, in the class with `η = 1`, `T = τ`, `g ≤ ḡ` and such that every adaptive protocol over
  `F.access ι` and over its call forms `Access.callFamily (F.access ι)` needs
  `c ḡ √s τ log(ḡ/ε)` queries. It also follows from `Dyson.no_retry_witnesses` and
  `AdaptiveODELowerBound.Model.treeWitnesses_retryWitnesses`.

This answers the scope remark of `ODELowerBoundExtensions.Dyson` (`Dyson/Family/Retry.lean`,
which refutes the uniform bound for the retry class only): the uniform bound is refuted also for
the single-program class `Family.Forces`.
-/

namespace DysonSingleProgram

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE
open ODELowerBoundExtensions.Dyson (dysonBound)

/-- **Eq. `odel:eq:fixed` for single heralded programs** (lines 4692-4697): at fixed `s`, `τ > 0`
and `ḡ ≥ 1` there are `C` and `ε₀ ∈ (0, 1)` such that for every `ε ≤ ε₀`, uniformly in `η > 0`,
every family of the class `InClass η ḡ` with `T η = τ` has a single-program solver over its own
access with at most `C log(1/ε)/log log(1/ε)` calls. -/
theorem solver_fixed (s : ℕ) (τ gbar : ℝ) (hτ : 0 < τ) (hg : 1 ≤ gbar) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ η : ℝ, 0 < η →
      ∀ {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {K : ℕ}
        (F : Family X N Z K s), F.InClass η gbar → F.T * η = τ →
        ∃ (ι : Type) (_ : Fintype ι) (G : Type) (_ : NormedAddCommGroup G)
          (_ : InnerProductSpace ℂ G) (_ : CompleteSpace G) (A : Solver ι F G ε),
          (A.prog.count : ℝ) ≤ C * (Real.log (1 / ε) / Real.log (Real.log (1 / ε))) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · refine ⟨0, 1 / 2, by norm_num, by norm_num, ?_⟩
    intro ε _ _ η _ X N Z _ _ _ _ K F
    exact absurd F.data.slots_pos (lt_irrefl 0)
  · have hsτ : 0 < (s : ℝ) * τ := mul_pos (Nat.cast_pos.mpr hs) hτ
    obtain ⟨C, ε₀, hε₀, hε₀1, hC⟩ := ODELowerBoundExtensions.Dyson.dyson_fixed _ gbar hsτ hg
    refine ⟨C, ε₀, hε₀, hε₀1, ?_⟩
    intro ε hε hεle η hη X N Z _ _ _ _ K F hF hTη
    have hT := ODELowerBoundExtensions.Dyson.retry_time_pos_of_mul_eq F hη hτ hTη
    have hz : (s : ℝ) * η * F.T = s * τ := by rw [← hTη]; ring
    obtain ⟨ι, hι, G, i1, i2, i3, A, hA⟩ :=
      solver_dyson F η gbar ε hF hη hT hg hε (hεle.trans hε₀1.le)
    rw [hz] at hA
    exact ⟨ι, hι, G, i1, i2, i3, A, hA.trans (hC ε hε hεle)⟩

/-- **Single heralded programs beat `c ḡ √s τ log(ḡ/ε)`** (lines 4698-4701): at fixed `s`,
`τ > 0`, `ḡ ≥ 1` and every `c > 0`, for all sufficiently small `ε` (threshold independent of
`η`), every family of the class `InClass η ḡ` with `T η = τ`, for every `η > 0`, has a
single-program solver with fewer than `c ḡ √s τ log(ḡ/ε)` calls. -/
theorem no_uniform_lower_bound (s : ℕ) (τ gbar c : ℝ) (hτ : 0 < τ) (hg : 1 ≤ gbar)
    (hc : 0 < c) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ η : ℝ, 0 < η →
      ∀ {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {K : ℕ}
        (F : Family X N Z K s), F.InClass η gbar → F.T * η = τ →
        ∃ (ι : Type) (_ : Fintype ι) (G : Type) (_ : NormedAddCommGroup G)
          (_ : InnerProductSpace ℂ G) (_ : CompleteSpace G) (A : Solver ι F G ε),
          (A.prog.count : ℝ) < c * gbar * Real.sqrt s * τ * Real.log (gbar / ε) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · refine ⟨1 / 2, by norm_num, ?_⟩
    intro ε _ _ η _ X N Z _ _ _ _ K F
    exact absurd F.data.slots_pos (lt_irrefl 0)
  · obtain ⟨ε₁, hε₁, h₁⟩ := ODELowerBoundExtensions.Dyson.eventually_lt (s : ℝ) τ gbar c
      (Nat.cast_pos.mpr hs) hτ hg hc
    refine ⟨min ε₁ 1, lt_min hε₁ one_pos, ?_⟩
    intro ε hε hεle η hη X N Z _ _ _ _ K F hF hTη
    have hT := ODELowerBoundExtensions.Dyson.retry_time_pos_of_mul_eq F hη hτ hTη
    have hz : (s : ℝ) * η * F.T = s * τ := by rw [← hTη]; ring
    obtain ⟨ι, hι, G, i1, i2, i3, A, hA⟩ :=
      solver_dyson F η gbar ε hF hη hT hg hε (hεle.trans (min_le_right _ _))
    rw [hz] at hA
    exact ⟨ι, hι, G, i1, i2, i3, A, hA.trans_lt (h₁ ε hε (hεle.trans (min_le_left _ _)))⟩

/-- **No uniform `ḡ √s τ log(ḡ/ε)` lower bound for single heralded programs** (lines
4698-4701): for fixed `s`, `τ > 0`, `ḡ ≥ 1` and every `c > 0`, for all sufficiently small `ε` no
family witnesses the bound `c ḡ √s τ log(ḡ/ε)` (`Family.Witnesses`). -/
theorem no_witnesses (s : ℕ) (τ gbar c : ℝ) (hτ : 0 < τ) (hg : 1 ≤ gbar) (hc : 0 < c) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {K : ℕ}
        (F : Family X N Z K s),
        ¬ F.Witnesses τ gbar ε (c * gbar * Real.sqrt s * τ * Real.log (gbar / ε)) := by
  obtain ⟨ε₀, hε₀, h⟩ := no_uniform_lower_bound s τ gbar c hτ hg hc
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεle X N Z _ _ _ _ K F hW
  obtain ⟨ι, hι, G, i1, i2, i3, A, hA⟩ :=
    h ε hε hεle 1 one_pos F hW.inClass (by rw [hW.time_eq, mul_one])
  have hb := (hW.forces ι G A).2
  linarith

/-- **No uniform `ḡ √s τ log(ḡ/ε)` lower bound for adaptive protocols** (lines 4698-4701): for
fixed `s`, `τ > 0`, `ḡ ≥ 1` and every `c > 0`, for all sufficiently small `ε` no family
tree-witnesses the bound `c ḡ √s τ log(ḡ/ε)` (`AdaptiveODELowerBound.Model.TreeWitnesses`: in the
class with `η = 1`, `T = τ`, `g ≤ ḡ`, and every adaptive protocol over `F.access ι` and over its
call forms `Access.callFamily (F.access ι)` needs that many queries); a tree witness is a witness
(`AdaptiveODELowerBound.Model.treeWitnesses_witnesses`). The statement also follows from
`ODELowerBoundExtensions.Dyson.no_retry_witnesses` and
`AdaptiveODELowerBound.Model.treeWitnesses_retryWitnesses`. -/
theorem no_tree_witnesses (s : ℕ) (τ gbar c : ℝ) (hτ : 0 < τ) (hg : 1 ≤ gbar) (hc : 0 < c) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {K : ℕ}
        (F : Family X N Z K s),
        ¬ AdaptiveODELowerBound.Model.TreeWitnesses F τ gbar ε
          (c * gbar * Real.sqrt s * τ * Real.log (gbar / ε)) := by
  obtain ⟨ε₀, hε₀, h⟩ := no_witnesses s τ gbar c hτ hg hc
  exact ⟨ε₀, hε₀, fun ε hε hle X N Z _ _ _ _ K F hW =>
    h ε hε hle F (AdaptiveODELowerBound.Model.treeWitnesses_witnesses hW)⟩

end

end DysonSingleProgram
