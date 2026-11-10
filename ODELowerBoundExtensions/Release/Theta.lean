import ODELowerBoundExtensions.Release.Instances
import ODELowerBoundExtensions.Release.Bridge

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The released ODE solver on the hard families: the two-sided bracket

Manuscript: Theorem `odel:thm:combined` and its comparison with the upper bounds
eq. `odel:eq:upper` ("within one logarithm") and eq. `odel:eq:refined`
(`O(ḡ [√s Θ + √(sΘℓ) + ℓ])`, `Θ = τ_H + τ_D ℓ`; "The first family in Theorem `odel:thm:combined`
has `τ_D = 0`. It matches the time term of `odel:eq:refined`; on that subclass, the whole upper
bound matches when `τ ≥ ℓ`"). The analogue of `SparseLowerBounds.Hamiltonian.release_theta`.

**The release run.** `ReleaseRun F τ ḡ ε` is a release-form run on the family `F`
(`Release/Instances`); every output of the released general-mesh solver
`TimeDependentExtensions.ODE.solver` on `F` with public source interfaces is one, and the structure
asks for no more than the released certificate (it does not require the solver's preconditions or
that the degree is the solver's output). It carries a refinement `R > 0`, a slot count, a degree `d`
for which the certificate holds, **any** public source interfaces `J₀`, `J_b` (`PublicSources`:
unitary and input-independent, Section `odel:sec:main`; the solver accepts every unitary choice, and
the lower bound needs them public), and the four-attempt protocol over the release's physical oracle
with spectator index `Index (refineData F.data R) τ ḡ ε`, with the released complete certificate for
every input (`ReleaseProtocol`, `Θ = τ` since `D = 0`, `ℓ = releaseLog ḡ ε = log(40000 ḡ/ε)`,
`g = 2ḡ`); and a system index `i₀` for the clean garbage register of the readout. Its counts
`matrixQueries` and `valueQueries` are the worst-case numbers of matrix queries and of value queries
over all transcripts (every attempt and failure branch). Since the solver is a `Prop`-valued
existence theorem, "the released solver" is every `ReleaseRun`, together with the existence of one
(`release_theta_exists`, with the public preparations `releaseJ₀`, `releaseJb`).

**Statements** (`S = ḡ √s τ + √(sτr) + r`, `c = log 2/(8192π)`):

* `queryShape_le_mul`, `queryShape_le_of_le`: `√s τ + √(sτℓ) + ℓ ≤ 3 ℓ √s τ` for `s, τ, ℓ ≥ 1`,
  and `≤ 3 √s τ` when `ℓ ≤ τ`; `release_shape_le`: `ḡ queryShape(s, τ, ℓ) ≤ 3 ℓ S` on
  `CombinedRange`.
* `release_theta`: for any release runs on the joint, mixed and precision families,
  `c S ≤ max(Q_J, Q_M, Q_P) ≤ 2548039680 ḡ (√s τ + √(sτℓ) + ℓ) ≤ 7644119040 ℓ S`, the same middle
  term is at most `7644119040 ḡ √s τ ℓ` (the paper's headline form `O(ḡ √s τ ℓ)` of eq.
  `odel:eq:upper`), and the value counts satisfy `c S ≤ max(V_J, V_M, V_P) ≤ max(Q_J, Q_M, Q_P)`
  (lower half `Release.combined_max_release` along `σ = stageOf K R`, upper half
  `Certificate.matrix_queries`, `1274019840 · 2ḡ`).
* `release_theta_exists`, `release_theta_bracket`: such runs exist (`exists_releaseProtocol`,
  `exists_release_params`), so the bracket is attained.
* `joint_release_theta`: on the joint family alone (`D = 0`, `g = Θ(ḡ)`), when `τ ≥ ℓ`,
  `ḡ √s τ / 400 ≤ Q_J ≤ 7644119040 ḡ √s τ`: upper and lower bounds match up to an absolute
  constant (Section `odel:sec:main`).

**The gap.** On the whole class the bracket is within the factor `3ℓ` of eq. `odel:eq:upper`; the
two precision terms of the upper bound carry the factor `ḡ` and `ℓ` in place of `r`, which the lower
bound does not. As for `release_theta`, the lower half is on the maximum over the three families,
not on one program: the families have different input, index and word types, and the padding to a
common dimension is not part of this module.

**Scope.** Only the general-mesh released solver (Theorem `ode:thm:time`) is connected. The
constant-coefficient released solver `SparseHamiltonian.ODECompleteEndpoint.solver` (Theorem
`ode:thm:main`) is not; the general-mesh solver covers the same hard families, all of which have
piecewise-constant coefficients. The names `release_shape_le`, `release_theta`,
`release_theta_exists` and `release_theta_bracket` repeat those of `SparseLowerBounds.Hamiltonian`;
this module opens that namespace selectively, and other modules cite these with the `Release.`
prefix.
-/

namespace ODELowerBoundExtensions.Release

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE
open SparseLowerBounds.Hamiltonian (hsR)
open NativeSparseBlockEncoding OracleCircuit TimeDependentExtensions

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

/-- **A release-form run on the family `F`** at `(τ, ḡ, ε)`: a four-attempt protocol
`ODECompleteTrial.algorithm` over the release's physical oracle on the `R`-fold refinement, with
public source interfaces, that carries the released complete certificate for every input
(`ReleaseProtocol`). Every output of `TimeDependentExtensions.ODE.solver` on `F` with public
source interfaces is one (`exists_releaseProtocol`); the structure does not require the solver's
own preconditions or that `degree` is the solver's output, so it is a superset of the solver's
outputs, which only strengthens the statements quantified over it. -/
structure ReleaseRun {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
    [DecidableEq Z] {K s : ℕ} (F : Family X N Z K s) (τ gbar ε : ℝ) where
  /-- A system index, the clean garbage register of the readout `endpointReadout 1 i₀`. -/
  i₀ : N
  /-- The refinement of the stages. -/
  R : ℕ
  R_pos : 0 < R
  /-- The number of slots of the SELECT. -/
  slots : ℕ
  /-- A degree for which the released certificate holds. -/
  degree : ℕ
  /-- The initial-state interface. -/
  J₀ : X → SysOp N
  /-- The forcing interface on the refined mesh. -/
  Jb : X → Fin (K * R) → SysOp N
  /-- The source interfaces are public (unitary and input-independent). -/
  sources_public : PublicSources J₀ Jb
  /-- A four-attempt protocol of the released form. -/
  prot : ODERepeatProtocol.Protocol
    (releaseOracle F R (TimeDependentODE.Index (refineData F.data R) τ gbar ε) slots degree J₀ Jb)
    (EuclideanSpace ℂ N)
  /-- The released complete certificate for every input. -/
  release : ReleaseProtocol F R (TimeDependentODE.Index (refineData F.data R) τ gbar ε) slots
    degree J₀ Jb prot τ (releaseLog gbar ε) (TimeDependentODE.ratio gbar) ε

/-- The worst-case number of matrix queries of a release run (row, column and value calls,
inverses included, over all transcripts). -/
def ReleaseRun.matrixQueries {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] [DecidableEq Z] {K s : ℕ} {F : Family X N Z K s} {τ gbar ε : ℝ}
    (A : ReleaseRun F τ gbar ε) : ℕ :=
  A.prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))

/-- The worst-case number of value queries of a release run (value calls, inverses included, over
all transcripts; location and source calls weigh `0`). -/
def ReleaseRun.valueQueries {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] [DecidableEq Z] {K s : ℕ} {F : Family X N Z K s} {τ gbar ε : ℝ}
    (A : ReleaseRun F τ gbar ε) : ℕ :=
  A.prot.worstCost
    (ODESourceQueryBudget.matrixWeight AdaptiveHamiltonianLowerBound.Access.valueWeight)

/-- A release run makes at most as many value queries as matrix queries. -/
theorem ReleaseRun.valueQueries_le {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] [DecidableEq Z] {K s : ℕ} {F : Family X N Z K s} {τ gbar ε : ℝ}
    (A : ReleaseRun F τ gbar ε) : A.valueQueries ≤ A.matrixQueries :=
  worstCost_mono A.prot fun l => by
    rcases l with q | b
    · cases q <;> simp [ODESourceQueryBudget.matrixWeight,
        AdaptiveHamiltonianLowerBound.Access.valueWeight]
    · simp [ODESourceQueryBudget.matrixWeight]

/-- `√s u + √(s u L) + L ≤ 3 L √s u` for `s, u, L ≥ 1`. -/
theorem queryShape_le_mul {s u L : ℝ} (hs : 1 ≤ s) (hu : 1 ≤ u) (hL : 1 ≤ L) :
    ImprovedODEQueryBudget.queryShape s u L ≤ 3 * L * (Real.sqrt s * u) := by
  have hs0 : 1 ≤ Real.sqrt s := Real.one_le_sqrt.mpr hs
  have hA : 1 ≤ Real.sqrt s * u := by nlinarith
  have huL : 1 ≤ u * L := by nlinarith
  have hsq : Real.sqrt (u * L) ≤ u * L := by
    calc Real.sqrt (u * L) ≤ Real.sqrt ((u * L) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = u * L := Real.sqrt_sq (by linarith)
  have hmid : Real.sqrt (s * u * L) ≤ L * (Real.sqrt s * u) := by
    rw [mul_assoc, Real.sqrt_mul (by linarith)]
    nlinarith
  unfold ImprovedODEQueryBudget.queryShape
  nlinarith

/-- `√s u + √(s u L) + L ≤ 3 √s u` for `s ≥ 1` and `0 ≤ L ≤ u`. -/
theorem queryShape_le_of_le {s u L : ℝ} (hs : 1 ≤ s) (hL : 0 ≤ L) (hLu : L ≤ u) :
    ImprovedODEQueryBudget.queryShape s u L ≤ 3 * (Real.sqrt s * u) := by
  have hs0 : 1 ≤ Real.sqrt s := Real.one_le_sqrt.mpr hs
  have hu : 0 ≤ u := hL.trans hLu
  have hmid : Real.sqrt (s * u * L) ≤ Real.sqrt s * u := by
    calc Real.sqrt (s * u * L) ≤ Real.sqrt (s * u * u) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hLu (by nlinarith))
      _ = Real.sqrt s * u := by
          rw [mul_assoc, Real.sqrt_mul (by linarith), Real.sqrt_mul_self hu]
  have hLs : L ≤ Real.sqrt s * u := by nlinarith
  unfold ImprovedODEQueryBudget.queryShape
  linarith

/-- `ℓ ≥ 1` for `ḡ ≥ 1` and `0 < ε ≤ 1` (`ImprovedODEQueryBudget.logBudget_ge_one` at
`g = 2ḡ`, accuracy `ε/2`). -/
theorem one_le_releaseLog_of {gbar ε : ℝ} (hg : 1 ≤ gbar) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ releaseLog gbar ε :=
  ImprovedODEQueryBudget.logBudget_ge_one _ _
    (by unfold TimeDependentODE.ratio; linarith)
    (by unfold TimeDependentODE.accuracy; linarith)
    (by unfold TimeDependentODE.accuracy; linarith)

/-- **The released query bound for a release run**: `Q ≤ 2548039680 ḡ queryShape(s, τ, ℓ)`
(`ReleaseProtocol.worstCost_le` with `g = ratio ḡ = 2ḡ`), given one input with a solution. -/
theorem ReleaseRun.matrixQueries_le {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] [DecidableEq Z] {K s : ℕ} {F : Family X N Z K s} {τ gbar ε : ℝ}
    (A : ReleaseRun F τ gbar ε) (x : X) (sol : ℝ → EuclideanSpace ℂ N) (hs : F.Solves x sol) :
    (A.matrixQueries : ℝ) ≤
      2548039680 * gbar * ImprovedODEQueryBudget.queryShape s τ (releaseLog gbar ε) := by
  have h := A.release.worstCost_le x sol hs
  unfold TimeDependentODE.ratio at h
  exact h.trans (le_of_eq (by ring))

/-- **A release run exists** on a family of the class with `D = 0`, `T = τ`, positive mass and
`K > 0`, with the public preparations `releaseJ₀`, `releaseJb` and the seed `e_{i₀}`
(`exists_release_params`, `exists_releaseProtocol`). -/
theorem releaseRun_nonempty {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] [DecidableEq Z] {K s : ℕ} (F : Family X N Z K s) {τ gbar ε : ℝ}
    (hF : F.InClass 1 gbar)
    (hskew : ∀ x k, ∃ H : Matrix N N ℂ, H.IsHermitian ∧ F.data.matrix (x, k) = Complex.I • H)
    (hT : F.T = τ) (hτ : 0 < τ) (hg : 1 ≤ gbar) (hε : 0 < ε) (hε1 : ε ≤ 1) (hB : 0 < F.mass)
    (hK : 0 < K) (i₀ : N) : Nonempty (ReleaseRun F τ gbar ε) := by
  obtain ⟨R, hR, Nsl, hN, hClock, hCayley, hErr⟩ := exists_release_params F hτ hg hε hB
  have hP := releaseSources_public F R i₀
  obtain ⟨d, p, hp⟩ := exists_releaseProtocol F hF hskew hT hτ hg hε hε1 hB hK R hR Nsl hN
    hClock hCayley hErr (releaseJ₀ F i₀) (releaseJb F R i₀) hP.initial_unitary
    hP.forcing_unitary (seedVec i₀) (norm_seedVec i₀) (fun h0 _ => prepUnitary_seed i₀ h0)
    (fun _ _ h0 => prepUnitary_seed i₀ h0)
  exact ⟨⟨i₀, R, hR, Nsl, d, releaseJ₀ F i₀, releaseJb F R i₀, hP, p, hp⟩⟩

/-- The joint family's input set is nonempty on `JointRange` (`nonempty_promised`). -/
theorem joint_nonempty {s : ℕ} {τ gbar ε : ℝ} (h : JointRange s τ gbar ε) :
    Nonempty (Promised (jointM gbar) (jointN τ) (2 ^ jointMu s)) := by
  have hM := four_le_jointM h.gbar_ge
  have hs := h.s_ge
  refine nonempty_promised (by omega) (one_le_jointN h.tau_ge) ?_
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ jointMu s := Nat.pow_le_pow_right (by norm_num) (one_le_jointMu (by omega))

variable {s : ℕ} {τ gbar ε : ℝ}

/-- `ℓ ≥ 1` on the range of Theorem `odel:thm:combined`. -/
theorem one_le_releaseLog (h : CombinedRange s τ gbar ε) : 1 ≤ releaseLog gbar ε := by
  exact one_le_releaseLog_of (by linarith [h.gbar_ge]) h.eps_pos (by linarith [h.eps_le])

/-- **The release's shape against the lower bound**: `ḡ (√s τ + √(sτℓ) + ℓ) ≤ 3 ℓ S`,
`S = ḡ √s τ + √(sτr) + r` (within one factor `ℓ`, eq. `odel:eq:upper`). -/
theorem release_shape_le (h : CombinedRange s τ gbar ε) :
    gbar * ImprovedODEQueryBudget.queryShape s τ (releaseLog gbar ε) ≤
      3 * releaseLog gbar ε *
        (gbar * Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) := by
  have hτ : (1 : ℝ) ≤ τ := by linarith [h.tau_ge]
  have hs : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by have := h.s_ge; omega)
  have hℓ := one_le_releaseLog h
  have hq := queryShape_le_mul hs hτ hℓ
  have hg : 0 ≤ gbar := by linarith [h.gbar_ge]
  have hr : 0 < hsR τ ε := h.toHSRange.hsR_pos
  have hB : 0 ≤ Real.sqrt (s * τ * hsR τ ε) := Real.sqrt_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hq hg
  have h2 : 0 ≤ 3 * releaseLog gbar ε := by linarith
  have h3 : 0 ≤ 3 * releaseLog gbar ε * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) :=
    mul_nonneg h2 (by linarith)
  calc gbar * ImprovedODEQueryBudget.queryShape s τ (releaseLog gbar ε)
      ≤ gbar * (3 * releaseLog gbar ε * (Real.sqrt s * τ)) := h1
    _ = 3 * releaseLog gbar ε * (gbar * Real.sqrt s * τ) := by ring
    _ ≤ _ := by nlinarith

/-- **`Θ` bracket for the released ODE solver** (Theorem `odel:thm:combined`): for any release runs
on the joint, mixed and precision families, with `S = ḡ √s τ + √(sτr) + r`:
`c S ≤ max(Q_J, Q_M, Q_P)` (`c = log 2/(8192π)`),
`max(Q_J, Q_M, Q_P) ≤ 2548039680 ḡ (√s τ + √(sτℓ) + ℓ)` and the latter is at most `7644119040 ℓ S`
and at most `7644119040 ḡ √s τ ℓ` (eq. `odel:eq:upper`), `ℓ = log(40000 ḡ/ε)`. The value-query
counts `V` also satisfy `c S ≤ max(V_J, V_M, V_P)`, and `V ≤ Q` run by run. The lower half is on the
maximum over the three families (module docstring). -/
theorem release_theta (h : CombinedRange s τ gbar ε)
    (AJ : ReleaseRun (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge) τ gbar ε)
    (AM : ReleaseRun (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) τ gbar ε)
    (AP : ReleaseRun (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) τ gbar ε) :
    combinedBound s τ gbar ε ≤
        max (AJ.matrixQueries : ℝ) (max (AM.matrixQueries : ℝ) AP.matrixQueries) ∧
      max (AJ.matrixQueries : ℝ) (max (AM.matrixQueries : ℝ) AP.matrixQueries) ≤
        2548039680 * gbar * ImprovedODEQueryBudget.queryShape s τ (releaseLog gbar ε) ∧
      2548039680 * gbar * ImprovedODEQueryBudget.queryShape s τ (releaseLog gbar ε) ≤
        7644119040 * releaseLog gbar ε *
          (gbar * Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ∧
      2548039680 * gbar * ImprovedODEQueryBudget.queryShape s τ (releaseLog gbar ε) ≤
        7644119040 * gbar * Real.sqrt s * τ * releaseLog gbar ε ∧
      combinedBound s τ gbar ε ≤
        max (AJ.valueQueries : ℝ) (max (AM.valueQueries : ℝ) AP.valueQueries) ∧
      max (AJ.valueQueries : ℝ) (max (AM.valueQueries : ℝ) AP.valueQueries) ≤
        max (AJ.matrixQueries : ℝ) (max (AM.matrixQueries : ℝ) AP.matrixQueries) := by
  have hshape : 2548039680 * gbar * ImprovedODEQueryBudget.queryShape s τ (releaseLog gbar ε) ≤
      7644119040 * releaseLog gbar ε *
        (gbar * Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) := by
    have := release_shape_le h
    nlinarith
  have hpaper : 2548039680 * gbar * ImprovedODEQueryBudget.queryShape s τ (releaseLog gbar ε) ≤
      7644119040 * gbar * Real.sqrt s * τ * releaseLog gbar ε := by
    have hτ : (1 : ℝ) ≤ τ := by linarith [h.tau_ge]
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by have := h.s_ge; omega)
    have hq := mul_le_mul_of_nonneg_left (queryShape_le_mul hs1 hτ (one_le_releaseLog h))
      (show (0 : ℝ) ≤ 2548039680 * gbar by linarith [h.gbar_ge])
    exact hq.trans (le_of_eq (by ring))
  have hg1 : (1 : ℝ) ≤ gbar := by linarith [h.gbar_ge]
  have hJ := (joint_witness h.toJointRange).inClass
  have hM := mixedFamilyAt_inClass h.toHSRange hg1
  have hP := precisionFamilyAt_inClass h.toHSRange hg1
  have hsolJ : ∀ x, ∃ sol, (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge).Solves x sol :=
    fun x => (hJ.solution x).elim fun sol hs => ⟨sol, hs.1⟩
  have hsolM : ∀ x, ∃ sol, (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])).Solves x sol :=
    fun x => (hM.solution x).elim fun sol hs => ⟨sol, hs.1⟩
  have hsolP : ∀ x, ∃ sol,
      (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])).Solves x sol :=
    fun x => (hP.solution x).elim fun sol hs => ⟨sol, hs.1⟩
  obtain ⟨hval, hlow⟩ := combined_max_release h (stageOf _ AJ.R) (stageOf _ AM.R)
    (stageOf _ AP.R) _ _ _ _ _ _ _ _ _ AJ.sources_public AM.sources_public AP.sources_public
    (AJ.release.toRetrySolver hsolJ AJ.i₀) (AM.release.toRetrySolver hsolM AM.i₀)
    (AP.release.toRetrySolver hsolP AP.i₀)
  obtain ⟨xJ⟩ := joint_nonempty h.toJointRange
  obtain ⟨solJ, hsJ⟩ := hsolJ xJ
  obtain ⟨solM, hsM⟩ := hsolM (fun _ => 0)
  obtain ⟨solP, hsP⟩ := hsolP (fun _ => false)
  have cJ : (AJ.valueQueries : ℝ) ≤ AJ.matrixQueries := by exact_mod_cast AJ.valueQueries_le
  have cM : (AM.valueQueries : ℝ) ≤ AM.matrixQueries := by exact_mod_cast AM.valueQueries_le
  have cP : (AP.valueQueries : ℝ) ≤ AP.matrixQueries := by exact_mod_cast AP.valueQueries_le
  exact ⟨hlow, max_le (AJ.matrixQueries_le xJ solJ hsJ)
    (max_le (AM.matrixQueries_le _ solM hsM) (AP.matrixQueries_le _ solP hsP)),
    hshape, hpaper, hval, max_le_max cJ (max_le_max cM cP)⟩

/-- **Non-vacuity**: release runs of the three hard families exist (the families meet the
hypotheses of `exists_releaseProtocol` with `η = 1`, `D = 0`, `T = τ`, the seed `e_{i₀}` and the
public preparations `releaseJ₀`, `releaseJb`). -/
theorem release_theta_exists (h : CombinedRange s τ gbar ε) :
    Nonempty (ReleaseRun (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge) τ gbar ε) ∧
      Nonempty (ReleaseRun (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) τ gbar ε) ∧
      Nonempty (ReleaseRun (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) τ gbar ε) := by
  have hτ : 0 < τ := by linarith [h.tau_ge]
  have hg1 : (1 : ℝ) ≤ gbar := by linarith [h.gbar_ge]
  have hε1 : ε ≤ 1 := by linarith [h.eps_le]
  have hI := Hamiltonian.hard_instances h.toHSRange
  refine ⟨?_, ?_, ?_⟩
  · have hM1 : 1 ≤ jointM gbar := by have := four_le_jointM h.gbar_ge; omega
    have hs := h.s_ge
    exact releaseRun_nonempty _ (joint_witness h.toJointRange).inClass
      (fun x k => jointFamily_skew x k) jointFamily_T hτ hg1 h.eps_pos hε1
      (by rw [show (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge).mass = 2 from
        jointFamily_mass hM1]; norm_num) (by omega) (Sum.inr ⟨0, by omega⟩)
  · exact releaseRun_nonempty _ (mixedFamilyAt_inClass h.toHSRange hg1)
      (fun x _ => ⟨_, hI.2.1.isHermitian x, rfl⟩) (mixedFamilyAt_T h.toHSRange) hτ hg1
      h.eps_pos hε1
      (by rw [show (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])).mass = _ from
        hamFamily_mass _ _ _ _, Hamiltonian.norm_searchInput]; norm_num) one_pos
      Hamiltonian.refZero
  · exact releaseRun_nonempty _ (precisionFamilyAt_inClass h.toHSRange hg1)
      (fun x _ => ⟨_, hI.2.2.1.isHermitian x, rfl⟩) (precisionFamilyAt_T h.toHSRange) hτ hg1
      h.eps_pos hε1
      (by rw [show (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])).mass = _ from
        hamFamily_mass _ _ _ _, Hamiltonian.norm_scalarInput]; norm_num) one_pos
      Hamiltonian.refZero

/-- **The released ODE solver on the hard families is `Θ(S)` up to the factor `3ℓ`**: there are
release runs on the joint, mixed and precision families with
`c S ≤ max(Q_J, Q_M, Q_P) ≤ 2548039680 ḡ (√s τ + √(sτℓ) + ℓ) ≤ 7644119040 ℓ S` (and
`≤ 7644119040 ḡ √s τ ℓ`; value counts `c S ≤ max V ≤ max Q`); by
`release_theta` every release run (any public source interfaces) satisfies the same bracket. -/
theorem release_theta_bracket (h : CombinedRange s τ gbar ε) :
    ∃ (AJ : ReleaseRun (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge) τ gbar ε)
      (AM : ReleaseRun (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) τ gbar ε)
      (AP : ReleaseRun (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) τ gbar ε),
      combinedBound s τ gbar ε ≤
          max (AJ.matrixQueries : ℝ) (max (AM.matrixQueries : ℝ) AP.matrixQueries) ∧
        max (AJ.matrixQueries : ℝ) (max (AM.matrixQueries : ℝ) AP.matrixQueries) ≤
          2548039680 * gbar * ImprovedODEQueryBudget.queryShape s τ (releaseLog gbar ε) ∧
        2548039680 * gbar * ImprovedODEQueryBudget.queryShape s τ (releaseLog gbar ε) ≤
          7644119040 * releaseLog gbar ε *
            (gbar * Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ∧
        2548039680 * gbar * ImprovedODEQueryBudget.queryShape s τ (releaseLog gbar ε) ≤
          7644119040 * gbar * Real.sqrt s * τ * releaseLog gbar ε ∧
        combinedBound s τ gbar ε ≤
          max (AJ.valueQueries : ℝ) (max (AM.valueQueries : ℝ) AP.valueQueries) ∧
        max (AJ.valueQueries : ℝ) (max (AM.valueQueries : ℝ) AP.valueQueries) ≤
          max (AJ.matrixQueries : ℝ) (max (AM.matrixQueries : ℝ) AP.matrixQueries) := by
  obtain ⟨⟨AJ⟩, ⟨AM⟩, ⟨AP⟩⟩ := release_theta_exists h
  exact ⟨AJ, AM, AP, release_theta h AJ AM AP⟩

/-- **Upper and lower bounds match on the joint family when `τ ≥ ℓ`** (Section `odel:sec:main`):
every release run on the joint family (`D = 0`, `g = Θ(ḡ)`) has
`ḡ √s τ / 400 ≤ Q_J ≤ 7644119040 ḡ √s τ`. -/
theorem joint_release_theta (h : JointRange s τ gbar ε)
    (AJ : ReleaseRun (jointFamilyAt s τ gbar h.s_ge h.tau_ge) τ gbar ε)
    (hτℓ : releaseLog gbar ε ≤ τ) :
    jointConst * gbar * Real.sqrt s * τ ≤ AJ.matrixQueries ∧
      (AJ.matrixQueries : ℝ) ≤ 7644119040 * (gbar * Real.sqrt s * τ) := by
  have hJ := (joint_witness h).inClass
  have hsol : ∀ x, ∃ sol, (jointFamilyAt s τ gbar h.s_ge h.tau_ge).Solves x sol :=
    fun x => (hJ.solution x).elim fun sol hs => ⟨sol, hs.1⟩
  have hlow := (joint_release h (stageOf _ AJ.R) _ _ _ AJ.sources_public
    (AJ.release.toRetrySolver hsol AJ.i₀)).2
  obtain ⟨x⟩ := joint_nonempty h
  obtain ⟨sol, hs⟩ := hsol x
  refine ⟨hlow, ?_⟩
  have hup := AJ.matrixQueries_le x sol hs
  have hℓ := one_le_releaseLog_of (gbar := gbar) (ε := ε) (by linarith [h.gbar_ge]) h.eps_pos (by linarith [h.eps_le])
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by have := h.s_ge; omega)
  have hq := queryShape_le_of_le hs1 (by linarith) hτℓ
  have hg : 0 ≤ gbar := by linarith [h.gbar_ge]
  have := mul_le_mul_of_nonneg_left hq hg
  nlinarith

end

end ODELowerBoundExtensions.Release
