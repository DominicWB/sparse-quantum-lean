import ODELowerBoundExtensions.Release.Access
import ODELowerBoundExtensions.Release.Theorem

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Theorem `odel:thm:combined` for retry protocols over the released solver's oracle

Manuscript: Section `odel:sec:main` ("the lower bounds apply to the upper bounds of the preceding
section") and Theorem `odel:thm:combined`. The analogue of
`SparseLowerBounds.Hamiltonian.main_max_release` for the ODE lower bound: the bounds hold for
**every** retry protocol (`RetrySolver`) over the physical oracle family of the released
general-mesh solver `TimeDependentExtensions.ODE.solver` run on the hard family's data along any
public placement `σ : Fin M → Fin K` of `M` mesh pieces into the `K` stages
(`meshOracle F σ ι N d J₀ J_b`, any spectator index `ι`, slot count `N`, degree `d`; the released
runs use the uniform refinement `σ = stageOf K R`, `releaseOracle`), with public source interfaces
(`PublicSources`: unitary and input-independent, Section `odel:sec:main`), success mass at least
`2/3` and conditional accuracy `ε` for the family's normalised solution. As in `main_max_release`,
two counts are bounded: the worst-case number of value queries
`Protocol.worstCost (ODESourceQueryBudget.matrixWeight valueWeight)` (forward and inverse value
calls; location and source calls not counted), and the release's own matrix count
`Protocol.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))` (row, column and value calls,
inverses included, source calls not counted), the quantity bounded by
`ODECompleteTrial.Certificate.matrix_queries`. Every attempt and failure branch is counted.

* `joint_release`: `c_J ḡ √s τ ≤ Q` on the joint family (`JointRange`), from
  `joint_general_retry` with the membership certificate `implementsOn_release_joint` (Boolean cost
  `matrixWeight hardCost = 2 · matrixWeight valueWeight`, `worstCost_mul`).
* `mixed_release`, `precision_release`: the `g = 1` bounds, from
  `AdaptiveHamiltonianLowerBound.mixed_tree_general` / `precision_tree_general` applied to
  `Tree.final` of the protocol, with `searchGrowth_release_ham` (weight `matrixWeight valueWeight`)
  and the numerics `mixrbound`, `rbound`, `failedmix` of `Hamiltonian/Theorem`.
* `combined_max_release`: max form, `c (ḡ √s τ + √(sτr) + r) ≤ max(Q_J, Q_M, Q_P)` for both counts,
  `c = log 2/(8192π)`, as `combined_max` (`Hamiltonian.assembly`).

In every case the matrix count follows from the value count (`worstCost_mono`). The names
`mixed_release` and `precision_release` repeat those of `SparseLowerBounds.Hamiltonian`; this module
opens that namespace selectively, and other modules cite these with the `Release.` prefix.
-/

namespace ODELowerBoundExtensions.Release

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE
open SparseLowerBounds.Hamiltonian (HSRange hsL hsR precN)
open NativeSparseBlockEncoding OracleCircuit TimeDependentExtensions
open AdaptiveHamiltonianLowerBound.Access (valueWeight)

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

/-- Value calls are matrix calls: `matrixWeight valueWeight ≤ matrixWeight 1` labelwise. -/
theorem matrixWeight_value_le (l : Query ⊕ Bool) :
    ODESourceQueryBudget.matrixWeight valueWeight l ≤
      ODESourceQueryBudget.matrixWeight (fun _ : Query => 1) l := by
  rcases l with q | b
  · cases q <;> decide
  · exact le_rfl

/-- The Boolean cost of a release label is twice its value weight:
`matrixWeight hardCost = 2 · matrixWeight valueWeight`. -/
theorem matrixWeight_hardCost :
    ODESourceQueryBudget.matrixWeight hardCost =
      fun l => 2 * ODESourceQueryBudget.matrixWeight valueWeight l := by
  funext l
  rcases l with q | b
  · cases q <;> rfl
  · rfl

/-- The value-query count of a retry protocol bounds its matrix-query count from below. -/
theorem worstCost_value_le_matrix {X W E : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {O : Query ⊕ Bool → X → W →L[ℂ] W}
    (p : ODERepeatProtocol.Protocol O E) :
    (p.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ) ≤
      p.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) := by
  exact_mod_cast worstCost_mono p matrixWeight_value_le

/-- **Accuracy of a retry solver on a `g = 1` family**: for Hermitian data and a unit initial
state the normalised solution is `exp(-iTH_x) x₀`, so the conditional output of every retry
solver of `hamFamily D T hT x₀` is `ε`-accurate for it. -/
theorem RetrySolver.accurate_ham {X N Z : Type*} [Fintype N] [DecidableEq N] {s : ℕ}
    (D : Data X N Z s) (T : ℝ) (hT : 0 ≤ T) (x₀ : EuclideanSpace ℂ N)
    (hH : ∀ x, (D.matrix x).IsHermitian) (hx₀ : ‖x₀‖ = 1) {L W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    {O : L → X → W →L[ℂ] W} {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] {ε : ℝ} (A : RetrySolver (hamFamily D T hT x₀) O E G ε) (x : X) :
    AdaptiveHamiltonianLowerBound.DensityAccurate A.readout (A.prot.conditionalDensity x)
      (Hamiltonian.evolve (D.matrix x) T x₀) ε := by
  have h := A.accurate x _ (hamFamily_solves D T hT x₀ x)
  have hu : ODEStateNormalization.unitDirection (Hamiltonian.evolve (D.matrix x) T x₀) =
      Hamiltonian.evolve (D.matrix x) T x₀ := by
    rw [ODEStateNormalization.unitDirection, Hamiltonian.norm_evolve_apply (hH x), hx₀,
      inv_one, one_smul]
  rw [hamFamily_T, hu] at h
  exact h

/-- **Theorem `odel:thm:joint` for the released solver's oracle**: on `JointRange`, every retry
solver over the release's physical oracle on the joint family along any placement `σ`, with public
source interfaces, makes at least `ḡ √s τ / 400` value queries, hence as many matrix queries, in
the worst case. -/
theorem joint_release {s : ℕ} {τ gbar ε : ℝ} (h : JointRange s τ gbar ε) {M : ℕ}
    (σ : Fin M → Fin (jointN τ + 2)) (ι : Type) [Fintype ι] [DecidableEq ι] (Nsl d : ℕ)
    {J₀ : _ → SysOp _} {Jb : _ → Fin M → SysOp _} (hJ : PublicSources J₀ Jb) {E G : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : RetrySolver (jointFamilyAt s τ gbar h.s_ge h.tau_ge)
      (meshOracle (jointFamilyAt s τ gbar h.s_ge h.tau_ge) σ ι Nsl d J₀ Jb) E G ε) :
    jointConst * gbar * Real.sqrt s * τ ≤
        A.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
      jointConst * gbar * Real.sqrt s * τ ≤
        A.prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) := by
  have hs := h.s_ge
  have hM := four_le_jointM h.gbar_ge
  have hT := jointN_time (by linarith [h.tau_ge] : (1 : ℝ) ≤ τ)
  obtain ⟨B, _, _, _, P, Enc, hEnc, hw⟩ := implementsOn_release_joint
    (one_le_jointMu (by omega : 2 ≤ s)) (two_pow_jointMu_le (by omega : 1 ≤ s)) hT σ ι Nsl d hJ
  have hU := MeshSource.physicalOracle_unitary (ι := ι)
    (stageData (jointFamilyAt s τ gbar h.s_ge h.tau_ge).data σ) Nsl d J₀ Jb hJ.initial_unitary
    hJ.forcing_unitary
  have hb := joint_general_retry (s := s) (ε := ε) (by omega) (even_jointM gbar) (one_le_jointN h.tau_ge)
    (one_le_jointMu (by omega)) (by linarith [h.eps_le]) P Enc hEnc _ hU _ hw A.prot A.readout
    A.readout_isometry A.success (fun x => by
      have hx := A.accurate x _ (jointSol_solves x)
      rwa [show (jointFamilyAt s τ gbar h.s_ge h.tau_ge).T = τ from jointFamily_T,
        unitDirection_jointSol_T hT] at hx)
  rw [matrixWeight_hardCost, worstCost_mul] at hb
  push_cast at hb
  have hv : jointConst * gbar * Real.sqrt s * τ ≤
      A.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) := by
    linarith [joint_bound_le h]
  exact ⟨hv, hv.trans (worstCost_value_le_matrix A.prot)⟩

/-- **Mixed family, released solver's oracle** (eq. `hsl:eq:mixrbound`): for `L ≥ 64τ` and
`s ≥ 64n/τ`, every retry solver over the release's physical oracle on the mixed family along any
placement, with public source interfaces, makes at least `(log 2/(384√2)) √(sτr)` value queries,
hence as many matrix queries, in the worst case. -/
theorem mixed_release {τ ε : ℝ} {s : ℕ} (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) {M : ℕ} (σ : Fin M → Fin 1) (ι : Type) [Fintype ι]
    [DecidableEq ι] (Nsl d : ℕ) {J₀ : _ → SysOp _} {Jb : _ → Fin M → SysOp _}
    (hJ : PublicSources J₀ Jb) {E G : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    (A : RetrySolver (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
      (meshOracle (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) σ ι Nsl d J₀ Jb)
      E G ε) :
    Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤
        A.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤
        A.prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) := by
  have hτ0 : (0 : ℝ) ≤ τ := by linarith [h.one_le_tau]
  have hI := (Hamiltonian.hard_instances h).2.1
  have hO := searchGrowth_release_ham (AdaptiveHamiltonianLowerBound.even_two_pow_hsMu h.s_ge)
    (Hamiltonian.mixedMainData τ ε s h.s_ge) id
    (AdaptiveHamiltonianLowerBound.Access.hardAccess_mixedMainData τ ε s h.s_ge) τ hτ0
    (Hamiltonian.searchInput (precN τ ε) (Hamiltonian.hsMu s) s) σ ι Nsl d hJ
  have hU := MeshSource.physicalOracle_unitary (ι := ι)
    (stageData (mixedFamilyAt τ ε s h.s_ge hτ0).data σ) Nsl d J₀ Jb hJ.initial_unitary
    hJ.forcing_unitary
  have hb := AdaptiveHamiltonianLowerBound.mixed_tree_general (F := ℂ) h hL hs
    (O := meshOracle (mixedFamilyAt τ ε s h.s_ge hτ0) σ ι Nsl d J₀ Jb) hU _ hO
    (SparseLinearSystems.Protocol.Tree.final A.prot) A.readout A.readout_isometry A.success
    (fun j => RetrySolver.accurate_ham _ _ _ _ hI.isHermitian
      (Hamiltonian.norm_searchInput _ _ _) A j)
  have hb' : Real.log 2 / 48 * Real.sqrt ((2 : ℝ) ^ Hamiltonian.hsMu s * precN τ ε * τ) ≤
      A.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) := hb
  have hX : 0 ≤ Real.log 2 / 96 * Real.sqrt ((2 : ℝ) ^ Hamiltonian.hsMu s * precN τ ε * τ) :=
    mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le (by norm_num)) (Real.sqrt_nonneg _)
  have hv : Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤
      A.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) := by
    linarith [Hamiltonian.mixrbound h hL]
  exact ⟨hv, hv.trans (worstCost_value_le_matrix A.prot)⟩

/-- **Precision family, released solver's oracle** (eqs. `hsl:eq:rbound`, `hsl:eq:failedmix`): for
`L ≥ 64τ`, every retry solver over the release's physical oracle on the precision family along any
placement, with public source interfaces, makes at least `r/32` value queries in the worst case,
and at least `√(sτr)/(64√2)` when `s < 64n/τ`; hence as many matrix queries. -/
theorem precision_release {τ ε : ℝ} {s : ℕ} (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    {M : ℕ} (σ : Fin M → Fin 1) (ι : Type) [Fintype ι] [DecidableEq ι] (Nsl d : ℕ)
    {J₀ : _ → SysOp _} {Jb : _ → Fin M → SysOp _} (hJ : PublicSources J₀ Jb) {E G : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : RetrySolver (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
      (meshOracle (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) σ ι Nsl d J₀ Jb)
      E G ε) :
    (hsR τ ε / 32 ≤ A.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
      hsR τ ε / 32 ≤ A.prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))) ∧
      ((s : ℝ) < 64 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤
            A.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
          Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤
            A.prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))) := by
  have hτ0 : (0 : ℝ) ≤ τ := by linarith [h.one_le_tau]
  have hI := (Hamiltonian.hard_instances h).2.2.1
  have hO := searchGrowth_release_ham even_two (Hamiltonian.precisionMainData τ ε s h.s_ge)
    AdaptiveHamiltonianLowerBound.Access.toBits
    (AdaptiveHamiltonianLowerBound.Access.hardAccess_precisionMainData τ ε s h.s_ge) τ hτ0
    (Hamiltonian.scalarInput (precN τ ε) s) σ ι Nsl d hJ
  have hU := MeshSource.physicalOracle_unitary (ι := ι)
    (stageData (precisionFamilyAt τ ε s h.s_ge hτ0).data σ) Nsl d J₀ Jb hJ.initial_unitary
    hJ.forcing_unitary
  have hb := AdaptiveHamiltonianLowerBound.precision_tree_general (F := ℂ) h hL
    (O := meshOracle (precisionFamilyAt τ ε s h.s_ge hτ0) σ ι Nsl d J₀ Jb) hU _ hO
    (SparseLinearSystems.Protocol.Tree.final A.prot) A.readout A.readout_isometry A.success
    (fun x => RetrySolver.accurate_ham _ _ _ _ hI.isHermitian
      (Hamiltonian.norm_scalarInput _ _) A x)
  have hb' : (precN τ ε : ℝ) / 2 ≤
      A.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) := hb
  have hn0 : (0 : ℝ) ≤ precN τ ε := Nat.cast_nonneg _
  have hm := worstCost_value_le_matrix A.prot
  refine ⟨⟨by linarith [Hamiltonian.rbound h hL], by linarith [Hamiltonian.rbound h hL]⟩,
    fun hs' => ⟨by linarith [Hamiltonian.failedmix h hL hs'],
      by linarith [Hamiltonian.failedmix h hL hs']⟩⟩

/-- **Theorem `odel:thm:combined` for the released solver's oracle, max form** (the analogue of
`main_max_release`): for any three retry solvers over the release's physical oracle on the joint,
mixed and precision families (any placements of mesh pieces, spectator indices, slot counts,
degrees, public source interfaces, output and garbage spaces), each accurate on its own family,
the largest worst-case value-query count, and hence the largest worst-case matrix-query count, is
at least `c (ḡ √s τ + √(sτr) + r)`, `c = log 2/(8192π)`. -/
theorem combined_max_release {s : ℕ} {τ gbar ε : ℝ} (h : CombinedRange s τ gbar ε)
    {MJ MM MP : ℕ} (σJ : Fin MJ → Fin (jointN τ + 2)) (σM : Fin MM → Fin 1)
    (σP : Fin MP → Fin 1) (ιJ ιM ιP : Type) [Fintype ιJ] [DecidableEq ιJ] [Fintype ιM]
    [DecidableEq ιM] [Fintype ιP] [DecidableEq ιP] (NJ dJ NM dM NP dP : ℕ)
    {J₀J : _ → SysOp _} {JbJ : _ → Fin MJ → SysOp _} (hJJ : PublicSources J₀J JbJ)
    {J₀M : _ → SysOp _} {JbM : _ → Fin MM → SysOp _} (hJM : PublicSources J₀M JbM)
    {J₀P : _ → SysOp _} {JbP : _ → Fin MP → SysOp _} (hJP : PublicSources J₀P JbP)
    {EJ EM EP GJ GM GP : Type}
    [NormedAddCommGroup EJ] [InnerProductSpace ℂ EJ] [CompleteSpace EJ] [FiniteDimensional ℂ EJ]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GJ] [InnerProductSpace ℂ GJ] [CompleteSpace GJ]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AJ : RetrySolver (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge)
      (meshOracle (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge) σJ ιJ NJ dJ J₀J JbJ)
      EJ GJ ε)
    (AM : RetrySolver (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]))
      (meshOracle (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) σM ιM NM dM J₀M JbM)
      EM GM ε)
    (AP : RetrySolver (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]))
      (meshOracle (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) σP ιP NP dP J₀P
        JbP) EP GP ε) :
    combinedBound s τ gbar ε ≤
        max (AJ.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
          (max (AM.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
            (AP.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight))) ∧
      combinedBound s τ gbar ε ≤
        max (AJ.prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ)
          (max (AM.prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ)
            (AP.prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)))) := by
  have hH := h.toHSRange
  have hJ := (joint_release h.toJointRange σJ ιJ NJ dJ hJJ AJ).1
  have hS : 0 ≤ Real.sqrt s * τ := mul_nonneg (Real.sqrt_nonneg _) (by linarith [h.tau_ge])
  have hcJ : Hamiltonian.cT ≤ jointConst * gbar := by
    have := cT_le_inv_200
    unfold jointConst
    linarith [h.gbar_ge]
  have hT : Hamiltonian.cT * Real.sqrt s * τ ≤
      (AJ.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ) := by
    calc Hamiltonian.cT * Real.sqrt s * τ = Hamiltonian.cT * (Real.sqrt s * τ) := by ring
      _ ≤ jointConst * gbar * (Real.sqrt s * τ) := mul_le_mul_of_nonneg_right hcJ hS
      _ = jointConst * gbar * Real.sqrt s * τ := by ring
      _ ≤ _ := hJ
  have hmax := Hamiltonian.assembly hH hT
    (fun hL => ⟨(precision_release hH hL σP ιP NP dP hJP AP).1.1,
      fun hs' => ((precision_release hH hL σP ιP NP dP hJP AP).2 hs').1⟩)
    (fun hL hs => (mixed_release hH hL hs σM ιM NM dM hJM AM).1)
  have hg : Hamiltonian.c0 * gbar * (Real.sqrt s * τ) ≤ jointConst * gbar * (Real.sqrt s * τ) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right c0_le_jointConst (by linarith [h.gbar_ge])) hS
  have hle := le_max_left (AJ.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
    (max (AM.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
      (AP.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight)))
  have hJ' : jointConst * gbar * (Real.sqrt s * τ) ≤
      (AJ.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ) := by
    calc jointConst * gbar * (Real.sqrt s * τ) = jointConst * gbar * Real.sqrt s * τ := by ring
      _ ≤ _ := hJ
  have hv : combinedBound s τ gbar ε ≤
      max (AJ.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
        (max (AM.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
          (AP.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight))) := by
    have hsτ : gbar * Real.sqrt s * τ = gbar * (Real.sqrt s * τ) := by ring
    unfold combinedBound
    rw [combinedConst_eq, hsτ]
    linarith [mul_nonneg Hamiltonian.c0_pos.le hS]
  exact ⟨hv, hv.trans (max_le_max (worstCost_value_le_matrix AJ.prot)
    (max_le_max (worstCost_value_le_matrix AM.prot) (worstCost_value_le_matrix AP.prot)))⟩

end

end ODELowerBoundExtensions.Release
