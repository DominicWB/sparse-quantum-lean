import ConstantODELowerBound.Runs
import ODELowerBoundExtensions.Release.Instances
import SparseODE.ODEGaussianParametersContinuation2

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Runs of the released constant-coefficient solver on the hard families exist

Theorem `ode:thm:main` (manuscript lines 3013-3033) and lines 4114-4115: the released
constant-coefficient solver `SparseHamiltonian.ODECompleteEndpoint.solver` runs on each hard
constant-coefficient family, so the bounds of `Runs` are not vacuous.

* `herald_const_runs_exist`: for every `ḡ ≥ 1`, runs on the time, mixed and precision families
  (`η_H = 1`, `η_D = 0`, `T = τ`; the Hermitian part of `iH` is `H` and the dissipative part `0`,
  `Release.hamiltonianPart_I_smul`, `Release.dissipativePart_I_smul`), with the seed `e_{i₀}`
  (`Release.seedVec`) and the public preparation `Release.prepUnitary i₀ x₀` (no forcing).
* `herald_const_bracket`: hence runs with
  `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P) ≤ 1274019840 ḡ (√s τ + √(sτℓ) + ℓ)` exist.
* `psd_const_runs_exist`: for every `ḡ ≥ √2`, runs on the two PSD families (`η_H = 0`,
  `η_D = 1`; the generators are real symmetric, `Solution.hamiltonianPart_of_isHermitian`,
  `Solution.dissipativePart_of_isHermitian`).
-/

namespace ConstantODELowerBound.Instances

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open SparseLowerBounds.Hamiltonian (HSRange hsR c0)
open ODELowerBoundExtensions.Release (SysOp)
open ODELowerBoundExtensions.Psd (PsdRange psdSearchFamilyAt psdScalarFamilyAt psdBound heatFamily)
open ConstantODELowerBound.Oracle ConstantODELowerBound.Protocol ConstantODELowerBound.Solver
open ConstantODELowerBound.Runs

-- The released solver's physical workspace is a nested register product; instance search and
-- elaboration over its types need the raised `synthInstance.maxSize` and `maxRecDepth`.
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

/-- **Runs exist on a one-stage family of the class**: under the hypotheses of
`Solver.exists_constProtocol`, with the seed `e_{i₀}` and the public preparations
`Release.prepUnitary i₀ x₀`, `Release.prepUnitary i₀ b`. -/
theorem constRun_nonempty {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
    [DecidableEq Z] {s : ℕ} (F : Family X N Z 1 s) {η τ gbar ε etaH etaD : ℝ}
    (hF : F.InClass η gbar) (hT : F.T = τ) (hτ : 0 < τ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD)
    (hpos : 0 < etaH + ImprovedODEQueryBudget.radius gbar ε * etaD)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (F.data.matrix (x, 0)) i j‖ ^ 2 ≤
      etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (F.data.matrix (x, 0)) i j‖ ^ 2 ≤
      etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (F.data.matrix (x, 0)) i j‖ ^ 2 ≤
      etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (F.data.matrix (x, 0)) i j‖ ^ 2 ≤
      etaD ^ 2)
    (i₀ : N) : Nonempty (ConstRun F τ gbar ε etaH etaD) := by
  have hP : PublicConstSources (fun _ : X => ODELowerBoundExtensions.Release.prepUnitary i₀ F.init)
      (fun _ : X => ODELowerBoundExtensions.Release.prepUnitary i₀ (F.src 0)) :=
    ⟨fun _ => ODELowerBoundExtensions.Release.prepUnitary_unitary _ _,
      fun _ _ => ODELowerBoundExtensions.Release.prepUnitary_unitary _ _,
      fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨Tsl, d, p, hp⟩ := exists_constProtocol F hF hT hτ hε hε2 hH hDiss hpos hrH hcH hrD hcD
    _ _ hP.initial_unitary (fun x => hP.forcing_unitary x 0)
    (ODELowerBoundExtensions.Release.seedVec i₀)
    (ODELowerBoundExtensions.Release.norm_seedVec i₀)
    (fun h0 _ => ODELowerBoundExtensions.Release.prepUnitary_seed i₀ h0)
    (fun h0 _ => ODELowerBoundExtensions.Release.prepUnitary_seed i₀ h0)
  exact ⟨⟨i₀, Tsl, d, _, _, hP, p, hp⟩⟩

/-- **Runs exist on a `g = 1` family** `ẋ = -iH_x x` (Hermitian data with row and column norms
at most one, unit start, `ḡ ≥ 1`): `η_H = 1`, `η_D = 0` (the Hermitian part of `iH` is `H`, the
dissipative part `0`). -/
theorem hamRun_nonempty {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
    [DecidableEq Z] {s : ℕ} (D : Data X N Z s) {τ gbar ε : ℝ} (hτ : 0 < τ)
    (x₀ : EuclideanSpace ℂ N) (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1) (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hx₀ : ‖x₀‖ = 1) (hg : 1 ≤ gbar) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (i₀ : N) :
    Nonempty (ConstRun (hamFamily D τ hτ.le x₀) τ gbar ε 1 0) := by
  have hF := hamFamily_inClass D τ hτ.le x₀ hH hrow hcol hx₀ hg
  have hnorm : ∀ x i j, ‖ODEMatrixEnergy.hamiltonianPart
      ((hamFamily D τ hτ.le x₀).data.matrix (x, 0)) i j‖ = ‖D.matrix x i j‖ := by
    intro x i j
    show ‖ODEMatrixEnergy.hamiltonianPart (Complex.I • D.matrix x) i j‖ = _
    rw [ODELowerBoundExtensions.Release.hamiltonianPart_I_smul (hH x)]
  have hdz : ∀ x, ODEMatrixEnergy.dissipativePart
      ((hamFamily D τ hτ.le x₀).data.matrix (x, 0)) = 0 :=
    fun x => ODELowerBoundExtensions.Release.dissipativePart_I_smul (hH x)
  exact constRun_nonempty _ hF (hamFamily_T D τ hτ.le x₀) hτ hε hε2 zero_le_one le_rfl
    (by rw [mul_zero, add_zero]; exact one_pos)
    (fun x i => by simp only [hnorm, one_pow]; exact hrow x i)
    (fun x j => by simp only [hnorm, one_pow]; exact hcol x j)
    (fun x i => by rw [hdz]; simp) (fun x j => by rw [hdz]; simp) i₀

/-- **Runs exist on a heat family** `ẋ = -D_x x` (Hermitian data, the family in the class with
row and column norms at most one, `ḡ ≥ 1`): `η_H = 0`, `η_D = 1`. The LCHS cutoff is positive
(`ODEGaussianParameters.width_ge_two`, `ODEGaussianParameters.cutoff_le_radius`). -/
theorem heatRun_nonempty {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
    [DecidableEq Z] {s : ℕ} (D : Data X N Z s) {τ gbar ε : ℝ} (hτ : 0 < τ)
    (x₀ : EuclideanSpace ℂ N) (hH : ∀ x, (D.matrix x).IsHermitian)
    (hF : (heatFamily D τ hτ.le x₀).InClass 1 gbar) (hg : 1 ≤ gbar) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (i₀ : N) :
    Nonempty (ConstRun (heatFamily D τ hτ.le x₀) τ gbar ε 0 1) := by
  have hz : ∀ x, ODEMatrixEnergy.hamiltonianPart
      ((heatFamily D τ hτ.le x₀).data.matrix (x, 0)) = 0 :=
    fun x => Solution.hamiltonianPart_of_isHermitian (hH x)
  have hd : ∀ x, ODEMatrixEnergy.dissipativePart
      ((heatFamily D τ hτ.le x₀).data.matrix (x, 0)) = D.matrix x :=
    fun x => Solution.dissipativePart_of_isHermitian (hH x)
  exact constRun_nonempty _ hF (ODELowerBoundExtensions.Psd.heatFamily_T D τ hτ.le x₀) hτ hε hε2
    le_rfl zero_le_one
    (by
      rw [zero_add, mul_one]
      have h1 := ODEGaussianParameters.width_ge_two gbar ε hg hε (by linarith)
      have h2 := ODEGaussianParameters.cutoff_le_radius gbar ε hg hε (by linarith)
      linarith)
    (fun x i => by rw [hz]; simp) (fun x j => by rw [hz]; simp)
    (fun x i => by rw [hd]; exact hF.row_norm x 0 i)
    (fun x j => by rw [hd]; exact hF.col_norm x 0 j)
    i₀

variable {s : ℕ} {τ gbar ε : ℝ}

/-- **Non-vacuity on the `g = 1` families**: for every `ḡ ≥ 1`, runs of the released
constant-coefficient solver on the time, mixed and precision families exist (the families meet
the hypotheses of `Solver.exists_constProtocol` with `η_H = 1`, `η_D = 0`, `T = τ`, the seed
`e_{i₀}` and the public preparations `Release.prepUnitary`). -/
theorem herald_const_runs_exist (h : HSRange τ s ε) (hg : 1 ≤ gbar) :
    Nonempty (ConstRun (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε 1 0) ∧
      Nonempty (ConstRun (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε 1 0) ∧
      Nonempty
        (ConstRun (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε 1 0) := by
  have hτ : 0 < τ := by linarith [h.one_le_tau]
  have hε2 : ε ≤ 1 / 2 := by linarith [h.eps_le]
  have hI := Hamiltonian.hard_instances h
  exact ⟨hamRun_nonempty _ hτ _ hI.1.isHermitian hI.1.row_norm_le hI.1.col_norm_le
      (Hamiltonian.norm_searchInput _ _ _) hg h.eps_pos hε2 Hamiltonian.refZero,
    hamRun_nonempty _ hτ _ hI.2.1.isHermitian hI.2.1.row_norm_le hI.2.1.col_norm_le
      (Hamiltonian.norm_searchInput _ _ _) hg h.eps_pos hε2 Hamiltonian.refZero,
    hamRun_nonempty _ hτ _ hI.2.2.1.isHermitian hI.2.2.1.row_norm_le hI.2.2.1.col_norm_le
      (Hamiltonian.norm_scalarInput _ _) hg h.eps_pos hε2 Hamiltonian.refZero⟩

/-- **The bracket at the released runs on the `g = 1` families**: for every `ḡ ≥ 1` there are
runs of the released constant-coefficient solver on the three families with
`c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P) ≤ 1274019840 ḡ (√s τ + √(sτℓ) + ℓ)`, and by
`herald_const_bounds` every run satisfies it. -/
theorem herald_const_bracket (h : HSRange τ s ε) (hg : 1 ≤ gbar) :
    ∃ (AT : ConstRun (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε 1 0)
      (AM : ConstRun (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε 1 0)
      (AP : ConstRun (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε 1 0),
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
          max (AT.matrixQueries : ℝ) (max (AM.matrixQueries : ℝ) AP.matrixQueries) ∧
        max (AT.matrixQueries : ℝ) (max (AM.matrixQueries : ℝ) AP.matrixQueries) ≤
          1274019840 * gbar *
            ImprovedODEQueryBudget.queryShape s τ (ImprovedODEQueryBudget.logBudget gbar ε) := by
  obtain ⟨⟨AT⟩, ⟨AM⟩, ⟨AP⟩⟩ := herald_const_runs_exist h hg
  obtain ⟨h1, h2, -⟩ := herald_const_bounds h AT AM AP
  exact ⟨AT, AM, AP, h1, h2⟩

/-- **Non-vacuity on the PSD families**: for every `ḡ ≥ √2`, runs of the released
constant-coefficient solver on the gadget and scalar families exist (`η_H = 0`, `η_D = 1`,
`T = τ`, the seed `e_{i₀}` and the public preparations `Release.prepUnitary`). -/
theorem psd_const_runs_exist (h : PsdRange τ s ε) (hg : Real.sqrt 2 ≤ gbar) :
    Nonempty (ConstRun (psdSearchFamilyAt h) τ gbar ε 0 1) ∧
      Nonempty (ConstRun (psdScalarFamilyAt h) τ gbar ε 0 1) := by
  have hτ : 0 < τ := by linarith [h.one_le_tau]
  have hε2 : ε ≤ 1 / 2 := by linarith [h.toHSRange.eps_le]
  have h12 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hg1 : 1 ≤ gbar := h12.trans hg
  have hI := ODELowerBoundExtensions.Psd.psd_hardInstance h
  exact ⟨heatRun_nonempty _ hτ _ hI.1.isHermitian
      (ODELowerBoundExtensions.Psd.psdSearchFamilyAt_inClass h hg) hg1 h.eps_pos hε2
      Hamiltonian.refZero,
    heatRun_nonempty _ hτ _ hI.2.1.isHermitian
      (ODELowerBoundExtensions.Psd.psdScalarFamilyAt_inClass h hg) hg1 h.eps_pos hε2
      Hamiltonian.refZero⟩

end

end ConstantODELowerBound.Instances
