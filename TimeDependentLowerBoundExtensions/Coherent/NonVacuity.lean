import TimeDependentLowerBoundExtensions.Coherent.Bound

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The coherent-selection lower bounds are not vacuous

The released selection simulators (`TimeDependentExtensions.Coherent.coherent_select` and
`coherent_windows`, the manuscript, lines 1505-1510) apply to constant data
(`TimeDependentHamiltonianLowerBound.constData`) of any Hermitian sparse instance with entry
bound `η`. For every public duration table (respectively every public table of windows) they
supply a program over the selection family of `main_max_select` (respectively
`main_max_windows`) whose clean isometric input encoding meets `SelectCriterion`
(respectively `WindowsCriterion`): `exists_selectProgram`, `exists_windowsProgram`. With a
branch of total duration (window length) `τ`, these are the hypotheses of the two bounds.
-/

namespace TimeDependentLowerBoundExtensions.Coherent

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit ContinuousLinearMap
open TimeDependentHamiltonianLowerBound (constData)
open scoped InnerProduct InnerProductSpace

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

/-- **The released selection simulator meets `SelectCriterion`** on constant data: under the
hypotheses of `TimeDependentExtensions.Coherent.coherent_select` (Hermitian instances, entry
bound `η`, clock and Cayley conditions on `Nsl` slots), there is one rescaling
`γ ∈ (0, 1]` with `γ √(2s) ≥ 1` such that for every public duration table `0 ≤ u_i(r) ≤ T`
some program over the selection family of `constData D M` with at most
`663552 · shape(2s, ηT, log(1/ε))` calls (the released count) meets `SelectCriterion` with the
clean isometric input encoding. -/
theorem exists_selectProgram (D : Data X N Z s) (hH : ∀ x, (D.matrix x).IsHermitian) {η : ℝ}
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) {M : ℕ} (hM : 0 < M) (σ : ℕ → Fin M)
    {Nsl : ℕ} (hN : 0 < Nsl) (b0 : ι × Fin M) (T ε : ℝ) (hη : 0 < η) (hT : 0 < T)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hClock : 8 * s * (η * T) ≤ Nsl)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) * (η * T)) ^ 3 ≤ ε * (Nsl : ℝ) ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (2 * (s : ℝ)) ∧
      ∀ u : ι → Fin M → ℝ, (∀ i r, 0 ≤ u i r) → (∀ i r, u i r ≤ T) →
      ∃ p : MultiOracleCircuit.Program
          (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ι) (constData D M) Nsl γ η T ε),
        (p.count : ℝ) ≤ 663552 * ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (η * T)
          (ImprovedPrecisionBudget.targetLog ε) ∧
        (TimeDependentExtensions.MeshSelect.alignedInput (constData D M) hM σ b0 Nsl γ η T ε)† ∘L
            TimeDependentExtensions.MeshSelect.alignedInput (constData D M) hM σ b0 Nsl γ η T ε =
          1 ∧
        SelectCriterion p.eval
          (TimeDependentExtensions.MeshSelect.alignedInput (constData D M) hM σ b0 Nsl γ η T ε)
          (constData D M) σ Nsl u ε := by
  obtain ⟨γ, hγ, hγ1, hγs, hAll⟩ := TimeDependentExtensions.Coherent.coherent_select
    (constData D M) hM σ hN b0 η T ε hη hT hε hεOne (fun y => hH y.1) (fun y i => hrow y.1 i)
    (fun y j => hcol y.1 j) hClock hCayley
  refine ⟨γ, hγ, hγ1, hγs, fun u hu huT => ?_⟩
  obtain ⟨p, hcount, hIn, hAct⟩ := hAll u hu huT
  set_option maxRecDepth 8192 in
  exact ⟨p, hcount, hIn, fun x => (hAct x).2⟩

/-- **The released windows simulator meets `WindowsCriterion`** on constant data: under the
hypotheses of `TimeDependentExtensions.Coherent.coherent_windows` (Hermitian instances, entry
bound `η`, a mesh `t` of `[0, T]` with `M` intervals, clock, Cayley and refinement conditions on
`Nsl` slots), there is one rescaling `γ ∈ (0, 1]` with `γ √(2s) ≥ 1` such that for every
public table of windows `a_i ≤ b_i ≤ M` some program over the selection family of
`constData D M` (filter accuracy `ε / 3`) with at most `663552 · shape(2s, ηT, log(3/ε))` calls
(the released count) meets `WindowsCriterion` with the clean isometric input encoding. -/
theorem exists_windowsProgram (D : Data X N Z s) (hH : ∀ x, (D.matrix x).IsHermitian) {η : ℝ}
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) {M : ℕ} (hM : 0 < M) (t : ℕ → ℝ)
    {Nsl : ℕ} (hN : 0 < Nsl) (b0 : ι × Fin M) (T ε : ℝ) (hη : 0 < η) (hT : 0 < T)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : TimeDependentExtensions.IsMesh t M T)
    (hClock : 8 * s * (η * T) ≤ Nsl)
    (hCayley : 9 * (Real.sqrt (2 * (s : ℝ)) * (η * T)) ^ 3 ≤ ε * (Nsl : ℝ) ^ 2)
    (hRefine : 3 * M * (Real.sqrt s * (η * T)) ≤ ε * Nsl) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (2 * (s : ℝ)) ∧
      ∀ a b : ι → ℕ, (∀ i, a i ≤ b i) → (∀ i, b i ≤ M) →
      ∃ p : MultiOracleCircuit.Program (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ι)
          (constData D M) Nsl γ η T (ε / 3)),
        (p.count : ℝ) ≤ 663552 * ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (η * T)
          (ImprovedPrecisionBudget.targetLog (ε / 3)) ∧
        (TimeDependentExtensions.MeshSelect.alignedInput (constData D M) hM
            (TimeDependentExtensions.pieceOf t T Nsl hM) b0 Nsl γ η T (ε / 3))† ∘L
            TimeDependentExtensions.MeshSelect.alignedInput (constData D M) hM
              (TimeDependentExtensions.pieceOf t T Nsl hM) b0 Nsl γ η T (ε / 3) = 1 ∧
        WindowsCriterion p.eval
          (TimeDependentExtensions.MeshSelect.alignedInput (constData D M) hM
            (TimeDependentExtensions.pieceOf t T Nsl hM) b0 Nsl γ η T (ε / 3))
          (constData D M) t a b ε := by
  obtain ⟨γ, hγ, hγ1, hγs, hAll⟩ := TimeDependentExtensions.Coherent.coherent_windows
    (constData D M) hM t hN b0 η T ε hη hT hε hεOne hmesh (fun y => hH y.1)
    (fun y i => hrow y.1 i) (fun y j => hcol y.1 j) hClock hCayley hRefine
  refine ⟨γ, hγ, hγ1, hγs, fun a b hab hbM => ?_⟩
  obtain ⟨p, hcount, hIn, hAct⟩ := hAll a b hab hbM
  set_option maxRecDepth 8192 in
  exact ⟨p, hcount, hIn, fun x => (hAct x).2⟩

end

end TimeDependentLowerBoundExtensions.Coherent
