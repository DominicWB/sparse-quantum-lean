import AdaptiveODELowerBound.Access.Calls
import AdaptiveHamiltonianLowerBound.Cost
import AdaptiveHamiltonianLowerBound.Access.Native

set_option autoImplicit false

/-!
# Search-weight growth of the call forms

Section `odel:sec:main` ("The value oracle and in-place row and column locators have the canonical
reversible access, including inverses, controls and coherent time addresses where needed") and the
construction before Theorem `odel:thm:joint` (a value query "uses at most two membership queries,
also for inverse and controlled calls").

For a labelled oracle family `O` with search-weight growth `w`
(`AdaptiveHamiltonianLowerBound.SearchGrowth`: label `l` has growth `(λ²)^{w l}` for the search
weight, forwards and backwards), every call form of every label
(`AdaptiveODELowerBound.Access.callFamily O`: plain, inverse, controlled and controlled inverse,
on control ⊗ workspace) has the growth of its label (`searchGrowth_callFamily`):

* the plain form `1 ⊗ O_l(x)` is a constant block diagonal
  (`AdaptiveHamiltonianLowerBound.wgrowth_diagonal`);
* the controlled form `|0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ O_l(x)` is the block diagonal of the branch mask
  `SparseHamiltonian.MaskedProgram.masked` with blocks `1` (growth `1 ≤ (λ²)^{w l}`) and `O_l(x)`;
* the inverse forms are the adjoints of these (`MaskedProgram.masked_adjoint`, `Joint.star_fiber`),
  covered by the backward half of the growth hypothesis.

This is the weight-method counterpart of `AdaptiveODELowerBound.Access.implementsOn_callFamily`
(Boolean implementations of the call forms) and applies to any oracle family, in particular to
the released solvers' physical oracles.
-/

namespace PhysicalODELowerBound.Access

noncomputable section
open SparseHamiltonian SparseLowerBounds
open AdaptiveHamiltonianLowerBound (SearchGrowth WGrowth)
open AdaptiveODELowerBound.Access (callFamily CallForm formOp ctrlOp)

/-- A constant block diagonal `1 ⊗ P(x)` on control ⊗ workspace has the growth of `P`. -/
theorem wgrowth_fiber {ι K : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] {m : ℕ} {a : Matrix (Fin m) (Fin m) ℂ}
    {P : (ι → Fin m) → K →L[ℂ] K} {C : ℝ} (hP : WGrowth a P C) :
    WGrowth a (fun j => Joint.fiber (fun _ : Bool => P j)) C := by
  have h1 := AdaptiveHamiltonianLowerBound.wgrowth_diagonal (S := Bool) a (fun _ => P) C
    (fun _ => hP)
  refine AdaptiveHamiltonianLowerBound.wgrowth_congr h1 (fun j => ?_)
  ext Ψ i
  rfl

/-- The controlled form `|0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ P(x)` has the growth `C ≥ 1` of `P`. -/
theorem wgrowth_ctrlOp {ι K : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] {m : ℕ} {a : Matrix (Fin m) (Fin m) ℂ}
    {P : (ι → Fin m) → K →L[ℂ] K} {C : ℝ} (hP : WGrowth a P C) (hC : 1 ≤ C) :
    WGrowth a (fun j => ctrlOp (P j)) C := by
  have h1 := AdaptiveHamiltonianLowerBound.wgrowth_diagonal (S := Bool) a
    (fun c j => if c then P j else 1) C (fun c => by
      cases c
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact AdaptiveHamiltonianLowerBound.wgrowth_mono
          (AdaptiveHamiltonianLowerBound.wgrowth_const a 1 (fun v => by simp)) hC
      · simpa only [↓reduceIte] using hP)
  exact AdaptiveHamiltonianLowerBound.wgrowth_congr h1 (fun j => rfl)

/-- **Call forms have the search-weight growth of their label**: if `O` has search-weight growth
`w`, then every call form of every label (`callFamily O`) has growth `w` of its label. -/
theorem searchGrowth_callFamily {ι K L : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {m : ℕ}
    {O : L → (ι → Fin m) → K →L[ℂ] K} {w : L → ℕ} (h : SearchGrowth m O w) :
    SearchGrowth m (callFamily O) (fun c => w c.1) := by
  intro a ha c
  rcases c with ⟨l, f⟩
  obtain ⟨h1, h2⟩ := h a ha l
  have hC := one_le_pow₀ (n := w l)
    (AdaptiveHamiltonianLowerBound.Access.one_le_searchLam_sq (m := m) ha)
  cases f
  · refine ⟨wgrowth_fiber h1, AdaptiveHamiltonianLowerBound.wgrowth_congr (wgrowth_fiber h2)
      (fun j => ?_)⟩
    show _ = star (Joint.fiber _)
    rw [Joint.star_fiber]
  · refine ⟨wgrowth_fiber h2, AdaptiveHamiltonianLowerBound.wgrowth_congr
      (wgrowth_fiber (P := fun j => star (star (O l j))) (by simpa only [star_star] using h1))
      (fun j => ?_)⟩
    show _ = star (Joint.fiber _)
    rw [Joint.star_fiber]
  · refine ⟨wgrowth_ctrlOp h1 hC, AdaptiveHamiltonianLowerBound.wgrowth_congr
      (wgrowth_ctrlOp h2 hC) (fun j => ?_)⟩
    show _ = star (ctrlOp _)
    simp only [ctrlOp, ContinuousLinearMap.star_eq_adjoint, MaskedProgram.masked_adjoint]
  · refine ⟨wgrowth_ctrlOp h2 hC, AdaptiveHamiltonianLowerBound.wgrowth_congr
      (wgrowth_ctrlOp (P := fun j => star (star (O l j))) (by simpa only [star_star] using h1)
        hC) (fun j => ?_)⟩
    show _ = star (ctrlOp _)
    simp only [ctrlOp, ContinuousLinearMap.star_eq_adjoint, MaskedProgram.masked_adjoint]

end

end PhysicalODELowerBound.Access
