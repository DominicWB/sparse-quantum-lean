import TimeDependentLowerBoundExtensions.Core.Masked
import TimeDependentExtensions.Coherent.Theorem
import TimeDependentHamiltonianLowerBound.Adaptive
import ODELowerBoundExtensions.Release.Normal

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The coherent-selection oracle family on constant data

The paragraphs after the proof of Theorem `hs:thm:time` permit coherent selection of known durations
and start times, "provided the corresponding coherent sampled-time access is supplied". The released
selection theorems (`TimeDependentExtensions.Coherent.coherent_select` and `coherent_windows`) run
on the physical family `TimeDependentExtensions.MeshSelect.alignedOracle (ι := ι) D N γ ρ T ε`: the
coherent sampled-time native Cayley query `∑_{(i,r)} |i,r⟩⟨i,r| ⊗ C_l(x, r)` with a branch register
`ι` (`SparseHamiltonian.TimeDependentODE.cayleyOracle`), in the chronological cells and with the
clean-output alignment spectator.

On constant data (`TimeDependentHamiltonianLowerBound.constData`) every sample is the instance,
so the branch and time registers are untouched spectators, and the native Cayley wrapper
(`ODELowerBoundExtensions.Release.cayleyWrap`) consists of spectators and fixed relabellings:

* `select_normal_form`: every label is `U⁻¹ (1_Ω ⊗ oracles D l x) U` for one fixed isometric
  identification `U` of the workspace;
* `nonempty_selectAccess`: every Boolean certificate of the native primitives passes to the
  selection family with the same weights;
* `admissible_select`, `admissible_callFamily_select`: admissibility with the value-query weight
  (adaptive algorithms), for the labels and for all their call forms (used in `Coherent.Bound`
  and `Coherent.Calls`).
-/

namespace TimeDependentLowerBoundExtensions.Coherent

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseLowerBounds SparseLowerBounds.Hamiltonian HsRelease
open TimeDependentHamiltonianLowerBound (constData)
open scoped InnerProduct InnerProductSpace

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

/-- The fixed wrapper of the coherent-selection family on constant data around one native
primitive: the native Cayley wrapper `ODELowerBoundExtensions.Release.cayleyWrap` on every branch
and time address (all reading the same instance), the fixed flattening
`SparseHamiltonian.TimeDependentODE.layout`, the control, dummy and reference spectators of the
active layer, the chronological cells `ActiveRegisterLayout.Label PUnit Nsl d` and the
clean-output alignment spectator `Bool`. -/
def selectWrap (ι N Z : Type) [Fintype ι] [Fintype N] [DecidableEq N] [Fintype Z] (M Nsl d : ℕ)
    (A : SparseFlagEmbedding.Space (N × N) Z →L[ℂ] SparseFlagEmbedding.Space (N × N) Z) :
    CleanOutputAlignment.Double (TimeDependentODE.Physical ι N Z M Nsl d) →L[ℂ]
      CleanOutputAlignment.Double (TimeDependentODE.Physical ι N Z M Nsl d) :=
  WeightedClock.diagonal (fun _ : Bool =>
    MaskedProgram.masked (fun _ : ActiveRegisterLayout.Label PUnit.{1} Nsl d => true)
      (LookupFromBasisOracle.spectator
        (S := (Bool × TimeDependentODE.Basis ι N Z M) × TimeDependentODE.Basis ι N Z M)
        ((TimeDependentODE.layout (ι := ι) (M := M) (n := N) (Z := Z)).conjStarAlgEquiv
          (WeightedClock.diagonal (fun _ : ι × Fin M =>
            ODELowerBoundExtensions.Release.cayleyWrap N Z A)))))

/-- `selectWrap` consists of spectators and fixed relabellings only. -/
theorem isWrap_selectWrap (ι N Z : Type) [Fintype ι] [Fintype N] [DecidableEq N] [Fintype Z]
    (M Nsl d : ℕ) : ODELowerBoundExtensions.Release.IsWrap (selectWrap ι N Z M Nsl d) :=
  (((((ODELowerBoundExtensions.Release.isWrap_cayleyWrap N Z).diagonalConst (ι × Fin M)).conj
    (TimeDependentODE.layout (ι := ι) (M := M) (n := N) (Z := Z))).spectator
      (S := (Bool × TimeDependentODE.Basis ι N Z M) × TimeDependentODE.Basis ι N Z M)).masked
    (ActiveRegisterLayout.Label PUnit.{1} Nsl d)).diagonalConst Bool

omit [DecidableEq ι] [DecidableEq Z] in
/-- The coherent-selection family of constant data is `selectWrap` of the native primitive. -/
theorem alignedOracle_eq_selectWrap (D : Data X N Z s) (M Nsl : ℕ) (γ ρ T ε : ℝ) (l : Query)
    (x : X) :
    TimeDependentExtensions.MeshSelect.alignedOracle (ι := ι) (constData D M) Nsl γ ρ T ε l x =
      selectWrap ι N Z M Nsl (TimeDependentODE.Select.degree (s : ℝ) γ ρ T ε Nsl)
        (oracles D l x) := by
  cases l <;> rfl

omit [DecidableEq ι] [DecidableEq Z] in
/-- **Normal form of the coherent-selection family on constant data**: for every branch
register `ι`, number `M` of samples, slot count `Nsl` and schedule there are a finite spectator
register `Ω` and a fixed isometric identification `U` of the workspace with `ℂ^Ω ⊗ NSpace` such
that every label is `U⁻¹ (1_Ω ⊗ oracles D l x) U`. -/
theorem select_normal_form (D : Data X N Z s) (M Nsl : ℕ) (γ ρ T ε : ℝ) :
    ∃ (Ω : Type) (_ : Fintype Ω)
      (U : TimeDependentExtensions.MeshSelect.Workspace ι N Z s M Nsl γ ρ T ε ≃ₗᵢ[ℂ]
        Joint Ω (SparseFlagEmbedding.Space (N × N) Z)),
      ∀ l x, TimeDependentExtensions.MeshSelect.alignedOracle (ι := ι) (constData D M) Nsl γ ρ T ε
          l x = U.symm.conjStarAlgEquiv (specOracles Ω D l x) := by
  obtain ⟨Ω, _, U, hU⟩ := isWrap_selectWrap ι N Z M Nsl
    (TimeDependentODE.Select.degree (s : ℝ) γ ρ T ε Nsl)
  exact ⟨Ω, inferInstance, U, fun l x => (alignedOracle_eq_selectWrap D M Nsl γ ρ T ε l x).trans
    (hU _)⟩

omit [DecidableEq ι] [DecidableEq Z] in
/-- **Certificates pass to the selection family**: every Boolean certificate of the native
primitives of `D` gives one of the selection family of `constData D M`, same weights. -/
theorem nonempty_selectAccess {I : Type*} [Fintype I] {y : X → I → Bool} (D : Data X N Z s)
    {w : Query → ℕ} (A : PhaseAccess I y (oracles D) w) (M Nsl : ℕ) (γ ρ T ε : ℝ) :
    Nonempty (PhaseAccess I y
      (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ι) (constData D M) Nsl γ ρ T ε) w) :=
  Core.nonempty_access_of_normal_form D A (select_normal_form D M Nsl γ ρ T ε)

omit [DecidableEq ι] [DecidableEq Z] in
/-- **The selection family of constant data is admissible** with the value-query weight, for
data with input-independent locators. -/
theorem admissible_select (D : Data X N Z s) (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x') (M Nsl : ℕ) (γ ρ T ε : ℝ)
    (q : Query) :
    AdaptiveHamiltonianLowerBound.Access.Admissible D
      (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ι) (constData D M) Nsl γ ρ T ε q)
      (AdaptiveHamiltonianLowerBound.Access.valueWeight q) :=
  TimeDependentHamiltonianLowerBound.admissible_of_normal_form D hrow hcol
    (select_normal_form D M Nsl γ ρ T ε) q

omit [DecidableEq ι] [DecidableEq Z] in
/-- **Every call form of the selection family of constant data is admissible** with the
value-query weight of its label. -/
theorem admissible_callFamily_select (D : Data X N Z s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x') (M Nsl : ℕ) (γ ρ T ε : ℝ)
    (c : Query × AdaptiveODELowerBound.Access.CallForm) :
    AdaptiveHamiltonianLowerBound.Access.Admissible D
      (AdaptiveODELowerBound.Access.callFamily
        (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ι) (constData D M) Nsl γ ρ T ε) c)
      (AdaptiveHamiltonianLowerBound.Access.valueWeight c.1) :=
  Core.admissible_callFamily_of_normal_form D hrow hcol (select_normal_form D M Nsl γ ρ T ε) c

end

end TimeDependentLowerBoundExtensions.Coherent
