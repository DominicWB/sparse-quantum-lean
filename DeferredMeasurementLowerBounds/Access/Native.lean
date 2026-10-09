import DeferredMeasurementLowerBounds.Deferral.Selection
import AdaptiveHamiltonianLowerBound.Access.Native

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Record-selected native calls are native calls

The admissible labels of the adaptive Hamiltonian-simulation and linear-system lower bounds
(`AdaptiveHamiltonianLowerBound.Access.Admissible`, `LinearSystemLowerBound.Native.Admissible`)
are native calls of weight at least one (in a fixed isometric layout of the workspace as
spectator branches of the native space, each branch applies the identity, one native query or
its inverse) and input-independent unitaries of any weight.

A record-selected call of native calls is again one native call: the layout of
`Joint R K` is the union over the records `r` of the layouts of the labels called at `r`
(`nativeCall_fiber`), inverse calls flip the direction of every branch (`nativeCall_star`), and
records without a call are identity branches of any layout (`nativeCall_one`). Hence, when the
counted labels are the input-dependent ones (`nativeCounted`), every label of the selection
family is admissible with its selection weight (`admissible_selFamily`): branch-dependent labels
and directions in one aligned slot cost one native call, with no loss in the constant.
-/

namespace DeferredMeasurementLowerBounds.Access

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open DeferredMeasurementLowerBounds.Model DeferredMeasurementLowerBounds.Deferral
open AdaptiveHamiltonianLowerBound.Access (NativeCall Admissible)
open scoped InnerProduct

variable {X N Z L : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s : ℕ}
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (D : NativeSparseBlockEncoding.Data X N Z s)

/-- The input-dependent labels of a family; for admissible labels they are native calls of
weight at least one. -/
def nativeCounted (O : L → X → K →L[ℂ] K) : L → Prop := fun l => ¬ ∀ x x', O l x = O l x'

/-- The inverse of a native call is a native call. -/
theorem nativeCall_star {O : X → K →L[ℂ] K} (h : NativeCall D O) :
    NativeCall D (fun x => star (O x)) := by
  obtain ⟨S, hS, layout, call, hcall⟩ := h
  refine ⟨S, hS, layout, fun σ => (call σ).map fun qb => (qb.1, !qb.2), fun x => ?_⟩
  show star (O x) = _
  rw [hcall x, ← map_star, ContinuousLinearMap.star_eq_adjoint, WeightedClock.diagonal_adjoint]
  congr 2
  funext σ
  rw [← ContinuousLinearMap.star_eq_adjoint, AdaptiveHamiltonianLowerBound.Access.callOp_star]

/-- The identity is a native call in the layout of any native call. -/
theorem nativeCall_one {O : X → K →L[ℂ] K} (h : NativeCall D O) :
    NativeCall D (fun _ => (1 : K →L[ℂ] K)) := by
  obtain ⟨S, hS, layout, -, -⟩ := h
  refine ⟨S, hS, layout, fun _ => none, fun x => ?_⟩
  show (1 : K →L[ℂ] K) = layout.symm.conjStarAlgEquiv
    (WeightedClock.diagonal fun _ : S => (1 : LinearSystemLowerBound.Native.NSpace N Z →L[ℂ]
      LinearSystemLowerBound.Native.NSpace N Z))
  rw [WeightedClock.diagonal_one, map_one]

/-- **A record-diagonal of native calls is a native call.** -/
theorem nativeCall_fiber {R : Type} [Fintype R] {U : R → X → K →L[ℂ] K}
    (h : ∀ r, NativeCall D (U r)) : NativeCall D (fun x => Joint.fiber fun r => U r x) := by
  choose S hS layout call hcall using h
  letI : ∀ r, Fintype (S r) := hS
  refine ⟨Σ r, S r, inferInstance,
    (LinearIsometryEquiv.piLpCongrRight 2 fun r => layout r).trans
      (LinearIsometryEquiv.piLpCurry ℂ 2
        (fun r (_ : S r) => LinearSystemLowerBound.Native.NSpace N Z)).symm,
    fun σ => call σ.1 σ.2, fun x => ?_⟩
  ext Ψ r
  rw [Joint.fiber_apply, hcall r x]
  rfl

/-- Input-dependent admissible labels have weight at least one. -/
theorem one_le_of_nativeCounted {O : L → X → K →L[ℂ] K} {w : L → ℕ}
    (hO : ∀ l, Admissible D (O l) (w l)) (l : L) (hl : nativeCounted O l) : 1 ≤ w l := by
  rcases hO l with ⟨_, h⟩ | ⟨hconst, _⟩
  · exact h
  · exact absurd hconst hl

/-- Input-dependent admissible labels are native calls. -/
theorem nativeCall_of_nativeCounted {O : L → X → K →L[ℂ] K} {w : L → ℕ}
    (hO : ∀ l, Admissible D (O l) (w l)) (l : L) (hl : nativeCounted O l) :
    NativeCall D (O l) := by
  rcases hO l with ⟨h, _⟩ | ⟨hconst, _⟩
  · exact h
  · exact absurd hconst hl

/-- An optional call of an input-dependent admissible label is a native call in the layout of
any native call. -/
theorem nativeCall_callOpt {O : L → X → K →L[ℂ] K} {w : L → ℕ}
    (hO : ∀ l, Admissible D (O l) (w l)) {f : X → K →L[ℂ] K} (h₀ : NativeCall D f)
    (c : Option ({l // nativeCounted O l} × Bool)) :
    NativeCall D (callOpt (fun l : {l // nativeCounted O l} => O l.1) c) := by
  rcases c with _ | ⟨l, _ | _⟩
  · exact nativeCall_one D h₀
  · exact nativeCall_of_nativeCounted D hO l.1 l.2
  · exact nativeCall_star D (nativeCall_of_nativeCounted D hO l.1 l.2)

/-- **Every label of the selection family of admissible labels is admissible** with its
selection weight, the counted labels being the input-dependent ones. -/
theorem admissible_selFamily {O : L → X → K →L[ℂ] K} {w : L → ℕ}
    (hO : ∀ l, Admissible D (O l) (w l)) (R : Type) [Fintype R]
    (c : SelLabel (nativeCounted O) R) :
    Admissible D (selFamily O (nativeCounted O) R c) (selWeight c) := by
  rcases c with π | π
  · by_cases hall : ∀ r, π r = none
    · right
      have h1 : ∀ x, selFamily O (nativeCounted O) R (.inl π) x = 1 := by
        intro x
        change Joint.fiber (fun r => callOpt _ (π r) x) = 1
        simp only [hall]
        exact Joint.fiber_one
      refine ⟨fun x x' => by rw [h1 x, h1 x'], fun x => ?_⟩
      rw [h1 x]
      exact ⟨by simp, by simp⟩
    · push Not at hall
      obtain ⟨r₀, hr₀⟩ := hall
      obtain ⟨⟨l₀, b₀⟩, -⟩ := Option.ne_none_iff_exists'.mp hr₀
      have h₀ := nativeCall_of_nativeCounted D hO l₀.1 l₀.2
      exact Or.inl ⟨nativeCall_fiber D fun r => nativeCall_callOpt D hO h₀ (π r), le_rfl⟩
  · right
    have hconst : ∀ x x', selFamily O (nativeCounted O) R (.inr π) x =
        selFamily O (nativeCounted O) R (.inr π) x' := by
      intro x x'
      change Joint.fiber (fun r => callOpt _ (π r) x) = Joint.fiber (fun r => callOpt _ (π r) x')
      congr 1
      funext r
      rcases π r with _ | ⟨l, b⟩
      · rfl
      · have hl : ∀ y y', O l.1 y = O l.1 y' := not_not.mp l.2
        simp only [callOpt, queryOp, hl x x']
    refine ⟨hconst, fun x => ?_⟩
    show IsUnitary (patOp (fun l : {l // ¬ nativeCounted O l} => O l.1) π x)
    have hU : ∀ (l : {l // ¬ nativeCounted O l}) (y : X), IsUnitary (O l.1 y) := fun l y =>
      AdaptiveHamiltonianLowerBound.Access.admissible_unitary D (O l.1) (w l.1) (hO l.1) y
    exact patOp_unitary (O := fun l : {l // ¬ nativeCounted O l} => O l.1) hU π x

/-- The selection family of the linear-system lower bound's admissible labels is admissible. -/
theorem native_admissible_selFamily {n m : ℕ}
    (D : NativeSparseBlockEncoding.Data (Fin n → Fin m) N Z s)
    {O : L → (Fin n → Fin m) → K →L[ℂ] K} {w : L → ℕ}
    (hO : ∀ l, LinearSystemLowerBound.Native.Admissible D (O l) (w l)) (R : Type) [Fintype R]
    (c : SelLabel (nativeCounted O) R) :
    LinearSystemLowerBound.Native.Admissible D (selFamily O (nativeCounted O) R c)
      (selWeight c) := by
  rw [← AdaptiveHamiltonianLowerBound.Access.admissible_iff_native]
  exact admissible_selFamily D (fun l =>
    (AdaptiveHamiltonianLowerBound.Access.admissible_iff_native D (O l) (w l)).mpr (hO l)) R c

end

end DeferredMeasurementLowerBounds.Access
