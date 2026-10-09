import AdaptiveODELowerBound.Access.Control
import ODELowerBoundExtensions.Homogeneous.Compile

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Value calls of the hard ODE data, their inverses and controlled forms

Manuscript lines 4289-4294: "A matrix value query is implemented using at most two Boolean
membership queries, by computing the relevant bit, writing the known entry, and uncomputing the
bit. The same holds for inverse and controlled calls." and lines 4119-4120 (public location lists
and unitary extensions, so the bounds hold when locators are free).

For the joint family of Theorem `odel:thm:joint` (`SparseLowerBounds.ODE.jointFamily`) and the
homogeneous family of Remark `odel:rem:homogeneous` (`Homogeneous.homFamily`), with any branch
register `ι`:

* `implementsOn_calls_joint`, `implementsOn_calls_hom`: every call form (plain, inverse,
  controlled, controlled inverse; `Access.callFamily`) of every label of the sampled-time access is
  implemented by at most `hardCost` queries of one Boolean membership phase oracle on one isometric
  encoding: at most **two** per value call, **none** per location call. From the released
  certificates `implementsOn_joint`, `Homogeneous.implementsOn_hom` and the generic
  `implementsOn_callFamily`.
* `calls_locator_const_joint`, `calls_locator_const_hom`: the location calls, in every call form,
  are input-independent (public), from the zero query count
  (`EncodedOracle.ImplementsOn.independent_of_zero`).
-/

namespace AdaptiveODELowerBound.Access

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open ODELowerBoundExtensions.Homogeneous (homFamily homBoolean homBusy HomIndex)

-- The nested time-addressed workspaces exceed the default instance size.
set_option synthInstance.maxSize 1024

/-- **Value calls of the joint family, their inverses and controlled forms cost at most two
Boolean queries** (lines 4289-4294): every call form of every sampled-time label of the joint
family is implemented on the call encoding by at most `hardCost` membership queries (two per
value call, none per location call). -/
theorem implementsOn_calls_joint (ι : Type*) [Fintype ι] {M n μ s : ℕ} (hμ : 1 ≤ μ)
    (hμs : 2 ^ μ ≤ s) (T : ℝ) (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T) (c : Query × CallForm) :
    EncodedOracle.ImplementsOn
      (fun x : Promised M n (2 ^ μ) => (callBoolean (jointBoolean ι M n μ s)).phase (membership x))
      (callFamily ((jointFamily M n μ s hμ hμs T hT).access ι) c)
      (callEncoding (ancillaEmbed (Workspace ι (JointIndex M μ s) (Hamiltonian.Word μ) (n + 2))))
      (hardCost c.1) :=
  implementsOn_callFamily (jointBoolean ι M n μ s) membership (ancillaEmbed _)
    _ (Family.access_unitary ι _) hardCost
    (implementsOn_joint ι hμ hμs T hT) c

/-- **The location calls of the joint family are public** in every call form: they do not depend
on the hidden input. -/
theorem calls_locator_const_joint (ι : Type*) [Fintype ι] {M n μ s : ℕ} (hμ : 1 ≤ μ)
    (hμs : 2 ^ μ ≤ s) (T : ℝ) (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T) {q : Query}
    (hq : q ≠ .value) (f : CallForm) (x x' : Promised M n (2 ^ μ)) :
    callFamily ((jointFamily M n μ s hμ hμs T hT).access ι) (q, f) x =
      callFamily ((jointFamily M n μ s hμ hμs T hT).access ι) (q, f) x' := by
  have h := implementsOn_calls_joint ι (M := M) hμ hμs T hT (q, f)
  have h0 : hardCost (q, f).1 = 0 := by
    cases q with
    | value => exact absurd rfl hq
    | _ => rfl
  rw [h0] at h
  exact h.independent_of_zero (callEncoding_isometry _ ancillaEmbed_isometry) x x'

/-- **Value calls of the homogeneous family, their inverses and controlled forms cost at most
two Boolean queries** (lines 4289-4294, 4383-4385): every call form of every sampled-time label
is implemented on the call encoding by at most `hardCost` membership queries. -/
theorem implementsOn_calls_hom (ι : Type*) [Fintype ι] {M n μ s : ℕ} (hμ : 1 ≤ μ)
    (hμs : 2 ^ μ ≤ s) (T : ℝ) (hT : homBusy M n ≤ T) (c : Query × CallForm) :
    EncodedOracle.ImplementsOn
      (fun x : Promised M n (2 ^ μ) => (callBoolean (homBoolean ι M n μ s)).phase (membership x))
      (callFamily ((homFamily M n μ s hμ hμs T hT).access ι) c)
      (callEncoding (ancillaEmbed (Workspace ι (HomIndex M μ s) (Hamiltonian.Word μ) (n + 4))))
      (hardCost c.1) :=
  implementsOn_callFamily (homBoolean ι M n μ s) membership (ancillaEmbed _)
    _ (Family.access_unitary ι _) hardCost
    (ODELowerBoundExtensions.Homogeneous.implementsOn_hom ι hμ hμs T hT) c

/-- **The location calls of the homogeneous family are public** in every call form. -/
theorem calls_locator_const_hom (ι : Type*) [Fintype ι] {M n μ s : ℕ} (hμ : 1 ≤ μ)
    (hμs : 2 ^ μ ≤ s) (T : ℝ) (hT : homBusy M n ≤ T) {q : Query} (hq : q ≠ .value)
    (f : CallForm) (x x' : Promised M n (2 ^ μ)) :
    callFamily ((homFamily M n μ s hμ hμs T hT).access ι) (q, f) x =
      callFamily ((homFamily M n μ s hμ hμs T hT).access ι) (q, f) x' := by
  have h := implementsOn_calls_hom ι (M := M) hμ hμs T hT (q, f)
  have h0 : hardCost (q, f).1 = 0 := by
    cases q with
    | value => exact absurd rfl hq
    | _ => rfl
  rw [h0] at h
  exact h.independent_of_zero (callEncoding_isometry _ ancillaEmbed_isometry) x x'

end

end AdaptiveODELowerBound.Access
