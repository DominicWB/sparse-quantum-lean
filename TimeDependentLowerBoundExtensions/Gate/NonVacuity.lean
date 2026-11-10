import TimeDependentLowerBoundExtensions.Gate.Bound

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The native-realisation hypothesis is satisfiable

The manuscript's gate model (Section `hs:sec:gates`) charges each controlled private operation a
fixed primitive-oracle cost, independent of its error `ξ`: "the primitive query cost remains a fixed
constant independent of `ξ`". The hypothesis `NativeRealization D D_x q` of `Gate.Bound` states this
in exact form, with the cost counted in value calls of the native sparse queries.

* `nativeRealization_call`: every call form (plain, inverse, controlled, controlled inverse;
  `AdaptiveODELowerBound.Access.callFamily`) of one native sparse query of `D`, on any spectator
  register, is natively realised with `q = 1`, by the one-call program and the identity
  encoding.

A realisation of the private operation `D_x = i·beOp D x` of the Hermitian block encodings,
expected with at most `8` value calls, is not proved here; stating it needs a padded qubit layout
of the native sparse space.
-/

namespace TimeDependentLowerBoundExtensions.Gate

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseLowerBounds
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open AdaptiveODELowerBound.Access (callFamily CallForm)
open scoped InnerProduct InnerProductSpace

/-- **One call form of a native sparse query is natively realised with `q = 1`**: for any
spectator register `Ω`, query `l` and call form `f`, the private operation
`x ↦ callFamily (specOracles Ω D) (l, f) x` is implemented exactly by the program with the
single call `(l, f)` on the identity encoding, with at most one value call. The manuscript's gate
model (Section `hs:sec:gates`) assumes a fixed primitive-oracle cost per private operation;
`NativeRealization` states that assumption in exact form, and this is its simplest instance. -/
theorem nativeRealization_call {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] {s : ℕ} (D : Data X N Z s) (Ω : Type) [Fintype Ω] (l : Query)
    (f : CallForm) :
    NativeRealization D (fun x => callFamily (specOracles Ω D) (l, f) x) 1 := by
  refine ⟨Ω, inferInstance, 1, MultiOracleCircuit.Program.query (l, f), ?_, fun x => ?_, ?_⟩
  · rw [ContinuousLinearMap.one_def, ContinuousLinearMap.adjoint_id,
      ContinuousLinearMap.id_comp]
  · rw [MultiOracleCircuit.Program.eval_query, ContinuousLinearMap.one_def,
      ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
  · show valueWeight l ≤ 1
    cases l <;> simp [valueWeight]

end

end TimeDependentLowerBoundExtensions.Gate
