import TimeDependentLowerBoundExtensions.Gate.NonVacuity
import TimeDependentLowerBoundExtensions.Tolerant.Approx

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Private operations realised by sparse queries within an error `ξ`

The manuscript's gate model (lines 1805-1812) gives each controlled private operation an error
at most `ξ` "in the ancilla convention", with a primitive-oracle cost that "is a fixed constant,
independent of `ξ`". The ancilla convention (the paragraph "Temporary ancillas", lines 511-533)
compares an implementation with its ideal operation as a map from the initialised input subspace
to the full output space, residual ancilla state included, and absorbs known changes of encoding.
The manuscript states this gate model for time-independent Hamiltonians (line 1849). Its use for
the slot-selected time-dependent circuits, as in `Gate.Bound`, extends lines 1513-1516; the hard
paths are constant in time.

`ApproxRealization D D_x q ξ` states this for the private operations of the gate-level circuits
of `Gate.Bound`: on one fixed isometric encoding `e` into a control qubit, a spectator register
and the native space, one program over all call forms (plain, inverse, controlled, controlled
inverse; `AdaptiveODELowerBound.Access.callFamily`) of the native sparse queries of `D`, with at
most `q` value calls (location calls free), satisfies `‖p(x) ∘ e - e ∘ D_x‖ ≤ ξ` for every input.
The count `q` does not depend on `ξ`. The error is placed on the bare operation `D_x`; every
controlled call and every inverse call of the circuit then has error at most `ξ` as well, through
masking and adjoints (`masked_approx`, `approx_adjoint`), as the controlled calls of
`Gate.NativeRealization` are obtained from the bare one. The manuscript places the error on the
controlled operation (lines 1805-1807); its hypothesis implies this one: a realisation of the
controlled operation `|0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ D_x` within `ξ` on an isometric encoding restricts,
on the control-one branch `v ↦ |1⟩ ⊗ v`, to a realisation of `D_x` within `ξ` with the same
program and count (`approxRealization_of_controlled`).

The package's configuration-form notion of approximate implementation,
`SparseHamiltonian.GateNative.ApproxOn`, compares two operators on one register on the vectors
supported on a set of configurations. The encoding form is used here because the realised
operation acts on a different space, reached through an arbitrary isometric encoding, as in
`Gate.NativeRealization`.

* `approxRealization_zero_iff`: the case `ξ = 0` is the exact hypothesis
  `Gate.NativeRealization`;
* `ApproxRealization.mono`: larger errors are allowed;
* `approxRealization_of_near`: an exact realisation of an operation within operator-norm
  distance `ξ` of `D_x` is a realisation of `D_x` within `ξ`;
* `approxRealization_call`: every call form of one native sparse query, with `q = 1` and every
  `ξ ≥ 0`;
* `approxRealization_of_controlled`: a realisation of the controlled operation within `ξ` gives
  one of `D_x` within `ξ`, with the same program and count.
-/

namespace TimeDependentLowerBoundExtensions.Tolerant

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseLowerBounds
open TimeDependentLowerBoundExtensions.Gate (NativeRealization)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open AdaptiveODELowerBound.Access (callFamily CallForm)
open scoped InnerProduct InnerProductSpace

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- **Realisation of a private operation within error `ξ`**: on one fixed isometric encoding
`e` into a control qubit, a spectator register and the native space, one program over all call
forms of the native sparse queries of `D`, with at most `q` value calls (location calls free),
implements `D_x` within operator-norm error `ξ` on the encoded subspace,
`‖p(x) ∘ e - e ∘ D_x‖ ≤ ξ`, uniformly in `x`. -/
def ApproxRealization (D : Data X N Z s) (Dp : X → V →L[ℂ] V) (q : ℕ) (ξ : ℝ) : Prop :=
  ∃ (Ω : Type) (_ : Fintype Ω)
    (e : V →L[ℂ] Joint Bool (Joint Ω (SparseFlagEmbedding.Space (N × N) Z)))
    (p : MultiOracleCircuit.Program (callFamily (specOracles Ω D))),
    e† ∘L e = 1 ∧ (∀ x, ‖p.eval x ∘L e - e ∘L Dp x‖ ≤ ξ) ∧
      p.cost (fun c => valueWeight c.1) ≤ q

/-- **The case `ξ = 0` is the exact realisation**: `ApproxRealization D D_x q 0` holds exactly
when `Gate.NativeRealization D D_x q` does. -/
theorem approxRealization_zero_iff (D : Data X N Z s) (Dp : X → V →L[ℂ] V) (q : ℕ) :
    ApproxRealization D Dp q 0 ↔ NativeRealization D Dp q := by
  constructor
  · rintro ⟨Ω, hΩ, e, p, he, hp, hq⟩
    exact ⟨Ω, hΩ, e, p, he, fun x => sub_eq_zero.mp (norm_le_zero_iff.mp (hp x)), hq⟩
  · rintro ⟨Ω, hΩ, e, p, he, hp, hq⟩
    refine ⟨Ω, hΩ, e, p, he, fun x => ?_, hq⟩
    rw [hp x, sub_self, norm_zero]

/-- An exact realisation (`Gate.NativeRealization`) is a realisation within every `ξ ≥ 0`, with
the same program, encoding and count. -/
theorem approxRealization_of_native {D : Data X N Z s} {Dp : X → V →L[ℂ] V} {q : ℕ} {ξ : ℝ}
    (hξ : 0 ≤ ξ) (h : NativeRealization D Dp q) : ApproxRealization D Dp q ξ := by
  obtain ⟨Ω, hΩ, e, p, he, hp, hq⟩ := h
  refine ⟨Ω, hΩ, e, p, he, fun x => ?_, hq⟩
  rw [hp x, sub_self, norm_zero]
  exact hξ

/-- **Larger errors are allowed**: a realisation within `ξ` is one within every `ξ' ≥ ξ`. -/
theorem ApproxRealization.mono {D : Data X N Z s} {Dp : X → V →L[ℂ] V} {q : ℕ} {ξ ξ' : ℝ}
    (h : ApproxRealization D Dp q ξ) (hξ : ξ ≤ ξ') : ApproxRealization D Dp q ξ' := by
  obtain ⟨Ω, hΩ, e, p, he, hp, hq⟩ := h
  exact ⟨Ω, hΩ, e, p, he, fun x => (hp x).trans hξ, hq⟩

/-- **Nearby exact realisations**: if an operation `D'_x` is realised exactly
(`Gate.NativeRealization D D' q`) and `‖D'_x - D_x‖ ≤ ξ` for every input, then `D_x` is realised
within `ξ` with the same program, encoding and count. -/
theorem approxRealization_of_near {D : Data X N Z s} {Dp Dq : X → V →L[ℂ] V} {q : ℕ} {ξ : ℝ}
    (h : NativeRealization D Dq q) (hnear : ∀ x, ‖Dq x - Dp x‖ ≤ ξ) :
    ApproxRealization D Dp q ξ := by
  obtain ⟨Ω, hΩ, e, p, he, hp, hq⟩ := h
  refine ⟨Ω, hΩ, e, p, he, fun x => ?_, hq⟩
  rw [hp x, ← ContinuousLinearMap.comp_sub, EncodedOracle.norm_comp_eq e he]
  exact hnear x

/-- **One call form of a native sparse query**: for any spectator register `Ω`, query `l`, call
form `f` and `ξ ≥ 0`, the private operation `x ↦ callFamily (specOracles Ω D) (l, f) x` is
realised within `ξ` with `q = 1` (`Gate.nativeRealization_call`). -/
theorem approxRealization_call (D : Data X N Z s) (Ω : Type) [Fintype Ω] (l : Query)
    (f : CallForm) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    ApproxRealization D (fun x => callFamily (specOracles Ω D) (l, f) x) 1 ξ :=
  approxRealization_of_native hξ (Gate.nativeRealization_call D Ω l f)

/-- **The manuscript's controlled form implies `ApproxRealization`**: if, on one fixed isometric
encoding `E` of `ℂ² ⊗ V`, one program over all call forms of the native sparse queries of `D`,
with at most `q` value calls, implements the controlled operation
`|0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ D_x` (`masked (fun b => b) D_x`) within `ξ` for every input, then `D_x` is
realised within `ξ` with the same program and count, on the encoding `E ∘ |1⟩`
(`approx_of_controlled`). -/
theorem approxRealization_of_controlled {D : Data X N Z s} {Dp : X → V →L[ℂ] V} {q : ℕ}
    {ξ : ℝ}
    (h : ∃ (Ω : Type) (_ : Fintype Ω)
      (E : Joint Bool V →L[ℂ] Joint Bool (Joint Ω (SparseFlagEmbedding.Space (N × N) Z)))
      (p : MultiOracleCircuit.Program (callFamily (specOracles Ω D))),
      E† ∘L E = 1 ∧
        (∀ x, ‖p.eval x ∘L E - E ∘L MaskedProgram.masked (fun b : Bool => b) (Dp x)‖ ≤ ξ) ∧
        p.cost (fun c => valueWeight c.1) ≤ q) :
    ApproxRealization D Dp q ξ := by
  obtain ⟨Ω, hΩ, E, p, hE, hp, hq⟩ := h
  exact ⟨Ω, hΩ, E ∘L controlOne V, p, comp_controlOne_isometry E hE,
    fun x => approx_of_controlled _ E _ (hp x), hq⟩

end

end TimeDependentLowerBoundExtensions.Tolerant
