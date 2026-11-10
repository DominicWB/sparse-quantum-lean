import SparseHamiltonian.MaskedProgram
import SparseHamiltonian.ODEStateNormalization

/-!
# The external block-input solver interface of Corollary `qls:cor:separate`

Corollary `qls:cor:separate` uses one result from outside the paper: the linear-system solver of
Gao, Ji and Liu with separate matrix and preparation query bounds. It enters here as the
hypothesis `SeparateSolver cM cb q₀`, a `Prop` passed as a theorem argument; it is never an
axiom, and it is not proved in this package.

`SeparateSolver cM cb q₀` concerns arbitrary finite block-input systems, not the sparse reduction.

* The system space `E` sits in a register `G` through a public isometry `ι`; a unitary `U` on `G`
  block-encodes the matrix `M = ι† U ι` with normalisation one (a projected encoding; the product
  encoding `v ↦ v ⊗ |a₀⟩` is the case `ι = embed a₀`). `M` need not be Hermitian.
* A unitary preparation `P` maps a public unit seed `r₀` to `ι β`, `‖β‖ = 1`.
* The public parameters are `κ ≥ 2`, `0 < δ < 1/2` and an estimate `η > 0` of `‖M⁻¹ β‖`.
* One circuit `S`, with a fixed isometric output selector `out`, is chosen from the public data
  before the oracle pair. Its workspace `Space G w` has one copy of `G` per solver branch; label
  `false` applies `U` and label `true` applies `P` on the branches selected by the fixed mask
  `ctrl`. Inverse calls are part of the program model.
* Separate worst-case budgets: at most `cM κ log(2/δ)` matrix calls and at most `cb (1 + κ/η)`
  preparation calls (`S.labelCount`).
* For every unitary pair with `‖v‖ ≤ κ ‖M v‖` and every `y` with `M y = β` and
  `(3/8) ‖y‖ ≤ η ≤ (5/2) ‖y‖`, the selected vector `a = out† S ψ₀` has `‖a‖² ≥ q₀` and its
  direction is within `δ` of the direction of `y`, up to a phase.

This single-circuit, fixed-selector form is stronger than the statement of Theorem 5.7 of Gao, Ji
and Liu (arXiv:2609.33686), whose success probability `2/3` comes from repeated measurements. It
is intended to follow from their proof: one Hermitian-input run with constant acceptance
probability, their Hermitian reduction for a general block-encoded matrix and the selection of
the lower system sector, before any outer repetition. That derivation is not formalised. The
constants are uniform in the dimensions, `κ`, `η` and `δ`.
-/

set_option autoImplicit false

namespace SparseLinearSystems.Separate

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit
open scoped InnerProduct

universe uE uG

section Workspace

variable (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- The solver workspace: one copy of the oracle register `G` per solver branch. -/
abbrev Space (w : ℕ) := PiLp 2 (fun _ : Fin w => G)

/-- Oracle inputs of the solver: the block encoding and the preparation. -/
abbrev Input := (G →L[ℂ] G) × (G →L[ℂ] G)

/-- Label `false` is the masked block encoding, label `true` the masked preparation. The mask
`ctrl` is part of the solver circuit. -/
def solverOracle (w : ℕ) (ctrl : Fin w → Bool) : Bool → Input G → Space G w →L[ℂ] Space G w :=
  fun b UP => MaskedProgram.masked ctrl (if b then UP.2 else UP.1)

end Workspace

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- The solver's initial state: branch `w₀`, oracle register `v`. -/
def initial {w : ℕ} (w₀ : Fin w) (v : G) : Space G w := PiLp.single 2 w₀ v

omit [InnerProductSpace ℂ G] [CompleteSpace G] in
theorem norm_initial {w : ℕ} (w₀ : Fin w) (v : G) : ‖(initial w₀ v : Space G w)‖ = ‖v‖ := by
  unfold initial
  exact PiLp.norm_single 2 (fun _ : Fin w => G) w₀ v

theorem solverOracle_unitary (w : ℕ) (ctrl : Fin w → Bool) (UP : Input G)
    (hU : IsUnitary UP.1) (hP : IsUnitary UP.2) (b : Bool) :
    IsUnitary (solverOracle G w ctrl b UP) := by
  unfold solverOracle
  cases b
  · exact MaskedProgram.masked_unitary _ _ hU
  · exact MaskedProgram.masked_unitary _ _ hP

/-- **Hypothesis: a uniform block-input solver with separate query budgets** (Gao–Ji–Liu).
For all finite systems, public isometric encodings, unit seeds and public parameters
`κ ≥ 2`, `0 < δ < 1/2`, `η > 0`, there is one circuit and one isometric output selector, with at
most `cM κ log(2/δ)` block-encoding calls and at most `cb (1 + κ/η)` preparation calls, such that
for every unitary block encoding `U` of `M = ι† U ι` and preparation `P` with `P r₀ = ι β`,
`‖β‖ = 1`, `‖v‖ ≤ κ ‖M v‖` and `M y = β` with `(3/8) ‖y‖ ≤ η ≤ (5/2) ‖y‖`, the selected vector has
squared norm at least `q₀` and direction within `δ` of that of `y`, up to a phase. -/
def SeparateSolver (cM cb q₀ : ℝ) : Prop :=
  ∀ (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [CompleteSpace E]
    (G : Type uG) [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
    [CompleteSpace G]
    (ι : E →L[ℂ] G), ι† ∘L ι = 1 → ∀ r₀ : G, ‖r₀‖ = 1 →
  ∀ κ δ η : ℝ, 2 ≤ κ → 0 < δ → δ < 1 / 2 → 0 < η →
  ∃ (w : ℕ) (w₀ : Fin w) (ctrl : Fin w → Bool)
    (S : MultiOracleCircuit.Program (solverOracle G w ctrl)) (out : E →L[ℂ] Space G w),
    out† ∘L out = 1 ∧
    (S.labelCount false : ℝ) ≤ cM * κ * Real.log (2 / δ) ∧
    (S.labelCount true : ℝ) ≤ cb * (1 + κ / η) ∧
    ∀ U P : G →L[ℂ] G, IsUnitary U → IsUnitary P →
      ∀ β y : E, ‖β‖ = 1 → P r₀ = ι β →
        (∀ v, ‖v‖ ≤ κ * ‖(ι† ∘L U ∘L ι) v‖) →
        (ι† ∘L U ∘L ι) y = β →
        3 / 8 * ‖y‖ ≤ η → η ≤ 5 / 2 * ‖y‖ →
        q₀ ≤ ‖(out†) (S.eval (U, P) (initial w₀ r₀))‖ ^ 2 ∧
        ∃ ω : ℂ, ‖ω‖ = 1 ∧
          ‖ω • ODEStateNormalization.unitDirection ((out†) (S.eval (U, P) (initial w₀ r₀))) -
            ODEStateNormalization.unitDirection y‖ ≤ δ

end

end SparseLinearSystems.Separate
