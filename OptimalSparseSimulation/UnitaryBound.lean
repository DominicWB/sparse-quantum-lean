import OptimalSparseSimulation.Unitary

set_option autoImplicit false

/-!
# The bound of Corollary `hs:cor:unitary` from Corollary `hs:cor:unitary-optimal`

Corollary `hs:cor:unitary` of the manuscript bounds the entry-oracle calls of a unitary
implementation with error on all output registers at most `ε`, `0 < ε ≤ 1/2`, by eq.
`hs:eq:unitarybound`, `O(√(Nℓ) + ℓ/log(e + ℓ/N))` with `ℓ = log(1/ε)`. Its refinement, Corollary
`hs:cor:unitary-optimal` (`unitary_optimal`, `unitary_optimal_inexact`), uses at most
`5·10¹³ (√(N ρ_ε) + ρ_ε)` calls with `ρ_ε = ℓ/log(e + ℓ)`. Since `ρ_ε ≤ ℓ` and, because
`ℓ/N ≤ ℓ`, also `ρ_ε ≤ ℓ/log(e + ℓ/N)`, the circuits of `unitary_optimal*` meet eq.
`hs:eq:unitarybound` with the explicit constant `5·10¹³` (`count_le_unitary_shape`).

The manuscript proves eq. `hs:eq:unitarybound` through Corollary `hs:cor:hybrid`, which is not
formalised and is not used here. Its Appendix `app:formalisation` says of the bound of Corollary
`hs:cor:unitary`: "Lean derives it from the stronger optimal-precision bound, rather than through
Corollary `hs:cor:hybrid`." This module adds that bound as a consequence of the stronger Corollary
`hs:cor:unitary-optimal`. The query lower bound `Ω(√N)` and the worst-case complexity `Θ(√N)` of the
last sentence of Corollary `hs:cor:unitary` are in `UnitaryImplementationExtensions`.

* `rho_le_log`, `rho_le_hybrid`, `optimal_shape_le_unitary_shape`, `count_le_unitary_shape`: the
  scalar comparisons;
* `unitary_bound_inexact`, `unitary_bound`: the upper bound of Corollary `hs:cor:unitary` at every
  precision `0 < ε ≤ 1/2`, for entries within `ε/(πN)` of the intended unitary and for exact
  entries, with at most `5·10¹³ (√(Nℓ) + ℓ/log(e + ℓ/N))` entry-oracle calls (inverse calls
  counted, no location oracle);
* `unitary_bound_inexact_with_reference`, `unitary_bound_with_reference`: the same with an
  untouched finite reference.
-/

namespace OptimalSparseSimulation

noncomputable section

open ContinuousLinearMap SparseHamiltonian OracleCircuit UnitaryPrecision UnitaryEntryOracle
open NativeSparseBlockEncoding (Query)
open UnitaryEntryData (Index)
open LargeSparsityCore.Parameters SignedFactorSimulation
open scoped InnerProduct
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192

/-! ### Scalar comparisons -/

/-- The additive term of eq. `hs:eq:unitarybound`, `ℓ/log(e + ℓ/N)` with `ℓ = log(1/ε)`. -/
def hybridTerm (N : ℕ) (ε : ℝ) : ℝ :=
  Real.log (1 / ε) / Real.log (Real.exp 1 + Real.log (1 / ε) / N)

theorem log_inv_nonneg {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : 0 ≤ Real.log (1 / ε) :=
  Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)

/-- `log(e + y) ≥ 1` for `y ≥ 0`. -/
theorem one_le_log_exp_add {y : ℝ} (hy : 0 ≤ y) : 1 ≤ Real.log (Real.exp 1 + y) := by
  have h : Real.log (Real.exp 1) ≤ Real.log (Real.exp 1 + y) :=
    Real.log_le_log (Real.exp_pos 1) (by linarith)
  rwa [Real.log_exp] at h

/-- `ρ_ε ≤ ℓ`. -/
theorem rho_le_log {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : rho ε ≤ Real.log (1 / ε) :=
  div_le_self (log_inv_nonneg hε hε1) (one_le_log_exp_add (log_inv_nonneg hε hε1))

/-- `ℓ/N ≤ ℓ` for every natural number `N` (with `ℓ/0 = 0`). -/
theorem div_nat_le_self {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (N : ℕ) : ℓ / N ≤ ℓ := by
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h, hℓ]
  · exact div_le_self hℓ (by exact_mod_cast h)

/-- `ρ_ε ≤ ℓ/log(e + ℓ/N)`. -/
theorem rho_le_hybrid {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (N : ℕ) : rho ε ≤ hybridTerm N ε := by
  have hℓ := log_inv_nonneg hε hε1
  have hq : 0 ≤ Real.log (1 / ε) / N := div_nonneg hℓ (Nat.cast_nonneg N)
  have hpos : 0 < Real.log (Real.exp 1 + Real.log (1 / ε) / N) :=
    lt_of_lt_of_le one_pos (one_le_log_exp_add hq)
  have hle : Real.log (Real.exp 1 + Real.log (1 / ε) / N) ≤
      Real.log (Real.exp 1 + Real.log (1 / ε)) :=
    Real.log_le_log (by positivity) (by linarith [div_nat_le_self hℓ N])
  exact div_le_div_of_nonneg_left hℓ hpos hle

/-- `√(N ρ_ε) + ρ_ε ≤ √(Nℓ) + ℓ/log(e + ℓ/N)`. -/
theorem optimal_shape_le_unitary_shape {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (N : ℕ) :
    Real.sqrt (N * rho ε) + rho ε ≤ Real.sqrt (N * Real.log (1 / ε)) + hybridTerm N ε :=
  add_le_add
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (rho_le_log hε hε1) (Nat.cast_nonneg N)))
    (rho_le_hybrid hε hε1 N)

/-- The constant bound `5·10¹³ (√(N ρ_ε) + ρ_ε)` implies the bound of eq. `hs:eq:unitarybound`. -/
theorem count_le_unitary_shape {c : ℝ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (N : ℕ)
    (h : c ≤ 5 * 10 ^ 13 * (Real.sqrt (N * rho ε) + rho ε)) :
    c ≤ 5 * 10 ^ 13 * (Real.sqrt (N * Real.log (1 / ε)) + hybridTerm N ε) :=
  h.trans (mul_le_mul_of_nonneg_left (optimal_shape_le_unitary_shape hε hε1 N) (by norm_num))

/-! ### Corollary `hs:cor:unitary` -/

variable {X : Type*} {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] [Nonempty n]

/-- **Corollary `hs:cor:unitary`, upper bound, inexact entries** (eq. `hs:eq:unitarybound`). Let
the entry table `T` represent, within `ε/(πN)` in every entry, an intended unitary family `U`,
`N = card n`, `0 < ε ≤ 1/2`. There are a known isometric input and one program whose only oracle
calls are ordinary calls of the entry table with spectator registers (no location oracle), unitary
for every instance, with full-output error at most `ε` against `U` and at most
`5·10¹³ (√(Nℓ) + ℓ/log(e + ℓ/N))` calls, inverse calls counted, `ℓ = log(1/ε)`. In the proof they
are the circuit of `unitary_optimal_inexact`, whose count `count_le_unitary_shape` compares. -/
theorem unitary_bound_inexact (T : Table X n Z) (U : X → Matrix n n ℂ)
    (hU : ∀ x, IsUnitary (SparseStateOverlap.matrixOperator (U x))) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2)
    (hEntry : ∀ x i j, ‖T.matrix x i j - U x i j‖ ≤ ε / (Real.pi * Fintype.card n)) :
    ∃ (ι : Type) (_ : Fintype ι)
      (inp : EuclideanSpace ℂ n →L[ℂ] PiLp 2 (fun _ : ι => NativeSignedFactor.Phys (Index n) Z))
      (p : OracleCircuit.Program (entryOracle T ι)),
      inp† ∘L inp = 1 ∧
      (p.count : ℝ) ≤ 5 * 10 ^ 13 *
        (Real.sqrt (Fintype.card n * Real.log (1 / ε)) + hybridTerm (Fintype.card n) ε) ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L inp - inp ∘L SparseStateOverlap.matrixOperator (U x)‖ ≤ ε := by
  obtain ⟨ι, hι, inp, p, hinp, hcount, hp⟩ := unitary_optimal_inexact T U hU ε hε hε1 hEntry
  exact ⟨ι, hι, inp, p, hinp,
    count_le_unitary_shape hε (hε1.trans (by norm_num)) (Fintype.card n) hcount, hp⟩

/-- **Corollary `hs:cor:unitary`, upper bound, exact entries** (eq. `hs:eq:unitarybound`): the
guarantee of `unitary_optimal` with at most `5·10¹³ (√(Nℓ) + ℓ/log(e + ℓ/N))` entry-oracle calls
(in the proof, the circuit of `unitary_optimal`, compared by `count_le_unitary_shape`). -/
theorem unitary_bound (D : UnitaryEntryData.Data X n Z) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2) :
    ∃ (ι : Type) (_ : Fintype ι)
      (inp : EuclideanSpace ℂ n →L[ℂ] PiLp 2 (fun _ : ι => NativeSignedFactor.Phys (Index n) Z))
      (p : OracleCircuit.Program (entryOracle (Table.ofData D) ι)),
      inp† ∘L inp = 1 ∧
      (p.count : ℝ) ≤ 5 * 10 ^ 13 *
        (Real.sqrt (Fintype.card n * Real.log (1 / ε)) + hybridTerm (Fintype.card n) ε) ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L inp - inp ∘L SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ ε := by
  obtain ⟨ι, hι, inp, p, hinp, hcount, hp⟩ := unitary_optimal D ε hε hε1
  exact ⟨ι, hι, inp, p, hinp,
    count_le_unitary_shape hε (hε1.trans (by norm_num)) (Fintype.card n) hcount, hp⟩

/-- **Corollary `hs:cor:unitary`, inexact entries, with an untouched reference.** -/
theorem unitary_bound_inexact_with_reference {R : Type*} [Fintype R] (T : Table X n Z)
    (U : X → Matrix n n ℂ) (hU : ∀ x, IsUnitary (SparseStateOverlap.matrixOperator (U x)))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hEntry : ∀ x i j, ‖T.matrix x i j - U x i j‖ ≤ ε / (Real.pi * Fintype.card n)) :
    ∃ (ι : Type) (_ : Fintype ι)
      (inp : EuclideanSpace ℂ n →L[ℂ] PiLp 2 (fun _ : ι => NativeSignedFactor.Phys (Index n) Z))
      (p : OracleCircuit.Program (entryOracle T ι)),
      inp† ∘L inp = 1 ∧
      (p.count : ℝ) ≤ 5 * 10 ^ 13 *
        (Real.sqrt (Fintype.card n * Real.log (1 / ε)) + hybridTerm (Fintype.card n) ε) ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ∀ ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n), ‖ψ‖ = 1 →
          ‖FiniteReferenceLift.lift (p.eval x) (FiniteReferenceLift.lift inp ψ) -
            FiniteReferenceLift.lift inp
              (FiniteReferenceLift.lift (SparseStateOverlap.matrixOperator (U x)) ψ)‖ ≤ ε := by
  obtain ⟨ι, hι, inp, p, hinp, hcount, hp⟩ :=
    unitary_optimal_inexact_with_reference (R := R) T U hU ε hε hε1 hEntry
  exact ⟨ι, hι, inp, p, hinp,
    count_le_unitary_shape hε (hε1.trans (by norm_num)) (Fintype.card n) hcount, hp⟩

/-- **Corollary `hs:cor:unitary`, exact entries, with an untouched reference.** -/
theorem unitary_bound_with_reference {R : Type*} [Fintype R]
    (D : UnitaryEntryData.Data X n Z) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∃ (ι : Type) (_ : Fintype ι)
      (inp : EuclideanSpace ℂ n →L[ℂ] PiLp 2 (fun _ : ι => NativeSignedFactor.Phys (Index n) Z))
      (p : OracleCircuit.Program (entryOracle (Table.ofData D) ι)),
      inp† ∘L inp = 1 ∧
      (p.count : ℝ) ≤ 5 * 10 ^ 13 *
        (Real.sqrt (Fintype.card n * Real.log (1 / ε)) + hybridTerm (Fintype.card n) ε) ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ∀ ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n), ‖ψ‖ = 1 →
          ‖FiniteReferenceLift.lift (p.eval x) (FiniteReferenceLift.lift inp ψ) -
            FiniteReferenceLift.lift inp
              (FiniteReferenceLift.lift (SparseStateOverlap.matrixOperator (D.matrix x)) ψ)‖ ≤
            ε := by
  obtain ⟨ι, hι, inp, p, hinp, hcount, hp⟩ :=
    unitary_optimal_with_reference (R := R) D ε hε hε1
  exact ⟨ι, hι, inp, p, hinp,
    count_le_unitary_shape hε (hε1.trans (by norm_num)) (Fintype.card n) hcount, hp⟩

end

end OptimalSparseSimulation
