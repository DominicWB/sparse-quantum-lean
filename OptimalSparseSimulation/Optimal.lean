import OptimalSparseSimulation.Forms
import OptimalSparseSimulation.Regimes
import LargeSparsityCore.NativeCore
import SparseHamiltonian.ManuscriptPrecision

set_option autoImplicit false

/-!
# Theorem `hs:thm:optimal`: the upper bound

the proof of Theorem `hs:thm:optimal`, eq. `opt:eq:regime-comparison`: for a Hermitian `H` with row
and column Euclidean norms at most `η`, `τ = η|t| ≥ 1`, `0 < ε ≤ 1/64`, `L = log(1/ε)`,
`h = log(e + L/τ)` and `r = L/h`, the evolution `e^{-itH}` is simulated with full-output error at
most `ε` using at most `2·10¹² (√s τ + √(sτr) + r)` native queries (`hs:eq:optimal-bound`, with an
explicit absolute constant). Three constructions are combined, all in the common form
`NativeSignedFactor.Simulates (physOracle D)`:

* `h < 10⁴`: the baseline simulation (`ImprovedSparseHamiltonian.simulation_log_one`,
  Theorem `hs:thm:main`), since then `L = hr ≤ 10⁴ r` (`bounded_bound`);
* `h ≥ 10⁴` and `sτ ≥ Lh`: the large-sparsity core (`LargeSparsityCore.Native.core_simulation`);
* `h ≥ 10⁴` and `sτ < Lh`: the native signed factor with `T = sτ` and `b = √s τ`
  (`NativeSignedFactor.native_signed_simulation_eta`, Theorem `opt:thm:signed`), since then
  `b ≤ r` and `r_b ≤ 4r` (`signed_bound`, `opt:eq:regime-comparison`).

The first two act on their own workspaces; their oracles are native calls with spectators
(`improved_form`, `cayleyActive_form`), and `simulates_of_spectatorForm` moves them to the common
form. Negative times are covered by each construction.

* `optimal_simulation`: the theorem, for every real `t` with `η|t| ≥ 1`.
* `optimal_simulation_with_reference`: the same circuit on inputs entangled with an untouched
  finite reference.
-/

namespace OptimalSparseSimulation

noncomputable section

open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open LargeSparsityCore.Parameters SignedFactorSimulation
open scoped InnerProduct
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096

variable {X : Type*} {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

/-- The query bound of Theorem `hs:thm:optimal`: `2·10¹² (√s τ + √(sτr) + r)` with
`r = r_τ = L/log(e + L/τ)`. -/
def bound (s : ℕ) (τ ε : ℝ) : ℝ :=
  2 * 10 ^ 12 * (Real.sqrt s * τ + Real.sqrt (s * τ * rb τ ε) + rb τ ε)

/-- **Theorem `hs:thm:optimal`, upper bound** (`hs:eq:optimal-bound`). Let `H = D.matrix x` be
Hermitian with row and column Euclidean norms at most `η`, and let `τ = η|t| ≥ 1` and
`0 < ε ≤ 1/64`. Then `e^{-itH}` is simulated in the common form `Simulates (physOracle D)`: one
known isometric input, one program whose only oracle calls are the original native primitives
with spectator registers, unitary for every instance, with full-output error at most `ε`, and
with at most `2·10¹² (√s τ + √(sτr) + r)` calls, `r = L/log(e + L/τ)` and `L = log(1/ε)`. -/
theorem optimal_simulation (D : Data X n Z s) {η t ε : ℝ} (hτ : 1 ≤ η * |t|)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    NativeSignedFactor.Simulates (NativeSignedFactor.physOracle D)
      (fun x => SparseStateOverlap.matrixOperator (D.matrix x)) t ε (bound s (η * |t|) ε) := by
  have hη : 0 < η := by
    by_contra h
    have h' : η ≤ 0 := not_lt.mp h
    nlinarith [abs_nonneg t]
  have hs : 1 ≤ s := D.slots_pos
  have hr := r_pos hτ hε hε1
  have hsτ : (0 : ℝ) ≤ s * (η * |t|) := mul_nonneg (Nat.cast_nonneg s) (by linarith)
  have hsτr := Real.sqrt_nonneg (s * (η * |t|) * rval (η * |t|) ε)
  have hb0 : 0 ≤ Real.sqrt s * (η * |t|) := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have hB : bound s (η * |t|) ε =
      2 * 10 ^ 12 * (Real.sqrt s * (η * |t|) + Real.sqrt (s * (η * |t|) * rval (η * |t|) ε) +
        rval (η * |t|) ε) := rfl
  by_cases h1 : hval (η * |t|) ε < 10 ^ 4
  · -- bounded `h`: the baseline simulation
    obtain ⟨γ, -, -, -, p, hcount, hinp, hp⟩ :=
      ImprovedSparseHamiltonian.simulation_log_one D η t ε hη hε (by linarith) hH hrow hcol
    refine simulates_of_spectatorForm (improved_form D γ η t ε) _ t ε _ _ hinp p ?_ hp
    have hb := bounded_bound (s := s) hτ hε hε1 h1
    unfold Lval at hb
    rw [hB]
    calc (p.count : ℝ)
        ≤ 995328 * (Real.sqrt s * (η * |t|) + Real.sqrt (s * (η * |t|) * Real.log (1 / ε)) +
            Real.log (1 / ε)) := hcount
      _ ≤ 995328 * (10 ^ 4 * (Real.sqrt s * (η * |t|) +
            Real.sqrt (s * (η * |t|) * rval (η * |t|) ε) + rval (η * |t|) ε)) := by
          gcongr
      _ ≤ _ := by nlinarith
  · replace h1 : 10 ^ 4 ≤ hval (η * |t|) ε := not_lt.mp h1
    by_cases h2 : Lval ε * hval (η * |t|) ε ≤ s * (η * |t|)
    · -- large `h` and `sτ ≥ Lh`: the large-sparsity core
      have R : Regime s (η * |t|) ε := ⟨by exact_mod_cast hs, hτ, hε, hε1, h1, h2⟩
      obtain ⟨hinp, p, hcount, hp⟩ :=
        LargeSparsityCore.Native.core_simulation D hη R hH (fun x => ⟨hrow x, hcol x⟩)
      refine simulates_of_spectatorForm (cayleyActive_form D _ _) _ t ε _ _ hinp p ?_ hp
      rw [hB]
      nlinarith
    · -- large `h` and `sτ < Lh`: the native signed factor
      replace h2 : (s : ℝ) * (η * |t|) < Lval ε * hval (η * |t|) ε := not_le.mp h2
      refine (NativeSignedFactor.native_signed_simulation_eta D hη hH hrow hcol t hε hε1).mono ?_
      have hsb := signed_bound (by exact_mod_cast hs) hτ hε hε1 h1 h2
      rw [hB]
      split_ifs
      · positivity
      · nlinarith

/-- **Theorem `hs:thm:optimal` with an untouched reference.** The circuit of
`optimal_simulation` keeps its full-output error on normalised inputs entangled with an
arbitrary finite reference register `R`; the reference does not enter the query bound. -/
theorem optimal_simulation_with_reference {R : Type*} [Fintype R] (D : Data X n Z s)
    {η t ε : ℝ} (hτ : 1 ≤ η * |t|) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ∃ (ι : Type) (_ : Fintype ι)
      (inp : EuclideanSpace ℂ n →L[ℂ] PiLp 2 (fun _ : ι => NativeSignedFactor.Phys n Z))
      (p : MultiOracleCircuit.Program
        (CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle D))),
      inp† ∘L inp = 1 ∧ (p.count : ℝ) ≤ bound s (η * |t|) ε ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ∀ ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n), ‖ψ‖ = 1 →
          ‖FiniteReferenceLift.lift (p.eval x) (FiniteReferenceLift.lift inp ψ) -
            FiniteReferenceLift.lift inp (FiniteReferenceLift.lift (NormedSpace.exp
              ((-Complex.I * (t : ℂ)) • SparseStateOverlap.matrixOperator (D.matrix x))) ψ)‖ ≤
            ε := by
  obtain ⟨ι, hι, inp, p, hinp, hcount, hp⟩ :=
    optimal_simulation D hτ hε hε1 hH hrow hcol
  refine ⟨ι, hι, inp, p, hinp, hcount, fun x => ⟨(hp x).1, fun ψ hψ => ?_⟩⟩
  simpa only [hψ, mul_one] using
    FiniteReferenceLift.same_embedding_error_le (p.eval x) inp _ ε (hp x).2 ψ

end

end OptimalSparseSimulation
