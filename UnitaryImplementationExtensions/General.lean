import SparseHamiltonian.UnitaryImplementation
import SparseHamiltonian.ManuscriptPrecision

set_option autoImplicit false

/-!
# Black-box unitary implementation at general precision

Corollary `hs:cor:unitary` of the manuscript (statement at lines 1769-1788,
exact-entry part of the proof at lines 1790-1812), exact entries and general
precision `0 < ε ≤ 1/2`.
The circuit is the one of `SparseHamiltonian.UnitaryImplementation`: the
Hermitian dilation `H_U = [[0, U], [U†, 0]]` is simulated for time `π/2` with
`s = N` and `η = 1` by `ImprovedSparseHamiltonian.simulation_log_one`, the
exact identity `exp(-i(π/2) H_U) = -i H_U` and a fixed flag flip and phase
correction give the clean implementation, and the known locators are compiled
away by `UnitaryEntryOracle.compile`, so that only ordinary entry queries
(forward or inverse) are counted.

The query bound is `exactConstant * (sqrt (N ℓ) + ℓ)` with `ℓ = log (1/ε)`.
At `ε = 1/4` the oracle and the encoding are those of the released corollary
(`oracle_quarter`, `input_quarter`); the released constant
`UnitaryImplementation.queryConstant` of that instance is kept separately.
The manuscript's additive term `ℓ / log (e + ℓ/N)` comes from the hybrid
corollary `hs:cor:hybrid`, which is not formalised; the bound proved here keeps
the additive `ℓ` of the released simulation theorem.
-/

namespace UnitaryImplementationExtensions.General

noncomputable section
open SparseHamiltonian
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

/-- The absolute constant of the general-precision bound with exact entries.
It is inherited from the released simulator and is not optimised. -/
def exactConstant : ℝ :=
  995328 * (Real.pi / 2 / Real.sqrt (Real.log 2) + Real.sqrt (Real.pi / 2) + 1)

/-- The constant is positive. -/
theorem exactConstant_pos : 0 < exactConstant := by
  unfold exactConstant
  have h1 : 0 ≤ Real.pi / 2 / Real.sqrt (Real.log 2) :=
    div_nonneg (by positivity) (Real.sqrt_nonneg _)
  have h2 : 0 ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
  positivity

/-- The three-term simulation bound at `s = N`, `η = 1`, time `π/2` and
precision `ε ≤ 1/2` is at most `exactConstant * (sqrt (N ℓ) + ℓ)`, using
`sqrt N ≤ (log 2)^{-1/2} sqrt (N ℓ)`. -/
theorem exact_budget (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) :
    995328 * (Real.sqrt (N : ℝ) * (1 * |Real.pi / 2|) +
      Real.sqrt ((N : ℝ) * (1 * |Real.pi / 2|) * Real.log (1 / ε)) +
        Real.log (1 / ε)) ≤
      exactConstant * (Real.sqrt ((N : ℝ) * Real.log (1 / ε)) + Real.log (1 / ε)) := by
  set ℓ := Real.log (1 / ε) with hℓdef
  have hTwo : (2 : ℝ) ≤ 1 / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have hLog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hℓ : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) hTwo
  have hℓpos : 0 < ℓ := hLog2.trans_le hℓ
  have hPi : 0 ≤ Real.pi / 2 := by positivity
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hAbs : 1 * |Real.pi / 2| = Real.pi / 2 := by
    rw [one_mul, abs_of_nonneg hPi]
  rw [hAbs]
  have hSqrtLog2 : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr hLog2
  have hSqrtℓ : Real.sqrt (Real.log 2) ≤ Real.sqrt ℓ := Real.sqrt_le_sqrt hℓ
  have hSplit : Real.sqrt ((N : ℝ) * ℓ) = Real.sqrt (N : ℝ) * Real.sqrt ℓ :=
    Real.sqrt_mul hN ℓ
  have hFirst : Real.sqrt (N : ℝ) * (Real.pi / 2) ≤
      Real.pi / 2 / Real.sqrt (Real.log 2) * Real.sqrt ((N : ℝ) * ℓ) := by
    rw [hSplit]
    have hEq : Real.sqrt (N : ℝ) * (Real.pi / 2) =
        Real.pi / 2 / Real.sqrt (Real.log 2) *
          (Real.sqrt (N : ℝ) * Real.sqrt (Real.log 2)) := by
      field_simp
    rw [hEq]
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hPi hSqrtLog2.le)
    exact mul_le_mul_of_nonneg_left hSqrtℓ (Real.sqrt_nonneg _)
  have hSecond : Real.sqrt ((N : ℝ) * (Real.pi / 2) * ℓ) =
      Real.sqrt (Real.pi / 2) * Real.sqrt ((N : ℝ) * ℓ) := by
    rw [mul_comm (N : ℝ) (Real.pi / 2), mul_assoc, Real.sqrt_mul hPi]
  rw [hSecond]
  unfold exactConstant
  set k := Real.pi / 2 / Real.sqrt (Real.log 2) with hkdef
  set c := Real.sqrt (Real.pi / 2) with hcdef
  set a := Real.sqrt ((N : ℝ) * ℓ) with hadef
  have hk : 0 ≤ k := div_nonneg hPi hSqrtLog2.le
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hkℓ : 0 ≤ k * ℓ := mul_nonneg hk hℓpos.le
  have hcℓ : 0 ≤ c * ℓ := mul_nonneg hc hℓpos.le
  calc
    995328 * (Real.sqrt (N : ℝ) * (Real.pi / 2) + c * a + ℓ) ≤
        995328 * (k * a + c * a + (a + k * ℓ + c * ℓ + ℓ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      linarith
    _ = 995328 * (k + c + 1) * (a + ℓ) := by ring

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z]

/-- The ordinary entry oracle with the simulator's spectators, at precision `ε`. -/
abbrev oracle (D : UnitaryEntryData.Data X n Z) (γ ε : ℝ) :=
  UnitaryEntryOracle.oracle D γ 1 (Real.pi / 2) ε

/-- The known clean encoding, used for both input and output. -/
def input (D : UnitaryEntryData.Data X n Z) (γ ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] UnitaryEntryOracle.Physical n Z γ 1 (Real.pi / 2) ε :=
  AlignedMultiOracleProgram.input
    (ImprovedSparseHamiltonian.input (UnitaryEntryData.toNative D)
      γ 1 (Real.pi / 2) ε ∘L UnitaryEntryData.includeOne)

omit [DecidableEq n] [Nonempty n] [DecidableEq Z] in
/-- At precision `1/4` the oracle is the one of the released corollary. -/
theorem oracle_quarter (D : UnitaryEntryData.Data X n Z) (γ : ℝ) :
    oracle D γ (1 / 4) = UnitaryImplementation.oracle D γ :=
  rfl

/-- At precision `1/4` the encoding is the one of the released corollary. -/
theorem input_quarter (D : UnitaryEntryData.Data X n Z) (γ : ℝ) :
    input D γ (1 / 4) = UnitaryImplementation.input D γ :=
  rfl

set_option maxHeartbeats 3000000 in
/-- **Unitary implementation from exact entries at general precision.** For
`0 < ε ≤ 1/2` there is a uniform clean circuit with full-output operator-norm
error at most `ε`, using at most `exactConstant * (sqrt (N log (1/ε)) +
log (1/ε))` ordinary entry or inverse-entry queries, `N = card n`. -/
theorem implementation (D : UnitaryEntryData.Data X n Z) (ε : ℝ)
    (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ p : OracleCircuit.Program (oracle D γ ε),
        (p.count : ℝ) ≤ exactConstant *
          (Real.sqrt ((Fintype.card n : ℝ) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (input D γ ε)† ∘L input D γ ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L input D γ ε - input D γ ε ∘L
            SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, _hWidth, p, hCount, hInput, hAction⟩ :=
    ImprovedSparseHamiltonian.simulation_log_one (UnitaryEntryData.toNative D)
      1 (Real.pi / 2) ε (by norm_num) hε hεHalf
      (UnitaryEntryData.dilation_hermitian D)
      (UnitaryEntryData.dilation_row_energy D)
      (UnitaryEntryData.dilation_column_energy D)
  obtain ⟨q, hCountEq, _hCosts, hClean, hResult⟩ :=
    UnitaryDilationTransfer.exists_clean_unitary_program
      (ImprovedSparseHamiltonian.oracle (UnitaryEntryData.toNative D)
        γ 1 (Real.pi / 2) ε)
      (ImprovedSparseHamiltonian.oracle_unitary (UnitaryEntryData.toNative D)
        γ 1 (Real.pi / 2) ε)
      (ImprovedSparseHamiltonian.input (UnitaryEntryData.toNative D)
        γ 1 (Real.pi / 2) ε)
      UnitaryEntryData.includeOne UnitaryEntryData.includeZero
      hInput UnitaryEntryData.includeOne_isometry UnitaryEntryData.includeZero_isometry
      (fun x => SparseStateOverlap.matrixOperator (UnitaryEntryData.dilationMatrix D x))
      (fun x => SparseStateOverlap.matrixOperator (D.matrix x))
      (UnitaryEntryData.dilation_sq D) (UnitaryEntryData.dilation_includeOne D)
      p ε (fun x => (hAction x).2)
  refine ⟨γ, hγ, hγOne, UnitaryEntryOracle.compile D γ 1 (Real.pi / 2) ε q,
    ?_, hClean, ?_⟩
  · have hCompile :
        ((UnitaryEntryOracle.compile D γ 1 (Real.pi / 2) ε q).count : ℝ) ≤
          (q.count : ℝ) := by
      exact_mod_cast UnitaryEntryOracle.compile_count_le D γ 1 (Real.pi / 2) ε q
    refine hCompile.trans ?_
    rw [hCountEq]
    exact hCount.trans (exact_budget (Fintype.card n) ε hε hεHalf)
  · intro x
    simp only [UnitaryEntryOracle.compile_eval]
    exact hResult x

set_option maxHeartbeats 3000000 in
/-- The same guarantee for inputs entangled with an untouched finite reference. -/
theorem reference_error {R : Type*} [Fintype R]
    (D : UnitaryEntryData.Data X n Z) (γ ε : ℝ)
    (p : OracleCircuit.Program (oracle D γ ε))
    (hError : ∀ x, ‖p.eval x ∘L input D γ ε - input D γ ε ∘L
      SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ ε)
    (x : X) (ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n)) :
    ‖FiniteReferenceLift.lift (p.eval x) (FiniteReferenceLift.lift (input D γ ε) ψ) -
      FiniteReferenceLift.lift (input D γ ε)
        (FiniteReferenceLift.lift (SparseStateOverlap.matrixOperator (D.matrix x)) ψ)‖ ≤
          ε * ‖ψ‖ :=
  FiniteReferenceLift.same_embedding_error_le (p.eval x) (input D γ ε)
    (SparseStateOverlap.matrixOperator (D.matrix x)) ε (hError x) ψ

end
end UnitaryImplementationExtensions.General
