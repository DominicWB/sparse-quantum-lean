import UnitaryImplementationExtensions.ApproxOracle
import UnitaryImplementationExtensions.ApproxNorm
import SparseHamiltonian.HamiltonianStability
import SparseHamiltonian.ManuscriptPrecision

set_option autoImplicit false

/-!
# Black-box unitary implementation from inexact entries

Corollary `hs:cor:unitary` of the manuscript (statement in Corollary `hs:cor:unitary`,
finite-precision part of the proof of Corollary `hs:cor:unitary`). The oracle exactly
represents a matrix `Ũ` whose entries are within `ε/(πN)` of the unitary `U`.
The dilation `H̃_U` of `Ũ` is `N`-sparse with norm at most `2`; it is simulated
for time `π/2` with `s = N`, `η = 2` and error `ε/2` by
`ImprovedSparseHamiltonian.simulation_spectral_log_one`. Duhamel's bound
(`HamiltonianStability.output_error_le`) and `‖H̃_U - H_U‖ ≤ N ξ ≤ ε/π` move the
guarantee to the exact dilation `H_U` with total error `ε`, and the exact
identity `exp(-i(π/2) H_U) = -i H_U` with the fixed flag flip and phase
correction (`UnitaryDilationTransfer.exists_clean_unitary_program`) gives a clean
implementation of `U`. The known locators are compiled away
(`ApproxOracle.compile`), so only ordinary entry queries, forward or inverse,
are counted.

The query bound is `inexactConstant * (sqrt (N ℓ) + ℓ)` with `ℓ = log (1/ε)`;
the manuscript's additive `ℓ / log (e + ℓ/N)` comes from the hybrid corollary
`hs:cor:hybrid`, which is not formalised.
-/

namespace UnitaryImplementationExtensions.Inexact

noncomputable section
open SparseHamiltonian
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

/-- The absolute constant of the inexact-entry bound. It is inherited from the
released simulator and is not optimised. -/
def inexactConstant : ℝ :=
  995328 * (Real.pi / Real.sqrt (Real.log 2) + Real.sqrt (2 * Real.pi) + 2)

/-- The constant is positive. -/
theorem inexactConstant_pos : 0 < inexactConstant := by
  unfold inexactConstant
  have h1 : 0 ≤ Real.pi / Real.sqrt (Real.log 2) :=
    div_nonneg Real.pi_pos.le (Real.sqrt_nonneg _)
  have h2 : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  positivity

/-- The three-term simulation bound at `s = N`, `η = 2`, time `π/2` and
precision `ε/2` is at most `inexactConstant * (sqrt (N ℓ) + ℓ)` for
`0 < ε ≤ 1/2`, using `log (2/ε) ≤ 2 ℓ` and `sqrt N ≤ (log 2)^{-1/2} sqrt (N ℓ)`. -/
theorem inexact_budget (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) :
    995328 * (Real.sqrt (N : ℝ) * (2 * |Real.pi / 2|) +
      Real.sqrt ((N : ℝ) * (2 * |Real.pi / 2|) * Real.log (1 / (ε / 2))) +
        Real.log (1 / (ε / 2))) ≤
      inexactConstant * (Real.sqrt ((N : ℝ) * Real.log (1 / ε)) + Real.log (1 / ε)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hℓ2 : Real.log 2 ≤ Real.log (1 / ε) := by
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hε]
    linarith
  have hsplit : Real.log (1 / (ε / 2)) = Real.log 2 + Real.log (1 / ε) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    field_simp
  have hpi : 2 * |Real.pi / 2| = Real.pi := by
    rw [abs_of_pos (by positivity)]
    ring
  rw [hpi]
  set ℓ := Real.log (1 / ε) with hℓ
  have hL : Real.log (1 / (ε / 2)) ≤ 2 * ℓ := by rw [hsplit]; linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hℓpos : 0 < ℓ := hlog2.trans_le hℓ2
  have hsqrtNl : Real.sqrt ((N : ℝ) * ℓ) = Real.sqrt (N : ℝ) * Real.sqrt ℓ :=
    Real.sqrt_mul hN ℓ
  have hsl : Real.sqrt (Real.log 2) ≤ Real.sqrt ℓ := Real.sqrt_le_sqrt hℓ2
  have hs2pos : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 hlog2
  have h1 : Real.sqrt (N : ℝ) * Real.pi ≤
      Real.pi / Real.sqrt (Real.log 2) * Real.sqrt ((N : ℝ) * ℓ) := by
    rw [hsqrtNl, div_mul_eq_mul_div, le_div_iff₀ hs2pos]
    have := mul_le_mul_of_nonneg_left hsl
      (mul_nonneg (Real.sqrt_nonneg (N : ℝ)) Real.pi_pos.le)
    linarith
  have h2 : Real.sqrt ((N : ℝ) * Real.pi * Real.log (1 / (ε / 2))) ≤
      Real.sqrt (2 * Real.pi) * Real.sqrt ((N : ℝ) * ℓ) := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have := mul_le_mul_of_nonneg_left hL (mul_nonneg hN Real.pi_pos.le)
    linarith
  have hc1 : 0 ≤ Real.pi / Real.sqrt (Real.log 2) :=
    div_nonneg Real.pi_pos.le (Real.sqrt_nonneg _)
  have hc2 : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  have hs : 0 ≤ Real.sqrt ((N : ℝ) * ℓ) := Real.sqrt_nonneg _
  unfold inexactConstant
  nlinarith [mul_nonneg hc1 hℓpos.le, mul_nonneg hc2 hℓpos.le]

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z]

/-- The ordinary entry oracle of the represented matrix, with the spectators of
the simulator at `η = 2`, time `π/2` and precision `ε/2`. -/
abbrev oracle (D : ApproxData.Data X n Z) (γ ε : ℝ) :=
  ApproxOracle.oracle D γ 2 (Real.pi / 2) (ε / 2)

/-- The known clean encoding, used for both input and output. -/
def input (D : ApproxData.Data X n Z) (γ ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] UnitaryEntryOracle.Physical n Z γ 2 (Real.pi / 2) (ε / 2) :=
  AlignedMultiOracleProgram.input
    (ImprovedSparseHamiltonian.input (ApproxData.toNative D)
      γ 2 (Real.pi / 2) (ε / 2) ∘L UnitaryEntryData.includeOne)

omit [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **Duhamel transfer.** A simulation of the represented dilation for time
`π/2` with error `ε/2` simulates the exact dilation of the target with error
`ε`, when every entry is within `ε/(πN)`. -/
theorem simulation_transfer {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (D : ApproxData.Data X n Z) (x : X) (ε : ℝ)
    (hEntry : ∀ i j, ‖ApproxData.represented D x i j - D.target x i j‖ ≤
      ε / (Real.pi * Fintype.card n))
    (S : EuclideanSpace ℂ (UnitaryEntryData.Index n) →L[ℂ] K)
    (F : EuclideanSpace ℂ (UnitaryEntryData.Index n) →L[ℂ] K) (hF : ‖F‖ ≤ 1)
    (hSim : ‖S - F ∘L NormedSpace.exp ((-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) •
      SparseStateOverlap.matrixOperator (ApproxData.dilation (ApproxData.represented D x)))‖ ≤
        ε / 2) :
    ‖S - F ∘L NormedSpace.exp ((-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) •
      SparseStateOverlap.matrixOperator (ApproxData.dilation (D.target x)))‖ ≤ ε := by
  have hδ : 0 ≤ ε / (Real.pi * Fintype.card n) :=
    (norm_nonneg _).trans (hEntry (Classical.arbitrary n) (Classical.arbitrary n))
  have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hNδ : (Fintype.card n : ℝ) * (ε / (Real.pi * Fintype.card n)) = ε / Real.pi := by
    field_simp
  have h := HamiltonianStability.output_error_le S F
    (SparseStateOverlap.matrixOperator (ApproxData.dilation (D.target x)))
    (SparseStateOverlap.matrixOperator (ApproxData.dilation (ApproxData.represented D x)))
    (Real.pi / 2) (ε / 2) (ε / Real.pi) hF
    (ApproxNorm.star_matrixOperator_dilation _) (ApproxNorm.star_matrixOperator_dilation _)
    hSim (by rw [← hNδ]; exact ApproxNorm.dilation_error_le D x _ hδ hEntry)
  calc _ ≤ ε / 2 + |Real.pi / 2| * (ε / Real.pi) := h
    _ = ε := by
      rw [abs_of_pos (by positivity)]
      field_simp
      ring

/-- The clean implementation before the known locators are compiled away. -/
theorem native_implementation (D : ApproxData.Data X n Z) (ε : ℝ)
    (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hEntry : ∀ x i j, ‖ApproxData.represented D x i j - D.target x i j‖ ≤
      ε / (Real.pi * Fintype.card n)) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ p : MultiOracleCircuit.Program (ApproxOracle.nativeOracle D γ 2 (Real.pi / 2) (ε / 2)),
        (p.count : ℝ) ≤ inexactConstant *
          (Real.sqrt ((Fintype.card n : ℝ) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (input D γ ε)† ∘L input D γ ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L input D γ ε - input D γ ε ∘L
            SparseStateOverlap.matrixOperator (D.target x)‖ ≤ ε := by
  have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hNδ : (Fintype.card n : ℝ) * (ε / (Real.pi * Fintype.card n)) ≤ 1 := by
    have hEq : (Fintype.card n : ℝ) * (ε / (Real.pi * Fintype.card n)) = ε / Real.pi := by
      field_simp
    rw [hEq, div_le_one Real.pi_pos]
    linarith [Real.pi_gt_three]
  obtain ⟨γ, hγ, hγOne, _hWidth, p, hCount, hInput, hAction⟩ :=
    ImprovedSparseHamiltonian.simulation_spectral_log_one (ApproxData.toNative D)
      2 (Real.pi / 2) (ε / 2) (by norm_num) (half_pos hε) (by linarith)
      (fun x => ApproxData.dilation_hermitian (ApproxData.represented D x))
      (fun x => ApproxNorm.norm_represented_dilation_le D x _
        ((norm_nonneg _).trans (hEntry x (Classical.arbitrary n) (Classical.arbitrary n)))
        (hEntry x) hNδ)
  have hF : ‖ImprovedSparseHamiltonian.input (ApproxData.toNative D)
      γ 2 (Real.pi / 2) (ε / 2)‖ ≤ 1 :=
    LabeledSimulationTransfer.isometry_norm_le_one _ hInput
  obtain ⟨q, hCountEq, _hCosts, hClean, hResult⟩ :=
    UnitaryDilationTransfer.exists_clean_unitary_program
      (ImprovedSparseHamiltonian.oracle (ApproxData.toNative D)
        γ 2 (Real.pi / 2) (ε / 2))
      (ImprovedSparseHamiltonian.oracle_unitary (ApproxData.toNative D)
        γ 2 (Real.pi / 2) (ε / 2))
      (ImprovedSparseHamiltonian.input (ApproxData.toNative D)
        γ 2 (Real.pi / 2) (ε / 2))
      UnitaryEntryData.includeOne UnitaryEntryData.includeZero
      hInput UnitaryEntryData.includeOne_isometry UnitaryEntryData.includeZero_isometry
      (fun x => SparseStateOverlap.matrixOperator
        (UnitaryEntryData.dilationMatrix (ApproxData.targetData D) x))
      (fun x => SparseStateOverlap.matrixOperator (D.target x))
      (UnitaryEntryData.dilation_sq (ApproxData.targetData D))
      (UnitaryEntryData.dilation_includeOne (ApproxData.targetData D))
      p ε (fun x => simulation_transfer D x ε (hEntry x) _ _ hF (hAction x).2)
  refine ⟨γ, hγ, hγOne, q, ?_, hClean, hResult⟩
  rw [hCountEq]
  exact hCount.trans (inexact_budget (Fintype.card n) ε hε hεHalf)

set_option maxHeartbeats 3000000 in
/-- **Unitary implementation from inexact entries.** If the reversible entry
oracle represents a matrix whose entries are within `ε/(πN)` of the unitary
`U = D.target x`, `N = card n`, `0 < ε ≤ 1/2`, then there is a uniform clean
circuit with full-output operator-norm error at most `ε` with respect to `U`,
using at most `inexactConstant * (sqrt (N log (1/ε)) + log (1/ε))` ordinary
entry or inverse-entry queries. No location oracle is used. -/
theorem implementation (D : ApproxData.Data X n Z) (ε : ℝ)
    (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hEntry : ∀ x i j, ‖ApproxData.represented D x i j - D.target x i j‖ ≤
      ε / (Real.pi * Fintype.card n)) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ p : OracleCircuit.Program (oracle D γ ε),
        (p.count : ℝ) ≤ inexactConstant *
          (Real.sqrt ((Fintype.card n : ℝ) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (input D γ ε)† ∘L input D γ ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L input D γ ε - input D γ ε ∘L
            SparseStateOverlap.matrixOperator (D.target x)‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, p, hCount, hInput, hAction⟩ :=
    native_implementation D ε hε hεHalf hEntry
  refine ⟨γ, hγ, hγOne, ApproxOracle.compile D γ 2 (Real.pi / 2) (ε / 2) p,
    ?_, hInput, ?_⟩
  · have hCompile :
        ((ApproxOracle.compile D γ 2 (Real.pi / 2) (ε / 2) p).count : ℝ) ≤
          (p.count : ℝ) := by
      exact_mod_cast ApproxOracle.compile_count_le D γ 2 (Real.pi / 2) (ε / 2) p
    exact hCompile.trans hCount
  · intro x
    simpa only [ApproxOracle.compile_eval] using hAction x

set_option maxHeartbeats 3000000 in
/-- The same guarantee for inputs entangled with an untouched finite reference. -/
theorem reference_error {R : Type*} [Fintype R]
    (D : ApproxData.Data X n Z) (γ ε : ℝ)
    (p : OracleCircuit.Program (oracle D γ ε))
    (hError : ∀ x, ‖p.eval x ∘L input D γ ε - input D γ ε ∘L
      SparseStateOverlap.matrixOperator (D.target x)‖ ≤ ε)
    (x : X) (ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n)) :
    ‖FiniteReferenceLift.lift (p.eval x) (FiniteReferenceLift.lift (input D γ ε) ψ) -
      FiniteReferenceLift.lift (input D γ ε)
        (FiniteReferenceLift.lift (SparseStateOverlap.matrixOperator (D.target x)) ψ)‖ ≤
          ε * ‖ψ‖ :=
  FiniteReferenceLift.same_embedding_error_le (p.eval x) (input D γ ε)
    (SparseStateOverlap.matrixOperator (D.target x)) ε (hError x) ψ

/-- Exact entries are the zero-error case: the theorem applies to the released
entry oracle of exact unitary data (`ApproxOracle.oracle_ofExact`), at the
parameters `η = 2` and precision `ε/2` of the inexact circuit. The sharper
exact-entry form, at `η = 1` and precision `ε`, is `General.implementation`. -/
theorem implementation_ofExact (D : UnitaryEntryData.Data X n Z) (ε : ℝ)
    (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ p : OracleCircuit.Program (UnitaryEntryOracle.oracle D γ 2 (Real.pi / 2) (ε / 2)),
        (p.count : ℝ) ≤ inexactConstant *
          (Real.sqrt ((Fintype.card n : ℝ) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (input (ApproxData.ofExact D) γ ε)† ∘L input (ApproxData.ofExact D) γ ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L input (ApproxData.ofExact D) γ ε -
            input (ApproxData.ofExact D) γ ε ∘L
              SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ ε := by
  have hEntry : ∀ x i j, ‖ApproxData.represented (ApproxData.ofExact D) x i j -
      (ApproxData.ofExact D).target x i j‖ ≤ ε / (Real.pi * Fintype.card n) := by
    intro x i j
    rw [ApproxData.ofExact_represented]
    change ‖D.matrix x i j - D.matrix x i j‖ ≤ _
    rw [sub_self, norm_zero]
    exact div_nonneg hε.le (by positivity)
  exact implementation (ApproxData.ofExact D) ε hε hεHalf hEntry

end
end UnitaryImplementationExtensions.Inexact
