import ManuscriptConformance.WriterProtocols
import ManuscriptConformance.LinearSystemSeparate

/-!
# Corollary `qls:cor:separate` with a writer value oracle

`qls_cor_separate_writer` restates Corollary `qls:cor:separate` for value access by a reversible
writer specified only on a clean target (`WriterAccess`): a supplied unitary writer `W x` with
`W x |a, 0⟩ = c x a |a, w_a⟩` for the stored words `w_a = D.table x a` and any phases `c x a`, an
arbitrary unitary on every other input, and its inverse (inverse calls are part of the program
model). The writer is not assumed to act by addition or XOR on any other target content.

The converted workspace is the physical workspace `Separate.Phys` of `qls_cor_separate` with one
more register holding a value word (the scratch register, clean in its zero word, `single0`).
Every physical call of `Separate.sepOracle` is implemented on this workspace (`Impl`): every
additive value call by writer, adder and inverse writer on the scratch register (two writer
calls), every locator and every controlled preparation call by the same call with the scratch
register a spectator. Each converted call is a primitive call (a locator or the writer) under one
fixed unital star-algebra homomorphism `Φ`, or a preparation call of `Separate.sepOracle` with the
scratch register a spectator.

The protocol of `qls_cor_separate`, fixed before the instance, is run with every circuit compiled
and every seed and output isometry encoded (`encodeProtocol`): its success mass and conditional
output are unchanged on every instance, its worst-case matrix calls (locator and writer calls) at
most double, and its worst-case preparation calls are the same. The external solver hypothesis
`ext_separateSolver` and the repetition count are those of `qls_cor_separate`.
-/

set_option autoImplicit false

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.WriterAccess NativeSparseBlockEncoding
  OracleCircuit
open scoped InnerProduct

set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 4096

universe u v w

set_option maxHeartbeats 4000000 in
/-- **Corollary `qls:cor:separate` with a writer value oracle**, conditional on the external solver
interface (`ext_separateSolver`, Gao–Ji–Liu) of `qls_cor_separate`. The hypotheses of
`qls_cor_separate`, and a supplied unitary writer `W x` with `W x |a, 0⟩ = c x a |a, w_a⟩` for the
stored words and any phases. On the workspace of the protocol `A` of `qls_cor_separate` with one
more value-word register, every physical call is implemented on the clean scratch register
(`hI`); the converted protocol `A' = encodeProtocol hI A`, fixed before the instance, has the
success mass and conditional output of `A` on every instance, at most twice its worst-case matrix
calls (locator and writer calls) and the same worst-case preparation calls. Hence on every
completed history at most `2 C_A √s κ log(1/ε)` matrix calls and, on every input with `‖A‖ ≤ 1`,
`A` invertible, `‖A⁻¹‖ ≤ κ` and `ν/2 ≤ ν̂ ≤ 2ν`, at most `C_b κ/ν` calls of `U_b`, `U_b†`, success
probability at least `2/3`, and conditional output within trace distance `ε` of
`A⁻¹|b⟩/‖A⁻¹b‖`. -/
theorem qls_cor_separate_writer (cM cb q₀ : ℝ) (hcM : 0 ≤ cM) (hcb : 0 < cb) (hq₀ : 0 < q₀)
    (ext_separateSolver : SparseLinearSystems.Separate.SeparateSolver.{v, max v w} cM cb q₀) :
    ∃ CA Cb : ℝ, 0 < CA ∧ 0 < Cb ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (D : NativeSparseBlockEncoding.Data X n Z s)
        (W : X → WReg n Z →L[ℂ] WReg n Z) (c : X → n × n → ℂ),
        (∀ x, IsUnitary (W x)) →
        (∀ x a, W x (EuclideanSpace.single (a, (0 : Z)) 1) =
          c x a • EuclideanSpace.single (a, D.table x a) 1) →
        ∀ (Ub : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n), (∀ x, IsUnitary (Ub x)) →
        ∀ sv : EuclideanSpace ℂ n, ‖sv‖ = 1 →
        ∀ κ ε νh : ℝ, 1 ≤ κ → 0 < ε → ε ≤ 1 / 10 →
        ∃ (Tc : ℕ)
          (A : ODERepeatProtocol.Protocol (SparseLinearSystems.Separate.sepOracle D Ub Tc)
            (EuclideanSpace ℂ n))
          (Ow : WQuery ⊕ Unit → X →
            PiLp 2 (fun _ : Z => SparseLinearSystems.Separate.Phys n Z Tc) →L[ℂ]
              PiLp 2 (fun _ : Z => SparseLinearSystems.Separate.Phys n Z Tc))
          (circ : SparseLinearSystems.Step.Lbl → MultiOracleCircuit.Program Ow)
          (hI : Impl (SparseLinearSystems.Separate.sepOracle D Ub Tc) Ow
            (single0 Z (SparseLinearSystems.Separate.Phys n Z Tc)) circ wcostU)
          (Φ : (WriterAccess.Space n Z →L[ℂ] WriterAccess.Space n Z) →⋆ₐ[ℂ]
            (PiLp 2 (fun _ : Z => SparseLinearSystems.Separate.Phys n Z Tc) →L[ℂ]
              PiLp 2 (fun _ : Z => SparseLinearSystems.Separate.Phys n Z Tc)))
          (_ : ∀ m x, Ow (.inl m) x = Φ (writerOracles D W m x))
          (_ : ∀ u x, Ow (.inr u) x = diagHom (K' := SparseLinearSystems.Separate.Phys n Z Tc) Z
            (SparseLinearSystems.Separate.sepOracle D Ub Tc (.inr u) x))
          (A' : ODERepeatProtocol.Protocol Ow (EuclideanSpace ℂ n)),
          A' = encodeProtocol hI A ∧
          A'.worstCost wMatW ≤ 2 * A.worstCost SparseLinearSystems.Step.wMat ∧
          A'.worstCost wSrcW = A.worstCost SparseLinearSystems.Step.wSrc ∧
          (∀ x, A'.successMass x = A.successMass x ∧
            A'.conditionalDensity x = A.conditionalDensity x) ∧
          (A.worstCost SparseLinearSystems.Step.wMat : ℝ) ≤
            CA * Real.sqrt s * κ * Real.log (1 / ε) ∧
          (A'.worstCost wMatW : ℝ) ≤ 2 * CA * Real.sqrt s * κ * Real.log (1 / ε) ∧
          (∀ h : ODERepeatProtocol.Protocol.History A',
            (h.cost wMatW : ℝ) ≤ 2 * CA * Real.sqrt s * κ * Real.log (1 / ε)) ∧
          ∀ x : X,
            ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1 →
            IsUnit (SparseStateOverlap.matrixOperator (D.matrix x)) →
            ‖Ring.inverse (SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ κ →
            ‖Ring.inverse (SparseStateOverlap.matrixOperator (D.matrix x)) (Ub x sv)‖ / 2 ≤ νh →
            νh ≤ 2 * ‖Ring.inverse (SparseStateOverlap.matrixOperator (D.matrix x)) (Ub x sv)‖ →
            (A.worstCost SparseLinearSystems.Step.wSrc : ℝ) ≤
                Cb * κ / ‖Ring.inverse (SparseStateOverlap.matrixOperator (D.matrix x)) (Ub x sv)‖ ∧
            (A'.worstCost wSrcW : ℝ) ≤
                Cb * κ / ‖Ring.inverse (SparseStateOverlap.matrixOperator (D.matrix x)) (Ub x sv)‖ ∧
            (∀ h : ODERepeatProtocol.Protocol.History A',
              (h.cost wSrcW : ℝ) ≤
                Cb * κ /
                  ‖Ring.inverse (SparseStateOverlap.matrixOperator (D.matrix x)) (Ub x sv)‖) ∧
            2 / 3 ≤ A'.successMass x ∧ ODEMixedOutput.IsDensity (A'.conditionalDensity x) ∧
              TraceDistanceLE (A'.conditionalDensity x)
                (ODEStateNormalization.unitDirection
                  (Ring.inverse (SparseStateOverlap.matrixOperator (D.matrix x)) (Ub x sv))) ε := by
  obtain ⟨CA, Cb, hCA, hCb, hcor⟩ :=
    qls_cor_separate.{u, v, w} cM cb q₀ hcM hcb hq₀ ext_separateSolver
  refine ⟨CA, Cb, hCA, hCb, ?_⟩
  intro X n Z _ _ _ _ _ s D W c hWu hW Ub hUb sv hsv κ ε νh hκ hε hε1
  obtain ⟨Tc, A, hMat, -, hA⟩ := hcor D Ub hUb sv hsv κ ε νh hκ hε hε1
  -- The writer implementation of the physical calls (as for `qls_thm_main_writer`).
  have h1 := (fimplH_flat D W hWu c hW).masked (B := NativeSparseMaskedAccess.Basis n Z) Bool
  have h2 : FImplH Z (NativeCayleyProgram.oracle D) _ wcost :=
    h1.conj (NativeDilationLayout.layout (B := NativeSparseMaskedAccess.Basis n Z))
  have h3 := h2.masked (B := NativeCayleyProgram.Basis n Z)
    (SparseLinearSystems.Separate.Cell Tc)
  obtain ⟨Ow, circ, Φ, hI0, hΦ, hU⟩ := h3.extra
    (fun (_ : Unit) => SparseLinearSystems.Source.sourceOracle
      (ι := SparseLinearSystems.Separate.Cell Tc) (Z := Z) Ub)
    (fun _ x => SparseLinearSystems.Source.sourceOracle_unitary Ub hUb x)
  have hI : Impl (SparseLinearSystems.Separate.sepOracle D Ub Tc) Ow
      (single0 Z (SparseLinearSystems.Separate.Phys n Z Tc)) circ wcostU := hI0
  -- Separate costs: at most two matrix calls per matrix call, the same preparation calls.
  have hcostM : (encodeProtocol hI A).worstCost wMatW ≤
      2 * A.worstCost SparseLinearSystems.Step.wMat := by
    rw [encodeProtocol_worstCost]
    exact protocol_worstCost_le_mul A wcostU_wMat_le
  have hcostS : (encodeProtocol hI A).worstCost wSrcW =
      A.worstCost SparseLinearSystems.Step.wSrc := by
    rw [encodeProtocol_worstCost]
    exact congrArg A.worstCost (funext wcostU_wSrc)
  have hM' : ((encodeProtocol hI A).worstCost wMatW : ℝ) ≤
      2 * CA * Real.sqrt s * κ * Real.log (1 / ε) := by
    have h' : ((encodeProtocol hI A).worstCost wMatW : ℝ) ≤
        2 * (A.worstCost SparseLinearSystems.Step.wMat : ℝ) := by exact_mod_cast hcostM
    calc ((encodeProtocol hI A).worstCost wMatW : ℝ)
        ≤ 2 * (A.worstCost SparseLinearSystems.Step.wMat : ℝ) := h'
      _ ≤ 2 * (CA * Real.sqrt s * κ * Real.log (1 / ε)) := by linarith
      _ = 2 * CA * Real.sqrt s * κ * Real.log (1 / ε) := by ring
  refine ⟨Tc, A, Ow, circ, hI, Φ, hΦ, hU, encodeProtocol hI A, rfl, hcostM, hcostS,
    fun x => ⟨encodeProtocol_successMass hI A x, encodeProtocol_conditionalDensity hI A x⟩,
    hMat, hM', fun h => (Nat.cast_le.mpr (h.cost_le_worstCost _)).trans hM',
    fun x h₁ h₂ h₃ hlo hhi => ?_⟩
  obtain ⟨hS, -, hsucc, hdens, hdist⟩ := hA x h₁ h₂ h₃ hlo hhi
  have hS' : ((encodeProtocol hI A).worstCost wSrcW : ℝ) ≤
      Cb * κ / ‖Ring.inverse (SparseStateOverlap.matrixOperator (D.matrix x)) (Ub x sv)‖ := by
    rw [hcostS]
    exact hS
  refine ⟨hS, hS', fun h => (Nat.cast_le.mpr (h.cost_le_worstCost _)).trans hS', ?_, ?_, ?_⟩
  · rw [encodeProtocol_successMass]
    exact hsucc
  · rw [encodeProtocol_conditionalDensity]
    exact hdens
  · rw [encodeProtocol_conditionalDensity]
    exact hdist

end

end ManuscriptConformance
