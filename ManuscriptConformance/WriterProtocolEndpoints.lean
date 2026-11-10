import ManuscriptConformance.WriterProtocols
import ManuscriptConformance.LinearSystemUpper
import ManuscriptConformance.ODEUpper

/-!
# The linear-system and ODE theorems with a writer value oracle (handover item B4)

`qls_thm_main_writer` and `ode_thm_main_writer` restate Theorems `qls:thm:main` and `ode:thm:main`
for value access by a reversible writer specified only on a clean target (`WriterAccess`). The
converted workspace is the released physical workspace with one more register holding a value word
(the scratch register, clean in its zero word, `single0`). The released protocol is run with every
circuit compiled (every value call replaced by writer, adder and inverse writer on the scratch
register; every locator and source call by the same call with the scratch register a spectator) and
every seed and output isometry encoded. Every Born probability, the success mass and the
conditional output are those of the released protocol; the worst-case matrix calls (locator and
writer calls) are at most twice those of the released protocol, the source calls the same. Every
converted call is a primitive call (a locator or the writer) under one fixed unital star-algebra
homomorphism `Φ`, or a source call of the released family with the scratch register a spectator.
-/

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.WriterAccess NativeSparseBlockEncoding
  OracleCircuit
open scoped InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 4000000

universe u v w

/-- **Theorem `qls:thm:main` with a writer value oracle.** The hypotheses of `qls_thm_main`, and a
supplied unitary writer `W x` with `W x |a, 0⟩ = c x a |a, w_a⟩` for the stored words and any
phases: on the released workspace with one more value-word register, the converted protocol `A'`
has the success mass and conditional output of the released protocol `A` on every instance, at most
twice its worst-case matrix calls (locator and writer calls) and the same worst-case source calls. -/
theorem qls_thm_main_writer :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (D : NativeSparseBlockEncoding.Data X n Z s)
        (W : X → WReg n Z →L[ℂ] WReg n Z) (c : X → n × n → ℂ),
        (∀ x, IsUnitary (W x)) →
        (∀ x a, W x (EuclideanSpace.single (a, (0 : Z)) 1) =
          c x a • EuclideanSpace.single (a, D.table x a) 1) →
        ∀ (Ub : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n), (∀ x, IsUnitary (Ub x)) →
        ∀ sv : EuclideanSpace ℂ n, ‖sv‖ = 1 →
        ∀ κ ε : ℝ, 1 ≤ κ → 0 < ε → ε ≤ 1 / 10 →
        ∃ (Tc : ℕ) (A : SparseLinearSystems.Protocol.Tree
            (SparseLinearSystems.Step.physOracle D Ub Tc) (SparseLinearSystems.LogicalWalk.PrivO n)
            (EuclideanSpace ℂ n))
          (Ow : WQuery ⊕ Unit → X →
            PiLp 2 (fun _ : Z => SparseLinearSystems.Step.Phys n Z Tc) →L[ℂ]
              PiLp 2 (fun _ : Z => SparseLinearSystems.Step.Phys n Z Tc))
          (Φ : (WriterAccess.Space n Z →L[ℂ] WriterAccess.Space n Z) →⋆ₐ[ℂ]
            (PiLp 2 (fun _ : Z => SparseLinearSystems.Step.Phys n Z Tc) →L[ℂ]
              PiLp 2 (fun _ : Z => SparseLinearSystems.Step.Phys n Z Tc)))
          (_ : ∀ m x, Ow (.inl m) x = Φ (writerOracles D W m x))
          (_ : ∀ u x, Ow (.inr u) x = diagHom (K' := SparseLinearSystems.Step.Phys n Z Tc) Z
            (SparseLinearSystems.Step.physOracle D Ub Tc (.inr u) x))
          (A' : SparseLinearSystems.Protocol.Tree Ow (SparseLinearSystems.LogicalWalk.PrivO n)
            (EuclideanSpace ℂ n)),
          (A.worstCost SparseLinearSystems.Step.wMat : ℝ) ≤
            C * Real.sqrt s * κ * Real.log (1 / ε) ∧
          (A.worstCost SparseLinearSystems.Step.wSrc : ℝ) ≤
            C * Real.sqrt s * κ * Real.log (1 / ε) ∧
          A'.worstCost wMatW ≤ 2 * A.worstCost SparseLinearSystems.Step.wMat ∧
          A'.worstCost wSrcW = A.worstCost SparseLinearSystems.Step.wSrc ∧
          (A'.worstCost wMatW : ℝ) ≤ 2 * C * Real.sqrt s * κ * Real.log (1 / ε) ∧
          (A'.worstCost wSrcW : ℝ) ≤ C * Real.sqrt s * κ * Real.log (1 / ε) ∧
          (∀ x, A'.successMass x = A.successMass x ∧
            A'.conditionalDensity x = A.conditionalDensity x) ∧
          ∀ x : X,
            ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1 →
            IsUnit (SparseStateOverlap.matrixOperator (D.matrix x)) →
            ‖Ring.inverse (SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ κ →
            2 / 3 ≤ A'.successMass x ∧ ODEMixedOutput.IsDensity (A'.conditionalDensity x) ∧
              TraceDistanceLE (A'.conditionalDensity x)
                (ODEStateNormalization.unitDirection
                  (Ring.inverse (SparseStateOverlap.matrixOperator (D.matrix x)) (Ub x sv))) ε := by
  obtain ⟨C, hC, hqls⟩ := qls_thm_main.{u, v, w}
  refine ⟨C, hC, ?_⟩
  intro X n Z _ _ _ _ _ s D W c hWu hW Ub hUb sv hsv κ ε hκ hε hε1
  obtain ⟨Tc, A, hMat, hSrc, hA⟩ := hqls D Ub hUb sv hsv κ ε hκ hε hε1
  have h1 := (fimplH_flat D W hWu c hW).masked (B := NativeSparseMaskedAccess.Basis n Z) Bool
  have h2 : FImplH Z (NativeCayleyProgram.oracle D) _ wcost :=
    h1.conj (NativeDilationLayout.layout (B := NativeSparseMaskedAccess.Basis n Z))
  have h3 := h2.masked (B := NativeCayleyProgram.Basis n Z) (SparseLinearSystems.Step.Idx Tc)
  obtain ⟨Ow, circ, Φ, hI0, hΦ, hU⟩ := h3.extra
    (fun (_ : Unit) => SparseLinearSystems.Source.sourceOracle
      (ι := SparseLinearSystems.Step.Idx Tc) (Z := Z) Ub)
    (fun _ x => SparseLinearSystems.Source.sourceOracle_unitary Ub hUb x)
  have hI : Impl (SparseLinearSystems.Step.physOracle D Ub Tc) Ow
      (single0 Z (SparseLinearSystems.Step.Phys n Z Tc)) circ wcostU := hI0
  have hcostM : (encodeTree hI A).worstCost wMatW ≤
      2 * A.worstCost SparseLinearSystems.Step.wMat := by
    rw [encodeTree_worstCost]
    exact tree_worstCost_le_mul A wcostU_wMat_le
  have hcostS : (encodeTree hI A).worstCost wSrcW = A.worstCost SparseLinearSystems.Step.wSrc := by
    rw [encodeTree_worstCost]
    exact congrArg A.worstCost (funext wcostU_wSrc)
  refine ⟨Tc, A, Ow, Φ, hΦ, hU, encodeTree hI A, hMat, hSrc, hcostM, hcostS, ?_, ?_,
    fun x => ⟨encodeTree_successMass hI A x, encodeTree_conditionalDensity hI A x⟩,
    fun x h₁ h₂ h₃ => ?_⟩
  · have h' : ((encodeTree hI A).worstCost wMatW : ℝ) ≤
        2 * (A.worstCost SparseLinearSystems.Step.wMat : ℝ) := by exact_mod_cast hcostM
    nlinarith
  · rw [hcostS]
    exact hSrc
  · rw [encodeTree_successMass, encodeTree_conditionalDensity]
    exact hA x h₁ h₂ h₃

/-- **Theorem `ode:thm:main` with a writer value oracle.** The hypotheses of `ode_thm_main`, and a
supplied unitary writer `W x` with `W x |a, 0⟩ = c x a |a, w_a⟩` for the stored words and any
phases: on the released workspace with one more value-word register, the converted circuits `q'`
act as the released circuits `q` on the clean scratch register, at the converted weighted costs,
and their four-trial protocol on the encoded seed and output flag has the guarantees of
`ode_thm_main`, with at most twice the matrix calls (locator and writer calls) and the same source
calls in every history. -/
theorem ode_thm_main_writer :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (D : Data X n Z s)
        (W : X → WReg n Z →L[ℂ] WReg n Z) (c : X → n × n → ℂ),
        (∀ x, IsUnitary (W x)) →
        (∀ x a, W x (EuclideanSpace.single (a, (0 : Z)) 1) =
          c x a • EuclideanSpace.single (a, D.table x a) 1) →
        ∀ (etaH etaD T gbar ε r₀ rb : ℝ),
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 →
        (∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) →
        (∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) →
        (∀ (x : X) (z : EuclideanSpace ℂ n), 0 ≤ (inner ℂ z (SparseStateOverlap.matrixOperator
          (ODEMatrixEnergy.dissipativePart (D.matrix x)) z)).re) →
        ∀ (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
        (∀ y, IsUnitary (J₀ y)) → (∀ y, IsUnitary (Jb y)) →
        ∀ seed : EuclideanSpace ℂ n, ‖seed‖ = 1 →
        ∃ (Tslots d : ℕ)
          (q : ℕ → MultiOracleCircuit.Program
            (ODEFinalNativeSource.physicalOracle
              (ι := Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕ Bool) D
              (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε))
              Tslots d J₀ Jb))
          (M : ℕ)
          (ψ : ODEFinalNativeSource.Physical (Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕
            Bool) n Z (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε))
            Tslots d)
          (F : EuclideanSpace ℂ n →L[ℂ] ODEFinalNativeSource.Physical
            (Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕ Bool) n Z
            (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε)) Tslots d)
          (Ow : WQuery ⊕ Bool → X →
            PiLp 2 (fun _ : Z => ODEFinalNativeSource.Physical
              (Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕ Bool) n Z
              (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε))
              Tslots d) →L[ℂ]
            PiLp 2 (fun _ : Z => ODEFinalNativeSource.Physical
              (Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕ Bool) n Z
              (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε))
              Tslots d))
          (Φ : (WriterAccess.Space n Z →L[ℂ] WriterAccess.Space n Z) →⋆ₐ[ℂ]
            (PiLp 2 (fun _ : Z => ODEFinalNativeSource.Physical
              (Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕ Bool) n Z
              (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε))
              Tslots d) →L[ℂ]
            PiLp 2 (fun _ : Z => ODEFinalNativeSource.Physical
              (Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕ Bool) n Z
              (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε))
              Tslots d)))
          (_ : ∀ m x, Ow (.inl m) x = Φ (writerOracles D W m x))
          (_ : ∀ b x, Ow (.inr b) x = diagHom (K' := ODEFinalNativeSource.Physical
              (Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕ Bool) n Z
              (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε))
              Tslots d) Z (ODEFinalNativeSource.physicalOracle
              (ι := Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕ Bool) D
              (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε))
              Tslots d J₀ Jb (.inr b) x))
          (q' : ℕ → MultiOracleCircuit.Program Ow),
          (∀ j x, (q' j).eval x ∘L single0 Z _ = single0 Z _ ∘L (q j).eval x) ∧
          (∀ j w, (q' j).cost w = (q j).cost (fun l => wcostB l w)) ∧
          ∀ (x : X) (v b : EuclideanSpace ℂ n), ‖v‖ = r₀ → ‖b‖ = rb →
            (v ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection v) →
            (b ≠ 0 → Jb x seed = ODEStateNormalization.unitDirection b) →
            ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 →
            r₀ + T * rb ≤
              gbar * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ →
            ∃ (hM : 0 < M) (hψ : ‖single0 Z _ ψ‖ = 1)
              (hF : (single0 Z _ ∘L F)† ∘L (single0 Z _ ∘L F) = 1),
              HeraldedOutput (ODERepeatProtocol.fourTrials q' M hM (single0 Z _ ψ) hψ
                  (single0 Z _ ∘L F) hF) x
                (ODEStateNormalization.unitDirection
                  (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T)) ε ∧
              RunsClose ((ODERepeatProtocol.fourTrials q' M hM (single0 Z _ ψ) hψ
                  (single0 Z _ ∘L F) hF).conditionalDensity x)
                (ODEStateNormalization.unitDirection
                  (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T)) ε ∧
              ((ODERepeatProtocol.fourTrials q' M hM (single0 Z _ ψ) hψ (single0 Z _ ∘L F)
                  hF).worstCost wMatB : ℝ) ≤
                2 * (C * gbar * (Real.sqrt s * (T * etaH + T * etaD * Real.log (10000 * gbar / ε)) +
                  Real.sqrt (s * (T * etaH + T * etaD * Real.log (10000 * gbar / ε)) *
                    Real.log (10000 * gbar / ε)) + Real.log (10000 * gbar / ε))) ∧
              ∀ c' : Bool, ((ODERepeatProtocol.fourTrials q' M hM (single0 Z _ ψ) hψ
                (single0 Z _ ∘L F) hF).worstCost (wSrcB c') : ℝ) ≤ C * gbar := by
  obtain ⟨C, hC, hode⟩ := ode_thm_main.{u, v, w}
  refine ⟨C, hC, ?_⟩
  intro X n Z _ _ _ _ _ s D W c hWu hW etaH etaD T gbar ε r₀ rb hH hDiss hT hε hεHalf hrH hcH hrD
    hcD hPSD J₀ Jb hJ₀ hJb seed hSeed
  obtain ⟨Tslots, d, q, M, ψ, F, hmain⟩ := hode D etaH etaD T gbar ε r₀ rb hH hDiss hT hε hεHalf
    hrH hcH hrD hcD hPSD J₀ Jb hJ₀ hJb seed hSeed
  have h1 := (fimplH_flat D W hWu c hW).masked (B := NativeSparseMaskedAccess.Basis n Z)
    (ODENativeLayout.Branch Z)
  have h2 : FImplH Z (ODENativeCayley.oracle D) _ wcost :=
    h1.conj (FlatBranchNativeAccess.layout (ι := ODENativeLayout.Branch Z)
      (B := NativeSparseMaskedAccess.Basis n Z))
  have h3 : FImplH Z (ODECoherentCayley.oracle (ι := Option (Fin (ODEPublicSourceMesh.meshSize D T
      (ImprovedODEQueryBudget.precision gbar ε))) × (Fin (ODEPublicGaussianEndpoint.gridSize D T
        gbar ε) ⊕ Bool)) D) _ wcost :=
    h2.diag (Option (Fin (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar
      ε))) × (Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕ Bool))
  have h4 : FImplH Z (ODEJointNative.cayleyOracle (ι := Option (Fin (ODEPublicSourceMesh.meshSize
      D T (ImprovedODEQueryBudget.precision gbar ε))) × (Fin (ODEPublicGaussianEndpoint.gridSize D T
        gbar ε) ⊕ Bool)) D) _ wcost :=
    h3.conj (ODEJointNative.layout (ι := Option (Fin (ODEPublicSourceMesh.meshSize D T
      (ImprovedODEQueryBudget.precision gbar ε))) × (Fin (ODEPublicGaussianEndpoint.gridSize D T
        gbar ε) ⊕ Bool)) (n := n) (Z := Z))
  have h5 := h4.masked (B := ODEJointNative.Basis (Option (Fin (ODEPublicSourceMesh.meshSize
      D T (ImprovedODEQueryBudget.precision gbar ε))) × (Fin (ODEPublicGaussianEndpoint.gridSize D T
        gbar ε) ⊕ Bool)) n Z) (ActiveRegisterLayout.Label PUnit.{1} Tslots d)
  have h6 : FImplH Z (ODEFinalNativeSource.matrixOracle
      (ι := Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕ Bool) D
      (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε)) Tslots d)
      _ wcost := h5.diag Bool
  have h7 := h6.conj (ODEFinalNativeSource.matrixLayout
    (ι := Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕ Bool) (n := n) (Z := Z)
    (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε)) Tslots d)
  have h8 := h7.masked (B := ODEFinalNativeSource.MatrixBasis
    (Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕ Bool) n Z
    (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε)) Tslots d)
    (ODEFinalNativeSource.SourceBasis (Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕ Bool)
      n (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε)))
  obtain ⟨Ow, circ, Φ, hI0, hΦ, hU⟩ := h8.extra (fun b x => ODEFinalNativeSource.physicalOracle
      (ι := Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕ Bool) D
      (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε))
      Tslots d J₀ Jb (.inr b) x)
    (fun b x => ODEFinalNativeSource.physicalOracle_unitary D _ Tslots d J₀ Jb hJ₀ hJb (.inr b) x)
  have hI : Impl (ODEFinalNativeSource.physicalOracle
      (ι := Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕ Bool) D
      (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε))
      Tslots d J₀ Jb) Ow (single0 Z _) circ wcostB := hI0
  refine ⟨Tslots, d, q, M, ψ, F, Ow, Φ, hΦ, hU,
    fun j => EncodedLabeledProgram.compile _ hI.iso _ (q j),
    fun j x => (transfer hI (q j)).2.1 x, fun j w => (transfer hI (q j)).1 w, ?_⟩
  intro x v b hv hb hv0 hb0 hsol hB
  obtain ⟨hM, hψ, hF, hOut, hRuns, hMat, hSrc⟩ := hmain x v b hv hb hv0 hb0 hsol hB
  have hfour := encodeProtocol_fourTrials hI q M hM ψ hψ F hF
  refine ⟨hM, by rw [norm_encode hI.iso, hψ], encode_isometry hI hF, ?_, ?_, ?_, fun c' => ?_⟩
  · rw [← hfour]
    obtain ⟨h₁, h₂, h₃⟩ := hOut
    refine ⟨?_, ?_, ?_⟩
    · rw [encodeProtocol_successMass]; exact h₁
    · rw [encodeProtocol_conditionalDensity]; exact h₂
    · rw [encodeProtocol_conditionalDensity]; exact h₃
  · rw [← hfour, encodeProtocol_conditionalDensity]
    exact hRuns
  · rw [← hfour, encodeProtocol_worstCost]
    have hle := protocol_worstCost_le_mul (ODERepeatProtocol.fourTrials q M hM ψ hψ F hF)
      (w₁ := fun l => wcostB l wMatB) (w₂ := ODESourceQueryBudget.matrixWeight fun _ => 1)
      (k := 2) (fun l => by
        rcases l with l | l
        · exact wcostB_wMat_le (.inl l)
        · exact wcostB_wMat_le (.inr l))
    have hle' : ((ODERepeatProtocol.fourTrials q M hM ψ hψ F hF).worstCost
        (fun l => wcostB l wMatB) : ℝ) ≤ 2 * ((ODERepeatProtocol.fourTrials q M hM ψ hψ F
          hF).worstCost (ODESourceQueryBudget.matrixWeight fun _ => 1) : ℝ) := by
      exact_mod_cast hle
    linarith
  · rw [← hfour, encodeProtocol_worstCost]
    have he : (fun l => wcostB l (wSrcB c')) = ODESourceQueryBudget.sourceWeight c' :=
      funext (wcostB_wSrc c')
    rw [he]
    exact hSrc c'

end
end ManuscriptConformance
