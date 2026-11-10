import ManuscriptConformance.WriterTimeEndpoints
import ManuscriptConformance.ActualRuns
import ManuscriptConformance.ODETime

/-!
# Per-run accuracy and approximate sources with a time-indexed writer (handover item B4)

The writer conversion moves a trial family by compiling its circuits and encoding its seed and
output isometry; the selected outputs of the trials are unchanged (`encodeTrials_amplitude`). So
the per-run properties of `ActualRuns` transfer: `trialsClose_encode`, `historiesClose_encode`
(every positive-probability successful trial and history is as accurate as before, the conditional
density the same ensemble of histories). Every endpoint over the actual oracles of the
time-dependent solver (`MeshOracles.actualOracle`: `ode_thm_time`, `ode_thm_time_actual`, the
branch-certificate forms) or of `ode:thm:general` (`GeneralODE.physicalOracle`) converts through
`fimplH_meshActual`, resp. `impl_generalPhysical`, and these lemmas.

`ode_thm_time_actual_writer`: Theorem `ode:thm:time` for exact source preparations with a
time-indexed writer, with `HeraldedOutput`, `TrialsClose` and `HistoriesClose` for the converted
four-attempt protocol and the doubled matrix-call budget.

Sources with temporary work registers: `fimplH_meshMatrix` (the matrix calls alone, for any supplied
source operations), `fimplH_workActual` (the actual oracles `CleanWorkODE.actualOracleW`: the matrix
calls with the work register a spectator, a homomorphism layer) and `ode_thm_time_approx_writer`
(Theorem `ode:thm:time` for approximate source preparations on clean work registers, with a
time-indexed writer: `HeraldedOutput` and the doubled budget for the converted protocol).
-/

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Set
open SparseHamiltonian.GeneralSourceExtensions SparseHamiltonian.WriterAccess
open scoped InnerProduct InnerProductSpace
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 4000000

universe u v w

section Transfer

variable {K K' P : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  {X L Q : Type*}
  {O : L → X → K →L[ℂ] K} {Ow : Q → X → K' →L[ℂ] K'} {E : K →L[ℂ] K'}
  {circ : L → MultiOracleCircuit.Program Ow} {c : L → (Q → ℕ) → ℕ}

/-- The encoded trials have the selected output directions of the released trials. -/
theorem encodeTrials_outputDirection (h : Impl O Ow E circ c)
    (t : ODERepeatProtocol.TrialFamily O P) (x : X) (j : Fin t.choices) :
    (encodeTrials h t).outputDirection x j = t.outputDirection x j := by
  unfold ODERepeatProtocol.TrialFamily.outputDirection
  rw [encodeTrials_amplitude]

/-- **Every accurate actual trial stays accurate** under the writer conversion. -/
theorem trialsClose_encode (h : Impl O Ow E circ c) (t : ODERepeatProtocol.TrialFamily O P)
    (x : X) (target : P) (ε : ℝ) (ht : TrialsClose t x target ε) :
    TrialsClose (encodeTrials h t) x target ε := by
  intro j hj
  rw [encodeTrials_amplitude] at hj
  obtain ⟨ω, hω, hle⟩ := ht j hj
  exact ⟨ω, hω, by rw [encodeTrials_outputDirection]; exact hle⟩

/-- **Every accurate successful history stays accurate** under the writer conversion, with the same
ensemble of histories. -/
theorem historiesClose_encode (h : Impl O Ow E circ c) (t : ODERepeatProtocol.TrialFamily O P)
    (x : X) (target : P) (ε : ℝ) (ht : HistoriesClose t x target ε) :
    HistoriesClose (encodeTrials h t) x target ε := by
  obtain ⟨h1, h2⟩ := ht
  have hp : (encodeTrials h t).probability x = t.probability x :=
    funext (encodeTrials_probability h t x)
  have hd : (fun a : Fin 4 × Fin t.choices => (encodeTrials h t).outputDirection x a.2) =
      (fun a : Fin 4 × Fin t.choices => t.outputDirection x a.2) :=
    funext fun a => encodeTrials_outputDirection h t x a.2
  refine ⟨?_, fun a ha => ?_⟩
  · rw [← encodeProtocol_repeat, encodeProtocol_conditionalDensity, h1, hp]
    exact congrArg _ hd.symm
  · rw [hp] at ha
    obtain ⟨hne, ω, hω, hle⟩ := h2 a ha
    exact ⟨by rw [encodeTrials_amplitude]; exact hne, ω, hω,
      by rw [encodeTrials_outputDirection]; exact hle⟩

end Transfer

/-- **Theorem `ode:thm:time` for exact source preparations with a time-indexed writer, with the
accuracy of every actual successful trial and history.** The hypotheses of `ode_thm_time_actual`
and a time-indexed writer as in `ode_thm_time_writer`: the trial family `tf` of
`ode_thm_time_actual` converted (`tf'`: every circuit compiled, the seed and output isometry
encoded) has the success mass and conditional output of `tf` in its four-attempt protocol, at most
twice its worst-case matrix calls and the same source calls; under the instance conditions:
`HeraldedOutput`, `TrialsClose`, `HistoriesClose` for `tf'` and the doubled budget. -/
theorem ode_thm_time_actual_writer :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s M : ℕ} (D : Data (X × Fin M) n Z s), 0 < M →
        ∀ (W : X × Fin M → WReg n Z →L[ℂ] WReg n Z) (c : X × Fin M → n × n → ℂ),
        (∀ y, IsUnitary (W y)) →
        (∀ y a, W y (EuclideanSpace.single (a, (0 : Z)) 1) =
          c y a • EuclideanSpace.single (a, D.table y a) 1) →
        ∀ (t : ℕ → ℝ) (N : ℕ), 0 < N →
        ∀ (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ),
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 1 ≤ gbar → 1 ≤ cq → 0 < ε → ε ≤ 1 →
        TimeDependentExtensions.IsMesh t M T →
        8 * s * ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T) ≤ N →
        3 * (Real.sqrt (2 * (s : ℝ)) *
          ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
          TimeDependentODE.precision (cq * gbar) ε * (N : ℝ) ^ 2 →
        (∀ i, v i ∈ Icc 0 T) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        ∀ (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))), (∀ x, IsUnitary (Pw x)) →
        ∀ (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
        (∀ x a, IsUnitary (J x a)) →
        ∀ seed : EuclideanSpace ℂ n, ‖seed‖ = 1 →
        ∃ (d : ℕ) (tf : ODERepeatProtocol.TrialFamily
            (MeshOracles.actualOracle (ι := TimeDependentODE.Index D T (cq * gbar) ε) D m N d Pw J)
            (EuclideanSpace ℂ n))
          (Ow : WQuery ⊕ GeneralSourceODE.SourceCall → X →
            PiLp 2 (fun _ : Z => MeshNative.PhysicalSpace (TimeDependentODE.Index D T (cq * gbar) ε)
              n Z m M N d) →L[ℂ]
            PiLp 2 (fun _ : Z => MeshNative.PhysicalSpace (TimeDependentODE.Index D T (cq * gbar) ε)
              n Z m M N d))
          (Φ : (PiLp 2 (fun _ : Fin M => WriterAccess.Space n Z) →L[ℂ]
              PiLp 2 (fun _ : Fin M => WriterAccess.Space n Z)) →⋆ₐ[ℂ]
            (PiLp 2 (fun _ : Z => MeshNative.PhysicalSpace (TimeDependentODE.Index D T (cq * gbar) ε)
              n Z m M N d) →L[ℂ]
            PiLp 2 (fun _ : Z => MeshNative.PhysicalSpace (TimeDependentODE.Index D T (cq * gbar) ε)
              n Z m M N d)))
          (_ : ∀ q x, Ow (.inl q) x = Φ (timeWriterOracles D W q x))
          (_ : ∀ k x, Ow (.inr k) x = diagHom (K' := MeshNative.PhysicalSpace
              (TimeDependentODE.Index D T (cq * gbar) ε) n Z m M N d) Z
            (MeshOracles.actualOracle (ι := TimeDependentODE.Index D T (cq * gbar) ε) D m N d Pw J
              (.inr k) x))
          (tf' : ODERepeatProtocol.TrialFamily Ow (EuclideanSpace ℂ n)),
          tf'.choices = tf.choices ∧
          (∀ x, (ODERepeatProtocol.Protocol.repeatTrials tf' 4).successMass x =
              (ODERepeatProtocol.Protocol.repeatTrials tf 4).successMass x ∧
            (ODERepeatProtocol.Protocol.repeatTrials tf' 4).conditionalDensity x =
              (ODERepeatProtocol.Protocol.repeatTrials tf 4).conditionalDensity x) ∧
          (ODERepeatProtocol.Protocol.repeatTrials tf' 4).worstCost wMatS ≤
            2 * (ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
              GeneralSourceODE.Oracles.matrixCalls ∧
          (ODERepeatProtocol.Protocol.repeatTrials tf' 4).worstCost wSrcS =
            (ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
              GeneralSourceODE.Oracles.sourceCalls ∧
          ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
            (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
            (bv : Fin m → EuclideanSpace ℂ n)
            (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces t G →
            RepresentedSampleODE.MildSolution t T b sol U →
            formal_classicalPropagator G t T U →
            GeneralSourceODE.Compiled.WeightPrep (Pw x) (GeneralSourceODE.sources (sol 0) bv ω) →
            (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
            (∀ i, ω i ≠ 0 → bv i ≠ 0 →
              J x (some i) seed = ODEStateNormalization.unitDirection (bv i)) →
            ODESourceBranches.mass (GeneralSourceODE.sources (sol 0) bv ω) ≤
              cq * Mesh.meshScale sol b t →
            ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
                ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * Mesh.meshScale sol b t →
            sol T ≠ 0 →
            Mesh.meshScale sol b t ≤ gbar * ‖sol T‖ →
            ζ + cq * (Mesh.sampleError D x t G + 2 * RepresentedSampleODE.dissipativeError D x t G +
                2 * Mesh.refinementError D t T N) ≤ ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (cq * gbar) ε *
                (RepresentedSampleODE.dissipativeError D x t G + Mesh.refinementError D t T N) ≤
              TimeDependentODE.precision (cq * gbar) ε →
            HeraldedOutput (ODERepeatProtocol.Protocol.repeatTrials tf' 4) x
              (ODEStateNormalization.unitDirection (sol T)) ε ∧
            TrialsClose tf' x (sol T) ε ∧ HistoriesClose tf' x (sol T) ε ∧
            ((ODERepeatProtocol.Protocol.repeatTrials tf' 4).worstCost wMatS : ℝ) ≤
              2 * (C * (cq * gbar) * (Real.sqrt s * (T * etaH + T * etaD *
                  Real.log (40000 * cq * gbar / ε)) +
                Real.sqrt (s * (T * etaH + T * etaD * Real.log (40000 * cq * gbar / ε)) *
                  Real.log (40000 * cq * gbar / ε)) + Real.log (40000 * cq * gbar / ε))) ∧
            ((ODERepeatProtocol.Protocol.repeatTrials tf' 4).worstCost wSrcS : ℝ) ≤
              C * (cq * gbar) := by
  obtain ⟨C, hC, hode⟩ := ode_thm_time_actual.{u, v, w}
  refine ⟨C, hC, ?_⟩
  intro X n Z _ _ _ _ _ s M D hM W c hWu hW t N hN etaH etaD T gbar cq ε m v ω hH hDiss hT hg hcq
    hε hεOne hmesh hClock hCayley hv hrH hcH hrD hcD Pw hPw J hJ seed hSeed
  obtain ⟨d, tf, hA⟩ := hode D hM t N hN etaH etaD T gbar cq ε v ω hH hDiss hT hg hcq hε hεOne
    hmesh hClock hCayley hv hrH hcH hrD hcD Pw hPw J hJ seed hSeed
  obtain ⟨Ow, circ, Φ, hI, hΦ, hU⟩ := fimplH_meshActual
    (ι := TimeDependentODE.Index D T (cq * gbar) ε) D W hWu c hW N d hPw hJ
  have hrep := encodeProtocol_repeat hI tf 4
  have hsrc : (fun l => wcostS l wSrcS) = GeneralSourceODE.Oracles.sourceCalls :=
    funext wcostS_wSrc
  have hmat : (ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
      (fun l => wcostS l wMatS) ≤
      2 * (ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
        GeneralSourceODE.Oracles.matrixCalls :=
    protocol_worstCost_le_mul _ (w₁ := fun l => wcostS l wMatS)
      (w₂ := GeneralSourceODE.Oracles.matrixCalls) (k := 2) wcostS_wMat_le
  refine ⟨d, tf, Ow, Φ, hΦ, hU, encodeTrials hI tf, rfl, fun x => ?_, ?_, ?_, ?_⟩
  · rw [← hrep, encodeProtocol_successMass, encodeProtocol_conditionalDensity]
    exact ⟨rfl, rfl⟩
  · rw [← hrep, encodeProtocol_worstCost]
    exact hmat
  · rw [← hrep, encodeProtocol_worstCost, hsrc]
  · intro x G b sol bv U ζ hG hreg hsol hUm hWp hL0 hL hMass hInt hTarget hB hB1 hB2
    obtain ⟨⟨h₁, h₂, h₃⟩, hTr, hHi, hMat, hSrc⟩ := hA x G b sol bv U ζ hG hreg hsol hUm hWp hL0
      hL hMass hInt hTarget hB hB1 hB2
    refine ⟨⟨?_, ?_, ?_⟩, trialsClose_encode hI tf x (sol T) ε hTr,
      historiesClose_encode hI tf x (sol T) ε hHi, ?_, ?_⟩
    · rw [← hrep, encodeProtocol_successMass]; exact h₁
    · rw [← hrep, encodeProtocol_conditionalDensity]; exact h₂
    · rw [← hrep, encodeProtocol_conditionalDensity]; exact h₃
    · rw [← hrep, encodeProtocol_worstCost]
      have hle : ((ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
          (fun l => wcostS l wMatS) : ℝ) ≤
          2 * ((ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
            GeneralSourceODE.Oracles.matrixCalls : ℝ) := by
        exact_mod_cast hmat
      linarith
    · rw [← hrep, encodeProtocol_worstCost, hsrc]
      exact hSrc

/-! ### Sources with temporary work registers -/

section Work

open GeneralSourceODE.Native (Label SourceBasis)

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s M m : ℕ}

/-- **The matrix calls of the actual oracles of the time-dependent solver from a time-indexed
writer** (any supplied source operations). -/
theorem fimplH_meshMatrix (D : Data (X × Fin M) n Z s)
    (W : X × Fin M → WReg n Z →L[ℂ] WReg n Z) (hWu : ∀ y, IsUnitary (W y))
    (c : X × Fin M → n × n → ℂ)
    (hW : ∀ y a, W y (EuclideanSpace.single (a, (0 : Z)) 1) =
      c y a • EuclideanSpace.single (a, D.table y a) 1)
    (N d : ℕ) (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    FImplH Z (fun l x => MeshOracles.actualOracle (ι := ι) D m N d Pw J (.inl l) x)
      (timeWriterOracles D W) wcost := by
  have h1 := (fimplH_flat D W hWu c hW).masked (B := NativeSparseMaskedAccess.Basis n Z)
    (ODENativeLayout.Branch Z)
  have h2 : FImplH Z (ODENativeCayley.oracle D) _ wcost :=
    h1.conj (FlatBranchNativeAccess.layout (ι := ODENativeLayout.Branch Z)
      (B := NativeSparseMaskedAccess.Basis n Z))
  have h3 : FImplH Z (TimeDependentODE.coherentOracle (ι := Label ι m) D)
      (timeWriterOracles D W) wcost :=
    (h2.label (TimeDependentODE.sample (ι := Label ι m) (M := M))).homOf
      (homOf_time (Label ι m) D W)
  have h4 : FImplH Z (TimeDependentODE.cayleyOracle (ι := Label ι m) D) _ wcost :=
    h3.conj (TimeDependentODE.layout (ι := Label ι m) (M := M) (n := n) (Z := Z))
  have h5 := h4.masked (B := TimeDependentODE.Basis (Label ι m) n Z M)
    (ActiveRegisterLayout.Label PUnit.{1} N d)
  have h6 : FImplH Z (MeshNative.matrixOracle (ι := ι) D m N d) _ wcost := h5.diag Bool
  have h7 := h6.conj (MeshNative.matrixLayout (ι := ι) (n := n) (Z := Z) m M N d)
  exact (h7.masked (B := MeshNative.MatrixBasis ι n Z m M N d) (SourceBasis ι n m)).congr
    (fun l x => rfl)

/-- **The actual oracles with a temporary work register from a time-indexed writer**: as
`fimplH_meshActual`, for `CleanWorkODE.actualOracleW` (the matrix calls with the work register a
spectator, the supplied operations on the label, data and work registers). -/
theorem fimplH_workActual (D : Data (X × Fin M) n Z s)
    (W : X × Fin M → WReg n Z →L[ℂ] WReg n Z) (hWu : ∀ y, IsUnitary (W y))
    (c : X × Fin M → n × n → ℂ)
    (hW : ∀ y a, W y (EuclideanSpace.single (a, (0 : Z)) 1) =
      c y a • EuclideanSpace.single (a, D.table y a) 1)
    (N d : ℕ) {Ws : Type*} [Fintype Ws] [DecidableEq Ws]
    {Pw : X → CleanWorkODE.LabelW m Ws →L[ℂ] CleanWorkODE.LabelW m Ws}
    (hPw : ∀ x, IsUnitary (Pw x))
    {J : X → CleanWorkODE.LoadW m n Ws →L[ℂ] CleanWorkODE.LoadW m n Ws}
    (hJ : ∀ x, IsUnitary (J x)) :
    ∃ (Ow : WQuery ⊕ GeneralSourceODE.SourceCall → X →
        PiLp 2 (fun _ : Z => CleanWorkODE.PhysW ι n Z Ws m M N d) →L[ℂ]
          PiLp 2 (fun _ : Z => CleanWorkODE.PhysW ι n Z Ws m M N d))
      (circ : Query ⊕ GeneralSourceODE.SourceCall → MultiOracleCircuit.Program Ow)
      (Φ : (PiLp 2 (fun _ : Fin M => Space n Z) →L[ℂ] PiLp 2 (fun _ : Fin M => Space n Z)) →⋆ₐ[ℂ]
        (PiLp 2 (fun _ : Z => CleanWorkODE.PhysW ι n Z Ws m M N d) →L[ℂ]
          PiLp 2 (fun _ : Z => CleanWorkODE.PhysW ι n Z Ws m M N d))),
      Impl (CleanWorkODE.actualOracleW (ι := ι) D m N d Pw J) Ow
        (single0 Z (CleanWorkODE.PhysW ι n Z Ws m M N d)) circ wcostS ∧
      (∀ q x, Ow (.inl q) x = Φ (timeWriterOracles D W q x)) ∧
      (∀ k x, Ow (.inr k) x = diagHom (K' := CleanWorkODE.PhysW ι n Z Ws m M N d) Z
        (CleanWorkODE.actualOracleW (ι := ι) D m N d Pw J (.inr k) x)) := by
  have h9 := ((fimplH_meshMatrix (ι := ι) D W hWu c hW N d (fun _ => 1) (fun _ _ => 1)).diag
    Ws).conj (CleanWorkODE.workSplit (A := SourceBasis ι n m) (W := Ws)
      (V := EuclideanSpace ℂ (NativeControlledOracle.Workspace
        (MeshNative.MatrixBasis ι n Z m M N d)))).symm
  obtain ⟨Ow, circ, Φ, hI0, hΦ, hU⟩ := h9.extra
    (fun k x => CleanWorkODE.actualOracleW (ι := ι) D m N d Pw J (.inr k) x)
    (fun k x => CleanWorkODE.actualOracleW_unitary (ι := ι) D m N d hPw hJ (.inr k) x)
  exact ⟨Ow, circ, Φ, hI0.congr (fun l x => by cases l <;> rfl), hΦ, hU⟩

end Work

/-- **Theorem `ode:thm:time` for approximate source preparations with temporary work registers,
with a time-indexed writer.** The hypotheses of `ode_thm_time_approx` and a time-indexed writer as
in `ode_thm_time_writer`: the protocol of `ode_thm_time_approx` converted has its success mass and
conditional output on every instance, at most twice its worst-case matrix calls and the same source
calls; under the instance conditions (the clean-input errors of the supplied preparations included):
`HeraldedOutput` and the doubled budget. -/
theorem ode_thm_time_approx_writer :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s M : ℕ} (D : Data (X × Fin M) n Z s), 0 < M →
        ∀ (Wr : X × Fin M → WReg n Z →L[ℂ] WReg n Z) (cw : X × Fin M → n × n → ℂ),
        (∀ y, IsUnitary (Wr y)) →
        (∀ y a, Wr y (EuclideanSpace.single (a, (0 : Z)) 1) =
          cw y a • EuclideanSpace.single (a, D.table y a) 1) →
        ∀ (t : ℕ → ℝ) (N : ℕ), 0 < N →
        ∀ (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ),
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 1 ≤ gbar → 1 ≤ cq → 0 < ε → ε ≤ 1 →
        TimeDependentExtensions.IsMesh t M T →
        8 * s * ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T) ≤ N →
        3 * (Real.sqrt (2 * (s : ℝ)) *
          ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
          TimeDependentODE.precision (cq * gbar) ε * (N : ℝ) ^ 2 →
        (∀ i, v i ∈ Icc 0 T) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        ∀ {W : Type} [Fintype W] [DecidableEq W] (w₀ : W)
          (Pw : X → CleanWorkODE.LabelW m W →L[ℂ] CleanWorkODE.LabelW m W),
        (∀ x, IsUnitary (Pw x)) →
        ∀ (J : X → CleanWorkODE.LoadW m n W →L[ℂ] CleanWorkODE.LoadW m n W),
        (∀ x, IsUnitary (J x)) →
        ∀ seed : EuclideanSpace ℂ n, ‖seed‖ = 1 →
        ∃ (d : ℕ) (A : ODERepeatProtocol.Protocol
            (CleanWorkODE.actualOracleW (ι := TimeDependentODE.Index D T (cq * gbar) ε) D m N d
              Pw J)
            (EuclideanSpace ℂ n))
          (Ow : WQuery ⊕ GeneralSourceODE.SourceCall → X →
            PiLp 2 (fun _ : Z => CleanWorkODE.PhysW (TimeDependentODE.Index D T (cq * gbar) ε)
              n Z W m M N d) →L[ℂ]
            PiLp 2 (fun _ : Z => CleanWorkODE.PhysW (TimeDependentODE.Index D T (cq * gbar) ε)
              n Z W m M N d))
          (Φ : (PiLp 2 (fun _ : Fin M => WriterAccess.Space n Z) →L[ℂ]
              PiLp 2 (fun _ : Fin M => WriterAccess.Space n Z)) →⋆ₐ[ℂ]
            (PiLp 2 (fun _ : Z => CleanWorkODE.PhysW (TimeDependentODE.Index D T (cq * gbar) ε)
              n Z W m M N d) →L[ℂ]
            PiLp 2 (fun _ : Z => CleanWorkODE.PhysW (TimeDependentODE.Index D T (cq * gbar) ε)
              n Z W m M N d)))
          (_ : ∀ q x, Ow (.inl q) x = Φ (timeWriterOracles D Wr q x))
          (_ : ∀ k x, Ow (.inr k) x = diagHom (K' := CleanWorkODE.PhysW
              (TimeDependentODE.Index D T (cq * gbar) ε) n Z W m M N d) Z
            (CleanWorkODE.actualOracleW (ι := TimeDependentODE.Index D T (cq * gbar) ε) D m N d
              Pw J (.inr k) x))
          (A' : ODERepeatProtocol.Protocol Ow (EuclideanSpace ℂ n)),
          (∀ x, A'.successMass x = A.successMass x ∧
            A'.conditionalDensity x = A.conditionalDensity x) ∧
          A'.worstCost wMatS ≤ 2 * A.worstCost GeneralSourceODE.Oracles.matrixCalls ∧
          A'.worstCost wSrcS = A.worstCost GeneralSourceODE.Oracles.sourceCalls ∧
          ∀ (x : X) (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
            (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (δ : ℝ)
            (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
            (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
            (bv : Fin m → EuclideanSpace ℂ n)
            (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
            IsUnitary P → (∀ a, IsUnitary (L a)) → 0 ≤ δ →
            cleanInputError w₀ (Pw x) P δ →
            cleanInputError w₀ (J x) (CleanWorkODE.ctrlL L) δ →
            60 * (cq * gbar) * δ ≤ 1 / 400 → 60 * (cq * gbar) * δ ≤ ε / 20 →
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces t G →
            RepresentedSampleODE.MildSolution t T b sol U →
            formal_classicalPropagator G t T U →
            GeneralSourceODE.Compiled.WeightPrep P (GeneralSourceODE.sources (sol 0) bv ω) →
            (sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0)) →
            (∀ i, ω i ≠ 0 → bv i ≠ 0 →
              L (some i) seed = ODEStateNormalization.unitDirection (bv i)) →
            ODESourceBranches.mass (GeneralSourceODE.sources (sol 0) bv ω) ≤
              cq * Mesh.meshScale sol b t →
            ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
                ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * Mesh.meshScale sol b t →
            sol T ≠ 0 →
            Mesh.meshScale sol b t ≤ gbar * ‖sol T‖ →
            ζ + cq * (Mesh.sampleError D x t G + 2 * RepresentedSampleODE.dissipativeError D x t G +
                2 * Mesh.refinementError D t T N) ≤ ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (cq * gbar) ε *
                (RepresentedSampleODE.dissipativeError D x t G + Mesh.refinementError D t T N) ≤
              TimeDependentODE.precision (cq * gbar) ε →
            HeraldedOutput A' x (ODEStateNormalization.unitDirection (sol T)) ε ∧
            (A'.worstCost wMatS : ℝ) ≤
              2 * (C * (cq * gbar) * (Real.sqrt s * (T * etaH + T * etaD *
                  Real.log (40000 * cq * gbar / ε)) +
                Real.sqrt (s * (T * etaH + T * etaD * Real.log (40000 * cq * gbar / ε)) *
                  Real.log (40000 * cq * gbar / ε)) + Real.log (40000 * cq * gbar / ε))) ∧
            (A'.worstCost wSrcS : ℝ) ≤ C * (cq * gbar) := by
  obtain ⟨C, hC, hode⟩ := ode_thm_time_approx.{u, v, w}
  refine ⟨C, hC, ?_⟩
  intro X n Z _ _ _ _ _ s M D hM Wr cw hWu hWr t N hN etaH etaD T gbar cq ε m v ω hH hDiss hT hg
    hcq hε hεOne hmesh hClock hCayley hv hrH hcH hrD hcD W _ _ w₀ Pw hPw J hJ seed hSeed
  obtain ⟨d, A, hA⟩ := hode D hM t N hN etaH etaD T gbar cq ε v ω hH hDiss hT hg hcq hε hεOne
    hmesh hClock hCayley hv hrH hcH hrD hcD w₀ Pw hPw J hJ seed hSeed
  obtain ⟨Ow, circ, Φ, hI, hΦ, hU⟩ := fimplH_workActual
    (ι := TimeDependentODE.Index D T (cq * gbar) ε) D Wr hWu cw hWr N d hPw hJ
  have hsrc : (fun l => wcostS l wSrcS) = GeneralSourceODE.Oracles.sourceCalls :=
    funext wcostS_wSrc
  have hmat : A.worstCost (fun l => wcostS l wMatS) ≤
      2 * A.worstCost GeneralSourceODE.Oracles.matrixCalls :=
    protocol_worstCost_le_mul A (w₁ := fun l => wcostS l wMatS)
      (w₂ := GeneralSourceODE.Oracles.matrixCalls) (k := 2) wcostS_wMat_le
  refine ⟨d, A, Ow, Φ, hΦ, hU, encodeProtocol hI A,
    fun x => ⟨encodeProtocol_successMass hI A x, encodeProtocol_conditionalDensity hI A x⟩, ?_, ?_,
    ?_⟩
  · rw [encodeProtocol_worstCost]
    exact hmat
  · rw [encodeProtocol_worstCost, hsrc]
  · intro x P L δ G b sol bv U ζ hP hL hδ hPc hJc hδ1 hδε hG hreg hsol hUm hWp hL0 hL' hMass hInt
      hTarget hB hB1 hB2
    obtain ⟨⟨h₁, h₂, h₃⟩, hMat, hSrc⟩ := hA x P L δ G b sol bv U ζ hP hL hδ hPc hJc hδ1 hδε hG
      hreg hsol hUm hWp hL0 hL' hMass hInt hTarget hB hB1 hB2
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [encodeProtocol_successMass]; exact h₁
    · rw [encodeProtocol_conditionalDensity]; exact h₂
    · rw [encodeProtocol_conditionalDensity]; exact h₃
    · rw [encodeProtocol_worstCost]
      have hle : (A.worstCost (fun l => wcostS l wMatS) : ℝ) ≤
          2 * (A.worstCost GeneralSourceODE.Oracles.matrixCalls : ℝ) := by
        exact_mod_cast hmat
      linarith
    · rw [encodeProtocol_worstCost, hsrc]
      exact hSrc

end

end ManuscriptConformance
