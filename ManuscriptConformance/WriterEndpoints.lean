import ManuscriptConformance.WriterProtocols
import ManuscriptConformance.Hamiltonian

/-!
# The Hamiltonian query endpoints with a writer value oracle (handover item B4)

`hs_thm_main_writer`, `hs_thm_optimal_writer` and `hs_thm_two_norm_writer` restate
Theorems `hs:thm:main`, `hs:thm:optimal` and `hs:thm:two-norm` for value access by a reversible
writer specified only on a clean target (`WriterAccess`): the released circuit of each theorem,
with every value call replaced by writer, adder and inverse writer on one extra clean scratch
register, and every locator call by the same locator call with the scratch register a spectator.
The converted circuit is fixed before the instance, makes exactly the locator calls of the released
circuit and two writer calls per value call (at most twice its calls), acts as the released circuit
on the clean scratch register, and has the same full-output error, also with an untouched
reference. The converted workspace is the released workspace with one more register holding a
value word (`single0`: the scratch register in its zero word); every physical call is a primitive
call (a locator, or the writer) under one fixed unital star-algebra homomorphism `Φ` (spectator
registers).
-/

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.WriterAccess NativeSparseBlockEncoding
  OracleCircuit
open scoped InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 4000000

universe u v w

/-- **The conversion of a released program.** For an implementation of the physical family by the
writer family on a fixed encoding, every program over the physical family becomes a program over
the writer family with the same locator calls, two writer calls per value call, the same action on
the encoding, and the same full-output errors on the encoded input. -/
theorem writer_convert {K K' : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K'] {X : Type*}
    {O : Query → X → K →L[ℂ] K} {Ow : WQuery → X → K' →L[ℂ] K'} {E : K →L[ℂ] K'}
    {circ : Query → MultiOracleCircuit.Program Ow} (h : Impl O Ow E circ wcost)
    (q : MultiOracleCircuit.Program O) {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℂ P] (J : P →L[ℂ] K) (V : X → P →L[ℂ] P) (ε : ℝ)
    (hq : ∀ x, IsUnitary (q.eval x) ∧ FullOutputError (q.eval x) J (V x) ε ∧
      ∀ (R : Type) [Fintype R], ReferenceOutputError R (q.eval x) J (V x) ε) :
    ∃ p : MultiOracleCircuit.Program Ow,
      (∀ x, p.eval x ∘L E = E ∘L q.eval x) ∧
      p.labelCount .row = q.labelCount .rowLocation ∧
      p.labelCount .column = q.labelCount .columnLocation ∧
      p.labelCount .writer = 2 * q.labelCount .value ∧
      p.count ≤ 2 * q.count ∧
      ∀ x, IsUnitary (p.eval x) ∧ FullOutputError (p.eval x) (E ∘L J) (V x) ε ∧
        ∀ (R : Type) [Fintype R], ReferenceOutputError R (p.eval x) (E ∘L J) (V x) ε := by
  obtain ⟨hcost, heval, hunit⟩ := transfer h q
  refine ⟨EncodedLabeledProgram.compile E h.iso circ q, heval, ?_, ?_, ?_, ?_, fun x =>
    ⟨hunit x, fullOutputError_encode h.iso (heval x) (hq x).2.1,
      fun R _ => referenceOutputError_encode R h.iso (heval x) ((hq x).2.2 R)⟩⟩
  · rw [MultiOracleCircuit.Program.labelCount, hcost, cost_wcost]
    simp
  · rw [MultiOracleCircuit.Program.labelCount, hcost, cost_wcost]
    simp
  · rw [MultiOracleCircuit.Program.labelCount, hcost, cost_wcost]
    simp
  · have h1 := hcost (fun _ => 1)
    rw [MultiOracleCircuit.Program.cost_const, Nat.mul_one] at h1
    rw [h1]
    exact cost_wcost_one_le q

/-- **Theorem `hs:thm:main` with a writer value oracle.** The hypotheses of `hs_thm_main`, and a
supplied unitary writer `W x` on the address and target registers with
`W x |a, 0⟩ = c x a |a, w_a⟩` for the stored word `w_a = D.table x a` and any phases `c x a`: the
circuit of `hs_thm_main` with each value call replaced by writer, adder and inverse writer on a
clean scratch register is fixed before the instance, makes the locator calls of the released
circuit and two writer calls per value call (at most `2 C` times the bound), acts as the released
circuit on the clean scratch register, and has full-output error at most `ε`, also with an
untouched reference. -/
theorem hs_thm_main_writer :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (D : Data X n Z s)
        (W : X → WReg n Z →L[ℂ] WReg n Z) (c : X → n × n → ℂ),
        (∀ x, IsUnitary (W x)) →
        (∀ x a, W x (EuclideanSpace.single (a, (0 : Z)) 1) =
          c x a • EuclideanSpace.single (a, D.table x a) 1) →
        ∀ (η t ε : ℝ), 0 < η → 0 < ε → ε ≤ 1 / 2 →
        (∀ x, (D.matrix x).IsHermitian) →
        (∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
        (∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
        ∃ (γ : ℝ) (q : MultiOracleCircuit.Program (ImprovedSparseHamiltonian.oracle D γ η t ε))
          (Ow : WQuery → X →
            PiLp 2 (fun _ : Z => ImprovedSparseHamiltonian.Physical n Z s γ η t ε) →L[ℂ]
              PiLp 2 (fun _ : Z => ImprovedSparseHamiltonian.Physical n Z s γ η t ε))
          (Φ : (WriterAccess.Space n Z →L[ℂ] WriterAccess.Space n Z) →⋆ₐ[ℂ]
            (PiLp 2 (fun _ : Z => ImprovedSparseHamiltonian.Physical n Z s γ η t ε) →L[ℂ]
              PiLp 2 (fun _ : Z => ImprovedSparseHamiltonian.Physical n Z s γ η t ε)))
          (_ : ∀ m x, Ow m x = Φ (writerOracles D W m x))
          (p : MultiOracleCircuit.Program Ow),
          (q.count : ℝ) ≤ C * mainBound s (η * |t|) ε ∧
          (∀ x, p.eval x ∘L single0 Z _ = single0 Z _ ∘L q.eval x) ∧
          p.labelCount .row = q.labelCount .rowLocation ∧
          p.labelCount .column = q.labelCount .columnLocation ∧
          p.labelCount .writer = 2 * q.labelCount .value ∧
          (p.count : ℝ) ≤ 2 * C * mainBound s (η * |t|) ε ∧
          (single0 Z _ ∘L ImprovedSparseHamiltonian.input D γ η t ε)† ∘L
            (single0 Z _ ∘L ImprovedSparseHamiltonian.input D γ η t ε) = 1 ∧
          ∀ x, IsUnitary (p.eval x) ∧
            FullOutputError (p.eval x) (single0 Z _ ∘L ImprovedSparseHamiltonian.input D γ η t ε)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                SparseStateOverlap.matrixOperator (D.matrix x))) ε ∧
            ∀ (R : Type) [Fintype R], ReferenceOutputError R (p.eval x)
              (single0 Z _ ∘L ImprovedSparseHamiltonian.input D γ η t ε)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                SparseStateOverlap.matrixOperator (D.matrix x))) ε := by
  obtain ⟨C, hC, hmain⟩ := hs_thm_main.{u, v, w}
  refine ⟨C, hC, ?_⟩
  intro X n Z _ _ _ _ _ s D W c hWu hW η t ε hη hε hε2 hH hrow hcol
  obtain ⟨γ, q, hcount, hin, hq⟩ := hmain D η t ε hη hε hε2 hH hrow hcol
  have h1 := (fimplH_flat D W hWu c hW).masked (B := NativeSparseMaskedAccess.Basis n Z) Bool
  have h2 : FImplH Z (NativeCayleyProgram.oracle D) _ wcost :=
    h1.conj (NativeDilationLayout.layout (B := NativeSparseMaskedAccess.Basis n Z))
  have h3 : FImplH Z (NativeCayleyActive.oracle D
      (ImprovedNativeSimulation.slots (s : ℝ) γ (η * |t|) ε)
      (ImprovedNativeSimulation.degree (s : ℝ) γ (η * |t|) ε)) _ wcost :=
    h2.masked (B := NativeCayleyProgram.Basis n Z) (ActiveRegisterLayout.Label PUnit.{1}
      (ImprovedNativeSimulation.slots (s : ℝ) γ (η * |t|) ε)
      (ImprovedNativeSimulation.degree (s : ℝ) γ (η * |t|) ε))
  have h4 : FImplH Z (ImprovedSparseHamiltonian.oracle D γ η t ε) _ wcost := h3.diag Bool
  obtain ⟨Ow, circ, hI, Φ, hΦ⟩ := h4
  obtain ⟨p, hpE, hrowc, hcolc, hwr, hpc, hp⟩ :=
    writer_convert hI q (ImprovedSparseHamiltonian.input D γ η t ε)
      (fun x => NormedSpace.exp ((-Complex.I * (t : ℂ)) •
        SparseStateOverlap.matrixOperator (D.matrix x))) ε hq
  refine ⟨γ, q, Ow, Φ, hΦ, p, hcount, hpE, hrowc, hcolc, hwr, ?_,
    encode_isometry hI hin, hp⟩
  have h2 : (p.count : ℝ) ≤ 2 * q.count := by exact_mod_cast hpc
  nlinarith

/-- **Theorem `hs:thm:optimal` with a writer value oracle**: the circuit of `hs_thm_optimal` with
each value call replaced by writer, adder and inverse writer on a clean scratch register, as in
`hs_thm_main_writer`. -/
theorem hs_thm_optimal_writer :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
        [DecidableEq Z] {s : ℕ} (D : Data X n Z s)
        (W : X → WReg n Z →L[ℂ] WReg n Z) (c : X → n × n → ℂ),
        (∀ x, IsUnitary (W x)) →
        (∀ x a, W x (EuclideanSpace.single (a, (0 : Z)) 1) =
          c x a • EuclideanSpace.single (a, D.table x a) 1) →
        ∀ (η t ε : ℝ), 1 ≤ η * |t| → 0 < ε → ε ≤ 1 / 64 →
        (∀ x, (D.matrix x).IsHermitian) →
        (∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
        (∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
        ∃ (ι : Type) (_ : Fintype ι)
          (J : EuclideanSpace ℂ n →L[ℂ] PiLp 2 (fun _ : ι => NativeSignedFactor.Phys n Z))
          (q : MultiOracleCircuit.Program
            (CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle D)))
          (Ow : WQuery → X →
            PiLp 2 (fun _ : Z => PiLp 2 (fun _ : ι => NativeSignedFactor.Phys n Z)) →L[ℂ]
              PiLp 2 (fun _ : Z => PiLp 2 (fun _ : ι => NativeSignedFactor.Phys n Z)))
          (Φ : (WriterAccess.Space n Z →L[ℂ] WriterAccess.Space n Z) →⋆ₐ[ℂ]
            (PiLp 2 (fun _ : Z => PiLp 2 (fun _ : ι => NativeSignedFactor.Phys n Z)) →L[ℂ]
              PiLp 2 (fun _ : Z => PiLp 2 (fun _ : ι => NativeSignedFactor.Phys n Z))))
          (_ : ∀ m x, Ow m x = Φ (writerOracles D W m x))
          (p : MultiOracleCircuit.Program Ow),
          J† ∘L J = 1 ∧ (q.count : ℝ) ≤ C * optimalBound s (η * |t|) ε ∧
          (∀ x, p.eval x ∘L single0 Z _ = single0 Z _ ∘L q.eval x) ∧
          p.labelCount .row = q.labelCount .rowLocation ∧
          p.labelCount .column = q.labelCount .columnLocation ∧
          p.labelCount .writer = 2 * q.labelCount .value ∧
          (p.count : ℝ) ≤ 2 * C * optimalBound s (η * |t|) ε ∧
          (single0 Z _ ∘L J)† ∘L (single0 Z _ ∘L J) = 1 ∧
          ∀ x, IsUnitary (p.eval x) ∧
            FullOutputError (p.eval x) (single0 Z _ ∘L J) (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))) ε ∧
            ∀ (R : Type) [Fintype R], ReferenceOutputError R (p.eval x) (single0 Z _ ∘L J)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                SparseStateOverlap.matrixOperator (D.matrix x))) ε := by
  obtain ⟨C, hC, hopt⟩ := hs_thm_optimal.{u}
  refine ⟨C, hC, ?_⟩
  intro X n Z _ _ _ _ _ s D W c hWu hW η t ε hτ hε hε1 hH hrow hcol
  obtain ⟨ι, hι, J, q, hJ, hcount, hq⟩ := hopt D η t ε hτ hε hε1 hH hrow hcol
  have h1 : FImplH Z (NativeSignedFactor.physOracle D) _ wcost :=
    (fimplH_flat D W hWu c hW).masked (B := NativeSparseMaskedAccess.Basis n Z) Bool
  have h2 : FImplH Z (CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle D))
      _ wcost := h1.diag ι
  obtain ⟨Ow, circ, hI, Φ, hΦ⟩ := h2
  obtain ⟨p, hpE, hrowc, hcolc, hwr, hpc, hp⟩ :=
    writer_convert hI q J (fun x => NormedSpace.exp ((-Complex.I * (t : ℂ)) •
        SparseStateOverlap.matrixOperator (D.matrix x))) ε hq
  refine ⟨ι, hι, J, q, Ow, Φ, hΦ, p, hJ, hcount, hpE, hrowc, hcolc, hwr, ?_,
    encode_isometry hI hJ, hp⟩
  have h2 : (p.count : ℝ) ≤ 2 * q.count := by exact_mod_cast hpc
  nlinarith

/-- **Theorem `hs:thm:two-norm` with a writer value oracle**: the circuit of `hs_thm_two_norm` with
each value call replaced by writer, adder and inverse writer on a clean scratch register, as in
`hs_thm_main_writer`. -/
theorem hs_thm_two_norm_writer :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
        [DecidableEq Z] {s : ℕ} (D : Data X n Z s)
        (W : X → WReg n Z →L[ℂ] WReg n Z) (c : X → n × n → ℂ),
        (∀ x, IsUnitary (W x)) →
        (∀ x a, W x (EuclideanSpace.single (a, (0 : Z)) 1) =
          c x a • EuclideanSpace.single (a, D.table x a) 1) →
        ∀ (η μ t ε : ℝ),
        μ ≤ η → η ≤ Real.sqrt s * μ → 1 ≤ η ^ 2 * |t| / μ → 0 < ε → ε ≤ 1 / 64 →
        (∀ x, (D.matrix x).IsHermitian) →
        (∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
        (∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
        (∀ x i j, ‖D.matrix x i j‖ ≤ μ) →
        ∃ (ι : Type) (_ : Fintype ι)
          (J : EuclideanSpace ℂ n →L[ℂ] PiLp 2 (fun _ : ι => NativeSignedFactor.Phys n Z))
          (q : MultiOracleCircuit.Program
            (CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle D)))
          (Ow : WQuery → X →
            PiLp 2 (fun _ : Z => PiLp 2 (fun _ : ι => NativeSignedFactor.Phys n Z)) →L[ℂ]
              PiLp 2 (fun _ : Z => PiLp 2 (fun _ : ι => NativeSignedFactor.Phys n Z)))
          (Φ : (WriterAccess.Space n Z →L[ℂ] WriterAccess.Space n Z) →⋆ₐ[ℂ]
            (PiLp 2 (fun _ : Z => PiLp 2 (fun _ : ι => NativeSignedFactor.Phys n Z)) →L[ℂ]
              PiLp 2 (fun _ : Z => PiLp 2 (fun _ : ι => NativeSignedFactor.Phys n Z))))
          (_ : ∀ m x, Ow m x = Φ (writerOracles D W m x))
          (p : MultiOracleCircuit.Program Ow),
          J† ∘L J = 1 ∧ (q.count : ℝ) ≤ C * twoNormBound s η μ t ε ∧
          (∀ x, p.eval x ∘L single0 Z _ = single0 Z _ ∘L q.eval x) ∧
          p.labelCount .row = q.labelCount .rowLocation ∧
          p.labelCount .column = q.labelCount .columnLocation ∧
          p.labelCount .writer = 2 * q.labelCount .value ∧
          (p.count : ℝ) ≤ 2 * C * twoNormBound s η μ t ε ∧
          (single0 Z _ ∘L J)† ∘L (single0 Z _ ∘L J) = 1 ∧
          ∀ x, IsUnitary (p.eval x) ∧
            FullOutputError (p.eval x) (single0 Z _ ∘L J) (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))) ε ∧
            ∀ (R : Type) [Fintype R], ReferenceOutputError R (p.eval x) (single0 Z _ ∘L J)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                SparseStateOverlap.matrixOperator (D.matrix x))) ε := by
  obtain ⟨C, hC, htwo⟩ := hs_thm_two_norm.{u}
  refine ⟨C, hC, ?_⟩
  intro X n Z _ _ _ _ _ s D W c hWu hW η μ t ε hμη hηs hθ hε hε1 hH hrow hcol hent
  obtain ⟨ι, hι, J, q, hJ, hcount, hq⟩ := htwo D η μ t ε hμη hηs hθ hε hε1 hH hrow hcol hent
  have h1 : FImplH Z (NativeSignedFactor.physOracle D) _ wcost :=
    (fimplH_flat D W hWu c hW).masked (B := NativeSparseMaskedAccess.Basis n Z) Bool
  have h2 : FImplH Z (CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle D))
      _ wcost := h1.diag ι
  obtain ⟨Ow, circ, hI, Φ, hΦ⟩ := h2
  obtain ⟨p, hpE, hrowc, hcolc, hwr, hpc, hp⟩ :=
    writer_convert hI q J (fun x => NormedSpace.exp ((-Complex.I * (t : ℂ)) •
        SparseStateOverlap.matrixOperator (D.matrix x))) ε hq
  refine ⟨ι, hι, J, q, Ow, Φ, hΦ, p, hJ, hcount, hpE, hrowc, hcolc, hwr, ?_,
    encode_isometry hI hJ, hp⟩
  have h2 : (p.count : ℝ) ≤ 2 * q.count := by exact_mod_cast hpc
  nlinarith

end
end ManuscriptConformance
