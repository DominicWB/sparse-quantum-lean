import SparseODE.CommonQueryShape

/-!
# Structural shape lemmas for the native compiler stack

These lemmas erase one syntax constructor at a time. They avoid asking the
kernel to normalize a complete native circuit and all of its fixed gates.
-/

namespace SparseHamiltonian.CommonQueryShape

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

namespace Shape

/-- Reverse query directions and composition order, ignoring gate matrices. -/
def adjoint {L : Type*} : Shape L → Shape L
  | .fixed => .fixed
  | .query l => .queryAdjoint l
  | .queryAdjoint l => .query l
  | .seq p q => .seq (adjoint q) (adjoint p)

/-- Substitute the shape of each physically implemented query letter. -/
def substitute {L M : Type*} (letters : L → Shape M) : Shape L → Shape M
  | .fixed => .fixed
  | .query l => letters l
  | .queryAdjoint l => (letters l).adjoint
  | .seq p q => .seq (substitute letters p) (substitute letters q)

end Shape

section Programs

variable {P K X L M : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {O : L → X → P →L[ℂ] P}

theorem erase_adjoint (p : MultiOracleCircuit.Program O) :
    erase p.adjoint = (erase p).adjoint := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
    simp only [MultiOracleCircuit.Program.adjoint, erase, Shape.adjoint, hp, hq]

theorem erase_transport (e : P ≃ₗᵢ[ℂ] K) (p : MultiOracleCircuit.Program O) :
    erase (p.transport e) = erase p := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
    simp only [MultiOracleCircuit.Program.transport, erase, hp, hq]

theorem erase_labeled_compile {F : M → X → K →L[ℂ] K}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (circuits : L → MultiOracleCircuit.Program F)
    (p : MultiOracleCircuit.Program O) :
    erase (EncodedLabeledProgram.compile E hE circuits p) =
      Shape.substitute (fun l => erase (circuits l)) (erase p) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => exact erase_adjoint (circuits l)
  | seq p q hp hq =>
    simp only [EncodedLabeledProgram.compile, erase, Shape.substitute, hp, hq]

theorem erase_maskedProgram {ι : Type*} [Fintype ι] (active : ι → Bool)
    (p : MultiOracleCircuit.Program O) :
    erase (NativeHermitianDilation.maskedProgram active p) = erase p := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
    simp only [NativeHermitianDilation.maskedProgram, erase, hp, hq]

theorem native_clean_conjugation_shape_eq
    (pF p q : MultiOracleCircuit.Program O) (h : erase p = erase q) :
    erase (NativeCleanConjugation.program pF p) =
      erase (NativeCleanConjugation.program pF q) := by
  simp only [NativeCleanConjugation.program, erase, h]

end Programs

section Native

variable {ι B X L M : Type*} [Fintype ι] [Fintype B] [DecidableEq B]

/-- A common logical syntax remains common after native controlled-query
compilation. The letter programs are retained as opaque arguments. -/
theorem native_masked_compile_shape_eq
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (label : M → L) (active : M → ι → Bool)
    (p q : MultiOracleCircuit.Program (NativeMaskedProgram.logicalOracle F label active))
    (h : erase p = erase q) :
    erase (NativeMaskedProgram.compile F a label active p) =
      erase (NativeMaskedProgram.compile F a label active q) := by
  simpa only [NativeMaskedProgram.compile, erase_labeled_compile] using
    congrArg (Shape.substitute
      (fun m => erase (NativeMaskedProgram.letter F a label active m))) h

omit [DecidableEq B] in
theorem flatten_shape_eq
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (p q : MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := ι) F))
    (h : erase p = erase q) :
    erase (FlatBranchNativeAccess.flatten F p) =
      erase (FlatBranchNativeAccess.flatten F q) := by
  simpa only [FlatBranchNativeAccess.flatten, erase_transport] using h

end Native

section Active

variable {C B X L : Type*} [Fintype C] [Fintype B] [DecidableEq B]

theorem whole_active_shape_eq
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (p q : MultiOracleCircuit.Program F) (T d r : ℕ)
    (h : erase p = erase q) :
    erase (NativeWholeProgramActive.program (C := C) F a p T d r) =
      erase (NativeWholeProgramActive.program (C := C) F a q T d r) := by
  unfold NativeWholeProgramActive.program NativeWholeProgramMask.program
  exact native_masked_compile_shape_eq
    (ι := ActiveRegisterLayout.Label C T d) (M := L)
    F a (id : L → L)
    (fun _ : L => NativeWholeProgramActive.active (C := C) T d r)
    (NativeHermitianDilation.maskedProgram
      (NativeWholeProgramActive.active (C := C) T d r) p)
    (NativeHermitianDilation.maskedProgram
      (NativeWholeProgramActive.active (C := C) T d r) q)
    ((erase_maskedProgram (O := F)
      (NativeWholeProgramActive.active (C := C) T d r) p).trans
        (h.trans (erase_maskedProgram (O := F)
          (NativeWholeProgramActive.active (C := C) T d r) q).symm))

end Active

end
end SparseHamiltonian.CommonQueryShape
