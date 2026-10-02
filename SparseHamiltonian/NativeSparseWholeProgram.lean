import SparseHamiltonian.NativeCleanConjugation

namespace SparseHamiltonian.NativeSparseWholeProgram

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct

variable {C X n Z : Type*} [Fintype C] [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Every active layer of any actual native sparse program has a physical
implementation using exactly three times its primitive query count. The
original valid-slot promises discharge all native-control requirements. -/
theorem active_certificate (D : Data X n Z s)
    (p : MultiOracleCircuit.Program (NativeSparseMaskedAccess.flatOracle D))
    (T d : ℕ) :
    ∀ r,
      (NativeWholeProgramActive.program (C := C) (NativeSparseMaskedAccess.flatOracle D)
        (NativeSparseMaskedAccess.cleanBasis D) p T d r).count = 3 * p.count ∧
      ∀ x,
        (NativeWholeProgramActive.program (C := C) (NativeSparseMaskedAccess.flatOracle D)
          (NativeSparseMaskedAccess.cleanBasis D) p T d r).eval x ∘L
          (NativeWholeProgramActive.input (C := C)
            (NativeSparseMaskedAccess.cleanBasis D) T d).toContinuousLinearMap =
        (NativeWholeProgramActive.input (C := C)
          (NativeSparseMaskedAccess.cleanBasis D) T d).toContinuousLinearMap ∘L
          ReuseLayerFactorization.activeClock
            (P := EuclideanSpace ℂ (NativeSparseMaskedAccess.Basis n Z))
            (WeightedClock.diagonal (fun _ : C => p.eval x)) T d r := by
  intro r
  exact ⟨NativeWholeProgramActive.program_count _ _ p T d r,
    NativeWholeProgramActive.program_intertwines _
      (NativeSparseMaskedAccess.flatOracle_unitary D)
      (NativeSparseMaskedAccess.cleanBasis D) (NativeSparseMaskedAccess.image D)
      (NativeSparseMaskedAccess.valid D) p T d r⟩

end
end SparseHamiltonian.NativeSparseWholeProgram
