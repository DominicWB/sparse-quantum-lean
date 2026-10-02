import SparseHamiltonian.CleanChronologicalEmbedding

namespace SparseHamiltonian.NativeWholeProgramActive

noncomputable section
open ContinuousLinearMap OracleCircuit ReuseLayerFactorization NativeMaskedOracle
open scoped InnerProduct
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

variable {C B X L : Type*} [Fintype C] [Fintype B] [DecidableEq B]
  (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The common clean encoding for an arbitrary logical private system. -/
def cleanInput (eP : P →ₗᵢ[ℂ] EuclideanSpace ℂ B)
    (eV : V →ₗᵢ[ℂ] Logical C B) (a : B) (T d : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := ChronologicalResolvent.BlockOperator.H T V) d) →ₗᵢ[ℂ]
      Physical (ActiveRegisterLayout.Label C T d) B :=
  (input (C := C) a T d).comp (CleanChronologicalEmbedding.embedding eP eV T d)

omit [CompleteSpace P] [CompleteSpace V] in
/-- A source program's exact clean action discharges the active-layer
implementation premise without introducing any controlled native oracle. -/
theorem program_clean_intertwines (hF : ∀ l x, IsUnitary (F l x)) (a : B)
    (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) =
      EuclideanSpace.single (image l x) 1)
    (p : MultiOracleCircuit.Program F)
    (eP : P →ₗᵢ[ℂ] EuclideanSpace ℂ B) (eV : V →ₗᵢ[ℂ] Logical C B)
    (D : X → V →L[ℂ] V)
    (hClean : ∀ x, WeightedClock.diagonal (fun _ : C => p.eval x) ∘L
      eV.toContinuousLinearMap = eV.toContinuousLinearMap ∘L D x)
    (T d r : ℕ) (x : X) :
    (program (C := C) F a p T d r).eval x ∘L
        (cleanInput eP eV a T d).toContinuousLinearMap =
      (cleanInput eP eV a T d).toContinuousLinearMap ∘L
        activeClock (P := P) (D x) T d r := by
  change (program (C := C) F a p T d r).eval x ∘L
      ((input (C := C) a T d).toContinuousLinearMap ∘L
        (CleanChronologicalEmbedding.embedding eP eV T d).toContinuousLinearMap) =
    ((input (C := C) a T d).toContinuousLinearMap ∘L
      (CleanChronologicalEmbedding.embedding eP eV T d).toContinuousLinearMap) ∘L _
  rw [← comp_assoc, program_intertwines F hF a image hvalid, comp_assoc,
    CleanChronologicalEmbedding.active_intertwines eP eV _ _ (hClean x), comp_assoc]

omit [CompleteSpace P] [CompleteSpace V] in
/-- A literal primitive program and one fixed encoding certify each complete
active Cayley layer at exactly three times the source program's query count. -/
theorem clean_implementsOn (hF : ∀ l x, IsUnitary (F l x)) (a : B)
    (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) =
      EuclideanSpace.single (image l x) 1)
    (p : MultiOracleCircuit.Program F)
    (eP : P →ₗᵢ[ℂ] EuclideanSpace ℂ B) (eV : V →ₗᵢ[ℂ] Logical C B)
    (D : X → V →L[ℂ] V)
    (hClean : ∀ x, WeightedClock.diagonal (fun _ : C => p.eval x) ∘L
      eV.toContinuousLinearMap = eV.toContinuousLinearMap ∘L D x)
    (T d r : ℕ) :
    LabeledEncodedOracle.ImplementsOn (oracle (C := C) F T d)
      (fun x => activeClock (P := P) (D x) T d r)
      (cleanInput eP eV a T d).toContinuousLinearMap (3 * p.count) :=
  ⟨program F a p T d r,
    program_clean_intertwines F hF a image hvalid p eP eV D hClean T d r,
    (program_count F a p T d r).le⟩

end
end SparseHamiltonian.NativeWholeProgramActive
