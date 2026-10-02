import SparseHamiltonian.DistributedSimulation

/-!
# One diagonal clock action in the complete chronological colligation

The clock appears only as an input factor in each local private column.
It therefore factors out of the entire chronological network as one diagonal
operator on the private time slots. The remaining coupling network does not
depend on the clock. These are exact operator identities; no sparse-oracle
query implementation or query cost is asserted here.
-/

namespace SparseHamiltonian.ChronologicalClockFactorization

noncomputable section
open scoped BigOperators InnerProduct
open ContinuousLinearMap ChronologicalResolvent ChronologicalCatalyst GlobalColligation

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace P] [CompleteSpace V] in
/-- A common clock factor exits each chronological block on its input side. -/
theorem chronologicalBlock_factor (R D₀ : V →L[ℂ] V) (A : P →L[ℂ] V)
    (u : P →L[ℂ] P) (B : V →L[ℂ] P) (r k : ℕ) :
    chronologicalBlock (R ∘L D₀) A u (B ∘L D₀) r k =
      chronologicalBlock R A u B r k ∘L D₀ := by
  unfold chronologicalBlock
  split
  · rfl
  · split
    · rfl
    · exact (zero_comp D₀).symm

omit [CompleteSpace P] [CompleteSpace V] in
/-- All private-slot clocks form a single diagonal input operation. -/
theorem chronologicalOperator_factor (R D₀ : V →L[ℂ] V) (A : P →L[ℂ] V)
    (u : P →L[ℂ] P) (B : V →L[ℂ] P) (T : ℕ) :
    chronologicalOperator (R ∘L D₀) A u (B ∘L D₀) T =
      chronologicalOperator R A u B T ∘L
        WeightedClock.diagonal (fun _ : Fin T => D₀) := by
  ext x i
  simp only [comp_apply, chronologicalOperator, BlockOperator.blocks_apply,
    WeightedClock.diagonal_apply, chronologicalBlock_factor]

omit [CompleteSpace P] [CompleteSpace V] in
/-- The public exit contains the same single diagonal input clock factor. -/
theorem publicExit_factor (D₀ : V →L[ℂ] V) (u : P →L[ℂ] P)
    (B : V →L[ℂ] P) (T : ℕ) :
    publicExit u (B ∘L D₀) T =
      publicExit u B T ∘L WeightedClock.diagonal (fun _ : Fin T => D₀) := by
  ext x
  simp only [publicExit, sum_apply, comp_apply, PiLp.proj_apply,
    WeightedClock.diagonal_apply]

/-- The parallel clock action leaves the public register unchanged. -/
def parallelClock (D₀ : V →L[ℂ] V) (T : ℕ) :
    WithLp 2 (P × BlockOperator.H T V) →L[ℂ] WithLp 2 (P × BlockOperator.H T V) :=
  blockMap 1 0 0 (WeightedClock.diagonal (fun _ : Fin T => D₀))

omit [CompleteSpace P] [CompleteSpace V] in
@[simp] theorem parallelClock_apply (D₀ : V →L[ℂ] V) (T : ℕ)
    (x : WithLp 2 (P × BlockOperator.H T V)) :
    parallelClock D₀ T x =
      WithLp.toLp 2 (x.fst, WeightedClock.diagonal (fun _ : Fin T => D₀) x.snd) := by
  simp [parallelClock, blockMap_apply]

omit [CompleteSpace P] [CompleteSpace V] in
/-- The full two-output chronology factors through just one parallel clock map. -/
theorem full_chronology_factor (R D₀ : V →L[ℂ] V) (A : P →L[ℂ] V)
    (u : P →L[ℂ] P) (B : V →L[ℂ] P) (T : ℕ) :
    blockMap (u ^ T) (publicExit u (B ∘L D₀) T) (stackedResponse A u T)
      (chronologicalOperator (R ∘L D₀) A u (B ∘L D₀) T) =
    blockMap (u ^ T) (publicExit u B T) (stackedResponse A u T)
      (chronologicalOperator R A u B T) ∘L parallelClock D₀ T := by
  rw [publicExit_factor, chronologicalOperator_factor]
  ext x
  simp only [comp_apply, blockMap_apply, parallelClock_apply, WithLp.fst, WithLp.snd]

/-- The clock-independent chronological coupling network. -/
def couplingNetwork (J : P →L[ℂ] V) (c κ σ : ℝ) (T : ℕ) :
    WithLp 2 (P × BlockOperator.H T V) →L[ℂ] WithLp 2 (P × BlockOperator.H T V) :=
  blockMap (((c : ℂ) • (1 : P →L[ℂ] P)) ^ T)
    (publicExit ((c : ℂ) • 1) ((-(σ : ℂ)) • J†) T)
    (stackedResponse ((σ : ℂ) • J) ((c : ℂ) • 1) T)
    (chronologicalOperator (1 - (κ : ℂ) • (J ∘L J†)) ((σ : ℂ) • J)
      ((c : ℂ) • 1) ((-(σ : ℂ)) • J†) T)

/-- The complete clock colligation with exactly the blocks used by the
chronological resolvent and catalyst constructions. -/
def clockColligation (D₀ : V →L[ℂ] V) (J : P →L[ℂ] V) (c κ σ : ℝ) (T : ℕ) :
    WithLp 2 (P × BlockOperator.H T V) →L[ℂ] WithLp 2 (P × BlockOperator.H T V) :=
  blockMap (((c : ℂ) • (1 : P →L[ℂ] P)) ^ T)
    (publicExit ((c : ℂ) • 1) ((-(σ : ℂ)) • (J† ∘L D₀)) T)
    (stackedResponse ((σ : ℂ) • J) ((c : ℂ) • 1) T)
    (GlobalResolvent.globalPrivateBlock D₀ J c κ σ T)

/-- The exact global private block factors into clock-independent coupling and
one diagonal clock action, independent of the number of time slots. -/
theorem globalPrivateBlock_factor (D₀ : V →L[ℂ] V) (J : P →L[ℂ] V)
    (c κ σ : ℝ) (T : ℕ) :
    GlobalResolvent.globalPrivateBlock D₀ J c κ σ T =
      chronologicalOperator (1 - (κ : ℂ) • (J ∘L J†)) ((σ : ℂ) • J)
        ((c : ℂ) • 1) ((-(σ : ℂ)) • J†) T ∘L
          WeightedClock.diagonal (fun _ : Fin T => D₀) := by
  simpa only [GlobalResolvent.globalPrivateBlock, GlobalResolvent.localPrivateBlock,
    smul_comp] using
    chronologicalOperator_factor (1 - (κ : ℂ) • (J ∘L J†)) D₀
      ((σ : ℂ) • J) ((c : ℂ) • 1) ((-(σ : ℂ)) • J†) T

/-- The full chronological transducer has a single parallel clock factor.
This operator identity alone does not assign an oracle query cost. -/
theorem clockColligation_factor (D₀ : V →L[ℂ] V) (J : P →L[ℂ] V)
    (c κ σ : ℝ) (T : ℕ) :
    clockColligation D₀ J c κ σ T = couplingNetwork J c κ σ T ∘L parallelClock D₀ T := by
  simpa only [clockColligation, couplingNetwork, GlobalResolvent.globalPrivateBlock,
    GlobalResolvent.localPrivateBlock, smul_comp] using
    full_chronology_factor (1 - (κ : ℂ) • (J ∘L J†)) D₀
      ((σ : ℂ) • J) ((c : ℂ) • 1) ((-(σ : ℂ)) • J†) T

end
end SparseHamiltonian.ChronologicalClockFactorization
