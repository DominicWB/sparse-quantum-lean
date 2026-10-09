import TimeDependentHamiltonian.Native.TimeIndexed

/-!
# Slot-dependent clean encodings and the sampled active layer

The released active-clock compiler runs one source program on every active
private cell. To apply the private operation of the sample `t` on the cells of
time slot `t`, the clean encoding writes `|t⟩` into the time register of each
private cell of slot `t` (`embeddingV`, `cleanInputV`); the time register is
untouched by every fixed gate and only addresses the coherent sampled-time
oracle. With this fixed encoding, the released masked compilation of the
sampled eighteen-query Cayley program implements the slot-dependent active
clock with exactly `54` primitive calls (`Sampled.implementsOn`), independently
of the number of time slots.
-/

namespace SparseHamiltonian.TimeDependent

noncomputable section

open ContinuousLinearMap OracleCircuit ReuseLayerFactorization NativeMaskedOracle
open scoped InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000

section Embedding

variable {P Q V W : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- Embed every private cell with the encoding of its time slot, and every
public reuse cell with one fixed encoding. -/
def embeddingV (eP : P →ₗᵢ[ℂ] Q) (eV : ℕ → V →ₗᵢ[ℂ] W) (T d : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := P)
      (V := ChronologicalResolvent.BlockOperator.H T V) d) →ₗᵢ[ℂ]
      PiLp 2 (SmoothingLCU.BranchSpace (P := Q)
        (V := ChronologicalResolvent.BlockOperator.H T W) d) where
  toLinearMap :=
    { toFun := fun x => WithLp.toLp 2 (fun i => WithLp.toLp 2
        (WithLp.toLp 2 (fun t : Fin T => eV (t : ℕ) ((x i).fst t)),
          WithLp.toLp 2 (fun j => eP ((x i).snd j))))
      map_add' := by
        intro x y
        apply PiLp.ext
        intro i
        apply WithLp.ofLp_injective 2
        apply Prod.ext
        · apply PiLp.ext
          intro t
          exact (eV (t : ℕ)).map_add _ _
        · apply PiLp.ext
          intro j
          exact eP.map_add _ _
      map_smul' := by
        intro z x
        apply PiLp.ext
        intro i
        apply WithLp.ofLp_injective 2
        apply Prod.ext
        · apply PiLp.ext
          intro t
          exact (eV (t : ℕ)).map_smul z _
        · apply PiLp.ext
          intro j
          exact eP.map_smul z _ }
  norm_map' := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    change (∑ i, ((∑ t : Fin T, ‖eV (t : ℕ) ((x i).fst t)‖ ^ 2) +
        ∑ j, ‖eP ((x i).snd j)‖ ^ 2)) =
      ∑ i, ((∑ t, ‖(x i).fst t‖ ^ 2) + ∑ j, ‖(x i).snd j‖ ^ 2)
    simp only [LinearIsometry.norm_map]

omit [CompleteSpace P] [CompleteSpace V] in
/-- The released uniform active clock is the slot-dependent one with a
constant slot family. -/
theorem activeClock_eq_activeClockV (U : V →L[ℂ] V) (T d r : ℕ) :
    activeClock (P := P) U T d r = activeClockV (P := P) (fun _ => U) T d r := rfl

omit [CompleteSpace P] [CompleteSpace Q] [CompleteSpace V] [CompleteSpace W] in
/-- Clean slotwise implementations extend to all chronological copies,
inactive branches and public bypasses. -/
theorem active_intertwinesV (eP : P →ₗᵢ[ℂ] Q) (eV : ℕ → V →ₗᵢ[ℂ] W)
    (U : ℕ → W →L[ℂ] W) (D : ℕ → V →L[ℂ] V)
    (h : ∀ t, U t ∘L (eV t).toContinuousLinearMap = (eV t).toContinuousLinearMap ∘L D t)
    (T d r : ℕ) :
    activeClockV (P := Q) U T d r ∘L (embeddingV eP eV T d).toContinuousLinearMap =
      (embeddingV eP eV T d).toContinuousLinearMap ∘L activeClockV (P := P) D T d r := by
  have hv (t : ℕ) (v : V) : U t (eV t v) = eV t (D t v) :=
    congrArg (fun A : V →L[ℂ] W => A v) (h t)
  ext x i
  by_cases hr : r < ReuseWeights.length d i
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply PiLp.ext
      intro t
      simp [activeClockV, activeQuery, activeBranch, hr, embeddingV, hv]
    · apply PiLp.ext
      intro j
      simp [activeClockV, activeQuery, activeBranch, hr, embeddingV]
  · simp [activeClockV, activeQuery, activeBranch, hr, embeddingV]

end Embedding

section Compiler

variable {C B X L : Type*} [Fintype C] [Fintype B] [DecidableEq B]
  (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The common clean encoding with slot-dependent private encodings. -/
def cleanInputV (eP : P →ₗᵢ[ℂ] EuclideanSpace ℂ B)
    (eV : ℕ → V →ₗᵢ[ℂ] Logical C B) (a : B) (T d : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := P)
      (V := ChronologicalResolvent.BlockOperator.H T V) d) →ₗᵢ[ℂ]
      Physical (ActiveRegisterLayout.Label C T d) B :=
  (NativeWholeProgramActive.input (C := C) a T d).comp (embeddingV eP eV T d)

omit [CompleteSpace P] [CompleteSpace V] in
/-- A source program whose clean action at each slot is that slot's private
operation discharges the slot-dependent active-layer premise. -/
theorem program_clean_intertwinesV (hF : ∀ l x, IsUnitary (F l x)) (a : B)
    (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) =
      EuclideanSpace.single (image l x) 1)
    (p : MultiOracleCircuit.Program F)
    (eP : P →ₗᵢ[ℂ] EuclideanSpace ℂ B) (eV : ℕ → V →ₗᵢ[ℂ] Logical C B)
    (D : X → ℕ → V →L[ℂ] V)
    (hClean : ∀ x t, WeightedClock.diagonal (fun _ : C => p.eval x) ∘L
      (eV t).toContinuousLinearMap = (eV t).toContinuousLinearMap ∘L D x t)
    (T d r : ℕ) (x : X) :
    (NativeWholeProgramActive.program (C := C) F a p T d r).eval x ∘L
        (cleanInputV eP eV a T d).toContinuousLinearMap =
      (cleanInputV eP eV a T d).toContinuousLinearMap ∘L
        activeClockV (P := P) (D x) T d r := by
  change (NativeWholeProgramActive.program (C := C) F a p T d r).eval x ∘L
      ((NativeWholeProgramActive.input (C := C) a T d).toContinuousLinearMap ∘L
        (embeddingV eP eV T d).toContinuousLinearMap) =
    ((NativeWholeProgramActive.input (C := C) a T d).toContinuousLinearMap ∘L
      (embeddingV eP eV T d).toContinuousLinearMap) ∘L _
  rw [← comp_assoc, NativeWholeProgramActive.program_intertwines F hF a image hvalid,
    comp_assoc, activeClock_eq_activeClockV,
    active_intertwinesV eP eV _ (D x) (hClean x) T d r, comp_assoc]

omit [CompleteSpace P] [CompleteSpace V] in
/-- Each slot-dependent active layer is implemented with exactly three times
the source program's query count. -/
theorem clean_implementsOnV (hF : ∀ l x, IsUnitary (F l x)) (a : B)
    (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) =
      EuclideanSpace.single (image l x) 1)
    (p : MultiOracleCircuit.Program F)
    (eP : P →ₗᵢ[ℂ] EuclideanSpace ℂ B) (eV : ℕ → V →ₗᵢ[ℂ] Logical C B)
    (D : X → ℕ → V →L[ℂ] V)
    (hClean : ∀ x t, WeightedClock.diagonal (fun _ : C => p.eval x) ∘L
      (eV t).toContinuousLinearMap = (eV t).toContinuousLinearMap ∘L D x t)
    (T d r : ℕ) :
    LabeledEncodedOracle.ImplementsOn (NativeWholeProgramActive.oracle (C := C) F T d)
      (fun x => activeClockV (P := P) (D x) T d r)
      (cleanInputV eP eV a T d).toContinuousLinearMap (3 * p.count) :=
  ⟨NativeWholeProgramActive.program (C := C) F a p T d r,
    program_clean_intertwinesV F hF a image hvalid p eP eV D hClean T d r,
    (NativeWholeProgramActive.program_count F a p T d r).le⟩

end Compiler

/-! ### The sampled native Cayley layer -/

namespace Sampled

open NativeSparseBlockEncoding

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- The sampled time used at slot `k`; slots are numbered `0, …, M - 1`. -/
def sampleIndex (hM : 0 < M) (k : ℕ) : Fin M := ⟨k % M, Nat.mod_lt k hM⟩

/-- The private Cayley action of each time slot. -/
def actions (D : Data (X × Fin M) n Z s) (hM : 0 < M) (γ : ℝ) (x : X) (k : ℕ) :
    SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n :=
  FixedNativeCayleySimulation.action D (x, sampleIndex hM k) γ

/-- Full native workspace: the active label, the time register and all query
spectators. -/
abbrev Physical (n Z : Type*) [Fintype n] [Fintype Z] (M T d : ℕ) :=
  NativeMaskedOracle.Physical (ActiveRegisterLayout.Label PUnit.{1} T d)
    (Fin M × NativeCayleyProgram.Basis n Z)

/-- The coherent sampled-time native queries with spectator registers. -/
abbrev oracle (D : Data (X × Fin M) n Z s) (T d : ℕ) :
    Query → X → Physical n Z M T d →L[ℂ] Physical n Z M T d :=
  NativeWholeProgramActive.oracle (C := PUnit.{1}) (sampledOracle D) T d

omit [DecidableEq Z] in
theorem oracle_unitary (D : Data (X × Fin M) n Z s) (T d : ℕ) (l : Query) (x : X) :
    IsUnitary (oracle D T d l x) :=
  NativeMaskedOracle.oracle_unitary _ (fun y => sampledOracle_unitary D l y) x

/-- The public system is prepared at the first sampled time; public cells are
never acted on by the sampled program. -/
def publicEmbedding (D : Data (X × Fin M) n Z s) (hM : 0 < M) :
    EuclideanSpace ℂ n →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin M × NativeCayleyProgram.Basis n Z) :=
  (timeEmbed ⟨0, hM⟩).comp (NativeCayleyActive.publicEmbedding D)

/-- The private cells of slot `k` carry the time register `|k⟩`. -/
def privateEmbedding (D : Data (X × Fin M) n Z s) (hM : 0 < M) (k : ℕ) :
    SparseEdgeMoments.OrientedSpace n →ₗᵢ[ℂ]
      NativeMaskedOracle.Logical PUnit.{1} (Fin M × NativeCayleyProgram.Basis n Z) :=
  FlatMaskedAccess.singleton (sampledClean D (sampleIndex hM k))

/-- The fixed logical-to-physical encoding, common to all reuse indices. -/
def embedding (D : Data (X × Fin M) n Z s) (hM : 0 < M) (T d : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := EuclideanSpace ℂ n)
      (V := ChronologicalResolvent.BlockOperator.H T (SparseEdgeMoments.OrientedSpace n)) d)
      →ₗᵢ[ℂ] Physical n Z M T d :=
  cleanInputV (publicEmbedding D hM) (privateEmbedding D hM) (sampledBasis D ⟨0, hM⟩) T d

/-- The literal primitive circuit for one active layer. -/
def program (D : Data (X × Fin M) n Z s) (hM : 0 < M) (γ : ℝ) (T d r : ℕ) :
    MultiOracleCircuit.Program (oracle D T d) :=
  NativeWholeProgramActive.program (C := PUnit.{1}) (sampledOracle D)
    (sampledBasis D ⟨0, hM⟩) (sampledProgram D γ) T d r

@[simp] theorem program_count (D : Data (X × Fin M) n Z s) (hM : 0 < M) (γ : ℝ)
    (T d r : ℕ) : (program D hM γ T d r).count = 54 := by
  simp [program]

/-- The slot-dependent active layer has an exact clean implementation with
fifty-four coherent sampled-time queries. -/
theorem implementsOn (D : Data (X × Fin M) n Z s) (hM : 0 < M) (γ : ℝ) (T d r : ℕ) :
    LabeledEncodedOracle.ImplementsOn (oracle D T d)
      (fun x => activeClockV (P := EuclideanSpace ℂ n) (actions D hM γ x) T d r)
      (embedding D hM T d).toContinuousLinearMap 54 := by
  have h := clean_implementsOnV (C := PUnit.{1}) (sampledOracle D)
    (fun l x => sampledOracle_unitary D l x) (sampledBasis D ⟨0, hM⟩)
    (fun l x => ((⟨0, hM⟩ : Fin M), NativeCayleyProgram.image D l (x, ⟨0, hM⟩)))
    (fun l x => sampledOracle_valid D ⟨0, hM⟩ l x) (sampledProgram D γ)
    (publicEmbedding D hM) (privateEmbedding D hM) (actions D hM γ)
    (fun x t => FlatMaskedAccess.singleton_intertwines _ _ _
      (sampledProgram_intertwines D γ x (sampleIndex hM t))) T d r
  have h54 : 3 * (sampledProgram D γ).count = 54 := by simp
  rw [h54] at h
  exact h

end Sampled

end

end SparseHamiltonian.TimeDependent
