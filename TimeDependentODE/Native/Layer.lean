import SparseODE.ODEJointSimulation
import TimeDependentHamiltonian.Native.Encoding

/-!
# Coherent sampled-time native layer for the ODE Cayley clock

The time-dependent ODE solver simulates, on every coherent branch `i`, the
ordered product of the tagged LCHS Hamiltonians of the samples `r < M`. The
released native construction (`ODECoherentCayley`, `ODEJointNative`) runs one
24-query tagged Cayley circuit coherently over a branch register whose label
controls only known rotations. Here the branch register is enlarged by the
sampled-time address `r : Fin M`:

* the public parameters (frequency `k i` and rescaling `γ i r`) may depend on
  both the branch and the time address, because they enter only fixed gates
  (`schedule`, built from the released common query shape);
* every query is one call of the coherent sampled-time oracle
  `∑_r |r⟩⟨r| ⊗ O_r`, with the branch label as a spectator (`labelOracle`,
  `compileLabel`), so the count stays 24;
* the clean encoding of chronological slot `t` writes the time address of
  its sample (`cleanSlot`), so one source program acts as the slot-`t` action
  on every private cell (`cayleyProgram_intertwines`);
* the released active-clock compiler then implements every slot-dependent
  active layer with exactly `72` primitive calls (`implementsOn`).
-/

namespace SparseHamiltonian.TimeDependentODE

noncomputable section

open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000

/-! ### Schedules whose labels read different oracle instances -/

section LabelSchedule

variable {κ L X Y K : Type*} [Fintype κ]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The coherent oracle in which the label `b` reads the instance `σ x b`. -/
def labelOracle (O : L → Y → K →L[ℂ] K) (σ : X → κ → Y) (l : L) (x : X) :
    PiLp 2 (fun _ : κ => K) →L[ℂ] PiLp 2 (fun _ : κ => K) :=
  WeightedClock.diagonal (fun b => O l (σ x b))

theorem labelOracle_unitary (O : L → Y → K →L[ℂ] K) (hO : ∀ l y, IsUnitary (O l y))
    (σ : X → κ → Y) (l : L) (x : X) : IsUnitary (labelOracle O σ l x) :=
  CoherentQuerySchedule.diagonal_unitary _ (fun b => hO l (σ x b))

/-- Compile a schedule with label-dependent fixed gates and label-dependent
oracle instances. Each query instruction is one call of the coherent oracle. -/
def compileLabel (O : L → Y → K →L[ℂ] K) (σ : X → κ → Y) :
    CoherentQuerySchedule.Schedule κ L K → MultiOracleCircuit.Program (labelOracle O σ)
  | .fixed U hU => .fixed (WeightedClock.diagonal U) (CoherentQuerySchedule.diagonal_unitary U hU)
  | .query l => .query l
  | .queryAdjoint l => .queryAdjoint l
  | .seq p q => .seq (compileLabel O σ p) (compileLabel O σ q)

@[simp] theorem compileLabel_count (O : L → Y → K →L[ℂ] K) (σ : X → κ → Y)
    (p : CoherentQuerySchedule.Schedule κ L K) : (compileLabel O σ p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
    simp only [compileLabel, MultiOracleCircuit.Program.count_seq,
      CoherentQuerySchedule.Schedule.count, hp, hq]

@[simp] theorem compileLabel_cost (O : L → Y → K →L[ℂ] K) (σ : X → κ → Y)
    (p : CoherentQuerySchedule.Schedule κ L K) (w : L → ℕ) :
    (compileLabel O σ p).cost w = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
    simp only [compileLabel, MultiOracleCircuit.Program.cost_seq,
      CoherentQuerySchedule.Schedule.cost, hp, hq]

/-- The compiled program has the exact diagonal semantics, every label using
its own instance, including inverse queries. -/
theorem compileLabel_eval (O : L → Y → K →L[ℂ] K) (σ : X → κ → Y)
    (p : CoherentQuerySchedule.Schedule κ L K) (x : X) :
    (compileLabel O σ p).eval x =
      WeightedClock.diagonal (fun b => (p.branch O b).eval (σ x b)) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => exact WeightedClock.diagonal_adjoint _
  | seq p q hp hq =>
    simp only [compileLabel, CoherentQuerySchedule.Schedule.branch,
      MultiOracleCircuit.Program.eval_seq, hp, hq]
    exact WeightedClock.diagonal_comp _ _

end LabelSchedule

/-! ### Placing a branch family at one time address -/

section SlotPlace

variable {ι K : Type*} [Fintype ι] [NormedAddCommGroup K] [InnerProductSpace ℂ K] {M : ℕ}

/-- Place an `ι`-indexed family at the time address `r` of the enlarged label
register `ι × Fin M`, with zero amplitude at other addresses. -/
def slotPlace (r : Fin M) :
    PiLp 2 (fun _ : ι => K) →ₗᵢ[ℂ] PiLp 2 (fun _ : ι × Fin M => K) where
  toFun v := WithLp.toLp 2 (fun b => if b.2 = r then v b.1 else 0)
  map_add' v w := by
    apply PiLp.ext
    intro b
    by_cases h : b.2 = r <;> simp [h]
  map_smul' c v := by
    apply PiLp.ext
    intro b
    by_cases h : b.2 = r <;> simp [h]
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single r]
    · simp
    · intro q _ hq
      simp [hq]
    · simp

@[simp] theorem slotPlace_apply (r : Fin M) (v : PiLp 2 (fun _ : ι => K)) (b : ι × Fin M) :
    slotPlace r v b = if b.2 = r then v b.1 else 0 := rfl

end SlotPlace

/-! ### The sampled-time native Cayley circuit -/

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s M : ℕ}

/-- The label `(i, r)` reads the sample `r` of the unknown instance. -/
def sample (x : X) (b : ι × Fin M) : X × Fin M := (x, b.2)

/-- The released tagged Cayley circuit on every label, with label-dependent
public parameters. Its common query shape is the released one. -/
def schedule (D : Data (X × Fin M) n Z s) (k : ι → ℝ) (γ : ι → Fin M → ℝ) (ρ : ℝ) :
    CoherentQuerySchedule.Schedule (ι × Fin M) Query
      (EuclideanSpace ℂ (ODENativeCayley.Basis n Z)) :=
  CommonQueryShape.schedule
    (CommonQueryShape.erase (ODENativeCayley.program D 0 0 ρ))
    (fun b => ODENativeCayley.program D (k b.1) (γ b.1 b.2) ρ)
    (fun b => ODECoherentCayley.program_shape D (k b.1) (γ b.1 b.2) ρ)

omit [Fintype ι] [DecidableEq ι] in
theorem schedule_branch (D : Data (X × Fin M) n Z s) (k : ι → ℝ) (γ : ι → Fin M → ℝ)
    (ρ : ℝ) (b : ι × Fin M) :
    (schedule D k γ ρ).branch (ODENativeCayley.oracle D) b =
      ODENativeCayley.program D (k b.1) (γ b.1 b.2) ρ :=
  CommonQueryShape.branch_schedule _ _ _ b

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem schedule_count (D : Data (X × Fin M) n Z s) (k : ι → ℝ)
    (γ : ι → Fin M → ℝ) (ρ : ℝ) : (schedule D k γ ρ).count = 24 := by
  rw [schedule, CommonQueryShape.schedule_count, CommonQueryShape.erase_count,
    ODENativeCayley.program_count]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem schedule_cost (D : Data (X × Fin M) n Z s) (k : ι → ℝ)
    (γ : ι → Fin M → ℝ) (ρ : ℝ) (w : Query → ℕ) :
    (schedule D k γ ρ).cost w =
      6 * w .rowLocation + 6 * w .columnLocation + 12 * w .value := by
  rw [schedule, CommonQueryShape.schedule_cost, CommonQueryShape.erase_cost,
    ODENativeCayley.program_cost]

/-- The coherent sampled-time native query, with the branch as a spectator. -/
abbrev coherentOracle (D : Data (X × Fin M) n Z s) :
    Query → X → PiLp 2 (fun _ : ι × Fin M => EuclideanSpace ℂ (ODENativeCayley.Basis n Z)) →L[ℂ]
      PiLp 2 (fun _ : ι × Fin M => EuclideanSpace ℂ (ODENativeCayley.Basis n Z)) :=
  labelOracle (ODENativeCayley.oracle D) (sample (ι := ι) (M := M))

/-- One coherent program for all branches and time addresses. -/
def coherentProgram (D : Data (X × Fin M) n Z s) (k : ι → ℝ) (γ : ι → Fin M → ℝ) (ρ : ℝ) :
    MultiOracleCircuit.Program (coherentOracle (ι := ι) D) :=
  compileLabel (ODENativeCayley.oracle D) sample (schedule D k γ ρ)

/-- Flattened computational basis: time-addressed branch label and payload. -/
abbrev Basis (ι n Z : Type*) (M : ℕ) := ODEJointNative.Basis (ι × Fin M) n Z

/-- Fixed register coordinates. -/
def layout :
    PiLp 2 (fun _ : ι × Fin M => EuclideanSpace ℂ (ODENativeCayley.Basis n Z))
      ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Basis ι n Z M) :=
  RegisterEquivalences.productFlatten (ι × Fin M) (ODENativeCayley.Basis n Z)

/-- The coherent sampled-time query in flattened coordinates. -/
abbrev cayleyOracle (D : Data (X × Fin M) n Z s) (l : Query) (x : X) :
    EuclideanSpace ℂ (Basis ι n Z M) →L[ℂ] EuclideanSpace ℂ (Basis ι n Z M) :=
  (layout (ι := ι) (M := M) (n := n) (Z := Z)).conjStarAlgEquiv
    (coherentOracle (ι := ι) D l x)

omit [DecidableEq ι] [DecidableEq Z] in
theorem cayleyOracle_unitary (D : Data (X × Fin M) n Z s) (l : Query) (x : X) :
    IsUnitary (cayleyOracle (ι := ι) D l x) := by
  unfold cayleyOracle
  exact OracleCircuit.IsUnitary.transport
    (labelOracle_unitary (ODENativeCayley.oracle D) (ODENativeCayley.oracle_unitary D)
      (sample (ι := ι) (M := M)) l x) (layout (ι := ι) (M := M) (n := n) (Z := Z))

/-- The literal twenty-four-query coherent sampled-time circuit. -/
def cayleyProgram (D : Data (X × Fin M) n Z s) (k : ι → ℝ) (γ : ι → Fin M → ℝ) (ρ : ℝ) :
    MultiOracleCircuit.Program (cayleyOracle (ι := ι) D) := by
  let p := MultiOracleCircuit.Program.transport
    (O := coherentOracle (ι := ι) D)
    (layout (ι := ι) (M := M) (n := n) (Z := Z)) (coherentProgram D k γ ρ)
  with_reducible exact p

omit [DecidableEq ι] in
@[simp] theorem cayleyProgram_count (D : Data (X × Fin M) n Z s) (k : ι → ℝ)
    (γ : ι → Fin M → ℝ) (ρ : ℝ) : (cayleyProgram D k γ ρ).count = 24 := by
  simp only [cayleyProgram, MultiOracleCircuit.Program.count_transport, coherentProgram,
    compileLabel_count, schedule_count]

omit [DecidableEq ι] in
@[simp] theorem cayleyProgram_cost (D : Data (X × Fin M) n Z s) (k : ι → ℝ)
    (γ : ι → Fin M → ℝ) (ρ : ℝ) (w : Query → ℕ) :
    (cayleyProgram D k γ ρ).cost w =
      6 * w .rowLocation + 6 * w .columnLocation + 12 * w .value := by
  simp only [cayleyProgram, MultiOracleCircuit.Program.cost_transport, coherentProgram,
    compileLabel_cost, schedule_cost]

/-- The private action of the cells at time address `r`: the released tagged
Cayley action of the sample `r` on every branch. -/
def slotAction (D : Data (X × Fin M) n Z s) (k : ι → ℝ) (γ : ι → Fin M → ℝ) (ρ : ℝ)
    (x : X) (r : Fin M) : ODEJointNative.Private ι n →L[ℂ] ODEJointNative.Private ι n :=
  WeightedClock.diagonal (fun i => ODEFixedTaggedMoments.action D (x, r)
    (ODEMatrixEnergy.lchsHamiltonian (D.matrix (x, r)) (k i)) ρ (γ i r))

/-- Clean encoding of a private cell at time address `r`. -/
def cleanSlot (D : Data (X × Fin M) n Z s) (r : Fin M) :
    ODEJointNative.Private ι n →ₗᵢ[ℂ] EuclideanSpace ℂ (Basis ι n Z M) :=
  (layout (ι := ι) (M := M) (n := n) (Z := Z)).toLinearIsometry.comp
    ((slotPlace (K := EuclideanSpace ℂ (ODENativeCayley.Basis n Z)) r).comp
      (ODEJointNative.coherentClean D))

omit [DecidableEq ι] in
/-- Components of the released coherent clean encoding. -/
theorem coherentClean_apply (D : Data (X × Fin M) n Z s)
    (v : ODEJointNative.Private ι n) (i : ι) :
    ODEJointNative.coherentClean D v i = ODENativeCayley.clean D (v i) :=
  CoherentQuerySchedule.rectangular_apply _ v i

omit [DecidableEq ι] in
/-- On the cells of time address `r`, the coherent program is the slot action. -/
theorem cayleyProgram_intertwines (D : Data (X × Fin M) n Z s) (k : ι → ℝ)
    (γ : ι → Fin M → ℝ) (ρ : ℝ) (x : X) (r : Fin M) :
    (cayleyProgram D k γ ρ).eval x ∘L (cleanSlot D r).toContinuousLinearMap =
      (cleanSlot D r).toContinuousLinearMap ∘L slotAction D k γ ρ x r := by
  rw [cayleyProgram, MultiOracleCircuit.Program.eval_transport]
  apply ContinuousLinearMap.ext
  intro v
  change layout ((coherentProgram D k γ ρ).eval x
      (layout.symm (layout (slotPlace r (ODEJointNative.coherentClean D v))))) =
    layout (slotPlace r (ODEJointNative.coherentClean D (slotAction D k γ ρ x r v)))
  rw [LinearIsometryEquiv.symm_apply_apply]
  congr 1
  rw [coherentProgram, compileLabel_eval]
  apply PiLp.ext
  intro b
  rw [WeightedClock.diagonal_apply, slotPlace_apply, slotPlace_apply, schedule_branch]
  by_cases hb : b.2 = r
  · rw [if_pos hb, if_pos hb, coherentClean_apply, coherentClean_apply]
    have h := congrArg (fun A : ODETaggedMoments.PrivateSpace n →L[ℂ]
        EuclideanSpace ℂ (ODENativeCayley.Basis n Z) => A (v b.1))
      (ODENativeCayley.program_intertwines D (k b.1) (γ b.1 b.2) ρ (x, b.2))
    simp only [comp_apply, LinearIsometry.coe_toContinuousLinearMap] at h
    rw [show sample x b = (x, b.2) from rfl, h, slotAction, WeightedClock.diagonal_apply, hb]
  · rw [if_neg hb, if_neg hb, map_zero]

/-- The public dummy input, at branch and time address `b0`. -/
def cleanBasis (D : Data (X × Fin M) n Z s) (b0 : ι × Fin M) : Basis ι n Z M :=
  (b0, ODENativeCayley.cleanBasis D)

/-- Basis image of the dummy input; used only as a validity witness. -/
def image (D : Data (X × Fin M) n Z s) (b0 : ι × Fin M) (l : Query) (x : X) :
    Basis ι n Z M :=
  (b0, ODENativeCayley.image D l (x, b0.2))

omit [AddCommGroup Z] in
theorem layout_symm_single (b0 : ι × Fin M) (c : ODENativeCayley.Basis n Z) (b : ι × Fin M) :
    (layout (ι := ι) (M := M) (n := n) (Z := Z)).symm
        (EuclideanSpace.single ((b0, c) : Basis ι n Z M) (1 : ℂ)) b =
      if b = b0 then EuclideanSpace.single c (1 : ℂ) else 0 := by
  apply PiLp.ext
  intro c'
  change (RegisterEquivalences.productFlatten (ι × Fin M) (ODENativeCayley.Basis n Z)).symm
      (EuclideanSpace.single ((b0, c) : Basis ι n Z M) (1 : ℂ)) b c' = _
  rw [RegisterEquivalences.productFlatten_symm_apply]
  by_cases hb : b = b0
  · subst hb
    by_cases hc : c' = c
    · subst hc
      simp
    · simp [hc]
  · simp [hb]

/-- The native valid-slot promise of the released data gives the dummy-input
validity for the coherent sampled-time query. -/
theorem valid (D : Data (X × Fin M) n Z s) (b0 : ι × Fin M) (l : Query) (x : X) :
    cayleyOracle D l x (EuclideanSpace.single (cleanBasis D b0) 1) =
      EuclideanSpace.single (image D b0 l x) 1 := by
  ext ⟨b, c⟩
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  change (WeightedClock.diagonal (fun b' => ODENativeCayley.oracle D l (sample x b'))
      ((layout (ι := ι) (M := M) (n := n) (Z := Z)).symm
        (EuclideanSpace.single (cleanBasis D b0) 1))) b c = _
  rw [WeightedClock.diagonal_apply, cleanBasis, layout_symm_single]
  by_cases hb : b = b0
  · subst hb
    rw [if_pos rfl]
    change ODENativeCayley.oracle D l (x, b.2)
        (EuclideanSpace.single (ODENativeCayley.cleanBasis D) 1) c = _
    rw [ODENativeCayley.valid D l (x, b.2)]
    simp only [image, PiLp.single_apply, Prod.mk.injEq, true_and]
  · rw [if_neg hb, map_zero]
    simp only [image, PiLp.zero_apply, PiLp.single_apply, Prod.mk.injEq]
    rw [if_neg (fun h => hb h.1)]

/-- Public cells are never acted on; they use the address-`r0` encoding of
the released boundary. -/
def publicEmbedding (D : Data (X × Fin M) n Z s) (r0 : Fin M) :
    ODEJointNative.Public ι n →ₗᵢ[ℂ] EuclideanSpace ℂ (Basis ι n Z M) :=
  (cleanSlot D r0).comp (ODEJointNative.boundaryIsometry D)

/-- The private cells of chronological slot `t` carry the time address of
the sample used at that slot. -/
def privateEmbedding (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ) :
    ODEJointNative.Private ι n →ₗᵢ[ℂ]
      NativeMaskedOracle.Logical PUnit.{1} (Basis ι n Z M) :=
  FlatMaskedAccess.singleton (cleanSlot D (TimeDependent.Sampled.sampleIndex hM t))

/-- Full native workspace of the sampled-time ODE clock. -/
abbrev Physical (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z] (M T d : ℕ) :=
  NativeMaskedOracle.Physical (ActiveRegisterLayout.Label PUnit.{1} T d) (Basis ι n Z M)

/-- Coherent sampled-time native queries with spectator registers. -/
abbrev oracle (D : Data (X × Fin M) n Z s) (T d : ℕ) :
    Query → X → Physical ι n Z M T d →L[ℂ] Physical ι n Z M T d :=
  NativeWholeProgramActive.oracle (C := PUnit.{1}) (cayleyOracle (ι := ι) D) T d

omit [DecidableEq ι] [DecidableEq Z] in
theorem oracle_unitary (D : Data (X × Fin M) n Z s) (T d : ℕ) (l : Query) (x : X) :
    IsUnitary (oracle (ι := ι) D T d l x) :=
  NativeMaskedOracle.oracle_unitary (cayleyOracle (ι := ι) D l)
    (cayleyOracle_unitary D l) x

/-- The fixed logical-to-physical encoding, common to all reuse indices. -/
def embedding (D : Data (X × Fin M) n Z s) (hM : 0 < M) (b0 : ι × Fin M) (T d : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := ODEJointNative.Public ι n)
      (V := ChronologicalResolvent.BlockOperator.H T (ODEJointNative.Private ι n)) d)
      →ₗᵢ[ℂ] Physical ι n Z M T d :=
  TimeDependent.cleanInputV (C := PUnit.{1}) (publicEmbedding D ⟨0, hM⟩)
    (privateEmbedding D hM) (cleanBasis D b0) T d

/-- The literal primitive circuit for one active layer. -/
def program (D : Data (X × Fin M) n Z s) (b0 : ι × Fin M) (k : ι → ℝ)
    (γ : ι → Fin M → ℝ) (ρ : ℝ) (T d r : ℕ) :
    MultiOracleCircuit.Program (oracle (ι := ι) D T d) :=
  NativeWholeProgramActive.program (C := PUnit.{1}) (cayleyOracle D)
    (cleanBasis D b0) (cayleyProgram D k γ ρ) T d r

@[simp] theorem program_count (D : Data (X × Fin M) n Z s) (b0 : ι × Fin M) (k : ι → ℝ)
    (γ : ι → Fin M → ℝ) (ρ : ℝ) (T d r : ℕ) : (program D b0 k γ ρ T d r).count = 72 := by
  rw [program, NativeWholeProgramActive.program_count, cayleyProgram_count]

/-- Every slot-dependent active layer has an exact clean implementation with
seventy-two coherent sampled-time queries, independently of `M`. -/
theorem implementsOn (D : Data (X × Fin M) n Z s) (hM : 0 < M) (b0 : ι × Fin M)
    (k : ι → ℝ) (γ : ι → Fin M → ℝ) (ρ : ℝ) (T d r : ℕ) :
    LabeledEncodedOracle.ImplementsOn (oracle (ι := ι) D T d)
      (fun x => TimeDependent.activeClockV (P := ODEJointNative.Public ι n)
        (fun t => slotAction D k γ ρ x (TimeDependent.Sampled.sampleIndex hM t)) T d r)
      (embedding D hM b0 T d).toContinuousLinearMap 72 := by
  have h := TimeDependent.clean_implementsOnV (C := PUnit.{1}) (cayleyOracle (ι := ι) D)
    (cayleyOracle_unitary D) (cleanBasis D b0) (image D b0) (valid D b0)
    (cayleyProgram D k γ ρ) (publicEmbedding D ⟨0, hM⟩) (privateEmbedding D hM)
    (fun x t => slotAction D k γ ρ x (TimeDependent.Sampled.sampleIndex hM t))
    (fun x t => FlatMaskedAccess.singleton_intertwines _ _ _
      (cayleyProgram_intertwines D k γ ρ x (TimeDependent.Sampled.sampleIndex hM t))) T d r
  have h72 : 3 * (cayleyProgram (ι := ι) D k γ ρ).count = 72 := by simp
  rw [h72] at h
  exact h

end

end SparseHamiltonian.TimeDependentODE
