import SparseHamiltonian.NativeSparseMaskedAccess
import SparseHamiltonian.CoherentQuerySchedule
import SparseHamiltonian.OracleTransport
import TimeDependentHamiltonian.Native.TimeIndexed

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Coherent sampled-time native access for the Dyson solver (`odel:lem:dyson`)

Manuscript lines 4170-4176 and 4191-4196: "the ordinary sparse-matrix construction gives a block
encoding of `A(t)/α`, `α = sη`, with a constant number of queries" (uniform row/column slot
superpositions and a controlled entry rotation; no Hermiticity), and "one coherent call at the
selected sample time accesses `A_h`".

The data convention is the release's: the time-indexed native data
`D : Data (X × Fin Kₛ) n Z s` (`D.matrix (x, r)` is the sample `r`, the convention of
`TimeDependentExtensions.ODE.solver` and of the ODE lower-bound class), queried through the native
primitives `NativeSparseBlockEncoding.oracles` in the flat coordinates of `NativeSparseMaskedAccess`
(`flatOracle`, with its basis-image promise `NativeSparseMaskedAccess.valid`). The coherent
sampled-time register is the release's (`SparseHamiltonian.TimeDependent.timeIndexed`,
`timeOracle`, `timeEmbed`, `TimeDependentHamiltonian/Native/TimeIndexed.lean`); the physical matrix
oracle is the release's masked native access (`NativeMaskedProgram.oracle`). The released ODE
solver uses the aligned Cayley access (`MeshSource.matrixOracle`) instead; both are
`Family.access` up to fixed spectators (`Release.physicalOracle_normal_form`,
`familyLayout_matrix`).

* `timeOracle D = TimeDependent.timeOracle (flatOracle D)`, `∑_r |r⟩⟨r| ⊗ flatOracle D l (x, r)`:
  one coherent sampled-time call;
* `timeOracle_valid`: the common basis-image promise at the time address `0`
  (`TimeDependent.timeOracle_valid`);
* `matrixOracle Ω D`: the physical oracle, the release's masked native access
  (`NativeMaskedProgram.oracle`) with branch register `Ω` (spectator control, dummy and
  reference registers), and `matrix_valid` in flat coordinates (`matrixLayout`);
* `payloadEncoding hK D`: the six-query block-encoding input
  `NativeSparseBlockEncoding.input D` placed at time address `0` (`TimeDependent.timeEmbed`);
* `sampleOperator D x r = G̃_r/(s Λ)`, `G̃_r = D.matrix (x, r)` the sampled generator
  (`−A(t_r)` in the paper's convention `ẋ = A x + b`), `Λ = D.scale`, and `slot_compression`:
  one coherent six-query call at time address `r` (`TimeDependent.timeIndexed`), conjugated by
  the known time swap, compresses to it (reusing `NativeSparseBlockEncoding.compression`).
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct BigOperators

/-- The flat native basis `((n × n) × Z) × Fin 3`. -/
abbrev NBasis (n Z : Type*) : Type _ := NativeSparseMaskedAccess.Basis n Z

/-- The payload basis: a time address and the native basis. -/
abbrev PBasis (Ks : ℕ) (n Z : Type*) : Type _ := Fin Ks × NBasis n Z

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s Ks : ℕ}

/-- A native gate in flat coordinates. -/
def flatGate (U : SparseFlagEmbedding.Space (n × n) Z →L[ℂ] SparseFlagEmbedding.Space (n × n) Z) :
    EuclideanSpace ℂ (NBasis n Z) →L[ℂ] EuclideanSpace ℂ (NBasis n Z) :=
  (NativeSparseMaskedAccess.layout (n := n) (Z := Z)).conjStarAlgEquiv U

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
/-- `flatGate` is multiplicative. -/
theorem flatGate_mul
    (U V : SparseFlagEmbedding.Space (n × n) Z →L[ℂ] SparseFlagEmbedding.Space (n × n) Z) :
    flatGate (U * V) = flatGate U * flatGate V := by
  simp [flatGate]

/-- **One coherent sampled-time native call** `∑_r |r⟩⟨r| ⊗ O_l(x, r)` (lines 4192-4193): the
release's `TimeDependent.timeOracle` of the flat native primitives. -/
abbrev timeOracle (D : Data (X × Fin Ks) n Z s) :
    Query → X → EuclideanSpace ℂ (PBasis Ks n Z) →L[ℂ] EuclideanSpace ℂ (PBasis Ks n Z) :=
  TimeDependent.timeOracle (NativeSparseMaskedAccess.flatOracle D)

omit [DecidableEq Z] in
/-- The coherent sampled-time native call is unitary (`TimeDependent.timeOracle_unitary`). -/
theorem timeOracle_unitary (D : Data (X × Fin Ks) n Z s) (l : Query) (x : X) :
    IsUnitary (timeOracle D l x) :=
  TimeDependent.timeOracle_unitary _ (NativeSparseMaskedAccess.flatOracle_unitary D) l x

/-- The public clean payload basis vector (time address `0`). -/
def cleanTime (hK : 0 < Ks) (D : Data (X × Fin Ks) n Z s) : PBasis Ks n Z :=
  (⟨0, hK⟩, NativeSparseMaskedAccess.cleanBasis D)

/-- Its unknown image; an analytical witness only. -/
def imageTime (hK : 0 < Ks) (D : Data (X × Fin Ks) n Z s) (l : Query) (x : X) :
    PBasis Ks n Z :=
  (⟨0, hK⟩, NativeSparseMaskedAccess.image D l (x, ⟨0, hK⟩))

/-- The common basis-image promise of the coherent call at time address `0`
(`TimeDependent.timeOracle_valid` with `NativeSparseMaskedAccess.valid`). -/
theorem timeOracle_valid (hK : 0 < Ks) (D : Data (X × Fin Ks) n Z s) (l : Query) (x : X) :
    timeOracle D l x (EuclideanSpace.single (cleanTime hK D) 1) =
      EuclideanSpace.single (imageTime hK D l x) 1 :=
  TimeDependent.timeOracle_valid (NativeSparseMaskedAccess.flatOracle D)
    (NativeSparseMaskedAccess.cleanBasis D) (NativeSparseMaskedAccess.image D)
    (NativeSparseMaskedAccess.valid D) ⟨0, hK⟩ l x

/-- **The physical matrix oracle**: the release's masked native access on branch register `Ω`
(every branch receives the same native call; control, dummy and reference are spectators). -/
abbrev matrixOracle (Ω : Type*) [Fintype Ω] (D : Data (X × Fin Ks) n Z s) :
    Query → X → NativeMaskedOracle.Physical Ω (PBasis Ks n Z) →L[ℂ]
      NativeMaskedOracle.Physical Ω (PBasis Ks n Z) :=
  NativeMaskedProgram.oracle (ι := Ω) (timeOracle D)

omit [DecidableEq Z] in
/-- The physical matrix oracle is unitary. -/
theorem matrixOracle_unitary (Ω : Type*) [Fintype Ω] (D : Data (X × Fin Ks) n Z s)
    (l : Query) (x : X) : IsUnitary (matrixOracle Ω D l x) :=
  NativeMaskedOracle.oracle_unitary (timeOracle D l) (timeOracle_unitary D l) x

/-- Decidable equality of the physical basis (control, dummy, reference and payload), scoped to
the namespace `ODELowerBoundExtensions.Dyson`. -/
scoped instance instDecidableEqWorkspace :
    DecidableEq (NativeControlledOracle.Workspace (PBasis Ks n Z)) :=
  @instDecidableEqProd _ _
    (@instDecidableEqProd _ _ (@instDecidableEqProd _ _ inferInstance inferInstance)
      inferInstance) inferInstance

/-- Flat coordinates of the physical matrix workspace. -/
def matrixLayout (Ω : Type*) [Fintype Ω] :
    NativeMaskedOracle.Physical Ω (PBasis Ks n Z) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Ω × NativeControlledOracle.Workspace (PBasis Ks n Z)) :=
  RegisterEquivalences.productFlatten Ω (NativeControlledOracle.Workspace (PBasis Ks n Z))

/-- A public clean physical basis vector. -/
def matrixClean {Ω : Type*} (hK : 0 < Ks) (D : Data (X × Fin Ks) n Z s) (ω₀ : Ω) :
    Ω × NativeControlledOracle.Workspace (PBasis Ks n Z) :=
  (ω₀, (((false, cleanTime hK D), cleanTime hK D), cleanTime hK D))

/-- Its unknown image. -/
def matrixImage {Ω : Type*} (hK : 0 < Ks) (D : Data (X × Fin Ks) n Z s) (ω₀ : Ω)
    (l : Query) (x : X) : Ω × NativeControlledOracle.Workspace (PBasis Ks n Z) :=
  (ω₀, (((false, cleanTime hK D), cleanTime hK D), imageTime hK D l x))

omit [DecidableEq Z] in
/-- A flat basis vector of `A × B`, read in the branch-indexed coordinates of
`RegisterEquivalences.productFlatten`. -/
theorem productFlatten_symm_single {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (a : A) (b : B) (z : ℂ) (a' : A) :
    (RegisterEquivalences.productFlatten A B).symm (EuclideanSpace.single (a, b) z) a' =
      if a' = a then EuclideanSpace.single b z else 0 := by
  apply PiLp.ext
  intro b'
  rw [RegisterEquivalences.productFlatten_symm_apply]
  by_cases ha : a' = a
  · subst ha
    by_cases hb : b' = b
    · subst hb
      simp
    · simp [hb]
  · simp [ha]

set_option maxRecDepth 4096 in
/-- The basis-image promise of the physical matrix oracle in flat coordinates (the hypothesis
`hvalid` of `ODECoordinateNativeControl`). -/
theorem matrix_valid {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (hK : 0 < Ks)
    (D : Data (X × Fin Ks) n Z s) (ω₀ : Ω) (l : Query) (x : X) :
    (matrixLayout (n := n) (Z := Z) (Ks := Ks) Ω).conjStarAlgEquiv (matrixOracle Ω D l x)
        (EuclideanSpace.single (matrixClean hK D ω₀) 1) =
      EuclideanSpace.single (matrixImage hK D ω₀ l x) 1 := by
  have hT := timeOracle_valid hK D l x
  ext ⟨ω, w⟩
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  change MaskedProgram.masked (fun _ : Ω => true)
      (NativeControlledOracle.oracle (timeOracle D l) x)
      ((RegisterEquivalences.productFlatten Ω
        (NativeControlledOracle.Workspace (PBasis Ks n Z))).symm
        (EuclideanSpace.single (matrixClean hK D ω₀) 1)) ω w = _
  rw [MaskedProgram.masked_apply, if_pos rfl, matrixClean, productFlatten_symm_single]
  by_cases hω : ω = ω₀
  · subst hω
    rw [if_pos rfl]
    change LookupFromBasisOracle.spectator (S := (Bool × PBasis Ks n Z) × PBasis Ks n Z)
        (timeOracle D l x)
        (EuclideanSpace.single (((false, cleanTime hK D), cleanTime hK D), cleanTime hK D) 1) w = _
    rw [LookupFromBasisOracle.spectator_single _ _ _ _ hT]
    simp only [matrixImage, PiLp.single_apply, Prod.mk.injEq, true_and]
  · rw [if_neg hω, map_zero]
    simp only [matrixImage, PiLp.zero_apply, PiLp.single_apply, Prod.mk.injEq]
    rw [if_neg (fun h => hω h.1)]

/-- The known swap of the time addresses `0` and `r`. -/
def timeSwap (hK : 0 < Ks) (r : Fin Ks) :
    EuclideanSpace ℂ (PBasis Ks n Z) →L[ℂ] EuclideanSpace ℂ (PBasis Ks n Z) :=
  (LookupOracle.permutationUnitary
    (Equiv.prodCongr (Equiv.swap ⟨0, hK⟩ r) (Equiv.refl (NBasis n Z)))).toLinearIsometry.toContinuousLinearMap

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
/-- The known time swap is unitary. -/
theorem timeSwap_unitary (hK : 0 < Ks) (r : Fin Ks) :
    IsUnitary (timeSwap (n := n) (Z := Z) hK r) :=
  LookupOracle.permutationUnitary_unitary _

/-- **The payload encoding**: the six-query block-encoding input
`NativeSparseBlockEncoding.input D` (uniform slots, clean value, good flag) in flat coordinates,
placed at time address `0` by the release's `TimeDependent.timeEmbed`. -/
def payloadEncoding (hK : 0 < Ks) (D : Data (X × Fin Ks) n Z s) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ (PBasis Ks n Z) :=
  (TimeDependent.timeEmbed (B := NBasis n Z) (⟨0, hK⟩ : Fin Ks)).toContinuousLinearMap ∘L
    (NativeSparseMaskedAccess.layout (n := n) (Z := Z)).toLinearIsometry.toContinuousLinearMap ∘L
    (NativeSparseBlockEncoding.input D).toContinuousLinearMap

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
/-- The known time swap moves a payload placed at time `a` to time `swap 0 r a`. -/
theorem timeSwap_timeEmbed (hK : 0 < Ks) (r a : Fin Ks) (w : EuclideanSpace ℂ (NBasis n Z)) :
    timeSwap hK r (TimeDependent.timeEmbed a w) =
      TimeDependent.timeEmbed (Equiv.swap ⟨0, hK⟩ r a) w := by
  ext ⟨q, b⟩
  change TimeDependent.timeEmbed a w
      ((Equiv.prodCongr (Equiv.swap ⟨0, hK⟩ r) (Equiv.refl (NBasis n Z))).symm (q, b)) = _
  rw [Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map, Equiv.symm_swap,
    TimeDependent.timeEmbed_apply, TimeDependent.timeEmbed_apply]
  simp only [Equiv.swap_apply_eq_iff, Equiv.refl_symm, Equiv.refl_apply]

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
/-- A native gate in flat coordinates acts on flattened vectors as the gate itself. -/
theorem flatGate_layout
    (U : SparseFlagEmbedding.Space (n × n) Z →L[ℂ] SparseFlagEmbedding.Space (n × n) Z)
    (u : SparseFlagEmbedding.Space (n × n) Z) :
    flatGate U (NativeSparseMaskedAccess.layout u) = NativeSparseMaskedAccess.layout (U u) := by
  simp [flatGate]

/-- The payload encoding is an isometry. -/
theorem payloadEncoding_isometry (hK : 0 < Ks) (D : Data (X × Fin Ks) n Z s) :
    (payloadEncoding hK D)† ∘L payloadEncoding hK D = 1 :=
  LinearIsometry.adjoint_comp_self
    ((TimeDependent.timeEmbed (B := NBasis n Z) (⟨0, hK⟩ : Fin Ks)).comp
      ((NativeSparseMaskedAccess.layout (n := n) (Z := Z)).toLinearIsometry.comp
        (NativeSparseBlockEncoding.input D)))

/-- The represented sample `G̃_r/(s Λ)`, `Λ = D.scale` (the normalisation `α = s η` of
line 4172). -/
def sampleOperator (D : Data (X × Fin Ks) n Z s) (x : X) (r : Fin Ks) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  SparseStateOverlap.matrixOperator (fun i j => D.matrix (x, r) i j / ((s : ℂ) * D.scale))

/-- The sample norm: `‖G̃_r/(s Λ)‖ ≤ 1` (a compression of a unitary). -/
theorem sampleOperator_norm_le (D : Data (X × Fin Ks) n Z s) (x : X) (r : Fin Ks) :
    ‖sampleOperator D x r‖ ≤ 1 := by
  have hU := NativeSparseBlockEncoding.program_unitary D (x, r)
  have hUiso : ((NativeSparseBlockEncoding.program D).eval (x, r))† ∘L
      (NativeSparseBlockEncoding.program D).eval (x, r) = 1 := by
    simpa only [IsUnitary, star_eq_adjoint, mul_def] using hU.1
  have hUn : ‖(NativeSparseBlockEncoding.program D).eval (x, r)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      rw [((NativeSparseBlockEncoding.program D).eval (x, r)).norm_map_iff_adjoint_comp_self.mpr
        hUiso v, one_mul]
  have hIn : ‖(NativeSparseBlockEncoding.input D).toContinuousLinearMap‖ ≤ 1 :=
    LinearIsometry.norm_toContinuousLinearMap_le _
  have hIa : ‖(NativeSparseBlockEncoding.input D).toContinuousLinearMap†‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hIn
  rw [sampleOperator, ← NativeSparseBlockEncoding.compression D (x, r)]
  calc
    _ ≤ ‖(NativeSparseBlockEncoding.input D).toContinuousLinearMap†‖ *
        (‖(NativeSparseBlockEncoding.program D).eval (x, r)‖ *
          ‖(NativeSparseBlockEncoding.input D).toContinuousLinearMap‖) :=
      (opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (1 * 1) := by gcongr
    _ = 1 := by norm_num

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- `G̃_r = (s Λ) • (G̃_r/(s Λ))`. -/
theorem matrixOperator_eq_smul (D : Data (X × Fin Ks) n Z s) (x : X) (r : Fin Ks) :
    SparseStateOverlap.matrixOperator (D.matrix (x, r)) =
      ((s : ℝ) * D.scale) • sampleOperator D x r := by
  have hs : ((s : ℂ) * D.scale) ≠ 0 := mul_ne_zero
    (Nat.cast_ne_zero.mpr D.slots_pos.ne') (Complex.ofReal_ne_zero.mpr D.scale_pos.ne')
  have hM : D.matrix (x, r) = ((s : ℂ) * D.scale) •
      Matrix.of (fun i j => D.matrix (x, r) i j / ((s : ℂ) * D.scale)) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hs]
  have hsmul : ∀ (c : ℂ) (M : Matrix n n ℂ), SparseStateOverlap.matrixOperator (c • M) =
      c • SparseStateOverlap.matrixOperator M := by
    intro c M
    simp only [SparseStateOverlap.matrixOperator, map_smul]
  have hc : ((s : ℂ) * D.scale) = (((s : ℝ) * D.scale : ℝ) : ℂ) := by push_cast; ring
  have hr : (algebraMap ℝ ℂ ((s : ℝ) * D.scale)) • sampleOperator D x r =
      ((s : ℝ) * D.scale) • sampleOperator D x r :=
    algebraMap_smul ℂ ((s : ℝ) * D.scale) (sampleOperator D x r)
  rw [hM, hsmul]
  exact (congrArg (fun z : ℂ => z • SparseStateOverlap.matrixOperator
    (Matrix.of fun i j => D.matrix (x, r) i j / ((s : ℂ) * D.scale))) hc).trans
    hr

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
/-- **O(1)-query block encoding at a selected time** (lines 4170-4176, 4191-4193): the six-query
program `NativeSparseBlockEncoding.program D`, run coherently in the time address and
conjugated by the known time swap to address `r`, compresses to `G̃_r/(s Λ)`. -/
theorem slot_compression (hK : 0 < Ks) (D : Data (X × Fin Ks) n Z s) (x : X) (r : Fin Ks) :
    (payloadEncoding hK D)† ∘L timeSwap hK r ∘L
        TimeDependent.timeIndexed
          (fun r' => flatGate ((NativeSparseBlockEncoding.program D).eval (x, r'))) ∘L
        timeSwap hK r ∘L payloadEncoding hK D =
      sampleOperator D x r := by
  have hPe : (payloadEncoding hK D)† =
      ((NativeSparseBlockEncoding.input D).toContinuousLinearMap† ∘L
        (NativeSparseMaskedAccess.layout (n := n) (Z := Z)).toLinearIsometry.toContinuousLinearMap†) ∘L
        (TimeDependent.timeEmbed (B := NBasis n Z) (⟨0, hK⟩ : Fin Ks)).toContinuousLinearMap† := by
    rw [payloadEncoding, adjoint_comp, adjoint_comp]
  have hE : ∀ y, adjoint (TimeDependent.timeEmbed (B := NBasis n Z) (⟨0, hK⟩ : Fin Ks)).toContinuousLinearMap
      (TimeDependent.timeEmbed (B := NBasis n Z) (⟨0, hK⟩ : Fin Ks) y) = y := fun y => by
    have h := LinearIsometry.adjoint_comp_self
      (TimeDependent.timeEmbed (B := NBasis n Z) (⟨0, hK⟩ : Fin Ks))
    exact congrArg (fun A => A y) h
  have hL : ∀ u, adjoint (NativeSparseMaskedAccess.layout (n := n) (Z := Z)).toLinearIsometry.toContinuousLinearMap
      (NativeSparseMaskedAccess.layout u) = u := fun u => by
    have h := LinearIsometry.adjoint_comp_self
      (NativeSparseMaskedAccess.layout (n := n) (Z := Z)).toLinearIsometry
    exact congrArg (fun A => A u) h
  have hT : ∀ y, TimeDependent.timeIndexed
      (fun r' => flatGate ((NativeSparseBlockEncoding.program D).eval (x, r')))
      (TimeDependent.timeEmbed r y) =
      TimeDependent.timeEmbed r (flatGate ((NativeSparseBlockEncoding.program D).eval (x, r)) y) :=
    fun y => by
      simpa only [comp_apply, LinearIsometry.coe_toContinuousLinearMap] using
        congrArg (fun A => A y) (TimeDependent.timeIndexed_timeEmbed
          (fun r' => flatGate ((NativeSparseBlockEncoding.program D).eval (x, r'))) r)
  rw [hPe, sampleOperator, ← NativeSparseBlockEncoding.compression D (x, r)]
  refine ContinuousLinearMap.ext fun v => ?_
  change adjoint (NativeSparseBlockEncoding.input D).toContinuousLinearMap
      (adjoint (NativeSparseMaskedAccess.layout (n := n) (Z := Z)).toLinearIsometry.toContinuousLinearMap
        (adjoint (TimeDependent.timeEmbed (B := NBasis n Z) (⟨0, hK⟩ : Fin Ks)).toContinuousLinearMap
          (timeSwap hK r (TimeDependent.timeIndexed
            (fun r' => flatGate ((NativeSparseBlockEncoding.program D).eval (x, r')))
            (timeSwap hK r (TimeDependent.timeEmbed (⟨0, hK⟩ : Fin Ks)
              (NativeSparseMaskedAccess.layout (NativeSparseBlockEncoding.input D v)))))))) =
    adjoint (NativeSparseBlockEncoding.input D).toContinuousLinearMap
      ((NativeSparseBlockEncoding.program D).eval (x, r) (NativeSparseBlockEncoding.input D v))
  rw [timeSwap_timeEmbed, Equiv.swap_apply_left, hT, timeSwap_timeEmbed, Equiv.swap_apply_right,
    hE, flatGate_layout, hL]

end

end ODELowerBoundExtensions.Dyson
