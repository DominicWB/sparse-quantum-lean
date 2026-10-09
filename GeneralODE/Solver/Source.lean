import GeneralODE.Solver.Interface
import GeneralODE.Analysis.HistorySolution

/-!
# Exact preparation of the history right-hand side

The right-hand side of the history system is `(μ b, x₀, 0, …, 0)` on the slots
`(forcing, 0, 1, …, 2m)`.  It is prepared exactly from `|0⟩ ⊗ seed` by a fixed
rotation of the slot register to the public weights `(‖x₀‖, μ‖b‖)/r`,
followed by one call of each supplied source preparation, controlled on its
slot.  No amplitude amplification is needed, since both weights are public.

The two source oracles act on the system register of the history space,
controlled on the slot register, with every other register a spectator:
label `false` applies `J₀` on slot `0`, label `true` applies `J_b` on the
forcing slot.  Every other slot is left unchanged; in particular a basis
vector with any other slot is fixed, as required by the native control
compiler.
-/

namespace SparseHamiltonian.GeneralODE.Solver

noncomputable section
open ContinuousLinearMap OracleCircuit Registers History
open scoped InnerProduct BigOperators ComplexConjugate
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

variable {n a X : Type} [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a] {m : ℕ}

/-- The slot carrying the initial value. -/
def slot0 (m : ℕ) : Slot m := some ⟨0, by omega⟩

theorem slot0_ne_none (m : ℕ) : slot0 m ≠ none := by simp [slot0]

/-- `J` on the system register when the slot register equals `tgt`. -/
def slotControlled (tgt : Slot m) (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    EuclideanSpace ℂ (Slot m × n) →L[ℂ] EuclideanSpace ℂ (Slot m × n) :=
  selMap (fun s => if s = tgt then J else 1)

omit [DecidableEq n] in
theorem slotControlled_unitary (tgt : Slot m) (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : IsUnitary J) : IsUnitary (slotControlled tgt J) :=
  selMap_unitary _ (fun s => by by_cases h : s = tgt <;> simp [h, hJ])

omit [DecidableEq n] in
theorem slotControlled_apply (tgt : Slot m) (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (w : EuclideanSpace ℂ (Slot m × n)) (s : Slot m) (i : n) :
    slotControlled tgt J w (s, i) =
      if s = tgt then J (slice w s) i else w (s, i) := by
  unfold slotControlled
  rw [selMap_apply]
  by_cases h : s = tgt <;> simp [h]

/-- The two source oracles on the solver's oracle register. -/
def sourceOracle (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    Bool → X → EuclideanSpace ℂ ((Slot m × n) × a) →L[ℂ] EuclideanSpace ℂ ((Slot m × n) × a) :=
  fun b x => actLeft (α := a)
    (if b then slotControlled (none : Slot m) (Jb x) else slotControlled (slot0 m) (J₀ x))

omit [DecidableEq n] [DecidableEq a] in
theorem sourceOracle_unitary (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x)) (b : Bool) (x : X) :
    IsUnitary (sourceOracle (m := m) (a := a) J₀ Jb b x) := by
  unfold sourceOracle actLeft
  apply isUnitary_map
  cases b
  · exact slotControlled_unitary _ _ (hJ₀ x)
  · exact slotControlled_unitary _ _ (hJb x)

/-- Basis vectors with a slot different from `0` and from the forcing slot are fixed. -/
theorem sourceOracle_single (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (s : Slot m) (hs0 : s ≠ slot0 m) (hsn : s ≠ none) (i : n) (c : a) (b : Bool) (x : X) :
    sourceOracle (m := m) (a := a) J₀ Jb b x (EuclideanSpace.single ((s, i), c) 1) =
      EuclideanSpace.single ((s, i), c) 1 := by
  ext ⟨⟨s', i'⟩, c'⟩
  unfold sourceOracle
  rw [actLeft_apply]
  have hcase : ∀ (tgt : Slot m) (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n), s ≠ tgt →
      slotControlled tgt J (WithLp.toLp 2 (fun b' => (EuclideanSpace.single ((s, i), c) (1 : ℂ) :
        EuclideanSpace ℂ ((Slot m × n) × a)) (b', c'))) (s', i') =
        (EuclideanSpace.single ((s, i), c) (1 : ℂ) : EuclideanSpace ℂ ((Slot m × n) × a))
          ((s', i'), c') := by
    intro tgt J hne
    rw [slotControlled_apply]
    by_cases hs' : s' = tgt
    · rw [if_pos hs']
      have hz : slice (WithLp.toLp 2 (fun b' => (EuclideanSpace.single ((s, i), c) (1 : ℂ) :
          EuclideanSpace ℂ ((Slot m × n) × a)) (b', c'))) s' = 0 := by
        ext j
        simp only [slice_apply, PiLp.zero_apply]
        rw [PiLp.single_apply]
        rw [if_neg]
        intro h
        apply hne
        rw [← hs']
        exact (congrArg (fun p => p.1.1) h).symm
      rw [hz, map_zero, PiLp.zero_apply, PiLp.single_apply, if_neg]
      intro h
      apply hne
      rw [← hs']
      exact (congrArg (fun p => p.1.1) h).symm
    · rw [if_neg hs']
  cases b
  · exact hcase _ _ hs0
  · exact hcase _ _ hsn

/-- Public slot weights `(‖x₀‖ |0⟩ + μ‖b‖ |forcing⟩)/r`. -/
def slotWeights (m : ℕ) (μ r₀ rb : ℝ) : EuclideanSpace ℂ (Slot m) :=
  (((r₀ / Real.sqrt (μ ^ 2 * rb ^ 2 + r₀ ^ 2) : ℝ) : ℂ) • EuclideanSpace.single (slot0 m) 1) +
    (((μ * rb / Real.sqrt (μ ^ 2 * rb ^ 2 + r₀ ^ 2) : ℝ) : ℂ) • EuclideanSpace.single none 1)

theorem slotWeights_apply (μ r₀ rb : ℝ) (s : Slot m) :
    slotWeights m μ r₀ rb s =
      (if s = slot0 m then ((r₀ / Real.sqrt (μ ^ 2 * rb ^ 2 + r₀ ^ 2) : ℝ) : ℂ) else 0) +
        (if s = none then ((μ * rb / Real.sqrt (μ ^ 2 * rb ^ 2 + r₀ ^ 2) : ℝ) : ℂ) else 0) := by
  simp [slotWeights, PiLp.single_apply]

theorem slotWeights_norm (μ r₀ rb : ℝ) (hr : 0 < μ ^ 2 * rb ^ 2 + r₀ ^ 2) :
    ‖slotWeights m μ r₀ rb‖ = 1 := by
  have hn : (none : Slot m) ≠ slot0 m := (slot0_ne_none m).symm
  have hsq : ‖slotWeights m μ r₀ rb‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_option, slotWeights_apply, if_neg hn, if_pos rfl,
      zero_add]
    rw [Finset.sum_eq_single ⟨0, by omega⟩]
    · have h1 : (some (⟨0, by omega⟩ : Fin (2 * m + 1)) : Slot m) = slot0 m := rfl
      rw [slotWeights_apply, if_pos h1, if_neg (by simp), add_zero]
      rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
        div_pow, div_pow, Real.sq_sqrt hr.le, mul_pow]
      field_simp
    · intro j _ hj
      have hj0 : (some j : Slot m) ≠ slot0 m := by
        intro h; apply hj; unfold slot0 at h; exact Option.some_injective _ h
      rw [slotWeights_apply, if_neg hj0, if_neg (by simp), add_zero, norm_zero]
      norm_num
    · simp
  have h0 : 0 ≤ ‖slotWeights m μ r₀ rb‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖slotWeights m μ r₀ rb‖ - 1)]

/-- A fixed slot rotation `|0⟩ ↦ slotWeights`. -/
def slotRotation (m : ℕ) (μ r₀ rb : ℝ) (hr : 0 < μ ^ 2 * rb ^ 2 + r₀ ^ 2) :
    EuclideanSpace ℂ (Slot m) →L[ℂ] EuclideanSpace ℂ (Slot m) :=
  Classical.choose (exists_unitary_single (slot0 m) (slotWeights m μ r₀ rb)
    (slotWeights_norm μ r₀ rb hr))

theorem slotRotation_spec (μ r₀ rb : ℝ) (hr : 0 < μ ^ 2 * rb ^ 2 + r₀ ^ 2) :
    IsUnitary (slotRotation m μ r₀ rb hr) ∧
      slotRotation m μ r₀ rb hr (EuclideanSpace.single (slot0 m) 1) = slotWeights m μ r₀ rb :=
  Classical.choose_spec (exists_unitary_single (slot0 m) (slotWeights m μ r₀ rb)
    (slotWeights_norm μ r₀ rb hr))

/-- The rotation acting on the slot register of the oracle register. -/
def rotationGate (m : ℕ) (a : Type) [Fintype a] (n : Type) [Fintype n]
    (μ r₀ rb : ℝ) (hr : 0 < μ ^ 2 * rb ^ 2 + r₀ ^ 2) :
    EuclideanSpace ℂ ((Slot m × n) × a) →L[ℂ] EuclideanSpace ℂ ((Slot m × n) × a) :=
  actLeft (α := a) (actLeft (α := n) (slotRotation m μ r₀ rb hr))

omit [DecidableEq n] [DecidableEq a] in
theorem rotationGate_unitary (μ r₀ rb : ℝ) (hr : 0 < μ ^ 2 * rb ^ 2 + r₀ ^ 2) :
    IsUnitary (rotationGate m a n μ r₀ rb hr) :=
  isUnitary_map _ (isUnitary_map _ (slotRotation_spec μ r₀ rb hr).1)

/-- The preparation program: rotation, then the initial and forcing calls. -/
def prepProgram (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (μ r₀ rb : ℝ) (hr : 0 < μ ^ 2 * rb ^ 2 + r₀ ^ 2) :
    MultiOracleCircuit.Program (sourceOracle (m := m) (a := a) J₀ Jb) :=
  .seq (.query true) (.seq (.query false) (.fixed _ (rotationGate_unitary μ r₀ rb hr)))

omit [DecidableEq n] [DecidableEq a] in
@[simp] theorem prepProgram_count (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (μ r₀ rb : ℝ) (hr : 0 < μ ^ 2 * rb ^ 2 + r₀ ^ 2) :
    (prepProgram (m := m) (a := a) J₀ Jb μ r₀ rb hr).count = 2 := rfl

omit [DecidableEq n] [DecidableEq a] in
theorem prepProgram_cost (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (μ r₀ rb : ℝ) (hr : 0 < μ ^ 2 * rb ^ 2 + r₀ ^ 2) (w : Bool → ℕ) :
    (prepProgram (m := m) (a := a) J₀ Jb μ r₀ rb hr).cost w = w true + (w false + 0) := rfl

/-- The fixed input `|0⟩ ⊗ seed` of the solver. -/
def sourceSeed (m : ℕ) (seed : EuclideanSpace ℂ n) : EuclideanSpace ℂ (Slot m × n) :=
  ketL (EuclideanSpace.single (slot0 m) 1) seed

omit [DecidableEq n] in
theorem sourceSeed_norm (seed : EuclideanSpace ℂ n) (hseed : ‖seed‖ = 1) :
    ‖sourceSeed m seed‖ = 1 := by
  unfold sourceSeed
  have h := ketL_isometry (ν := n) (EuclideanSpace.single (slot0 m) (1 : ℂ)) (by simp)
  rw [(ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr h seed, hseed]

/-- The flattened history right-hand side. -/
def rhsVector (m : ℕ) (μ : ℝ) (x0 b : EuclideanSpace ℂ n) : EuclideanSpace ℂ (Slot m × n) :=
  RegisterEquivalences.productFlatten (Slot m) n (rhs m μ x0 b)

omit [DecidableEq n] in
theorem rhsVector_apply (μ : ℝ) (x0 b : EuclideanSpace ℂ n) (s : Slot m) (i : n) :
    rhsVector m μ x0 b (s, i) =
      if s = none then (μ : ℂ) * b i else if s = slot0 m then x0 i else 0 := by
  unfold rhsVector
  change rhs m μ x0 b s i = _
  rcases s with _ | ⟨j, hj⟩
  · simp [rhs]
  · have hn : (some (⟨j, hj⟩ : Fin (2 * m + 1)) : Slot m) ≠ none := by simp
    rw [if_neg hn]
    by_cases h0 : j = 0
    · subst h0
      simp [rhs, slot0]
    · have : (some (⟨j, hj⟩ : Fin (2 * m + 1)) : Slot m) ≠ slot0 m := by
        intro h; apply h0; unfold slot0 at h
        exact congrArg Fin.val (Option.some_injective _ h)
      rw [if_neg this]
      simp [rhs, h0]

omit [DecidableEq n] in
theorem norm_rhsVector (μ : ℝ) (x0 b : EuclideanSpace ℂ n) (hμ : 0 ≤ μ) :
    ‖rhsVector m μ x0 b‖ = Real.sqrt (μ ^ 2 * ‖b‖ ^ 2 + ‖x0‖ ^ 2) := by
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (norm_nonneg _), ← sq]
  unfold rhsVector
  rw [LinearIsometryEquiv.norm_map, PiLp.norm_sq_eq_of_L2 _ (rhs m μ x0 b), Fintype.sum_option]
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · simp [rhs, norm_smul, mul_pow, abs_of_nonneg hμ]
  · intro j _ hj
    have hj' : j ≠ 0 := fun h => hj (by rw [h]; rfl)
    simp [rhs, hj']
  · simp

omit [DecidableEq n] in
/-- The preparation maps `(|0⟩ ⊗ seed) ⊗ |a₀⟩` to the normalized right-hand side. -/
theorem prepProgram_eval (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (μ r₀ rb : ℝ) (hr : 0 < μ ^ 2 * rb ^ 2 + r₀ ^ 2)
    (seed x0 b : EuclideanSpace ℂ n) (x : X) (h₀ : ‖x0‖ = r₀) (hb : ‖b‖ = rb)
    (hJ₀ : x0 ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection x0)
    (hJb : b ≠ 0 → Jb x seed = ODEStateNormalization.unitDirection b) (a₀ : a) :
    (prepProgram (m := m) (a := a) J₀ Jb μ r₀ rb hr).eval x (embed a₀ (sourceSeed m seed)) =
      embed a₀ (((Real.sqrt (μ ^ 2 * rb ^ 2 + r₀ ^ 2))⁻¹ : ℝ) • rhsVector m μ x0 b) := by
  set r := Real.sqrt (μ ^ 2 * rb ^ 2 + r₀ ^ 2) with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.mpr hr
  -- every gate acts on the left factor, hence commutes with `embed`
  change sourceOracle J₀ Jb true x (sourceOracle J₀ Jb false x
    (rotationGate m a n μ r₀ rb hr (ketR (EuclideanSpace.single a₀ 1) (sourceSeed m seed)))) =
      ketR (EuclideanSpace.single a₀ 1) _
  unfold sourceOracle rotationGate
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [actLeft_ketR, actLeft_ketR, actLeft_ketR]
  congr 1
  -- the slot rotation on `|0⟩ ⊗ seed`
  have hrot : actLeft (α := n) (slotRotation m μ r₀ rb hr) (sourceSeed m seed) =
      ketL (slotWeights m μ r₀ rb) seed := by
    ext ⟨s, i⟩
    rw [actLeft_apply]
    have hv : (WithLp.toLp 2 (fun s' => sourceSeed m seed (s', i)) : EuclideanSpace ℂ (Slot m)) =
        seed i • EuclideanSpace.single (slot0 m) 1 := by
      ext s'
      simp [sourceSeed, mul_comm]
    rw [hv, map_smul, (slotRotation_spec μ r₀ rb hr).2]
    simp [mul_comm]
  rw [hrot]
  have hn0 : (none : Slot m) ≠ slot0 m := (slot0_ne_none m).symm
  have hv1 : ∀ s i, slotControlled (slot0 m) (J₀ x) (ketL (slotWeights m μ r₀ rb) seed) (s, i) =
      slotWeights m μ r₀ rb s * (if s = slot0 m then J₀ x seed i else seed i) := by
    intro s i
    rw [slotControlled_apply]
    have hsl : slice (ketL (slotWeights m μ r₀ rb) seed) s = slotWeights m μ r₀ rb s • seed := by
      ext j; simp
    by_cases h : s = slot0 m
    · rw [if_pos h, if_pos h, hsl, map_smul]; simp
    · rw [if_neg h, if_neg h]; simp
  have hsl1 : slice (slotControlled (slot0 m) (J₀ x) (ketL (slotWeights m μ r₀ rb) seed)) none =
      slotWeights m μ r₀ rb none • seed := by
    ext j
    rw [slice_apply, hv1, if_neg hn0]; simp
  ext ⟨s, i⟩
  rw [slotControlled_apply, PiLp.smul_apply, rhsVector_apply]
  by_cases hs : s = none
  · subst hs
    rw [if_pos rfl, if_pos rfl, hsl1, map_smul, slotWeights_apply, if_neg hn0, if_pos rfl, zero_add]
    simp only [PiLp.smul_apply, smul_eq_mul, Complex.real_smul]
    by_cases hb0 : b = 0
    · have hrb : rb = 0 := by rw [← hb, hb0, norm_zero]
      subst hb0
      simp [hrb]
    · rw [hJb hb0, ODEStateNormalization.unitDirection]
      simp only [PiLp.smul_apply, Complex.real_smul, hb]
      have hrb : 0 < rb := by rw [← hb]; exact norm_pos_iff.mpr hb0
      have hrb' : (rb : ℂ) ≠ 0 := by exact_mod_cast hrb.ne'
      have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
      simp only [← hrdef]
      push_cast
      field_simp
  · rw [if_neg hs, if_neg hs, hv1]
    by_cases h0 : s = slot0 m
    · subst h0
      rw [if_pos rfl, if_pos rfl, slotWeights_apply, if_pos rfl, if_neg (slot0_ne_none m), add_zero]
      simp only [Complex.real_smul]
      by_cases hx0 : x0 = 0
      · have hr₀ : r₀ = 0 := by rw [← h₀, hx0, norm_zero]
        subst hx0
        simp [hr₀]
      · rw [hJ₀ hx0, ODEStateNormalization.unitDirection]
        simp only [PiLp.smul_apply, Complex.real_smul, h₀]
        have hr₀ : 0 < r₀ := by rw [← h₀]; exact norm_pos_iff.mpr hx0
        have hr₀' : (r₀ : ℂ) ≠ 0 := by exact_mod_cast hr₀.ne'
        have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
        simp only [← hrdef]
        push_cast
        field_simp
    · rw [if_neg h0, if_neg h0, slotWeights_apply, if_neg h0, if_neg hs]
      simp

end

end SparseHamiltonian.GeneralODE.Solver
