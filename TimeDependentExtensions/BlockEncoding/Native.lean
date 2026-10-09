import TimeDependentExtensions.Hamiltonian.Native

set_option autoImplicit false

/-!
# The time-indexed block-encoding special case: the moment interface and one active layer

The paragraph "Relation to time-indexed block encodings" after Theorem `hs:thm:time`: coherent
and controlled access is supplied to Hermitian unitaries `O_r` on `K = ℂ^{B₀}` with
`J† O_r J = H̃_r / α` for a known isometry `J`. The primitive query is the controlled
time-indexed oracle `|c, r⟩ ⊗ v ↦ |c, r⟩ ⊗ O_r^c v` (`primitive`); one call counts once with
`c` and `r` in superposition.

* Equation `hs:eq:blockspecial` (`blockspecial`): with `D_{0,r} = i O_r`,
  `R_{0,r}(1) = (1 - D_{0,r})^{-1} = (1 + i O_r)/2`, `J† R_{0,r}(1) J = (1 + i H̃_r/α)/2` and
  `R_{0,r}(1)† R_{0,r}(1) = 1/2`; the moment interface therefore holds with `Q = ν = 1` and
  boundary moment `1/√2` (`endpoint_norm_le`).
* Every slot-dependent active layer of the chronological clock, with slot `k` applying
  `D_{0,σ(k)}`, is implemented with three primitive calls (`implementsOn`): the private cells
  of slot `k` carry `|1, σ(k)⟩` in the control and time registers, and the released masked
  compiler supplies the activity control from the dummy input `|0, 0⟩ ⊗ |b₀⟩`, on which every
  primitive call acts as the identity.
-/

namespace TimeDependentExtensions

namespace BlockEncoding

noncomputable section

open SparseHamiltonian SparseHamiltonian.TimeDependent ContinuousLinearMap OracleCircuit
open scoped InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000

variable {X n B₀ : Type*} [Fintype n] [DecidableEq n] [Fintype B₀] [DecidableEq B₀] {M : ℕ}

/-! ### The interface (equation `hs:eq:blockspecial`) -/

section Interface

variable {P K : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem one_sub_mul_one_add {A : Type*} [Ring A] (a : A) : (1 - a) * (1 + a) = 1 - a * a := by
  noncomm_ring

theorem one_add_mul_one_sub {A : Type*} [Ring A] (a : A) : (1 + a) * (1 - a) = 1 - a * a := by
  noncomm_ring

/-- The private action `D₀ = i O`. -/
def privateAction (O : K →L[ℂ] K) : K →L[ℂ] K := Complex.I • O

/-- The resolvent at one, `(1 + i O) / 2`. -/
def resolvent (O : K →L[ℂ] K) : K →L[ℂ] K := (2 : ℂ)⁻¹ • (1 + Complex.I • O)

/-- The block-encoded sample in units of the normalisation, `J† O J`. -/
def compressed (O : K →L[ℂ] K) (J : P →L[ℂ] K) : P →L[ℂ] P := J† ∘L O ∘L J

theorem sq_eq_one (O : K →L[ℂ] K) (hO : star O = O) (hU : IsUnitary O) : O * O = 1 := by
  have h := hU.1
  rwa [hO] at h

theorem privateAction_isometry (O : K →L[ℂ] K) (hO : star O = O) (hU : IsUnitary O) :
    (privateAction O)† ∘L privateAction O = 1 := by
  change star (Complex.I • O) * (Complex.I • O) = 1
  rw [star_smul, hO, smul_mul_smul_comm, sq_eq_one O hO hU, Complex.star_def, Complex.conj_I,
    neg_mul, Complex.I_mul_I, neg_neg, one_smul]

/-- **Equation `hs:eq:blockspecial`**, the resolvent: `(1 - i O) (1 + i O) / 2 = 1` in both
orders. -/
theorem resolvent_right (O : K →L[ℂ] K) (hO : star O = O) (hU : IsUnitary O) :
    (1 - privateAction O) ∘L resolvent O = 1 := by
  change (1 - Complex.I • O) * ((2 : ℂ)⁻¹ • (1 + Complex.I • O)) = 1
  have h : (1 - Complex.I • O) * (1 + Complex.I • O) = (2 : ℂ) • (1 : K →L[ℂ] K) := by
    rw [one_sub_mul_one_add, smul_mul_smul_comm, Complex.I_mul_I, sq_eq_one O hO hU,
      neg_one_smul, sub_neg_eq_add, two_smul]
  rw [mul_smul_comm, h, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem resolvent_left (O : K →L[ℂ] K) (hO : star O = O) (hU : IsUnitary O) :
    resolvent O ∘L (1 - privateAction O) = 1 := by
  change ((2 : ℂ)⁻¹ • (1 + Complex.I • O)) * (1 - Complex.I • O) = 1
  have h : (1 + Complex.I • O) * (1 - Complex.I • O) = (2 : ℂ) • (1 : K →L[ℂ] K) := by
    rw [one_add_mul_one_sub, smul_mul_smul_comm, Complex.I_mul_I, sq_eq_one O hO hU,
      neg_one_smul, sub_neg_eq_add, two_smul]
  rw [smul_mul_assoc, h, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- **Equation `hs:eq:blockspecial`**, the boundary block:
`J† R(1) J = (1 + i J† O J) / 2`. -/
theorem resolvent_boundary (O : K →L[ℂ] K) (J : P →L[ℂ] K) (hJ : J† ∘L J = 1) :
    J† ∘L resolvent O ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • compressed O J) := by
  rw [resolvent, compressed, smul_comp, comp_smul, add_comp, comp_add, smul_comp, comp_smul,
    show (1 : K →L[ℂ] K) ∘L J = J from ContinuousLinearMap.id_comp J, hJ]

/-- **Equation `hs:eq:blockspecial`**, the moment: `R(1)† R(1) = 1/2`. -/
theorem resolvent_moment (O : K →L[ℂ] K) (hO : star O = O) (hU : IsUnitary O) :
    (resolvent O)† ∘L resolvent O = (2 : ℂ)⁻¹ • (1 : K →L[ℂ] K) := by
  change star ((2 : ℂ)⁻¹ • (1 + Complex.I • O)) * ((2 : ℂ)⁻¹ • (1 + Complex.I • O)) = _
  have hs : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by simp
  have hIO : star (Complex.I • O) = -(Complex.I • O) := by
    rw [star_smul, hO, Complex.star_def, Complex.conj_I, neg_smul]
  have h : (1 - Complex.I • O) * (1 + Complex.I • O) = (2 : ℂ) • (1 : K →L[ℂ] K) := by
    rw [one_sub_mul_one_add, smul_mul_smul_comm, Complex.I_mul_I, sq_eq_one O hO hU,
      neg_one_smul, sub_neg_eq_add, two_smul]
  rw [star_smul, hs, star_add, star_one, hIO, ← sub_eq_add_neg, smul_mul_smul_comm, h,
    smul_smul]
  congr 1
  norm_num

theorem resolvent_norm_le (O : K →L[ℂ] K) (hU : IsUnitary O) : ‖resolvent O‖ ≤ 1 := by
  have hO1 : ‖O‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro v
    have h := (O.norm_map_iff_adjoint_comp_self.mpr hU.1) v
    rw [h, one_mul]
  unfold resolvent
  calc ‖(2 : ℂ)⁻¹ • (1 + Complex.I • O)‖ ≤ ‖(2 : ℂ)⁻¹‖ * (‖(1 : K →L[ℂ] K)‖ + ‖Complex.I • O‖) :=
        (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _))
    _ ≤ 2⁻¹ * (1 + 1) := by
        rw [norm_inv, Complex.norm_ofNat]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply add_le_add norm_id_le
        rw [norm_smul, Complex.norm_I, one_mul]
        exact hO1
    _ = 1 := by norm_num

/-- The boundary moment `‖R(1) J‖ ≤ 1/√2`. -/
theorem endpoint_norm_le (O : K →L[ℂ] K) (hO : star O = O) (hU : IsUnitary O)
    (J : P →L[ℂ] K) (hJ : J† ∘L J = 1) : ‖resolvent O ∘L J‖ ≤ Real.sqrt (1 / 2) := by
  have h2 : (resolvent O ∘L J)† ∘L (resolvent O ∘L J) = (2 : ℂ)⁻¹ • (1 : P →L[ℂ] P) := by
    rw [adjoint_comp, comp_assoc, ← comp_assoc ((resolvent O)†) (resolvent O) J,
      resolvent_moment O hO hU, smul_comp, comp_smul,
      show (1 : K →L[ℂ] K) ∘L J = J from ContinuousLinearMap.id_comp J, hJ]
  apply opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  have hinner : inner ℂ ((resolvent O ∘L J) v) ((resolvent O ∘L J) v) =
      (2 : ℂ)⁻¹ * inner ℂ v v := by
    rw [← adjoint_inner_right]
    change inner ℂ v (((resolvent O ∘L J)† ∘L (resolvent O ∘L J)) v) = _
    rw [h2, smul_apply, one_apply_eq_self, inner_smul_right]
  have hsq : ‖(resolvent O ∘L J) v‖ ^ 2 = 1 / 2 * ‖v‖ ^ 2 := by
    have h := congrArg Complex.re hinner
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    simpa [Complex.mul_re, ← Complex.ofReal_pow] using h
  have hsq' : ‖(resolvent O ∘L J) v‖ ^ 2 = (Real.sqrt (1 / 2) * ‖v‖) ^ 2 := by
    rw [hsq, mul_pow, Real.sq_sqrt (by norm_num)]
  exact le_of_eq ((sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp hsq')

theorem compressed_self_adjoint (O : K →L[ℂ] K) (hO : star O = O) (J : P →L[ℂ] K) :
    star (compressed O J) = compressed O J := by
  change (J† ∘L O ∘L J)† = J† ∘L O ∘L J
  rw [adjoint_comp, adjoint_comp, adjoint_adjoint, ← star_eq_adjoint, hO, comp_assoc]

theorem compressed_norm_le (O : K →L[ℂ] K) (hU : IsUnitary O) (J : P →L[ℂ] K)
    (hJ : J† ∘L J = 1) : ‖compressed O J‖ ≤ 1 := by
  have hJn : ‖J‖ ≤ 1 := SparseMatrixNorm.norm_le_one_of_adjoint_comp J hJ
  have hJa : ‖J†‖ ≤ 1 := by rw [LinearIsometryEquiv.norm_map]; exact hJn
  have hO1 : ‖O‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro v
    rw [(O.norm_map_iff_adjoint_comp_self.mpr hU.1) v, one_mul]
  calc ‖J† ∘L O ∘L J‖ ≤ ‖J†‖ * (‖O‖ * ‖J‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _)
          (norm_nonneg _))
    _ ≤ 1 * (1 * 1) := by gcongr
    _ = 1 := by norm_num

end Interface

/-! ### The controlled time-indexed oracle -/

/-- The register basis: control bit, time address and block-encoding basis. -/
abbrev Basis (B₀ : Type*) (M : ℕ) := (Bool × Fin M) × B₀

/-- Fixed coordinates of the controlled time-indexed register. -/
def layout (B₀ : Type*) [Fintype B₀] [DecidableEq B₀] (M : ℕ) :
    PiLp 2 (fun _ : Bool × Fin M => EuclideanSpace ℂ B₀) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Basis B₀ M) :=
  RegisterEquivalences.productFlatten (Bool × Fin M) B₀

/-- `|c, r⟩ ⊗ v ↦ |c, r⟩ ⊗ O_r^c v` in register coordinates. -/
def controlled (O : X → Fin M → EuclideanSpace ℂ B₀ →L[ℂ] EuclideanSpace ℂ B₀) (x : X) :
    PiLp 2 (fun _ : Bool × Fin M => EuclideanSpace ℂ B₀) →L[ℂ]
      PiLp 2 (fun _ : Bool × Fin M => EuclideanSpace ℂ B₀) :=
  WeightedClock.diagonal (fun c : Bool × Fin M => if c.1 then O x c.2 else 1)

/-- **The primitive query**: the controlled time-indexed block-encoding oracle. -/
def primitive (O : X → Fin M → EuclideanSpace ℂ B₀ →L[ℂ] EuclideanSpace ℂ B₀) (_l : Unit)
    (x : X) : EuclideanSpace ℂ (Basis B₀ M) →L[ℂ] EuclideanSpace ℂ (Basis B₀ M) :=
  (layout B₀ M).conjStarAlgEquiv (controlled O x)

theorem primitive_unitary (O : X → Fin M → EuclideanSpace ℂ B₀ →L[ℂ] EuclideanSpace ℂ B₀)
    (hO : ∀ x r, IsUnitary (O x r)) (l : Unit) (x : X) : IsUnitary (primitive O l x) :=
  IsUnitary.transport (CoherentQuerySchedule.diagonal_unitary _ (fun c => by
    by_cases h : c.1
    · simp only [h, if_true]; exact hO x c.2
    · simp only [h]; exact isUnitary_one)) (layout B₀ M)

/-- Place a payload at one control/time address. -/
def place (c : Bool × Fin M) :
    EuclideanSpace ℂ B₀ →ₗᵢ[ℂ] PiLp 2 (fun _ : Bool × Fin M => EuclideanSpace ℂ B₀) where
  toFun v := WithLp.toLp 2 (fun c' => if c' = c then v else 0)
  map_add' v w := by
    apply PiLp.ext
    intro c'
    by_cases h : c' = c <;> simp [h]
  map_smul' z v := by
    apply PiLp.ext
    intro c'
    by_cases h : c' = c <;> simp [h]
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2, Finset.sum_eq_single c]
    · simp
    · intro c' _ hc'
      simp [hc']
    · simp

omit [DecidableEq B₀] in
@[simp] theorem place_apply (c : Bool × Fin M) (v : EuclideanSpace ℂ B₀) (c' : Bool × Fin M) :
    place c v c' = if c' = c then v else 0 := rfl

omit [DecidableEq B₀] in
theorem controlled_place (O : X → Fin M → EuclideanSpace ℂ B₀ →L[ℂ] EuclideanSpace ℂ B₀)
    (x : X) (c : Bool × Fin M) (v : EuclideanSpace ℂ B₀) :
    controlled O x (place c v) = place c ((if c.1 then O x c.2 else 1) v) := by
  apply PiLp.ext
  intro c'
  rw [controlled, WeightedClock.diagonal_apply, place_apply, place_apply]
  by_cases h : c' = c
  · subst h
    simp
  · simp [h]

/-- The dummy input `|0, 0⟩ ⊗ |b₀⟩`. -/
def dummy (hM : 0 < M) (b₀ : B₀) : Basis B₀ M := ((false, ⟨0, hM⟩), b₀)

theorem layout_symm_single (hM : 0 < M) (b₀ : B₀) :
    (layout B₀ M).symm (EuclideanSpace.single (dummy hM b₀) (1 : ℂ)) =
      place (false, ⟨0, hM⟩) (EuclideanSpace.single b₀ (1 : ℂ)) := by
  apply PiLp.ext
  intro c
  apply PiLp.ext
  intro b
  change (RegisterEquivalences.productFlatten (Bool × Fin M) B₀).symm
    (EuclideanSpace.single (dummy hM b₀) (1 : ℂ)) c b = _
  rw [RegisterEquivalences.productFlatten_symm_apply, place_apply]
  by_cases hc : c = (false, ⟨0, hM⟩)
  · subst hc
    by_cases hb : b = b₀
    · subst hb
      simp [dummy]
    · simp [dummy, hb]
  · simp [dummy, hc]

/-- Every primitive call fixes the dummy input with phase one. -/
theorem primitive_valid (O : X → Fin M → EuclideanSpace ℂ B₀ →L[ℂ] EuclideanSpace ℂ B₀)
    (hM : 0 < M) (b₀ : B₀) (l : Unit) (x : X) :
    primitive O l x (EuclideanSpace.single (dummy hM b₀) 1) =
      EuclideanSpace.single (dummy hM b₀) 1 := by
  rw [primitive, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, layout_symm_single,
    controlled_place]
  simp only [Bool.false_eq_true, ↓reduceIte, one_apply_eq_self]
  rw [← layout_symm_single hM b₀, LinearIsometryEquiv.apply_symm_apply]

/-! ### One active layer -/

/-- The source program: one primitive call followed by the phase `i`. -/
def sourceProgram (O : X → Fin M → EuclideanSpace ℂ B₀ →L[ℂ] EuclideanSpace ℂ B₀) :
    MultiOracleCircuit.Program (primitive O) :=
  .seq (.fixed (Complex.I • (1 : EuclideanSpace ℂ (Basis B₀ M) →L[ℂ]
      EuclideanSpace ℂ (Basis B₀ M))) (by
    constructor
    · rw [star_smul, star_one, smul_mul_smul_comm, Complex.star_def, Complex.conj_I, one_mul,
        neg_mul, Complex.I_mul_I, neg_neg, one_smul]
    · rw [star_smul, star_one, smul_mul_smul_comm, Complex.star_def, Complex.conj_I, one_mul,
        mul_neg, Complex.I_mul_I, neg_neg, one_smul]))
    (.query ())

@[simp] theorem sourceProgram_count
    (O : X → Fin M → EuclideanSpace ℂ B₀ →L[ℂ] EuclideanSpace ℂ B₀) :
    (sourceProgram O).count = 1 := rfl

/-- The private cells of slot `k` carry `|1, σ k⟩` in the control and time registers. -/
def privateEmbedding (σ : ℕ → Fin M) (k : ℕ) :
    EuclideanSpace ℂ B₀ →ₗᵢ[ℂ] NativeMaskedOracle.Logical PUnit.{1} (Basis B₀ M) :=
  FlatMaskedAccess.singleton ((layout B₀ M).toLinearIsometry.comp (place (true, σ k)))

/-- An isometry from its adjoint relation. -/
def isometryOf {P K : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (J : P →L[ℂ] K) (hJ : J† ∘L J = 1) : P →ₗᵢ[ℂ] K where
  toLinearMap := J.toLinearMap
  norm_map' := (J.norm_map_iff_adjoint_comp_self.mpr hJ)

/-- Public cells are never acted on; they use the address `|0, 0⟩` and the boundary `J`. -/
def publicEmbedding (hM : 0 < M) (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ B₀)
    (hJ : J† ∘L J = 1) : EuclideanSpace ℂ n →ₗᵢ[ℂ] EuclideanSpace ℂ (Basis B₀ M) :=
  (layout B₀ M).toLinearIsometry.comp ((place (false, ⟨0, hM⟩)).comp (isometryOf J hJ))

/-- The full native workspace of the block-encoding clock. -/
abbrev Physical (B₀ : Type*) [Fintype B₀] (M T d : ℕ) :=
  NativeMaskedOracle.Physical (ActiveRegisterLayout.Label PUnit.{1} T d) (Basis B₀ M)

/-- The controlled time-indexed oracle with untouched spectator registers. -/
abbrev oracle (O : X → Fin M → EuclideanSpace ℂ B₀ →L[ℂ] EuclideanSpace ℂ B₀) (T d : ℕ) :
    Unit → X → Physical B₀ M T d →L[ℂ] Physical B₀ M T d :=
  NativeWholeProgramActive.oracle (C := PUnit.{1}) (primitive O) T d

theorem oracle_unitary (O : X → Fin M → EuclideanSpace ℂ B₀ →L[ℂ] EuclideanSpace ℂ B₀)
    (hO : ∀ x r, IsUnitary (O x r)) (T d : ℕ) (l : Unit) (x : X) :
    IsUnitary (oracle O T d l x) :=
  NativeMaskedOracle.oracle_unitary (primitive O l) (fun x => primitive_unitary O hO l x) x

/-- The fixed logical-to-physical encoding. -/
def embedding (hM : 0 < M) (b₀ : B₀) (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ B₀)
    (hJ : J† ∘L J = 1) (σ : ℕ → Fin M) (T d : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := EuclideanSpace ℂ n)
      (V := ChronologicalResolvent.BlockOperator.H T (EuclideanSpace ℂ B₀)) d)
      →ₗᵢ[ℂ] Physical B₀ M T d :=
  cleanInputV (C := PUnit.{1}) (publicEmbedding hM J hJ) (privateEmbedding σ) (dummy hM b₀) T d

omit [DecidableEq n] in
/-- **One active layer with three primitive calls.** Every slot-dependent active layer of the
chronological clock with private actions `i O_{σ k}` has an exact clean implementation with
three controlled time-indexed queries. -/
theorem implementsOn (O : X → Fin M → EuclideanSpace ℂ B₀ →L[ℂ] EuclideanSpace ℂ B₀)
    (hO : ∀ x r, IsUnitary (O x r)) (hM : 0 < M) (b₀ : B₀)
    (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ B₀) (hJ : J† ∘L J = 1)
    (σ : ℕ → Fin M) (T d r : ℕ) :
    LabeledEncodedOracle.ImplementsOn (oracle O T d)
      (fun x => activeClockV (P := EuclideanSpace ℂ n)
        (fun k => privateAction (O x (σ k))) T d r)
      (embedding hM b₀ J hJ σ T d).toContinuousLinearMap 3 := by
  have hClean : ∀ x k, WeightedClock.diagonal (fun _ : PUnit.{1} => (sourceProgram O).eval x) ∘L
      (privateEmbedding σ k).toContinuousLinearMap =
        (privateEmbedding σ k).toContinuousLinearMap ∘L privateAction (O x (σ k)) := by
    intro x k
    apply FlatMaskedAccess.singleton_intertwines
    apply ContinuousLinearMap.ext
    intro v
    simp only [comp_apply, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.coe_comp,
      Function.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry]
    rw [sourceProgram, MultiOracleCircuit.Program.eval_seq,
      MultiOracleCircuit.Program.eval_fixed, MultiOracleCircuit.Program.eval_query,
      mul_apply_eq_comp, primitive, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.symm_apply_apply, controlled_place]
    simp only [↓reduceIte, smul_apply, one_apply_eq_self, privateAction]
    rw [← LinearIsometryEquiv.map_smul, ← LinearIsometry.map_smul]
  have h := clean_implementsOnV (C := PUnit.{1}) (primitive O)
    (fun l x => primitive_unitary O hO l x) (dummy hM b₀) (fun _ _ => dummy hM b₀)
    (fun l x => primitive_valid O hM b₀ l x) (sourceProgram O) (publicEmbedding hM J hJ)
    (privateEmbedding σ) (fun x k => privateAction (O x (σ k))) hClean T d r
  rw [sourceProgram_count] at h
  exact h

end

end BlockEncoding

end TimeDependentExtensions
