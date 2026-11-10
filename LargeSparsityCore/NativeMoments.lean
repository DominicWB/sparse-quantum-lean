import LargeSparsityCore.NativeOperators

set_option autoImplicit false

/-!
# The known boundary of the joint representation and its moments

The known input (`Jin`) is the public slot preparation on both orientations
(`SparseHamiltonian.FixedLocatorConjugation.fixedBoundary`), with a clean value word and the flag
state `(|0⟩ + |2⟩)/√2`: one half of the boundary enters the correction factor (flag `0`), the
other half the clipped edge generator (flag `2`). This is the boundary `J = (J₀, J_c)/√2` of
`opt:eq:joint-lift`, with both parts sharing the same edge register.

In the frame `𝒰(x)`, the input becomes, at the computed word `z = t_e` of every edge `e`,
`ψ_e = (flagRot(c₂) (|0⟩ + |2⟩)/√2) ⊗ V(c₂)† y_e` with `y_e` the edge-`e` part of the sparse
boundary `J₀ v` (`frame_input_apply`). Since the private operators are diagonal in the frame,
every compressed moment is a sum over the edges of local expressions:

* `J† K J = H/α` with `α = sη/q` (`compression`, `opt:eq:joint-moments`);
* `‖P_± J‖² ≤ β/(2s)` (`norm_Ppl_input_sq_le`, `norm_Pmi_input_sq_le`, `opt:eq:isolated-weights`);
* `‖K P₀ J‖² ≤ 2q²/s` (`norm_bulk_input_sq_le`) and `‖K J‖² ≤ 2q²(1 + β)/s`
  (`norm_K_input_sq_le`).
-/

namespace LargeSparsityCore.Native

noncomputable section

open ContinuousLinearMap SparseHamiltonian NativeSignedFactor OrientedNativeLayout
open NativeSparseBlockEncoding OracleCircuit CayleyBlocks SparseEdgeMoments
open scoped InnerProduct ComplexConjugate

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

/-! ### The known input -/

/-- The flag amplitudes `(|0⟩ + |2⟩)/√2`. -/
def phi (f : Fin 3) : ℂ := if f = 1 then 0 else r2

/-- Clean value word, flag state `phi`, both orientations. -/
def cleanF : OrientedSpace n →L[ℂ] Space n Z :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 (fun b : Bool => WithLp.toLp 2
        (fun a : NativeSparseMaskedAccess.Basis n Z =>
          if a.1.2 = 0 then phi a.2 * OrientedEdgeCayley.regroup w a.1.1 b else 0))
      map_add' := by
        intro w w'
        ext b a
        simp only [map_add, PiLp.add_apply]
        split_ifs <;> ring
      map_smul' := by
        intro c w
        ext b a
        simp only [map_smul, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> ring }

omit [DecidableEq n] in
@[simp] theorem cleanF_apply (w : OrientedSpace n) (b : Bool) (e : n × n) (z : Z) (f : Fin 3) :
    cleanF w b ((e, z), f) =
      if z = 0 then phi f * OrientedEdgeCayley.regroup w e b else 0 := rfl

theorem norm_r2_sq : ‖r2‖ ^ 2 = 1 / 2 := by
  rw [r2, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

omit [DecidableEq n] in
/-- The clean flagged encoding is an isometry. -/
theorem norm_cleanF (w : OrientedSpace n) : ‖(cleanF (Z := Z) w)‖ = ‖w‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← OrientedEdgeCayley.regroup.norm_map w, PiLp.norm_sq_eq_of_L2,
    PiLp.norm_sq_eq_of_L2]
  have hin : ∀ b : Bool, ‖(cleanF (Z := Z) w) b‖ ^ 2 =
      ∑ e : n × n, ‖OrientedEdgeCayley.regroup w e b‖ ^ 2 := by
    intro b
    rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_eq_single (0 : Z)]
    · rw [Fin.sum_univ_three]
      simp only [cleanF_apply, if_true, phi, norm_mul]
      simp only [Fin.isValue, Fin.reduceEq, if_false, norm_zero, zero_mul]
      have h := norm_r2_sq
      simp only [mul_pow, h]
      ring
    · intro z _ hz
      apply Finset.sum_eq_zero
      intro f _
      simp [cleanF_apply, hz]
    · intro h
      exact absurd (Finset.mem_univ _) h
  simp only [hin]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [PiLp.norm_sq_eq_of_L2]

/-- The known input `J`: the public slot preparation, clean value word, flag state `phi`. -/
def Jin (D : Data X n Z s) : EuclideanSpace ℂ n →L[ℂ] Space n Z :=
  cleanF ∘L FixedLocatorConjugation.fixedBoundary D.slot

theorem Jin_isometry (D : Data X n Z s) : (Jin D)† ∘L Jin D = 1 := by
  apply (norm_map_iff_adjoint_comp_self (Jin D)).mp
  intro v
  rw [Jin, comp_apply, norm_cleanF]
  exact (norm_map_iff_adjoint_comp_self _).mpr
    (FixedLocatorConjugation.fixedBoundary_isometry D.slot D.slots_pos) v

/-! ### The frame applied to the input -/

set_option maxRecDepth 8192 in
/-- The locators act on the edge register of the flagged clean encoding. -/
theorem locator_cleanF (D : Data X n Z s) (x : X) (w : OrientedSpace n) :
    (locatorProgram D).eval x (cleanF w) = cleanF (FixedLocatorConjugation.locator D x w) := by
  ext b a
  rcases a with ⟨⟨e, z⟩, f⟩
  cases b
  · change D.rowOracle x (WithLp.toLp 2 (fun j => cleanF w false ((j, z), f))) e = _
    have hs : (WithLp.toLp 2 (fun j : n × n => cleanF (Z := Z) w false ((j, z), f)) :
        EdgeSpace n) = (if z = 0 then phi f else 0) • FixedLocatorConjugation.leftPart w := by
      ext j
      simp only [cleanF_apply, OrientedEdgeCayley.regroup_false, PiLp.smul_apply, smul_eq_mul,
        FixedLocatorConjugation.leftPart]
      split_ifs <;> simp
    rw [hs, map_smul, cleanF_apply, OrientedEdgeCayley.regroup_false,
      FixedLocatorConjugation.locator, FixedLocatorConjugation.block_inl]
    simp only [PiLp.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  · change D.columnOracle x (WithLp.toLp 2 (fun j => cleanF w true ((j, z), f))) e = _
    have hs : (WithLp.toLp 2 (fun j : n × n => cleanF (Z := Z) w true ((j, z), f)) :
        EdgeSpace n) = (if z = 0 then phi f else 0) • FixedLocatorConjugation.rightPart w := by
      ext j
      simp only [cleanF_apply, OrientedEdgeCayley.regroup_true, PiLp.smul_apply, smul_eq_mul,
        FixedLocatorConjugation.rightPart]
      split_ifs <;> simp
    rw [hs, map_smul, cleanF_apply, OrientedEdgeCayley.regroup_true,
      FixedLocatorConjugation.locator, FixedLocatorConjugation.block_inr]
    simp only [PiLp.smul_apply, smul_eq_mul]
    split_ifs <;> simp

theorem value_cleanF_apply (D : Data X n Z s) (x : X) (w : OrientedSpace n) (b : Bool)
    (e : n × n) (z : Z) (f : Fin 3) :
    logicalOracle D .value x (cleanF w) b ((e, z), f) =
      if z = D.table x e then phi f * OrientedEdgeCayley.regroup w e b else 0 := by
  rw [logical_value_apply, cleanF_apply]
  simp only [sub_eq_zero]

/-- The flag amplitudes after the local gate, `flagRot(c) phi`. -/
def gflag (c : ℂ) (f : Fin 3) : ℂ := ∑ f', flagRot c f f' * phi f'

theorem gflag_zero (c : ℂ) : gflag c 0 = r2 * amp c := by
  simp [gflag, Fin.sum_univ_three, flagRot, phi]
  ring

theorem gflag_one (c : ℂ) : gflag c 1 = r2 * fam c := by
  simp [gflag, Fin.sum_univ_three, flagRot, phi]
  ring

theorem gflag_two (c : ℂ) : gflag c 2 = r2 := by
  simp [gflag, Fin.sum_univ_three, flagRot, phi]

/-- The sparse boundary vector `J₀ v` at an edge, as an orientation qubit. -/
def yv (D : Data X n Z s) (x : X) (v : EuclideanSpace ℂ n) (e : n × n) : Qubit :=
  OrientedEdgeCayley.regroup (boundary (D.rowloc x) (D.colloc x) v) e

set_option maxRecDepth 8192 in
/-- **The input in the frame.** -/
theorem frame_input_apply (D : Data X n Z s) (η β : ℝ) (x : X) (v : EuclideanSpace ℂ n)
    (b : Bool) (e : n × n) (z : Z) (f : Fin 3) :
    U D η β x (Jin D v) b ((e, z), f) =
      if z = D.table x e then
        gflag (c2 D η β (e, z)) f * Ocl (c2 D η β (e, z)) (yv D x v e) b else 0 := by
  have hL : (locatorProgram D).eval x (Jin D v) =
      cleanF (boundary (D.rowloc x) (D.colloc x) v) := by
    rw [Jin, comp_apply, locator_cleanF, ← comp_apply (FixedLocatorConjugation.locator D x),
      FixedLocatorConjugation.locator_boundary]
  change frame D η β (logicalOracle D .value x ((locatorProgram D).eval x (Jin D v))) b
    ((e, z), f) = _
  rw [hL, frame_apply]
  simp only [value_cleanF_apply]
  split_ifs with hz
  · rw [Ocl_apply, gflag, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b' _
    apply Finset.sum_congr rfl
    intro f' _
    rw [yv]
    ring
  · simp

/-! ### Sums over the computed words -/

omit [DecidableEq n] [AddCommGroup Z] in
/-- Inner products of two vectors supported on the words `z = t e`. -/
theorem inner_supported (t : n × n → Z) (u w : Space n Z) (A B : Bool → n × n → Fin 3 → ℂ)
    (hu : ∀ b e z f, u b ((e, z), f) = if z = t e then A b e f else 0)
    (hw : ∀ b e z f, w b ((e, z), f) = if z = t e then B b e f else 0) :
    inner ℂ u w = ∑ b, ∑ e, ∑ f, conj (A b e f) * B b e f := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro b _
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_eq_single (t e)]
  · apply Finset.sum_congr rfl
    intro f _
    rw [hu, hw, if_pos rfl, if_pos rfl, RCLike.inner_apply]
    ring
  · intro z _ hz
    apply Finset.sum_eq_zero
    intro f _
    rw [hu, hw, if_neg hz, if_neg hz, RCLike.inner_apply]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [DecidableEq n] [AddCommGroup Z] in
/-- Norms of vectors supported on the words `z = t e`. -/
theorem norm_sq_supported (t : n × n → Z) (u : Space n Z) (A : Bool → n × n → Fin 3 → ℂ)
    (hu : ∀ b e z f, u b ((e, z), f) = if z = t e then A b e f else 0) :
    ‖u‖ ^ 2 = ∑ b, ∑ e, ∑ f, ‖A b e f‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro b _
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_eq_single (t e)]
  · apply Finset.sum_congr rfl
    intro f _
    rw [hu, if_pos rfl]
  · intro z _ hz
    apply Finset.sum_eq_zero
    intro f _
    rw [hu, if_neg hz]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The component of the input in the frame at the computed word. -/
def Psi (D : Data X n Z s) (η β : ℝ) (x : X) (v : EuclideanSpace ℂ n) (b : Bool) (e : n × n)
    (f : Fin 3) : ℂ :=
  gflag (c2 D η β (e, D.table x e)) f * Ocl (c2 D η β (e, D.table x e)) (yv D x v e) b

theorem frame_input_eq (D : Data X n Z s) (η β : ℝ) (x : X) (v : EuclideanSpace ℂ n)
    (b : Bool) (e : n × n) (z : Z) (f : Fin 3) :
    U D η β x (Jin D v) b ((e, z), f) = if z = D.table x e then Psi D η β x v b e f else 0 := by
  rw [frame_input_apply]
  split_ifs with hz
  · subst hz
    rfl
  · rfl

theorem dg_frame_input_eq (D : Data X n Z s) (η β : ℝ) (x : X) (m : Bool → Adr n Z → Fin 3 → ℂ)
    (v : EuclideanSpace ℂ n) (b : Bool) (e : n × n) (z : Z) (f : Fin 3) :
    dg m (U D η β x (Jin D v)) b ((e, z), f) =
      if z = D.table x e then m b (e, D.table x e) f * Psi D η β x v b e f else 0 := by
  rw [dg_apply, frame_input_eq]
  split_ifs with hz
  · subst hz
    rfl
  · simp

/-- Compressed diagonal operators as sums over the edges. -/
theorem inner_dg_input (D : Data X n Z s) (η β : ℝ) (x : X) (m : Bool → Adr n Z → Fin 3 → ℂ)
    (v v' : EuclideanSpace ℂ n) :
    inner ℂ (U D η β x (Jin D v)) (dg m (U D η β x (Jin D v'))) =
      ∑ b, ∑ e, ∑ f, conj (Psi D η β x v b e f) *
        (m b (e, D.table x e) f * Psi D η β x v' b e f) :=
  inner_supported (fun e => D.table x e) _ _ _ _ (frame_input_eq D η β x v)
    (dg_frame_input_eq D η β x m v')

theorem norm_dg_input_sq (D : Data X n Z s) (η β : ℝ) (x : X) (m : Bool → Adr n Z → Fin 3 → ℂ)
    (v : EuclideanSpace ℂ n) :
    ‖dg m (U D η β x (Jin D v))‖ ^ 2 =
      ∑ b, ∑ e, ∑ f, ‖m b (e, D.table x e) f‖ ^ 2 * ‖Psi D η β x v b e f‖ ^ 2 := by
  rw [norm_sq_supported (fun e => D.table x e) _ _ (dg_frame_input_eq D η β x m v)]
  simp only [norm_mul, mul_pow]

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- Summing the orientation of the frame component: `∑_b |Psi|² = |gflag|² ‖y_e‖²`. -/
theorem sum_norm_Psi_sq (D : Data X n Z s) (η β : ℝ) (x : X) (v : EuclideanSpace ℂ n)
    (e : n × n) (f : Fin 3) :
    ∑ b, ‖Psi D η β x v b e f‖ ^ 2 =
      ‖gflag (c2 D η β (e, D.table x e)) f‖ ^ 2 * ‖yv D x v e‖ ^ 2 := by
  simp only [Psi, norm_mul, mul_pow]
  rw [← Finset.mul_sum, ← norm_Ocl (c2 D η β (e, D.table x e)) (yv D x v e),
    PiLp.norm_sq_eq_of_L2]

/-! ### Weighted sums over the sparse boundary -/

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem norm_yv_sq (D : Data X n Z s) (x : X) (v : EuclideanSpace ℂ n) (e : n × n) :
    ‖yv D x v e‖ ^ 2 = ‖boundary (D.rowloc x) (D.colloc x) v (.inl e)‖ ^ 2 +
      ‖boundary (D.rowloc x) (D.colloc x) v (.inr e)‖ ^ 2 := by
  rw [yv, PiLp.norm_sq_eq_of_L2, Fintype.sum_bool, OrientedEdgeCayley.regroup_true,
    OrientedEdgeCayley.regroup_false, add_comm]

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- `∑_e a_e ‖(J₀ v)_e‖² ≤ (W/s) ‖v‖²` when every row and column sum of `a ≥ 0` is at most
`W`. -/
theorem edge_sum_le (D : Data X n Z s) (x : X) (a : n × n → ℝ) (ha : ∀ e, 0 ≤ a e) {W : ℝ}
    (hR : ∀ i, ∑ j, a (i, j) ≤ W) (hC : ∀ j, ∑ i, a (i, j) ≤ W) (v : EuclideanSpace ℂ n) :
    ∑ e, a e * ‖yv D x v e‖ ^ 2 ≤ W / s * ‖v‖ ^ 2 := by
  classical
  set w : ℝ := (2 * (s : ℝ))⁻¹ with hw
  have hJ : ∀ i j, ‖boundary (D.rowloc x) (D.colloc x) v (.inl (i, j))‖ ^ 2 =
      w * (if SparseSlotStates.selected (D.rowloc x) i j then ‖v i‖ ^ 2 else 0) := by
    intro i j
    simp only [boundary, smul_apply, PiLp.smul_apply, stack_inl, rowIncidence_apply,
      smul_eq_mul]
    rw [norm_mul, mul_pow, boundaryWeight_norm_sq]
    split_ifs <;> simp [hw]
  have hJ' : ∀ i j, ‖boundary (D.rowloc x) (D.colloc x) v (.inr (i, j))‖ ^ 2 =
      w * (if SparseSlotStates.selected (D.colloc x) j i then ‖v j‖ ^ 2 else 0) := by
    intro i j
    simp only [boundary, smul_apply, PiLp.smul_apply, stack_inr, columnIncidence_apply,
      smul_eq_mul]
    rw [norm_mul, mul_pow, boundaryWeight_norm_sq]
    split_ifs <;> simp [hw]
  have hw0 : 0 ≤ w := by positivity
  have hsel : ∀ (P : Prop) [Decidable P] (c : ℝ), 0 ≤ c → (if P then c else 0) ≤ c := by
    intro P _ c hc
    split_ifs <;> linarith
  -- bound each edge term by the unrestricted row and column terms
  have hterm : ∀ i j, a (i, j) * ‖yv D x v (i, j)‖ ^ 2 ≤
      w * (‖v i‖ ^ 2 * a (i, j)) + w * (‖v j‖ ^ 2 * a (i, j)) := by
    intro i j
    rw [norm_yv_sq, hJ, hJ']
    have h1 := hsel (SparseSlotStates.selected (D.rowloc x) i j) (‖v i‖ ^ 2) (sq_nonneg _)
    have h2 := hsel (SparseSlotStates.selected (D.colloc x) j i) (‖v j‖ ^ 2) (sq_nonneg _)
    have ha' := ha (i, j)
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg ha' hw0),
      mul_le_mul_of_nonneg_left h2 (mul_nonneg ha' hw0)]
  have hrow : ∑ i, ∑ j, w * (‖v i‖ ^ 2 * a (i, j)) ≤ w * (W * ‖v‖ ^ 2) := by
    rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hw0
    rw [mul_comm W]
    exact mul_le_mul_of_nonneg_left (hR i) (sq_nonneg _)
  have hcol : ∑ i, ∑ j, w * (‖v j‖ ^ 2 * a (i, j)) ≤ w * (W * ‖v‖ ^ 2) := by
    rw [Finset.sum_comm, PiLp.norm_sq_eq_of_L2, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hw0
    rw [mul_comm W]
    exact mul_le_mul_of_nonneg_left (hC j) (sq_nonneg _)
  have hs : (0 : ℝ) < s := by exact_mod_cast D.slots_pos
  calc ∑ e, a e * ‖yv D x v e‖ ^ 2 = ∑ i, ∑ j, a (i, j) * ‖yv D x v (i, j)‖ ^ 2 :=
        Fintype.sum_prod_type _
    _ ≤ ∑ i, ∑ j, (w * (‖v i‖ ^ 2 * a (i, j)) + w * (‖v j‖ ^ 2 * a (i, j))) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = ∑ i, ∑ j, w * (‖v i‖ ^ 2 * a (i, j)) + ∑ i, ∑ j, w * (‖v j‖ ^ 2 * a (i, j)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_add_distrib]
    _ ≤ w * (W * ‖v‖ ^ 2) + w * (W * ‖v‖ ^ 2) := add_le_add hrow hcol
    _ = W / s * ‖v‖ ^ 2 := by
        rw [hw]
        field_simp
        ring

/-! ### Entries at the oracle words -/

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem c1_table (D : Data X n Z s) (η β : ℝ) (x : X) (e : n × n) :
    c1 D η β (e, D.table x e) = cclip η β (D.matrix x e.1 e.2) := by
  rw [c1, D.decoded]

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem c2_table (D : Data X n Z s) (η β : ℝ) (x : X) (e : n × n) :
    c2 D η β (e, D.table x e) = ccorr η β (D.matrix x e.1 e.2) := by
  rw [c2, D.decoded]

/-- The row and column norm promise. -/
def Promise (D : Data X n Z s) (η : ℝ) (x : X) : Prop :=
  (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) ∧ (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem Promise.entry_le {D : Data X n Z s} {η : ℝ} {x : X} (h : Promise D η x) (hη : 0 ≤ η)
    (i j : n) : ‖D.matrix x i j‖ ≤ η :=
  norm_le_of_energy_le η (D.matrix x i) hη (h.1 i) j

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The rows and columns of `|c₂|` sum to at most `β`. -/
theorem c2_sums {D : Data X n Z s} {η β : ℝ} {x : X} (h : Promise D η x) (hη : 0 < η)
    (hβ : 0 ≤ β) :
    (∀ i, ∑ j, ‖c2 D η β ((i, j), D.table x (i, j))‖ ≤ β) ∧
      (∀ j, ∑ i, ‖c2 D η β ((i, j), D.table x (i, j))‖ ≤ β) := by
  have hb : ∀ i j, ‖c2 D η β ((i, j), D.table x (i, j))‖ ≤ β / η ^ 2 * ‖D.matrix x i j‖ ^ 2 := by
    intro i j
    rw [c2_table]
    refine (norm_ccorr_le hη hβ _).trans (le_of_eq ?_)
    ring
  have hη2 : 0 < η ^ 2 := by positivity
  constructor
  · intro i
    calc ∑ j, ‖c2 D η β ((i, j), D.table x (i, j))‖ ≤ ∑ j, β / η ^ 2 * ‖D.matrix x i j‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => hb i j
      _ = β / η ^ 2 * ∑ j, ‖D.matrix x i j‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ β / η ^ 2 * η ^ 2 := mul_le_mul_of_nonneg_left (h.1 i) (by positivity)
      _ = β := by field_simp
  · intro j
    calc ∑ i, ‖c2 D η β ((i, j), D.table x (i, j))‖ ≤ ∑ i, β / η ^ 2 * ‖D.matrix x i j‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => hb i j
      _ = β / η ^ 2 * ∑ i, ‖D.matrix x i j‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ β / η ^ 2 * η ^ 2 := mul_le_mul_of_nonneg_left (h.2 j) (by positivity)
      _ = β := by field_simp

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The rows and columns of `|c₁|²` sum to at most `1`. -/
theorem c1_sums {D : Data X n Z s} {η β : ℝ} {x : X} (h : Promise D η x) (hη : 0 < η)
    (hβ : 0 ≤ β) :
    (∀ i, ∑ j, ‖c1 D η β ((i, j), D.table x (i, j))‖ ^ 2 ≤ 1) ∧
      (∀ j, ∑ i, ‖c1 D η β ((i, j), D.table x (i, j))‖ ^ 2 ≤ 1) := by
  have hb : ∀ i j, ‖c1 D η β ((i, j), D.table x (i, j))‖ ^ 2 ≤
      (η ^ 2)⁻¹ * ‖D.matrix x i j‖ ^ 2 := by
    intro i j
    rw [c1_table]
    have h1 := norm_cclip_le hη hβ (D.matrix x i j)
    have h2 : (‖D.matrix x i j‖ / η) ^ 2 = (η ^ 2)⁻¹ * ‖D.matrix x i j‖ ^ 2 := by
      field_simp
    rw [← h2]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hη2 : 0 < η ^ 2 := by positivity
  constructor
  · intro i
    calc ∑ j, ‖c1 D η β ((i, j), D.table x (i, j))‖ ^ 2 ≤
          ∑ j, (η ^ 2)⁻¹ * ‖D.matrix x i j‖ ^ 2 := Finset.sum_le_sum fun j _ => hb i j
      _ = (η ^ 2)⁻¹ * ∑ j, ‖D.matrix x i j‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (η ^ 2)⁻¹ * η ^ 2 := mul_le_mul_of_nonneg_left (h.1 i) (by positivity)
      _ = 1 := by field_simp
  · intro j
    calc ∑ i, ‖c1 D η β ((i, j), D.table x (i, j))‖ ^ 2 ≤
          ∑ i, (η ^ 2)⁻¹ * ‖D.matrix x i j‖ ^ 2 := Finset.sum_le_sum fun i _ => hb i j
      _ = (η ^ 2)⁻¹ * ∑ i, ‖D.matrix x i j‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (η ^ 2)⁻¹ * η ^ 2 := mul_le_mul_of_nonneg_left (h.2 j) (by positivity)
      _ = 1 := by field_simp

/-! ### The flag amplitudes -/

theorem norm_gflag_zero_sq (c : ℂ) : ‖gflag c 0‖ ^ 2 = ‖c‖ / 2 := by
  rw [gflag_zero, norm_mul, mul_pow, norm_r2_sq, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    amp, Real.sq_sqrt (norm_nonneg _)]
  ring

theorem norm_gflag_two_sq (c : ℂ) : ‖gflag c 2‖ ^ 2 = 1 / 2 := by
  rw [gflag_two, norm_r2_sq]

/-! ### Weighted norms of the input in the frame -/

omit [DecidableEq Z] in
theorem U_adjoint_norm (D : Data X n Z s) (η β : ℝ) (x : X) (w : Space n Z) :
    ‖adjoint (U D η β x) w‖ = ‖w‖ := by
  have h : ((U D η β x)†)† ∘L (U D η β x)† = 1 := by
    rw [adjoint_adjoint]
    exact U_coisometry D η β x
  exact (norm_map_iff_adjoint_comp_self _).mpr h w

/-- A weighted norm of a diagonal operator on the input, with weights bounded by `w f a`. -/
theorem norm_dg_input_sq_le (D : Data X n Z s) (η β : ℝ) (x : X)
    (m : Bool → Adr n Z → Fin 3 → ℂ) (w : Fin 3 → Adr n Z → ℝ)
    (hw : ∀ b a f, ‖m b a f‖ ^ 2 ≤ w f a) (v : EuclideanSpace ℂ n) :
    ‖dg m (U D η β x (Jin D v))‖ ^ 2 ≤
      ∑ e, (∑ f, w f (e, D.table x e) * ‖gflag (c2 D η β (e, D.table x e)) f‖ ^ 2) *
        ‖yv D x v e‖ ^ 2 := by
  rw [norm_dg_input_sq]
  calc ∑ b, ∑ e, ∑ f, ‖m b (e, D.table x e) f‖ ^ 2 * ‖Psi D η β x v b e f‖ ^ 2 ≤
        ∑ b, ∑ e, ∑ f, w f (e, D.table x e) * ‖Psi D η β x v b e f‖ ^ 2 :=
        Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun f _ =>
          mul_le_mul_of_nonneg_right (hw b _ f) (sq_nonneg _)
    _ = ∑ e, ∑ f, w f (e, D.table x e) * ∑ b, ‖Psi D η β x v b e f‖ ^ 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro e _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro f _
        rw [Finset.mul_sum]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro e _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro f _
        rw [sum_norm_Psi_sq]
        ring

/-! ### The isolated weights -/

/-- **Isolated weight** (`opt:eq:isolated-weights`): `‖P₊ J v‖² ≤ β/(2s) ‖v‖²`. -/
theorem norm_Ppl_input_sq_le (D : Data X n Z s) {η β : ℝ} (hη : 0 < η) (hβ : 0 ≤ β) {x : X}
    (hP : Promise D η x) (v : EuclideanSpace ℂ n) :
    ‖Ppl D η β x (Jin D v)‖ ^ 2 ≤ β / (2 * s) * ‖v‖ ^ 2 := by
  have e1 : Ppl D η β x (Jin D v) = adjoint (U D η β x) (LamP (U D η β x (Jin D v))) := rfl
  rw [e1, U_adjoint_norm, LamP]
  refine (norm_dg_input_sq_le D η β x _ (fun f _ => if f = 0 then 1 else 0) ?_ v).trans ?_
  · intro b a f
    unfold ipl
    split_ifs <;> simp_all
  · have hsum := edge_sum_le D x (fun e => ‖c2 D η β (e, D.table x e)‖ / 2)
      (fun e => by positivity) (W := β / 2)
      (fun i => by
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right ((c2_sums hP hη hβ).1 i) (by norm_num))
      (fun j => by
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right ((c2_sums hP hη hβ).2 j) (by norm_num)) v
    have e2 : ∀ e, (∑ f : Fin 3, (if f = 0 then (1 : ℝ) else 0) *
        ‖gflag (c2 D η β (e, D.table x e)) f‖ ^ 2) = ‖c2 D η β (e, D.table x e)‖ / 2 := by
      intro e
      rw [Fin.sum_univ_three]
      simp [norm_gflag_zero_sq]
    simp only [e2]
    refine hsum.trans (le_of_eq ?_)
    ring

/-- **Isolated weight**: `‖P₋ J v‖² ≤ β/(2s) ‖v‖²`. -/
theorem norm_Pmi_input_sq_le (D : Data X n Z s) {η β : ℝ} (hη : 0 < η) (hβ : 0 ≤ β) {x : X}
    (hP : Promise D η x) (v : EuclideanSpace ℂ n) :
    ‖Pmi D η β x (Jin D v)‖ ^ 2 ≤ β / (2 * s) * ‖v‖ ^ 2 := by
  have e1 : Pmi D η β x (Jin D v) = adjoint (U D η β x) (LamM (U D η β x (Jin D v))) := rfl
  rw [e1, U_adjoint_norm, LamM]
  refine (norm_dg_input_sq_le D η β x _ (fun f _ => if f = 0 then 1 else 0) ?_ v).trans ?_
  · intro b a f
    unfold imi
    split_ifs <;> simp_all
  · have hsum := edge_sum_le D x (fun e => ‖c2 D η β (e, D.table x e)‖ / 2)
      (fun e => by positivity) (W := β / 2)
      (fun i => by
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right ((c2_sums hP hη hβ).1 i) (by norm_num))
      (fun j => by
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right ((c2_sums hP hη hβ).2 j) (by norm_num)) v
    have e2 : ∀ e, (∑ f : Fin 3, (if f = 0 then (1 : ℝ) else 0) *
        ‖gflag (c2 D η β (e, D.table x e)) f‖ ^ 2) = ‖c2 D η β (e, D.table x e)‖ / 2 := by
      intro e
      rw [Fin.sum_univ_three]
      simp [norm_gflag_zero_sq]
    simp only [e2]
    refine hsum.trans (le_of_eq ?_)
    ring

/-! ### The generator on the input -/

omit [DecidableEq Z] in
theorem Kbulk_eq (D : Data X n Z s) (η β q : ℝ) (x : X) :
    Kop D η β q x ∘L CayleyBlocks.bulk (Ppl D η β x) (Pmi D η β x) =
      (U D η β x)† ∘L dg (fun b a f => (kappa D η β q b a f : ℂ) * (1 - ipl b f - imi b f)) ∘L
        U D η β x := by
  rw [Kop, Ppl, Pmi, bulk_conj (U_isometry D η β x), conj_comp (U_coisometry D η β x),
    CayleyBlocks.bulk, LamK, LamP, LamM, ← dg_one, dg_sub, dg_sub, dg_comp]

/-- **Bulk second moment** (`opt:eq:isolated-weights`): `‖K P₀ J v‖² ≤ (2q²/s) ‖v‖²`. -/
theorem norm_bulk_input_sq_le (D : Data X n Z s) {η β : ℝ} (q : ℝ) (hη : 0 < η) (hβ : 0 ≤ β)
    {x : X} (hP : Promise D η x) (v : EuclideanSpace ℂ n) :
    ‖(Kop D η β q x ∘L CayleyBlocks.bulk (Ppl D η β x) (Pmi D η β x)) (Jin D v)‖ ^ 2 ≤
      2 * q ^ 2 / s * ‖v‖ ^ 2 := by
  rw [Kbulk_eq, comp_apply, comp_apply, U_adjoint_norm]
  refine (norm_dg_input_sq_le D η β x _
    (fun f a => if f = 2 then 4 * q ^ 2 * ‖c1 D η β a‖ ^ 2 else 0) ?_ v).trans ?_
  · intro b a f
    have hs : |sgn b| = 1 := by unfold sgn; split_ifs <;> simp
    by_cases hf0 : f = 0
    · subst hf0
      cases b <;> simp [ipl, imi]
    · by_cases hf1 : f = 1
      · subst hf1
        simp [kappa]
      · have hf2 : f = 2 := by omega
        subst hf2
        simp only [kappa, ipl, imi, Fin.isValue, Fin.reduceEq, if_false, and_false, sub_zero,
          mul_one, if_true]
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
        have : (2 * q * ‖c1 D η β a‖ * sgn b) ^ 2 = 4 * q ^ 2 * ‖c1 D η β a‖ ^ 2 * (sgn b) ^ 2 := by
          ring
        rw [this, ← sq_abs (sgn b), hs]
        ring_nf
        exact le_rfl
  · have e2 : ∀ e, (∑ f : Fin 3, (if f = 2 then 4 * q ^ 2 * ‖c1 D η β (e, D.table x e)‖ ^ 2
        else 0) * ‖gflag (c2 D η β (e, D.table x e)) f‖ ^ 2) =
        2 * q ^ 2 * ‖c1 D η β (e, D.table x e)‖ ^ 2 := by
      intro e
      rw [Fin.sum_univ_three]
      simp only [Fin.isValue, Fin.reduceEq, if_false, zero_mul, if_true, norm_gflag_two_sq,
        zero_add]
      ring
    simp only [e2]
    have hsum := edge_sum_le D x (fun e => 2 * q ^ 2 * ‖c1 D η β (e, D.table x e)‖ ^ 2)
      (fun e => by positivity) (W := 2 * q ^ 2)
      (fun i => by
        rw [← Finset.mul_sum]
        have := (c1_sums hP hη hβ).1 i
        nlinarith [sq_nonneg q])
      (fun j => by
        rw [← Finset.mul_sum]
        have := (c1_sums hP hη hβ).2 j
        nlinarith [sq_nonneg q]) v
    exact hsum

/-- **Full second moment** (`opt:eq:joint-moments`): `‖K J v‖² ≤ (2q²(1 + β)/s) ‖v‖²`. -/
theorem norm_K_input_sq_le (D : Data X n Z s) {η β : ℝ} (q : ℝ) (hη : 0 < η) (hβ : 0 ≤ β)
    {x : X} (hP : Promise D η x) (v : EuclideanSpace ℂ n) :
    ‖Kop D η β q x (Jin D v)‖ ^ 2 ≤ 2 * q ^ 2 * (1 + β) / s * ‖v‖ ^ 2 := by
  rw [Kop, comp_apply, comp_apply, U_adjoint_norm, LamK]
  refine (norm_dg_input_sq_le D η β x _
    (fun f a => if f = 0 then 4 * q ^ 2 else if f = 1 then 0 else
      4 * q ^ 2 * ‖c1 D η β a‖ ^ 2) ?_ v).trans ?_
  · intro b a f
    have hs : (sgn b) ^ 2 = 1 := by unfold sgn; split_ifs <;> norm_num
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    unfold kappa
    split_ifs
    · have : (2 * q * sgn b) ^ 2 = 4 * q ^ 2 * (sgn b) ^ 2 := by ring
      rw [this, hs, mul_one]
    · simp
    · have : (2 * q * ‖c1 D η β a‖ * sgn b) ^ 2 = 4 * q ^ 2 * ‖c1 D η β a‖ ^ 2 * (sgn b) ^ 2 := by
        ring
      rw [this, hs, mul_one]
  · have e2 : ∀ e, (∑ f : Fin 3, (if f = 0 then 4 * q ^ 2 else if f = 1 then 0 else
        4 * q ^ 2 * ‖c1 D η β (e, D.table x e)‖ ^ 2) *
          ‖gflag (c2 D η β (e, D.table x e)) f‖ ^ 2) =
        2 * q ^ 2 * (‖c2 D η β (e, D.table x e)‖ + ‖c1 D η β (e, D.table x e)‖ ^ 2) := by
      intro e
      rw [Fin.sum_univ_three]
      simp only [Fin.isValue, Fin.reduceEq, if_false, if_true, zero_mul, norm_gflag_two_sq,
        norm_gflag_zero_sq, add_zero]
      ring
    simp only [e2]
    have hsum := edge_sum_le D x
      (fun e => 2 * q ^ 2 * (‖c2 D η β (e, D.table x e)‖ + ‖c1 D η β (e, D.table x e)‖ ^ 2))
      (fun e => by positivity) (W := 2 * q ^ 2 * (β + 1))
      (fun i => by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        have h1 := (c2_sums hP hη hβ).1 i
        have h2 := (c1_sums hP hη hβ).1 i
        have hq := sq_nonneg q
        nlinarith)
      (fun j => by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        have h1 := (c2_sums hP hη hβ).2 j
        have h2 := (c1_sums hP hη hβ).2 j
        have hq := sq_nonneg q
        nlinarith) v
    refine hsum.trans (le_of_eq ?_)
    ring

/-! ### The compression -/

theorem inner_signQ (u u' : Qubit) :
    inner ℂ u (signQ u') = conj (u false) * u' false - conj (u true) * u' true := by
  rw [PiLp.inner_apply, Fintype.sum_bool, RCLike.inner_apply, RCLike.inner_apply]
  simp only [signQ, ComplexAmplitudeRotation.matrix_false, ComplexAmplitudeRotation.matrix_true]
  ring

theorem generator_add (a b : ℂ) :
    ExactEdgeCayley.generator (a + b) =
      ExactEdgeCayley.generator a + ExactEdgeCayley.generator b := by
  ext y t
  cases t <;> simp [ExactEdgeCayley.generator_false, ExactEdgeCayley.generator_true, add_mul,
    map_add]

/-- The orientation sum for one flag: `∑_b conj(g u_b) (w s(b)) (g u'_b) = |g|² w ⟨u, σ u'⟩`. -/
theorem flag_term (g : ℂ) (w : ℝ) (u u' : Qubit) :
    ∑ b : Bool, conj (g * u b) * (((w * sgn b : ℝ) : ℂ) * (g * u' b)) =
      ((‖g‖ ^ 2 * w : ℝ) : ℂ) * inner ℂ u (signQ u') := by
  rw [inner_signQ, Fintype.sum_bool]
  simp only [sgn, if_true, Bool.false_eq_true, if_false, map_mul]
  push_cast
  rw [← Complex.conj_mul' g]
  ring

/-- The eigenvalue weights of one flag: `κ = w_f s(b)`. -/
def kw (D : Data X n Z s) (η β q : ℝ) (a : Adr n Z) (f : Fin 3) : ℝ :=
  if f = 0 then 2 * q else if f = 1 then 0 else 2 * q * ‖c1 D η β a‖

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem kappa_eq (D : Data X n Z s) (η β q : ℝ) (b : Bool) (a : Adr n Z) (f : Fin 3) :
    kappa D η β q b a f = kw D η β q a f * sgn b := by
  unfold kappa kw
  split_ifs <;> ring

/-- **The local compression on one edge**: the success flag gives `q |c₂| ⟨u, σ u'⟩ = q ⟨y, E(c₂)
y'⟩`, the clipped flag `q ⟨y, E(c₁) y'⟩`. -/
theorem edge_term (c₁ c₂ : ℂ) (hph : Ocl c₂ = Ocl c₁) (q : ℝ) (y y' : Qubit) :
    ∑ f : Fin 3, ∑ b : Bool, conj (gflag c₂ f * Ocl c₂ y b) *
      (((((if f = 0 then 2 * q else if f = 1 then 0 else 2 * q * ‖c₁‖) * sgn b : ℝ)) : ℂ) *
        (gflag c₂ f * Ocl c₂ y' b)) =
      (q : ℂ) * inner ℂ y (ExactEdgeCayley.generator (c₁ + c₂) y') := by
  have h1 := inner_Ocl_sign c₁ y y'
  have h2 := inner_Ocl_sign c₂ y y'
  rw [← hph] at h1
  rw [generator_add, add_apply, inner_add_right, ← h1, ← h2]
  simp only [flag_term]
  rw [Fin.sum_univ_three]
  simp only [Fin.isValue, if_true, Fin.reduceEq, if_false, norm_gflag_zero_sq,
    norm_gflag_two_sq]
  push_cast
  ring

omit [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- `⟨w, E_M w'⟩ = ∑_e ⟨w_e, E(M_e) w'_e⟩`. -/
theorem inner_entryGenerator (M : Matrix n n ℂ) (w w' : OrientedSpace n) :
    inner ℂ w (entryGenerator M w') = ∑ e : n × n, inner ℂ (OrientedEdgeCayley.regroup w e)
      (ExactEdgeCayley.generator (M e.1 e.2) (OrientedEdgeCayley.regroup w' e)) := by
  rw [← OrientedEdgeCayley.lift_generator, ← OrientedEdgeCayley.regroup.inner_map_map,
    OrientedEdgeCayley.regroup_lift, PiLp.inner_apply]
  rfl

/-- The joint entries `c₁ + c₂` at the oracle words. -/
def Mjoint (D : Data X n Z s) (η β : ℝ) (x : X) : Matrix n n ℂ :=
  fun i j => c1 D η β ((i, j), D.table x (i, j)) + c2 D η β ((i, j), D.table x (i, j))

/-- **The compressed generator**: `⟨J v, K J v'⟩ = q ⟨J₀ v, E_M J₀ v'⟩` with `M = c₁ + c₂`. -/
theorem inner_input_K (D : Data X n Z s) {η β : ℝ} (q : ℝ) (hη : 0 < η) (hβ : 0 < β) (x : X)
    (v v' : EuclideanSpace ℂ n) :
    inner ℂ (Jin D v) (Kop D η β q x (Jin D v')) = (q : ℂ) *
      inner ℂ (boundary (D.rowloc x) (D.colloc x) v)
        (entryGenerator (Mjoint D η β x) (boundary (D.rowloc x) (D.colloc x) v')) := by
  rw [Kop, comp_apply, comp_apply, adjoint_inner_right, LamK, inner_dg_input,
    inner_entryGenerator, Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  have hph : Ocl (c2 D η β (e, D.table x e)) = Ocl (c1 D η β (e, D.table x e)) :=
    Ocl_congr (phase_ccorr hη hβ _)
  have h := edge_term (c1 D η β (e, D.table x e)) (c2 D η β (e, D.table x e)) hph q
    (yv D x v e) (yv D x v' e)
  refine Eq.trans ?_ h
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro b _
  rw [kappa_eq]
  rfl

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem Mjoint_eq (D : Data X n Z s) {η β : ℝ} (hη : 0 < η) (hβ : 0 ≤ β) {x : X}
    (hP : Promise D η x) : Mjoint D η β x = fun i j => D.matrix x i j * (η : ℂ)⁻¹ := by
  funext i j
  rw [Mjoint, c1_table, c2_table, cclip_add_ccorr hη hβ (hP.entry_le hη.le i j),
    div_eq_mul_inv]

/-- **The joint compression** (`opt:eq:joint-moments`): `J† K J = H/α` with `α = sη/q`. -/
theorem compression (D : Data X n Z s) {η β : ℝ} (q : ℝ) (hη : 0 < η) (hβ : 0 < β) {x : X}
    (hH : (D.matrix x).IsHermitian) (hP : Promise D η x) :
    (Jin D)† ∘L Kop D η β q x ∘L Jin D =
      ((q / (s * η) : ℝ) : ℂ) • SparseStateOverlap.matrixOperator (D.matrix x) := by
  set M := Mjoint D η β x with hMdef
  have hM : M = fun i j => D.matrix x i j * (η : ℂ)⁻¹ := Mjoint_eq D hη hβ.le hP
  have hMH : M.IsHermitian := by
    rw [hM]
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_mul', hH.apply i j, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hrow : ∀ i j, M i j ≠ 0 → SparseSlotStates.selected (D.rowloc x) i j := by
    intro i j h
    apply D.row_covers x i j
    intro h0
    exact h (by simp [hM, h0])
  have hcol : ∀ i j, M i j ≠ 0 → SparseSlotStates.selected (D.colloc x) j i := by
    intro i j h
    apply D.column_covers x i j
    intro h0
    exact h (by simp [hM, h0])
  have hcomp := generator_compression D.slots_pos M hMH (D.rowloc x) (D.colloc x) hrow hcol
  rw [generator, smul_comp, comp_smul] at hcomp
  have hs0 : (Real.sqrt (s : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast D.slots_pos)
    exact_mod_cast this.ne'
  have hr : (Real.sqrt (s : ℝ) : ℂ) * (Real.sqrt (s : ℝ) : ℂ) = (s : ℂ) := by
    have h : Real.sqrt (s : ℝ) * Real.sqrt (s : ℝ) = (s : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg s)
    exact_mod_cast h
  have hX : (boundary (D.rowloc x) (D.colloc x))† ∘L entryGenerator M ∘L
      boundary (D.rowloc x) (D.colloc x) = (s : ℂ)⁻¹ • SparseStateOverlap.matrixOperator M := by
    calc (boundary (D.rowloc x) (D.colloc x))† ∘L entryGenerator M ∘L
          boundary (D.rowloc x) (D.colloc x)
        = (Real.sqrt (s : ℝ) : ℂ)⁻¹ • ((Real.sqrt (s : ℝ) : ℂ) •
            ((boundary (D.rowloc x) (D.colloc x))† ∘L entryGenerator M ∘L
              boundary (D.rowloc x) (D.colloc x))) := by
          rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
      _ = (s : ℂ)⁻¹ • SparseStateOverlap.matrixOperator M := by
          rw [hcomp, smul_smul, ← mul_inv, hr]
  have hMop : SparseStateOverlap.matrixOperator M =
      (η : ℂ)⁻¹ • SparseStateOverlap.matrixOperator (D.matrix x) := by
    rw [hM, NativeSignedFactor.matrixOperator_mul_const]
  apply ContinuousLinearMap.ext
  intro v'
  apply ext_inner_left ℂ
  intro v
  rw [comp_apply, comp_apply, adjoint_inner_right, inner_input_K D q hη hβ x,
    ← adjoint_inner_right, ← comp_apply, ← comp_apply, comp_assoc, ← hMdef, hX, hMop,
    smul_apply, smul_apply, smul_apply, inner_smul_right, inner_smul_right, inner_smul_right,
    ← mul_assoc, ← mul_assoc]
  congr 1
  have hη0 : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast D.slots_pos.ne'
  push_cast
  field_simp

end

end LargeSparsityCore.Native
