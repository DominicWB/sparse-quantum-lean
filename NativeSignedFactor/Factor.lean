import NativeSignedFactor.Gate

set_option autoImplicit false

/-!
# The native factor identities

For a Hermitian sparse matrix `H` with entries of modulus at most `κ` and row and column
Euclidean norms at most `η`, the logical native factor satisfies (`opt:eq:native-factor`,
`opt:eq:whole-factor`)

* `B† Z B = H/(sκ)` (`Cop_eq`), from `B† Z B = J₀† E_{H/κ} J₀` (`facOp_sign`) and the edge
  compression `J₀† E_X J₀ = X/s` (`SparseHamiltonian.SparseEdgeMoments.generator_compression`);
* `B† B ⪯ η/(√s κ) I` (`Dop_le`), from `‖B v‖² = ∑_e |c_e| ‖(J₀ v)_e‖²` and Cauchy–Schwarz
  over the `s` listed slots of every row and column (`norm_factor_sq_le`).

With `κ = η` this is `H = sη B† Z B` and `B† B ⪯ s^{-1/2} I`. The clean physical encoding of the
logical workspace intertwines the physical factor program with the logical one
(`physProgram_intertwines`), and the factor structure is transported along it (`transport`,
`physKnown`) with the same compressions (`phys_Cop`, `phys_Dop_le`).
-/

namespace NativeSignedFactor

noncomputable section

open ContinuousLinearMap SparseHamiltonian OracleCircuit NativeSparseBlockEncoding
open OrientedNativeLayout SparseEdgeMoments SignedFactorSimulation
open scoped InnerProduct ComplexConjugate

/-! ### Transport of a factor structure along an isometry -/

section Transport

variable {P V W : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

omit [CompleteSpace P] in
theorem adjoint_comp_cancel {J : V →L[ℂ] W} (hJ : J† ∘L J = 1) (A : P →L[ℂ] V) :
    J† ∘L (J ∘L A) = A := by
  rw [← comp_assoc, hJ, one_def, id_comp]

/-- A factor structure on `V`, transported along a known isometry `J : V → W`: the input is
`J E`, the projection `J Π J†` and the reflection `J Z J† + (1 - J J†)`. -/
def transport (K : Known P V) (J : V →L[ℂ] W) (hJ : J† ∘L J = 1) : Known P W where
  E := J ∘L K.E
  proj := J ∘L K.proj ∘L J†
  Z := J ∘L K.Z ∘L J† + (1 - J ∘L J†)
  E_isometry := by
    rw [adjoint_comp, comp_assoc, adjoint_comp_cancel hJ, K.E_isometry]
  proj_adjoint := by
    simp only [adjoint_comp, adjoint_adjoint, K.proj_adjoint, comp_assoc]
  proj_idem := by
    have h := K.proj_idem
    rw [mul_def] at h ⊢
    simp only [comp_assoc, adjoint_comp_cancel hJ]
    rw [← comp_assoc K.proj K.proj, h]
  Z_adjoint := by
    have h := K.Z_adjoint
    simp only [map_add, map_sub, adjoint_comp, adjoint_adjoint, adjoint_one, h, comp_assoc]
  Z_sq := by
    have hZ := K.Z_sq
    rw [mul_def] at hZ
    have hAA : (J ∘L K.Z ∘L J†) * (J ∘L K.Z ∘L J†) = J ∘L J† := by
      rw [mul_def]; simp only [comp_assoc, adjoint_comp_cancel hJ]
      rw [← comp_assoc K.Z K.Z, hZ, one_def, id_comp]
    have hAP : (J ∘L K.Z ∘L J†) * (J ∘L J†) = J ∘L K.Z ∘L J† := by
      rw [mul_def]; simp only [comp_assoc, adjoint_comp_cancel hJ]
    have hPA : (J ∘L J†) * (J ∘L K.Z ∘L J†) = J ∘L K.Z ∘L J† := by
      rw [mul_def]; simp only [comp_assoc, adjoint_comp_cancel hJ]
    have hPP : (J ∘L J†) * (J ∘L J†) = J ∘L J† := by
      rw [mul_def]; simp only [comp_assoc, adjoint_comp_cancel hJ]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, hAA, hAP, hPA, hPP]
    abel
  Z_comm := by
    have hc := K.Z_comm
    rw [mul_def, mul_def] at hc
    have h1 : (J ∘L K.Z ∘L J†) * (J ∘L K.proj ∘L J†) = J ∘L (K.Z ∘L K.proj) ∘L J† := by
      rw [mul_def]; simp only [comp_assoc, adjoint_comp_cancel hJ]
    have h2 : (J ∘L K.proj ∘L J†) * (J ∘L K.Z ∘L J†) = J ∘L (K.proj ∘L K.Z) ∘L J† := by
      rw [mul_def]; simp only [comp_assoc, adjoint_comp_cancel hJ]
    have h3 : (J ∘L J†) * (J ∘L K.proj ∘L J†) = J ∘L K.proj ∘L J† := by
      rw [mul_def]; simp only [comp_assoc, adjoint_comp_cancel hJ]
    have h4 : (J ∘L K.proj ∘L J†) * (J ∘L J†) = J ∘L K.proj ∘L J† := by
      rw [mul_def]; simp only [comp_assoc, adjoint_comp_cancel hJ]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, h1, h2, h3, h4, hc]

/-- The transported factor of an intertwined unitary is the image of the original factor. -/
theorem transport_factor (K : Known P V) {J : V →L[ℂ] W} (hJ : J† ∘L J = 1)
    {U' : W →L[ℂ] W} {U : V →L[ℂ] V} (h : U' ∘L J = J ∘L U) :
    (transport K J hJ).factor U' = J ∘L K.factor U := by
  change (J ∘L K.proj ∘L J†) ∘L U' ∘L J ∘L K.E = J ∘L K.proj ∘L U ∘L K.E
  rw [← comp_assoc U' J, h]
  simp only [comp_assoc, adjoint_comp_cancel hJ]

theorem transport_Cop (K : Known P V) {J : V →L[ℂ] W} (hJ : J† ∘L J = 1)
    {U' : W →L[ℂ] W} {U : V →L[ℂ] V} (h : U' ∘L J = J ∘L U) :
    (transport K J hJ).Cop U' = K.Cop U := by
  rw [Known.Cop, Known.Cop, transport_factor K hJ h]
  have hZ : J† ∘L (transport K J hJ).Z ∘L J = K.Z := by
    change J† ∘L (J ∘L K.Z ∘L J† + (1 - J ∘L J†)) ∘L J = K.Z
    rw [add_comp, sub_comp, one_def, id_comp, comp_add, comp_sub]
    simp only [comp_assoc, adjoint_comp_cancel hJ, hJ]
    rw [sub_self, add_zero, one_def, comp_id]
  rw [adjoint_comp]
  calc (K.factor U)† ∘L J† ∘L (transport K J hJ).Z ∘L J ∘L K.factor U
      = (K.factor U)† ∘L (J† ∘L (transport K J hJ).Z ∘L J) ∘L K.factor U := by
        simp only [comp_assoc]
    _ = _ := by rw [hZ]

theorem transport_Dop (K : Known P V) {J : V →L[ℂ] W} (hJ : J† ∘L J = 1)
    {U' : W →L[ℂ] W} {U : V →L[ℂ] V} (h : U' ∘L J = J ∘L U) :
    (transport K J hJ).Dop U' = K.Dop U := by
  rw [Known.Dop, Known.Dop, transport_factor K hJ h, adjoint_comp, comp_assoc,
    adjoint_comp_cancel hJ]

end Transport

/-! ### Loewner bound from a norm bound -/

section Loewner

variable {P W : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- `‖B v‖² ≤ δ ‖v‖²` for all `v` gives `B† B ⪯ δ I`. -/
theorem adjoint_comp_self_le {B : P →L[ℂ] W} {δ : ℝ}
    (h : ∀ v, ‖B v‖ ^ 2 ≤ δ * ‖v‖ ^ 2) :
    B† ∘L B ≤ (δ : ℂ) • (1 : P →L[ℂ] P) := by
  rw [ContinuousLinearMap.le_def, isPositive_def']
  refine ⟨?_, fun v => ?_⟩
  · refine IsSelfAdjoint.sub ?_ (isPositive_adjoint_comp_self B).isSelfAdjoint
    rw [IsSelfAdjoint, star_smul, star_one]
    simp
  · rw [reApplyInnerSelf_apply, sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
      inner_smul_left, comp_apply, adjoint_inner_left, map_sub, Complex.conj_ofReal]
    have h1 : RCLike.re (inner ℂ v v) = ‖v‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    have h2 : RCLike.re (inner ℂ (B v) (B v)) = ‖B v‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    have h3 : RCLike.re ((δ : ℂ) * inner ℂ v v) = δ * RCLike.re (inner ℂ v v) := by
      simp only [RCLike.re_to_complex, Complex.re_ofReal_mul]
    rw [h3, h1, h2]
    linarith [h v]

/-- The norm bound `‖B v‖² ≤ δ ‖v‖²` for every `v`. -/
def NormBound (B : P →L[ℂ] W) (δ : ℝ) : Prop := ∀ v, ‖B v‖ ^ 2 ≤ δ * ‖v‖ ^ 2

/-- A norm bound on the factor gives the Loewner bound on the successful weight. -/
theorem Dop_le_of_bound (K : Known P W) (U : W →L[ℂ] W) {δ : ℝ}
    (h : NormBound (K.factor U) δ) :
    K.Dop U ≤ (δ : ℂ) • (1 : P →L[ℂ] P) :=
  adjoint_comp_self_le h

end Loewner

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

/-! ### Edge operators -/

omit [DecidableEq n] in
/-- The adjoint of a lifted edge operator is the lift of the adjoints. -/
theorem lift_adjoint (G : n × n → Qubit →L[ℂ] Qubit) :
    (OrientedEdgeCayley.lift G)† = OrientedEdgeCayley.lift (fun e => (G e)†) := by
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_left ℂ
  intro v
  calc inner ℂ v (((OrientedEdgeCayley.lift G)†) w)
      = inner ℂ (OrientedEdgeCayley.lift G v) w := adjoint_inner_right _ _ _
    _ = inner ℂ (OrientedEdgeCayley.regroup (OrientedEdgeCayley.lift G v))
          (OrientedEdgeCayley.regroup w) := (OrientedEdgeCayley.regroup.inner_map_map _ _).symm
    _ = inner ℂ (WeightedClock.diagonal G (OrientedEdgeCayley.regroup v))
          (OrientedEdgeCayley.regroup w) := by rw [OrientedEdgeCayley.regroup_lift]
    _ = inner ℂ (OrientedEdgeCayley.regroup v)
          (((WeightedClock.diagonal G)†) (OrientedEdgeCayley.regroup w)) :=
        (adjoint_inner_right _ _ _).symm
    _ = inner ℂ (OrientedEdgeCayley.regroup v)
          (WeightedClock.diagonal (fun e => (G e)†) (OrientedEdgeCayley.regroup w)) := by
        rw [WeightedClock.diagonal_adjoint]
    _ = inner ℂ (OrientedEdgeCayley.regroup v)
          (OrientedEdgeCayley.regroup (OrientedEdgeCayley.lift (fun e => (G e)†) w)) := by
        rw [OrientedEdgeCayley.regroup_lift]
    _ = _ := OrientedEdgeCayley.regroup.inner_map_map _ _

omit [DecidableEq n] in
/-- The orientation sign of the logical workspace restricts to the edge sign. -/
theorem sign_clean :
    sign ∘L (clean (n := n) (Z := Z)).toContinuousLinearMap =
      clean.toContinuousLinearMap ∘L OrientedEdgeCayley.lift (fun _ => signQ) := by
  ext v b a
  rcases a with ⟨⟨e, z⟩, f⟩
  simp only [comp_apply, LinearIsometry.coe_toContinuousLinearMap, sign_apply, clean_apply]
  split_ifs <;> cases b <;>
    simp [signQ, OrientedEdgeCayley.lift_inl, OrientedEdgeCayley.lift_inr]

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The signed edge compression: `facOp† σ facOp = E_c`, `c` the entries at the oracle
values. -/
theorem facOp_sign (D : Data X n Z s) (κ : ℝ) (x : X) :
    (facOp D κ x)† ∘L OrientedEdgeCayley.lift (fun _ => signQ) ∘L facOp D κ x =
      entryGenerator (fun i j => entry D κ ((i, j), D.table x (i, j))) := by
  rw [facOp, lift_adjoint, ← OrientedEdgeCayley.lift_generator, ← mul_def, ← mul_def,
    ← OrientedEdgeCayley.lift_mul, ← OrientedEdgeCayley.lift_mul]
  congr 1
  funext e
  rw [mul_def, mul_def]
  exact facQ_sign _

omit [DecidableEq n] in
theorem norm_facQ_sq (c : ℂ) (y : Qubit) : ‖facQ c y‖ ^ 2 = ‖c‖ * ‖y‖ ^ 2 := by
  have h := congrArg (fun T : Qubit →L[ℂ] Qubit => inner ℂ y (T y)) (facQ_gram c)
  simp only [comp_apply, adjoint_inner_right, smul_apply, one_apply_eq_self,
    inner_smul_right] at h
  have h1 : ‖facQ c y‖ ^ 2 = RCLike.re (inner ℂ (facQ c y) (facQ c y)) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have h2 : ‖y‖ ^ 2 = RCLike.re (inner ℂ y y) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [h1, h2, h]
  simp

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The norm of the edge factor: `‖facOp w‖² = ∑_e |c_e| (|w_{e,row}|² + |w_{e,col}|²)`. -/
theorem norm_facOp_sq (D : Data X n Z s) (κ : ℝ) (x : X) (w : OrientedSpace n) :
    ‖facOp D κ x w‖ ^ 2 = ∑ e : n × n, ‖entry D κ (e, D.table x e)‖ *
      (‖w (.inl e)‖ ^ 2 + ‖w (.inr e)‖ ^ 2) := by
  rw [← OrientedEdgeCayley.regroup.norm_map, facOp, OrientedEdgeCayley.regroup_lift,
    PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro e _
  rw [WeightedClock.diagonal_apply, norm_facQ_sq, PiLp.norm_sq_eq_of_L2, Fintype.sum_bool,
    OrientedEdgeCayley.regroup_true, OrientedEdgeCayley.regroup_false, add_comm]

/-! ### The signed compression -/

omit [DecidableEq n] in
theorem matrixOperator_mul_const (a : ℂ) (H : Matrix n n ℂ) :
    SparseStateOverlap.matrixOperator (fun i j => H i j * a) =
      a • SparseStateOverlap.matrixOperator H := by
  ext v i
  simp only [SparseStateOverlap.matrixOperator_apply, smul_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq n] in
/-- The logical restriction of the sign: `clean† Z clean` is the edge sign. -/
theorem clean_sign_clean :
    (clean (n := n) (Z := Z)).toContinuousLinearMap† ∘L sign ∘L clean.toContinuousLinearMap =
      OrientedEdgeCayley.lift (fun _ => signQ) := by
  rw [sign_clean, ← comp_assoc, LinearIsometry.adjoint_comp_self, one_def, id_comp]

/-- **Signed compression** (`opt:eq:native-factor`): `B† Z B = H/(sκ)` for a Hermitian `H`
with entries of modulus at most `κ`. -/
theorem Cop_eq (D : Data X n Z s) {κ : ℝ} (hκ : 0 < κ) (x : X)
    (hH : (D.matrix x).IsHermitian) (hentry : ∀ i j, ‖D.matrix x i j‖ ≤ κ) :
    (known D).Cop ((factorProgram D κ).eval x) =
      ((((s : ℝ) * κ)⁻¹ : ℝ) : ℂ) • SparseStateOverlap.matrixOperator (D.matrix x) := by
  set M : Matrix n n ℂ := fun i j => D.matrix x i j * (κ : ℂ)⁻¹ with hM_def
  have hM : (fun i j => entry D κ ((i, j), D.table x (i, j))) = M := by
    funext i j
    rw [entry_table D x (i, j) (hentry i j) hκ, div_eq_mul_inv]
  have hMH : M.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [hM_def, star_mul', hH.apply i j, star_inv₀, Complex.star_def,
      Complex.conj_ofReal]
  have hrow : ∀ i j, M i j ≠ 0 → SparseSlotStates.selected (D.rowloc x) i j := by
    intro i j h
    apply D.row_covers x i j
    intro h0
    exact h (by simp [hM_def, h0])
  have hcol : ∀ i j, M i j ≠ 0 → SparseSlotStates.selected (D.colloc x) j i := by
    intro i j h
    apply D.column_covers x i j
    intro h0
    exact h (by simp [hM_def, h0])
  have hcomp := generator_compression D.slots_pos M hMH (D.rowloc x) (D.colloc x) hrow hcol
  rw [generator, smul_comp, comp_smul] at hcomp
  have hs0 : (Real.sqrt (s : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast D.slots_pos)
    exact_mod_cast this.ne'
  have hX : (boundary (D.rowloc x) (D.colloc x))† ∘L entryGenerator M ∘L
      boundary (D.rowloc x) (D.colloc x) =
      ((Real.sqrt (s : ℝ) : ℂ)⁻¹ * (Real.sqrt (s : ℝ) : ℂ)⁻¹) •
        SparseStateOverlap.matrixOperator M := by
    calc (boundary (D.rowloc x) (D.colloc x))† ∘L entryGenerator M ∘L
          boundary (D.rowloc x) (D.colloc x)
        = (Real.sqrt (s : ℝ) : ℂ)⁻¹ • ((Real.sqrt (s : ℝ) : ℂ) •
            ((boundary (D.rowloc x) (D.colloc x))† ∘L entryGenerator M ∘L
              boundary (D.rowloc x) (D.colloc x))) := by
          rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
      _ = _ := by rw [hcomp, smul_smul]
  have hkey : (known D).Cop ((factorProgram D κ).eval x) =
      (boundary (D.rowloc x) (D.colloc x))† ∘L entryGenerator M ∘L
        boundary (D.rowloc x) (D.colloc x) := by
    have hZ : (known D).Z = sign := rfl
    rw [Known.Cop, factor_eq, hZ, ← hM, ← facOp_sign, ← clean_sign_clean (n := n) (Z := Z)]
    simp only [adjoint_comp, comp_assoc]
  rw [hkey, hX, hM_def, matrixOperator_mul_const, smul_smul]
  congr 1
  have hr : Real.sqrt (s : ℝ) * Real.sqrt (s : ℝ) = (s : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg s)
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  rw [← mul_inv, ← Complex.ofReal_mul, hr, ← mul_inv]
  push_cast
  ring

/-! ### The successful weight -/

/-- Cauchy–Schwarz over the `s` listed slots of one row. -/
theorem sum_selected_le (loc : n → Fin s → n) (hinj : ∀ i, Function.Injective (loc i)) (i : n)
    (a : n → ℝ) (ha : ∀ j, 0 ≤ a j) {B : ℝ} (hB : 0 ≤ B) (hsq : ∑ j, a j ^ 2 ≤ B ^ 2) :
    ∑ j, (if SparseSlotStates.selected loc i j then a j else 0) ≤ Real.sqrt (s : ℝ) * B := by
  classical
  set ind : n → ℝ := fun j => if SparseSlotStates.selected loc i j then 1 else 0
  have hS : ∑ j, (if SparseSlotStates.selected loc i j then a j else 0) =
      ∑ j, ind j * a j := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : SparseSlotStates.selected loc i j <;> simp [ind, h]
  have hind : ∑ j, ind j ^ 2 = (s : ℝ) := by
    have h1 : ∑ j, ind j ^ 2 = ∑ j, (if SparseSlotStates.selected loc i j then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : SparseSlotStates.selected loc i j <;> simp [ind, h]
    rw [h1, SparseSlotStates.sum_selected loc hinj i (fun _ => (1 : ℝ))]
    simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ ind a
  rw [hind] at hcs
  have hnn : 0 ≤ ∑ j, ind j * a j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (by by_cases h : SparseSlotStates.selected loc i j <;>
      simp [ind, h]) (ha j)
  rw [hS]
  apply (sq_le_sq₀ hnn (mul_nonneg (Real.sqrt_nonneg _) hB)).mp
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg s)]
  calc (∑ j, ind j * a j) ^ 2 ≤ (s : ℝ) * ∑ j, a j ^ 2 := hcs
    _ ≤ (s : ℝ) * B ^ 2 := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg s)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- Squared entry moduli are bounded by the squared row energy. -/
theorem entry_row_sq_le (D : Data X n Z s) {κ η : ℝ} (hκ : 0 < κ) (x : X)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (i : n) :
    ∑ j, ‖entry D κ ((i, j), D.table x (i, j))‖ ^ 2 ≤ (η / κ) ^ 2 := by
  calc ∑ j, ‖entry D κ ((i, j), D.table x (i, j))‖ ^ 2
      ≤ ∑ j, (‖D.matrix x i j‖ / κ) ^ 2 :=
        Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _)
          (norm_entry_table_le D x (i, j) hκ) 2
    _ = (∑ j, ‖D.matrix x i j‖ ^ 2) / κ ^ 2 := by
        rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro j _; rw [div_pow]
    _ ≤ η ^ 2 / κ ^ 2 := by gcongr; exact hrow i
    _ = (η / κ) ^ 2 := (div_pow _ _ _).symm

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem entry_col_sq_le (D : Data X n Z s) {κ η : ℝ} (hκ : 0 < κ) (x : X)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (j : n) :
    ∑ i, ‖entry D κ ((i, j), D.table x (i, j))‖ ^ 2 ≤ (η / κ) ^ 2 := by
  calc ∑ i, ‖entry D κ ((i, j), D.table x (i, j))‖ ^ 2
      ≤ ∑ i, (‖D.matrix x i j‖ / κ) ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _)
          (norm_entry_table_le D x (i, j) hκ) 2
    _ = (∑ i, ‖D.matrix x i j‖ ^ 2) / κ ^ 2 := by
        rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro i _; rw [div_pow]
    _ ≤ η ^ 2 / κ ^ 2 := by gcongr; exact hcol j
    _ = (η / κ) ^ 2 := (div_pow _ _ _).symm

/-- **Successful weight**: `‖B v‖² ≤ η/(√s κ) ‖v‖²` from the row and column Euclidean norms. -/
theorem norm_factor_sq_le (D : Data X n Z s) {κ η : ℝ} (hκ : 0 < κ) (hη : 0 ≤ η) (x : X)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (v : EuclideanSpace ℂ n) :
    ‖(known D).factor ((factorProgram D κ).eval x) v‖ ^ 2 ≤
      η / (Real.sqrt (s : ℝ) * κ) * ‖v‖ ^ 2 := by
  classical
  set a : n → n → ℝ := fun i j => ‖entry D κ ((i, j), D.table x (i, j))‖ with ha_def
  have ha0 : ∀ i j, 0 ≤ a i j := fun i j => norm_nonneg _
  set w : ℝ := (2 * (s : ℝ))⁻¹ with hw
  have hB : 0 ≤ η / κ := div_nonneg hη hκ.le
  have hR : ∀ i, ∑ j, (if SparseSlotStates.selected (D.rowloc x) i j then a i j else 0) ≤
      Real.sqrt (s : ℝ) * (η / κ) := fun i =>
    sum_selected_le (D.rowloc x) (D.row_injective x) i (a i) (ha0 i) hB
      (entry_row_sq_le D hκ x hrow i)
  have hC : ∀ j, ∑ i, (if SparseSlotStates.selected (D.colloc x) j i then a i j else 0) ≤
      Real.sqrt (s : ℝ) * (η / κ) := fun j =>
    sum_selected_le (D.colloc x) (D.column_injective x) j (fun i => a i j) (fun i => ha0 i j)
      hB (entry_col_sq_le D hκ x hcol j)
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
  rw [factor_eq, comp_apply, comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map, norm_facOp_sq, Fintype.sum_prod_type]
  simp only [hJ, hJ']
  have hsplit : ∑ i, ∑ j, ‖entry D κ ((i, j), D.table x (i, j))‖ *
      (w * (if SparseSlotStates.selected (D.rowloc x) i j then ‖v i‖ ^ 2 else 0) +
        w * (if SparseSlotStates.selected (D.colloc x) j i then ‖v j‖ ^ 2 else 0)) =
      w * ∑ i, ‖v i‖ ^ 2 *
          ∑ j, (if SparseSlotStates.selected (D.rowloc x) i j then a i j else 0) +
        w * ∑ j, ‖v j‖ ^ 2 *
          ∑ i, (if SparseSlotStates.selected (D.colloc x) j i then a i j else 0) := by
    have e1 : w * ∑ i, ‖v i‖ ^ 2 *
        ∑ j, (if SparseSlotStates.selected (D.rowloc x) i j then a i j else 0) =
        ∑ i, ∑ j, w * (‖v i‖ ^ 2 *
          (if SparseSlotStates.selected (D.rowloc x) i j then a i j else 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum, Finset.mul_sum]
    have e2 : w * ∑ j, ‖v j‖ ^ 2 *
        ∑ i, (if SparseSlotStates.selected (D.colloc x) j i then a i j else 0) =
        ∑ i, ∑ j, w * (‖v j‖ ^ 2 *
          (if SparseSlotStates.selected (D.colloc x) j i then a i j else 0)) := by
      calc _ = ∑ j, ∑ i, w * (‖v j‖ ^ 2 *
            (if SparseSlotStates.selected (D.colloc x) j i then a i j else 0)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum, Finset.mul_sum]
        _ = _ := Finset.sum_comm
    rw [e1, e2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h1 : SparseSlotStates.selected (D.rowloc x) i j <;>
      by_cases h2 : SparseSlotStates.selected (D.colloc x) j i <;> simp [h1, h2, ha_def] <;> ring
  rw [hsplit]
  have hv : ‖v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
  have hw0 : 0 ≤ w := by positivity
  have h1 : ∑ i, ‖v i‖ ^ 2 *
      ∑ j, (if SparseSlotStates.selected (D.rowloc x) i j then a i j else 0) ≤
      Real.sqrt (s : ℝ) * (η / κ) * ‖v‖ ^ 2 := by
    rw [hv, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      rw [mul_comm (Real.sqrt (s : ℝ) * (η / κ))]
      exact mul_le_mul_of_nonneg_left (hR i) (sq_nonneg _)
  have h2 : ∑ j, ‖v j‖ ^ 2 *
      ∑ i, (if SparseSlotStates.selected (D.colloc x) j i then a i j else 0) ≤
      Real.sqrt (s : ℝ) * (η / κ) * ‖v‖ ^ 2 := by
    rw [hv, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      rw [mul_comm (Real.sqrt (s : ℝ) * (η / κ))]
      exact mul_le_mul_of_nonneg_left (hC j) (sq_nonneg _)
  have hs : (0 : ℝ) < s := by exact_mod_cast D.slots_pos
  have hsq : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr hs
  have hr : Real.sqrt (s : ℝ) * Real.sqrt (s : ℝ) = (s : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg s)
  have heq : w * (Real.sqrt (s : ℝ) * (η / κ) * ‖v‖ ^ 2) +
      w * (Real.sqrt (s : ℝ) * (η / κ) * ‖v‖ ^ 2) =
      η / (Real.sqrt (s : ℝ) * κ) * ‖v‖ ^ 2 := by
    set r := Real.sqrt (s : ℝ) with hr_def
    rw [hw, ← hr]
    field_simp
    ring
  calc _ ≤ w * (Real.sqrt (s : ℝ) * (η / κ) * ‖v‖ ^ 2) +
        w * (Real.sqrt (s : ℝ) * (η / κ) * ‖v‖ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hw0) (mul_le_mul_of_nonneg_left h2 hw0)
    _ = _ := heq

/-- **Successful weight** (`opt:eq:whole-factor`): `B† B ⪯ η/(√s κ) I`. -/
theorem Dop_le (D : Data X n Z s) {κ η : ℝ} (hκ : 0 < κ) (hη : 0 ≤ η) (x : X)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    (known D).Dop ((factorProgram D κ).eval x) ≤
      ((η / (Real.sqrt (s : ℝ) * κ) : ℝ) : ℂ) • (1 : EuclideanSpace ℂ n →L[ℂ] _) :=
  adjoint_comp_self_le (norm_factor_sq_le D hκ hη x hrow hcol)

/-! ### The exact successful weight -/

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The edge Gram operator: `facOp† facOp` multiplies both orientations of edge `e` by `|c_e|`. -/
theorem facOp_gram (D : Data X n Z s) (κ : ℝ) (x : X) :
    (facOp D κ x)† ∘L facOp D κ x = OrientedEdgeCayley.lift (fun e =>
      ((‖entry D κ (e, D.table x e)‖ : ℝ) : ℂ) • (1 : Qubit →L[ℂ] Qubit)) := by
  rw [facOp, lift_adjoint, ← mul_def, ← OrientedEdgeCayley.lift_mul]
  congr 1
  funext e
  rw [mul_def]
  exact facQ_gram _

omit [DecidableEq n] in
theorem lift_scalar_stack (a : n × n → ℂ) (A B : EuclideanSpace ℂ n →L[ℂ] EdgeSpace n) :
    OrientedEdgeCayley.lift (fun e => a e • (1 : Qubit →L[ℂ] Qubit)) ∘L stack A B =
      stack (edgeDiagonal (fun i j => a (i, j)) ∘L A)
        (edgeDiagonal (fun i j => a (i, j)) ∘L B) := by
  ext v e
  rcases e with ⟨i, j⟩ | ⟨i, j⟩ <;> rfl

/-- **Exact successful weight** (`opt:eq:native-factor`): `B† B = D_H/(sκ)` with
`D_H = diag(∑_j |H_ij|)`, for a Hermitian `H` with entries of modulus at most `κ`. -/
theorem Dop_eq (D : Data X n Z s) {κ : ℝ} (hκ : 0 < κ) (x : X)
    (hH : (D.matrix x).IsHermitian) (hentry : ∀ i j, ‖D.matrix x i j‖ ≤ κ) :
    (known D).Dop ((factorProgram D κ).eval x) =
      ((((s : ℝ) * κ)⁻¹ : ℝ) : ℂ) • SparseStateOverlap.matrixOperator
        (Matrix.diagonal (fun i => ((∑ j, ‖D.matrix x i j‖ : ℝ) : ℂ))) := by
  classical
  set a : n × n → ℂ := fun e => ((‖entry D κ (e, D.table x e)‖ : ℝ) : ℂ) with ha_def
  have ha : ∀ i j, a (i, j) = ((‖D.matrix x i j‖ / κ : ℝ) : ℂ) := by
    intro i j
    simp only [ha_def]
    rw [entry_table D x (i, j) (hentry i j) hκ, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hκ]
  have hkey : (known D).Dop ((factorProgram D κ).eval x) =
      (boundary (D.rowloc x) (D.colloc x))† ∘L
        (OrientedEdgeCayley.lift (fun e => a e • (1 : Qubit →L[ℂ] Qubit))) ∘L
          boundary (D.rowloc x) (D.colloc x) := by
    rw [Known.Dop, factor_eq, ← facOp_gram]
    simp only [adjoint_comp, comp_assoc]
    rw [← comp_assoc (((clean (n := n) (Z := Z)).toContinuousLinearMap)†)
      (clean (n := n) (Z := Z)).toContinuousLinearMap, LinearIsometry.adjoint_comp_self,
      one_def, id_comp]
  rw [hkey]
  ext v i
  simp only [boundary, map_smulₛₗ, conj_boundaryWeight, smul_comp, comp_smul,
    lift_scalar_stack, stack_adjoint_stack, smul_apply, add_apply, comp_apply,
    PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, rowIncidence_adjoint_apply,
    columnIncidence_adjoint_apply, edgeDiagonal_apply, rowIncidence_apply,
    columnIncidence_apply, SparseStateOverlap.matrixOperator_apply, Matrix.diagonal_apply]
  have hrowsum : (∑ j, if SparseSlotStates.selected (D.rowloc x) i j then
      a (i, j) * (if SparseSlotStates.selected (D.rowloc x) i j then v i else 0) else 0) =
      ((∑ j, ‖D.matrix x i j‖ / κ : ℝ) : ℂ) * v i := by
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [ha]
    by_cases h : SparseSlotStates.selected (D.rowloc x) i j
    · simp [h]
    · have h0 : D.matrix x i j = 0 := by
        by_contra hne
        exact h (D.row_covers x i j hne)
      simp [h, h0]
  have hcolsum : (∑ k, if SparseSlotStates.selected (D.colloc x) i k then
      a (k, i) * (if SparseSlotStates.selected (D.colloc x) i k then v i else 0) else 0) =
      ((∑ j, ‖D.matrix x i j‖ / κ : ℝ) : ℂ) * v i := by
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [ha]
    have hsym : ‖D.matrix x k i‖ = ‖D.matrix x i k‖ := by
      rw [← hH.apply i k, norm_star]
    by_cases h : SparseSlotStates.selected (D.colloc x) i k
    · simp [h, hsym]
    · have h0 : D.matrix x k i = 0 := by
        by_contra hne
        exact h (D.column_covers x k i hne)
      have h0' : D.matrix x i k = 0 := by
        rw [← norm_eq_zero, ← hsym, h0, norm_zero]
      simp [h, h0']
  rw [hrowsum, hcolsum]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hw : boundaryWeight s * boundaryWeight s = ((2 * (s : ℝ))⁻¹ : ℝ) := by
    have h := boundaryWeight_norm_sq s
    unfold boundaryWeight at h ⊢
    rw [← Complex.ofReal_mul]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
    rw [← h, sq]
  have hs : (s : ℝ) ≠ 0 := by exact_mod_cast D.slots_pos.ne'
  rw [← mul_assoc, hw]
  push_cast
  rw [← Finset.sum_div]
  field_simp
  ring

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- `D_H ⪯ √s η I` (`opt:eq:whole-factor`): every absolute row sum is at most `√s η`, by
Cauchy–Schwarz over the `s` listed slots of the row. -/
theorem row_abs_sum_le (D : Data X n Z s) {η : ℝ} (hη : 0 ≤ η) (x : X)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (i : n) :
    ∑ j, ‖D.matrix x i j‖ ≤ Real.sqrt (s : ℝ) * η := by
  have h := sum_selected_le (D.rowloc x) (D.row_injective x) i (fun j => ‖D.matrix x i j‖)
    (fun j => norm_nonneg _) hη (hrow i)
  refine le_of_eq_of_le ?_ h
  apply Finset.sum_congr rfl
  intro j _
  by_cases hs : SparseSlotStates.selected (D.rowloc x) i j
  · simp [hs]
  · have h0 : D.matrix x i j = 0 := by
      by_contra hne
      exact hs (D.row_covers x i j hne)
    simp [hs, h0]

end

end NativeSignedFactor
