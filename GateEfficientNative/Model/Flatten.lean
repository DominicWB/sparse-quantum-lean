import GateEfficientNative.Model.Approx

/-!
# Flattening registers and clean work wires

The released gate-level libraries carry the system as an abstract payload `P`.
For a qubit system on wires `S` with an untouched reference `R` the payload is
`P = Reg S R`, and the register `Reg W (Reg S R)` is identified isometrically
with the flat register `Reg (W ⊕ S) R` (`flat`).  Conjugation by this
identification (`conj`) turns

* an elementary gate on `W` into the same gate on the wires `W` of `W ⊕ S`
  (`conj_gateOp`);
* an operator on exposed wires `ι` of `W` with payload `Reg S R` into the
  flattened operator on the exposed wires `ι ⊕ S` (`conj_localOp`).

Added work wires `X` are carried by `Reg (B ⊕ X) R`.  The clean embedding
`cleanEmb` puts every work wire at zero, `CleanX` is the predicate of clean
work wires, and `liftB O` acts as `O` on the wires `B` and as the identity on
the work wires; it commutes with the clean embedding (`liftB_cleanEmb`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateODE (overwrite_apply_ι overwrite_apply_out ctrlOK_map update_comp_injective)
open scoped InnerProduct BigOperators

/-! ### Flattening -/

section Flat

variable (W S : Type*) [Fintype W] [DecidableEq W] [Fintype S] [DecidableEq S]
variable (R : Type*) [NormedAddCommGroup R] [InnerProductSpace ℂ R]

/-- Configurations of `W ⊕ S` as pairs. -/
def cfgSumEquiv : Cfg (W ⊕ S) ≃ (Σ _ : Cfg W, Cfg S) :=
  (Equiv.sumArrowEquivProdArrow W S Bool).trans (Equiv.sigmaEquivProd (Cfg W) (Cfg S)).symm

/-- The isometric flattening of a register with a register payload. -/
def flat : Reg W (Reg S R) ≃ₗᵢ[ℂ] Reg (W ⊕ S) R :=
  (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : Cfg W) (_ : Cfg S) => R)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ R (cfgSumEquiv W S).symm)

variable {W S R}

theorem flat_apply (ψ : Reg W (Reg S R)) (y : Cfg (W ⊕ S)) :
    flat W S R ψ y = ψ (fun w => y (Sum.inl w)) (fun s => y (Sum.inr s)) := rfl

theorem flat_symm_apply (φ : Reg (W ⊕ S) R) (x : Cfg W) (s : Cfg S) :
    (flat W S R).symm φ x s = φ (Sum.elim x s) := by
  conv_rhs => rw [← (flat W S R).apply_symm_apply φ]
  rw [flat_apply]
  rfl

/-- The flattening as a continuous linear map. -/
abbrev fl : Reg W (Reg S R) →L[ℂ] Reg (W ⊕ S) R :=
  (flat W S R).toContinuousLinearEquiv.toContinuousLinearMap

/-- The inverse flattening. -/
abbrev unfl : Reg (W ⊕ S) R →L[ℂ] Reg W (Reg S R) :=
  (flat W S R).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem fl_unfl : (fl (W := W) (S := S) (R := R)) ∘L unfl = 1 := by
  ext φ; simp

theorem unfl_fl : (unfl (W := W) (S := S) (R := R)) ∘L fl = 1 := by
  ext ψ; simp

variable [CompleteSpace R]

theorem fl_adjoint : (fl (W := W) (S := S) (R := R))† = unfl := by
  apply ContinuousLinearMap.ext
  intro φ
  apply ext_inner_right ℂ
  intro ψ
  rw [adjoint_inner_left]
  have h := (flat W S R).inner_map_map ((flat W S R).symm φ) ψ
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h

/-- Conjugation by the flattening. -/
def conj (O : Reg W (Reg S R) →L[ℂ] Reg W (Reg S R)) : Reg (W ⊕ S) R →L[ℂ] Reg (W ⊕ S) R :=
  fl ∘L O ∘L unfl

omit [CompleteSpace R] in
theorem conj_comp (O O' : Reg W (Reg S R) →L[ℂ] Reg W (Reg S R)) :
    conj (O ∘L O') = conj O ∘L conj O' := by
  unfold conj
  ext φ
  simp

omit [CompleteSpace R] in
theorem conj_one : conj (1 : Reg W (Reg S R) →L[ℂ] Reg W (Reg S R)) = 1 := by
  unfold conj
  ext φ
  simp

theorem conj_adjoint (O : Reg W (Reg S R) →L[ℂ] Reg W (Reg S R)) :
    conj (O†) = (conj O)† := by
  unfold conj
  rw [adjoint_comp, adjoint_comp, fl_adjoint]
  have h : (unfl (W := W) (S := S) (R := R))† = fl := by
    rw [← fl_adjoint, adjoint_adjoint]
  rw [h, comp_assoc]

theorem conj_isUnitary {O : Reg W (Reg S R) →L[ℂ] Reg W (Reg S R)} (hO : IsUnitary O) :
    IsUnitary (conj O) := by
  constructor
  · rw [star_eq_adjoint, ← conj_adjoint, mul_def, ← conj_comp, ← mul_def, ← star_eq_adjoint,
      hO.1, conj_one]
  · rw [star_eq_adjoint, ← conj_adjoint, mul_def, ← conj_comp, ← mul_def, ← star_eq_adjoint,
      hO.2, conj_one]

omit [CompleteSpace R] in
theorem conj_apply (O : Reg W (Reg S R) →L[ℂ] Reg W (Reg S R)) (φ : Reg (W ⊕ S) R)
    (y : Cfg (W ⊕ S)) :
    conj O φ y = O ((flat W S R).symm φ) (fun w => y (Sum.inl w)) (fun s => y (Sum.inr s)) :=
  rfl

/-- Flattening an elementary gate. -/
theorem conj_gateOp (cs : List (W × Bool)) (t : W) (u : Matrix Bool Bool ℂ) :
    conj (gateOp (Q := Reg S R) cs t u) =
      gateOp (cs.map (fun c => (Sum.inl c.1, c.2))) (Sum.inl t) u := by
  ext φ y
  rw [conj_apply, gateOp, condOp_apply, gateOp, condOp_apply]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro b _
  have hu : (fun w => Function.update y (Sum.inl t) false (Sum.inl w)) =
      Function.update (fun w => y (Sum.inl w)) t false :=
    update_comp_injective Sum.inl_injective y t false
  have hsel : ctrlOK (cs.map (fun c => (Sum.inl c.1, c.2))) (Function.update y (Sum.inl t) false) =
      ctrlOK cs (Function.update (fun w => y (Sum.inl w)) t false) := by
    rw [ctrlOK_map, hu]
  rw [hsel, flat_symm_apply]
  have hcfg : (Sum.elim (Function.update (fun w => y (Sum.inl w)) t b) fun s => y (Sum.inr s)) =
      Function.update y (Sum.inl t) b := by
    funext v
    cases v with
    | inl w =>
        by_cases hw : w = t
        · subst hw; simp
        · simp [hw]
    | inr s =>
        simp
  rw [hcfg]

/-- Exposed wires of the flattened register. -/
def mapId {A : Type*} (ι : A → W) : A ⊕ S → W ⊕ S := Sum.map ι id

omit [Fintype W] [DecidableEq W] [Fintype S] [DecidableEq S] in
theorem mapId_injective {A : Type*} {ι : A → W} (hι : Function.Injective ι) :
    Function.Injective (mapId (S := S) ι) :=
  Sum.map_injective.mpr ⟨hι, Function.injective_id⟩

omit [Fintype W] [CompleteSpace R] in
theorem overwrite_mapId {A : Type*} [Fintype A] [DecidableEq A] {ι : A → W}
    (hι : Function.Injective ι) (y : Cfg (W ⊕ S)) (c : Cfg (A ⊕ S)) :
    overwrite (mapId (S := S) ι) y c =
      Sum.elim (overwrite ι (fun w => y (Sum.inl w)) (fun a => c (Sum.inl a)))
        (fun s => c (Sum.inr s)) := by
  funext v
  cases v with
  | inl w =>
      by_cases hw : ∃ a, ι a = w
      · obtain ⟨a, rfl⟩ := hw
        have h1 := overwrite_apply_ι (mapId_injective (S := S) hι) y c (Sum.inl a)
        have h2 := overwrite_apply_ι hι (fun w => y (Sum.inl w)) (fun a => c (Sum.inl a)) a
        exact h1.trans h2.symm
      · have hout : ∀ c, mapId (S := S) ι c ≠ Sum.inl w := by
          intro c hc
          cases c with
          | inl a => exact hw ⟨a, Sum.inl_injective hc⟩
          | inr s => cases hc
        rw [overwrite_apply_out _ y c _ hout]
        simp only [Sum.elim_inl]
        rw [overwrite_apply_out ι _ _ w (fun a ha => hw ⟨a, ha⟩)]
  | inr s =>
      exact overwrite_apply_ι (mapId_injective (S := S) hι) y c (Sum.inr s)

omit [CompleteSpace R] [Fintype W] in
theorem clearCfg_mapId {A : Type*} [Fintype A] [DecidableEq A] {ι : A → W}
    (hι : Function.Injective ι) (y : Cfg (W ⊕ S)) :
    (fun w => clearCfg (mapId (S := S) ι) y (Sum.inl w)) =
      clearCfg ι (fun w => y (Sum.inl w)) := by
  funext w
  rw [clearCfg, overwrite_mapId hι]
  rfl

/-- Flattening an operator on exposed wires. -/
theorem conj_localOp {A : Type*} [Fintype A] [DecidableEq A] {ι : A → W}
    (hι : Function.Injective ι) (F : Cfg W → (Reg A (Reg S R) →L[ℂ] Reg A (Reg S R))) :
    conj (localOp ι hι F : Reg W (Reg S R) →L[ℂ] Reg W (Reg S R)) =
      localOp (mapId (S := S) ι) (mapId_injective hι)
        (fun y => conj (F (fun w => y (Sum.inl w)))) := by
  ext φ y
  rw [conj_apply, localOp_apply, localOp_apply, conj_apply, clearCfg_mapId hι]
  have hs : (flat A S R).symm (slice (mapId (S := S) ι) φ y) =
      slice ι ((flat W S R).symm φ) (fun w => y (Sum.inl w)) := by
    apply PiLp.ext
    intro b
    apply PiLp.ext
    intro s
    rw [flat_symm_apply, slice_apply, slice_apply, flat_symm_apply, overwrite_mapId hι]
    congr 1
  rw [hs]
  rfl

end Flat

/-! ### Clean work wires -/

section Clean

variable {B X : Type*} [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R]

/-- Every added work wire is zero. -/
def CleanX (y : Cfg (B ⊕ X)) : Prop := ∀ x, y (Sum.inr x) = false

/-- The clean embedding: every added work wire is zero. -/
def cleanEmb : Reg B R →L[ℂ] Reg (B ⊕ X) R :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Cfg (B ⊕ X) => R)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun y =>
      if (fun x => y (Sum.inr x)) = (fun _ => false) then coord (fun b => y (Sum.inl b)) else 0)

omit [Fintype B] [DecidableEq B] [DecidableEq X] in
theorem cleanEmb_apply (ψ : Reg B R) (y : Cfg (B ⊕ X)) :
    cleanEmb ψ y = if (fun x => y (Sum.inr x)) = (fun _ => false) then ψ (fun b => y (Sum.inl b))
      else 0 := by
  change (if (fun x => y (Sum.inr x)) = (fun _ => false) then coord (fun b => y (Sum.inl b))
    else 0) ψ = _
  split_ifs <;> rfl

omit [Fintype B] [DecidableEq B] [DecidableEq X] in
theorem supp_cleanEmb (ψ : Reg B R) : Supp CleanX (cleanEmb (X := X) ψ) := by
  intro y hy
  rw [cleanEmb_apply, if_neg]
  intro h
  apply hy
  intro x
  exact congrFun h x

theorem norm_cleanEmb (ψ : Reg B R) : ‖cleanEmb (X := X) ψ‖ = ‖ψ‖ := by
  have hsq : ‖cleanEmb (X := X) ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    rw [← (Equiv.sumArrowEquivProdArrow B X Bool).symm.sum_comp, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_eq_single (fun _ => false)]
    · rw [cleanEmb_apply, if_pos]
      · rfl
      · rfl
    · intro x _ hx
      rw [cleanEmb_apply, if_neg]
      · simp
      · intro h
        apply hx
        exact h
    · intro h; exact absurd (Finset.mem_univ _) h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

variable [CompleteSpace R]

/-- `O` on the wires `B`, the identity on the work wires. -/
def liftB (O : Reg B R →L[ℂ] Reg B R) : Reg (B ⊕ X) R →L[ℂ] Reg (B ⊕ X) R :=
  localOp Sum.inl Sum.inl_injective (fun _ => O)

theorem liftB_comp (O O' : Reg B R →L[ℂ] Reg B R) :
    liftB (X := X) (O ∘L O') = liftB O ∘L liftB O' := by
  unfold liftB
  rw [localOp_comp]

theorem liftB_one : liftB (X := X) (1 : Reg B R →L[ℂ] Reg B R) = 1 := by
  unfold liftB
  exact localOp_one _

theorem liftB_adjoint (O : Reg B R →L[ℂ] Reg B R) : liftB (X := X) (O†) = (liftB O)† := by
  unfold liftB
  rw [localOp_adjoint]

theorem liftB_isUnitary {O : Reg B R →L[ℂ] Reg B R} (hO : IsUnitary O) :
    IsUnitary (liftB (X := X) O) :=
  localOp_isUnitary _ _ (fun _ => hO)

omit [Fintype X] [CompleteSpace R] in
theorem overwrite_inl_inr (y : Cfg (B ⊕ X)) (b : Cfg B) (x : X) :
    overwrite (Sum.inl : B → B ⊕ X) y b (Sum.inr x) = y (Sum.inr x) :=
  overwrite_apply_out _ y b _ (fun c hc => by cases hc)

theorem preserves_liftB (O : Reg B R →L[ℂ] Reg B R) : Preserves CleanX (liftB (X := X) O) := by
  apply preserves_localOp
  intro y b hy x
  rw [overwrite_inl_inr]
  exact hy x

theorem pres2_liftB (O : Reg B R →L[ℂ] Reg B R) : Pres2 CleanX (liftB (X := X) O) := by
  refine ⟨preserves_liftB O, ?_⟩
  rw [← liftB_adjoint]
  exact preserves_liftB _

/-- The lifted operator commutes with the clean embedding. -/
theorem liftB_cleanEmb (O : Reg B R →L[ℂ] Reg B R) :
    liftB (X := X) O ∘L cleanEmb = cleanEmb ∘L O := by
  ext ψ y
  rw [comp_apply, comp_apply, liftB, localOp_apply, cleanEmb_apply]
  have hs : slice (Sum.inl : B → B ⊕ X) (cleanEmb ψ) y =
      if (fun x => y (Sum.inr x)) = (fun _ => false) then ψ else 0 := by
    apply PiLp.ext
    intro b
    rw [slice_apply, cleanEmb_apply]
    have h1 : (fun x => overwrite (Sum.inl : B → B ⊕ X) y b (Sum.inr x)) =
        (fun x => y (Sum.inr x)) := funext (fun x => overwrite_inl_inr y b x)
    have h2 : (fun c => overwrite (Sum.inl : B → B ⊕ X) y b (Sum.inl c)) = b :=
      funext (fun c => overwrite_apply_ι Sum.inl_injective y b c)
    rw [h1, h2]
    split_ifs <;> simp
  rw [hs]
  split_ifs
  · rfl
  · simp

/-- The clean-embedding form of approximate agreement with a lifted ideal. -/
theorem norm_sub_cleanEmb_le {C : Reg (B ⊕ X) R →L[ℂ] Reg (B ⊕ X) R}
    {O : Reg B R →L[ℂ] Reg B R} {δ : ℝ} (h : ApproxOn CleanX C (liftB O) δ) (hδ : 0 ≤ δ) :
    ‖C ∘L cleanEmb - cleanEmb ∘L O‖ ≤ δ :=
  norm_comp_sub_le (W := B ⊕ X) (Q := R) (P := Reg B R) (cleanEmb (X := X)) O h hδ
    supp_cleanEmb norm_cleanEmb (liftB_cleanEmb O)

end Clean

end

end SparseHamiltonian.GateNative
