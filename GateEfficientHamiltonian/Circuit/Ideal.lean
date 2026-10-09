import GateEfficientHamiltonian.Circuit.LCU

/-!
# Unitarity and clean-subspace invariance of the ideal operators

Every ideal macro operation of the simulator is unitary, and it maps vectors
supported on clean configurations (all work wires zero) to such vectors, as
does its adjoint (`Pres2`).  These facts are needed to compose gate-level
agreement statements and to transfer them to inverse circuits.
-/

namespace SparseHamiltonian.GateCircuit

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators

section General

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

theorem isUnitary_comp {A B : Reg W Q →L[ℂ] Reg W Q} (hA : IsUnitary A) (hB : IsUnitary B) :
    IsUnitary (A ∘L B) := by
  rw [← mul_def]; exact hA.mul hB

theorem isUnitary_adj {A : Reg W Q →L[ℂ] Reg W Q} (hA : IsUnitary A) : IsUnitary (A†) := by
  rw [← star_eq_adjoint]; exact hA.adjoint

theorem unitary_adj_comp {A : Reg W Q →L[ℂ] Reg W Q} (h : IsUnitary A) : A† ∘L A = 1 := by
  have := h.1; rwa [star_eq_adjoint, mul_def] at this

theorem unitary_comp_adj {A : Reg W Q →L[ℂ] Reg W Q} (h : IsUnitary A) : A ∘L A† = 1 := by
  have := h.2; rwa [star_eq_adjoint, mul_def] at this

theorem isUnitary_neg {A : Reg W Q →L[ℂ] Reg W Q} (h : IsUnitary A) : IsUnitary (-A) := by
  constructor
  · rw [star_neg, neg_mul_neg]; exact h.1
  · rw [star_neg, neg_mul_neg]; exact h.2

theorem isUnitary_permOp (e : Cfg W ≃ Cfg W) : IsUnitary (permOp (Q := Q) e) := by
  constructor
  · rw [star_eq_adjoint, permOp_adjoint, mul_def, permOp_comp, Equiv.self_trans_symm, permOp_refl]
  · rw [star_eq_adjoint, permOp_adjoint, mul_def, permOp_comp, Equiv.symm_trans_self, permOp_refl]

theorem condOp_isUnitary' (t : W) (u : Cfg W → Matrix Bool Bool ℂ)
    (hu : ∀ x, UnitaryMat (u x)) : IsUnitary (condOp (Q := Q) t u) :=
  condOp_isUnitary t u hu

theorem unitaryMat_ite (p : Prop) [Decidable p] (u : Matrix Bool Bool ℂ) (hu : UnitaryMat u) :
    UnitaryMat (if p then u else 1) := by
  split_ifs
  · exact hu
  · exact one_unitaryMat

/-! ### Invariance of a predicate on configurations -/

/-- `O` and its adjoint both preserve the `S`-supported vectors. -/
def Pres2 (S : Cfg W → Prop) (O : Reg W Q →L[ℂ] Reg W Q) : Prop :=
  Preserves S O ∧ Preserves S (O†)

theorem Pres2.comp {S : Cfg W → Prop} {A B : Reg W Q →L[ℂ] Reg W Q} (hA : Pres2 S A)
    (hB : Pres2 S B) : Pres2 S (A ∘L B) :=
  ⟨hB.1.comp hA.1, by rw [adjoint_comp]; exact hA.2.comp hB.2⟩

theorem Pres2.adj {S : Cfg W → Prop} {A : Reg W Q →L[ℂ] Reg W Q} (h : Pres2 S A) :
    Pres2 S (A†) :=
  ⟨h.2, by rw [adjoint_adjoint]; exact h.1⟩

omit [CompleteSpace Q] in
theorem preserves_neg {S : Cfg W → Prop} {A : Reg W Q →L[ℂ] Reg W Q} (h : Preserves S A) :
    Preserves S (-A) := by
  intro ψ hψ x hx
  rw [neg_apply]
  simp [h ψ hψ x hx]

theorem Pres2.neg {S : Cfg W → Prop} {A : Reg W Q →L[ℂ] Reg W Q} (h : Pres2 S A) :
    Pres2 S (-A) :=
  ⟨preserves_neg h.1, by rw [map_neg]; exact preserves_neg h.2⟩

theorem pres2_one (S : Cfg W → Prop) : Pres2 S (1 : Reg W Q →L[ℂ] Reg W Q) := by
  refine ⟨Preserves.one S, ?_⟩
  have : (1 : Reg W Q →L[ℂ] Reg W Q)† = 1 := by
    rw [← star_eq_adjoint, star_one]
  rw [this]; exact Preserves.one S

theorem preserves_condOp (S : Cfg W → Prop) (t : W) (u : Cfg W → Matrix Bool Bool ℂ)
    (hS : ∀ x b, S x → S (Function.update x t b)) : Preserves S (condOp (Q := Q) t u) := by
  intro ψ hψ x hx
  rw [condOp_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [hψ _ (fun h => hx (by
    have := hS _ (x t) h
    rwa [Function.update_idem, Function.update_eq_self] at this)), smul_zero]

theorem pres2_condOp (S : Cfg W → Prop) (t : W) (u : Cfg W → Matrix Bool Bool ℂ)
    (hS : ∀ x b, S x → S (Function.update x t b)) : Pres2 S (condOp (Q := Q) t u) := by
  refine ⟨preserves_condOp S t u hS, ?_⟩
  rw [condOp_adjoint]
  exact preserves_condOp S t _ hS

theorem pres2_gateOp (S : Cfg W → Prop) (cs : List (W × Bool)) (t : W)
    (u : Matrix Bool Bool ℂ) (hS : ∀ x b, S x → S (Function.update x t b)) :
    Pres2 S (gateOp (Q := Q) cs t u) :=
  pres2_condOp S t _ hS

omit [Fintype W] in
theorem overwrite_overwrite {A : Type*} [Fintype A] [DecidableEq A] (ι : A → W) (x : Cfg W)
    (b b' : Cfg A) : overwrite ι (overwrite ι x b) b' = overwrite ι x b' := by
  simp only [overwrite, outPart_joinCfg]

theorem preserves_localOp {A : Type*} [Fintype A] [DecidableEq A] (S : Cfg W → Prop)
    (ι : A → W) (hι : Function.Injective ι) (F : Cfg W → (Reg A Q →L[ℂ] Reg A Q))
    (hS : ∀ y b, S y → S (overwrite ι y b)) : Preserves S (localOp ι hι F) := by
  intro ψ hψ x hx
  rw [localOp_apply]
  have h0 : slice ι ψ x = 0 := by
    apply PiLp.ext
    intro b
    rw [slice_apply]
    apply hψ
    intro h
    apply hx
    have := hS _ (fun a => x (ι a)) h
    rwa [overwrite_overwrite, show overwrite ι x (fun a => x (ι a)) = x from joinCfg_self hι x]
      at this
  rw [h0, map_zero]
  rfl

theorem pres2_localOp {A : Type*} [Fintype A] [DecidableEq A] (S : Cfg W → Prop)
    (ι : A → W) (hι : Function.Injective ι) (F : Cfg W → (Reg A Q →L[ℂ] Reg A Q))
    (hS : ∀ y b, S y → S (overwrite ι y b)) : Pres2 S (localOp ι hι F) := by
  refine ⟨preserves_localOp S ι hι F hS, ?_⟩
  rw [localOp_adjoint]
  exact preserves_localOp S ι hι _ hS

omit [CompleteSpace Q] in
theorem preserves_permOp (S : Cfg W → Prop) (e : Cfg W ≃ Cfg W) (he : ∀ x, S x → S (e x)) :
    Preserves S (permOp (Q := Q) e) := by
  intro ψ hψ x hx
  rw [permOp_apply]
  apply hψ
  intro h
  apply hx
  have := he _ h
  rwa [Equiv.apply_symm_apply] at this

theorem pres2_permOp (S : Cfg W → Prop) (e : Cfg W ≃ Cfg W) (he : ∀ x, S x → S (e x))
    (he' : ∀ x, S x → S (e.symm x)) : Pres2 S (permOp (Q := Q) e) := by
  refine ⟨preserves_permOp S e he, ?_⟩
  rw [permOp_adjoint]
  exact preserves_permOp S e.symm he'

end General

namespace Sim

open GatePointerEncoding (wordValue wordEquivFin wordFin successorEquiv)
open ChronologicalResolvent CoherentReuse
open GateDyadicBoundary (centralCosine centralSine)

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Clean configurations are closed under logical updates -/

theorem clean_update_of_logical (x : Cfg (Wire a m r K)) (w : Wire a m r K) (b : Bool)
    (hw : isFlag w = false) (h : Clean x) : Clean (Function.update x w b) :=
  (clean_update_logical x w b hw).mpr h

theorem clean_overwrite_anc (y : Cfg (Wire a m r K)) (b : Cfg (Fin a)) (h : Clean y) :
    Clean (overwrite Wire.anc y b) :=
  (clean_overwrite y b).mpr h

theorem clean_incEquiv (x : Cfg (Wire a m r K)) (h : Clean x) :
    Clean (incEquiv (K := K) (m := m) (a := a) x) := by
  change Clean (incFun (successorEquiv r) x)
  unfold incFun
  split_ifs
  · exact (clean_setPtr _ _).mpr h
  · exact h

theorem clean_incEquiv_symm (x : Cfg (Wire a m r K)) (h : Clean x) :
    Clean ((incEquiv (K := K) (m := m) (a := a)).symm x) := by
  change Clean (incFun (successorEquiv r).symm x)
  unfold incFun
  split_ifs
  · exact (clean_setPtr _ _).mpr h
  · exact h

/-! ### Clean invariance of the ideal operators -/

theorem pres2_frameCond (j : Fin (cap r + 1)) (i : Fin m) (R : Matrix Bool Bool ℂ) :
    Pres2 Clean (frameCond (a := a) (K := K) (P := P) j i R) :=
  pres2_condOp _ _ _ (fun x b h => clean_update_of_logical x _ b rfl h)

theorem pres2_centralCond (j : Fin (cap r + 1)) (zz vv : ℝ) :
    Pres2 Clean (centralCond (a := a) (K := K) (P := P) (m := m) j zz vv) :=
  pres2_condOp _ _ _ (fun x b h => clean_update_of_logical x _ b rfl h)

theorem pres2_regAscend (j : Fin (cap r + 1)) (R : ℕ → Matrix Bool Bool ℂ) (n : ℕ)
    (hn : n ≤ m) : Pres2 Clean (regAscend (a := a) (K := K) (P := P) j R n hn) := by
  induction n with
  | zero => exact pres2_one _
  | succ n ih => exact (pres2_frameCond _ _ _).comp (ih _)

theorem pres2_regDescend (j : Fin (cap r + 1)) (R : ℕ → Matrix Bool Bool ℂ) (n : ℕ)
    (hn : n ≤ m) : Pres2 Clean (regDescend (a := a) (K := K) (P := P) j R n hn) := by
  induction n with
  | zero => exact pres2_one _
  | succ n ih => exact (ih _).comp (pres2_frameCond _ _ _)

theorem pres2_NET (j : Fin (cap r + 1)) (c σ : ℝ) :
    Pres2 Clean (NET (a := a) (K := K) (P := P) (m := m) j c σ) :=
  (pres2_regDescend _ _ _ _).comp ((pres2_centralCond _ _ _).comp (pres2_regAscend _ _ _ _))

theorem pres2_secOracle (O : Vsp a P →L[ℂ] Vsp a P) :
    Pres2 Clean (secOracle (K := K) (m := m) (r := r) O) := by
  unfold secOracle oracleOp
  exact pres2_localOp _ _ _ _ (fun y b h => clean_overwrite_anc y b h)

theorem pres2_BNET (j : Fin (cap r + 1)) (c σ : ℝ) (UJ : Vsp a P →L[ℂ] Vsp a P) :
    Pres2 Clean (BNET (K := K) (m := m) j c σ UJ) :=
  (pres2_secOracle _).comp ((pres2_NET _ _ _).comp (pres2_secOracle _))

theorem pres2_INC : Pres2 Clean (INC (K := K) (m := m) (a := a) (r := r) (P := P)) :=
  pres2_permOp _ _ (fun x h => clean_incEquiv x h) (fun x h => clean_incEquiv_symm x h)

theorem pres2_STEP (j : Fin (cap r + 1)) (c σ : ℝ) (UJ D : Vsp a P →L[ℂ] Vsp a P) :
    Pres2 Clean (STEP (K := K) (m := m) j c σ UJ D) :=
  pres2_INC.comp ((pres2_BNET _ _ _ _).comp (pres2_secOracle _))

theorem pres2_selectN (c σ : ℝ) (UJ D : Vsp a P →L[ℂ] Vsp a P) (n : ℕ) :
    Pres2 Clean (selectN (K := K) (m := m) (r := r) c σ UJ D n) := by
  induction n with
  | zero => exact pres2_one _
  | succ n ih =>
      rw [selectN]
      split_ifs
      · exact (pres2_STEP _ _ _ _ _).comp ih
      · exact ih

theorem pres2_treeFrom {q : ℕ} (ts : Fin q → Wire a m r K) (hts : ∀ t, isFlag (ts t) = false)
    (M : Fin q → Cfg (Wire a m r K) → Matrix Bool Bool ℂ) (k : ℕ) (hk : k ≤ q) :
    Pres2 Clean (treeFrom (Q := P) ts M k hk) := by
  induction k with
  | zero => exact pres2_one _
  | succ k ih =>
      exact (ih _).comp (pres2_condOp _ _ _ (fun x b h => clean_update_of_logical x _ b (hts _) h))

theorem pres2_RANGE1 (lw : Word r) (n : ℕ) :
    Pres2 Clean (RANGE1 (K := K) (m := m) (a := a) (P := P) lw n) :=
  pres2_treeFrom _ (fun _ => rfl) _ _ _

theorem pres2_rangeL {L : ℕ} (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (l : List (Fin L)) :
    Pres2 Clean (rangeL (K := K) (m := m) (a := a) (P := P) hL nOf l) := by
  induction l with
  | nil => exact pres2_one _
  | cons ℓ l ih => exact (pres2_RANGE1 _ _).comp ih

theorem pres2_RANGE {L : ℕ} (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) :
    Pres2 Clean (RANGE (K := K) (m := m) (a := a) (P := P) hL nOf) :=
  pres2_rangeL _ _ _

theorem pres2_PREP (f : Word r → ℝ) :
    Pres2 Clean (PREP (K := K) (m := m) (a := a) (P := P) f) :=
  pres2_treeFrom _ (fun _ => rfl) _ _ _

theorem pres2_LCU {L : ℕ} (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ)
    (UJ D : Vsp a P →L[ℂ] Vsp a P) (N : ℕ) :
    Pres2 Clean (LCU (K := K) (m := m) hL nOf wt c σ UJ D N) :=
  (pres2_PREP _).adj.comp ((pres2_RANGE _ _).adj.comp ((pres2_selectN _ _ _ _ _).comp
    ((pres2_RANGE _ _).comp (pres2_PREP _))))

/-! ### Unitary matrices of the network -/

theorem kk_conj (z : ℝ) : (starRingEnd ℂ) (Dyadic.kk z) = Dyadic.kk z := by
  simp [Dyadic.kk]

theorem kk_sq' (z : ℝ) :
    ((GateDyadicBoundary.rootDenominator z : ℝ) : ℂ)⁻¹ ^ 2 * (1 + (z : ℂ) ^ 2) = 1 := by
  rw [pow_two]; exact Dyadic.kk_sq z

theorem unMat_unitary (z : ℝ) : UnitaryMat (Dyadic.unMat z) := by
  have hk := kk_sq' z
  constructor <;>
  · funext i j
    simp only [Matrix.mul_apply, Fintype.sum_bool, Matrix.conjTranspose_apply, Dyadic.unMat,
      Matrix.one_apply, RCLike.star_def]
    cases i <;> cases j <;> simp <;>
      first | ring1 | linear_combination hk

theorem outMat_unitary (z : ℝ) : UnitaryMat (Dyadic.outMat z) := by
  have hk := kk_sq' z
  constructor <;>
  · funext i j
    simp only [Matrix.mul_apply, Fintype.sum_bool, Matrix.conjTranspose_apply, Dyadic.outMat,
      Matrix.one_apply, RCLike.star_def]
    cases i <;> cases j <;> simp <;>
      first | ring1 | linear_combination hk

theorem rotMat_eq_rotC (z v : ℝ) : rotMat z v = rotC z v := by
  funext i j; cases i <;> cases j <;> rfl

theorem rotMat_unitary (z v : ℝ) (h : z ^ 2 + v ^ 2 = 1) : UnitaryMat (rotMat z v) := by
  rw [rotMat_eq_rotC]; exact rotC_unitary z v h

/-! ### Unitarity of the ideal operators -/

theorem frameCond_isUnitary (j : Fin (cap r + 1)) (i : Fin m) (R : Matrix Bool Bool ℂ)
    (hR : UnitaryMat R) : IsUnitary (frameCond (a := a) (K := K) (P := P) j i R) :=
  condOp_isUnitary' _ _ (fun _ => unitaryMat_ite _ R hR)

theorem regAscend_isUnitary (j : Fin (cap r + 1)) (R : ℕ → Matrix Bool Bool ℂ)
    (hR : ∀ k, UnitaryMat (R k)) (n : ℕ) (hn : n ≤ m) :
    IsUnitary (regAscend (a := a) (K := K) (P := P) j R n hn) := by
  induction n with
  | zero => exact isUnitary_one
  | succ n ih => exact isUnitary_comp (frameCond_isUnitary _ _ _ (hR n)) (ih _)

theorem regDescend_isUnitary (j : Fin (cap r + 1)) (R : ℕ → Matrix Bool Bool ℂ)
    (hR : ∀ k, UnitaryMat (R k)) (n : ℕ) (hn : n ≤ m) :
    IsUnitary (regDescend (a := a) (K := K) (P := P) j R n hn) := by
  induction n with
  | zero => exact isUnitary_one
  | succ n ih => exact isUnitary_comp (ih _) (frameCond_isUnitary _ _ _ (hR n))

theorem centralCond_isUnitary (j : Fin (cap r + 1)) (zz vv : ℝ) (h : zz ^ 2 + vv ^ 2 = 1) :
    IsUnitary (centralCond (a := a) (K := K) (P := P) (m := m) j zz vv) :=
  condOp_isUnitary' _ _ (fun _ => unitaryMat_ite _ _ (rotMat_unitary zz vv h))

theorem NET_isUnitary (j : Fin (cap r + 1)) (c σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1) :
    IsUnitary (NET (a := a) (K := K) (P := P) (m := m) j c σ) :=
  isUnitary_comp (regDescend_isUnitary _ _ (fun _ => outMat_unitary _) _ _)
    (isUnitary_comp (centralCond_isUnitary _ _ _ (GateDyadicBoundary.central_unit c σ hunit m))
      (regAscend_isUnitary _ _ (fun _ => unMat_unitary _) _ _))

theorem secOracle_isUnitary (O : Vsp a P →L[ℂ] Vsp a P) (hO : IsUnitary O) :
    IsUnitary (secOracle (K := K) (m := m) (r := r) O) :=
  oracleOp_isUnitary _ _ _ O hO

theorem BNET_isUnitary (j : Fin (cap r + 1)) (c σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1)
    (UJ : Vsp a P →L[ℂ] Vsp a P) (hUJ : IsUnitary UJ) :
    IsUnitary (BNET (K := K) (m := m) j c σ UJ) :=
  isUnitary_comp (secOracle_isUnitary _ hUJ)
    (isUnitary_comp (NET_isUnitary _ _ _ hunit) (secOracle_isUnitary _ (isUnitary_adj hUJ)))

theorem INC_isUnitary : IsUnitary (INC (K := K) (m := m) (a := a) (r := r) (P := P)) :=
  isUnitary_permOp _

theorem STEP_isUnitary (j : Fin (cap r + 1)) (c σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1)
    (UJ D : Vsp a P →L[ℂ] Vsp a P) (hUJ : IsUnitary UJ) (hD : IsUnitary D) :
    IsUnitary (STEP (K := K) (m := m) j c σ UJ D) :=
  isUnitary_comp INC_isUnitary
    (isUnitary_comp (BNET_isUnitary _ _ _ hunit _ hUJ) (secOracle_isUnitary _ hD))

theorem selectN_isUnitary (c σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1)
    (UJ D : Vsp a P →L[ℂ] Vsp a P) (hUJ : IsUnitary UJ) (hD : IsUnitary D) (n : ℕ) :
    IsUnitary (selectN (K := K) (m := m) (r := r) c σ UJ D n) := by
  induction n with
  | zero => exact isUnitary_one
  | succ n ih =>
      rw [selectN]
      split_ifs
      · exact isUnitary_comp (STEP_isUnitary _ _ _ hunit _ _ hUJ hD) ih
      · exact ih

theorem treeFrom_isUnitary {q : ℕ} (ts : Fin q → Wire a m r K)
    (M : Fin q → Cfg (Wire a m r K) → Matrix Bool Bool ℂ) (hM : ∀ s x, UnitaryMat (M s x))
    (k : ℕ) (hk : k ≤ q) : IsUnitary (treeFrom (Q := P) ts M k hk) := by
  induction k with
  | zero => exact isUnitary_one
  | succ k ih => exact isUnitary_comp (ih _) (condOp_isUnitary' _ _ (hM _))

theorem rangeLevel_unitary (n s : ℕ) (w : Word r) : UnitaryMat (rangeLevel n s w) := by
  unfold rangeLevel
  split_ifs
  · exact tightRot_unitary n s
  · exact hadC_unitary

theorem RANGE1_isUnitary (lw : Word r) (n : ℕ) :
    IsUnitary (RANGE1 (K := K) (m := m) (a := a) (P := P) lw n) := by
  apply treeFrom_isUnitary
  intro s x
  unfold rangeM
  split_ifs
  · exact rangeLevel_unitary _ _ _
  · exact one_unitaryMat

theorem rangeL_isUnitary {L : ℕ} (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (l : List (Fin L)) :
    IsUnitary (rangeL (K := K) (m := m) (a := a) (P := P) hL nOf l) := by
  induction l with
  | nil => exact isUnitary_one
  | cons ℓ l ih => exact isUnitary_comp (RANGE1_isUnitary _ _) ih

theorem RANGE_isUnitary {L : ℕ} (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) :
    IsUnitary (RANGE (K := K) (m := m) (a := a) (P := P) hL nOf) :=
  rangeL_isUnitary _ _ _

theorem PREP_isUnitary (f : Word r → ℝ) :
    IsUnitary (PREP (K := K) (m := m) (a := a) (P := P) f) :=
  treeFrom_isUnitary _ _ (fun s _ => treeMat_unitary f s _) _ _

theorem LCU_isUnitary {L : ℕ} (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ)
    (hunit : c ^ 2 + σ ^ 2 = 1) (UJ D : Vsp a P →L[ℂ] Vsp a P) (hUJ : IsUnitary UJ)
    (hD : IsUnitary D) (N : ℕ) :
    IsUnitary (LCU (K := K) (m := m) hL nOf wt c σ UJ D N) :=
  isUnitary_comp (isUnitary_adj (PREP_isUnitary _))
    (isUnitary_comp (isUnitary_adj (RANGE_isUnitary _ _))
      (isUnitary_comp (selectN_isUnitary _ _ hunit _ _ hUJ hD _)
        (isUnitary_comp (RANGE_isUnitary _ _) (PREP_isUnitary _))))

end Sim

end

end SparseHamiltonian.GateCircuit
