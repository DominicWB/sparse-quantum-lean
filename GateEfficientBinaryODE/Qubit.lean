import GateEfficientBinaryODE.Swap
import GateEfficientBinary.Sparse.Simulation

/-!
# The four-sector private register as qubits

With indices given by `k`-bit words (`en : Cfg (Fin k) ≃ n`), the four-sector private space
`Space4 n` (part, orientation, tagged edge) is carried by the qubits `PR4 k = Fin (k + 3) ⊕ Fin k`:
the ancilla wires `0`, `1`, `2` hold the orientation, the tag and the part, the ancilla wires
`3, …, k + 2` the second index and the system wires the first index (`phi4`). The space is
flattened to `ℓ²(Bool × Bool × ((n × n) ⊕ (n × n)))` (`flat4`) and lifted to the qubits by the
qubit lift of `GateEfficientBinary` (`qlift4`, a unital star algebra homomorphism and a
contraction).

* `qlift4_loc4`: the lifted locator applies the row location oracle to the index wires when the
  orientation and the tag agree and the column location oracle otherwise;
* `qlift4_dg_lift`: the lift of an edgewise operation of both parts is the one-qubit operation on
  the orientation wire selected by the part, the tag and the edge.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary
open SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateODE (overwrite_apply_ι overwrite_apply_out)
open NativeSparseBlockEncoding (Data)
open scoped InnerProduct

/-! ### Wires -/

/-- The private register: the ancilla wires `Fin (k + 3)` and the system wires `Fin k`. -/
abbrev PR4 (k : ℕ) := Fin (k + 3) ⊕ Fin k

variable {k : ℕ}

/-- The orientation wire, ancilla `0`. -/
def oW (k : ℕ) : PR4 k := Sum.inl ⟨0, by omega⟩

/-- The tag wire, ancilla `1`. -/
def tW (k : ℕ) : PR4 k := Sum.inl ⟨1, by omega⟩

/-- The part wire, ancilla `2`. -/
def pW (k : ℕ) : PR4 k := Sum.inl ⟨2, by omega⟩

/-- The index wires: the first index on the system wires, the second index on the ancilla wires
`3, …, k + 2`. -/
def ix4 (k : ℕ) : EW k → PR4 k
  | Sum.inl j => Sum.inr j
  | Sum.inr j => Sum.inl ⟨j.val + 3, by omega⟩

theorem ix4_injective (k : ℕ) : Function.Injective (ix4 k) := by
  rintro (e | e) (e' | e') h <;> simp only [ix4, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq,
    Fin.mk.injEq] at h
  · rw [h]
  · exact congrArg Sum.inr (Fin.ext (by omega))

@[simp] theorem ix4_ne_oW (e : EW k) : ix4 k e ≠ oW k := by
  rcases e with e | e <;> simp [ix4, oW]

@[simp] theorem ix4_ne_tW (e : EW k) : ix4 k e ≠ tW k := by
  rcases e with e | e <;> simp [ix4, tW]

@[simp] theorem ix4_ne_pW (e : EW k) : ix4 k e ≠ pW k := by
  rcases e with e | e <;> simp [ix4, pW]

@[simp] theorem oW_ne_tW : oW k ≠ tW k := by simp [oW, tW]

@[simp] theorem oW_ne_pW : oW k ≠ pW k := by simp [oW, pW]

@[simp] theorem tW_ne_pW : tW k ≠ pW k := by simp [tW, pW]

/-! ### Configurations -/

/-- The configuration with part `p`, orientation `o`, tag `t` and indices `d`. -/
def mk4 (p o t : Bool) (d : Cfg (EW k)) : Cfg (PR4 k) :=
  Sum.elim (fun i : Fin (k + 3) => if h : i.val < 3 then
      (if i.val = 0 then o else if i.val = 1 then t else p)
    else d (Sum.inr ⟨i.val - 3, by have := i.isLt; omega⟩)) (fun j => d (Sum.inl j))

@[simp] theorem mk4_oW (p o t : Bool) (d : Cfg (EW k)) : mk4 p o t d (oW k) = o := by
  simp [mk4, oW]

@[simp] theorem mk4_tW (p o t : Bool) (d : Cfg (EW k)) : mk4 p o t d (tW k) = t := by
  simp [mk4, tW]

@[simp] theorem mk4_pW (p o t : Bool) (d : Cfg (EW k)) : mk4 p o t d (pW k) = p := by
  simp [mk4, pW]

@[simp] theorem mk4_ix (p o t : Bool) (d : Cfg (EW k)) (e : EW k) :
    mk4 p o t d (ix4 k e) = d e := by
  rcases e with e | e
  · rfl
  · simp [mk4, ix4]

/-- A configuration of the private register is determined by its four parts. -/
theorem cfg4_ext {c c' : Cfg (PR4 k)} (hp : c (pW k) = c' (pW k)) (ho : c (oW k) = c' (oW k))
    (ht : c (tW k) = c' (tW k)) (hd : ∀ e, c (ix4 k e) = c' (ix4 k e)) : c = c' := by
  funext w
  rcases w with ⟨i, hi⟩ | j
  · rcases i with _ | _ | _ | i
    · exact ho
    · exact ht
    · exact hp
    · exact hd (Sum.inr ⟨i, by omega⟩)
  · exact hd (Sum.inl j)

theorem mk4_eta (c : Cfg (PR4 k)) :
    mk4 (c (pW k)) (c (oW k)) (c (tW k)) (fun e => c (ix4 k e)) = c :=
  cfg4_ext (by simp) (by simp) (by simp) (fun e => by simp)

/-! ### Tagged edges of configurations -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The tagged edge held by the tag and index wires. -/
def te (en : Cfg (Fin k) ≃ n) (c : Cfg (PR4 k)) : (n × n) ⊕ (n × n) :=
  if c (tW k) then Sum.inr (phiE en (fun e => c (ix4 k e)))
  else Sum.inl (phiE en (fun e => c (ix4 k e)))

/-- The configuration of a tagged edge. -/
def ofTe (en : Cfg (Fin k) ≃ n) (p o : Bool) : (n × n) ⊕ (n × n) → Cfg (PR4 k)
  | Sum.inl d => mk4 p o false ((phiE en).symm d)
  | Sum.inr d => mk4 p o true ((phiE en).symm d)

omit [Fintype n] [DecidableEq n] in
theorem te_ofTe (en : Cfg (Fin k) ≃ n) (p o : Bool) (e : (n × n) ⊕ (n × n)) :
    te en (ofTe en p o e) = e := by
  rcases e with d | d <;> simp [te, ofTe]

omit [Fintype n] [DecidableEq n] in
theorem ofTe_te (en : Cfg (Fin k) ≃ n) (c : Cfg (PR4 k)) :
    ofTe en (c (pW k)) (c (oW k)) (te en c) = c := by
  unfold te
  cases h : c (tW k)
  · simp only [Bool.false_eq_true, if_false, ofTe, Equiv.symm_apply_apply]
    conv_rhs => rw [← mk4_eta c]
    rw [h]
  · simp only [if_true, ofTe, Equiv.symm_apply_apply]
    conv_rhs => rw [← mk4_eta c]
    rw [h]

omit [Fintype n] [DecidableEq n] in
@[simp] theorem pW_ofTe (en : Cfg (Fin k) ≃ n) (p o : Bool) (e : (n × n) ⊕ (n × n)) :
    ofTe en p o e (pW k) = p := by
  rcases e with d | d <;> simp [ofTe]

omit [Fintype n] [DecidableEq n] in
@[simp] theorem oW_ofTe (en : Cfg (Fin k) ≃ n) (p o : Bool) (e : (n × n) ⊕ (n × n)) :
    ofTe en p o e (oW k) = o := by
  rcases e with d | d <;> simp [ofTe]

/-- **The qubit identification** of the four-sector index set: part, orientation, tagged edge. -/
def phi4 (en : Cfg (Fin k) ≃ n) : Cfg (PR4 k) ≃ Bool × (Bool × ((n × n) ⊕ (n × n))) where
  toFun c := (c (pW k), (c (oW k), te en c))
  invFun z := ofTe en z.1 z.2.1 z.2.2
  left_inv c := ofTe_te en c
  right_inv z := by
    obtain ⟨p, o, e⟩ := z
    simp [te_ofTe]

omit [Fintype n] [DecidableEq n] in
theorem phi4_apply (en : Cfg (Fin k) ≃ n) (c : Cfg (PR4 k)) :
    phi4 en c = (c (pW k), (c (oW k), te en c)) := rfl

omit [Fintype n] [DecidableEq n] in
/-- Two configurations agree off the orientation wire iff their parts and tagged edges agree. -/
theorem update_oW_eq_iff (en : Cfg (Fin k) ≃ n) (y c : Cfg (PR4 k)) (b : Bool) :
    Function.update y (oW k) b = c ↔
      b = c (oW k) ∧ y (pW k) = c (pW k) ∧ te en y = te en c := by
  constructor
  · rintro rfl
    refine ⟨by simp, by rw [Function.update_of_ne (Ne.symm oW_ne_pW)], ?_⟩
    unfold te
    rw [Function.update_of_ne (Ne.symm oW_ne_tW)]
    have : (fun e => Function.update y (oW k) b (ix4 k e)) = fun e => y (ix4 k e) := by
      funext e
      exact Function.update_of_ne (ix4_ne_oW e) _ _
    rw [this]
  · rintro ⟨hb, hp, ht⟩
    have h2 : ofTe en (y (pW k)) b (te en y) = Function.update y (oW k) b := by
      conv_rhs => rw [← ofTe_te en (Function.update y (oW k) b)]
      have hpp : Function.update y (oW k) b (pW k) = y (pW k) :=
        Function.update_of_ne (Ne.symm oW_ne_pW) _ _
      have hte : te en (Function.update y (oW k) b) = te en y := by
        unfold te
        rw [Function.update_of_ne (Ne.symm oW_ne_tW)]
        have : (fun e => Function.update y (oW k) b (ix4 k e)) = fun e => y (ix4 k e) := by
          funext e
          exact Function.update_of_ne (ix4_ne_oW e) _ _
        rw [this]
      rw [hpp, hte, Function.update_self]
    rw [← h2, ht, hp, hb, ofTe_te]

/-! ### Flattening the four-sector space -/

/-- The index set of the four-sector space. -/
abbrev I4 (n : Type*) := Bool × (Bool × ((n × n) ⊕ (n × n)))

/-- **The flattening** `Space4 n ≃ ℓ²(I4 n)`. -/
def flat4 : Space4 n ≃ₗᵢ[ℂ] EuclideanSpace ℂ (I4 n) where
  toLinearEquiv :=
    { toFun := fun v => WithLp.toLp 2 (fun z => v z.1 z.2.1 z.2.2)
      invFun := fun w => WithLp.toLp 2 (fun p => WithLp.toLp 2 (fun o => WithLp.toLp 2
        (fun e => w (p, (o, e)))))
      left_inv := by intro v; rfl
      right_inv := by intro w; rfl
      map_add' := by intro v w; rfl
      map_smul' := by intro c v; rfl }
  norm_map' := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖(WithLp.toLp 2 (fun z : I4 n => v z.1 z.2.1 z.2.2) : EuclideanSpace ℂ (I4 n))‖ ^ 2 =
      ‖v‖ ^ 2
    rw [EuclideanSpace.norm_sq_eq, PiLp.norm_sq_eq_of_L2]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro p _
    rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro o _
    rw [EuclideanSpace.norm_sq_eq]

omit [DecidableEq n] in
@[simp] theorem flat4_apply (v : Space4 n) (z : I4 n) : flat4 v z = v z.1 z.2.1 z.2.2 := rfl

omit [DecidableEq n] in
@[simp] theorem flat4_symm_apply (w : EuclideanSpace ℂ (I4 n)) (p o : Bool)
    (e : (n × n) ⊕ (n × n)) : flat4.symm w p o e = w (p, (o, e)) := rfl

/-! ### The lift -/

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The qubit lift** of the four-sector space, a unital star algebra homomorphism. -/
def q4hom (en : Cfg (Fin k) ≃ n) :
    (Space4 n →L[ℂ] Space4 n) →⋆ₐ[ℂ] (Reg (PR4 k) R →L[ℂ] Reg (PR4 k) R) :=
  (qliftHom (R := R) (phi4 en)).comp (flat4 (n := n)).conjStarAlgEquiv.toStarAlgHom

/-- The qubit lift of a four-sector operator. -/
abbrev qlift4 (en : Cfg (Fin k) ≃ n) (A : Space4 n →L[ℂ] Space4 n) :
    Reg (PR4 k) R →L[ℂ] Reg (PR4 k) R :=
  q4hom (R := R) en A

theorem qlift4_eq (en : Cfg (Fin k) ≃ n) (A : Space4 n →L[ℂ] Space4 n) :
    qlift4 (R := R) en A = qlift (phi4 en) (flat4.conjStarAlgEquiv A) := rfl

theorem qlift4_mul (en : Cfg (Fin k) ≃ n) (A B : Space4 n →L[ℂ] Space4 n) :
    qlift4 (R := R) en (A * B) = qlift4 en A * qlift4 en B :=
  map_mul _ A B

theorem qlift4_comp (en : Cfg (Fin k) ≃ n) (A B : Space4 n →L[ℂ] Space4 n) :
    qlift4 (R := R) en (A ∘L B) = qlift4 en A ∘L qlift4 en B :=
  map_mul _ A B

theorem qlift4_one (en : Cfg (Fin k) ≃ n) :
    qlift4 (R := R) en (1 : Space4 n →L[ℂ] Space4 n) = 1 :=
  map_one _

theorem qlift4_sub (en : Cfg (Fin k) ≃ n) (A B : Space4 n →L[ℂ] Space4 n) :
    qlift4 (R := R) en (A - B) = qlift4 en A - qlift4 en B :=
  map_sub _ A B

theorem qlift4_add (en : Cfg (Fin k) ≃ n) (A B : Space4 n →L[ℂ] Space4 n) :
    qlift4 (R := R) en (A + B) = qlift4 en A + qlift4 en B :=
  map_add _ A B

theorem qlift4_smul (en : Cfg (Fin k) ≃ n) (c : ℂ) (A : Space4 n →L[ℂ] Space4 n) :
    qlift4 (R := R) en (c • A) = c • qlift4 en A :=
  map_smul _ c A

theorem qlift4_adjoint (en : Cfg (Fin k) ≃ n) (A : Space4 n →L[ℂ] Space4 n) :
    qlift4 (R := R) en (A†) = (qlift4 en A)† :=
  map_star _ A

theorem qlift4_isUnitary (en : Cfg (Fin k) ≃ n) {A : Space4 n →L[ℂ] Space4 n}
    (hA : IsUnitary A) : IsUnitary (qlift4 (R := R) en A) := by
  have h1 : star A * A = 1 := hA.1
  have h2 : A * star A = 1 := hA.2
  constructor
  · rw [← map_star (q4hom (R := R) en), ← map_mul, h1, map_one]
  · rw [← map_star (q4hom (R := R) en), ← map_mul, h2, map_one]

omit [DecidableEq n] in
theorem norm_conj_flat4_le (A : Space4 n →L[ℂ] Space4 n) :
    ‖(flat4 (n := n)).conjStarAlgEquiv A‖ ≤ ‖A‖ := by
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply]
  refine (opNorm_comp_le _ _).trans ?_
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans ?_
  · exact LinearIsometry.norm_toContinuousLinearMap_le _
  · refine (opNorm_comp_le _ _).trans ?_
    exact mul_le_of_le_one_right (norm_nonneg _) (LinearIsometry.norm_toContinuousLinearMap_le _)

theorem norm_qlift4_le (en : Cfg (Fin k) ≃ n) (A : Space4 n →L[ℂ] Space4 n) :
    ‖qlift4 (R := R) en A‖ ≤ ‖A‖ :=
  (norm_qlift_le _ _).trans (norm_conj_flat4_le A)

/-- The lift on the ancilla register with the system payload. -/
abbrev elift4 (en : Cfg (Fin k) ≃ n) (A : Space4 n →L[ℂ] Space4 n) :
    Reg (Fin (k + 3)) (Reg (Fin k) R) →L[ℂ] Reg (Fin (k + 3)) (Reg (Fin k) R) :=
  unconj (qlift4 (R := R) en A)

theorem elift4_comp (en : Cfg (Fin k) ≃ n) (A B : Space4 n →L[ℂ] Space4 n) :
    elift4 (R := R) en (A ∘L B) = elift4 (R := R) en A ∘L elift4 (R := R) en B := by
  rw [elift4, qlift4_comp, unconj_comp]

theorem elift4_one (en : Cfg (Fin k) ≃ n) :
    elift4 (R := R) en (1 : Space4 n →L[ℂ] Space4 n) = 1 := by
  rw [elift4, qlift4_one, unconj_one]

theorem elift4_sub (en : Cfg (Fin k) ≃ n) (A B : Space4 n →L[ℂ] Space4 n) :
    elift4 (R := R) en (A - B) = elift4 (R := R) en A - elift4 (R := R) en B := by
  rw [elift4, qlift4_sub, unconj_sub]

theorem elift4_adjoint (en : Cfg (Fin k) ≃ n) (A : Space4 n →L[ℂ] Space4 n) :
    elift4 (R := R) en (A†) = (elift4 (R := R) en A)† := by
  rw [elift4, qlift4_adjoint, unconj_adjoint]

theorem norm_elift4_le (en : Cfg (Fin k) ≃ n) (A : Space4 n →L[ℂ] Space4 n) :
    ‖elift4 (R := R) en A‖ ≤ ‖A‖ :=
  (norm_unconj_le _).trans (norm_qlift4_le _ _)

theorem elift4_isUnitary (en : Cfg (Fin k) ≃ n) {A : Space4 n →L[ℂ] Space4 n}
    (hA : IsUnitary A) : IsUnitary (elift4 (R := R) en A) :=
  unconj_isUnitary (qlift4_isUnitary _ hA)

/-! ### Matrix entries -/

theorem flat4_symm_single (z : I4 n) (p o : Bool) (e : (n × n) ⊕ (n × n)) :
    (flat4 (n := n)).symm (EuclideanSpace.single z 1) p o e =
      if (p, (o, e)) = z then 1 else 0 := by
  rw [flat4_symm_apply]
  simp

/-- The coordinates of the lift of an operator on a basis vector. -/
theorem qlift4_bas_apply (en : Cfg (Fin k) ≃ n) (A : Space4 n →L[ℂ] Space4 n)
    (c y : Cfg (PR4 k)) (q : R) :
    qlift4 en A (bas c q) y =
      A ((flat4 (n := n)).symm (EuclideanSpace.single (phi4 en c) 1)) (y (pW k)) (y (oW k))
        (te en y) • q := by
  rw [qlift4_eq, qlift_bas_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, flat4_apply]
  rfl

/-! ### The edgewise action -/

theorem regroup_flat4_single (z : I4 n) (p : Bool) (e : (n × n) ⊕ (n × n)) :
    ODETaggedCayley.regroup ((flat4 (n := n)).symm (EuclideanSpace.single z 1) p) e =
      if p = z.1 ∧ e = z.2.2 then EuclideanSpace.single z.2.1 1 else 0 := by
  obtain ⟨p0, o0, e0⟩ := z
  apply PiLp.ext
  intro b
  rw [ODETaggedCayley.regroup_apply, flat4_symm_single]
  by_cases h : p = p0 ∧ e = e0
  · rw [if_pos h]
    obtain ⟨rfl, rfl⟩ := h
    by_cases hb : b = o0
    · subst hb
      simp
    · simp [hb]
  · rw [if_neg h]
    have : (p, (b, e)) ≠ (p0, (o0, e0)) := by
      intro h'
      simp only [Prod.mk.injEq] at h'
      exact h ⟨h'.1, h'.2.2⟩
    simp [this]

/-- **The lifted edgewise operation**: the lift of `G p` on the edges of the part `p` is the
one-qubit operation `G p e` on the orientation wire, for the part and the tagged edge `e` of the
other wires. -/
theorem qlift4_dg_lift (en : Cfg (Fin k) ≃ n)
    (G : Bool → (n × n) ⊕ (n × n) → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit) :
    qlift4 (R := R) en (dg (fun p => ODETaggedCayley.lift (G p))) =
      condOp (oW k) (fun c => qmat (G (c (pW k)) (te en c))) := by
  apply ext_bas_clm
  intro c q
  apply PiLp.ext
  intro y
  rw [qlift4_bas_apply, condOp_apply]
  simp only [WeightedClock.diagonal_apply, ODETaggedCayley.lift_apply, regroup_flat4_single,
    phi4_apply]
  have hupd : ∀ b, Function.update y (oW k) b = c ↔
      b = c (oW k) ∧ y (pW k) = c (pW k) ∧ te en y = te en c := update_oW_eq_iff en y c
  have hp0 : Function.update y (oW k) false (pW k) = y (pW k) :=
    Function.update_of_ne (Ne.symm oW_ne_pW) _ _
  have hte0 : te en (Function.update y (oW k) false) = te en y := by
    unfold te
    rw [Function.update_of_ne (Ne.symm oW_ne_tW)]
    have : (fun e => Function.update y (oW k) false (ix4 k e)) = fun e => y (ix4 k e) := by
      funext e
      exact Function.update_of_ne (ix4_ne_oW e) _ _
    rw [this]
  simp only [bas_apply, hupd, hp0, hte0]
  rw [Finset.sum_eq_single (c (oW k))]
  · by_cases h : y (pW k) = c (pW k) ∧ te en y = te en c
    · obtain ⟨h1, h2⟩ := h
      simp only [h1, h2, and_self, if_true, qmat]
    · have h' : ¬ (y (pW k) = c (pW k) ∧ te en y = te en c) := h
      simp only [h', if_false, and_false]
      simp
  · intro b _ hb
    simp [hb]
  · simp

/-! ### The locator -/

omit [Fintype n] [DecidableEq n] in
theorem te_eq_iff (en : Cfg (Fin k) ≃ n) (y c : Cfg (PR4 k)) :
    te en y = te en c ↔ y (tW k) = c (tW k) ∧
      (fun e => y (ix4 k e)) = fun e => c (ix4 k e) := by
  unfold te
  constructor
  · intro h
    cases hy : y (tW k) <;> cases hc : c (tW k) <;> rw [hy, hc] at h <;>
      simp only [Bool.false_eq_true, if_false, if_true, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq] at h
    · exact ⟨rfl, (phiE en).injective h⟩
    · exact ⟨rfl, (phiE en).injective h⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

@[simp] theorem block_single_inl_inl (A B : EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n))
    (d d' : n × n) : FixedLocatorConjugation.block A B (EuclideanSpace.single (Sum.inl d) 1)
      (Sum.inl d') = A (EuclideanSpace.single d 1) d' := by
  rw [FixedLocatorConjugation.block_inl, leftPart_single_inl]

@[simp] theorem block_single_inl_inr (A B : EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n))
    (d d' : n × n) : FixedLocatorConjugation.block A B (EuclideanSpace.single (Sum.inl d) 1)
      (Sum.inr d') = 0 := by
  rw [FixedLocatorConjugation.block_inr, rightPart_single_inl]
  simp

@[simp] theorem block_single_inr_inl (A B : EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n))
    (d d' : n × n) : FixedLocatorConjugation.block A B (EuclideanSpace.single (Sum.inr d) 1)
      (Sum.inl d') = 0 := by
  rw [FixedLocatorConjugation.block_inl, leftPart_single_inr]
  simp

@[simp] theorem block_single_inr_inr (A B : EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n))
    (d d' : n × n) : FixedLocatorConjugation.block A B (EuclideanSpace.single (Sum.inr d) 1)
      (Sum.inr d') = B (EuclideanSpace.single d 1) d' := by
  rw [FixedLocatorConjugation.block_inr, rightPart_single_inr]

omit [Fintype n] [DecidableEq n] [InnerProductSpace ℂ R] [CompleteSpace R] in
theorem slice_ix4_bas (c y : Cfg (PR4 k)) (q : R) :
    slice (ix4 k) (bas c q) y =
      if y (pW k) = c (pW k) ∧ y (oW k) = c (oW k) ∧ y (tW k) = c (tW k) then
        bas (fun e => c (ix4 k e)) q else 0 := by
  apply PiLp.ext
  intro d
  rw [slice_apply, bas_apply]
  have hov : overwrite (ix4 k) y d =
      mk4 (y (pW k)) (y (oW k)) (y (tW k)) d := by
    apply cfg4_ext
    · rw [overwrite_apply_out _ y d _ (fun e => ix4_ne_pW e), mk4_pW]
    · rw [overwrite_apply_out _ y d _ (fun e => ix4_ne_oW e), mk4_oW]
    · rw [overwrite_apply_out _ y d _ (fun e => ix4_ne_tW e), mk4_tW]
    · intro e
      rw [overwrite_apply_ι (ix4_injective k), mk4_ix]
  rw [hov]
  have hiff : mk4 (y (pW k)) (y (oW k)) (y (tW k)) d = c ↔
      (y (pW k) = c (pW k) ∧ y (oW k) = c (oW k) ∧ y (tW k) = c (tW k)) ∧
        d = fun e => c (ix4 k e) := by
    constructor
    · rintro rfl
      exact ⟨⟨by simp, by simp, by simp⟩, funext fun e => by simp⟩
    · rintro ⟨⟨h1, h2, h3⟩, rfl⟩
      rw [h1, h2, h3, mk4_eta]
  by_cases h : y (pW k) = c (pW k) ∧ y (oW k) = c (oW k) ∧ y (tW k) = c (tW k)
  · rw [if_pos h, bas_apply]
    by_cases hd : d = fun e => c (ix4 k e)
    · rw [if_pos (hiff.2 ⟨h, hd⟩), if_pos hd]
    · rw [if_neg (fun h' => hd (hiff.1 h').2), if_neg hd]
  · rw [if_neg (fun h' => h (hiff.1 h').1), if_neg h]
    simp

attribute [local simp] leftPart_single_inl leftPart_single_inr rightPart_single_inl
  rightPart_single_inr in
/-- **The lifted locator**: the row location oracle on the index wires when the orientation and
the tag agree, the column location oracle otherwise. -/
theorem qlift4_loc4 {X Z : Type*} {s : ℕ} (D : Data X n Z s) (en : Cfg (Fin k) ≃ n) (x : X) :
    qlift4 (R := R) en (loc4 D x) =
      localOp (ix4 k) (ix4_injective k) (fun c => if c (oW k) = c (tW k) then
        qlift (phiE en) (D.rowOracle x) else qlift (phiE en) (D.columnOracle x)) := by
  apply ext_bas_clm
  intro c q
  apply PiLp.ext
  intro y
  rw [qlift4_bas_apply, localOp_apply, slice_ix4_bas]
  have ho : clearCfg (ix4 k) y (oW k) = y (oW k) :=
    overwrite_apply_out _ y _ _ (fun e => ix4_ne_oW e)
  have ht : clearCfg (ix4 k) y (tW k) = y (tW k) :=
    overwrite_apply_out _ y _ _ (fun e => ix4_ne_tW e)
  simp only [ho, ht]
  simp only [loc4, locS, WeightedClock.diagonal_apply, phi4_apply]
  have hte : ∀ z : Cfg (PR4 k), te en z = if z (tW k) then
      Sum.inr (phiE en (fun e => z (ix4 k e))) else Sum.inl (phiE en (fun e => z (ix4 k e))) :=
    fun z => rfl
  by_cases hpo : y (pW k) = c (pW k) ∧ y (oW k) = c (oW k)
  · have hw : (flat4 (n := n)).symm (EuclideanSpace.single (c (pW k), c (oW k), te en c) 1)
        (y (pW k)) (y (oW k)) = EuclideanSpace.single (te en c) 1 := by
      apply PiLp.ext
      intro e
      rw [flat4_symm_single, hpo.1, hpo.2]
      by_cases he : e = te en c
      · subst he
        simp
      · simp [he]
    rw [hw]
    by_cases h3 : y (tW k) = c (tW k)
    · rw [if_pos (⟨hpo.1, hpo.2, h3⟩ : y (pW k) = c (pW k) ∧ y (oW k) = c (oW k) ∧
        y (tW k) = c (tW k)), hte y, hte c, ← h3]
      cases hyo : y (oW k) <;> cases hyt : y (tW k) <;> simp [qlift_bas_apply]
    · rw [if_neg (fun h : y (pW k) = c (pW k) ∧ y (oW k) = c (oW k) ∧ y (tW k) = c (tW k) =>
        h3 h.2.2), hte y, hte c]
      cases hy : y (tW k) <;> cases hc : c (tW k) <;> rw [hy, hc] at h3 <;>
        first
        | exact absurd rfl h3
        | (cases hyo : y (oW k) <;> simp)
  · have hw : (flat4 (n := n)).symm (EuclideanSpace.single (c (pW k), c (oW k), te en c) 1)
        (y (pW k)) (y (oW k)) = 0 := by
      apply PiLp.ext
      intro e
      rw [flat4_symm_single, if_neg]
      · rfl
      intro h'
      simp only [Prod.mk.injEq] at h'
      exact hpo ⟨h'.1, h'.2.1⟩
    rw [hw, if_neg (fun h : y (pW k) = c (pW k) ∧ y (oW k) = c (oW k) ∧ y (tW k) = c (tW k) =>
      hpo ⟨h.1, h.2.1⟩)]
    simp

end

end SparseHamiltonian.GateBinaryODE
