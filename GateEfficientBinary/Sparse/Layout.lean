import GateEfficientBinary.Sparse.Lift
import GateEfficientNative.Native.Lift
import SparseHamiltonian.FixedNativeCayleySimulation

/-!
# The private edge register as qubits

The private register of the sparse Cayley operation is the oriented edge space
`ℓ²((n × n) ⊕ (n × n))` (`SparseEdgeMoments.OrientedSpace n`): an orientation and an edge
`(i, j)`. With indices given by `k`-bit words (`en : Cfg (Fin k) ≃ n`) it is carried by the
qubits `PR k = Fin (k + 1) ⊕ Fin k`: the ancilla wire `0` holds the orientation, the ancilla
wires `1, …, k` the second index `j` and the system wires the first index `i` (`phiPR`).

* `qlift_block`: the lift of a full locator `block A B` (`A` on the first orientation, `B` on
  the second) applies `A` or `B` to the index wires, selected by the orientation wire;
* `qlift_lift`: the lift of an edgewise operation `OrientedEdgeCayley.lift G` is the one-qubit
  operation `G e` on the orientation wire, selected by the edge `e` held by the index wires;
* `qmat_action`: the matrix of the exact edge action `ExactEdgeCayley.action z` is the edge
  rotation `edgeMat z` of the native model;
* `unconj`, `liftE`, `selOp_unconj`: operators on the flat private register as selected private
  operations without selection wires.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinary

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateODE (overwrite_apply_ι overwrite_apply_out)
open scoped InnerProduct ComplexConjugate

/-! ### Wires and configurations -/

/-- The wires of an edge register: the first index (`inl`) and the second index (`inr`). -/
abbrev EW (k : ℕ) := Fin k ⊕ Fin k

/-- The private register: the ancilla wires `Fin (k + 1)` and the system wires `Fin k`. -/
abbrev PR (k : ℕ) := Fin (k + 1) ⊕ Fin k

/-- The orientation wire, the ancilla wire `0`. -/
def oPR (k : ℕ) : PR k := Sum.inl 0

/-- The index wires: the first index on the system wires, the second index on the ancilla
wires `1, …, k`. -/
def ixPR (k : ℕ) : EW k → PR k
  | Sum.inl j => Sum.inr j
  | Sum.inr j => Sum.inl j.succ

theorem ixPR_injective (k : ℕ) : Function.Injective (ixPR k) := by
  rintro (e | e) (e' | e') h <;> simp_all [ixPR]

theorem ixPR_ne_o (k : ℕ) (e : EW k) : ixPR k e ≠ oPR k := by
  rcases e with e | e <;> simp [ixPR, oPR, Fin.succ_ne_zero]

variable {k : ℕ}

/-- The configuration of the private register with orientation `b` and indices `d`. -/
def mkPR (b : Bool) (d : Cfg (EW k)) : Cfg (PR k) :=
  Sum.elim (Fin.cons b (fun j => d (Sum.inr j)) : Fin (k + 1) → Bool) (fun j => d (Sum.inl j))

@[simp] theorem mkPR_o (b : Bool) (d : Cfg (EW k)) : mkPR b d (oPR k) = b := by
  simp [mkPR, oPR]

@[simp] theorem mkPR_ix (b : Bool) (d : Cfg (EW k)) (e : EW k) : mkPR b d (ixPR k e) = d e := by
  rcases e with e | e <;> simp [mkPR, ixPR]

theorem mkPR_eta (c : Cfg (PR k)) : mkPR (c (oPR k)) (fun e => c (ixPR k e)) = c := by
  funext w
  rcases w with i | j
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp [mkPR, oPR]
    · simp [mkPR, ixPR]
  · simp [mkPR, ixPR]

theorem mkPR_eq_iff (b : Bool) (d : Cfg (EW k)) (c : Cfg (PR k)) :
    mkPR b d = c ↔ b = c (oPR k) ∧ d = fun e => c (ixPR k e) := by
  constructor
  · rintro rfl
    exact ⟨(mkPR_o b d).symm, funext fun e => (mkPR_ix b d e).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact mkPR_eta c

theorem overwrite_ixPR (y : Cfg (PR k)) (d : Cfg (EW k)) :
    overwrite (ixPR k) y d = mkPR (y (oPR k)) d := by
  rw [← mkPR_eta (overwrite (ixPR k) y d), overwrite_apply_out _ y d _ (ixPR_ne_o k)]
  congr 1
  funext e
  exact overwrite_apply_ι (ixPR_injective k) y d e

theorem update_oPR (y : Cfg (PR k)) (b : Bool) :
    Function.update y (oPR k) b = mkPR b (fun e => y (ixPR k e)) := by
  rw [← mkPR_eta (Function.update y (oPR k) b), Function.update_self]
  congr 1
  funext e
  exact Function.update_of_ne (ixPR_ne_o k e) _ _

/-! ### Edges of configurations -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The index pair held by an edge register. -/
def phiE (en : Cfg (Fin k) ≃ n) : Cfg (EW k) ≃ n × n where
  toFun d := (en (fun j => d (Sum.inl j)), en (fun j => d (Sum.inr j)))
  invFun p := Sum.elim (en.symm p.1) (en.symm p.2)
  left_inv d := by
    funext e
    rcases e with j | j <;> simp
  right_inv p := by simp

omit [Fintype n] [DecidableEq n] in
theorem phiE_apply (en : Cfg (Fin k) ≃ n) (d : Cfg (EW k)) :
    phiE en d = (en (fun j => d (Sum.inl j)), en (fun j => d (Sum.inr j))) := rfl

/-- The oriented edge held by the private register. -/
def phiPR (en : Cfg (Fin k) ≃ n) : Cfg (PR k) ≃ (n × n) ⊕ (n × n) where
  toFun c := if c (oPR k) then Sum.inr (phiE en (fun e => c (ixPR k e)))
    else Sum.inl (phiE en (fun e => c (ixPR k e)))
  invFun := Sum.elim (fun p => mkPR false ((phiE en).symm p))
    (fun p => mkPR true ((phiE en).symm p))
  left_inv c := by
    conv_rhs => rw [← mkPR_eta c]
    cases h : c (oPR k) <;> simp [h]
  right_inv p := by
    rcases p with p | p <;> simp

omit [Fintype n] [DecidableEq n] in
theorem phiPR_apply (en : Cfg (Fin k) ≃ n) (c : Cfg (PR k)) :
    phiPR en c = if c (oPR k) then Sum.inr (phiE en (fun e => c (ixPR k e)))
      else Sum.inl (phiE en (fun e => c (ixPR k e))) := rfl

/-! ### The lifted locator and edge action -/

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The coordinates of the lift of an operator on a basis vector. -/
theorem qlift_bas_apply {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (φ : Cfg V ≃ ι) (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (c : Cfg V) (q : R)
    (y : Cfg V) : qlift φ A (bas c q) y = A (EuclideanSpace.single (φ c) 1) (φ y) • q := by
  rw [qlift_eq, matOp_apply, Finset.sum_eq_single c]
  · simp [toMat]
  · intro c' _ hc'
    simp [hc']
  · simp

omit [InnerProductSpace ℂ R] [CompleteSpace R] in
theorem slice_ixPR_bas (c y : Cfg (PR k)) (q : R) :
    slice (ixPR k) (bas c q) y =
      if y (oPR k) = c (oPR k) then bas (fun e => c (ixPR k e)) q else 0 := by
  apply PiLp.ext
  intro d
  rw [slice_apply, overwrite_ixPR, bas_apply]
  by_cases h : y (oPR k) = c (oPR k)
  · rw [if_pos h, bas_apply]
    by_cases hd : d = fun e => c (ixPR k e)
    · rw [if_pos ((mkPR_eq_iff _ _ _).2 ⟨h, hd⟩), if_pos hd]
    · rw [if_neg (fun h' => hd ((mkPR_eq_iff _ _ _).1 h').2), if_neg hd]
  · rw [if_neg (fun h' => h ((mkPR_eq_iff _ _ _).1 h').1), if_neg h]
    simp

theorem leftPart_single_inl (e0 : n × n) :
    FixedLocatorConjugation.leftPart (EuclideanSpace.single (Sum.inl e0) (1 : ℂ) :
      SparseEdgeMoments.OrientedSpace n) = EuclideanSpace.single e0 1 := by
  ext e
  simp [FixedLocatorConjugation.leftPart]

theorem leftPart_single_inr (e0 : n × n) :
    FixedLocatorConjugation.leftPart (EuclideanSpace.single (Sum.inr e0) (1 : ℂ) :
      SparseEdgeMoments.OrientedSpace n) = 0 := by
  ext e
  simp [FixedLocatorConjugation.leftPart]

theorem rightPart_single_inl (e0 : n × n) :
    FixedLocatorConjugation.rightPart (EuclideanSpace.single (Sum.inl e0) (1 : ℂ) :
      SparseEdgeMoments.OrientedSpace n) = 0 := by
  ext e
  simp [FixedLocatorConjugation.rightPart]

theorem rightPart_single_inr (e0 : n × n) :
    FixedLocatorConjugation.rightPart (EuclideanSpace.single (Sum.inr e0) (1 : ℂ) :
      SparseEdgeMoments.OrientedSpace n) = EuclideanSpace.single e0 1 := by
  ext e
  simp [FixedLocatorConjugation.rightPart]

/-- **The lifted locator.** The lift of `block A B` applies `A` (orientation `false`) or `B`
(orientation `true`) to the index wires. -/
theorem qlift_block (en : Cfg (Fin k) ≃ n)
    (A B : EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n)) :
    qlift (R := R) (phiPR en) (FixedLocatorConjugation.block A B) =
      localOp (ixPR k) (ixPR_injective k)
        (fun c => if c (oPR k) then qlift (phiE en) B else qlift (phiE en) A) := by
  apply ext_bas_clm
  intro c q
  apply PiLp.ext
  intro y
  rw [qlift_bas_apply, localOp_apply, slice_ixPR_bas]
  beta_reduce
  rw [clearCfg_apply_out _ _ _ (ixPR_ne_o k)]
  cases hc : c (oPR k) <;> cases hy : y (oPR k) <;>
    simp [phiPR_apply, hc, hy, qlift_bas_apply, leftPart_single_inl, leftPart_single_inr,
      rightPart_single_inl, rightPart_single_inr]

/-- The matrix of a one-qubit operator: `qmat T b c = ⟨b| T |c⟩`. -/
def qmat (T : ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit) : Matrix Bool Bool ℂ :=
  fun b c => T (EuclideanSpace.single c 1) b

theorem regroup_single_phiPR (en : Cfg (Fin k) ≃ n) (c : Cfg (PR k)) (e : n × n) :
    OrientedEdgeCayley.regroup (EuclideanSpace.single (phiPR en c) (1 : ℂ)) e =
      if e = phiE en (fun e => c (ixPR k e)) then EuclideanSpace.single (c (oPR k)) 1
        else 0 := by
  apply PiLp.ext
  intro b
  by_cases he : e = phiE en (fun e => c (ixPR k e))
  · rw [if_pos he]
    cases hc : c (oPR k) <;> cases b <;> simp [phiPR_apply, hc, he]
  · rw [if_neg he]
    cases hc : c (oPR k) <;> cases b <;> simp [phiPR_apply, hc, he]

/-- **The lifted edgewise operation.** The lift of `OrientedEdgeCayley.lift G` is the
one-qubit operation `G e` on the orientation wire, for the edge `e` of the index wires. -/
theorem qlift_lift (en : Cfg (Fin k) ≃ n)
    (G : n × n → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit) :
    qlift (R := R) (phiPR en) (OrientedEdgeCayley.lift G) =
      condOp (oPR k) (fun c => qmat (G (phiE en (fun e => c (ixPR k e))))) := by
  apply ext_bas_clm
  intro c q
  apply PiLp.ext
  intro y
  rw [qlift_bas_apply, condOp_apply]
  have hix : (fun e => Function.update y (oPR k) false (ixPR k e)) = fun e => y (ixPR k e) := by
    funext e
    exact Function.update_of_ne (ixPR_ne_o k e) _ _
  have hupd : ∀ b, (Function.update y (oPR k) b = c) ↔
      (b = c (oPR k) ∧ (fun e => y (ixPR k e)) = fun e => c (ixPR k e)) := by
    intro b
    rw [update_oPR, mkPR_eq_iff]
  simp only [bas_apply, hupd, hix]
  have hy' : phiPR en y = if y (oPR k) then Sum.inr (phiE en (fun e => y (ixPR k e)))
      else Sum.inl (phiE en (fun e => y (ixPR k e))) := rfl
  rw [hy', Finset.sum_eq_single (c (oPR k))]
  · by_cases hd : (fun e => y (ixPR k e)) = fun e => c (ixPR k e)
    · have he : phiE en (fun e => y (ixPR k e)) = phiE en (fun e => c (ixPR k e)) := by rw [hd]
      cases hy : y (oPR k) <;>
        simp only [if_true, Bool.false_eq_true, if_false, OrientedEdgeCayley.lift_inl,
          OrientedEdgeCayley.lift_inr, regroup_single_phiPR, hd, and_self, qmat]
    · have he : phiE en (fun e => y (ixPR k e)) ≠ phiE en (fun e => c (ixPR k e)) :=
        fun h => hd ((phiE en).injective h)
      cases hy : y (oPR k) <;>
        simp [OrientedEdgeCayley.lift_inl, OrientedEdgeCayley.lift_inr,
          regroup_single_phiPR, he, hd]
  · intro b _ hb
    simp [hb]
  · simp

/-- The matrix of the exact edge action is the edge rotation of the native model. -/
theorem qmat_action (z : ℂ) : qmat (ExactEdgeCayley.action z) = edgeMat z := by
  funext b c
  simp only [qmat, edgeMat, ExactEdgeCayley.action_eq_rational]
  cases b <;> cases c <;>
    simp [ExactEdgeCayley.generator_false, ExactEdgeCayley.generator_true] <;>
    exact Or.inl (by ring)

/-! ### Flat operators as selected private operations -/

section Flat

variable {W S : Type*} [Fintype W] [DecidableEq W] [Fintype S] [DecidableEq S]

/-- An operator on the flat register `W ⊕ S` as an operator on `W` with payload `Reg S R`. -/
def unconj (O : Reg (W ⊕ S) R →L[ℂ] Reg (W ⊕ S) R) : Reg W (Reg S R) →L[ℂ] Reg W (Reg S R) :=
  unfl ∘L O ∘L fl

omit [CompleteSpace R] in
theorem conj_unconj (O : Reg (W ⊕ S) R →L[ℂ] Reg (W ⊕ S) R) :
    GateNative.conj (unconj O) = O := by
  unfold GateNative.conj unconj
  ext φ
  simp

omit [CompleteSpace R] in
theorem unconj_comp (O O' : Reg (W ⊕ S) R →L[ℂ] Reg (W ⊕ S) R) :
    unconj (O ∘L O') = unconj O ∘L unconj O' := by
  unfold unconj
  ext ψ
  simp

omit [CompleteSpace R] in
theorem unconj_one : unconj (1 : Reg (W ⊕ S) R →L[ℂ] Reg (W ⊕ S) R) = 1 := by
  unfold unconj
  ext ψ
  simp

omit [CompleteSpace R] in
theorem unconj_sub (O O' : Reg (W ⊕ S) R →L[ℂ] Reg (W ⊕ S) R) :
    unconj (O - O') = unconj O - unconj O' := by
  unfold unconj
  ext ψ
  simp

theorem unconj_adjoint (O : Reg (W ⊕ S) R →L[ℂ] Reg (W ⊕ S) R) :
    unconj (O†) = (unconj O)† := by
  unfold unconj
  rw [adjoint_comp, adjoint_comp, fl_adjoint]
  have h : (unfl (W := W) (S := S) (R := R))† = fl := by
    rw [← fl_adjoint, adjoint_adjoint]
  rw [h, comp_assoc]

theorem unconj_isUnitary {O : Reg (W ⊕ S) R →L[ℂ] Reg (W ⊕ S) R} (hO : IsUnitary O) :
    IsUnitary (unconj O) := by
  constructor
  · rw [star_eq_adjoint, ← unconj_adjoint, mul_def, ← unconj_comp, ← mul_def,
      ← star_eq_adjoint, hO.1, unconj_one]
  · rw [star_eq_adjoint, ← unconj_adjoint, mul_def, ← unconj_comp, ← mul_def,
      ← star_eq_adjoint, hO.2, unconj_one]

omit [CompleteSpace R] in
theorem norm_unconj_apply (O : Reg (W ⊕ S) R →L[ℂ] Reg (W ⊕ S) R) (ψ : Reg W (Reg S R)) :
    ‖unconj O ψ‖ = ‖O (fl ψ)‖ := by
  unfold unconj
  simp

omit [CompleteSpace R] in
theorem norm_unconj_le (O : Reg (W ⊕ S) R →L[ℂ] Reg (W ⊕ S) R) : ‖unconj O‖ ≤ ‖O‖ := by
  refine opNorm_le_bound (unconj O) (norm_nonneg O) (fun ψ => ?_)
  rw [norm_unconj_apply]
  calc ‖O (fl ψ)‖ ≤ ‖O‖ * ‖fl (W := W) (S := S) (R := R) ψ‖ := le_opNorm _ _
    _ = ‖O‖ * ‖ψ‖ := by simp

end Flat

section NoSel

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- An operator on the wires `W` as an operator on `Empty ⊕ W` (no selection wires). -/
def liftE (O : Reg W R →L[ℂ] Reg W R) : Reg (Empty ⊕ W) R →L[ℂ] Reg (Empty ⊕ W) R :=
  localOp Sum.inr Sum.inr_injective (fun _ => O)

theorem liftE_comp (O O' : Reg W R →L[ℂ] Reg W R) : liftE (O ∘L O') = liftE O ∘L liftE O' := by
  unfold liftE
  rw [localOp_comp]

theorem liftE_adjoint (O : Reg W R →L[ℂ] Reg W R) : liftE (O†) = (liftE O)† := by
  unfold liftE
  rw [localOp_adjoint]

theorem liftE_isUnitary {O : Reg W R →L[ℂ] Reg W R} (hO : IsUnitary O) : IsUnitary (liftE O) :=
  localOp_isUnitary _ _ (fun _ => hO)

/-- The selected private operation of a constant family is the lifted flat operation. -/
theorem selOp_unconj {S : Type*} [Fintype S] [DecidableEq S] {a : ℕ}
    (O : Reg (Fin a ⊕ S) R →L[ℂ] Reg (Fin a ⊕ S) R) :
    selOp (Sel := Empty) (fun _ => unconj O) = liftE O := by
  unfold selOp liftE
  congr 1
  funext y
  exact conj_unconj O

end NoSel

end

end SparseHamiltonian.GateBinary
