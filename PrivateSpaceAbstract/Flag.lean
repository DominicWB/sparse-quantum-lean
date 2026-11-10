import PrivateSpaceAbstract.Pad

/-!
# The padded private call from the supplied private unitary, and the zero system

Two completions of Lemma `hs:lem:abstract` for an arbitrary private space (`Pad`).

**The padded call.** The circuits of `abstract_simulation_private` call the padded unitary
`padUnitary V D₀ = V D₀ V† - (1 - V V†)`. It factors through one use of the supplied private
unitary:

* `flagCall V D₀ = V D₀ V† + (1 - V V†)` is `D₀` under the range flag of `V`: `D₀` on the range of
  `V` (`flagCall_comp_isometry`) and the identity on its orthogonal complement
  (`flagCall_apply_of_orth`); it is unitary for unitary `D₀` (`flagCall_unitary`) and
  `(flagCall V D₀)† = flagCall V D₀†` (`flagCall_adjoint`);
* `rangeRefl V = V V† - (1 - V V†)` is the known reflection about the range of `V`, a self-adjoint
  involution (`rangeRefl_adjoint`, `rangeRefl_mul_self`, `rangeRefl_unitary`) that does not depend
  on the data; it commutes with `flagCall V D₀` (`flagCall_comm_rangeRefl`);
* `padUnitary_eq_flagCall`: `padUnitary V D₀ = flagCall V D₀ ∘ rangeRefl V`, and
  `padUnitary_adjoint_eq_flagCall`: its adjoint is `flagCall V D₀† ∘ rangeRefl V`;
* `oracleOp_padUnitary`, `oracleOp_padUnitary_adjoint`: under any list of literal controls on the
  wires of a circuit, a call of the padded unitary (or its adjoint) is the call of `flagCall V D₀`
  (or of `flagCall V D₀†`) under the same controls after the controlled known reflection.

So every call of the padded unitary counted in `abstract_simulation_private` is one call of `D₀` or
`D₀†` under its control and the range flag, plus one use of the known reflection `rangeRefl V`,
which makes no call. This is an operator identity for the abstract query theorem: an arbitrary
isometry `V` (and `rangeRefl V`) need not have a cheap elementary implementation, and no gate count
for it is claimed.

**The zero system.** No isometry maps a nonzero private space into the register of a zero system,
so `abstract_simulation_finite` assumes a nonzero system. For a zero system the simulation is
trivial: every circuit, in particular the empty one (no calls, no gates), is exact, with every
supplied unitary (`run_subsingleton_exact`, `abstract_simulation_zero`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.PrivateSpaceAbstract

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim GateRemarks
open scoped InnerProduct

variable {a : ℕ} {P K : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ### The supplied private unitary under the range flag -/

/-- **The supplied private unitary under the range flag of `V`**: `V D₀ V† + (1 - V V†)`. -/
def flagCall (V : K →L[ℂ] Anc a P) (D₀ : K →L[ℂ] K) : Anc a P →L[ℂ] Anc a P :=
  V ∘L D₀ ∘L V† + (1 - V ∘L V†)

/-- **The known reflection about the range of `V`**: `V V† - (1 - V V†)`. -/
def rangeRefl (V : K →L[ℂ] Anc a P) : Anc a P →L[ℂ] Anc a P :=
  V ∘L V† - (1 - V ∘L V†)

theorem flagCall_apply (V : K →L[ℂ] Anc a P) (D₀ : K →L[ℂ] K) (x : Anc a P) :
    flagCall V D₀ x = V (D₀ ((V†) x)) + (x - V ((V†) x)) := rfl

theorem rangeRefl_apply (V : K →L[ℂ] Anc a P) (x : Anc a P) :
    rangeRefl V x = V ((V†) x) - (x - V ((V†) x)) := rfl

theorem adjoint_rangeRefl_apply {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) (x : Anc a P) :
    (V†) (rangeRefl V x) = (V†) x := by
  rw [rangeRefl_apply, map_sub, map_sub, isometry_adjoint_apply hV, sub_self, sub_zero]

theorem adjoint_flagCall_apply {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) (D₀ : K →L[ℂ] K)
    (x : Anc a P) : (V†) (flagCall V D₀ x) = D₀ ((V†) x) := by
  rw [flagCall_apply, map_add, map_sub, isometry_adjoint_apply hV, isometry_adjoint_apply hV,
    sub_self, add_zero]

/-- **On the range of `V`** the flagged call acts as `D₀`. -/
theorem flagCall_comp_isometry {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) (D₀ : K →L[ℂ] K) :
    flagCall V D₀ ∘L V = V ∘L D₀ := by
  refine ContinuousLinearMap.ext fun y => ?_
  rw [comp_apply, comp_apply, flagCall_apply, isometry_adjoint_apply hV, sub_self, add_zero]

/-- **On the orthogonal complement of the range of `V`** the flagged call is the identity. -/
theorem flagCall_apply_of_orth (V : K →L[ℂ] Anc a P) (D₀ : K →L[ℂ] K) {w : Anc a P}
    (hw : (V†) w = 0) : flagCall V D₀ w = w := by
  rw [flagCall_apply, hw, map_zero, map_zero, sub_zero, zero_add]

theorem flagCall_adjoint (V : K →L[ℂ] Anc a P) (D₀ : K →L[ℂ] K) :
    (flagCall V D₀)† = flagCall V (D₀†) := by
  have h1 : ((1 : Anc a P →L[ℂ] Anc a P)†) = 1 := by rw [← star_eq_adjoint, star_one]
  rw [flagCall, flagCall, map_add, map_sub, h1, adjoint_comp, adjoint_comp, adjoint_comp,
    adjoint_adjoint, comp_assoc]

theorem rangeRefl_adjoint (V : K →L[ℂ] Anc a P) : (rangeRefl V)† = rangeRefl V := by
  have h1 : ((1 : Anc a P →L[ℂ] Anc a P)†) = 1 := by rw [← star_eq_adjoint, star_one]
  rw [rangeRefl, map_sub, map_sub, h1, adjoint_comp, adjoint_adjoint]

/-- The reflection is an involution. -/
theorem rangeRefl_mul_self {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) :
    rangeRefl V ∘L rangeRefl V = 1 := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [comp_apply, rangeRefl_apply V (rangeRefl V x), adjoint_rangeRefl_apply hV, rangeRefl_apply,
    one_apply_eq_self]
  abel

/-- The reflection is unitary. -/
theorem rangeRefl_unitary {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) : IsUnitary (rangeRefl V) := by
  have h : star (rangeRefl V) * rangeRefl V = 1 := by
    rw [star_eq_adjoint, rangeRefl_adjoint, mul_def, rangeRefl_mul_self hV]
  exact ⟨h, by rw [star_eq_adjoint, rangeRefl_adjoint] at h ⊢; exact h⟩

/-- **The padded unitary factors through the flagged call**: `padUnitary V D₀ = flagCall V D₀ ∘
rangeRefl V`. -/
theorem padUnitary_eq_flagCall {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) (D₀ : K →L[ℂ] K) :
    padUnitary V D₀ = flagCall V D₀ ∘L rangeRefl V := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [comp_apply, flagCall_apply V D₀ (rangeRefl V x), adjoint_rangeRefl_apply hV,
    rangeRefl_apply, padUnitary_apply]
  abel

/-- The flagged call commutes with the known reflection. -/
theorem flagCall_comm_rangeRefl {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) (D₀ : K →L[ℂ] K) :
    flagCall V D₀ ∘L rangeRefl V = rangeRefl V ∘L flagCall V D₀ := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [comp_apply, comp_apply, flagCall_apply V D₀ (rangeRefl V x), adjoint_rangeRefl_apply hV,
    rangeRefl_apply V (flagCall V D₀ x), adjoint_flagCall_apply hV, rangeRefl_apply,
    flagCall_apply]
  abel

/-- The flagged call of a unitary is unitary. -/
theorem flagCall_unitary {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) {D₀ : K →L[ℂ] K}
    (hD₀ : IsUnitary D₀) : IsUnitary (flagCall V D₀) := by
  have h : flagCall V D₀ = padUnitary V D₀ ∘L rangeRefl V := by
    rw [padUnitary_eq_flagCall hV, comp_assoc, rangeRefl_mul_self hV]
    exact ContinuousLinearMap.ext fun _ => rfl
  rw [h]
  exact (padUnitary_unitary hV hD₀).mul (rangeRefl_unitary hV)

/-- **The adjoint of the padded unitary** factors through the flagged call of `D₀†`. -/
theorem padUnitary_adjoint_eq_flagCall {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1)
    (D₀ : K →L[ℂ] K) : (padUnitary V D₀)† = flagCall V (D₀†) ∘L rangeRefl V := by
  rw [padUnitary_adjoint, padUnitary_eq_flagCall hV]

/-! ### Controlled calls on the wires of a circuit -/

section Controlled

variable {W : Type*} [Fintype W] [DecidableEq W]

omit [CompleteSpace K] in
/-- A controlled call of a product is the product of the controlled calls. -/
theorem oracleOp_comp (anc : Fin a → W) (hanc : Function.Injective anc) (cs : List (W × Bool))
    (A B : Anc a P →L[ℂ] Anc a P) :
    oracleOp anc hanc cs (A ∘L B) = oracleOp anc hanc cs A ∘L oracleOp anc hanc cs B := by
  unfold oracleOp
  rw [localOp_comp]
  congr 1
  funext x
  split_ifs
  · rfl
  · exact ContinuousLinearMap.ext fun _ => rfl

/-- **A controlled call of the padded unitary** is the controlled flagged call of `D₀` after the
controlled known reflection, under the same literal controls. -/
theorem oracleOp_padUnitary (anc : Fin a → W) (hanc : Function.Injective anc)
    (cs : List (W × Bool)) {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) (D₀ : K →L[ℂ] K) :
    oracleOp anc hanc cs (padUnitary V D₀) =
      oracleOp anc hanc cs (flagCall V D₀) ∘L oracleOp anc hanc cs (rangeRefl V) := by
  rw [padUnitary_eq_flagCall hV, oracleOp_comp]

/-- **A controlled call of the adjoint of the padded unitary** is the controlled flagged call of
`D₀†` after the controlled known reflection. -/
theorem oracleOp_padUnitary_adjoint (anc : Fin a → W) (hanc : Function.Injective anc)
    (cs : List (W × Bool)) {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) (D₀ : K →L[ℂ] K) :
    oracleOp anc hanc cs ((padUnitary V D₀)†) =
      oracleOp anc hanc cs (flagCall V (D₀†)) ∘L oracleOp anc hanc cs (rangeRefl V) := by
  rw [padUnitary_adjoint_eq_flagCall hV, oracleOp_comp]

end Controlled

/-! ### The zero system -/

omit [CompleteSpace P] in
/-- On a zero system every two operators out of it agree. -/
theorem eq_of_subsingleton {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [Subsingleton P] (f g : P →L[ℂ] F) : f = g :=
  ContinuousLinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]

/-- **On a zero system every circuit is exact**: for every semantics, input embedding and target
operator, the full-output error is zero. -/
theorem run_subsingleton_exact [Subsingleton P] {W : Type*} [Fintype W] [DecidableEq W]
    (σ : Sem W a P) (C : List (Instr W)) (ι : P →L[ℂ] Reg W P) (E : P →L[ℂ] P) :
    ‖run σ C ∘L ι - ι ∘L E‖ = 0 := by
  rw [eq_of_subsingleton (run σ C ∘L ι) (ι ∘L E), sub_self]
  simp

/-- **Lemma `hs:lem:abstract` for a zero system**: the empty circuit makes no call of the private
unitary or of `U_J` and has no gate, and for every pair of supplied unitaries it has full-output
error zero against `exp(-it (α h))`, so at most every `ε ≥ 0`. -/
theorem abstract_simulation_zero [Subsingleton P] (a : ℕ) (α t Q ν ε : ℝ) (hε : 0 ≤ ε)
    (UJ D : Anc a P →L[ℂ] Anc a P) (h : P →L[ℂ] P) :
    nPriv ([] : List (Instr (SimWire a Q (α * |t|) ν ε))) = 0 ∧
    nUJ ([] : List (Instr (SimWire a Q (α * |t|) ν ε))) = 0 ∧
    nGates ([] : List (Instr (SimWire a Q (α * |t|) ν ε))) = 0 ∧
    ‖run (simSem UJ D) ([] : List (Instr (SimWire a Q (α * |t|) ν ε))) ∘L io -
        io ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) • ((α : ℂ) • h))‖ ≤ ε := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rw [run_subsingleton_exact]
  exact hε

end

end SparseHamiltonian.PrivateSpaceAbstract
