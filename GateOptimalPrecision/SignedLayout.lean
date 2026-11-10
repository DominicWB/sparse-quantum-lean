import GateOptimalPrecision.Reuse
import SignedFactorSimulation.Theorem
import GateEfficientNative.Native.Private

/-!
# The factor interface on the gate register

Section `gate:sec:signed` uses a factor `B = Π U_B E` with a known clean embedding `E`, a known
success projection `Π` and a known sign reflection `Z` on success (`gate:eq:factor`), and the
private operation `P = U_B† (K + iI)(K - iI)⁻¹ U_B` with `K = qZ` on success and `0` on failure
(`gate:eq:factor-private`): "Only the three known middle phases need an external control. On an
inactive branch the unconditional factor and inverse cancel."

On the gate register the factor acts on `a` ancilla qubits and the system:

* `wKnown UJ f z` (`SignedFactorSimulation.Known`): the boundary `E = U_J ι₀` for a supplied
  unitary `U_J`, the success projection `Π = [wire f = 1]` and the sign `Z = (-1)^{wire z}`;
* the attenuation of Section `gate:sec:signed` ("If `T_f < M`, attenuate `B` by `√(T_f/M)` … The
  attenuation is a known flag rotation, with no extra factor queries") uses one more ancilla qubit,
  wire `0` of `a + 1` ancillas: `attKnown UJ f z κ` has the boundary
  `E' = (U_J on the last a wires) ∘ R_κ(wire 0) ∘ ι₀`, success `Π' = [wire 0 = 0, wire f+1 = 1]` and
  sign `Z' = (-1)^{wire z+1}`, and the factor unitary `U_B` acts on the last `a` wires (`liftA U`);
  then `B' = √κ |0⟩ ⊗ B` (`attKnown_factor`), so `C' = κ C` and `D' = κ D` (`attKnown_Cop`,
  `attKnown_Dop`);
* the supporting operators: diagonal operators `dg` with the projection and sign entries
  `projD`, `signD` (`attProjD`, `attSignD` on `a + 1` wires), the inclusions `incl b` of `a` into
  `a + 1` ancilla wires, `liftA` (an operator on the last `a` wires) and the flag rotation
  `flagRot κ` (`rotMat κ`, `attUJ`).

The expansion of the private calls (the diagonal phase `attPhaseD`, its three gates and
`privExpand`, `ujExpand`, `run_expand`, `expand_counts`) is in `GateOptimalPrecision.SignedExpand`.
-/

set_option autoImplicit false

namespace GateOptimalPrecision

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim
open SignedFactorSimulation (Known)
open scoped InnerProduct InnerProductSpace BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Diagonal operators on an ancilla register -/

section Diagonal

variable {n : ℕ}

/-- The diagonal operator with entries `d` on the configurations of `n` ancilla qubits. -/
def dg (d : Cfg (Fin n) → ℂ) : Anc n P →L[ℂ] Anc n P := matOp (Matrix.diagonal d)

omit [CompleteSpace P] in
theorem dg_apply (d : Cfg (Fin n) → ℂ) (ψ : Anc n P) (b : Cfg (Fin n)) :
    dg d ψ b = d b • ψ b := by
  rw [dg, matOp_apply, Finset.sum_eq_single b]
  · simp
  · intro c _ hc; simp [Ne.symm hc]
  · intro h; exact absurd (Finset.mem_univ b) h

omit [CompleteSpace P] in
theorem dg_comp (d e : Cfg (Fin n) → ℂ) :
    dg (P := P) d ∘L dg e = dg (fun b => d b * e b) := by
  rw [dg, dg, dg, matOp_mul, Matrix.diagonal_mul_diagonal]

theorem dg_adjoint (d : Cfg (Fin n) → ℂ) :
    (dg (P := P) d)† = dg (fun b => star (d b)) := by
  rw [dg, matOp_adjoint, Matrix.diagonal_conjTranspose]
  rfl

omit [CompleteSpace P] in
theorem dg_one : dg (P := P) (fun _ : Cfg (Fin n) => (1 : ℂ)) = 1 := by
  rw [dg, show (Matrix.diagonal fun _ : Cfg (Fin n) => (1 : ℂ)) = 1 from Matrix.diagonal_one,
    matOp_one]

omit [CompleteSpace P] in
theorem dg_add (d e : Cfg (Fin n) → ℂ) :
    dg (P := P) (fun b => d b + e b) = dg d + dg e := by
  ext ψ b
  rw [add_apply, PiLp.add_apply, dg_apply, dg_apply, dg_apply, add_smul]

omit [CompleteSpace P] in
theorem dg_smul (c : ℂ) (d : Cfg (Fin n) → ℂ) :
    dg (P := P) (fun b => c * d b) = c • dg d := by
  ext ψ b
  rw [smul_apply, PiLp.smul_apply, dg_apply, dg_apply, mul_smul]

omit [CompleteSpace P] in
theorem dg_sub (d e : Cfg (Fin n) → ℂ) :
    dg (P := P) (fun b => d b - e b) = dg d - dg e := by
  ext ψ b
  rw [sub_apply, PiLp.sub_apply, dg_apply, dg_apply, dg_apply, sub_smul]

omit [CompleteSpace P] in
theorem dg_bas (d : Cfg (Fin n) → ℂ) (c : Cfg (Fin n)) (q : P) :
    dg d (bas c q) = d c • bas c q := by
  apply PiLp.ext
  intro b
  rw [dg_apply, bas_apply, PiLp.smul_apply, bas_apply]
  split_ifs with h
  · rw [h]
  · simp

end Diagonal

/-! ### The wire-defined factor interface -/

section Wire

variable {a : ℕ}

/-- The success indicator `[wire f = 1]`. -/
def projD (f : Fin a) : Cfg (Fin a) → ℂ := fun b => if b f then 1 else 0

/-- The sign `(-1)^{wire z}`. -/
def signD (z : Fin a) : Cfg (Fin a) → ℂ := fun b => if b z then -1 else 1

theorem star_projD (f : Fin a) (b : Cfg (Fin a)) : star (projD f b) = projD f b := by
  unfold projD; split_ifs <;> simp

theorem star_signD (z : Fin a) (b : Cfg (Fin a)) : star (signD z b) = signD z b := by
  unfold signD; split_ifs <;> simp

theorem projD_mul_self (f : Fin a) (b : Cfg (Fin a)) : projD f b * projD f b = projD f b := by
  unfold projD; split_ifs <;> simp

theorem signD_mul_self (z : Fin a) (b : Cfg (Fin a)) : signD z b * signD z b = 1 := by
  unfold signD; split_ifs <;> simp

/-- **The factor interface on `a` ancilla qubits**: `E = U_J ι₀`, `Π = [wire f = 1]` and
`Z = (-1)^{wire z}`. -/
def wKnown (UJ : Anc a P →L[ℂ] Anc a P) (hUJ : UJ† ∘L UJ = 1) (f z : Fin a) :
    Known P (Anc a P) where
  E := UJ ∘L iota0
  proj := dg (projD f)
  Z := dg (signD z)
  E_isometry := isometry_comp UJ iota0 hUJ iota0_isometry
  proj_adjoint := by
    rw [dg_adjoint]
    congr 1
    funext b
    exact star_projD f b
  proj_idem := by
    rw [mul_def, dg_comp]
    congr 1
    funext b
    exact projD_mul_self f b
  Z_adjoint := by
    rw [dg_adjoint]
    congr 1
    funext b
    exact star_signD z b
  Z_sq := by
    rw [mul_def, dg_comp]
    simp only [signD_mul_self]
    exact dg_one
  Z_comm := by
    rw [mul_def, mul_def, dg_comp, dg_comp]
    congr 1
    funext b
    ring

end Wire

/-! ### One more ancilla qubit -/

section Flag

variable {a : ℕ}

/-- The inclusion of `a` ancilla qubits as wires `1, …, a` with wire `0` in the state `b`. -/
def incl (b : Bool) : Anc a P →L[ℂ] Anc (a + 1) P :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Cfg (Fin (a + 1)) => P)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun x => if x 0 = b then coord (Q := P) (Fin.tail x) else 0)

omit [CompleteSpace P] in
theorem incl_apply (b : Bool) (φ : Anc a P) (x : Cfg (Fin (a + 1))) :
    incl b φ x = if x 0 = b then φ (Fin.tail x) else 0 := by
  simp only [incl, comp_apply]
  split_ifs with h <;> simp [h]

omit [CompleteSpace P] in
theorem sum_cfg_succ {E : Type*} [AddCommMonoid E] (g : Cfg (Fin (a + 1)) → E) :
    ∑ x, g x = ∑ c : Bool, ∑ y : Cfg (Fin a), g (Fin.cons c y) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (a + 1) => Bool)).symm _ _
    (fun x => by simp [Fin.consEquiv])).trans rfl

omit [CompleteSpace P] in
theorem inner_incl (b : Bool) (φ ψ : Anc a P) : ⟪incl b φ, incl b ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, sum_cfg_succ]
  rw [Fintype.sum_bool]
  cases b
  · simp [incl_apply]
  · simp [incl_apply]

omit [CompleteSpace P] in
theorem norm_incl (b : Bool) (φ : Anc a P) : ‖incl b φ‖ = ‖φ‖ := by
  have h := inner_incl b φ φ
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖incl b φ‖ ^ 2 = ‖φ‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h'

theorem incl_isometry (b : Bool) : (incl (P := P) (a := a) b)† ∘L incl b = 1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp (norm_incl b)

omit [CompleteSpace P] in
theorem tail_cons_zero {x : Cfg (Fin (a + 1))} :
    (x = fun _ => false) ↔ (x 0 = false ∧ Fin.tail x = fun _ => false) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, ht⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h0
    · exact congrFun ht j

omit [CompleteSpace P] in
/-- The clean embedding of `a + 1` ancillas is the clean embedding of `a` ancillas with wire `0`
in the state `0`. -/
theorem iota0_succ : (iota0 (a := a + 1) (P := P)) = incl false ∘L iota0 (a := a) := by
  ext p x
  rw [comp_apply, incl_apply, iota0_apply]
  by_cases h0 : x 0 = false
  · rw [if_pos h0, iota0_apply]
    by_cases ht : Fin.tail x = zw a
    · rw [if_pos ht, if_pos (tail_cons_zero.mpr ⟨h0, ht⟩)]
    · rw [if_neg ht, if_neg (fun h => ht (tail_cons_zero.mp h).2)]
  · rw [if_neg h0, if_neg (fun h => h0 (tail_cons_zero.mp h).1)]

/-- An operator on the last `a` of `a + 1` ancilla qubits. -/
def liftA (A : Anc a P →L[ℂ] Anc a P) : Anc (a + 1) P →L[ℂ] Anc (a + 1) P :=
  localOp Fin.succ (Fin.succ_injective a) (fun _ => A)

omit [CompleteSpace P] in
theorem overwrite_succ_zero (x : Cfg (Fin (a + 1))) (c : Cfg (Fin a)) :
    overwrite Fin.succ x c 0 = x 0 :=
  GateODE.overwrite_apply_out Fin.succ x c 0 (fun i => Fin.succ_ne_zero i)

omit [CompleteSpace P] in
theorem tail_overwrite_succ (x : Cfg (Fin (a + 1))) (c : Cfg (Fin a)) :
    Fin.tail (overwrite Fin.succ x c) = c :=
  funext (fun i => GateODE.overwrite_apply_ι (Fin.succ_injective a) x c i)

theorem liftA_incl (A : Anc a P →L[ℂ] Anc a P) (b : Bool) :
    liftA A ∘L incl b = incl b ∘L A := by
  ext φ x
  rw [comp_apply, comp_apply, liftA, localOp_apply, incl_apply]
  have hs : slice Fin.succ (incl b φ) x = if x 0 = b then φ else 0 := by
    apply PiLp.ext
    intro c
    rw [slice_apply, incl_apply, overwrite_succ_zero, tail_overwrite_succ]
    split_ifs <;> rfl
  rw [hs]
  split_ifs with h
  · rfl
  · rw [map_zero]; rfl

theorem liftA_comp (A B : Anc a P →L[ℂ] Anc a P) : liftA A ∘L liftA B = liftA (A ∘L B) := by
  rw [liftA, liftA, liftA, localOp_comp]

theorem liftA_adjoint (A : Anc a P →L[ℂ] Anc a P) : (liftA A)† = liftA (A†) := by
  rw [liftA, liftA, localOp_adjoint]

theorem liftA_one : liftA (1 : Anc a P →L[ℂ] Anc a P) = 1 := by
  rw [liftA, localOp_one]

theorem liftA_isUnitary {A : Anc a P →L[ℂ] Anc a P} (hA : IsUnitary A) : IsUnitary (liftA A) :=
  localOp_isUnitary _ _ (fun _ => hA)

/-- The attenuation rotation `|0⟩ ↦ √κ|0⟩ + √(1-κ)|1⟩`. -/
def rotMat (κ : ℝ) : Matrix Bool Bool ℂ := fun i j =>
  match i, j with
  | false, false => (Real.sqrt κ : ℂ)
  | true, false => (Real.sqrt (1 - κ) : ℂ)
  | false, true => -(Real.sqrt (1 - κ) : ℂ)
  | true, true => (Real.sqrt κ : ℂ)

theorem rotMat_unitary {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ ≤ 1) : UnitaryMat (rotMat κ) := by
  have hs : (Real.sqrt κ : ℂ) * Real.sqrt κ + Real.sqrt (1 - κ) * Real.sqrt (1 - κ) = 1 := by
    have e1 := Real.mul_self_sqrt h0
    have e2 := Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ 1 - κ)
    have : (Real.sqrt κ * Real.sqrt κ + Real.sqrt (1 - κ) * Real.sqrt (1 - κ) : ℝ) = 1 := by
      linarith
    exact_mod_cast this
  constructor
  · funext i j
    simp only [Matrix.mul_apply, Fintype.sum_bool, Matrix.conjTranspose_apply, Matrix.one_apply]
    cases i <;> cases j <;> simp [rotMat, Complex.conj_ofReal] <;>
      first | linear_combination hs | linear_combination (-1 : ℂ) * hs | ring
  · funext i j
    simp only [Matrix.mul_apply, Fintype.sum_bool, Matrix.conjTranspose_apply, Matrix.one_apply]
    cases i <;> cases j <;> simp [rotMat, Complex.conj_ofReal] <;>
      first | linear_combination hs | linear_combination (-1 : ℂ) * hs | ring

/-- The attenuation rotation on wire `0`. -/
def flagRot (κ : ℝ) : Anc (a + 1) P →L[ℂ] Anc (a + 1) P := gateOp [] 0 (rotMat κ)

theorem flagRot_incl (κ : ℝ) :
    flagRot (P := P) (a := a) κ ∘L incl false =
      (Real.sqrt κ : ℂ) • incl false + (Real.sqrt (1 - κ) : ℂ) • incl true := by
  ext φ x
  rw [comp_apply, flagRot, gateOp_apply [] 0 _ (by simp), ctrlOK_nil, if_pos rfl,
    Fintype.sum_bool]
  simp only [add_apply, smul_apply, PiLp.add_apply, PiLp.smul_apply, incl_apply]
  have ht : ∀ c : Bool, Fin.tail (Function.update x 0 c) = Fin.tail x := by
    intro c; funext i; simp [Fin.tail]
  simp only [Function.update_self, ht]
  cases h : x 0 <;> simp [rotMat]

theorem flagRot_isUnitary {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ ≤ 1) :
    IsUnitary (flagRot (P := P) (a := a) κ) :=
  gateOp_isUnitary _ _ _ (rotMat_unitary h0 h1)

/-- The attenuated boundary unitary: the flag rotation, then `U_J` on the last `a` wires. -/
def attUJ (UJ : Anc a P →L[ℂ] Anc a P) (κ : ℝ) : Anc (a + 1) P →L[ℂ] Anc (a + 1) P :=
  liftA UJ ∘L flagRot κ

theorem attUJ_isUnitary {UJ : Anc a P →L[ℂ] Anc a P} (hUJ : IsUnitary UJ) {κ : ℝ}
    (h0 : 0 ≤ κ) (h1 : κ ≤ 1) : IsUnitary (attUJ UJ κ) := by
  unfold attUJ
  rw [← mul_def]
  exact (liftA_isUnitary hUJ).mul (flagRot_isUnitary h0 h1)

/-- The attenuated success indicator `[wire 0 = 0, wire f+1 = 1]`. -/
def attProjD (f : Fin a) : Cfg (Fin (a + 1)) → ℂ := fun x =>
  if x 0 = false ∧ x f.succ = true then 1 else 0

/-- The attenuated sign `(-1)^{wire z+1}`. -/
def attSignD (z : Fin a) : Cfg (Fin (a + 1)) → ℂ := fun x => if x z.succ then -1 else 1

omit [CompleteSpace P] in
theorem attProj_incl_false (f : Fin a) :
    dg (P := P) (attProjD f) ∘L incl false = incl false ∘L dg (projD f) := by
  ext φ x
  rw [comp_apply, comp_apply, dg_apply, incl_apply, incl_apply, dg_apply]
  unfold attProjD projD
  by_cases h0 : x 0 = false
  · simp [h0, Fin.tail]
  · simp [h0]

omit [CompleteSpace P] in
theorem attProj_incl_true (f : Fin a) : dg (P := P) (attProjD f) ∘L incl true = 0 := by
  ext φ x
  rw [comp_apply, dg_apply, incl_apply]
  unfold attProjD
  by_cases h0 : x 0 = true
  · simp [h0]
  · simp [h0]

omit [CompleteSpace P] in
theorem attSign_incl (z : Fin a) (b : Bool) :
    dg (P := P) (attSignD z) ∘L incl b = incl b ∘L dg (signD z) := by
  ext φ x
  rw [comp_apply, comp_apply, dg_apply, incl_apply, incl_apply, dg_apply]
  unfold attSignD signD
  split_ifs <;> simp_all [Fin.tail]

/-- **The attenuated factor interface** on `a + 1` ancilla qubits (see the module docstring). -/
def attKnown (UJ : Anc a P →L[ℂ] Anc a P) (hUJ : IsUnitary UJ) (f z : Fin a) {κ : ℝ}
    (h0 : 0 ≤ κ) (h1 : κ ≤ 1) : Known P (Anc (a + 1) P) where
  E := attUJ UJ κ ∘L iota0
  proj := dg (attProjD f)
  Z := dg (attSignD z)
  E_isometry := isometry_comp (attUJ UJ κ) (iota0 (a := a + 1) (P := P))
    (unitary_adj_comp (attUJ_isUnitary hUJ h0 h1)) iota0_isometry
  proj_adjoint := by
    rw [dg_adjoint]
    congr 1
    funext b
    unfold attProjD; split_ifs <;> simp
  proj_idem := by
    rw [mul_def, dg_comp]
    congr 1
    funext b
    unfold attProjD; split_ifs <;> simp
  Z_adjoint := by
    rw [dg_adjoint]
    congr 1
    funext b
    unfold attSignD; split_ifs <;> simp
  Z_sq := by
    rw [mul_def, dg_comp]
    have : (fun b : Cfg (Fin (a + 1)) => attSignD z b * attSignD z b) = fun _ => (1 : ℂ) := by
      funext b; unfold attSignD; split_ifs <;> simp
    rw [this]
    exact dg_one
  Z_comm := by
    rw [mul_def, mul_def, dg_comp, dg_comp]
    congr 1
    funext b
    ring

theorem flagRot_incl_apply (κ : ℝ) (φ : Anc a P) :
    flagRot κ (incl false φ) =
      (Real.sqrt κ : ℂ) • incl false φ + (Real.sqrt (1 - κ) : ℂ) • incl true φ := by
  rw [← comp_apply, flagRot_incl]
  rfl

theorem liftA_incl_apply (A : Anc a P →L[ℂ] Anc a P) (b : Bool) (φ : Anc a P) :
    liftA A (incl b φ) = incl b (A φ) := by
  rw [← comp_apply, liftA_incl]
  rfl

omit [CompleteSpace P] in
theorem attProj_incl_false_apply (f : Fin a) (φ : Anc a P) :
    dg (attProjD f) (incl false φ) = incl false (dg (projD f) φ) := by
  rw [← comp_apply, attProj_incl_false]
  rfl

omit [CompleteSpace P] in
theorem attProj_incl_true_apply (f : Fin a) (φ : Anc a P) :
    dg (attProjD f) (incl true φ) = 0 := by
  rw [← comp_apply, attProj_incl_true]
  rfl

omit [CompleteSpace P] in
theorem iota0_succ_apply (p : P) :
    iota0 (a := a + 1) p = incl false (iota0 (a := a) p) := by
  rw [iota0_succ]
  rfl

theorem incl_sign_incl (z : Fin a) :
    (incl (P := P) (a := a) false)† ∘L dg (attSignD z) ∘L incl false = dg (signD z) := by
  rw [attSign_incl, ← comp_assoc, incl_isometry, one_comp']

/-- **The attenuated factor**: `B' = √κ |0⟩ ⊗ B` for the factor unitary `U_B` on the last `a`
wires. -/
theorem attKnown_factor (UJ : Anc a P →L[ℂ] Anc a P) (hUJ : IsUnitary UJ) (f z : Fin a)
    {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ ≤ 1) (U : Anc a P →L[ℂ] Anc a P) :
    (attKnown UJ hUJ f z h0 h1).factor (liftA U) =
      (Real.sqrt κ : ℂ) • (incl false ∘L (wKnown UJ (unitary_adj_comp hUJ) f z).factor U) := by
  change dg (attProjD f) ∘L liftA U ∘L (liftA UJ ∘L flagRot κ) ∘L iota0 =
    (Real.sqrt κ : ℂ) • (incl false ∘L dg (projD f) ∘L U ∘L UJ ∘L iota0)
  ext p
  simp only [comp_apply, smul_apply, iota0_succ_apply, flagRot_incl_apply, map_add, map_smul,
    liftA_incl_apply, attProj_incl_false_apply, attProj_incl_true_apply, smul_zero, add_zero]

theorem sqrt_conj_mul {κ : ℝ} (h0 : 0 ≤ κ) :
    (starRingEnd ℂ) (Real.sqrt κ : ℂ) * (Real.sqrt κ : ℂ) = (κ : ℂ) := by
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt h0]

theorem attKnown_Cop (UJ : Anc a P →L[ℂ] Anc a P) (hUJ : IsUnitary UJ) (f z : Fin a)
    {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ ≤ 1) (U : Anc a P →L[ℂ] Anc a P) :
    (attKnown UJ hUJ f z h0 h1).Cop (liftA U) =
      (κ : ℂ) • (wKnown UJ (unitary_adj_comp hUJ) f z).Cop U := by
  rw [Known.Cop, attKnown_factor, Known.Cop]
  generalize (wKnown UJ (unitary_adj_comp hUJ) f z).factor U = B
  have hZ : (attKnown UJ hUJ f z h0 h1).Z = dg (attSignD z) := rfl
  have hZw : (wKnown UJ (unitary_adj_comp hUJ) f z).Z = dg (signD z) := rfl
  rw [hZ, hZw]
  calc ((Real.sqrt κ : ℂ) • (incl false ∘L B))† ∘L dg (attSignD z) ∘L
        ((Real.sqrt κ : ℂ) • (incl false ∘L B)) =
      ((starRingEnd ℂ) (Real.sqrt κ : ℂ) * (Real.sqrt κ : ℂ)) •
        (B† ∘L ((incl false)† ∘L dg (attSignD z) ∘L incl false) ∘L B) := by
        simp only [map_smulₛₗ, adjoint_comp, smul_comp, comp_smul, smul_smul, comp_assoc]
        rw [mul_comm]
    _ = (κ : ℂ) • (B† ∘L dg (signD z) ∘L B) := by rw [incl_sign_incl, sqrt_conj_mul h0]

theorem attKnown_Dop (UJ : Anc a P →L[ℂ] Anc a P) (hUJ : IsUnitary UJ) (f z : Fin a)
    {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ ≤ 1) (U : Anc a P →L[ℂ] Anc a P) :
    (attKnown UJ hUJ f z h0 h1).Dop (liftA U) =
      (κ : ℂ) • (wKnown UJ (unitary_adj_comp hUJ) f z).Dop U := by
  rw [Known.Dop, attKnown_factor, Known.Dop]
  generalize (wKnown UJ (unitary_adj_comp hUJ) f z).factor U = B
  calc ((Real.sqrt κ : ℂ) • (incl false ∘L B))† ∘L ((Real.sqrt κ : ℂ) • (incl false ∘L B)) =
      ((starRingEnd ℂ) (Real.sqrt κ : ℂ) * (Real.sqrt κ : ℂ)) •
        (B† ∘L ((incl false)† ∘L incl false) ∘L B) := by
        simp only [map_smulₛₗ, adjoint_comp, smul_comp, comp_smul, smul_smul, comp_assoc]
        rw [mul_comm]
    _ = (κ : ℂ) • (B† ∘L B) := by
        rw [incl_isometry, sqrt_conj_mul h0]
        rfl

end Flag

end

end GateOptimalPrecision
