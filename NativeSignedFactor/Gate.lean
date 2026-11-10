import NativeSignedFactor.Local
import SparseHamiltonian.OrientedNativeValue
import SparseHamiltonian.OrientedEdgeCayley
import SparseHamiltonian.FixedLocatorConjugation
import SignedFactorSimulation.Theorem

set_option autoImplicit false

/-!
# The native factor unitary

The factor unitary `U_B` acts on the released logical native workspace
(`SparseHamiltonian.OrientedNativeLayout.Space`): an orientation bit, an edge address, a value
word and a three-valued flag. It applies the row locator on the row orientation and the column
locator on the column orientation (`SparseHamiltonian.OrientedNativeLayout.locatorProgram`,
two calls), computes the entry word, applies the local factor gate controlled by the edge and
the word (`gate`), and uncomputes the word (`valueProgram`, two calls).

The known input is the public uniform slot preparation on both orientations followed by the
clean value and flag registers (`input`); the success projection is flag `0` (`proj`) and the
success reflection is the sign of the orientation bit (`sign`). On a clean input the flag-`0`
output is the edge factor `facOp` (`proj_value_clean`), so the factor is
`B = clean ∘ facOp ∘ J₀` (`factor_eq`), with the sparse boundary
`J₀ = SparseHamiltonian.SparseEdgeMoments.boundary`.
-/

namespace NativeSignedFactor

noncomputable section

open ContinuousLinearMap SparseHamiltonian OracleCircuit NativeSparseBlockEncoding
open OrientedNativeLayout SparseEdgeMoments
open scoped InnerProduct ComplexConjugate

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

/-! ### Layout -/

/-- The address register: an edge and a value word. -/
abbrev Adr (n Z : Type*) := (n × n) × Z

/-- Move the orientation bit next to the flag. -/
def addrEquiv (n Z : Type*) : Bool × (Adr n Z × Fin 3) ≃ Adr n Z × (Bool × Fin 3) where
  toFun p := (p.2.1, (p.1, p.2.2))
  invFun q := (q.2.1, (q.1, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The workspace as a direct sum over addresses of the orientation-and-flag space. -/
def addrLayout : Space n Z ≃ₗᵢ[ℂ]
    PiLp 2 (fun _ : Adr n Z => EuclideanSpace ℂ (Bool × Fin 3)) :=
  (RegisterEquivalences.productFlatten Bool (NativeSparseMaskedAccess.Basis n Z)).trans
    ((LookupOracle.permutationUnitary (addrEquiv n Z)).trans
      (RegisterEquivalences.productFlatten (Adr n Z) (Bool × Fin 3)).symm)

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
@[simp] theorem addrLayout_apply (v : Space n Z) (a : Adr n Z) (b : Bool) (f : Fin 3) :
    addrLayout v a (b, f) = v b (a, f) := rfl

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
@[simp] theorem addrLayout_symm_apply
    (w : PiLp 2 (fun _ : Adr n Z => EuclideanSpace ℂ (Bool × Fin 3)))
    (b : Bool) (a : Adr n Z) (f : Fin 3) :
    addrLayout.symm w b (a, f) = w a (b, f) := rfl

/-! ### The gate -/

/-- The clipped normalised entry `clip(decode(e,z)/κ)` attached to an address. -/
def entry (D : Data X n Z s) (κ : ℝ) (a : Adr n Z) : ℂ := clip (D.decode a.1 a.2 / (κ : ℂ))

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem norm_entry_le (D : Data X n Z s) (κ : ℝ) (a : Adr n Z) : ‖entry D κ a‖ ≤ 1 :=
  norm_clip_le _

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- On an oracle value the entry is the normalised matrix entry, if it lies in the disk. -/
theorem entry_table (D : Data X n Z s) {κ : ℝ} (x : X) (e : n × n)
    (h : ‖D.matrix x e.1 e.2‖ ≤ κ) (hκ : 0 < κ) :
    entry D κ (e, D.table x e) = D.matrix x e.1 e.2 / (κ : ℂ) := by
  rw [entry, D.decoded]
  apply clip_of_norm_le
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
  exact (div_le_one hκ).mpr h

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- On an oracle value the entry modulus is at most `|H_e|/κ`. -/
theorem norm_entry_table_le (D : Data X n Z s) {κ : ℝ} (x : X) (e : n × n) (hκ : 0 < κ) :
    ‖entry D κ (e, D.table x e)‖ ≤ ‖D.matrix x e.1 e.2‖ / κ := by
  rw [entry, D.decoded]
  refine (norm_clip_le_norm _).trans (le_of_eq ?_)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]

/-- The value-controlled local factor gate: `localGate (entry D κ a)` at every address `a`. -/
def gate (D : Data X n Z s) (κ : ℝ) : Space n Z →L[ℂ] Space n Z :=
  (addrLayout (n := n) (Z := Z)).symm.conjStarAlgEquiv
    (WeightedClock.diagonal (fun a : Adr n Z => localOp (entry D κ a)))

omit [AddCommGroup Z] [DecidableEq Z] in
/-- Every value word, including words never returned by the oracle, gives a unitary. -/
theorem gate_unitary (D : Data X n Z s) (κ : ℝ) : IsUnitary (gate D κ) :=
  (NativeMaskedOracle.diagonal_unitary _
    (fun a => localOp_unitary (norm_entry_le D κ a))).transport addrLayout.symm

omit [AddCommGroup Z] [DecidableEq Z] in
/-- Coordinates of the gate on an arbitrary, possibly dirty, workspace vector. -/
theorem gate_apply (D : Data X n Z s) (κ : ℝ) (v : Space n Z) (b : Bool) (e : n × n) (z : Z)
    (f : Fin 3) :
    gate D κ v b ((e, z), f) = ∑ b', ∑ f', orient (entry D κ (e, z)) b b' *
      flagRot (entry D κ (e, z)) f f' * v b' ((e, z), f') := by
  change localOp (entry D κ (e, z)) (addrLayout v (e, z)) (b, f) = _
  rw [localOp_apply]
  rfl

/-! ### Programs -/

/-- Compute the entry word, apply the gate, uncompute: two value calls. -/
def valueProgram (D : Data X n Z s) (κ : ℝ) : MultiOracleCircuit.Program (logicalOracle D) :=
  .seq (.queryAdjoint .value) (.seq (.fixed (gate D κ) (gate_unitary D κ)) (.query .value))

/-- The logical factor unitary `U_B`: the two locators, then the value-controlled gate. -/
def factorProgram (D : Data X n Z s) (κ : ℝ) : MultiOracleCircuit.Program (logicalOracle D) :=
  .seq (valueProgram D κ) (locatorProgram D)

omit [DecidableEq Z] in
@[simp] theorem factorProgram_count (D : Data X n Z s) (κ : ℝ) :
    (factorProgram D κ).count = 4 := rfl

omit [DecidableEq Z] in
/-- One row-locator, one column-locator and two value calls. -/
theorem factorProgram_cost (D : Data X n Z s) (κ : ℝ) (w : Query → ℕ) :
    (factorProgram D κ).cost w = w .rowLocation + w .columnLocation + 2 * w .value := by
  change w .value + (0 + w .value) + (w .columnLocation + w .rowLocation) = _
  omega

omit [DecidableEq Z] in
theorem factorProgram_unitary (D : Data X n Z s) (κ : ℝ) (x : X) :
    IsUnitary ((factorProgram D κ).eval x) :=
  (factorProgram D κ).eval_unitary (logicalOracle_unitary D) x

/-! ### The edge factor -/

/-- The edge factor: `√‖c_e‖ V(c_e)†` on every edge, `c_e` the entry at the oracle value. -/
def facOp (D : Data X n Z s) (κ : ℝ) (x : X) : OrientedSpace n →L[ℂ] OrientedSpace n :=
  OrientedEdgeCayley.lift (fun e => facQ (entry D κ (e, D.table x e)))

/-- The gate output on a clean computed input; the value register is restored afterwards. -/
def outVec (D : Data X n Z s) (κ : ℝ) (x : X) (v : OrientedSpace n) : Space n Z :=
  WithLp.toLp 2 (fun b : Bool => WithLp.toLp 2 (fun a : NativeSparseMaskedAccess.Basis n Z =>
    if a.1.2 = 0 then flagRot (entry D κ (a.1.1, D.table x a.1.1)) a.2 0 *
      ∑ b', orient (entry D κ (a.1.1, D.table x a.1.1)) b b' *
        OrientedEdgeCayley.regroup v a.1.1 b'
    else 0))

theorem gate_value_clean (D : Data X n Z s) (κ : ℝ) (x : X) (v : OrientedSpace n) :
    gate D κ (logicalOracle D .value x (clean v)) =
      logicalOracle D .value x (outVec D κ x v) := by
  ext b a
  rcases a with ⟨⟨e, z⟩, f⟩
  rw [gate_apply, logical_value_apply]
  simp only [logical_value_apply, clean_apply]
  change _ = if z - D.table x e = 0 then _ else _
  by_cases hz : z - D.table x e = 0
  · have hz' : z = D.table x e := sub_eq_zero.mp hz
    rw [if_pos hz]
    subst hz'
    simp only [hz, true_and, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b' _
    cases b' <;> simp [OrientedEdgeCayley.regroup_false, OrientedEdgeCayley.regroup_true] <;> ring
  · rw [if_neg hz]
    simp [hz]

theorem value_clean (D : Data X n Z s) (κ : ℝ) (x : X) (v : OrientedSpace n) :
    (valueProgram D κ).eval x (clean v) = outVec D κ x v := by
  change star (logicalOracle D .value x) (gate D κ (logicalOracle D .value x (clean v))) = _
  rw [gate_value_clean]
  have h := (logicalOracle_unitary D .value x).1
  have h' := congrArg (fun T : Space n Z →L[ℂ] Space n Z => T (outVec D κ x v)) h
  simpa only [mul_apply_eq_comp, comp_apply, one_def, id_apply] using h'

/-! ### The known structure -/

/-- Flag-`0` projection on one native register. -/
def flagZero : EuclideanSpace ℂ (NativeSparseMaskedAccess.Basis n Z) →L[ℂ]
    EuclideanSpace ℂ (NativeSparseMaskedAccess.Basis n Z) :=
  RelativeAmplitudeError.complexDiagonal (fun a => if a.2 = 0 then 1 else 0)

/-- The success projection `Π`: flag `0`. -/
def proj : Space n Z →L[ℂ] Space n Z := WeightedClock.diagonal (fun _ : Bool => flagZero)

/-- The success reflection `Z`: the sign of the orientation bit, `+1` for `false` and `-1` for
`true`. On the success outputs of the gate this bit carries the `±` label of the local factor. -/
def sign : Space n Z →L[ℂ] Space n Z :=
  WeightedClock.diagonal (fun b : Bool =>
    (if b then (-1 : ℂ) else 1) • (1 : EuclideanSpace ℂ (NativeSparseMaskedAccess.Basis n Z) →L[ℂ]
      EuclideanSpace ℂ (NativeSparseMaskedAccess.Basis n Z)))

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
@[simp] theorem proj_apply (v : Space n Z) (b : Bool) (a : NativeSparseMaskedAccess.Basis n Z) :
    proj v b a = (if a.2 = 0 then 1 else 0) * v b a := rfl

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
@[simp] theorem sign_apply (v : Space n Z) (b : Bool) (a : NativeSparseMaskedAccess.Basis n Z) :
    sign v b a = (if b then (-1 : ℂ) else 1) * v b a := rfl

/-- The known input: the public slot preparation on both orientations, clean registers. -/
def input (D : Data X n Z s) : EuclideanSpace ℂ n →L[ℂ] Space n Z :=
  (clean (n := n) (Z := Z)).toContinuousLinearMap ∘L
    FixedLocatorConjugation.fixedBoundary D.slot

theorem input_isometry (D : Data X n Z s) : (input D (Z := Z))† ∘L input D = 1 := by
  rw [input, adjoint_comp, comp_assoc, ← comp_assoc _ _ (FixedLocatorConjugation.fixedBoundary _),
    LinearIsometry.adjoint_comp_self, one_def, id_comp]
  exact FixedLocatorConjugation.fixedBoundary_isometry D.slot D.slots_pos

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem proj_adjoint : (proj (n := n) (Z := Z))† = proj := by
  rw [proj, WeightedClock.diagonal_adjoint]
  congr 1
  funext b
  rw [flagZero, RelativeAmplitudeError.complexDiagonal_adjoint]
  congr 1
  funext a
  split_ifs <;> simp

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem proj_idem : proj (n := n) (Z := Z) * proj = proj := by
  ext v b a
  simp only [mul_apply_eq_comp, proj_apply]
  split_ifs <;> simp

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem sign_adjoint : (sign (n := n) (Z := Z))† = sign := by
  rw [sign, WeightedClock.diagonal_adjoint]
  congr 1
  funext b
  rw [← ContinuousLinearMap.star_eq_adjoint, star_smul, star_one]
  cases b
  · simp
  · simp only [if_true]
    rw [star_neg, star_one]

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem sign_sq : sign (n := n) (Z := Z) * sign = 1 := by
  ext v b a
  simp only [mul_apply_eq_comp, sign_apply]
  cases b <;> simp

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem sign_proj : sign (n := n) (Z := Z) * proj = proj * sign := by
  ext v b a
  simp only [mul_apply_eq_comp, sign_apply, proj_apply]
  ring

/-- The known structure of the logical native factor. -/
def known (D : Data X n Z s) : SignedFactorSimulation.Known (EuclideanSpace ℂ n) (Space n Z) where
  E := input D
  proj := proj
  Z := sign
  E_isometry := input_isometry D
  proj_adjoint := proj_adjoint
  proj_idem := proj_idem
  Z_adjoint := sign_adjoint
  Z_sq := sign_sq
  Z_comm := sign_proj

/-! ### The factor -/

/-- On a clean input, the flag-`0` output of the value program is the edge factor. -/
theorem proj_value_clean (D : Data X n Z s) (κ : ℝ) (x : X) :
    proj ∘L (valueProgram D κ).eval x ∘L (clean (n := n) (Z := Z)).toContinuousLinearMap =
      clean.toContinuousLinearMap ∘L facOp D κ x := by
  ext v b a
  rcases a with ⟨⟨e, z⟩, f⟩
  simp only [comp_apply, LinearIsometry.coe_toContinuousLinearMap, value_clean, proj_apply,
    clean_apply]
  change (if f = 0 then 1 else 0) * (if z = 0 then _ else 0) = _
  by_cases hz : z = 0
  · by_cases hf : f = 0
    · subst hz hf
      have h1 : flagRot (entry D κ (e, D.table x e)) 0 0 =
          (amp (entry D κ (e, D.table x e)) : ℂ) := by simp [flagRot]
      simp only [if_true, true_and, one_mul, h1, orient_sum]
      cases b <;> rfl
    · simp [hf]
  · simp [hz]

/-- The factor of the logical native factor unitary: `B = clean ∘ facOp ∘ J₀`. -/
theorem factor_eq (D : Data X n Z s) (κ : ℝ) (x : X) :
    (known D).factor ((factorProgram D κ).eval x) =
      (clean (n := n) (Z := Z)).toContinuousLinearMap ∘L facOp D κ x ∘L
        boundary (D.rowloc x) (D.colloc x) := by
  change proj ∘L ((valueProgram D κ).eval x * (locatorProgram D).eval x) ∘L
    (clean.toContinuousLinearMap ∘L FixedLocatorConjugation.fixedBoundary D.slot) = _
  rw [mul_def, ← FixedLocatorConjugation.locator_boundary D x]
  have hL := locatorProgram_intertwines D x
  have hP := proj_value_clean D κ x
  calc proj ∘L ((valueProgram D κ).eval x ∘L (locatorProgram D).eval x) ∘L
        (clean.toContinuousLinearMap ∘L FixedLocatorConjugation.fixedBoundary D.slot)
      = proj ∘L (valueProgram D κ).eval x ∘L ((locatorProgram D).eval x ∘L
          clean.toContinuousLinearMap) ∘L FixedLocatorConjugation.fixedBoundary D.slot := by
        simp only [comp_assoc]
    _ = (proj ∘L (valueProgram D κ).eval x ∘L clean.toContinuousLinearMap) ∘L
          (FixedLocatorConjugation.locator D x ∘L
            FixedLocatorConjugation.fixedBoundary D.slot) := by
        rw [hL]; simp only [comp_assoc]
    _ = _ := by rw [hP]; simp only [comp_assoc]

end

end NativeSignedFactor
