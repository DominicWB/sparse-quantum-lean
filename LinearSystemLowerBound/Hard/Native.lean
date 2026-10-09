import LinearSystemLowerBound.Weight.Growth
import LinearSystemLowerBound.Hard.Dilation
import SparseHamiltonian.NativeSparseBlockEncoding
import SparseHamiltonian.OracleTransport

/-!
# Native sparse queries of the hard family and their weight growth

The released native sparse access (`NativeSparseBlockEncoding.Data`, `oracles`) consists of
the in-place row and column location oracles and the additive entry-value oracle
`|α, z⟩ ↦ |α, z + table x α⟩`, all on the common space `NSpace N Z`.

**Admissible oracle labels** (`Admissible D O w`).  An algorithm may use any workspace `K`
and any label type.  A label is admissible if it is

* a *native call* (`NativeCall D O`): in a fixed isometric layout `K ≃ ⊕_{σ ∈ S} NSpace`,
  the oracle acts on each spectator branch `σ` as the identity, as one native query of `D`,
  or as the inverse of one (`callOp`); this covers spectator registers, controlled and masked
  versions, inverses and coherent choices of the native query; its weight is at least one;
* or an input-independent unitary (for instance the right-hand-side preparation), with any
  weight.

For data whose locators are input-independent and whose table entries are fixed functions
of at most one input bit (`HardAccess`), every admissible label has weight growth
`((1 + 2/√m)²)^w` in both directions (`growth_admissible`).  The value query costs one
growth factor: on each address block it is a translation of the value register that depends
on one bit (`growth_lookup`, `growth_transl`).
-/

namespace LinearSystemLowerBound.Native

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct
open LinearSystemLowerBound LinearSystemLowerBound.Hard SparseHamiltonian ContinuousLinearMap

variable {n m : ℕ}

/-- The common native space: address, value and three-valued flag. -/
abbrev NSpace (N Z : Type*) := SparseFlagEmbedding.Space (N × N) Z

/-- The value register with payload `Q`. -/
abbrev VSpace (Z Q : Type*) := PiLp 2 (fun _ : Z => Q)

/-! ### Translations of the value register -/

section Transl

variable {Z Q : Type*} [Fintype Z] [AddCommGroup Z] [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]

/-- Translation `|z⟩ ↦ |z + δ⟩` of the value register. -/
def transl (δ : Z) : VSpace Z Q →L[ℂ] VSpace Z Q :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ Q (Equiv.addRight δ)).toLinearIsometry.toContinuousLinearMap

theorem transl_apply (δ : Z) (v : VSpace Z Q) (z : Z) : transl δ v z = v (z - δ) := by
  simp [transl, Equiv.piCongrLeft'_apply, sub_eq_add_neg]

theorem norm_transl (δ : Z) (v : VSpace Z Q) : ‖transl δ v‖ = ‖v‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ Q (Equiv.addRight δ)).norm_map v

omit [AddCommGroup Z] in
theorem growth_congr {O O' : (Fin n → Fin m) → VSpace Z Q →L[ℂ] VSpace Z Q} {C : ℝ}
    (h : Growth O C) (hO : ∀ x, O x = O' x) : Growth O' C := by
  have : O = O' := funext hO
  rw [← this]
  exact h

/-- **A one-bit translation** has weight growth `(1 + 2/√m)²`. -/
theorem growth_transl (hm : m ≠ 0) (g : (Fin n → Fin m) → Z) (hg : BitDetermined g) :
    Growth (fun x => (transl (g x) : VSpace Z Q →L[ℂ] VSpace Z Q)) ((1 + 2 / Real.sqrt m) ^ 2) := by
  have h1 : (1 : ℝ) ≤ (1 + 2 / Real.sqrt m) ^ 2 := by
    have : (0 : ℝ) ≤ 2 / Real.sqrt m := by positivity
    nlinarith
  rcases hg with ⟨e, he⟩ | ⟨c, q₀, e₀, e₁, he⟩
  · exact growth_mono (growth_congr (growth_const (transl (Q := Q) e) (norm_transl (Q := Q) e))
      (fun x => by rw [he])) h1
  · exact growth_congr (growth_bit hm c q₀ (transl (Q := Q) e₀) (transl (Q := Q) e₁)
      (norm_transl (Q := Q) e₀) (norm_transl (Q := Q) e₁)) (fun x => by rw [he]; split_ifs <;> rfl)

end Transl

/-! ### Additive lookups -/

section Lookup

variable {A Z Q : Type*} [Fintype A] [Fintype Z] [AddCommGroup Z] [NormedAddCommGroup Q]
  [InnerProductSpace ℂ Q]

/-- The value block at one address. -/
def slot (α : A) (φ : Fam (Fin n → Fin m) (PiLp 2 (fun _ : A × Z => Q))) :
    Fam (Fin n → Fin m) (VSpace Z Q) :=
  WithLp.toLp 2 (fun x => WithLp.toLp 2 (fun z => φ x (α, z)))

omit [AddCommGroup Z] [InnerProductSpace ℂ Q] in
theorem norm_sq_slot (φ : Fam (Fin n → Fin m) (PiLp 2 (fun _ : A × Z => Q))) :
    ‖φ‖ ^ 2 = ∑ α, ‖slot α φ‖ ^ 2 := by
  rw [norm_sq_fam]
  simp only [norm_sq_fam, slot, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

omit [AddCommGroup Z] in
theorem slot_act (α : A) (M : Matrix (Fin n → Fin m) (Fin n → Fin m) ℂ)
    (φ : Fam (Fin n → Fin m) (PiLp 2 (fun _ : A × Z => Q))) :
    slot α (act M φ) = act M (slot α φ) := by
  ext x z
  simp only [slot, act_apply, PiLp.toLp_apply, piLp_sum_apply, PiLp.smul_apply]

theorem slot_lookup (f : (Fin n → Fin m) → A → Z) (α : A)
    (ψ : Fam (Fin n → Fin m) (PiLp 2 (fun _ : A × Z => Q))) :
    slot α (joint (fun x => LookupControlledGate.oracle (K := Q) f x) ψ) =
      joint (fun x => transl (f x α)) (slot α ψ) := by
  ext x z
  simp [slot, joint_apply, transl_apply]

theorem slot_lookup_star [CompleteSpace Q] (f : (Fin n → Fin m) → A → Z) (α : A)
    (ψ : Fam (Fin n → Fin m) (PiLp 2 (fun _ : A × Z => Q))) :
    slot α (joint (fun x => star (LookupControlledGate.oracle (K := Q) f x)) ψ) =
      joint (fun x => transl (-(f x α))) (slot α ψ) := by
  ext x z
  simp [slot, joint_apply, transl_apply, star_eq_adjoint, sub_neg_eq_add]

/-- Weight growth of a block-diagonal family of value translations. -/
theorem growth_slots (O : (Fin n → Fin m) →
      PiLp 2 (fun _ : A × Z => Q) →L[ℂ] PiLp 2 (fun _ : A × Z => Q))
    (g : (Fin n → Fin m) → A → Z) (C : ℝ)
    (hslot : ∀ α ψ, slot α (joint O ψ) = joint (fun x => transl (g x α)) (slot α ψ))
    (h : ∀ α, Growth (fun x => (transl (g x α) : VSpace Z Q →L[ℂ] VSpace Z Q)) C) :
    Growth O C := by
  intro ψ
  rw [norm_sq_slot, norm_sq_slot, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro α _
  rw [slot_act, hslot, slot_act]
  exact h α _

/-- **An additive lookup** has the weight growth of its one-bit address blocks. -/
theorem growth_lookup (hm : m ≠ 0) (f : (Fin n → Fin m) → A → Z)
    (hf : ∀ α, BitDetermined (fun x => f x α)) :
    Growth (fun x => LookupControlledGate.oracle (K := Q) f x) ((1 + 2 / Real.sqrt m) ^ 2) :=
  growth_slots _ f _ (slot_lookup f) (fun α => growth_transl hm _ (hf α))

theorem growth_lookup_star [CompleteSpace Q] (hm : m ≠ 0) (f : (Fin n → Fin m) → A → Z)
    (hf : ∀ α, BitDetermined (fun x => f x α)) :
    Growth (fun x => star (LookupControlledGate.oracle (K := Q) f x))
      ((1 + 2 / Real.sqrt m) ^ 2) :=
  growth_slots _ (fun x α => -(f x α)) _ (slot_lookup_star f)
    (fun α => growth_transl hm _ ((hf α).comp (fun z => -z)))

end Lookup

/-! ### Native calls and admissible labels -/

section Admissible

variable {N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s : ℕ}

/-- One spectator branch of a native call: identity, a native query, or its inverse. -/
def callOp (D : NativeSparseBlockEncoding.Data (Fin n → Fin m) N Z s) :
    Option (NativeSparseBlockEncoding.Query × Bool) → (Fin n → Fin m) →
      NSpace N Z →L[ℂ] NSpace N Z
  | none, _ => 1
  | some (q, false), x => NativeSparseBlockEncoding.oracles D q x
  | some (q, true), x => star (NativeSparseBlockEncoding.oracles D q x)

/-- **A native call**: in a fixed isometric layout of the workspace as spectator branches of
the native space, every branch applies the identity, one native query, or its inverse. -/
def NativeCall {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (D : NativeSparseBlockEncoding.Data (Fin n → Fin m) N Z s)
    (O : (Fin n → Fin m) → K →L[ℂ] K) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (layout : K ≃ₗᵢ[ℂ] PiLp 2 (fun _ : S => NSpace N Z))
    (call : S → Option (NativeSparseBlockEncoding.Query × Bool)),
    ∀ x, O x = layout.symm.conjStarAlgEquiv
      (WeightedClock.diagonal (fun σ : S => callOp D (call σ) x))

/-- **Admissible labels**: native calls of weight at least one, or input-independent
unitaries of any weight. -/
def Admissible {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (D : NativeSparseBlockEncoding.Data (Fin n → Fin m) N Z s)
    (O : (Fin n → Fin m) → K →L[ℂ] K) (w : ℕ) : Prop :=
  (NativeCall D O ∧ 1 ≤ w) ∨ ((∀ x x', O x = O x') ∧ ∀ x, OracleCircuit.IsUnitary (O x))

/-- **Access conditions of the hard family**: input-independent location oracles and table
entries that are fixed functions of at most one input bit. -/
structure HardAccess (D : NativeSparseBlockEncoding.Data (Fin n → Fin m) N Z s) : Prop where
  row_const : ∀ x x', D.rowOracle x = D.rowOracle x'
  column_const : ∀ x x', D.columnOracle x = D.columnOracle x'
  table_bit : ∀ α, BitDetermined (fun x => D.table x α)

theorem diagonal_unitary {S : Type*} [Fintype S] {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (U : S → V →L[ℂ] V)
    (hU : ∀ σ, OracleCircuit.IsUnitary (U σ)) :
    OracleCircuit.IsUnitary (WeightedClock.diagonal U) := by
  constructor
  · change (WeightedClock.diagonal U)† ∘L WeightedClock.diagonal U = 1
    rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    simp only [show ∀ σ, (U σ)† ∘L U σ = 1 from fun σ => (hU σ).1, WeightedClock.diagonal_one]
  · change WeightedClock.diagonal U ∘L (WeightedClock.diagonal U)† = 1
    rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    simp only [show ∀ σ, U σ ∘L (U σ)† = 1 from fun σ => (hU σ).2, WeightedClock.diagonal_one]

theorem callOp_unitary (D : NativeSparseBlockEncoding.Data (Fin n → Fin m) N Z s)
    (c : Option (NativeSparseBlockEncoding.Query × Bool)) (x : Fin n → Fin m) :
    OracleCircuit.IsUnitary (callOp D c x) := by
  rcases c with _ | ⟨q, _ | _⟩
  · show OracleCircuit.IsUnitary (1 : NSpace N Z →L[ℂ] NSpace N Z)
    exact ⟨by simp, by simp⟩
  · exact NativeSparseBlockEncoding.oracles_unitary D q x
  · exact (NativeSparseBlockEncoding.oracles_unitary D q x).adjoint

theorem callOp_star (D : NativeSparseBlockEncoding.Data (Fin n → Fin m) N Z s)
    (c : Option (NativeSparseBlockEncoding.Query × Bool)) (x : Fin n → Fin m) :
    star (callOp D c x) = callOp D (c.map fun p => (p.1, !p.2)) x := by
  rcases c with _ | ⟨q, _ | _⟩
  · simp [callOp]
  · simp [callOp]
  · simp [callOp]

/-- Growth of one native query. -/
theorem growth_oracles (hm : m ≠ 0) (D : NativeSparseBlockEncoding.Data (Fin n → Fin m) N Z s)
    (hD : HardAccess D) (q : NativeSparseBlockEncoding.Query) :
    Growth (fun x => NativeSparseBlockEncoding.oracles D q x) ((1 + 2 / Real.sqrt m) ^ 2) ∧
      Growth (fun x => star (NativeSparseBlockEncoding.oracles D q x))
        ((1 + 2 / Real.sqrt m) ^ 2) := by
  have h1 : (1 : ℝ) ≤ (1 + 2 / Real.sqrt m) ^ 2 := by
    have : (0 : ℝ) ≤ 2 / Real.sqrt m := by positivity
    nlinarith
  have hconst : ∀ (U : (Fin n → Fin m) → NSpace N Z →L[ℂ] NSpace N Z),
      (∀ x x', U x = U x') → (∀ x, OracleCircuit.IsUnitary (U x)) →
      Growth U ((1 + 2 / Real.sqrt m) ^ 2) ∧
        Growth (fun x => star (U x)) ((1 + 2 / Real.sqrt m) ^ 2) := by
    intro U hU hUu
    obtain ⟨x₀⟩ : Nonempty (Fin n → Fin m) := ⟨fun _ => ⟨0, Nat.pos_of_ne_zero hm⟩⟩
    have e1 : U = fun _ => U x₀ := funext fun x => hU x x₀
    have e2 : (fun x => star (U x)) = fun _ => star (U x₀) := funext fun x => by rw [hU x x₀]
    refine ⟨?_, ?_⟩
    · rw [e1]
      exact growth_mono (growth_const _ (isUnitary_norm (hUu x₀))) h1
    · rw [e2]
      exact growth_mono (growth_const _ (isUnitary_norm (hUu x₀).adjoint)) h1
  cases q with
  | rowLocation =>
      exact hconst _ (fun x x' => by
          simp only [NativeSparseBlockEncoding.oracles, SparseFlagEmbedding.location,
            hD.row_const x x'])
        (fun x => NativeSparseBlockEncoding.oracles_unitary D _ x)
  | columnLocation =>
      exact hconst _ (fun x x' => by
          simp only [NativeSparseBlockEncoding.oracles, SparseFlagEmbedding.location,
            hD.column_const x x'])
        (fun x => NativeSparseBlockEncoding.oracles_unitary D _ x)
  | value =>
      exact ⟨growth_lookup (Q := SparseFlagEmbedding.Qutrit) hm D.table hD.table_bit,
        growth_lookup_star (Q := SparseFlagEmbedding.Qutrit) hm D.table hD.table_bit⟩

theorem growth_callOp (hm : m ≠ 0) (D : NativeSparseBlockEncoding.Data (Fin n → Fin m) N Z s)
    (hD : HardAccess D) (c : Option (NativeSparseBlockEncoding.Query × Bool)) :
    Growth (fun x => callOp D c x) ((1 + 2 / Real.sqrt m) ^ 2) := by
  have h1 : (1 : ℝ) ≤ (1 + 2 / Real.sqrt m) ^ 2 := by
    have : (0 : ℝ) ≤ 2 / Real.sqrt m := by positivity
    nlinarith
  rcases c with _ | ⟨q, _ | _⟩
  · exact growth_mono (growth_const 1 (fun v => by simp)) h1
  · exact (growth_oracles hm D hD q).1
  · exact (growth_oracles hm D hD q).2

/-- **Weight growth of admissible labels**, in both directions. -/
theorem growth_admissible (hm : m ≠ 0) {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (D : NativeSparseBlockEncoding.Data (Fin n → Fin m) N Z s) (hD : HardAccess D)
    (O : (Fin n → Fin m) → K →L[ℂ] K) (w : ℕ) (hO : Admissible D O w) :
    Growth O (((1 + 2 / Real.sqrt m) ^ 2) ^ w) ∧
      Growth (fun x => star (O x)) (((1 + 2 / Real.sqrt m) ^ 2) ^ w) ∧
      ∀ x, OracleCircuit.IsUnitary (O x) := by
  set C := (1 + 2 / Real.sqrt m) ^ 2
  have h1 : (1 : ℝ) ≤ C := by
    have : (0 : ℝ) ≤ 2 / Real.sqrt m := by positivity
    nlinarith
  rcases hO with ⟨⟨S, hS, layout, call, hcall⟩, hw⟩ | ⟨hconst, hunit⟩
  · have hpow : C ≤ C ^ w := le_self_pow₀ h1 (by omega)
    have hdiag : Growth (fun x => WeightedClock.diagonal (fun σ : S => callOp D (call σ) x)) C :=
      growth_diagonal (fun σ x => callOp D (call σ) x) C (fun σ => growth_callOp hm D hD _)
    have hdiag' : Growth (fun x => WeightedClock.diagonal
        (fun σ : S => callOp D ((call σ).map fun p => (p.1, !p.2)) x)) C :=
      growth_diagonal _ C (fun σ => growth_callOp hm D hD _)
    have hO : O = fun x => layout.symm.conjStarAlgEquiv
        (WeightedClock.diagonal (fun σ : S => callOp D (call σ) x)) := funext hcall
    have hstar : (fun x => star (O x)) = fun x => layout.symm.conjStarAlgEquiv
        (WeightedClock.diagonal (fun σ : S => callOp D ((call σ).map fun p => (p.1, !p.2)) x)) := by
      funext x
      rw [hcall, ← map_star, star_eq_adjoint, WeightedClock.diagonal_adjoint]
      congr 2
      funext σ
      rw [← star_eq_adjoint, callOp_star]
    refine ⟨?_, ?_, ?_⟩
    · rw [hO]
      exact growth_mono (growth_conj layout.symm _ C hdiag) hpow
    · rw [hstar]
      exact growth_mono (growth_conj layout.symm _ C hdiag') hpow
    · intro x
      rw [hcall]
      exact (diagonal_unitary _ (fun σ => callOp_unitary D (call σ) x)).transport layout.symm
  · have hCw : 1 ≤ C ^ w := one_le_pow₀ h1
    obtain ⟨x₀⟩ : Nonempty (Fin n → Fin m) := ⟨fun _ => ⟨0, Nat.pos_of_ne_zero hm⟩⟩
    have e1 : O = fun _ => O x₀ := funext fun x => hconst x x₀
    have e2 : (fun x => star (O x)) = fun _ => star (O x₀) := funext fun x => by rw [hconst x x₀]
    refine ⟨?_, ?_, hunit⟩
    · rw [e1]
      exact growth_mono (growth_const _ (isUnitary_norm (hunit x₀))) hCw
    · rw [e2]
      exact growth_mono (growth_const _ (isUnitary_norm (hunit x₀).adjoint)) hCw

end Admissible

end

end LinearSystemLowerBound.Native
