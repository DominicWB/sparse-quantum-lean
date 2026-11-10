import GeneralSparseAccess.PaddedData
import GateOptimalBinary.Tables

/-!
# Binary entry decoding

Theorem `ode:thm:gates` states: "Assume efficient binary entry decoding, polynomial-cost reversible
public arithmetic and the finite-gate assumptions of Section `gate:sec:result`." The package's
gate-level dissipative solvers read the stored words as two `b`-bit two's complement words decoded
by `c₀(X + iY)` and compute the rotation angles by reversible public arithmetic (the register
programs and CORDIC circuits of `GateBinaryODE`, `GateBinaryODETime`). For sparse access with any
public decoder `val` of the stored words (Section `hs:sec:control`), this module formalises the
binary entry decoding, with exactness (`val w = c₀ (X + iY)` for `b'`-bit components) as this
package's own condition:

* `BinDecode b b' A`: a reversible circuit of controlled NOT gates with at most three controls on
  the stored word (`2b` bits), the decoded word (two `b'`-bit two's complement components) and `A`
  work wires, which writes the decoded word `dw w` on clean output and work wires and restores the
  work wires (`compute`); `BinDecode.Exact dc val c₀`: the decoding is exact,
  `val w = c₀ (X(w) + i Y(w))` for the components `X(w)`, `Y(w)` of `dw w`; `BinDecode.cost`: its
  gates and wires (`|circ| + 2b + 2b' + A`), `BinDecode.wires`: its wires (`2b + 2b' + A`);
* `QData.decData`: the decoded data, the sparse access with the stored words replaced by their
  decoded words read by `c₀(X + iY)`, with the same matrix (`decData_matrix`) and locators;
* `BinDecode.copy`: the copy of the stored word, an exact decoding of the decoder `c₀(X + iY)` with
  `2b` gates (`copy_exact`, `copy_cost`: cost `6b + A`);
* `BinDecode.table`: the lookup-table decoding of any word function, with `2^{2b} · 2b' (4b + 1)`
  gates at most (`table_cost_le`); every decoder whose values are binary entries, `val w = c₀ (X + iY)`
  for two `b'`-bit two's complement words, has an exact table decoding (`exists_table_exact`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralDecoderODE

noncomputable section
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative SparseHamiltonian.GateBinary
open SparseHamiltonian.GeneralSparseAccess
open GateOptimalBinary (tableC tableC_elem tableC_classical tableC_compute tableC_length)

/-! ### Decoding circuits -/

/-- **The wires of a decoding circuit**: the stored word, the decoded word and `A` work wires. -/
abbrev DW (b b' A : ℕ) := VW b ⊕ AWr b' b' A

/-- **A binary entry decoding** of stored words of `2b` bits into words of two `b'`-bit two's
complement components: a reversible circuit of controlled NOT gates with at most three controls that
writes the decoded word `dw w` on clean output and work wires and restores the work wires. -/
structure BinDecode (b b' A : ℕ) where
  /-- The circuit. -/
  circ : List (Gate (DW b b' A))
  /-- The decoded word. -/
  dw : Cfg (VW b) → Cfg (VW b')
  elem : ∀ g ∈ circ, g.cs.length ≤ 3
  classical : Classical circ
  compute : ∀ w : Cfg (VW b), cfgRun circ (Sum.elim w (fun _ => false)) =
    Sum.elim w (Sum.elim (dw w) (fun _ => false))

namespace BinDecode

variable {b b' A : ℕ}

/-- **The decoding is exact** for the decoder `val` with the scale `c₀`: the decoded word is a
binary entry of the value, `val w = c₀ (X(w) + i Y(w))`. -/
def Exact (dc : BinDecode b b' A) (val : Cfg (VW b) → ℂ) (c₀ : ℝ) : Prop :=
  ∀ w, val w = (c₀ : ℂ) * gauss (dc.dw w)

/-- **The cost of a decoding**: its gates and its wires (the stored word, the decoded word and the
work wires). -/
def cost (dc : BinDecode b b' A) : ℕ := dc.circ.length + (2 * b + 2 * b' + A)

/-- **The wires of a decoding**: the stored word, the decoded word and the work wires. -/
def wires (_dc : BinDecode b b' A) : ℕ := 2 * b + 2 * b' + A

/-- The wires are part of the cost. -/
theorem wires_le_cost (dc : BinDecode b b' A) : dc.wires ≤ dc.cost := by
  unfold wires cost
  omega

/-- The gates of a decoding are elementary. -/
theorem gateOK (dc : BinDecode b b' A) : ∀ g ∈ dc.circ, GateOK 3 g := fun g hg =>
  ⟨dc.elem g hg, (dc.classical g hg).2, by rw [(dc.classical g hg).1]; exact pauliX_unitary⟩

end BinDecode

/-! ### The zero word and the size of a decoded value -/

section Words

variable {b : ℕ}

theorem twos_allFalse {B : Type*} {m : ℕ} (r : Fin m → B) : twos r (fun _ : B => false) = 0 := by
  unfold twos
  have h : (fun j => if h : j < m then (fun _ : B => false) (r ⟨j, h⟩) else false) =
      fun _ => false := by
    funext j
    split_ifs <;> rfl
  have h0 : ofBits (fun _ => false) m = 0#m := by
    rw [← ofBits_getLsbD (0#m)]
    apply ofBits_congr
    intro i _
    simp
  rw [h, h0, BitVec.toInt_zero]

/-- The all-zero word decodes to zero. -/
theorem gauss_allFalse : gauss (b := b) (fun _ => false) = 0 := by
  unfold gauss
  rw [twos_allFalse, twos_allFalse]
  simp

theorem abs_twos_le {B : Type*} {m : ℕ} (r : Fin m → B) (x : B → Bool) :
    |(twos r x : ℝ)| ≤ 2 ^ m := by
  have h1 := BitVec.toInt_lt (x := ofBits (fun j => if h : j < m then x (r ⟨j, h⟩) else false) m)
  have h2 := BitVec.le_toInt (ofBits (fun j => if h : j < m then x (r ⟨j, h⟩) else false) m)
  have h3 : (2 : ℤ) ^ (m - 1) ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (Nat.sub_le m 1)
  have hz : |twos r x| ≤ (2 : ℤ) ^ m := by
    unfold twos
    rw [abs_le]
    constructor <;> linarith
  exact_mod_cast hz

/-- **The size of a decoded value**: `‖X + i Y‖ ≤ 2^{b+1}` for `b`-bit components. -/
theorem norm_gauss_le (z : Cfg (VW b)) : ‖gauss z‖ ≤ 2 ^ (b + 1) := by
  unfold gauss
  have hx := abs_twos_le (B := VW b) Sum.inl z
  have hy := abs_twos_le (B := VW b) Sum.inr z
  calc ‖((twos (B := VW b) Sum.inl z : ℂ) + (twos (B := VW b) Sum.inr z : ℂ) * Complex.I)‖
      ≤ ‖(twos (B := VW b) Sum.inl z : ℂ)‖ + ‖(twos (B := VW b) Sum.inr z : ℂ) * Complex.I‖ :=
        norm_add_le _ _
    _ = |(twos (B := VW b) Sum.inl z : ℝ)| + |(twos (B := VW b) Sum.inr z : ℝ)| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast, Complex.norm_intCast]
    _ ≤ 2 ^ b + 2 ^ b := add_le_add hx hy
    _ = 2 ^ (b + 1) := by ring

end Words

/-! ### The decoded data -/

end

end SparseHamiltonian.GeneralDecoderODE

namespace SparseHamiltonian.GeneralSparseAccess.QData

noncomputable section
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative SparseHamiltonian.GateBinary
open SparseHamiltonian.GeneralDecoderODE

variable {X : Type*} {N s k b b' A : ℕ}

/-- **The decoded data**: the sparse access of `D` with every stored word replaced by its decoded
word, read by the decoder `c₀(X + iY)`; for an exact decoding it has the matrix of `D`, and its
locators are those of `D`. -/
def decData (D : QData X N s k b) (dc : BinDecode b b' A) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hdc : dc.Exact D.val c₀) : QData X N s k b' where
  hN := D.hN
  hs := D.hs
  slots_pos := D.slots_pos
  scale := c₀ * 2 ^ (b' + 1)
  scale_pos := by positivity
  matrix := D.matrix
  table x e := dc.dw (D.table x e)
  val z := (c₀ : ℂ) * gauss z
  val_bound z := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc₀.le]
    exact mul_le_mul_of_nonneg_left (norm_gauss_le z) hc₀.le
  decoded x i j := (hdc _).symm.trans (D.decoded x i j)
  rowloc := D.rowloc
  colloc := D.colloc
  row_injective := D.row_injective
  column_injective := D.column_injective
  row_covers := D.row_covers
  column_covers := D.column_covers
  rowOracle := D.rowOracle
  columnOracle := D.columnOracle
  row_unitary := D.row_unitary
  column_unitary := D.column_unitary
  row_valid := D.row_valid
  column_valid := D.column_valid

variable (D : QData X N s k b) (dc : BinDecode b b' A) (c₀ : ℝ) (hc₀ : 0 < c₀)
  (hdc : dc.Exact D.val c₀)

@[simp] theorem decData_matrix : (D.decData dc c₀ hc₀ hdc).matrix = D.matrix := rfl

@[simp] theorem decData_table (x : X) (e : Cfg (EW k)) :
    (D.decData dc c₀ hc₀ hdc).table x e = dc.dw (D.table x e) := rfl

@[simp] theorem decData_val (z : Cfg (VW b')) :
    (D.decData dc c₀ hc₀ hdc).val z = (c₀ : ℂ) * gauss z := rfl

@[simp] theorem decData_rowOracle (x : X) :
    (D.decData dc c₀ hc₀ hdc).rowOracle x = D.rowOracle x := rfl

@[simp] theorem decData_columnOracle (x : X) :
    (D.decData dc c₀ hc₀ hdc).columnOracle x = D.columnOracle x := rfl

/-- The all-zero decoded word decodes to zero. -/
theorem decData_val_zero : (D.decData dc c₀ hc₀ hdc).val (fun _ => false) = 0 := by
  rw [decData_val, gauss_allFalse, mul_zero]

/-- **The lift of the matrix extended by zero** is that of `D`. -/
theorem decData_padMat (x : X) : (D.decData dc c₀ hc₀ hdc).padMat x = D.padMat x := rfl

end

end SparseHamiltonian.GeneralSparseAccess.QData

namespace SparseHamiltonian.GeneralDecoderODE

noncomputable section
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative SparseHamiltonian.GateBinary
open SparseHamiltonian.GeneralSparseAccess
open GateOptimalBinary (tableC tableC_elem tableC_classical tableC_compute tableC_length)

/-! ### The copy of the stored word -/

section Copy

variable {b A : ℕ}

/-- The copy gate of the wire `v` of the stored word into the decoded word. -/
def copyGate (v : VW b) : Gate (DW b b A) :=
  ⟨[(Sum.inl v, true)], Sum.inr (Sum.inl v), pauliX⟩

/-- The copy gates. -/
def copyGates (b A : ℕ) : List (Gate (DW b b A)) :=
  (Finset.univ : Finset (VW b)).toList.map copyGate

theorem flipCfg_copyGate (v0 : VW b) (z : Cfg (DW b b A)) (u : DW b b A) :
    flipCfg [(Sum.inl v0, true)] (Sum.inr (Sum.inl v0)) z u =
      if u = Sum.inr (Sum.inl v0) then (z u ^^ z (Sum.inl v0)) else z u := by
  unfold flipCfg ctrlOK
  by_cases hz : z (Sum.inl v0) = true
  · simp only [List.all_cons, List.all_nil, Bool.and_true, hz, beq_self_eq_true, if_true]
    by_cases hu : u = Sum.inr (Sum.inl v0)
    · subst hu
      simp
    · rw [Function.update_of_ne hu, if_neg hu]
  · have hz' : z (Sum.inl v0) = false := by simpa using hz
    simp only [List.all_cons, List.all_nil, Bool.and_true, hz', beq_iff_eq, Bool.false_eq_true,
      if_false, Bool.xor_false, ite_self]

/-- **The copy gates of a list of distinct wires**: every target is XOR-ed with its source, and no
other wire changes. -/
theorem cfgRun_copyGates_list (L : List (VW b)) (hL : L.Nodup) (z : Cfg (DW b b A)) :
    (∀ v, cfgRun (L.map copyGate) z (Sum.inl v) = z (Sum.inl v)) ∧
    (∀ v ∈ L, cfgRun (L.map copyGate) z (Sum.inr (Sum.inl v)) =
      (z (Sum.inr (Sum.inl v)) ^^ z (Sum.inl v))) ∧
    (∀ v, v ∉ L → cfgRun (L.map copyGate) z (Sum.inr (Sum.inl v)) = z (Sum.inr (Sum.inl v))) ∧
    (∀ a, cfgRun (L.map copyGate) z (Sum.inr (Sum.inr a)) = z (Sum.inr (Sum.inr a))) := by
  induction L generalizing z with
  | nil =>
      exact ⟨fun _ => rfl, fun v hv => absurd hv (List.not_mem_nil), fun _ _ => rfl, fun _ => rfl⟩
  | cons v0 L ih =>
      rw [List.nodup_cons] at hL
      have e : cfgRun ((v0 :: L).map copyGate) z =
          cfgRun (L.map copyGate) (flipCfg [(Sum.inl v0, true)] (Sum.inr (Sum.inl v0)) z) := rfl
      rw [e]
      obtain ⟨ha, hb, hc, hd⟩ := ih hL.2 (flipCfg [(Sum.inl v0, true)] (Sum.inr (Sum.inl v0)) z)
      have hz1 := flipCfg_copyGate (A := A) v0 z
      refine ⟨fun v => ?_, fun v hv => ?_, fun v hv => ?_, fun a => ?_⟩
      · rw [ha, hz1, if_neg (fun h => by cases h)]
      · rcases List.mem_cons.mp hv with rfl | hv'
        · rw [hc _ hL.1, hz1, if_pos rfl]
        · have hne : v ≠ v0 := fun h => hL.1 (h ▸ hv')
          have hne' : (Sum.inr (Sum.inl v) : DW b b A) ≠ Sum.inr (Sum.inl v0) := fun h =>
            hne (Sum.inl_injective (Sum.inr_injective h))
          rw [hb v hv', hz1, if_neg hne', hz1, if_neg (fun h => by cases h)]
      · have hne : v ≠ v0 := fun h => hv (h ▸ List.mem_cons_self)
        have hne' : (Sum.inr (Sum.inl v) : DW b b A) ≠ Sum.inr (Sum.inl v0) := fun h =>
          hne (Sum.inl_injective (Sum.inr_injective h))
        rw [hc v (fun h => hv (List.mem_cons_of_mem v0 h)), hz1, if_neg hne']
      · rw [hd, hz1, if_neg (fun h => by cases h)]

theorem classical_copyGates (b A : ℕ) : Classical (copyGates b A) := by
  intro g hg
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hg
  refine ⟨rfl, ?_⟩
  intro c hc
  simp only [copyGate, List.mem_cons, List.not_mem_nil, or_false] at hc
  rw [hc]
  exact Sum.inl_ne_inr

/-- **The copy of the stored word**: the decoded word is the stored word. -/
def BinDecode.copy (b A : ℕ) : BinDecode b b A where
  circ := copyGates b A
  dw := id
  elem g hg := by
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hg
    simp [copyGate]
  classical := classical_copyGates b A
  compute w := by
    obtain ⟨ha, hb, -, hd⟩ := cfgRun_copyGates_list (A := A) _ (Finset.nodup_toList _)
      (Sum.elim w (fun _ => false))
    funext u
    rcases u with v | v | a
    · exact ha v
    · rw [show copyGates b A = (Finset.univ : Finset (VW b)).toList.map copyGate from rfl,
        hb v (Finset.mem_toList.mpr (Finset.mem_univ v))]
      simp
    · exact hd a

/-- **The copy is an exact decoding of the decoder `c₀(X + iY)`.** -/
theorem BinDecode.copy_exact (b A : ℕ) (val : Cfg (VW b) → ℂ) (c₀ : ℝ)
    (h : ∀ z, val z = (c₀ : ℂ) * gauss z) : (BinDecode.copy b A).Exact val c₀ := h

/-- The copy has `2b` gates on `4b + A` wires. -/
theorem BinDecode.copy_cost (b A : ℕ) : (BinDecode.copy b A).cost = 6 * b + A := by
  show (copyGates b A).length + (2 * b + 2 * b + A) = _
  unfold copyGates
  rw [List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_sum, Fintype.card_fin]
  ring

end Copy

/-! ### The lookup-table decoding -/

section Table

variable {b b' A : ℕ}

theorem card_VW (b : ℕ) : Fintype.card (VW b) = 2 * b := by
  rw [Fintype.card_sum, Fintype.card_fin]
  ring

/-- **The lookup-table decoding** of a word function, with `A ≥ 2b - 1` work wires. -/
def BinDecode.table (hA : 2 * b ≤ A + 1) (dw : Cfg (VW b) → Cfg (VW b')) : BinDecode b b' A where
  circ := tableC (I := VW b) (bT := b') (bP := b') (A := A) dw
  dw := dw
  elem := tableC_elem _
  classical := tableC_classical (by rw [card_VW]; exact hA) _
  compute w := tableC_compute (by rw [card_VW]; exact hA) _ w

/-- The cost of the lookup-table decoding: at most `2^{2b} · 2b' (4b + 1)` gates on
`2b + 2b' + A` wires. -/
theorem BinDecode.table_cost_le (hA : 2 * b ≤ A + 1) (dw : Cfg (VW b) → Cfg (VW b')) :
    (BinDecode.table (A := A) hA dw).cost ≤
      2 ^ (2 * b) * (2 * b') * (4 * b + 1) + (2 * b + 2 * b' + A) := by
  show (tableC (I := VW b) (bT := b') (bP := b') (A := A) dw).length + (2 * b + 2 * b' + A) ≤ _
  have h := tableC_length (I := VW b) (bT := b') (bP := b') (A := A) dw
  rw [card_VW] at h
  have e : 2 ^ (2 * b) * (b' + b') * (2 * (2 * b) + 1) = 2 ^ (2 * b) * (2 * b') * (4 * b + 1) := by
    ring
  omega

/-- **Every decoder with binary entries has an exact decoding**: if every value is
`c₀ (X + i Y)` for two `b'`-bit two's complement words, the lookup-table decoding of these words is
exact. -/
theorem exists_table_exact (hA : 2 * b ≤ A + 1) (val : Cfg (VW b) → ℂ) (c₀ : ℝ)
    (h : ∀ w, ∃ z : Cfg (VW b'), val w = (c₀ : ℂ) * gauss z) :
    ∃ dc : BinDecode b b' A, dc.Exact val c₀ ∧
      dc.cost ≤ 2 ^ (2 * b) * (2 * b') * (4 * b + 1) + (2 * b + 2 * b' + A) :=
  ⟨BinDecode.table hA (fun w => (h w).choose), fun w => (h w).choose_spec,
    BinDecode.table_cost_le hA _⟩

end Table

end

end SparseHamiltonian.GeneralDecoderODE
