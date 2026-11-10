import GateEfficientHamiltonian.Circuit.Range
import GeneralSparseAccess.Compare

/-!
# Sparse access of general size on qubit registers

The manuscript's sparse access (Section `hs:sec:control`) for an `N × N` matrix with `s`-sparse
lists, `1 ≤ s ≤ N`, on qubit registers of `k` qubits, `N ≤ 2^k`, whose valid indices `0 ≤ i < N` and
list positions `0 ≤ a < s` are stored as little-endian binary words (`binW`):

* the value oracle XORs a stored word into the value register on every index pair of the register
  (`table`, on all `2^k × 2^k` configurations), and the public decoder `val` of the words gives the
  entries on the valid pairs (`decoded`);
* the row locator replaces a list position by its column index, `|i, a⟩ ↦ |i, row(i, a)⟩`, and the
  column locator replaces a list position by a row index while retaining the column,
  `|j, a⟩ ↦ |j, col(j, a)⟩` (`row_valid`, `column_valid`), for `i, j < N` and `a < s`; each is a
  unitary on its full register (`row_unitary`, `column_unitary`) whose action outside the valid list
  inputs is arbitrary;
* every list contains all nonzero entries of its row or column and has `s` distinct indices
  (`row_covers`, `column_covers`, `row_injective`, `column_injective`).

`QData.prims` are the three primitive oracles on the qubit register `PY k b` of the gate model: the
locators on the edge register and the value oracle as a permutation XOR-ing the stored word into
the value wires. `padMat` is the matrix on all `2^k` index configurations that agrees with the
matrix on valid indices and vanishes on the others; the conformance statements compare with its
evolution.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralSparseAccess

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary
open SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GatePointerEncoding (wordValue)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

/-! ### Binary words -/

/-- The little-endian `k`-bit word of a number. -/
def binW (k n : ℕ) : Cfg (Fin k) := fun j => n.testBit j.val

theorem wordValue_binW {k n : ℕ} (h : n < 2 ^ k) : wordValue (binW k n) = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · exact testBit_wordValue (binW k n) ⟨i, hi⟩
  · rw [testBit_wordValue_ge _ i (Nat.le_of_not_lt hi),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num)
        (Nat.le_of_not_lt hi)))]

theorem binW_wordValue {k : ℕ} (y : Cfg (Fin k)) : binW k (wordValue y) = y := by
  funext j
  exact testBit_wordValue y j

theorem binW_inj {k n m : ℕ} (hn : n < 2 ^ k) (hm : m < 2 ^ k) (h : binW k n = binW k m) :
    n = m := by
  rw [← wordValue_binW hn, ← wordValue_binW hm, h]

/-- The edge configuration of a pair of index words. -/
def edgeW (k : ℕ) (d₁ d₂ : Cfg (Fin k)) : Cfg (EW k) := Sum.elim d₁ d₂

@[simp] theorem edgeW_inl {k : ℕ} (d₁ d₂ : Cfg (Fin k)) (j : Fin k) :
    edgeW k d₁ d₂ (Sum.inl j) = d₁ j := rfl

@[simp] theorem edgeW_inr {k : ℕ} (d₁ d₂ : Cfg (Fin k)) (j : Fin k) :
    edgeW k d₁ d₂ (Sum.inr j) = d₂ j := rfl

theorem edgeW_eta {k : ℕ} (e : Cfg (EW k)) :
    edgeW k (fun j => e (Sum.inl j)) (fun j => e (Sum.inr j)) = e := by
  funext w
  rcases w with j | j <;> rfl

/-! ### The data -/

/-- **Sparse access of general size on qubit registers** (Section `hs:sec:control`): an `N × N`
matrix with `s`-sparse lists, `1 ≤ s ≤ N ≤ 2^k`, indices and list positions stored as `k`-bit
little-endian words, value words of `2b` bits read by the public decoder `val`, and locators that
are unitary on the full registers with the prescribed action on valid list inputs only. -/
structure QData (X : Type*) (N s k b : ℕ) where
  hN : N ≤ 2 ^ k
  hs : s ≤ N
  slots_pos : 0 < s
  scale : ℝ
  scale_pos : 0 < scale
  matrix : X → Matrix (Fin N) (Fin N) ℂ
  table : X → Cfg (EW k) → Cfg (VW b)
  val : Cfg (VW b) → ℂ
  val_bound : ∀ z, ‖val z‖ ≤ scale
  decoded : ∀ x (i j : Fin N), val (table x (edgeW k (binW k i) (binW k j))) = matrix x i j
  rowloc : X → Fin N → Fin s → Fin N
  colloc : X → Fin N → Fin s → Fin N
  row_injective : ∀ x i, Function.Injective (rowloc x i)
  column_injective : ∀ x j, Function.Injective (colloc x j)
  row_covers : ∀ x i j, matrix x i j ≠ 0 → ∃ a, rowloc x i a = j
  column_covers : ∀ x i j, matrix x i j ≠ 0 → ∃ a, colloc x j a = i
  rowOracle : X → EuclideanSpace ℂ (Cfg (EW k)) →L[ℂ] EuclideanSpace ℂ (Cfg (EW k))
  columnOracle : X → EuclideanSpace ℂ (Cfg (EW k)) →L[ℂ] EuclideanSpace ℂ (Cfg (EW k))
  row_unitary : ∀ x, IsUnitary (rowOracle x)
  column_unitary : ∀ x, IsUnitary (columnOracle x)
  row_valid : ∀ x (i : Fin N) (a : Fin s),
    rowOracle x (EuclideanSpace.single (edgeW k (binW k i) (binW k a)) 1) =
      EuclideanSpace.single (edgeW k (binW k i) (binW k (rowloc x i a))) 1
  column_valid : ∀ x (j : Fin N) (a : Fin s),
    columnOracle x (EuclideanSpace.single (edgeW k (binW k j) (binW k a)) 1) =
      EuclideanSpace.single (edgeW k (binW k j) (binW k (colloc x j a))) 1

namespace QData

variable {X : Type*} {N s k b : ℕ}

theorem N_pos (D : QData X N s k b) : 0 < N := lt_of_lt_of_le D.slots_pos D.hs

theorem s_le_pow (D : QData X N s k b) : s ≤ 2 ^ k := D.hs.trans D.hN

theorem lt_pow_of_N (D : QData X N s k b) (i : Fin N) : i.val < 2 ^ k :=
  lt_of_lt_of_le i.isLt D.hN

theorem lt_pow_of_s (D : QData X N s k b) (a : Fin s) : a.val < 2 ^ k :=
  lt_of_lt_of_le a.isLt D.s_le_pow

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The primitive oracles** on the register `PY k b` (an edge register and the value wires): the
row and the column locator on the edge register and the value oracle XOR-ing the stored word of
the edge into the value wires. -/
def prims (D : QData X N s k b) (x : X) : Query → Reg (PY k b) R →L[ℂ] Reg (PY k b) R
  | .rowLocation =>
      localOp Sum.inl Sum.inl_injective
        (fun _ => qlift (Equiv.refl (Cfg (EW k))) (D.rowOracle x))
  | .columnLocation =>
      localOp Sum.inl Sum.inl_injective
        (fun _ => qlift (Equiv.refl (Cfg (EW k))) (D.columnOracle x))
  | .value => permOp (xorEquiv (fun d => D.table x d))

theorem prims_row (D : QData X N s k b) (x : X) :
    D.prims (R := R) x Query.rowLocation = localOp Sum.inl Sum.inl_injective
      (fun _ => qlift (R := R) (Equiv.refl (Cfg (EW k))) (D.rowOracle x)) := by
  simp only [prims]

theorem prims_col (D : QData X N s k b) (x : X) :
    D.prims (R := R) x Query.columnLocation = localOp Sum.inl Sum.inl_injective
      (fun _ => qlift (R := R) (Equiv.refl (Cfg (EW k))) (D.columnOracle x)) := by
  simp only [prims]

theorem prims_val (D : QData X N s k b) (x : X) :
    D.prims (R := R) x Query.value = permOp (xorEquiv (fun d => D.table x d)) := by
  simp only [prims]

theorem prims_isUnitary (D : QData X N s k b) (x : X) (j : Query) :
    IsUnitary (D.prims (R := R) x j) := by
  cases j with
  | rowLocation =>
      rw [prims_row]
      exact localOp_isUnitary _ _ (fun _ => qlift_isUnitary _ (D.row_unitary x))
  | columnLocation =>
      rw [prims_col]
      exact localOp_isUnitary _ _ (fun _ => qlift_isUnitary _ (D.column_unitary x))
  | value =>
      rw [prims_val]
      exact isUnitary_permOp _

/-- **The padded matrix** on the `2^k` index configurations: the matrix on valid indices and zero
elsewhere. -/
def padMat (D : QData X N s k b) (x : X) : Matrix (Cfg (Fin k)) (Cfg (Fin k)) ℂ :=
  fun y y' => if h : wordValue y < N ∧ wordValue y' < N then
    D.matrix x ⟨wordValue y, h.1⟩ ⟨wordValue y', h.2⟩ else 0

theorem padMat_binW (D : QData X N s k b) (x : X) (i j : Fin N) :
    D.padMat x (binW k i) (binW k j) = D.matrix x i j := by
  have hi := wordValue_binW (D.lt_pow_of_N i)
  have hj := wordValue_binW (D.lt_pow_of_N j)
  have hlt : wordValue (binW k i) < N ∧ wordValue (binW k j) < N :=
    ⟨by rw [hi]; exact i.isLt, by rw [hj]; exact j.isLt⟩
  have e1 : (⟨wordValue (binW k i), hlt.1⟩ : Fin N) = i := Fin.ext hi
  have e2 : (⟨wordValue (binW k j), hlt.2⟩ : Fin N) = j := Fin.ext hj
  unfold padMat
  rw [dif_pos hlt, e1, e2]

end QData

end

end SparseHamiltonian.GeneralSparseAccess
