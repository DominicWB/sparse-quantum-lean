import SparseODE.ODEFixedTaggedMoments

/-!
# Public two-entry decoder for the tagged LCHS Cayley gates

The address tag is a spectator of the original entry lookup. A fixed address
exchange obtains the transposed entry. The gate table depends on both decoded
words and known real parameters, but not on the unknown matrix instance.
-/

namespace SparseHamiltonian.ODETaggedValueDecoder

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

/-- One copy of each original address for each support tag. -/
abbrev Address (n : Type*) := (n × n) ⊕ (n × n)

def edge {n : Type*} : Address n → n × n := Sum.elim id id

def tag {n : Type*} : Address n → Bool := Sum.elim (fun _ => false) (fun _ => true)

/-- The tag is unchanged while the two original address indices are exchanged. -/
def exchange (n : Type*) : Address n ≃ Address n where
  toFun := Sum.map Prod.swap Prod.swap
  invFun := Sum.map Prod.swap Prod.swap
  left_inv := by intro a; cases a <;> rfl
  right_inv := by intro a; cases a <;> rfl

@[simp] theorem edge_exchange {n : Type*} (a : Address n) :
    edge (exchange n a) = (edge a).swap := by cases a <;> rfl

@[simp] theorem tag_exchange {n : Type*} (a : Address n) :
    tag (exchange n a) = tag a := by cases a <;> rfl

/-- Exact LCHS entry, formed from the two original complex entries. -/
def entry (k : ℝ) (u v : ℂ) : ℂ :=
  (((k : ℂ) - Complex.I) / 2) * u + (((k : ℂ) + Complex.I) / 2) * star v

/-- An entry shared by both supports is split in half; absent supports vanish. -/
def taggedEntry (k : ℝ) (a : Bool) (u v : ℂ) : ℂ :=
  if a then
    if v = 0 then 0 else if u = 0 then entry k u v else entry k u v / 2
  else
    if u = 0 then 0 else if v = 0 then entry k u v else entry k u v / 2

/-- This public scalar arithmetic exactly reproduces the already verified
tagged matrix, including cancellation and unmatched zero padding. -/
theorem taggedEntry_eq {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (k : ℝ) (a : Bool) (i j : n) :
    taggedEntry k a (M i j) (M j i) =
      ODETaggedSupport.tagValue M (ODEMatrixEnergy.lchsHamiltonian M k) a i j := by
  cases a <;> by_cases h₀ : M i j = 0 <;> by_cases h₁ : M j i = 0 <;>
    simp only [taggedEntry, entry, ODETaggedSupport.tagValue,
      ODETaggedSupport.tagZero, ODETaggedSupport.tagOne,
      ODEMatrixEnergy.lchsHamiltonian_entry, h₀, h₁,
      Bool.false_eq_true, if_false, if_true]

@[simp] theorem taggedEntry_zero (k : ℝ) (a : Bool) :
    taggedEntry k a 0 0 = 0 := by cases a <;> simp [taggedEntry]

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- The original table with an untouched support-tag address. -/
def table (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (a : Address n) : Z :=
  D.table x (edge a)

/-- Unknown data enter only through the two value words. The first word is
the transposed-address value and the second is the current-address value. -/
def decodedEntry (D : NativeSparseBlockEncoding.Data X n Z s) (k : ℝ)
    (a : Address n) (u v : Z) : ℂ :=
  taggedEntry k (tag a) (D.decode (edge a) v) (D.decode (edge a).swap u)

/-- The exact tagged entry selected by an actual input instance. -/
def actualEntry (D : NativeSparseBlockEncoding.Data X n Z s) (k : ℝ)
    (x : X) (a : Address n) : ℂ :=
  ODETaggedSupport.tagValue (D.matrix x) (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k)
    (tag a) (edge a).1 (edge a).2

theorem decodedEntry_correct (D : NativeSparseBlockEncoding.Data X n Z s)
    (k : ℝ) (x : X) (a : Address n) :
    decodedEntry D k a (table D x (exchange n a)) (table D x a) =
      actualEntry D k x a := by
  unfold decodedEntry table actualEntry
  rw [edge_exchange]
  rcases h : edge a with ⟨i, j⟩
  change taggedEntry k (tag a) (D.decode (i, j) (D.table x (i, j)))
      (D.decode (j, i) (D.table x (j, i))) =
    ODETaggedSupport.tagValue (D.matrix x)
      (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) (tag a) i j
  rw [D.decoded, D.decoded]
  exact taggedEntry_eq (D.matrix x) k (tag a) i j

/-- The public scale multiplying the tagged entry in the Cayley rotation. -/
def scale (s : ℕ) (γ ρ : ℝ) : ℝ := γ * Real.sqrt (2 * (s : ℝ)) / ρ

/-- Exact rotation for every pair of codes, including dirty scratch inputs. -/
def gates (D : NativeSparseBlockEncoding.Data X n Z s) (k γ ρ : ℝ)
    (a : Address n) (u v : Z) : ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit :=
  ExactEdgeCayley.action ((scale s γ ρ : ℂ) * decodedEntry D k a u v)

theorem gates_unitary (D : NativeSparseBlockEncoding.Data X n Z s) (k γ ρ : ℝ)
    (a : Address n) (u v : Z) : IsUnitary (gates D k γ ρ a u v) :=
  ExactEdgeCayley.action_unitary _

theorem gates_correct (D : NativeSparseBlockEncoding.Data X n Z s)
    (k γ ρ : ℝ) (x : X) (a : Address n) :
    gates D k γ ρ a (table D x (exchange n a)) (table D x a) =
      ExactEdgeCayley.action ((scale s γ ρ : ℂ) * actualEntry D k x a) := by
  unfold gates
  rw [decodedEntry_correct]

end
end SparseHamiltonian.ODETaggedValueDecoder
