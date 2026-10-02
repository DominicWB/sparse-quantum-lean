import SparseHamiltonian.AmplificationQuery

/-!
# Synchronized finite SELECT schedules

A dependent direct sum of branches is executed in parallel layers. Branches
that have finished use identity in later layers. The number of layers is a
maximum branch length, not a sum of lengths. Query bounds below require uniform
implementations of each entire layer; no direct-sum query access is postulated.
-/

namespace SparseHamiltonian.SynchronizedSelect

noncomputable section
open scoped BigOperators
open ContinuousLinearMap OracleCircuit

section Products
variable {M : Type*} [Monoid M]

/-- Chronological product: the new operation acts on the left. -/
def product (step : ℕ → M) : ℕ → M
  | 0 => 1
  | n + 1 => step n * product step n

@[simp] theorem product_zero (step : ℕ → M) : product step 0 = 1 := rfl
@[simp] theorem product_succ (step : ℕ → M) (n : ℕ) :
    product step (n + 1) = step n * product step n := rfl

/-- Only operations strictly before the stopping time affect the product. -/
theorem product_congr (a b : ℕ → M) (N : ℕ) (h : ∀ r < N, a r = b r) :
    product a N = product b N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [product_succ, product_succ, h N (by omega), ih (fun r hr => h r (by omega))]

/-- Padding a finished branch by identities preserves its exact action. -/
theorem product_padded (step : ℕ → M) (n N : ℕ) (hn : n ≤ N) :
    product (fun r => if r < n then step r else 1) N = product step n := by
  have hbase : product (fun r => if r < n then step r else 1) n = product step n := by
    apply product_congr
    intro r hr
    simp only [if_pos hr]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa only [Nat.add_zero] using hbase
  | succ k ih =>
      rw [Nat.add_succ, product_succ, if_neg (by omega : ¬ n + k < n), one_mul, ih (by omega)]

end Products

section Hilbert
variable {ι : Type*} [Fintype ι]
  {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)]

/-- Direct sums commute with chronological products, including dependent spaces. -/
theorem product_diagonal (step : ∀ i, ℕ → V i →L[ℂ] V i) (N : ℕ) :
    product (fun r => WeightedClock.diagonal (fun i => step i r)) N =
      WeightedClock.diagonal (fun i => product (step i) N) := by
  induction N with
  | zero => exact WeightedClock.diagonal_one.symm
  | succ N ih =>
      rw [product_succ, ih]
      exact WeightedClock.diagonal_comp _ _

/-- One entire synchronized layer, with an identity on each finished branch. -/
def layer (step : ∀ i, ℕ → V i →L[ℂ] V i) (length : ι → ℕ) (r : ℕ) :
    PiLp 2 V →L[ℂ] PiLp 2 V :=
  WeightedClock.diagonal (fun i => if r < length i then step i r else 1)

/-- SELECT executed with one layer per possible branch step. -/
def schedule (step : ∀ i, ℕ → V i →L[ℂ] V i) (length : ι → ℕ) (N : ℕ) :
    PiLp 2 V →L[ℂ] PiLp 2 V := product (layer step length) N

/-- The parallel padded schedule equals the exact SELECT of the branch products. -/
theorem schedule_eq (step : ∀ i, ℕ → V i →L[ℂ] V i) (length : ι → ℕ) (N : ℕ)
    (hN : ∀ i, length i ≤ N) :
    schedule step length N = WeightedClock.diagonal (fun i => product (step i) (length i)) := by
  unfold schedule layer
  rw [product_diagonal]
  congr 1
  funext i
  exact product_padded (step i) (length i) N (hN i)

end Hilbert

section Queries
variable {X K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Compose actual uniform layer programs; the bound is the sum of their costs. -/
theorem implements_product (O : X → K →L[ℂ] K) (step : ℕ → X → K →L[ℂ] K)
    (q : ℕ → ℕ) (N : ℕ)
    (h : ∀ r < N, Implements O (step r) (q r)) :
    Implements O (fun x => product (fun r => step r x) N) (∑ r ∈ Finset.range N, q r) := by
  induction N with
  | zero => exact Implements.identity
  | succ N ih =>
      have hPrev := ih (fun r hr => h r (by omega))
      have hNext := (h N (by omega)).mul hPrev
      simpa only [product_succ, Finset.sum_range_succ, Nat.add_comm] using hNext

/-- A common certified layer bound gives a linear bound in the number of layers. -/
theorem implements_product_uniform (O : X → K →L[ℂ] K)
    (step : ℕ → X → K →L[ℂ] K) (q N : ℕ)
    (h : ∀ r < N, Implements O (step r) q) :
    Implements O (fun x => product (fun r => step r x) N) (N * q) := by
  simpa using implements_product O step (fun _ => q) N h

end Queries

section SelectedQueries
variable {ι X : Type*} [Fintype ι]
  {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)]
  [∀ i, CompleteSpace (V i)]

/-- Maximum-length query accounting for SELECT, conditional only on actual
uniform implementations of the synchronized whole-layer operations. A separate
oracle construction must discharge these premises. -/
theorem selected_implements (O : X → PiLp 2 V →L[ℂ] PiLp 2 V)
    (step : X → ∀ i, ℕ → V i →L[ℂ] V i) (length : ι → ℕ) (N q : ℕ)
    (hN : ∀ i, length i ≤ N)
    (hLayer : ∀ r < N, Implements O (fun x => layer (step x) length r) q) :
    Implements O (fun x => WeightedClock.diagonal
      (fun i => product (step x i) (length i))) (N * q) := by
  have h := implements_product_uniform O (fun r x => layer (step x) length r) q N hLayer
  exact h.congr (fun x => schedule_eq (step x) length N hN)

end SelectedQueries
end
end SparseHamiltonian.SynchronizedSelect
