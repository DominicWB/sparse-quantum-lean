import ODELowerBoundExtensions.Dyson.Series
import TimeDependentExtensions.Mesh.Refinement

set_option autoImplicit false

/-!
# The slot schedule of a configuration (`odel:lem:dyson`, lines 4200-4206)

The SELECT circuit of the Dyson LCU has `K` factor slots, executed in the order `0, 1, …, K-1`.
For a configuration `c` of degree `k ≤ K`, slot `j < k` applies the block-encoded matrix of the
cell `cell c j` (the `j`-th entry of the sorted label sequence of `c`), and the slots `j ≥ k` are
idle (identity). The cell of a slot is public and computed reversibly from the label (line 4202,
"sort a working copy reversibly while retaining the original labels"); here it is a known
function of the configuration register.

* `Cfg.start c r = ∑_{i<r} c i`: the first slot of cell `r`;
* `Cfg.cell hM c j`: the cell `r` with `start r ≤ j < start (r+1)`;
* `Cfg.active c j = (j < degree c)`;
* `slot_product`: the slot product `∏_{j<K} (active ? X_{cell j} : 1)` (slot `0` first) is the
  configuration product `cfgProduct X c` (reuses `evolution_blocks`).
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

open SparseHamiltonian
open SparseHamiltonian.TimeDependent (evolution)
open scoped BigOperators

namespace Cfg

variable {K M : ℕ}

/-- The first slot of cell `r`: `start c r = ∑_{i<r} c i`. -/
def start (c : Cfg K M) (r : ℕ) : ℕ := ∑ i ∈ Finset.range r, c.count i

/-- The cell of slot `j`: the largest `r < M` with `start c r ≤ j`, i.e. the cell `r` with
`start c r ≤ j < start c (r+1)` when `j < degree c`. -/
def cell (hM : 0 < M) (c : Cfg K M) (j : ℕ) : Fin M :=
  ⟨Nat.findGreatest (fun r => c.start r ≤ j) (M - 1), by
    have h := Nat.findGreatest_le (P := fun r => c.start r ≤ j) (M - 1)
    omega⟩

/-- Slot `j` is used by `c` iff `j < degree c`. -/
def active (c : Cfg K M) (j : ℕ) : Bool := decide (j < c.degree)

/-- The first block starts at slot `0`. -/
theorem start_zero (c : Cfg K M) : c.start 0 = 0 := by
  simp [start]

/-- The last block ends at the total degree. -/
theorem start_last (c : Cfg K M) : c.start M = c.degree := by
  rw [start, degree, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [count, r.isLt]

/-- The block starts are monotone. -/
theorem start_mono (c : Cfg K M) : Monotone c.start := by
  intro _ _ h
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

/-- A block length is the cell count: `start c (r + 1) - start c r = count c r`. -/
theorem start_succ_sub (c : Cfg K M) (r : ℕ) : c.start (r + 1) - c.start r = c.count r := by
  rw [start, start, Finset.sum_range_succ, Nat.add_sub_cancel_left]

/-- Slot `j` is active iff `j < degree c`. -/
theorem active_iff (c : Cfg K M) (j : ℕ) : c.active j = true ↔ j < c.degree :=
  decide_eq_true_iff

/-- The defining property of the cell of an active slot. -/
theorem cell_spec (hM : 0 < M) (c : Cfg K M) {j : ℕ} (hj : j < c.degree) :
    c.start (c.cell hM j) ≤ j ∧ j < c.start ((c.cell hM j : ℕ) + 1) := by
  show c.start (Nat.findGreatest (fun r => c.start r ≤ j) (M - 1)) ≤ j ∧
    j < c.start (Nat.findGreatest (fun r => c.start r ≤ j) (M - 1) + 1)
  refine ⟨Nat.findGreatest_spec (P := fun r => c.start r ≤ j) (Nat.zero_le _)
    (by simp [start_zero]), ?_⟩
  have hle := Nat.findGreatest_le (P := fun r => c.start r ≤ j) (M - 1)
  rcases Nat.lt_or_ge (Nat.findGreatest (fun r => c.start r ≤ j) (M - 1)) (M - 1) with h | h
  · have := Nat.findGreatest_is_greatest (P := fun r => c.start r ≤ j)
      (Nat.lt_succ_self _) (show _ + 1 ≤ M - 1 by omega)
    exact Nat.lt_of_not_le this
  · have heq : Nat.findGreatest (fun r => c.start r ≤ j) (M - 1) + 1 = M := by omega
    rw [heq, start_last]
    exact hj

/-- Inside the block of cell `r`, the slot cell is `r`. -/
theorem cell_eq (hM : 0 < M) (c : Cfg K M) {r j : ℕ} (hr : r < M) (h1 : c.start r ≤ j)
    (h2 : j < c.start (r + 1)) : (c.cell hM j : ℕ) = r := by
  show Nat.findGreatest (fun r => c.start r ≤ j) (M - 1) = r
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by omega, fun _ => h1, fun k hk _ hP => ?_⟩
  have := c.start_mono (show r + 1 ≤ k by omega)
  exact absurd hP (by omega)

end Cfg

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- **Slot product = configuration product**: executing the `K` slots in order, slot `j`
applying `X (cell c j)` when active and the identity otherwise, gives
`X_{M-1}^{c_{M-1}} ⋯ X_0^{c_0}`. -/
theorem slot_product {K M : ℕ} (hM : 0 < M) (X : ℕ → V →L[ℂ] V) (c : Cfg K M) :
    evolution (fun j => if c.active j then X (c.cell hM j) else 1) K = cfgProduct X c := by
  set U : ℕ → V →L[ℂ] V := fun j => if c.active j then X (c.cell hM j) else 1 with hU
  -- the idle tail `[degree, K)` is the identity
  have htail : evolution U K = evolution U c.degree := by
    have hK : K = c.degree + (K - c.degree) := (Nat.add_sub_cancel' c.degree_le).symm
    have h1 : TimeDependent.orderedProduct U (0 + c.degree) (K - c.degree) = 1 := by
      rw [TimeDependentExtensions.orderedProduct_congr_const U 1 _ _ (fun j _ => by
        have : ¬ c.active (0 + c.degree + j) = true := by
          rw [Cfg.active_iff]; omega
        simp only [hU, if_neg this]), one_pow]
    show TimeDependent.orderedProduct U 0 K = TimeDependent.orderedProduct U 0 c.degree
    calc TimeDependent.orderedProduct U 0 K
        = TimeDependent.orderedProduct U 0 (c.degree + (K - c.degree)) := congrArg _ hK
      _ = TimeDependent.orderedProduct U 0 c.degree := by
        rw [TimeDependentExtensions.orderedProduct_add, h1, one_mul]
  rw [htail, ← c.start_last, TimeDependentExtensions.evolution_blocks U c.start c.start_zero
    c.start_mono M, cfgProduct]
  refine TimeDependentExtensions.evolution_congr' _ _ M fun r hr => ?_
  rw [TimeDependentExtensions.orderedProduct_congr_const U (X r) _ _ (fun j hj => by
    have hlt : c.start r + j < c.start (r + 1) := by omega
    have hdeg : c.start (r + 1) ≤ c.degree := by
      rw [← c.start_last]; exact c.start_mono (by omega)
    have hact : c.active (c.start r + j) = true := by
      rw [Cfg.active_iff]; omega
    have hcell := c.cell_eq hM hr (Nat.le_add_right _ _) hlt
    simp only [hU, if_pos hact, hcell]), c.start_succ_sub r]

end

end ODELowerBoundExtensions.Dyson
