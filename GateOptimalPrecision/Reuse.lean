import GateOptimalPrecision.Amplify
import SignedFactorSimulation.Cascade

/-!
# Compiled signed reuse (Lemma `gate:lem:reuse`)

Lemma `gate:lem:reuse`: for known real weights `w_1, …, w_R` with `∑ |w_j| ≤ A₀`, an LCU
circuit has the successful block `A₀⁻¹ ∑_j w_j Ces_j(F)`, where `F` is the causal transfer of the
chronological product of the boundary network and the private operation, using `R` private calls
and `O(R(C_E + a_E + m + log(R+1)))` other gates.

The circuit is the released LCU circuit of the baseline gate theorem
(`SparseHamiltonian.GateCircuit.Sim.lcuI`, ideal operator `LCU`): it prepares the branch table and
the uniform pointer state of every branch exactly by binary trees of rotations, runs `N` reuse
steps (private call, boundary network at the current pointer word, pointer increment), and
unprepares. Its released block identity (`lcu_compression`) is a signed sum of reuse blocks; here
it is written in the Cesàro form of the manuscript:

* `netTransfer c σ J D m`: the causal transfer `F(w) = A + wB(I - wD)⁻¹C` of the chronological
  product on `2^m` slots (`gate:eq:global`, `gate:eq:transfer`);
* `lcu_ces`: the clean block of the ideal LCU operator is `∑_ℓ (wt_ℓ/2) Ces_{n_ℓ}(F)` (by the clock
  identity `SignedFactorSimulation.successfulBlock_eq_ces`), for any table with `∑ |wt_ℓ| = 2`;
* `padWt`, `padLen`, `padWt_mass`, `pad_sum`: weights with `∑ |w_j| ≤ A₀` are scaled by `2/A₀` and
  completed by two branches of length one with opposite weights `±(1 - ∑ |w_j|/A₀)` that cancel in
  the block (`padMass`; the manuscript pads with a dummy branch that fails the success test
  instead), so that the block is `A₀⁻¹ ∑_j w_j Ces_{n_j}(F)` (`lcu_ces_pad`, for the ideal operator
  `LCU`);
* `lcuI_ces_pad`: the same block for the released circuit `lcuI` run with the oracles `U_J` and
  `D` (through the released agreement `Sim.lcu_agrees`);
* `netTransfer_cascade`: for the Cayley boundary scalars of a step `v ≥ 0`, the transfer is the
  cascade transfer of the query proof (`SignedFactorSimulation.cascTransfer`).

The counts are those of the released circuit (`Sim.lcuI_counts`): exactly `N` private calls,
`2N` boundary calls and at most `2·2^r(2r+1) + 2L(8r+2) + N(4a+8m+7r+5)` elementary gates for
`L` labels on an `r`-bit label register; with `2^r = O(R)` and `N ≤ R` this is
`O(R(a + m + log(R+1)))`.
-/

set_option autoImplicit false

namespace GateOptimalPrecision

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim
open OptimalPrecision (ces)
open scoped InnerProduct BigOperators

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### The transfer of the chronological product -/

/-- The causal transfer of the chronological product of `2^m` boundary rotations with boundary
`J` and private operation `D` (`gate:eq:transfer`). -/
def netTransfer (c σ : ℝ) (J : P →L[ℂ] Vsp a P) (D : Vsp a P →L[ℂ] Vsp a P) (m : ℕ) :
    ℂ → P →L[ℂ] P :=
  SignedFactorSimulation.transfer (blkA c (2 ^ m)) (blkB c σ J D (2 ^ m)) (blkC c σ J (2 ^ m))
    (blkG c (1 - c) σ J D (2 ^ m))

/-- **Lemma `gate:lem:reuse`, block identity.** The clean block of the ideal operator `LCU` of the
released LCU circuit is `∑_ℓ (wt_ℓ/2) Ces_{n_ℓ}(F)` for the causal transfer `F` of the chronological
product with boundary `J = U_J ι₀`. -/
theorem lcu_ces {L : ℕ} (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (N : ℕ)
    (hn : ∀ ℓ, 0 < nOf ℓ ∧ nOf ℓ ≤ N) (hN : N ≤ cap r) (hr : 0 < r)
    (wt : Fin L → ℝ) (hwt : ∑ ℓ, |wt ℓ| = 2) (c σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1)
    (UJ D : Vsp a P →L[ℂ] Vsp a P) (hUJ : UJ ∘L UJ† = 1) :
    (io (a := a) (m := m) (r := r) (K := K) (P := P))† ∘L
        (LCU (K := K) (m := m) hL nOf wt c σ UJ D N ∘L io) =
      ∑ ℓ, ((wt ℓ / 2 : ℝ) : ℂ) • ces (netTransfer c σ (UJ ∘L iota0) D m) (nOf ℓ) := by
  rw [lcu_compression hL nOf N hn hN hr wt hwt c (1 - c) σ hunit rfl UJ D hUJ]
  rw [blkB_net, blkC_net, blkG_net _ _ _ UJ D hUJ]
  refine Finset.sum_congr rfl (fun ℓ _ => ?_)
  rw [SignedFactorSimulation.successfulBlock_eq_ces]
  rfl

/-- For the Cayley boundary scalars of a step `v ≥ 0`, the transfer of the chronological product
is the cascade transfer of the query proof. -/
theorem netTransfer_cascade {v : ℝ} (hv : 0 ≤ v) (J : P →L[ℂ] Vsp a P)
    (D : Vsp a P →L[ℂ] Vsp a P) (m : ℕ) :
    netTransfer (CayleyTransfer.c v) (CayleyTransfer.sigma v) J D m =
      SignedFactorSimulation.cascTransfer D J v (2 ^ m) := by
  obtain ⟨hκ, -⟩ := SignedFactorSimulation.cayley_scalars hv
  unfold netTransfer SignedFactorSimulation.cascTransfer SignedFactorSimulation.cascD
  rw [← hκ]
  rfl

/-! ### Padding a signed table to absolute mass two -/

/-- The padding weight `1 - A₀⁻¹ ∑_j |w_j|` of each of the two dummy branches. -/
def padMass {R : ℕ} (A₀ : ℝ) (w : Fin R → ℝ) : ℝ := 1 - (∑ j, |w j|) / A₀

/-- The scaled and padded weights: `2 w_j/A₀` on the ordinary labels, `±padMass` on the two
dummy labels. -/
def padWt {R : ℕ} (A₀ : ℝ) (w : Fin R → ℝ) : Fin (R + 2) → ℝ :=
  Fin.addCases (fun j : Fin R => 2 * w j / A₀)
    (fun i : Fin 2 => if i = 0 then padMass A₀ w else -padMass A₀ w)

/-- The reuse lengths: `n_j` on the ordinary labels, one on the dummy labels. -/
def padLen {R : ℕ} (len : Fin R → ℕ) : Fin (R + 2) → ℕ :=
  Fin.addCases len (fun _ : Fin 2 => 1)

theorem padMass_nonneg {R : ℕ} {A₀ : ℝ} (hA : 0 < A₀) (w : Fin R → ℝ)
    (hw : ∑ j, |w j| ≤ A₀) : 0 ≤ padMass A₀ w := by
  unfold padMass
  rw [sub_nonneg, div_le_one hA]
  exact hw

theorem padWt_mass {R : ℕ} {A₀ : ℝ} (hA : 0 < A₀) (w : Fin R → ℝ) (hw : ∑ j, |w j| ≤ A₀) :
    ∑ ℓ, |padWt A₀ w ℓ| = 2 := by
  have hp := padMass_nonneg hA w hw
  rw [Fin.sum_univ_add]
  simp only [padWt, Fin.addCases_left, Fin.addCases_right, Fin.sum_univ_two]
  simp only [Fin.isValue, if_true, show (1 : Fin 2) ≠ 0 from by decide, if_false, abs_neg,
    abs_of_nonneg hp]
  have h1 : ∑ j : Fin R, |2 * w j / A₀| = 2 * (∑ j, |w j|) / A₀ := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [abs_div, abs_mul, abs_of_pos hA, abs_two]
  rw [h1]
  unfold padMass
  field_simp
  ring

theorem padLen_spec {R N : ℕ} (len : Fin R → ℕ) (hlen : ∀ j, 0 < len j ∧ len j ≤ N)
    (hN : 1 ≤ N) (ℓ : Fin (R + 2)) : 0 < padLen len ℓ ∧ padLen len ℓ ≤ N := by
  refine Fin.addCases (fun j => ?_) (fun i => ?_) ℓ
  · simp only [padLen, Fin.addCases_left]; exact hlen j
  · simp only [padLen, Fin.addCases_right]; exact ⟨one_pos, hN⟩

/-- The padded signed sum is `A₀⁻¹ ∑_j w_j F(n_j)`: the two dummy branches cancel. -/
theorem pad_sum {R : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E] (A₀ : ℝ)
    (w : Fin R → ℝ) (len : Fin R → ℕ) (F : ℕ → E) :
    ∑ ℓ, ((padWt A₀ w ℓ / 2 : ℝ) : ℂ) • F (padLen len ℓ) =
      ((A₀⁻¹ : ℝ) : ℂ) • ∑ j, (w j : ℂ) • F (len j) := by
  rw [Fin.sum_univ_add]
  simp only [padWt, padLen, Fin.addCases_left, Fin.addCases_right, Fin.sum_univ_two]
  simp only [Fin.isValue, if_true, show (1 : Fin 2) ≠ 0 from by decide, if_false]
  rw [Finset.smul_sum]
  have h0 : ((padMass A₀ w / 2 : ℝ) : ℂ) • F 1 + ((-padMass A₀ w / 2 : ℝ) : ℂ) • F 1 = 0 := by
    rw [← add_smul]
    push_cast
    ring_nf
    exact zero_smul ℂ _
  rw [h0, add_zero]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_smul]
  congr 1
  push_cast
  field_simp

/-- **Lemma `gate:lem:reuse`.** For weights `w_1, …, w_R` with `∑ |w_j| ≤ A₀` and reuse lengths
`0 < n_j ≤ N`, the padded LCU circuit has the clean block `A₀⁻¹ ∑_j w_j Ces_{n_j}(F)`. -/
theorem lcu_ces_pad {R : ℕ} (hL : R + 2 ≤ 2 ^ r) {A₀ : ℝ} (hA : 0 < A₀) (w : Fin R → ℝ)
    (hw : ∑ j, |w j| ≤ A₀) (len : Fin R → ℕ) (N : ℕ) (hlen : ∀ j, 0 < len j ∧ len j ≤ N)
    (hN1 : 1 ≤ N) (hN : N ≤ cap r) (hr : 0 < r) (c σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1)
    (UJ D : Vsp a P →L[ℂ] Vsp a P) (hUJ : UJ ∘L UJ† = 1) :
    (io (a := a) (m := m) (r := r) (K := K) (P := P))† ∘L
        (LCU (K := K) (m := m) hL (padLen len) (padWt A₀ w) c σ UJ D N ∘L io) =
      ((A₀⁻¹ : ℝ) : ℂ) • ∑ j, (w j : ℂ) • ces (netTransfer c σ (UJ ∘L iota0) D m) (len j) := by
  rw [lcu_ces hL (padLen len) N (padLen_spec len hlen hN1) hN hr (padWt A₀ w)
    (padWt_mass hA w hw) c σ hunit UJ D hUJ]
  exact pad_sum A₀ w len _

/-- **Lemma `gate:lem:reuse` for the released circuit.** The padded released LCU circuit `lcuI`, run
with the oracles `U_J` and `D` on a register with `K ≥ a + m + 2r` work wires, has the clean block
`A₀⁻¹ ∑_j w_j Ces_{n_j}(F)`. -/
theorem lcuI_ces_pad {R : ℕ} (hL : R + 2 ≤ 2 ^ r) {A₀ : ℝ} (hA : 0 < A₀) (w : Fin R → ℝ)
    (hw : ∑ j, |w j| ≤ A₀) (len : Fin R → ℕ) (N : ℕ) (hlen : ∀ j, 0 < len j ∧ len j ≤ N)
    (hN1 : 1 ≤ N) (hN : N ≤ cap r) (hr : 0 < r) (hK : a + m + 2 * r ≤ K) (c σ : ℝ)
    (hunit : c ^ 2 + σ ^ 2 = 1) (UJ D : Vsp a P →L[ℂ] Vsp a P) (hUJ : UJ ∘L UJ† = 1) :
    (io (a := a) (m := m) (r := r) (K := K) (P := P))† ∘L
        (run (simSem UJ D) (lcuI (a := a) (m := m) (K := K) hL (padLen len) (padWt A₀ w) c σ N) ∘L
          io) =
      ((A₀⁻¹ : ℝ) : ℂ) • ∑ j, (w j : ℂ) • ces (netTransfer c σ (UJ ∘L iota0) D m) (len j) := by
  have hn : ∀ ℓ, padLen len ℓ < 2 ^ r := by
    intro ℓ
    have h := (padLen_spec len hlen hN1 ℓ).2
    have h2 : cap r < 2 ^ r := by
      unfold cap
      have := Nat.two_pow_pos r
      omega
    omega
  have hag := lcu_agrees (P := P) (a := a) (m := m) (K := K) UJ D hL (padLen len) (padWt A₀ w)
    c σ N hn hK
  have hio : run (simSem UJ D) (lcuI (a := a) (m := m) (K := K) hL (padLen len) (padWt A₀ w)
      c σ N) ∘L io = LCU (K := K) (m := m) hL (padLen len) (padWt A₀ w) c σ UJ D N ∘L io := by
    refine ContinuousLinearMap.ext (fun ψ => ?_)
    rw [comp_apply, comp_apply, io_apply]
    exact hag _ (supp_bas _ (fun w _ => rfl) ψ)
  rw [hio]
  exact lcu_ces_pad hL hA w hw len N hlen hN1 hN hr c σ hunit UJ D hUJ

end

end GateOptimalPrecision
