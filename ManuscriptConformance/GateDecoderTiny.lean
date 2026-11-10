import ManuscriptConformance.GateMainDecoder
import SparseHamiltonian.SparseValuePrecision
import SparseHamiltonian.HamiltonianStability

/-!
# Conformance: tiny decoded entries without their phase

The general-decoder endpoints `hs_thm_gates_decoder` and `gate_thm_main_decoder` assume a
reversible arithmetic of the local rotation parameters for the decoder `val` of the stored words
(`comp_rotArith`, and in `gate:thm:main` also `comp_signedArithV`, `comp_clipArithV`); through
`GeneralDecoder.RotWordArith.phi` it must approximate `arg (val w)` modulo `2π` for every word with
`val w ≠ 0`, however small `|val w|` is. Here the phase of a tiny entry is not needed.

**The thresholded decoder.** For a public test `small` on the stored words that only selects
entries of modulus at most `τ` (`∀ w, small w → |val w| ≤ τ`) and that does not separate an entry
from its conjugate (`val w' = conj (val w) → small w' = small w`, as for a test of `|val w|`),
`dropVal small val` is `0` on the selected words and `val` elsewhere. An arithmetic for the
thresholded decoder decides the test reversibly and returns the parameters of the zero entry on
the selected words: no phase word is asked there (`RotWordArith.phi` only on words with
`dropVal small val w ≠ 0`, `dropVal_ne_zero`). With `small = false` the thresholded decoder is
`val` (`dropVal_false`), so the old assumption remains sufficient.

**The bridge.** `QData.dropTiny` is the same sparse access (the same table, locators and oracles,
so the same primitive calls: `dropTiny_prims`) with the thresholded decoder and the matrix
without the selected entries. It keeps every promise of the instance (`dropTiny_isHermitian`,
`dropTiny_row`, `dropTiny_col`, `dropTiny_entry`), and its padded matrix differs from that of the
data by at most `s τ` in operator norm (`padMat_dropTiny_sub`: entrywise at most `τ`, at most `s`
nonzero differences in every row and column, on the original locator lists). The Hamiltonian
evolution then changes by at most `|t| s τ` (`fullOutputError_evolution_perturb`,
`HamiltonianStability.evolution_error_le`).

**The endpoints.** `hs_thm_gates_decoder_tiny` and `gate_thm_main_decoder_tiny`: the conclusions of
`hs_thm_gates_decoder` and `gate_thm_main_decoder` with the arithmetic assumptions for the
thresholded decoder, for the same circuit on the original data, with full-output error at most
`ε + |t| s τ` against the evolution of the original matrix. With `τ ≤ ε/(2 s |t|)` and the endpoint
run at `ε/2` this is `ε`. The test is part of the assumed arithmetic: its decision is computed on
the stored word by the circuit of `comp_rotArith` for the thresholded decoder, with the cost
bound of that assumption.

The threshold here is global, `s τ |t|` in the evolution; it is not the local per-rotation
tolerance of the manuscript's argument (`D(0)` used where `‖D(a) - D(0)‖` is within the local
tolerance), which would need the weaker phase premise inside `GateNative.ArithOK` itself.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

namespace SparseHamiltonian.GeneralSparseAccess

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary SparseHamiltonian.GeneralDecoder
open SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GatePointerEncoding (wordValue)
open SparseHamiltonian.SparseValuePrecision (operator_error_le_of_sparse_difference)
open scoped InnerProduct

/-! ### The thresholded decoder -/

section Threshold

variable {b : ℕ}

/-- **The thresholded decoder**: `0` on the words selected by `small`, `val` elsewhere. -/
def dropVal (small : Cfg (VW b) → Bool) (val : Cfg (VW b) → ℂ) : Cfg (VW b) → ℂ :=
  fun w => if small w = true then 0 else val w

theorem dropVal_false (val : Cfg (VW b) → ℂ) : dropVal (fun _ => false) val = val := by
  funext w
  simp [dropVal]

/-- A selected word decodes to zero, so no phase word is asked for it. -/
theorem dropVal_ne_zero {small : Cfg (VW b) → Bool} {val : Cfg (VW b) → ℂ} {w : Cfg (VW b)}
    (h : dropVal small val w ≠ 0) : small w = false ∧ dropVal small val w = val w := by
  unfold dropVal at h ⊢
  cases hs : small w
  · simp
  · simp [hs] at h

theorem norm_dropVal_le (small : Cfg (VW b) → Bool) (val : Cfg (VW b) → ℂ) (w : Cfg (VW b)) :
    ‖dropVal small val w‖ ≤ ‖val w‖ := by
  unfold dropVal
  split_ifs
  · rw [norm_zero]; exact norm_nonneg _
  · exact le_rfl

end Threshold

/-! ### The data with the thresholded decoder -/

namespace QData

variable {X : Type*} {N s k b : ℕ}

/-- **The sparse access with the thresholded decoder**: the same table, locators and oracles; the
decoder `dropVal small D.val` and the matrix without the selected entries. -/
def dropTiny (D : QData X N s k b) (small : Cfg (VW b) → Bool) : QData X N s k b where
  hN := D.hN
  hs := D.hs
  slots_pos := D.slots_pos
  scale := D.scale
  scale_pos := D.scale_pos
  matrix x i j := dropVal small D.val (D.table x (edgeW k (binW k i) (binW k j)))
  table := D.table
  val := dropVal small D.val
  val_bound z := (norm_dropVal_le small D.val z).trans (D.val_bound z)
  decoded _ _ _ := rfl
  rowloc := D.rowloc
  colloc := D.colloc
  row_injective := D.row_injective
  column_injective := D.column_injective
  row_covers x i j h := D.row_covers x i j (by
    intro h0
    apply h
    have h1 := D.decoded x i j
    rw [h0] at h1
    show dropVal small D.val _ = 0
    unfold dropVal
    split_ifs
    · rfl
    · exact h1)
  column_covers x i j h := D.column_covers x i j (by
    intro h0
    apply h
    have h1 := D.decoded x i j
    rw [h0] at h1
    show dropVal small D.val _ = 0
    unfold dropVal
    split_ifs
    · rfl
    · exact h1)
  rowOracle := D.rowOracle
  columnOracle := D.columnOracle
  row_unitary := D.row_unitary
  column_unitary := D.column_unitary
  row_valid := D.row_valid
  column_valid := D.column_valid

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The thresholded access has the same primitive oracles. -/
theorem dropTiny_prims (D : QData X N s k b) (small : Cfg (VW b) → Bool) (x : X) :
    (D.dropTiny small).prims (R := R) x = D.prims (R := R) x := by
  funext j
  cases j <;> rfl

theorem dropTiny_matrix (D : QData X N s k b) (small : Cfg (VW b) → Bool) (x : X) (i j : Fin N) :
    (D.dropTiny small).matrix x i j =
      if small (D.table x (edgeW k (binW k i) (binW k j))) = true then 0 else D.matrix x i j := by
  show dropVal small D.val _ = _
  unfold dropVal
  rw [D.decoded x i j]

theorem norm_dropTiny_le (D : QData X N s k b) (small : Cfg (VW b) → Bool) (x : X) (i j : Fin N) :
    ‖(D.dropTiny small).matrix x i j‖ ≤ ‖D.matrix x i j‖ := by
  rw [dropTiny_matrix]
  split_ifs
  · rw [norm_zero]; exact norm_nonneg _
  · exact le_rfl

/-- The thresholded matrix of a Hermitian instance is Hermitian when the test does not separate an
entry from its conjugate. -/
theorem dropTiny_isHermitian (D : QData X N s k b) {small : Cfg (VW b) → Bool}
    (hsym : ∀ w w', D.val w' = star (D.val w) → small w' = small w) (x : X)
    (hH : (D.matrix x).IsHermitian) : ((D.dropTiny small).matrix x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have hji : D.val (D.table x (edgeW k (binW k j) (binW k i))) =
      star (D.val (D.table x (edgeW k (binW k i) (binW k j)))) := by
    rw [D.decoded, D.decoded, hH.apply j i]
  have hs := hsym _ _ hji
  rw [dropTiny_matrix, dropTiny_matrix, hs]
  split_ifs
  · exact star_zero _
  · exact hH.apply i j

theorem dropTiny_row (D : QData X N s k b) (small : Cfg (VW b) → Bool) (x : X) {η : ℝ}
    (h : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (i : Fin N) :
    ∑ j, ‖(D.dropTiny small).matrix x i j‖ ^ 2 ≤ η ^ 2 :=
  (Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _)
    (norm_dropTiny_le D small x i j) 2).trans (h i)

theorem dropTiny_col (D : QData X N s k b) (small : Cfg (VW b) → Bool) (x : X) {η : ℝ}
    (h : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (j : Fin N) :
    ∑ i, ‖(D.dropTiny small).matrix x i j‖ ^ 2 ≤ η ^ 2 :=
  (Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _)
    (norm_dropTiny_le D small x i j) 2).trans (h j)

theorem dropTiny_entry (D : QData X N s k b) (small : Cfg (VW b) → Bool) (x : X) {μ : ℝ}
    (h : ∀ i j, ‖D.matrix x i j‖ ≤ μ) (i j : Fin N) : ‖(D.dropTiny small).matrix x i j‖ ≤ μ :=
  (norm_dropTiny_le D small x i j).trans (h i j)

/-- The padded matrix of a Hermitian instance is Hermitian. -/
theorem padMat_isHermitian (D : QData X N s k b) (x : X) (hH : (D.matrix x).IsHermitian) :
    (D.padMat x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro y y'
  unfold QData.padMat
  by_cases hv : wordValue y < N ∧ wordValue y' < N
  · rw [dif_pos ⟨hv.2, hv.1⟩, dif_pos hv]
    exact hH.apply _ _
  · rw [dif_neg (fun h' => hv ⟨h'.2, h'.1⟩), dif_neg hv, star_zero]

/-- The entries of the difference of the padded matrices: the selected entries of the data. -/
theorem padMat_dropTiny_sub_apply (D : QData X N s k b) (small : Cfg (VW b) → Bool) (x : X)
    (y y' : Cfg (Fin k)) :
    D.padMat x y y' - (D.dropTiny small).padMat x y y' =
      if h : wordValue y < N ∧ wordValue y' < N then
        (if small (D.table x (edgeW k (binW k (⟨wordValue y, h.1⟩ : Fin N))
          (binW k (⟨wordValue y', h.2⟩ : Fin N)))) = true then
          D.matrix x ⟨wordValue y, h.1⟩ ⟨wordValue y', h.2⟩ else 0) else 0 := by
  unfold QData.padMat
  split_ifs with hv hs
  · rw [dropTiny_matrix, if_pos hs, sub_zero]
  · rw [dropTiny_matrix, if_neg hs, sub_self]
  · rw [sub_self]

/-- **The selected entries are at most `τ`**. -/
theorem norm_padMat_dropTiny_sub_le (D : QData X N s k b) {small : Cfg (VW b) → Bool} {τ : ℝ}
    (hτ : 0 ≤ τ) (hsm : ∀ w, small w = true → ‖D.val w‖ ≤ τ) (x : X) (y y' : Cfg (Fin k)) :
    ‖D.padMat x y y' - (D.dropTiny small).padMat x y y'‖ ≤ τ := by
  rw [padMat_dropTiny_sub_apply]
  split_ifs with hv hs
  · rw [← D.decoded]
    exact hsm _ hs
  · rw [norm_zero]; exact hτ
  · rw [norm_zero]; exact hτ

/-- A nonzero difference is on the locator list of its row and of its column. -/
theorem padMat_dropTiny_sub_ne_zero (D : QData X N s k b) (small : Cfg (VW b) → Bool) (x : X)
    {y y' : Cfg (Fin k)} (hne : D.padMat x y y' - (D.dropTiny small).padMat x y y' ≠ 0) :
    ∃ h : wordValue y < N ∧ wordValue y' < N,
      (∃ a, y' = binW k (D.rowloc x ⟨wordValue y, h.1⟩ a)) ∧
      (∃ a, y = binW k (D.colloc x ⟨wordValue y', h.2⟩ a)) := by
  rw [padMat_dropTiny_sub_apply] at hne
  by_cases hv : wordValue y < N ∧ wordValue y' < N
  · refine ⟨hv, ?_, ?_⟩
    · rw [dif_pos hv] at hne
      have hH : D.matrix x ⟨wordValue y, hv.1⟩ ⟨wordValue y', hv.2⟩ ≠ 0 := by
        intro h0; apply hne; split_ifs <;> simp [h0]
      obtain ⟨a, ha⟩ := D.row_covers x _ _ hH
      refine ⟨a, ?_⟩
      rw [ha]
      exact (binW_wordValue y').symm
    · rw [dif_pos hv] at hne
      have hH : D.matrix x ⟨wordValue y, hv.1⟩ ⟨wordValue y', hv.2⟩ ≠ 0 := by
        intro h0; apply hne; split_ifs <;> simp [h0]
      obtain ⟨a, ha⟩ := D.column_covers x _ _ hH
      refine ⟨a, ?_⟩
      rw [ha]
      exact (binW_wordValue y).symm
  · rw [dif_neg hv] at hne
    exact absurd rfl hne

/-- **The thresholded padded matrix is within `s τ` of the padded matrix**, on the original
locator lists. -/
theorem padMat_dropTiny_sub (D : QData X N s k b) {small : Cfg (VW b) → Bool} {τ : ℝ}
    (hτ : 0 ≤ τ) (hsm : ∀ w, small w = true → ‖D.val w‖ ≤ τ) (x : X) :
    ‖SparseStateOverlap.matrixOperator (D.padMat x) -
        SparseStateOverlap.matrixOperator ((D.dropTiny small).padMat x)‖ ≤ (s : ℝ) * τ := by
  classical
  apply operator_error_le_of_sparse_difference _ _ s τ hτ
  · intro y
    by_cases hy : wordValue y < N
    · calc (nonzeroPositions fun y' => D.padMat x y y' - (D.dropTiny small).padMat x y y').card
          ≤ ((Finset.univ : Finset (Fin s)).image
              fun a => binW k (D.rowloc x ⟨wordValue y, hy⟩ a)).card := by
            apply Finset.card_le_card
            intro y' hy'
            simp only [nonzeroPositions, Finset.mem_filter, Finset.mem_univ, true_and] at hy'
            obtain ⟨h, ⟨a, ha⟩, -⟩ := padMat_dropTiny_sub_ne_zero D small x hy'
            exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha.symm⟩
        _ ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_image_le
        _ = s := by rw [Finset.card_univ, Fintype.card_fin]
    · have h0 : nonzeroPositions (fun y' => D.padMat x y y' - (D.dropTiny small).padMat x y y') =
          ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro y' hy'
        simp only [nonzeroPositions, Finset.mem_filter, Finset.mem_univ, true_and] at hy'
        obtain ⟨h, -, -⟩ := padMat_dropTiny_sub_ne_zero D small x hy'
        exact hy h.1
      rw [h0, Finset.card_empty]
      exact Nat.zero_le _
  · intro y'
    by_cases hy' : wordValue y' < N
    · calc (nonzeroPositions fun y => D.padMat x y y' - (D.dropTiny small).padMat x y y').card
          ≤ ((Finset.univ : Finset (Fin s)).image
              fun a => binW k (D.colloc x ⟨wordValue y', hy'⟩ a)).card := by
            apply Finset.card_le_card
            intro y hy
            simp only [nonzeroPositions, Finset.mem_filter, Finset.mem_univ, true_and] at hy
            obtain ⟨h, -, ⟨a, ha⟩⟩ := padMat_dropTiny_sub_ne_zero D small x hy
            exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha.symm⟩
        _ ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_image_le
        _ = s := by rw [Finset.card_univ, Fintype.card_fin]
    · have h0 : nonzeroPositions (fun y => D.padMat x y y' - (D.dropTiny small).padMat x y y') =
          ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro y hy
        simp only [nonzeroPositions, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        obtain ⟨h, -, -⟩ := padMat_dropTiny_sub_ne_zero D small x hy
        exact hy' h.2
      rw [h0, Finset.card_empty]
      exact Nat.zero_le _
  · exact norm_padMat_dropTiny_sub_le D hτ hsm x

end QData

end

end SparseHamiltonian.GeneralSparseAccess

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateSynth SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget
  SparseHamiltonian.GeneralSparseAccess SparseHamiltonian.GeneralDecoder
open GateOptimalPrecision (FactorArithOK)
open SparseHamiltonian.SparseValuePrecision (matrixOperator_star_eq)
open scoped InnerProduct

universe u w

/-! ### The evolution of the original matrix -/

section Perturb

variable {K P : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [NormedAddCommGroup P]
  [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **A full-output error against a nearby evolution** gives one against the evolution, with the
sharp time-linear cost. -/
theorem fullOutputError_evolution_perturb {A : K →L[ℂ] K} {J : P →L[ℂ] K} (hJ : ‖J‖ ≤ 1)
    {G G' : P →L[ℂ] P} (hG : star G = G) (hG' : star G' = G') {t ε δ : ℝ} (hδ : ‖G - G'‖ ≤ δ)
    (h : FullOutputError A J (NormedSpace.exp ((-Complex.I * (t : ℂ)) • G')) ε) :
    FullOutputError A J (NormedSpace.exp ((-Complex.I * (t : ℂ)) • G)) (ε + |t| * δ) := by
  intro ψ hψ
  have hE := HamiltonianStability.evolution_error_le G' G t hG' hG
  have hGG : ‖G' - G‖ ≤ δ := by rwa [norm_sub_rev]
  have h2 : ‖J ((NormedSpace.exp ((-Complex.I * (t : ℂ)) • G')) ψ) -
      J ((NormedSpace.exp ((-Complex.I * (t : ℂ)) • G)) ψ)‖ ≤ |t| * δ := by
    have e : J ((NormedSpace.exp ((-Complex.I * (t : ℂ)) • G')) ψ) -
        J ((NormedSpace.exp ((-Complex.I * (t : ℂ)) • G)) ψ) =
        J ((NormedSpace.exp ((-Complex.I * (t : ℂ)) • G') -
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • G)) ψ) := by
      rw [← map_sub]; rfl
    rw [e]
    calc _ ≤ ‖J‖ * ‖(NormedSpace.exp ((-Complex.I * (t : ℂ)) • G') -
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • G)) ψ‖ := le_opNorm _ _
      _ ≤ 1 * (‖NormedSpace.exp ((-Complex.I * (t : ℂ)) • G') -
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • G)‖ * ‖ψ‖) :=
          mul_le_mul hJ (le_opNorm _ _) (norm_nonneg _) zero_le_one
      _ ≤ |t| * δ := by
          rw [hψ, mul_one, one_mul]
          exact hE.trans (mul_le_mul_of_nonneg_left hGG (abs_nonneg t))
  calc ‖A (J ψ) - J ((NormedSpace.exp ((-Complex.I * (t : ℂ)) • G)) ψ)‖
      ≤ ‖A (J ψ) - J ((NormedSpace.exp ((-Complex.I * (t : ℂ)) • G')) ψ)‖ +
        ‖J ((NormedSpace.exp ((-Complex.I * (t : ℂ)) • G')) ψ) -
          J ((NormedSpace.exp ((-Complex.I * (t : ℂ)) • G)) ψ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε + |t| * δ := add_le_add (h ψ hψ) h2

end Perturb

set_option maxHeartbeats 1600000 in
/-- **The lifted evolutions of the data and of the thresholded data**: the full-output error
against the thresholded evolution gives that against the evolution of the data, with the cost
`|t| s τ`. -/
theorem fullOutputError_dropTiny {X : Type*} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b)
    {small : Cfg (VW b) → Bool} {τ : ℝ} (hτ : 0 ≤ τ) (hsm : ∀ w, small w = true → ‖D.val w‖ ≤ τ)
    (hsym : ∀ w w', D.val w' = star (D.val w) → small w' = small w)
    {R W : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R] [Fintype W]
    [DecidableEq W] (sys : Fin k ↪ W) (A : Reg W R →L[ℂ] Reg W R) (x : X)
    (hH : (D.matrix x).IsHermitian) (t ε : ℝ)
    (h : FullOutputError A (cleanAlong sys)
      (NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl (Cfg (Fin k)))
        (SparseStateOverlap.matrixOperator ((D.dropTiny small).padMat x)))) ε) :
    FullOutputError A (cleanAlong sys)
      (NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl (Cfg (Fin k)))
        (SparseStateOverlap.matrixOperator (D.padMat x)))) (ε + |t| * ((s : ℝ) * τ)) := by
  have hH' := D.dropTiny_isHermitian hsym x hH
  have hP := D.padMat_isHermitian x hH
  have hP' := (D.dropTiny small).padMat_isHermitian x hH'
  have hstar : ∀ M : Matrix (Cfg (Fin k)) (Cfg (Fin k)) ℂ, M.IsHermitian →
      star (qlift (R := R) (Equiv.refl (Cfg (Fin k))) (SparseStateOverlap.matrixOperator M)) =
        qlift (R := R) (Equiv.refl (Cfg (Fin k))) (SparseStateOverlap.matrixOperator M) := by
    intro M hM
    rw [star_eq_adjoint, ← qlift_adjoint, ← star_eq_adjoint, matrixOperator_star_eq M hM]
  have hsub : qlift (R := R) (Equiv.refl (Cfg (Fin k)))
        (SparseStateOverlap.matrixOperator (D.padMat x)) -
      qlift (R := R) (Equiv.refl (Cfg (Fin k)))
        (SparseStateOverlap.matrixOperator ((D.dropTiny small).padMat x)) =
      qlift (R := R) (Equiv.refl (Cfg (Fin k)))
        (SparseStateOverlap.matrixOperator (D.padMat x) -
          SparseStateOverlap.matrixOperator ((D.dropTiny small).padMat x)) :=
    (map_sub (qliftHom (R := R) (Equiv.refl (Cfg (Fin k)))) _ _).symm
  have hδ : ‖qlift (R := R) (Equiv.refl (Cfg (Fin k)))
        (SparseStateOverlap.matrixOperator (D.padMat x)) -
      qlift (R := R) (Equiv.refl (Cfg (Fin k)))
        (SparseStateOverlap.matrixOperator ((D.dropTiny small).padMat x))‖ ≤ (s : ℝ) * τ := by
    rw [hsub]
    exact (norm_qlift_le _ _).trans (D.padMat_dropTiny_sub hτ hsm x)
  intro ψ hψ
  have hE := HamiltonianStability.evolution_error_le _ _ t (hstar _ hP) (hstar _ hP')
  have h1 := h ψ hψ
  set G := qlift (R := R) (Equiv.refl (Cfg (Fin k)))
    (SparseStateOverlap.matrixOperator (D.padMat x)) with hG
  set G' := qlift (R := R) (Equiv.refl (Cfg (Fin k)))
    (SparseStateOverlap.matrixOperator ((D.dropTiny small).padMat x)) with hG'
  set E := NormedSpace.exp ((-Complex.I * (t : ℂ)) • G) with hEdef
  set E' := NormedSpace.exp ((-Complex.I * (t : ℂ)) • G') with hE'def
  have h2 : ‖cleanAlong (R := R) sys (E' ψ) - cleanAlong sys (E ψ)‖ ≤ |t| * ((s : ℝ) * τ) := by
    rw [← map_sub, norm_cleanAlong, norm_sub_rev]
    calc ‖E ψ - E' ψ‖ = ‖(E - E') ψ‖ := rfl
      _ ≤ ‖E - E'‖ * ‖ψ‖ := le_opNorm _ _
      _ ≤ |t| * ((s : ℝ) * τ) := by
          rw [hψ, mul_one]
          exact hE.trans (mul_le_mul_of_nonneg_left hδ (abs_nonneg t))
  calc ‖A (cleanAlong sys ψ) - cleanAlong sys (E ψ)‖
      ≤ ‖A (cleanAlong sys ψ) - cleanAlong sys (E' ψ)‖ +
        ‖cleanAlong (R := R) sys (E' ψ) - cleanAlong sys (E ψ)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε + |t| * ((s : ℝ) * τ) := add_le_add h1 h2

/-! ### The endpoints -/

set_option maxHeartbeats 8000000 in
/-- **Theorem `hs:thm:gates` for general decoders, without the phase of tiny entries.** As
`hs_thm_gates_decoder`, with the arithmetic assumption `comp_rotArith` for the thresholded decoder
`dropVal small val` instead of `val`: no phase word is asked for a word selected by the public test
`small`, which only selects entries of modulus at most `τ` and does not separate an entry from its
conjugate. The same circuit, on the original data, has full-output error at most `ε + |t| s τ`
against the evolution of the original matrix. -/
theorem hs_thm_gates_decoder_tiny (cA : ℝ) (dA : ℕ) (hcA : 0 ≤ cA) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (Kd : ℕ) {𝒢 : Set Kind}
    {X₁ X₂ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ}
    (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b) (bd : ℕ)
        (η t ε : ℝ) (small : Cfg (VW b) → Bool) (τ : ℝ),
        2 ^ k < 2 * N → b ≤ bd → 0 ≤ τ →
        (∀ w, small w = true → ‖D.val w‖ ≤ τ) →
        (∀ w w', D.val w' = star (D.val w) → small w' = small w) →
        comp_rotArith cA dA bd k b (dropVal small D.val) (1 / η) (Real.sqrt (2 * s) / η) →
        0 < η → 0 < ε → ε ≤ 1 / 2 →
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (sys : Fin k ↪ W)
          (Cc : List (NInstr W (PY k b) NativeSparseBlockEncoding.Query)),
          (∀ i ∈ Cc, i.Valid) ∧ (∀ g, NInstr.gate g ∈ Cc → GateOf 𝒢 g) ∧
          (nCallsN (fun _ => true) Cc : ℝ) ≤ 6635520 * mainBound s (η * |t|) ε ∧
          (nGatesN Cc : ℝ) ≤ C * mainBound s (η * |t|) ε *
            (bitH bd N (mainBound s (η * |t|) ε) ε + 1) ^ K ∧
          ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
            (x : X),
            (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            FullOutputError (nrun (D.prims (R := R) x) Cc) (cleanAlong sys)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) (Equiv.refl _) (SparseStateOverlap.matrixOperator (D.padMat x))))
              (ε + |t| * ((s : ℝ) * τ)) := by
  obtain ⟨C, K, hC, h⟩ := hs_thm_gates_decoder.{u, w} cA dA hcA hc₀ hc₁ Kd
    ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  refine ⟨C, K, hC, ?_⟩
  intro X N s k b D bd η t ε small τ hk hbd hτ hsm hsym hdec hη hε hε2
  obtain ⟨W, hW, hWd, sys, Cc, hv, hg, hcalls, hgates, herr⟩ :=
    h (D.dropTiny small) bd η t ε hk hbd hdec hη hε hε2
  refine ⟨W, hW, hWd, sys, Cc, hv, hg, hcalls, hgates, ?_⟩
  intro R _ _ _ x hH hrow hcol
  have h' := herr (R := R) x (D.dropTiny_isHermitian hsym x hH) (D.dropTiny_row small x hrow)
    (D.dropTiny_col small x hcol)
  rw [GeneralSparseAccess.QData.dropTiny_prims] at h'
  exact fullOutputError_dropTiny D hτ hsm hsym sys _ x hH t ε h'

set_option maxHeartbeats 8000000 in
/-- **Theorem `gate:thm:main` for general decoders, without the phase of tiny entries.** As
`gate_thm_main_decoder`, with the three arithmetic assumptions (`comp_rotArith`,
`comp_signedArithV`, `comp_clipArithV`) for the thresholded decoder `dropVal small val`: no phase
word is asked for a word selected by the public test `small`, which only selects entries of
modulus at most `τ` and does not separate an entry from its conjugate. The same circuit, on the
original data, has full-output error at most `ε + |t| s τ` against the evolution of the original
matrix. -/
theorem gate_thm_main_decoder_tiny (cA : ℝ) (dA : ℕ) (hcA : 0 ≤ cA) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (Kd : ℕ) {𝒢 : Set Kind} {X₁ X₂ : Type} [Fintype X₁] [DecidableEq X₁]
    [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ}
    (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b) (bd : ℕ)
        (η μ t ε : ℝ) (small : Cfg (VW b) → Bool) (τ : ℝ),
        2 ^ k < 2 * N → b ≤ bd → 0 ≤ τ →
        (∀ w, small w = true → ‖D.val w‖ ≤ τ) →
        (∀ w w', D.val w' = star (D.val w) → small w' = small w) →
        comp_rotArith cA dA bd k b (dropVal small D.val) (1 / η) (Real.sqrt (2 * s) / η) →
        comp_signedArithV cA dA bd k b (dropVal small D.val) μ →
        comp_clipArithV cA dA bd k b (dropVal small D.val) μ (genClipBeta η μ t ε)
          (genClipScale s η μ t ε) →
        μ ≤ η → η ≤ Real.sqrt s * μ → 1 ≤ η ^ 2 * |t| / μ → 0 < ε → ε ≤ 1 / 64 →
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (sys : Fin k ↪ W)
          (Cc : List (NInstr W (PY k b) NativeSparseBlockEncoding.Query)),
          (∀ i ∈ Cc, i.Valid) ∧ (∀ g, NInstr.gate g ∈ Cc → GateOf 𝒢 g) ∧
          (nCallsN (fun _ => true) Cc : ℝ) ≤ 288 * 10 ^ 12 * twoNormBound s η μ t ε ∧
          (nGatesN Cc : ℝ) ≤ C * twoNormBound s η μ t ε *
            (gateWord bd N s (twoNormBound s η μ t ε) ε + 1) ^ K ∧
          (Fintype.card W : ℝ) ≤
            k + C * (gateWord bd N s (twoNormBound s η μ t ε) ε + 1) ^ K ∧
          ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
            [FiniteDimensional ℂ R] (x : X),
            (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) → (∀ i j, ‖D.matrix x i j‖ ≤ μ) →
            FullOutputError (nrun (D.prims (R := R) x) Cc) (cleanAlong sys)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) (Equiv.refl _) (SparseStateOverlap.matrixOperator (D.padMat x))))
              (ε + |t| * ((s : ℝ) * τ)) := by
  obtain ⟨C, K, hC, h⟩ := gate_thm_main_decoder.{u, w} cA dA hcA hc₀ hc₁ Kd
    ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  refine ⟨C, K, hC, ?_⟩
  intro X N s k b D bd η μ t ε small τ hk hbd hτ hsm hsym hdec hsg hcl hμη hημ hτμ hε hε2
  obtain ⟨W, hW, hWd, sys, Cc, hv, hg, hcalls, hgates, hcard, herr⟩ :=
    h (D.dropTiny small) bd η μ t ε hk hbd hdec hsg hcl hμη hημ hτμ hε hε2
  refine ⟨W, hW, hWd, sys, Cc, hv, hg, hcalls, hgates, hcard, ?_⟩
  intro R _ _ _ _ x hH hrow hcol hent
  have h' := herr (R := R) x (D.dropTiny_isHermitian hsym x hH) (D.dropTiny_row small x hrow)
    (D.dropTiny_col small x hcol) (D.dropTiny_entry small x hent)
  rw [GeneralSparseAccess.QData.dropTiny_prims] at h'
  exact fullOutputError_dropTiny D hτ hsm hsym sys _ x hH t ε h'

/-- **The phase premise on a tiny word is vacuous for the thresholded decoder** (acceptance check):
for a word selected by the test, whatever its phase, the thresholded decoder is zero, so
`RotWordArith.phi` asks nothing there. -/
theorem dropVal_phi_vacuous {b : ℕ} (small : Cfg (VW b) → Bool) (val : Cfg (VW b) → ℂ)
    (κ : ℝ) {w : Cfg (VW b)} (hw : small w = true) :
    ¬ ((κ : ℂ) * dropVal small val w ≠ 0) := by
  simp [dropVal, hw]

end

end ManuscriptConformance
