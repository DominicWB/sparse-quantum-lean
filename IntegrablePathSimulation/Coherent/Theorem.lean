import IntegrablePathSimulation.Propagator.Duhamel
import TimeDependentExtensions.Coherent.Theorem

set_option autoImplicit false

/-!
# Coherent start times and durations for integrable Hermitian paths

The paragraph "Regularity and coherent parameters" after the proof of Theorem `hs:thm:time`
of the manuscript (lines 1618-1632): for an integrable Hermitian path it suffices to have a
certified bound on the integrated sample errors, all uses of regularity are confined to this
classical certificate, and the proof also permits coherent selection of known durations and
start times with one schedule fixed for the largest duration.

`coherent_windows` states the coherent selection of windows `[t_{a_i}, t_{b_i}]` (start times
and durations at mesh points) of the released `TimeDependentExtensions.Coherent.coherent_windows`
for one path `H` on `[0, T]` that is Hermitian at almost every time and interval integrable,
with the same rescaling `γ`, oracle family, clean encoding, slot conditions
`8 s η T ≤ N`, `9 (√(2s) η T)³ ≤ ε N²`, `3 M √s η T ≤ ε N`, certificate `≤ ε / 3` and query
count `663552 · shape (2s) (η T) (log (6/ε))`. The branch evolutions `V_i` are integral-sense
solutions from the identity at `t_{a_i}` on `[t_{a_i}, t_{b_i}]`
(`Propagator.SolvesIntegralOn`). The proof is the released one with the classical window
estimate replaced by `Propagator.SolvesIntegralOn.window_error`.
-/

namespace IntegrablePathSimulation.Coherent

noncomputable section

open SparseHamiltonian SparseHamiltonian.TimeDependent ContinuousLinearMap OracleCircuit
open NativeSparseBlockEncoding MeasureTheory Set
open TimeDependentExtensions (IsMesh pieceOf)
open IntegrablePathSimulation.Propagator (SolvesIntegralOn)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s M : ℕ}

set_option maxRecDepth 8192 in
/-- **Coherent start times and durations at mesh points, for integrable paths.** One rescaling
`γ`, hence one oracle family and one clean encoding, serves every public table of windows
`a_i ≤ b_i ≤ M`: for each table there is a program such that, for every instance, every path
that is Hermitian at almost every time of `[0, T]` and interval integrable on `[0, T]`, whose
integrated sample errors are at most `ε / 3`, and every family `V_i` of integral-sense
solutions of that path on `[t_{a_i}, t_{b_i}]` from the identity at `t_{a_i}`, the full output
is within `ε` of `∑_i |i⟩⟨i| ⊗ V_i(t_{b_i})`. The slot conditions are `8 s η T ≤ N`,
`9 (√(2s) η T)³ ≤ ε N²` and `3 M √s η T ≤ ε N`. -/
theorem coherent_windows (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) (b0 : ι × Fin M) (η T ε : ℝ) (hη : 0 < η) (hT : 0 < T) (hε : 0 < ε)
    (hεOne : ε ≤ 1) (hmesh : IsMesh t M T)
    (hH : ∀ y, (D.matrix y).IsHermitian)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hClock : 8 * s * (η * T) ≤ N)
    (hCayley : 9 * (Real.sqrt (2 * (s : ℝ)) * (η * T)) ^ 3 ≤ ε * (N : ℝ) ^ 2)
    (hRefine : 3 * M * (Real.sqrt s * (η * T)) ≤ ε * N) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (2 * (s : ℝ)) ∧
      ∀ a b : ι → ℕ, (∀ i, a i ≤ b i) → (∀ i, b i ≤ M) →
      ∃ p : MultiOracleCircuit.Program
          (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ι) D N γ η T (ε / 3)),
        (p.count : ℝ) ≤ 663552 * ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (η * T)
          (ImprovedPrecisionBudget.targetLog (ε / 3)) ∧
        (TimeDependentExtensions.MeshSelect.alignedInput D hM (pieceOf t T N hM) b0 N γ η T
            (ε / 3))† ∘L
          TimeDependentExtensions.MeshSelect.alignedInput D hM (pieceOf t T N hM) b0 N γ η T
            (ε / 3) = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ (H : ℝ → Matrix n n ℂ) (V : ι → ℝ → EuclideanSpace ℂ n →L[ℂ]
              EuclideanSpace ℂ n),
            (∀ᵐ u, u ∈ Icc 0 T → (H u).IsHermitian) →
            IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (H u)) volume 0 T →
            ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
              ‖SparseStateOverlap.matrixOperator (H u) -
                SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 3 →
            (∀ i, V i (t (a i)) = 1) →
            (∀ i, SolvesIntegralOn (fun u => SparseStateOverlap.matrixOperator (H u)) (V i)
              (t (a i)) (t (b i))) →
            ‖p.eval x ∘L TimeDependentExtensions.MeshSelect.alignedInput D hM
                  (pieceOf t T N hM) b0 N γ η T (ε / 3) -
              TimeDependentExtensions.MeshSelect.alignedInput D hM (pieceOf t T N hM) b0 N γ η T
                  (ε / 3) ∘L
                WeightedClock.diagonal (fun i => V i (t (b i)))‖ ≤ ε := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨γ, hγ, hγOne, hWidth, hAll⟩ := TimeDependentExtensions.Coherent.coherent_select D hM
    (pieceOf t T N hM) hN b0 η T (ε / 3) hη hT hε3 (by linarith) hH hrow hcol hClock
    (by nlinarith)
  refine ⟨γ, hγ, hγOne, hWidth, fun a b hab hbM => ?_⟩
  have hu : ∀ i r, 0 ≤ TimeDependentExtensions.Coherent.windows (M := M) T a b i r :=
    fun i r => by unfold TimeDependentExtensions.Coherent.windows; split_ifs <;> linarith
  have huT : ∀ i r, TimeDependentExtensions.Coherent.windows (M := M) T a b i r ≤ T :=
    fun i r => by unfold TimeDependentExtensions.Coherent.windows; split_ifs <;> linarith
  obtain ⟨p, hCount, hIn, hAct⟩ := hAll (TimeDependentExtensions.Coherent.windows T a b) hu huT
  refine ⟨p, hCount, hIn, fun x => ⟨(hAct x).1, ?_⟩⟩
  intro H V hPath hInt hCert hV0 hV
  set ι' := TimeDependentExtensions.MeshSelect.alignedInput D hM (pieceOf t T N hM) b0 N γ η T
    (ε / 3)
  have hιn : ‖ι'‖ ≤ 1 := SparseMatrixNorm.norm_le_one_of_adjoint_comp _ hIn
  -- The operator path and the per-branch distance of the selected product from `V_i`.
  let Hop : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun u =>
    SparseStateOverlap.matrixOperator (H u)
  have hHop : ∀ᵐ u, u ∈ Icc 0 T → star (Hop u) = Hop u := by
    filter_upwards [hPath] with u hu hmem
    exact SparseValuePrecision.matrixOperator_star_eq _ (hu hmem)
  let A : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
    SparseStateOverlap.matrixOperator (D.matrix (x, Sampled.sampleIndex hM r))
  have hA : ∀ r, star (A r) = A r := fun r =>
    SparseValuePrecision.matrixOperator_star_eq _ (hH _)
  have hΛ : ∀ r, ‖A r‖ ≤ Real.sqrt s * η := fun r =>
    TimeDependentExtensions.Hamiltonian.sample_norm_le D η hη _ (hH _) (hrow _) (hcol _)
  have hbranch : ∀ i, ‖(evolution (fun k => NormedSpace.exp
      ((-Complex.I * ((TimeDependentExtensions.Coherent.windows T a b i (pieceOf t T N hM k) / N
          : ℝ) : ℂ)) •
        SparseStateOverlap.matrixOperator (D.matrix (x, pieceOf t T N hM k)))) N) -
      V i (t (b i))‖ ≤ ε / 3 + ε / 3 := by
    intro i
    -- Group the slots by mesh interval.
    let w' : ℕ → ℝ := fun r => if a i ≤ r ∧ r < b i then T else 0
    let f : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
      NormedSpace.exp ((-Complex.I * ((w' r / N : ℝ) : ℂ)) • A r)
    have hslot : evolution (fun k => NormedSpace.exp
        ((-Complex.I * ((TimeDependentExtensions.Coherent.windows T a b i (pieceOf t T N hM k) /
          N : ℝ) : ℂ)) •
          SparseStateOverlap.matrixOperator (D.matrix (x, pieceOf t T N hM k)))) N =
        evolution (fun k => f (TimeDependentExtensions.slotPiece t T N M k)) N := by
      congr 1
      funext k
      have hk : Sampled.sampleIndex hM (TimeDependentExtensions.slotPiece t T N M k) =
          pieceOf t T N hM k :=
        TimeDependentExtensions.Hamiltonian.sampleIndex_of_lt hM
          (TimeDependentExtensions.slotPiece_lt hM k)
      simp only [f, A, hk]
      rfl
    let ℓ : ℕ → ℝ := fun r => (TimeDependentExtensions.blockLength t T N r : ℝ) * (T / N)
    let G : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
      NormedSpace.exp ((-Complex.I * ((ℓ r : ℝ) : ℂ)) • A r)
    have hgroup : evolution (fun k => f (TimeDependentExtensions.slotPiece t T N M k)) N =
        TimeDependent.orderedProduct G (a i) (b i - a i) := by
      rw [TimeDependentExtensions.evolution_slotPiece f hmesh hT]
      have hf : ∀ r, f r ^ TimeDependentExtensions.blockLength t T N r =
          if a i ≤ r ∧ r < b i then G r else 1 := by
        intro r
        show NormedSpace.exp ((-Complex.I * ((w' r / N : ℝ) : ℂ)) • A r) ^
          TimeDependentExtensions.blockLength t T N r = _
        rw [TimeDependentExtensions.exp_pow]
        by_cases hr : a i ≤ r ∧ r < b i
        · rw [if_pos hr]
          show NormedSpace.exp _ = NormedSpace.exp ((-Complex.I * ((ℓ r : ℝ) : ℂ)) • A r)
          congr 4
          simp only [w', if_pos hr, ℓ]
        · rw [if_neg hr]
          simp only [w', if_neg hr, zero_div, mul_zero, Complex.ofReal_zero, zero_smul,
            NormedSpace.exp_zero]
      rw [TimeDependentExtensions.evolution_congr' _ _ M (fun r _ => hf r),
        TimeDependentExtensions.Coherent.evolution_window
          (fun r => if a i ≤ r ∧ r < b i then G r else 1) (hab i) (hbM i)
          (fun r hr => if_neg (by omega))]
      exact TimeDependentExtensions.Coherent.orderedProduct_congr _ _ _ _
        (fun j hj => if_pos (by omega))
    -- The mesh product over the window.
    let E : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
      NormedSpace.exp ((-Complex.I * ((t (r + 1) - t r : ℝ) : ℂ)) • A r)
    have hmis : ‖TimeDependent.orderedProduct G (a i) (b i - a i) -
        TimeDependent.orderedProduct E (a i) (b i - a i)‖ ≤ ε / 3 := by
      rw [TimeDependentExtensions.Coherent.orderedProduct_eq_evolution,
        TimeDependentExtensions.Coherent.orderedProduct_eq_evolution]
      have hstep : ∀ j, ‖G (a i + j) - E (a i + j)‖ ≤ T / N * (Real.sqrt s * η) := by
        intro j
        refine (TimeDependentExtensions.exp_sub_exp_norm_le (A _) (hA _) _ _).trans ?_
        exact mul_le_mul (TimeDependentExtensions.blockLength_sub_lt hmesh hT hN _).le (hΛ _)
          (norm_nonneg _) (div_pos hT hNR).le
      have h1 := evolution_sub_norm_le_mul _ _
        (fun j => TimeDependentExtensions.exp_skew_norm_le (A _) (hA _) _)
        (fun j => TimeDependentExtensions.exp_skew_norm_le (A _) (hA _) _) hstep (b i - a i)
      have hlen : ((b i - a i : ℕ) : ℝ) ≤ M := by
        exact_mod_cast (show b i - a i ≤ M by have := hbM i; omega)
      have hbound : (M : ℝ) * (T / N * (Real.sqrt s * η)) ≤ ε / 3 := by
        have heq : (M : ℝ) * (T / N * (Real.sqrt s * η)) =
            M * (Real.sqrt s * (η * T)) / N := by
          field_simp
        rw [heq, div_le_iff₀ hNR]
        linarith
      calc _ ≤ ((b i - a i : ℕ) : ℝ) * (T / N * (Real.sqrt s * η)) := h1
        _ ≤ (M : ℝ) * (T / N * (Real.sqrt s * η)) :=
          mul_le_mul_of_nonneg_right hlen (by positivity)
        _ ≤ ε / 3 := hbound
    -- Duhamel on the window, for the integral-sense solution `V_i`.
    have hab' : a i + (b i - a i) = b i := by have := hab i; omega
    have hsub : Icc (t (a i)) (t (b i)) ⊆ Icc 0 T := fun u hu =>
      ⟨(hmesh.nonneg _).trans hu.1, hu.2.trans (hmesh.le_last (hbM i))⟩
    have hwin := Propagator.SolvesIntegralOn.window_error (H := Hop) A hmesh.mono (a i)
      (b i - a i) (by rw [hab']; exact hV i) (hV0 i)
      (by
        rw [hab']
        filter_upwards [hHop] with u hu hmem
        exact hu (hsub hmem))
      hA
      (by
        rw [hab']
        refine hInt.mono_set (Set.uIcc_subset_uIcc ?_ ?_)
        · exact Set.mem_uIcc_of_le (hmesh.nonneg _) (hmesh.le_last ((hab i).trans (hbM i)))
        · exact Set.mem_uIcc_of_le (hmesh.nonneg _) (hmesh.le_last (hbM i)))
    rw [hab'] at hwin
    have hnonneg : ∀ r, 0 ≤ ∫ u in t r..t (r + 1), ‖Hop u - A r‖ := fun r =>
      intervalIntegral.integral_nonneg (hmesh.mono (Nat.le_succ r)) (fun u _ => norm_nonneg _)
    have hsum : ∑ j ∈ Finset.range (b i - a i), ∫ u in t (a i + j)..t (a i + j + 1),
        ‖Hop u - A (a i + j)‖ ≤ ε / 3 := by
      rw [← Finset.sum_Ico_eq_sum_range (fun r => ∫ u in t r..t (r + 1), ‖Hop u - A r‖)]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.range M) ?_
        (fun r _ _ => hnonneg r)) ?_
      · intro r hr
        rw [Finset.mem_Ico] at hr
        rw [Finset.mem_range]
        have := hbM i
        omega
      · rw [← Fin.sum_univ_eq_sum_range (fun r => ∫ u in t r..t (r + 1), ‖Hop u - A r‖) M]
        have hidx : ∀ r : Fin M, Sampled.sampleIndex hM r = r := fun r =>
          TimeDependentExtensions.Hamiltonian.sampleIndex_val hM r
        simpa only [Hop, A, hidx] using hCert
    rw [hslot, hgroup]
    calc ‖TimeDependent.orderedProduct G (a i) (b i - a i) - V i (t (b i))‖ ≤
          ‖TimeDependent.orderedProduct G (a i) (b i - a i) -
            TimeDependent.orderedProduct E (a i) (b i - a i)‖ +
          ‖TimeDependent.orderedProduct E (a i) (b i - a i) - V i (t (b i))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε / 3 + ε / 3 := by
        apply add_le_add hmis
        rw [norm_sub_rev]
        exact hwin.trans hsum
  have hsel := (hAct x).2
  have hdiag : TimeDependentExtensions.Coherent.selected D (pieceOf t T N hM) N
      (TimeDependentExtensions.Coherent.windows T a b) x -
      WeightedClock.diagonal (fun i => V i (t (b i))) =
        WeightedClock.diagonal (fun i => evolution (fun k => NormedSpace.exp
          ((-Complex.I * ((TimeDependentExtensions.Coherent.windows T a b i (pieceOf t T N hM k) /
            N : ℝ) : ℂ)) •
            SparseStateOverlap.matrixOperator (D.matrix (x, pieceOf t T N hM k)))) N -
          V i (t (b i))) := by
    ext v i
    rfl
  have hdn : ‖TimeDependentExtensions.Coherent.selected D (pieceOf t T N hM) N
      (TimeDependentExtensions.Coherent.windows T a b) x -
      WeightedClock.diagonal (fun i => V i (t (b i)))‖ ≤ ε / 3 + ε / 3 := by
    rw [hdiag]
    exact WeightedClock.norm_diagonal_le _ _ (by positivity) hbranch
  calc ‖p.eval x ∘L ι' - ι' ∘L WeightedClock.diagonal (fun i => V i (t (b i)))‖ ≤
        ‖p.eval x ∘L ι' - ι' ∘L TimeDependentExtensions.Coherent.selected D (pieceOf t T N hM) N
          (TimeDependentExtensions.Coherent.windows T a b) x‖ +
        ‖ι' ∘L TimeDependentExtensions.Coherent.selected D (pieceOf t T N hM) N
            (TimeDependentExtensions.Coherent.windows T a b) x -
          ι' ∘L WeightedClock.diagonal (fun i => V i (t (b i)))‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε / 3 + 1 * (ε / 3 + ε / 3) := by
      apply add_le_add hsel
      rw [← comp_sub]
      exact (opNorm_comp_le _ _).trans (mul_le_mul hιn hdn (norm_nonneg _) zero_le_one)
    _ = ε := by ring

end

end IntegrablePathSimulation.Coherent
