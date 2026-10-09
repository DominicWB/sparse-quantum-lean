import IntegrablePathSimulation.Coherent.Theorem
import IntegrablePathSimulation.Propagator.Classical

set_option autoImplicit false

/-!
# The released coherent windows as a corollary

`coherent_windows_piecewise` is the released `TimeDependentExtensions.Coherent.coherent_windows`
(piecewise paths with one piece per mesh interval and classical solutions of the pieces of
each window), with its statement unchanged, derived from `Coherent.coherent_windows` for
integrable paths: the pieces are glued into one integrable path (`Propagator.glue`), the
classical window solutions solve the integral equation of the glued path on each window
(`Propagator.solvesIntegralOn_glue`), and the certificates agree because the glued path
equals each piece almost everywhere on its interval (`Propagator.glue_ae_eq`).
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
/-- **The released coherent windows as a corollary.** The statement of
`TimeDependentExtensions.Coherent.coherent_windows` (Hermitian, interval-integrable pieces and
classical solutions of the pieces of each window), derived from `coherent_windows` for
integrable paths. -/
theorem coherent_windows_piecewise (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ}
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
          ∀ (Hp : Fin M → ℝ → Matrix n n ℂ) (V : ι → ℝ → EuclideanSpace ℂ n →L[ℂ]
              EuclideanSpace ℂ n),
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), (Hp r u).IsHermitian) →
            (∀ r : Fin M, IntervalIntegrable
              (fun u => SparseStateOverlap.matrixOperator (Hp r u)) volume
                (t r) (t ((r : ℕ) + 1))) →
            ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
              ‖SparseStateOverlap.matrixOperator (Hp r u) -
                SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 3 →
            (∀ i, V i (t (a i)) = 1) →
            (∀ i (r : Fin M), a i ≤ (r : ℕ) → (r : ℕ) < b i →
              SolvesOn (fun u => SparseStateOverlap.matrixOperator (Hp r u)) (V i)
                (t r) (t ((r : ℕ) + 1))) →
            ‖p.eval x ∘L TimeDependentExtensions.MeshSelect.alignedInput D hM
                  (pieceOf t T N hM) b0 N γ η T (ε / 3) -
              TimeDependentExtensions.MeshSelect.alignedInput D hM (pieceOf t T N hM) b0 N γ η T
                  (ε / 3) ∘L
                WeightedClock.diagonal (fun i => V i (t (b i)))‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, hWidth, hAll⟩ := coherent_windows D hM t hN b0 η T ε hη hT hε hεOne
    hmesh hH hrow hcol hClock hCayley hRefine
  refine ⟨γ, hγ, hγOne, hWidth, fun a b hab hbM => ?_⟩
  obtain ⟨p, hCount, hIn, hAct⟩ := hAll a b hab hbM
  refine ⟨p, hCount, hIn, fun x => ⟨(hAct x).1, ?_⟩⟩
  intro Hp V hPath hInt hCert hV0 hV
  let Hq : ℕ → ℝ → Matrix n n ℂ := fun r => Hp (Sampled.sampleIndex hM r)
  let Hop : ℕ → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r u =>
    SparseStateOverlap.matrixOperator (Hq r u)
  have hIntq : ∀ r < M, IntervalIntegrable (Hop r) volume (t r) (t (r + 1)) := by
    intro r hr
    simp only [Hop, Hq, TimeDependentExtensions.Hamiltonian.sampleIndex_of_lt hM hr]
    exact hInt ⟨r, hr⟩
  apply (hAct x).2 (Propagator.glue Hq t M) V
  · refine ae_of_all _ fun u hu => ?_
    have hlt : Propagator.pieceIndex t M u < M := Propagator.pieceIndex_lt hM u
    have h := hPath ⟨Propagator.pieceIndex t M u, hlt⟩ u
      (Propagator.mem_Icc_pieceIndex hmesh hM hu)
    show (Hp (Sampled.sampleIndex hM (Propagator.pieceIndex t M u)) u).IsHermitian
    rw [TimeDependentExtensions.Hamiltonian.sampleIndex_of_lt hM hlt]
    exact h
  · exact Propagator.intervalIntegrable_glue hmesh hIntq
  · refine (le_of_eq (Finset.sum_congr rfl fun r _ => ?_)).trans hCert
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le (hmesh.mono (Nat.le_succ r))]
    filter_upwards [Propagator.glue_ae_eq Hq hmesh r.isLt] with u hu hmem
    rw [hu hmem]
    simp only [Hq, TimeDependentExtensions.Hamiltonian.sampleIndex_val]
  · exact hV0
  · intro i
    exact Propagator.solvesIntegralOn_glue (Hp := Hop) hmesh (hab i) (hbM i)
      (fun r har hrb => by
        simpa only [Hop, Hq,
          TimeDependentExtensions.Hamiltonian.sampleIndex_of_lt hM
            (show r < M by have := hbM i; omega)] using hV i ⟨r, by have := hbM i; omega⟩ har hrb)
      (fun r _ hrb => hIntq r (by have := hbM i; omega))

end

end IntegrablePathSimulation.Coherent
