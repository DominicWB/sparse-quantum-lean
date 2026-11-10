import IntegrablePathSimulation.Hamiltonian.Theorem
import IntegrablePathSimulation.Propagator.Classical
import TimeDependentExtensions.Hamiltonian.Corollaries

set_option autoImplicit false

/-!
# Consequences of the simulation theorem for integrable paths

* `simulation_piecewise`: the released `TimeDependentExtensions.Hamiltonian.simulation`
  (piecewise paths with breakpoints at the mesh points and classical piecewise propagators),
  with its statement unchanged, as a corollary of `simulation`: the pieces are glued into one
  integrable path (`Propagator.glue`), the piecewise propagator is a propagator of the glued
  path (`Propagator.isPropagator_glue`), and the certificates agree because the glued path
  equals each piece almost everywhere on its interval.
* `simulation_classical`: the released `TimeDependentExtensions.Hamiltonian.simulation_path`
  (one path, classical propagator on `[0, T]`), with its statement unchanged, as a corollary
  (`Propagator.isPropagator_of_solvesOn`).
* `simulation_dyson`: the bound of `simulation` against the Dyson series
  `Propagator.picardSeries`, the time-ordered exponential `U_H(T, 0)` of equation
  `hs:eq:timeerror` in iterated-integral form, with no propagator supplied.
* `simulation_with_reference`: the bound of `simulation` with an arbitrary untouched finite
  reference register (Theorem `hs:thm:time` of the manuscript: "The error includes all work
  registers and is unchanged by an untouched reference system"), for integrable paths.
-/

namespace IntegrablePathSimulation.Hamiltonian

noncomputable section

open SparseHamiltonian SparseHamiltonian.TimeDependent ContinuousLinearMap OracleCircuit
open NativeSparseBlockEncoding CayleyClockInterface FixedNativeCayleySimulation
open MeasureTheory Set
open TimeDependentExtensions (IsMesh)
open IntegrablePathSimulation.Propagator (IsPropagator)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

set_option maxRecDepth 8192 in
/-- **The released piecewise theorem as a corollary.** The statement of
`TimeDependentExtensions.Hamiltonian.simulation` (piecewise Hermitian, interval-integrable
paths with one piece per mesh interval and classical piecewise propagators), derived from
`simulation` for integrable paths. -/
theorem simulation_piecewise (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ)
    (η T ε : ℝ) (N : ℕ) (hη : 0 < η) (hT : 0 < T) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hN : 0 < N) (hmesh : IsMesh t M T)
    (hClock : 4 * s * (η * T) ≤ N)
    (hCayley : 9 * (Real.sqrt s * (η * T)) ^ 3 ≤ ε * (N : ℝ) ^ 2)
    (hRefine : 9 * M * (Real.sqrt s * (η * T)) ≤ ε * N)
    (hH : ∀ y, (D.matrix y).IsHermitian)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * T) +
            Real.sqrt ((s : ℝ) * (η * T) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε)† ∘L
          TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ (Hp : Fin M → ℝ → Matrix n n ℂ)
            (U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)),
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), (Hp r u).IsHermitian) →
            (∀ r : Fin M, IntervalIntegrable
              (fun u => SparseStateOverlap.matrixOperator (Hp r u)) volume
                (t r) (t ((r : ℕ) + 1))) →
            ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
              ‖SparseStateOverlap.matrixOperator (Hp r u) -
                SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 9 →
            U 0 = 1 →
            (∀ r : Fin M, SolvesOn (fun u => SparseStateOverlap.matrixOperator (Hp r u)) U
              (t r) (t ((r : ℕ) + 1))) →
            ‖p.eval x ∘L TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε -
              TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε ∘L U T‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hAction⟩ :=
    simulation D hM t η T ε N hη hT hε hεHalf hN hmesh hClock hCayley hRefine hH hrow hcol
  refine ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, fun x => ⟨(hAction x).1, ?_⟩⟩
  intro Hp U hPath hInt hCert hU0 hU
  let Hq : ℕ → ℝ → Matrix n n ℂ := fun r => Hp (Sampled.sampleIndex hM r)
  let Hop : ℕ → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r u =>
    SparseStateOverlap.matrixOperator (Hq r u)
  have hIntq : ∀ r < M, IntervalIntegrable (Hop r) volume (t r) (t (r + 1)) := by
    intro r hr
    simp only [Hop, Hq, TimeDependentExtensions.Hamiltonian.sampleIndex_of_lt hM hr]
    exact hInt ⟨r, hr⟩
  apply (hAction x).2 (Propagator.glue Hq t M) U
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
  · exact Propagator.isPropagator_glue hmesh ⟨hU0, fun r hr => by
      simpa only [Hop, Hq, TimeDependentExtensions.Hamiltonian.sampleIndex_of_lt hM hr] using
        hU ⟨r, hr⟩⟩ hIntq

set_option maxRecDepth 8192 in
/-- **The released one-path theorem as a corollary.** The statement of
`TimeDependentExtensions.Hamiltonian.simulation_path` (one Hermitian, interval-integrable path
and a classical propagator on `[0, T]`), derived from `simulation` for integrable paths. -/
theorem simulation_classical (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ)
    (η T ε : ℝ) (N : ℕ) (hη : 0 < η) (hT : 0 < T) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hN : 0 < N) (hmesh : IsMesh t M T)
    (hClock : 4 * s * (η * T) ≤ N)
    (hCayley : 9 * (Real.sqrt s * (η * T)) ^ 3 ≤ ε * (N : ℝ) ^ 2)
    (hRefine : 9 * M * (Real.sqrt s * (η * T)) ≤ ε * N)
    (hH : ∀ y, (D.matrix y).IsHermitian)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * T) +
            Real.sqrt ((s : ℝ) * (η * T) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε)† ∘L
          TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ (H : ℝ → Matrix n n ℂ) (U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)),
            (∀ u ∈ Icc 0 T, (H u).IsHermitian) →
            IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (H u)) volume 0 T →
            ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
              ‖SparseStateOverlap.matrixOperator (H u) -
                SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 9 →
            U 0 = 1 → SolvesOn (fun u => SparseStateOverlap.matrixOperator (H u)) U 0 T →
            ‖p.eval x ∘L TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε -
              TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε ∘L U T‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hAction⟩ :=
    simulation D hM t η T ε N hη hT hε hεHalf hN hmesh hClock hCayley hRefine hH hrow hcol
  refine ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, fun x => ⟨(hAction x).1, ?_⟩⟩
  intro H U hPath hInt hCert hU0 hU
  exact (hAction x).2 H U (ae_of_all _ hPath) hInt hCert
    (Propagator.isPropagator_of_solvesOn hT.le hU0 hU hInt)

set_option maxRecDepth 8192 in
/-- **The time-ordered exponential.** The program and encoding of `simulation` approximate the
Dyson series `Propagator.picardSeries` of every path that is Hermitian at almost every time of
`[0, T]`, interval integrable on `[0, T]` and certified to `ε / 9`:
`‖𝒜 ι - ι U_H(T, 0)‖ ≤ ε` with `U_H(T, 0) = 𝒯 exp (-i ∫_0^T H(u) du)`. -/
theorem simulation_dyson (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (η T ε : ℝ)
    (N : ℕ) (hη : 0 < η) (hT : 0 < T) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) (hN : 0 < N)
    (hmesh : IsMesh t M T)
    (hClock : 4 * s * (η * T) ≤ N)
    (hCayley : 9 * (Real.sqrt s * (η * T)) ^ 3 ≤ ε * (N : ℝ) ^ 2)
    (hRefine : 9 * M * (Real.sqrt s * (η * T)) ≤ ε * N)
    (hH : ∀ y, (D.matrix y).IsHermitian)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * T) +
            Real.sqrt ((s : ℝ) * (η * T) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε)† ∘L
          TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ H : ℝ → Matrix n n ℂ,
            (∀ᵐ u, u ∈ Icc 0 T → (H u).IsHermitian) →
            IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (H u)) volume 0 T →
            ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
              ‖SparseStateOverlap.matrixOperator (H u) -
                SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 9 →
            ‖p.eval x ∘L TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε -
              TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε ∘L
                Propagator.picardSeries (fun u => SparseStateOverlap.matrixOperator (H u)) T‖ ≤
              ε := by
  obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hAction⟩ :=
    simulation D hM t η T ε N hη hT hε hεHalf hN hmesh hClock hCayley hRefine hH hrow hcol
  refine ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, fun x => ⟨(hAction x).1, ?_⟩⟩
  intro H hPath hInt hCert
  exact (hAction x).2 H _ hPath hInt hCert (Propagator.isPropagator_picardSeries hT.le hInt)

set_option maxRecDepth 8192 in
/-- **Untouched references.** The program and encoding of `simulation` obey the full-output
bound for integrable paths on arbitrary normalised inputs entangled with an untouched finite
reference register. -/
theorem simulation_with_reference {R : Type*} [Fintype R] (D : Data (X × Fin M) n Z s)
    (hM : 0 < M) (t : ℕ → ℝ) (η T ε : ℝ) (N : ℕ) (hη : 0 < η) (hT : 0 < T) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2) (hN : 0 < N) (hmesh : IsMesh t M T)
    (hClock : 4 * s * (η * T) ≤ N)
    (hCayley : 9 * (Real.sqrt s * (η * T)) ^ 3 ≤ ε * (N : ℝ) ^ 2)
    (hRefine : 9 * M * (Real.sqrt s * (η * T)) ≤ ε * N)
    (hH : ∀ y, (D.matrix y).IsHermitian)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * T) +
            Real.sqrt ((s : ℝ) * (η * T) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε)† ∘L
          TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ (H : ℝ → Matrix n n ℂ) (U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)),
            (∀ᵐ u, u ∈ Icc 0 T → (H u).IsHermitian) →
            IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (H u)) volume 0 T →
            ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
              ‖SparseStateOverlap.matrixOperator (H u) -
                SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 9 →
            IsPropagator (fun u => SparseStateOverlap.matrixOperator (H u)) U T →
            ∀ ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n), ‖ψ‖ = 1 →
              ‖FiniteReferenceLift.lift (p.eval x)
                  (FiniteReferenceLift.lift
                    (TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε) ψ) -
                FiniteReferenceLift.lift
                    (TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε)
                  (FiniteReferenceLift.lift (U T) ψ)‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hAction⟩ :=
    simulation D hM t η T ε N hη hT hε hεHalf hN hmesh hClock hCayley hRefine hH hrow hcol
  refine ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, fun x => ⟨(hAction x).1, ?_⟩⟩
  intro H U hPath hInt hCert hU ψ hψ
  simpa only [hψ, mul_one] using
    FiniteReferenceLift.same_embedding_error_le (p.eval x)
      (TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε) (U T) ε
      ((hAction x).2 H U hPath hInt hCert hU) ψ

end

end IntegrablePathSimulation.Hamiltonian
