import TimeDependentExtensions.Hamiltonian.Theorem
import SparseHamiltonian.FiniteReferenceLift

set_option autoImplicit false

/-!
# Consequences of the general-mesh simulation theorem

* `simulation_lipschitz`: piecewise Lipschitz paths with breakpoints at the mesh points and
  one-sided samples, `‖H_r(t_r) - H̃_r‖ ≤ δ_r`, `β_r`-Lipschitz pieces; the certificate is
  `∑_r (β_r Δ_r² / 2 + δ_r Δ_r)` (equation `hs:eq:timedisc` without the Cayley term, which
  the refined slots take care of). A propagator of the piecewise path exists, so the
  statement is not vacuous.
* `simulation_path`: one Hermitian, interval-integrable path on `[0, T]` and any mesh, with
  the integrated certificate `∑_r ∫_{t_r}^{t_{r+1}} ‖H(u) - H̃_r‖ du`, for every classical
  propagator of the path (one exists, for example, for continuous paths).
* `simulation_with_reference`: the guarantee of `simulation` on inputs entangled with an
  untouched finite reference register.
* `slotCount`, `slotCount_spec`: an explicit admissible slot count; every larger one is
  admissible too.
* `isMesh_uniform`: the uniform mesh of the released theorem is a mesh.
-/

namespace TimeDependentExtensions

namespace Hamiltonian

noncomputable section

open SparseHamiltonian SparseHamiltonian.TimeDependent ContinuousLinearMap OracleCircuit
open NativeSparseBlockEncoding MeasureTheory Set
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

set_option maxRecDepth 8192 in
/-- **Piecewise Lipschitz paths with breakpoints.** The program and encoding of
`simulation` approximate every propagator of every path with `β_r`-Lipschitz Hermitian
pieces on the mesh intervals whose one-sided samples satisfy `‖H_r(t_r) - H̃_r‖ ≤ δ_r`,
provided `∑_r (β_r Δ_r² / 2 + δ_r Δ_r) ≤ ε / 9`; such a propagator exists. -/
theorem simulation_lipschitz (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ)
    (η T ε : ℝ) (N : ℕ) (hη : 0 < η) (hT : 0 < T) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hN : 0 < N) (hmesh : IsMesh t M T)
    (hClock : 4 * s * (η * T) ≤ N)
    (hCayley : 9 * (Real.sqrt s * (η * T)) ^ 3 ≤ ε * (N : ℝ) ^ 2)
    (hRefine : 9 * M * (Real.sqrt s * (η * T)) ≤ ε * N)
    (hH : ∀ y, (D.matrix y).IsHermitian)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program (oracle D N γ η T ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * T) +
            Real.sqrt ((s : ℝ) * (η * T) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (input D hM t N γ η T ε)† ∘L input D hM t N γ η T ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ (Hp : Fin M → ℝ → Matrix n n ℂ) (β δ : Fin M → ℝ),
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), (Hp r u).IsHermitian) →
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)),
              ∀ v ∈ Icc (t r) (t ((r : ℕ) + 1)),
                ‖SparseStateOverlap.matrixOperator (Hp r u) -
                  SparseStateOverlap.matrixOperator (Hp r v)‖ ≤ β r * |u - v|) →
            (∀ r : Fin M, ‖SparseStateOverlap.matrixOperator (Hp r (t r)) -
              SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δ r) →
            ∑ r : Fin M, (β r * (t ((r : ℕ) + 1) - t r) ^ 2 / 2 +
              δ r * (t ((r : ℕ) + 1) - t r)) ≤ ε / 9 →
            (∃ U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n), U 0 = 1 ∧
              ∀ r : Fin M, SolvesOn (fun u => SparseStateOverlap.matrixOperator (Hp r u)) U
                (t r) (t ((r : ℕ) + 1))) ∧
            ∀ U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n), U 0 = 1 →
              (∀ r : Fin M, SolvesOn (fun u => SparseStateOverlap.matrixOperator (Hp r u)) U
                (t r) (t ((r : ℕ) + 1))) →
              ‖p.eval x ∘L input D hM t N γ η T ε - input D hM t N γ η T ε ∘L U T‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hAction⟩ :=
    simulation D hM t η T ε N hη hT hε hεHalf hN hmesh hClock hCayley hRefine hH hrow hcol
  refine ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, fun x => ⟨(hAction x).1, ?_⟩⟩
  intro Hp β δ hPath hLip hVal hSum
  have hle : ∀ r : Fin M, t r ≤ t ((r : ℕ) + 1) := fun r => hmesh.mono (Nat.le_succ _)
  have hcont : ∀ r : Fin M, ContinuousOn
      (fun u => SparseStateOverlap.matrixOperator (Hp r u)) (Icc (t r) (t ((r : ℕ) + 1))) :=
    fun r => continuousOn_of_lipschitz _ (hLip r)
  have hInt : ∀ r : Fin M, IntervalIntegrable
      (fun u => SparseStateOverlap.matrixOperator (Hp r u)) volume (t r) (t ((r : ℕ) + 1)) :=
    fun r => (hcont r).intervalIntegrable_of_Icc (hle r)
  have hCert : ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
      ‖SparseStateOverlap.matrixOperator (Hp r u) -
        SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 9 :=
    (Finset.sum_le_sum fun r _ =>
      integral_le_of_lipschitz' _ _ (hle r) (hLip r) (hVal r)).trans hSum
  refine ⟨?_, fun U hU0 hU => (hAction x).2 Hp U hPath hInt hCert hU0 hU⟩
  let Hq : ℕ → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r u =>
    SparseStateOverlap.matrixOperator (Hp (Sampled.sampleIndex hM r) u)
  obtain ⟨U, hU0, hU⟩ := exists_piecewise_propagator Hq hmesh.zero hmesh.mono M
    (fun r hr => by
      simp only [Hq, sampleIndex_of_lt hM hr]
      exact hcont ⟨r, hr⟩)
  refine ⟨U, hU0, fun r => ?_⟩
  have h := hU r r.isLt
  simp only [Hq, sampleIndex_val] at h
  exact h

set_option maxRecDepth 8192 in
/-- **One path, any mesh.** The program and encoding of `simulation` approximate every
propagator of every Hermitian, interval-integrable path `H` on `[0, T]` whose integrated sample
errors `∑_r ∫_{t_r}^{t_{r+1}} ‖H(u) - H̃_r‖ du` are at most `ε / 9`. Propagators are classical
(`SolvesOn` on `[0, T]`); one exists, for example, for continuous paths. -/
theorem simulation_path (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ)
    (η T ε : ℝ) (N : ℕ) (hη : 0 < η) (hT : 0 < T) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hN : 0 < N) (hmesh : IsMesh t M T)
    (hClock : 4 * s * (η * T) ≤ N)
    (hCayley : 9 * (Real.sqrt s * (η * T)) ^ 3 ≤ ε * (N : ℝ) ^ 2)
    (hRefine : 9 * M * (Real.sqrt s * (η * T)) ≤ ε * N)
    (hH : ∀ y, (D.matrix y).IsHermitian)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program (oracle D N γ η T ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * T) +
            Real.sqrt ((s : ℝ) * (η * T) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (input D hM t N γ η T ε)† ∘L input D hM t N γ η T ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ (H : ℝ → Matrix n n ℂ) (U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)),
            (∀ u ∈ Icc 0 T, (H u).IsHermitian) →
            IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (H u)) volume 0 T →
            ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
              ‖SparseStateOverlap.matrixOperator (H u) -
                SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 9 →
            U 0 = 1 → SolvesOn (fun u => SparseStateOverlap.matrixOperator (H u)) U 0 T →
            ‖p.eval x ∘L input D hM t N γ η T ε - input D hM t N γ η T ε ∘L U T‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hAction⟩ :=
    simulation D hM t η T ε N hη hT hε hεHalf hN hmesh hClock hCayley hRefine hH hrow hcol
  refine ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, fun x => ⟨(hAction x).1, ?_⟩⟩
  intro H U hPath hInt hCert hU0 hU
  have hlo : ∀ r : Fin M, 0 ≤ t r := fun r => hmesh.nonneg r
  have hhi : ∀ r : Fin M, t ((r : ℕ) + 1) ≤ T := fun r => hmesh.le_last r.isLt
  apply (hAction x).2 (fun _ => H) U _ _ hCert hU0
  · exact fun r => hU.mono (hlo r) (hhi r)
  · intro r u hu
    exact hPath u ⟨(hlo r).trans hu.1, hu.2.trans (hhi r)⟩
  · intro r
    apply hInt.mono_set
    apply Set.uIcc_subset_uIcc
    · exact Set.mem_uIcc_of_le (hlo r) ((hmesh.mono (Nat.le_succ _)).trans (hhi r))
    · exact Set.mem_uIcc_of_le ((hlo r).trans (hmesh.mono (Nat.le_succ _))) (hhi r)

set_option maxRecDepth 8192 in
/-- **Untouched references.** The program and encoding of `simulation` obey the full-output
bound on arbitrary normalised inputs entangled with an untouched finite reference register. -/
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
      ∃ p : MultiOracleCircuit.Program (oracle D N γ η T ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * T) +
            Real.sqrt ((s : ℝ) * (η * T) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (input D hM t N γ η T ε)† ∘L input D hM t N γ η T ε = 1 ∧
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
            ∀ ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n), ‖ψ‖ = 1 →
              ‖FiniteReferenceLift.lift (p.eval x)
                  (FiniteReferenceLift.lift (input D hM t N γ η T ε) ψ) -
                FiniteReferenceLift.lift (input D hM t N γ η T ε)
                  (FiniteReferenceLift.lift (U T) ψ)‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hAction⟩ :=
    simulation D hM t η T ε N hη hT hε hεHalf hN hmesh hClock hCayley hRefine hH hrow hcol
  refine ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, fun x => ⟨(hAction x).1, ?_⟩⟩
  intro Hp U hPath hInt hCert hU0 hU ψ hψ
  simpa only [hψ, mul_one] using
    FiniteReferenceLift.same_embedding_error_le (p.eval x) (input D hM t N γ η T ε) (U T) ε
      ((hAction x).2 Hp U hPath hInt hCert hU0 hU) ψ

/-! ### An explicit admissible slot count -/

/-- An explicit slot count meeting the three public slot conditions. -/
def slotCount (s M : ℕ) (η T ε : ℝ) : ℕ :=
  ⌈4 * s * (η * T) + 9 * M * (Real.sqrt s * (η * T)) / ε +
    Real.sqrt (9 * (Real.sqrt s * (η * T)) ^ 3 / ε)⌉₊ + 1

/-- Every slot count at least `slotCount s M η T ε` satisfies the clock condition, the Cayley
condition and the refinement condition of `simulation`. -/
theorem slotCount_spec (s M : ℕ) (η T ε : ℝ) (hη : 0 ≤ η) (hT : 0 ≤ T) (hε : 0 < ε)
    (N : ℕ) (hN : slotCount s M η T ε ≤ N) :
    0 < N ∧ 4 * s * (η * T) ≤ N ∧ 9 * (Real.sqrt s * (η * T)) ^ 3 ≤ ε * (N : ℝ) ^ 2 ∧
      9 * M * (Real.sqrt s * (η * T)) ≤ ε * N := by
  set A : ℝ := 4 * s * (η * T)
  set B : ℝ := 9 * M * (Real.sqrt s * (η * T)) / ε
  set C : ℝ := Real.sqrt (9 * (Real.sqrt s * (η * T)) ^ 3 / ε)
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hceil := Nat.le_ceil (A + B + C)
  have hSize : A + B + C ≤ slotCount s M η T ε := by
    have hcast : ((⌈A + B + C⌉₊ + 1 : ℕ) : ℝ) = (⌈A + B + C⌉₊ : ℝ) + 1 := by push_cast; ring
    change A + B + C ≤ ((⌈A + B + C⌉₊ + 1 : ℕ) : ℝ)
    rw [hcast]
    linarith
  have hNR : (slotCount s M η T ε : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨lt_of_lt_of_le (Nat.succ_pos _) hN, by linarith, ?_, ?_⟩
  · have hCle : C ≤ N := by linarith
    have hsq : C ^ 2 = 9 * (Real.sqrt s * (η * T)) ^ 3 / ε := by
      simp only [C]
      rw [Real.sq_sqrt (by positivity)]
    have h2 : C ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hC hCle 2
    have h3 := mul_le_mul_of_nonneg_left h2 hε.le
    have hεC : ε * C ^ 2 = 9 * (Real.sqrt s * (η * T)) ^ 3 := by
      rw [hsq]
      field_simp
    linarith
  · have hBle : B ≤ N := by linarith
    have h := mul_le_mul_of_nonneg_left hBle hε.le
    have hεB : ε * B = 9 * M * (Real.sqrt s * (η * T)) := by
      simp only [B]
      field_simp
    linarith

/-- The uniform mesh `t_r = r T / M` of `TimeDependent.simulation` is a mesh. -/
theorem isMesh_uniform (hM : 0 < M) {T : ℝ} (hT : 0 ≤ T) :
    IsMesh (fun r : ℕ => (r : ℝ) * T / M) M T := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨by simp, by field_simp, ?_⟩
  intro a b hab
  apply div_le_div_of_nonneg_right _ hMR.le
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hT

end

end Hamiltonian

end TimeDependentExtensions
