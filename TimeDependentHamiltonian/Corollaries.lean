import TimeDependentHamiltonian.Theorem
import TimeDependentHamiltonian.Continuous.Existence

/-!
# Consequences of the time-dependent simulation theorem

* `simulation_propagator`: the propagator of the intended path exists, and the
  same program approximates it; the main theorem is therefore not vacuous.
* `simulation_with_reference`: the error bound holds on arbitrary normalized
  inputs entangled with an untouched finite reference.
* `meshSize`, `meshSize_spec`: an explicit admissible mesh size.
* `input_isometry`: the clean encoding is an isometry for all public
  parameters.
* `zero_path_identity`, `zero_certificate`: for zero time or a zero path,
  every propagator from the identity is the identity, so the identity program
  over the same oracles, with no queries, is exact.
-/

namespace SparseHamiltonian.TimeDependent

noncomputable section

open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

set_option maxRecDepth 8192 in
/-- The propagator of the intended path exists and is approximated by the
program of `simulation`. -/
theorem simulation_propagator (D : Data (X × Fin M) n Z s) (Hpath : X → ℝ → Matrix n n ℂ)
    (η t β δ ε : ℝ) (hη : 0 < η) (ht : 0 ≤ t) (hβ : 0 ≤ β) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2) (hM : 0 < M)
    (hMesh : 4 * s * (η * t) ≤ M) (hFreeze : 9 * β * t ^ 2 ≤ ε * M)
    (hCayley : 9 * (Real.sqrt s * (η * t)) ^ 3 ≤ ε * (M : ℝ) ^ 2)
    (hH : ∀ y, (D.matrix y).IsHermitian)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hPath : ∀ x, ∀ u ∈ Icc 0 t, (Hpath x u).IsHermitian)
    (hLip : ∀ x, ∀ u ∈ Icc 0 t, ∀ v ∈ Icc 0 t,
      ‖SparseStateOverlap.matrixOperator (Hpath x u) -
        SparseStateOverlap.matrixOperator (Hpath x v)‖ ≤ β * |u - v|)
    (hVal : ∀ x (r : Fin M), ‖SparseStateOverlap.matrixOperator (Hpath x (r * t / M)) -
      SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δ)
    (hValBudget : t * δ ≤ ε / 12) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program (oracle D γ η t ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * t) +
            Real.sqrt ((s : ℝ) * (η * t) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (input D hM γ η t ε)† ∘L input D hM γ η t ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∃ U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n), U 0 = 1 ∧
            SolvesOn (fun u => SparseStateOverlap.matrixOperator (Hpath x u)) U 0 t ∧
            ‖p.eval x ∘L input D hM γ η t ε - input D hM γ η t ε ∘L U t‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hAction⟩ :=
    simulation D Hpath η t β δ ε hη ht hβ hε hεHalf hM hMesh hFreeze hCayley hH hrow hcol
      hPath hLip hVal hValBudget
  refine ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, fun x => ⟨(hAction x).1, ?_⟩⟩
  obtain ⟨U, hU0, hU⟩ := exists_solvesOn_of_lipschitz
    (fun u => SparseStateOverlap.matrixOperator (Hpath x u)) ht (hLip x)
  exact ⟨U, hU0, hU, (hAction x).2 U hU0 hU⟩

set_option maxRecDepth 8192 in
/-- The same program and clean encoding obey the full-output bound on
arbitrary normalized inputs entangled with an untouched finite reference. -/
theorem simulation_with_reference {R : Type*} [Fintype R]
    (D : Data (X × Fin M) n Z s) (Hpath : X → ℝ → Matrix n n ℂ)
    (η t β δ ε : ℝ) (hη : 0 < η) (ht : 0 ≤ t) (hβ : 0 ≤ β) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2) (hM : 0 < M)
    (hMesh : 4 * s * (η * t) ≤ M) (hFreeze : 9 * β * t ^ 2 ≤ ε * M)
    (hCayley : 9 * (Real.sqrt s * (η * t)) ^ 3 ≤ ε * (M : ℝ) ^ 2)
    (hH : ∀ y, (D.matrix y).IsHermitian)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hPath : ∀ x, ∀ u ∈ Icc 0 t, (Hpath x u).IsHermitian)
    (hLip : ∀ x, ∀ u ∈ Icc 0 t, ∀ v ∈ Icc 0 t,
      ‖SparseStateOverlap.matrixOperator (Hpath x u) -
        SparseStateOverlap.matrixOperator (Hpath x v)‖ ≤ β * |u - v|)
    (hVal : ∀ x (r : Fin M), ‖SparseStateOverlap.matrixOperator (Hpath x (r * t / M)) -
      SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δ)
    (hValBudget : t * δ ≤ ε / 12) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program (oracle D γ η t ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * t) +
            Real.sqrt ((s : ℝ) * (η * t) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (input D hM γ η t ε)† ∘L input D hM γ η t ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n), U 0 = 1 →
            SolvesOn (fun u => SparseStateOverlap.matrixOperator (Hpath x u)) U 0 t →
            ∀ ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n), ‖ψ‖ = 1 →
              ‖FiniteReferenceLift.lift (p.eval x)
                  (FiniteReferenceLift.lift (input D hM γ η t ε) ψ) -
                FiniteReferenceLift.lift (input D hM γ η t ε)
                  (FiniteReferenceLift.lift (U t) ψ)‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hAction⟩ :=
    simulation D Hpath η t β δ ε hη ht hβ hε hεHalf hM hMesh hFreeze hCayley hH hrow hcol
      hPath hLip hVal hValBudget
  refine ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, fun x => ⟨(hAction x).1, ?_⟩⟩
  intro U hU0 hU ψ hψ
  simpa only [hψ, mul_one] using
    FiniteReferenceLift.same_embedding_error_le (p.eval x) (input D hM γ η t ε) (U t) ε
      ((hAction x).2 U hU0 hU) ψ

/-! ### An explicit admissible mesh -/

/-- An explicit mesh size meeting the three discretisation conditions. -/
def meshSize (s : ℕ) (η t β ε : ℝ) : ℕ :=
  ⌈4 * s * (η * t) + 9 * β * t ^ 2 / ε +
    Real.sqrt (9 * (Real.sqrt s * (η * t)) ^ 3 / ε)⌉₊ + 1

theorem meshSize_spec (s : ℕ) (η t β ε : ℝ) (hη : 0 ≤ η) (ht : 0 ≤ t) (hβ : 0 ≤ β)
    (hε : 0 < ε) :
    0 < meshSize s η t β ε ∧
      4 * s * (η * t) ≤ meshSize s η t β ε ∧
      9 * β * t ^ 2 ≤ ε * meshSize s η t β ε ∧
      9 * (Real.sqrt s * (η * t)) ^ 3 ≤ ε * (meshSize s η t β ε : ℝ) ^ 2 := by
  set A : ℝ := 4 * s * (η * t)
  set B : ℝ := 9 * β * t ^ 2 / ε
  set C : ℝ := Real.sqrt (9 * (Real.sqrt s * (η * t)) ^ 3 / ε)
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hceil := Nat.le_ceil (A + B + C)
  have hM : A + B + C ≤ meshSize s η t β ε := by
    have hcast : ((⌈A + B + C⌉₊ + 1 : ℕ) : ℝ) = (⌈A + B + C⌉₊ : ℝ) + 1 := by push_cast; ring
    change A + B + C ≤ ((⌈A + B + C⌉₊ + 1 : ℕ) : ℝ)
    rw [hcast]
    linarith
  refine ⟨Nat.succ_pos _, by linarith, ?_, ?_⟩
  · have hBle : B ≤ meshSize s η t β ε := by linarith
    have h := mul_le_mul_of_nonneg_left hBle hε.le
    have hεB : ε * B = 9 * β * t ^ 2 := by
      simp only [B]
      field_simp
    linarith
  · have hCle : C ≤ meshSize s η t β ε := by linarith
    have hsq : C ^ 2 = 9 * (Real.sqrt s * (η * t)) ^ 3 / ε := by
      simp only [C]
      rw [Real.sq_sqrt (by positivity)]
    have h2 : C ^ 2 ≤ (meshSize s η t β ε : ℝ) ^ 2 := pow_le_pow_left₀ hC hCle 2
    have h3 := mul_le_mul_of_nonneg_left h2 hε.le
    have hεC : ε * C ^ 2 = 9 * (Real.sqrt s * (η * t)) ^ 3 := by
      rw [hsq]
      field_simp
    linarith

/-! ### Zero Hamiltonian -/

/-- A zero Hamiltonian gives the identity propagator on `[0, t]`. -/
theorem zero_path_identity {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [CompleteSpace P] (U : ℝ → P →L[ℂ] P) {t : ℝ} (ht : 0 ≤ t) (hU0 : U 0 = 1)
    (hU : SolvesOn (fun _ => (0 : P →L[ℂ] P)) U 0 t) : U t = 1 := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f' := fun _ => (0 : P →L[ℂ] P))
    (C := 0) (fun u hu => by simpa using hU u hu) (fun _ _ => by simp) t ⟨ht, le_rfl⟩
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero, hU0] at h
  exact h

set_option maxRecDepth 8192 in
/-- The clean encoding of `simulation` is an isometry for all public
parameters. -/
theorem input_isometry (D : Data (X × Fin M) n Z s) (hM : 0 < M) (γ η t ε : ℝ) :
    (input D hM γ η t ε)† ∘L input D hM γ η t ε = 1 := by
  have hE := (Sampled.embedding D hM M (Sampled.degree (s : ℝ) γ (η * t) ε M)).adjoint_comp_self
  have hIn := SharpClockQuery.input_isometry (P := EuclideanSpace ℂ n)
    (V := SparseEdgeMoments.OrientedSpace n) (Sampled.step (s : ℝ) γ (η * t) M)
    (CayleyClockInterface.width (s : ℝ) γ) (CayleyClockInterface.moment γ) M (ε / 3)
    (CayleyClockInterface.width_ge_one _ _)
  exact AlignedMultiOracleProgram.input_isometry _ (Sampled.isometry_comp _ _ hE hIn)

set_option maxRecDepth 8192 in
/-- **Zero time or a zero path.** The identity program over the coherent
sampled-time oracles of `simulation` makes no queries and is exact for the
same clean encoding and every propagator of the path. -/
theorem zero_certificate (D : Data (X × Fin M) n Z s) (Hpath : X → ℝ → Matrix n n ℂ)
    (hM : 0 < M) (γ η t ε : ℝ) (ht : 0 ≤ t)
    (hZero : t = 0 ∨ ∀ x, ∀ u ∈ Icc 0 t, Hpath x u = 0) :
    (MultiOracleCircuit.Program.identity (O := oracle D γ η t ε)).count = 0 ∧
      (input D hM γ η t ε)† ∘L input D hM γ η t ε = 1 ∧
      ∀ x, IsUnitary ((MultiOracleCircuit.Program.identity (O := oracle D γ η t ε)).eval x) ∧
        ∀ U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n), U 0 = 1 →
          SolvesOn (fun u => SparseStateOverlap.matrixOperator (Hpath x u)) U 0 t →
          ‖(MultiOracleCircuit.Program.identity (O := oracle D γ η t ε)).eval x ∘L
              input D hM γ η t ε - input D hM γ η t ε ∘L U t‖ = 0 := by
  refine ⟨MultiOracleCircuit.Program.count_identity, input_isometry D hM γ η t ε,
    fun x => ⟨?_, fun U hU0 hU => ?_⟩⟩
  · rw [MultiOracleCircuit.Program.eval_identity]
    exact isUnitary_one
  · have hUt : U t = 1 := by
      rcases hZero with h0 | hpath
      · rw [h0, hU0]
      · apply zero_path_identity U ht hU0
        intro u hu
        have h := hU u hu
        simp only [hpath x u hu, NativeZeroSimulation.matrixOperator_zero] at h
        simpa using h
    rw [hUt, MultiOracleCircuit.Program.eval_identity, sub_eq_zero.mpr, norm_zero]
    rfl

end

end SparseHamiltonian.TimeDependent
