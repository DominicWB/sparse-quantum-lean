import TimeDependentHamiltonian.Corollaries
import ZeroTimeRemarks.Hamiltonian

/-!
# Theorem `hs:thm:time` at zero time or zero norm bound (uniform meshes)

Theorem `hs:thm:time` of the accompanying paper ends with "Zero time or a known zero
Hamiltonian requires no matrix queries." For the released uniform-mesh endpoint
`SparseHamiltonian.TimeDependent.simulation` (which assumes `η > 0`), the released
`TimeDependent.zero_certificate` already gives the identity program over the same coherent
sampled-time oracles for `t = 0` or a path that vanishes on `[0, t]`. This file adds the
remaining case of a public bound `η = 0` and the combined statement.

* `evolution_one`: the ordered product of identities is the identity.
* `isometry_norm_le_one`, `identity_error_le`: the identity program changes the clean
  output by at most `‖U(t) - 1‖`.
* `zero_bound`: if the public row bound is `η = 0`, every represented sample vanishes, the
  path is within `δ` of zero at the mesh points, and the identity program over
  `TimeDependent.oracle D γ η t ε` (no query) has full-output error at most `β t² / M + t δ`
  for every propagator, by the released discretisation estimate `TimeDependent.mesh_error`;
  `freeze_value_le`: under the released mesh conditions `9 β t² ≤ ε M` and `t δ ≤ ε / 12`
  this is at most `ε`.
* `simulation_nonneg`: Theorem `hs:thm:time` on uniform meshes for every `η ≥ 0`, with at
  most `0` queries if `t = 0` or `η = 0` and the released bound otherwise;
  `simulation_with_reference_nonneg`: the same bound with an untouched finite reference.
-/

set_option autoImplicit false

namespace SparseHamiltonian.ZeroTimeRemarks.TimeUniform

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding TimeDependent Set
open scoped BigOperators InnerProduct
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096

section Generic

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

omit [CompleteSpace P] in
/-- The ordered product of `n` identities is the identity (`hs:thm:time`). -/
theorem evolution_one (k : ℕ) : evolution (fun _ => (1 : P →L[ℂ] P)) k = 1 := by
  induction k with
  | zero => exact evolution_zero _
  | succ k ih => rw [evolution_succ, ih, one_mul]

/-- An isometric encoding has operator norm at most one (`hs:thm:time`). -/
theorem isometry_norm_le_one {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
    [CompleteSpace Q] (ι : P →L[ℂ] Q) (hι : ι† ∘L ι = 1) : ‖ι‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  rw [(ι.norm_map_iff_adjoint_comp_self.mpr hι) v, one_mul]

/-- The identity program changes an isometrically encoded output by at most `‖V - 1‖`:
`‖1 ∘ ι - ι ∘ V‖ ≤ ‖V - 1‖` (`hs:thm:time`). -/
theorem identity_error_le {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
    [CompleteSpace Q] (ι : P →L[ℂ] Q) (hι : ι† ∘L ι = 1) (V : P →L[ℂ] P) :
    ‖(1 : Q →L[ℂ] Q) ∘L ι - ι ∘L V‖ ≤ ‖V - 1‖ := by
  have h : (1 : Q →L[ℂ] Q) ∘L ι - ι ∘L V = ι ∘L (1 - V) := by
    ext v
    simp only [sub_apply, comp_apply, one_apply_eq_self, map_sub]
  rw [h]
  calc
    ‖ι ∘L (1 - V)‖ ≤ ‖ι‖ * ‖1 - V‖ := opNorm_comp_le _ _
    _ ≤ 1 * ‖1 - V‖ := mul_le_mul_of_nonneg_right (isometry_norm_le_one ι hι) (norm_nonneg _)
    _ = ‖V - 1‖ := by rw [one_mul, norm_sub_rev]

end Generic

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- **Theorem `hs:thm:time` with the public bound `η = 0`.** The row promise with `η = 0`
forces every represented sample to vanish. For every public rescaling `γ`, the identity
program over the coherent sampled-time oracles `TimeDependent.oracle D γ η t ε` makes no
query, the clean encoding is an isometry, and for every instance and every propagator `U` of
the path (`U 0 = 1`, `SolvesOn` on `[0, t]`) the full output is within `β t² / M + t δ` of the
clean evolved state, by the released discretisation estimate `TimeDependent.mesh_error` with
zero samples. No mesh condition is needed; under the released ones the bound is at most `ε`
(`freeze_value_le`). -/
theorem zero_bound (D : Data (X × Fin M) n Z s) (Hpath : X → ℝ → Matrix n n ℂ)
    (γ η t β δ ε : ℝ) (hη : η = 0) (ht : 0 ≤ t) (hβ : 0 ≤ β) (hM : 0 < M)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hPath : ∀ x, ∀ u ∈ Icc 0 t, (Hpath x u).IsHermitian)
    (hLip : ∀ x, ∀ u ∈ Icc 0 t, ∀ v ∈ Icc 0 t,
      ‖SparseStateOverlap.matrixOperator (Hpath x u) -
        SparseStateOverlap.matrixOperator (Hpath x v)‖ ≤ β * |u - v|)
    (hVal : ∀ x (r : Fin M), ‖SparseStateOverlap.matrixOperator (Hpath x (r * t / M)) -
      SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δ) :
    (MultiOracleCircuit.Program.identity (O := oracle D γ η t ε)).count = 0 ∧
      (input D hM γ η t ε)† ∘L input D hM γ η t ε = 1 ∧
      ∀ x, IsUnitary ((MultiOracleCircuit.Program.identity (O := oracle D γ η t ε)).eval x) ∧
        ∀ U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n), U 0 = 1 →
          SolvesOn (fun u => SparseStateOverlap.matrixOperator (Hpath x u)) U 0 t →
          ‖(MultiOracleCircuit.Program.identity (O := oracle D γ η t ε)).eval x ∘L
              input D hM γ η t ε - input D hM γ η t ε ∘L U t‖ ≤ β * t ^ 2 / M + t * δ := by
  have hZero : ∀ y, D.matrix y = 0 := by
    apply NativeZeroSimulation.matrix_zero_of_energy D
    intro y i
    simpa only [hη, zero_pow (by norm_num : 2 ≠ 0)] using hrow y i
  refine ⟨MultiOracleCircuit.Program.count_identity, input_isometry D hM γ η t ε,
    fun x => ⟨?_, fun U hU0 hU => ?_⟩⟩
  · rw [MultiOracleCircuit.Program.eval_identity]
    exact isUnitary_one
  · have hMesh := mesh_error (H := fun u => SparseStateOverlap.matrixOperator (Hpath x u))
      (U := U) (fun _ => (0 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)) hM ht hβ hU0 hU
      (fun u hu => SparseValuePrecision.matrixOperator_star_eq _ (hPath x u hu))
      (fun _ => star_zero _) (hLip x)
      (fun k hk => by
        have h := hVal x ⟨k, hk⟩
        rw [hZero, NativeZeroSimulation.matrixOperator_zero] at h
        simpa using h)
    have hOne : evolution (fun _ => NormedSpace.exp ((-Complex.I * ((t / M : ℝ) : ℂ)) •
        (0 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n))) M = 1 := by
      have h1 : NormedSpace.exp ((-Complex.I * ((t / M : ℝ) : ℂ)) •
          (0 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)) = 1 :=
        Hamiltonian.exp_eq_one (t / M) 0 (Or.inr rfl)
      rw [h1]
      exact evolution_one M
    rw [hOne] at hMesh
    rw [MultiOracleCircuit.Program.eval_identity]
    exact (identity_error_le _ (input_isometry D hM γ η t ε) (U t)).trans hMesh

/-- Under the released mesh conditions `9 β t² ≤ ε M` and `t δ ≤ ε / 12`, the discretisation
bound of `zero_bound` is at most `ε`: `β t² / M + t δ ≤ ε` (`hs:thm:time`). -/
theorem freeze_value_le (t β δ ε : ℝ) (hM : 0 < M) (hFreeze : 9 * β * t ^ 2 ≤ ε * M)
    (hβ : 0 ≤ β) (hValBudget : t * δ ≤ ε / 12) : β * t ^ 2 / M + t * δ ≤ ε := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hFr : β * t ^ 2 / M ≤ ε / 9 := by
    rw [div_le_iff₀ hMR]
    linarith
  have hε : 0 ≤ ε := by
    have h1 : 0 ≤ 9 * β * t ^ 2 := by positivity
    nlinarith
  linarith

/-- **Theorem `hs:thm:time` on uniform meshes for every `η ≥ 0`.** Under the hypotheses of
the released `TimeDependent.simulation` with `0 ≤ η` in place of `0 < η`, there are an
admissible rescaling `γ` and one program over the coherent sampled-time oracles
`TimeDependent.oracle D γ η t ε`, uniform over the instances, with at most `0` queries if
`t = 0` or `η = 0` and at most `995328 (√s τ + √(s τ log(1/ε)) + log(1/ε))`, `τ = η t`,
otherwise; the clean encoding is an isometry, and for every instance and every propagator of
the path the full output is within `ε` of the clean evolved state. For `t = 0` this is the
released `TimeDependent.zero_certificate`, for `η = 0` it is `zero_bound` with
`freeze_value_le`. -/
theorem simulation_nonneg (D : Data (X × Fin M) n Z s) (Hpath : X → ℝ → Matrix n n ℂ)
    (η t β δ ε : ℝ) (hη : 0 ≤ η) (ht : 0 ≤ t) (hβ : 0 ≤ β) (hε : 0 < ε)
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
        (p.count : ℝ) ≤ (if t = 0 ∨ η = 0 then 0 else 995328 *
          (Real.sqrt (s : ℝ) * (η * t) +
            Real.sqrt ((s : ℝ) * (η * t) * Real.log (1 / ε)) + Real.log (1 / ε))) ∧
        (input D hM γ η t ε)† ∘L input D hM γ η t ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n), U 0 = 1 →
            SolvesOn (fun u => SparseStateOverlap.matrixOperator (Hpath x u)) U 0 t →
            ‖p.eval x ∘L input D hM γ η t ε - input D hM γ η t ε ∘L U t‖ ≤ ε := by
  obtain ⟨h0, h1, hs⟩ := Hamiltonian.one_admissible (Z := Z) D
  by_cases hη0 : η = 0
  · obtain ⟨hc, hIn, hAct⟩ := zero_bound D Hpath 1 η t β δ ε hη0 ht hβ hM hrow hPath hLip hVal
    have hle := freeze_value_le t β δ ε hM hFreeze hβ hValBudget
    refine ⟨1, h0, h1, hs, MultiOracleCircuit.Program.identity, ?_, hIn,
      fun x => ⟨(hAct x).1, fun U hU0 hU => ((hAct x).2 U hU0 hU).trans hle⟩⟩
    rw [if_pos (Or.inr hη0), hc, Nat.cast_zero]
  · by_cases ht0 : t = 0
    · obtain ⟨hc, hIn, hAct⟩ := zero_certificate D Hpath hM 1 η t ε ht (Or.inl ht0)
      refine ⟨1, h0, h1, hs, MultiOracleCircuit.Program.identity, ?_, hIn,
        fun x => ⟨(hAct x).1, fun U hU0 hU => ?_⟩⟩
      · rw [if_pos (Or.inl ht0), hc, Nat.cast_zero]
      · rw [(hAct x).2 U hU0 hU]
        exact hε.le
    · have hηpos : 0 < η := lt_of_le_of_ne hη (Ne.symm hη0)
      obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hAct⟩ := simulation D Hpath η t β δ ε
        hηpos ht hβ hε hεHalf hM hMesh hFreeze hCayley hH hrow hcol hPath hLip hVal hValBudget
      refine ⟨γ, hγ, hγOne, hWidth, p, ?_, hIn, hAct⟩
      rw [if_neg (fun h => h.elim ht0 hη0)]
      exact hCount

/-- **Theorem `hs:thm:time` on uniform meshes for every `η ≥ 0`, with an untouched
reference.** The program and clean encoding of `simulation_nonneg` obey the same full-output
bound `ε` on every normalised input entangled with an untouched finite reference register, as
in the released `TimeDependent.simulation_with_reference`. -/
theorem simulation_with_reference_nonneg {R : Type*} [Fintype R]
    (D : Data (X × Fin M) n Z s) (Hpath : X → ℝ → Matrix n n ℂ)
    (η t β δ ε : ℝ) (hη : 0 ≤ η) (ht : 0 ≤ t) (hβ : 0 ≤ β) (hε : 0 < ε)
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
        (p.count : ℝ) ≤ (if t = 0 ∨ η = 0 then 0 else 995328 *
          (Real.sqrt (s : ℝ) * (η * t) +
            Real.sqrt ((s : ℝ) * (η * t) * Real.log (1 / ε)) + Real.log (1 / ε))) ∧
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
    simulation_nonneg D Hpath η t β δ ε hη ht hβ hε hεHalf hM hMesh hFreeze hCayley hH hrow
      hcol hPath hLip hVal hValBudget
  refine ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, fun x => ⟨(hAction x).1, ?_⟩⟩
  intro U hU0 hU ψ hψ
  simpa only [hψ, mul_one] using
    FiniteReferenceLift.same_embedding_error_le (p.eval x) (input D hM γ η t ε) (U t) ε
      ((hAction x).2 U hU0 hU) ψ

end
end SparseHamiltonian.ZeroTimeRemarks.TimeUniform
