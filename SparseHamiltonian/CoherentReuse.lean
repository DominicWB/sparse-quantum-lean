import SparseHamiltonian.GlobalExit

/-!
# Coherent reuse on a finite Hilbert sum

A copy of the public input occupies each of `n` normalized time slots. The
shared private register starts at zero and is carried between successive local
colligations. The successful public block is the actual uniform compression of
this finite chronological construction, not an assumed reuse formula.
-/

namespace SparseHamiltonian.CoherentReuse

noncomputable section

open ContinuousLinearMap
open ChronologicalResolvent FiniteChronologicalInverse
open scoped BigOperators InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The real amplitude of each occupied time slot. -/
def uniformAmplitude (n : ℕ) : ℝ := (Real.sqrt (n : ℝ))⁻¹

theorem uniformAmplitude_sq (n : ℕ) : uniformAmplitude n ^ 2 = (n : ℝ)⁻¹ := by
  rw [uniformAmplitude, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

theorem uniformAmplitude_complex_sq (n : ℕ) :
    (uniformAmplitude n : ℂ) * (uniformAmplitude n : ℂ) = (n : ℂ)⁻¹ := by
  rw [← Complex.ofReal_mul, ← pow_two, uniformAmplitude_sq, Complex.ofReal_inv,
    Complex.ofReal_natCast]

/-- Prepare the normalized uniform superposition of public time slots. -/
def uniformEmbedding (n : ℕ) : P →L[ℂ] BlockOperator.H n P :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => P)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun _ : Fin n => (uniformAmplitude n : ℂ) • (1 : P →L[ℂ] P))

omit [CompleteSpace P] in
@[simp] theorem uniformEmbedding_apply (n : ℕ) (p : P) (r : Fin n) :
    uniformEmbedding n p r = (uniformAmplitude n : ℂ) • p := rfl

omit [CompleteSpace P] in
/-- The uniform preparation preserves norms whenever at least one slot exists. -/
theorem uniformEmbedding_norm (n : ℕ) (hn : n ≠ 0) (p : P) :
    ‖uniformEmbedding n p‖ = ‖p‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [uniformEmbedding_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ uniformAmplitude n by unfold uniformAmplitude; positivity),
    mul_pow, uniformAmplitude_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn), one_mul]

/-- Uniform postselection is the genuine adjoint of uniform preparation. -/
theorem uniformEmbedding_adjoint_apply (n : ℕ) (x : BlockOperator.H n P) :
    ((uniformEmbedding n)†) x = ∑ r : Fin n, (uniformAmplitude n : ℂ) • x r := by
  apply ext_inner_right ℂ
  intro p
  simp only [adjoint_inner_left, PiLp.inner_apply, uniformEmbedding_apply,
    sum_inner, inner_smul_left, inner_smul_right, Complex.conj_ofReal]

/-- Preparing and postselecting the uniform clock acts as the identity. -/
theorem uniformEmbedding_adjoint_comp (n : ℕ) (hn : n ≠ 0) :
    (uniformEmbedding n : P →L[ℂ] BlockOperator.H n P)† ∘L uniformEmbedding n = 1 := by
  ext p
  simp only [comp_apply, uniformEmbedding_adjoint_apply, uniformEmbedding_apply,
    smul_smul, uniformAmplitude_complex_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn), one_smul]
  rfl

/-- The actual public output slots after chronological reuse, with private
initial state zero. Here the shared and slot roles of the chronology are swapped. -/
def publicReuse (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) (n : ℕ) :
    BlockOperator.H n P →L[ℂ] BlockOperator.H n P :=
  chronologicalOperator A B D C n

/-- The successful block obtained by preparing and postselecting uniform slots. -/
def successfulBlock (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) (n : ℕ) : P →L[ℂ] P :=
  (uniformEmbedding n)† ∘L publicReuse A B C D n ∘L uniformEmbedding n

omit [CompleteSpace P] [CompleteSpace V] in
/-- Solving the actual shared private recurrence on constant public input. -/
theorem sharedPrivate_constant (C Γ : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hPrivate : C + D ∘L Γ = Γ) (p : P) (a : ℂ) (r : ℕ) :
    forcedPublicState D C (fun _ => a • p) r =
      a • (Γ p - (D ^ r) (Γ p)) := by
  induction r with
  | zero => simp
  | succ r hr =>
      have hc := congrArg (fun L : P →L[ℂ] V => L p) hPrivate
      simp only [add_apply, comp_apply] at hc
      rw [forcedPublicState_succ, hr, map_smul, map_smul, ← smul_add,
        pow_succ', mul_apply_eq_comp, map_sub]
      congr 1
      calc
        D (Γ p) - D ((D ^ r) (Γ p)) + C p =
            (C p + D (Γ p)) - D ((D ^ r) (Γ p)) := by abel
        _ = Γ p - D ((D ^ r) (Γ p)) := by rw [hc]

omit [CompleteSpace P] [CompleteSpace V] in
/-- Each public output slot is the ideal output minus a propagated private
boundary term; the formula follows from the shared private recurrence. -/
theorem publicReuse_uniform_apply (A U : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C Γ : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hPublic : A + B ∘L Γ = U) (hPrivate : C + D ∘L Γ = Γ)
    (n : ℕ) (p : P) (r : Fin n) :
    publicReuse A B C D n (uniformEmbedding n p) r =
      (uniformAmplitude n : ℂ) • (U p - B ((D ^ (r : ℕ)) (Γ p))) := by
  change chronologicalOperator A B D C n
    (WithLp.toLp 2 (fun _ : Fin n => (uniformAmplitude n : ℂ) • p)) r = _
  rw [chronologicalOperator_apply A B D C
    (fun _ => (uniformAmplitude n : ℂ) • p) r]
  unfold chronologicalPrivateState
  rw [sharedPrivate_constant C Γ D hPrivate]
  have hp := congrArg (fun L : P →L[ℂ] P => L p) hPublic
  simp only [add_apply, comp_apply] at hp
  simp only [map_smul, map_sub, ← smul_add]
  congr 1
  rw [← hp]
  abel

omit [CompleteSpace V] in
/-- The uniform compression of the implemented reuse construction is exactly
`U - B g_n(D) Γ`, with the genuine complex operator average. -/
theorem successfulBlock_eq (A U : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C Γ : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hPublic : A + B ∘L Γ = U) (hPrivate : C + D ∘L Γ = Γ)
    (n : ℕ) (hn : n ≠ 0) :
    successfulBlock A B C D n = U - B ∘L averagedGeometricFilter D n ∘L Γ := by
  ext p
  simp only [successfulBlock, comp_apply, uniformEmbedding_adjoint_apply,
    publicReuse_uniform_apply A U B C Γ D hPublic hPrivate, smul_smul,
    uniformAmplitude_complex_sq, sub_apply]
  rw [← Finset.smul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (Nat.cast_ne_zero.mpr hn)]
  congr 1
  simp only [averagedGeometricFilter, smul_apply, map_smul, sum_apply, map_sum]
  rw [Fin.sum_univ_eq_sum_range (fun r => B ((D ^ r) (Γ p))) n]

omit [CompleteSpace P] [CompleteSpace V] in
/-- The implementation conserves public-slot plus final private energy under
the local colligation energy identity. -/
theorem publicReuse_energy (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2)
    (n : ℕ) (x : BlockOperator.H n P) :
    ‖publicReuse A B C D n x‖ ^ 2 +
      ‖forcedPublicState D C (extendSequence x) n‖ ^ 2 = ‖x‖ ^ 2 :=
  ChronologicalContraction.chronologicalOperator_energy A B D C hStep n x

omit [CompleteSpace P] [CompleteSpace V] in
/-- In particular the actual public output of the reuse circuit is contractive. -/
theorem publicReuse_norm_le_one (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2)
    (n : ℕ) : ‖publicReuse A B C D n‖ ≤ 1 :=
  ChronologicalContraction.chronologicalOperator_norm_le_one A B D C hStep n

end

end SparseHamiltonian.CoherentReuse
