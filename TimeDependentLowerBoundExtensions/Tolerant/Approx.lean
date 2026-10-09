import TimeDependentLowerBoundExtensions.Core.Masked

set_option autoImplicit false

/-!
# Approximate implementations: inverses and masked calls

Operator facts used to add up the errors of approximately realised calls (the manuscript's gate
model, lines 1805-1812, with the ancilla convention of lines 511-533: an implementation `A` of
`B` on an isometric encoding `e` has error `‖A ∘ e - e ∘ B‖`).

* `approx_adjoint`: for unitaries, the inverse of an implementation within `ξ` implements the
  inverse within `ξ` (the approximate form of `EncodedOracle.adjoint_intertwines`);
* `masked_approx`: executing an implementation within `ξ` only in the branches of a fixed mask of
  a branch register (`SparseHamiltonian.MaskedProgram.masked`) gives an implementation of the
  masked operation within `ξ` on the branchwise encoding
  (`SparseLowerBounds.Adaptive.Access.jointMap`);
* `approx_comp_encoding`: errors add up through an isometric encoding;
* `controlOne`, `approx_of_controlled`: an implementation within `ξ` of the controlled operation
  `|0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ B` (`masked (fun b => b) B` on `ℂ² ⊗ Q`) restricts, on the control-one
  branch `v ↦ |1⟩ ⊗ v`, to an implementation of `B` within `ξ` on an isometric encoding
  (`comp_controlOne_isometry`).
-/

namespace TimeDependentLowerBoundExtensions.Tolerant

noncomputable section

open SparseHamiltonian OracleCircuit
open SparseLowerBounds
open SparseLowerBounds.Adaptive.Access (jointMap)
open scoped InnerProduct InnerProductSpace

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- **Approximate intertwining of inverses**: for unitaries `U` and `F` and any `E`, if
`‖U ∘ E - E ∘ F‖ ≤ ξ` then `‖U† ∘ E - E ∘ F†‖ ≤ ξ` (the approximate form of
`EncodedOracle.adjoint_intertwines`; `U† E - E F† = U† (E F - U E) F†`). Its configuration-form
analogue, for operators on one register, is `SparseHamiltonian.GateNative.ApproxOn.adjoint`. -/
theorem approx_adjoint {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
    [CompleteSpace Q] (U : W →L[ℂ] W) (F : Q →L[ℂ] Q) (E : Q →L[ℂ] W) (hU : IsUnitary U)
    (hF : IsUnitary F) {ξ : ℝ} (h : ‖U ∘L E - E ∘L F‖ ≤ ξ) :
    ‖U† ∘L E - E ∘L F†‖ ≤ ξ := by
  have h1 : U† ∘L U = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hU.1
  have h2 : F ∘L F† = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hF.2
  have key : U† ∘L E - E ∘L F† = U† ∘L (E ∘L F - U ∘L E) ∘L F† := by
    have h1' : ∀ x, (U†) (U x) = x := fun x => by
      simpa using DFunLike.congr_fun h1 x
    have h2' : ∀ y, F ((F†) y) = y := fun y => by
      simpa using DFunLike.congr_fun h2 y
    ext v
    simp [h1', h2']
  have hUa : ‖U†‖ ≤ 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hU.adjoint.norm_le_one
  have hFa : ‖F†‖ ≤ 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hF.adjoint.norm_le_one
  rw [key]
  calc ‖U† ∘L (E ∘L F - U ∘L E) ∘L F†‖
      ≤ ‖U†‖ * (‖E ∘L F - U ∘L E‖ * ‖F†‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖E ∘L F - U ∘L E‖ * 1) := by gcongr
    _ = ‖U ∘L E - E ∘L F‖ := by rw [one_mul, mul_one, norm_sub_rev]
    _ ≤ ξ := h

omit [CompleteSpace W] in
/-- **Masking preserves approximate implementations**: if `‖A ∘ e - e ∘ B‖ ≤ ξ`, then for every
mask `msk` of a branch register `ι`,
`‖masked msk A ∘ jointMap ι e - jointMap ι e ∘ masked msk B‖ ≤ ξ` (the difference is
`A ∘ e - e ∘ B` on the active branches and `0` on the others). -/
theorem masked_approx {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
    [CompleteSpace Q] (ι : Type*) [Fintype ι] (msk : ι → Bool) (A : W →L[ℂ] W)
    (B : Q →L[ℂ] Q) (e : Q →L[ℂ] W) {ξ : ℝ} (h : ‖A ∘L e - e ∘L B‖ ≤ ξ) :
    ‖MaskedProgram.masked msk A ∘L jointMap ι e - jointMap ι e ∘L MaskedProgram.masked msk B‖
      ≤ ξ := by
  have hξ : 0 ≤ ξ := (norm_nonneg _).trans h
  refine ContinuousLinearMap.opNorm_le_bound _ hξ fun Ψ => ?_
  have hb : ∀ i, ‖(MaskedProgram.masked msk A ∘L jointMap ι e -
      jointMap ι e ∘L MaskedProgram.masked msk B) Ψ i‖ ≤ ξ * ‖Ψ i‖ := by
    intro i
    cases hm : msk i
    · simpa [hm, SparseLowerBounds.Adaptive.Access.jointMap_apply] using
        mul_nonneg hξ (norm_nonneg (Ψ i))
    · simpa [hm, SparseLowerBounds.Adaptive.Access.jointMap_apply] using
        (A ∘L e - e ∘L B).le_of_opNorm_le h (Ψ i)
  have hsq : ‖(MaskedProgram.masked msk A ∘L jointMap ι e -
      jointMap ι e ∘L MaskedProgram.masked msk B) Ψ‖ ^ 2 ≤ (ξ * ‖Ψ‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb i) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hξ (norm_nonneg _))
    two_ne_zero).1 hsq

/-- **Errors add up through an encoding**: if `A` implements `B` within `a` on an isometric
encoding `E` (`‖A ∘ E - E ∘ B‖ ≤ a`) and `B` implements `C` within `b` on an isometric
encoding `ι`, then `A` implements `C` within `a + b` on `E ∘ ι`. -/
theorem approx_comp_encoding {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : W →L[ℂ] W) (E : K →L[ℂ] W) (hE : E† ∘L E = 1) (B : K →L[ℂ] K) (ι : H →L[ℂ] K)
    (hι : ι† ∘L ι = 1) (C : H →L[ℂ] H) {a b : ℝ} (h₁ : ‖A ∘L E - E ∘L B‖ ≤ a)
    (h₂ : ‖B ∘L ι - ι ∘L C‖ ≤ b) :
    ‖A ∘L (E ∘L ι) - (E ∘L ι) ∘L C‖ ≤ a + b := by
  have heq : A ∘L (E ∘L ι) - (E ∘L ι) ∘L C =
      (A ∘L E - E ∘L B) ∘L ι + E ∘L (B ∘L ι - ι ∘L C) := by
    simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.comp_assoc]
    abel
  have hι1 : ‖ι‖ ≤ 1 := by
    have h := EncodedOracle.norm_comp_eq ι hι (1 : H →L[ℂ] H)
    rw [ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id] at h
    rw [h]
    exact ContinuousLinearMap.norm_id_le
  rw [heq]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) hι1)).trans h₁
  · rw [EncodedOracle.norm_comp_eq E hE]
    exact h₂

/-- **The control-one injection** `v ↦ |1⟩ ⊗ v` of `Q` into `ℂ² ⊗ Q` (`Joint Bool Q`). It is
the `|1⟩`-branch counterpart of `TimeDependentHamiltonianLowerBound.boolEmbed` (branch `false`):
the controlled private operation acts on the active branch `true`. -/
def controlOne (Q : Type*) [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] :
    Q →L[ℂ] Joint Bool Q :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Bool => Q)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : Bool => Q) true

/-- The control-one injection is an isometry. -/
theorem controlOne_isometry (Q : Type*) [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
    [CompleteSpace Q] : (controlOne Q)† ∘L controlOne Q = 1 := by
  ext1 v
  refine ext_inner_left ℂ fun w => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  simp only [controlOne, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    PiLp.inner_apply]
  rw [Fintype.sum_eq_single true (fun i hi => by simp [hi])]
  simp

/-- The controlled operation `masked (fun b => b) B` acts on the control-one branch by `B`. -/
theorem masked_comp_controlOne {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
    (B : Q →L[ℂ] Q) :
    MaskedProgram.masked (fun b : Bool => b) B ∘L controlOne Q = controlOne Q ∘L B := by
  ext1 v
  refine PiLp.ext fun i => ?_
  cases i <;> simp [controlOne]

/-- The encoding `E ∘ controlOne Q` of an isometric `E` of `ℂ² ⊗ Q` is an isometry. -/
theorem comp_controlOne_isometry {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
    [CompleteSpace Q] (E : Joint Bool Q →L[ℂ] W) (hE : E† ∘L E = 1) :
    (E ∘L controlOne Q)† ∘L (E ∘L controlOne Q) = 1 := by
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc (ContinuousLinearMap.adjoint E), hE,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, controlOne_isometry]

omit [CompleteSpace W] in
/-- **Controlled implementations restrict to the bare operation**: if `A` implements the
controlled operation `|0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ B` (`masked (fun b => b) B`) within `ξ` on an
encoding `E` of `ℂ² ⊗ Q`, then `A` implements `B` within `ξ` on the encoding `E ∘ controlOne Q`,
isometric when `E` is (`comp_controlOne_isometry`). -/
theorem approx_of_controlled {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
    [CompleteSpace Q] (A : W →L[ℂ] W) (E : Joint Bool Q →L[ℂ] W)
    (B : Q →L[ℂ] Q) {ξ : ℝ}
    (h : ‖A ∘L E - E ∘L MaskedProgram.masked (fun b : Bool => b) B‖ ≤ ξ) :
    ‖A ∘L (E ∘L controlOne Q) - (E ∘L controlOne Q) ∘L B‖ ≤ ξ := by
  have heq : A ∘L (E ∘L controlOne Q) - (E ∘L controlOne Q) ∘L B =
      (A ∘L E - E ∘L MaskedProgram.masked (fun b : Bool => b) B) ∘L controlOne Q := by
    simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc,
      masked_comp_controlOne]
  have hc1 : ‖controlOne Q‖ ≤ 1 := by
    have h1 := EncodedOracle.norm_comp_eq (controlOne Q) (controlOne_isometry Q)
      (1 : Q →L[ℂ] Q)
    rw [ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id] at h1
    rw [h1]
    exact ContinuousLinearMap.norm_id_le
  rw [heq]
  exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) hc1)).trans h

end

end TimeDependentLowerBoundExtensions.Tolerant
