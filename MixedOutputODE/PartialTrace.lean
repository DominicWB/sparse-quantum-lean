import MixedOutputODE.TraceNorm
import GeneralODE.Block.Registers

/-!
# Partial trace over a retained work register

A solver may keep a finite work register `W` (its work and measurement
records). Its outputs live in `EuclideanSpace ℂ (n × W)`; discarding `W` is
the partial trace `ptrace X = ∑_w ⟨w| X |w⟩` (`slot w` is `v ↦ v ⊗ |w⟩`).
An operator `V` acting on the first factor gives `V ⊗ 1` (`tensorLeft`).

The partial trace commutes with operators on the first factor
(`ptrace_conj`), sends pure states to ensembles of their slices
(`ptrace_pure`), preserves the trace (`tr_ptrace`) and positivity
(`ptrace_isPositive`), and so sends density operators to density operators
(`ptrace_isDensity`).
-/

namespace SparseHamiltonian.MixedOutputODE

noncomputable section
open ContinuousLinearMap ODEMixedOutput InnerProductSpace GeneralODE.Registers
open scoped InnerProduct BigOperators ComplexConjugate

variable {n s W : Type*} [Fintype n] [Fintype s] [Fintype W] [DecidableEq W]

/-- `v ↦ v ⊗ |w⟩`. -/
def slot (w : W) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ (n × W) :=
  ketR (EuclideanSpace.single w 1)

theorem slot_adjoint_apply (w w' : W) (v : EuclideanSpace ℂ n) :
    ((slot w)†) (slot (n := n) w' v) = if w = w' then v else 0 := by
  rw [slot, slot, ketR_adjoint, braR_ketR, EuclideanSpace.inner_single_left,
    PiLp.single_apply]
  split_ifs <;> simp

theorem slot_adjoint_comp_slot (w w' : W) :
    (slot (n := n) w)† ∘L slot w' = if w = w' then 1 else 0 := by
  ext1 v
  rw [comp_apply, slot_adjoint_apply]
  split_ifs <;> simp

/-- Resolution of the identity on `n × W`. -/
theorem sum_slot_comp_adjoint :
    ∑ w : W, slot (n := n) w ∘L (slot w)† = 1 := by
  ext z p
  rcases p with ⟨i, w'⟩
  simp only [sum_apply, comp_apply, slot, ketR_adjoint, ketR_apply, braR_apply,
    PiLp.single_apply, one_apply_eq_self, WithLp.ofLp_sum, Finset.sum_apply]
  simp [apply_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- The partial trace over the right factor. -/
def ptrace (X : EuclideanSpace ℂ (n × W) →L[ℂ] EuclideanSpace ℂ (n × W)) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  ∑ w, (slot w)† ∘L X ∘L slot w

/-- `V ⊗ 1` on `n × W`. -/
def tensorLeft (V : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ s) :
    EuclideanSpace ℂ (n × W) →L[ℂ] EuclideanSpace ℂ (s × W) :=
  ∑ w, slot w ∘L V ∘L (slot w)†

theorem tensorLeft_slot (V : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ s) (w : W) :
    tensorLeft V ∘L slot w = slot w ∘L V := by
  rw [tensorLeft, finsetSum_comp, Finset.sum_eq_single w]
  · rw [comp_assoc, comp_assoc, slot_adjoint_comp_slot, if_pos rfl, one_def, comp_id]
  · intro w' _ hw'
    rw [comp_assoc, comp_assoc, slot_adjoint_comp_slot, if_neg hw', comp_zero, comp_zero]
  · intro h
    exact absurd (Finset.mem_univ w) h

theorem adjoint_tensorLeft (V : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ s) :
    (tensorLeft (W := W) V)† = tensorLeft (V†) := by
  rw [tensorLeft, tensorLeft, map_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [adjoint_comp, adjoint_comp, adjoint_adjoint, comp_assoc]

theorem slot_adjoint_tensorLeft (V : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ s) (w : W) :
    (slot w)† ∘L tensorLeft V = V ∘L (slot w)† := by
  have h := congrArg ContinuousLinearMap.adjoint (tensorLeft_slot (W := W) (V†) w)
  rw [adjoint_comp, adjoint_comp, adjoint_tensorLeft, adjoint_adjoint] at h
  exact h

theorem tensorLeft_isometry (V : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ s)
    (hV : V† ∘L V = 1) : (tensorLeft (W := W) V)† ∘L tensorLeft V = 1 := by
  rw [adjoint_tensorLeft, tensorLeft, finsetSum_comp, ← sum_slot_comp_adjoint (n := n) (W := W)]
  apply Finset.sum_congr rfl
  intro w _
  rw [comp_assoc, comp_assoc, slot_adjoint_tensorLeft, ← comp_assoc (V†), hV, one_def, id_comp]

/-- The partial trace commutes with operators on the first factor. -/
theorem ptrace_conj (V : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ s)
    (X : EuclideanSpace ℂ (s × W) →L[ℂ] EuclideanSpace ℂ (s × W)) :
    ptrace ((tensorLeft V)† ∘L X ∘L tensorLeft V) = V† ∘L ptrace X ∘L V := by
  rw [ptrace, ptrace, finsetSum_comp, comp_finsetSum]
  apply Finset.sum_congr rfl
  intro w _
  have h1 : (slot (n := n) w)† ∘L (tensorLeft V)† = V† ∘L (slot w)† := by
    rw [adjoint_tensorLeft, slot_adjoint_tensorLeft]
  calc
    (slot w)† ∘L ((tensorLeft V)† ∘L X ∘L tensorLeft V) ∘L slot w =
        ((slot (n := n) w)† ∘L (tensorLeft V)†) ∘L X ∘L (tensorLeft V ∘L slot w) := by
      simp only [comp_assoc]
    _ = (V† ∘L (slot w)†) ∘L X ∘L (slot w ∘L V) := by rw [h1, tensorLeft_slot]
    _ = V† ∘L ((slot w)† ∘L X ∘L slot w) ∘L V := by simp only [comp_assoc]

omit [Fintype n] [Fintype s] [Fintype W] [DecidableEq W] in
/-- A pure state transported by an adjoint. -/
theorem pureOperator_adjoint_apply {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (L : F →L[ℂ] E) (z : E) :
    pureOperator ((L†) z) = L† ∘L pureOperator z ∘L L := by
  unfold pureOperator
  rw [InnerProductSpace.rankOne_comp, ← comp_rankOne]

/-- The partial trace of a pure state is the ensemble of its slices. -/
theorem ptrace_pure (z : EuclideanSpace ℂ (n × W)) :
    ptrace (pureOperator z) = ∑ w, pureOperator (((slot w)†) z) := by
  rw [ptrace]
  apply Finset.sum_congr rfl
  intro w _
  rw [pureOperator_adjoint_apply]

theorem ptrace_smul (c : ℂ) (X : EuclideanSpace ℂ (n × W) →L[ℂ] EuclideanSpace ℂ (n × W)) :
    ptrace (c • X) = c • ptrace X := by
  rw [ptrace, ptrace, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [smul_comp, comp_smul]

omit [Fintype s] in
/-- The partial trace preserves the trace. -/
theorem tr_ptrace (X : EuclideanSpace ℂ (n × W) →L[ℂ] EuclideanSpace ℂ (n × W)) :
    tr (ptrace X) = tr X := by
  have hcyc : ∀ w, tr ((slot (n := n) w)† ∘L X ∘L slot w) =
      tr (X ∘L (slot w ∘L (slot w)†)) := by
    intro w
    change LinearMap.trace ℂ _ (((slot (n := n) w)†).toLinearMap ∘ₗ (X ∘L slot w).toLinearMap) =
      LinearMap.trace ℂ _ ((X ∘L slot w).toLinearMap ∘ₗ ((slot (n := n) w)†).toLinearMap)
    exact LinearMap.trace_comp_comm' _ _
  have hsum1 : tr (ptrace X) = ∑ w, tr ((slot (n := n) w)† ∘L X ∘L slot w) := by
    simp only [ptrace, tr, ContinuousLinearMap.toLinearMap_sum, map_sum]
  have hsum2 : ∑ w, tr (X ∘L (slot (n := n) w ∘L (slot w)†)) =
      tr (X ∘L ∑ w, slot (n := n) w ∘L (slot w)†) := by
    rw [comp_finsetSum]
    simp only [tr, ContinuousLinearMap.toLinearMap_sum, map_sum]
  rw [hsum1, Finset.sum_congr rfl (fun w _ => hcyc w), hsum2, sum_slot_comp_adjoint, one_def,
    comp_id]

/-- The partial trace preserves positivity. -/
theorem ptrace_isPositive {X : EuclideanSpace ℂ (n × W) →L[ℂ] EuclideanSpace ℂ (n × W)}
    (hX : X.IsPositive) : (ptrace X).IsPositive := by
  unfold ptrace
  apply ContinuousLinearMap.isPositive_sum
  intro w _
  exact hX.adjoint_conj (slot w)

/-- The partial trace of a density operator is a density operator. -/
theorem ptrace_isDensity {X : EuclideanSpace ℂ (n × W) →L[ℂ] EuclideanSpace ℂ (n × W)}
    (hX : IsDensity X) : IsDensity (ptrace X) :=
  ⟨ptrace_isPositive hX.1, by
    change tr (ptrace X) = 1
    rw [tr_ptrace]
    exact hX.2⟩

end

end SparseHamiltonian.MixedOutputODE
