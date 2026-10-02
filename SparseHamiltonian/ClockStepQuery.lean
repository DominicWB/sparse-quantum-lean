import SparseHamiltonian.QueryClockLinks

/-!
# A distributed clock step as a fixed shift and a coherent SELECT

The prefix gauge is used only to prove the operator identity. The implementing
circuit consists of the fixed phased cyclic shift and a coherent selection of
individual links. In particular the input-dependent prefix gauge is never
counted as a free gate.
-/

namespace SparseHamiltonian.ClockStepQuery

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The cyclic shift with a fixed phase `i` on its return edge. -/
def phasedShift (q : ℕ) : ClockOperators.H q V →L[ℂ] ClockOperators.H q V :=
  ClockOperators.clock (LinearMap.id : V →ₗ[ℂ] V) q (fun _ => rfl) (fun _ _ => rfl)

@[simp] theorem phasedShift_zero (q : ℕ) (x : ClockOperators.H q V) :
    phasedShift q x 0 = Complex.I • x (Fin.last q) := rfl

@[simp] theorem phasedShift_succ (q : ℕ) (x : ClockOperators.H q V) (j : Fin q) :
    phasedShift q x j.succ = x j.castSucc := rfl

/-- The fixed phased shift is onto, including a clock with a single slot. -/
theorem phasedShift_surjective (q : ℕ) :
    Function.Surjective (phasedShift (V := V) q) := by
  intro x
  refine ⟨WithLp.toLp 2 (Fin.lastCases ((-Complex.I) • x 0) (fun j => x j.succ)), ?_⟩
  apply PiLp.ext
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [phasedShift_zero, Fin.lastCases_last, smul_smul]
    simp
  · simp only [phasedShift_succ, Fin.lastCases_castSucc]

/-- Select an internal link on each source slot, with identity at the return slot. -/
def linkSelect (q : ℕ) (L : ℕ → V ≃ₗᵢ[ℂ] V) :
    ClockOperators.H q V →L[ℂ] ClockOperators.H q V :=
  WeightedClock.diagonal (Fin.lastCases 1 (fun j : Fin q =>
    (L j.val).toContinuousLinearEquiv.toContinuousLinearMap))

@[simp] theorem linkSelect_last (q : ℕ) (L : ℕ → V ≃ₗᵢ[ℂ] V)
    (x : ClockOperators.H q V) : linkSelect q L x (Fin.last q) = x (Fin.last q) := by
  simp [linkSelect]

@[simp] theorem linkSelect_castSucc (q : ℕ) (L : ℕ → V ≃ₗᵢ[ℂ] V)
    (x : ClockOperators.H q V) (j : Fin q) :
    linkSelect q L x j.castSucc = L j.val (x j.castSucc) := by
  simp [linkSelect]

variable [CompleteSpace V]

/-- Both unitary identities for the fixed cyclic shift. -/
theorem phasedShift_unitary (q : ℕ) : IsUnitary (phasedShift (V := V) q) := by
  have hLeft : (phasedShift (V := V) q)† ∘L phasedShift q = 1 :=
    ClockOperators.clock_adjoint_comp _ _ _ _
  refine ⟨hLeft, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := phasedShift_surjective q x
  have hy := congrArg (fun A : ClockOperators.H q V →L[ℂ] ClockOperators.H q V => A y) hLeft
  change phasedShift q (((phasedShift q)†) (phasedShift q y)) = phasedShift q y
  exact congrArg (phasedShift q) hy

/-- The distributed clock has a direct circuit factorization, with no gauge gates. -/
theorem prefix_distributedClock_factor (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w))
    (L : ℕ → V ≃ₗᵢ[ℂ] V) (hProduct : ∀ v, O v = ClockGauge.prefixGauge L q v) :
    ClockGauge.distributedClock O q hO hHerm (fun j => ClockGauge.prefixGauge L j.val) =
      phasedShift q ∘L linkSelect q L := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [ClockGauge.prefix_distributedClock_zero O q hO hHerm L hProduct]
    simp only [comp_apply, phasedShift_zero, linkSelect_last]
  · rw [ClockGauge.prefix_distributedClock_succ]
    simp only [comp_apply, phasedShift_succ, linkSelect_castSucc]

/-- A uniform implementation of SELECT implements a clock step at exactly the
same cost. Only the input-independent phased shift is added to the circuit. -/
theorem distributedClock_implements {X : Type*}
    (R : X → ClockOperators.H q V →L[ℂ] ClockOperators.H q V)
    (O : X → V →ₗ[ℂ] V)
    (hO : ∀ x v, O x (O x v) = v)
    (hHerm : ∀ x v w, inner ℂ (O x v) w = inner ℂ v (O x w))
    (L : X → ℕ → V ≃ₗᵢ[ℂ] V)
    (hProduct : ∀ x v, O x v = ClockGauge.prefixGauge (L x) q v)
    (c : ℕ) (hSelect : Implements R (fun x => linkSelect q (L x)) c) :
    Implements R (fun x => ClockGauge.distributedClock (O x) q (hO x) (hHerm x)
      (fun j => ClockGauge.prefixGauge (L x) j.val)) c := by
  have hShift := Implements.fixed (O := R) (phasedShift q) (phasedShift_unitary q)
  have h := hShift.mul hSelect
  simpa only [Nat.zero_add] using h.congr (fun x =>
    (prefix_distributedClock_factor (O x) q (hO x) (hHerm x) (L x) (hProduct x)).symm)

/-- Coherent SELECT with an identity padded return slot. -/
def paddedSelect (q : ℕ) (A : Fin q → V →L[ℂ] V) :
    ClockOperators.H q V →L[ℂ] ClockOperators.H q V :=
  WeightedClock.diagonal (Fin.lastCases 1 A)

/-- Fixed unitary link gates give a fixed unitary SELECT, with no dimension assumption. -/
theorem paddedSelect_unitary (q : ℕ) (A : Fin q → V →L[ℂ] V)
    (hA : ∀ j, IsUnitary (A j)) : IsUnitary (paddedSelect q A) := by
  have hSlots : ∀ j : Fin (q + 1), IsUnitary (Fin.lastCases 1 A j) := by
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa only [Fin.lastCases_last] using (isUnitary_one (K := V))
    · simpa only [Fin.lastCases_castSucc] using hA k
  constructor
  · exact WeightedClock.diagonal_isometry _ (fun j => (hSlots j).1)
  · change paddedSelect q A ∘L (paddedSelect q A)† = 1
    rw [paddedSelect, WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    have hRight : ∀ j : Fin (q + 1), (Fin.lastCases 1 A j) ∘L (Fin.lastCases 1 A j)† = 1 :=
      fun j => (hSlots j).2
    simp only [hRight, WeightedClock.diagonal_one]

omit [CompleteSpace V] in
/-- The data-dependent part of each link can be coherently selected once,
then followed by a single fixed diagonal gate. -/
theorem linkSelect_factor (q : ℕ) (L : ℕ → V ≃ₗᵢ[ℂ] V)
    (A M : Fin q → V →L[ℂ] V)
    (hL : ∀ j : Fin q, (L j.val).toContinuousLinearEquiv.toContinuousLinearMap =
      A j ∘L M j) :
    linkSelect q L = paddedSelect q A ∘L paddedSelect q M := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [paddedSelect, linkSelect]
  · simpa only [linkSelect, paddedSelect, WeightedClock.diagonal_apply,
      Fin.lastCases_castSucc, comp_apply] using
      congrArg (fun F : V →L[ℂ] V => F (x k.castSucc)) (hL k)

/-- The only query obligation is the explicitly selected data-dependent
part of the links. The selected fixed-gate diagonal and the final shift are
independent of the unknown input. The resulting bound is independent of the number of clock slots. -/
theorem distributedClock_implements_of_link_factors {X : Type*}
    (R : X → ClockOperators.H q V →L[ℂ] ClockOperators.H q V)
    (O : X → V →ₗ[ℂ] V)
    (hO : ∀ x v, O x (O x v) = v)
    (hHerm : ∀ x v w, inner ℂ (O x v) w = inner ℂ v (O x w))
    (L : X → ℕ → V ≃ₗᵢ[ℂ] V)
    (hProduct : ∀ x v, O x v = ClockGauge.prefixGauge (L x) q v)
    (A : Fin q → V →L[ℂ] V) (hA : ∀ j, IsUnitary (A j))
    (M : X → Fin q → V →L[ℂ] V)
    (hL : ∀ x (j : Fin q),
      (L x j.val).toContinuousLinearEquiv.toContinuousLinearMap = A j ∘L M x j)
    (c : ℕ) (hQuery : Implements R (fun x => paddedSelect q (M x)) c) :
    Implements R (fun x => ClockGauge.distributedClock (O x) q (hO x) (hHerm x)
      (fun j => ClockGauge.prefixGauge (L x) j.val)) c := by
  apply distributedClock_implements R O hO hHerm L hProduct c
  have hFixed := Implements.fixed (O := R) (paddedSelect q A) (paddedSelect_unitary q A hA)
  have h := hFixed.mul hQuery
  simpa only [Nat.zero_add] using h.congr (fun x =>
    (linkSelect_factor q (L x) A (M x) (hL x)).symm)

end
end SparseHamiltonian.ClockStepQuery
