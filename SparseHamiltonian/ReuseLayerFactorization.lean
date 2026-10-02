import SparseHamiltonian.LookupProgramControl

/-!
# Isolating the clock queries in synchronized reuse

A synchronized reuse layer consists of a fixed coupling network followed by
one active-branch action on the shared private register. This factorization
removes any implementation obligation for the entire coupling network: only
the explicitly controlled private clock action requires an oracle certificate.
The boundary embedding is fixed independently of the unknown oracle input.
-/

namespace SparseHamiltonian.ReuseLayerFactorization

noncomputable section
open ContinuousLinearMap OracleCircuit ReuseSchedule ReuseQuery GlobalColligation
open ChronologicalResolvent ChronologicalCatalyst ChronologicalClockFactorization
open scoped InnerProduct
set_option maxHeartbeats 1000000

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Act on the shared private register and leave all public reuse slots fixed. -/
def sharedAction (Q : V →L[ℂ] V) (n : ℕ) : Space n P V →L[ℂ] Space n P V :=
  blockMap Q 0 0 1

omit [CompleteSpace P] [CompleteSpace V] in
@[simp] theorem sharedAction_apply (Q : V →L[ℂ] V) (n : ℕ) (x : Space n P V) :
    sharedAction Q n x = WithLp.toLp 2 (Q x.fst, x.snd) := by
  simp [sharedAction, blockMap_apply]

omit [CompleteSpace P] [CompleteSpace V] in
/-- A common private-input factor does not depend on the selected public slot. -/
theorem slotInteraction_factor (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D Q : V →L[ℂ] V) {n : ℕ} (r : Fin n) :
    slotInteraction A (B ∘L Q) C (D ∘L Q) r =
      slotInteraction A B C D r ∘L sharedAction Q n := by
  ext x
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change (slotInteraction A (B ∘L Q) C (D ∘L Q) r x).fst =
      (slotInteraction A B C D r (sharedAction Q n x)).fst
    rw [slotInteraction_fst, slotInteraction_fst, sharedAction_apply]
    rfl
  · apply PiLp.ext
    intro j
    change (slotInteraction A (B ∘L Q) C (D ∘L Q) r x).snd j =
      (slotInteraction A B C D r (sharedAction Q n x)).snd j
    rw [slotInteraction_snd, slotInteraction_snd, sharedAction_apply]
    rfl

/-- The private query is disabled on branches whose reuse has finished. -/
def activeBranch (Q : V →L[ℂ] V) (n r : ℕ) : Space n P V →L[ℂ] Space n P V :=
  if r < n then sharedAction Q n else 1

omit [CompleteSpace P] [CompleteSpace V] in
/-- Padding the coupling and the query by identity preserves the factorization. -/
theorem slotStep_factor (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D Q : V →L[ℂ] V) (n r : ℕ) :
    slotStep A (B ∘L Q) C (D ∘L Q) n r =
      slotStep A B C D n r ∘L activeBranch Q n r := by
  by_cases h : r < n
  · simp only [slotStep, activeBranch, dif_pos h, if_pos h, slotInteraction_factor]
  · simp only [slotStep, activeBranch, dif_neg h, if_neg h, one_def, id_comp]

/-- One shared-register query, simultaneously controlled by branch activity. -/
def activeQuery (Q : V →L[ℂ] V) (d r : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := V) d) →L[ℂ]
      PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := V) d) :=
  WeightedClock.diagonal (fun i => activeBranch Q (ReuseWeights.length d i) r)

omit [CompleteSpace P] [CompleteSpace V] in
/-- A complete synchronized layer has one explicit active private-query factor. -/
theorem reuseLayer_factor (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D Q : V →L[ℂ] V) (d r : ℕ) :
    reuseLayer A (B ∘L Q) C (D ∘L Q) d r =
      reuseLayer A B C D d r ∘L activeQuery Q d r := by
  unfold reuseLayer activeQuery
  rw [WeightedClock.diagonal_comp]
  congr 1
  funext i
  exact slotStep_factor A B C D Q _ r

/-- Unitary local interactions give unitary padded branch steps. -/
theorem slotStep_unitary [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2)
    (n r : ℕ) : IsUnitary (slotStep A B C D n r) := by
  unfold slotStep
  split
  · exact slotInteraction_unitary A B C D hStep _
  · exact isUnitary_one

/-- The synchronized coupling is a fixed unitary when its local blocks are. -/
theorem reuseLayer_unitary [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2)
    (d r : ℕ) : IsUnitary (reuseLayer A B C D d r) := by
  have h := fun i : ReuseWeights.Index d =>
    slotStep_unitary A B C D hStep (ReuseWeights.length d i) r
  constructor
  · change (reuseLayer A B C D d r)† ∘L reuseLayer A B C D d r = 1
    unfold reuseLayer
    rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    exact (congrArg WeightedClock.diagonal (funext fun i => (h i).1)).trans
      WeightedClock.diagonal_one
  · change reuseLayer A B C D d r ∘L (reuseLayer A B C D d r)† = 1
    unfold reuseLayer
    rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    exact (congrArg WeightedClock.diagonal (funext fun i => (h i).2)).trans
      WeightedClock.diagonal_one

/-- Fixed coupling adds no oracle queries to the controlled private action. -/
theorem reuseLayer_implements [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    {X : Type*} (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2)
    (Q : X → V →L[ℂ] V) (d r q : ℕ)
    (O : X → PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := V) d) →L[ℂ]
      PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := V) d))
    (hQuery : Implements O (fun x => activeQuery (Q x) d r) q) :
    Implements O (fun x => reuseLayer A (B ∘L Q x) C (D ∘L Q x) d r) q := by
  have hFixed := Implements.fixed (O := O) (reuseLayer A B C D d r)
    (reuseLayer_unitary A B C D hStep d r)
  have h := (hFixed.mul hQuery).congr (fun x => (reuseLayer_factor A B C D (Q x) d r).symm)
  simpa only [Nat.zero_add] using h

/-- The oracle-independent part of a complete chronological reuse layer. -/
def couplingLayer (J : P →L[ℂ] V) (c κ σ : ℝ) (T d r : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := BlockOperator.H T V) d) →L[ℂ]
      PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := BlockOperator.H T V) d) :=
  reuseLayer (((c : ℂ) • (1 : P →L[ℂ] P)) ^ T)
    (publicExit ((c : ℂ) • 1) ((-(σ : ℂ)) • J†) T)
    (stackedResponse ((σ : ℂ) • J) ((c : ℂ) • 1) T)
    (chronologicalOperator (1 - (κ : ℂ) • (J ∘L J†)) ((σ : ℂ) • J)
      ((c : ℂ) • 1) ((-(σ : ℂ)) • J†) T) d r

/-- Only the unfinished branches run the parallel private clock. -/
def activeClock (D : V →L[ℂ] V) (T d r : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := BlockOperator.H T V) d) →L[ℂ]
      PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := BlockOperator.H T V) d) :=
  activeQuery (WeightedClock.diagonal (fun _ : Fin T => D)) d r

/-- The exact four blocks used by clock simulation have this single query factor. -/
theorem clockReuseLayer_factor (D : V →L[ℂ] V) (J : P →L[ℂ] V)
    (c κ σ : ℝ) (T d r : ℕ) :
    reuseLayer (((c : ℂ) • (1 : P →L[ℂ] P)) ^ T)
      (publicExit ((c : ℂ) • 1) ((-(σ : ℂ)) • (J† ∘L D)) T)
      (stackedResponse ((σ : ℂ) • J) ((c : ℂ) • 1) T)
      (GlobalResolvent.globalPrivateBlock D J c κ σ T) d r =
      couplingLayer J c κ σ T d r ∘L activeClock D T d r := by
  rw [globalPrivateBlock_factor]
  have hB : publicExit ((c : ℂ) • (1 : P →L[ℂ] P))
      ((-(σ : ℂ)) • (J† ∘L D)) T =
      publicExit ((c : ℂ) • 1) ((-(σ : ℂ)) • J†) T ∘L
        WeightedClock.diagonal (fun _ : Fin T => D) := by
    simpa only [smul_comp] using
      publicExit_factor D ((c : ℂ) • (1 : P →L[ℂ] P)) ((-(σ : ℂ)) • J†) T
  rw [hB]
  exact reuseLayer_factor _ _ _ _ _ d r

/-- Clock-independent chronology conserves energy by the boundary rotation. -/
theorem coupling_energy (J : P →L[ℂ] V) (hJ : J† ∘L J = 1)
    (c κ σ : ℝ) (hκ : κ = 1 - c) (hσ : σ ^ 2 = 1 - c ^ 2)
    (T : ℕ) (p : P) (v : BlockOperator.H T V) :
    ‖(((c : ℂ) • (1 : P →L[ℂ] P)) ^ T) p +
      publicExit ((c : ℂ) • 1) ((-(σ : ℂ)) • J†) T v‖ ^ 2 +
    ‖chronologicalOperator (1 - (κ : ℂ) • (J ∘L J†)) ((σ : ℂ) • J)
      ((c : ℂ) • 1) ((-(σ : ℂ)) • J†) T v +
      stackedResponse ((σ : ℂ) • J) ((c : ℂ) • 1) T p‖ ^ 2 =
    ‖p‖ ^ 2 + ‖v‖ ^ 2 := by
  have hlocal := LocalRotation.local_step_energy (1 : V →L[ℂ] V) J c κ σ hκ hσ
    (by rw [adjoint_one]; rfl) hJ
  simp only [GlobalResolvent.localPrivateBlock, one_def, comp_id] at hlocal
  have h := chronological_full_energy (1 - (κ : ℂ) • (J ∘L J†))
    ((σ : ℂ) • J) ((c : ℂ) • 1) ((-(σ : ℂ)) • J†) hlocal T p v
  simpa only [add_comm (stackedResponse ((σ : ℂ) • J) ((c : ℂ) • 1) T p)] using h

/-- The entire coupling is a legal fixed unitary gate. -/
theorem couplingLayer_unitary [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    (J : P →L[ℂ] V) (hJ : J† ∘L J = 1)
    (c κ σ : ℝ) (hκ : κ = 1 - c) (hσ : σ ^ 2 = 1 - c ^ 2) (T d r : ℕ) :
    IsUnitary (couplingLayer J c κ σ T d r) :=
  reuseLayer_unitary _ _ _ _ (coupling_energy J hJ c κ σ hκ hσ T) d r

/-- The actual scheduled clock layer has no additional queries beyond its
explicit active clock action. All coupling data is independent of `x`. -/
theorem clockLayer_implements [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    {X : Type*} (D : X → V →L[ℂ] V) (J : P →L[ℂ] V) (hJ : J† ∘L J = 1)
    (w Q qbar : ℝ) (T : ℕ) (δ : ℝ) (hw : 0 ≤ w) (hwQuarter : w ≤ 1 / 4)
    (r q : ℕ)
    (O : X → ClockQuery.Space (P := P) (V := V) w Q qbar T δ →L[ℂ]
      ClockQuery.Space (P := P) (V := V) w Q qbar T δ)
    (hQuery : Implements O (fun x => activeClock (P := P) (D x) T
      (FilterSchedule.degree Q ((T : ℝ) * w * qbar) δ) r) q) :
    Implements O (fun x => ClockQuery.layer (D x) J w Q qbar T δ r) q := by
  obtain ⟨_hκ, _hκUpper, hκc, hσc, _hσw⟩ := CayleyTransfer.scalar_promises w hw hwQuarter
  have hFixed := Implements.fixed (O := O)
    (couplingLayer J (CayleyTransfer.c w) (CayleyTransfer.kappa w)
      (CayleyTransfer.sigma w) T (FilterSchedule.degree Q ((T : ℝ) * w * qbar) δ) r)
    (couplingLayer_unitary J hJ _ _ _ hκc hσc T _ r)
  have h := (hFixed.mul hQuery).congr (fun x =>
    (clockReuseLayer_factor (D x) J _ _ _ T _ r).symm)
  simpa only [Nat.zero_add, ClockQuery.layer] using h


end
end SparseHamiltonian.ReuseLayerFactorization
