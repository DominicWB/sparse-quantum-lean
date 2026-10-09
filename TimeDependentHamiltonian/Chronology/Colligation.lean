import TimeDependentHamiltonian.Chronology.Varying

/-!
# The chronological clock with slot-dependent private operations

For a common boundary isometry `J`, common rotation scalars `c, κ, σ` and a
private operation `D k` at each time slot `k`, the chronological transducer
is the released oracle-independent coupling network followed by the parallel
slot action `⊕ₖ D k`. This module proves for that transducer

* exact energy conservation (`colligation_energy`);
* that its private block is the slot-dependent chronological operator
  (`privateV_eq`);
* the public and private catalyst transduction identities, whose public action
  is the ordered product `U (T-1) ⋯ U 0` of the local public actions
  (`colligation_public`, `colligation_private`);
* the additive catalyst cost and the exit identity;
* the resolvent bound `3 (Q + W) exp (3 W / (4 Q))` on the disk
  `‖z - 1‖ ≤ 1 / (4 Q)`, where `W = T w qbar` (`exists_privateV_resolvent`),
  and the resulting filter precision (`filter_precisionV`).

These are the formal counterparts of equations `hs:eq:timecatalyst` and
`hs:eq:timeresolvent` of the manuscript, for a uniform mesh.
-/

namespace SparseHamiltonian.TimeDependent

noncomputable section

open ContinuousLinearMap
open SparseHamiltonian.ChronologicalResolvent SparseHamiltonian.ChronologicalCatalyst
open SparseHamiltonian.GlobalColligation SparseHamiltonian.FiniteChronologicalInverse
open scoped BigOperators InnerProduct

section Normed

variable {P V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The released forced state of a slotwise transformed sequence is the
slot-dependent forced state with transformed exits. -/
theorem forcedPublicState_slot (u : P →L[ℂ] P) (B : V →L[ℂ] P)
    (D : ℕ → V →L[ℂ] V) (y : ℕ → V) (n : ℕ) :
    forcedPublicState u B (fun k => D k (y k)) n =
      forcedState (fun _ => u) (fun k => B ∘L D k) y n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [forcedPublicState_succ, forcedState_succ, ih, comp_apply]

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem restrict_eq_toLp {T : ℕ} (y : ℕ → V) :
    restrictSequence T y = WithLp.toLp 2 (fun k : Fin T => y k) := rfl

/-- The ordered public evolution `U (n-1) ⋯ U 0`. -/
def evolution (U : ℕ → P →L[ℂ] P) (n : ℕ) : P →L[ℂ] P := orderedProduct U 0 n

@[simp] theorem evolution_zero (U : ℕ → P →L[ℂ] P) : evolution U 0 = 1 := rfl

theorem evolution_succ (U : ℕ → P →L[ℂ] P) (n : ℕ) :
    evolution U (n + 1) = U n * evolution U n := by
  simp only [evolution, orderedProduct_succ, zero_add]

/-- Norm-preserving local actions give a norm-preserving ordered evolution. -/
theorem evolution_norm (U : ℕ → P →L[ℂ] P) (hU : ∀ k p, ‖U k p‖ = ‖p‖)
    (n : ℕ) (p : P) : ‖evolution U n p‖ = ‖p‖ := by
  induction n with
  | zero => simp
  | succ n ih => rw [evolution_succ, mul_apply_eq_comp, hU, ih]

/-- Stack the local catalysts along the actual ordered public trajectory. -/
def stackedV (Γ : ℕ → P →L[ℂ] V) (U : ℕ → P →L[ℂ] P) (T : ℕ) :
    P →L[ℂ] BlockOperator.H T V :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin T => V)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun r : Fin T => Γ r ∘L evolution U r)

@[simp] theorem stackedV_apply (Γ : ℕ → P →L[ℂ] V) (U : ℕ → P →L[ℂ] P)
    (T : ℕ) (p : P) (r : Fin T) : stackedV Γ U T p r = Γ r (evolution U r p) := rfl

theorem stackedV_eq_toLp (Γ : ℕ → P →L[ℂ] V) (U : ℕ → P →L[ℂ] P) (T : ℕ) (p : P) :
    stackedV Γ U T p = WithLp.toLp 2 (fun k : Fin T => Γ k (evolution U k p)) := rfl

/-- The public trajectory with an arbitrary initial public state. -/
def publicStateV (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (y : ℕ → V) (p : P) : ℕ → P
  | 0 => p
  | n + 1 => u n (publicStateV u B y p n) + B n (y n)

theorem publicStateV_eq (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (y : ℕ → V)
    (p : P) (n : ℕ) :
    publicStateV u B y p n = orderedProduct u 0 n p + forcedState u B y n := by
  induction n with
  | zero => simp [publicStateV]
  | succ n ih =>
      simp only [publicStateV, ih, map_add, forcedState_succ, orderedProduct_succ,
        zero_add, mul_apply_eq_comp]
      abel

/-- Local public transduction propagates the ordered public evolution. -/
theorem catalyst_publicStateV (Γ : ℕ → P →L[ℂ] V) (U u : ℕ → P →L[ℂ] P)
    (B : ℕ → V →L[ℂ] P) (hPublic : ∀ k, u k + B k ∘L Γ k = U k) (p : P) (n : ℕ) :
    publicStateV u B (fun k => Γ k (evolution U k p)) p n = evolution U n p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [publicStateV, ih, evolution_succ, mul_apply_eq_comp, ← hPublic n]
      rfl

/-- The forced state depends only on the forcing before the current slot. -/
theorem forcedState_congr (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (y y' : ℕ → V)
    (n : ℕ) (h : ∀ k < n, y k = y' k) : forcedState u B y n = forcedState u B y' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [forcedState_succ, forcedState_succ, ih (fun k hk => h k (by omega)),
        h n (by omega)]

/-- The slot-dependent block operator on a restricted sequence. -/
theorem operator_apply_restrict (R : ℕ → V →L[ℂ] V) (A : ℕ → P →L[ℂ] V)
    (u : ℕ → P →L[ℂ] P) (B : ℕ → V →L[ℂ] P) (y : ℕ → V) {T : ℕ} (r : Fin T) :
    operator R A u B T (restrictSequence T y) r = privateState R A u B y r :=
  operator_apply R A u B y r

theorem stackedV_eq_restrict (Γ : ℕ → P →L[ℂ] V) (U : ℕ → P →L[ℂ] P) (T : ℕ) (p : P) :
    stackedV Γ U T p = restrictSequence T (fun k => Γ k (evolution U k p)) := rfl

/-- Squared catalyst costs add over the slots. -/
theorem stackedV_norm_sq_le (Γ : ℕ → P →L[ℂ] V) (U : ℕ → P →L[ℂ] P)
    (hU : ∀ k p, ‖U k p‖ = ‖p‖) (C : ℝ) (hΓ : ∀ k, ‖Γ k‖ ^ 2 ≤ C) (T : ℕ) :
    ‖stackedV Γ U T‖ ^ 2 ≤ (T : ℝ) * C := by
  have hC : 0 ≤ C := (sq_nonneg ‖Γ 0‖).trans (hΓ 0)
  have hTC : 0 ≤ (T : ℝ) * C := mul_nonneg (Nat.cast_nonneg _) hC
  have hBound : ‖stackedV Γ U T‖ ≤ Real.sqrt ((T : ℝ) * C) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro p
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hTC, PiLp.norm_sq_eq_of_L2]
    calc
      ∑ r : Fin T, ‖stackedV Γ U T p r‖ ^ 2 ≤ ∑ _ : Fin T, C * ‖p‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro r _hr
        rw [stackedV_apply]
        calc
          ‖Γ r (evolution U r p)‖ ^ 2 ≤ (‖Γ r‖ * ‖evolution U r p‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (le_opNorm _ _) 2
          _ = ‖Γ r‖ ^ 2 * ‖p‖ ^ 2 := by rw [evolution_norm U hU, mul_pow]
          _ ≤ C * ‖p‖ ^ 2 := mul_le_mul_of_nonneg_right (hΓ r) (sq_nonneg _)
      _ = (T : ℝ) * C * ‖p‖ ^ 2 := by simp [mul_assoc]
  have hs := pow_le_pow_left₀ (norm_nonneg _) hBound 2
  simpa only [Real.sq_sqrt hTC] using hs

end Normed

section Slots

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The parallel slotwise private action `⊕ₖ D k`. -/
def slotAction (D : ℕ → V →L[ℂ] V) (T : ℕ) :
    BlockOperator.H T V →L[ℂ] BlockOperator.H T V :=
  WeightedClock.diagonal (fun t : Fin T => D t)

@[simp] theorem slotAction_apply (D : ℕ → V →L[ℂ] V) (T : ℕ)
    (x : BlockOperator.H T V) (t : Fin T) : slotAction D T x t = D t (x t) := rfl

theorem extend_slotAction (D : ℕ → V →L[ℂ] V) (T : ℕ)
    (x : BlockOperator.H T V) (k : ℕ) :
    extendSequence (slotAction D T x) k = D k (extendSequence x k) := by
  by_cases hk : k < T
  · simp [extendSequence, hk]
  · simp [extendSequence, hk]

end Slots

section Hilbert

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The private block of the slot-dependent chronological transducer. -/
def privateV (D : ℕ → V →L[ℂ] V) (J : P →L[ℂ] V) (c κ σ : ℝ) (T : ℕ) :
    BlockOperator.H T V →L[ℂ] BlockOperator.H T V :=
  chronologicalOperator (1 - (κ : ℂ) • (J ∘L J†)) ((σ : ℂ) • J)
    ((c : ℂ) • 1) ((-(σ : ℂ)) • J†) T ∘L slotAction D T

/-- The public exit block of the slot-dependent chronological transducer. -/
def exitV (D : ℕ → V →L[ℂ] V) (J : P →L[ℂ] V) (c σ : ℝ) (T : ℕ) :
    BlockOperator.H T V →L[ℂ] P :=
  publicExit ((c : ℂ) • (1 : P →L[ℂ] P)) ((-(σ : ℂ)) • J†) T ∘L slotAction D T

/-- Isometric slot operations give an isometric parallel action. -/
theorem slotAction_norm (D : ℕ → V →L[ℂ] V) (hD : ∀ k, (D k)† ∘L D k = 1)
    (T : ℕ) (x : BlockOperator.H T V) : ‖slotAction D T x‖ = ‖x‖ := by
  have hIso : (slotAction D T)† ∘L slotAction D T = 1 :=
    WeightedClock.diagonal_isometry (fun t : Fin T => D t) (fun t => hD t)
  have h := (norm_map_iff_adjoint_comp_self (slotAction D T)).mpr hIso x
  simpa only [one_mul] using h

/-- Exact energy conservation of the slot-dependent transducer. The coupling
network is the released oracle-independent one; only isometry of each `D k`
is used. -/
theorem colligation_energy (D : ℕ → V →L[ℂ] V) (J : P →L[ℂ] V)
    (hJ : J† ∘L J = 1) (hD : ∀ k, (D k)† ∘L D k = 1)
    (c κ σ : ℝ) (hκ : κ = 1 - c) (hσ : σ ^ 2 = 1 - c ^ 2) (T : ℕ)
    (p : P) (v : BlockOperator.H T V) :
    ‖(((c : ℂ) • (1 : P →L[ℂ] P)) ^ T) p + exitV D J c σ T v‖ ^ 2 +
      ‖stackedResponse ((σ : ℂ) • J) ((c : ℂ) • 1) T p + privateV D J c κ σ T v‖ ^ 2 =
      ‖p‖ ^ 2 + ‖v‖ ^ 2 := by
  have h := ReuseLayerFactorization.coupling_energy J hJ c κ σ hκ hσ T p
    (slotAction D T v)
  rw [slotAction_norm D hD T v] at h
  rw [add_comm (stackedResponse ((σ : ℂ) • J) ((c : ℂ) • 1) T p)]
  simpa only [exitV, privateV, comp_apply] using h

/-- The private block is a contraction. -/
theorem privateV_norm_le_one (D : ℕ → V →L[ℂ] V) (J : P →L[ℂ] V)
    (hJ : J† ∘L J = 1) (hD : ∀ k, (D k)† ∘L D k = 1)
    (c κ σ : ℝ) (hκ : κ = 1 - c) (hσ : σ ^ 2 = 1 - c ^ 2) (T : ℕ) :
    ‖privateV D J c κ σ T‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  have h := colligation_energy D J hJ hD c κ σ hκ hσ T 0 v
  simp only [map_zero, zero_add, norm_zero] at h
  have hsq : ‖privateV D J c κ σ T v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    nlinarith [sq_nonneg ‖exitV D J c σ T v‖]
  rw [one_mul]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-! ### Identification with the slot-dependent chronological operator -/

/-- The slot-dependent private block is the chronological operator with local
private blocks `localPrivateBlock (D k) J κ` and exits `-σ J† D k`. -/
theorem privateV_eq (D : ℕ → V →L[ℂ] V) (J : P →L[ℂ] V) (c κ σ : ℝ) (T : ℕ) :
    privateV D J c κ σ T =
      operator (fun k => GlobalResolvent.localPrivateBlock (D k) J κ)
        (fun _ => (σ : ℂ) • J) (fun _ => (c : ℂ) • (1 : P →L[ℂ] P))
        (fun k => (-(σ : ℂ)) • (J† ∘L D k)) T := by
  ext x r
  have hslot : slotAction D T x =
      restrictSequence T (fun k => D k (extendSequence x k)) := by
    rw [← restrict_extend (slotAction D T x)]
    congr 1
    funext k
    exact extend_slotAction D T x k
  have hx : x = restrictSequence T (extendSequence x) := (restrict_extend x).symm
  have hL : privateV D J c κ σ T x r =
      chronologicalPrivateState (1 - (κ : ℂ) • (J ∘L J†)) ((σ : ℂ) • J)
        ((c : ℂ) • 1) ((-(σ : ℂ)) • J†) (fun k => D k (extendSequence x k)) r := by
    rw [privateV, comp_apply, hslot, restrict_eq_toLp]
    exact chronologicalOperator_apply (1 - (κ : ℂ) • (J ∘L J†)) ((σ : ℂ) • J)
      ((c : ℂ) • 1) ((-(σ : ℂ)) • J†) (fun k => D k (extendSequence x k)) r
  rw [hL]
  conv_rhs => rw [hx, restrict_eq_toLp, operator_apply]
  have hB : (fun k => ((-(σ : ℂ)) • J†) ∘L D k) =
      (fun k => (-(σ : ℂ)) • (J† ∘L D k)) := by
    funext k
    rw [smul_comp]
  rw [chronologicalPrivateState, privateState, forcedPublicState_slot, hB]
  rfl

/-- The exit block applied to a private trajectory is the forced public state. -/
theorem exitV_apply (D : ℕ → V →L[ℂ] V) (J : P →L[ℂ] V) (c σ : ℝ) (T : ℕ)
    (x : BlockOperator.H T V) :
    exitV D J c σ T x =
      forcedState (fun _ => (c : ℂ) • (1 : P →L[ℂ] P))
        (fun k => (-(σ : ℂ)) • (J† ∘L D k)) (extendSequence x) T := by
  rw [exitV, comp_apply, publicExit_apply]
  have hseq : extendSequence (slotAction D T x) = fun k => D k (extendSequence x k) := by
    funext k
    exact extend_slotAction D T x k
  rw [hseq, forcedPublicState_slot]
  have hB : (fun k => ((-(σ : ℂ)) • J†) ∘L D k) =
      (fun k => (-(σ : ℂ)) • (J† ∘L D k)) := by
    funext k
    rw [smul_comp]
  rw [hB]

/-! ### Catalyst with slot-dependent local actions -/

/-- Unitary local actions give a unitary ordered evolution. -/
theorem evolution_unitary (U : ℕ → P →L[ℂ] P)
    (hIso : ∀ k, star (U k) * U k = 1) (hCoiso : ∀ k, U k * star (U k) = 1) (n : ℕ) :
    star (evolution U n) * evolution U n = 1 ∧ evolution U n * star (evolution U n) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [evolution_succ, star_mul]
      constructor
      · calc
          star (evolution U n) * star (U n) * (U n * evolution U n) =
              star (evolution U n) * (star (U n) * U n) * evolution U n := by noncomm_ring
          _ = 1 := by rw [hIso n, mul_one, ih.1]
      · calc
          U n * evolution U n * (star (evolution U n) * star (U n)) =
              U n * (evolution U n * star (evolution U n)) * star (U n) := by noncomm_ring
          _ = 1 := by rw [ih.2, mul_one, hCoiso n]

/-- The public action of the stacked catalyst is the ordered product of the
local public actions. -/
theorem colligation_public (D : ℕ → V →L[ℂ] V) (J : P →L[ℂ] V) (c σ : ℝ)
    (Γ : ℕ → P →L[ℂ] V) (U : ℕ → P →L[ℂ] P)
    (hPublic : ∀ k, (c : ℂ) • (1 : P →L[ℂ] P) + ((-(σ : ℂ)) • (J† ∘L D k)) ∘L Γ k = U k)
    (T : ℕ) :
    ((c : ℂ) • (1 : P →L[ℂ] P)) ^ T + exitV D J c σ T ∘L stackedV Γ U T =
      evolution U T := by
  ext p
  rw [add_apply, comp_apply, exitV_apply]
  have hcongr : forcedState (fun _ => (c : ℂ) • (1 : P →L[ℂ] P))
      (fun k => (-(σ : ℂ)) • (J† ∘L D k)) (extendSequence (stackedV Γ U T p)) T =
      forcedState (fun _ => (c : ℂ) • (1 : P →L[ℂ] P))
        (fun k => (-(σ : ℂ)) • (J† ∘L D k)) (fun k => Γ k (evolution U k p)) T := by
    apply forcedState_congr
    intro k hk
    simp [extendSequence, hk]
  rw [hcongr, ← orderedProduct_const _ 0 T, ← publicStateV_eq]
  exact catalyst_publicStateV Γ U _ _ hPublic p T

/-- The stacked catalyst is stationary under the slot-dependent private block. -/
theorem colligation_private (D : ℕ → V →L[ℂ] V) (J : P →L[ℂ] V) (c κ σ : ℝ)
    (Γ : ℕ → P →L[ℂ] V) (U : ℕ → P →L[ℂ] P)
    (hPrivate : ∀ k, (σ : ℂ) • J + GlobalResolvent.localPrivateBlock (D k) J κ ∘L Γ k = Γ k)
    (hPublic : ∀ k, (c : ℂ) • (1 : P →L[ℂ] P) + ((-(σ : ℂ)) • (J† ∘L D k)) ∘L Γ k = U k)
    (T : ℕ) :
    stackedResponse ((σ : ℂ) • J) ((c : ℂ) • 1) T + privateV D J c κ σ T ∘L stackedV Γ U T =
      stackedV Γ U T := by
  ext p r
  rw [add_apply, comp_apply, PiLp.add_apply, privateV_eq, stackedV_eq_restrict,
    operator_apply_restrict, stackedResponse_apply, privateState, restrictSequence_apply]
  have hpub := catalyst_publicStateV Γ U (fun _ => (c : ℂ) • (1 : P →L[ℂ] P))
    (fun k => (-(σ : ℂ)) • (J† ∘L D k)) hPublic p r
  rw [publicStateV_eq, orderedProduct_const] at hpub
  have hloc := congrArg (fun M : P →L[ℂ] V => M (evolution U r p)) (hPrivate r)
  simp only [add_apply, comp_apply] at hloc
  calc
    ((σ : ℂ) • J) ((((c : ℂ) • (1 : P →L[ℂ] P)) ^ (r : ℕ)) p) +
        (GlobalResolvent.localPrivateBlock (D r) J κ (Γ r (evolution U r p)) +
          ((σ : ℂ) • J) (forcedState (fun _ => (c : ℂ) • (1 : P →L[ℂ] P))
            (fun k => (-(σ : ℂ)) • (J† ∘L D k)) (fun k => Γ k (evolution U k p)) r)) =
        ((σ : ℂ) • J) ((((c : ℂ) • (1 : P →L[ℂ] P)) ^ (r : ℕ)) p +
          forcedState (fun _ => (c : ℂ) • (1 : P →L[ℂ] P))
            (fun k => (-(σ : ℂ)) • (J† ∘L D k)) (fun k => Γ k (evolution U k p)) r) +
          GlobalResolvent.localPrivateBlock (D r) J κ (Γ r (evolution U r p)) := by
      rw [map_add]
      abel
    _ = ((σ : ℂ) • J) (evolution U r p) +
          GlobalResolvent.localPrivateBlock (D r) J κ (Γ r (evolution U r p)) := by
      rw [hpub]
    _ = Γ r (evolution U r p) := hloc

/-- The exit identity of the slot-dependent transducer. -/
theorem exitV_identity (D : ℕ → V →L[ℂ] V) (J : P →L[ℂ] V)
    (hJ : J† ∘L J = 1) (hD : ∀ k, (D k)† ∘L D k = 1)
    (c κ σ : ℝ) (hκ : κ = 1 - c) (hσ : σ ^ 2 = 1 - c ^ 2)
    (Γ : ℕ → P →L[ℂ] V) (U : ℕ → P →L[ℂ] P)
    (hPrivate : ∀ k, (σ : ℂ) • J + GlobalResolvent.localPrivateBlock (D k) J κ ∘L Γ k = Γ k)
    (hPublic : ∀ k, (c : ℂ) • (1 : P →L[ℂ] P) + ((-(σ : ℂ)) • (J† ∘L D k)) ∘L Γ k = U k)
    (T : ℕ) (hCoiso : evolution U T ∘L (evolution U T)† = 1) :
    exitV D J c σ T =
      evolution U T ∘L ((stackedV Γ U T)† ∘L (1 - privateV D J c κ σ T)) := by
  have hEnergy := colligation_energy D J hJ hD c κ σ hκ hσ T
  exact ExitIdentity.exit_block_eq _ (evolution U T) (exitV D J c σ T)
    (stackedResponse ((σ : ℂ) • J) ((c : ℂ) • 1) T) (stackedV Γ U T)
    (privateV D J c κ σ T) (block_gram_mixed _ _ _ _ hEnergy)
    (block_gram_private _ _ _ _ hEnergy) (colligation_public D J c σ Γ U hPublic T)
    (colligation_private D J c κ σ Γ U hPrivate hPublic T) hCoiso

/-! ### Resolvent and filter precision -/

/-- Clock promises at every sampled time give the weighted resolvent bound of
the slot-dependent private block on the whole clock disk. -/
theorem exists_privateV_resolvent
    (D R1 : ℕ → V →L[ℂ] V) (J : P →L[ℂ] V) (H : ℕ → P →L[ℂ] P)
    (c κ σ w Q b qbar : ℝ) (T : ℕ) (z : ℂ)
    (hQ : 0 < Q) (hw : 0 ≤ w) (hκ : 0 ≤ κ) (hκUpper : κ ≤ 2 / 9)
    (hκc : κ = 1 - c) (hσc : σ ^ 2 = 1 - c ^ 2) (hσw : σ ^ 2 ≤ 2 * w)
    (hD : ∀ k, (D k)† ∘L D k = 1) (hJ : J† ∘L J = 1)
    (hRight : ∀ k, (1 - D k) ∘L R1 k = 1) (hLeft : ∀ k, R1 k ∘L (1 - D k) = 1)
    (hR1 : ∀ k, ‖R1 k‖ ≤ Q)
    (hBoundary : ∀ k, J† ∘L R1 k ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H k))
    (hSelf : ∀ k, star (H k) = H k) (hH : ∀ k, ‖H k‖ ≤ 1)
    (hEndpoint : ∀ k, ‖R1 k ∘L J‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (hz : ‖z - 1‖ ≤ 1 / (4 * Q)) :
    ∃ S : BlockOperator.H T V →L[ℂ] BlockOperator.H T V,
      (z • 1 - privateV D J c κ σ T) ∘L S = 1 ∧
      S ∘L (z • 1 - privateV D J c κ σ T) = 1 ∧
      ‖S‖ ≤ 3 * (Q + (T : ℝ) * w * qbar) *
        Real.exp (3 * ((T : ℝ) * w * qbar) / (4 * Q)) := by
  have hb : 0 ≤ b := (norm_nonneg _).trans (hEndpoint 0)
  have hq : 0 ≤ qbar := by nlinarith [sq_nonneg b]
  have hcert := fun k => GlobalResolvent.exists_local_clock_certificate (D k) (R1 k) J
    (H k) c κ σ w Q b qbar z hQ hw hκ hκUpper hκc hσc hσw (hD k) hJ (hRight k)
    (hLeft k) (hR1 k) (hBoundary k) (hSelf k) (hH k) (hEndpoint k) hbq hqQ hz
  choose S hSRight hSLeft hSNorm hSJ hES hTransfer using hcert
  have hσNorm : ‖(σ : ℂ)‖ ^ 2 ≤ 2 * w := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hσw
  have hCoupling : ∀ r k, ‖S r ∘L ((σ : ℂ) • J)‖ *
      ‖((-(σ : ℂ)) • (J† ∘L D k)) ∘L S k‖ ≤ (144 / 49 : ℝ) * w * qbar := by
    intro r k
    simpa only [comp_smul, smul_comp] using
      ChronologicalBound.coupling_norm_product_le (S r ∘L J) ((J† ∘L D k) ∘L S k)
        (σ : ℂ) hw hb hσNorm hbq (hSJ r) (hES k)
  rw [privateV_eq]
  exact exists_resolvent (fun k => GlobalResolvent.localPrivateBlock (D k) J κ) S
    (fun _ => (σ : ℂ) • J) (fun _ => (c : ℂ) • (1 : P →L[ℂ] P))
    (fun k => (-(σ : ℂ)) • (J† ∘L D k)) T z hQ hw hq hSRight hSLeft hSNorm hCoupling
    hTransfer

/-- The sharp filter schedule controls the slot-dependent private block. -/
theorem filter_precisionV
    (D R1 : ℕ → V →L[ℂ] V) (J : P →L[ℂ] V) (H : ℕ → P →L[ℂ] P)
    (c κ σ w Q b qbar : ℝ) (T : ℕ)
    (hQ : 1 ≤ Q) (hw : 0 ≤ w) (hκ : 0 ≤ κ) (hκUpper : κ ≤ 2 / 9)
    (hκc : κ = 1 - c) (hσc : σ ^ 2 = 1 - c ^ 2) (hσw : σ ^ 2 ≤ 2 * w)
    (hD : ∀ k, (D k)† ∘L D k = 1) (hJ : J† ∘L J = 1)
    (hRight : ∀ k, (1 - D k) ∘L R1 k = 1) (hLeft : ∀ k, R1 k ∘L (1 - D k) = 1)
    (hR1 : ∀ k, ‖R1 k‖ ≤ Q)
    (hBoundary : ∀ k, J† ∘L R1 k ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H k))
    (hSelf : ∀ k, star (H k) = H k) (hH : ∀ k, ‖H k‖ ≤ 1)
    (hEndpoint : ∀ k, ‖R1 k ∘L J‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (δ : ℝ) (hδ : 0 < δ) (hδOne : δ ≤ 1) :
    ‖averagedGeometricFilter (privateV D J c κ σ T)
      (SharpFilterSchedule.length Q) ^
        SharpFilterSchedule.depth Q ((T : ℝ) * w * qbar) δ‖ ≤ δ ∧
    6 * ((T : ℝ) * w * qbar) ≤
      (SharpFilterSchedule.degree Q ((T : ℝ) * w * qbar) δ : ℝ) ∧
    (SharpFilterSchedule.degree Q ((T : ℝ) * w * qbar) δ : ℝ) ≤
      128 * ((T : ℝ) * w * qbar + Q * (1 + Real.log (1 / δ))) := by
  have hb : 0 ≤ b := (norm_nonneg _).trans (hEndpoint 0)
  have hq : 0 ≤ qbar := by nlinarith [sq_nonneg b]
  have hW : 0 ≤ (T : ℝ) * w * qbar := by positivity
  have hQpos : 0 < Q := by linarith
  have hContract := privateV_norm_le_one D J hJ hD c κ σ hκc hσc T
  have hdisk (z : ℂ) (hz : ‖z - 1‖ ≤ 1 / (4 * Q)) :=
    exists_privateV_resolvent D R1 J H c κ σ w Q b qbar T z hQpos hw hκ hκUpper
      hκc hσc hσw hD hJ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ hz
  have hdecay := FilterDecay.filter_norm_le_clock_scale
    (privateV D J c κ σ T) (SharpFilterSchedule.length Q)
    (SharpFilterSchedule.depth Q ((T : ℝ) * w * qbar) δ) Q
    (3 * (Q + (T : ℝ) * w * qbar) * Real.exp (3 * ((T : ℝ) * w * qbar) / (4 * Q)))
    hQpos (SharpFilterSchedule.length_ge Q) (SharpFilterSchedule.depth_pos _ _ _)
    hContract hdisk
  refine ⟨?_, SharpFilterSchedule.degree_ge_six Q _ δ hQ hW hδ hδOne,
    SharpFilterSchedule.degree_le Q _ δ hQ hW hδ hδOne⟩
  refine hdecay.trans (le_of_eq_of_le ?_ (SharpFilterSchedule.quarter_decay_le Q _ δ hQ hW hδ))
  unfold FilterSchedule.prefactor
  ring

end Hilbert

end

end SparseHamiltonian.TimeDependent
