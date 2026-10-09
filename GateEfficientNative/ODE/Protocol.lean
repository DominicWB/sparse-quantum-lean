import GateEfficientNative.ODE.Certificate
import GateEfficientODE.Protocol

/-!
# The native four-attempt protocol

The native trial circuits are read as released multi-oracle programs whose
labels are the native instructions and whose oracle input is the family of
primitive oracles (`nprogram`), so weighted costs count elementary gates and
primitive calls exactly (`nprogram_cost`).  The protocol is the released
bounded four-attempt wrapper: an attempt draws a uniform trial count
`j < chosenIterations g`, prepares the native seed, runs `trialN prepN j` and
measures the clean-output herald `goodN`.

* `nprotocol_worst`: worst-case counts over every history, including four
  failures.
* `noutcome`: if the native preparation is unitary, keeps the native flag
  and pool clean and its decoded vector is within the released certificate's
  error budget enlarged to `9νB`, the protocol succeeds with probability at
  least `175/256 > 2/3` and its conditional output is a density operator within
  trace distance `ε` of the normalised solution.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateODE (OInstr OWire AW goodF)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-! ### Native circuits as released programs -/

section Programs

variable {V Y J : Type*} [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y]

/-- Every native instruction is a named oracle of the released program model,
evaluated at the family of primitive oracles. -/
def nfamily : NInstr V Y J → (J → Reg Y ℂ →L[ℂ] Reg Y ℂ) → Reg V ℂ →L[ℂ] Reg V ℂ :=
  fun i prim => i.eval prim

/-- A native circuit as a released multi-oracle program. -/
def ntoProgram :
    List (NInstr V Y J) → MultiOracleCircuit.Program (nfamily (V := V) (Y := Y) (J := J))
  | [] => .identity
  | i :: is => .seq (ntoProgram is) (.query i)

theorem ntoProgram_eval (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (is : List (NInstr V Y J)) :
    (ntoProgram is).eval prim = nrun prim is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      rw [ntoProgram, MultiOracleCircuit.Program.eval_seq, ih,
        MultiOracleCircuit.Program.eval_query, nrun_cons, mul_def]
      rfl

theorem ntoProgram_cost (is : List (NInstr V Y J)) (w : NInstr V Y J → ℕ) :
    (ntoProgram (V := V) is).cost w = (is.map w).sum := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      rw [ntoProgram, MultiOracleCircuit.Program.cost_seq, ih,
        MultiOracleCircuit.Program.cost_query, List.map_cons, List.sum_cons, add_comm]

/-- Counts elementary gates. -/
def wGateN : NInstr V Y J → ℕ := fun i => if i.isGate then 1 else 0

/-- Counts primitive calls of the oracles satisfying `p`, forward or inverse. -/
def wCallN (p : J → Bool) : NInstr V Y J → ℕ := fun i => if i.isCall p then 1 else 0

omit [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] in
theorem sum_indicator (q : NInstr V Y J → Bool) (is : List (NInstr V Y J)) :
    (is.map (fun i => if q i then 1 else 0)).sum = is.countP q := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
      by_cases h : q i = true
      · simp [h, add_comm]
      · simp [h]

theorem ntoProgram_counts (is : List (NInstr V Y J)) (p : J → Bool) :
    (ntoProgram (V := V) is).cost wGateN = nGatesN is ∧
    (ntoProgram (V := V) is).cost (wCallN p) = nCallsN p is := by
  constructor
  · rw [ntoProgram_cost]; exact sum_indicator _ _
  · rw [ntoProgram_cost]; exact sum_indicator _ _

end Programs

/-! ### The protocol -/

section Protocol

variable {a m r K k l f : ℕ} {S Zs Z Y J : Type*} {nP bT bP A : ℕ}
variable [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y]

/-- The native trial with `j` steps as a released program. -/
def nprogram (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) (j : ℕ) :
    MultiOracleCircuit.Program (nfamily (V := HWO a m r K k l f S Zs nP Z bT bP A) (Y := Y)
      (J := J)) :=
  ntoProgram (trialN prepN j)

/-- **The native four-attempt protocol.**  It depends only on the native
preparation circuit and the public bound `g`. -/
def nprotocol (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) (g : ℝ)
    (hg : 1 ≤ g) :
    ODERepeatProtocol.Protocol (nfamily (V := HWO a m r K k l f S Zs nP Z bT bP A) (Y := Y)
      (J := J)) (Reg S ℂ) :=
  ODERepeatProtocol.fourTrials (nprogram prepN) (ODEGroverAverage.chosenIterations g)
    (ODEGroverAverage.chosenIterations_bounds g hg).1 sN norm_sN goodN goodN_isometry

/-- The public trial family. -/
def ntrials (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) (g : ℝ)
    (hg : 1 ≤ g) :
    ODERepeatProtocol.TrialFamily (nfamily (V := HWO a m r K k l f S Zs nP Z bT bP A) (Y := Y)
      (J := J)) (Reg S ℂ) :=
  ODERepeatProtocol.ofCircuits (nprogram prepN) (ODEGroverAverage.chosenIterations g)
    (ODEGroverAverage.chosenIterations_bounds g hg).1 sN norm_sN goodN goodN_isometry

theorem ntrial_cost_bound (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (g : ℝ) (hg : 1 ≤ g) (j : ℕ) (hj : j < ODEGroverAverage.chosenIterations g) (p : J → Bool) :
    ((nprogram prepN j).cost wGateN : ℝ) ≤
      10 * g * nGatesN prepN +
        5 * g * (4 * (Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) +
          Fintype.card Zs + Fintype.card S) + 3) ∧
    ((nprogram prepN j).cost (wCallN p) : ℝ) ≤ 10 * g * nCallsN p prepN := by
  obtain ⟨cG, cC⟩ := ntoProgram_counts (trialN prepN j) p
  have hM := (ODEGroverAverage.chosenIterations_bounds g hg).2.2
  have hjM : (j : ℝ) + 1 ≤ ODEGroverAverage.chosenIterations g := by exact_mod_cast hj
  have hj1 : (2 * (j : ℝ) + 1) ≤ 10 * g := by linarith
  have hj2 : (j : ℝ) ≤ 5 * g := by linarith
  unfold nprogram
  rw [cG, cC, trialN_nCalls]
  constructor
  · have h := trialN_nGates (Y := Y) (J := J) prepN j
    have h' : (nGatesN (trialN prepN j) : ℝ) ≤ (2 * j + 1) * nGatesN prepN +
        j * (4 * (Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) +
          Fintype.card Zs + Fintype.card S) + 3) := by exact_mod_cast h
    have h1 : (2 * (j : ℝ) + 1) * nGatesN prepN ≤ 10 * g * nGatesN prepN :=
      mul_le_mul_of_nonneg_right hj1 (Nat.cast_nonneg _)
    have h2 : (j : ℝ) * (4 * (Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) +
          Fintype.card Zs + Fintype.card S) + 3 : ℕ) ≤
        5 * g * (4 * (Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) +
          Fintype.card Zs + Fintype.card S) + 3 : ℕ) :=
      mul_le_mul_of_nonneg_right hj2 (Nat.cast_nonneg _)
    push_cast at h' h2 ⊢
    linarith
  · push_cast
    have h1 : (2 * (j : ℝ) + 1) * nCallsN p prepN ≤ 10 * g * nCallsN p prepN :=
      mul_le_mul_of_nonneg_right hj1 (Nat.cast_nonneg _)
    linarith

/-- **Worst-case counts of the native protocol**, over every history. -/
theorem nprotocol_worst (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (g : ℝ) (hg : 1 ≤ g) (p : J → Bool) :
    ((nprotocol prepN g hg).worstCost wGateN : ℝ) ≤
      40 * g * nGatesN prepN +
        20 * g * (4 * (Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) +
          Fintype.card Zs + Fintype.card S) + 3) ∧
    ((nprotocol prepN g hg).worstCost (wCallN p) : ℝ) ≤ 40 * g * nCallsN p prepN := by
  have hW := fun w B (h : ∀ j, j < ODEGroverAverage.chosenIterations g →
      ((nprogram prepN j).cost w : ℝ) ≤ B) =>
    ODERepeatProtocol.fourTrials_worstCost_le (nprogram prepN) (ODEGroverAverage.chosenIterations g)
      (ODEGroverAverage.chosenIterations_bounds g hg).1 sN norm_sN goodN goodN_isometry w B h
  constructor
  · have h := hW wGateN _ (fun j hj => (ntrial_cost_bound prepN g hg j hj p).1)
    unfold nprotocol
    linarith
  · have h := hW (wCallN p) _ (fun j hj => (ntrial_cost_bound prepN g hg j hj p).2)
    unfold nprotocol
    linarith

theorem ntrials_eval (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (g : ℝ) (hg : 1 ≤ g) (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (j : Fin (ntrials prepN g hg).choices) :
    ((ntrials prepN g hg).circuit j).eval prim = nrun prim (trialN prepN j.val) :=
  ntoProgram_eval prim _

theorem ntrials_amplitude (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (g : ℝ) (hg : 1 ≤ g) (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (j : Fin (ntrials prepN g hg).choices) :
    (ntrials prepN g hg).amplitude prim j = (goodN†) (nrun prim (trialN prepN j.val) sN) := by
  change (goodN†) (((ntrials prepN g hg).circuit j).eval prim sN) = _
  rw [ntrials_eval]

/-- The guarantees of the native protocol for one instance. -/
structure NOutcome (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (g ε : ℝ) (hg : 1 ≤ g) (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (x : Reg S ℂ) : Prop where
  unitary_trials : ∀ j, IsUnitary (nrun prim (trialN prepN j))
  mean_success : (1 : ℝ) / 4 ≤
    (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations g),
      ‖ODEHeraldedSuccess.successProjector goodN (nrun prim (trialN prepN j) sN)‖ ^ 2) /
      (ODEGroverAverage.chosenIterations g : ℝ)
  trial_direction : ∀ j : ℕ, (goodN†) (nrun prim (trialN prepN j) sN) ≠ 0 →
    ∃ ω : ℂ, ‖ω‖ = 1 ∧
      ‖ω • unitDirection ((goodN†) (nrun prim (trialN prepN j) sN)) - unitDirection x‖ ≤ ε / 500
  success_lower : (175 : ℝ) / 256 ≤ (nprotocol prepN g hg).successMass prim
  success_two_thirds : (2 : ℝ) / 3 ≤ (nprotocol prepN g hg).successMass prim
  output_density : ODEMixedOutput.IsDensity ((nprotocol prepN g hg).conditionalDensity prim)
  conditional_error :
    ∃ h : ((nprotocol prepN g hg).conditionalDensity prim -
        ODEMixedOutput.pureOperator (unitDirection x)).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance ((nprotocol prepN g hg).conditionalDensity prim)
        (ODEMixedOutput.pureOperator (unitDirection x)) h ≤ ε

/-- **The native protocol is correct** whenever its trials are valid and the
mean success and direction bounds of the trial circuits hold. -/
theorem noutcome_of_bounds (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j))
    (hvalid : ∀ i ∈ prepN, i.Valid) (x : Reg S ℂ) (hx : x ≠ 0) (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε)
    (hmean : (1 : ℝ) / 4 ≤
      (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations g),
        ‖ODEHeraldedSuccess.successProjector goodN (nrun prim (trialN prepN j) sN)‖ ^ 2) /
        (ODEGroverAverage.chosenIterations g : ℝ))
    (hdir : ∀ j : ℕ, (goodN†) (nrun prim (trialN prepN j) sN) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection ((goodN†) (nrun prim (trialN prepN j) sN)) - unitDirection x‖ ≤
          ε / 500) :
    NOutcome prepN g ε hg prim x := by
  have hunit : ∀ j, IsUnitary (nrun prim (trialN prepN j)) := fun j =>
    nrun_isUnitary prim hprim _ (trialN_valid prepN hvalid j)
  have hunitT : ∀ j, IsUnitary (((ntrials prepN g hg).circuit j).eval prim) := by
    intro j
    rw [ntrials_eval]
    exact hunit _
  have hprob : ∀ j, (ntrials prepN g hg).probability prim j =
      ‖ODEHeraldedSuccess.successProjector goodN (nrun prim (trialN prepN j.val) sN)‖ ^ 2 := by
    intro j
    rw [(ntrials prepN g hg).probability_eq_projected prim j, ntrials_eval]
    rfl
  have hsumP : ∑ j : Fin (ntrials prepN g hg).choices, (ntrials prepN g hg).probability prim j =
      ∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations g),
        ‖ODEHeraldedSuccess.successProjector goodN (nrun prim (trialN prepN j) sN)‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun j _ => hprob j)]
    exact Fin.sum_univ_eq_sum_range (fun j => ‖ODEHeraldedSuccess.successProjector goodN
      (nrun prim (trialN prepN j) sN)‖ ^ 2) _
  have hmeanT : (1 : ℝ) / 4 ≤
      ODERepeatProbability.mean ((ntrials prepN g hg).probability prim) := by
    unfold ODERepeatProbability.mean
    rw [hsumP]
    exact hmean
  have hupper : ODERepeatProbability.mean ((ntrials prepN g hg).probability prim) ≤ 1 :=
    ODERepeatProbability.mean_le_one _ (ntrials prepN g hg).choices_pos
      (fun j => ((ntrials prepN g hg).probability_bounds prim hunitT j).2)
  have hnonneg : ∀ j, 0 ≤ (ntrials prepN g hg).probability prim j :=
    fun j => ((ntrials prepN g hg).probability_bounds prim hunitT j).1
  have hsucc : (nprotocol prepN g hg).successMass prim =
      ODERepeatProbability.successProbability ((ntrials prepN g hg).probability prim) :=
    ODERepeatProtocol.Protocol.four_successMass_eq (ntrials prepN g hg) prim
  have hdens : (nprotocol prepN g hg).conditionalDensity prim =
      ODEMixedOutput.ensemble
        (ODERepeatProbability.conditionalWeight ((ntrials prepN g hg).probability prim))
        (fun a => (ntrials prepN g hg).outputDirection prim a.2) :=
    ODERepeatProtocol.Protocol.four_conditionalDensity_eq (ntrials prepN g hg) prim
  have hw := ODERepeatProbability.conditionalWeight_nonneg _ hnonneg hmeanT hupper
  have hsum := ODERepeatProbability.conditionalWeight_sum _ hmeanT hupper
  have hne : ∀ a : Fin 4 × Fin (ntrials prepN g hg).choices,
      ODERepeatProbability.conditionalWeight ((ntrials prepN g hg).probability prim) a ≠ 0 →
      (ntrials prepN g hg).amplitude prim a.2 ≠ 0 := by
    intro a ha hz
    apply ODERepeatProbability.conditionalWeight_ne_zero_implies _ a ha
    rw [ODERepeatProtocol.TrialFamily.probability, hz, norm_zero]
    norm_num
  have hclose : ∀ a : Fin 4 × Fin (ntrials prepN g hg).choices,
      ODERepeatProbability.conditionalWeight ((ntrials prepN g hg).probability prim) a ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • (ntrials prepN g hg).outputDirection prim a.2 -
        unitDirection x‖ ≤ ε / 500 := by
    intro a ha
    have hz := hne a ha
    rw [ntrials_amplitude] at hz
    have h := hdir a.2.val hz
    rw [ODERepeatProtocol.TrialFamily.outputDirection, ntrials_amplitude]
    exact h
  have hunitDir : ∀ a : Fin 4 × Fin (ntrials prepN g hg).choices,
      ODERepeatProbability.conditionalWeight ((ntrials prepN g hg).probability prim) a ≠ 0 →
      ‖(ntrials prepN g hg).outputDirection prim a.2‖ = 1 :=
    fun a ha => ODEStateNormalization.unitDirection_norm _ (hne a ha)
  obtain ⟨hDensity, hSymm, hDistance⟩ := ODEMixedOutput.ensemble_trace_distance_le
    (ODERepeatProbability.conditionalWeight ((ntrials prepN g hg).probability prim))
    (fun a => (ntrials prepN g hg).outputDirection prim a.2)
    (unitDirection x) (ε / 500) hw hsum hunitDir (ODEStateNormalization.unitDirection_norm _ hx)
    hclose
  have hlow : (175 : ℝ) / 256 ≤ (nprotocol prepN g hg).successMass prim := by
    rw [hsucc]
    exact ODERepeatProbability.successProbability_lower _ hmeanT hupper
  have htwo : (2 : ℝ) / 3 ≤ (nprotocol prepN g hg).successMass prim := by
    rw [hsucc]
    exact ODERepeatProbability.successProbability_two_thirds _ hmeanT hupper
  have hden : ODEMixedOutput.IsDensity ((nprotocol prepN g hg).conditionalDensity prim) := by
    rw [hdens]
    exact hDensity
  have herr : ∃ h : ((nprotocol prepN g hg).conditionalDensity prim -
        ODEMixedOutput.pureOperator (unitDirection x)).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance ((nprotocol prepN g hg).conditionalDensity prim)
        (ODEMixedOutput.pureOperator (unitDirection x)) h ≤ ε := by
    rw [hdens]
    refine ⟨hSymm, hDistance.trans ?_⟩
    linarith
  exact ⟨hunit, hmean, hdir, hlow, htwo, hden, herr⟩

/-- **The native protocol is correct** whenever its preparation is a unitary
that keeps the native flag and pool clean and lies within `ν` of a released
preparation whose decoded vector meets the released vector error. -/
theorem noutcome
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
      Fintype.card S ≤ nP + 1)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j))
    (hvalid : ∀ i ∈ prepN, i.Valid)
    (hP : Pres2 (ZeroOn reflWire) (nrun prim prepN))
    (Urel : Reg (AW a m r K k l f) (Reg S ℂ) →L[ℂ] Reg (AW a m r K k l f) (Reg S ℂ))
    {δ : ℝ} (hA : ApproxOn CleanX (nrun prim prepN) (liftB (conj Urel)) δ)
    (x : Reg S ℂ) (B g ε : ℝ) (hx : x ≠ 0) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hNorm : ‖x‖ ≤ B) (hBudget : B ≤ g * ‖x‖)
    (hrel : ‖(3 * B) • (goodF†) (Urel (GateODE.seedState seedV)) - x‖ ≤
      6 * ImprovedODEQueryBudget.precision g ε * B)
    (hδ : δ ≤ ImprovedODEQueryBudget.precision g ε) :
    NOutcome prepN g ε hg prim x := by
  have hU : IsUnitary (nrun prim prepN) := nrun_isUnitary prim hprim _ hvalid
  obtain ⟨-, -, hmean, hdir⟩ := native_trial_bounds prim hnP prepN hU hP Urel hA x B g ε hx hg hε
    hεHalf hNorm hBudget hrel hδ
  exact noutcome_of_bounds prepN prim hprim hvalid x hx g ε hg hε hmean hdir

end Protocol

end

end SparseHamiltonian.GateNative
