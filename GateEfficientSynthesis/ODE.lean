import GateEfficientSynthesis.Hamiltonian
import GateEfficientSynthesis.Perturb
import GateEfficientNative.ODE.Time

/-!
# Theorem `ode:thm:gates` over a finite gate set: the four-attempt protocol

The native four-attempt protocol `nprotocol prepN g` of `GateEfficientNative` draws a uniform
trial count `j < chosenIterations g` and runs the native trial `trialN prepN j`, a circuit of
elementary gates and primitive oracle calls. Under the synthesis hypothesis
`Synthesis 𝒢 X len`, the synthesised protocol `sprotocol hS η prepN g` runs instead the
synthesis of every trial with the synthesis budget `η` (`synthBudget`), on the native register
with the synthesis ancillas `X` added, from the native seed with clean ancillas (`sseed`), and
measures the native herald with clean ancillas (`sgood`).

* `sprotocol_valid`: every synthesised trial consists of valid gates of `𝒢` and primitive
  calls.
* `sprotocol_worst`, `sprotocol_worst_log`: worst-case counts over every history. Every
  synthesised trial makes the primitive calls of the native trial, so the protocol makes at most
  `40 g` times the calls of the preparation, the native bound; with `len ζ ≤ c₁ log(1/ζ) + c₀`
  the elementary gates are at most the native gate bound times `c₁ log((G+1)/η) + c₀`, `G` the
  native gate bound of one trial.
* `soutcome`: if the native protocol has its guarantees for an instance (`NOutcome`) and
  `η ≤ min(1/400, ε/20)`, the synthesised protocol succeeds with probability at least `2/3` and
  its conditional output is a density operator within trace distance `ε` of the normalised
  target (`SOutcome`). The proof perturbs the decoded amplitudes of the trials by at most `η`
  (`perturb_four`). Unlike `NOutcome`, `SOutcome` makes no claim about single trials: every gate
  of a trial, the reflections included, is synthesised, and the output direction of a trial whose
  native success amplitude is at most about `η` is not controlled; such a trial succeeds with
  probability `O(η²)`, which the bound on the conditional output accounts for.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSynth

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open GateODE (AW)
open ODEStateNormalization (unitDirection unitDirection_norm)
open scoped InnerProduct BigOperators

/-! ### The guarantees of a protocol -/

section Outcome

variable {S : Type*} [Fintype S] [DecidableEq S]
variable {L' X' K' : Type*} [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']

/-- The guarantees of a four-attempt protocol for one instance (oracle input `prim`): success
probability at least `2/3`, and a conditional output that is a density operator within trace
distance `ε` of the normalised target `x`. -/
structure SOutcome {O : L' → X' → K' →L[ℂ] K'} (P : ODERepeatProtocol.Protocol O (Reg S ℂ))
    (ε : ℝ) (prim : X') (x : Reg S ℂ) : Prop where
  success_two_thirds : (2 : ℝ) / 3 ≤ P.successMass prim
  output_density : ODEMixedOutput.IsDensity (P.conditionalDensity prim)
  conditional_error :
    ∃ h : (P.conditionalDensity prim -
        ODEMixedOutput.pureOperator (unitDirection x)).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance (P.conditionalDensity prim)
        (ODEMixedOutput.pureOperator (unitDirection x)) h ≤ ε

end Outcome

/-! ### The synthesised protocol -/

section Protocol

variable {a m r K k l f : ℕ} {S Zs Z Y J X : Type*} {nP bT bP A : ℕ}
variable [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- The seed of the synthesised trials: the native seed with clean synthesis ancillas. -/
def sseed : Reg (HWO a m r K k l f S Zs nP Z bT bP A ⊕ X) ℂ := cleanEmb sN

theorem norm_sseed :
    ‖(sseed : Reg (HWO a m r K k l f S Zs nP Z bT bP A ⊕ X) ℂ)‖ = 1 := by
  rw [sseed, norm_cleanEmb, norm_sN]

/-- The clean output encoding of the synthesised register: the native one with clean synthesis
ancillas. -/
def sgood : Reg S ℂ →L[ℂ] Reg (HWO a m r K k l f S Zs nP Z bT bP A ⊕ X) ℂ :=
  cleanEmb ∘L goodN

theorem sgood_isometry :
    (sgood : Reg S ℂ →L[ℂ] Reg (HWO a m r K k l f S Zs nP Z bT bP A ⊕ X) ℂ)† ∘L sgood = 1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp
    (fun ψ => by rw [sgood, comp_apply, norm_cleanEmb, norm_goodN])

/-- The synthesised trial with `j` steps as a released program. -/
def sprogram (hS : Synthesis 𝒢 X len) (η : ℝ)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) (j : ℕ) :
    MultiOracleCircuit.Program
      (nfamily (V := HWO a m r K k l f S Zs nP Z bT bP A ⊕ X) (Y := Y) (J := J)) :=
  ntoProgram (synthBudget hS η (trialN prepN j))

/-- The public trial family of the synthesised protocol. -/
def strials (hS : Synthesis 𝒢 X len) (η : ℝ)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) (g : ℝ) (hg : 1 ≤ g) :
    ODERepeatProtocol.TrialFamily
      (nfamily (V := HWO a m r K k l f S Zs nP Z bT bP A ⊕ X) (Y := Y) (J := J)) (Reg S ℂ) :=
  ODERepeatProtocol.ofCircuits (sprogram hS η prepN) (ODEGroverAverage.chosenIterations g)
    (ODEGroverAverage.chosenIterations_bounds g hg).1 sseed norm_sseed sgood sgood_isometry

/-- **The synthesised four-attempt protocol.** It depends only on the native preparation
circuit, the public bound `g`, the synthesis hypothesis and the synthesis budget `η`. -/
def sprotocol (hS : Synthesis 𝒢 X len) (η : ℝ)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) (g : ℝ) (hg : 1 ≤ g) :
    ODERepeatProtocol.Protocol
      (nfamily (V := HWO a m r K k l f S Zs nP Z bT bP A ⊕ X) (Y := Y) (J := J)) (Reg S ℂ) :=
  ODERepeatProtocol.fourTrials (sprogram hS η prepN) (ODEGroverAverage.chosenIterations g)
    (ODEGroverAverage.chosenIterations_bounds g hg).1 sseed norm_sseed sgood sgood_isometry

omit [Fintype Y] [DecidableEq Y] in
/-- **Every synthesised trial consists of valid gates of `𝒢` and primitive calls.** -/
theorem sprotocol_valid (hS : Synthesis 𝒢 X len) {η : ℝ} (hη : 0 < η)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ j, ∀ i ∈ trialN prepN j, i.Valid) (j : ℕ) :
    (∀ i ∈ synthBudget hS η (trialN prepN j), i.Valid) ∧
      ∀ g, NInstr.gate g ∈ synthBudget hS η (trialN prepN j) → GateOf 𝒢 g :=
  let h := synthBudget_spec hS hη _ (hvalid j)
  ⟨h.1, h.2.1⟩

/-- The counts of one synthesised trial. -/
theorem sprogram_counts (hS : Synthesis 𝒢 X len) {η : ℝ} (hη : 0 < η)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ j, ∀ i ∈ trialN prepN j, i.Valid) (j : ℕ) (q : J → Bool) :
    (sprogram hS η prepN j).cost wGateN ≤
      nGatesN (trialN prepN j) * len (η / (nGatesN (trialN prepN j) + 1)) ∧
    (sprogram hS η prepN j).cost (wCallN q) = (nprogram prepN j).cost (wCallN q) := by
  obtain ⟨cG, cC⟩ := ntoProgram_counts (synthBudget hS η (trialN prepN j)) q
  obtain ⟨-, -, hG, hC⟩ := synthBudget_spec hS hη _ (hvalid j)
  refine ⟨?_, ?_⟩
  · rw [sprogram, cG]
    exact hG
  · rw [sprogram, cC, hC q, nprogram, (ntoProgram_counts (trialN prepN j) q).2]

/-- **Worst-case counts of the synthesised protocol**, over every history: at most four times a
bound on the gates of the synthesised trials, and at most `40 g` times the primitive calls of the
native preparation (the native bound). -/
theorem sprotocol_worst (hS : Synthesis 𝒢 X len) {η : ℝ} (hη : 0 < η)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ j, ∀ i ∈ trialN prepN j, i.Valid) (g : ℝ) (hg : 1 ≤ g) (q : J → Bool) :
    (∀ B : ℝ, (∀ j, j < ODEGroverAverage.chosenIterations g →
        ((nGatesN (trialN prepN j) * len (η / (nGatesN (trialN prepN j) + 1)) : ℕ) : ℝ) ≤ B) →
      ((sprotocol hS η prepN g hg).worstCost wGateN : ℝ) ≤ 4 * B) ∧
    ((sprotocol hS η prepN g hg).worstCost (wCallN q) : ℝ) ≤ 40 * g * nCallsN q prepN := by
  have hW := fun w B (h : ∀ j, j < ODEGroverAverage.chosenIterations g →
      ((sprogram hS η prepN j).cost w : ℝ) ≤ B) =>
    ODERepeatProtocol.fourTrials_worstCost_le (sprogram hS η prepN)
      (ODEGroverAverage.chosenIterations g) (ODEGroverAverage.chosenIterations_bounds g hg).1
      sseed norm_sseed sgood sgood_isometry w B h
  refine ⟨fun B hB => hW wGateN B (fun j hj => ?_), ?_⟩
  · exact (Nat.cast_le.mpr (sprogram_counts hS hη prepN hvalid j q).1).trans (hB j hj)
  · have h := hW (wCallN q) (10 * g * nCallsN q prepN) (fun j hj => by
      rw [(sprogram_counts hS hη prepN hvalid j q).2]
      exact (ntrial_cost_bound prepN g hg j hj q).2)
    unfold sprotocol
    linarith

/-- **Worst-case gate count of the synthesised protocol with logarithmic synthesis length**: if
`len ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]` and `η ≤ 1`, then in every history the synthesised
protocol uses at most `(40 g N + 20 g (4 n + 3)) (c₁ log((G + 1)/η) + c₀)` elementary gates,
`N` the gates of the native preparation, `n` the wires tested by the seed reflection and
`G = 10 g N + 5 g (4 n + 3)` the native gate bound of one trial. -/
theorem sprotocol_worst_log (hS : Synthesis 𝒢 X len) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ j, ∀ i ∈ trialN prepN j, i.Valid) (g : ℝ) (hg : 1 ≤ g) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (len ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀) :
    ((sprotocol hS η prepN g hg).worstCost wGateN : ℝ) ≤
      (40 * g * nGatesN prepN +
        20 * g * (4 * (Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) +
          Fintype.card Zs + Fintype.card S) + 3)) *
      (c₁ * Real.log ((10 * g * nGatesN prepN +
        5 * g * (4 * (Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) +
          Fintype.card Zs + Fintype.card S) + 3) + 1) / η) + c₀) := by
  have h := (sprotocol_worst hS hη prepN hvalid g hg (fun _ => true)).1 _ (fun j hj =>
    gates_log_le hc₀ hc₁ hlen hη hη1 _ _ (by
      have h1 := (ntrial_cost_bound prepN g hg j hj (fun _ => true)).1
      rwa [nprogram, (ntoProgram_counts (trialN prepN j) (fun _ => true)).1] at h1))
  refine h.trans (le_of_eq ?_)
  ring

/-- An isometry has a contractive adjoint. -/
theorem norm_adjoint_apply_le {E' K'' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
    [CompleteSpace E'] [NormedAddCommGroup K''] [InnerProductSpace ℂ K''] [CompleteSpace K'']
    (F : E' →L[ℂ] K'') (hF : F† ∘L F = 1) (w : K'') : ‖(F†) w‖ ≤ ‖w‖ := by
  have h := ODERepeatProtocol.herald_probability_partition F hF w
  have h0 := sq_nonneg ‖w - F ((F†) w)‖
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith)

theorem strials_eval (hS : Synthesis 𝒢 X len) (η : ℝ)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) (g : ℝ) (hg : 1 ≤ g)
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (j : Fin (strials hS η prepN g hg).choices) :
    ((strials hS η prepN g hg).circuit j).eval prim =
      nrun prim (synthBudget hS η (trialN prepN j.val)) :=
  ntoProgram_eval prim _

theorem strials_amplitude (hS : Synthesis 𝒢 X len) (η : ℝ)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) (g : ℝ) (hg : 1 ≤ g)
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (j : Fin (strials hS η prepN g hg).choices) :
    (strials hS η prepN g hg).amplitude prim j =
      (sgood†) (nrun prim (synthBudget hS η (trialN prepN j.val)) sseed) := by
  change (sgood†) (((strials hS η prepN g hg).circuit j).eval prim sseed) = _
  rw [strials_eval]

/-- The synthesised decoded amplitude of a trial is within `η` of the native one. -/
theorem strials_close (hS : Synthesis 𝒢 X len) {η : ℝ} (hη : 0 < η)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ j, ∀ i ∈ trialN prepN j, i.Valid) (g : ℝ) (hg : 1 ≤ g)
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j))
    (j : Fin (strials hS η prepN g hg).choices) :
    ‖(strials hS η prepN g hg).amplitude prim j -
      (goodN†) (nrun prim (trialN prepN j.val) sN)‖ ≤ η := by
  rw [strials_amplitude]
  have hC := hvalid j.val
  generalize trialN prepN j.val = C at hC ⊢
  have hN1 : (0 : ℝ) < nGatesN C + 1 := by positivity
  have hζ : 0 < η / (nGatesN C + 1) := div_pos hη hN1
  have hA := norm_sub_cleanEmb_le (X := X) (synthC_approxOn prim hS hζ C hC hprim)
    (mul_nonneg (Nat.cast_nonneg _) hζ.le)
  have e1 : (goodN†) (nrun prim C sN) =
      ((sgood : Reg S ℂ →L[ℂ] Reg (HWO a m r K k l f S Zs nP Z bT bP A ⊕ X) ℂ)†)
        (cleanEmb (nrun prim C sN)) := by
    have hcl : ((cleanEmb (B := HWO a m r K k l f S Zs nP Z bT bP A) (X := X) (R := ℂ))†)
        (cleanEmb (nrun prim C sN)) = nrun prim C sN := by
      rw [← comp_apply, cleanEmb_isometry, one_apply_eq_self]
    rw [sgood, adjoint_comp, comp_apply, hcl]
  rw [e1, ← map_sub]
  refine (norm_adjoint_apply_le _ sgood_isometry _).trans ?_
  have e2 : nrun prim (synthBudget hS η C) sseed - cleanEmb (nrun prim C sN) =
      (nrun prim (synthC hS (η / (nGatesN C + 1)) C) ∘L cleanEmb -
        cleanEmb ∘L nrun prim C : Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ →L[ℂ]
          Reg (HWO a m r K k l f S Zs nP Z bT bP A ⊕ X) ℂ) sN := by
    rw [sub_apply, comp_apply, comp_apply]
    rfl
  rw [e2]
  refine (le_opNorm _ _).trans ?_
  rw [norm_sN, mul_one]
  refine hA.trans ?_
  rw [mul_div_assoc', div_le_iff₀ hN1]
  nlinarith

/-- The native mean success in the form of the native trial family. -/
theorem ntrials_mean (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) (g : ℝ)
    (hg : 1 ≤ g) (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (ε : ℝ) (x : Reg S ℂ)
    (hN : NOutcome prepN g ε hg prim x) :
    (1 : ℝ) / 4 ≤ ODERepeatProbability.mean ((ntrials prepN g hg).probability prim) := by
  have hprob : ∀ j, (ntrials prepN g hg).probability prim j =
      ‖ODEHeraldedSuccess.successProjector goodN (nrun prim (trialN prepN j.val) sN)‖ ^ 2 := by
    intro j
    rw [(ntrials prepN g hg).probability_eq_projected prim j, ntrials_eval]
    rfl
  unfold ODERepeatProbability.mean
  rw [Finset.sum_congr rfl (fun j _ => hprob j)]
  rw [Fin.sum_univ_eq_sum_range (fun j => ‖ODEHeraldedSuccess.successProjector goodN
    (nrun prim (trialN prepN j) sN)‖ ^ 2)]
  exact hN.mean_success

/-- **The synthesised protocol is correct** whenever the native protocol is: for an instance
with unitary primitive oracles on which the native protocol has its guarantees (`NOutcome`), a
synthesis budget `0 < η ≤ min(1/400, ε/20)` gives success probability at least `2/3` and a
conditional output within trace distance `ε` of the normalised target. -/
theorem soutcome (hS : Synthesis 𝒢 X len) {η ε : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 400)
    (hηε : η ≤ ε / 20) (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ j, ∀ i ∈ trialN prepN j, i.Valid) (g : ℝ) (hg : 1 ≤ g)
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j)) (x : Reg S ℂ)
    (hx : x ≠ 0) (hN : NOutcome prepN g ε hg prim x) :
    SOutcome (sprotocol hS η prepN g hg) ε prim x := by
  have hε : 0 ≤ ε := by linarith
  have hunitS : ∀ j, IsUnitary (((strials hS η prepN g hg).circuit j).eval prim) := by
    intro j
    rw [strials_eval]
    exact nrun_isUnitary prim hprim _ (synthBudget_spec hS hη _ (hvalid j.val)).1
  have hunitN : ∀ j, IsUnitary (((ntrials prepN g hg).circuit j).eval prim) := by
    intro j
    rw [ntrials_eval]
    exact hN.unitary_trials _
  have hbS := (strials hS η prepN g hg).probability_bounds prim hunitS
  have hbN := (ntrials prepN g hg).probability_bounds prim hunitN
  have ha : ∀ j, ‖(ntrials prepN g hg).amplitude prim j‖ ≤ 1 := fun j =>
    (sq_le_one_iff₀ (norm_nonneg _)).mp (hbN j).2
  have ha' : ∀ j, ‖(strials hS η prepN g hg).amplitude prim j‖ ≤ 1 := fun j =>
    (sq_le_one_iff₀ (norm_nonneg _)).mp (hbS j).2
  have hclose : ∀ j : Fin (strials hS η prepN g hg).choices,
      ‖(strials hS η prepN g hg).amplitude prim j - (ntrials prepN g hg).amplitude prim j‖ ≤
        η := by
    intro j
    rw [ntrials_amplitude]
    exact strials_close hS hη prepN hvalid g hg prim hprim j
  have hdir : ∀ j : Fin (ntrials prepN g hg).choices, (ntrials prepN g hg).amplitude prim j ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection ((ntrials prepN g hg).amplitude prim j) - unitDirection x‖ ≤
          ε / 500 := by
    intro j hz
    rw [ntrials_amplitude] at hz ⊢
    exact hN.trial_direction j.val hz
  obtain ⟨hS2, hD, hh, htr⟩ := perturb_four (strials hS η prepN g hg).choices_pos
    ((ntrials prepN g hg).amplitude prim) ((strials hS η prepN g hg).amplitude prim)
    (unitDirection x) (unitDirection_norm x hx) (δ := ε / 500) (by positivity) hη1 ha ha' hclose
    (ntrials_mean prepN g hg prim ε x hN) hdir
  have hsucc : (sprotocol hS η prepN g hg).successMass prim =
      ODERepeatProbability.successProbability ((strials hS η prepN g hg).probability prim) :=
    ODERepeatProtocol.Protocol.four_successMass_eq (strials hS η prepN g hg) prim
  have hdens : (sprotocol hS η prepN g hg).conditionalDensity prim =
      ODEMixedOutput.ensemble
        (ODERepeatProbability.conditionalWeight ((strials hS η prepN g hg).probability prim))
        (fun b => (strials hS η prepN g hg).outputDirection prim b.2) :=
    ODERepeatProtocol.Protocol.four_conditionalDensity_eq (strials hS η prepN g hg) prim
  refine ⟨?_, ?_, ?_⟩
  · rw [hsucc]
    exact hS2
  · rw [hdens]
    exact hD
  · rw [hdens]
    exact ⟨hh, htr.trans (by linarith)⟩

end Protocol

end

end SparseHamiltonian.GateSynth
