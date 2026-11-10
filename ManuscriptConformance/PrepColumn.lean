import ManuscriptConformance.ODEUpper
import SourceAccuracyODE.Outcome

/-!
# The native protocol depends only on the column of its preparation (handover item D1, part)

Item D1 asks for a proof that the actual algorithm depends only on the allowed clean-input action
of the preparation and its image under the actual adjoint. This module proves that for the
amplification of the native four-attempt protocol `GateNative.nprotocol`. Its trials are the
preparation followed by the native amplification steps (good reflection, the literal inverse of the
preparation, seed reflection, preparation, global sign; `GateNative.stepN`). On the clean
reflection wire they are the actual Grover trials of the preparation (`GateNative.trialN_seed`).
Those depend on the preparation only through its column `U sN` on the seed, because the conjugated
seed reflection is `U (1 - 2|sN⟩⟨sN|) U† = 1 - 2|U sN⟩⟨U sN|` for a unitary `U`.

* `ODERepeatProtocol.fourTrials_law_congr`: the four-attempt protocol of a public trial family has
  the success mass and conditional output of any other with the same trial outputs on the seed.
* `GateNative.trialN_seed_congr`: two native preparations, unitary and preserving the clean
  reflection wire (`Pres2 (ZeroOn reflWire)`), with the same column have the same trial outputs.
  The primitives and the circuits may both differ.
* `GateNative.nprotocol_law_congr`: their protocols have the same success mass and conditional
  output.
* `SourceAccuracyODE.WOutcome.of_column`: the released guarantee `WOutcome` transfers to every valid
  preparation with the same column, for unitary primitives. This covers the per-trial directions,
  the mean success, the success masses and the conditional output.
* `ManuscriptConformance.heraldedOutput_of_column`: the same for `HeraldedOutput`.

Scope: this is the amplification half of D1, in the exact case. The other half is not proved: that
the column of the released preparations depends only on the loading circuit's action on its label
columns (a structural property of the macro expansion `tnprepC`). So the theorems here do not yet
weaken the loading hypotheses of the endpoints. Their use is to transfer every released guarantee
to a preparation known to agree with the released one on the seed.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.ODERepeatProtocol

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators InnerProduct

variable {E K X L X' L' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **The four-attempt protocol depends only on the trial outputs on the seed**: two public trial
families of circuits (over any oracle families, at any instances) whose evaluations agree on the
seed for every trial label have four-attempt protocols with the same success mass and conditional
output. -/
theorem fourTrials_law_congr {O : L → X → K →L[ℂ] K} {O' : L' → X' → K →L[ℂ] K}
    (q : ℕ → MultiOracleCircuit.Program O) (q' : ℕ → MultiOracleCircuit.Program O') (M : ℕ)
    (hM : 0 < M) (ψ : K) (hψ : ‖ψ‖ = 1) (F : E →L[ℂ] K) (hF : F† ∘L F = 1) (x : X) (x' : X')
    (h : ∀ j, j < M → (q j).eval x ψ = (q' j).eval x' ψ) :
    (fourTrials q M hM ψ hψ F hF).successMass x =
        (fourTrials q' M hM ψ hψ F hF).successMass x' ∧
      (fourTrials q M hM ψ hψ F hF).conditionalDensity x =
        (fourTrials q' M hM ψ hψ F hF).conditionalDensity x' := by
  have hamp : (ofCircuits q M hM ψ hψ F hF).amplitude x =
      (ofCircuits q' M hM ψ hψ F hF).amplitude x' := by
    funext j
    change (F†) ((q j.val).eval x ψ) = (F†) ((q' j.val).eval x' ψ)
    rw [h j.val j.isLt]
  have hprob : (ofCircuits q M hM ψ hψ F hF).probability x =
      (ofCircuits q' M hM ψ hψ F hF).probability x' := by
    funext j
    change ‖(ofCircuits q M hM ψ hψ F hF).amplitude x j‖ ^ 2 =
      ‖(ofCircuits q' M hM ψ hψ F hF).amplitude x' j‖ ^ 2
    rw [hamp]
  have hdir : (ofCircuits q M hM ψ hψ F hF).outputDirection x =
      (ofCircuits q' M hM ψ hψ F hF).outputDirection x' := by
    funext j
    change ODEStateNormalization.unitDirection ((ofCircuits q M hM ψ hψ F hF).amplitude x j) =
      ODEStateNormalization.unitDirection ((ofCircuits q' M hM ψ hψ F hF).amplitude x' j)
    rw [hamp]
  unfold fourTrials
  rw [Protocol.four_successMass_eq, Protocol.four_successMass_eq,
    Protocol.four_conditionalDensity_eq, Protocol.four_conditionalDensity_eq, hprob, hdir]
  exact ⟨rfl, rfl⟩

end

end SparseHamiltonian.ODERepeatProtocol

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateODE (AW)
open scoped InnerProduct BigOperators

variable {a m r K k l f : ℕ} {S Zs Z : Type*} {nP bT bP A : ℕ}
variable {Y J Y' J' : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z]
  [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

/-- **The native trials depend only on the column of the preparation**: for two native
preparations (on the same register, with any primitives and circuits) that are unitary and preserve
the clean reflection wire, with the same action on the seed, every trial has the same output on the
seed. -/
theorem trialN_seed_congr
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
      Fintype.card S ≤ nP + 1)
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (prim' : J' → Reg Y' ℂ →L[ℂ] Reg Y' ℂ)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (prepN' : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y' J'))
    (hU : IsUnitary (nrun prim prepN)) (hP : Pres2 (ZeroOn reflWire) (nrun prim prepN))
    (hU' : IsUnitary (nrun prim' prepN')) (hP' : Pres2 (ZeroOn reflWire) (nrun prim' prepN'))
    (hcol : nrun prim prepN sN = nrun prim' prepN' sN) (j : ℕ) :
    nrun prim (trialN prepN j) sN = nrun prim' (trialN prepN' j) sN := by
  rw [trialN_seed prim hnP prepN hU hP j, trialN_seed prim' hnP prepN' hU' hP' j]
  unfold ODEGroverActual.trial ODEGroverActual.actualG
  rw [hcol]

/-- **The native protocols of two preparations with the same column have the same law**: the same
success mass and the same conditional output. -/
theorem nprotocol_law_congr
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
      Fintype.card S ≤ nP + 1)
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (prim' : J' → Reg Y' ℂ →L[ℂ] Reg Y' ℂ)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (prepN' : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y' J'))
    (hU : IsUnitary (nrun prim prepN)) (hP : Pres2 (ZeroOn reflWire) (nrun prim prepN))
    (hU' : IsUnitary (nrun prim' prepN')) (hP' : Pres2 (ZeroOn reflWire) (nrun prim' prepN'))
    (hcol : nrun prim prepN sN = nrun prim' prepN' sN) (g : ℝ) (hg : 1 ≤ g) :
    (nprotocol prepN g hg).successMass prim = (nprotocol prepN' g hg).successMass prim' ∧
      (nprotocol prepN g hg).conditionalDensity prim =
        (nprotocol prepN' g hg).conditionalDensity prim' := by
  apply ODERepeatProtocol.fourTrials_law_congr
  intro j _
  change (ntoProgram (trialN prepN j)).eval prim sN = (ntoProgram (trialN prepN' j)).eval prim' sN
  rw [ntoProgram_eval, ntoProgram_eval]
  exact trialN_seed_congr hnP prim prim' prepN prepN' hU hP hU' hP' hcol j

end

end SparseHamiltonian.GateNative

namespace SparseHamiltonian.SourceAccuracyODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open GateODE (AW)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

variable {a m r K k l f : ℕ} {S Zs Z : Type*} {nP bT bP A : ℕ}
variable {Y J Y' J' : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z]
  [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

/-- **The released guarantee depends only on the column of the actual preparation**: if the native
protocol of `prepN` with the primitives `prim` has the guarantee `WOutcome … β` against `x`, then so
has that of every valid preparation `prepN'` with unitary primitives `prim'` that preserves the
clean reflection wire and acts on the seed as `prepN`. The per-trial directions, the mean success,
the success masses and the conditional output all transfer. -/
theorem WOutcome.of_column
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
      Fintype.card S ≤ nP + 1)
    {prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)}
    {prepN' : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y' J')} {g β : ℝ} {hg : 1 ≤ g}
    {prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ} {prim' : J' → Reg Y' ℂ →L[ℂ] Reg Y' ℂ} {x : Reg S ℂ}
    (h : WOutcome prepN g β hg prim x) (hP : Pres2 (ZeroOn reflWire) (nrun prim prepN))
    (hv' : ∀ i ∈ prepN', i.Valid) (hprim' : ∀ j, IsUnitary (prim' j))
    (hP' : Pres2 (ZeroOn reflWire) (nrun prim' prepN'))
    (hcol : nrun prim prepN sN = nrun prim' prepN' sN) :
    WOutcome prepN' g β hg prim' x := by
  have hU : IsUnitary (nrun prim prepN) := by
    have h0 := h.unitary_trials 0
    rwa [trialN, List.replicate_zero, List.flatten_nil, List.append_nil] at h0
  have hU' : IsUnitary (nrun prim' prepN') := nrun_isUnitary prim' hprim' _ hv'
  have ht := trialN_seed_congr hnP prim prim' prepN prepN' hU hP hU' hP' hcol
  obtain ⟨hm, hc⟩ := nprotocol_law_congr hnP prim prim' prepN prepN' hU hP hU' hP' hcol g hg
  refine ⟨fun j => nrun_isUnitary prim' hprim' _ (trialN_valid prepN' hv' j), ?_, fun j hj => ?_,
    ?_, ?_, ?_, ?_⟩
  · have e : (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations g),
        ‖ODEHeraldedSuccess.successProjector goodN (nrun prim' (trialN prepN' j) sN)‖ ^ 2) =
        ∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations g),
          ‖ODEHeraldedSuccess.successProjector goodN (nrun prim (trialN prepN j) sN)‖ ^ 2 :=
      Finset.sum_congr rfl (fun j _ => by rw [ht j])
    rw [e]
    exact h.mean_success
  · rw [← ht j] at hj ⊢
    exact h.trial_direction j hj
  · rw [← hm]
    exact h.success_lower
  · rw [← hm]
    exact h.success_two_thirds
  · rw [← hc]
    exact h.output_density
  · rw [← hc]
    exact h.conditional_error

end

end SparseHamiltonian.SourceAccuracyODE

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateODE (AW)
open scoped InnerProduct

variable {a m r K k l f : ℕ} {S Zs Z : Type*} {nP bT bP A : ℕ}
variable {Y J Y' J' : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z]
  [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

/-- **The heralded-output guarantee depends only on the column of the actual preparation**: for two
native preparations, unitary and preserving the clean reflection wire, with the same action on the
seed, the native protocol of one has `HeraldedOutput` against a target exactly when that of the
other has. -/
theorem heraldedOutput_of_column
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
      Fintype.card S ≤ nP + 1)
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (prim' : J' → Reg Y' ℂ →L[ℂ] Reg Y' ℂ)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (prepN' : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y' J'))
    (hU : IsUnitary (nrun prim prepN)) (hP : Pres2 (ZeroOn reflWire) (nrun prim prepN))
    (hU' : IsUnitary (nrun prim' prepN')) (hP' : Pres2 (ZeroOn reflWire) (nrun prim' prepN'))
    (hcol : nrun prim prepN sN = nrun prim' prepN' sN) (g : ℝ) (hg : 1 ≤ g) (target : Reg S ℂ)
    (ε : ℝ) :
    HeraldedOutput (nprotocol prepN g hg) prim target ε ↔
      HeraldedOutput (nprotocol prepN' g hg) prim' target ε := by
  obtain ⟨hm, hc⟩ := nprotocol_law_congr hnP prim prim' prepN prepN' hU hP hU' hP' hcol g hg
  unfold HeraldedOutput
  rw [hm, hc]

end

end ManuscriptConformance
