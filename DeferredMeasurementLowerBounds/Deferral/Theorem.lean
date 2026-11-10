import DeferredMeasurementLowerBounds.Deferral.Output
import SparseLinearSystems.Protocol.Tree

set_option autoImplicit false

/-!
# The deferral theorem

Manuscript: the proofs of Lemmas `hsl:lem:precision` and `qlsl:lem:xor`. Every measured algorithm
`M` (mid-run and multi-outcome measurements, classical control, randomness, resets of
finite-dimensional registers, any workspace) over a unitary oracle family `O` is simulated by **one
unitary oracle program** over the selection family (`deferredProgram`), on the workspace with
`M.depth` record registers of width `M.width`, run on a unit seed (`deferredSeed`) and read through
one output isometry (`deferredOutput`):

* the decoded final vector `amplitude` (indexed by the output records) has the success mass of
  `M` as squared norm (`norm_sq_amplitude`), and its record-wise projectors sum to the heralded
  output of `M` (`sum_pure_amplitude`): discarding the records gives exactly the output of `M`;
* the program makes at most the worst-case number of counted calls of `M` over all transcripts
  (`cost_deferredProgram`), with any choice of the counted labels, and it makes no oracle call
  outside the selection family: the aligned calls of all branches form one record-selected call
  `Σ_r |r⟩⟨r| ⊗ O(π r)`, itself a record-controlled call. Its cost in a given access model is
  stated per model in `Access`: one native call for admissible native labels, one controlled
  call for the phase oracle and for the sampled-time value call, and for general single-label
  controlled access one or two controlled calls per counted label used in the slot.

`deferral` packages these facts; it applies to every program-level lower bound whose access
class contains the selection family and whose accuracy is a property of the output with the
records discarded. `deferredTree` is the same program as an adaptive protocol of the package
(one fresh trial, `SparseLinearSystems.Protocol.Tree.final`).
-/

namespace DeferredMeasurementLowerBounds.Deferral

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open SparseLinearSystems.Protocol
open DeferredMeasurementLowerBounds.Model
open scoped InnerProduct

variable {K E F X L : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {O : L → X → K →L[ℂ] K}

/-- The record values of the deferral of `M`. -/
abbrev DRec (M : Measured O E) : Type := Rec M.width M.depth

/-- The output records of the deferral of `M`. -/
abbrev DOut (M : Measured O E) : Type := OutRec M.width M M.depth

variable (counted : L → Prop) [DecidablePred counted]

/-- **The deferred program** of a measured algorithm. -/
def deferredProgram (M : Measured O E) :
    MultiOracleCircuit.Program (selFamily O counted (DRec M)) :=
  (defer O counted M.width M M.depth).prog

/-- The seed of the deferred program: the initial vector on the fresh record. -/
def deferredSeed (M : Measured O E) (φ : K) : Joint (DRec M) K :=
  freshInj M.width M.depth φ

/-- The output isometry of the deferred program. -/
def deferredOutput (M : Measured O E) : Joint (DOut M) E →L[ℂ] Joint (DRec M) K :=
  deferOutput M.width M M.depth

/-- The decoded final vector of the deferred program. -/
def amplitude (M : Measured O E) (x : X) (φ : K) : Joint (DOut M) E :=
  ((deferredOutput M)†) ((deferredProgram counted M).eval x (deferredSeed M φ))

variable {counted}

/-- A unit initial vector gives a unit seed. -/
theorem norm_deferredSeed (M : Measured O E) {φ : K} (hφ : ‖φ‖ = 1) :
    ‖deferredSeed M φ‖ = 1 := by
  rw [deferredSeed, ((freshInj (K := K) M.width M.depth).norm_map_iff_adjoint_comp_self.mpr
    (freshInj_isometry M.width M.depth)) φ, hφ]

/-- The deferred output is an isometry. -/
theorem deferredOutput_isometry (M : Measured O E) :
    (deferredOutput M)† ∘L deferredOutput M = 1 :=
  deferOutput_isometry _ _ _

/-- The deferred program of unitary labels is unitary. -/
theorem deferredProgram_unitary (hO : ∀ l x, IsUnitary (O l x)) (M : Measured O E) (x : X) :
    IsUnitary ((deferredProgram counted M).eval x) :=
  (deferredProgram counted M).eval_unitary (fun c y => selFamily_unitary hO counted (DRec M) c y) x

/-- **Padding to the worst case**: the deferred program makes at most the worst-case number of
counted calls of the measured algorithm. -/
theorem cost_deferredProgram (M : Measured O E) :
    (deferredProgram counted M).cost selWeight ≤ M.worstCost (countWeight counted) :=
  cost_defer _ _ _

/-- **The deferred output is the output of the measured algorithm** with the records
discarded. -/
theorem sum_pure_amplitude (M : Measured O E) (x : X) (φ : K) :
    ∑ r, ODEMixedOutput.pureOperator (amplitude counted M x φ r) = M.successDensity x φ := by
  rw [amplitude, deferredProgram, deferredSeed, deferredOutput,
    eval_defer M.width M M.depth le_rfl le_rfl x φ]
  exact sum_pure_deferOutput M.width M M.depth le_rfl le_rfl x φ

/-- **The deferred program heralds success with the probability of the measured algorithm.** -/
theorem norm_sq_amplitude (M : Measured O E) (x : X) (φ : K) :
    ‖amplitude counted M x φ‖ ^ 2 = M.successMass x φ := by
  rw [amplitude, deferredProgram, deferredSeed, deferredOutput,
    eval_defer M.width M M.depth le_rfl le_rfl x φ]
  exact norm_sq_deferOutput M.width M M.depth le_rfl le_rfl x φ

/-- **Deferred measurement** (proofs of Lemmas `hsl:lem:precision` and `qlsl:lem:xor`:
purification, deferred measurement and padding to the worst-case query count). Every measured
algorithm over a unitary family is simulated by one unitary program over the selection family on
a unit seed with one isometric output, with the same success mass and, records discarded, the
same heralded output, and with at most the worst-case number of counted calls of the measured
algorithm. -/
theorem deferral (hO : ∀ l x, IsUnitary (O l x)) (M : Measured O E) {φ : K} (hφ : ‖φ‖ = 1) :
    ∃ (R J : Type) (_ : Fintype R) (_ : Fintype J)
      (p : MultiOracleCircuit.Program (selFamily O counted R)) (seed : Joint R K)
      (out : Joint J E →L[ℂ] Joint R K),
      ‖seed‖ = 1 ∧ out† ∘L out = 1 ∧ (∀ x, IsUnitary (p.eval x)) ∧
      p.cost selWeight ≤ M.worstCost (countWeight counted) ∧
      ∀ x, ∑ j, ODEMixedOutput.pureOperator (((out†) (p.eval x seed)) j) = M.successDensity x φ ∧
        ‖(out†) (p.eval x seed)‖ ^ 2 = M.successMass x φ :=
  ⟨DRec M, DOut M, inferInstance, inferInstance, deferredProgram counted M, deferredSeed M φ,
    deferredOutput M, norm_deferredSeed M hφ, deferredOutput_isometry M,
    deferredProgram_unitary hO M, cost_deferredProgram M,
    fun x => ⟨sum_pure_amplitude M x φ, norm_sq_amplitude M x φ⟩⟩

/-! ### The deferred program as an adaptive protocol -/

variable (counted)

/-- The deferred program as one fresh trial. -/
def deferredTrial (M : Measured O E) (φ : K) (hφ : ‖φ‖ = 1) :
    ODERepeatProtocol.TrialFamily (selFamily O counted (DRec M)) (Joint (DOut M) E) where
  choices := 1
  choices_pos := one_pos
  circuit _ := deferredProgram counted M
  seed := deferredSeed M φ
  seed_unit := norm_deferredSeed M hφ
  output := deferredOutput M
  output_isometry := deferredOutput_isometry M

/-- **The deferred program as an adaptive protocol**: one fresh trial, then stop. -/
def deferredTree (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (M : Measured O E) (φ : K) (hφ : ‖φ‖ = 1) :
    Tree (selFamily O counted (DRec M)) F (Joint (DOut M) E) :=
  .final (.freshTrial (deferredTrial counted M φ hφ) .abort)

variable {counted}

/-- The single trial of the deferred protocol decodes to the decoded final vector. -/
theorem amplitude_deferredTrial (M : Measured O E) {φ : K} (hφ : ‖φ‖ = 1) (x : X)
    (j : Fin 1) :
    (deferredTrial counted M φ hφ).amplitude x j = amplitude counted M x φ :=
  rfl

/-- The single trial of the deferred protocol succeeds with the probability of the measured
algorithm. -/
theorem meanSuccess_deferredTrial (M : Measured O E) {φ : K} (hφ : ‖φ‖ = 1) (x : X) :
    (deferredTrial counted M φ hφ).meanSuccess x = M.successMass x φ := by
  change (∑ j : Fin 1, ‖(deferredTrial counted M φ hφ).amplitude x j‖ ^ 2) / ((1 : ℕ) : ℝ) = _
  simp only [amplitude_deferredTrial, Finset.univ_unique, Finset.sum_singleton, Nat.cast_one,
    div_one]
  exact norm_sq_amplitude M x φ

/-- The deferred protocol heralds success with the probability of the measured algorithm. -/
theorem successMass_deferredTree (M : Measured O E) {φ : K} (hφ : ‖φ‖ = 1) (x : X) :
    (deferredTree counted F M φ hφ).successMass x = M.successMass x φ := by
  simp only [deferredTree, Tree.successMass, Tree.expect,
    ODERepeatProtocol.Protocol.freshTrial_successMass_eq, meanSuccess_deferredTrial]
  simp [ODERepeatProtocol.Protocol.successMass, ODERepeatProtocol.Protocol.failureMass]

/-- The heralded output of the deferred protocol is the pure state of the decoded vector. -/
theorem successDensity_deferredTree [FiniteDimensional ℂ E] (M : Measured O E) {φ : K}
    (hφ : ‖φ‖ = 1) (x : X) :
    (deferredTree counted F M φ hφ).successDensity x =
      ODEMixedOutput.pureOperator (amplitude counted M x φ) := by
  simp only [deferredTree, Tree.successDensity, Tree.expect,
    ODERepeatProtocol.Protocol.successDensity, smul_zero, add_zero,
    ODERepeatProtocol.TrialFamily.oneTrialDensity_eq_kraus]
  change ((1 : ℕ) : ℂ)⁻¹ • ∑ j : Fin 1, ODEMixedOutput.pureOperator
    ((deferredTrial counted M φ hφ).amplitude x j) = _
  simp only [amplitude_deferredTrial, Finset.univ_unique, Finset.sum_singleton, Nat.cast_one,
    inv_one, one_smul]

/-- The conditional output of the deferred protocol. -/
theorem conditionalDensity_deferredTree [FiniteDimensional ℂ E] (M : Measured O E) {φ : K}
    (hφ : ‖φ‖ = 1) (x : X) :
    (deferredTree counted F M φ hφ).conditionalDensity x =
      ((M.successMass x φ)⁻¹ : ℂ) • ODEMixedOutput.pureOperator (amplitude counted M x φ) := by
  rw [Tree.conditionalDensity, successMass_deferredTree M hφ x, successDensity_deferredTree M hφ x]

/-- The deferred protocol makes at most the worst-case number of counted calls. -/
theorem worstCost_deferredTree (M : Measured O E) {φ : K} (hφ : ‖φ‖ = 1) :
    (deferredTree counted F M φ hφ).worstCost selWeight ≤ M.worstCost (countWeight counted) := by
  simp only [deferredTree, Tree.worstCost, ODERepeatProtocol.Protocol.worstCost,
    ODERepeatProtocol.TrialFamily.maxCost, add_zero]
  exact Finset.sup_le fun _ _ => cost_deferredProgram M

end

end DeferredMeasurementLowerBounds.Deferral
