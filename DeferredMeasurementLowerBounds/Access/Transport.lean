import DeferredMeasurementLowerBounds.Deferral.Theorem
import SparseHamiltonian.EncodedLabeledProgram
import ODELowerBoundExtensions.Release.Model

set_option autoImplicit false

/-!
# Compiling the deferred program into an access model

A lower bound is stated for programs over a fixed access model (an oracle family `O'` on a
workspace `K'`). The deferred program of a measured algorithm is a program over the selection
family on `Joint (DRec M) K`. Given an isometric encoding `Enc : Joint (DRec M) K → K'` and, for
every label `c` of the selection family, a program `circuits c` over `O'` that acts on the
encoded subspace as `c` (`(circuits c).eval x ∘ Enc = Enc ∘ selFamily c x`), the package's
encoded compiler `EncodedLabeledProgram.compile` gives one program over `O'`
(`compiledProgram`); its fixed unitaries are the subspace lifts of the deferred unitaries.

As an adaptive protocol with seed `Enc (deferredSeed M φ)` and output isometry
`Enc ∘ deferredOutput M` (`compiledTree`), it has the success mass of the measured algorithm and
the conditional output `|a⟩⟨a| / ‖a‖²` of the decoded vector `a = amplitude counted M x φ`
(`successMass_compiledTree`, `conditionalDensity_compiledTree`), and its weighted cost is at most
`k` times the worst-case number of counted calls of the measured algorithm when each counted
pattern compiles to weight at most `k` and each other pattern to weight zero
(`worstCost_compiledTree_mul`; `k = 1` is `worstCost_compiledTree`).
-/

namespace DeferredMeasurementLowerBounds.Access

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open SparseLinearSystems.Protocol
open DeferredMeasurementLowerBounds.Model DeferredMeasurementLowerBounds.Deferral
open scoped InnerProduct

variable {K E X L K' L' : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
  {O : L → X → K →L[ℂ] K} {O' : L' → X → K' →L[ℂ] K'}
  (counted : L → Prop) [DecidablePred counted]

/-- **The compiled deferred program** over the access model `O'`. -/
def compiledProgram (M : Measured O E) (Enc : Joint (DRec M) K →L[ℂ] K')
    (hEnc : Enc† ∘L Enc = 1)
    (circuits : SelLabel counted (DRec M) → MultiOracleCircuit.Program O') :
    MultiOracleCircuit.Program O' :=
  EncodedLabeledProgram.compile Enc hEnc circuits (deferredProgram counted M)

/-- The compiled program as one fresh trial. -/
def compiledTrial (M : Measured O E) (φ : K) (hφ : ‖φ‖ = 1) (Enc : Joint (DRec M) K →L[ℂ] K')
    (hEnc : Enc† ∘L Enc = 1)
    (circuits : SelLabel counted (DRec M) → MultiOracleCircuit.Program O') :
    ODERepeatProtocol.TrialFamily O' (Joint (DOut M) E) where
  choices := 1
  choices_pos := one_pos
  circuit _ := compiledProgram counted M Enc hEnc circuits
  seed := Enc (deferredSeed M φ)
  seed_unit := by
    rw [(Enc.norm_map_iff_adjoint_comp_self.mpr hEnc) (deferredSeed M φ), norm_deferredSeed M hφ]
  output := Enc ∘L deferredOutput M
  output_isometry := by
    have h1 : (1 : Joint (DRec M) K →L[ℂ] Joint (DRec M) K) ∘L deferredOutput M =
        deferredOutput M := ContinuousLinearMap.id_comp _
    rw [adjoint_comp, comp_assoc, ← comp_assoc (Enc†) Enc (deferredOutput M), hEnc, h1,
      deferredOutput_isometry]

/-- **The compiled deferred program as an adaptive protocol** over the access model `O'`. -/
def compiledTree (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (M : Measured O E) (φ : K) (hφ : ‖φ‖ = 1) (Enc : Joint (DRec M) K →L[ℂ] K')
    (hEnc : Enc† ∘L Enc = 1)
    (circuits : SelLabel counted (DRec M) → MultiOracleCircuit.Program O') :
    Tree O' F (Joint (DOut M) E) :=
  .final (.freshTrial (compiledTrial counted M φ hφ Enc hEnc circuits) .abort)

variable {counted} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The decoded final vector of the compiled program is that of the deferred program. -/
theorem amplitude_compiled (hO : ∀ l x, IsUnitary (O l x)) (hO' : ∀ l x, IsUnitary (O' l x))
    (M : Measured O E) (φ : K) (Enc : Joint (DRec M) K →L[ℂ] K') (hEnc : Enc† ∘L Enc = 1)
    (circuits : SelLabel counted (DRec M) → MultiOracleCircuit.Program O')
    (hcirc : ∀ c x, (circuits c).eval x ∘L Enc = Enc ∘L selFamily O counted (DRec M) c x)
    (x : X) :
    ((Enc ∘L deferredOutput M)†) ((compiledProgram counted M Enc hEnc circuits).eval x
      (Enc (deferredSeed M φ))) = amplitude counted M x φ := by
  have h := congrArg (fun T => T (deferredSeed M φ))
    (EncodedLabeledProgram.compile_eval Enc hEnc circuits hO'
      (fun c y => selFamily_unitary hO counted (DRec M) c y) hcirc (deferredProgram counted M) x)
  simp only [comp_apply] at h
  rw [compiledProgram, h, adjoint_comp, comp_apply, ← comp_apply (Enc†) Enc, hEnc]
  rfl

/-- The single trial of the compiled protocol decodes to the decoded final vector. -/
theorem amplitude_compiledTrial (hO : ∀ l x, IsUnitary (O l x))
    (hO' : ∀ l x, IsUnitary (O' l x)) (M : Measured O E) {φ : K} (hφ : ‖φ‖ = 1)
    (Enc : Joint (DRec M) K →L[ℂ] K') (hEnc : Enc† ∘L Enc = 1)
    (circuits : SelLabel counted (DRec M) → MultiOracleCircuit.Program O')
    (hcirc : ∀ c x, (circuits c).eval x ∘L Enc = Enc ∘L selFamily O counted (DRec M) c x)
    (x : X) (j : Fin 1) :
    (compiledTrial counted M φ hφ Enc hEnc circuits).amplitude x j = amplitude counted M x φ :=
  amplitude_compiled hO hO' M φ Enc hEnc circuits hcirc x

/-- The single trial of the compiled protocol succeeds with the probability of the measured
algorithm. -/
theorem meanSuccess_compiledTrial (hO : ∀ l x, IsUnitary (O l x))
    (hO' : ∀ l x, IsUnitary (O' l x)) (M : Measured O E) {φ : K} (hφ : ‖φ‖ = 1)
    (Enc : Joint (DRec M) K →L[ℂ] K') (hEnc : Enc† ∘L Enc = 1)
    (circuits : SelLabel counted (DRec M) → MultiOracleCircuit.Program O')
    (hcirc : ∀ c x, (circuits c).eval x ∘L Enc = Enc ∘L selFamily O counted (DRec M) c x)
    (x : X) :
    (compiledTrial counted M φ hφ Enc hEnc circuits).meanSuccess x = M.successMass x φ := by
  change (∑ j : Fin 1,
    ‖(compiledTrial counted M φ hφ Enc hEnc circuits).amplitude x j‖ ^ 2) / ((1 : ℕ) : ℝ) = _
  simp only [amplitude_compiledTrial hO hO' M hφ Enc hEnc circuits hcirc, Finset.univ_unique,
    Finset.sum_singleton, Nat.cast_one, div_one]
  exact norm_sq_amplitude M x φ

/-- The compiled protocol heralds success with the probability of the measured algorithm. -/
theorem successMass_compiledTree (hO : ∀ l x, IsUnitary (O l x))
    (hO' : ∀ l x, IsUnitary (O' l x)) (M : Measured O E) {φ : K} (hφ : ‖φ‖ = 1)
    (Enc : Joint (DRec M) K →L[ℂ] K') (hEnc : Enc† ∘L Enc = 1)
    (circuits : SelLabel counted (DRec M) → MultiOracleCircuit.Program O')
    (hcirc : ∀ c x, (circuits c).eval x ∘L Enc = Enc ∘L selFamily O counted (DRec M) c x)
    (x : X) :
    (compiledTree counted F M φ hφ Enc hEnc circuits).successMass x = M.successMass x φ := by
  simp only [compiledTree, Tree.successMass, Tree.expect,
    ODERepeatProtocol.Protocol.freshTrial_successMass_eq,
    meanSuccess_compiledTrial hO hO' M hφ Enc hEnc circuits hcirc]
  simp [ODERepeatProtocol.Protocol.successMass, ODERepeatProtocol.Protocol.failureMass]

/-- The heralded output of the compiled protocol is the pure state of the decoded vector. -/
theorem successDensity_compiledTree [FiniteDimensional ℂ E] (hO : ∀ l x, IsUnitary (O l x))
    (hO' : ∀ l x, IsUnitary (O' l x)) (M : Measured O E) {φ : K} (hφ : ‖φ‖ = 1)
    (Enc : Joint (DRec M) K →L[ℂ] K') (hEnc : Enc† ∘L Enc = 1)
    (circuits : SelLabel counted (DRec M) → MultiOracleCircuit.Program O')
    (hcirc : ∀ c x, (circuits c).eval x ∘L Enc = Enc ∘L selFamily O counted (DRec M) c x)
    (x : X) :
    (compiledTree counted F M φ hφ Enc hEnc circuits).successDensity x =
      ODEMixedOutput.pureOperator (amplitude counted M x φ) := by
  simp only [compiledTree, Tree.successDensity, Tree.expect,
    ODERepeatProtocol.Protocol.successDensity, smul_zero, add_zero,
    ODERepeatProtocol.TrialFamily.oneTrialDensity_eq_kraus]
  change ((1 : ℕ) : ℂ)⁻¹ • ∑ j : Fin 1, ODEMixedOutput.pureOperator
    ((compiledTrial counted M φ hφ Enc hEnc circuits).amplitude x j) = _
  simp only [amplitude_compiledTrial hO hO' M hφ Enc hEnc circuits hcirc, Finset.univ_unique,
    Finset.sum_singleton, Nat.cast_one, inv_one, one_smul]

/-- The conditional output of the compiled protocol. -/
theorem conditionalDensity_compiledTree [FiniteDimensional ℂ E]
    (hO : ∀ l x, IsUnitary (O l x)) (hO' : ∀ l x, IsUnitary (O' l x)) (M : Measured O E)
    {φ : K} (hφ : ‖φ‖ = 1) (Enc : Joint (DRec M) K →L[ℂ] K') (hEnc : Enc† ∘L Enc = 1)
    (circuits : SelLabel counted (DRec M) → MultiOracleCircuit.Program O')
    (hcirc : ∀ c x, (circuits c).eval x ∘L Enc = Enc ∘L selFamily O counted (DRec M) c x)
    (x : X) :
    (compiledTree counted F M φ hφ Enc hEnc circuits).conditionalDensity x =
      ((M.successMass x φ)⁻¹ : ℂ) • ODEMixedOutput.pureOperator (amplitude counted M x φ) := by
  rw [Tree.conditionalDensity, successMass_compiledTree hO hO' M hφ Enc hEnc circuits hcirc x,
    successDensity_compiledTree hO hO' M hφ Enc hEnc circuits hcirc x]

/-- **The compiled protocol makes at most `k` times the worst-case number of counted calls**,
when every counted pattern compiles to weight at most `k` and every other pattern to weight
zero. -/
theorem worstCost_compiledTree_mul (M : Measured O E) {φ : K} (hφ : ‖φ‖ = 1)
    (Enc : Joint (DRec M) K →L[ℂ] K') (hEnc : Enc† ∘L Enc = 1)
    (circuits : SelLabel counted (DRec M) → MultiOracleCircuit.Program O') (w' : L' → ℕ)
    (k : ℕ) (hw : ∀ c, (circuits c).cost w' ≤ k * selWeight c) :
    (compiledTree counted F M φ hφ Enc hEnc circuits).worstCost w' ≤
      k * M.worstCost (countWeight counted) := by
  simp only [compiledTree, Tree.worstCost, ODERepeatProtocol.Protocol.worstCost,
    ODERepeatProtocol.TrialFamily.maxCost, add_zero]
  refine Finset.sup_le fun _ _ => ?_
  change (compiledProgram counted M Enc hEnc circuits).cost w' ≤ _
  rw [compiledProgram, EncodedLabeledProgram.compile_cost]
  calc (deferredProgram counted M).cost (fun c => (circuits c).cost w')
      ≤ (deferredProgram counted M).cost (fun c => k * selWeight c) :=
        MultiOracleCircuit.Program.cost_mono _ hw
    _ = k * (deferredProgram counted M).cost selWeight :=
        ODELowerBoundExtensions.Release.program_cost_mul _ _ _
    _ ≤ k * M.worstCost (countWeight counted) := Nat.mul_le_mul_left _ (cost_deferredProgram M)

/-- **The compiled protocol makes at most the worst-case number of counted calls**, when every
counted pattern compiles to weight at most one and every other pattern to weight zero. -/
theorem worstCost_compiledTree (M : Measured O E) {φ : K} (hφ : ‖φ‖ = 1)
    (Enc : Joint (DRec M) K →L[ℂ] K') (hEnc : Enc† ∘L Enc = 1)
    (circuits : SelLabel counted (DRec M) → MultiOracleCircuit.Program O') (w' : L' → ℕ)
    (hw : ∀ c, (circuits c).cost w' ≤ selWeight c) :
    (compiledTree counted F M φ hφ Enc hEnc circuits).worstCost w' ≤
      M.worstCost (countWeight counted) := by
  have h := worstCost_compiledTree_mul (F := F) M hφ Enc hEnc circuits w' 1
    (fun c => (one_mul (selWeight c)).symm ▸ hw c)
  rwa [one_mul] at h

end

end DeferredMeasurementLowerBounds.Access
