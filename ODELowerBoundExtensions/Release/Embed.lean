import ODELowerBoundExtensions.Release.Model
import AdaptiveHamiltonianLowerBound.Theorem

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Every released solver is a one-attempt retry solver

Manuscript lines 3675-3678 (the output model of Theorem `odel:thm:combined`). A solver of
`SparseLowerBounds.ODE.Solver` (one program, a seed of norm at most one, an isometric readout
onto system ⊗ garbage, a herald projection) is the retry protocol with **one attempt and one
circuit label** (`toRetryProt`, the release's `repeatTrials t 1 = freshTrial t abort`), with the
same counts:

* the trial output space is the herald's range `heraldSpace A = (ker herald)ᗮ` (a
  finite-dimensional subspace of the workspace), with output isometry its inclusion
  `Submodule.subtypeL`; the release's herald
  `output ∘ output†` is then the solver's herald projection, so success and conditional output
  are unchanged and the release `TrialFamily` is used as it is (no readout generalisation);
* the trial seed is the normalised seed `normSeed A` (`TrialFamily` asks for a unit seed);
  success probability and heralded accuracy are homogeneous of degree two in the seed, so
  normalising a nonzero seed of norm at most one keeps both (`toRetry_success`,
  `toRetry_accurate`); on a nonempty input set the seed is nonzero (`seed_ne_zero`);
* the readout is `A.out ∘ subtypeL` (`toRetryReadout`), and the conditional density read through
  it reproduces `Readout.HeraldedAccurate` divided by the success probability.

Consequences: `retryForces_forces` (`RetryForces` implies the released `Family.Forces`) and
`retryWitnesses_witnesses` (`RetryWitnesses` implies `Family.Witnesses`), with no hypothesis on the
input set (on an empty input set the aborting protocol is a retry solver of cost `0`, so
`RetryForces` already gives `b ≤ 0`). Hence each disjunct of `Release.combined_retry` implies the
corresponding disjunct of `SparseLowerBounds.ODE.combined`: the released theorem is the one-trial
special case.
-/

namespace ODELowerBoundExtensions.Release

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open scoped InnerProduct InnerProductSpace

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {K s : ℕ}
  {F : Family X N Z K s} {ι : Type} [Fintype ι] {G : Type} [NormedAddCommGroup G]
  [InnerProductSpace ℂ G] [CompleteSpace G] {ε : ℝ}

/-- The success subspace of a solver: the orthogonal complement of the kernel of its herald
projection, that is, the herald's range (written as an orthogonal complement so that it carries
the inner-product module structure of the workspace). -/
abbrev heraldSpace (A : Solver ι F G ε) : Submodule ℂ (Workspace ι N Z K) :=
  (LinearMap.ker A.herald.toLinearMap)ᗮ

/-- The herald's range is complete (finite-dimensional). -/
instance heraldSpace_completeSpace (A : Solver ι F G ε) : CompleteSpace (heraldSpace A) :=
  FiniteDimensional.complete ℂ _

/-- The normalised seed `seed/‖seed‖`. -/
def normSeed (A : Solver ι F G ε) : Workspace ι N Z K := ((‖A.seed‖ : ℂ)⁻¹) • A.seed

/-- A nonzero seed normalises to a unit vector. -/
theorem norm_normSeed (A : Solver ι F G ε) (h : A.seed ≠ 0) : ‖normSeed A‖ = 1 := by
  have hpos : 0 < ‖A.seed‖ := norm_pos_iff.mpr h
  rw [normSeed, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
    inv_mul_cancel₀ hpos.ne']

/-- The inclusion of the herald's range is an isometry. -/
theorem heraldSpace_subtypeL_isometry (A : Solver ι F G ε) :
    ((heraldSpace A).subtypeL)† ∘L (heraldSpace A).subtypeL = 1 := by
  rw [Submodule.adjoint_subtypeL]
  ext1 v
  simp

/-- The herald's range is the solver's success subspace: the inclusion of the projection of
`v` onto `heraldSpace A` is `herald v` (the orthogonal projection onto `(ker P)ᗮ` of a star
projection `P` is `P`). -/
theorem subtypeL_adjoint_apply (A : Solver ι F G ε) (v : Workspace ι N Z K) :
    (((((heraldSpace A).subtypeL)†) v : heraldSpace A) : Workspace ι N Z K) = A.herald v := by
  have hP := A.herald_proj
  have hsym := hP.isSelfAdjoint.isSymmetric
  rw [Submodule.adjoint_subtypeL, Submodule.coe_orthogonalProjectionOnto_apply]
  refine Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
  · rw [Submodule.mem_orthogonal]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    have hu' : A.herald u = 0 := hu
    have := hsym u v
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [← this, hu', inner_zero_left]
  · apply Submodule.le_orthogonal_orthogonal
    rw [LinearMap.mem_ker]
    show A.herald (v - A.herald v) = 0
    rw [map_sub, sub_eq_zero]
    exact (congrArg (fun T => T v) hP.isIdempotentElem.eq).symm

/-- **The one-choice trial** of a solver: its program, the normalised seed and the inclusion
of the herald's range as clean output. -/
def toTrial (A : Solver ι F G ε) (h : A.seed ≠ 0) :
    ODERepeatProtocol.TrialFamily (F.access ι) (heraldSpace A) where
  choices := 1
  choices_pos := one_pos
  circuit _ := A.prog
  seed := normSeed A
  seed_unit := norm_normSeed A h
  output := (heraldSpace A).subtypeL
  output_isometry := heraldSpace_subtypeL_isometry A

/-- **The one-attempt protocol** of a solver: the release's `repeatTrials` with one attempt (one
fresh trial, then abort). -/
def toRetryProt (A : Solver ι F G ε) (h : A.seed ≠ 0) :
    ODERepeatProtocol.Protocol (F.access ι) (heraldSpace A) :=
  ODERepeatProtocol.Protocol.repeatTrials (toTrial A h) 1

/-- The readout of the decoded output: the solver's readout on the herald's range. -/
def toRetryReadout (A : Solver ι F G ε) : heraldSpace A →L[ℂ] SysGarb N G :=
  A.out ∘L (heraldSpace A).subtypeL

/-- The readout of the herald's range is an isometry. -/
theorem toRetryReadout_isometry (A : Solver ι F G ε) :
    (toRetryReadout A)† ∘L toRetryReadout A = 1 := by
  rw [toRetryReadout, ContinuousLinearMap.adjoint_comp]
  ext1 v
  have h1 := congrArg (fun T => T ((heraldSpace A).subtypeL v)) A.out_isometry
  have h2 := congrArg (fun T => T v) (heraldSpace_subtypeL_isometry A)
  simp only [ContinuousLinearMap.comp_apply] at h1 h2 ⊢
  rw [h1]
  exact h2

/-- The decoded amplitude of the one-choice trial is the normalised seed's heralded output:
`amplitude = ‖seed‖⁻¹ • S† (prog.eval x seed)`, with `S` the inclusion of the herald's range. -/
theorem toTrial_amplitude (A : Solver ι F G ε) (h : A.seed ≠ 0) (x : X)
    (j : Fin (toTrial A h).choices) :
    (toTrial A h).amplitude x j =
      ((‖A.seed‖ : ℂ)⁻¹) • (((heraldSpace A).subtypeL)†) (A.prog.eval x A.seed) := by
  change (((heraldSpace A).subtypeL)†) (A.prog.eval x (normSeed A)) = _
  rw [normSeed, map_smul, map_smul]

/-- The success probability of the one-choice trial is the solver's, divided by `‖seed‖²`. -/
theorem toTrial_meanSuccess (A : Solver ι F G ε) (h : A.seed ≠ 0) (x : X) :
    (toTrial A h).meanSuccess x =
      ‖A.herald (A.prog.eval x A.seed)‖ ^ 2 / ‖A.seed‖ ^ 2 := by
  have hpos : 0 < ‖A.seed‖ := norm_pos_iff.mpr h
  have hn : ‖(((heraldSpace A).subtypeL)†) (A.prog.eval x A.seed)‖ =
      ‖A.herald (A.prog.eval x A.seed)‖ := by
    rw [← subtypeL_adjoint_apply]; rfl
  change (∑ j : Fin 1, ‖(toTrial A h).amplitude x j‖ ^ 2) / ((1 : ℕ) : ℝ) = _
  rw [Fin.sum_univ_one, toTrial_amplitude, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hpos, hn, Nat.cast_one, div_one, mul_pow, inv_pow,
    inv_mul_eq_div]

/-- The success mass of the one-attempt protocol is the success probability of its trial. -/
theorem toRetryProt_successMass (A : Solver ι F G ε) (h : A.seed ≠ 0) (x : X) :
    (toRetryProt A h).successMass x = (toTrial A h).meanSuccess x := by
  rw [toRetryProt, ODERepeatProtocol.Protocol.repeat_successMass, pow_one, sub_sub_cancel]

/-- The one-attempt protocol succeeds with the solver's success probability, divided by
`‖seed‖² ≤ 1`, hence with probability at least `2/3`. -/
theorem toRetry_success (A : Solver ι F G ε) (h : A.seed ≠ 0) (x : X) :
    2 / 3 ≤ (toRetryProt A h).successMass x := by
  have hpos : 0 < ‖A.seed‖ := norm_pos_iff.mpr h
  have hle : ‖A.seed‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) A.seed_norm_le
  rw [toRetryProt_successMass, toTrial_meanSuccess, le_div_iff₀ (by positivity)]
  have := A.success x
  nlinarith [sq_nonneg ‖A.seed‖]

set_option maxHeartbeats 400000 in
/-- The conditional output of the one-attempt protocol is the pure state of the heralded
output `S† Φ` of the solver (unnormalised seed), divided by its success probability `‖P Φ‖²`. -/
theorem toRetry_conditionalDensity (A : Solver ι F G ε) (h : A.seed ≠ 0) (x : X) :
    (toRetryProt A h).conditionalDensity x =
      (((‖A.herald (A.prog.eval x A.seed)‖ ^ 2)⁻¹ : ℝ) : ℂ) •
        ODEMixedOutput.pureOperator ((((heraldSpace A).subtypeL)†) (A.prog.eval x A.seed)) := by
  have hpos : 0 < ‖A.seed‖ := norm_pos_iff.mpr h
  letI : Unique (Fin (toTrial A h).choices) := Fin.instUnique
  have hcC : ((toTrial A h).choices : ℂ) = 1 := Nat.cast_one
  have hS : (toRetryProt A h).successDensity x =
      (toTrial A h).oneTrialDensity x + (((1 - (toTrial A h).meanSuccess x : ℝ)) : ℂ) • 0 :=
    rfl
  have h1 : (toRetryProt A h).successDensity x = (toTrial A h).oneTrialDensity x := by
    rw [hS, smul_zero, add_zero]
  have h2 : (toTrial A h).oneTrialDensity x =
      ODEMixedOutput.pureOperator ((toTrial A h).amplitude x default) := by
    rw [ODERepeatProtocol.TrialFamily.oneTrialDensity_eq_kraus, Fintype.sum_unique, hcC, inv_one,
      one_smul]
  have h3 : (toRetryProt A h).successMass x =
      ‖A.herald (A.prog.eval x A.seed)‖ ^ 2 / ‖A.seed‖ ^ 2 := by
    rw [toRetryProt_successMass, toTrial_meanSuccess]
  have h4 : (toRetryProt A h).conditionalDensity x =
      (((toRetryProt A h).successMass x : ℂ))⁻¹ • (toRetryProt A h).successDensity x := rfl
  rw [h4, h1, h2, h3, toTrial_amplitude, ODEMixedOutput.pureOperator_smul, smul_smul]
  congr 1
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  have hs2 : (‖A.seed‖ : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  push_cast
  field_simp

/-- The conditional output of the one-attempt protocol is `ε`-accurate: heralded accuracy
divided by the success probability. -/
theorem toRetry_accurate (A : Solver ι F G ε) (h : A.seed ≠ 0) (x : X)
    (sol : ℝ → EuclideanSpace ℂ N) (hs : F.Solves x sol) :
    DensityAccurate (toRetryReadout A) ((toRetryProt A h).conditionalDensity x)
      (ODEStateNormalization.unitDirection (sol F.T)) ε := by
  intro M hM hMn
  have hacc := A.accurate x sol hs M hM hMn
  rw [toRetry_conditionalDensity, LinearSystemLowerBound.corr_smul_real,
    LinearSystemLowerBound.corr_pure]
  have hu : (2 : ℝ) / 3 ≤ ‖A.herald (A.prog.eval x A.seed)‖ ^ 2 := A.success x
  generalize A.prog.eval x A.seed = Φ at hacc hu ⊢
  have hu0 : 0 < ‖A.herald Φ‖ ^ 2 := by linarith
  have hb : (((((heraldSpace A).subtypeL)†) Φ : heraldSpace A) : Workspace ι N Z K) =
      A.herald Φ :=
    subtypeL_adjoint_apply A Φ
  -- both expectations reduce to `⟪out (P Φ), (M ⊗ 1) out (P Φ)⟫`
  have hL : ⟪(((heraldSpace A).subtypeL)†) Φ,
      Readout.outObs (toRetryReadout A) M ((((heraldSpace A).subtypeL)†) Φ)⟫_ℂ =
      ⟪A.out (A.herald Φ), Readout.liftObs M (A.out (A.herald Φ))⟫_ℂ := by
    rw [Readout.outObs, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply]
    simp only [toRetryReadout, ContinuousLinearMap.comp_apply]
    rw [show (heraldSpace A).subtypeL ((((heraldSpace A).subtypeL)†) Φ) = A.herald Φ from hb]
  have hR : ⟪Φ, (A.herald ∘L Readout.outObs A.out M ∘L A.herald) Φ⟫_ℂ =
      ⟪A.out (A.herald Φ), Readout.liftObs M (A.out (A.herald Φ))⟫_ℂ := by
    have hsym := A.herald_proj.isSelfAdjoint.isSymmetric
    simp only [ContinuousLinearMap.comp_apply]
    have := hsym Φ (Readout.outObs A.out M (A.herald Φ))
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [← this, Readout.outObs, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply]
  rw [hL]
  rw [hR] at hacc
  generalize (⟪A.out (A.herald Φ), Readout.liftObs M (A.out (A.herald Φ))⟫_ℂ).re = q at hacc ⊢
  generalize (⟪ODEStateNormalization.unitDirection (sol F.T),
    M (ODEStateNormalization.unitDirection (sol F.T))⟫_ℂ).re = m at hacc ⊢
  generalize ‖A.herald Φ‖ ^ 2 = u at hacc hu0 ⊢
  have hrw : u⁻¹ * q - m = (q - u * m) / u := by
    field_simp
  rw [hrw, abs_div, abs_of_pos hu0, div_le_iff₀ hu0]
  exact hacc

/-- **A solver as a one-attempt, one-choice retry solver** (same program, same counts). -/
def solverToRetry (A : Solver ι F G ε) (h : A.seed ≠ 0) :
    RetrySolver F (F.access ι) (heraldSpace A) G ε where
  prot := toRetryProt A h
  readout := toRetryReadout A
  readout_isometry := toRetryReadout_isometry A
  success := toRetry_success A h
  accurate := toRetry_accurate A h

/-- **Same counts**: the worst-case weighted cost of the one-attempt protocol is the weighted
cost of the solver's program. -/
theorem toRetry_worstCost (A : Solver ι F G ε) (h : A.seed ≠ 0) (w : Query → ℕ) :
    (solverToRetry A h).prot.worstCost w = A.prog.cost w := by
  change (ODERepeatProtocol.Protocol.repeatTrials (toTrial A h) 1).worstCost w = _
  rw [ODERepeatProtocol.Protocol.repeat_worstCost, one_mul]
  change (Finset.univ : Finset (Fin 1)).sup (fun _ => A.prog.cost w) = _
  rw [Finset.univ_unique, Finset.sup_singleton]

/-- On a nonempty input set a solver's seed is nonzero (its success probability is positive). -/
theorem seed_ne_zero [Nonempty X] (A : Solver ι F G ε) : A.seed ≠ 0 := by
  intro h0
  have := A.success (Classical.arbitrary X)
  rw [h0, map_zero, map_zero, norm_zero] at this
  norm_num at this

/-- **Retry bounds are released bounds**: if `F` forces `b` on retry protocols, it forces `b`
on the solvers of `SparseLowerBounds.ODE.Solver` (value queries and all queries). No hypothesis on
the input set: on an empty one the aborting protocol is a retry solver of cost `0`. -/
theorem retryForces_forces {b : ℝ} (h : RetryForces F ε b) : F.Forces ε b := by
  intro ι _ G _ _ _ A
  rcases isEmpty_or_nonempty X with hX | hX
  · let E := EuclideanSpace ℂ (Fin 0)
    have hE : ∀ v : E, v = 0 := fun v => by ext i; exact Fin.elim0 i
    let R : RetrySolver F (F.access ι) E G ε :=
      { prot := .abort
        readout := 0
        readout_isometry := by ext1 v; exact (hE _).trans (hE _).symm
        success := fun x => isEmptyElim x
        accurate := fun x => isEmptyElim x }
    have hR := h ι E G R
    have h0 : R.prot.worstCost AdaptiveHamiltonianLowerBound.Access.valueWeight = 0 := rfl
    rw [h0, Nat.cast_zero] at hR
    exact ⟨hR.1.trans (Nat.cast_nonneg _), hR.1.trans (Nat.cast_nonneg _)⟩
  · have hR := h ι (heraldSpace A) G (solverToRetry A (seed_ne_zero A))
    rw [toRetry_worstCost, toRetry_worstCost, AdaptiveHamiltonianLowerBound.cost_valueWeight,
      MultiOracleCircuit.Program.cost_const, mul_one] at hR
    exact hR

/-- **Retry witnesses are released witnesses** (`Family.Witnesses`). -/
theorem retryWitnesses_witnesses {τ gbar b : ℝ}
    (h : RetryWitnesses F τ gbar ε b) : F.Witnesses τ gbar ε b := by
  exact ⟨h.inClass, h.time_eq, retryForces_forces h.forces⟩

end

end ODELowerBoundExtensions.Release
