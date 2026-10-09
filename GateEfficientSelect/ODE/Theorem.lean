import GateEfficientSelect.ODE.Certificate
import TimeDependentODE.Continuous.Existence

/-!
# Gate-efficient dissipative ODE solver on branch-dependent meshes, exact gates

This is the time-dependent, exact-gate part of Theorem `ode:thm:gates` with the branch-dependent
meshes of Lemma `ode:lem:gate-select` and a positive source quadrature with the source
certificate of equation `ode:eq:gate-source-certificates`, in place of the masking of every
source branch on one common mesh with the left-endpoint quadrature of the released
`GateODE.Time.solver`.

**The protocol** is the released one, `GateODE.Time.TParams.protocol p v`: it depends only on
the public data `p` (including the mesh exponent `m`) and the seed `v`, so its validity and its
worst-case counts of gates and calls are those of the released theorem. The branch-dependent
meshes enter only through the instance: the private operation of the joint label `z = (s, w)` at
slot `r` serves the branch of the source label `s` on its own mesh, of start `startB v s`
(`0` or a node `v q ∈ [0, T]`) and step `(T - startB v s) / 2^m`, with the sample
addresses `addrB v s r = startB v s + r (T - startB v s) / 2^m` (`BInstanceOK`).

**Main theorem** (`solverB`). For public data satisfying the released `PublicOK` and a unit
seed `v`, the protocol consists of valid elementary instructions, uses in every history at most
`80 g · prepGates + 40 g · reflGates` elementary gates, `480 g d` private calls, `960 g d` calls
of `U_J` or `U_J†`, `80 g` loading calls, `160 g` weight-preparation calls and `40 g` seed
reflections, and for every instance satisfying `BInstanceOK` satisfies the released `Outcome`:
success probability at least `175/256 > 2/3`, every successful trial within `ε / 500` of
`x(T)/‖x(T)‖` up to a global phase, and a conditional output density operator within trace
distance `ε` of `x(T)/‖x(T)‖`.

`exists_branch_solution`: for a Lipschitz generator path, the homogeneous solutions `y_s` of
the source certificate exist from every start time and source vector.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSelect.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire)
open GateODE (goodF seedState)
open GateODE.Time (TParams TOracles trun)
open TimeDependentODE (SolvesODE)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **The homogeneous branch solutions exist.** For a Lipschitz generator path on `[0, T]`,
every start time `a ∈ [0, T]` and every vector `z`, the homogeneous equation `y' = -G(u) y` has a
solution on `[a, T]` with `y(a) = z`. -/
theorem exists_branch_solution (G : ℝ → P →L[ℂ] P) (T βG a : ℝ) (ha : 0 ≤ a) (haT : a ≤ T)
    (hGLip : ∀ u ∈ Set.Icc 0 T, ∀ u' ∈ Set.Icc 0 T, ‖G u - G u'‖ ≤ βG * |u - u'|) (z : P) :
    ∃ y : ℝ → P, y a = z ∧ SolvesODE G (fun _ => 0) y a T := by
  have hmaps : Set.MapsTo (fun t : ℝ => t + a) (Set.Icc 0 (T - a)) (Set.Icc 0 T) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hGc : ContinuousOn G (Set.Icc 0 T) :=
    TimeDependentODE.continuousOn_of_norm_sub_le G hGLip
  obtain ⟨y, hy0, hy⟩ := TimeDependentODE.exists_solvesODE (fun t => G (t + a)) (fun _ => 0)
    (sub_nonneg.mpr haT) (hGc.comp (continuous_add_const a).continuousOn hmaps)
    continuousOn_const z
  refine ⟨fun t => y (t - a), by simp [hy0], ?_⟩
  intro t ht
  have hmaps' : Set.MapsTo (fun s : ℝ => s - a) (Set.Icc a T) (Set.Icc 0 (T - a)) := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hg : HasDerivWithinAt (fun s : ℝ => s - a) 1 (Set.Icc a T) t :=
    ((hasDerivAt_id' t).sub_const a).hasDerivWithinAt
  have h := (hy (t - a) (hmaps' ht)).scomp t hg hmaps'
  simpa only [one_smul, sub_add_cancel, Function.comp_def] using h

variable (p : TParams)

variable [FiniteDimensional ℂ P]

/-- **The released time-dependent protocol is correct on branch-dependent meshes** for every
instance satisfying `BInstanceOK`. -/
theorem outcomeB (hp : p.PublicOK) (v₀ : P) (hv : ‖v₀‖ = 1) (σ : TOracles p.a p.m p.l P)
    (v wq : ℕ → ℝ) (fv : ℕ → P) (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P)
    (G : ℝ → P →L[ℂ] P) (b x : ℝ → P) (ys : Bool × (Fin p.m → Bool) → ℝ → P) (βG δG κ : ℝ)
    (hI : BInstanceOK p v₀ σ v wq fv Hb Lb G b x ys βG δG κ) :
    p.Outcome v₀ hv hp.g_ge σ (x p.T) := by
  have hU := hI.unitary
  have hunit : ∀ j, IsUnitary (trun v₀ σ (p.trialC j)) := fun j =>
    GateODE.Time.trun_isUnitary v₀ σ hU hv _ (p.trialC_valid hp.tau_pos.le hp.nu_pos hp.mesh j)
  obtain ⟨hM, _, hmean, hdir⟩ := trial_boundsB p hp v₀ hv σ v wq fv Hb Lb G b x ys βG δG κ hI
  have hunitT : ∀ j, IsUnitary (((p.trials v₀ hv hp.g_ge).circuit j).eval σ) := by
    intro j
    rw [p.trials_eval]
    exact hunit _
  have hprob : ∀ j, (p.trials v₀ hv hp.g_ge).probability σ j =
      ‖ODEHeraldedSuccess.successProjector goodF
        (trun v₀ σ (p.trialC j.val) (seedState v₀))‖ ^ 2 := by
    intro j
    rw [(p.trials v₀ hv hp.g_ge).probability_eq_projected σ j, p.trials_eval, p.trials_output,
      p.trials_seed]
  have hsumP : ∑ j : Fin (p.trials v₀ hv hp.g_ge).choices,
      (p.trials v₀ hv hp.g_ge).probability σ j =
      ∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations p.ratio),
        ‖ODEHeraldedSuccess.successProjector goodF
          (trun v₀ σ (p.trialC j) (seedState v₀))‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun j _ => hprob j)]
    exact Fin.sum_univ_eq_sum_range (fun j => ‖ODEHeraldedSuccess.successProjector goodF
      (trun v₀ σ (p.trialC j) (seedState v₀))‖ ^ 2) _
  have hmeanT : (1 : ℝ) / 4 ≤
      ODERepeatProbability.mean ((p.trials v₀ hv hp.g_ge).probability σ) := by
    unfold ODERepeatProbability.mean
    rw [hsumP]
    exact hmean
  have hupper : ODERepeatProbability.mean ((p.trials v₀ hv hp.g_ge).probability σ) ≤ 1 :=
    ODERepeatProbability.mean_le_one _ (p.trials v₀ hv hp.g_ge).choices_pos
      (fun j => ((p.trials v₀ hv hp.g_ge).probability_bounds σ hunitT j).2)
  have hnonneg : ∀ j, 0 ≤ (p.trials v₀ hv hp.g_ge).probability σ j :=
    fun j => ((p.trials v₀ hv hp.g_ge).probability_bounds σ hunitT j).1
  have hsucc : (p.protocol v₀ hv hp.g_ge).successMass σ =
      ODERepeatProbability.successProbability ((p.trials v₀ hv hp.g_ge).probability σ) :=
    ODERepeatProtocol.Protocol.four_successMass_eq (p.trials v₀ hv hp.g_ge) σ
  have hdens : (p.protocol v₀ hv hp.g_ge).conditionalDensity σ =
      ODEMixedOutput.ensemble
        (ODERepeatProbability.conditionalWeight ((p.trials v₀ hv hp.g_ge).probability σ))
        (fun a => (p.trials v₀ hv hp.g_ge).outputDirection σ a.2) :=
    ODERepeatProtocol.Protocol.four_conditionalDensity_eq (p.trials v₀ hv hp.g_ge) σ
  have hw := ODERepeatProbability.conditionalWeight_nonneg _ hnonneg hmeanT hupper
  have hsum := ODERepeatProbability.conditionalWeight_sum _ hmeanT hupper
  have hne : ∀ a : Fin 4 × Fin (p.trials v₀ hv hp.g_ge).choices,
      ODERepeatProbability.conditionalWeight ((p.trials v₀ hv hp.g_ge).probability σ) a ≠ 0 →
      (p.trials v₀ hv hp.g_ge).amplitude σ a.2 ≠ 0 := by
    intro a ha hz
    apply ODERepeatProbability.conditionalWeight_ne_zero_implies _ a ha
    rw [ODERepeatProtocol.TrialFamily.probability, hz, norm_zero]
    norm_num
  have hclose : ∀ a : Fin 4 × Fin (p.trials v₀ hv hp.g_ge).choices,
      ODERepeatProbability.conditionalWeight ((p.trials v₀ hv hp.g_ge).probability σ) a ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • (p.trials v₀ hv hp.g_ge).outputDirection σ a.2 -
        unitDirection (x p.T)‖ ≤ p.ε / 500 := by
    intro a ha
    have hz := hne a ha
    rw [p.trials_amplitude] at hz
    have h := hdir a.2.val hz
    rw [ODERepeatProtocol.TrialFamily.outputDirection, p.trials_amplitude]
    exact h
  have hunitDir : ∀ a : Fin 4 × Fin (p.trials v₀ hv hp.g_ge).choices,
      ODERepeatProbability.conditionalWeight ((p.trials v₀ hv hp.g_ge).probability σ) a ≠ 0 →
      ‖(p.trials v₀ hv hp.g_ge).outputDirection σ a.2‖ = 1 :=
    fun a ha => ODEStateNormalization.unitDirection_norm _ (hne a ha)
  obtain ⟨hDensity, hSymm, hDistance⟩ := ODEMixedOutput.ensemble_trace_distance_le
    (ODERepeatProbability.conditionalWeight ((p.trials v₀ hv hp.g_ge).probability σ))
    (fun a => (p.trials v₀ hv hp.g_ge).outputDirection σ a.2)
    (unitDirection (x p.T)) (p.ε / 500) hw hsum
    hunitDir (ODEStateNormalization.unitDirection_norm _ hI.target_ne) hclose
  have hlow : (175 : ℝ) / 256 ≤ (p.protocol v₀ hv hp.g_ge).successMass σ := by
    rw [hsucc]
    exact ODERepeatProbability.successProbability_lower _ hmeanT hupper
  have htwo : (2 : ℝ) / 3 ≤ (p.protocol v₀ hv hp.g_ge).successMass σ := by
    rw [hsucc]
    exact ODERepeatProbability.successProbability_two_thirds _ hmeanT hupper
  have hden : ODEMixedOutput.IsDensity ((p.protocol v₀ hv hp.g_ge).conditionalDensity σ) := by
    rw [hdens]
    exact hDensity
  have herr : ∃ h : ((p.protocol v₀ hv hp.g_ge).conditionalDensity σ -
        ODEMixedOutput.pureOperator (unitDirection (x p.T))).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance ((p.protocol v₀ hv hp.g_ge).conditionalDensity σ)
        (ODEMixedOutput.pureOperator (unitDirection (x p.T))) h ≤ p.ε := by
    rw [hdens]
    refine ⟨hSymm, hDistance.trans ?_⟩
    have := hp.ε_pos
    linarith
  exact ⟨hunit, hmean, hdir, hlow, htwo, hden, herr⟩

/-- **Gate-efficient dissipative ODE solver on branch-dependent meshes, exact gates**
(Theorem `ode:thm:gates`, time-dependent part, with the branch-dependent meshes of Lemma
`ode:lem:gate-select` and a positive source quadrature). The protocol of the released
`GateODE.Time.solver` depends only on the public data `p` and the seed `v`; it keeps the
released validity, worst-case counts, register and degree bounds, and for every instance
satisfying `BInstanceOK` (`(σ, v, w, f, H_b, L_b, G, b, x, y, βG, δG, κ)` quantified afterwards)
it satisfies the released `Outcome` for `x(T)`. -/
theorem solverB (hp : p.PublicOK) (v₀ : P) (hv : ‖v₀‖ = 1) :
    (∀ j, ∀ g ∈ p.trialC j, g.Valid Wire.anc) ∧
    ((p.protocol v₀ hv hp.g_ge).worstCost p.wGate : ℝ) ≤
      80 * p.g * p.prepGates + 40 * p.g * p.reflGates ∧
    ((p.protocol v₀ hv hp.g_ge).worstCost p.wPriv : ℝ) ≤ 480 * p.g * p.d ∧
    ((p.protocol v₀ hv hp.g_ge).worstCost p.wUJ : ℝ) ≤ 960 * p.g * p.d ∧
    ((p.protocol v₀ hv hp.g_ge).worstCost p.wLoad : ℝ) ≤ 80 * p.g ∧
    ((p.protocol v₀ hv hp.g_ge).worstCost p.wPrep : ℝ) ≤ 160 * p.g ∧
    ((p.protocol v₀ hv hp.g_ge).worstCost p.wSeed : ℝ) ≤ 40 * p.g ∧
    p.prepGates = 200 * (p.d + 1) * (p.a + p.m + p.r + 1) + 3 * (2 ^ p.l * (2 * p.l + 1)) ∧
    p.reflGates = 6 * (2 * p.a + 4 * p.m + 6 * p.r + 4 + p.l) + 4 ∧
    Fintype.card p.W = 4 * p.a + 8 * p.m + 12 * p.r + 2 * p.l + 8 ∧
    (p.d : ℝ) ≤ 128 * (p.tau * p.qbar + p.Q * (1 + Real.log (3 / p.nu))) ∧
    2 * p.d + 2 ≤ 2 ^ p.r ∧ 2 ^ p.r ≤ 4 * (p.d + 1) ∧
    p.J + 2 ≤ 2 ^ p.l ∧ 2 ^ p.l < 2 * (p.J + 2) ∧
    (p.J : ℝ) ≤ p.R * (p.T * p.lamD + 2 * Real.log (512 / p.nu)) / Real.pi + 3 ∧
    ∀ (σ : TOracles p.a p.m p.l P) (v wq : ℕ → ℝ) (fv : ℕ → P)
      (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P) (b x : ℝ → P)
      (ys : Bool × (Fin p.m → Bool) → ℝ → P) (βG δG κ : ℝ),
      BInstanceOK p v₀ σ v wq fv Hb Lb G b x ys βG δG κ →
        p.Outcome v₀ hv hp.g_ge σ (x p.T) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, -⟩ :=
    GateODE.Time.solver p hp v₀ hv
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    fun σ v wq fv Hb Lb G b x ys βG δG κ hI =>
      outcomeB p hp v₀ hv σ v wq fv Hb Lb G b x ys βG δG κ hI⟩

end

end SparseHamiltonian.GateSelect.ODE
