import DysonSingleProgram.Parallel.ReadoutSupport

set_option autoImplicit false

/-!
# The first-success herald and readout reproduce the released four-attempt law

Manuscript lines 4111-4113 (Section `odel:sec:main`, output model) and 4687-4689 (proof of Lemma
`odel:lem:dyson`). For a stage `S` and a released retry
protocol `k` (`ODERepeatProtocol.Protocol`), `S.Good μ k` says that the stage's herald is a
projection, its readout is an isometry, its seed weights are unit (`∑ ‖ω_i‖² = 1`) and, on every
input, its heralded output reproduces the protocol: success probability `k.successMass x` and,
for every system operator `A`, `Re ⟪Φ, P e†(A ⊗ 1)e P Φ⟫ = Re tr(A ρ_x)` with
`ρ_x = k.successDensity x` (`LinearSystemLowerBound.corr`).

This is the program form of the vector-level purification step
`ODELowerBoundExtensions.Release.purification_step` (same space `ℂ^{M × d} ⊗ H`, same new state
`trialVec ⊗ Ψ`, same success/failure split); the single-program class needs, instead of one
contraction per observable, a herald projection and one isometric readout for all observables, so
the readout is built here and the computations reuse the lemmas of `Release.Purify`.

* `Stage.good_base`: the stage without attempts reproduces `abort` (success `0`);
* `Stage.good_step`: if the attempt program `C` prepares the purified released attempt
  `Release.trialVec t x` from the unit seed `μ`, then `S.step C μ t.output` reproduces
  `freshTrial t k` (the recursion `successDensity (freshTrial t k) = oneTrialDensity t +
  (1 - meanSuccess t) • successDensity k`, `TrialFamily.oneTrialDensity_eq_kraus`,
  `Release.inner_trialVec_fiber`, `Release.coordLift_tens`, `Release.fiber_tens`).
-/

namespace DysonSingleProgram.Parallel

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit Register
open ODELowerBoundExtensions.Release (coordLift tens jointFlatten jointSwap trialVec)
open ODELowerBoundExtensions.Dyson (encodedProjector_idem encodedProjector_adjoint
  one_sub_encodedProjector_adjoint adjoint_apply_self)
open scoped InnerProduct InnerProductSpace

variable {X L : Type*} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [CompleteSpace W] [FiniteDimensional ℂ W] {M : ℕ} {N : Type} [Fintype N] [DecidableEq N]
  {O : L → X → W →L[ℂ] W}

/-- **A stage reproduces a released retry protocol `k`**: unit seed weights
(`∑ ‖ω_i‖² = 1`), herald projection, isometric readout, and on every input the success
probability and the heralded readout correlation of every system operator are those of `k`. -/
structure Stage.Good {Lt : Type*} {Ot : Lt → X → W →L[ℂ] W} (S : Stage O M N)
    (μ : Joint (Fin M) W) (k : ODERepeatProtocol.Protocol Ot (EuclideanSpace ℂ N)) : Prop where
  weight_norm : ∑ i, ‖S.weight i‖ ^ 2 = 1
  herald_proj : IsStarProjection S.herald
  out_isometry : S.out.adjoint ∘L S.out = 1
  success : ∀ x, ‖S.herald (S.prog.eval x (S.seed μ))‖ ^ 2 = k.successMass x
  corr : ∀ (x : X) (A : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N),
    (⟪S.prog.eval x (S.seed μ),
      (S.herald ∘L Readout.outObs S.out A ∘L S.herald) (S.prog.eval x (S.seed μ))⟫_ℂ).re =
      LinearSystemLowerBound.corr A (k.successDensity x)

omit [FiniteDimensional ℂ W] [DecidableEq N] in
/-- The seed of a stage with unit weights and a unit main seed is a unit vector. -/
theorem Stage.norm_seed (S : Stage O M N) (μ : Joint (Fin M) W) (hμ : ‖μ‖ = 1)
    (hw : ∑ i, ‖S.weight i‖ ^ 2 = 1) : ‖S.seed μ‖ = 1 := by
  have h : ‖S.seed μ‖ ^ 2 = 1 ^ 2 := by
    rw [Stage.seed, PiLp.norm_sq_eq_of_L2]
    simp only [norm_smul, hμ, one_pow, mul_one, hw]
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 h

omit [FiniteDimensional ℂ W] in
/-- **The stage without attempts reproduces `abort`.** -/
theorem Stage.good_base {Lt : Type*} {Ot : Lt → X → W →L[ℂ] W} (i₀ : N) (μ : Joint (Fin M) W) :
    (Stage.base (O := O) (M := M) i₀).Good μ
      (ODERepeatProtocol.Protocol.abort : ODERepeatProtocol.Protocol Ot (EuclideanSpace ℂ N)) := by
  have hb : ∀ v i, baseOut (M := M) (W := W) i₀ v i = if i = i₀ then v else 0 := by
    intro v i
    by_cases h : i = i₀ <;> simp [baseOut, h]
  have hiso : ∀ v, ‖baseOut (M := M) (W := W) i₀ v‖ = ‖v‖ := by
    intro v
    have h2 : ‖baseOut (M := M) (W := W) i₀ v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp [hb, apply_ite]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
  refine ⟨by simp [Stage.base], ?_, ?_, fun x => ?_, fun x A => ?_⟩
  · exact IsStarProjection.zero _
  · exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp hiso
  · show ‖(0 : Joint Unit (Joint (Fin M) W) →L[ℂ] Joint Unit (Joint (Fin M) W)) _‖ ^ 2 = _
    simp [ODERepeatProtocol.Protocol.successMass, ODERepeatProtocol.Protocol.failureMass]
  · show (⟪_, ((0 : Joint Unit (Joint (Fin M) W) →L[ℂ] Joint Unit (Joint (Fin M) W)) ∘L _ ∘L
      (0 : Joint Unit (Joint (Fin M) W) →L[ℂ] Joint Unit (Joint (Fin M) W))) _⟫_ℂ).re = _
    simp [ODERepeatProtocol.Protocol.successDensity, LinearSystemLowerBound.corr_zero]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **One more attempt reproduces one more fresh trial**: if `C` prepares the purified released
attempt `trialVec t x` of the released trial family `t = ofCircuits q M ψ Fo` from the unit seed
`μ` on every input, then `S.step C μ Fo` reproduces `freshTrial t k` whenever `S` reproduces
`k`. -/
theorem Stage.good_step {Lq : Type*} {Oq : Lq → X → W →L[ℂ] W} (hO : ∀ l x, IsUnitary (O l x))
    (S : Stage O M N) (C : MultiOracleCircuit.Program (fiberOracle (Fin M) O))
    (μ : Joint (Fin M) W) (hμ : ‖μ‖ = 1) (q : ℕ → MultiOracleCircuit.Program Oq) (hM : 0 < M)
    (ψ : W) (hψ : ‖ψ‖ = 1) (Fo : EuclideanSpace ℂ N →L[ℂ] W) (hFo : Fo.adjoint ∘L Fo = 1)
    (hC : ∀ x, C.eval x μ = trialVec (ODERepeatProtocol.ofCircuits q M hM ψ hψ Fo hFo) x)
    (k : ODERepeatProtocol.Protocol Oq (EuclideanSpace ℂ N)) (hS : S.Good μ k) :
    (S.step C μ Fo).Good μ (.freshTrial (ODERepeatProtocol.ofCircuits q M hM ψ hψ Fo hFo) k) := by
  classical
  set t := ODERepeatProtocol.ofCircuits q M hM ψ hψ Fo hFo with ht
  set fl : Joint (S.step C μ Fo).I (Joint (Fin M) W) ≃ₗᵢ[ℂ]
      Joint (Coord M W) (Joint S.I (Joint (Fin M) W)) :=
    jointFlatten (Coord M W) S.I (Joint (Fin M) W) with hfl
  have hst : ∀ x, (S.step C μ Fo).prog.eval x ((S.step C μ Fo).seed μ) =
      fl.symm (tens (C.eval x μ) (S.prog.eval x (S.seed μ))) := fun x =>
    Stage.eval_step_seed S C μ Fo x
  have hFF : ∀ v, Fo.adjoint (Fo v) = v := adjoint_apply_self Fo hFo
  have hOM : ∀ l x, IsUnitary (fiberOracle (Fin M) O l x) := fun l x =>
    PhaseCircuit.isUnitary_fiber _ fun _ => hO l x
  have hOI : ∀ l x, IsUnitary (fiberOracle S.I (fiberOracle (Fin M) O) l x) := fun l x =>
    PhaseCircuit.isUnitary_fiber _ fun _ => hOM l x
  have hΨ : ∀ x, ‖S.prog.eval x (S.seed μ)‖ = 1 := fun x => by
    rw [(S.prog.eval x).norm_map_iff_adjoint_comp_self.mpr (S.prog.eval_unitary hOI x).1]
    exact S.norm_seed μ hμ hS.weight_norm
  have hφ : ∀ x, ‖C.eval x μ‖ = 1 := fun x => by
    rw [(C.eval x).norm_map_iff_adjoint_comp_self.mpr (C.eval_unitary hOM x).1, hμ]
  have hher : ∀ z, (S.step C μ Fo).herald (fl.symm z) = fl.symm (heraldStep Fo S.herald z) :=
    fun z => by
      show fl.symm (heraldStep Fo S.herald (fl.symm.symm (fl.symm z))) = _
      rw [LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply]
  have hout : ∀ z, (S.step C μ Fo).out (fl.symm z) = outStep Fo S.out z := fun z => by
    show outStep Fo S.out (fl (fl.symm z)) = _
    rw [LinearIsometryEquiv.apply_symm_apply]
  have hHP : IsStarProjection (S.step C μ Fo).herald :=
    (isStarProjection_heraldStep Fo hFo S.herald hS.herald_proj).map fl.symm.conjStarAlgEquiv
  have hPs : S.herald† = S.herald := hS.herald_proj.isSelfAdjoint.adjoint_eq
  have hnH : ∀ z, ‖(S.step C μ Fo).herald (fl.symm z)‖ = ‖heraldStep Fo S.herald z‖ := fun z => by
    rw [hher]
    exact fl.symm.norm_map _
  -- the success projector `Π = Fo Fo†` on the attempt register
  have hPP : (Fo ∘L Fo†) ∘L (Fo ∘L Fo†) = Fo ∘L Fo† :=
    ContinuousLinearMap.ext (encodedProjector_idem Fo hFo)
  have hPa : (Fo ∘L Fo†)† = Fo ∘L Fo† := encodedProjector_adjoint Fo
  have hff : ∀ (G G' : W →L[ℂ] W) (v : Joint (Fin M) W),
      Joint.fiber (fun _ => G) (Joint.fiber (fun _ => G') v) = Joint.fiber (fun _ => G ∘L G') v :=
    fun G G' v => congrArg (fun T => T v) (Joint.fiber_mul (fun _ => G) (fun _ => G'))
  have hPQ : (Fo ∘L Fo†) ∘L (1 - Fo ∘L Fo†) = 0 := by ext v; simp [hFF]
  have hQP : (1 - Fo ∘L Fo†) ∘L (Fo ∘L Fo†) = 0 := by ext v; simp [hFF]
  have hQQ : (1 - Fo ∘L Fo†) ∘L (1 - Fo ∘L Fo†) = 1 - Fo ∘L Fo† := by ext v; simp [hFF]
  have hQa : (1 - Fo ∘L Fo†)† = 1 - Fo ∘L Fo† := one_sub_encodedProjector_adjoint Fo
  have hfz : ∀ v : Joint (Fin M) W, Joint.fiber (fun _ => (0 : W →L[ℂ] W)) v = 0 := fun v => by
    ext; simp
  have htz : ∀ u : Joint S.I (Joint (Fin M) W), tens (0 : Joint (Fin M) W) u = 0 := fun u => by
    ext; simp [tens]
  have hsub : ∀ v : Joint (Fin M) W,
      Joint.fiber (fun _ => 1 - Fo ∘L Fo†) v = v - Joint.fiber (fun _ => Fo ∘L Fo†) v :=
    fun v => by ext; simp
  -- the herald on the product state
  have hsplit : ∀ (v : Joint (Fin M) W) (u : Joint S.I (Joint (Fin M) W)),
      heraldStep Fo S.herald (tens v u) = tens (Joint.fiber (fun _ => Fo ∘L Fo†) v) u +
        tens (Joint.fiber (fun _ => 1 - Fo ∘L Fo†) v) (S.herald u) := fun v u => by
    show coordLift (Fo ∘L Fo†) (tens v u) +
      coordLift (1 - Fo ∘L Fo†) (Joint.fiber (fun _ => S.herald) (tens v u)) = _
    rw [ODELowerBoundExtensions.Release.fiber_tens, ODELowerBoundExtensions.Release.coordLift_tens,
      ODELowerBoundExtensions.Release.coordLift_tens]
  -- the mean success probability of the attempt
  have hmean : ∀ x, ⟪C.eval x μ, Joint.fiber (fun _ => Fo ∘L Fo†) (C.eval x μ)⟫_ℂ =
      ((t.meanSuccess x : ℝ) : ℂ) := fun x => by
    have hPrj : ∀ j, ⟪(t.circuit j).eval x t.seed, (Fo ∘L Fo†) ((t.circuit j).eval x t.seed)⟫_ℂ =
        ((t.probability x j : ℝ) : ℂ) := by
      intro j
      rw [ContinuousLinearMap.comp_apply,
        ← ContinuousLinearMap.adjoint_inner_left Fo ((Fo†) ((t.circuit j).eval x t.seed)),
        inner_self_eq_norm_sq_to_K]
      simp [ODERepeatProtocol.TrialFamily.probability, ODERepeatProtocol.TrialFamily.amplitude, ht,
        ODERepeatProtocol.ofCircuits]
    rw [hC x]
    refine (ODELowerBoundExtensions.Release.inner_trialVec_fiber t (Fo ∘L Fo†) x).trans ?_
    simp only [hPrj, ODERepeatProtocol.TrialFamily.meanSuccess]
    push_cast
    ring
  have hnorms : ∀ x,
      ⟪Joint.fiber (fun _ => Fo ∘L Fo†) (C.eval x μ),
        Joint.fiber (fun _ => Fo ∘L Fo†) (C.eval x μ)⟫_ℂ = ((t.meanSuccess x : ℝ) : ℂ) ∧
      ⟪Joint.fiber (fun _ => Fo ∘L Fo†) (C.eval x μ),
        Joint.fiber (fun _ => 1 - Fo ∘L Fo†) (C.eval x μ)⟫_ℂ = 0 ∧
      ⟪Joint.fiber (fun _ => 1 - Fo ∘L Fo†) (C.eval x μ),
        Joint.fiber (fun _ => Fo ∘L Fo†) (C.eval x μ)⟫_ℂ = 0 ∧
      ⟪Joint.fiber (fun _ => 1 - Fo ∘L Fo†) (C.eval x μ),
        Joint.fiber (fun _ => 1 - Fo ∘L Fo†) (C.eval x μ)⟫_ℂ =
          ((1 - t.meanSuccess x : ℝ) : ℂ) := fun x => by
    have h1 : ⟪C.eval x μ, C.eval x μ⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hφ]; simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [inner_fiber_fiber, hPa, hPP, hmean]
    · rw [inner_fiber_fiber, hPa, hPQ, hfz, inner_zero_right]
    · rw [inner_fiber_fiber, hQa, hQP, hfz, inner_zero_right]
    · rw [inner_fiber_fiber, hQa, hQQ, hsub, inner_sub_right, h1, hmean]
      push_cast
      ring
  refine ⟨?_, hHP, ?_, fun x => ?_, fun x A => ?_⟩
  · -- unit seed weights
    show ∑ ai : Coord M W × S.I, ‖coordV ai.1 μ * S.weight ai.2‖ ^ 2 = 1
    have hc : ∑ a : Coord M W, ‖coordV a μ‖ ^ 2 = 1 := by
      have h : ‖μ‖ ^ 2 = 1 := by rw [hμ, one_pow]
      rw [PiLp.norm_sq_eq_of_L2] at h
      rw [← h, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← ((stdOrthonormalBasis ℂ W).repr).norm_map, EuclideanSpace.norm_sq_eq]
      rfl
    rw [Fintype.sum_prod_type]
    simp only [norm_mul, mul_pow, ← Finset.mul_sum, hS.weight_norm, mul_one, hc]
  · -- the readout is an isometry
    refine (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp fun v => ?_
    show ‖outStep Fo S.out (fl v)‖ = ‖v‖
    exact (norm_outStep Fo hFo S.out hS.out_isometry (fl v)).trans (fl.norm_map v)
  · -- success probability
    obtain ⟨n1, n2, n3, n4⟩ := hnorms x
    have hPΨ := hS.success x
    rw [hst, hnH, hsplit,
      ODERepeatProtocol.Protocol.freshTrial_successMass_eq, ← hPΨ]
    have hu : ⟪S.prog.eval x (S.seed μ), S.prog.eval x (S.seed μ)⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hΨ]; simp
    have hPn : ⟪S.herald (S.prog.eval x (S.seed μ)), S.herald (S.prog.eval x (S.seed μ))⟫_ℂ =
        ((‖S.herald (S.prog.eval x (S.seed μ))‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    have hc : ⟪tens (Joint.fiber (fun _ => Fo ∘L Fo†) (C.eval x μ)) (S.prog.eval x (S.seed μ)) +
        tens (Joint.fiber (fun _ => 1 - Fo ∘L Fo†) (C.eval x μ))
          (S.herald (S.prog.eval x (S.seed μ))),
        tens (Joint.fiber (fun _ => Fo ∘L Fo†) (C.eval x μ)) (S.prog.eval x (S.seed μ)) +
        tens (Joint.fiber (fun _ => 1 - Fo ∘L Fo†) (C.eval x μ))
          (S.herald (S.prog.eval x (S.seed μ)))⟫_ℂ =
        ((t.meanSuccess x + (1 - t.meanSuccess x) *
          ‖S.herald (S.prog.eval x (S.seed μ))‖ ^ 2 : ℝ) : ℂ) := by
      simp only [inner_add_left, inner_add_right, ODELowerBoundExtensions.Release.inner_tens, n1,
        n2, n3, n4, hu, hPn]
      push_cast
      ring
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hc, RCLike.re_to_complex, Complex.ofReal_re]
  · -- heralded readout correlation
    obtain ⟨n1, n2, n3, n4⟩ := hnorms x
    have hred : ∀ z, ⟪fl.symm z, ((S.step C μ Fo).herald ∘L
        Readout.outObs (S.step C μ Fo).out A ∘L (S.step C μ Fo).herald) (fl.symm z)⟫_ℂ =
        ⟪outStep Fo S.out (heraldStep Fo S.herald z),
          Readout.liftObs A (outStep Fo S.out (heraldStep Fo S.herald z))⟫_ℂ := fun z => by
      have hadj : (S.step C μ Fo).herald† = (S.step C μ Fo).herald :=
        hHP.isSelfAdjoint.adjoint_eq
      have e1 : ⟪fl.symm z, ((S.step C μ Fo).herald ∘L
          Readout.outObs (S.step C μ Fo).out A ∘L (S.step C μ Fo).herald) (fl.symm z)⟫_ℂ =
          ⟪(S.step C μ Fo).herald (fl.symm z), Readout.outObs (S.step C μ Fo).out A
            ((S.step C μ Fo).herald (fl.symm z))⟫_ℂ := by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
          ← ContinuousLinearMap.adjoint_inner_left ((S.step C μ Fo).herald), hadj]
      rw [e1, hher, Readout.outObs, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_inner_right, hout]
      rfl
    rw [hst, hred, inner_outStep_liftObs, inner_succRead_liftObs,
      inner_failRead_liftObs, hsplit]
    have hA : Joint.fiber (fun _ => Fo ∘L Fo†) (Joint.fiber (fun _ => Fo ∘L Fo†) (C.eval x μ)) =
        Joint.fiber (fun _ => Fo ∘L Fo†) (C.eval x μ) := by rw [hff, hPP]
    have hB : Joint.fiber (fun _ => Fo ∘L Fo†)
        (Joint.fiber (fun _ => 1 - Fo ∘L Fo†) (C.eval x μ)) = 0 := by
      rw [hff, hPQ, hfz]
    have hB' : Joint.fiber (fun _ => 1 - Fo ∘L Fo†)
        (Joint.fiber (fun _ => Fo ∘L Fo†) (C.eval x μ)) = 0 := by
      rw [hff, hQP, hfz]
    have hD : Joint.fiber (fun _ => 1 - Fo ∘L Fo†)
        (Joint.fiber (fun _ => 1 - Fo ∘L Fo†) (C.eval x μ)) =
        Joint.fiber (fun _ => 1 - Fo ∘L Fo†) (C.eval x μ) := by rw [hff, hQQ]
    simp only [map_add, ODELowerBoundExtensions.Release.coordLift_tens, hA, hB, hB', hD, htz,
      add_zero, zero_add, ODELowerBoundExtensions.Release.fiber_tens,
      ODELowerBoundExtensions.Release.inner_tens, n4]
    have hG : ⟪Joint.fiber (fun _ => Fo ∘L Fo†) (C.eval x μ),
        Joint.fiber (fun _ => Fo ∘L A ∘L Fo†) (Joint.fiber (fun _ => Fo ∘L Fo†) (C.eval x μ))⟫_ℂ =
        (t.choices : ℂ)⁻¹ * ∑ j, ⟪t.amplitude x j, A (t.amplitude x j)⟫_ℂ := by
      rw [hff, inner_fiber_fiber,
        show (Fo ∘L Fo†)† ∘L ((Fo ∘L A ∘L Fo†) ∘L (Fo ∘L Fo†)) = Fo ∘L A ∘L Fo† by
          rw [hPa]; ext v; simp [hFF], hC x]
      refine (ODELowerBoundExtensions.Release.inner_trialVec_fiber t (Fo ∘L A ∘L Fo†) x).trans ?_
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [ContinuousLinearMap.comp_apply, ODERepeatProtocol.TrialFamily.amplitude]
      exact (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
    have hu : ⟪S.prog.eval x (S.seed μ), S.prog.eval x (S.seed μ)⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hΨ]; simp
    have hc := hS.corr x A
    simp only [ContinuousLinearMap.comp_apply] at hc
    rw [hG, hu, ← ContinuousLinearMap.adjoint_inner_right, hPs,
      ODERepeatProtocol.Protocol.successDensity, LinearSystemLowerBound.corr_add,
      LinearSystemLowerBound.corr_smul_real, ← hc, t.oneTrialDensity_eq_kraus]
    have hM' : ((t.choices : ℂ))⁻¹ = (((t.choices : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [hM', LinearSystemLowerBound.corr_smul_real, LinearSystemLowerBound.corr_sum]
    simp only [LinearSystemLowerBound.corr_pure, mul_one, Complex.add_re, Complex.re_ofReal_mul,
      Complex.re_sum]

end

end DysonSingleProgram.Parallel
