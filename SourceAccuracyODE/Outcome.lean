import GateEfficientNative.ODE.Protocol
import ZeroTimeGateODE.Certificate

/-!
# The native protocol with a general per-trial direction bound

The released guarantees `GateNative.NOutcome prepN g ε` of the native four-attempt protocol fix the
per-trial direction bound at `ε / 500`, and the released certificates reach it from a vector error
of at most `9 ν B` for a lifted preparation (`GateNative.output_certificate9`) and `2 ν B` for a
direct source assembly (`ZeroTimeGateODE.output_certificate_direct`), `ν = ε / (10⁴ g)`. Theorem
`ode:thm:gates` asks only that every successful trial be within `ε` of the normalised solution,
with conditional trace distance at most `ε`, and its proof tolerates the vector error `19 ν B` (eq.
`ode:eq:gate-vector-error`). Here the same protocol is certified from any relative vector error
`ρ ≤ 1/4`:

* `WOutcome prepN g β`: the guarantees of `NOutcome` with the per-trial direction bound and the
  conditional trace distance both at most `β` (`WOutcome.mono`);
* `woutcome_of_bounds`: mean success at least `1/4` and per-trial direction error at most `β` give
  `WOutcome … β` (the released `noutcome_of_bounds`, with the trace distance `β` of the released
  ensemble bound);
* `trial_bounds_of_rel`, `native_trial_bounds_rel`: a decoded vector `c d` within `ρ ‖y‖` of `y`,
  `c ≤ 3 g ‖y‖`, gives mean success at least `1/4` (the released amplification theorem for every
  amplitude at least `1/(4g)`, `ZeroTimeGateODE.randomized_certificate_full`) and per-trial
  direction error `2ρ`;
* `woutcome_of_vec`: the protocol of a valid native preparation has `WOutcome … (2ρ + η)` against
  `x` if its decoded vector is within `ρ` of an intermediate target `y` whose direction is within
  `η` of that of `x`;
* `native_vector_error_le`: a native preparation within `δ` of a lifted released preparation whose
  decoded vector meets the released vector error `6 ν B` has vector error `3 B δ + 6 ν B`;
* `woutcome_lifted`, `woutcome_direct`: `WOutcome … (2ρ + η)` from the released certificate of a
  lifted preparation (`(3δ + 6ν) g ≤ ρ`) and of a direct source assembly (`δ g ≤ ρ`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.SourceAccuracyODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open GateODE (OWire AW goodF)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-- `ν g = ε / 10⁴` for the released precision `ν = ε/(10⁴ g)`. -/
theorem precision_mul (g ε : ℝ) (hg : 0 < g) :
    ImprovedODEQueryBudget.precision g ε * g = ε / 10000 := by
  have e : ImprovedODEQueryBudget.precision g ε = ε / (10000 * g) := rfl
  rw [e]
  field_simp

/-! ### Amplification from a relative vector error -/

section Output

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **Randomized amplification from a relative vector error**: for an isometric decoding `G`, a
unitary preparation `U` and a unit seed `s` whose scaled decoded vector `c G† (U s)` is within
`ρ ‖x‖` of `x`, `ρ ≤ 1/4`, `0 < c ≤ 3 g ‖x‖`, the actual Grover trials have mean success at least
`1/4` over the released cutoff, and every nonzero decoded trial is within `2ρ` of `x / ‖x‖` up to
a global phase. -/
theorem trial_bounds_of_rel (G : P →L[ℂ] E) (hG : G† ∘L G = 1) (U : E →L[ℂ] E)
    (hU : IsUnitary U) (s : E) (hs : ‖s‖ = 1) (x : P) (c g ρ : ℝ) (hx : x ≠ 0) (hg : 1 ≤ g)
    (hc : 0 < c) (hρ : ρ ≤ 1 / 4) (hscale : c ≤ 3 * g * ‖x‖)
    (hvec : ‖c • (G†) (U s) - x‖ ≤ ρ * ‖x‖) :
    0 < ODEGroverAverage.chosenIterations g ∧
    (ODEGroverAverage.chosenIterations g : ℝ) ≤ 5 * g ∧
    (1 : ℝ) / 4 ≤ (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations g),
      ‖ODEHeraldedSuccess.successProjector G (ODEGroverActual.trial G U s j)‖ ^ 2) /
        (ODEGroverAverage.chosenIterations g : ℝ) ∧
    ∀ j : ℕ, (G†) (ODEGroverActual.trial G U s j) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection ((G†) (ODEGroverActual.trial G U s j)) - unitDirection x‖ ≤
          2 * ρ := by
  have hρ1 : ρ < 1 := by linarith
  obtain ⟨-, hdir⟩ := ODEStateNormalization.relative_error x _ ρ hx hρ1 hvec
  rw [ODEHeraldedSuccess.unitDirection_pos_smul c hc] at hdir
  have hamp : ODEGroverActual.amplitude G U s = ‖(G†) (U s)‖ := by
    rw [ODEGroverActual.amplitude, ← ODEHeraldedSuccess.successfulComponent,
      ODEHeraldedSuccess.successfulComponent_norm _ hG]
    rfl
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hg0 : 0 < g := by linarith
  have hd0 : 0 ≤ ‖(G†) (U s)‖ := norm_nonneg _
  have hlow : (1 - ρ) * ‖x‖ ≤ c * ‖(G†) (U s)‖ := by
    have h1 := norm_sub_norm_le x (c • (G†) (U s))
    rw [norm_sub_rev x, norm_smul, Real.norm_eq_abs, abs_of_pos hc] at h1
    linarith
  have hlow' : 1 / (4 * g) ≤ ‖(G†) (U s)‖ := by
    have h2 : c * ‖(G†) (U s)‖ ≤ 3 * g * ‖x‖ * ‖(G†) (U s)‖ :=
      mul_le_mul_of_nonneg_right hscale hd0
    have h3 : (1 - ρ) * ‖x‖ ≤ (3 * g * ‖(G†) (U s)‖) * ‖x‖ := by
      have e : 3 * g * ‖x‖ * ‖(G†) (U s)‖ = (3 * g * ‖(G†) (U s)‖) * ‖x‖ := by ring
      linarith
    have h4 : 1 - ρ ≤ 3 * g * ‖(G†) (U s)‖ := le_of_mul_le_mul_right h3 hxn
    rw [div_le_iff₀ (by linarith)]
    have e : ‖(G†) (U s)‖ * (4 * g) = (4 / 3) * (3 * g * ‖(G†) (U s)‖) := by ring
    rw [e]
    linarith
  exact ZeroTimeGateODE.randomized_certificate_full G hG U hU s hs g hg
    (by rw [hamp]; exact hlow') x (2 * ρ) hdir

end Output

/-! ### The native protocol -/

section Native

variable {a m r K k l f : ℕ} {S Zs Z Y J : Type*} {nP bT bP A : ℕ}
variable [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y]

/-- **The guarantees of the native protocol for one instance, per-trial bound `β`**: the fields
of `GateNative.NOutcome` with the per-trial direction error and the conditional trace distance
both at most `β`. -/
structure WOutcome (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (g β : ℝ) (hg : 1 ≤ g) (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (x : Reg S ℂ) : Prop where
  unitary_trials : ∀ j, IsUnitary (nrun prim (trialN prepN j))
  mean_success : (1 : ℝ) / 4 ≤
    (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations g),
      ‖ODEHeraldedSuccess.successProjector goodN (nrun prim (trialN prepN j) sN)‖ ^ 2) /
      (ODEGroverAverage.chosenIterations g : ℝ)
  trial_direction : ∀ j : ℕ, (goodN†) (nrun prim (trialN prepN j) sN) ≠ 0 →
    ∃ ω : ℂ, ‖ω‖ = 1 ∧
      ‖ω • unitDirection ((goodN†) (nrun prim (trialN prepN j) sN)) - unitDirection x‖ ≤ β
  success_lower : (175 : ℝ) / 256 ≤ (nprotocol prepN g hg).successMass prim
  success_two_thirds : (2 : ℝ) / 3 ≤ (nprotocol prepN g hg).successMass prim
  output_density : ODEMixedOutput.IsDensity ((nprotocol prepN g hg).conditionalDensity prim)
  conditional_error :
    ∃ h : ((nprotocol prepN g hg).conditionalDensity prim -
        ODEMixedOutput.pureOperator (unitDirection x)).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance ((nprotocol prepN g hg).conditionalDensity prim)
        (ODEMixedOutput.pureOperator (unitDirection x)) h ≤ β

/-- A weaker per-trial bound. -/
theorem WOutcome.mono {prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)}
    {g β β' : ℝ} {hg : 1 ≤ g} {prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ} {x : Reg S ℂ}
    (h : WOutcome prepN g β hg prim x) (hβ : β ≤ β') : WOutcome prepN g β' hg prim x := by
  refine ⟨h.unitary_trials, h.mean_success, fun j hj => ?_, h.success_lower,
    h.success_two_thirds, h.output_density, ?_⟩
  · obtain ⟨ω, hω, hd⟩ := h.trial_direction j hj
    exact ⟨ω, hω, hd.trans hβ⟩
  · obtain ⟨hs, hd⟩ := h.conditional_error
    exact ⟨hs, hd.trans hβ⟩

/-- **The native protocol is correct with per-trial bound `β`** whenever its trials are valid and
the mean success and direction bounds of the trial circuits hold (the released
`GateNative.noutcome_of_bounds` with the bound `β` in place of `ε / 500`). -/
theorem woutcome_of_bounds (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j))
    (hvalid : ∀ i ∈ prepN, i.Valid) (x : Reg S ℂ) (hx : x ≠ 0) (g β : ℝ) (hg : 1 ≤ g)
    (hmean : (1 : ℝ) / 4 ≤
      (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations g),
        ‖ODEHeraldedSuccess.successProjector goodN (nrun prim (trialN prepN j) sN)‖ ^ 2) /
        (ODEGroverAverage.chosenIterations g : ℝ))
    (hdir : ∀ j : ℕ, (goodN†) (nrun prim (trialN prepN j) sN) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection ((goodN†) (nrun prim (trialN prepN j) sN)) - unitDirection x‖ ≤ β) :
    WOutcome prepN g β hg prim x := by
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
        unitDirection x‖ ≤ β := by
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
    (unitDirection x) β hw hsum hunitDir (ODEStateNormalization.unitDirection_norm _ hx)
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
        (ODEMixedOutput.pureOperator (unitDirection x)) h ≤ β := by
    rw [hdens]
    exact ⟨hSymm, hDistance⟩
  exact ⟨hunit, hmean, hdir, hlow, htwo, hden, herr⟩

/-- **Mean success and per-trial direction error of the native trials from a relative vector
error**: for every native ODE register with a large enough pool and every unitary native
preparation that never touches the native flag and pool of the zero tests and whose scaled clean
decoded vector `c dN` is within `ρ ‖y‖` of `y`, `ρ ≤ 1/4`, `0 < c ≤ 3 g ‖y‖`, the released native
trials have mean success at least `1/4` over the released cutoff and every nonzero decoded trial is
within `2ρ` of `y / ‖y‖` up to a global phase. -/
theorem native_trial_bounds_rel (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
      Fintype.card S ≤ nP + 1)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hU : IsUnitary (nrun prim prepN)) (hP : Pres2 (ZeroOn reflWire) (nrun prim prepN))
    (y : Reg S ℂ) (c g ρ : ℝ) (hy : y ≠ 0) (hg : 1 ≤ g) (hc : 0 < c) (hρ : ρ ≤ 1 / 4)
    (hscale : c ≤ 3 * g * ‖y‖)
    (hvec : ‖c • (goodN†) (nrun prim prepN sN) - y‖ ≤ ρ * ‖y‖) :
    (1 : ℝ) / 4 ≤ (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations g),
      ‖ODEHeraldedSuccess.successProjector goodN (nrun prim (trialN prepN j) sN)‖ ^ 2) /
        (ODEGroverAverage.chosenIterations g : ℝ) ∧
    ∀ j : ℕ, (goodN†) (nrun prim (trialN prepN j) sN) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection ((goodN†) (nrun prim (trialN prepN j) sN)) - unitDirection y‖ ≤
          2 * ρ := by
  have htrial : ∀ j, nrun prim (trialN prepN j) sN =
      ODEGroverActual.trial goodN (nrun prim prepN) sN j :=
    fun j => trialN_seed prim hnP prepN hU hP j
  have hGi := goodN_isometry (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)
  have hs := norm_sN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
    (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)
  simp only [htrial]
  generalize goodN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
    (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A) = G at hGi hvec ⊢
  generalize nrun prim prepN = U at hU hvec ⊢
  generalize (sN : Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ) = s at hs hvec ⊢
  obtain ⟨-, -, hmean, hdir⟩ := trial_bounds_of_rel G hGi U hU s hs y c g ρ hy hg hc hρ hscale hvec
  exact ⟨hmean, hdir⟩

/-- **The native protocol is correct from a relative vector error**: for every native ODE register
with a large enough pool and every valid native preparation that never touches the native flag and
pool of the zero tests, if its scaled clean decoded vector `c dN` is within `ρ ‖y‖` of an
intermediate target `y`, `ρ ≤ 1/4`, `0 < c ≤ 3 g ‖y‖`, and the direction of `y` is within `η` of
that of `x`, then `nprotocol prepN g` has the guarantees `WOutcome … (2ρ + η)` against `x`. -/
theorem woutcome_of_vec
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
      Fintype.card S ≤ nP + 1)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j))
    (hvalid : ∀ i ∈ prepN, i.Valid) (hP : Pres2 (ZeroOn reflWire) (nrun prim prepN))
    (y x : Reg S ℂ) (c g ρ η : ℝ) (hy : y ≠ 0) (hx : x ≠ 0) (hg : 1 ≤ g) (hc : 0 < c)
    (hρ : ρ ≤ 1 / 4) (hscale : c ≤ 3 * g * ‖y‖)
    (hvec : ‖c • (goodN†) (nrun prim prepN sN) - y‖ ≤ ρ * ‖y‖)
    (hdirY : ‖unitDirection y - unitDirection x‖ ≤ η) :
    WOutcome prepN g (2 * ρ + η) hg prim x := by
  obtain ⟨hmean, hdir⟩ := native_trial_bounds_rel prim hnP prepN
    (nrun_isUnitary prim hprim _ hvalid) hP y c g ρ hy hg hc hρ hscale hvec
  refine woutcome_of_bounds prepN prim hprim hvalid x hx g (2 * ρ + η) hg hmean ?_
  intro j hj
  obtain ⟨ω, hω, hd⟩ := hdir j hj
  refine ⟨ω, hω, ?_⟩
  refine (norm_sub_le_norm_sub_add_norm_sub _ (unitDirection y) _).trans ?_
  linarith only [hd, hdirY]

/-- **The vector error of a native preparation** within `δ` of a lifted released preparation
`Urel` whose decoded vector meets the released error `6 ν B`: `‖3B dN - x‖ ≤ 3 B δ + 6 ν B`. -/
theorem native_vector_error_le
    (UN : Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ →L[ℂ]
      Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ)
    (Urel : Reg (AW a m r K k l f) (Reg S ℂ) →L[ℂ] Reg (AW a m r K k l f) (Reg S ℂ))
    {δ : ℝ} (hA : ApproxOn CleanX UN (liftB (conj Urel)) δ) (x : Reg S ℂ) (B ν : ℝ) (hB : 0 ≤ B)
    (hrel : ‖(3 * B) • (goodF†) (Urel (GateODE.seedState seedV)) - x‖ ≤ 6 * ν * B) :
    ‖(3 * B) • (goodN†) (UN sN) - x‖ ≤ 3 * B * δ + 6 * ν * B := by
  have hc := native_decoded_close UN Urel hA
  have e : (3 * B) • ((goodN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
      (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A))†) (UN sN) - x =
      (3 * B) • ((goodN†) (UN sN) - (goodF†) (Urel (GateODE.seedState seedV))) +
        ((3 * B) • (goodF†) (Urel (GateODE.seedState seedV)) - x) := by
    rw [smul_sub]
    abel
  rw [e]
  calc _ ≤ ‖(3 * B) • (((goodN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
        (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A))†) (UN sN) -
        (goodF†) (Urel (GateODE.seedState seedV)))‖ +
        ‖(3 * B) • (goodF†) (Urel (GateODE.seedState seedV)) - x‖ := norm_add_le _ _
    _ ≤ 3 * B * δ + 6 * ν * B := by
        gcongr
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left hc (by positivity)

/-- **The native protocol from the released certificate of a lifted preparation**: for every
native ODE register with a large enough pool and every valid native preparation within `δ` of the
lifted released preparation `Urel`, which never touches the native flag and pool, if the decoded
vector of `Urel` meets the released error `6 ν B` against an intermediate target `y`,
`0 < B ≤ g ‖y‖`, `(3δ + 6ν) g ≤ ρ ≤ 1/4`, and the direction of `y` is within `η` of that of `x`,
then `nprotocol prepN g` has the guarantees `WOutcome … (2ρ + η)` against `x`. -/
theorem woutcome_lifted
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
      Fintype.card S ≤ nP + 1)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j))
    (hvalid : ∀ i ∈ prepN, i.Valid) (hP : Pres2 (ZeroOn reflWire) (nrun prim prepN))
    (Urel : Reg (AW a m r K k l f) (Reg S ℂ) →L[ℂ] Reg (AW a m r K k l f) (Reg S ℂ))
    {δ : ℝ} (hA : ApproxOn CleanX (nrun prim prepN) (liftB (conj Urel)) δ)
    (y x : Reg S ℂ) (B g ν ρ η : ℝ) (hy : y ≠ 0) (hx : x ≠ 0) (hg : 1 ≤ g) (hB : 0 < B)
    (hBudget : B ≤ g * ‖y‖)
    (hrel : ‖(3 * B) • (goodF†) (Urel (GateODE.seedState seedV)) - y‖ ≤ 6 * ν * B)
    (hδν : 0 ≤ 3 * δ + 6 * ν) (hρ : (3 * δ + 6 * ν) * g ≤ ρ) (hρ4 : ρ ≤ 1 / 4)
    (hdirY : ‖unitDirection y - unitDirection x‖ ≤ η) :
    WOutcome prepN g (2 * ρ + η) hg prim x := by
  have hvec := native_vector_error_le (nrun prim prepN) Urel hA y B ν hB.le hrel
  have hvec' : ‖(3 * B) • (goodN†) (nrun prim prepN sN) - y‖ ≤ ρ * ‖y‖ := by
    refine hvec.trans ?_
    have h1 : 3 * B * δ + 6 * ν * B = (3 * δ + 6 * ν) * B := by ring
    have h2 : (3 * δ + 6 * ν) * B ≤ (3 * δ + 6 * ν) * (g * ‖y‖) :=
      mul_le_mul_of_nonneg_left hBudget hδν
    have h3 : (3 * δ + 6 * ν) * (g * ‖y‖) ≤ ρ * ‖y‖ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hρ (norm_nonneg _)
    linarith
  have hscale : 3 * B ≤ 3 * g * ‖y‖ := by linarith
  exact woutcome_of_vec hnP prepN prim hprim hvalid hP y x (3 * B) g ρ η hy hx hg (by linarith) hρ4
    hscale hvec' hdirY

/-- **The native protocol for a direct source assembly**: for every native ODE register with a large
enough pool and every valid native preparation within `δ ≥ 0` of a lifted released preparation whose
decoded vector is exactly `y / B`, which never touches the native flag and pool, if
`0 < B ≤ g ‖y‖`, `δ g ≤ ρ ≤ 1/4` and the direction of `y` is within `η` of that of `x`, then
`nprotocol prepN g` has the guarantees `WOutcome … (2ρ + η)` against `x`. -/
theorem woutcome_direct
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
      Fintype.card S ≤ nP + 1)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j))
    (hvalid : ∀ i ∈ prepN, i.Valid) (hP : Pres2 (ZeroOn reflWire) (nrun prim prepN))
    (Urel : Reg (AW a m r K k l f) (Reg S ℂ) →L[ℂ] Reg (AW a m r K k l f) (Reg S ℂ))
    {δ : ℝ} (hA : ApproxOn CleanX (nrun prim prepN) (liftB (conj Urel)) δ)
    (y x : Reg S ℂ) (B g ρ η : ℝ) (hy : y ≠ 0) (hx : x ≠ 0) (hg : 1 ≤ g) (hB : 0 < B)
    (hBudget : B ≤ g * ‖y‖) (hrel : B • (goodF†) (Urel (GateODE.seedState seedV)) = y)
    (hδ : 0 ≤ δ) (hρ : δ * g ≤ ρ) (hρ4 : ρ ≤ 1 / 4)
    (hdirY : ‖unitDirection y - unitDirection x‖ ≤ η) :
    WOutcome prepN g (2 * ρ + η) hg prim x := by
  have hvec := ZeroTimeGateODE.vector_error_direct (nrun prim prepN) Urel hA y B hB.le hrel
  have hvec' : ‖B • (goodN†) (nrun prim prepN sN) - y‖ ≤ ρ * ‖y‖ := by
    refine hvec.trans ?_
    have h2 : B * δ ≤ (g * ‖y‖) * δ := mul_le_mul_of_nonneg_right hBudget hδ
    have h3 : (g * ‖y‖) * δ ≤ ρ * ‖y‖ := by
      have e : (g * ‖y‖) * δ = (δ * g) * ‖y‖ := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hρ (norm_nonneg _)
    linarith
  have hscale : B ≤ 3 * g * ‖y‖ := by
    have : 0 ≤ g * ‖y‖ := mul_nonneg (by linarith) (norm_nonneg _)
    linarith
  exact woutcome_of_vec hnP prepN prim hprim hvalid hP y x B g ρ η hy hx hg hB hρ4 hscale hvec'
    hdirY

end Native

end

end SparseHamiltonian.SourceAccuracyODE
