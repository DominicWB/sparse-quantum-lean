import GateEfficientSynthesisTrials.Approx
import GateEfficientNative.ODE.Protocol

/-!
# The certificate of the synthesised preparation and the per-trial claim

The released analysis certifies the decoded vector of the released preparation `Urel`:
`‖3B d - x‖ ≤ 6νB` with `ν = ε/(10000 g)`. The native preparation is within `δ` of the lifted
released preparation, and the synthesised preparation within `η + δ` (`synthPrep_approx`).
With `η + δ ≤ 4ν/3` the decoded vector of the actual (synthesised) preparation unitary on the
trial register satisfies `‖3B dS - x‖ ≤ 10νB` (`vector_error10`), equation
`ode:eq:gate-vector-error` for the implemented circuit. The released output certificate holds
verbatim with `10νB` in place of `9νB` (the relative error is still at most `ε/1000`):
`output_certificate10`, and the released randomized amplification theorem applies to the actual
preparation (`trial_bounds_of_vec10`).

For every native ODE register and every preparation that is unitary, keeps the flag and the pool
of the zero tests clean and has the vector error `10νB`, the released native trials are exactly
the actual Grover trials of the preparation unitary (the released `trialN_seed`), so every
successful trial has the data direction of that unitary up to a global phase, within `ε/500` of
the normalised target, and the mean success is at least `1/4` (`native_trial_bounds10`); the
protocol has the guarantees `GateNative.NOutcome` (`noutcome10`).

The trials of the synthesised protocol are the released native trials on the trial register,
with the synthesised preparation, its exact adjoint and the exact zero tests, so the protocol
`nprotocol (synthPrep hS η prepN) g` has the guarantees `NOutcome` (`synth_noutcome`): unitary
trials, mean success at least `1/4`, every successful trial within `ε/500` of `x/‖x‖` up to a
global phase, success probability at least `175/256 ≥ 2/3`, and a conditional output within
trace distance `ε`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSynthTrials

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateSynth
open GateODE (AW goodF)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-! ### The output certificate with the vector error `10νB` -/

section Output

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The released output certificate with vector error `10νB`** instead of `6νB`: the
direction error is still at most `ε/500` and the successful amplitude lies in
`[1/(4g), 1/2)`. -/
theorem output_certificate10 (x y : E) (B g ε : ℝ)
    (hx : x ≠ 0) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hNorm : ‖x‖ ≤ B) (hBudget : B ≤ g * ‖x‖)
    (hError : ‖y - x‖ ≤ 10 * ImprovedODEQueryBudget.precision g ε * B) :
    y ≠ 0 ∧ ‖unitDirection y‖ = 1 ∧
      ‖unitDirection y - unitDirection x‖ ≤ ε / 500 ∧
      1 / (4 * g) ≤ ‖y‖ / (3 * B) ∧ ‖y‖ / (3 * B) < 1 / 2 := by
  have hg0 : 0 < g := by linarith
  have hB : 0 < B := (norm_pos_iff.mpr hx).trans_le hNorm
  have hν : ImprovedODEQueryBudget.precision g ε = ε / (10000 * g) := rfl
  have hRel : ‖y - x‖ ≤ (ε / 1000) * ‖x‖ := by
    refine hError.trans ?_
    calc 10 * ImprovedODEQueryBudget.precision g ε * B
        ≤ 10 * ImprovedODEQueryBudget.precision g ε * (g * ‖x‖) :=
          mul_le_mul_of_nonneg_left hBudget (by rw [hν]; positivity)
      _ = (ε / 1000) * ‖x‖ := by
          rw [hν]
          field_simp
          ring
  have hSmall : ε / 1000 < 1 := by linarith
  have hDirection := ODEStateNormalization.relative_error x y (ε / 1000) hx hSmall hRel
  have hLower := ODEStateNormalization.extraction_amplitude_lower_of_budget_le x y B g 3
    (ε / 1000) hB hg0 (by norm_num) hSmall.le hBudget hRel
  have hνBound : ImprovedODEQueryBudget.precision g ε ≤ 1 / 10000 := by
    rw [hν]
    apply (div_le_iff₀ (by positivity : 0 < 10000 * g)).2
    nlinarith
  have hUpper : ‖y‖ ≤ (1 + 10 * ImprovedODEQueryBudget.precision g ε) * B := by
    calc
      _ ≤ ‖y - x‖ + ‖x‖ := by
        simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub y x 0
      _ ≤ 10 * ImprovedODEQueryBudget.precision g ε * B + B := add_le_add hError hNorm
      _ = _ := by ring
  refine ⟨hDirection.1, ODEStateNormalization.unitDirection_norm y hDirection.1, ?_, ?_, ?_⟩
  · convert hDirection.2 using 1; ring
  · calc
      1 / (4 * g) = (3 / 4 : ℝ) / (3 * g) := by
        field_simp
      _ ≤ (1 - ε / 1000) / (3 * g) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      _ ≤ ‖y‖ / (3 * B) := hLower
  · apply (div_lt_iff₀ (by positivity : 0 < 3 * B)).2
    have hScale := mul_le_mul_of_nonneg_right hνBound hB.le
    nlinarith

/-- **The randomized amplification bounds for a decoded vector with the error `10νB`**, for
any isometric decoding `G`, unitary preparation `U` and unit seed `s`: the public cutoff
`chosenIterations g ≤ 5g` gives mean success at least `1/4`, and every nonzero decoded trial is
within `ε/500` of `x/‖x‖` up to a global phase. -/
theorem trial_bounds_of_vec10 {K P : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    (G : P →L[ℂ] K) (hG : G† ∘L G = 1) (U : K →L[ℂ] K) (hU : IsUnitary U) (s : K)
    (hs : ‖s‖ = 1) (x : P) (B g ε : ℝ) (hx : x ≠ 0) (hg : 1 ≤ g) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2) (hNorm : ‖x‖ ≤ B) (hBudget : B ≤ g * ‖x‖)
    (hvec : ‖(3 * B) • (G†) (U s) - x‖ ≤ 10 * ImprovedODEQueryBudget.precision g ε * B) :
    0 < ODEGroverAverage.chosenIterations g ∧
    (ODEGroverAverage.chosenIterations g : ℝ) ≤ 5 * g ∧
    (1 : ℝ) / 4 ≤ (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations g),
      ‖ODEHeraldedSuccess.successProjector G (ODEGroverActual.trial G U s j)‖ ^ 2) /
        (ODEGroverAverage.chosenIterations g : ℝ) ∧
    ∀ j : ℕ, (G†) (ODEGroverActual.trial G U s j) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection ((G†) (ODEGroverActual.trial G U s j)) - unitDirection x‖ ≤
          ε / 500 := by
  have hB : 0 < B := (norm_pos_iff.mpr hx).trans_le hNorm
  have h3B : 0 < 3 * B := by positivity
  obtain ⟨_, _, hdir, hlow, hup⟩ :=
    output_certificate10 x _ B g ε hx hg hε hεHalf hNorm hBudget hvec
  have hscale : ‖(3 * B) • (G†) (U s)‖ / (3 * B) = ‖(G†) (U s)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos h3B]
    exact mul_div_cancel_left₀ _ h3B.ne'
  rw [hscale] at hlow hup
  rw [ODEHeraldedSuccess.unitDirection_pos_smul (3 * B) h3B] at hdir
  have hamp : ODEGroverActual.amplitude G U s = ‖(G†) (U s)‖ := by
    rw [ODEGroverActual.amplitude, ← ODEHeraldedSuccess.successfulComponent,
      ODEHeraldedSuccess.successfulComponent_norm _ hG]
    rfl
  exact ODEGroverActual.randomized_certificate G hG U hU s hs g hg (by rw [hamp]; exact hlow)
    (by rw [hamp]; exact hup.le) x (ε / 500) hdir

end Output

/-! ### The synthesised preparation -/

section Synth

variable {a m r K k l f : ℕ} {S Zs Z Y J X : Type*} {nP bT bP A : ℕ}
variable [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {len : ℝ → ℕ}

omit [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X] in
/-- **The vector error of a preparation within `δ ≤ 4ν/3`**: `‖3B dN - x‖ ≤ 10νB`. -/
theorem vector_error10
    (UN : Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ →L[ℂ]
      Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ)
    (Urel : Reg (AW a m r K k l f) (Reg S ℂ) →L[ℂ] Reg (AW a m r K k l f) (Reg S ℂ))
    {δ : ℝ} (hA : ApproxOn CleanX UN (liftB (conj Urel)) δ) (x : Reg S ℂ) (B ν : ℝ)
    (hB : 0 ≤ B) (hrel : ‖(3 * B) • (goodF†) (Urel (GateODE.seedState seedV)) - x‖ ≤ 6 * ν * B)
    (hδ : δ ≤ 4 / 3 * ν) :
    ‖(3 * B) • (goodN†) (UN sN) - x‖ ≤ 10 * ν * B := by
  have hc := native_decoded_close UN Urel hA
  have e : (3 * B) • ((goodN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
      (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A))†) (UN sN) - x =
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
    _ ≤ 3 * B * (4 / 3 * ν) + 6 * ν * B := by gcongr
    _ = 10 * ν * B := by ring

variable (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)

omit [Fintype X] [DecidableEq X] in
/-- **Mean success and the per-trial direction error with the vector error `10νB`.** For every
native ODE register and every preparation `P` on it that is unitary, never touches the flag and
the pool of the zero tests, and is within `δ ≤ 4ν/3` of the lifted released preparation whose
decoded vector meets the released vector error `6νB`, the released native trials
`trialN P j` (the actual preparation, its literal inverse, the exact zero tests) have mean
success at least `1/4` over the public cutoff `chosenIterations g ≤ 5g`, and every nonzero
decoded trial is within `ε/500` of `x/‖x‖` up to a global phase. -/
theorem native_trial_bounds10
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
      Fintype.card S ≤ nP + 1)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hU : IsUnitary (nrun prim prepN)) (hP : Pres2 (ZeroOn reflWire) (nrun prim prepN))
    (Urel : Reg (AW a m r K k l f) (Reg S ℂ) →L[ℂ] Reg (AW a m r K k l f) (Reg S ℂ))
    {δ : ℝ} (hA : ApproxOn CleanX (nrun prim prepN) (liftB (conj Urel)) δ)
    (x : Reg S ℂ) (B g ε : ℝ) (hx : x ≠ 0) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hNorm : ‖x‖ ≤ B) (hBudget : B ≤ g * ‖x‖)
    (hrel : ‖(3 * B) • (goodF†) (Urel (GateODE.seedState seedV)) - x‖ ≤
      6 * ImprovedODEQueryBudget.precision g ε * B)
    (hδ : δ ≤ 4 / 3 * ImprovedODEQueryBudget.precision g ε) :
    0 < ODEGroverAverage.chosenIterations g ∧
    (ODEGroverAverage.chosenIterations g : ℝ) ≤ 5 * g ∧
    (1 : ℝ) / 4 ≤ (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations g),
      ‖ODEHeraldedSuccess.successProjector goodN (nrun prim (trialN prepN j) sN)‖ ^ 2) /
        (ODEGroverAverage.chosenIterations g : ℝ) ∧
    ∀ j : ℕ, (goodN†) (nrun prim (trialN prepN j) sN) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection ((goodN†) (nrun prim (trialN prepN j) sN)) - unitDirection x‖ ≤
          ε / 500 := by
  have hvec := vector_error10 (nrun prim prepN) Urel hA x B _
    ((norm_pos_iff.mpr hx).trans_le hNorm).le hrel hδ
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
  exact trial_bounds_of_vec10 G hGi U hU s hs x B g ε hx hg hε hεHalf hNorm hBudget hvec

omit [Fintype X] [DecidableEq X] in
/-- **The native protocol is correct with the vector error `10νB`**: under the hypotheses of
`native_trial_bounds10`, for valid instructions and unitary primitive oracles, the protocol
`nprotocol P g` has the guarantees `NOutcome`. -/
theorem noutcome10
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
      Fintype.card S ≤ nP + 1)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hprim : ∀ j, IsUnitary (prim j)) (hvalid : ∀ i ∈ prepN, i.Valid)
    (hP : Pres2 (ZeroOn reflWire) (nrun prim prepN))
    (Urel : Reg (AW a m r K k l f) (Reg S ℂ) →L[ℂ] Reg (AW a m r K k l f) (Reg S ℂ))
    {δ : ℝ} (hA : ApproxOn CleanX (nrun prim prepN) (liftB (conj Urel)) δ)
    (x : Reg S ℂ) (B g ε : ℝ) (hx : x ≠ 0) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hNorm : ‖x‖ ≤ B) (hBudget : B ≤ g * ‖x‖)
    (hrel : ‖(3 * B) • (goodF†) (Urel (GateODE.seedState seedV)) - x‖ ≤
      6 * ImprovedODEQueryBudget.precision g ε * B)
    (hδ : δ ≤ 4 / 3 * ImprovedODEQueryBudget.precision g ε) :
    NOutcome prepN g ε hg prim x := by
  obtain ⟨-, -, hmean, hdir⟩ := native_trial_bounds10 prim hnP prepN
    (nrun_isUnitary prim hprim _ hvalid) hP Urel hA x B g ε hx hg hε hεHalf hNorm hBudget hrel hδ
  exact noutcome_of_bounds prepN prim hprim hvalid x hx g ε hg hε hmean hdir

/-- **The synthesised protocol is correct, trial by trial.** Let the native preparation be
within `δ` of the lifted released preparation, whose decoded vector meets the released vector
error `6νB`, and let `η + δ ≤ 4ν/3`. Then the released native protocol
`nprotocol (synthPrep hS η prepN) g` on the trial register (the synthesised preparation, its
exact adjoint and the exact zero tests) has the guarantees `NOutcome`: unitary trials, mean
success at least `1/4`, every successful trial within `ε/500` of `x/‖x‖` up to a global phase,
success probability at least `175/256 ≥ 2/3`, and a conditional output density within trace
distance `ε` of `x/‖x‖`. -/
theorem synth_noutcome (hS : Synthesis 𝒢 X len) {η : ℝ} (hη : 0 < η)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ i ∈ prepN, i.Valid) (hprim : ∀ j, IsUnitary (prim j))
    (Urel : Reg (AW a m r K k l f) (Reg S ℂ) →L[ℂ] Reg (AW a m r K k l f) (Reg S ℂ))
    {δ : ℝ} (hδ : 0 ≤ δ) (hA : ApproxOn CleanX (nrun prim prepN) (liftB (conj Urel)) δ)
    (x : Reg S ℂ) (B g ε : ℝ) (hx : x ≠ 0) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hNorm : ‖x‖ ≤ B) (hBudget : B ≤ g * ‖x‖)
    (hrel : ‖(3 * B) • (goodF†) (Urel (GateODE.seedState seedV)) - x‖ ≤
      6 * ImprovedODEQueryBudget.precision g ε * B)
    (hηδ : η + δ ≤ 4 / 3 * ImprovedODEQueryBudget.precision g ε) :
    NOutcome (synthPrep hS η prepN) g ε hg prim x :=
  noutcome10 prim hnP_SWO (synthPrep hS η prepN) hprim (synthPrep_valid hS hη prepN hvalid)
    (synthPrep_pres hS η prepN prim) Urel
    (synthPrep_approx hS hη prepN hvalid prim hprim Urel hδ hA) x B g ε hx hg hε hεHalf hNorm
    hBudget hrel hηδ

end Synth

end

end SparseHamiltonian.GateSynthTrials
