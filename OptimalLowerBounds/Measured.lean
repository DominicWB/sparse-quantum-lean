import OptimalLowerBounds.Adaptive
import DeferredMeasurementLowerBounds.Corollaries.Hamiltonian
import DeferredMeasurementLowerBounds.Model.Embed

set_option synthInstance.maxHeartbeats 400000

/-!
# Proposition `hsl:prop:two-norm` and the denominator paragraph for measured algorithms

Proposition `hsl:prop:two-norm` states "The output need only satisfy the known-input system
trace-distance guarantee [eq. `hsl:eq:accuracy`], with physical time `t` replacing `τ` in the target
state, permitting mixed states but no postselection", and
Theorem `hsl:thm:main`, to which its proof reduces, covers measurements by deferral ("Purification
and deferred measurement include adaptive and randomised algorithms", proof of Lemma
`hsl:lem:precision`). This module states the lower bounds of `OptimalLowerBounds` for **measured
algorithms** (`DeferredMeasurementLowerBounds.Model.Measured`: oracle calls, forward or inverse;
input-independent instruments with finitely many outcomes in the middle of a run, followed by the
classically chosen continuation of the observed outcome; heralded output; rejection), on one
persistent workspace, with

* oracle labels admissible for the enlarged data (`Admissible`: native calls with spectators,
  controls, masks, inverses and coherent choices of the native query; input-independent unitaries;
  a workspace that carries a native call is a finite direct sum of copies of the native query
  space, hence finite-dimensional),
* a unit initial vector, success probability at least `2/3` on every input,
* conditional output `ε`-accurate in trace distance (`DensityAccurate`) for
  `e^{-itH_X}(ψ_in ⊗ u_m)`,

and the count `M.worstCost w`, the maximum over all transcripts (including those of probability
zero) of the weighted number of calls, inverse calls included.

**Proof.** Each measured algorithm is deferred (`DeferredMeasurementLowerBounds.Deferral`: one
record register per instrument, Halmos dilations, the `k`-th counted call of every branch
aligned into slot `k`); the record-selected calls of admissible labels are admissible
(`DeferredMeasurementLowerBounds.Access.admissible_selFamily`), the deferred protocol has the same
success mass, its output read through the lifted readout is as accurate, and it makes at most the
worst-case number of input-dependent calls (`deferred_admissible` in
`DeferredMeasurementLowerBounds.Corollaries`). Then the adaptive bounds of
`OptimalLowerBounds/Adaptive.lean` apply. No constant is lost.

* **`two_norm_main_max_measured`** (eq. `twonorml:eq:lower`, max form, admissible labels; the
  per-family bounds `time_two_measured`, `mixed_two_measured`, `precision_two_measured`);
  **`two_norm_main_max_measured_calls`** (the plain, inverse, controlled and controlled-inverse
  forms of the native primitives with spectators, each value form counted as one value call);
  **`two_norm_main_max_measured_common`** (the common oracle of the upper bounds,
  `CoherentQuerySchedule.oracle (physOracle D)`, value calls counted).
* **`main_max_measured_common`**: the lower half of Theorem `hs:thm:optimal`
  (eq. `hsl:eq:main`) for measured algorithms over the common oracle of the original families.
* **`denom_lower_measured`**, **`wrong_denominator_measured`**,
  **`wrong_denominator_measured_common`**: the denominator paragraph for measured algorithms.
* **Non-vacuity and `Θ`**: a common-form simulation is a measured algorithm meeting every
  hypothesis, with success probability one and worst-case value-call count at most its query
  bound (`measured_of_simulates`). Hence **`optimal_measured_theta`** (the released simulations of
  `hs:thm:optimal` on the original families meet every hypothesis of `main_max_measured_common`,
  and `c₀ S ≤ max(Q_T, Q_M, Q_P) ≤ 2·10¹² S` for them) and, on the aligned families
  (`measured_on_aligned`), **`two_norm_measured_theta`** (the same for
  `two_norm_main_max_measured_common` with `S'`); `denom_measured` for the counterexample
  family.
-/

namespace OptimalLowerBounds

noncomputable section
set_option autoImplicit false
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit SparseLowerBounds
open SparseLowerBounds.Hamiltonian SparseLowerBounds.Readout
open DeferredMeasurementLowerBounds.Model DeferredMeasurementLowerBounds.Deferral
open DeferredMeasurementLowerBounds.Access DeferredMeasurementLowerBounds.Readout
open DeferredMeasurementLowerBounds.Corollaries
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open AdaptiveHamiltonianLowerBound.Access (Admissible valueWeight)
open AdaptiveODELowerBound.Access (CallForm callFamily)
open scoped InnerProduct InnerProductSpace
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

variable {θ ε : ℝ} {s m : ℕ} {c t : ℝ}

/-! ### Proposition `hsl:prop:two-norm` for measured algorithms -/

section Families

variable {K E G L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **Enlarged time family, measured algorithms** (eq. `hsl:eq:timelower` at `s₀`, `θ`): every
measured algorithm over admissible labels of `timeTwo`, with a unit initial vector, success
probability at least `2/3` on every input and conditional output `ε`-accurate for
`e^{-itH_X}(ψ_in ⊗ u_m)` (`c m t = θ`), has worst-case cost at least `c_T √s₀ θ`. -/
theorem time_two_measured (h : HSRange θ s ε) (hm : 0 < m) (hc : c ≠ 0) (hθ : c * m * t = θ)
    (O : L → (Fin (timeN θ) → Fin (2 ^ hsMu s)) → K →L[ℂ] K) (w : L → ℕ)
    (hO : ∀ l, Admissible (timeTwo θ s h.s_ge m hm c hc) (O l) (w l))
    (M : Measured O E) (φ : K) (hφ : ‖φ‖ = 1)
    (e : E →L[ℂ] SysGarb (SearchIndex (timeN θ) (hsMu s) s × Fin m) G) (he : e† ∘L e = 1)
    (hsucc : ∀ j, 2 / 3 ≤ M.successMass j φ)
    (hacc : ∀ j, DensityAccurate e (M.conditionalDensity j φ)
      (evolve ((timeTwo θ s h.s_ge m hm c hc).matrix j) t
        (embedU m (searchInput (timeN θ) (hsMu s) s))) ε) :
    cT * Real.sqrt s * θ ≤ M.worstCost w := by
  classical
  have d := deferred_admissible (timeTwo θ s h.s_ge m hm c hc) O w hO M hφ e _ hacc
  exact (time_two_tree h hm hc hθ (selFamily O (nativeCounted O) (DRec M)) selWeight
    (admissible_selFamily _ hO (DRec M)) (deferredTree (nativeCounted O) ℂ M φ hφ)
    (liftReadout (DOut M) e) (liftReadout_isometry he) (fun j => (d j).2.1 ▸ hsucc j)
    (fun j => (d j).1)).trans
    (worstCost_deferredTree_le (fun l hl => one_le_of_nativeCounted _ hO l hl) M hφ)

/-- **Enlarged mixed family, measured algorithms** (eq. `hsl:eq:mixrbound` at `s₀`, `θ`): for
`L ≥ 64θ` and `s₀ ≥ 64n/θ`, worst-case cost at least `(log 2/(384√2)) √(s₀ θ r_μ)`. -/
theorem mixed_two_measured (h : HSRange θ s ε) (hL : 64 * θ ≤ hsL ε)
    (hs : 64 * (precN θ ε : ℝ) / θ ≤ s) (hm : 0 < m) (hc : c ≠ 0) (hθ : c * m * t = θ)
    (O : L → (Fin (precN θ ε) → Fin (2 ^ hsMu s)) → K →L[ℂ] K) (w : L → ℕ)
    (hO : ∀ l, Admissible (mixedTwo θ ε s h.s_ge m hm c hc) (O l) (w l))
    (M : Measured O E) (φ : K) (hφ : ‖φ‖ = 1)
    (e : E →L[ℂ] SysGarb (SearchIndex (precN θ ε) (hsMu s) s × Fin m) G) (he : e† ∘L e = 1)
    (hsucc : ∀ j, 2 / 3 ≤ M.successMass j φ)
    (hacc : ∀ j, DensityAccurate e (M.conditionalDensity j φ)
      (evolve ((mixedTwo θ ε s h.s_ge m hm c hc).matrix j) t
        (embedU m (searchInput (precN θ ε) (hsMu s) s))) ε) :
    Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * θ * hsR θ ε) ≤ M.worstCost w := by
  classical
  have d := deferred_admissible (mixedTwo θ ε s h.s_ge m hm c hc) O w hO M hφ e _ hacc
  exact (mixed_two_tree h hL hs hm hc hθ (selFamily O (nativeCounted O) (DRec M)) selWeight
    (admissible_selFamily _ hO (DRec M)) (deferredTree (nativeCounted O) ℂ M φ hφ)
    (liftReadout (DOut M) e) (liftReadout_isometry he) (fun j => (d j).2.1 ▸ hsucc j)
    (fun j => (d j).1)).trans
    (worstCost_deferredTree_le (fun l hl => one_le_of_nativeCounted _ hO l hl) M hφ)

/-- **Enlarged precision family, measured algorithms** (eqs. `hsl:eq:rbound`,
`hsl:eq:failedmix` at `s₀`, `θ`): for `L ≥ 64θ`, worst-case cost at least `r_μ/32`, and at least
`√(s₀ θ r_μ)/(64√2)` when `s₀ < 64n/θ`. -/
theorem precision_two_measured (h : HSRange θ s ε) (hL : 64 * θ ≤ hsL ε) (hm : 0 < m)
    (hc : c ≠ 0) (hθ : c * m * t = θ)
    (O : L → (Fin (precN θ ε) → Bool) → K →L[ℂ] K) (w : L → ℕ)
    (hO : ∀ l, Admissible (precisionTwo θ ε s h.s_ge m hm c hc) (O l) (w l))
    (M : Measured O E) (φ : K) (hφ : ‖φ‖ = 1)
    (e : E →L[ℂ] SysGarb (ScalarIndex (precN θ ε) s × Fin m) G) (he : e† ∘L e = 1)
    (hsucc : ∀ x, 2 / 3 ≤ M.successMass x φ)
    (hacc : ∀ x, DensityAccurate e (M.conditionalDensity x φ)
      (evolve ((precisionTwo θ ε s h.s_ge m hm c hc).matrix x) t
        (embedU m (scalarInput (precN θ ε) s))) ε) :
    hsR θ ε / 32 ≤ M.worstCost w ∧
      ((s : ℝ) < 64 * precN θ ε / θ →
        Real.sqrt (s * θ * hsR θ ε) / (64 * Real.sqrt 2) ≤ M.worstCost w) := by
  classical
  have d := deferred_admissible (precisionTwo θ ε s h.s_ge m hm c hc) O w hO M hφ e _ hacc
  have hb := precision_two_tree h hL hm hc hθ (selFamily O (nativeCounted O) (DRec M)) selWeight
    (admissible_selFamily _ hO (DRec M)) (deferredTree (nativeCounted O) ℂ M φ hφ)
    (liftReadout (DOut M) e) (liftReadout_isometry he) (fun x => (d x).2.1 ▸ hsucc x)
    (fun x => (d x).1)
  have hw := worstCost_deferredTree_le (fun l hl => one_le_of_nativeCounted _ hO l hl) M hφ
  exact ⟨hb.1.trans hw, fun hs' => (hb.2 hs').trans hw⟩

end Families

/-- **Proposition `hsl:prop:two-norm` for measured algorithms, max form** (eq.
`twonorml:eq:lower`): for any three measured algorithms (measurements inside a run with classical
continuations, one persistent workspace) over admissible labels of the enlarged time, mixed and
precision families respectively, each with a unit initial vector, success probability at least
`2/3` on every input and conditional output `ε`-accurate in trace distance for
`e^{-itH_X}(ψ_in ⊗ u_m)` (`c m t = θ`), with `s = s₀ m`, `η = |c|√m`, `μ = |c|` and
`r_μ = hsR θ ε`: `c₀ (√s η|t| + √(sμ|t| r_μ) + r_μ) ≤ max(Q_T, Q_M, Q_P)`, where `Q` is the
worst-case weighted number of calls over all transcripts and `c₀ = log 2/(4096π)`. -/
theorem two_norm_main_max_measured (h : HSRange θ s ε) (hm : 0 < m) (hc : c ≠ 0)
    (hθ : c * m * t = θ)
    {KT ET GT LT KM EM GM LM KP EP GP LP : Type*}
    [NormedAddCommGroup KT] [InnerProductSpace ℂ KT] [CompleteSpace KT]
    [NormedAddCommGroup ET] [InnerProductSpace ℂ ET] [CompleteSpace ET] [FiniteDimensional ℂ ET]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup KM] [InnerProductSpace ℂ KM] [CompleteSpace KM]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup KP] [InnerProductSpace ℂ KP] [CompleteSpace KP]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (OT : LT → (Fin (timeN θ) → Fin (2 ^ hsMu s)) → KT →L[ℂ] KT) (wT : LT → ℕ)
    (hOT : ∀ l, Admissible (timeTwo θ s h.s_ge m hm c hc) (OT l) (wT l))
    (MT : Measured OT ET) (φT : KT) (hφT : ‖φT‖ = 1)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN θ) (hsMu s) s × Fin m) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ MT.successMass j φT)
    (haccT : ∀ j, DensityAccurate eT (MT.conditionalDensity j φT)
      (evolve ((timeTwo θ s h.s_ge m hm c hc).matrix j) t
        (embedU m (searchInput (timeN θ) (hsMu s) s))) ε)
    (OM : LM → (Fin (precN θ ε) → Fin (2 ^ hsMu s)) → KM →L[ℂ] KM) (wM : LM → ℕ)
    (hOM : ∀ l, Admissible (mixedTwo θ ε s h.s_ge m hm c hc) (OM l) (wM l))
    (MM : Measured OM EM) (φM : KM) (hφM : ‖φM‖ = 1)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN θ ε) (hsMu s) s × Fin m) GM)
    (heM : eM† ∘L eM = 1) (hsuccM : ∀ j, 2 / 3 ≤ MM.successMass j φM)
    (haccM : ∀ j, DensityAccurate eM (MM.conditionalDensity j φM)
      (evolve ((mixedTwo θ ε s h.s_ge m hm c hc).matrix j) t
        (embedU m (searchInput (precN θ ε) (hsMu s) s))) ε)
    (OP : LP → (Fin (precN θ ε) → Bool) → KP →L[ℂ] KP) (wP : LP → ℕ)
    (hOP : ∀ l, Admissible (precisionTwo θ ε s h.s_ge m hm c hc) (OP l) (wP l))
    (MP : Measured OP EP) (φP : KP) (hφP : ‖φP‖ = 1)
    (eP : EP →L[ℂ] SysGarb (ScalarIndex (precN θ ε) s × Fin m) GP) (heP : eP† ∘L eP = 1)
    (hsuccP : ∀ x, 2 / 3 ≤ MP.successMass x φP)
    (haccP : ∀ x, DensityAccurate eP (MP.conditionalDensity x φP)
      (evolve ((precisionTwo θ ε s h.s_ge m hm c hc).matrix x) t
        (embedU m (scalarInput (precN θ ε) s))) ε) :
    c0 * (Real.sqrt ((s * m : ℕ) : ℝ) * (|c| * Real.sqrt m) * |t| +
        Real.sqrt ((s * m : ℕ) * |c| * |t| * hsR θ ε) + hsR θ ε) ≤
      max (MT.worstCost wT : ℝ) (max (MM.worstCost wM : ℝ) (MP.worstCost wP)) := by
  rw [two_shape_eq hθ h.tau_pos]
  exact assembly h (time_two_measured h hm hc hθ OT wT hOT MT φT hφT eT heT hsuccT haccT)
    (fun hL => precision_two_measured h hL hm hc hθ OP wP hOP MP φP hφP eP heP hsuccP haccP)
    (fun hL hs => mixed_two_measured h hL hs hm hc hθ OM wM hOM MM φM hφM eM heM hsuccM haccM)

/-- **Proposition `hsl:prop:two-norm` for measured algorithms over the call forms of the native
primitives** (max form): as `two_norm_main_max_measured`, with oracle calls the plain, inverse,
controlled and controlled-inverse forms (`AdaptiveODELowerBound.Access.callFamily`, on a control
qubit) of the native primitives of the enlarged families acting on untouched spectator registers
`ℂ^Ω`, every value form counted as one value call and location forms free. -/
theorem two_norm_main_max_measured_calls (h : HSRange θ s ε) (hm : 0 < m) (hc : c ≠ 0)
    (hθ : c * m * t = θ) (ΩT ΩM ΩP : Type) [Fintype ΩT] [Fintype ΩM] [Fintype ΩP]
    {ET GT EM GM EP GP : Type*}
    [NormedAddCommGroup ET] [InnerProductSpace ℂ ET] [CompleteSpace ET] [FiniteDimensional ℂ ET]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AT : Measured (callFamily (specOracles ΩT (timeTwo θ s h.s_ge m hm c hc))) ET)
    (φT : Joint Bool (Joint ΩT (SearchTwoSpace (timeN θ) (hsMu s) s (timeC θ) θ m)))
    (hφT : ‖φT‖ = 1)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN θ) (hsMu s) s × Fin m) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ AT.successMass j φT)
    (haccT : ∀ j, DensityAccurate eT (AT.conditionalDensity j φT)
      (evolve ((timeTwo θ s h.s_ge m hm c hc).matrix j) t
        (embedU m (searchInput (timeN θ) (hsMu s) s))) ε)
    (AM : Measured (callFamily (specOracles ΩM (mixedTwo θ ε s h.s_ge m hm c hc))) EM)
    (φM : Joint Bool (Joint ΩM (SearchTwoSpace (precN θ ε) (hsMu s) s 1 θ m)))
    (hφM : ‖φM‖ = 1)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN θ ε) (hsMu s) s × Fin m) GM)
    (heM : eM† ∘L eM = 1) (hsuccM : ∀ j, 2 / 3 ≤ AM.successMass j φM)
    (haccM : ∀ j, DensityAccurate eM (AM.conditionalDensity j φM)
      (evolve ((mixedTwo θ ε s h.s_ge m hm c hc).matrix j) t
        (embedU m (searchInput (precN θ ε) (hsMu s) s))) ε)
    (AP : Measured (callFamily (specOracles ΩP (precisionTwo θ ε s h.s_ge m hm c hc))) EP)
    (φP : Joint Bool (Joint ΩP (ScalarTwoSpace (precN θ ε) s θ m))) (hφP : ‖φP‖ = 1)
    (eP : EP →L[ℂ] SysGarb (ScalarIndex (precN θ ε) s × Fin m) GP) (heP : eP† ∘L eP = 1)
    (hsuccP : ∀ x, 2 / 3 ≤ AP.successMass x φP)
    (haccP : ∀ x, DensityAccurate eP (AP.conditionalDensity x φP)
      (evolve ((precisionTwo θ ε s h.s_ge m hm c hc).matrix x) t
        (embedU m (scalarInput (precN θ ε) s))) ε) :
    c0 * (Real.sqrt ((s * m : ℕ) : ℝ) * (|c| * Real.sqrt m) * |t| +
        Real.sqrt ((s * m : ℕ) * |c| * |t| * hsR θ ε) + hsR θ ε) ≤
      max (AT.worstCost (fun q => valueWeight q.1) : ℝ)
        (max (AM.worstCost (fun q => valueWeight q.1) : ℝ)
          (AP.worstCost (fun q => valueWeight q.1))) := by
  obtain ⟨hIT, hIM, hIP⟩ := two_instances h hm hc
  exact two_norm_main_max_measured h hm hc hθ _ (fun q => valueWeight q.1)
    (AdaptiveODELowerBound.Access.admissible_callFamily_spec ΩT _
      (fun x x' => (hIT.locators_const x x').2.2.1) (fun x x' => (hIT.locators_const x x').2.2.2))
    AT φT hφT eT heT hsuccT haccT _ (fun q => valueWeight q.1)
    (AdaptiveODELowerBound.Access.admissible_callFamily_spec ΩM _
      (fun x x' => (hIM.locators_const x x').2.2.1) (fun x x' => (hIM.locators_const x x').2.2.2))
    AM φM hφM eM heM hsuccM haccM _ (fun q => valueWeight q.1)
    (AdaptiveODELowerBound.Access.admissible_callFamily_spec ΩP _
      (fun x x' => (hIP.locators_const x x').2.2.1) (fun x x' => (hIP.locators_const x x').2.2.2))
    AP φP hφP eP heP hsuccP haccP

/-- **Proposition `hsl:prop:two-norm` for measured algorithms over the common oracle of the upper
bounds** (max form): as `two_norm_main_max_measured`, with oracle calls (forward or inverse) of
the common family `CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle D)` of
the enlarged families — the query model of `NativeSignedFactor.Simulates`, in which Theorem
`hs:thm:two-norm` is stated — and `Q` the worst-case number of value calls. -/
theorem two_norm_main_max_measured_common (h : HSRange θ s ε) (hm : 0 < m) (hc : c ≠ 0)
    (hθ : c * m * t = θ) (ιT ιM ιP : Type) [Fintype ιT] [Fintype ιM] [Fintype ιP]
    {ET GT EM GM EP GP : Type*}
    [NormedAddCommGroup ET] [InnerProductSpace ℂ ET] [CompleteSpace ET] [FiniteDimensional ℂ ET]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AT : Measured (CoherentQuerySchedule.oracle (ι := ιT)
      (NativeSignedFactor.physOracle (timeTwo θ s h.s_ge m hm c hc))) ET)
    (φT : CommonSpace ιT (SearchIndex (timeN θ) (hsMu s) s × Fin m)
      (Word (searchBits (timeN θ) (hsMu s) s (timeC θ) θ)))
    (hφT : ‖φT‖ = 1)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN θ) (hsMu s) s × Fin m) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ AT.successMass j φT)
    (haccT : ∀ j, DensityAccurate eT (AT.conditionalDensity j φT)
      (evolve ((timeTwo θ s h.s_ge m hm c hc).matrix j) t
        (embedU m (searchInput (timeN θ) (hsMu s) s))) ε)
    (AM : Measured (CoherentQuerySchedule.oracle (ι := ιM)
      (NativeSignedFactor.physOracle (mixedTwo θ ε s h.s_ge m hm c hc))) EM)
    (φM : CommonSpace ιM (SearchIndex (precN θ ε) (hsMu s) s × Fin m)
      (Word (searchBits (precN θ ε) (hsMu s) s 1 θ)))
    (hφM : ‖φM‖ = 1)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN θ ε) (hsMu s) s × Fin m) GM)
    (heM : eM† ∘L eM = 1) (hsuccM : ∀ j, 2 / 3 ≤ AM.successMass j φM)
    (haccM : ∀ j, DensityAccurate eM (AM.conditionalDensity j φM)
      (evolve ((mixedTwo θ ε s h.s_ge m hm c hc).matrix j) t
        (embedU m (searchInput (precN θ ε) (hsMu s) s))) ε)
    (AP : Measured (CoherentQuerySchedule.oracle (ι := ιP)
      (NativeSignedFactor.physOracle (precisionTwo θ ε s h.s_ge m hm c hc))) EP)
    (φP : CommonSpace ιP (ScalarIndex (precN θ ε) s × Fin m) (Word (scalarBits (precN θ ε) s θ)))
    (hφP : ‖φP‖ = 1)
    (eP : EP →L[ℂ] SysGarb (ScalarIndex (precN θ ε) s × Fin m) GP) (heP : eP† ∘L eP = 1)
    (hsuccP : ∀ x, 2 / 3 ≤ AP.successMass x φP)
    (haccP : ∀ x, DensityAccurate eP (AP.conditionalDensity x φP)
      (evolve ((precisionTwo θ ε s h.s_ge m hm c hc).matrix x) t
        (embedU m (scalarInput (precN θ ε) s))) ε) :
    c0 * (Real.sqrt ((s * m : ℕ) : ℝ) * (|c| * Real.sqrt m) * |t| +
        Real.sqrt ((s * m : ℕ) * |c| * |t| * hsR θ ε) + hsR θ ε) ≤
      max (AT.worstCost valueWeight : ℝ)
        (max (AM.worstCost valueWeight : ℝ) (AP.worstCost valueWeight)) := by
  obtain ⟨hIT, hIM, hIP⟩ := two_instances h hm hc
  exact two_norm_main_max_measured h hm hc hθ _ valueWeight
    (admissible_common _ (fun x x' => (hIT.locators_const x x').2.2.1)
      (fun x x' => (hIT.locators_const x x').2.2.2) ιT)
    AT φT hφT eT heT hsuccT haccT _ valueWeight
    (admissible_common _ (fun x x' => (hIM.locators_const x x').2.2.1)
      (fun x x' => (hIM.locators_const x x').2.2.2) ιM)
    AM φM hφM eM heM hsuccM haccM _ valueWeight
    (admissible_common _ (fun x x' => (hIP.locators_const x x').2.2.1)
      (fun x x' => (hIP.locators_const x x').2.2.2) ιP)
    AP φP hφP eP heP hsuccP haccP

/-! ### Theorem `hs:thm:optimal`, lower half, for measured algorithms over the common oracle -/

/-- **The lower half of Theorem `hs:thm:optimal` for measured algorithms in the common query
model** (eq. `hsl:eq:main`, max form): for any three measured algorithms over the common oracle
`CoherentQuerySchedule.oracle (physOracle D)` of the time, mixed and precision families of
`hsl:thm:main` (the query model of `NativeSignedFactor.Simulates`), each with a unit initial
vector, success probability at least `2/3` on every input and conditional output `ε`-accurate in
trace distance for `e^{-iτH_x} ψ_in`, `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, `Q` the
worst-case number of value calls over all transcripts. -/
theorem main_max_measured_common {τ : ℝ} (h : HSRange τ s ε) (ιT ιM ιP : Type) [Fintype ιT]
    [Fintype ιM] [Fintype ιP] {ET GT EM GM EP GP : Type*}
    [NormedAddCommGroup ET] [InnerProductSpace ℂ ET] [CompleteSpace ET] [FiniteDimensional ℂ ET]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AT : Measured (CoherentQuerySchedule.oracle (ι := ιT)
      (NativeSignedFactor.physOracle (timeData τ s h.s_ge))) ET)
    (φT : CommonSpace ιT (SearchIndex (timeN τ) (hsMu s) s)
      (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)))
    (hφT : ‖φT‖ = 1)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ AT.successMass j φT)
    (haccT : ∀ j, DensityAccurate eT (AT.conditionalDensity j φT)
      (evolve ((timeData τ s h.s_ge).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (AM : Measured (CoherentQuerySchedule.oracle (ι := ιM)
      (NativeSignedFactor.physOracle (mixedMainData τ ε s h.s_ge))) EM)
    (φM : CommonSpace ιM (SearchIndex (precN τ ε) (hsMu s) s)
      (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)))
    (hφM : ‖φM‖ = 1)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (hsuccM : ∀ j, 2 / 3 ≤ AM.successMass j φM)
    (haccM : ∀ j, DensityAccurate eM (AM.conditionalDensity j φM)
      (evolve ((mixedMainData τ ε s h.s_ge).matrix j) τ (searchInput (precN τ ε) (hsMu s) s))
      ε)
    (AP : Measured (CoherentQuerySchedule.oracle (ι := ιP)
      (NativeSignedFactor.physOracle (precisionMainData τ ε s h.s_ge))) EP)
    (φP : CommonSpace ιP (ScalarIndex (precN τ ε) s) (Word (scalarBits (precN τ ε) s τ)))
    (hφP : ‖φP‖ = 1)
    (eP : EP →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP) (heP : eP† ∘L eP = 1)
    (hsuccP : ∀ x, 2 / 3 ≤ AP.successMass x φP)
    (haccP : ∀ x, DensityAccurate eP (AP.conditionalDensity x φP)
      (evolve ((precisionMainData τ ε s h.s_ge).matrix x) τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (AT.worstCost valueWeight : ℝ)
        (max (AM.worstCost valueWeight : ℝ) (AP.worstCost valueWeight)) := by
  obtain ⟨hT, hM, hP, -⟩ := hard_instances h
  exact main_max_measured h _ valueWeight
    (admissible_common _ (fun x x' => (hT.locators_const x x').2.2.1)
      (fun x x' => (hT.locators_const x x').2.2.2) ιT)
    AT φT hφT eT heT hsuccT haccT _ valueWeight
    (admissible_common _ (fun x x' => (hM.locators_const x x').2.2.1)
      (fun x x' => (hM.locators_const x x').2.2.2) ιM)
    AM φM hφM eM heM hsuccM haccM _ valueWeight
    (admissible_common _ (fun x x' => (hP.locators_const x x').2.2.1)
      (fun x x' => (hP.locators_const x x').2.2.2) ιP)
    AP φP hφP eP heP hsuccP haccP

/-! ### The denominator paragraph for measured algorithms -/

/-- **The required queries for measured algorithms** (eq. `twonorml:eq:necessary-denominator`):
for `k ≥ 47` every measured algorithm over admissible labels of `denomData k`, with a unit
initial vector, success probability at least `2/3` and conditional output `ε`-accurate
(`ε = e^{-L}`) for `e^{-iH_x}(ψ_in ⊗ u_m)` at `t = 1`, has worst-case cost at least `r_μ/32`. -/
theorem denom_lower_measured {k : ℕ} (hk : 47 ≤ k) {K E G L : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (O : L → (Fin (precN (denomTheta k) (denomEps k)) → Bool) → K →L[ℂ] K) (w : L → ℕ)
    (hO : ∀ l, Admissible (denomData k) (O l) (w l)) (M : Measured O E) (φ : K)
    (hφ : ‖φ‖ = 1)
    (e : E →L[ℂ] SysGarb (ScalarIndex (precN (denomTheta k) (denomEps k)) 2 × Fin (denomM k)) G)
    (he : e† ∘L e = 1) (hsucc : ∀ x, 2 / 3 ≤ M.successMass x φ)
    (hacc : ∀ x, DensityAccurate e (M.conditionalDensity x φ) (evolve ((denomData k).matrix x) 1
      (embedU (denomM k) (scalarInput (precN (denomTheta k) (denomEps k)) 2))) (denomEps k)) :
    hsR (denomTheta k) (denomEps k) / 32 ≤ M.worstCost w := by
  classical
  have d := deferred_admissible (denomData k) O w hO M hφ e _ hacc
  have hb := denom_lower_tree hk (selFamily O (nativeCounted O) (DRec M)) selWeight
    (admissible_selFamily (denomData k) hO (DRec M)) (deferredTree (nativeCounted O) ℂ M φ hφ)
    (liftReadout (DOut M) e) (liftReadout_isometry he) (fun x => (d x).2.1 ▸ hsucc x)
    (fun x => (d x).1)
  exact hb.trans (worstCost_deferredTree_le
    (fun l hl => one_le_of_nativeCounted (denomData k) hO l hl) M hφ)

/-- **The logarithmic denominator must change, measured algorithms** (eqs.
`twonorml:eq:counterexample-parameters`, `twonorml:eq:wrong-denominator`,
`twonorml:eq:necessary-denominator`): for every constant `C` and every
`k ≥ max(47, ⌈(384 C)² + 3⌉)`, every measured algorithm over admissible labels of `denomData k`
(native calls with spectators, controls, masks and inverses, input-independent unitaries), with
a unit initial vector, success probability at least `2/3` and conditional output `ε`-accurate in
trace distance for `e^{-iH_x}(ψ_in ⊗ u_m)` (`t = 1`, `ε = e^{-L}`), makes more than
`C (√s η|t| + √(sμ|t| r̃) + r̃)` weighted calls in the worst case, at `s = 2m`, `η = 1`,
`μ = m^{-1/2}`. -/
theorem wrong_denominator_measured (C : ℝ) {k : ℕ} (hk : max 47 ⌈(384 * C) ^ 2 + 3⌉₊ ≤ k)
    {K E G L : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (O : L → (Fin (precN (denomTheta k) (denomEps k)) → Bool) → K →L[ℂ] K) (w : L → ℕ)
    (hO : ∀ l, Admissible (denomData k) (O l) (w l)) (M : Measured O E) (φ : K)
    (hφ : ‖φ‖ = 1)
    (e : E →L[ℂ] SysGarb (ScalarIndex (precN (denomTheta k) (denomEps k)) 2 × Fin (denomM k)) G)
    (he : e† ∘L e = 1) (hsucc : ∀ x, 2 / 3 ≤ M.successMass x φ)
    (hacc : ∀ x, DensityAccurate e (M.conditionalDensity x φ) (evolve ((denomData k).matrix x) 1
      (embedU (denomM k) (scalarInput (precN (denomTheta k) (denomEps k)) 2))) (denomEps k)) :
    C * wrongShape (2 * denomM k) 1 (denomMu k) 1 (denomEps k) < M.worstCost w := by
  have hk47 : 47 ≤ k := le_of_max_le_left hk
  have hkC : (384 * C) ^ 2 + 3 ≤ k :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hk)
  exact wrong_lt_of_lower C hk47 hkC (denom_lower_measured hk47 O w hO M φ hφ e he hsucc hacc)

/-- **The logarithmic denominator must change, measured algorithms over the common oracle** of the
upper bounds (`CoherentQuerySchedule.oracle (physOracle (denomData k))`, value calls counted). -/
theorem wrong_denominator_measured_common (C : ℝ) {k : ℕ}
    (hk : max 47 ⌈(384 * C) ^ 2 + 3⌉₊ ≤ k) (ι : Type) [Fintype ι] {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (M : Measured (CoherentQuerySchedule.oracle (ι := ι)
      (NativeSignedFactor.physOracle (denomData k))) E)
    (φ : CommonSpace ι (ScalarIndex (precN (denomTheta k) (denomEps k)) 2 × Fin (denomM k))
      (Word (scalarBits (precN (denomTheta k) (denomEps k)) 2 (denomTheta k))))
    (hφ : ‖φ‖ = 1)
    (e : E →L[ℂ] SysGarb (ScalarIndex (precN (denomTheta k) (denomEps k)) 2 × Fin (denomM k)) G)
    (he : e† ∘L e = 1) (hsucc : ∀ x, 2 / 3 ≤ M.successMass x φ)
    (hacc : ∀ x, DensityAccurate e (M.conditionalDensity x φ) (evolve ((denomData k).matrix x) 1
      (embedU (denomM k) (scalarInput (precN (denomTheta k) (denomEps k)) 2))) (denomEps k)) :
    C * wrongShape (2 * denomM k) 1 (denomMu k) 1 (denomEps k) < M.worstCost valueWeight :=
  wrong_denominator_measured C hk _ valueWeight
    (admissible_common _ (fun x x' => ((denom_instance k).locators_const x x').2.2.1)
      (fun x x' => ((denom_instance k).locators_const x x').2.2.2) ι)
    M φ hφ e he hsucc hacc

/-! ### Non-vacuity: the released simulations as measured algorithms -/

section NonVacuity

/-- **A common-form simulation is a measured algorithm meeting every hypothesis of the measured
lower bounds**: the program, run on the encoded input `inp ψ` and output in full
(`Model.ofProgram p (output 1)`, read through the endpoint readout), has a unit initial vector,
an isometric readout, success probability one, conditional output `ε`-accurate in trace distance
for `e^{-itH_x} ψ` on every input, and worst-case number of value calls at most its query
bound. -/
theorem measured_of_simulates {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] [DecidableEq Z] {s' : ℕ} (D : Data X N Z s')
    (hH : ∀ x, (D.matrix x).IsHermitian) {t' ε' q : ℝ}
    (hq : NativeSignedFactor.Simulates (NativeSignedFactor.physOracle D)
      (fun x => SparseStateOverlap.matrixOperator (D.matrix x)) t' ε' q)
    (ψ : EuclideanSpace ℂ N) (hψ : ‖ψ‖ = 1) (i₀ : N) :
    ∃ (ι : Type) (_ : Fintype ι)
      (M : Measured (CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle D))
        (CommonSpace ι N Z))
      (φ : CommonSpace ι N Z) (e : CommonSpace ι N Z →L[ℂ] SysGarb N (CommonSpace ι N Z)),
      ‖φ‖ = 1 ∧ e† ∘L e = 1 ∧ (∀ x, M.successMass x φ = 1) ∧
      (∀ x, DensityAccurate e (M.conditionalDensity x φ) (evolve (D.matrix x) t' ψ) ε') ∧
      (M.worstCost valueWeight : ℝ) ≤ q := by
  obtain ⟨ι, _, inp, p, hinp, hcount, hsim⟩ := hq
  obtain ⟨-, hacc⟩ := accurate_of_endpoint_program (common_unitary D ι) p inp hinp i₀ hH hψ
    fun x => (hsim x).2
  have hφ : ‖inp ψ‖ = 1 := by rw [Reduction.norm_encode inp hinp, hψ]
  have h1 : (1 : CommonSpace ι N Z →L[ℂ] CommonSpace ι N Z)† ∘L
      (1 : CommonSpace ι N Z →L[ℂ] CommonSpace ι N Z) = 1 := by
    rw [ContinuousLinearMap.adjoint_one]
    exact ContinuousLinearMap.ext fun v => rfl
  have hmass : ∀ x, (ofProgram p (Measured.output
      (1 : CommonSpace ι N Z →L[ℂ] CommonSpace ι N Z) h1)).successMass x (inp ψ) = 1 := by
    intro x
    rw [successMass_ofProgram]
    simp only [Measured.successMass, ContinuousLinearMap.adjoint_one,
      one_apply_eq_self]
    rw [LinearSystemLowerBound.isUnitary_norm (p.eval_unitary (common_unitary D ι) x), hφ,
      one_pow]
  refine ⟨ι, inferInstance, ofProgram p (Measured.output
    (1 : CommonSpace ι N Z →L[ℂ] CommonSpace ι N Z) h1), inp ψ, endpointReadout inp i₀,
    hφ, endpointReadout_isometry inp hinp i₀, hmass, fun x => ?_, ?_⟩
  · have hd : (ofProgram p (Measured.output
        (1 : CommonSpace ι N Z →L[ℂ] CommonSpace ι N Z) h1)).conditionalDensity x (inp ψ) =
        ODEMixedOutput.pureOperator (p.eval x (inp ψ)) := by
      rw [Measured.conditionalDensity, hmass x, successDensity_ofProgram]
      simp only [Measured.successDensity, ContinuousLinearMap.adjoint_one,
        one_apply_eq_self]
      simp
    rw [hd, AdaptiveHamiltonianLowerBound.densityAccurate_pure_iff]
    exact hacc x
  · rw [worstCost_ofProgram]
    simp only [Measured.worstCost, add_zero]
    rw [AdaptiveHamiltonianLowerBound.cost_valueWeight]
    exact (by exact_mod_cast labelCount_le_count p .value :
      (p.labelCount .value : ℝ) ≤ p.count).trans hcount

set_option maxHeartbeats 1000000 in
/-- **`Θ` for measured algorithms in the common query model** (eq. `hs:eq:optimal-theta`): there
are measured algorithms over the common oracle of the time, mixed and precision families of
`hsl:thm:main` (the released common-form simulations of `hs:thm:optimal`, `optimal_on_hard`) that
meet every hypothesis of `main_max_measured_common` (unit initial vectors, isometric readouts,
success probability one, conditional accuracy `ε` for `e^{-iτH_x} ψ_in`), and for them, with
`S = √s τ + √(sτr) + r`, `c₀ S ≤ max(Q_T, Q_M, Q_P) ≤ 2·10¹² S`, `Q` the worst-case number of
value calls. -/
theorem optimal_measured_theta {τ : ℝ} (h : HSRange τ s ε) :
    ∃ (ιT ιM ιP : Type) (_ : Fintype ιT) (_ : Fintype ιM) (_ : Fintype ιP)
      (AT : Measured (CoherentQuerySchedule.oracle (ι := ιT)
        (NativeSignedFactor.physOracle (timeData τ s h.s_ge)))
        (CommonSpace ιT (SearchIndex (timeN τ) (hsMu s) s)
          (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ))))
      (AM : Measured (CoherentQuerySchedule.oracle (ι := ιM)
        (NativeSignedFactor.physOracle (mixedMainData τ ε s h.s_ge)))
        (CommonSpace ιM (SearchIndex (precN τ ε) (hsMu s) s)
          (Word (searchBits (precN τ ε) (hsMu s) s 1 τ))))
      (AP : Measured (CoherentQuerySchedule.oracle (ι := ιP)
        (NativeSignedFactor.physOracle (precisionMainData τ ε s h.s_ge)))
        (CommonSpace ιP (ScalarIndex (precN τ ε) s) (Word (scalarBits (precN τ ε) s τ))))
      (φT : CommonSpace ιT (SearchIndex (timeN τ) (hsMu s) s)
        (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)))
      (φM : CommonSpace ιM (SearchIndex (precN τ ε) (hsMu s) s)
        (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)))
      (φP : CommonSpace ιP (ScalarIndex (precN τ ε) s) (Word (scalarBits (precN τ ε) s τ)))
      (eT : CommonSpace ιT (SearchIndex (timeN τ) (hsMu s) s)
          (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) →L[ℂ]
        SysGarb (SearchIndex (timeN τ) (hsMu s) s)
          (CommonSpace ιT (SearchIndex (timeN τ) (hsMu s) s)
            (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ))))
      (eM : CommonSpace ιM (SearchIndex (precN τ ε) (hsMu s) s)
          (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) →L[ℂ]
        SysGarb (SearchIndex (precN τ ε) (hsMu s) s)
          (CommonSpace ιM (SearchIndex (precN τ ε) (hsMu s) s)
            (Word (searchBits (precN τ ε) (hsMu s) s 1 τ))))
      (eP : CommonSpace ιP (ScalarIndex (precN τ ε) s) (Word (scalarBits (precN τ ε) s τ)) →L[ℂ]
        SysGarb (ScalarIndex (precN τ ε) s)
          (CommonSpace ιP (ScalarIndex (precN τ ε) s) (Word (scalarBits (precN τ ε) s τ)))),
      (‖φT‖ = 1 ∧ eT† ∘L eT = 1 ∧ (∀ j, AT.successMass j φT = 1) ∧
        ∀ j, DensityAccurate eT (AT.conditionalDensity j φT)
          (evolve ((timeData τ s h.s_ge).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε) ∧
      (‖φM‖ = 1 ∧ eM† ∘L eM = 1 ∧ (∀ j, AM.successMass j φM = 1) ∧
        ∀ j, DensityAccurate eM (AM.conditionalDensity j φM)
          (evolve ((mixedMainData τ ε s h.s_ge).matrix j) τ
            (searchInput (precN τ ε) (hsMu s) s)) ε) ∧
      (‖φP‖ = 1 ∧ eP† ∘L eP = 1 ∧ (∀ x, AP.successMass x φP = 1) ∧
        ∀ x, DensityAccurate eP (AP.conditionalDensity x φP)
          (evolve ((precisionMainData τ ε s h.s_ge).matrix x) τ (scalarInput (precN τ ε) s)) ε) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (AT.worstCost valueWeight : ℝ)
          (max (AM.worstCost valueWeight : ℝ) (AP.worstCost valueWeight)) ∧
      max (AT.worstCost valueWeight : ℝ)
          (max (AM.worstCost valueWeight : ℝ) (AP.worstCost valueWeight)) ≤
        2 * 10 ^ 12 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) := by
  obtain ⟨hIT, hIM, hIP, -⟩ := hard_instances h
  obtain ⟨hST, hSM, hSP⟩ := optimal_on_hard h
  obtain ⟨ιT, _, AT, φT, eT, hφT, heT, hsT, haT, hqT⟩ := measured_of_simulates _ hIT.isHermitian
    hST (searchInput (timeN τ) (hsMu s) s) (norm_searchInput _ _ _) refZero
  obtain ⟨ιM, _, AM, φM, eM, hφM, heM, hsM, haM, hqM⟩ := measured_of_simulates _ hIM.isHermitian
    hSM (searchInput (precN τ ε) (hsMu s) s) (norm_searchInput _ _ _) refZero
  obtain ⟨ιP, _, AP, φP, eP, hφP, heP, hsP, haP, hqP⟩ := measured_of_simulates _ hIP.isHermitian
    hSP (scalarInput (precN τ ε) s) (norm_scalarInput _ _) refZero
  refine ⟨ιT, ιM, ιP, inferInstance, inferInstance, inferInstance, AT, AM, AP, φT, φM, φP, eT,
    eM, eP, ⟨hφT, heT, hsT, haT⟩, ⟨hφM, heM, hsM, haM⟩, ⟨hφP, heP, hsP, haP⟩, ?_,
    max_le hqT (max_le hqM hqP)⟩
  exact main_max_measured_common h ιT ιM ιP AT φT hφT eT heT
    (fun j => by rw [hsT j]; norm_num) haT AM φM hφM eM heM (fun j => by rw [hsM j]; norm_num)
    haM AP φP hφP eP heP (fun x => by rw [hsP x]; norm_num) haP

/-- **The aligned families as measured algorithms**: data meeting `TwoNormInstance` and the
hypotheses of `hs:thm:two-norm` (`two_on_aligned_of`) are simulated by a measured algorithm over
the common oracle that meets every hypothesis of the measured lower bounds on every known unit
input, with at most `2·10¹² (√s η|t| + √(sμ|t| r_μ) + r_μ)` value calls in the worst case. -/
theorem measured_on_aligned_of {X N : Type} [Fintype N] [DecidableEq N] {B : ℕ}
    (D : Data X N (Word B) (s * m)) (hD : TwoNormInstance D c m) (hθ1 : 1 ≤ θ) (hs : 1 ≤ s)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) (hm : 0 < m) (hc : c ≠ 0) (hθ : c * m * t = θ)
    (ψ : EuclideanSpace ℂ N) (hψ : ‖ψ‖ = 1) (i₀ : N) :
    ∃ (ι : Type) (_ : Fintype ι)
      (M : Measured (CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle D))
        (CommonSpace ι N (Word B)))
      (φ : CommonSpace ι N (Word B))
      (e : CommonSpace ι N (Word B) →L[ℂ] SysGarb N (CommonSpace ι N (Word B))),
      ‖φ‖ = 1 ∧ e† ∘L e = 1 ∧ (∀ x, M.successMass x φ = 1) ∧
      (∀ x, DensityAccurate e (M.conditionalDensity x φ) (evolve (D.matrix x) t ψ) ε) ∧
      (M.worstCost valueWeight : ℝ) ≤ 2 * 10 ^ 12 *
        (Real.sqrt ((s * m : ℕ) : ℝ) * (|c| * Real.sqrt m) * |t| +
          Real.sqrt ((s * m : ℕ) * |c| * |t| * hsR θ ε) + hsR θ ε) :=
  measured_of_simulates D hD.isHermitian (two_on_aligned_of D hD hθ1 hs hε hε1 hm hc hθ) ψ hψ i₀

/-- `measured_on_aligned_of` in the range `HSRange θ s₀ ε`. -/
theorem measured_on_aligned {X N : Type} [Fintype N] [DecidableEq N] {B : ℕ}
    (D : Data X N (Word B) (s * m)) (hD : TwoNormInstance D c m) (h : HSRange θ s ε)
    (hm : 0 < m) (hc : c ≠ 0) (hθ : c * m * t = θ) (ψ : EuclideanSpace ℂ N) (hψ : ‖ψ‖ = 1)
    (i₀ : N) :
    ∃ (ι : Type) (_ : Fintype ι)
      (M : Measured (CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle D))
        (CommonSpace ι N (Word B)))
      (φ : CommonSpace ι N (Word B))
      (e : CommonSpace ι N (Word B) →L[ℂ] SysGarb N (CommonSpace ι N (Word B))),
      ‖φ‖ = 1 ∧ e† ∘L e = 1 ∧ (∀ x, M.successMass x φ = 1) ∧
      (∀ x, DensityAccurate e (M.conditionalDensity x φ) (evolve (D.matrix x) t ψ) ε) ∧
      (M.worstCost valueWeight : ℝ) ≤ 2 * 10 ^ 12 *
        (Real.sqrt ((s * m : ℕ) : ℝ) * (|c| * Real.sqrt m) * |t| +
          Real.sqrt ((s * m : ℕ) * |c| * |t| * hsR θ ε) + hsR θ ε) :=
  measured_on_aligned_of D hD h.one_le_tau (by have := h.s_ge; omega) h.eps_pos h.eps_le hm hc hθ
    ψ hψ i₀

set_option maxHeartbeats 1000000 in
/-- **`Θ` on the aligned two-norm families for measured algorithms over the common oracle**:
there are measured algorithms over the common oracle of the enlarged time, mixed and precision
families (the released common-form simulations of `hs:thm:two-norm`) that meet every hypothesis
of `two_norm_main_max_measured_common` (unit initial vectors, isometric readouts, success
probability one, conditional accuracy `ε` for `e^{-itH_X}(ψ_in ⊗ u_m)`), and for them, with
`S' = √s η|t| + √(sμ|t| r_μ) + r_μ`,
`c₀ S' ≤ max(Q_T, Q_M, Q_P) ≤ 2·10¹² S'`, `Q` the worst-case number of value calls. -/
theorem two_norm_measured_theta (h : HSRange θ s ε) (hm : 0 < m) (hc : c ≠ 0)
    (hθ : c * m * t = θ) :
    ∃ (ιT ιM ιP : Type) (_ : Fintype ιT) (_ : Fintype ιM) (_ : Fintype ιP)
      (AT : Measured (CoherentQuerySchedule.oracle (ι := ιT)
        (NativeSignedFactor.physOracle (timeTwo θ s h.s_ge m hm c hc)))
        (CommonSpace ιT (SearchIndex (timeN θ) (hsMu s) s × Fin m)
          (Word (searchBits (timeN θ) (hsMu s) s (timeC θ) θ))))
      (AM : Measured (CoherentQuerySchedule.oracle (ι := ιM)
        (NativeSignedFactor.physOracle (mixedTwo θ ε s h.s_ge m hm c hc)))
        (CommonSpace ιM (SearchIndex (precN θ ε) (hsMu s) s × Fin m)
          (Word (searchBits (precN θ ε) (hsMu s) s 1 θ))))
      (AP : Measured (CoherentQuerySchedule.oracle (ι := ιP)
        (NativeSignedFactor.physOracle (precisionTwo θ ε s h.s_ge m hm c hc)))
        (CommonSpace ιP (ScalarIndex (precN θ ε) s × Fin m) (Word (scalarBits (precN θ ε) s θ))))
      (φT : CommonSpace ιT (SearchIndex (timeN θ) (hsMu s) s × Fin m)
        (Word (searchBits (timeN θ) (hsMu s) s (timeC θ) θ)))
      (φM : CommonSpace ιM (SearchIndex (precN θ ε) (hsMu s) s × Fin m)
        (Word (searchBits (precN θ ε) (hsMu s) s 1 θ)))
      (φP : CommonSpace ιP (ScalarIndex (precN θ ε) s × Fin m) (Word (scalarBits (precN θ ε) s θ)))
      (eT : CommonSpace ιT (SearchIndex (timeN θ) (hsMu s) s × Fin m)
          (Word (searchBits (timeN θ) (hsMu s) s (timeC θ) θ)) →L[ℂ]
        SysGarb (SearchIndex (timeN θ) (hsMu s) s × Fin m)
          (CommonSpace ιT (SearchIndex (timeN θ) (hsMu s) s × Fin m)
            (Word (searchBits (timeN θ) (hsMu s) s (timeC θ) θ))))
      (eM : CommonSpace ιM (SearchIndex (precN θ ε) (hsMu s) s × Fin m)
          (Word (searchBits (precN θ ε) (hsMu s) s 1 θ)) →L[ℂ]
        SysGarb (SearchIndex (precN θ ε) (hsMu s) s × Fin m)
          (CommonSpace ιM (SearchIndex (precN θ ε) (hsMu s) s × Fin m)
            (Word (searchBits (precN θ ε) (hsMu s) s 1 θ))))
      (eP : CommonSpace ιP (ScalarIndex (precN θ ε) s × Fin m)
          (Word (scalarBits (precN θ ε) s θ)) →L[ℂ]
        SysGarb (ScalarIndex (precN θ ε) s × Fin m)
          (CommonSpace ιP (ScalarIndex (precN θ ε) s × Fin m) (Word (scalarBits (precN θ ε) s θ)))),
      (‖φT‖ = 1 ∧ eT† ∘L eT = 1 ∧ (∀ j, AT.successMass j φT = 1) ∧
        ∀ j, DensityAccurate eT (AT.conditionalDensity j φT)
          (evolve ((timeTwo θ s h.s_ge m hm c hc).matrix j) t
            (embedU m (searchInput (timeN θ) (hsMu s) s))) ε) ∧
      (‖φM‖ = 1 ∧ eM† ∘L eM = 1 ∧ (∀ j, AM.successMass j φM = 1) ∧
        ∀ j, DensityAccurate eM (AM.conditionalDensity j φM)
          (evolve ((mixedTwo θ ε s h.s_ge m hm c hc).matrix j) t
            (embedU m (searchInput (precN θ ε) (hsMu s) s))) ε) ∧
      (‖φP‖ = 1 ∧ eP† ∘L eP = 1 ∧ (∀ x, AP.successMass x φP = 1) ∧
        ∀ x, DensityAccurate eP (AP.conditionalDensity x φP)
          (evolve ((precisionTwo θ ε s h.s_ge m hm c hc).matrix x) t
            (embedU m (scalarInput (precN θ ε) s))) ε) ∧
      c0 * (Real.sqrt ((s * m : ℕ) : ℝ) * (|c| * Real.sqrt m) * |t| +
          Real.sqrt ((s * m : ℕ) * |c| * |t| * hsR θ ε) + hsR θ ε) ≤
        max (AT.worstCost valueWeight : ℝ)
          (max (AM.worstCost valueWeight : ℝ) (AP.worstCost valueWeight)) ∧
      max (AT.worstCost valueWeight : ℝ)
          (max (AM.worstCost valueWeight : ℝ) (AP.worstCost valueWeight)) ≤
        2 * 10 ^ 12 * (Real.sqrt ((s * m : ℕ) : ℝ) * (|c| * Real.sqrt m) * |t| +
          Real.sqrt ((s * m : ℕ) * |c| * |t| * hsR θ ε) + hsR θ ε) := by
  obtain ⟨hIT, hIM, hIP⟩ := two_instances h hm hc
  obtain ⟨ιT, _, AT, φT, eT, hφT, heT, hsT, haT, hqT⟩ := measured_on_aligned _ hIT h hm hc hθ
    (embedU m (searchInput (timeN θ) (hsMu s) s)) (norm_embedU_searchInput _ _ _ hm)
    (refZero, ⟨0, hm⟩)
  obtain ⟨ιM, _, AM, φM, eM, hφM, heM, hsM, haM, hqM⟩ := measured_on_aligned _ hIM h hm hc hθ
    (embedU m (searchInput (precN θ ε) (hsMu s) s)) (norm_embedU_searchInput _ _ _ hm)
    (refZero, ⟨0, hm⟩)
  obtain ⟨ιP, _, AP, φP, eP, hφP, heP, hsP, haP, hqP⟩ := measured_on_aligned _ hIP h hm hc hθ
    (embedU m (scalarInput (precN θ ε) s)) (norm_embedU_scalarInput _ _ hm) (refZero, ⟨0, hm⟩)
  refine ⟨ιT, ιM, ιP, inferInstance, inferInstance, inferInstance, AT, AM, AP, φT, φM, φP, eT,
    eM, eP, ⟨hφT, heT, hsT, haT⟩, ⟨hφM, heM, hsM, haM⟩, ⟨hφP, heP, hsP, haP⟩, ?_,
    max_le hqT (max_le hqM hqP)⟩
  exact two_norm_main_max_measured_common h hm hc hθ ιT ιM ιP AT φT hφT eT heT
    (fun j => by rw [hsT j]; norm_num) haT AM φM hφM eM heM (fun j => by rw [hsM j]; norm_num)
    haM AP φP hφP eP heP (fun x => by rw [hsP x]; norm_num) haP

/-- **The counterexample family is simulable by a measured algorithm with the corrected
denominator** (non-vacuity of the measured denominator statements): for `k ≥ 2` there is a
measured algorithm over the common oracle of `denomData k` that meets every hypothesis of
`wrong_denominator_measured_common` (unit initial vector, isometric readout, success probability
one, conditional accuracy `ε = e^{-L}` at `t = 1`), with at most
`2·10¹² (√s η|t| + √(sμ|t| r_μ) + r_μ)` value calls in the worst case (`denom_simulates`). -/
theorem denom_measured {k : ℕ} (hk : 2 ≤ k) :
    ∃ (ι : Type) (_ : Fintype ι)
      (M : Measured (CoherentQuerySchedule.oracle (ι := ι)
        (NativeSignedFactor.physOracle (denomData k)))
        (CommonSpace ι (ScalarIndex (precN (denomTheta k) (denomEps k)) 2 × Fin (denomM k))
          (Word (scalarBits (precN (denomTheta k) (denomEps k)) 2 (denomTheta k)))))
      (φ : CommonSpace ι (ScalarIndex (precN (denomTheta k) (denomEps k)) 2 × Fin (denomM k))
        (Word (scalarBits (precN (denomTheta k) (denomEps k)) 2 (denomTheta k))))
      (e : CommonSpace ι (ScalarIndex (precN (denomTheta k) (denomEps k)) 2 × Fin (denomM k))
          (Word (scalarBits (precN (denomTheta k) (denomEps k)) 2 (denomTheta k))) →L[ℂ]
        SysGarb (ScalarIndex (precN (denomTheta k) (denomEps k)) 2 × Fin (denomM k))
          (CommonSpace ι (ScalarIndex (precN (denomTheta k) (denomEps k)) 2 × Fin (denomM k))
            (Word (scalarBits (precN (denomTheta k) (denomEps k)) 2 (denomTheta k))))),
      ‖φ‖ = 1 ∧ e† ∘L e = 1 ∧ (∀ x, M.successMass x φ = 1) ∧
      (∀ x, DensityAccurate e (M.conditionalDensity x φ) (evolve ((denomData k).matrix x) 1
        (embedU (denomM k) (scalarInput (precN (denomTheta k) (denomEps k)) 2))) (denomEps k)) ∧
      (M.worstCost valueWeight : ℝ) ≤ 2 * 10 ^ 12 *
        (Real.sqrt ((2 * denomM k : ℕ) : ℝ) * (|denomMu k| * Real.sqrt (denomM k)) * |1| +
          Real.sqrt ((2 * denomM k : ℕ) * |denomMu k| * |1| * hsR (denomTheta k) (denomEps k)) +
          hsR (denomTheta k) (denomEps k)) :=
  measured_of_simulates (denomData k) (denom_instance k).isHermitian (denom_simulates hk) _
    (norm_embedU_scalarInput _ _ (denomM_pos k)) (refZero, ⟨0, denomM_pos k⟩)

end NonVacuity

end

end OptimalLowerBounds
