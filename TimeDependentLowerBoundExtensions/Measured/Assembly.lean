import TimeDependentLowerBoundExtensions.Measured.Compile
import TimeDependentLowerBoundExtensions.Measured.MaskedLift
import DeferredMeasurementLowerBounds.Corollaries.Hamiltonian
import AdaptiveODELowerBound.Access.Calls

set_option autoImplicit false

/-!
# Theorem `hsl:thm:main` for measured algorithms over families compiled into native calls

Theorem `hsl:thm:main` (the manuscript, lines 2102-2119, eq. `hsl:eq:main`) for algorithms with
measurements inside a run (lines 2363-2364: "Randomised or adaptive algorithms are covered by
purification and deferred measurement"), over oracle families whose calls are not single native
calls but fixed products of them.

* `NativeCompiles D O c`: every label `l` of `O` is computed exactly, on the same workspace, by a
  program `P l` over a family of labels admissible for `D`
  (`AdaptiveHamiltonianLowerBound.Access.Admissible`), of weighted cost at most `c`.
* `NativeCompiles.map`: the certificate passes through masked lifts (spectators, relabellings,
  control masks), same `c`; `NativeCompiles.callFamily`: it passes to all call forms (plain,
  inverse, controlled, controlled inverse; `AdaptiveODELowerBound.Access.callFamily`), same `c`.
* `nativeCompiles_of_admissible`: a family of admissible labels of weight at most `c` is natively
  compiled with cost `c` (one call per label), so the certificate contains
  `AdaptiveHamiltonianLowerBound.Access.Admissible`.
* `exists_compiled_measured`: a measured algorithm over `O` compiles
  (`TimeDependentLowerBoundExtensions.Measured.compile`) into a
  measured algorithm over the admissible family with the same success mass and conditional
  output and at most `c` times the worst-case number of calls.
* `main_max_measured_compiled`: for three measured algorithms over families with such
  certificates on the time, mixed and precision families,
  `c₀ (√s τ + √(sτr) + r) ≤ c · max(Q_T, Q_M, Q_P)`, `c₀ = log 2/(4096π)`, `Q` the worst-case
  number of calls (inverse calls included), from
  `DeferredMeasurementLowerBounds.Corollaries.main_max_measured`.

`NativeCompiles` is the `AdaptiveHamiltonianLowerBound.Access.Admissible` counterpart of the
Boolean certificates `SparseLowerBounds.Hamiltonian.HsRelease.PhaseAccess` and of their closures
in `TimeDependentLowerBoundExtensions.Core` (`maskedAccess`, `callAccess`): the measured corollary
`main_max_measured` consumes admissible labels, so the certificate records programs over
admissible labels. With `c = 1` and labels of unit weight (`nativeCompiles_of_admissible`),
`main_max_measured_compiled` is `DeferredMeasurementLowerBounds.Corollaries.main_max_measured`
for unit weights. The measured class contains the unitary programs over the same families
(`DeferredMeasurementLowerBounds.Model.ofProgram`, `successMass_ofProgram`,
`worstCost_ofProgram`); that runs of the released simulators also meet the success and accuracy
hypotheses is shown on constant data in `TimeDependentLowerBoundExtensions.Measured.NonVacuity`.
-/

namespace TimeDependentLowerBoundExtensions.Measured

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct
open SparseHamiltonian ContinuousLinearMap
open SparseLowerBounds SparseLowerBounds.Readout SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding
open DeferredMeasurementLowerBounds.Model
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open AdaptiveHamiltonianLowerBound.Access (Admissible)

/-! ### Certificates -/

section Certificates

variable {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s : ℕ}
variable {K K' L : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']

/-- **Native compilation with cost `c`**: there are a family `B` of labels admissible for `D`
with weights `w` and, for every label `l` of `O`, a program `P l` over `B` with
`(P l).eval x = O l x` on every input and `(P l).cost w ≤ c`. -/
def NativeCompiles (D : NativeSparseBlockEncoding.Data X N Z s) (O : L → X → K →L[ℂ] K)
    (c : ℕ) : Prop :=
  ∃ (L' : Type) (B : L' → X → K →L[ℂ] K) (w : L' → ℕ) (P : L → MultiOracleCircuit.Program B),
    (∀ l', Admissible D (B l') (w l')) ∧ (∀ l x, (P l).eval x = O l x) ∧
      ∀ l, (P l).cost w ≤ c

/-- **Admissible labels are natively compiled**: a family of labels admissible for `D` with
weights at most `c` is natively compiled with cost `c`, each label by its one-call program. -/
theorem nativeCompiles_of_admissible {D : NativeSparseBlockEncoding.Data X N Z s} {L₀ : Type}
    {O : L₀ → X → K →L[ℂ] K} {w : L₀ → ℕ} {c : ℕ} (hO : ∀ l, Admissible D (O l) (w l))
    (hw : ∀ l, w l ≤ c) : NativeCompiles D O c :=
  ⟨L₀, O, w, fun l => .query l, hO, fun _ _ => rfl, hw⟩

/-- **Native compilation passes through masked lifts**, with the same cost. -/
theorem NativeCompiles.map {D : NativeSparseBlockEncoding.Data X N Z s}
    {O : L → X → K →L[ℂ] K} {c : ℕ} (h : NativeCompiles D O c)
    {Φ : (K →L[ℂ] K) → (K' →L[ℂ] K')} (hΦ : IsMaskedLift Φ) :
    NativeCompiles D (fun l x => Φ (O l x)) c := by
  obtain ⟨L', B, w, P, hB, hP, hc⟩ := h
  refine ⟨L', fun l' x => Φ (B l' x), w, fun l => liftProgram hΦ id (P l),
    fun l' => hΦ.admissible (hB l'), fun l x => ?_, fun l => ?_⟩
  · rw [eval_liftProgram hΦ id (fun _ _ => rfl), hP]
  · rw [cost_liftProgram]
    exact hc l

/-- **Native compilation passes to all call forms** (plain, inverse, controlled and
controlled inverse), with the same cost. -/
theorem NativeCompiles.callFamily {D : NativeSparseBlockEncoding.Data X N Z s}
    {O : L → X → K →L[ℂ] K} {c : ℕ} (h : NativeCompiles D O c) :
    NativeCompiles D (AdaptiveODELowerBound.Access.callFamily O) c := by
  obtain ⟨L', B, w, P, hB, hP, hc⟩ := h
  have hF := isMaskedLift_fiber (W := K) Bool
  have hC := isMaskedLift_masked (W := K) Bool (fun b : Bool => b)
  let B' : L' × Bool → X → Joint Bool K →L[ℂ] Joint Bool K := fun p x =>
    cond p.2 (AdaptiveODELowerBound.Access.ctrlOp (B p.1 x)) (Joint.fiber fun _ => B p.1 x)
  let P' : L × AdaptiveODELowerBound.Access.CallForm → MultiOracleCircuit.Program B' := fun p =>
    match p.2 with
    | .plain => liftProgram (B := B') hF (fun l' => (l', false)) (P p.1)
    | .inverse => liftProgram (B := B') hF (fun l' => (l', false)) (P p.1).adjoint
    | .controlled => liftProgram (B := B') hC (fun l' => (l', true)) (P p.1)
    | .controlledInverse => liftProgram (B := B') hC (fun l' => (l', true)) (P p.1).adjoint
  refine ⟨L' × Bool, B', fun p => w p.1, P', ?_, ?_, ?_⟩
  · rintro ⟨l', _ | _⟩
    · exact hF.admissible (hB l')
    · exact hC.admissible (hB l')
  · rintro ⟨l, f⟩ x
    cases f
    · show (liftProgram (B := B') hF (fun l' => (l', false)) (P l)).eval x = _
      rw [eval_liftProgram hF (fun l' => (l', false)) (fun _ _ => rfl), hP]
      rfl
    · show (liftProgram (B := B') hF (fun l' => (l', false)) (P l).adjoint).eval x = _
      rw [eval_liftProgram hF (fun l' => (l', false)) (fun _ _ => rfl),
        MultiOracleCircuit.Program.eval_adjoint, hP]
      rfl
    · show (liftProgram (B := B') hC (fun l' => (l', true)) (P l)).eval x = _
      rw [eval_liftProgram hC (fun l' => (l', true)) (fun _ _ => rfl), hP]
      rfl
    · show (liftProgram (B := B') hC (fun l' => (l', true)) (P l).adjoint).eval x = _
      rw [eval_liftProgram hC (fun l' => (l', true)) (fun _ _ => rfl),
        MultiOracleCircuit.Program.eval_adjoint, hP]
      rfl
  · rintro ⟨l, f⟩
    cases f
    · show (liftProgram (B := B') hF (fun l' => (l', false)) (P l)).cost _ ≤ c
      rw [cost_liftProgram]
      exact hc l
    · show (liftProgram (B := B') hF (fun l' => (l', false)) (P l).adjoint).cost _ ≤ c
      rw [cost_liftProgram, MultiOracleCircuit.Program.cost_adjoint]
      exact hc l
    · show (liftProgram (B := B') hC (fun l' => (l', true)) (P l)).cost _ ≤ c
      rw [cost_liftProgram]
      exact hc l
    · show (liftProgram (B := B') hC (fun l' => (l', true)) (P l).adjoint).cost _ ≤ c
      rw [cost_liftProgram, MultiOracleCircuit.Program.cost_adjoint]
      exact hc l

/-- **A measured algorithm over a natively compiled family** is a measured algorithm over an
admissible family with the same success mass and conditional output, on every input and initial
vector, and at most `c` times the worst-case number of calls. -/
theorem exists_compiled_measured {D : NativeSparseBlockEncoding.Data X N Z s}
    {O : L → X → K →L[ℂ] K} {c : ℕ} (h : NativeCompiles D O c) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (M : Measured O E) :
    ∃ (L' : Type) (B : L' → X → K →L[ℂ] K) (w : L' → ℕ) (M' : Measured B E),
      (∀ l', Admissible D (B l') (w l')) ∧ (∀ x φ, M'.successMass x φ = M.successMass x φ) ∧
      (∀ x φ, M'.conditionalDensity x φ = M.conditionalDensity x φ) ∧
      M'.worstCost w ≤ c * M.worstCost (fun _ => 1) := by
  obtain ⟨L', B, w, P, hB, hP, hc⟩ := h
  exact ⟨L', B, w, compile P M, hB, successMass_compile P hP M,
    conditionalDensity_compile P hP M, worstCost_compile_le P M w hc⟩

end Certificates

/-! ### The three hard families -/

variable {τ ε : ℝ} {s : ℕ}

/-- **Theorem `hsl:thm:main` for measured algorithms over natively compiled families**
(eq. `hsl:eq:main`, max form): for any three measured algorithms over families with native
compilations of cost `c` for the time, mixed and precision families, with unit initial vectors,
success probability at least `2/3` on every input and conditional output `ε`-accurate in trace
distance, `c₀ (√s τ + √(sτr) + r) ≤ c · max(Q_T, Q_M, Q_P)`, `c₀ = log 2/(4096π)`, where `Q` is
the worst-case number of calls over all transcripts (inverse calls included). -/
theorem main_max_measured_compiled (h : HSRange τ s ε) (c : ℕ)
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
    (OT : LT → (Fin (timeN τ) → Fin (2 ^ hsMu s)) → KT →L[ℂ] KT)
    (hOT : NativeCompiles (timeData τ s h.s_ge) OT c)
    (MT : Measured OT ET) (φT : KT) (hφT : ‖φT‖ = 1)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ MT.successMass j φT)
    (haccT : ∀ j, DensityAccurate eT (MT.conditionalDensity j φT)
      (evolve ((timeData τ s h.s_ge).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (OM : LM → (Fin (precN τ ε) → Fin (2 ^ hsMu s)) → KM →L[ℂ] KM)
    (hOM : NativeCompiles (mixedMainData τ ε s h.s_ge) OM c)
    (MM : Measured OM EM) (φM : KM) (hφM : ‖φM‖ = 1)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (hsuccM : ∀ j, 2 / 3 ≤ MM.successMass j φM)
    (haccM : ∀ j, DensityAccurate eM (MM.conditionalDensity j φM)
      (evolve ((mixedMainData τ ε s h.s_ge).matrix j) τ (searchInput (precN τ ε) (hsMu s) s))
      ε)
    (OP : LP → (Fin (precN τ ε) → Bool) → KP →L[ℂ] KP)
    (hOP : NativeCompiles (precisionMainData τ ε s h.s_ge) OP c)
    (MP : Measured OP EP) (φP : KP) (hφP : ‖φP‖ = 1)
    (eP : EP →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP) (heP : eP† ∘L eP = 1)
    (hsuccP : ∀ x, 2 / 3 ≤ MP.successMass x φP)
    (haccP : ∀ x, DensityAccurate eP (MP.conditionalDensity x φP)
      (evolve ((precisionMainData τ ε s h.s_ge).matrix x) τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      c * max (MT.worstCost (fun _ => 1) : ℝ)
        (max (MM.worstCost (fun _ => 1) : ℝ) (MP.worstCost (fun _ => 1))) := by
  obtain ⟨LT', BT, wT, MT', hBT, hsT, hcT, hqT⟩ := exists_compiled_measured hOT MT
  obtain ⟨LM', BM, wM, MM', hBM, hsM, hcM, hqM⟩ := exists_compiled_measured hOM MM
  obtain ⟨LP', BP, wP, MP', hBP, hsP, hcP, hqP⟩ := exists_compiled_measured hOP MP
  have key := DeferredMeasurementLowerBounds.Corollaries.main_max_measured h
    BT wT hBT MT' φT hφT eT heT (fun j => by rw [hsT]; exact hsuccT j)
    (fun j => by rw [hcT]; exact haccT j)
    BM wM hBM MM' φM hφM eM heM (fun j => by rw [hsM]; exact hsuccM j)
    (fun j => by rw [hcM]; exact haccM j)
    BP wP hBP MP' φP hφP eP heP (fun x => by rw [hsP]; exact hsuccP x)
    (fun x => by rw [hcP]; exact haccP x)
  have hT : (MT'.worstCost wT : ℝ) ≤ c * (MT.worstCost (fun _ => 1) : ℝ) := by
    exact_mod_cast hqT
  have hM : (MM'.worstCost wM : ℝ) ≤ c * (MM.worstCost (fun _ => 1) : ℝ) := by
    exact_mod_cast hqM
  have hP : (MP'.worstCost wP : ℝ) ≤ c * (MP.worstCost (fun _ => 1) : ℝ) := by
    exact_mod_cast hqP
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  refine key.trans ((max_le_max hT (max_le_max hM hP)).trans_eq ?_)
  rw [mul_max_of_nonneg _ _ hc0, mul_max_of_nonneg _ _ hc0]

end

end TimeDependentLowerBoundExtensions.Measured
