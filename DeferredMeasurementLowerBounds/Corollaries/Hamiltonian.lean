import DeferredMeasurementLowerBounds.Deferral.Theorem
import DeferredMeasurementLowerBounds.Access.Native
import DeferredMeasurementLowerBounds.Readout.Density
import AdaptiveHamiltonianLowerBound.Theorem

set_option autoImplicit false

/-!
# Theorem `hsl:thm:main` for measured algorithms

Manuscript Theorem `hsl:thm:main` (lines 2102-2119, eq. `hsl:eq:main`) and line 2364
("Randomised or adaptive algorithms are covered by purification and deferred measurement").

`main_max_measured`: for any three **measured algorithms** (mid-run and multi-outcome
measurements, classical control, randomness and resets of finite-dimensional registers on a
persistent workspace of any dimension,
`Model.Measured`), with admissible oracle labels for the time, mixed and precision hard
families respectively, a unit initial vector, success probability at least `2/3` on every input
and conditional output `ε`-accurate in trace distance (`DensityAccurate`), the worst-case
weighted numbers of calls satisfy `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)` with the
constant `c₀ = log 2/(4096π)` of the theorem: **no constant is lost**. `main_exists_measured`
is the family form: one of the three hard families forces every such measured algorithm.

Proof: each measured algorithm is deferred (`Deferral.deferredTree`, counted labels the
input-dependent ones); the record-selected calls of admissible labels are admissible
(`Access.admissible_selFamily`), the deferred protocol has the same success mass
(`Deferral.successMass_deferredTree`), its output read through the lifted readout is as accurate
(`Readout.densityAccurate_liftReadout`), and it makes at most the worst-case number of
input-dependent calls, each of weight at least one (`Access.one_le_of_nativeCounted`). Then
`AdaptiveHamiltonianLowerBound.main_max_tree` applies.
-/

namespace DeferredMeasurementLowerBounds.Corollaries

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct
open SparseHamiltonian SparseLinearSystems.Protocol ContinuousLinearMap
open LinearSystemLowerBound SparseLowerBounds SparseLowerBounds.Readout
open SparseLowerBounds.Hamiltonian NativeSparseBlockEncoding
open DeferredMeasurementLowerBounds.Model DeferredMeasurementLowerBounds.Deferral
open DeferredMeasurementLowerBounds.Access DeferredMeasurementLowerBounds.Readout
open AdaptiveHamiltonianLowerBound (DensityAccurate)

variable {τ ε : ℝ} {s : ℕ}

/-- The deferred protocol of a measured algorithm makes at most its worst-case weighted number of
calls when every input-dependent label has weight at least one. -/
theorem worstCost_deferredTree_le {X E K L : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {O : L → X → K →L[ℂ] K} {w : L → ℕ} (hw : ∀ l, nativeCounted O l → 1 ≤ w l)
    [DecidablePred (nativeCounted O)] (M : Measured O E) {φ : K} (hφ : ‖φ‖ = 1) :
    ((deferredTree (nativeCounted O) ℂ M φ hφ).worstCost selWeight : ℝ) ≤ M.worstCost w := by
  exact_mod_cast (worstCost_deferredTree (counted := nativeCounted O) (F := ℂ) M hφ).trans
    (worstCost_countWeight_le M (nativeCounted O) hw)

/-- **The deferred protocol of an accurate measured algorithm over admissible labels** is an
accurate adaptive protocol over admissible labels whose worst-case cost is at most that of the
measured algorithm. -/
theorem deferred_admissible {S : Type} {X G E K L N Z : Type*} [Fintype S] [DecidableEq S]
    [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {sD : ℕ}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (D : NativeSparseBlockEncoding.Data X N Z sD) (O : L → X → K →L[ℂ] K) (w : L → ℕ)
    (hO : ∀ l, AdaptiveHamiltonianLowerBound.Access.Admissible D (O l) (w l))
    [DecidablePred (nativeCounted O)] (M : Measured O E) {φ : K} (hφ : ‖φ‖ = 1)
    (e : E →L[ℂ] SysGarb S G) (target : X → EuclideanSpace ℂ S)
    (hacc : ∀ x, DensityAccurate e (M.conditionalDensity x φ) (target x) ε) (x : X) :
    DensityAccurate (liftReadout (DOut M) e)
        ((deferredTree (nativeCounted O) ℂ M φ hφ).conditionalDensity x) (target x) ε ∧
      (deferredTree (nativeCounted O) ℂ M φ hφ).successMass x = M.successMass x φ ∧
      ((deferredTree (nativeCounted O) ℂ M φ hφ).worstCost selWeight : ℝ) ≤ M.worstCost w := by
  refine ⟨?_, successMass_deferredTree (counted := nativeCounted O) (F := ℂ) M hφ x,
    worstCost_deferredTree_le (fun l hl => one_le_of_nativeCounted D hO l hl) M hφ⟩
  rw [conditionalDensity_deferredTree (counted := nativeCounted O) (F := ℂ) M hφ x]
  apply densityAccurate_liftReadout
  rw [sum_pure_amplitude (counted := nativeCounted O) M x φ]
  exact hacc x

set_option maxHeartbeats 1000000 in
/-- **Theorem `hsl:thm:main` for measured algorithms, eq. `hsl:eq:main`, max form**: for any
three measured algorithms with admissible labels, accurate on the time, mixed and precision
families respectively, `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, `c₀ = log 2/(4096π)`,
where `Q` is the worst-case weighted number of calls over all transcripts. -/
theorem main_max_measured (h : HSRange τ s ε)
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
    (OT : LT → (Fin (timeN τ) → Fin (2 ^ hsMu s)) → KT →L[ℂ] KT) (wT : LT → ℕ)
    (hOT : ∀ l, AdaptiveHamiltonianLowerBound.Access.Admissible (timeData τ s h.s_ge) (OT l)
      (wT l))
    (MT : Measured OT ET) (φT : KT) (hφT : ‖φT‖ = 1)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ MT.successMass j φT)
    (haccT : ∀ j, DensityAccurate eT (MT.conditionalDensity j φT)
      (evolve ((timeData τ s h.s_ge).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (OM : LM → (Fin (precN τ ε) → Fin (2 ^ hsMu s)) → KM →L[ℂ] KM) (wM : LM → ℕ)
    (hOM : ∀ l, AdaptiveHamiltonianLowerBound.Access.Admissible (mixedMainData τ ε s h.s_ge)
      (OM l) (wM l))
    (MM : Measured OM EM) (φM : KM) (hφM : ‖φM‖ = 1)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (hsuccM : ∀ j, 2 / 3 ≤ MM.successMass j φM)
    (haccM : ∀ j, DensityAccurate eM (MM.conditionalDensity j φM)
      (evolve ((mixedMainData τ ε s h.s_ge).matrix j) τ (searchInput (precN τ ε) (hsMu s) s))
      ε)
    (OP : LP → (Fin (precN τ ε) → Bool) → KP →L[ℂ] KP) (wP : LP → ℕ)
    (hOP : ∀ l, AdaptiveHamiltonianLowerBound.Access.Admissible (precisionMainData τ ε s h.s_ge)
      (OP l) (wP l))
    (MP : Measured OP EP) (φP : KP) (hφP : ‖φP‖ = 1)
    (eP : EP →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP) (heP : eP† ∘L eP = 1)
    (hsuccP : ∀ x, 2 / 3 ≤ MP.successMass x φP)
    (haccP : ∀ x, DensityAccurate eP (MP.conditionalDensity x φP)
      (evolve ((precisionMainData τ ε s h.s_ge).matrix x) τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (MT.worstCost wT : ℝ) (max (MM.worstCost wM : ℝ) (MP.worstCost wP)) := by
  classical
  have dT := deferred_admissible (timeData τ s h.s_ge) OT wT hOT MT hφT eT _ haccT
  have dM := deferred_admissible (mixedMainData τ ε s h.s_ge) OM wM hOM MM hφM eM _ haccM
  have dP := deferred_admissible (precisionMainData τ ε s h.s_ge) OP wP hOP MP hφP eP _ haccP
  have hmax := AdaptiveHamiltonianLowerBound.main_max_tree h
    (selFamily OT (nativeCounted OT) (DRec MT)) selWeight
    (admissible_selFamily (timeData τ s h.s_ge) hOT (DRec MT))
    (deferredTree (nativeCounted OT) ℂ MT φT hφT) (liftReadout (DOut MT) eT)
    (liftReadout_isometry heT) (fun j => (dT j).2.1 ▸ hsuccT j) (fun j => (dT j).1)
    (selFamily OM (nativeCounted OM) (DRec MM)) selWeight
    (admissible_selFamily (mixedMainData τ ε s h.s_ge) hOM (DRec MM))
    (deferredTree (nativeCounted OM) ℂ MM φM hφM) (liftReadout (DOut MM) eM)
    (liftReadout_isometry heM) (fun j => (dM j).2.1 ▸ hsuccM j) (fun j => (dM j).1)
    (selFamily OP (nativeCounted OP) (DRec MP)) selWeight
    (admissible_selFamily (precisionMainData τ ε s h.s_ge) hOP (DRec MP))
    (deferredTree (nativeCounted OP) ℂ MP φP hφP) (liftReadout (DOut MP) eP)
    (liftReadout_isometry heP) (fun x => (dP x).2.1 ▸ hsuccP x) (fun x => (dP x).1)
  refine hmax.trans (max_le_max ?_ (max_le_max ?_ ?_))
  · exact worstCost_deferredTree_le
      (fun l hl => one_le_of_nativeCounted (timeData τ s h.s_ge) hOT l hl) MT hφT
  · exact worstCost_deferredTree_le
      (fun l hl => one_le_of_nativeCounted (mixedMainData τ ε s h.s_ge) hOM l hl) MM hφM
  · exact worstCost_deferredTree_le
      (fun l hl => one_le_of_nativeCounted (precisionMainData τ ε s h.s_ge) hOP l hl) MP hφP

universe uK uE uG uL

/-- **Theorem `hsl:thm:main` for measured algorithms, family form**: for every parameter triple,
one of the three hard families (time, mixed or precision) forces **every** measured algorithm
with admissible labels, a unit initial vector, success probability at least `2/3` and
conditional accuracy `ε` (any workspace `K`, finite-dimensional output space `E`, garbage `G`
and label type `L` in the given universes) to make at least `c₀ (√s τ + √(sτr) + r)` weighted
calls in the worst case over all transcripts. -/
theorem main_exists_measured (h : HSRange τ s ε) :
    (∀ (K : Type uK) (E : Type uE) (G : Type uG) (L : Type uL)
        [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
        [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
        [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
        (O : L → (Fin (timeN τ) → Fin (2 ^ hsMu s)) → K →L[ℂ] K) (w : L → ℕ),
        (∀ l, AdaptiveHamiltonianLowerBound.Access.Admissible (timeData τ s h.s_ge) (O l) (w l)) →
        ∀ (M : Measured O E) (φ : K), ‖φ‖ = 1 →
        ∀ (e : E →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) G),
        e† ∘L e = 1 → (∀ j, 2 / 3 ≤ M.successMass j φ) →
        (∀ j, DensityAccurate e (M.conditionalDensity j φ)
          (evolve ((timeData τ s h.s_ge).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε) →
        c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ M.worstCost w) ∨
    (∀ (K : Type uK) (E : Type uE) (G : Type uG) (L : Type uL)
        [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
        [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
        [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
        (O : L → (Fin (precN τ ε) → Fin (2 ^ hsMu s)) → K →L[ℂ] K) (w : L → ℕ),
        (∀ l, AdaptiveHamiltonianLowerBound.Access.Admissible (mixedMainData τ ε s h.s_ge) (O l)
          (w l)) →
        ∀ (M : Measured O E) (φ : K), ‖φ‖ = 1 →
        ∀ (e : E →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) G),
        e† ∘L e = 1 → (∀ j, 2 / 3 ≤ M.successMass j φ) →
        (∀ j, DensityAccurate e (M.conditionalDensity j φ)
          (evolve ((mixedMainData τ ε s h.s_ge).matrix j) τ
            (searchInput (precN τ ε) (hsMu s) s)) ε) →
        c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ M.worstCost w) ∨
    (∀ (K : Type uK) (E : Type uE) (G : Type uG) (L : Type uL)
        [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
        [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
        [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
        (O : L → (Fin (precN τ ε) → Bool) → K →L[ℂ] K) (w : L → ℕ),
        (∀ l, AdaptiveHamiltonianLowerBound.Access.Admissible (precisionMainData τ ε s h.s_ge)
          (O l) (w l)) →
        ∀ (M : Measured O E) (φ : K), ‖φ‖ = 1 →
        ∀ (e : E →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) G),
        e† ∘L e = 1 → (∀ x, 2 / 3 ≤ M.successMass x φ) →
        (∀ x, DensityAccurate e (M.conditionalDensity x φ)
          (evolve ((precisionMainData τ ε s h.s_ge).matrix x) τ (scalarInput (precN τ ε) s)) ε) →
        c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ M.worstCost w) := by
  by_contra hneg
  push Not at hneg
  obtain ⟨⟨KT, ET, GT, LT, _, _, _, _, _, _, _, _, _, _, OT, wT, hOT, MT, φT, hφT, eT, heT,
      hsuccT, haccT, hT⟩,
    ⟨KM, EM, GM, LM, _, _, _, _, _, _, _, _, _, _, OM, wM, hOM, MM, φM, hφM, eM, heM,
      hsuccM, haccM, hM⟩,
    ⟨KP, EP, GP, LP, _, _, _, _, _, _, _, _, _, _, OP, wP, hOP, MP, φP, hφP, eP, heP,
      hsuccP, haccP, hP⟩⟩ := hneg
  have hmax := main_max_measured h OT wT hOT MT φT hφT eT heT hsuccT haccT OM wM hOM MM φM hφM
    eM heM hsuccM haccM OP wP hOP MP φP hφP eP heP hsuccP haccP
  have := max_lt hT (max_lt hM hP)
  linarith

end

end DeferredMeasurementLowerBounds.Corollaries
