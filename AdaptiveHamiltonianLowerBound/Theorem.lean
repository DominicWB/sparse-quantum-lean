import AdaptiveHamiltonianLowerBound.Families
import AdaptiveHamiltonianLowerBound.Model.Single
import SparseLowerBounds.Hamiltonian.Assembly

set_option autoImplicit false

/-!
# Theorem `hsl:thm:main` for adaptive algorithms

Manuscript: Theorem `hsl:thm:main` and its proof, eq. `hsl:eq:main`,
`max(Q_T, Q_M, Q_P) ≥ c₀ (√s τ + √(sτr) + r)` with `c₀ = log 2/(4096π)`, now for adaptive
algorithms: the released adaptive protocols `SparseLinearSystems.Protocol.Tree` (fresh
measured runs with classical branching on the outcomes, uniformly random trial labels and
repeated trials, a heralded final output), with every oracle label admissible for the hard
data (`Access.Admissible`), success probability at least `2/3` on every input and
conditional output `ε`-accurate in trace distance (`DensityAccurate`). The count is the
worst-case weighted number of calls over all transcripts, `T.worstCost w`.

* `main_max_tree`: max form (the three terms are witnessed by different families).
* `main_exists_tree`: family form — one of the three hard families, chosen by the
  parameters, forces every accurate adaptive algorithm (any workspace, flag, output, garbage
  and label types) to have worst-case cost at least `c₀ (√s τ + √(sτr) + r)`.
* `main_max_programs`: non-adaptive programs with admissible labels (unit seeds,
  finite-dimensional workspaces) as the special case of one fresh trial with no test runs
  (`Single.tree`); this covers controlled native calls in non-adaptive programs.
* `main_max_spec_programs`: the released non-adaptive theorem in spectator form, with the
  count `labelCount .value` (`cost_valueWeight`), for unit seeds, an isometric readout also
  for the precision family and spectator types in `Type`.
-/

namespace AdaptiveHamiltonianLowerBound

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct
open SparseHamiltonian SparseLinearSystems.Protocol ContinuousLinearMap
open LinearSystemLowerBound SparseLowerBounds SparseLowerBounds.Readout
open SparseLowerBounds.Hamiltonian NativeSparseBlockEncoding

-- The nested spaces over the search index exceed the default instance size.
set_option synthInstance.maxSize 1024

universe uK uF uE uG uL

variable {τ ε : ℝ} {s : ℕ}

/-- **Theorem `hsl:thm:main` for adaptive algorithms, eq. `hsl:eq:main`, max form**: for any
three adaptive algorithms with admissible labels, accurate on the time, mixed and precision
families respectively,
`c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, `c₀ = log 2/(4096π)`, where `Q` is the
worst-case weighted number of calls. -/
theorem main_max_tree (h : HSRange τ s ε)
    {KT FT ET GT LT KM FM EM GM LM KP FP EP GP LP : Type*}
    [NormedAddCommGroup KT] [InnerProductSpace ℂ KT] [CompleteSpace KT]
    [NormedAddCommGroup FT] [InnerProductSpace ℂ FT] [CompleteSpace FT]
    [NormedAddCommGroup ET] [InnerProductSpace ℂ ET] [CompleteSpace ET] [FiniteDimensional ℂ ET]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup KM] [InnerProductSpace ℂ KM] [CompleteSpace KM]
    [NormedAddCommGroup FM] [InnerProductSpace ℂ FM] [CompleteSpace FM]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup KP] [InnerProductSpace ℂ KP] [CompleteSpace KP]
    [NormedAddCommGroup FP] [InnerProductSpace ℂ FP] [CompleteSpace FP]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (OT : LT → (Fin (timeN τ) → Fin (2 ^ hsMu s)) → KT →L[ℂ] KT) (wT : LT → ℕ)
    (hOT : ∀ l, Access.Admissible (timeData τ s h.s_ge) (OT l) (wT l)) (TT : Tree OT FT ET)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ TT.successMass j)
    (haccT : ∀ j, DensityAccurate eT (TT.conditionalDensity j)
      (evolve ((timeData τ s h.s_ge).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (OM : LM → (Fin (precN τ ε) → Fin (2 ^ hsMu s)) → KM →L[ℂ] KM) (wM : LM → ℕ)
    (hOM : ∀ l, Access.Admissible (mixedMainData τ ε s h.s_ge) (OM l) (wM l))
    (TM : Tree OM FM EM)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (hsuccM : ∀ j, 2 / 3 ≤ TM.successMass j)
    (haccM : ∀ j, DensityAccurate eM (TM.conditionalDensity j)
      (evolve ((mixedMainData τ ε s h.s_ge).matrix j) τ (searchInput (precN τ ε) (hsMu s) s))
      ε)
    (OP : LP → (Fin (precN τ ε) → Bool) → KP →L[ℂ] KP) (wP : LP → ℕ)
    (hOP : ∀ l, Access.Admissible (precisionMainData τ ε s h.s_ge) (OP l) (wP l))
    (TP : Tree OP FP EP)
    (eP : EP →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP) (heP : eP† ∘L eP = 1)
    (hsuccP : ∀ x, 2 / 3 ≤ TP.successMass x)
    (haccP : ∀ x, DensityAccurate eP (TP.conditionalDensity x)
      (evolve ((precisionMainData τ ε s h.s_ge).matrix x) τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (TT.worstCost wT : ℝ) (max (TM.worstCost wM : ℝ) (TP.worstCost wP)) :=
  assembly h (time_tree h OT wT hOT TT eT heT hsuccT haccT)
    (fun hL => precision_tree h hL OP wP hOP TP eP heP hsuccP haccP)
    (fun hL hs => mixed_tree h hL hs OM wM hOM TM eM heM hsuccM haccM)

/-- **Theorem `hsl:thm:main` for adaptive algorithms, family form**: for every parameter
triple, one of the three hard families (time, mixed or precision, chosen by the parameters)
forces **every** adaptive algorithm with admissible labels, success probability at least
`2/3` and conditional accuracy `ε` (any workspace `K`, flag space `F`, finite-dimensional
output space `E`, garbage `G` and label type `L` in the given universes) to have worst-case
cost at least `c₀ (√s τ + √(sτr) + r)`. -/
theorem main_exists_tree (h : HSRange τ s ε) :
    (∀ (K : Type uK) (F : Type uF) (E : Type uE) (G : Type uG) (L : Type uL)
        [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
        [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
        [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
        [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
        (O : L → (Fin (timeN τ) → Fin (2 ^ hsMu s)) → K →L[ℂ] K) (w : L → ℕ),
        (∀ l, Access.Admissible (timeData τ s h.s_ge) (O l) (w l)) →
        ∀ (T : Tree O F E) (e : E →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) G),
        e† ∘L e = 1 → (∀ j, 2 / 3 ≤ T.successMass j) →
        (∀ j, DensityAccurate e (T.conditionalDensity j)
          (evolve ((timeData τ s h.s_ge).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε) →
        c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ T.worstCost w) ∨
    (∀ (K : Type uK) (F : Type uF) (E : Type uE) (G : Type uG) (L : Type uL)
        [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
        [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
        [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
        [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
        (O : L → (Fin (precN τ ε) → Fin (2 ^ hsMu s)) → K →L[ℂ] K) (w : L → ℕ),
        (∀ l, Access.Admissible (mixedMainData τ ε s h.s_ge) (O l) (w l)) →
        ∀ (T : Tree O F E) (e : E →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) G),
        e† ∘L e = 1 → (∀ j, 2 / 3 ≤ T.successMass j) →
        (∀ j, DensityAccurate e (T.conditionalDensity j)
          (evolve ((mixedMainData τ ε s h.s_ge).matrix j) τ
            (searchInput (precN τ ε) (hsMu s) s)) ε) →
        c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ T.worstCost w) ∨
    (∀ (K : Type uK) (F : Type uF) (E : Type uE) (G : Type uG) (L : Type uL)
        [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
        [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
        [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
        [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
        (O : L → (Fin (precN τ ε) → Bool) → K →L[ℂ] K) (w : L → ℕ),
        (∀ l, Access.Admissible (precisionMainData τ ε s h.s_ge) (O l) (w l)) →
        ∀ (T : Tree O F E) (e : E →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) G),
        e† ∘L e = 1 → (∀ x, 2 / 3 ≤ T.successMass x) →
        (∀ x, DensityAccurate e (T.conditionalDensity x)
          (evolve ((precisionMainData τ ε s h.s_ge).matrix x) τ (scalarInput (precN τ ε) s)) ε) →
        c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ T.worstCost w) := by
  by_contra hneg
  push Not at hneg
  obtain ⟨⟨KT, FT, ET, GT, LT, _, _, _, _, _, _, _, _, _, _, _, _, _, OT, wT, hOT, TT, eT, heT,
      hsuccT, haccT, hT⟩,
    ⟨KM, FM, EM, GM, LM, _, _, _, _, _, _, _, _, _, _, _, _, _, OM, wM, hOM, TM, eM, heM,
      hsuccM, haccM, hM⟩,
    ⟨KP, FP, EP, GP, LP, _, _, _, _, _, _, _, _, _, _, _, _, _, OP, wP, hOP, TP, eP, heP,
      hsuccP, haccP, hP⟩⟩ := hneg
  have hmax := main_max_tree h OT wT hOT TT eT heT hsuccT haccT OM wM hOM TM eM heM hsuccM
    haccM OP wP hOP TP eP heP hsuccP haccP
  have := max_lt hT (max_lt hM hP)
  linarith

/-! ### The non-adaptive theorem as a special case -/

/-- **Non-adaptive algorithms with admissible labels** (unit seeds, finite-dimensional
workspaces): each program is the adaptive protocol `Single.tree` with one fresh trial and no
test runs, which succeeds with probability one and outputs the pure final state; the bound
holds for the weighted cost `p.cost w`. This covers controlled, masked and coherently
selected native calls in non-adaptive programs. -/
theorem main_max_programs (h : HSRange τ s ε)
    {KT GT LT KM GM LM KP GP LP : Type*}
    [NormedAddCommGroup KT] [InnerProductSpace ℂ KT] [CompleteSpace KT] [FiniteDimensional ℂ KT]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup KM] [InnerProductSpace ℂ KM] [CompleteSpace KM] [FiniteDimensional ℂ KM]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup KP] [InnerProductSpace ℂ KP] [CompleteSpace KP] [FiniteDimensional ℂ KP]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (OT : LT → (Fin (timeN τ) → Fin (2 ^ hsMu s)) → KT →L[ℂ] KT) (wT : LT → ℕ)
    (hOT : ∀ l, Access.Admissible (timeData τ s h.s_ge) (OT l) (wT l))
    (pT : MultiOracleCircuit.Program OT) (φT : KT) (hφT : ‖φT‖ = 1)
    (eT : KT →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (haccT : ∀ j, Accurate eT (pT.eval j φT)
      (evolve ((timeData τ s h.s_ge).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (OM : LM → (Fin (precN τ ε) → Fin (2 ^ hsMu s)) → KM →L[ℂ] KM) (wM : LM → ℕ)
    (hOM : ∀ l, Access.Admissible (mixedMainData τ ε s h.s_ge) (OM l) (wM l))
    (pM : MultiOracleCircuit.Program OM) (φM : KM) (hφM : ‖φM‖ = 1)
    (eM : KM →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (haccM : ∀ j, Accurate eM (pM.eval j φM)
      (evolve ((mixedMainData τ ε s h.s_ge).matrix j) τ (searchInput (precN τ ε) (hsMu s) s))
      ε)
    (OP : LP → (Fin (precN τ ε) → Bool) → KP →L[ℂ] KP) (wP : LP → ℕ)
    (hOP : ∀ l, Access.Admissible (precisionMainData τ ε s h.s_ge) (OP l) (wP l))
    (pP : MultiOracleCircuit.Program OP) (φP : KP) (hφP : ‖φP‖ = 1)
    (eP : KP →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP) (heP : eP† ∘L eP = 1)
    (haccP : ∀ x, Accurate eP (pP.eval x φP)
      (evolve ((precisionMainData τ ε s h.s_ge).matrix x) τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (pT.cost wT : ℝ) (max (pM.cost wM : ℝ) (pP.cost wP)) := by
  have hUT := fun j => pT.eval_unitary (fun l x => Access.admissible_unitary _ _ _ (hOT l) x) j
  have hUM := fun j => pM.eval_unitary (fun l x => Access.admissible_unitary _ _ _ (hOM l) x) j
  have hUP := fun x => pP.eval_unitary (fun l x => Access.admissible_unitary _ _ _ (hOP l) x) x
  have key := main_max_tree h OT wT hOT (Single.tree ℂ pT φT hφT) eT heT
    (fun j => by rw [Single.successMass_tree pT φT hφT j (hUT j)]; norm_num)
    (fun j => by
      rw [Single.conditionalDensity_tree pT φT hφT j (hUT j), densityAccurate_pure_iff]
      exact haccT j)
    OM wM hOM (Single.tree ℂ pM φM hφM) eM heM
    (fun j => by rw [Single.successMass_tree pM φM hφM j (hUM j)]; norm_num)
    (fun j => by
      rw [Single.conditionalDensity_tree pM φM hφM j (hUM j), densityAccurate_pure_iff]
      exact haccM j)
    OP wP hOP (Single.tree ℂ pP φP hφP) eP heP
    (fun x => by rw [Single.successMass_tree pP φP hφP x (hUP x)]; norm_num)
    (fun x => by
      rw [Single.conditionalDensity_tree pP φP hφP x (hUP x), densityAccurate_pure_iff]
      exact haccP x)
  rwa [Single.worstCost_tree, Single.worstCost_tree, Single.worstCost_tree] at key

/-- Weighting the native labels by `valueWeight` counts value queries. -/
theorem cost_valueWeight {X K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {O : Query → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O) :
    p.cost Access.valueWeight = p.labelCount .value := by
  unfold MultiOracleCircuit.Program.labelCount
  congr 1
  funext q
  exact Access.valueWeight_eq q

/-- **The released non-adaptive Theorem `hsl:thm:main` as a special case** (spectator form):
the labels `specOracles Ω D` are admissible with `valueWeight`
(`Access.admissible_specOracles`), whose weighted cost is the number of value queries
`labelCount .value`. Compared with `SparseLowerBounds.Hamiltonian.main_max`, the seeds are
unit vectors (not of norm at most one), the precision readout is an isometry as well, and the
spectator types are in `Type`. -/
theorem main_max_spec_programs (h : HSRange τ s ε) (ΩT ΩM ΩP : Type)
    [Fintype ΩT] [Fintype ΩM] [Fintype ΩP] {GT GM GP : Type*}
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (pT : MultiOracleCircuit.Program (specOracles ΩT (timeData τ s h.s_ge)))
    (φT : Joint ΩT (SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ)) (hφT : ‖φT‖ = 1)
    (eT : Joint ΩT (SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ) →L[ℂ]
      SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (haccT : ∀ j, Accurate eT (pT.eval j φT)
      (evolve ((timeData τ s h.s_ge).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (pM : MultiOracleCircuit.Program (specOracles ΩM (mixedMainData τ ε s h.s_ge)))
    (φM : Joint ΩM (SearchSpace (precN τ ε) (hsMu s) s 1 τ)) (hφM : ‖φM‖ = 1)
    (eM : Joint ΩM (SearchSpace (precN τ ε) (hsMu s) s 1 τ) →L[ℂ]
      SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (haccM : ∀ j, Accurate eM (pM.eval j φM)
      (evolve ((mixedMainData τ ε s h.s_ge).matrix j) τ (searchInput (precN τ ε) (hsMu s) s))
      ε)
    (pP : MultiOracleCircuit.Program (specOracles ΩP (precisionMainData τ ε s h.s_ge)))
    (φP : Joint ΩP (ScalarSpace (precN τ ε) s τ)) (hφP : ‖φP‖ = 1)
    (eP : Joint ΩP (ScalarSpace (precN τ ε) s τ) →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP)
    (heP : eP† ∘L eP = 1)
    (haccP : ∀ x, Accurate eP (pP.eval x φP)
      (evolve ((precisionMainData τ ε s h.s_ge).matrix x) τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) := by
  have hDT := Access.hardAccess_timeData τ s h.s_ge
  have hDM := Access.hardAccess_mixedMainData τ ε s h.s_ge
  have hDP := Access.hardAccess_precisionMainData τ ε s h.s_ge
  have key := main_max_programs h _ Access.valueWeight
    (Access.admissible_specOracles ΩT _ hDT.row_const hDT.column_const) pT φT hφT eT heT haccT
    _ Access.valueWeight (Access.admissible_specOracles ΩM _ hDM.row_const hDM.column_const)
    pM φM hφM eM heM haccM
    _ Access.valueWeight (Access.admissible_specOracles ΩP _ hDP.row_const hDP.column_const)
    pP φP hφP eP heP haccP
  rwa [cost_valueWeight, cost_valueWeight, cost_valueWeight] at key

end

end AdaptiveHamiltonianLowerBound
