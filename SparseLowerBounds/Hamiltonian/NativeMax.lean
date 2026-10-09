import SparseLowerBounds.Hamiltonian.Theorem

set_option synthInstance.maxHeartbeats 400000

/-!
# Theorem `hsl:thm:main` without a spectator register

`main_max` is stated for programs over the native primitives acting on every copy of an
untouched spectator register (`specOracles`).  This module states the same combined bound for
programs over the bare native primitives (`oracles`): it is assembled from the per-family
bounds `time_main_native`, `mixed_main_native` and `precision_main_native` by `assembly`,
exactly as `main_max` is assembled from the spectator forms.
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Readout
open scoped Matrix InnerProduct InnerProductSpace

-- The nested spaces over the search index exceed the default instance size.
set_option synthInstance.maxSize 1024

variable {τ ε : ℝ} {s : ℕ}

/-- **Theorem `hsl:thm:main`, eq. `hsl:eq:main`, without a spectator register**: for any three
programs over the native primitives of the time, mixed and precision families, each
`ε`-accurate on its own family, `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)` with
`c₀ = log 2/(4096π)` (`main_max` is the spectator form). -/
theorem main_max_native (h : HSRange τ s ε) {GT GM GP : Type*}
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (pT : MultiOracleCircuit.Program (oracles (timeData τ s h.s_ge)))
    (φT : SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ) (hφT : ‖φT‖ ≤ 1)
    (eT : SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ →L[ℂ]
      SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (haccT : ∀ j, Accurate eT (pT.eval j φT)
      (evolve ((timeData τ s h.s_ge).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (pM : MultiOracleCircuit.Program (oracles (mixedMainData τ ε s h.s_ge)))
    (φM : SearchSpace (precN τ ε) (hsMu s) s 1 τ) (hφM : ‖φM‖ ≤ 1)
    (eM : SearchSpace (precN τ ε) (hsMu s) s 1 τ →L[ℂ]
      SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (haccM : ∀ j, Accurate eM (pM.eval j φM)
      (evolve ((mixedMainData τ ε s h.s_ge).matrix j) τ (searchInput (precN τ ε) (hsMu s) s)) ε)
    (pP : MultiOracleCircuit.Program (oracles (precisionMainData τ ε s h.s_ge)))
    (φP : ScalarSpace (precN τ ε) s τ)
    (eP : ScalarSpace (precN τ ε) s τ →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP)
    (haccP : ∀ x, Accurate eP (pP.eval x φP)
      (evolve ((precisionMainData τ ε s h.s_ge).matrix x) τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) := by
  refine assembly h (time_main_native h pT φT hφT eT heT haccT).1 (fun hL => ?_)
    (fun hL hs => ?_)
  · have := precision_main_native h hL pP φP eP haccP
    exact ⟨this.1, this.2.2⟩
  · exact (mixed_main_native h hL hs pM φM hφM eM heM haccM).1

end

end SparseLowerBounds.Hamiltonian
