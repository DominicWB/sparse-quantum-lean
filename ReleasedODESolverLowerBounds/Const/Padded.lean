import ReleasedODESolverLowerBounds.Const.Corollaries

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Padded forms of the ODE lower bounds for measured solvers over the constant-coefficient oracle

Manuscript Section `odel:sec:main` ("the lower bounds apply to the upper bounds of the preceding
section"), with measurements inside a run (proof of Lemma `hsl:lem:precision`): the padding claims
for the `g = 1` families (the end of the proof of Theorem `hsl:thm:main`, "Further known zero
padding equalises dimensions or accommodates a qubit register"; proof of Theorem
`odel:thm:combined`, "Pad dimensions to a common known size if desired"), over the physical oracle
of the released constant-coefficient solver of Theorem `ode:thm:main` and over its call forms.

Every statement is the corresponding statement of `PhysicalODELowerBound.Const` with
`MeasuredConstWitnesses` in place of `ConstWitnesses`
(`measuredConstWitnesses_of_constWitnesses`), or, for the max form, with realised measured counts
(`MeasuredConstCost.exists_constCost_le`); the dimension and sparsity conjuncts, hypotheses and
constants are those of the lifted statements.
-/

namespace ReleasedODESolverLowerBounds.Const

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit
open LowerBoundRemarks.HamiltonianPadding (PadTo)
open ODELowerBoundExtensions.Padding (timePadFamilyAt mixedPadFamilyAt precisionPadFamilyAt
  SparsityAttained)

-- The released solver's physical workspace is a nested register product.
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

variable {s : ℕ} {τ gbar ε : ℝ}

/-- **The precision terms of Theorem `odel:thm:combined` for measured solvers over the
constant-coefficient physical oracle with the padded `g = 1` families**: on `HSRange` with
`ḡ ≥ 1` and any known paddings, a padded `g = 1` family witnesses `c₀ (√(sτr) + r)`. -/
theorem precision_terms_witness_pad_measured_const (h : HSRange τ s ε) (hg : 1 ≤ gbar)
    (PT PM PP : Type) [Fintype PT] [DecidableEq PT] [Fintype PM] [DecidableEq PM]
    [Fintype PP] [DecidableEq PP] :
    MeasuredConstWitnesses (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeasuredConstWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM) τ
        gbar ε (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeasuredConstWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP)
        τ gbar ε (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) :=
  (PhysicalODELowerBound.Const.precision_terms_witness_pad_const h hg PT PM PP).imp
    measuredConstWitnesses_of_constWitnesses
    (Or.imp measuredConstWitnesses_of_constWitnesses measuredConstWitnesses_of_constWitnesses)

/-- **Eq. `odel:eq:hsbound` for measured solvers over the constant-coefficient physical oracle
with the padded families, max form over realised counts.** -/
theorem herald_max_pad_measured_const (h : HSRange τ s ε) (PT PM PP : Type) [Fintype PT]
    [DecidableEq PT] [Fintype PM] [DecidableEq PM] [Fintype PP] [DecidableEq PP] {qT qM qP : ℝ}
    (hT : MeasuredConstCost (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT) ε qT)
    (hM : MeasuredConstCost (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM) ε qM)
    (hP : MeasuredConstCost (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP) ε
      qP) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ max qT (max qM qP) := by
  obtain ⟨qT', hT', hT''⟩ := hT.exists_constCost_le
  obtain ⟨qM', hM', hM''⟩ := hM.exists_constCost_le
  obtain ⟨qP', hP', hP''⟩ := hP.exists_constCost_le
  exact (PhysicalODELowerBound.Const.herald_max_cost_pad_const h PT PM PP hT' hM' hP').trans
    (max_le_max hT'' (max_le_max hM'' hP''))

/-- **Eq. `odel:eq:hsbound` in one common dimension for measured solvers over the
constant-coefficient physical oracle**: for every `Nd` at least the dimensions of the three hard
families, the time, mixed and precision families padded by `PadTo S Nd` have dimension exactly
`Nd` and maximum sparsity exactly `s`, and for any `ḡ ≥ 1` one of them witnesses
`c₀ (√s τ + √(sτr) + r)` on measured solvers. -/
theorem herald_common_dimension_measured_const (h : HSRange τ s ε) (hg : 1 ≤ gbar) (Nd : ℕ)
    (hT : Fintype.card (SearchIndex (timeN τ) (hsMu s) s) ≤ Nd)
    (hM : Fintype.card (SearchIndex (precN τ ε) (hsMu s) s) ≤ Nd)
    (hP : Fintype.card (ScalarIndex (precN τ ε) s) ≤ Nd) :
    Fintype.card (SearchIndex (timeN τ) (hsMu s) s ⊕
        PadTo (SearchIndex (timeN τ) (hsMu s) s) Nd) = Nd ∧
      Fintype.card (SearchIndex (precN τ ε) (hsMu s) s ⊕
        PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd) = Nd ∧
      Fintype.card (ScalarIndex (precN τ ε) s ⊕ PadTo (ScalarIndex (precN τ ε) s) Nd) = Nd ∧
      (SparsityAttained (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (SearchIndex (timeN τ) (hsMu s) s) Nd)) ∧
        SparsityAttained (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd)) ∧
        SparsityAttained (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (ScalarIndex (precN τ ε) s) Nd))) ∧
      (MeasuredConstWitnesses (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (SearchIndex (timeN τ) (hsMu s) s) Nd)) τ gbar ε
          (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
        MeasuredConstWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd)) τ gbar ε
          (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
        MeasuredConstWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (ScalarIndex (precN τ ε) s) Nd)) τ gbar ε
          (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    PhysicalODELowerBound.Const.herald_common_dimension_const h hg Nd hT hM hP
  exact ⟨h1, h2, h3, h4, h5.imp measuredConstWitnesses_of_constWitnesses
    (Or.imp measuredConstWitnesses_of_constWitnesses measuredConstWitnesses_of_constWitnesses)⟩

/-- **Eq. `odel:eq:hsbound` on a qubit register for measured solvers over the
constant-coefficient physical oracle**: for every `q` with `4 s (τ + r + 1) ≤ 2^q`, the time,
mixed and precision families padded by `PadTo S (2^q)` have dimension exactly `2^q` and maximum
sparsity exactly `s`, and for any `ḡ ≥ 1` one of them witnesses `c₀ (√s τ + √(sτr) + r)` on
measured solvers. -/
theorem herald_qubit_register_measured_const (h : HSRange τ s ε) (hg : 1 ≤ gbar) (q : ℕ)
    (hq : 4 * s * (τ + hsR τ ε + 1) ≤ (2 : ℝ) ^ q) :
    Fintype.card (SearchIndex (timeN τ) (hsMu s) s ⊕
        PadTo (SearchIndex (timeN τ) (hsMu s) s) (2 ^ q)) = 2 ^ q ∧
      Fintype.card (SearchIndex (precN τ ε) (hsMu s) s ⊕
        PadTo (SearchIndex (precN τ ε) (hsMu s) s) (2 ^ q)) = 2 ^ q ∧
      Fintype.card (ScalarIndex (precN τ ε) s ⊕
        PadTo (ScalarIndex (precN τ ε) s) (2 ^ q)) = 2 ^ q ∧
      (SparsityAttained (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (SearchIndex (timeN τ) (hsMu s) s) (2 ^ q))) ∧
        SparsityAttained (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) (2 ^ q))) ∧
        SparsityAttained (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (ScalarIndex (precN τ ε) s) (2 ^ q)))) ∧
      (MeasuredConstWitnesses (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (SearchIndex (timeN τ) (hsMu s) s) (2 ^ q))) τ gbar ε
          (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
        MeasuredConstWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) (2 ^ q))) τ gbar ε
          (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
        MeasuredConstWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (ScalarIndex (precN τ ε) s) (2 ^ q))) τ gbar ε
          (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    PhysicalODELowerBound.Const.herald_qubit_register_const h hg q hq
  exact ⟨h1, h2, h3, h4, h5.imp measuredConstWitnesses_of_constWitnesses
    (Or.imp measuredConstWitnesses_of_constWitnesses measuredConstWitnesses_of_constWitnesses)⟩

end

end ReleasedODESolverLowerBounds.Const
