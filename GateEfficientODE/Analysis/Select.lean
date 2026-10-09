import GateEfficientODE.Analysis.Input

/-!
# The coherent selection of the released simulator

The branch of the joint label `z = (s, w)` evolves for the duration `dur s`
with the LCHS Hamiltonian `H + k_w L` of node `k_w = nodeW w`
(`branchU = exp(-i dur (H + k_w L))`, `ODEWeightedLCHS.evolution`).  With the
common time `tau = T (λH + R λD)` it is `exp(-i tau H_z)` for the rescaled
branch Hamiltonian `H_z = (dur s / tau)(H + k_w L)`, of norm at most one.

`ClockPromise` collects the hypotheses of the released gate-level simulator
(`GateCircuit.Sim.gate_efficient_simulation`) for `U_J`, a private Cayley
operation and a Hamiltonian: the resolvent `R₁ = (1 - D)⁻¹` with `‖R₁‖ ≤ Q`,
the boundary identity `J† R₁ J = (1 + iH)/2` for `J = U_J ι₀`, and the
endpoint bound `‖R₁ J‖ ≤ b`, `b² ≤ qbar / 2`.  These are the clock promises
of Theorem `hs:thm:main`, here required for every label `z` with the
label-selected private operation `D z` and the branch Hamiltonian `H_z`.

Under them the embedded simulator is within `ν = ε / (10000 g)` of the
direct sum of the branch evolutions on the clean branch space
(`select_error`): the released full-output bound holds for every branch with
the same circuit, and the block estimate `localOp_branch_error` combines the
branches coherently.
-/

namespace SparseHamiltonian.GateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire anc_injective simCircuit simSem iota0 io io_apply
  gate_efficient_simulation)
open GatePointerEncoding (wordValue wordValue_lt_pow)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The clock promises of the released gate-level simulator for `U_J`, a
private Cayley operation `D` and a Hamiltonian `H`. -/
structure ClockPromise {a : ℕ} (UJ D : Anc a P →L[ℂ] Anc a P) (H : P →L[ℂ] P) (Q qbar : ℝ) :
    Prop where
  promise : ∃ (R1 : Anc a P →L[ℂ] Anc a P) (b : ℝ),
    (1 - D) ∘L R1 = 1 ∧ R1 ∘L (1 - D) = 1 ∧ ‖R1‖ ≤ Q ∧
    (UJ ∘L iota0)† ∘L R1 ∘L (UJ ∘L iota0) = (2 : ℂ)⁻¹ • (1 + Complex.I • H) ∧
    ‖R1 ∘L (UJ ∘L iota0)‖ ≤ b ∧ b ^ 2 ≤ qbar / 2

namespace Params

variable (p : Params)

/-- The evolution of the branch with source label `s` and LCHS word `w`. -/
def branchU (H L : P →L[ℂ] P) (s : Bool × (Fin p.k → Bool)) (w : Fin p.l → Bool) :
    P →L[ℂ] P :=
  ODEWeightedLCHS.evolution L H (p.dur s) (p.nodeW w)

/-- The rescaled branch Hamiltonian, simulated for the common time `tau`. -/
def branchH (H L : P →L[ℂ] P) (z : Label p.k p.l) : P →L[ℂ] P :=
  ((p.dur z.1 / p.tau : ℝ) : ℂ) • (H + ((p.nodeW z.2 : ℝ) : ℂ) • L)

theorem dur_nonneg (hT : 0 ≤ p.T) (s : Bool × (Fin p.k → Bool)) : 0 ≤ p.dur s := by
  unfold dur
  split_ifs
  · positivity
  · exact hT

theorem dur_le (hT : 0 ≤ p.T) (s : Bool × (Fin p.k → Bool)) : p.dur s ≤ p.T := by
  unfold dur
  split_ifs
  · have hv : (wordValue s.2 : ℝ) ≤ 2 ^ p.k := by
      have := wordValue_lt_pow s.2
      exact_mod_cast this.le
    calc (wordValue s.2 : ℝ) * (p.T / 2 ^ p.k) ≤ 2 ^ p.k * (p.T / 2 ^ p.k) :=
          mul_le_mul_of_nonneg_right hv (by positivity)
      _ = p.T := by field_simp
  · exact le_rfl

theorem branchH_selfAdjoint (H L : P →L[ℂ] P) (hH : star H = H) (hL : star L = L)
    (z : Label p.k p.l) : star (p.branchH H L z) = p.branchH H L z := by
  unfold branchH
  rw [star_smul, star_add, star_smul, hH, hL]
  simp [Complex.conj_ofReal]

omit [CompleteSpace P] in
theorem branchH_norm_le (hT : 0 ≤ p.T) (hτ : 0 < p.tau) (hg : 1 ≤ p.g) (hε : 0 < p.ε)
    (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD) (H L : P →L[ℂ] P) (hHn : ‖H‖ ≤ p.lamH)
    (hLn : ‖L‖ ≤ p.lamD) (z : Label p.k p.l) : ‖p.branchH H L z‖ ≤ 1 := by
  have hD0 : 0 ≤ p.lamD := (norm_nonneg L).trans hLn
  have hR := p.nodeW_abs_le hg hε hεOne hTD z.2
  have hX : ‖H + ((p.nodeW z.2 : ℝ) : ℂ) • L‖ ≤ p.lamH + p.R * p.lamD := by
    calc ‖H + ((p.nodeW z.2 : ℝ) : ℂ) • L‖ ≤ ‖H‖ + |p.nodeW z.2| * ‖L‖ := by
          refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ p.lamH + p.R * p.lamD := add_le_add hHn
          (mul_le_mul hR hLn (norm_nonneg _) ((abs_nonneg _).trans hR))
  have hd0 := p.dur_nonneg hT z.1
  have hd1 := p.dur_le hT z.1
  unfold branchH
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hd0 hτ.le)]
  have hsum : 0 ≤ p.lamH + p.R * p.lamD := (norm_nonneg _).trans hX
  calc p.dur z.1 / p.tau * ‖H + ((p.nodeW z.2 : ℝ) : ℂ) • L‖ ≤
        p.T / p.tau * (p.lamH + p.R * p.lamD) :=
        mul_le_mul (div_le_div_of_nonneg_right hd1 hτ.le) hX (norm_nonneg _)
          (div_nonneg hT hτ.le)
    _ = 1 := by
        rw [div_mul_eq_mul_div]
        exact div_self hτ.ne'

omit [CompleteSpace P] in
theorem exp_branchH (hτ : 0 < p.tau) (H L : P →L[ℂ] P) (z : Label p.k p.l) :
    NormedSpace.exp ((-Complex.I * (p.tau : ℂ)) • p.branchH H L z) = p.branchU H L z.1 z.2 := by
  unfold branchH branchU ODEWeightedLCHS.evolution
  rw [smul_smul]
  congr 2
  have h1 : (p.tau : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  rw [Complex.ofReal_div, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ h1]

/-- The released simulator for one label, with its clean column. -/
theorem branch_block (hT : 0 ≤ p.T) (hτ : 0 < p.tau) (hg : 1 ≤ p.g) (hε : 0 < p.ε)
    (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD) (hQ : 1 ≤ p.Q) (hqQ : p.qbar ≤ p.Q)
    (UJ D : Anc p.a P →L[ℂ] Anc p.a P) (hUJ : IsUnitary UJ) (hD : IsUnitary D)
    (H L : P →L[ℂ] P) (hH : star H = H) (hL : star L = L) (hHn : ‖H‖ ≤ p.lamH)
    (hLn : ‖L‖ ≤ p.lamD) (z : Label p.k p.l)
    (hC : ClockPromise UJ D (p.branchH H L z) p.Q p.qbar) :
    ‖GateCircuit.run (simSem UJ D) (simCircuit p.a p.tau p.Q p.qbar p.nu) ∘L
        basL (W := Wire p.a p.m p.r p.K) (Q := P) (fun _ => false) -
      basL (fun _ => false) ∘L p.branchU H L z.1 z.2‖ ≤ p.nu := by
  obtain ⟨R1, b, hRight, hLeft, hR1, hBoundary, hEndpoint, hbq⟩ := hC.promise
  have hν : 0 < p.nu := ImprovedODEQueryBudget.precision_pos p.g p.ε hg hε
  have hν1 : p.nu ≤ 1 := by
    unfold nu ImprovedODEQueryBudget.precision
    rw [div_le_one (by positivity)]
    nlinarith
  have hsim := gate_efficient_simulation p.a UJ D R1 (p.branchH H L z) hUJ hD p.tau p.Q b p.qbar
    p.nu hτ.le hQ hRight hLeft hR1 hBoundary (p.branchH_selfAdjoint H L hH hL z)
    (p.branchH_norm_le hT hτ hg hε hεOne hTD H L hHn hLn z) hEndpoint hbq hqQ hν hν1
  have hio : basL (W := Wire p.a p.m p.r p.K) (Q := P) (fun _ => false) = io := by
    refine ContinuousLinearMap.ext (fun ψ => ?_)
    rw [basL_apply, io_apply]
  obtain ⟨_, _, _, _, _, hfin, _⟩ := hsim
  rw [p.exp_branchH hτ H L z] at hfin
  rw [hio]
  convert hfin using 4

/-- The hypotheses on the supplied unitaries and the Hamiltonian parts. -/
structure SelectHyp (σ : Oracles p.a (Label p.k p.l) P) (H L : P →L[ℂ] P) : Prop where
  uj : IsUnitary σ.UJ
  priv : ∀ z, IsUnitary (σ.D z)
  selfH : star H = H
  selfL : star L = L
  normH : ‖H‖ ≤ p.lamH
  normL : ‖L‖ ≤ p.lamD
  clock : ∀ z, ClockPromise σ.UJ (σ.D z) (p.branchH H L z) p.Q p.qbar

/-- **The coherent selection is within `ν` of the direct sum of branch
evolutions on the clean branch space.** -/
theorem select_error (hT : 0 ≤ p.T) (hτ : 0 < p.tau) (hg : 1 ≤ p.g) (hε : 0 < p.ε)
    (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD) (hQ : 1 ≤ p.Q) (hqQ : p.qbar ≤ p.Q) (v : P)
    (σ : Oracles p.a (Label p.k p.l) P) (H L : P →L[ℂ] P) (hS : p.SelectHyp σ H L) :
    ‖run (wiring v) σ p.select ∘L p.branchE -
        p.branchE ∘L WeightedClock.diagonal (fun z => p.branchU H L z.1 z.2)‖ ≤ p.nu := by
  have hν : 0 < p.nu := ImprovedODEQueryBudget.precision_pos p.g p.ε hg hε
  rw [select, run_map_embI]
  apply localOp_branch_error Sum.inl_injective _ cfgOf (fun _ _ => rfl)
    outPart_cfgOf_injective _ p.nu hν.le
  intro z
  have hlab : OInstr.semAt (wiring (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k)
      (l := p.l) (f := p.f) v) σ (clearCfg Sum.inl (cfgOf z)) =
      simSem (m := p.m) (r := p.r) (K := p.K) σ.UJ (σ.D z) := by
    have h : ∀ o : OWire p.k p.l p.f,
        clearCfg (Sum.inl : Wire p.a p.m p.r p.K → p.W) (cfgOf z) (Sum.inr o) =
          cfgOf z (Sum.inr o) :=
      fun o => overwrite_apply_out Sum.inl _ _ _ (fun s h => by cases h)
    unfold OInstr.semAt
    simp only [h]
    rfl
  rw [hlab]
  have hb := p.branch_block hT hτ hg hε hεOne hTD hQ hqQ σ.UJ (σ.D z) hS.uj (hS.priv z) H L hS.selfH
    hS.selfL hS.normH hS.normL z (hS.clock z)
  convert hb using 4

end Params

end

end SparseHamiltonian.GateODE
