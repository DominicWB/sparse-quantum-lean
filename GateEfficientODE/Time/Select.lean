import GateEfficientODE.Time.Input
import GateEfficientODE.Analysis.Select
import TimeDependentODE.LCHS.Products
import TimeDependentODE.Continuous.Discretisation

/-!
# The coherent time-dependent selection

The source label `s` starts at slot `start s` (`0` for the initial label,
`q` for the forcing label `(true, q)`), and its slot durations are
`dur s r = (T / 2^m) · mask (start s) r`.  The branch of the joint label
`z = (s, w)` is the ordered product of the slot evolutions
`exp (-i dur s r (H_r + k_w L_r))` for the represented samples `H_r, L_r`
and the LCHS node `k_w` (`branchU`), the product family
`TimeDependentODE.GaussianLCHS.productFamily` at the real node `k_w`.  With
the common time `tau = T (λH + R λD)` and step `w = tau / 2^m`, the slot
evolution is `exp (-i w H_{z,r})` for the normalised slot Hamiltonian
`H_{z,r} = (T mask / tau)(H_r + k_w L_r)` of norm at most one (`branchH`).

`SelectHypT` collects the hypotheses on the supplied unitaries: the clock
promises of the released simulator at every label and slot (`ClockPromise`),
for the slot-selected private operation `D z r` and `H_{z,r}`.  Under them
the embedded slot-selected simulator is within `ν` of the direct sum of the
branch evolutions on the clean branch space (`select_error`).
-/

namespace SparseHamiltonian.GateODE.Time

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire anc_injective iota0 io io_apply stepW)
open GatePointerEncoding (wordValue wordValue_lt_pow)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

namespace TParams

variable (p : TParams)

theorem nu_pos (hg : 1 ≤ p.g) (hε : 0 < p.ε) : 0 < p.nu :=
  ImprovedODEQueryBudget.precision_pos p.ratio p.acc (p.ratio_ge hg) (p.acc_pos hε)

theorem nu_le_one (hg : 1 ≤ p.g) (hεOne : p.ε ≤ 1) : p.nu ≤ 1 := by
  have hr : 1 ≤ p.ratio := p.ratio_ge hg
  have h : p.acc ≤ 10000 * p.ratio := by
    have := p.acc_le_one hεOne
    linarith
  show p.acc / (10000 * p.ratio) ≤ 1
  rw [div_le_one (by linarith)]
  exact h

/-- The start slot of a source label. -/
def start (s : Bool × (Fin p.m → Bool)) : ℕ := if s.1 then wordValue s.2 else 0

/-- The slot durations of a source label. -/
def dur (s : Bool × (Fin p.m → Bool)) (r : ℕ) : ℝ :=
  p.T / p.M * TimeDependentODE.mask (p.start s) r

/-- The normalised slot Hamiltonian of the joint label `z` at slot `r`. -/
def branchH (Hs Ls : ℕ → P →L[ℂ] P) (z : Label p.m p.l) (r : ℕ) : P →L[ℂ] P :=
  ((p.T * TimeDependentODE.mask (p.start z.1) r / p.tau : ℝ) : ℂ) •
    (Hs r + ((p.nodeW z.2 : ℝ) : ℂ) • Ls r)

/-- The evolution of the branch with source label `s` and LCHS word `w`. -/
def branchU (Hs Ls : ℕ → P →L[ℂ] P) (s : Bool × (Fin p.m → Bool)) (w : Fin p.l → Bool) :
    P →L[ℂ] P :=
  TimeDependentODE.GaussianLCHS.productFamily Hs Ls (p.dur s) p.M (p.nodeW w : ℂ)

theorem mask_le_one (q r : ℕ) : TimeDependentODE.mask q r ≤ 1 := by
  unfold TimeDependentODE.mask
  split_ifs <;> norm_num

theorem dur_nonneg (hT : 0 ≤ p.T) (s : Bool × (Fin p.m → Bool)) (r : ℕ) : 0 ≤ p.dur s r :=
  mul_nonneg (div_nonneg hT (Nat.cast_nonneg _)) (TimeDependentODE.mask_nonneg _ _)

theorem dur_le (hT : 0 ≤ p.T) (s : Bool × (Fin p.m → Bool)) (r : ℕ) : p.dur s r ≤ p.T / p.M := by
  unfold dur
  calc p.T / p.M * TimeDependentODE.mask (p.start s) r ≤ p.T / p.M * 1 :=
        mul_le_mul_of_nonneg_left (mask_le_one _ _) (div_nonneg hT (Nat.cast_nonneg _))
    _ = p.T / p.M := mul_one _

theorem branchH_selfAdjoint (Hs Ls : ℕ → P →L[ℂ] P) (z : Label p.m p.l) (r : ℕ)
    (hH : star (Hs r) = Hs r) (hL : star (Ls r) = Ls r) :
    star (p.branchH Hs Ls z r) = p.branchH Hs Ls z r := by
  unfold branchH
  rw [star_smul, star_add, star_smul, hH, hL]
  simp [Complex.conj_ofReal]

omit [CompleteSpace P] in
theorem branchH_norm_le (hT : 0 ≤ p.T) (hτ : 0 < p.tau) (hg : 1 ≤ p.g) (hε : 0 < p.ε)
    (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD) (Hs Ls : ℕ → P →L[ℂ] P) (z : Label p.m p.l)
    (r : ℕ) (hHn : ‖Hs r‖ ≤ p.lamH) (hLn : ‖Ls r‖ ≤ p.lamD) : ‖p.branchH Hs Ls z r‖ ≤ 1 := by
  have hR := p.nodeW_abs_le hg hε hεOne hTD z.2
  have hX : ‖Hs r + ((p.nodeW z.2 : ℝ) : ℂ) • Ls r‖ ≤ p.lamH + p.R * p.lamD := by
    calc ‖Hs r + ((p.nodeW z.2 : ℝ) : ℂ) • Ls r‖ ≤ ‖Hs r‖ + |p.nodeW z.2| * ‖Ls r‖ := by
          refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ p.lamH + p.R * p.lamD := add_le_add hHn
          (mul_le_mul hR hLn (norm_nonneg _) ((abs_nonneg _).trans hR))
  have hm0 := TimeDependentODE.mask_nonneg (p.start z.1) r
  have hm1 := mask_le_one (p.start z.1) r
  have hc0 : 0 ≤ p.T * TimeDependentODE.mask (p.start z.1) r / p.tau :=
    div_nonneg (mul_nonneg hT hm0) hτ.le
  unfold branchH
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
  have hsum : 0 ≤ p.lamH + p.R * p.lamD := (norm_nonneg _).trans hX
  calc p.T * TimeDependentODE.mask (p.start z.1) r / p.tau *
        ‖Hs r + ((p.nodeW z.2 : ℝ) : ℂ) • Ls r‖ ≤ p.T / p.tau * (p.lamH + p.R * p.lamD) := by
        apply mul_le_mul _ hX (norm_nonneg _) (div_nonneg hT hτ.le)
        apply div_le_div_of_nonneg_right _ hτ.le
        calc p.T * TimeDependentODE.mask (p.start z.1) r ≤ p.T * 1 :=
              mul_le_mul_of_nonneg_left hm1 hT
          _ = p.T := mul_one _
    _ = 1 := by
        rw [div_mul_eq_mul_div]
        exact div_self hτ.ne'

omit [CompleteSpace P] in
/-- The slot exponential of the normalised Hamiltonian is the LCHS slot
evolution. -/
theorem exp_branchH (hτ : 0 < p.tau) (Hs Ls : ℕ → P →L[ℂ] P) (z : Label p.m p.l) (r : ℕ) :
    NormedSpace.exp ((-Complex.I * (stepW p.tau p.m : ℂ)) • p.branchH Hs Ls z r) =
      ODEWeightedLCHS.evolution (Ls r) (Hs r) (p.dur z.1 r) (p.nodeW z.2) := by
  have hτ0 : p.tau ≠ 0 := hτ.ne'
  have hreal : stepW p.tau p.m * (p.T * TimeDependentODE.mask (p.start z.1) r / p.tau) =
      p.T / p.M * TimeDependentODE.mask (p.start z.1) r := by
    unfold stepW
    calc p.tau / ((2 ^ p.m : ℕ) : ℝ) * (p.T * TimeDependentODE.mask (p.start z.1) r / p.tau) =
        p.T * TimeDependentODE.mask (p.start z.1) r * (p.tau / p.tau) / ((2 ^ p.m : ℕ) : ℝ) := by
          ring
      _ = p.T / p.M * TimeDependentODE.mask (p.start z.1) r := by
          rw [div_self hτ0]
          ring
  unfold branchH ODEWeightedLCHS.evolution dur
  rw [smul_smul, mul_assoc, ← Complex.ofReal_mul, hreal]

omit [CompleteSpace P] in
/-- The ordered product of the slot exponentials is the branch evolution. -/
theorem evolution_branchH (hτ : 0 < p.tau) (Hs Ls : ℕ → P →L[ℂ] P) (z : Label p.m p.l) :
    TimeDependent.evolution
        (fun r => NormedSpace.exp ((-Complex.I * (stepW p.tau p.m : ℂ)) • p.branchH Hs Ls z r))
        (2 ^ p.m) = p.branchU Hs Ls z.1 z.2 := by
  unfold branchU
  rw [TimeDependentODE.GaussianLCHS.productFamily_ofReal]
  congr 1
  funext r
  exact p.exp_branchH hτ Hs Ls z r

/-- Uniform clock promises: one endpoint bound `sqrt (qbar / 2)` serves every
slot. -/
theorem clock_family (UJ : Anc p.a P →L[ℂ] Anc p.a P) (D : ℕ → Anc p.a P →L[ℂ] Anc p.a P)
    (H : ℕ → P →L[ℂ] P)
    (hC : ∀ r < p.M, ClockPromise UJ (D r) (H r) p.Q p.qbar) :
    ∃ R1 : ℕ → Anc p.a P →L[ℂ] Anc p.a P, ∀ r < p.M,
      (1 - D r) ∘L R1 r = 1 ∧ R1 r ∘L (1 - D r) = 1 ∧ ‖R1 r‖ ≤ p.Q ∧
      (UJ ∘L iota0)† ∘L R1 r ∘L (UJ ∘L iota0) = (2 : ℂ)⁻¹ • (1 + Complex.I • H r) ∧
      ‖R1 r ∘L (UJ ∘L iota0)‖ ≤ Real.sqrt (p.qbar / 2) := by
  have h : ∀ r, r < p.M → ∃ (R1 : Anc p.a P →L[ℂ] Anc p.a P) (b : ℝ),
      (1 - D r) ∘L R1 = 1 ∧ R1 ∘L (1 - D r) = 1 ∧ ‖R1‖ ≤ p.Q ∧
      (UJ ∘L iota0)† ∘L R1 ∘L (UJ ∘L iota0) = (2 : ℂ)⁻¹ • (1 + Complex.I • H r) ∧
      ‖R1 ∘L (UJ ∘L iota0)‖ ≤ b ∧ b ^ 2 ≤ p.qbar / 2 := fun r hr => (hC r hr).promise
  choose R1 b hR using h
  refine ⟨fun r => if hr : r < p.M then R1 r hr else 0, fun r hr => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hR r hr
  simp only [dif_pos hr]
  exact ⟨h1, h2, h3, h4, h5.trans ((le_abs_self _).trans (Real.abs_le_sqrt h6))⟩

/-- The hypotheses on the supplied unitaries and the represented samples. -/
structure SelectHypT (σ : TOracles p.a p.m p.l P) (Hs Ls : ℕ → P →L[ℂ] P) : Prop where
  uj : IsUnitary σ.UJ
  priv : ∀ z, ∀ r < p.M, IsUnitary (σ.D z r)
  selfH : ∀ r < p.M, star (Hs r) = Hs r
  selfL : ∀ r < p.M, star (Ls r) = Ls r
  normH : ∀ r < p.M, ‖Hs r‖ ≤ p.lamH
  normL : ∀ r < p.M, ‖Ls r‖ ≤ p.lamD
  clock : ∀ z, ∀ r < p.M, ClockPromise σ.UJ (σ.D z r) (p.branchH Hs Ls z r) p.Q p.qbar

/-- The slot-selected simulator for one label, with its clean column. -/
theorem branch_block (hT : 0 ≤ p.T) (hτ : 0 < p.tau) (hg : 1 ≤ p.g) (hε : 0 < p.ε)
    (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD) (hQ : 1 ≤ p.Q) (hq : 0 ≤ p.qbar)
    (hqQ : p.qbar ≤ p.Q) (hm : TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m)
    (σ : TOracles p.a p.m p.l P) (Hs Ls : ℕ → P →L[ℂ] P) (hS : p.SelectHypT σ Hs Ls)
    (z : Label p.m p.l) :
    ‖SlotSim.runT (m := p.m) (r := p.r) (K := p.K) σ.UJ (σ.D z)
        (SlotSim.simCircuitT p.a p.tau p.Q p.qbar p.nu p.m) ∘L
        basL (W := Wire p.a p.m p.r p.K) (Q := P) (fun _ => false) -
      basL (fun _ => false) ∘L p.branchU Hs Ls z.1 z.2‖ ≤ p.nu := by
  obtain ⟨R1, hR1⟩ := p.clock_family σ.UJ (σ.D z) (p.branchH Hs Ls z) (hS.clock z)
  have hν : 0 < p.nu := p.nu_pos hg hε
  have hν1 : p.nu ≤ 1 := p.nu_le_one hg hεOne
  have hb : Real.sqrt (p.qbar / 2) ^ 2 ≤ p.qbar / 2 := by
    rw [Real.sq_sqrt (by linarith)]
  have hsim := SlotSim.simulationT (P := P) p.a p.m σ.UJ (σ.D z) R1 (p.branchH Hs Ls z) hS.uj
    (hS.priv z) p.tau p.Q (Real.sqrt (p.qbar / 2)) p.qbar p.nu hτ.le hQ
    (fun r hr => (hR1 r hr).1) (fun r hr => (hR1 r hr).2.1) (fun r hr => (hR1 r hr).2.2.1)
    (fun r hr => (hR1 r hr).2.2.2.1)
    (fun r hr => p.branchH_selfAdjoint Hs Ls z r (hS.selfH r hr) (hS.selfL r hr))
    (fun r hr => p.branchH_norm_le hT hτ hg hε hεOne hTD Hs Ls z r (hS.normH r hr)
      (hS.normL r hr))
    (fun r hr => (hR1 r hr).2.2.2.2) hb hqQ hν hν1 hm
  have hfin := hsim.2.2.2.2.2.1
  rw [p.evolution_branchH hτ Hs Ls z] at hfin
  have hio : basL (W := Wire p.a p.m p.r p.K) (Q := P) (fun _ => false) = io := by
    refine ContinuousLinearMap.ext (fun ψ => ?_)
    rw [basL_apply, io_apply]
  rw [hio]
  convert hfin using 4

/-- The block estimate for an arbitrary embedded simulator circuit. -/
theorem select_error_of_blocks (v : P) (σ : TOracles p.a p.m p.l P)
    (gs : List (Instr (Wire p.a p.m p.r p.K))) (U : Label p.m p.l → P →L[ℂ] P) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hblock : ∀ z, ‖SlotSim.runT σ.UJ (σ.D z) gs ∘L
        basL (W := Wire p.a p.m p.r p.K) (Q := P) (fun _ => false) -
      basL (fun _ => false) ∘L U z‖ ≤ ε) :
    ‖trun v σ (gs.map (embI (O := OWire p.m p.l p.f))) ∘L p.branchE -
        p.branchE ∘L WeightedClock.diagonal U‖ ≤ ε := by
  rw [trun_map_embI]
  apply localOp_branch_error Sum.inl_injective _ cfgOf (fun _ _ => rfl)
    outPart_cfgOf_injective _ ε hε
  intro z
  have hlab : labAt (clearCfg Sum.inl (cfgOf (a := p.a) (m := p.m) (r := p.r) (K := p.K)
      (k := p.m) (l := p.l) (f := p.f) z)) = z := by
    have h : ∀ o : OWire p.m p.l p.f,
        clearCfg (Sum.inl : Wire p.a p.m p.r p.K → p.W) (cfgOf z) (Sum.inr o) =
          cfgOf z (Sum.inr o) :=
      fun o => overwrite_apply_out Sum.inl _ _ _ (fun s h => by cases h)
    unfold labAt
    simp only [h]
    rfl
  rw [hlab]
  exact hblock z

/-- **The coherent time-dependent selection is within `ν` of the direct sum
of branch evolutions on the clean branch space.** -/
theorem select_error (hT : 0 ≤ p.T) (hτ : 0 < p.tau) (hg : 1 ≤ p.g) (hε : 0 < p.ε)
    (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD) (hQ : 1 ≤ p.Q) (hq : 0 ≤ p.qbar)
    (hqQ : p.qbar ≤ p.Q) (hm : TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m) (v : P)
    (σ : TOracles p.a p.m p.l P) (Hs Ls : ℕ → P →L[ℂ] P) (hS : p.SelectHypT σ Hs Ls) :
    ‖trun v σ p.select ∘L p.branchE -
        p.branchE ∘L WeightedClock.diagonal (fun z => p.branchU Hs Ls z.1 z.2)‖ ≤ p.nu := by
  have h := p.select_error_of_blocks v σ (SlotSim.simCircuitT p.a p.tau p.Q p.qbar p.nu p.m)
    (fun z => p.branchU Hs Ls z.1 z.2) p.nu (p.nu_pos hg hε).le
    (fun z => p.branch_block hT hτ hg hε hεOne hTD hQ hq hqQ hm σ Hs Ls hS z)
  rw [select]
  convert h using 3

end TParams

end

end SparseHamiltonian.GateODE.Time
