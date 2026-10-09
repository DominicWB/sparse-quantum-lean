import GateEfficientSelect.Lemma

/-!
# Branch-dependent meshes in the time-dependent dissipative solver

The released time-dependent solver `GateODE.Time` (Theorem `ode:thm:gates`, time-dependent
part) masks every source branch on one common mesh. Here the same public protocol is analysed
with the branch-dependent meshes of Lemma `ode:lem:gate-select`: the source label `s` starts at
the time `startB v s` (`0` for the initial labels, an arbitrary node `v q ∈ [0, T]` for the
forcing label `(true, q)`), and its branch runs for the duration `durB v s = T - startB v s` on
its own uniform mesh of `2^m` slots of length `durB v s / 2^m`, with the sample addresses
`addrB v s r = startB v s + r · durB v s / 2^m`.

* Represented samples `Hb s r`, `Lb s r` of the branch `s` at slot `r`: the slot generator is
  `L + i H` (`TimeDependentODE`'s convention, `GateODE.Time.gens`).
* The private operation of the joint label `z = (s, w)` at slot `r` carries the clock promise of
  the released simulator for the normalised slot Hamiltonian
  `branchHB v Hb Lb z r = (durB v s / τ)(Hb s r + k_w Lb s r)`, `τ = T (λH + R λD)`. One
  simulator step `τ / 2^m` is then the branch step `durB v s / 2^m`
  (`exp_branchHB`); the circuit and its boundary rotations do not depend on the branch.
* `branchUB`: the ordered product of the LCHS slot evolutions of the branch at the node `k_w`;
  `propB`: the ordered product of the dissipative slot propagators
  `exp (-(durB / 2^m)(Lb s r + i Hb s r))` of the branch (the same product family at `-i`).
* `bsW wq fv`: forcing vectors with quadrature weights in the released source format, so that the
  source vector of the forcing label `(true, q)` is `w_q f_q` (`zsrc_bsW`) and the source mass is
  `‖x(0)‖ + ∑_q w_q ‖f_q‖` (`mass_bsW`).
* `targetB`: the exact target of the circuit, `∑_s propB s (z_s)`.

`select_errorB`: under the clock promises at every label and slot, the embedded slot-selected
simulator of the released protocol is within `ν` of the direct sum of the branch evolutions
`branchUB` (the block estimate of the released `GateODE.Time.TParams.select_error_of_blocks` with
`branch_block` on every branch).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSelect.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire Vsp anc_injective iota0 io io_apply stepW)
open GateODE (Label ClockPromise basL basL_apply)
open GateODE.Time (TParams TOracles trun)
open GatePointerEncoding (wordValue wordValue_lt_pow)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]

variable (p : TParams)

/-- The start time of a source label: `0` for the initial labels and `v q` for the forcing
label `(true, q)`. -/
def startB (v : ℕ → ℝ) (s : Bool × (Fin p.m → Bool)) : ℝ :=
  if s.1 then v (wordValue s.2) else 0

/-- The duration `T - startB v s` of the branch of a source label. -/
def durB (v : ℕ → ℝ) (s : Bool × (Fin p.m → Bool)) : ℝ := p.T - startB p v s

/-- The slot length of the branch of a source label: its duration over the `2^m` slots. -/
def stepB (v : ℕ → ℝ) (s : Bool × (Fin p.m → Bool)) (_r : ℕ) : ℝ := durB p v s / p.M

/-- The sample address of slot `r` of the branch of `s`. -/
def addrB (v : ℕ → ℝ) (s : Bool × (Fin p.m → Bool)) (r : ℕ) : ℝ :=
  startB p v s + r * durB p v s / p.M

/-- The normalised slot Hamiltonian of the joint label `z = (s, w)` at slot `r`. -/
def branchHB (v : ℕ → ℝ) (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P)
    (z : Label p.m p.l) (r : ℕ) : P →L[ℂ] P :=
  ((durB p v z.1 / p.tau : ℝ) : ℂ) • (Hb z.1 r + ((p.nodeW z.2 : ℝ) : ℂ) • Lb z.1 r)

/-- The evolution of the branch with source label `s` and LCHS word `w` on its own mesh. -/
def branchUB [CompleteSpace P] (v : ℕ → ℝ) (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P)
    (s : Bool × (Fin p.m → Bool)) (w : Fin p.l → Bool) : P →L[ℂ] P :=
  TimeDependentODE.GaussianLCHS.productFamily (Hb s) (Lb s) (stepB p v s) p.M (p.nodeW w : ℂ)

/-- The dissipative propagator of the branch of `s` on its own mesh. -/
def propB [CompleteSpace P] (v : ℕ → ℝ) (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P)
    (s : Bool × (Fin p.m → Bool)) : P →L[ℂ] P :=
  TimeDependentODE.GaussianLCHS.productFamily (Hb s) (Lb s) (stepB p v s) p.M (-Complex.I)

/-- Forcing vectors with quadrature weights, in the source format of the released solver
(whose forcing label `(true, q)` carries `(T / 2^m) bs q`). -/
def bsW (wq : ℕ → ℝ) (fv : ℕ → P) (q : ℕ) : P := (((p.M / p.T) * wq q : ℝ) : ℂ) • fv q

/-- The exact target of the circuit: every branch propagator applied to its source vector. -/
def targetB [CompleteSpace P] (v : ℕ → ℝ) (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P)
    (x0 : P) (wq : ℕ → ℝ) (fv : ℕ → P) : P :=
  ∑ s, propB p v Hb Lb s (p.zsrc x0 (bsW p wq fv) s)

/-! ### Start times, durations and source vectors -/

theorem startB_mem (v : ℕ → ℝ) (hv : ∀ q < p.M, 0 ≤ v q ∧ v q ≤ p.T) (hT : 0 ≤ p.T)
    (s : Bool × (Fin p.m → Bool)) : 0 ≤ startB p v s ∧ startB p v s ≤ p.T := by
  unfold startB
  split_ifs
  · exact hv _ (wordValue_lt_pow s.2)
  · exact ⟨le_rfl, hT⟩

theorem durB_nonneg (v : ℕ → ℝ) (hv : ∀ q < p.M, 0 ≤ v q ∧ v q ≤ p.T) (hT : 0 ≤ p.T)
    (s : Bool × (Fin p.m → Bool)) : 0 ≤ durB p v s :=
  sub_nonneg.mpr (startB_mem p v hv hT s).2

theorem durB_le (v : ℕ → ℝ) (hv : ∀ q < p.M, 0 ≤ v q ∧ v q ≤ p.T) (hT : 0 ≤ p.T)
    (s : Bool × (Fin p.m → Bool)) : durB p v s ≤ p.T := by
  have := (startB_mem p v hv hT s).1
  unfold durB
  linarith

theorem stepB_nonneg (v : ℕ → ℝ) (hv : ∀ q < p.M, 0 ≤ v q ∧ v q ≤ p.T) (hT : 0 ≤ p.T)
    (s : Bool × (Fin p.m → Bool)) (r : ℕ) : 0 ≤ stepB p v s r :=
  div_nonneg (durB_nonneg p v hv hT s) (Nat.cast_nonneg _)

theorem sum_stepB (v : ℕ → ℝ) (s : Bool × (Fin p.m → Bool)) :
    ∑ r ∈ Finset.range p.M, stepB p v s r = durB p v s := by
  unfold stepB
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM : (p.M : ℝ) ≠ 0 := by exact_mod_cast p.M_pos.ne'
  field_simp

/-- The source vector of a forcing label is its weighted forcing vector. -/
theorem zsrc_bsW (hT : 0 < p.T) (x0 : P) (wq : ℕ → ℝ) (fv : ℕ → P) (w : Fin p.m → Bool) :
    p.zsrc x0 (bsW p wq fv) (true, w) = ((wq (wordValue w) : ℝ) : ℂ) • fv (wordValue w) := by
  unfold GateODE.Time.TParams.zsrc bsW
  simp only [if_true]
  rw [smul_smul]
  congr 1
  have hM : (p.M : ℝ) ≠ 0 := by exact_mod_cast p.M_pos.ne'
  rw [← Complex.ofReal_mul]
  congr 1
  field_simp

/-- The source mass with quadrature weights: `‖x(0)‖ + ∑_q w_q ‖f_q‖`. -/
theorem mass_bsW (hT : 0 < p.T) (x0 : P) (wq : ℕ → ℝ) (hw : ∀ q < p.M, 0 ≤ wq q) (fv : ℕ → P) :
    p.mass x0 (bsW p wq fv) = ‖x0‖ + ∑ q ∈ Finset.range p.M, wq q * ‖fv q‖ := by
  rw [p.mass_eq hT.le, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  unfold bsW
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hT.le)
      (hw q (Finset.mem_range.mp hq))), ← mul_assoc,
    ← mul_assoc]
  have hM : (p.M : ℝ) ≠ 0 := by exact_mod_cast p.M_pos.ne'
  congr 1
  field_simp

/-! ### The normalised slot Hamiltonians -/

variable [CompleteSpace P]

theorem branchHB_selfAdjoint (v : ℕ → ℝ) (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P)
    (z : Label p.m p.l) (r : ℕ) (hH : star (Hb z.1 r) = Hb z.1 r)
    (hL : star (Lb z.1 r) = Lb z.1 r) :
    star (branchHB p v Hb Lb z r) = branchHB p v Hb Lb z r := by
  unfold branchHB
  rw [star_smul, star_add, star_smul, hH, hL]
  simp [Complex.conj_ofReal]

omit [CompleteSpace P] in
/-- The branch sample `Hb + k_w Lb` has norm at most `λH + R λD`. -/
theorem branch_sample_norm_le (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1)
    (hTD : 0 ≤ p.T * p.lamD) (H L : P →L[ℂ] P) (w : Fin p.l → Bool) (hHn : ‖H‖ ≤ p.lamH)
    (hLn : ‖L‖ ≤ p.lamD) :
    ‖H + ((p.nodeW w : ℝ) : ℂ) • L‖ ≤ p.lamH + p.R * p.lamD := by
  have hR := p.nodeW_abs_le hg hε hεOne hTD w
  calc ‖H + ((p.nodeW w : ℝ) : ℂ) • L‖ ≤ ‖H‖ + |p.nodeW w| * ‖L‖ := by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ p.lamH + p.R * p.lamD := add_le_add hHn
        (mul_le_mul hR hLn (norm_nonneg _) ((abs_nonneg _).trans hR))

omit [CompleteSpace P] in
/-- One step `τ / 2^m` of the normalised slot Hamiltonian is the LCHS slot evolution of the
branch for its own step `durB / 2^m`. -/
theorem exp_branchHB (hτ : 0 < p.tau) (v : ℕ → ℝ)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (z : Label p.m p.l) (r : ℕ) :
    NormedSpace.exp ((-Complex.I * (stepW p.tau p.m : ℂ)) • branchHB p v Hb Lb z r) =
      ODEWeightedLCHS.evolution (Lb z.1 r) (Hb z.1 r) (stepB p v z.1 r) (p.nodeW z.2) := by
  unfold branchHB
  rw [exp_branch_step p.m p.tau (durB p v z.1) hτ]
  rfl

/-- The ordered product of the simulator steps is the branch evolution. -/
theorem evolution_branchHB (v : ℕ → ℝ)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (z : Label p.m p.l) :
    TimeDependent.evolution
        (fun r => NormedSpace.exp ((-Complex.I * ((durB p v z.1 / ((2 ^ p.m : ℕ) : ℝ) : ℝ) : ℂ)) •
          (Hb z.1 r + ((p.nodeW z.2 : ℝ) : ℂ) • Lb z.1 r))) (2 ^ p.m) =
      branchUB p v Hb Lb z.1 z.2 := by
  unfold branchUB
  rw [TimeDependentODE.GaussianLCHS.productFamily_ofReal]
  rfl

/-! ### The coherent selection -/

/-- The branch of one joint label: the slot-selected simulator of the released protocol is
within `ν` of the branch evolution on its clean column. -/
theorem branch_blockB (hp : p.PublicOK) (v : ℕ → ℝ) (hv : ∀ q < p.M, 0 ≤ v q ∧ v q ≤ p.T)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (UJ : Vsp p.a P →L[ℂ] Vsp p.a P)
    (D : ℕ → Vsp p.a P →L[ℂ] Vsp p.a P) (z : Label p.m p.l)
    (hUJ : IsUnitary UJ) (hD : ∀ r < p.M, IsUnitary (D r))
    (hH : ∀ r < p.M, star (Hb z.1 r) = Hb z.1 r) (hL : ∀ r < p.M, star (Lb z.1 r) = Lb z.1 r)
    (hHn : ∀ r < p.M, ‖Hb z.1 r‖ ≤ p.lamH) (hLn : ∀ r < p.M, ‖Lb z.1 r‖ ≤ p.lamD)
    (hC : ∀ r < p.M, ClockPromise UJ (D r) (branchHB p v Hb Lb z r) p.Q p.qbar) :
    ‖SlotSim.runT (m := p.m) (r := p.r) (K := p.K) UJ D
        (SlotSim.simCircuitT p.a p.tau p.Q p.qbar p.nu p.m) ∘L
        basL (W := Wire p.a p.m p.r p.K) (Q := P) (fun _ => false) -
      basL (fun _ => false) ∘L branchUB p v Hb Lb z.1 z.2‖ ≤ p.nu := by
  have hT := hp.T_pos.le
  have hu := durB_nonneg p v hv hT z.1
  have huT := durB_le p v hv hT z.1
  have hXn : ∀ r < 2 ^ p.m, durB p v z.1 * ‖Hb z.1 r + ((p.nodeW z.2 : ℝ) : ℂ) • Lb z.1 r‖ ≤
      p.tau := by
    intro r hr
    have h := branch_sample_norm_le p hp.g_ge hp.ε_pos hp.eps_le_one hp.TD_nonneg (Hb z.1 r)
      (Lb z.1 r) z.2 (hHn r hr) (hLn r hr)
    calc durB p v z.1 * ‖Hb z.1 r + ((p.nodeW z.2 : ℝ) : ℂ) • Lb z.1 r‖ ≤
        p.T * (p.lamH + p.R * p.lamD) :=
          mul_le_mul huT h (norm_nonneg _) hT
      _ = p.tau := rfl
  have hX : ∀ r < 2 ^ p.m, star (Hb z.1 r + ((p.nodeW z.2 : ℝ) : ℂ) • Lb z.1 r) =
      Hb z.1 r + ((p.nodeW z.2 : ℝ) : ℂ) • Lb z.1 r := by
    intro r hr
    rw [star_add, star_smul, hH r hr, hL r hr, Complex.star_def, Complex.conj_ofReal]
  have h := branch_block p.a p.m UJ D (fun r => Hb z.1 r + ((p.nodeW z.2 : ℝ) : ℂ) • Lb z.1 r)
    p.tau (durB p v z.1) p.Q p.qbar p.nu hp.tau_pos hu hp.Q_ge hp.qbar_le hp.nu_pos
    (p.nu_le_one hp.g_ge hp.eps_le_one) hp.mesh hUJ hD hX hXn hC
  beta_reduce at h
  rw [evolution_branchHB p v Hb Lb z] at h
  have hio : basL (W := Wire p.a p.m p.r p.K) (Q := P) (fun _ => false) = io := by
    refine ContinuousLinearMap.ext (fun ψ => ?_)
    rw [basL_apply, io_apply]
  rw [hio]
  convert h using 4

/-- **The coherent selection on branch-dependent meshes is within `ν` of the direct sum of the
branch evolutions on the clean branch space.** -/
theorem select_errorB (hp : p.PublicOK) (v₀ : P) (σ : TOracles p.a p.m p.l P) (v : ℕ → ℝ)
    (hv : ∀ q < p.M, 0 ≤ v q ∧ v q ≤ p.T) (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P)
    (hUJ : IsUnitary σ.UJ) (hD : ∀ z, ∀ r < p.M, IsUnitary (σ.D z r))
    (hH : ∀ s, ∀ r < p.M, star (Hb s r) = Hb s r) (hL : ∀ s, ∀ r < p.M, star (Lb s r) = Lb s r)
    (hHn : ∀ s, ∀ r < p.M, ‖Hb s r‖ ≤ p.lamH) (hLn : ∀ s, ∀ r < p.M, ‖Lb s r‖ ≤ p.lamD)
    (hC : ∀ z, ∀ r < p.M, ClockPromise σ.UJ (σ.D z r) (branchHB p v Hb Lb z r) p.Q p.qbar) :
    ‖trun v₀ σ p.select ∘L p.branchE -
        p.branchE ∘L WeightedClock.diagonal (fun z => branchUB p v Hb Lb z.1 z.2)‖ ≤ p.nu := by
  have h := p.select_error_of_blocks v₀ σ (SlotSim.simCircuitT p.a p.tau p.Q p.qbar p.nu p.m)
    (fun z => branchUB p v Hb Lb z.1 z.2) p.nu hp.nu_pos.le
    (fun z => branch_blockB p hp v hv Hb Lb σ.UJ (σ.D z) z hUJ (hD z) (hH z.1) (hL z.1)
      (hHn z.1) (hLn z.1) (hC z))
  rw [GateODE.Time.TParams.select]
  convert h using 3

end

end SparseHamiltonian.GateSelect.ODE
