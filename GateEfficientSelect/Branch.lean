import GateEfficientSelect.Model

/-!
# One branch on its own mesh

A branch of Lemma `ode:lem:gate-select` evolves for its own duration `u` on its own uniform
mesh of `2^m` slots of length `u / 2^m`, while the circuit is the released slot-selected
simulator for one common normalised time `τ` with step `τ / 2^m` on every slot. The branch
duration enters through the normalised Hamiltonian of the private operation: for represented
slot samples `X j` with `u ‖X j‖ ≤ τ`, the private operation `D j` of the branch carries the
clock promise of the released simulator for `(u / τ) X j`. One normalised Cayley step of length
`τ / 2^m` is then the Cayley step of length `u / 2^m` for `X j`, the same as the paper's
branch rotation parameter `c_z` with step `w_z = α u / 2^m` (for `τ = α T`); the boundary
rotations of the circuit do not depend on the branch.

* `clock_family`: one endpoint bound `sqrt (qbar / 2)` serves every slot.
* `branch_block`: the circuit is within `ε` of the ordered product of the slot exponentials
  `exp (-i (u / 2^m) X j)` on the clean column (the released
  `GateCircuit.SlotSim.simulationT`).
* `branch_propagator`: for a `β`-Lipschitz Hermitian path `h` on `[0, u]` with
  `‖h (j u / 2^m) - X j‖ ≤ δ`, the circuit is within `ε + β u² / 2^m + u δ` of every propagator
  `U` of `h` with `U 0 = 1` (the released freezing estimate `TimeDependent.mesh_error`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSelect

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire Vsp iota0 io io_norm_le stepW simR fDeg)
open GateCircuit.SlotSim (clampAt clampAt_of_lt min_pred_lt evolution_eq_of_lt)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- Uniform clock promises: one endpoint bound `sqrt (qbar / 2)` serves every slot. -/
theorem clock_family {a : ℕ} (M : ℕ) (UJ : Vsp a P →L[ℂ] Vsp a P)
    (D : ℕ → Vsp a P →L[ℂ] Vsp a P) (H : ℕ → P →L[ℂ] P) (Q qbar : ℝ)
    (hC : ∀ j < M, GateODE.ClockPromise UJ (D j) (H j) Q qbar) :
    ∃ R1 : ℕ → Vsp a P →L[ℂ] Vsp a P, ∀ j < M,
      (1 - D j) ∘L R1 j = 1 ∧ R1 j ∘L (1 - D j) = 1 ∧ ‖R1 j‖ ≤ Q ∧
      (UJ ∘L iota0)† ∘L R1 j ∘L (UJ ∘L iota0) = (2 : ℂ)⁻¹ • (1 + Complex.I • H j) ∧
      ‖R1 j ∘L (UJ ∘L iota0)‖ ≤ Real.sqrt (qbar / 2) := by
  have h : ∀ j, j < M → ∃ (R1 : Vsp a P →L[ℂ] Vsp a P) (b : ℝ),
      (1 - D j) ∘L R1 = 1 ∧ R1 ∘L (1 - D j) = 1 ∧ ‖R1‖ ≤ Q ∧
      (UJ ∘L iota0)† ∘L R1 ∘L (UJ ∘L iota0) = (2 : ℂ)⁻¹ • (1 + Complex.I • H j) ∧
      ‖R1 ∘L (UJ ∘L iota0)‖ ≤ b ∧ b ^ 2 ≤ qbar / 2 := fun j hj => (hC j hj).promise
  choose R1 b hR using h
  refine ⟨fun j => if hj : j < M then R1 j hj else 0, fun j hj => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hR j hj
  simp only [dif_pos hj]
  exact ⟨h1, h2, h3, h4, h5.trans ((le_abs_self _).trans (Real.abs_le_sqrt h6))⟩

/-- A clock promise forces `qbar ≥ 0`. -/
theorem qbar_nonneg_of_clock {a : ℕ} (UJ D : Vsp a P →L[ℂ] Vsp a P) (H : P →L[ℂ] P)
    (Q qbar : ℝ) (hC : GateODE.ClockPromise UJ D H Q qbar) : 0 ≤ qbar := by
  obtain ⟨_, b, -, -, -, -, -, hb⟩ := hC.promise
  nlinarith [sq_nonneg b]

omit [CompleteSpace P] in
/-- One normalised Cayley step of the common time `τ` is the step `u / 2^m` of the branch. -/
theorem exp_branch_step (m : ℕ) (τ u : ℝ) (hτ : 0 < τ) (X : P →L[ℂ] P) :
    NormedSpace.exp ((-Complex.I * (stepW τ m : ℂ)) • (((u / τ : ℝ) : ℂ) • X)) =
      NormedSpace.exp ((-Complex.I * ((u / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • X) := by
  rw [smul_smul]
  congr 2
  have hτ0 : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hM : ((2 ^ m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.two_pow_pos m).ne'
  unfold stepW
  push_cast
  field_simp

/-- **One branch on its own mesh, discrete form.** For a common normalised time `τ > 0`, a
branch duration `u ≥ 0` and represented slot samples `X j` with `u ‖X j‖ ≤ τ`, let every slot
operation `D j` carry the clock promise of the released simulator for the normalised sample
`(u / τ) X j`. Then the released slot-selected simulator for `τ`, with `2^m ≥ steps τ (ε/3)`
slots, is within `ε` of the ordered product of the branch slot exponentials
`exp (-i (u / 2^m) X j)` on its clean column, with every wire compared. -/
theorem branch_block (a m : ℕ) (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P)
    (X : ℕ → P →L[ℂ] P) (τ u Q qbar ε : ℝ) (hτ : 0 < τ) (hu : 0 ≤ u) (hQ : 1 ≤ Q)
    (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1) (hm : TimeSchedule.steps τ (ε / 3) ≤ 2 ^ m)
    (hUJ : IsUnitary UJ) (hD : ∀ j < 2 ^ m, IsUnitary (D j))
    (hX : ∀ j < 2 ^ m, star (X j) = X j) (hXn : ∀ j < 2 ^ m, u * ‖X j‖ ≤ τ)
    (hC : ∀ j < 2 ^ m, GateODE.ClockPromise UJ (D j) (((u / τ : ℝ) : ℂ) • X j) Q qbar) :
    ‖SlotSim.runT UJ D (SlotSim.simCircuitT a τ Q qbar ε m) ∘L io -
      io ∘L TimeDependent.evolution
        (fun j => NormedSpace.exp ((-Complex.I * ((u / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • X j))
        (2 ^ m)‖ ≤ ε := by
  obtain ⟨R1, hR1⟩ := clock_family (2 ^ m) UJ D (fun j => ((u / τ : ℝ) : ℂ) • X j) Q qbar hC
  have hq : 0 ≤ qbar := qbar_nonneg_of_clock UJ (D 0) _ Q qbar (hC 0 (Nat.two_pow_pos m))
  have hb : Real.sqrt (qbar / 2) ^ 2 ≤ qbar / 2 := by
    rw [Real.sq_sqrt (by linarith)]
  have hself : ∀ j < 2 ^ m, star (((u / τ : ℝ) : ℂ) • X j) = ((u / τ : ℝ) : ℂ) • X j := by
    intro j hj
    rw [star_smul, hX j hj, Complex.star_def, Complex.conj_ofReal]
  have hnorm : ∀ j < 2 ^ m, ‖((u / τ : ℝ) : ℂ) • X j‖ ≤ 1 := by
    intro j hj
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hu hτ.le),
      div_mul_eq_mul_div, div_le_one hτ]
    exact hXn j hj
  have hsim := SlotSim.simulationT (P := P) a m UJ D R1 (fun j => ((u / τ : ℝ) : ℂ) • X j) hUJ hD
    τ Q (Real.sqrt (qbar / 2)) qbar ε hτ.le hQ (fun j hj => (hR1 j hj).1)
    (fun j hj => (hR1 j hj).2.1) (fun j hj => (hR1 j hj).2.2.1) (fun j hj => (hR1 j hj).2.2.2.1)
    hself hnorm (fun j hj => (hR1 j hj).2.2.2.2) hb hqQ hε hε1 hm
  have hfin := hsim.2.2.2.2.2.1
  have hexp : (fun j => NormedSpace.exp ((-Complex.I * (stepW τ m : ℂ)) •
      (((u / τ : ℝ) : ℂ) • X j))) =
      fun j => NormedSpace.exp ((-Complex.I * ((u / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • X j) := by
    funext j
    exact exp_branch_step m τ u hτ (X j)
  rw [hexp] at hfin
  exact hfin

/-- **One branch on its own mesh, against the propagator.** Under the hypotheses of
`branch_block`, let `h` be a Hermitian path on `[0, u]` with operator-norm Lipschitz bound `β`
whose values at the slot addresses `j u / 2^m` are within `δ` of the represented samples `X j`.
Then the released slot-selected simulator for `τ` is within `ε + β u² / 2^m + u δ` of every
propagator `U` of `h` with `U 0 = 1`, on its clean column with every wire compared. -/
theorem branch_propagator (a m : ℕ) (UJ : Vsp a P →L[ℂ] Vsp a P)
    (D : ℕ → Vsp a P →L[ℂ] Vsp a P) (X : ℕ → P →L[ℂ] P) (h U : ℝ → P →L[ℂ] P)
    (τ u β δ Q qbar ε : ℝ) (hτ : 0 < τ) (hu : 0 ≤ u) (hβ : 0 ≤ β) (hQ : 1 ≤ Q)
    (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1) (hm : TimeSchedule.steps τ (ε / 3) ≤ 2 ^ m)
    (hUJ : IsUnitary UJ) (hD : ∀ j < 2 ^ m, IsUnitary (D j))
    (hX : ∀ j < 2 ^ m, star (X j) = X j) (hXn : ∀ j < 2 ^ m, u * ‖X j‖ ≤ τ)
    (hC : ∀ j < 2 ^ m, GateODE.ClockPromise UJ (D j) (((u / τ : ℝ) : ℂ) • X j) Q qbar)
    (hh : ∀ t ∈ Set.Icc 0 u, star (h t) = h t)
    (hLip : ∀ t ∈ Set.Icc 0 u, ∀ t' ∈ Set.Icc 0 u, ‖h t - h t'‖ ≤ β * |t - t'|)
    (hVal : ∀ j : ℕ, j < 2 ^ m → ‖h (j * u / 2 ^ m) - X j‖ ≤ δ)
    (hU0 : U 0 = 1) (hU : TimeDependent.SolvesOn h U 0 u) :
    ‖SlotSim.runT UJ D (SlotSim.simCircuitT a τ Q qbar ε m) ∘L io - io ∘L U u‖ ≤
      ε + β * u ^ 2 / 2 ^ m + u * δ := by
  have hMpos : 0 < 2 ^ m := Nat.two_pow_pos m
  have hsim := branch_block a m UJ D X τ u Q qbar ε hτ hu hQ hqQ hε hε1 hm hUJ hD hX hXn hC
  have hcl := min_pred_lt hMpos
  have hmesh := TimeDependent.mesh_error (H := h) (U := U) (δ := δ) (clampAt (2 ^ m) X) hMpos hu
    hβ hU0 hU hh (fun k => hX _ (hcl k)) hLip (fun k hk => by
      rw [clampAt_of_lt _ _ hk]
      have h1 := hVal k hk
      push_cast
      exact h1)
  have hev : TimeDependent.evolution (fun k => NormedSpace.exp
        ((-Complex.I * ((u / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • clampAt (2 ^ m) X k)) (2 ^ m) =
      TimeDependent.evolution (fun k => NormedSpace.exp
        ((-Complex.I * ((u / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • X k)) (2 ^ m) :=
    evolution_eq_of_lt _ _ _ (fun k hk => by rw [clampAt_of_lt _ _ hk])
  rw [hev] at hmesh
  have h2 : ‖(io : P →L[ℂ] Reg (Wire a m (simR Q τ qbar ε) (a + m + 2 * simR Q τ qbar ε)) P) ∘L
        TimeDependent.evolution (fun k => NormedSpace.exp
          ((-Complex.I * ((u / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • X k)) (2 ^ m) - io ∘L U u‖ ≤
      β * u ^ 2 / 2 ^ m + u * δ := by
    rw [← comp_sub]
    refine (opNorm_comp_le _ _).trans ?_
    have h3 : ‖TimeDependent.evolution (fun k => NormedSpace.exp
        ((-Complex.I * ((u / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • X k)) (2 ^ m) - U u‖ ≤
        β * u ^ 2 / 2 ^ m + u * δ := by
      rw [norm_sub_rev]
      have hpow : (((2 ^ m : ℕ) : ℝ)) = (2 : ℝ) ^ m := by norm_num
      rw [← hpow]
      exact hmesh
    calc _ ≤ 1 * (β * u ^ 2 / 2 ^ m + u * δ) :=
          mul_le_mul io_norm_le h3 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have key := norm_sub_le_norm_sub_add_norm_sub
    (SlotSim.runT UJ D (SlotSim.simCircuitT a τ Q qbar ε m) ∘L io)
    ((io : P →L[ℂ] Reg (Wire a m (simR Q τ qbar ε) (a + m + 2 * simR Q τ qbar ε)) P) ∘L
      TimeDependent.evolution (fun k => NormedSpace.exp
        ((-Complex.I * ((u / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • X k)) (2 ^ m))
    ((io : P →L[ℂ] Reg (Wire a m (simR Q τ qbar ε) (a + m + 2 * simR Q τ qbar ε)) P) ∘L U u)
  linarith

end

end SparseHamiltonian.GateSelect
