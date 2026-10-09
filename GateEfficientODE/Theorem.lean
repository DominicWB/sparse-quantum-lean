import GateEfficientODE.Protocol

/-!
# Gate-efficient dissipative ODE solver: constant coefficients, exact gates

This is the constant-coefficient, exact-gate part of Theorem `ode:thm:gates`
of the manuscript: the problem `x' = -(L + iH) x + b`, `L ≥ 0`, solved by an
explicit circuit of elementary gates and counted calls, with the analytic
LCHS grid of `J = O(ℓ (T λD + ℓ))` labels (`ode:eq:grid`, `ode:eq:gate-grid-size`).

**Access model.** The system is an abstract finite-dimensional Hilbert space
`P`.  As in the released gate-level Hamiltonian simulator, the matrix enters
only through `U_J` (on `a` ancilla qubits and the system) and the private
Cayley operation; here the private operation is label-selected: one call
applies `D z` on every configuration whose solver wires carry the joint
label `z = ((ini, node), LCHS word)` (`Oracles`, `OInstr.priv`).  The source
interfaces `J₀ = J false` and `J_b = J true` are supplied unitaries, called
under the source-sector wire, and the public payload reflection about the
seed vector is a separate counted instruction.  All other operations are
elementary gates: one-qubit unitaries with at most three literal controls.

**The circuit.** `Params.prepC` is
`SRC · LCHS · LOAD · SELECT · PHASE · LCHS⁻¹ · SRC⁻¹` (`Circuit/Trial`), one
amplification step is `R_good · prepC⁻¹ · R_seed · prepC · (-1)`, and the
trial with `j` steps is `trialC j = prepC · step^j`.  The LCHS register holds
the analytic Gaussian grid `AnalyticLCHS` (`J = 2K + 1` nodes `n h`, `|n| ≤ K`,
step `h ≤ π / (T λD / 2 + log (512/ν))`, coefficients `h · kernel (n h)`),
padded to `J + 2` labels of total coefficient mass three on
`l = ⌈log₂ (J + 2)⌉` wires; its amplitudes are prepared by an explicit
rotation tree and its phases by an explicit uniformly controlled diagonal,
together at most `3 · 2^l (2l + 1)` gates.  The grid error is controlled by
the exponential convergence of the trapezoidal rule for the integrand,
holomorphic on the strip `|Im k| ≤ 1/2` (`StripQuadrature.trapezoid_error_op`,
via Poisson summation).  The source register holds
`2^k` left-endpoint quadrature nodes, `2^k ≥ T (λH + λD) / ν`.  The complete
protocol (`Params.protocol`) is the released bounded four-attempt wrapper
`ODERepeatProtocol.fourTrials` with a uniform trial count
`j < chosenIterations g`.

**Main theorem** (`solver`).  For public data satisfying `PublicOK` and a unit
seed `v`, the protocol, chosen before every unknown instance:

* consists of valid elementary instructions only;
* uses, in every history including four failures, at most
  `40 g · prepGates + 20 g · reflGates` elementary gates, where
  `prepGates = 200 (d+1)(a+m+r+1) + 2 (k+1) + 3 · 2^l (2l+1)` and
  `reflGates = 6 (2a + 3m + 6r + 4 + k + l) + 4`; at most `240 g d` private
  calls and `480 g d` calls of `U_J` or `U_J†`; at most `40 g` calls of each
  source interface; and at most `20 g` seed reflections;
* acts on `4a + 6m + 12r + 2k + 2l + 8` qubit wires and the system;
* has filter degree `d ≤ 128 (τ qbar + Q (1 + log (3/ν)))`, `τ = T (λH + R λD)`,
  with the released simulator sizes `2^m < 2 · steps`, `2^r ≤ 4 (d+1)`,
  `J + 2 ≤ 2^l < 2 (J + 2)`, `2^k < 2 (⌈T (λH + λD)/ν⌉ + 1)`, and
  `J ≤ R (T λD + 2 log (512/ν)) / π + 3`, where `R = 4 log (20000 g/ε)` and
  `512/ν = 5120000 g/ε` (`J_le_log`), so `J = O(ℓ (T λD + ℓ))`;
* for every instance satisfying `InstanceOK` (clock promises of the released
  simulator for every branch Hamiltonian, unitary oracles, source directions,
  `L ≥ 0`, norm bounds and the budget `B ≤ g ‖x(T)‖`) satisfies `Outcome`:
  success probability at least `175/256 > 2/3`, and the conditional output
  is a density operator within trace distance `ε` of `x(T) / ‖x(T)‖`.

`gate_count` simplifies the gate bound to
`9000 g ((d+1)(a+m+r+1) + (k+1) + (J+2)(l+1))`, and `gate_count_grid`
substitutes the grid bound: the LCHS register contributes
`O(g J log J) = O(g ℓ (T λD + ℓ) log (ℓ (T λD + ℓ)))` gates.

Not formalised here: synthesis of the rotation angles over a finite gate set,
time-dependent coefficients, entry decoding and arithmetic inside the matrix
oracles, and the gate costs of the supplied source interfaces.
-/

namespace SparseHamiltonian.GateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire simM simR simK fDeg simM_spec simR_spec)
open scoped InnerProduct BigOperators Real

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Public sizes -/

/-- The solver wires as a sum type. -/
def OWire.equiv (k l f : ℕ) : OWire k l f ≃ (Unit ⊕ Fin k) ⊕ (Fin l ⊕ (Unit ⊕ Fin f)) where
  toFun
    | .ini => .inl (.inl ())
    | .src i => .inl (.inr i)
    | .lch i => .inr (.inl i)
    | .flg => .inr (.inr (.inl ()))
    | .pool i => .inr (.inr (.inr i))
  invFun
    | .inl (.inl ()) => .ini
    | .inl (.inr i) => .src i
    | .inr (.inl i) => .lch i
    | .inr (.inr (.inl ())) => .flg
    | .inr (.inr (.inr i)) => .pool i
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with (⟨⟩ | i) | i | ⟨⟩ | i <;> rfl

theorem card_oWire (k l f : ℕ) : Fintype.card (OWire k l f) = k + l + f + 2 := by
  rw [Fintype.card_congr (OWire.equiv k l f)]
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  ring

/-- `2 ^ ⌈log₂ n⌉ < 2 n` for `n ≥ 1`. -/
theorem pow_clog_lt (n : ℕ) (hn : 1 ≤ n) : 2 ^ Nat.clog 2 n < 2 * n := by
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h1
    have hpos : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) h1
    have e : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n).pred := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
      rw [pow_succ]
      ring
    omega
  · have : n = 1 := by omega
    subst this
    simp

namespace Params

variable (p : Params)

theorem card_simWires :
    Fintype.card (Wire p.a p.m p.r p.K) = 2 * p.a + 3 * p.m + 6 * p.r + 3 :=
  GateCircuit.Sim.card_simWire p.a p.Q p.tau p.qbar p.nu

/-- The number of qubit wires of the solver. -/
theorem card_W : Fintype.card p.W = 4 * p.a + 6 * p.m + 12 * p.r + 2 * p.k + 2 * p.l + 8 := by
  have h1 := p.card_simWires
  have h2 := card_oWire p.k p.l p.f
  have h3 : Fintype.card p.W =
      Fintype.card (Wire p.a p.m p.r p.K) + Fintype.card (OWire p.k p.l p.f) :=
    Fintype.card_sum
  have h4 : p.f = Fintype.card (Wire p.a p.m p.r p.K) + p.k + p.l := rfl
  omega

/-- The released degree bound of the filter. -/
theorem degree_bound (hp : p.PublicOK) :
    (p.d : ℝ) ≤ 128 * (p.tau * p.qbar + p.Q * (1 + Real.log (3 / p.nu))) := by
  have hν := hp.nu_pos
  have hν1 : p.nu ≤ 1 / 10000 :=
    ImprovedODEQueryBudget.precision_le_one_ten_thousandth p.g p.ε hp.g_ge hp.eps_le_one
  have h := SharpFilterSchedule.degree_le p.Q (p.tau * p.qbar) (p.nu / 3) hp.Q_ge
    (mul_nonneg hp.tau_pos.le hp.qbar_nonneg) (by positivity) (by linarith)
  have e1 : (p.d : ℝ) = (SharpFilterSchedule.degree p.Q (p.tau * p.qbar) (p.nu / 3) : ℝ) := rfl
  have e2 : Real.log (3 / p.nu) = SharpFilterSchedule.logBudget (p.nu / 3) := by
    unfold SharpFilterSchedule.logBudget
    rw [one_div_div]
  rw [e1, e2]
  exact h

/-- The sizes of the released simulator. -/
theorem sim_sizes :
    TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m ∧
    2 ^ p.m < 2 * TimeSchedule.steps p.tau (p.nu / 3) ∧
    2 * p.d + 2 ≤ 2 ^ p.r ∧ 2 ^ p.r ≤ 4 * (p.d + 1) := by
  obtain ⟨h1, h2⟩ := simM_spec p.tau p.nu
  obtain ⟨h3, _, h4⟩ := simR_spec p.Q p.tau p.qbar p.nu
  exact ⟨h1, h2, h3, h4⟩

/-- The LCHS label register holds the `J + 2` padded labels with less than
a factor two to spare. -/
theorem l_bounds : p.J + 2 ≤ 2 ^ p.l ∧ 2 ^ p.l < 2 * (p.J + 2) :=
  ⟨p.J_add_two_le, pow_clog_lt _ (by omega)⟩

/-- The analytic LCHS grid has `O(R (T λD + log (1/ν)))` labels. -/
theorem J_le (hp : p.PublicOK) :
    (p.J : ℝ) ≤ p.R * (p.T * p.lamD + 2 * Real.log (512 / p.nu)) / π + 3 :=
  AnalyticLCHS.gridSize_le hp.TD_nonneg hp.g_ge hp.ε_pos hp.eps_le_one

/-- The grid bound in the public parameters: with `ℓ = log (g / ε)`, `J = O(ℓ (T λD + ℓ))`. -/
theorem J_le_log (hp : p.PublicOK) :
    (p.J : ℝ) ≤ 4 * Real.log (20000 * p.g / p.ε) *
      (p.T * p.lamD + 2 * Real.log (5120000 * p.g / p.ε)) / π + 3 := by
  have h := p.J_le hp
  have e1 : p.R = 4 * Real.log (20000 * p.g / p.ε) := rfl
  have e2 : 512 / p.nu = 5120000 * p.g / p.ε := by
    show 512 / ImprovedODEQueryBudget.precision p.g p.ε = _
    unfold ImprovedODEQueryBudget.precision
    have h1 := hp.ε_pos
    have h2 : 0 < p.g := lt_of_lt_of_le one_pos hp.g_ge
    field_simp
    ring
  rwa [e1, e2] at h

/-- The quadrature register: `2^k` nodes with `T (λH + λD) ≤ ν 2^k`. -/
theorem k_bounds (hν : 0 < p.nu) :
    p.T * (p.lamH + p.lamD) ≤ p.nu * 2 ^ p.k ∧
    2 ^ p.k < 2 * (⌈p.T * (p.lamH + p.lamD) / p.nu⌉₊ + 1) := by
  refine ⟨p.two_pow_k hν, ?_⟩
  show 2 ^ Nat.clog 2 ⌈p.T * (p.lamH + p.lamD) / p.nu⌉₊ <
    2 * (⌈p.T * (p.lamH + p.lamD) / p.nu⌉₊ + 1)
  rcases Nat.eq_zero_or_pos ⌈p.T * (p.lamH + p.lamD) / p.nu⌉₊ with h0 | h0
  · rw [h0, Nat.clog_zero_right]
    norm_num
  · exact lt_of_lt_of_le (pow_clog_lt _ h0) (by omega)

/-- The gate budget of one preparation, explicitly. -/
theorem prepGates_eq : p.prepGates =
    200 * (p.d + 1) * (p.a + p.m + p.r + 1) + 2 * (p.k + 1) + 3 * (2 ^ p.l * (2 * p.l + 1)) :=
  rfl

/-- The gate budget of the reflections and the sign of one step, explicitly. -/
theorem reflGates_eq : p.reflGates = 6 * (2 * p.a + 3 * p.m + 6 * p.r + 4 + p.k + p.l) + 4 := by
  have h := p.card_simWires
  unfold reflGates nz
  omega

/-- **A simplified worst-case gate count.** -/
theorem gate_count (hp : p.PublicOK) (v : P) (hv : ‖v‖ = 1) :
    ((p.protocol v hv hp.g_ge).worstCost p.wGate : ℝ) ≤
      9000 * p.g * (((p.d : ℝ) + 1) * ((p.a : ℝ) + p.m + p.r + 1) + ((p.k : ℝ) + 1) +
        ((p.J : ℝ) + 2) * ((p.l : ℝ) + 1)) := by
  have h := (p.protocol_worst hp v hv).1
  have hl := p.l_bounds.2
  have hg := hp.g_ge
  rw [p.prepGates_eq, p.reflGates_eq] at h
  generalize (p.protocol v hv hp.g_ge).worstCost p.wGate = W at h ⊢
  generalize p.d = D at h ⊢
  generalize p.a = A at h ⊢
  generalize p.m = M at h ⊢
  generalize p.r = R at h ⊢
  generalize p.k = K at h ⊢
  generalize p.l = L at h hl ⊢
  generalize p.J = J at h hl ⊢
  generalize p.g = g at h hg ⊢
  have hX : ((2 : ℝ) ^ L) ≤ 2 * ((J : ℝ) + 2) := by exact_mod_cast hl.le
  push_cast at h
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have h1 : (2 : ℝ) ^ L * (2 * L + 1) ≤ 2 * ((J : ℝ) + 2) * (2 * L + 1) :=
    mul_le_mul_of_nonneg_right hX (by positivity)
  have h2 : (0 : ℝ) ≤ D * (A + M + R + 1) := by positivity
  have h3 : (0 : ℝ) ≤ J * L := by positivity
  have hin : 40 * (200 * ((D : ℝ) + 1) * (A + M + R + 1) + 2 * (K + 1) +
        3 * (2 ^ L * (2 * L + 1))) + 20 * (6 * (2 * (A : ℝ) + 3 * M + 6 * R + 4 + K + L) + 4) ≤
      9000 * (((D : ℝ) + 1) * (A + M + R + 1) + (K + 1) + (J + 2) * (L + 1)) := by
    nlinarith
  calc (W : ℝ) ≤ g * (40 * (200 * ((D : ℝ) + 1) * (A + M + R + 1) + 2 * (K + 1) +
        3 * (2 ^ L * (2 * L + 1))) + 20 * (6 * (2 * (A : ℝ) + 3 * M + 6 * R + 4 + K + L) + 4)) := by
        linarith
    _ ≤ g * (9000 * (((D : ℝ) + 1) * (A + M + R + 1) + (K + 1) + (J + 2) * (L + 1))) :=
        mul_le_mul_of_nonneg_left hin (by linarith)
    _ = _ := by ring

/-- **The gate count with the analytic grid**: with `J ≤ R (T λD + 2 log (512/ν)) / π + 3`
substituted, every history uses at most
`9000 g ((d+1)(a+m+r+1) + (k+1) + (R (T λD + 2 log (512/ν)) / π + 5)(l+1))` gates. -/
theorem gate_count_grid (hp : p.PublicOK) (v : P) (hv : ‖v‖ = 1) :
    ((p.protocol v hv hp.g_ge).worstCost p.wGate : ℝ) ≤
      9000 * p.g * (((p.d : ℝ) + 1) * ((p.a : ℝ) + p.m + p.r + 1) + ((p.k : ℝ) + 1) +
        (p.R * (p.T * p.lamD + 2 * Real.log (512 / p.nu)) / π + 5) * ((p.l : ℝ) + 1)) := by
  have h := p.gate_count hp v hv
  have hJ := p.J_le hp
  have hl : (0 : ℝ) ≤ (p.l : ℝ) + 1 := by positivity
  have hg : 0 ≤ 9000 * p.g := by have := hp.g_ge; linarith
  have h1 : ((p.J : ℝ) + 2) * ((p.l : ℝ) + 1) ≤
      (p.R * (p.T * p.lamD + 2 * Real.log (512 / p.nu)) / π + 5) * ((p.l : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hl
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hg)
  linarith

end Params

/-! ### The main theorem -/

/-- **Gate-efficient dissipative ODE solver, constant coefficients, exact
gates.**  The protocol depends only on the public data `p` and the seed `v`;
the instance `(σ, H, L, x0, b)` is quantified afterwards. -/
theorem solver [FiniteDimensional ℂ P] (p : Params) (hp : p.PublicOK) (v : P) (hv : ‖v‖ = 1) :
    (∀ j, ∀ g ∈ p.trialC j, g.Valid Wire.anc) ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wGate : ℝ) ≤
      40 * p.g * p.prepGates + 20 * p.g * p.reflGates ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wPriv : ℝ) ≤ 240 * p.g * p.d ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wUJ : ℝ) ≤ 480 * p.g * p.d ∧
    (∀ c, ((p.protocol v hv hp.g_ge).worstCost (p.wSrc c) : ℝ) ≤ 40 * p.g) ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wSeed : ℝ) ≤ 20 * p.g ∧
    p.prepGates =
      200 * (p.d + 1) * (p.a + p.m + p.r + 1) + 2 * (p.k + 1) + 3 * (2 ^ p.l * (2 * p.l + 1)) ∧
    p.reflGates = 6 * (2 * p.a + 3 * p.m + 6 * p.r + 4 + p.k + p.l) + 4 ∧
    Fintype.card p.W = 4 * p.a + 6 * p.m + 12 * p.r + 2 * p.k + 2 * p.l + 8 ∧
    (p.d : ℝ) ≤ 128 * (p.tau * p.qbar + p.Q * (1 + Real.log (3 / p.nu))) ∧
    TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m ∧
    2 ^ p.m < 2 * TimeSchedule.steps p.tau (p.nu / 3) ∧
    2 * p.d + 2 ≤ 2 ^ p.r ∧ 2 ^ p.r ≤ 4 * (p.d + 1) ∧
    p.J + 2 ≤ 2 ^ p.l ∧ 2 ^ p.l < 2 * (p.J + 2) ∧
    (p.J : ℝ) ≤ p.R * (p.T * p.lamD + 2 * Real.log (512 / p.nu)) / π + 3 ∧
    p.T * (p.lamH + p.lamD) ≤ p.nu * 2 ^ p.k ∧
    2 ^ p.k < 2 * (⌈p.T * (p.lamH + p.lamD) / p.nu⌉₊ + 1) ∧
    ∀ (σ : Oracles p.a (Label p.k p.l) P) (H L : P →L[ℂ] P) (x0 b : P),
      p.InstanceOK v σ H L x0 b → p.Outcome v hv hp.g_ge σ (p.target H L x0 b) := by
  obtain ⟨wG, wP, wU, wS, wE⟩ := p.protocol_worst hp v hv
  obtain ⟨s1, s2, s3, s4⟩ := p.sim_sizes
  obtain ⟨l1, l2⟩ := p.l_bounds
  obtain ⟨k1, k2⟩ := p.k_bounds hp.nu_pos
  exact ⟨p.trialC_valid hp.tau_pos.le hp.nu_pos hp.r₀_nonneg hp.rb_nonneg hp.T_pos.le hp.B_pos,
    wG, wP, wU, wS, wE, p.prepGates_eq, p.reflGates_eq, p.card_W, p.degree_bound hp,
    s1, s2, s3, s4, l1, l2, p.J_le hp, k1, k2,
    fun σ H L x0 b hI => p.outcome hp v hv σ H L x0 b hI⟩

end

end SparseHamiltonian.GateODE
