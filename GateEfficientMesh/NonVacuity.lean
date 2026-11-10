import GateEfficientMesh.BinaryMesh
import GateEfficientMesh.ODE.Exact
import GateEfficientMesh.ODE.MeshTarget
import TimeDependentExtensions.ODE.Corollaries

/-!
# Non-vacuity of the certified and mesh hypotheses

Theorem `hs:thm:time` with the circuit of `hs:thm:gates`, and the time-dependent part of Theorem
`ode:thm:gates`: the hypotheses of the endpoints of this library beyond the released ones (a
certificate, a propagator or solution, and on a mesh a rounding condition) are met by natural
instances; the statement guide cites these theorems for its satisfiability argument.

* `time_simulation_mesh_piecewise_constant`: under the released clock promises, with the explicit
  exponent `meshExponent`, the piecewise constant path equal to the mesh samples has mesh
  certificate `0` and a classical piecewise propagator, which is also an integral-sense
  propagator of the glued path, and `time_simulation_mesh` gives the error bound `ε` for it.
* `time_simulation_mesh_glued`: the same through the integral-sense conjunct of
  `time_simulation_mesh` (the glued path is self-adjoint almost everywhere, interval integrable
  and has certificate `0`).
* `slotExponent_native_mesh_spec`, `slotExponent_binary_mesh_spec`: the explicit exponent
  `slotExponent` meets the subdivision and rounding conditions of the native and binary-data mesh
  theorems.
* `ODE.released_time_solver_outcome`: the guarantee of the released `GateODE.Time.solver` from
  `ODE.ode_time_solver_certified` and `ODE.certified_of_instanceOK`.
* `ODE.meshCertificate_samples_zero_forcing`, `ODE.meshCertificate_zero_forcing_le`: with zero
  forcing and generator pieces equal to the mesh samples, the mesh certificate is the refinement
  cost `Mm h Λ ‖x(0)‖`, and the certified budget `ε B/(2000 g)` holds whenever
  `2000 g Mm Λ T ≤ ε 2^m`.
* `ODE.meshCertificate_one_interval`, `ODE.slotCertificate_samples`: for data equal to the
  samples, the mesh certificate of one interval keeps the quadrature term `Λ (T + h)² ‖b̃‖`, which
  does not decrease with `m`, whereas the certificate on the uniform slots is
  `Λ h²/2 · 2^m ‖b̃‖ = Λ T h ‖b̃‖/2`.
* `ODE.exists_mesh_solution`: classical piecewise solutions exist for pieces equal to the
  samples (the released `TimeDependentExtensions.ODE.exists_piecewise_solution`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateMesh

noncomputable section

open ContinuousLinearMap MeasureTheory Set OracleCircuit GateCircuit GateCircuit.Sim
open GateCircuit.SlotSim
open TimeDependentExtensions (IsMesh slotPiece IsPiecewisePropagator)
open IntegrablePathSimulation.Propagator (IsPropagator glue)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Hamiltonians -/

/-- **The exact-gate mesh theorem applies to piecewise constant paths** (Theorem `hs:thm:time` with
the circuit of `hs:thm:gates`, extended by uniform refinement to nonuniform meshes). Under the
released clock promises for the mesh samples `H̃_r` and with the explicit exponent
`m = meshExponent α T ε M`, every path `Hp` equal to `H̃_r` on the mesh interval `r` has mesh
certificate `0` and a classical piecewise propagator `U`, which is also an integral-sense propagator
of the glued path, and the circuit of `time_simulation_mesh` is within `ε` of `U(T)`. -/
theorem time_simulation_mesh_piecewise_constant (a M : ℕ) (hM : 0 < M)
    (UJ : Vsp a P →L[ℂ] Vsp a P) (D R1 : ℕ → Vsp a P →L[ℂ] Vsp a P) (Hs : ℕ → P →L[ℂ] P)
    (tm : ℕ → ℝ) (T α Q b qbar ε : ℝ) (hmesh : IsMesh tm M T) (hT : 0 < T) (hα : 0 < α)
    (hQ : 1 ≤ Q) (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hUJ : IsUnitary UJ) (hD : ∀ r < M, IsUnitary (D r))
    (hRight : ∀ r < M, (1 - D r) ∘L R1 r = 1)
    (hLeft : ∀ r < M, R1 r ∘L (1 - D r) = 1) (hR1 : ∀ r < M, ‖R1 r‖ ≤ Q)
    (hBoundary : ∀ r < M, (UJ ∘L iota0)† ∘L R1 r ∘L (UJ ∘L iota0) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • ((α : ℂ)⁻¹ • Hs r)))
    (hEndpoint : ∀ r < M, ‖R1 r ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2)
    (hSelf : ∀ r < M, star (Hs r) = Hs r) (hHs : ∀ r < M, ‖Hs r‖ ≤ α)
    (Hp : ℕ → ℝ → P →L[ℂ] P) (hHp : ∀ r u, Hp r u = Hs r) :
    ∑ r ∈ Finset.range M, ∫ u in tm r..tm (r + 1), ‖Hp r u - Hs r‖ = 0 ∧
    ∃ U : ℝ → P →L[ℂ] P, IsPiecewisePropagator Hp tm M U ∧ IsPropagator (glue Hp tm M) U T ∧
      ‖runT UJ (fun k => D (slotPiece tm T (2 ^ meshExponent α T ε M) M k))
          (simCircuitT a (α * T) Q qbar (ε / 2) (meshExponent α T ε M)) ∘L io - io ∘L U T‖ ≤
        ε := by
  obtain rfl : Hp = fun r _ => Hs r := funext fun r => funext fun u => hHp r u
  obtain ⟨h1, h2, -⟩ := mesh_exponent_spec α T ε M hT hε
  obtain ⟨U, hU⟩ := TimeDependentExtensions.exists_piecewise_propagator (fun r (_ : ℝ) => Hs r)
    hmesh.zero hmesh.mono M (fun _ _ => continuousOn_const)
  have hint : ∀ r < M, IntervalIntegrable ((fun r (_ : ℝ) => Hs r) r) volume (tm r)
      (tm (r + 1)) := fun _ _ => intervalIntegrable_const
  have hU' := IntegrablePathSimulation.Propagator.isPropagator_glue hmesh hU hint
  have hcert : ∑ r ∈ Finset.range M, ∫ u in tm r..tm (r + 1),
      ‖(fun r (_ : ℝ) => Hs r) r u - Hs r‖ = 0 := by
    simp
  obtain ⟨-, -, -, -, -, -, -, -, -, hpw⟩ := time_simulation_mesh a (meshExponent α T ε M) M hM
    UJ D R1 Hs tm T α Q b qbar ε hmesh hT hα hQ hqQ hε hε1 h1 h2 hUJ hD hRight hLeft hR1
    hBoundary hEndpoint hbq hSelf hHs
  refine ⟨hcert, U, hU, hU', hpw _ U (fun r hr _ _ => hSelf r hr) hint ?_ hU⟩
  rw [hcert]
  linarith

/-- **The integral-sense conjunct of the exact-gate mesh theorem is reachable** (Theorem
`hs:thm:time` with the circuit of `hs:thm:gates`, extended by uniform refinement to nonuniform
meshes). Under the hypotheses of `time_simulation_mesh_piecewise_constant`, the glued path of the
piecewise constant path is self-adjoint almost everywhere, interval integrable and has certificate
`0`, and it has an integral-sense propagator `U` with the error bound `ε` of
`time_simulation_mesh`. -/
theorem time_simulation_mesh_glued (a M : ℕ) (hM : 0 < M)
    (UJ : Vsp a P →L[ℂ] Vsp a P) (D R1 : ℕ → Vsp a P →L[ℂ] Vsp a P) (Hs : ℕ → P →L[ℂ] P)
    (tm : ℕ → ℝ) (T α Q b qbar ε : ℝ) (hmesh : IsMesh tm M T) (hT : 0 < T) (hα : 0 < α)
    (hQ : 1 ≤ Q) (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hUJ : IsUnitary UJ) (hD : ∀ r < M, IsUnitary (D r))
    (hRight : ∀ r < M, (1 - D r) ∘L R1 r = 1)
    (hLeft : ∀ r < M, R1 r ∘L (1 - D r) = 1) (hR1 : ∀ r < M, ‖R1 r‖ ≤ Q)
    (hBoundary : ∀ r < M, (UJ ∘L iota0)† ∘L R1 r ∘L (UJ ∘L iota0) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • ((α : ℂ)⁻¹ • Hs r)))
    (hEndpoint : ∀ r < M, ‖R1 r ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2)
    (hSelf : ∀ r < M, star (Hs r) = Hs r) (hHs : ∀ r < M, ‖Hs r‖ ≤ α)
    (Hp : ℕ → ℝ → P →L[ℂ] P) (hHp : ∀ r u, Hp r u = Hs r) :
    (∀ᵐ u, u ∈ Icc 0 T → star (glue Hp tm M u) = glue Hp tm M u) ∧
    IntervalIntegrable (glue Hp tm M) volume 0 T ∧
    ∑ r ∈ Finset.range M, ∫ u in tm r..tm (r + 1), ‖glue Hp tm M u - Hs r‖ = 0 ∧
    ∃ U : ℝ → P →L[ℂ] P, IsPropagator (glue Hp tm M) U T ∧
      ‖runT UJ (fun k => D (slotPiece tm T (2 ^ meshExponent α T ε M) M k))
          (simCircuitT a (α * T) Q qbar (ε / 2) (meshExponent α T ε M)) ∘L io - io ∘L U T‖ ≤
        ε := by
  obtain rfl : Hp = fun r _ => Hs r := funext fun r => funext fun u => hHp r u
  obtain ⟨h1, h2, -⟩ := mesh_exponent_spec α T ε M hT hε
  obtain ⟨U, hU⟩ := TimeDependentExtensions.exists_piecewise_propagator (fun r (_ : ℝ) => Hs r)
    hmesh.zero hmesh.mono M (fun _ _ => continuousOn_const)
  have hint : ∀ r < M, IntervalIntegrable ((fun r (_ : ℝ) => Hs r) r) volume (tm r)
      (tm (r + 1)) := fun _ _ => intervalIntegrable_const
  have hU' := IntegrablePathSimulation.Propagator.isPropagator_glue hmesh hU hint
  have hae := IntegrablePathSimulation.Propagator.ae_star_glue hmesh
    (fun r hr (_ : ℝ) _ => hSelf r hr)
  have hgi := IntegrablePathSimulation.Propagator.intervalIntegrable_glue hmesh hint
  have hcert : ∑ r ∈ Finset.range M, ∫ u in tm r..tm (r + 1),
      ‖glue (fun r (_ : ℝ) => Hs r) tm M u - Hs r‖ = 0 := by
    rw [IntegrablePathSimulation.Propagator.sum_integral_glue Hs hmesh]
    simp
  obtain ⟨-, -, -, -, -, -, -, -, hI, -⟩ := time_simulation_mesh a (meshExponent α T ε M) M hM
    UJ D R1 Hs tm T α Q b qbar ε hmesh hT hα hQ hqQ hε hε1 h1 h2 hUJ hD hRight hLeft hR1
    hBoundary hEndpoint hbq hSelf hHs
  refine ⟨hae, hgi, hcert, U, hU', hI _ U hae hgi ?_ hU'⟩
  rw [hcert]
  linarith

/-- **An admissible exponent of the native mesh theorem**: `m = slotExponent (steps (α T)
(ε/12)) (8 M α T/ε)` meets the subdivision condition `steps (α T) (ε/12) ≤ 2^m` and the
rounding condition `8 M α T ≤ ε 2^m` of `native_time_simulation_mesh`. -/
theorem slotExponent_native_mesh_spec (α T ε : ℝ) (M : ℕ) (hε : 0 < ε) :
    TimeSchedule.steps (α * T) (ε / 12) ≤
        2 ^ slotExponent (TimeSchedule.steps (α * T) (ε / 12)) (8 * M * α * T / ε) ∧
      8 * M * α * T ≤
        ε * 2 ^ slotExponent (TimeSchedule.steps (α * T) (ε / 12)) (8 * M * α * T / ε) := by
  obtain ⟨h1, h2, -⟩ :=
    slotExponent_round_spec _ (TimeSchedule.steps_pos _ _) (8 * M * α * T) ε hε
  exact ⟨h1, h2⟩

/-- **An admissible exponent of the binary-data mesh theorem**: with `τ' = time s T γ = √s T/γ`,
`m = slotExponent (steps τ' (ε/12)) (8 M τ'/ε)` meets the subdivision condition
`steps τ' (ε/12) ≤ 2^m` and the rounding condition `8 M τ' ≤ ε 2^m` of
`binary_time_simulation_mesh` and `binary_time_simulation_budget_mesh`. -/
theorem slotExponent_binary_mesh_spec (s T γ ε : ℝ) (M : ℕ) (hε : 0 < ε) :
    TimeSchedule.steps (CayleyClockInterface.time s T γ) (ε / 12) ≤
        2 ^ slotExponent (TimeSchedule.steps (CayleyClockInterface.time s T γ) (ε / 12))
          (8 * M * CayleyClockInterface.time s T γ / ε) ∧
      8 * M * CayleyClockInterface.time s T γ ≤
        ε * 2 ^ slotExponent (TimeSchedule.steps (CayleyClockInterface.time s T γ) (ε / 12))
          (8 * M * CayleyClockInterface.time s T γ / ε) := by
  obtain ⟨h1, h2, -⟩ := slotExponent_round_spec _ (TimeSchedule.steps_pos _ _)
    (8 * M * CayleyClockInterface.time s T γ) ε hε
  exact ⟨h1, h2⟩

/-! ### Dissipative equations -/

namespace ODE

open GateODE.Time (TParams TOracles gens)

/-- **The released time-dependent solver as a corollary** (Theorem `ode:thm:gates`,
time-dependent part): every instance of the released `GateODE.Time.TParams.InstanceOK` has the
released guarantee `GateODE.Time.TParams.Outcome`, through `certified_of_instanceOK` and
`ode_time_solver_certified`. -/
theorem released_time_solver_outcome [FiniteDimensional ℂ P] (p : TParams) (hp : p.PublicOK)
    (v : P) (hv : ‖v‖ = 1) (σ : TOracles p.a p.m p.l P) (Hs Ls : ℕ → P →L[ℂ] P)
    (G : ℝ → P →L[ℂ] P) (b x : ℝ → P) (bs : ℕ → P) (βG δG βb δb bmax : ℝ)
    (hI : p.InstanceOK v σ Hs Ls G b x bs βG δG βb δb bmax) :
    p.Outcome v hv hp.g_ge σ (x p.T) := by
  obtain ⟨hC, hx, hG, hGi, hbi, hb0, hb, hne, hB, hc⟩ := certified_of_instanceOK p hp hI
  exact (ode_time_solver_certified p hp v hv).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    σ Hs Ls (fun _ => G) (fun _ => b) x bs bmax hC hx hG hGi hbi hb0 hb hne hB hc

omit [CompleteSpace P] in
/-- **The mesh certificate of the samples without forcing** (Theorem `ode:thm:gates`,
time-dependent part, extended by uniform refinement to nonuniform meshes): with generator pieces
equal to the mesh samples `L_q + i H_q` and zero forcing, the mesh certificate is the refinement
cost `Mm h Λ r₀`. -/
theorem meshCertificate_samples_zero_forcing (p : TParams) (tm : ℕ → ℝ) (Mm : ℕ)
    (Hm Lm : ℕ → P →L[ℂ] P) (r₀ bmax : ℝ) :
    meshCertificate p tm Mm Hm Lm (fun _ => 0) (fun q _ => gens Hm Lm q) (fun _ _ => 0) r₀ bmax =
      Mm * (p.T / p.M) * (p.lamH + p.lamD) * r₀ := by
  simp [meshCertificate]

omit [CompleteSpace P] in
/-- **The certified budget on a mesh is met without forcing** (Theorem `ode:thm:gates`,
time-dependent part, extended by uniform refinement to nonuniform meshes): with generator pieces
equal to the mesh samples and zero forcing, `meshCertificate ≤ ε B/(2000 g)` for the source mass
`B = ‖x(0)‖` of the slot data whenever `2000 g Mm Λ T ≤ ε 2^m`. -/
theorem meshCertificate_zero_forcing_le (p : TParams) (hp : p.PublicOK) (tm : ℕ → ℝ) (Mm : ℕ)
    (Hm Lm : ℕ → P →L[ℂ] P) (x0 : P) (bmax : ℝ)
    (hm : 2000 * p.g * Mm * (p.lamH + p.lamD) * p.T ≤ p.ε * p.M) :
    meshCertificate p tm Mm Hm Lm (fun _ => 0) (fun q _ => gens Hm Lm q) (fun _ _ => 0) ‖x0‖
        bmax ≤ p.ε * p.mass x0 (fun _ => 0) / (2000 * p.g) := by
  rw [meshCertificate_samples_zero_forcing, p.mass_eq hp.T_pos.le]
  simp only [norm_zero, Finset.sum_const_zero, mul_zero, add_zero]
  have hg : 0 < p.g := lt_of_lt_of_le one_pos hp.g_ge
  have hM : (0 : ℝ) < p.M := by exact_mod_cast p.M_pos
  have hx := norm_nonneg x0
  have key : (Mm : ℝ) * (p.T / p.M) * (p.lamH + p.lamD) * (2000 * p.g) ≤ p.ε := by
    have e : (Mm : ℝ) * (p.T / p.M) * (p.lamH + p.lamD) * (2000 * p.g) =
        2000 * p.g * Mm * (p.lamH + p.lamD) * p.T / p.M := by
      field_simp
    rw [e, div_le_iff₀ hM]
    exact hm
  rw [le_div_iff₀ (by positivity)]
  nlinarith [key, hx]

omit [CompleteSpace P] in
/-- **The quadrature of one mesh interval is kept** (Theorem `ode:thm:gates`, time-dependent
part, extended by uniform refinement to nonuniform meshes): for one interval (`Mm = 1`) and
pieces equal to the samples, the mesh certificate is `(Λ (T + h)² + h) ‖b̃‖ + h Λ (r₀ + T ‖b̃‖)`;
its quadrature term `Λ (T + h)² ‖b̃‖` does not decrease with `m` (compare
`slotCertificate_samples`). -/
theorem meshCertificate_one_interval (p : TParams) (Hm Lm : ℕ → P →L[ℂ] P) (bm : P)
    (r₀ bmax : ℝ) :
    meshCertificate p (fun r => if r = 0 then 0 else p.T) 1 Hm Lm (fun _ => bm)
        (fun q _ => gens Hm Lm q) (fun _ _ => bm) r₀ bmax =
      ((p.lamH + p.lamD) * (p.T + p.T / p.M) ^ 2 + p.T / p.M) * ‖bm‖ +
        1 * (p.T / p.M) * (p.lamH + p.lamD) * (r₀ + p.T * ‖bm‖) := by
  simp [meshCertificate]

omit [CompleteSpace P] in
/-- **The quadrature on the uniform slots** (Theorem `ode:thm:gates`, time-dependent part): for
pieces equal to the samples and a constant forcing sample, the slot certificate is
`Λ h²/2 · 2^m ‖b̃‖ = Λ T h ‖b̃‖ / 2`. -/
theorem slotCertificate_samples (p : TParams) (Hs Ls : ℕ → P →L[ℂ] P) (bm : P) (r₀ bmax : ℝ) :
    slotCertificate p Hs Ls (fun _ => bm) (fun k _ => gens Hs Ls k) (fun _ _ => bm) r₀ bmax =
      (p.lamH + p.lamD) * (p.T / p.M) ^ 2 / 2 * (p.M * ‖bm‖) := by
  simp [slotCertificate]

/-- **Classical piecewise solutions exist** for generator and forcing pieces equal to the mesh
samples (Theorem `ode:thm:gates`, time-dependent part, extended by uniform refinement to
nonuniform meshes; the released `TimeDependentExtensions.ODE.exists_piecewise_solution`). -/
theorem exists_mesh_solution (tm : ℕ → ℝ) (Mm : ℕ) (T : ℝ) (hmesh : IsMesh tm Mm T)
    (Hm Lm : ℕ → P →L[ℂ] P) (bm : ℕ → P) (x0 : P) :
    ∃ x : ℝ → P, x 0 = x0 ∧ ∀ q < Mm,
      TimeDependentODE.SolvesODE (fun _ => gens Hm Lm q) (fun _ => bm q) x (tm q)
        (tm (q + 1)) :=
  TimeDependentExtensions.ODE.exists_piecewise_solution (fun q _ => gens Hm Lm q)
    (fun q _ => bm q) hmesh.zero hmesh.mono Mm (fun _ _ => continuousOn_const)
    (fun _ _ => continuousOn_const) x0

end ODE

end

end SparseHamiltonian.GateMesh
