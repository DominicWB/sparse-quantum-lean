import GateEfficientMesh.Slots
import GateEfficientTimeDependent.Theorem

/-!
# Exact gates: integrated certificates and nonuniform meshes

A package extension, Theorem `hs:thm:time` with the circuit of `hs:thm:gates`, states, for the
time-dependent setting of Theorem `hs:thm:time` on a uniform mesh of `M = 2^m ≥ 2` slots, that the
circuit with slot-selected private Cayley operations has full-output error at most `ε` relative to
`U_H(T, 0)` (in the manuscript Theorem `hs:thm:gates` is "a time-independent result", and a circuit
of this kind is the single-label case of Lemma `ode:lem:gate-select`). The released theorem
`GateCircuit.SlotSim.gate_efficient_time_simulation`
proves this for Lipschitz paths with uniform sample errors. The paragraphs after the proof of
Theorem `hs:thm:time` state that a known bound on the integrated sample errors suffices. This module
proves the gate-level statement in that generality, for the released circuit `simCircuitT` with the
released counts:

* `slot_product_error`: the released circuit is within `ε + ‖∏_k exp(-i (t/2^m) H̃_k) - U‖`
  of every operator `U` on clean inputs (from the released `simulationT`);
* `time_simulation_certified`: uniform slots; for every Hermitian path with an integral-sense
  propagator, and for every classical piecewise path with one piece per slot, the full output
  is within `ε` of `U(t)` whenever the certificate `∑_k ∫_{kt/2^m}^{(k+1)t/2^m} ‖H(u) - H̃_k‖ du`
  is at most `ε / 2`; only the subdivision condition `steps (α t) (ε/6) ≤ 2^m` is required;
* `time_simulation_mesh`: a nonuniform mesh `0 = t_0 ≤ ⋯ ≤ t_M = T` with one sample per
  interval; slot `k` applies the supplied private operation of the sample of the interval
  containing `k T / 2^m` (`slotPiece`); error `ε` under the mesh certificate `≤ ε/4` and the
  rounding condition `4 M α T ≤ ε 2^m`; `mesh_exponent_spec` gives an explicit `m`, and
  `slotExponent_round_spec` the explicit `m` of the native and binary-data mesh theorems;
* `time_simulation_lipschitz`: the released Lipschitz conclusion as a corollary.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateMesh

noncomputable section

open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim GateCircuit.SlotSim
open MeasureTheory Set
open TimeDependentExtensions (IsMesh slotPiece slotPiece_lt IsPiecewisePropagator)
open IntegrablePathSimulation.Propagator (IsPropagator)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### The circuit against the slot product -/

/-- **The released circuit against any operator.** For slot-selected private operations `D k`
with the clock promises of the released analysis for the normalised samples `H̃_k / α`, the
released circuit `simCircuitT a (α t) Q qbar ε m` with `steps (α t) (ε/3) ≤ 2^m` is within
`ε + ‖∏_k exp(-i (t/2^m) H̃_k) - U‖` of `U` on clean inputs, for every operator `U`. -/
theorem slot_product_error (a m : ℕ) (UJ : Vsp a P →L[ℂ] Vsp a P)
    (D R1 : ℕ → Vsp a P →L[ℂ] Vsp a P) (Hs : ℕ → P →L[ℂ] P) (t α Q b qbar ε : ℝ)
    (ht : 0 ≤ t) (hα : 0 < α) (hQ : 1 ≤ Q) (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hm : TimeSchedule.steps (α * t) (ε / 3) ≤ 2 ^ m)
    (hUJ : IsUnitary UJ) (hD : ∀ k < 2 ^ m, IsUnitary (D k))
    (hRight : ∀ k < 2 ^ m, (1 - D k) ∘L R1 k = 1)
    (hLeft : ∀ k < 2 ^ m, R1 k ∘L (1 - D k) = 1) (hR1 : ∀ k < 2 ^ m, ‖R1 k‖ ≤ Q)
    (hBoundary : ∀ k < 2 ^ m, (UJ ∘L iota0)† ∘L R1 k ∘L (UJ ∘L iota0) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • ((α : ℂ)⁻¹ • Hs k)))
    (hEndpoint : ∀ k < 2 ^ m, ‖R1 k ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2)
    (hSelf : ∀ k < 2 ^ m, star (Hs k) = Hs k) (hHs : ∀ k < 2 ^ m, ‖Hs k‖ ≤ α)
    (U : P →L[ℂ] P) :
    ‖runT UJ D (simCircuitT a (α * t) Q qbar ε m) ∘L io - io ∘L U‖ ≤
      ε + ‖slotEvolution Hs t m - U‖ := by
  have hαC : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have hnSelf : ∀ k < 2 ^ m, star ((α : ℂ)⁻¹ • Hs k) = (α : ℂ)⁻¹ • Hs k := by
    intro k hk
    rw [star_smul, hSelf k hk, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hnNorm : ∀ k < 2 ^ m, ‖(α : ℂ)⁻¹ • Hs k‖ ≤ 1 := by
    intro k hk
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hα.le,
      inv_mul_le_iff₀ hα, mul_one]
    exact hHs k hk
  obtain ⟨-, -, -, -, -, hsim, -⟩ := simulationT (P := P) a m UJ D R1
    (fun k => (α : ℂ)⁻¹ • Hs k) hUJ hD (α * t) Q b qbar ε (mul_nonneg hα.le ht) hQ hRight hLeft
    hR1 hBoundary hnSelf hnNorm hEndpoint hbq hqQ hε hε1 hm
  have hexp : (fun k => NormedSpace.exp ((-Complex.I * (stepW (α * t) m : ℂ)) •
      ((α : ℂ)⁻¹ • Hs k))) =
      fun k => NormedSpace.exp ((-Complex.I * ((t / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • Hs k) := by
    funext k
    congr 1
    rw [smul_smul]
    congr 1
    unfold stepW
    push_cast
    field_simp
  rw [hexp] at hsim
  have hio := io_norm_le (a := a) (m := m) (r := simR Q (α * t) qbar ε)
    (K := a + m + 2 * simR Q (α * t) qbar ε) (P := P)
  have h2 : ‖(io : P →L[ℂ] Reg (Wire a m (simR Q (α * t) qbar ε)
      (a + m + 2 * simR Q (α * t) qbar ε)) P) ∘L slotEvolution Hs t m - io ∘L U‖ ≤
      ‖slotEvolution Hs t m - U‖ := by
    rw [← comp_sub]
    refine (opNorm_comp_le _ _).trans ?_
    calc _ ≤ 1 * ‖slotEvolution Hs t m - U‖ :=
          mul_le_mul_of_nonneg_right hio (norm_nonneg _)
      _ = _ := one_mul _
  have key := norm_sub_le_norm_sub_add_norm_sub
    (runT UJ D (simCircuitT a (α * t) Q qbar ε m) ∘L io)
    ((io : P →L[ℂ] Reg (Wire a m (simR Q (α * t) qbar ε)
      (a + m + 2 * simR Q (α * t) qbar ε)) P) ∘L slotEvolution Hs t m) (io ∘L U)
  have hsim' : ‖runT UJ D (simCircuitT a (α * t) Q qbar ε m) ∘L io -
      (io : P →L[ℂ] Reg (Wire a m (simR Q (α * t) qbar ε)
        (a + m + 2 * simR Q (α * t) qbar ε)) P) ∘L slotEvolution Hs t m‖ ≤ ε := hsim
  linarith

/-! ### Uniform slots -/

/-- **Gate-efficient time-dependent simulation under the integrated certificate, exact gates**
(Theorem `hs:thm:time` with the circuit of `hs:thm:gates`, with the certificate of the paragraphs
after the proof of Theorem `hs:thm:time`).

The released circuit `simCircuitT a (α t) Q qbar (ε/2) m` is fixed by the public numbers. Let
`U_J` and the slot-selected private operations `D k` be unitaries such that every `D k`
(`k < 2^m`) carries the clock promise of the released analysis for the normalised represented
sample `H̃_k / α` (`H̃_k` self-adjoint, `‖H̃_k‖ ≤ α`). Under the subdivision condition
`steps (α t) (ε/6) ≤ 2^m` alone, the circuit consists of valid elementary instructions, makes
exactly `6d` private calls and `12d` calls of `U_J` or `U_J†`, uses at most
`200 (d+1)(a+m+r+1)` elementary gates on `2a + 3m + 6r + 3` qubits, with
`d ≤ 128 (α t qbar + Q (1 + log (6/ε)))` and `2d + 2 ≤ 2^r ≤ 4 (d+1)`, and its full output on
clean inputs is within `ε` of `U(t)`

* for every path `H` that is self-adjoint at almost every time of `[0, t]` and interval
  integrable, and every integral-sense propagator `U` of `H`, and
* for every piecewise path with one piece `H_k` per slot, self-adjoint and interval integrable
  on the closed slot, and every classical piecewise propagator `U`,

whenever `∑_k ∫_{kt/2^m}^{(k+1)t/2^m} ‖H(u) - H̃_k‖ du ≤ ε / 2`. -/
theorem time_simulation_certified (a m : ℕ) (UJ : Vsp a P →L[ℂ] Vsp a P)
    (D R1 : ℕ → Vsp a P →L[ℂ] Vsp a P) (Hs : ℕ → P →L[ℂ] P) (t α Q b qbar ε : ℝ)
    (ht : 0 ≤ t) (hα : 0 < α) (hQ : 1 ≤ Q) (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hCayley : TimeSchedule.steps (α * t) (ε / 6) ≤ 2 ^ m)
    (hUJ : IsUnitary UJ) (hD : ∀ k < 2 ^ m, IsUnitary (D k))
    (hRight : ∀ k < 2 ^ m, (1 - D k) ∘L R1 k = 1)
    (hLeft : ∀ k < 2 ^ m, R1 k ∘L (1 - D k) = 1) (hR1 : ∀ k < 2 ^ m, ‖R1 k‖ ≤ Q)
    (hBoundary : ∀ k < 2 ^ m, (UJ ∘L iota0)† ∘L R1 k ∘L (UJ ∘L iota0) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • ((α : ℂ)⁻¹ • Hs k)))
    (hEndpoint : ∀ k < 2 ^ m, ‖R1 k ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2)
    (hSelf : ∀ k < 2 ^ m, star (Hs k) = Hs k) (hHs : ∀ k < 2 ^ m, ‖Hs k‖ ≤ α) :
    (∀ g ∈ simCircuitT a (α * t) Q qbar (ε / 2) m, g.Valid Wire.anc) ∧
    nPriv (simCircuitT a (α * t) Q qbar (ε / 2) m) = 6 * fDeg Q (α * t) qbar (ε / 2) ∧
    nUJ (simCircuitT a (α * t) Q qbar (ε / 2) m) = 12 * fDeg Q (α * t) qbar (ε / 2) ∧
    nGates (simCircuitT a (α * t) Q qbar (ε / 2) m) ≤
      200 * (fDeg Q (α * t) qbar (ε / 2) + 1) * (a + m + simR Q (α * t) qbar (ε / 2) + 1) ∧
    Fintype.card (Wire a m (simR Q (α * t) qbar (ε / 2))
        (a + m + 2 * simR Q (α * t) qbar (ε / 2))) =
      2 * a + 3 * m + 6 * simR Q (α * t) qbar (ε / 2) + 3 ∧
    (fDeg Q (α * t) qbar (ε / 2) : ℝ) ≤ 128 * (α * t * qbar + Q * (1 + Real.log (6 / ε))) ∧
    2 * fDeg Q (α * t) qbar (ε / 2) + 2 ≤ 2 ^ simR Q (α * t) qbar (ε / 2) ∧
    2 ^ simR Q (α * t) qbar (ε / 2) ≤ 4 * (fDeg Q (α * t) qbar (ε / 2) + 1) ∧
    (∀ H U : ℝ → P →L[ℂ] P, (∀ᵐ u, u ∈ Icc 0 t → star (H u) = H u) →
      IntervalIntegrable H volume 0 t →
      ∑ k ∈ Finset.range (2 ^ m), ∫ u in slotMesh t m k..slotMesh t m (k + 1), ‖H u - Hs k‖ ≤
        ε / 2 →
      IsPropagator H U t →
      ‖runT UJ D (simCircuitT a (α * t) Q qbar (ε / 2) m) ∘L io - io ∘L U t‖ ≤ ε) ∧
    (∀ (Hp : ℕ → ℝ → P →L[ℂ] P) (U : ℝ → P →L[ℂ] P),
      (∀ k < 2 ^ m, ∀ u ∈ Icc (slotMesh t m k) (slotMesh t m (k + 1)),
        star (Hp k u) = Hp k u) →
      (∀ k < 2 ^ m, IntervalIntegrable (Hp k) volume (slotMesh t m k) (slotMesh t m (k + 1))) →
      ∑ k ∈ Finset.range (2 ^ m),
          ∫ u in slotMesh t m k..slotMesh t m (k + 1), ‖Hp k u - Hs k‖ ≤ ε / 2 →
      IsPiecewisePropagator Hp (slotMesh t m) (2 ^ m) U →
      ‖runT UJ D (simCircuitT a (α * t) Q qbar (ε / 2) m) ∘L io - io ∘L U t‖ ≤ ε) := by
  have hε2 : 0 < ε / 2 := by linarith
  have hε21 : ε / 2 ≤ 1 := by linarith
  have hm : TimeSchedule.steps (α * t) (ε / 2 / 3) ≤ 2 ^ m := by
    rw [show ε / 2 / 3 = ε / 6 by ring]
    exact hCayley
  have hnSelf : ∀ k < 2 ^ m, star ((α : ℂ)⁻¹ • Hs k) = (α : ℂ)⁻¹ • Hs k := by
    intro k hk
    rw [star_smul, hSelf k hk, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hnNorm : ∀ k < 2 ^ m, ‖(α : ℂ)⁻¹ • Hs k‖ ≤ 1 := by
    intro k hk
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hα.le,
      inv_mul_le_iff₀ hα, mul_one]
    exact hHs k hk
  obtain ⟨hvalid, hP, hJ, hG, hW, -, hdeg⟩ := simulationT (P := P) a m UJ D R1
    (fun k => (α : ℂ)⁻¹ • Hs k) hUJ hD (α * t) Q b qbar (ε / 2) (mul_nonneg hα.le ht) hQ hRight
    hLeft hR1 hBoundary hnSelf hnNorm hEndpoint hbq hqQ hε2 hε21 hm
  obtain ⟨hr1, _, hr2⟩ := simR_spec Q (α * t) qbar (ε / 2)
  have hlog : (1 : ℝ) / (ε / 2 / 3) = 6 / ε := by
    field_simp
    ring
  rw [hlog] at hdeg
  have herr := fun U => slot_product_error a m UJ D R1 Hs t α Q b qbar (ε / 2) ht hα hQ hqQ hε2
    hε21 hm hUJ hD hRight hLeft hR1 hBoundary hEndpoint hbq hSelf hHs U
  refine ⟨hvalid, hP, hJ, hG, hW, hdeg, hr1, hr2, fun H U hH hint hcert hU => ?_,
    fun Hp U hH hint hcert hU => ?_⟩
  · have h1 := herr (U t)
    have h2 := slot_error_integral Hs ht m hU hH hSelf hint
    rw [norm_sub_rev] at h2
    linarith
  · have h1 := herr (U t)
    have h2 := slot_error_piecewise Hs ht m hU hH hSelf hint
    rw [norm_sub_rev] at h2
    linarith

/-! ### Nonuniform meshes -/

/-- An explicit slot exponent for a mesh of `M` intervals: the least power of two that is at
least the subdivision count `steps (α T) (ε/6)` and the rounding count `⌈4 M α T / ε⌉`. It is
the released `meshExp` with the rounding rate `M α / T` in place of the Lipschitz bound. -/
def meshExponent (α T ε : ℝ) (M : ℕ) : ℕ := meshExp α T (M * α / T) ε

/-- The explicit slot exponent meets the subdivision and rounding conditions with less than a
factor two to spare. -/
theorem mesh_exponent_spec (α T ε : ℝ) (M : ℕ) (hT : 0 < T) (hε : 0 < ε) :
    TimeSchedule.steps (α * T) (ε / 6) ≤ 2 ^ meshExponent α T ε M ∧
    4 * M * α * T ≤ ε * 2 ^ meshExponent α T ε M ∧
    2 ^ meshExponent α T ε M <
      2 * max (TimeSchedule.steps (α * T) (ε / 6)) ⌈4 * M * α * T / ε⌉₊ := by
  obtain ⟨h1, h2, h3⟩ := meshExp_spec α T (M * α / T) ε hε
  have e : 4 * (M * α / T) * T ^ 2 = 4 * M * α * T := by
    field_simp
  rw [e] at h2 h3
  exact ⟨h1, h2, h3⟩

/-- The least slot exponent whose clock of `2^m` slots meets a subdivision count `N₁ ≥ 1` and a
real bound `x`: `m = ⌈log₂ max (N₁, ⌈x⌉)⌉` (for the native and binary-data circuits on a mesh,
`N₁ = steps (α T) (ε/12)` and `x = 8 M α T / ε`). -/
def slotExponent (N₁ : ℕ) (x : ℝ) : ℕ := Nat.clog 2 (max N₁ ⌈x⌉₊)

/-- The slot exponent meets both bounds with less than a factor two to spare. -/
theorem slotExponent_spec (N₁ : ℕ) (x : ℝ) (hN₁ : 1 ≤ N₁) :
    N₁ ≤ 2 ^ slotExponent N₁ x ∧ x ≤ 2 ^ slotExponent N₁ x ∧
      2 ^ slotExponent N₁ x < 2 * max N₁ ⌈x⌉₊ := by
  have hle : max N₁ ⌈x⌉₊ ≤ 2 ^ slotExponent N₁ x := Nat.le_pow_clog (by norm_num) _
  refine ⟨(le_max_left _ _).trans hle, ?_, two_pow_clog_lt _ (hN₁.trans (le_max_left _ _))⟩
  have h1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have h2 : ((⌈x⌉₊ : ℕ) : ℝ) ≤ ((2 ^ slotExponent N₁ x : ℕ) : ℝ) := by
    exact_mod_cast (le_max_right _ _).trans hle
  push_cast at h2
  linarith

/-- **An explicit admissible slot exponent for the native and binary mesh theorems.** For a
subdivision count `N₁ ≥ 1` (`steps (α T) (ε/12)` in `native_time_simulation_mesh`,
`steps τ' (ε/12)` in `binary_time_simulation_mesh`) and a rounding cost `c` (`8 M α T`,
respectively `8 M τ'`), the exponent `m = slotExponent N₁ (c/ε)` satisfies the subdivision
condition `N₁ ≤ 2^m` and the rounding condition `c ≤ ε 2^m`, with
`2^m < 2 max(N₁, ⌈c/ε⌉)`. -/
theorem slotExponent_round_spec (N₁ : ℕ) (hN₁ : 1 ≤ N₁) (c ε : ℝ) (hε : 0 < ε) :
    N₁ ≤ 2 ^ slotExponent N₁ (c / ε) ∧ c ≤ ε * 2 ^ slotExponent N₁ (c / ε) ∧
      2 ^ slotExponent N₁ (c / ε) < 2 * max N₁ ⌈c / ε⌉₊ := by
  obtain ⟨h1, h2, h3⟩ := slotExponent_spec N₁ (c / ε) hN₁
  refine ⟨h1, ?_, h3⟩
  rw [div_le_iff₀ hε] at h2
  linarith

/-- **Gate-efficient time-dependent simulation on a nonuniform mesh, exact gates** (Theorem
`hs:thm:time` with the circuit of `hs:thm:gates`, extended by uniform refinement to nonuniform
meshes with breakpoints, with the integrated certificate).

Let `0 = t_0 ≤ ⋯ ≤ t_M = T` be a mesh with `M ≥ 1` intervals and `T > 0`, and let `U_J` and the
private operations `D_r` (`r < M`) carry the clock promises of the released analysis for the
normalised samples `H̃_r / α` (`H̃_r` self-adjoint, `‖H̃_r‖ ≤ α`). The uniform clock has `2^m`
slots; slot `k` applies the supplied operation `D_{σ k}` of the interval `σ k = slotPiece` that
contains `k T / 2^m` (the slot-selected operation of the exact-gate model). Under the
subdivision condition `steps (α T) (ε/6) ≤ 2^m` and the rounding condition
`4 M α T ≤ ε 2^m`, the released circuit `simCircuitT a (α T) Q qbar (ε/2) m` has the released
counts, and its full output is within `ε` of `U(T)` for every path that is self-adjoint at
almost every time and interval integrable (integral-sense propagators), and for every piecewise
path with one piece per mesh interval (classical piecewise propagators), whenever the mesh
certificate `∑_r ∫_{t_r}^{t_{r+1}} ‖H(u) - H̃_r‖ du` is at most `ε / 4`. The mesh enters the
counts only through `m`. -/
theorem time_simulation_mesh (a m M : ℕ) (hM : 0 < M) (UJ : Vsp a P →L[ℂ] Vsp a P)
    (D R1 : ℕ → Vsp a P →L[ℂ] Vsp a P) (Hs : ℕ → P →L[ℂ] P) (tm : ℕ → ℝ)
    (T α Q b qbar ε : ℝ) (hmesh : IsMesh tm M T) (hT : 0 < T) (hα : 0 < α) (hQ : 1 ≤ Q)
    (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hCayley : TimeSchedule.steps (α * T) (ε / 6) ≤ 2 ^ m)
    (hRound : 4 * M * α * T ≤ ε * 2 ^ m)
    (hUJ : IsUnitary UJ) (hD : ∀ r < M, IsUnitary (D r))
    (hRight : ∀ r < M, (1 - D r) ∘L R1 r = 1)
    (hLeft : ∀ r < M, R1 r ∘L (1 - D r) = 1) (hR1 : ∀ r < M, ‖R1 r‖ ≤ Q)
    (hBoundary : ∀ r < M, (UJ ∘L iota0)† ∘L R1 r ∘L (UJ ∘L iota0) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • ((α : ℂ)⁻¹ • Hs r)))
    (hEndpoint : ∀ r < M, ‖R1 r ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2)
    (hSelf : ∀ r < M, star (Hs r) = Hs r) (hHs : ∀ r < M, ‖Hs r‖ ≤ α) :
    (∀ g ∈ simCircuitT a (α * T) Q qbar (ε / 2) m, g.Valid Wire.anc) ∧
    nPriv (simCircuitT a (α * T) Q qbar (ε / 2) m) = 6 * fDeg Q (α * T) qbar (ε / 2) ∧
    nUJ (simCircuitT a (α * T) Q qbar (ε / 2) m) = 12 * fDeg Q (α * T) qbar (ε / 2) ∧
    nGates (simCircuitT a (α * T) Q qbar (ε / 2) m) ≤
      200 * (fDeg Q (α * T) qbar (ε / 2) + 1) * (a + m + simR Q (α * T) qbar (ε / 2) + 1) ∧
    Fintype.card (Wire a m (simR Q (α * T) qbar (ε / 2))
        (a + m + 2 * simR Q (α * T) qbar (ε / 2))) =
      2 * a + 3 * m + 6 * simR Q (α * T) qbar (ε / 2) + 3 ∧
    (fDeg Q (α * T) qbar (ε / 2) : ℝ) ≤ 128 * (α * T * qbar + Q * (1 + Real.log (6 / ε))) ∧
    2 * fDeg Q (α * T) qbar (ε / 2) + 2 ≤ 2 ^ simR Q (α * T) qbar (ε / 2) ∧
    2 ^ simR Q (α * T) qbar (ε / 2) ≤ 4 * (fDeg Q (α * T) qbar (ε / 2) + 1) ∧
    (∀ H U : ℝ → P →L[ℂ] P, (∀ᵐ u, u ∈ Icc 0 T → star (H u) = H u) →
      IntervalIntegrable H volume 0 T →
      ∑ r ∈ Finset.range M, ∫ u in tm r..tm (r + 1), ‖H u - Hs r‖ ≤ ε / 4 →
      IsPropagator H U T →
      ‖runT UJ (fun k => D (slotPiece tm T (2 ^ m) M k))
          (simCircuitT a (α * T) Q qbar (ε / 2) m) ∘L io - io ∘L U T‖ ≤ ε) ∧
    (∀ (Hp : ℕ → ℝ → P →L[ℂ] P) (U : ℝ → P →L[ℂ] P),
      (∀ r < M, ∀ u ∈ Icc (tm r) (tm (r + 1)), star (Hp r u) = Hp r u) →
      (∀ r < M, IntervalIntegrable (Hp r) volume (tm r) (tm (r + 1))) →
      ∑ r ∈ Finset.range M, ∫ u in tm r..tm (r + 1), ‖Hp r u - Hs r‖ ≤ ε / 4 →
      IsPiecewisePropagator Hp tm M U →
      ‖runT UJ (fun k => D (slotPiece tm T (2 ^ m) M k))
          (simCircuitT a (α * T) Q qbar (ε / 2) m) ∘L io - io ∘L U T‖ ≤ ε) := by
  have hσ : ∀ k, slotPiece tm T (2 ^ m) M k < M := fun k => slotPiece_lt hM k
  obtain ⟨hvalid, hP, hJ, hG, hW, hdeg, hr1, hr2, -, -⟩ := time_simulation_certified a m UJ
    (fun k => D (slotPiece tm T (2 ^ m) M k)) (fun k => R1 (slotPiece tm T (2 ^ m) M k))
    (fun k => Hs (slotPiece tm T (2 ^ m) M k)) T α Q b qbar ε hT.le hα hQ hqQ hε hε1 hCayley hUJ
    (fun k _ => hD _ (hσ k)) (fun k _ => hRight _ (hσ k)) (fun k _ => hLeft _ (hσ k))
    (fun k _ => hR1 _ (hσ k)) (fun k _ => hBoundary _ (hσ k)) (fun k _ => hEndpoint _ (hσ k))
    hbq (fun k _ => hSelf _ (hσ k)) (fun k _ => hHs _ (hσ k))
  have hε2 : 0 < ε / 2 := by linarith
  have hε21 : ε / 2 ≤ 1 := by linarith
  have hm : TimeSchedule.steps (α * T) (ε / 2 / 3) ≤ 2 ^ m := by
    rw [show ε / 2 / 3 = ε / 6 by ring]
    exact hCayley
  have herr := fun U => slot_product_error a m UJ (fun k => D (slotPiece tm T (2 ^ m) M k))
    (fun k => R1 (slotPiece tm T (2 ^ m) M k)) (fun k => Hs (slotPiece tm T (2 ^ m) M k)) T α Q b
    qbar (ε / 2) hT.le hα hQ hqQ hε2 hε21 hm hUJ (fun k _ => hD _ (hσ k))
    (fun k _ => hRight _ (hσ k)) (fun k _ => hLeft _ (hσ k)) (fun k _ => hR1 _ (hσ k))
    (fun k _ => hBoundary _ (hσ k)) (fun k _ => hEndpoint _ (hσ k)) hbq
    (fun k _ => hSelf _ (hσ k)) (fun k _ => hHs _ (hσ k)) U
  have hround : (M : ℝ) * (T / 2 ^ m) * α ≤ ε / 4 := by
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    rw [show (M : ℝ) * (T / 2 ^ m) * α = M * α * T / 2 ^ m by ring, div_le_iff₀ h2]
    linarith
  refine ⟨hvalid, hP, hJ, hG, hW, hdeg, hr1, hr2, fun H U hH hint hcert hU => ?_,
    fun Hp U hH hint hcert hU => ?_⟩
  · have h1 := herr (U T)
    have h2 := mesh_slot_error Hs hM hmesh hT m hU hH hSelf hHs hint
    rw [norm_sub_rev] at h2
    linarith
  · have h1 := herr (U T)
    have h2 := mesh_slot_error_piecewise Hs hM hmesh hT m hU hH hSelf hHs hint
    rw [norm_sub_rev] at h2
    linarith

/-! ### The released Lipschitz form as a corollary -/

/-- **The released Lipschitz statement as a corollary.** Under the hypotheses of the released
`GateCircuit.SlotSim.gate_efficient_time_simulation` (a `β`-Lipschitz Hermitian path, sample
errors `δ` at the slot points, `4 β t² ≤ ε 2^m`, `4 t δ ≤ ε`), the certificate is at most
`ε / 2`, so `time_simulation_certified` gives its error bound for every classical
propagator. -/
theorem time_simulation_lipschitz (a m : ℕ) (UJ : Vsp a P →L[ℂ] Vsp a P)
    (D R1 : ℕ → Vsp a P →L[ℂ] Vsp a P) (Hpath : ℝ → P →L[ℂ] P) (Hs : ℕ → P →L[ℂ] P)
    (t α β δ Q b qbar ε : ℝ) (ht : 0 ≤ t) (hα : 0 < α) (hQ : 1 ≤ Q)
    (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hCayley : TimeSchedule.steps (α * t) (ε / 6) ≤ 2 ^ m)
    (hFreeze : 4 * β * t ^ 2 ≤ ε * 2 ^ m)
    (hUJ : IsUnitary UJ) (hD : ∀ k < 2 ^ m, IsUnitary (D k))
    (hRight : ∀ k < 2 ^ m, (1 - D k) ∘L R1 k = 1)
    (hLeft : ∀ k < 2 ^ m, R1 k ∘L (1 - D k) = 1) (hR1 : ∀ k < 2 ^ m, ‖R1 k‖ ≤ Q)
    (hBoundary : ∀ k < 2 ^ m, (UJ ∘L iota0)† ∘L R1 k ∘L (UJ ∘L iota0) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • ((α : ℂ)⁻¹ • Hs k)))
    (hEndpoint : ∀ k < 2 ^ m, ‖R1 k ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2)
    (hSelf : ∀ k < 2 ^ m, star (Hs k) = Hs k) (hHs : ∀ k < 2 ^ m, ‖Hs k‖ ≤ α)
    (hPath : ∀ u ∈ Icc 0 t, star (Hpath u) = Hpath u)
    (hLip : ∀ u ∈ Icc 0 t, ∀ v ∈ Icc 0 t, ‖Hpath u - Hpath v‖ ≤ β * |u - v|)
    (hVal : ∀ k : ℕ, k < 2 ^ m → ‖Hpath (k * t / 2 ^ m) - Hs k‖ ≤ δ)
    (hValBudget : 4 * t * δ ≤ ε) (U : ℝ → P →L[ℂ] P) (hU0 : U 0 = 1)
    (hU : TimeDependent.SolvesOn Hpath U 0 t) :
    ‖runT UJ D (simCircuitT a (α * t) Q qbar (ε / 2) m) ∘L io - io ∘L U t‖ ≤ ε := by
  obtain ⟨-, -, -, -, -, -, -, -, hint_err, -⟩ := time_simulation_certified a m UJ D R1 Hs t α Q
    b qbar ε ht hα hQ hqQ hε hε1 hCayley hUJ hD hRight hLeft hR1 hBoundary hEndpoint hbq hSelf hHs
  have hint : IntervalIntegrable Hpath volume 0 t :=
    (TimeDependentExtensions.continuousOn_of_lipschitz Hpath hLip).intervalIntegrable_of_Icc ht
  have hcert := slot_certificate_le_of_lipschitz Hpath Hs ht m hLip
    (fun k hk => by simpa [slotMesh] using hVal k hk)
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  have hfr : β * t ^ 2 / (2 * 2 ^ m) ≤ ε / 8 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  exact hint_err Hpath U (ae_of_all _ hPath) hint (by linarith)
    (IntegrablePathSimulation.Propagator.isPropagator_of_solvesOn ht hU0 hU hint)

end

end SparseHamiltonian.GateMesh
