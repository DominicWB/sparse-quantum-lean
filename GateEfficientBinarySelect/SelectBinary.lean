import GateEfficientBinarySelect.SelectNative
import GateEfficientBinarySelect.Pub

/-!
# Lemma `ode:lem:gate-select` from binary data

Lemma `ode:lem:gate-select` for the labels of the time-dependent solver and the private
operations constructed from time-indexed binary sparse data: a label `z` on the label wires
`LabW m l` (the source sector, the node word and the LCHS word) specifies the frequency
`k_z = ν_w` of its LCHS node (`kOf`, `|k_z| ≤ R`) and the start time `v_z = u' T / 2^m` of its
source node (`vOf`, `vOf_eq`); its branch runs on its own mesh of `2^m` slots, with sample
addresses `v_z + j (T - v_z) / 2^m = addrN · T / 2^(2m)` on the grid of `2^(2m)` points
(`addr_eq`). The private operation of slot `j` of the branch of `z` is the Cayley operation
`privFamB` of the lifted grid sample at that address with the Cayley parameter
`γ (2^m - u') / 2^m` (`DOf`), and the represented sample is `X_{z,j} = H_g + k_z L_g`, the lifted
Hamiltonian and dissipative parts of that grid sample (`XOf`).

* `binary_gate_select`: **the lemma with exact gates and the clock promises discharged**: the
  released circuit of `GateEfficientSelect` with these private operations, under the integrated
  sample-error certificate of `gate_select_certified`; unitarity, self-adjointness, the norm
  bound `‖X_{z,j}‖ ≤ λ_H + R λ_D` and the clock promises with the label-independent constants
  `Q = width(4s, γ)`, `q̄ = moment γ` follow from the row and column energy bounds of the grid
  samples.
* `binary_native_gate_select`: **the lemma with native private calls from binary data**: the
  native circuit `nativeSel` with the private operation `ndQ` (the address program computing the
  branch address and the duration word from the label and the slot, and the time-indexed compute
  circuit) and the arithmetic `arQ` (the branch scale computed from the duration word), its exact
  counts and register, and full-output error at most `δ` on the clean-input space. The gates
  beyond those of the released circuit, `G_sel = 84 d (σ+3) + 6 d G_C` with
  `G_C = 2 (|apG| + 28 k + 2) + 2 |arith| + 2 bP + bT + 1`, carry the factor `d`; the work wires
  `A_sel = |ZA| + 6k + 4b + bT + bP + A + 3` added to the released register do not depend on `d`
  (equation `ode:eq:gate-select-gates`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinarySelect

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateCircuit.Sim (Wire simR fDeg)
open SparseHamiltonian.GateBinaryODETime (PubT)
open SparseHamiltonian.GateODE (Label)
open SparseHamiltonian.GateODE.Time (TParams)
open SparseHamiltonian.GateSelect (branchPath runS selE SW)
open SparseHamiltonian.GateSelect.ODE (startB durB addrB branchHB)
open SparseHamiltonian.GateQuad (vQ)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### The labels, the start times and the represented samples -/

/-- `H + k L` is self-adjoint for self-adjoint `H`, `L` and real `k`. -/
theorem star_add_smul_real {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [CompleteSpace P] (H L : P →L[ℂ] P) (hH : star H = H) (hL : star L = L) (k : ℝ) :
    star (H + ((k : ℝ) : ℂ) • L) = H + ((k : ℝ) : ℂ) • L := by
  rw [star_add, star_smul, hH, hL, Complex.star_def, Complex.conj_ofReal]

section Labels

variable (q : PubT) {X n : Type*} [Fintype n] [DecidableEq n]

/-- The frequency of a label: the LCHS node of its LCHS word. -/
def kOf (z : Cfg (LabW q.params.m q.params.l)) : ℝ := q.params.nodeW (labOfW z).2

/-- The start time of a label: `0` for the initial sector and `u T / 2^m` for the source node
`u`. -/
def vOf (z : Cfg (LabW q.params.m q.params.l)) : ℝ :=
  startB q.params (vQ q.params q.params.M) (labOfW z).1

/-- **The private operations from binary data**: slot `j` of the branch of the label `z`. -/
def DOf (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (x : X) (z : Cfg (LabW q.params.m q.params.l)) (j : ℕ) :
    Anc q.params.a (Reg (Fin q.kx) ℂ) →L[ℂ] Anc q.params.a (Reg (Fin q.kx) ℂ) :=
  privFamB q.params D en x q.rho q.γ (labOfW z) j

/-- **The represented sample** of slot `j` of the branch of the label `z`: `H_g + k_z L_g` for the
lifted Hamiltonian and dissipative parts of the grid sample at the branch address. -/
def XOf (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (x : X) (z : Cfg (LabW q.params.m q.params.l)) (j : ℕ) :
    Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ :=
  HbB q.params D en x (labOfW z).1 j + ((kOf q z : ℝ) : ℂ) • LbB q.params D en x (labOfW z).1 j

/-- The start time of a label is the dyadic node `u' T / 2^m`. -/
theorem vOf_eq (z : Cfg (LabW q.params.m q.params.l)) :
    vOf q z = (startW (labOfW z).1 : ℝ) * q.T / 2 ^ q.m := by
  rw [vOf, startB_vQ, M_cast]
  rfl

/-- **The sample addresses of the branch of a label are points of the grid** of `2^(2m)` points:
`v_z + j (T - v_z) / 2^m = addrN · T / 2^(2m)`. -/
theorem addr_eq (z : Cfg (LabW q.params.m q.params.l)) (j : ℕ) :
    vOf q z + j * (q.T - vOf q z) / 2 ^ q.m = (addrN (labOfW z).1 j : ℝ) * q.T / 2 ^ (2 * q.m) := by
  have h := addrB_vQ q.params (labOfW z).1 j
  unfold addrB durB at h
  rw [M_cast] at h
  exact h

/-- The frequencies of the labels are at most the LCHS radius `R`. -/
theorem kOf_abs_le (hq : q.OK) (z : Cfg (LabW q.params.m q.params.l)) : |kOf q z| ≤ q.params.R :=
  q.params.nodeW_abs_le hq.g_ge hq.ε_pos (q.ε_le_one hq) (q.TD_nonneg hq) _

theorem vOf_mem (hq : q.OK) (z : Cfg (LabW q.params.m q.params.l)) :
    0 ≤ vOf q z ∧ vOf q z ≤ q.T := by
  exact GateSelect.ODE.startB_mem q.params (vQ q.params q.params.M)
    (GateQuad.vQ_mem q.params hq.T_pos.le q.params.M) hq.T_pos.le (labOfW z).1

/-- The common normalised time is `(λ_H + R λ_D) T`. -/
theorem lam_mul_T : (q.params.lamH + q.params.R * q.params.lamD) * q.T = q.params.tau :=
  mul_comm _ _

/-- **The selection hypotheses from binary data**: unitarity of `U_J` and of the private
operations, self-adjoint represented samples with `‖X_{z,j}‖ ≤ λ_H + R λ_D` and the clock
promises with the label-independent constants `Q`, `q̄` for the normalised samples
`((T - v_z)/τ) X_{z,j}`. -/
theorem select_hyps (hq : q.OK) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (x : X)
    (hrH : ∀ g i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ g j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ g i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ g j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤
      q.etaD ^ 2) :
    IsUnitary (UJop (R := ℂ) q.UJg) ∧
    (∀ z, ∀ j < 2 ^ q.params.m, IsUnitary (DOf q D en x z j)) ∧
    (∀ z, ∀ j < 2 ^ q.params.m, GateODE.ClockPromise (P := Reg (Fin q.kx) ℂ) (a := q.params.a)
      (UJop (R := ℂ) q.UJg) (DOf q D en x z j)
      ((((q.T - vOf q z) / q.params.tau : ℝ) : ℂ) • XOf q D en x z j) q.params.Q q.params.qbar) ∧
    (∀ z, ∀ j < 2 ^ q.params.m, star (XOf q D en x z j) = XOf q D en x z j) ∧
    (∀ z, ∀ j < 2 ^ q.params.m,
      ‖XOf q D en x z j‖ ≤ q.params.lamH + q.params.R * q.params.lamD) := by
  have hNH : ∀ s, ∀ r < q.params.M, ‖HbB q.params D en x s r‖ ≤ q.params.lamH :=
    fun s r _ => (HbB_norm_le q.params D en x q.etaH hq.etaH_nonneg hrH hcH s r).trans
      (q.sqrt_le_lam hq q.etaH hq.etaH_nonneg)
  have hNL : ∀ s, ∀ r < q.params.M, ‖LbB q.params D en x s r‖ ≤ q.params.lamD :=
    fun s r _ => (LbB_norm_le q.params D en x q.etaD hq.etaD_nonneg hrD hcD s r).trans
      (q.sqrt_le_lam hq q.etaD hq.etaD_nonneg)
  refine ⟨UJop_isUnitary _ (hadUJ4_ok q.σ q.hσ),
    fun z j _ => privFamB_isUnitary _ _ _ _ _ _ _ _, fun z j hj => ?_, fun z j hj => ?_,
    fun z j hj => ?_⟩
  · exact clockB q.params D en q.σ q.hσ rfl hrange x q.etaH q.etaD q.rho q.γ hq.etaH_nonneg
      hq.etaD_nonneg rfl (q.rho_pos hq) hq.γ_pos hq.T_pos hq.g_ge hq.ε_pos (q.ε_le_one hq)
      (q.TD_nonneg hq) q.tau_eq hrH hcH hrD hcD (labOfW z) j hj
  · exact star_add_smul_real _ _ (HbB_self q.params D en x _ j) (LbB_self q.params D en x _ j) _
  · have hk := kOf_abs_le q hq z
    have hR : 0 ≤ q.params.R := (abs_nonneg _).trans hk
    calc ‖XOf q D en x z j‖
        ≤ ‖HbB q.params D en x (labOfW z).1 j‖ +
          ‖((kOf q z : ℝ) : ℂ) • LbB q.params D en x (labOfW z).1 j‖ := norm_add_le _ _
      _ = ‖HbB q.params D en x (labOfW z).1 j‖ +
          |kOf q z| * ‖LbB q.params D en x (labOfW z).1 j‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ q.params.lamH + q.params.R * q.params.lamD := by
        gcongr
        · exact hNH _ j hj
        · exact hNL _ j hj

end Labels

/-! ### The lemma with exact gates -/

section Exact

variable (q : PubT) {X n : Type*} [Fintype n] [DecidableEq n]

/-- **Lemma `ode:lem:gate-select` from binary data, exact gates, with the clock promises
discharged.**

Let the public data `q` satisfy the public conditions and the time-indexed binary data `D` on
the grid of `2^(2m)` points satisfy the slot condition `hrange` and the row and column energy
bounds `η_H`, `η_D` at every grid sample. The released circuit
`SlotSim.simCircuitT a τ Q q̄ (δ/2) m` of `GateEfficientSelect` (`τ = (λ_H + R λ_D) T`), read with
the label- and slot-selected private operations `DOf` from the binary data, has the released
validity, counts, register and degree bounds. For Hermitian paths `H`, `D` on `[0, T]` with
Lipschitz bounds `βH`, `βD`, the subdivision `steps τ (δ/6) ≤ 2^m`, the freezing condition
`8 (βH + R βD) T² ≤ δ 2^m` and the integrated sample-error certificate
`sampleErr z ≤ δ/16` of every label (the represented samples `XOf` against `H + k_z D` at the
branch addresses), for every family of propagators `U z` of the branch paths of `H + k_z D` from
`v_z` (which exist) the circuit is within `δ` of the controlled direct sum
`∑_z |z⟩⟨z| ⊗ U z (T - v_z)` on the clean-input space, with the full output compared. -/
theorem binary_gate_select (hq : q.OK) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (x : X)
    (hrH : ∀ g i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ g j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ g i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ g j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (Hp Dp : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (βH βD δ : ℝ) (hβH : 0 ≤ βH)
    (hβD : 0 ≤ βD) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hCayley : TimeSchedule.steps q.params.tau (δ / 6) ≤ 2 ^ q.params.m)
    (hFreeze : 8 * (βH + q.params.R * βD) * q.T ^ 2 ≤ δ * 2 ^ q.params.m)
    (hHp : ∀ t ∈ Set.Icc 0 q.T, star (Hp t) = Hp t)
    (hDp : ∀ t ∈ Set.Icc 0 q.T, star (Dp t) = Dp t)
    (hLipH : ∀ t ∈ Set.Icc 0 q.T, ∀ t' ∈ Set.Icc 0 q.T, ‖Hp t - Hp t'‖ ≤ βH * |t - t'|)
    (hLipD : ∀ t ∈ Set.Icc 0 q.T, ∀ t' ∈ Set.Icc 0 q.T, ‖Dp t - Dp t'‖ ≤ βD * |t - t'|)
    (hCert : ∀ z, sampleErr Hp Dp (kOf q) (vOf q) (XOf q D en x) q.T q.params.m z ≤ δ / 16) :
    (∀ g ∈ SlotSim.simCircuitT q.params.a q.params.tau q.params.Q q.params.qbar (δ / 2)
      q.params.m, g.Valid Wire.anc) ∧
    nPriv (SlotSim.simCircuitT q.params.a q.params.tau q.params.Q q.params.qbar (δ / 2)
      q.params.m) = 6 * fDeg q.params.Q q.params.tau q.params.qbar (δ / 2) ∧
    nUJ (SlotSim.simCircuitT q.params.a q.params.tau q.params.Q q.params.qbar (δ / 2)
      q.params.m) = 12 * fDeg q.params.Q q.params.tau q.params.qbar (δ / 2) ∧
    nGates (SlotSim.simCircuitT q.params.a q.params.tau q.params.Q q.params.qbar (δ / 2)
      q.params.m) ≤
      200 * (fDeg q.params.Q q.params.tau q.params.qbar (δ / 2) + 1) *
        (q.params.a + q.params.m + simR q.params.Q q.params.tau q.params.qbar (δ / 2) + 1) ∧
    (fDeg q.params.Q q.params.tau q.params.qbar (δ / 2) : ℝ) ≤
      128 * (q.params.tau * q.params.qbar + q.params.Q * (1 + Real.log (6 / δ))) ∧
    (∀ z, ∃ U : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ, U 0 = 1 ∧
      TimeDependent.SolvesOn (branchPath Hp Dp (kOf q) (vOf q) z) U 0 (q.T - vOf q z)) ∧
    ∀ U : Cfg (LabW q.params.m q.params.l) → ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ,
      (∀ z, U z 0 = 1) →
      (∀ z, TimeDependent.SolvesOn (branchPath Hp Dp (kOf q) (vOf q) z) (U z) 0
        (q.T - vOf q z)) →
      ‖runS (a := q.params.a) (P := Reg (Fin q.kx) ℂ) (L := LabW q.params.m q.params.l)
          (UJop (R := ℂ) q.UJg) (DOf q D en x)
          (SlotSim.simCircuitT q.params.a q.params.tau q.params.Q q.params.qbar (δ / 2)
            q.params.m) ∘L
          selE (a := q.params.a) (m := q.params.m)
            (r := simR q.params.Q q.params.tau q.params.qbar (δ / 2))
            (K := q.params.a + q.params.m + 2 * simR q.params.Q q.params.tau q.params.qbar (δ / 2))
            (L := LabW q.params.m q.params.l) (P := Reg (Fin q.kx) ℂ) -
        selE (a := q.params.a) (m := q.params.m)
            (r := simR q.params.Q q.params.tau q.params.qbar (δ / 2))
            (K := q.params.a + q.params.m + 2 * simR q.params.Q q.params.tau q.params.qbar (δ / 2))
            (L := LabW q.params.m q.params.l) (P := Reg (Fin q.kx) ℂ) ∘L
          WeightedClock.diagonal (fun z => U z (q.T - vOf q z))‖ ≤ δ := by
  have hp := q.params_ok hq
  obtain ⟨hUJ, hU, hC, hX, hXn⟩ := select_hyps q hq D en hrange x hrH hcH hrD hcD
  have hα : 0 < q.params.lamH + q.params.R * q.params.lamD := hp.energy_pos
  obtain ⟨hvalid, hP, hJ, hG, -, hdeg, -, -, hex, herr⟩ :=
    gate_select_certified (L := LabW q.params.m q.params.l) (P := Reg (Fin q.kx) ℂ) q.params.a
      q.params.m (UJop (R := ℂ) q.UJg) (DOf q D en x) Hp Dp (kOf q) (vOf q) (XOf q D en x) q.T
      (q.params.lamH + q.params.R * q.params.lamD) q.params.tau q.params.R βH βD q.params.Q
      q.params.qbar δ hq.T_pos hα (lam_mul_T q) hβH hβD hp.Q_ge hp.qbar_le hδ hδ1 hCayley hFreeze
      (kOf_abs_le q hq) (fun z => (vOf_mem q hq z).1) (fun z => (vOf_mem q hq z).2) hUJ hU hC
      hX hXn hHp hDp hLipH hLipD hCert
  refine ⟨hvalid, hP, hJ, hG, hdeg, hex, fun U hU0 hU => ?_⟩
  convert herr U hU0 hU using 1

end Exact

/-! ### The lemma with native private calls -/

section Native

variable (q : PubT) {X n : Type*} [Fintype n] [DecidableEq n]

/-- **Lemma `ode:lem:gate-select` from binary data with native private calls** (equation
`ode:eq:gate-select-gates`, before finite-set synthesis).

For the public data `q` and the time-indexed binary data `D` of `binary_gate_select` with
decoder `hdec`, the native circuit
`nativeSel a m τ Q q̄ δ q.UJg (ndQ q) (arQ q)` depends only on the public data: `U_J` from its
`σ + 3` Hadamard gates, and every label- and slot-selected private call by the native
operation `ndQ q` (the address program computing the branch address `addrN` on the grid of
`2^(2m)` points and the duration word `2^m - u'` from the label and slot wires, the
time-indexed compute circuit reading the address, and the arithmetic `arQ q` with the branch
Cayley parameter `γ (2^m - u') / 2^m` from the duration word). It consists of valid
instructions; it makes exactly `12 d` times `2` row-location, `2` column-location and `2` value
calls of the coherent sampled-time oracles; it uses at most
`200 (d+1)(a+m+r+1) + 84 d (σ+3) + 6 d G_C` elementary gates with
`G_C = 2 (|apG| + 28 k + 2) + 2 |arith| + 2 bP + bT + 1` and `|apG| ≤ 13 (2m+14)(m+5)`; its
register has `k + (2a + 3m + 6r + 3 + (1 + m + l)) + (|ZA| + 6k + 4b + bT + bP + A + 3)` qubits,
`|ZA| = 1 + 2 (2m+14) + (4m+62)(2m+14)` (none of the added work wires depends on `d`). Under the
hypotheses of `binary_gate_select` at accuracy `δ/2` (the subdivision `steps τ (δ/12) ≤ 2^m`, the
freezing condition `16 (βH + R βD) T² ≤ δ 2^m` and the certificate `sampleErr z ≤ δ/32`) and
the arithmetic budget `48 d ζ ≤ δ`, for every family of propagators `U z` of the branch paths
its full output on the clean-input space `selN` is within `δ` of the controlled direct sum
`∑_z |z⟩⟨z| ⊗ U z (T - v_z)`. -/
theorem binary_native_gate_select (hq : q.OK)
    (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z) (x : X)
    (hrH : ∀ g i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ g j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ g i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ g j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (Hp Dp : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (βH βD δ : ℝ) (hβH : 0 ≤ βH)
    (hβD : 0 ≤ βD) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hCayley : TimeSchedule.steps q.params.tau (δ / 12) ≤ 2 ^ q.params.m)
    (hFreeze : 16 * (βH + q.params.R * βD) * q.T ^ 2 ≤ δ * 2 ^ q.params.m)
    (hHp : ∀ t ∈ Set.Icc 0 q.T, star (Hp t) = Hp t)
    (hDp : ∀ t ∈ Set.Icc 0 q.T, star (Dp t) = Dp t)
    (hLipH : ∀ t ∈ Set.Icc 0 q.T, ∀ t' ∈ Set.Icc 0 q.T, ‖Hp t - Hp t'‖ ≤ βH * |t - t'|)
    (hLipD : ∀ t ∈ Set.Icc 0 q.T, ∀ t' ∈ Set.Icc 0 q.T, ‖Dp t - Dp t'‖ ≤ βD * |t - t'|)
    (hCert : ∀ z, sampleErr Hp Dp (kOf q) (vOf q) (XOf q D en x) q.T q.params.m z ≤ δ / 32)
    (hζδ : 48 * (fDeg q.params.Q q.params.tau q.params.qbar (δ / 4) : ℝ) * q.ζ ≤ δ) :
    (∀ i ∈ nativeSel (L := LabW q.params.m q.params.l) q.params.a q.params.m q.params.tau
      q.params.Q q.params.qbar δ q.UJg (ndQ q) (arQ q), i.Valid) ∧
    (∀ c : Query → Bool, nCallsN c (nativeSel (L := LabW q.params.m q.params.l) q.params.a
      q.params.m q.params.tau q.params.Q q.params.qbar δ q.UJg (ndQ q) (arQ q)) =
      12 * fDeg q.params.Q q.params.tau q.params.qbar (δ / 4) *
        (2 * (if c Query.rowLocation then 1 else 0) +
          2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0))) ∧
    nGatesN (nativeSel (L := LabW q.params.m q.params.l) q.params.a q.params.m q.params.tau
      q.params.Q q.params.qbar δ q.UJg (ndQ q) (arQ q)) ≤
      200 * (fDeg q.params.Q q.params.tau q.params.qbar (δ / 4) + 1) *
          (q.params.a + q.params.m + simR q.params.Q q.params.tau q.params.qbar (δ / 4) + 1) +
        84 * fDeg q.params.Q q.params.tau q.params.qbar (δ / 4) * (q.σ + 3) +
        6 * fDeg q.params.Q q.params.tau q.params.qbar (δ / 4) *
          (2 * ((apG q.kx q.b q.m q.params.l).length + (28 * q.kx + 2)) +
            2 * (arQ q).circ.length + (2 * (arQ q).bP + (arQ q).bT + 1)) ∧
    Fintype.card (HW (SW q.params.a q.params.m (simR q.params.Q q.params.tau q.params.qbar (δ / 4))
        (q.params.a + q.params.m + 2 * simR q.params.Q q.params.tau q.params.qbar (δ / 4))
        (LabW q.params.m q.params.l)) (Fin q.kx) Empty (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT
        (arQ q).bP (arQ q).A) =
      q.kx + (2 * (q.kx + 3) + 3 * q.m + 6 * simR q.params.Q q.params.tau q.params.qbar (δ / 4) +
          3 + (1 + q.m + q.params.l)) +
        (((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) + (6 * q.kx + 4 * q.b)) +
          (arQ q).bT + (arQ q).bP + (arQ q).A + 3) ∧
    (fDeg q.params.Q q.params.tau q.params.qbar (δ / 4) : ℝ) ≤
      128 * (q.params.tau * q.params.qbar + q.params.Q * (1 + Real.log (12 / δ))) ∧
    (∀ z, ∃ U : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ, U 0 = 1 ∧
      TimeDependent.SolvesOn (branchPath Hp Dp (kOf q) (vOf q) z) U 0 (q.T - vOf q z)) ∧
    ∀ U : Cfg (LabW q.params.m q.params.l) → ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ,
      (∀ z, U z 0 = 1) →
      (∀ z, TimeDependent.SolvesOn (branchPath Hp Dp (kOf q) (vOf q) z) (U z) 0
        (q.T - vOf q z)) →
      ‖nrun (primsT (R := ℂ) (m := 2 * q.m) D en x)
            (nativeSel (L := LabW q.params.m q.params.l) q.params.a q.params.m q.params.tau
              q.params.Q q.params.qbar δ q.UJg (ndQ q) (arQ q)) ∘L
          selN (L := LabW q.params.m q.params.l) (S := Fin q.kx) (Z := ZA q.m ⊕ SZ4 q.kx q.b)
            (R := ℂ) q.params.a q.params.m (simR q.params.Q q.params.tau q.params.qbar (δ / 4))
            (q.params.a + q.params.m + 2 * simR q.params.Q q.params.tau q.params.qbar (δ / 4))
            (arQ q).bT (arQ q).bP (arQ q).A -
        selN (L := LabW q.params.m q.params.l) (S := Fin q.kx) (Z := ZA q.m ⊕ SZ4 q.kx q.b)
            (R := ℂ) q.params.a q.params.m (simR q.params.Q q.params.tau q.params.qbar (δ / 4))
            (q.params.a + q.params.m + 2 * simR q.params.Q q.params.tau q.params.qbar (δ / 4))
            (arQ q).bT (arQ q).bP (arQ q).A ∘L
          WeightedClock.diagonal (fun z => U z (q.T - vOf q z))‖ ≤ δ := by
  have hp := q.params_ok hq
  obtain ⟨hUJ, hU, hC, hX, hXn⟩ := select_hyps q hq D en hrange x hrH hcH hrD hcD
  have hα : 0 < q.params.lamH + q.params.R * q.params.lamD := hp.energy_pos
  have hN : NativeOK (primsT (R := ℂ) (m := 2 * q.m) D en x) (ndQ q)
      (selOp (selFam (m := q.params.m) (DOf q D en x) false)) :=
    nativeOKQ q hq D en hrange hdec x
  obtain ⟨hvalid, hcalls, hG, hcard, hdeg, -, -, hex, herr⟩ :=
    native_gate_select (L := LabW q.params.m q.params.l) q.params.a q.params.m
      (primsT (R := ℂ) (m := 2 * q.m) D en x) (primsT_isUnitary D en x) q.UJg
      (hadUJ4_ok q.σ q.hσ) (ndQ q) (ndQ_public q) (arQ q) q.ζ hq.ζ_pos.le (arQ_ok q hq)
      (DOf q D en x) hN Hp Dp (kOf q) (vOf q) (XOf q D en x) q.T
      (q.params.lamH + q.params.R * q.params.lamD) q.params.tau q.params.R βH βD q.params.Q
      q.params.qbar δ hq.T_pos hα (lam_mul_T q) hβH hβD hp.Q_ge hp.qbar_le hδ hδ1 hCayley hFreeze
      (kOf_abs_le q hq) (fun z => (vOf_mem q hq z).1) (fun z => (vOf_mem q hq z).2) hU hC hX
      hXn hHp hDp hLipH hLipD hCert hζδ
  have hUJl : q.UJg.length = q.σ + 3 := hadUJ4_length q.σ q.hσ
  refine ⟨hvalid, fun c => ?_, ?_, ?_, hdeg, hex, fun U hU0 hU => ?_⟩
  · rw [hcalls c, ndQ_nCalls]
  · rw [hUJl, ndQ_nGates] at hG
    exact hG
  · have hL : Fintype.card (LabW q.params.m q.params.l) = 1 + q.m + q.params.l := by
      simp only [GateNative.LabW, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
      rfl
    rw [hcard, Fintype.card_fin, Fintype.card_sum (α := ZA q.m), card_ZA, card_SZ4, hL]
    rfl
  · convert herr U hU0 hU using 1

end Native

end

end SparseHamiltonian.GateBinarySelect
