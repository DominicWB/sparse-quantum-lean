import GateEfficientBinarySelect.BudgetBits

/-!
# The cost of coherent selection from binary data, for the circuit itself

Lemma `ode:lem:gate-select` with equation `ode:eq:gate-select-gates` for the native selection
circuit of `binary_native_gate_select` at `δ = 4ν` (`ν` the accuracy parameter of the solver),
where its filter degree and reuse register are those of the solver (`d = q.params.d`,
`r = q.params.r`), its subdivision condition is the released mesh condition and its arithmetic
budget follows from `98304 q* ζ ≤ ν`; for other accuracies only the arithmetic bounds
`select_gates_words`, `select_gates_bits` of `G_sel` and `A_sel` with a free degree are stated:

* `binary_select_lemma_words`: exactly `12 d` times `2 + 2 + 2` calls of the sampled-time
  oracles, at most `394300 (d+1) (𝔴+1)³` elementary gates (the released circuit and `G_sel`) and
  at most `4200 (𝔴+1)³` qubits, `𝔴 = wordsB q`, with `d ≤ 4096 q*`, and full-output error at most
  `4ν` on the clean-input space;
* `binary_select_lemma_bits`: the same with at most `11·10¹² (d+1) (𝔟+1)³` gates and
  `2·10¹¹ (𝔟+1)³` qubits under the bit-length hypotheses of the budget in `𝔟`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinarySelect

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateCircuit.Sim (simR fDeg)
open SparseHamiltonian.GateBinaryODETime (PubT)
open SparseHamiltonian.GateSelect (branchPath SW)
open SparseHamiltonian.GateBitBudget (bitB HasBits bitB_nonneg cube_le)
open SparseHamiltonian.GateODEBudget (gammaOf qOf binary_ode_time_sizes pubT_shapeOK)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

section Cost

variable (q : PubT) {X n : Type*} [Fintype n] [DecidableEq n]

/-- **Coherent selection from binary data at `δ = 4ν`, in the register words**
(Lemma `ode:lem:gate-select` with equation `ode:eq:gate-select-gates`, for the circuit itself).
Let the public data `q` have the public rescaling `γ = gammaOf T η_H η_D (2g) (ε/2)` and the
arithmetic budget `98304 q* ζ ≤ ν` (`q* = qOf s T η_H η_D (2g) (ε/2)`). At `δ = 4ν` the native
selection circuit of `binary_native_gate_select` has the degree `d = q.params.d` and the reuse
register `r = q.params.r` of the solver, its subdivision condition is the released mesh condition
and its arithmetic budget `48 d ζ ≤ 4ν` holds. Under the freezing condition
`16 (βH + R βD) T² ≤ 4ν 2^m` and the integrated sample-error certificate `sampleErr z ≤ ν/8` of
every label, the circuit makes exactly `12 d` times `2 + 2 + 2` calls of the row-location,
column-location and value oracles, has at most `394300 (d+1) (𝔴+1)³` elementary gates (the
released circuit and `G_sel`) on at most `4200 (𝔴+1)³` qubits (`𝔴 = wordsB q`), `d ≤ 4096 q*`,
and for every family of propagators of the branch paths it is within `4ν` of their controlled
direct sum on the clean-input space. -/
theorem binary_select_lemma_words (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : 98304 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ ≤ q.params.nu)
    (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z) (x : X)
    (hrH : ∀ g i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ g j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ g i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ g j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (Hp Dp : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (βH βD : ℝ) (hβH : 0 ≤ βH)
    (hβD : 0 ≤ βD)
    (hFreeze : 16 * (βH + q.params.R * βD) * q.T ^ 2 ≤ 4 * q.params.nu * 2 ^ q.params.m)
    (hHp : ∀ t ∈ Set.Icc 0 q.T, star (Hp t) = Hp t)
    (hDp : ∀ t ∈ Set.Icc 0 q.T, star (Dp t) = Dp t)
    (hLipH : ∀ t ∈ Set.Icc 0 q.T, ∀ t' ∈ Set.Icc 0 q.T, ‖Hp t - Hp t'‖ ≤ βH * |t - t'|)
    (hLipD : ∀ t ∈ Set.Icc 0 q.T, ∀ t' ∈ Set.Icc 0 q.T, ‖Dp t - Dp t'‖ ≤ βD * |t - t'|)
    (hCert : ∀ z, sampleErr Hp Dp (kOf q) (vOf q) (XOf q D en x) q.T q.params.m z ≤
      q.params.nu / 8) :
    (∀ c : Query → Bool, nCallsN c (nativeSel (L := LabW q.params.m q.params.l) q.params.a
      q.params.m q.params.tau q.params.Q q.params.qbar (4 * q.params.nu) q.UJg (ndQ q) (arQ q)) =
      12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0))) ∧
    nGatesN (nativeSel (L := LabW q.params.m q.params.l) q.params.a q.params.m q.params.tau
      q.params.Q q.params.qbar (4 * q.params.nu) q.UJg (ndQ q) (arQ q)) ≤
      394300 * (q.params.d + 1) * (wordsB q + 1) ^ 3 ∧
    Fintype.card (HW (SW q.params.a q.params.m
        (simR q.params.Q q.params.tau q.params.qbar (4 * q.params.nu / 4))
        (q.params.a + q.params.m +
          2 * simR q.params.Q q.params.tau q.params.qbar (4 * q.params.nu / 4))
        (LabW q.params.m q.params.l)) (Fin q.kx) Empty (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT
        (arQ q).bP (arQ q).A) ≤ 4200 * (wordsB q + 1) ^ 3 ∧
    (q.params.d : ℝ) ≤ 4096 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) ∧
    ∀ U : Cfg (LabW q.params.m q.params.l) → ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ,
      (∀ z, U z 0 = 1) →
      (∀ z, TimeDependent.SolvesOn (branchPath Hp Dp (kOf q) (vOf q) z) (U z) 0
        (q.T - vOf q z)) →
      ‖nrun (primsT (R := ℂ) (m := 2 * q.m) D en x)
            (nativeSel (L := LabW q.params.m q.params.l) q.params.a q.params.m q.params.tau
              q.params.Q q.params.qbar (4 * q.params.nu) q.UJg (ndQ q) (arQ q)) ∘L
          selN (L := LabW q.params.m q.params.l) (S := Fin q.kx) (Z := ZA q.m ⊕ SZ4 q.kx q.b)
            (R := ℂ) q.params.a q.params.m
            (simR q.params.Q q.params.tau q.params.qbar (4 * q.params.nu / 4))
            (q.params.a + q.params.m +
              2 * simR q.params.Q q.params.tau q.params.qbar (4 * q.params.nu / 4))
            (arQ q).bT (arQ q).bP (arQ q).A -
        selN (L := LabW q.params.m q.params.l) (S := Fin q.kx) (Z := ZA q.m ⊕ SZ4 q.kx q.b)
            (R := ℂ) q.params.a q.params.m
            (simR q.params.Q q.params.tau q.params.qbar (4 * q.params.nu / 4))
            (q.params.a + q.params.m +
              2 * simR q.params.Q q.params.tau q.params.qbar (4 * q.params.nu / 4))
            (arQ q).bT (arQ q).bP (arQ q).A ∘L
          WeightedClock.diagonal (fun z => U z (q.T - vOf q z))‖ ≤ 4 * q.params.nu := by
  have hp := q.params_ok hq
  have hν := hp.nu_pos
  have hν1 : q.params.nu ≤ 1 / 10000 :=
    ImprovedODEQueryBudget.precision_le_one_ten_thousandth q.params.ratio q.params.acc
      (q.params.ratio_ge hp.g_ge) (q.params.acc_le_one hp.eps_le_one)
  obtain ⟨-, hd, -, -, -, -⟩ := binary_ode_time_sizes q hq hγ
  have hd' : (q.params.d : ℝ) ≤ 4096 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := hd
  have e4 : 4 * q.params.nu / 4 = q.params.nu := by ring
  have hC : TimeSchedule.steps q.params.tau (4 * q.params.nu / 12) ≤ 2 ^ q.params.m := by
    rw [show 4 * q.params.nu / 12 = q.params.nu / 3 by ring]
    exact hq.mesh
  have hζδ : 48 * (fDeg q.params.Q q.params.tau q.params.qbar (4 * q.params.nu / 4) : ℝ) *
      q.ζ ≤ 4 * q.params.nu := by
    rw [e4]
    have h1 := mul_le_mul_of_nonneg_right hd' hq.ζ_pos.le
    have e : (fDeg q.params.Q q.params.tau q.params.qbar q.params.nu : ℝ) = q.params.d := rfl
    rw [e]
    linarith
  obtain ⟨-, hcalls, hG, hcard, -, -, herr⟩ :=
    binary_native_gate_select q hq D en hrange hdec x hrH hcH hrD hcD Hp Dp βH βD
      (4 * q.params.nu) hβH hβD (by positivity) (by linarith) hC hFreeze hHp hDp hLipH hLipD
      (fun z => (hCert z).trans (le_of_eq (by ring))) hζδ
  obtain ⟨hsel, hA⟩ := select_gates_words q q.params.d
  have hW : wordsB q + 1 ≤ (wordsB q + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  have hw : q.kx + q.params.m + simR q.params.Q q.params.tau q.params.qbar q.params.nu +
      q.params.l ≤ wordsB q := by
    show q.kx + q.params.m + q.params.r + q.params.l ≤ wordsB q
    unfold wordsB
    omega
  have hm : q.params.m = q.m := rfl
  have ha : q.params.a = q.kx + 3 := rfl
  refine ⟨fun c => ?_, ?_, ?_, hd', herr⟩
  · rw [hcalls c, e4]
  · have hfd : fDeg q.params.Q q.params.tau q.params.qbar (4 * q.params.nu / 4) = q.params.d := by
      rw [e4]
    have hsr : simR q.params.Q q.params.tau q.params.qbar (4 * q.params.nu / 4) =
        simR q.params.Q q.params.tau q.params.qbar q.params.nu := by
      rw [e4]
    simp only [hfd, hsr] at hG
    have hamr : q.params.a + q.params.m + simR q.params.Q q.params.tau q.params.qbar q.params.nu +
        1 ≤ 4 * (wordsB q + 1) ^ 3 := by
      rw [ha]
      omega
    have h1 : 200 * (q.params.d + 1) *
        (q.params.a + q.params.m + simR q.params.Q q.params.tau q.params.qbar q.params.nu + 1) ≤
        800 * ((q.params.d + 1) * (wordsB q + 1) ^ 3) := by
      calc _ ≤ 200 * (q.params.d + 1) * (4 * (wordsB q + 1) ^ 3) := Nat.mul_le_mul_left _ hamr
        _ = _ := by ring
    have h2 : 393500 * q.params.d * (wordsB q + 1) ^ 3 ≤
        393500 * ((q.params.d + 1) * (wordsB q + 1) ^ 3) := by
      calc _ = 393500 * (q.params.d * (wordsB q + 1) ^ 3) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.le_succ _))
    calc _ ≤ _ := hG
      _ = _ := Nat.add_assoc _ _ _
      _ ≤ 800 * ((q.params.d + 1) * (wordsB q + 1) ^ 3) +
          393500 * ((q.params.d + 1) * (wordsB q + 1) ^ 3) :=
        Nat.add_le_add h1 (hsel.trans h2)
      _ = 394300 * (q.params.d + 1) * (wordsB q + 1) ^ 3 := by ring
  · have key : q.kx + (2 * (q.kx + 3) + 3 * q.m +
        6 * simR q.params.Q q.params.tau q.params.qbar (4 * q.params.nu / 4) + 3 +
        (1 + q.m + q.params.l)) +
        (((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) + (6 * q.kx + 4 * q.b)) +
          (arQ q).bT + (arQ q).bP + (arQ q).A + 3) ≤ 4200 * (wordsB q + 1) ^ 3 := by
      have hsr : simR q.params.Q q.params.tau q.params.qbar (4 * q.params.nu / 4) =
          simR q.params.Q q.params.tau q.params.qbar q.params.nu := by
        rw [e4]
      rw [hsr]
      rw [hm] at hw
      generalize simR q.params.Q q.params.tau q.params.qbar q.params.nu = r at hw ⊢
      generalize (wordsB q + 1) ^ 3 = W at hA hW ⊢
      generalize wordsB q = w at hw hW
      have h1 : q.kx + (2 * (q.kx + 3) + 3 * q.m + 6 * r + 3 + (1 + q.m + q.params.l)) ≤
          10 * W := by
        omega
      have hW1 : 1 ≤ W := by omega
      exact (Nat.add_le_add h1 hA).trans (by omega)
    exact (le_of_eq hcard).trans key

/-- **Coherent selection from binary data at `δ = 4ν`, in `𝔟`** (Lemma
`ode:lem:gate-select` with equation `ode:eq:gate-select-gates` in the word budget of equation
`ode:eq:gate-word-budget`). Under the hypotheses of `binary_select_lemma_words`, an arithmetic
accuracy `ζ ≥ ν/(196608 q*)`, stored bits `b ≤ b_data` and `c₀`, `T`, `η_H`, `η_D` of bit length
`b_data`, with `𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε`: the native selection circuit at
`δ = 4ν` has at most `11·10¹² (d+1) (𝔟+1)³` elementary gates and at most `2·10¹¹ (𝔟+1)³` qubits,
`d = q.params.d ≤ 4096 q*`, makes exactly `12 d` times `2 + 2 + 2` calls of the sampled-time
oracles, and is within `4ν` of the controlled direct sum of the branch propagators. -/
theorem binary_select_lemma_bits (bd : ℕ) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζl : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hζ : 98304 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ ≤ q.params.nu)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD)
    (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z) (x : X)
    (hrH : ∀ g i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ g j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ g i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ g j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (Hp Dp : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (βH βD : ℝ) (hβH : 0 ≤ βH)
    (hβD : 0 ≤ βD)
    (hFreeze : 16 * (βH + q.params.R * βD) * q.T ^ 2 ≤ 4 * q.params.nu * 2 ^ q.params.m)
    (hHp : ∀ t ∈ Set.Icc 0 q.T, star (Hp t) = Hp t)
    (hDp : ∀ t ∈ Set.Icc 0 q.T, star (Dp t) = Dp t)
    (hLipH : ∀ t ∈ Set.Icc 0 q.T, ∀ t' ∈ Set.Icc 0 q.T, ‖Hp t - Hp t'‖ ≤ βH * |t - t'|)
    (hLipD : ∀ t ∈ Set.Icc 0 q.T, ∀ t' ∈ Set.Icc 0 q.T, ‖Dp t - Dp t'‖ ≤ βD * |t - t'|)
    (hCert : ∀ z, sampleErr Hp Dp (kOf q) (vOf q) (XOf q D en x) q.T q.params.m z ≤
      q.params.nu / 8) :
    (∀ c : Query → Bool, nCallsN c (nativeSel (L := LabW q.params.m q.params.l) q.params.a
      q.params.m q.params.tau q.params.Q q.params.qbar (4 * q.params.nu) q.UJg (ndQ q) (arQ q)) =
      12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0))) ∧
    (nGatesN (nativeSel (L := LabW q.params.m q.params.l) q.params.a q.params.m q.params.tau
      q.params.Q q.params.qbar (4 * q.params.nu) q.UJg (ndQ q) (arQ q)) : ℝ) ≤
      11 * 10 ^ 12 * ((q.params.d : ℝ) + 1) * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 ∧
    (Fintype.card (HW (SW q.params.a q.params.m
        (simR q.params.Q q.params.tau q.params.qbar (4 * q.params.nu / 4))
        (q.params.a + q.params.m +
          2 * simR q.params.Q q.params.tau q.params.qbar (4 * q.params.nu / 4))
        (LabW q.params.m q.params.l)) (Fin q.kx) Empty (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT
        (arQ q).bP (arQ q).A) : ℝ) ≤
      2 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 ∧
    (q.params.d : ℝ) ≤ 4096 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) ∧
    ∀ U : Cfg (LabW q.params.m q.params.l) → ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ,
      (∀ z, U z 0 = 1) →
      (∀ z, TimeDependent.SolvesOn (branchPath Hp Dp (kOf q) (vOf q) z) (U z) 0
        (q.T - vOf q z)) →
      ‖nrun (primsT (R := ℂ) (m := 2 * q.m) D en x)
            (nativeSel (L := LabW q.params.m q.params.l) q.params.a q.params.m q.params.tau
              q.params.Q q.params.qbar (4 * q.params.nu) q.UJg (ndQ q) (arQ q)) ∘L
          selN (L := LabW q.params.m q.params.l) (S := Fin q.kx) (Z := ZA q.m ⊕ SZ4 q.kx q.b)
            (R := ℂ) q.params.a q.params.m
            (simR q.params.Q q.params.tau q.params.qbar (4 * q.params.nu / 4))
            (q.params.a + q.params.m +
              2 * simR q.params.Q q.params.tau q.params.qbar (4 * q.params.nu / 4))
            (arQ q).bT (arQ q).bP (arQ q).A -
        selN (L := LabW q.params.m q.params.l) (S := Fin q.kx) (Z := ZA q.m ⊕ SZ4 q.kx q.b)
            (R := ℂ) q.params.a q.params.m
            (simR q.params.Q q.params.tau q.params.qbar (4 * q.params.nu / 4))
            (q.params.a + q.params.m +
              2 * simR q.params.Q q.params.tau q.params.qbar (4 * q.params.nu / 4))
            (arQ q).bT (arQ q).bP (arQ q).A ∘L
          WeightedClock.diagonal (fun z => U z (q.T - vOf q z))‖ ≤ 4 * q.params.nu := by
  obtain ⟨hcalls, hG, hcard, hd, herr⟩ :=
    binary_select_lemma_words q hq hγ hζ D en hrange hdec x hrH hcH hrD hcD Hp Dp βH βD hβH hβD
      hFreeze hHp hDp hLipH hLipD hCert
  have hw := wordsB_le bd q hq hγ hζl hb hc0 hT hH hD
  have h := pubT_shapeOK q hq
  have hℓ := h.ell_ge
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hB0 : 0 ≤ bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith [h.one_le_q]) hg0) hq.ε_pos hε1
  have hw' : (wordsB q : ℝ) ≤ 300 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) := by linarith
  have hcube := cube_le (Nat.cast_nonneg (wordsB q)) hB0 hw'
  have hY : 0 ≤ (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 := by positivity
  have hG' : (nGatesN (nativeSel (L := LabW q.params.m q.params.l) q.params.a q.params.m
      q.params.tau q.params.Q q.params.qbar (4 * q.params.nu) q.UJg (ndQ q) (arQ q)) : ℝ) ≤
      394300 * ((q.params.d : ℝ) + 1) * ((wordsB q : ℝ) + 1) ^ 3 := by exact_mod_cast hG
  have hcard' : (Fintype.card (HW (SW q.params.a q.params.m
        (simR q.params.Q q.params.tau q.params.qbar (4 * q.params.nu / 4))
        (q.params.a + q.params.m +
          2 * simR q.params.Q q.params.tau q.params.qbar (4 * q.params.nu / 4))
        (LabW q.params.m q.params.l)) (Fin q.kx) Empty (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT
        (arQ q).bP (arQ q).A) : ℝ) ≤ 4200 * ((wordsB q : ℝ) + 1) ^ 3 := by exact_mod_cast hcard
  generalize (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 = Y at hcube hY ⊢
  have hd0 : (0 : ℝ) ≤ (q.params.d : ℝ) + 1 := by positivity
  refine ⟨hcalls, ?_, ?_, hd, herr⟩
  · have h3 : (394300 : ℝ) * ((q.params.d : ℝ) + 1) * ((wordsB q : ℝ) + 1) ^ 3 ≤
        394300 * ((q.params.d : ℝ) + 1) * ((300 + 1) ^ 3 * Y) :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    have h4 : (394300 : ℝ) * ((q.params.d : ℝ) + 1) * ((300 + 1) ^ 3 * Y) ≤
        11 * 10 ^ 12 * ((q.params.d : ℝ) + 1) * Y := by
      have e : (394300 : ℝ) * ((q.params.d : ℝ) + 1) * ((300 + 1) ^ 3 * Y) =
          10752916264300 * (((q.params.d : ℝ) + 1) * Y) := by ring
      have e' : (11 * 10 ^ 12 : ℝ) * ((q.params.d : ℝ) + 1) * Y =
          11000000000000 * (((q.params.d : ℝ) + 1) * Y) := by ring
      rw [e, e']
      have : 0 ≤ ((q.params.d : ℝ) + 1) * Y := mul_nonneg hd0 hY
      linarith
    linarith
  · have h3 : (4200 : ℝ) * ((wordsB q : ℝ) + 1) ^ 3 ≤ 4200 * ((300 + 1) ^ 3 * Y) :=
      mul_le_mul_of_nonneg_left hcube (by norm_num)
    have e : (4200 : ℝ) * ((300 + 1) ^ 3 * Y) = 114537784200 * Y := by ring
    linarith

end Cost

end

end SparseHamiltonian.GateBinarySelect
