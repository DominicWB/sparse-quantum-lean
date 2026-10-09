import GateEfficientSelect.Lemma
import GateEfficientMesh.Slots

/-!
# Lemma `ode:lem:gate-select` under the integrated sample-error certificate, exact gates

Lemma `ode:lem:gate-select` assumes, at the addresses `v_z + r u_z / M` (`u_z = T - v_z`),
represented Hermitian samples whose "certified total operator-norm error, integrated over the
selected interval, is at most `δ/16`", besides the freezing bound `L_* u_z² / (2M) ≤ δ/16` from
the Lipschitz constant `L_* ≥ Lip(H) + R Lip(D)`. The released `GateSelect.gate_select` uses a
uniform sample bound `δ` at every address instead. This module proves the lemma with the
integrated certificate, for the released circuit and counts:

* `sampleErr`: the integrated represented-sample error of a label,
  `∑_r (u_z / 2^m) ‖H(v_z + r u_z/2^m) + k_z D(v_z + r u_z/2^m) - X_{z,r}‖`;
  a uniform bound `δ` gives at most `u_z δ` (`sampleErr_le_of_uniform`);
* `slot_cert_le`: for a `β`-Lipschitz path, the integrated certificate of the slots
  `∑_r ∫_{slot r} ‖h(t) - X_r‖ dt` is at most `β u² / (2 · 2^m)` plus the integrated sample error;
* `branch_error_cert`: one branch is within `ε/2 + L u_z²/(2 · 2^m) + sampleErr z` of every
  propagator of its branch path;
* `gate_select_certified`: Lemma `ode:lem:gate-select` with the mesh condition
  `8 L T² ≤ ε 2^m` of equation `ode:eq:gate-select-mesh` and the certificate
  `sampleErr z ≤ ε/16` for every label; the released circuit, counts and register;
* `gate_select_integral`: more generally, for any Hermitian interval-integrable branch paths
  with integral-sense propagators whose slot certificates `∑_r ∫_{slot r} ‖h_z(t) - X_{z,r}‖ dt`
  are at most `ε/2`, without a Lipschitz bound.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinarySelect

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit MeasureTheory Set
open GateCircuit.Sim (Wire Vsp io io_norm_le simR fDeg card_wire)
open GateSelect (branchPath branchPath_selfAdjoint branchPath_lipschitz runS selE SW select_error
  card_SW qbar_nonneg_of_clock branch_block)
open GateMesh (slotMesh slotEvolution)
open IntegrablePathSimulation.Propagator (IsPropagator)
open scoped InnerProduct BigOperators

/-! ### The integrated sample error -/

section Cert

variable {L : Type*} {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]

/-- **The integrated represented-sample error of a label** `z`: the operator-norm errors of the
represented samples `X z j` at the branch addresses `v z + j (T - v z) / 2^m`, weighted by the
slot length `(T - v z) / 2^m` (the error of the selected samples integrated over the selected
interval `[v z, T]`). -/
def sampleErr (Hp Dp : ℝ → P →L[ℂ] P) (k v : Cfg L → ℝ) (X : Cfg L → ℕ → P →L[ℂ] P) (T : ℝ)
    (m : ℕ) (z : Cfg L) : ℝ :=
  ∑ j ∈ Finset.range (2 ^ m), (T - v z) / 2 ^ m *
    ‖Hp (v z + j * (T - v z) / 2 ^ m) + ((k z : ℝ) : ℂ) • Dp (v z + j * (T - v z) / 2 ^ m) -
      X z j‖

/-- A uniform sample bound `δ` gives the integrated sample error at most `(T - v z) δ`. -/
theorem sampleErr_le_of_uniform (Hp Dp : ℝ → P →L[ℂ] P) (k v : Cfg L → ℝ)
    (X : Cfg L → ℕ → P →L[ℂ] P) (T δ : ℝ) (m : ℕ) (z : Cfg L) (hvT : v z ≤ T)
    (hVal : ∀ j : ℕ, j < 2 ^ m →
      ‖Hp (v z + j * (T - v z) / 2 ^ m) + ((k z : ℝ) : ℂ) • Dp (v z + j * (T - v z) / 2 ^ m) -
        X z j‖ ≤ δ) :
    sampleErr Hp Dp k v X T m z ≤ (T - v z) * δ := by
  have hu : 0 ≤ (T - v z) / 2 ^ m := div_nonneg (sub_nonneg.mpr hvT) (by positivity)
  calc sampleErr Hp Dp k v X T m z
      ≤ ∑ j ∈ Finset.range (2 ^ m), (T - v z) / 2 ^ m * δ := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hVal j (Finset.mem_range.mp hj)) hu
    _ = (T - v z) * δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        field_simp

/-- **The slot certificate of a Lipschitz path with per-slot sample errors**: for a
`β`-Lipschitz path `h` on `[0, u]` and slot samples `Xs j`,
`∑_j ∫_{slot j} ‖h(t) - Xs j‖ dt ≤ β u² / (2 · 2^m) + ∑_j (u / 2^m) ‖h(j u / 2^m) - Xs j‖`. -/
theorem slot_cert_le {E : Type*} [NormedAddCommGroup E] (h : ℝ → E) (Xs : ℕ → E) {u β : ℝ}
    (hu : 0 ≤ u) (m : ℕ)
    (hLip : ∀ t ∈ Icc 0 u, ∀ t' ∈ Icc 0 u, ‖h t - h t'‖ ≤ β * |t - t'|) :
    ∑ j ∈ Finset.range (2 ^ m), ∫ t in slotMesh u m j..slotMesh u m (j + 1), ‖h t - Xs j‖ ≤
      β * u ^ 2 / (2 * 2 ^ m) +
        ∑ j ∈ Finset.range (2 ^ m), u / 2 ^ m * ‖h (slotMesh u m j) - Xs j‖ := by
  have hmesh := GateMesh.isMesh_slotMesh hu m
  have hstep : ∀ j ∈ Finset.range (2 ^ m),
      ∫ t in slotMesh u m j..slotMesh u m (j + 1), ‖h t - Xs j‖ ≤
        β * (u / 2 ^ m) ^ 2 / 2 + u / 2 ^ m * ‖h (slotMesh u m j) - Xs j‖ := by
    intro j hj
    have hjM := Finset.mem_range.mp hj
    have h0 : 0 ≤ slotMesh u m j := hmesh.nonneg j
    have h1 : slotMesh u m j ≤ slotMesh u m (j + 1) := hmesh.mono (Nat.le_succ j)
    have h2 : slotMesh u m (j + 1) ≤ u := hmesh.le_last (by omega)
    have hsub : Icc (slotMesh u m j) (slotMesh u m (j + 1)) ⊆ Icc 0 u := Icc_subset_Icc h0 h2
    have hI := TimeDependentExtensions.integral_le_of_lipschitz' h (Xs j) h1
      (fun s hs s' hs' => hLip s (hsub hs) s' (hsub hs')) le_rfl
    have e : slotMesh u m (j + 1) - slotMesh u m j = u / 2 ^ m := by
      rw [GateMesh.slotMesh_succ_sub]
      push_cast
      ring
    rw [e] at hI
    linarith
  refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  field_simp

end Cert

/-! ### One branch -/

section Branch

variable {L : Type*} {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **One branch against the slot product.** Under the clock promises of the released
simulator for the normalised samples `((T - v z) / (α T)) X z j`, the released slot-selected
simulator for the common time `α T` and accuracy `ε/2` is within `ε/2 + ‖S_z - U‖` of every
operator `U` on its clean column, `S_z` the ordered product of the branch slot exponentials
`exp(-i ((T - v z)/2^m) X z j)`. -/
theorem branch_slot_error (a m : ℕ) (UJ : Vsp a P →L[ℂ] Vsp a P)
    (D : Cfg L → ℕ → Vsp a P →L[ℂ] Vsp a P) (v : Cfg L → ℝ) (X : Cfg L → ℕ → P →L[ℂ] P)
    (z : Cfg L) (T α Q qbar ε : ℝ) (hT : 0 < T) (hα : 0 < α) (hQ : 1 ≤ Q) (hqQ : qbar ≤ Q)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hCayley : TimeSchedule.steps (α * T) (ε / 6) ≤ 2 ^ m)
    (hv0 : 0 ≤ v z) (hvT : v z ≤ T) (hUJ : IsUnitary UJ) (hD : ∀ j < 2 ^ m, IsUnitary (D z j))
    (hClock : ∀ j < 2 ^ m, GateODE.ClockPromise UJ (D z j)
      ((((T - v z) / (α * T) : ℝ) : ℂ) • X z j) Q qbar)
    (hX : ∀ j < 2 ^ m, star (X z j) = X z j) (hXn : ∀ j < 2 ^ m, ‖X z j‖ ≤ α)
    (U : P →L[ℂ] P) :
    ‖SlotSim.runT UJ (D z) (SlotSim.simCircuitT a (α * T) Q qbar (ε / 2) m) ∘L io - io ∘L U‖ ≤
      ε / 2 + ‖slotEvolution (X z) (T - v z) m - U‖ := by
  have hτ : 0 < α * T := mul_pos hα hT
  have hε2 : 0 < ε / 2 := by linarith
  have hε21 : ε / 2 ≤ 1 := by linarith
  have hm : TimeSchedule.steps (α * T) (ε / 2 / 3) ≤ 2 ^ m := by
    rw [show ε / 2 / 3 = ε / 6 by ring]
    exact hCayley
  have hu : 0 ≤ T - v z := sub_nonneg.mpr hvT
  have huT : T - v z ≤ T := by linarith
  have hXn' : ∀ j < 2 ^ m, (T - v z) * ‖X z j‖ ≤ α * T := by
    intro j hj
    calc (T - v z) * ‖X z j‖ ≤ T * α :=
          mul_le_mul huT (hXn j hj) (norm_nonneg _) hT.le
      _ = α * T := mul_comm _ _
  have hblock := branch_block a m UJ (D z) (X z) (α * T) (T - v z) Q qbar (ε / 2) hτ hu hQ hqQ
    hε2 hε21 hm hUJ hD hX hXn' hClock
  have hS : TimeDependent.evolution (fun j => NormedSpace.exp
      ((-Complex.I * (((T - v z) / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • X z j)) (2 ^ m) =
      slotEvolution (X z) (T - v z) m := rfl
  rw [hS] at hblock
  have h2 : ‖(io : P →L[ℂ] Reg (Wire a m (simR Q (α * T) qbar (ε / 2))
      (a + m + 2 * simR Q (α * T) qbar (ε / 2))) P) ∘L slotEvolution (X z) (T - v z) m -
      io ∘L U‖ ≤ ‖slotEvolution (X z) (T - v z) m - U‖ := by
    rw [← comp_sub]
    refine (opNorm_comp_le _ _).trans ?_
    calc _ ≤ 1 * ‖slotEvolution (X z) (T - v z) m - U‖ :=
          mul_le_mul_of_nonneg_right io_norm_le (norm_nonneg _)
      _ = _ := one_mul _
  have key := norm_sub_le_norm_sub_add_norm_sub
    (SlotSim.runT UJ (D z) (SlotSim.simCircuitT a (α * T) Q qbar (ε / 2) m) ∘L io)
    ((io : P →L[ℂ] Reg (Wire a m (simR Q (α * T) qbar (ε / 2))
      (a + m + 2 * simR Q (α * T) qbar (ε / 2))) P) ∘L slotEvolution (X z) (T - v z) m)
    (io ∘L U)
  linarith

/-- **One branch under the integrated certificate.** Under the hypotheses of
`GateSelect.branch_error` without the sample bound, the released slot-selected simulator for the
common time `α T` and accuracy `ε/2`, with the private operations of the label `z`, is within
`ε/2 + (βH + R βD) (T - v z)² / (2 · 2^m) + sampleErr z` of every propagator of the branch path
of `z` at `T - v z`, on its clean column with every wire compared. -/
theorem branch_error_cert (a m : ℕ) (UJ : Vsp a P →L[ℂ] Vsp a P)
    (D : Cfg L → ℕ → Vsp a P →L[ℂ] Vsp a P) (Hp Dp : ℝ → P →L[ℂ] P) (k v : Cfg L → ℝ)
    (X : Cfg L → ℕ → P →L[ℂ] P) (U : ℝ → P →L[ℂ] P) (z : Cfg L)
    (T α R βH βD Q qbar ε : ℝ) (hT : 0 < T) (hα : 0 < α)
    (hQ : 1 ≤ Q) (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hCayley : TimeSchedule.steps (α * T) (ε / 6) ≤ 2 ^ m)
    (hk : |k z| ≤ R) (hv0 : 0 ≤ v z) (hvT : v z ≤ T)
    (hUJ : IsUnitary UJ) (hD : ∀ j < 2 ^ m, IsUnitary (D z j))
    (hClock : ∀ j < 2 ^ m, GateODE.ClockPromise UJ (D z j)
      ((((T - v z) / (α * T) : ℝ) : ℂ) • X z j) Q qbar)
    (hX : ∀ j < 2 ^ m, star (X z j) = X z j) (hXn : ∀ j < 2 ^ m, ‖X z j‖ ≤ α)
    (hHp : ∀ t ∈ Set.Icc 0 T, star (Hp t) = Hp t) (hDp : ∀ t ∈ Set.Icc 0 T, star (Dp t) = Dp t)
    (hLipH : ∀ t ∈ Set.Icc 0 T, ∀ t' ∈ Set.Icc 0 T, ‖Hp t - Hp t'‖ ≤ βH * |t - t'|)
    (hLipD : ∀ t ∈ Set.Icc 0 T, ∀ t' ∈ Set.Icc 0 T, ‖Dp t - Dp t'‖ ≤ βD * |t - t'|)
    (hU0 : U 0 = 1) (hU : TimeDependent.SolvesOn (branchPath Hp Dp k v z) U 0 (T - v z)) :
    ‖SlotSim.runT UJ (D z) (SlotSim.simCircuitT a (α * T) Q qbar (ε / 2) m) ∘L io -
      io ∘L U (T - v z)‖ ≤
      ε / 2 + (βH + R * βD) * (T - v z) ^ 2 / (2 * 2 ^ m) + sampleErr Hp Dp k v X T m z := by
  have hu : 0 ≤ T - v z := sub_nonneg.mpr hvT
  have hLip := branchPath_lipschitz Hp Dp k v T R βH βD z hk hv0 hLipH hLipD
  have hint : IntervalIntegrable (branchPath Hp Dp k v z) volume 0 (T - v z) :=
    (TimeDependentExtensions.continuousOn_of_lipschitz _ hLip).intervalIntegrable_of_Icc hu
  have hProp : IsPropagator (branchPath Hp Dp k v z) U (T - v z) :=
    IntegrablePathSimulation.Propagator.isPropagator_of_solvesOn hu hU0 hU hint
  have hself := branchPath_selfAdjoint Hp Dp k v T z hv0 hHp hDp
  have h1 := branch_slot_error a m UJ D v X z T α Q qbar ε hT hα hQ hqQ hε hε1 hCayley hv0 hvT
    hUJ hD hClock hX hXn (U (T - v z))
  have h2 := GateMesh.slot_error_integral (X z) hu m hProp (ae_of_all _ hself) hX hint
  rw [norm_sub_rev] at h2
  have h3 := slot_cert_le (branchPath Hp Dp k v z) (X z) hu m hLip
  have h4 : ∑ j ∈ Finset.range (2 ^ m), (T - v z) / 2 ^ m *
      ‖branchPath Hp Dp k v z (slotMesh (T - v z) m j) - X z j‖ =
      sampleErr Hp Dp k v X T m z := rfl
  rw [h4] at h3
  linarith

end Branch

/-! ### The lemma -/

section Lemma

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **Lemma `ode:lem:gate-select` under the integrated sample-error certificate, exact gates.**

The circuit `SlotSim.simCircuitT a τ Q qbar (ε/2) m` for the common normalised time `τ = α T`,
read with the label- and slot-selected private call `D z j`, is fixed by the public numbers.
Labels `z` specify frequencies `|k z| ≤ R` and start times `0 ≤ v z ≤ T`; branch `z` runs on its
own mesh with the sample addresses `v z + j (T - v z) / 2^m`, and `D z j` carries the clock
promise of the released simulator for the normalised sample `((T - v z) / τ) X z j`,
`‖X z j‖ ≤ α`. Under
the mesh conditions `steps τ (ε/6) ≤ 2^m` and `8 (βH + R βD) T² ≤ ε 2^m` (the freezing
condition `M ≥ 8 L_* T²/δ` of equation `ode:eq:gate-select-mesh`) and the integrated
sample-error certificate `sampleErr z ≤ ε/16` of every label, the circuit consists of valid
elementary instructions, makes exactly `6d` private calls and `12d` calls of `U_J` or `U_J†`,
uses at most `200 (d+1)(a+m+r+1)` elementary gates, none of these counts depending on the labels,
and for every family of propagators `U z` of the branch paths (which exist) it is within `ε` of
the controlled direct sum `∑_z |z⟩⟨z| ⊗ U z (T - v z)` on the clean-input space, with the full
output compared. -/
theorem gate_select_certified (a m : ℕ) (UJ : Vsp a P →L[ℂ] Vsp a P)
    (D : Cfg L → ℕ → Vsp a P →L[ℂ] Vsp a P) (Hp Dp : ℝ → P →L[ℂ] P) (k v : Cfg L → ℝ)
    (X : Cfg L → ℕ → P →L[ℂ] P) (T α τ R βH βD Q qbar ε : ℝ) (hT : 0 < T) (hα : 0 < α)
    (hτ : α * T = τ)
    (hβH : 0 ≤ βH) (hβD : 0 ≤ βD) (hQ : 1 ≤ Q) (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hCayley : TimeSchedule.steps τ (ε / 6) ≤ 2 ^ m)
    (hFreeze : 8 * (βH + R * βD) * T ^ 2 ≤ ε * 2 ^ m)
    (hk : ∀ z, |k z| ≤ R) (hv0 : ∀ z, 0 ≤ v z) (hvT : ∀ z, v z ≤ T)
    (hUJ : IsUnitary UJ) (hD : ∀ z, ∀ j < 2 ^ m, IsUnitary (D z j))
    (hClock : ∀ z, ∀ j < 2 ^ m, GateODE.ClockPromise UJ (D z j)
      ((((T - v z) / τ : ℝ) : ℂ) • X z j) Q qbar)
    (hX : ∀ z, ∀ j < 2 ^ m, star (X z j) = X z j) (hXn : ∀ z, ∀ j < 2 ^ m, ‖X z j‖ ≤ α)
    (hHp : ∀ t ∈ Set.Icc 0 T, star (Hp t) = Hp t) (hDp : ∀ t ∈ Set.Icc 0 T, star (Dp t) = Dp t)
    (hLipH : ∀ t ∈ Set.Icc 0 T, ∀ t' ∈ Set.Icc 0 T, ‖Hp t - Hp t'‖ ≤ βH * |t - t'|)
    (hLipD : ∀ t ∈ Set.Icc 0 T, ∀ t' ∈ Set.Icc 0 T, ‖Dp t - Dp t'‖ ≤ βD * |t - t'|)
    (hCert : ∀ z, sampleErr Hp Dp k v X T m z ≤ ε / 16) :
    (∀ g ∈ SlotSim.simCircuitT a τ Q qbar (ε / 2) m, g.Valid Wire.anc) ∧
    nPriv (SlotSim.simCircuitT a τ Q qbar (ε / 2) m) = 6 * fDeg Q τ qbar (ε / 2) ∧
    nUJ (SlotSim.simCircuitT a τ Q qbar (ε / 2) m) = 12 * fDeg Q τ qbar (ε / 2) ∧
    nGates (SlotSim.simCircuitT a τ Q qbar (ε / 2) m) ≤
      200 * (fDeg Q τ qbar (ε / 2) + 1) * (a + m + simR Q τ qbar (ε / 2) + 1) ∧
    Fintype.card (SW a m (simR Q τ qbar (ε / 2))
        (a + m + 2 * simR Q τ qbar (ε / 2)) L) =
      2 * a + 3 * m + 6 * simR Q τ qbar (ε / 2) + 3 + Fintype.card L ∧
    (fDeg Q τ qbar (ε / 2) : ℝ) ≤ 128 * (τ * qbar + Q * (1 + Real.log (6 / ε))) ∧
    2 * fDeg Q τ qbar (ε / 2) + 2 ≤ 2 ^ simR Q τ qbar (ε / 2) ∧
    2 ^ simR Q τ qbar (ε / 2) ≤ 4 * (fDeg Q τ qbar (ε / 2) + 1) ∧
    (∀ z, ∃ U : ℝ → P →L[ℂ] P, U 0 = 1 ∧
      TimeDependent.SolvesOn (branchPath Hp Dp k v z) U 0 (T - v z)) ∧
    ∀ U : Cfg L → ℝ → P →L[ℂ] P, (∀ z, U z 0 = 1) →
      (∀ z, TimeDependent.SolvesOn (branchPath Hp Dp k v z) (U z) 0 (T - v z)) →
      ‖runS UJ D (SlotSim.simCircuitT a τ Q qbar (ε / 2) m) ∘L selE -
        selE ∘L WeightedClock.diagonal (fun z => U z (T - v z))‖ ≤ ε := by
  subst hτ
  have hτ : 0 < α * T := mul_pos hα hT
  have hε2 : 0 < ε / 2 := by linarith
  have hm : TimeSchedule.steps (α * T) (ε / 2 / 3) ≤ 2 ^ m := by
    rw [show ε / 2 / 3 = ε / 6 by ring]
    exact hCayley
  have hz0 : Cfg L := fun _ => false
  have hq : 0 ≤ qbar :=
    qbar_nonneg_of_clock UJ (D hz0 0) _ Q qbar (hClock hz0 0 (Nat.two_pow_pos m))
  have hR : 0 ≤ R := (abs_nonneg _).trans (hk hz0)
  have hβ : 0 ≤ βH + R * βD := add_nonneg hβH (mul_nonneg hR hβD)
  obtain ⟨hvalid, hP, hJ, hG⟩ := SlotSim.simCircuitT_public a m (α * T) Q qbar (ε / 2) hτ.le hε2 hm
  obtain ⟨hr1, -, hr2⟩ := GateCircuit.Sim.simR_spec Q (α * T) qbar (ε / 2)
  have hdeg : (fDeg Q (α * T) qbar (ε / 2) : ℝ) ≤
      128 * (α * T * qbar + Q * (1 + Real.log (6 / ε))) := by
    have h := SharpFilterSchedule.degree_le Q (α * T * qbar) (ε / 2 / 3) hQ
      (mul_nonneg hτ.le hq) (by positivity) (by linarith)
    have e1 : fDeg Q (α * T) qbar (ε / 2) =
        SharpFilterSchedule.degree Q (α * T * qbar) (ε / 2 / 3) := rfl
    have e2 : (1 : ℝ) / (ε / 2 / 3) = 6 / ε := by
      field_simp
      ring
    unfold SharpFilterSchedule.logBudget at h
    rw [e2] at h
    rw [e1]
    exact h
  have hcard : Fintype.card (SW a m (simR Q (α * T) qbar (ε / 2))
      (a + m + 2 * simR Q (α * T) qbar (ε / 2)) L) =
      2 * a + 3 * m + 6 * simR Q (α * T) qbar (ε / 2) + 3 + Fintype.card L := by
    rw [card_SW, card_wire]
    ring
  refine ⟨hvalid, hP, hJ, hG, hcard, hdeg, hr1, hr2, fun z => ?_, fun U hU0 hU => ?_⟩
  · exact TimeDependent.exists_solvesOn_of_lipschitz _ (sub_nonneg.mpr (hvT z))
      (branchPath_lipschitz Hp Dp k v T R βH βD z (hk z) (hv0 z) hLipH hLipD)
  · apply select_error UJ D _ (fun z => U z (T - v z)) ε hε.le
    intro z
    have h := branch_error_cert a m UJ D Hp Dp k v X (U z) z T α R βH βD Q qbar ε hT hα
      hQ hqQ hε hε1 hCayley (hk z) (hv0 z) (hvT z) hUJ (hD z) (hClock z) (hX z) (hXn z) hHp hDp
      hLipH hLipD (hU0 z) (hU z)
    refine h.trans ?_
    have hu : 0 ≤ T - v z := sub_nonneg.mpr (hvT z)
    have huT : T - v z ≤ T := by linarith [hv0 z]
    have hsq : (T - v z) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hu huT 2
    have hM : (0 : ℝ) < 2 ^ m := by positivity
    have hfr : (βH + R * βD) * (T - v z) ^ 2 / (2 * 2 ^ m) ≤ ε / 16 := by
      rw [div_le_iff₀ (by positivity)]
      have h1 := mul_le_mul_of_nonneg_left hsq hβ
      linarith
    have hc := hCert z
    linarith

/-- **Coherent selection under an integrated slot certificate, exact gates** (the "more
generally, a certificate for the same uniform meshes suffices" of Theorem `ode:thm:gates`).
Under the clock promises and the subdivision condition of `gate_select_certified`, for any
branch paths `h z` that are self-adjoint at almost every time of `[0, T - v z]` and interval
integrable, every family of integral-sense propagators `U z` of them, and slot certificates
`∑_j ∫_{slot j of branch z} ‖h z t - X z j‖ dt ≤ ε/2`, the circuit is within `ε` of the
controlled direct sum `∑_z |z⟩⟨z| ⊗ U z (T - v z)` on the clean-input space; no Lipschitz bound
is used. -/
theorem gate_select_integral (a m : ℕ) (UJ : Vsp a P →L[ℂ] Vsp a P)
    (D : Cfg L → ℕ → Vsp a P →L[ℂ] Vsp a P) (v : Cfg L → ℝ) (X : Cfg L → ℕ → P →L[ℂ] P)
    (T α τ Q qbar ε : ℝ) (hT : 0 < T) (hα : 0 < α) (hτ : α * T = τ) (hQ : 1 ≤ Q)
    (hqQ : qbar ≤ Q) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hCayley : TimeSchedule.steps τ (ε / 6) ≤ 2 ^ m)
    (hv0 : ∀ z, 0 ≤ v z) (hvT : ∀ z, v z ≤ T)
    (hUJ : IsUnitary UJ) (hD : ∀ z, ∀ j < 2 ^ m, IsUnitary (D z j))
    (hClock : ∀ z, ∀ j < 2 ^ m, GateODE.ClockPromise UJ (D z j)
      ((((T - v z) / τ : ℝ) : ℂ) • X z j) Q qbar)
    (hX : ∀ z, ∀ j < 2 ^ m, star (X z j) = X z j) (hXn : ∀ z, ∀ j < 2 ^ m, ‖X z j‖ ≤ α)
    (h U : Cfg L → ℝ → P →L[ℂ] P)
    (hH : ∀ z, ∀ᵐ t, t ∈ Icc 0 (T - v z) → star (h z t) = h z t)
    (hint : ∀ z, IntervalIntegrable (h z) volume 0 (T - v z))
    (hU : ∀ z, IsPropagator (h z) (U z) (T - v z))
    (hCert : ∀ z, ∑ j ∈ Finset.range (2 ^ m),
      ∫ t in slotMesh (T - v z) m j..slotMesh (T - v z) m (j + 1), ‖h z t - X z j‖ ≤ ε / 2) :
    ‖runS UJ D (SlotSim.simCircuitT a τ Q qbar (ε / 2) m) ∘L selE -
      selE ∘L WeightedClock.diagonal (fun z => U z (T - v z))‖ ≤ ε := by
  subst hτ
  apply select_error UJ D _ (fun z => U z (T - v z)) ε hε.le
  intro z
  have hu : 0 ≤ T - v z := sub_nonneg.mpr (hvT z)
  have h1 := branch_slot_error a m UJ D v X z T α Q qbar ε hT hα hQ hqQ hε hε1 hCayley (hv0 z)
    (hvT z) hUJ (hD z) (hClock z) (hX z) (hXn z) (U z (T - v z))
  have h2 := GateMesh.slot_error_integral (X z) hu m (hU z) (hH z) (hX z) (hint z)
  rw [norm_sub_rev] at h2
  refine h1.trans ?_
  have hc := hCert z
  linarith

end Lemma

end

end SparseHamiltonian.GateBinarySelect
