import GateEfficientSelect.Branch

/-!
# Lemma `ode:lem:gate-select`: gate-efficient coherent selection, exact gates

Labels `z` are the configurations of a finite set `L` of label wires. A label specifies a
frequency `k z` with `|k z| ≤ R` and a start time `0 ≤ v z ≤ T`; its branch is the time-ordered
propagator of `H(t) + k_z D(t)` from `v z` to `T`, i.e. the propagator at `T - v z` of the
shifted branch path `branchPath Hp Dp k v z t = H(v z + t) + k_z D(v z + t)`. Branch `z` is
discretised on its own uniform mesh of `2^m` slots of length `(T - v z) / 2^m`, with the sample
addresses `v z + j (T - v z) / 2^m`, as in the proof of the lemma.

**Circuit.** The released slot-selected simulator `SlotSim.simCircuitT a (α T) Q qbar (ε/2) m`
for the common normalised time `α T`, read with the label-selected private call (`runS`). It is
fixed by the public numbers; it does not depend on the labels, the start times, the frequencies
or the samples.

**Hypotheses** (`gate_select`): unitary `U_J` and `D z j`, where `D z j` carries the clock
promise of the released simulator (`GateODE.ClockPromise`) for the normalised sample
`((T - v z) / (α T)) X z j` of the represented Hermitian sample `X z j`, `‖X z j‖ ≤ α`; Hermitian
paths `H`, `D` on `[0, T]` with Lipschitz bounds `βH`, `βD`; samples
`‖H(v z + j u_z / 2^m) + k_z D(v z + j u_z / 2^m) - X z j‖ ≤ δ` with `u_z = T - v z`; the
public mesh conditions `steps (α T) (ε/6) ≤ 2^m` (subdivision of the Cayley steps) and
`4 (βH + R βD) T² ≤ ε 2^m` (freezing, the lemma's `L_* ≥ Lip(H) + R Lip(D)`), and the sample
budget `4 T δ ≤ ε`.

**Guarantees.** The circuit consists of valid elementary instructions; it makes exactly `6d`
label- and slot-selected private calls and `12d` calls of `U_J` or `U_J†`, and uses at most
`200 (d+1)(a+m+r+1)` elementary gates, with `d ≤ 128 (α T qbar + Q (1 + log (6/ε)))` and
`2d + 2 ≤ 2^r ≤ 4 (d+1)`; it acts on the `2a + 3m + 6r + 3` simulator wires and the label
wires. No count depends on the number of labels or of label wires, and the number `2^m` of
slots enters only through `m`. Every branch path has a propagator, and for every family of
propagators `U z` with `U z 0 = 1`, the circuit is within `ε` of the controlled direct sum
`∑_z |z⟩⟨z| ⊗ U z (T - v z)` on the clean-input space `selE`, with the full output compared,
including every simulator wire and on inputs entangled with an untouched reference inside the
system space. The inverse instruction list runs as the adjoint and has the same counts
(`gate_select_inverse`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSelect

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire Vsp io simR fDeg card_wire)
open scoped InnerProduct BigOperators

variable {L : Type*} {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]

/-- The branch path of the label `z`: `H + k_z D` from the start time `v z`. -/
def branchPath (Hp Dp : ℝ → P →L[ℂ] P) (k v : Cfg L → ℝ) (z : Cfg L) (t : ℝ) : P →L[ℂ] P :=
  Hp (v z + t) + ((k z : ℝ) : ℂ) • Dp (v z + t)

/-- The branch path is Hermitian on `[0, T - v z]`. -/
theorem branchPath_selfAdjoint [CompleteSpace P] (Hp Dp : ℝ → P →L[ℂ] P) (k v : Cfg L → ℝ) (T : ℝ)
    (z : Cfg L) (hv0 : 0 ≤ v z) (hHp : ∀ t ∈ Set.Icc 0 T, star (Hp t) = Hp t)
    (hDp : ∀ t ∈ Set.Icc 0 T, star (Dp t) = Dp t) :
    ∀ t ∈ Set.Icc 0 (T - v z), star (branchPath Hp Dp k v z t) = branchPath Hp Dp k v z t := by
  intro t ht
  have hmem : v z + t ∈ Set.Icc 0 T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  unfold branchPath
  rw [star_add, star_smul, hHp _ hmem, hDp _ hmem, Complex.star_def, Complex.conj_ofReal]

/-- The branch path is Lipschitz with constant `βH + R βD` on `[0, T - v z]`. -/
theorem branchPath_lipschitz (Hp Dp : ℝ → P →L[ℂ] P) (k v : Cfg L → ℝ) (T R βH βD : ℝ)
    (z : Cfg L) (hk : |k z| ≤ R) (hv0 : 0 ≤ v z)
    (hLipH : ∀ t ∈ Set.Icc 0 T, ∀ t' ∈ Set.Icc 0 T, ‖Hp t - Hp t'‖ ≤ βH * |t - t'|)
    (hLipD : ∀ t ∈ Set.Icc 0 T, ∀ t' ∈ Set.Icc 0 T, ‖Dp t - Dp t'‖ ≤ βD * |t - t'|) :
    ∀ t ∈ Set.Icc 0 (T - v z), ∀ t' ∈ Set.Icc 0 (T - v z),
      ‖branchPath Hp Dp k v z t - branchPath Hp Dp k v z t'‖ ≤ (βH + R * βD) * |t - t'| := by
  intro t ht t' ht'
  have hm : v z + t ∈ Set.Icc 0 T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hm' : v z + t' ∈ Set.Icc 0 T := ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  have hd : |v z + t - (v z + t')| = |t - t'| := by ring_nf
  have h1 := hLipH _ hm _ hm'
  have h2 := hLipD _ hm _ hm'
  rw [hd] at h1 h2
  unfold branchPath
  have e : Hp (v z + t) + ((k z : ℝ) : ℂ) • Dp (v z + t) -
      (Hp (v z + t') + ((k z : ℝ) : ℂ) • Dp (v z + t')) =
      (Hp (v z + t) - Hp (v z + t')) + ((k z : ℝ) : ℂ) • (Dp (v z + t) - Dp (v z + t')) := by
    rw [smul_sub]
    abel
  rw [e]
  calc _ ≤ ‖Hp (v z + t) - Hp (v z + t')‖ + |k z| * ‖Dp (v z + t) - Dp (v z + t')‖ := by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ βH * |t - t'| + R * (βD * |t - t'|) := by
        refine add_le_add h1 (mul_le_mul hk h2 (norm_nonneg _) ((abs_nonneg _).trans hk))
    _ = (βH + R * βD) * |t - t'| := by ring

/-- The error budget of one branch: `ε/2` for the simulation, `β u² / 2^m ≤ ε/4` for freezing
and `u δ ≤ ε/4` for the samples, when `u ≤ T`. -/
theorem branch_budget (β u T δ ε M : ℝ) (hβ : 0 ≤ β) (hu : 0 ≤ u) (huT : u ≤ T) (hδ : 0 ≤ δ)
    (hM : 0 < M) (hFreeze : 4 * β * T ^ 2 ≤ ε * M) (hValBudget : 4 * T * δ ≤ ε) :
    ε / 2 + β * u ^ 2 / M + u * δ ≤ ε := by
  have hsq : u ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hu huT 2
  have hfr : β * u ^ 2 / M ≤ ε / 4 := by
    rw [div_le_iff₀ hM]
    nlinarith [mul_le_mul_of_nonneg_left hsq hβ]
  have hsm : u * δ ≤ ε / 4 := by
    have := mul_le_mul_of_nonneg_right huT hδ
    linarith
  linarith

variable [CompleteSpace P]

/-- **One label of the selection.** For the label `z`, the released slot-selected simulator for
the common normalised time `α T`, with the private operations `D z j` of the label, is within
`ε` of every propagator of the branch path of `z` at `T - v z`, on its clean column with every
wire compared. -/
theorem branch_error (a m : ℕ) (UJ : Vsp a P →L[ℂ] Vsp a P)
    (D : Cfg L → ℕ → Vsp a P →L[ℂ] Vsp a P) (Hp Dp : ℝ → P →L[ℂ] P) (k v : Cfg L → ℝ)
    (X : Cfg L → ℕ → P →L[ℂ] P) (U : ℝ → P →L[ℂ] P) (z : Cfg L)
    (T α R βH βD δ Q qbar ε : ℝ) (hT : 0 < T) (hα : 0 < α)
    (hβH : 0 ≤ βH) (hβD : 0 ≤ βD) (hQ : 1 ≤ Q) (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hCayley : TimeSchedule.steps (α * T) (ε / 6) ≤ 2 ^ m)
    (hFreeze : 4 * (βH + R * βD) * T ^ 2 ≤ ε * 2 ^ m) (hValBudget : 4 * T * δ ≤ ε)
    (hk : |k z| ≤ R) (hv0 : 0 ≤ v z) (hvT : v z ≤ T)
    (hUJ : IsUnitary UJ) (hD : ∀ j < 2 ^ m, IsUnitary (D z j))
    (hClock : ∀ j < 2 ^ m, GateODE.ClockPromise UJ (D z j)
      ((((T - v z) / (α * T) : ℝ) : ℂ) • X z j) Q qbar)
    (hX : ∀ j < 2 ^ m, star (X z j) = X z j) (hXn : ∀ j < 2 ^ m, ‖X z j‖ ≤ α)
    (hHp : ∀ t ∈ Set.Icc 0 T, star (Hp t) = Hp t) (hDp : ∀ t ∈ Set.Icc 0 T, star (Dp t) = Dp t)
    (hLipH : ∀ t ∈ Set.Icc 0 T, ∀ t' ∈ Set.Icc 0 T, ‖Hp t - Hp t'‖ ≤ βH * |t - t'|)
    (hLipD : ∀ t ∈ Set.Icc 0 T, ∀ t' ∈ Set.Icc 0 T, ‖Dp t - Dp t'‖ ≤ βD * |t - t'|)
    (hVal : ∀ j : ℕ, j < 2 ^ m →
      ‖Hp (v z + j * (T - v z) / 2 ^ m) + ((k z : ℝ) : ℂ) • Dp (v z + j * (T - v z) / 2 ^ m) -
        X z j‖ ≤ δ)
    (hU0 : U 0 = 1) (hU : TimeDependent.SolvesOn (branchPath Hp Dp k v z) U 0 (T - v z)) :
    ‖SlotSim.runT UJ (D z) (SlotSim.simCircuitT a (α * T) Q qbar (ε / 2) m) ∘L io -
      io ∘L U (T - v z)‖ ≤ ε := by
  have hτ : 0 < α * T := mul_pos hα hT
  have hε2 : 0 < ε / 2 := by linarith
  have hε21 : ε / 2 ≤ 1 := by linarith
  have hm : TimeSchedule.steps (α * T) (ε / 2 / 3) ≤ 2 ^ m := by
    rw [show ε / 2 / 3 = ε / 6 by ring]
    exact hCayley
  have hR : 0 ≤ R := (abs_nonneg _).trans hk
  have hβ : 0 ≤ βH + R * βD := add_nonneg hβH (mul_nonneg hR hβD)
  have hu : 0 ≤ T - v z := sub_nonneg.mpr hvT
  have huT : T - v z ≤ T := by linarith
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hVal 0 (Nat.two_pow_pos m))
  have hXn' : ∀ j < 2 ^ m, (T - v z) * ‖X z j‖ ≤ α * T := by
    intro j hj
    calc (T - v z) * ‖X z j‖ ≤ T * α :=
          mul_le_mul huT (hXn j hj) (norm_nonneg _) hT.le
      _ = α * T := mul_comm _ _
  have hVal' : ∀ j : ℕ, j < 2 ^ m →
      ‖branchPath Hp Dp k v z (j * (T - v z) / 2 ^ m) - X z j‖ ≤ δ := fun j hj => hVal j hj
  have h := branch_propagator a m UJ (D z) (X z) (branchPath Hp Dp k v z) U (α * T)
    (T - v z) (βH + R * βD) δ Q qbar (ε / 2) hτ hu hβ hQ hqQ hε2 hε21 hm hUJ hD hX hXn' hClock
    (branchPath_selfAdjoint Hp Dp k v T z hv0 hHp hDp)
    (branchPath_lipschitz Hp Dp k v T R βH βD z hk hv0 hLipH hLipD) hVal' hU0 hU
  have hb := branch_budget (βH + R * βD) (T - v z) T δ ε (2 ^ m) hβ hu huT hδ (by positivity)
    hFreeze hValBudget
  exact h.trans hb

variable [Fintype L] [DecidableEq L]

/-- **Lemma `ode:lem:gate-select`: gate-efficient coherent selection, exact gates.**

The circuit `SlotSim.simCircuitT a (α T) Q qbar (ε/2) m`, read with the label- and
slot-selected private call `D z j`, is fixed by the public numbers. Labels `z` specify
frequencies `|k z| ≤ R` and start times `0 ≤ v z ≤ T`; branch `z` runs on its own mesh with the
sample addresses `v z + j (T - v z) / 2^m`, and `D z j` carries the clock promise of the
released simulator for the normalised sample `((T - v z) / (α T)) X z j`, `‖X z j‖ ≤ α`. Under
the mesh conditions `steps (α T) (ε/6) ≤ 2^m` and `4 (βH + R βD) T² ≤ ε 2^m` and the sample
budget `4 T δ ≤ ε`, the circuit consists of valid elementary instructions, makes exactly `6d`
private calls and `12d` calls of `U_J` or `U_J†`, uses at most `200 (d+1)(a+m+r+1)` elementary
gates, none of these counts depending on the labels, and for every family of propagators
`U z` of the branch paths (which exist) it is within `ε` of the controlled direct sum
`∑_z |z⟩⟨z| ⊗ U z (T - v z)` on the clean-input space, with the full output compared. -/
theorem gate_select (a m : ℕ) (UJ : Vsp a P →L[ℂ] Vsp a P)
    (D : Cfg L → ℕ → Vsp a P →L[ℂ] Vsp a P) (Hp Dp : ℝ → P →L[ℂ] P) (k v : Cfg L → ℝ)
    (X : Cfg L → ℕ → P →L[ℂ] P) (T α R βH βD δ Q qbar ε : ℝ) (hT : 0 < T) (hα : 0 < α)
    (hβH : 0 ≤ βH) (hβD : 0 ≤ βD) (hQ : 1 ≤ Q) (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hCayley : TimeSchedule.steps (α * T) (ε / 6) ≤ 2 ^ m)
    (hFreeze : 4 * (βH + R * βD) * T ^ 2 ≤ ε * 2 ^ m) (hValBudget : 4 * T * δ ≤ ε)
    (hk : ∀ z, |k z| ≤ R) (hv0 : ∀ z, 0 ≤ v z) (hvT : ∀ z, v z ≤ T)
    (hUJ : IsUnitary UJ) (hD : ∀ z, ∀ j < 2 ^ m, IsUnitary (D z j))
    (hClock : ∀ z, ∀ j < 2 ^ m, GateODE.ClockPromise UJ (D z j)
      ((((T - v z) / (α * T) : ℝ) : ℂ) • X z j) Q qbar)
    (hX : ∀ z, ∀ j < 2 ^ m, star (X z j) = X z j) (hXn : ∀ z, ∀ j < 2 ^ m, ‖X z j‖ ≤ α)
    (hHp : ∀ t ∈ Set.Icc 0 T, star (Hp t) = Hp t) (hDp : ∀ t ∈ Set.Icc 0 T, star (Dp t) = Dp t)
    (hLipH : ∀ t ∈ Set.Icc 0 T, ∀ t' ∈ Set.Icc 0 T, ‖Hp t - Hp t'‖ ≤ βH * |t - t'|)
    (hLipD : ∀ t ∈ Set.Icc 0 T, ∀ t' ∈ Set.Icc 0 T, ‖Dp t - Dp t'‖ ≤ βD * |t - t'|)
    (hVal : ∀ z, ∀ j : ℕ, j < 2 ^ m →
      ‖Hp (v z + j * (T - v z) / 2 ^ m) + ((k z : ℝ) : ℂ) • Dp (v z + j * (T - v z) / 2 ^ m) -
        X z j‖ ≤ δ) :
    (∀ g ∈ SlotSim.simCircuitT a (α * T) Q qbar (ε / 2) m, g.Valid Wire.anc) ∧
    nPriv (SlotSim.simCircuitT a (α * T) Q qbar (ε / 2) m) = 6 * fDeg Q (α * T) qbar (ε / 2) ∧
    nUJ (SlotSim.simCircuitT a (α * T) Q qbar (ε / 2) m) = 12 * fDeg Q (α * T) qbar (ε / 2) ∧
    nGates (SlotSim.simCircuitT a (α * T) Q qbar (ε / 2) m) ≤
      200 * (fDeg Q (α * T) qbar (ε / 2) + 1) * (a + m + simR Q (α * T) qbar (ε / 2) + 1) ∧
    Fintype.card (SW a m (simR Q (α * T) qbar (ε / 2))
        (a + m + 2 * simR Q (α * T) qbar (ε / 2)) L) =
      2 * a + 3 * m + 6 * simR Q (α * T) qbar (ε / 2) + 3 + Fintype.card L ∧
    (fDeg Q (α * T) qbar (ε / 2) : ℝ) ≤ 128 * (α * T * qbar + Q * (1 + Real.log (6 / ε))) ∧
    2 * fDeg Q (α * T) qbar (ε / 2) + 2 ≤ 2 ^ simR Q (α * T) qbar (ε / 2) ∧
    2 ^ simR Q (α * T) qbar (ε / 2) ≤ 4 * (fDeg Q (α * T) qbar (ε / 2) + 1) ∧
    (∀ z, ∃ U : ℝ → P →L[ℂ] P, U 0 = 1 ∧
      TimeDependent.SolvesOn (branchPath Hp Dp k v z) U 0 (T - v z)) ∧
    ∀ U : Cfg L → ℝ → P →L[ℂ] P, (∀ z, U z 0 = 1) →
      (∀ z, TimeDependent.SolvesOn (branchPath Hp Dp k v z) (U z) 0 (T - v z)) →
      ‖runS UJ D (SlotSim.simCircuitT a (α * T) Q qbar (ε / 2) m) ∘L selE -
        selE ∘L WeightedClock.diagonal (fun z => U z (T - v z))‖ ≤ ε := by
  have hτ : 0 < α * T := mul_pos hα hT
  have hε2 : 0 < ε / 2 := by linarith
  have hε21 : ε / 2 ≤ 1 := by linarith
  have hm : TimeSchedule.steps (α * T) (ε / 2 / 3) ≤ 2 ^ m := by
    rw [show ε / 2 / 3 = ε / 6 by ring]
    exact hCayley
  have hz0 : Cfg L := fun _ => false
  have hq : 0 ≤ qbar :=
    qbar_nonneg_of_clock UJ (D hz0 0) _ Q qbar (hClock hz0 0 (Nat.two_pow_pos m))
  have hR : 0 ≤ R := (abs_nonneg _).trans (hk hz0)
  obtain ⟨hvalid, hP, hJ, hG⟩ := SlotSim.simCircuitT_public a m (α * T) Q qbar (ε / 2) hτ.le hε2 hm
  obtain ⟨hr1, -, hr2⟩ := GateCircuit.Sim.simR_spec Q (α * T) qbar (ε / 2)
  -- the degree bound
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
  -- the register
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
    exact branch_error a m UJ D Hp Dp k v X (U z) z T α R βH βD δ Q qbar ε hT hα hβH hβD hQ hqQ
      hε hε1 hCayley hFreeze hValBudget (hk z) (hv0 z) (hvT z) hUJ (hD z) (hClock z) (hX z)
      (hXn z) hHp hDp hLipH hLipD (hVal z) (hU0 z) (hU z)

/-- **The inverse of the selection circuit** is the adjoint of the actual circuit and has the
same validity and counts. -/
theorem gate_select_inverse {a m r K : ℕ} (UJ : Vsp a P →L[ℂ] Vsp a P)
    (D : Cfg L → ℕ → Vsp a P →L[ℂ] Vsp a P) (C : List (Instr (Wire a m r K)))
    (hC : ∀ g ∈ C, g.Valid Wire.anc) :
    runS UJ D (invList C) = (runS UJ D C)† ∧
    (∀ g ∈ invList C, g.Valid Wire.anc) ∧
    nPriv (invList C) = nPriv C ∧ nUJ (invList C) = nUJ C ∧ nGates (invList C) = nGates C := by
  refine ⟨runS_invList UJ D C, ?_, nPriv_invList C, nUJ_invList C, nGates_invList C⟩
  intro g hg
  simp only [invList, List.mem_reverse, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  exact Instr.valid_inv _ g' (hC g' hg')

end

end SparseHamiltonian.GateSelect
