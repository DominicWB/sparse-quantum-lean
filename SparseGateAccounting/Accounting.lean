import SparseGateAccounting.Promises

/-!
# The explicit accounting of Theorem `hs:thm:gates` for sparse access of general size

Equations `hs:eq:gate-known`, `hs:eq:gate-Gzero` and `hs:eq:gate-total`, for sparse access of
general size (`GeneralSparseAccess.QData`) with any public decoder `D.val`, and for any supplied
finite-set controlled private circuit `pc`. The circuit `pc` calls the supplied sparse oracles
(`D.prims x`) and is within `ξ`, on clean work wires, of the enable-controlled private Cayley
operation of the normalised padded data (`PrivOK`); it carries all of the decoding, the rotation
arithmetic, the validity tests and the routing, so `G_C(ξ) = nGatesN pc` and
`A_C(ξ) = |Z| + bT + bP + A`; the qubit count adds three flag wires of the controlled `U_J` gates,
the enable wire of `pc` is the sector wire of the simulator, and the gates inside the supplied
oracles are not counted.

The clock promises of the construction are discharged, not assumed:

* `sparse_known_gates`: before synthesis, exactly `6 d` times the primitive calls of `pc`, exactly
  `6 d G_C` gates inside the private calls, at most `G₀ ≤ 884 d (C_J + a + m + r)` other gates
  (`hs:eq:gate-known`), and error `ε/2 + 6 d ξ`;
* `sparse_gate_total`: over the gate set, with `24 d ξ ≤ ε` (so `ξ = ε/(24 d)` of
  `hs:eq:gate-Gzero`, `xi_budget`): gates `6 d G_C + G₀ (c₁ log((G₀+1)/(ε/4)) + c₀ + 1)`, the exact
  qubit count, error `ε` on all output registers with an untouched reference (`hs:eq:gate-total`),
  and the schedule `hs:eq:gate-schedule`, `hs:eq:gate-clocks` with `s'` in place of `s`;
* `sparse_gate_total_signed`: every real time: the compiled circuit of `|t|` for `t ≥ 0`, its literal
  inverse for `t < 0`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.SparseGateAccounting

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim GateNative GateSynth
  GateSelective GateBinary GateSchedule GeneralSparseAccess CayleyClockInterface
open GateSynthTrials (AdjClosed)
open ManuscriptConformance (cleanAlong exp_padForm_comp)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

variable {X : Type*} {N s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {Z : Type*} [Fintype Z] [DecidableEq Z] {bT bP A : ℕ}
variable {Xs : Type*} [Fintype Xs] [DecidableEq Xs] {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- **A supplied controlled private circuit**: on the enable wire, the private register of
`a = k + 2` ancillas and `k + 1` system qubits, the work wires `Z` and the arithmetic wires, calling
the supplied sparse oracles. -/
abbrev PrivC (k b : ℕ) (Z : Type*) (bT bP A : ℕ) :=
  List (NInstr (PWr Empty (Fin (k + 1 + 1) ⊕ Fin (k + 1)) Z bT bP A) (PY k b) Query)

/-- **The promise of the supplied circuit**: on clean work wires, with the supplied oracles of the
instance `x`, within `ξ` of the enable-controlled private Cayley operation of the normalised padded
data. -/
abbrev PrivOK (D : QData X N s k b) (η : ℝ) (hη : 0 < η) (x : X) (γ ξ : ℝ)
    (pc : PrivC k b Z bT bP A) : Prop :=
  ApproxOn CleanP (nrun (D.prims (R := R) x) pc)
    (ctrlIdeal (selOp (fun _ : Cfg Empty => Dbin (R := R) (normPad D η hη) (Equiv.refl _) x γ))) ξ

/-- The native circuit with the manuscript's schedule at `s'` and the supplied private circuit. -/
abbrev preC (D : QData X N s k b) (γ τ ε : ℝ) (pc : PrivC k b Z bT bP A) :=
  simPMs (k + 1 + 1) τ (width ((sP s : ℕ) : ℝ) γ) (moment γ) ε (padUJ D) pc

/-- The selective finite-set circuit: the supplied circuit retained, the rest synthesised. -/
abbrev finC (hS : Synthesis 𝒢 Xs L) (D : QData X N s k b) (γ τ ε : ℝ)
    (pc : PrivC k b Z bT bP A) :=
  selSimMs hS (k + 1 + 1) τ (width ((sP s : ℕ) : ℝ) γ) (moment γ) ε (padUJ D) pc

/-- The selective finite-set circuit for a signed clock. -/
abbrev finCSigned (hS : Synthesis 𝒢 Xs L) (D : QData X N s k b) (γ t ε : ℝ)
    (pc : PrivC k b Z bT bP A) :=
  selSimMsSigned hS (k + 1 + 1) t (width ((sP s : ℕ) : ℝ) γ) (moment γ) ε (padUJ D) pc

/-- The instance promises pass to the normalised padded data. -/
theorem normPad_energies (D : QData X N s k b) {η : ℝ} (hη : 0 < η) {x : X}
    (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ((normPad D η hη).matrix x).IsHermitian ∧
      (∀ i, ∑ j, ‖(normPad D η hη).matrix x i j‖ ^ 2 ≤ 1) ∧
      (∀ j, ∑ i, ‖(normPad D η hη).matrix x i j‖ ^ 2 ≤ 1) := by
  have hM := padForm_padDataE D
  exact ⟨NativeSparseRescaling.normalize_hermitian _ η hη x (hM.isHermitian x hH),
    fun i => NativeSparseRescaling.normalized_row_energy _ η hη x i (hM.row_le x hrow i),
    fun j => NativeSparseRescaling.normalized_column_energy _ η hη x j (hM.col_le x hcol j)⟩

/-- The slots of the normalised padded data are the low words of `⌈log₂ s⌉` bits. -/
theorem normPad_range (D : QData X N s k b) (η : ℝ) (hη : 0 < η) (j : Cfg (Fin (k + 1))) :
    (∃ m, (normPad D η hη).slot m = j) ↔
      ∃ u : Fin (sbP s) → Bool, j = (Equiv.refl (Cfg (Fin (k + 1)))) (lowWord (sbP s) u) :=
  pslot_range D.s_le_pow j

/-- **The accuracy `ξ = ε/(24 d)`**, the form of `hs:eq:gate-Gzero` at the degree `d` of `s'`, meets
the budget of the private calls. -/
theorem xi_budget (s : ℕ) (γ : ℝ) {τ ε : ℝ} (hτ : 0 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    24 * (dg s γ τ ε : ℝ) * (ε / (24 * (dg s γ τ ε : ℝ))) = ε := by
  have hd : (0 : ℝ) < (dg s γ τ ε : ℝ) := by exact_mod_cast dg_pos s γ hτ hε hε1
  field_simp

set_option maxRecDepth 8192 in
/-- **Equation `hs:eq:gate-known`** for sparse access of general size. For `QData` with any decoder,
row and column norms at most `η`, a rescaling `0 < γ ≤ 1`, the time `T ≥ 0`, the clock `τ = αT`
(`clock`), `0 < ε ≤ 1` and a valid supplied private circuit `pc` with the promise `PrivOK`: the
native circuit is valid; it makes exactly `6 d` times the primitive calls of `pc`; its gates are
those of its `6 d` private calls and the known gates of the empty private circuit, at most
`G₀ ≤ 884 d (C_J + a + m + r)`, `a = k + 2`, `C_J = ⌈log₂ s⌉ + 1`; it has the stated qubit count;
and its full output is within `ε/2 + 6 d ξ` of the evolution, both on the padded index register and
on the clean marker against `QData.padMat`, with an untouched reference `R`. -/
theorem sparse_known_gates (D : QData X N s k b) {η : ℝ} (hη : 0 < η) (pc : PrivC k b Z bT bP A)
    (hpcV : ∀ i ∈ pc, i.Valid) (ξ : ℝ) (hξ : 0 ≤ ξ) (γ T τ ε : ℝ) (hτ : τ = clock s η T γ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hT : 0 ≤ T) (hε : 0 < ε) (hε1 : ε ≤ 1) (x : X)
    (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (hpc : PrivOK (R := R) D η hη x γ ξ pc) :
    (∀ i ∈ preC D γ τ ε pc, i.Valid) ∧
    (∀ p : Query → Bool, nCallsN p (preC D γ τ ε pc) = 6 * dg s γ τ ε * nCallsN p pc) ∧
    nGatesN (preC D γ τ ε pc) =
      nGatesN (preC D γ τ ε ([] : PrivC k b Z bT bP A)) + 6 * dg s γ τ ε * nGatesN pc ∧
    nGatesN (preC D γ τ ε ([] : PrivC k b Z bT bP A)) ≤ synG k s γ τ ε ∧
    synG k s γ τ ε ≤ 884 * (dg s γ τ ε * (sbP s + 1 + (k + 1 + 1) + slotMs τ ε + rg s γ τ ε)) ∧
    Fintype.card (HW (SimWireMs (k + 1 + 1) (width ((sP s : ℕ) : ℝ) γ) τ (moment γ) ε) (Fin (k + 1))
        Empty Z bT bP A) =
      k + 1 + (2 * (k + 1 + 1) + 3 * slotMs τ ε + 6 * rg s γ τ ε + 3) +
        (Fintype.card Z + bT + bP + A + 3) ∧
    ‖nrun (D.prims (R := R) x) (preC D γ τ ε pc) ∘L sysEmb (io (P := Reg (Fin (k + 1)) R)) -
        sysEmb (io (P := Reg (Fin (k + 1)) R)) ∘L NormedSpace.exp ((-Complex.I * (T : ℂ)) •
          qlift (R := R) (Equiv.refl _)
            (SparseStateOverlap.matrixOperator (D.padDataE.matrix x)))‖ ≤
      ε / 2 + 6 * dg s γ τ ε * ξ ∧
    ‖nrun (D.prims (R := R) x) (preC D γ τ ε pc) ∘L
        (sysEmb (io (P := Reg (Fin (k + 1)) R)) ∘L
          cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) -
        (sysEmb (io (P := Reg (Fin (k + 1)) R)) ∘L
          cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) ∘L
          NormedSpace.exp ((-Complex.I * (T : ℂ)) • qlift (R := R) (Equiv.refl _)
            (SparseStateOverlap.matrixOperator (D.padMat x)))‖ ≤
      ε / 2 + 6 * dg s γ τ ε * ξ := by
  obtain ⟨hH', hrow', hcol'⟩ := normPad_energies D hη hH hrow hcol
  have hτ0 : 0 ≤ τ := by
    rw [hτ]
    exact div_nonneg (mul_nonneg (mul_nonneg hη.le hT) (Real.sqrt_nonneg _)) hγ.le
  have he : (-Complex.I * (τ : ℂ)) • Hbin (R := R) (normPad D η hη) (Equiv.refl _) x γ =
      (-Complex.I * (T : ℂ)) • qlift (R := R) (Equiv.refl _)
        (SparseStateOverlap.matrixOperator (D.padDataE.matrix x)) := by
    rw [hτ]
    exact evolution_eq D hη x hH' T hγ
  obtain ⟨hv, hc, hg, hg0, -, herr⟩ := sim_supplied_ms (k + 1 + 1) (D.prims (R := R) x)
    (D.prims_isUnitary x) (padUJ D) (hadUJ_ok _ _) pc hpcV ξ hξ
    (Dbin (R := R) (normPad D η hη) (Equiv.refl _) x γ)
    (R1bin (R := R) (normPad D η hη) (Equiv.refl _) x γ)
    (Hbin (R := R) (normPad D η hη) (Equiv.refl _) x γ)
    (Dbin_isUnitary _ _ x γ) hpc τ (width ((sP s : ℕ) : ℝ) γ) (endpoint γ) (moment γ)
    ε hτ0 (width_ge_one _ _) (one_sub_Dbin_R1bin _ _ x γ) (R1bin_one_sub_Dbin _ _ x γ)
    (norm_R1bin_le _ _ x γ hγ.le hrow')
    (R1bin_boundary _ _ (sbP s) (sbP_le_succ D) rfl (normPad_range D η hη) x γ)
    (Hbin_self _ _ x γ) (norm_Hbin_le _ _ x γ hγ.le hγ1 hrow' hcol')
    (R1bin_endpoint _ _ (sbP s) (sbP_le_succ D) rfl (normPad_range D η hη) x γ hγ.le hrow' hcol')
    (endpoint_sq γ).le (moment_le_width _ γ hγ.le hγ1) hε hε1
  rw [padUJ_length D] at hg0
  rw [he] at herr
  refine ⟨hv, hc, hg, hg0, synG_le k s γ hτ0 hε hε1, ?_, ?_, ?_⟩
  · rw [card_HW, card_wire]
    simp only [Fintype.card_empty, Fintype.card_fin, simKK]
    ring
  · convert herr using 4
  · convert error_low herr using 2
    rw [sub_comp]
    simp only [comp_assoc]
    rw [exp_padForm_comp D (padForm_padDataE D) x T]

set_option maxRecDepth 8192 in
/-- **Equations `hs:eq:gate-Gzero` and `hs:eq:gate-total`** for sparse access of general size. Under
the synthesis hypothesis with `L ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]`, an adjoint-closed `𝒢`, and the
hypotheses of `sparse_known_gates` for a supplied circuit `pc` over `𝒢` with `24 d ξ ≤ ε`: the
selective circuit consists of valid gates of `𝒢` and primitive calls; it makes exactly `6 d` times
the primitive calls of `pc`; it synthesises at most `G₀` gate occurrences; it has at most
`6 d G_C + G₀ (c₁ log((G₀+1)/(ε/4)) + c₀ + 1)` gates, `G_C = nGatesN pc`; it has
`k + 1 + (2a + 3m + 6r + 3) + (|Z| + bT + bP + A + 3) + |Xs|` qubits; its full output, with every
qubit outside the system clean and an untouched reference, is within `ε` of the evolution, on the
padded index register and on the clean marker against `QData.padMat`; `d = k' (⌈32Q⌉ - 1)`,
`k' = ⌈4W/Q + log₂(4096/ε)⌉` (`depthMs`), with
`d ≤ 128 W + 32 Q (log₂(4096/ε) + 1)`; `2^m` is the least power of two at least
`max{2, 4τ, √(τ³/(3ε))}`; and `r = ⌈log₂(2d + 2)⌉`. -/
theorem sparse_gate_total (hS : Synthesis 𝒢 Xs L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (D : QData X N s k b) {η : ℝ} (hη : 0 < η) (pc : PrivC k b Z bT bP A)
    (hpcV : ∀ i ∈ pc, i.Valid) (hpcG : ∀ g, NInstr.gate g ∈ pc → GateOf 𝒢 g) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (γ T τ ε : ℝ) (hτ : τ = clock s η T γ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hT : 0 ≤ T) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hξε : 24 * (dg s γ τ ε : ℝ) * ξ ≤ ε) (x : X) (hH : (D.matrix x).IsHermitian)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (hpc : PrivOK (R := R) D η hη x γ ξ pc) :
    (∀ i ∈ finC hS D γ τ ε pc, i.Valid) ∧
    (∀ g, NInstr.gate g ∈ finC hS D γ τ ε pc → GateOf 𝒢 g) ∧
    (∀ p : Query → Bool, nCallsN p (finC hS D γ τ ε pc) = 6 * dg s γ τ ε * nCallsN p pc) ∧
    nSynN 𝒢 (preC D γ τ ε pc) ≤ synG k s γ τ ε ∧
    (nGatesN (finC hS D γ τ ε pc) : ℝ) ≤
      6 * (dg s γ τ ε : ℝ) * nGatesN pc + (synG k s γ τ ε : ℝ) *
        (c₁ * Real.log (((synG k s γ τ ε : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
    Fintype.card (HW (SimWireMs (k + 1 + 1) (width ((sP s : ℕ) : ℝ) γ) τ (moment γ) ε) (Fin (k + 1))
        Empty Z bT bP A ⊕ Xs) =
      k + 1 + (2 * (k + 1 + 1) + 3 * slotMs τ ε + 6 * rg s γ τ ε + 3) +
        (Fintype.card Z + bT + bP + A + 3) + Fintype.card Xs ∧
    ‖nrun (D.prims (R := R) x) (finC hS D γ τ ε pc) ∘L
        (cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          NormedSpace.exp ((-Complex.I * (T : ℂ)) • qlift (R := R) (Equiv.refl _)
            (SparseStateOverlap.matrixOperator (D.padDataE.matrix x)))‖ ≤ ε ∧
    ‖nrun (D.prims (R := R) x) (finC hS D γ τ ε pc) ∘L
        ((cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) -
        ((cleanEmb ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) ∘L
          NormedSpace.exp ((-Complex.I * (T : ℂ)) • qlift (R := R) (Equiv.refl _)
            (SparseStateOverlap.matrixOperator (D.padMat x)))‖ ≤ ε ∧
    dg s γ τ ε = depthMs (width ((sP s : ℕ) : ℝ) γ) (τ * moment γ) ε *
      (SharpFilterSchedule.length (width ((sP s : ℕ) : ℝ) γ) - 1) ∧
    (dg s γ τ ε : ℝ) ≤ 128 * (τ * moment γ) +
      32 * width ((sP s : ℕ) : ℝ) γ * (Real.logb 2 (4096 / ε) + 1) ∧
    meshMs τ ε ≤ 2 ^ slotMs τ ε ∧ (∀ j : ℕ, meshMs τ ε ≤ 2 ^ j → slotMs τ ε ≤ j) ∧
    rg s γ τ ε = Nat.clog 2 (2 * dg s γ τ ε + 2) := by
  obtain ⟨hH', hrow', hcol'⟩ := normPad_energies D hη hH hrow hcol
  have hτ0 : 0 ≤ τ := by
    rw [hτ]
    exact div_nonneg (mul_nonneg (mul_nonneg hη.le hT) (Real.sqrt_nonneg _)) hγ.le
  have he : (-Complex.I * (τ : ℂ)) • Hbin (R := R) (normPad D η hη) (Equiv.refl _) x γ =
      (-Complex.I * (T : ℂ)) • qlift (R := R) (Equiv.refl _)
        (SparseStateOverlap.matrixOperator (D.padDataE.matrix x)) := by
    rw [hτ]
    exact evolution_eq D hη x hH' T hγ
  obtain ⟨hv, hk, hc, hsyn, hg, -, herr, hd, hdle, hm, hl⟩ := sel_simulation_ms hS hadj hc₀ hc₁
    hL (k + 1 + 1) (D.prims (R := R) x) (D.prims_isUnitary x) (padUJ D) (hadUJ_ok _ _) pc hpcV hpcG
    ξ hξ (Dbin (R := R) (normPad D η hη) (Equiv.refl _) x γ)
    (R1bin (R := R) (normPad D η hη) (Equiv.refl _) x γ)
    (Hbin (R := R) (normPad D η hη) (Equiv.refl _) x γ)
    (Dbin_isUnitary _ _ x γ) hpc τ (width ((sP s : ℕ) : ℝ) γ) (endpoint γ) (moment γ)
    ε hτ0 (width_ge_one _ _) (one_sub_Dbin_R1bin _ _ x γ) (R1bin_one_sub_Dbin _ _ x γ)
    (norm_R1bin_le _ _ x γ hγ.le hrow')
    (R1bin_boundary _ _ (sbP s) (sbP_le_succ D) rfl (normPad_range D η hη) x γ)
    (Hbin_self _ _ x γ) (norm_Hbin_le _ _ x γ hγ.le hγ1 hrow' hcol')
    (R1bin_endpoint _ _ (sbP s) (sbP_le_succ D) rfl (normPad_range D η hη) x γ hγ.le hrow' hcol')
    (endpoint_sq γ).le (moment_le_width _ γ hγ.le hγ1) hε hε1 hξε
  rw [padUJ_length D] at hsyn hg
  rw [he] at herr
  refine ⟨hv, hk, hc, hsyn, hg, ?_, ?_, ?_, hd, hdle, hm, hl, rfl⟩
  · rw [Fintype.card_sum, card_HW, card_wire]
    simp only [Fintype.card_empty, Fintype.card_fin, simKK]
    ring
  · convert herr using 4
  · convert error_low herr using 2
    rw [sub_comp]
    simp only [comp_assoc]
    rw [exp_padForm_comp D (padForm_padDataE D) x T]

set_option maxRecDepth 8192 in
/-- **Every real time** (`sparse_gate_total`): for the signed clock `t' = η t √s' / γ` the circuit
of `|t'|`, or its literal reverse-adjoint for `t < 0`, has the same validity, gate set, calls, gates
and qubit count, and its full output is within `ε` of `exp(-itH)`. Here `|t'|` is the clock of `|t|`
(`abs_clock`), so the schedule is that of `sparse_gate_total` at the time `|t|`. -/
theorem sparse_gate_total_signed (hS : Synthesis 𝒢 Xs L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (D : QData X N s k b) {η : ℝ} (hη : 0 < η) (pc : PrivC k b Z bT bP A)
    (hpcV : ∀ i ∈ pc, i.Valid) (hpcG : ∀ g, NInstr.gate g ∈ pc → GateOf 𝒢 g) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (γ t t' ε : ℝ) (ht' : t' = clock s η t γ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hξε : 24 * (dg s γ |t'| ε : ℝ) * ξ ≤ ε) (x : X) (hH : (D.matrix x).IsHermitian)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (hpc : PrivOK (R := R) D η hη x γ ξ pc) :
    (∀ i ∈ finCSigned hS D γ t' ε pc, i.Valid) ∧
    (∀ g, NInstr.gate g ∈ finCSigned hS D γ t' ε pc → GateOf 𝒢 g) ∧
    (∀ p : Query → Bool, nCallsN p (finCSigned hS D γ t' ε pc) = 6 * dg s γ |t'| ε * nCallsN p pc) ∧
    (nGatesN (finCSigned hS D γ t' ε pc) : ℝ) ≤
      6 * (dg s γ |t'| ε : ℝ) * nGatesN pc + (synG k s γ |t'| ε : ℝ) *
        (c₁ * Real.log (((synG k s γ |t'| ε : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
    Fintype.card (HW (SimWireMs (k + 1 + 1) (width ((sP s : ℕ) : ℝ) γ) |t'| (moment γ) ε)
        (Fin (k + 1)) Empty Z bT bP A ⊕ Xs) =
      k + 1 + (2 * (k + 1 + 1) + 3 * slotMs |t'| ε + 6 * rg s γ |t'| ε + 3) +
        (Fintype.card Z + bT + bP + A + 3) + Fintype.card Xs ∧
    ‖nrun (D.prims (R := R) x) (finCSigned hS D γ t' ε pc) ∘L
        (cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
            (SparseStateOverlap.matrixOperator (D.padDataE.matrix x)))‖ ≤ ε ∧
    ‖nrun (D.prims (R := R) x) (finCSigned hS D γ t' ε pc) ∘L
        ((cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) -
        ((cleanEmb ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
            (SparseStateOverlap.matrixOperator (D.padMat x)))‖ ≤ ε := by
  subst ht'
  obtain ⟨hH', hrow', hcol'⟩ := normPad_energies D hη hH hrow hcol
  obtain ⟨hv, hk, hc, hg, herr⟩ := sel_simulation_ms_signed hS hadj hc₀ hc₁
    hL (k + 1 + 1) (D.prims (R := R) x) (D.prims_isUnitary x) (padUJ D) (hadUJ_ok _ _) pc hpcV hpcG
    ξ hξ (Dbin (R := R) (normPad D η hη) (Equiv.refl _) x γ)
    (R1bin (R := R) (normPad D η hη) (Equiv.refl _) x γ)
    (Hbin (R := R) (normPad D η hη) (Equiv.refl _) x γ)
    (Dbin_isUnitary _ _ x γ) hpc (clock s η t γ) (width ((sP s : ℕ) : ℝ) γ) (endpoint γ) (moment γ)
    ε (width_ge_one _ _) (one_sub_Dbin_R1bin _ _ x γ) (R1bin_one_sub_Dbin _ _ x γ)
    (norm_R1bin_le _ _ x γ hγ.le hrow')
    (R1bin_boundary _ _ (sbP s) (sbP_le_succ D) rfl (normPad_range D η hη) x γ)
    (Hbin_self _ _ x γ) (norm_Hbin_le _ _ x γ hγ.le hγ1 hrow' hcol')
    (R1bin_endpoint _ _ (sbP s) (sbP_le_succ D) rfl (normPad_range D η hη) x γ hγ.le hrow' hcol')
    (endpoint_sq γ).le (moment_le_width _ γ hγ.le hγ1) hε hε1 hξε
  rw [padUJ_length D] at hg
  rw [evolution_eq D hη x hH' t hγ] at herr
  refine ⟨hv, hk, hc, hg, ?_, herr, ?_⟩
  · rw [Fintype.card_sum, card_HW, card_wire]
    simp only [Fintype.card_empty, Fintype.card_fin, simKK]
    ring
  · convert error_low herr using 2
    rw [sub_comp]
    simp only [comp_assoc]
    rw [exp_padForm_comp D (padForm_padDataE D) x t]

end

end SparseHamiltonian.SparseGateAccounting
