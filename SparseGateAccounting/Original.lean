import SparseGateAccounting.Native

/-!
# The sparse accounting on the schedule of the original sparsity `s`

`SparseGateAccounting.Accounting` and `Native` run the schedule at the padded slot count
`s' = 2^⌈log₂ s⌉`, because the boundary circuit `U_J` there is the Hadamard gates on the low slot
wires, which prepare the uniform superposition of all `s'` slot words. This file keeps the original
sparsity `s` in the boundary normalisation, the clock and the schedule:

* `restrictSlots`: the first `s` slots of sparse data with `s'` slots, when they cover every nonzero
  entry (same entries, table, decoder and oracles);
* `padDataS D`: the padded data with the validity decoder restricted to its first `s` slots (the
  slots of the original lists; `padDataS_row_covers`, `padDataS_column_covers`), and `normS D η hη`
  its normalisation by `η`. Its oracles are those of the padded data (`prims_normS`), so the padded
  calls are implemented from the supplied ones exactly as before;
* `UJPrep UJg slot en`: the promise of a supplied boundary circuit `U_J` (a list of elementary gates on
  the ancilla and system wires): on the clean ancillas it prepares the boundary state of the `s`
  slots, `U_J ι₀ = J ι₀`. The Hadamard circuit meets it when `s` is a power of two
  (`hadUJ_prep`); for other `s` it is the uniform-range preparation over the `s` slot words, which is
  supplied, not constructed, here;
* `boundary_lift_of`, `R1bin_boundary_of`, `R1bin_endpoint_of`: the boundary and endpoint promises of
  the clock for any supplied `U_J` with `UJPrep`, for any sparse data;
* `sparse_gate_total_s`, `sparse_gate_total_signed_s`: the accounting of `sparse_gate_total` with the
  original `s`: `α = η √s / γ` (`clockS`), `Q = width s γ = ⌈max{1, γ √s}⌉`, the degree `d = dgS` of
  `width s γ`, the reuse register `rgS`, `C_J = |U_J|` and `G₀ = synGS`, for a supplied private
  circuit with the promise `PrivOKS` (the private Cayley operation of `normS`);
* `privOpS`, `privCircS`, `privCircS_privOK`, `privCircS_spec`, `exists_arithS`: the constructed private
  circuit for `normS` (the decoder rescaled by `γ √s`), with its promise derived as in `Native`;
* `sparse_gate_original` (the headline): from the synthesis hypothesis, the arithmetic interface of the
  decoder at `γ √s / η` and a supplied boundary circuit with `UJPrep`, one circuit fixed before the
  instance, with exactly `6 d` private calls at the degree `d` of the original `s`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.SparseGateAccounting

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim GateNative GateSynth
  GateSelective GateBinary GateSchedule GeneralSparseAccess CayleyClockInterface GeneralDecoder
open GateSynthTrials (AdjClosed)
open ManuscriptConformance (cleanAlong)
open NativeSparseBlockEncoding (Query Data)
open scoped InnerProduct

/-! ### The first `s` slots -/

section Restrict

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s' : ℕ}

/-- **The first `s` slots of sparse data with `s'` slots**, when they cover every nonzero entry: the
same entries, table, decoder and oracles, the slots, locators and validity of the first `s` slots. -/
def restrictSlots (D : Data X n Z s') (s : ℕ) (hs : 0 < s) (hss : s ≤ s')
    (hrow : ∀ x i j, D.matrix x i j ≠ 0 → ∃ m : Fin s, D.rowloc x i (Fin.castLE hss m) = j)
    (hcol : ∀ x i j, D.matrix x i j ≠ 0 → ∃ m : Fin s, D.colloc x j (Fin.castLE hss m) = i) :
    Data X n Z s where
  slot := (Fin.castLEEmb hss).trans D.slot
  slots_pos := hs
  scale := D.scale
  scale_pos := D.scale_pos
  matrix := D.matrix
  table := D.table
  decode := D.decode
  decode_bound := D.decode_bound
  decoded := D.decoded
  rowloc x i m := D.rowloc x i (Fin.castLE hss m)
  colloc x j m := D.colloc x j (Fin.castLE hss m)
  row_injective x i := (D.row_injective x i).comp (Fin.castLE_injective hss)
  column_injective x j := (D.column_injective x j).comp (Fin.castLE_injective hss)
  row_covers x i j h := by
    obtain ⟨m, hm⟩ := hrow x i j h
    exact Finset.mem_image.mpr ⟨m, Finset.mem_univ _, hm⟩
  column_covers x i j h := by
    obtain ⟨m, hm⟩ := hcol x i j h
    exact Finset.mem_image.mpr ⟨m, Finset.mem_univ _, hm⟩
  rowOracle := D.rowOracle
  columnOracle := D.columnOracle
  row_unitary := D.row_unitary
  column_unitary := D.column_unitary
  row_valid x i m := D.row_valid x i (Fin.castLE hss m)
  column_valid x j m := D.column_valid x j (Fin.castLE hss m)

end Restrict

/-! ### The padded data on the original slots -/

section PadS

variable {X : Type*} {N s k b : ℕ}

/-- The slots of the original lists cover every nonzero entry of the padded data, along rows. -/
theorem padDataS_row_covers (D : QData X N s k b) (x : X) (y y' : Cfg (Fin (k + 1)))
    (h : D.padDataE.matrix x y y' ≠ 0) :
    ∃ m : Fin s, D.padDataE.rowloc x y (Fin.castLE (le_sP s) m) = y' := by
  change D.pdecode (y, y') (D.ptableE x (y, y')) ≠ 0 at h
  rw [QData.pdecode_ptableE] at h
  split_ifs at h with hv
  · obtain ⟨a, ha⟩ := D.row_covers x _ _ h
    refine ⟨a, ?_⟩
    change QData.plist (D.rowloc x) y _ = y'
    unfold QData.plist
    rw [dif_pos ⟨hv.1, a.isLt⟩]
    have : (⟨(Fin.castLE (le_sP s) a).val, a.isLt⟩ : Fin s) = a := rfl
    rw [this, ha]
    exact idx_binW_pdec hv.2
  · exact absurd rfl h

/-- The slots of the original lists cover every nonzero entry of the padded data, along columns. -/
theorem padDataS_column_covers (D : QData X N s k b) (x : X) (y y' : Cfg (Fin (k + 1)))
    (h : D.padDataE.matrix x y y' ≠ 0) :
    ∃ m : Fin s, D.padDataE.colloc x y' (Fin.castLE (le_sP s) m) = y := by
  change D.pdecode (y, y') (D.ptableE x (y, y')) ≠ 0 at h
  rw [QData.pdecode_ptableE] at h
  split_ifs at h with hv
  · obtain ⟨a, ha⟩ := D.column_covers x _ _ h
    refine ⟨a, ?_⟩
    change QData.plist (D.colloc x) y' _ = y
    unfold QData.plist
    rw [dif_pos ⟨hv.2, a.isLt⟩]
    have : (⟨(Fin.castLE (le_sP s) a).val, a.isLt⟩ : Fin s) = a := rfl
    rw [this, ha]
    exact idx_binW_pdec hv.1
  · exact absurd rfl h

/-- **The padded data with the validity decoder on the original `s` slots.** -/
abbrev padDataS (D : QData X N s k b) : Data X (Cfg (Fin (k + 1))) (Cfg (VW b)) s :=
  restrictSlots D.padDataE s D.slots_pos (le_sP s) (padDataS_row_covers D)
    (fun x y y' h => padDataS_column_covers D x y y' h)

/-- **The normalised padded data on the original slots.** -/
abbrev normS (D : QData X N s k b) (η : ℝ) (hη : 0 < η) :
    Data X (Cfg (Fin (k + 1))) (Cfg (VW b)) s :=
  NativeSparseRescaling.normalize (padDataS D) η hη

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The oracles of the data on the original slots are those of the padded data. -/
theorem prims_normS (D : QData X N s k b) {η : ℝ} (hη : 0 < η) (x : X) :
    GateBinary.prims (R := R) (normS D η hη) (Equiv.refl _) x =
      GateBinary.prims (R := R) D.padDataE (Equiv.refl _) x :=
  rfl

/-- The instance promises pass to the normalised data on the original slots. -/
theorem normS_energies (D : QData X N s k b) {η : ℝ} (hη : 0 < η) {x : X}
    (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ((normS D η hη).matrix x).IsHermitian ∧
      (∀ i, ∑ j, ‖(normS D η hη).matrix x i j‖ ^ 2 ≤ 1) ∧
      (∀ j, ∑ i, ‖(normS D η hη).matrix x i j‖ ^ 2 ≤ 1) :=
  normPad_energies D hη hH hrow hcol

/-- The first original slot is the all-zero index word. -/
theorem normS_zero_slot (D : QData X N s k b) {η : ℝ} (hη : 0 < η) :
    ∃ m, (normS D η hη).slot m = zIdx (Equiv.refl (Cfg (Fin (k + 1)))) := by
  refine ⟨⟨0, D.slots_pos⟩, ?_⟩
  funext j
  show idx false (binW k 0) j = false
  simp [idx, binW]

end PadS

/-! ### The clock promises with a supplied boundary circuit -/

section Boundary

variable {X n : Type*} [Fintype n] [DecidableEq n] {k b s : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The promise of a supplied boundary circuit** `U_J`: on the clean ancillas it prepares the
boundary state of the slots, `U_J ι₀ = J ι₀` (`GateBinary.bdryP`: the oriented uniform superposition
of the slot words). -/
abbrev UJPrep (UJg : List (Gate (Fin (k + 1) ⊕ Fin k))) (slot : Fin s ↪ n)
    (en : Cfg (Fin k) ≃ n) : Prop :=
  UJop (R := R) UJg ∘L iota0 (a := k + 1) (P := Reg (Fin k) R) =
    unconj (qlift (R := R) (phiPR en) (bdryP slot en)) ∘L iota0

/-- **The Hadamard circuit meets the promise when `s` is a power of two** and the slots are the low
words (`GateBinary.hadUJ_iota0`). -/
theorem hadUJ_prep (σ : ℕ) (hσ : σ ≤ k) (en : Cfg (Fin k) ≃ n) (slot : Fin s ↪ n)
    (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u)) :
    UJPrep (R := R) (hadUJ k σ hσ) slot en :=
  hadUJ_iota0 σ hσ en slot hs hrange

/-- **Compression by a supplied boundary circuit**: `(U_J ι₀)† A (U_J ι₀) = J† A J` for every
operator `A` of the oriented space, lifted. -/
theorem boundary_lift_of {UJg : List (Gate (Fin (k + 1) ⊕ Fin k))} (en : Cfg (Fin k) ≃ n)
    (slot : Fin s ↪ n) (hUJ : UJPrep (R := R) UJg slot en)
    (A : SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n) :
    (UJop (R := R) UJg ∘L iota0 (a := k + 1) (P := Reg (Fin k) R))† ∘L
        unconj (qlift (R := R) (phiPR en) A) ∘L
          (UJop (R := R) UJg ∘L iota0 (a := k + 1) (P := Reg (Fin k) R)) =
      qlift en ((FixedLocatorConjugation.fixedBoundary slot)† ∘L A ∘L
        FixedLocatorConjugation.fixedBoundary slot) := by
  have hadj : (UJop (R := R) UJg ∘L iota0 (a := k + 1) (P := Reg (Fin k) R))† =
      (iota0 (a := k + 1) (P := Reg (Fin k) R))† ∘L
        unconj (qlift (R := R) (phiPR en) ((bdryP slot en)†)) := by
    rw [hUJ, adjoint_comp, ← unconj_adjoint, ← qlift_adjoint]
  rw [hadj, hUJ, comp_assoc, unconj_qlift_sandwich, iota0_bdryP_compress]

/-- **The boundary promise with a supplied boundary circuit**:
`(U_J ι₀)† R₁ (U_J ι₀) = (1 + i H)/2`, for sparse data with any number of slots. -/
theorem R1bin_boundary_of (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n)
    {UJg : List (Gate (Fin (k + 1) ⊕ Fin k))} (hUJ : UJPrep (R := R) UJg D.slot en) (x : X)
    (γ : ℝ) :
    (UJop (R := R) UJg ∘L iota0 (a := k + 1) (P := Reg (Fin k) R))† ∘L
        R1bin (R := R) D en x γ ∘L
          (UJop (R := R) UJg ∘L iota0 (a := k + 1) (P := Reg (Fin k) R)) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • Hbin (R := R) D en x γ) := by
  rw [R1bin, boundary_lift_of en D.slot hUJ,
    show FixedLocatorConjugation.fixedBoundary D.slot = FixedNativeCayleySimulation.boundary D
      from rfl,
    ImprovedCayleyMoments.resolventAtOne_compression _ _
      (FixedNativeCayleySimulation.boundary_isometry D), qlift_smul, qlift_add, qlift_one,
    qlift_smul]
  rfl

/-- **The endpoint promise with a supplied boundary circuit**: `‖R₁ U_J ι₀‖ ≤ √((1 + γ²)/4)`. -/
theorem R1bin_endpoint_of (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n)
    {UJg : List (Gate (Fin (k + 1) ⊕ Fin k))} (hUJ : UJPrep (R := R) UJg D.slot en) (x : X)
    (γ : ℝ) (hγ : 0 ≤ γ) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) :
    ‖R1bin (R := R) D en x γ ∘L
        (UJop (R := R) UJg ∘L iota0 (a := k + 1) (P := Reg (Fin k) R))‖ ≤ endpoint γ := by
  have hJ := FixedNativeCayleySimulation.boundary_isometry D
  have hKJ := FixedNativeCayleySimulation.generator_boundary_norm_le D x hrow hcol
  have hq := endpoint_norm _ _ γ (FixedNativeCayleySimulation.generator_self_adjoint D x) hJ hγ
    hKJ
  have hgram : (R1bin (R := R) D en x γ ∘L
      (UJop (R := R) UJg ∘L iota0 (a := k + 1) (P := Reg (Fin k) R)))† ∘L
      (R1bin (R := R) D en x γ ∘L
        (UJop (R := R) UJg ∘L iota0 (a := k + 1) (P := Reg (Fin k) R))) =
      qlift en ((ImprovedCayleyMoments.resolventAtOne
        (scaled (FixedNativeCayleySimulation.generator D x) γ) ∘L
          FixedNativeCayleySimulation.boundary D)† ∘L
        (ImprovedCayleyMoments.resolventAtOne
          (scaled (FixedNativeCayleySimulation.generator D x) γ) ∘L
          FixedNativeCayleySimulation.boundary D)) := by
    rw [adjoint_comp_comp, adjoint_comp_comp, R1bin, ← elift_adjoint, ← elift_comp,
      boundary_lift_of en D.slot hUJ]
    rfl
  have h1 := norm_adjoint_comp_self (R1bin (R := R) D en x γ ∘L
    (UJop (R := R) UJg ∘L iota0 (a := k + 1) (P := Reg (Fin k) R)))
  rw [hgram] at h1
  have h2 := norm_qlift_le (R := R) en ((ImprovedCayleyMoments.resolventAtOne
    (scaled (FixedNativeCayleySimulation.generator D x) γ) ∘L
      FixedNativeCayleySimulation.boundary D)† ∘L
    (ImprovedCayleyMoments.resolventAtOne
      (scaled (FixedNativeCayleySimulation.generator D x) γ) ∘L
      FixedNativeCayleySimulation.boundary D))
  rw [norm_adjoint_comp_self, h1] at h2
  have he : 0 ≤ endpoint γ := Real.sqrt_nonneg _
  exact (mul_self_le_mul_self_iff (norm_nonneg _) he).2
    (h2.trans (mul_le_mul hq hq (norm_nonneg _) he))

end Boundary

/-! ### The accounting on the schedule of the original sparsity -/

section AccountingS

variable {X : Type*} {N s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {Z : Type*} [Fintype Z] [DecidableEq Z] {bT bP A : ℕ}
variable {Xs : Type*} [Fintype Xs] [DecidableEq Xs] {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- **The time `αT` of the schedule with the original sparsity**: `η t √s / γ`. -/
abbrev clockS (s : ℕ) (η t γ : ℝ) : ℝ := time (s : ℝ) (η * t) γ

/-- The clock of `|t|` is the absolute value of the clock of `t`. -/
theorem abs_clockS (s : ℕ) {η γ : ℝ} (hη : 0 < η) (hγ : 0 < γ) (t : ℝ) :
    |clockS s η t γ| = clockS s η |t| γ := by
  simp only [clockS, time, abs_div, abs_mul, abs_of_pos hη, abs_of_pos hγ,
    abs_of_nonneg (Real.sqrt_nonneg _)]

/-- The filter degree `d` of the schedule with the original sparsity. -/
abbrev dgS (s : ℕ) (γ τ ε : ℝ) : ℕ := degreeMs (width (s : ℝ) γ) (τ * moment γ) ε

/-- The reuse register `r_reuse = ⌈log₂(2d + 2)⌉` of the schedule with the original sparsity. -/
abbrev rgS (s : ℕ) (γ τ ε : ℝ) : ℕ := rMs (width (s : ℝ) γ) τ (moment γ) ε

/-- **The gate occurrences to synthesise**: `G₀ = 200 (d+1)(a+m+r+1) + 84 d C_J` with `a = k + 2`
and `C_J` the gates of the supplied boundary circuit. -/
abbrev synGS (k s : ℕ) (γ τ ε : ℝ) (CJ : ℕ) : ℕ :=
  200 * (dgS s γ τ ε + 1) * (k + 1 + 1 + slotMs τ ε + rgS s γ τ ε + 1) + 84 * dgS s γ τ ε * CJ

/-- The degree of the schedule with the original sparsity is positive. -/
theorem dgS_pos (s : ℕ) (γ : ℝ) {τ ε : ℝ} (hτ : 0 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ dgS s γ τ ε := by
  have hQ := width_ge_one (s : ℝ) γ
  have hm : 0 ≤ moment γ := by unfold moment; positivity
  have hk := (depthMs_admissible _ (τ * moment γ) ε hQ (mul_nonneg hτ hm) hε hε1).pos
  have hL := (SharpFilterSchedule.length_sub_one_bounds _ hQ).1
  have hL1 : 1 ≤ SharpFilterSchedule.length (width (s : ℝ) γ) - 1 := by
    have : (1 : ℝ) ≤ ((SharpFilterSchedule.length (width (s : ℝ) γ) - 1 : ℕ) : ℝ) :=
      hQ.trans hL
    exact_mod_cast this
  exact Nat.mul_pos hk hL1

/-- **The promise of a supplied private circuit for the original slots**: on clean work wires,
within `ξ` of the enable-controlled private Cayley operation of `normS`. -/
abbrev PrivOKS (D : QData X N s k b) (η : ℝ) (hη : 0 < η) (x : X) (γ ξ : ℝ)
    (pc : PrivC k b Z bT bP A) : Prop :=
  ApproxOn CleanP (nrun (D.prims (R := R) x) pc)
    (ctrlIdeal (selOp (fun _ : Cfg Empty => Dbin (R := R) (normS D η hη) (Equiv.refl _) x γ))) ξ

/-- The selective finite-set circuit with the original sparsity and a supplied boundary circuit. -/
abbrev finCS (hS : Synthesis 𝒢 Xs L) (s : ℕ) (UJg : List (Gate (Fin (k + 1 + 1) ⊕ Fin (k + 1))))
    (γ τ ε : ℝ) (pc : PrivC k b Z bT bP A) :=
  selSimMs hS (k + 1 + 1) τ (width (s : ℝ) γ) (moment γ) ε UJg pc

/-- The native circuit before synthesis with the original sparsity. -/
abbrev preCS (s : ℕ) (UJg : List (Gate (Fin (k + 1 + 1) ⊕ Fin (k + 1)))) (γ τ ε : ℝ)
    (pc : PrivC k b Z bT bP A) :=
  simPMs (k + 1 + 1) τ (width (s : ℝ) γ) (moment γ) ε UJg pc

/-- The selective finite-set circuit for a signed clock with the original sparsity. -/
abbrev finCSignedS (hS : Synthesis 𝒢 Xs L) (s : ℕ)
    (UJg : List (Gate (Fin (k + 1 + 1) ⊕ Fin (k + 1)))) (γ t ε : ℝ) (pc : PrivC k b Z bT bP A) :=
  selSimMsSigned hS (k + 1 + 1) t (width (s : ℝ) γ) (moment γ) ε UJg pc

/-- **The exponent of the compressed generator is the exponent of the padded matrix**, with the
original sparsity in the clock. -/
theorem evolutionS_eq (D : QData X N s k b) {η : ℝ} (hη : 0 < η) (x : X)
    (hH : ((normS D η hη).matrix x).IsHermitian) (t : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    (-Complex.I * ((clockS s η t γ : ℝ) : ℂ)) •
        Hbin (R := R) (normS D η hη) (Equiv.refl _) x γ =
      (-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
        (SparseStateOverlap.matrixOperator (D.padDataE.matrix x)) := by
  rw [clockS, Hbin_exponent _ _ x hH (η * t) γ hγ.ne',
    NativeSparseRescaling.matrixOperator_normalize, qlift_smul, smul_smul]
  congr 1
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  push_cast
  field_simp

set_option maxRecDepth 8192 in
/-- **Equations `hs:eq:gate-Gzero` and `hs:eq:gate-total` with the original sparsity `s`** for
sparse access of general size. As `sparse_gate_total`, with a supplied boundary circuit `U_J` of
gates with at most three controls preparing the boundary state of the `s` original slots
(`UJPrep`) and a supplied private circuit with the promise `PrivOKS`: the schedule has
`α = η √s / γ` (`clockS`), `Q = width s γ`, `d = dgS`, `r = rgS`, `C_J = |U_J|` and `G₀ = synGS`. -/
theorem sparse_gate_total_s (hS : Synthesis 𝒢 Xs L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (D : QData X N s k b) {η : ℝ} (hη : 0 < η)
    (UJg : List (Gate (Fin (k + 1 + 1) ⊕ Fin (k + 1)))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (hUJ : UJPrep (R := R) UJg (normS D η hη).slot (Equiv.refl _)) (pc : PrivC k b Z bT bP A)
    (hpcV : ∀ i ∈ pc, i.Valid) (hpcG : ∀ g, NInstr.gate g ∈ pc → GateOf 𝒢 g) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (γ T τ ε : ℝ) (hτ : τ = clockS s η T γ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hT : 0 ≤ T) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hξε : 24 * (dgS s γ τ ε : ℝ) * ξ ≤ ε) (x : X) (hH : (D.matrix x).IsHermitian)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (hpc : PrivOKS (R := R) D η hη x γ ξ pc) :
    (∀ i ∈ finCS hS s UJg γ τ ε pc, i.Valid) ∧
    (∀ g, NInstr.gate g ∈ finCS hS s UJg γ τ ε pc → GateOf 𝒢 g) ∧
    (∀ p : Query → Bool, nCallsN p (finCS hS s UJg γ τ ε pc) =
      6 * dgS s γ τ ε * nCallsN p pc) ∧
    nSynN 𝒢 (preCS s UJg γ τ ε pc) ≤ synGS k s γ τ ε UJg.length ∧
    (nGatesN (finCS hS s UJg γ τ ε pc) : ℝ) ≤
      6 * (dgS s γ τ ε : ℝ) * nGatesN pc + (synGS k s γ τ ε UJg.length : ℝ) *
        (c₁ * Real.log (((synGS k s γ τ ε UJg.length : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
    Fintype.card (HW (SimWireMs (k + 1 + 1) (width (s : ℝ) γ) τ (moment γ) ε) (Fin (k + 1))
        Empty Z bT bP A ⊕ Xs) =
      k + 1 + (2 * (k + 1 + 1) + 3 * slotMs τ ε + 6 * rgS s γ τ ε + 3) +
        (Fintype.card Z + bT + bP + A + 3) + Fintype.card Xs ∧
    ‖nrun (D.prims (R := R) x) (finCS hS s UJg γ τ ε pc) ∘L
        (cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          NormedSpace.exp ((-Complex.I * (T : ℂ)) • qlift (R := R) (Equiv.refl _)
            (SparseStateOverlap.matrixOperator (D.padDataE.matrix x)))‖ ≤ ε ∧
    ‖nrun (D.prims (R := R) x) (finCS hS s UJg γ τ ε pc) ∘L
        ((cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) -
        ((cleanEmb ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) ∘L
          NormedSpace.exp ((-Complex.I * (T : ℂ)) • qlift (R := R) (Equiv.refl _)
            (SparseStateOverlap.matrixOperator (D.padMat x)))‖ ≤ ε ∧
    dgS s γ τ ε = depthMs (width (s : ℝ) γ) (τ * moment γ) ε *
      (SharpFilterSchedule.length (width (s : ℝ) γ) - 1) ∧
    (dgS s γ τ ε : ℝ) ≤ 128 * (τ * moment γ) +
      32 * width (s : ℝ) γ * (Real.logb 2 (4096 / ε) + 1) ∧
    meshMs τ ε ≤ 2 ^ slotMs τ ε ∧ (∀ j : ℕ, meshMs τ ε ≤ 2 ^ j → slotMs τ ε ≤ j) ∧
    rgS s γ τ ε = Nat.clog 2 (2 * dgS s γ τ ε + 2) := by
  obtain ⟨hH', hrow', hcol'⟩ := normS_energies D hη hH hrow hcol
  have hτ0 : 0 ≤ τ := by
    rw [hτ]
    exact div_nonneg (mul_nonneg (mul_nonneg hη.le hT) (Real.sqrt_nonneg _)) hγ.le
  have he : (-Complex.I * (τ : ℂ)) • Hbin (R := R) (normS D η hη) (Equiv.refl _) x γ =
      (-Complex.I * (T : ℂ)) • qlift (R := R) (Equiv.refl _)
        (SparseStateOverlap.matrixOperator (D.padDataE.matrix x)) := by
    rw [hτ]
    exact evolutionS_eq D hη x hH' T hγ
  obtain ⟨hv, hk, hc, hsyn, hg, -, herr, hd, hdle, hm, hl⟩ := sel_simulation_ms hS hadj hc₀ hc₁
    hL (k + 1 + 1) (D.prims (R := R) x) (D.prims_isUnitary x) UJg hUJg pc hpcV hpcG
    ξ hξ (Dbin (R := R) (normS D η hη) (Equiv.refl _) x γ)
    (R1bin (R := R) (normS D η hη) (Equiv.refl _) x γ)
    (Hbin (R := R) (normS D η hη) (Equiv.refl _) x γ)
    (Dbin_isUnitary _ _ x γ) hpc τ (width (s : ℝ) γ) (endpoint γ) (moment γ)
    ε hτ0 (width_ge_one _ _) (one_sub_Dbin_R1bin _ _ x γ) (R1bin_one_sub_Dbin _ _ x γ)
    (norm_R1bin_le _ _ x γ hγ.le hrow')
    (R1bin_boundary_of _ _ hUJ x γ)
    (Hbin_self _ _ x γ) (norm_Hbin_le _ _ x γ hγ.le hγ1 hrow' hcol')
    (R1bin_endpoint_of _ _ hUJ x γ hγ.le hrow' hcol')
    (endpoint_sq γ).le (moment_le_width _ γ hγ.le hγ1) hε hε1 hξε
  rw [he] at herr
  refine ⟨hv, hk, hc, hsyn, hg, ?_, ?_, ?_, hd, hdle, hm, hl, rfl⟩
  · rw [Fintype.card_sum, card_HW, card_wire]
    simp only [Fintype.card_empty, Fintype.card_fin, simKK]
    ring
  · convert herr using 4
  · convert error_low herr using 2
    rw [sub_comp]
    simp only [comp_assoc]
    rw [ManuscriptConformance.exp_padForm_comp D (padForm_padDataE D) x T]

end AccountingS

section SignedS

variable {X : Type*} {N s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {Z : Type*} [Fintype Z] [DecidableEq Z] {bT bP A : ℕ}
variable {Xs : Type*} [Fintype Xs] [DecidableEq Xs] {𝒢 : Set Kind} {L : ℝ → ℕ}

set_option maxRecDepth 8192 in
/-- **Every real time with the original sparsity** (`sparse_gate_total_s`): for the signed clock
`t' = η t √s / γ` the circuit of `|t'|`, or its literal reverse-adjoint for `t < 0`, has the same
validity, gate set, calls, gates and qubit count, and its full output is within `ε` of
`exp(-itH)`. -/
theorem sparse_gate_total_signed_s (hS : Synthesis 𝒢 Xs L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (D : QData X N s k b) {η : ℝ} (hη : 0 < η)
    (UJg : List (Gate (Fin (k + 1 + 1) ⊕ Fin (k + 1)))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (hUJ : UJPrep (R := R) UJg (normS D η hη).slot (Equiv.refl _)) (pc : PrivC k b Z bT bP A)
    (hpcV : ∀ i ∈ pc, i.Valid) (hpcG : ∀ g, NInstr.gate g ∈ pc → GateOf 𝒢 g) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (γ t t' ε : ℝ) (ht' : t' = clockS s η t γ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hξε : 24 * (dgS s γ |t'| ε : ℝ) * ξ ≤ ε) (x : X)
    (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (hpc : PrivOKS (R := R) D η hη x γ ξ pc) :
    (∀ i ∈ finCSignedS hS s UJg γ t' ε pc, i.Valid) ∧
    (∀ g, NInstr.gate g ∈ finCSignedS hS s UJg γ t' ε pc → GateOf 𝒢 g) ∧
    (∀ p : Query → Bool, nCallsN p (finCSignedS hS s UJg γ t' ε pc) =
      6 * dgS s γ |t'| ε * nCallsN p pc) ∧
    (nGatesN (finCSignedS hS s UJg γ t' ε pc) : ℝ) ≤
      6 * (dgS s γ |t'| ε : ℝ) * nGatesN pc + (synGS k s γ |t'| ε UJg.length : ℝ) *
        (c₁ * Real.log (((synGS k s γ |t'| ε UJg.length : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
    Fintype.card (HW (SimWireMs (k + 1 + 1) (width (s : ℝ) γ) |t'| (moment γ) ε)
        (Fin (k + 1)) Empty Z bT bP A ⊕ Xs) =
      k + 1 + (2 * (k + 1 + 1) + 3 * slotMs |t'| ε + 6 * rgS s γ |t'| ε + 3) +
        (Fintype.card Z + bT + bP + A + 3) + Fintype.card Xs ∧
    ‖nrun (D.prims (R := R) x) (finCSignedS hS s UJg γ t' ε pc) ∘L
        (cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
            (SparseStateOverlap.matrixOperator (D.padDataE.matrix x)))‖ ≤ ε ∧
    ‖nrun (D.prims (R := R) x) (finCSignedS hS s UJg γ t' ε pc) ∘L
        ((cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) -
        ((cleanEmb ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
            (SparseStateOverlap.matrixOperator (D.padMat x)))‖ ≤ ε := by
  subst ht'
  obtain ⟨hH', hrow', hcol'⟩ := normS_energies D hη hH hrow hcol
  obtain ⟨hv, hk, hc, hg, herr⟩ := sel_simulation_ms_signed hS hadj hc₀ hc₁
    hL (k + 1 + 1) (D.prims (R := R) x) (D.prims_isUnitary x) UJg hUJg pc hpcV hpcG
    ξ hξ (Dbin (R := R) (normS D η hη) (Equiv.refl _) x γ)
    (R1bin (R := R) (normS D η hη) (Equiv.refl _) x γ)
    (Hbin (R := R) (normS D η hη) (Equiv.refl _) x γ)
    (Dbin_isUnitary _ _ x γ) hpc (clockS s η t γ) (width (s : ℝ) γ) (endpoint γ) (moment γ)
    ε (width_ge_one _ _) (one_sub_Dbin_R1bin _ _ x γ) (R1bin_one_sub_Dbin _ _ x γ)
    (norm_R1bin_le _ _ x γ hγ.le hrow')
    (R1bin_boundary_of _ _ hUJ x γ)
    (Hbin_self _ _ x γ) (norm_Hbin_le _ _ x γ hγ.le hγ1 hrow' hcol')
    (R1bin_endpoint_of _ _ hUJ x γ hγ.le hrow' hcol')
    (endpoint_sq γ).le (moment_le_width _ γ hγ.le hγ1) hε hε1 hξε
  rw [evolutionS_eq D hη x hH' t hγ] at herr
  refine ⟨hv, hk, hc, hg, ?_, herr, ?_⟩
  · rw [Fintype.card_sum, card_HW, card_wire]
    simp only [Fintype.card_empty, Fintype.card_fin, simKK]
    ring
  · convert error_low herr using 2
    rw [sub_comp]
    simp only [comp_assoc]
    rw [ManuscriptConformance.exp_padForm_comp D (padForm_padDataE D) x t]

end SignedS

/-! ### The constructed private circuit for the original slots -/

section NativeS

variable {X : Type*} {N s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {Xs : Type*} [Fintype Xs] [DecidableEq Xs] {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- **The native private operation for the original slots on the supplied oracles**: as `privOp`,
for `normS` with the decoder `γ √s decode`. -/
abbrev privOpS (D : QData X N s k b) (η : ℝ) (hη : 0 < η) (γ : ℝ) :
    NativeOp Empty (PR (k + 1)) (SZ (k + 1) b ⊕ AW k b) (PY k b) Query :=
  GeneralSparseODE.substOp (sparseOpD (normS D η hη) (Equiv.refl _) (γ * Real.sqrt s))
    (implPE N s)

/-- **The constructed controlled private circuit for the original slots.** -/
abbrev privCircS (hS : Synthesis 𝒢 Xs L) (δ : ℝ) (D : QData X N s k b) (η : ℝ) (hη : 0 < η)
    (γ : ℝ) (ar : Arith (BW (k + 1) b)) :
    PrivC k b ((SZ (k + 1) b ⊕ AW k b) ⊕ Xs) ar.bT ar.bP ar.A :=
  privSel hS δ (privOpS D η hη γ) (GeneralSparseODE.liftA (Xa := AW k b) ar)

/-- The gates of the native implementation for the original slots before the selective
compilation. -/
abbrev privGS (D : QData X N s k b) (η : ℝ) (hη : 0 < η) (γ : ℝ) (ar : Arith (BW (k + 1) b)) :
    ℕ :=
  2 * nGatesN (privOpS D η hη γ).V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)

/-- The decoder for the original slots at the rescaling `κ` is the decoder of the padded data at
`κ / η`. -/
theorem normS_dec (D : QData X N s k b) {η : ℝ} (hη : 0 < η) (κ : ℝ) :
    (sparseOpD (normS D η hη) (Equiv.refl _) κ).dec =
      fun y => ((κ / η : ℝ) : ℂ) * D.padDataE.decode (phiE (Equiv.refl _) (eword y)) (vword y) := by
  funext y
  show (κ : ℂ) * (((η⁻¹ : ℝ) : ℂ) * D.padDataE.decode _ _) = _
  push_cast
  ring

theorem privOpS_public (D : QData X N s k b) {η : ℝ} (hη : 0 < η) (γ : ℝ) :
    (privOpS D η hη γ).Public :=
  GeneralSparseODE.substOp_public (sparseOpD_public _ _ _) (valid_implPE N s)

/-- The calls of the compute circuit for the original slots: at most `3` per call of the compute
circuit of the padded data, of the same kind. -/
theorem privOpS_calls (D : QData X N s k b) {η : ℝ} (hη : 0 < η) (γ : ℝ) (p : Query → Bool) :
    nCallsN p (privOpS D η hη γ).V ≤
      3 * (2 * (if p Query.rowLocation then 1 else 0) +
        2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0)) := by
  have h := GeneralSparseODE.nCallsN_substOp_le
    (sparseOpD (normS D η hη) (Equiv.refl _) (γ * Real.sqrt s))
    (kindOK_implPE (k := k) (b := b) N s) p
  rw [sparseOpD_V, computeV_nCalls] at h
  exact h

/-- The gates of the compute circuit for the original slots. -/
theorem privOpS_gates (D : QData X N s k b) {η : ℝ} (hη : 0 < η) (γ : ℝ) :
    nGatesN (privOpS D η hη γ).V ≤ 28 * (k + 1) + implG k b * 5 := by
  have h := GeneralSparseODE.nGatesN_substOp_le
    (sparseOpD (normS D η hη) (Equiv.refl _) (γ * Real.sqrt s)) (implPE N s) (implG k b)
    (nGatesN_implPE_le N s)
  rw [sparseOpD_V, computeV_nGates, computeV_nCalls] at h
  simpa using h

/-- **The promise of the constructed circuit for the original slots** (`PrivOKS`), derived. -/
theorem privCircS_privOK (hS : Synthesis 𝒢 Xs L) {δ : ℝ} (hδ : 0 < δ) (D : QData X N s k b)
    {η : ℝ} (hη : 0 < η) (γ : ℝ) (ar : Arith (BW (k + 1) b)) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr (oPR (k + 1))))
      (sparseOpD (normS D η hη) (Equiv.refl _) (γ * Real.sqrt s)).dec ζ) (x : X) :
    PrivOKS (R := R) D η hη x γ (δ + 4 * ζ) (privCircS hS δ D η hη γ ar) := by
  have har' := GeneralSparseODE.arithOK_liftA (Xa := AW k b) ar (oPR (k + 1)) _ ζ har
  obtain ⟨-, -, -, -, happrox⟩ := privSel_spec (R := R) hS hδ (privOpS D η hη γ)
    (privOpS_public D hη γ) (GeneralSparseODE.liftA (Xa := AW k b) ar) hζ har'
  obtain ⟨k0, hk0⟩ := normS_zero_slot D hη
  have hN := sparse_nativeOKD (R := R) (normS D η hη) (Equiv.refl _) k0 hk0 x γ
  have hN' := GeneralSparseODE.nativeOK_substOp (D.prims (R := R) x)
    (GateBinary.prims (R := R) D.padDataE (Equiv.refl _) x) (D.prims_isUnitary x)
    (GateBinary.prims_isUnitary _ _ x) (implOKE (R := R) (N := N) (s := s) D x)
    (sparseOpD (normS D η hη) (Equiv.refl _) (γ * Real.sqrt s)) (sparseOpD_public _ _ _)
    _ hN
  exact happrox (D.prims (R := R) x) (D.prims_isUnitary x) _ hN'

/-- **The constructed circuit for the original slots**: as `privCirc_spec`. -/
theorem privCircS_spec (hS : Synthesis 𝒢 Xs L) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (D : QData X N s k b) {η : ℝ} (hη : 0 < η) (γ : ℝ)
    (ar : Arith (BW (k + 1) b)) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr (oPR (k + 1))))
      (sparseOpD (normS D η hη) (Equiv.refl _) (γ * Real.sqrt s)).dec ζ) :
    (∀ i ∈ privCircS hS δ D η hη γ ar, i.Valid) ∧
    (∀ g, NInstr.gate g ∈ privCircS hS δ D η hη γ ar → GateOf 𝒢 g) ∧
    (∀ p : Query → Bool, nCallsN p (privCircS hS δ D η hη γ ar) =
      2 * nCallsN p (privOpS D η hη γ).V) ∧
    (∀ p : Query → Bool, nCallsN p (privOpS D η hη γ).V ≤
      3 * (2 * (if p Query.rowLocation then 1 else 0) +
        2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0))) ∧
    nGatesN (privOpS D η hη γ).V ≤ 28 * (k + 1) + implG k b * 5 ∧
    (nGatesN (privCircS hS δ D η hη γ ar) : ℝ) ≤
      (privGS D η hη γ ar : ℝ) *
        (1 + c₁ * Real.log (((privGS D η hη γ ar : ℝ) + 1) / δ) + c₀) ∧
    ∀ x : X, PrivOKS (R := R) D η hη x γ (δ + 4 * ζ) (privCircS hS δ D η hη γ ar) := by
  have har' := GeneralSparseODE.arithOK_liftA (Xa := AW k b) ar (oPR (k + 1)) _ ζ har
  obtain ⟨hv, hg, hgates, hc, -⟩ := privSel_spec (R := R) hS hδ (privOpS D η hη γ)
    (privOpS_public D hη γ) (GeneralSparseODE.liftA (Xa := AW k b) ar) hζ har'
  have hsum := nKeepN_add_nSynN 𝒢
    (privMacro (privOpS D η hη γ) (GeneralSparseODE.liftA (Xa := AW k b) ar))
  rw [privMacro_nGates, GeneralSparseODE.liftA_circ_length] at hsum
  exact ⟨hv, hg, hc, privOpS_calls D hη γ, privOpS_gates D hη γ,
    selGates_le hc₀ hc₁ hL hδ hδ1 hsum hgates,
    fun x => privCircS_privOK hS hδ D hη γ ar hζ har x⟩

/-- **The arithmetic for the original slots** from the arithmetic interface of the decoder at the
rescaling `γ √s / η`. -/
theorem exists_arithS {cA : ℝ} {dA : ℕ} (hcA : 0 ≤ cA) (D : QData X N s k b) {bd : ℕ} {K₀ K : ℝ}
    (hrot : ManuscriptConformance.comp_rotArith cA dA bd k b D.val K₀ K) {η : ℝ} (hη : 0 < η)
    {γ : ℝ} (hγ : 0 < γ) (hK₀ : K₀ ≤ γ * Real.sqrt s / η)
    (hK : γ * Real.sqrt s / η ≤ K) {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    ∃ ar : Arith (BW (k + 1) b),
      ArithOK ar (Sum.inl (Sum.inr (oPR (k + 1))))
        (sparseOpD (normS D η hη) (Equiv.refl _) (γ * Real.sqrt s)).dec ζ ∧
      ((ar.circ.length + ar.bT + ar.bP + ar.A : ℕ) : ℝ) ≤
        (3 * cA + 18) * ((bd : ℝ) + ((k + 1 : ℕ) : ℝ) + Real.logb 2 (1 / ζ) + 1) ^ max dA 1 := by
  have hdec := ManuscriptConformance.comp_decArith_padDataE hcA D hrot
  have hs : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.2 (by exact_mod_cast D.slots_pos)
  have hκ : 0 < γ * Real.sqrt s / η := div_pos (mul_pos hγ hs) hη
  obtain ⟨ar, hok, hcost⟩ := hdec _ hκ hK₀ hK ζ hζ hζ1
  refine ⟨ar, ?_, hcost⟩
  rw [normS_dec]
  exact hok

end NativeS

/-! ### The headline with the original sparsity -/

section HeadlineS

variable {X : Type*} {N s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {Xs : Type*} [Fintype Xs] [DecidableEq Xs] {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- **The Hadamard boundary circuit for the original slots when `s` is a power of two**: then the
original slots are all the low words of `⌈log₂ s⌉` bits and `padUJ D` meets `UJPrep`. -/
theorem padUJ_prep (D : QData X N s k b) {η : ℝ} (hη : 0 < η) (hs : s = 2 ^ sbP s) :
    UJPrep (R := R) (padUJ D) (normS D η hη).slot (Equiv.refl _) := by
  have hsP : s = sP s := hs
  refine hadUJ_prep (R := R) (sbP s) (sbP_le_succ D) (Equiv.refl _) _ hs fun j => ?_
  simp only [Equiv.refl_apply]
  rw [← pslot_range D.s_le_pow j]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨Fin.castLE (le_sP s) m, rfl⟩
  · rintro ⟨m, rfl⟩
    exact ⟨⟨m.val, lt_of_lt_of_eq m.isLt hsP.symm⟩, rfl⟩

set_option maxRecDepth 8192 in
/-- **Theorem `hs:thm:gates` with the explicit accounting on the schedule of the original sparsity
`s`, the private circuit constructed.** For sparse access of general size with any public decoder,
from the synthesis hypothesis, the arithmetic interface of the decoder on a range containing
`γ √s / η`, and a supplied boundary circuit `U_J` (gates with at most three controls, `C_J = |U_J|`)
preparing the boundary state of the `s` original slots (`UJPrep`; met by `padUJ D` when `s` is a
power of two, `padUJ_prep`), with `ζ = ε/(192 d)` and `δ = ε/(48 d)` at the degree `d = dgS` of the
original `s`: there is an arithmetic `ar`, fixed by the public data, with the cost bound of
`exists_arithS`, such that the circuit `finCS hS s U_J γ τ ε (privCircS hS (ε/(48 d)) D η hη γ ar)`
has the counts of `privCircS_spec` and, on every instance whose matrix is Hermitian with row and
column Euclidean norms at most `η`: valid gates of `𝒢`, exactly `6 d` private calls and so
`12 d |V'|_calls` primitive calls, at most `G₀ = synGS` synthesised occurrences outside the private
circuit, at most `6 d G_C + G₀ (c₁ log((G₀+1)/(ε/4)) + c₀ + 1)` gates, `k + 1` system qubits and the
stated further qubits, full-output error at most `ε` with an untouched reference, and the schedule
`d = k' (⌈32Q⌉ - 1)`, `Q = width s γ`, `α = η √s / γ`. -/
theorem sparse_gate_original (cA : ℝ) (dA : ℕ) (hcA : 0 ≤ cA) (hS : Synthesis 𝒢 Xs L)
    (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (D : QData X N s k b) (bd : ℕ) {K₀ K : ℝ}
    (hrot : ManuscriptConformance.comp_rotArith cA dA bd k b D.val K₀ K) {η : ℝ} (hη : 0 < η)
    (UJg : List (Gate (Fin (k + 1 + 1) ⊕ Fin (k + 1)))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (hUJ : UJPrep (R := R) UJg (normS D η hη).slot (Equiv.refl _))
    (γ T τ ε : ℝ) (hτ : τ = clockS s η T γ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hK₀ : K₀ ≤ γ * Real.sqrt s / η) (hK : γ * Real.sqrt s / η ≤ K) (hT : 0 ≤ T)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ ar : Arith (BW (k + 1) b),
      ((ar.circ.length + ar.bT + ar.bP + ar.A : ℕ) : ℝ) ≤
        (3 * cA + 18) * ((bd : ℝ) + ((k + 1 : ℕ) : ℝ) +
          Real.logb 2 (192 * (dgS s γ τ ε : ℝ) / ε) + 1) ^ max dA 1 ∧
      (∀ p : Query → Bool, nCallsN p (privOpS D η hη γ).V ≤
        3 * (2 * (if p Query.rowLocation then 1 else 0) +
          2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0))) ∧
      nGatesN (privOpS D η hη γ).V ≤ 28 * (k + 1) + implG k b * 5 ∧
      (nGatesN (privCircS hS (ε / (48 * (dgS s γ τ ε : ℝ))) D η hη γ ar) : ℝ) ≤
        (privGS D η hη γ ar : ℝ) *
          (1 + c₁ * Real.log (((privGS D η hη γ ar : ℝ) + 1) / (ε / (48 * (dgS s γ τ ε : ℝ)))) +
            c₀) ∧
      ∀ x : X, (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
        (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
        (∀ i ∈ finCS hS s UJg γ τ ε
          (privCircS hS (ε / (48 * (dgS s γ τ ε : ℝ))) D η hη γ ar), i.Valid) ∧
        (∀ g, NInstr.gate g ∈ finCS hS s UJg γ τ ε
          (privCircS hS (ε / (48 * (dgS s γ τ ε : ℝ))) D η hη γ ar) → GateOf 𝒢 g) ∧
        (∀ p : Query → Bool, nCallsN p (finCS hS s UJg γ τ ε
            (privCircS hS (ε / (48 * (dgS s γ τ ε : ℝ))) D η hη γ ar)) =
          6 * dgS s γ τ ε * (2 * nCallsN p (privOpS D η hη γ).V)) ∧
        nSynN 𝒢 (preCS s UJg γ τ ε
          (privCircS hS (ε / (48 * (dgS s γ τ ε : ℝ))) D η hη γ ar)) ≤
          synGS k s γ τ ε UJg.length ∧
        (nGatesN (finCS hS s UJg γ τ ε
            (privCircS hS (ε / (48 * (dgS s γ τ ε : ℝ))) D η hη γ ar)) : ℝ) ≤
          6 * (dgS s γ τ ε : ℝ) *
              nGatesN (privCircS hS (ε / (48 * (dgS s γ τ ε : ℝ))) D η hη γ ar) +
            (synGS k s γ τ ε UJg.length : ℝ) *
              (c₁ * Real.log (((synGS k s γ τ ε UJg.length : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
        Fintype.card (HW (SimWireMs (k + 1 + 1) (width (s : ℝ) γ) τ (moment γ) ε)
            (Fin (k + 1)) Empty ((SZ (k + 1) b ⊕ AW k b) ⊕ Xs) ar.bT ar.bP ar.A ⊕ Xs) =
          k + 1 + (2 * (k + 1 + 1) + 3 * slotMs τ ε + 6 * rgS s γ τ ε + 3) +
            ((6 * (k + 1) + 2 * b) + (6 * k + 6 + 2 * b) + Fintype.card Xs + ar.bT + ar.bP +
              ar.A + 3) + Fintype.card Xs ∧
        ‖nrun (D.prims (R := R) x) (finCS hS s UJg γ τ ε
            (privCircS hS (ε / (48 * (dgS s γ τ ε : ℝ))) D η hη γ ar)) ∘L
            (cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) -
            (cleanEmb ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
              NormedSpace.exp ((-Complex.I * (T : ℂ)) • qlift (R := R) (Equiv.refl _)
                (SparseStateOverlap.matrixOperator (D.padDataE.matrix x)))‖ ≤ ε ∧
        ‖nrun (D.prims (R := R) x) (finCS hS s UJg γ τ ε
            (privCircS hS (ε / (48 * (dgS s γ τ ε : ℝ))) D η hη γ ar)) ∘L
            ((cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
              cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) -
            ((cleanEmb ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
              cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) ∘L
              NormedSpace.exp ((-Complex.I * (T : ℂ)) • qlift (R := R) (Equiv.refl _)
                (SparseStateOverlap.matrixOperator (D.padMat x)))‖ ≤ ε ∧
        dgS s γ τ ε = depthMs (width (s : ℝ) γ) (τ * moment γ) ε *
          (SharpFilterSchedule.length (width (s : ℝ) γ) - 1) ∧
        (dgS s γ τ ε : ℝ) ≤ 128 * (τ * moment γ) +
          32 * width (s : ℝ) γ * (Real.logb 2 (4096 / ε) + 1) ∧
        meshMs τ ε ≤ 2 ^ slotMs τ ε ∧ (∀ j : ℕ, meshMs τ ε ≤ 2 ^ j → slotMs τ ε ≤ j) ∧
        rgS s γ τ ε = Nat.clog 2 (2 * dgS s γ τ ε + 2) := by
  have hτ0 : 0 ≤ τ := by
    rw [hτ]
    exact div_nonneg (mul_nonneg (mul_nonneg hη.le hT) (Real.sqrt_nonneg _)) hγ.le
  have hdR : (1 : ℝ) ≤ (dgS s γ τ ε : ℝ) := by exact_mod_cast dgS_pos s γ hτ0 hε hε1
  obtain ⟨hζ, hζ1, hδ, hδ1, hξ⟩ := budget_facts hε hε1 hdR
  obtain ⟨ar, hok, hcost⟩ := exists_arithS hcA D hrot hη hγ hK₀ hK hζ hζ1
  obtain ⟨hpcV, hpcG, hcC, hcV, hgV, hgP, hpc⟩ := privCircS_spec (R := R) hS hc₀ hc₁ hL hδ hδ1
    D hη γ ar hζ.le hok
  refine ⟨ar, ?_, hcV, hgV, hgP, fun x hH hrow hcol => ?_⟩
  · rw [one_div_div] at hcost
    exact hcost
  obtain ⟨hv, hg, hc, hsyn, hgates, hcard, herr1, herr2, hd, hdle, hm1, hm2, hr⟩ :=
    sparse_gate_total_s (R := R) hS hadj hc₀ hc₁ hL D hη UJg hUJg hUJ
      (privCircS hS (ε / (48 * (dgS s γ τ ε : ℝ))) D η hη γ ar) hpcV hpcG _
      (by positivity) γ T τ ε hτ hγ hγ1 hT hε hε1 hξ x hH hrow hcol (hpc x)
  refine ⟨hv, hg, fun p => by rw [hc p, hcC p], hsyn, hgates, ?_, herr1, herr2, hd, hdle, hm1,
    hm2, hr⟩
  rw [hcard, Fintype.card_sum, Fintype.card_sum, card_SZ, ManuscriptConformance.card_AW]

set_option maxRecDepth 8192 in
/-- **Every real time for the constructed circuit with the original sparsity**
(`sparse_gate_total_signed_s` with `pc = privCircS hS δ D η hη γ ar`): for an arithmetic `ar`
computing the rotation parameters within `ζ` and `24 d (δ + 4 ζ) ≤ ε` at the clock `|t'|`, the
circuit of `|t'|`, or its literal reverse-adjoint for `t < 0`, with the promise derived. -/
theorem sparse_gate_original_signed (hS : Synthesis 𝒢 Xs L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (D : QData X N s k b) {η : ℝ} (hη : 0 < η)
    (UJg : List (Gate (Fin (k + 1 + 1) ⊕ Fin (k + 1)))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (hUJ : UJPrep (R := R) UJg (normS D η hη).slot (Equiv.refl _)) (ar : Arith (BW (k + 1) b))
    {δ ζ : ℝ} (hδ : 0 < δ) (hζ : 0 ≤ ζ) (γ t t' ε : ℝ)
    (har : ArithOK ar (Sum.inl (Sum.inr (oPR (k + 1))))
      (sparseOpD (normS D η hη) (Equiv.refl _) (γ * Real.sqrt s)).dec ζ)
    (ht' : t' = clockS s η t γ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hξε : 24 * (dgS s γ |t'| ε : ℝ) * (δ + 4 * ζ) ≤ ε) (x : X)
    (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    (∀ i ∈ finCSignedS hS s UJg γ t' ε (privCircS hS δ D η hη γ ar), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ finCSignedS hS s UJg γ t' ε (privCircS hS δ D η hη γ ar) →
      GateOf 𝒢 g) ∧
    (∀ p : Query → Bool, nCallsN p (finCSignedS hS s UJg γ t' ε (privCircS hS δ D η hη γ ar)) =
      6 * dgS s γ |t'| ε * nCallsN p (privCircS hS δ D η hη γ ar)) ∧
    (nGatesN (finCSignedS hS s UJg γ t' ε (privCircS hS δ D η hη γ ar)) : ℝ) ≤
      6 * (dgS s γ |t'| ε : ℝ) * nGatesN (privCircS hS δ D η hη γ ar) +
        (synGS k s γ |t'| ε UJg.length : ℝ) *
          (c₁ * Real.log (((synGS k s γ |t'| ε UJg.length : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
    Fintype.card (HW (SimWireMs (k + 1 + 1) (width (s : ℝ) γ) |t'| (moment γ) ε)
        (Fin (k + 1)) Empty ((SZ (k + 1) b ⊕ AW k b) ⊕ Xs) ar.bT ar.bP ar.A ⊕ Xs) =
      k + 1 + (2 * (k + 1 + 1) + 3 * slotMs |t'| ε + 6 * rgS s γ |t'| ε + 3) +
        (Fintype.card ((SZ (k + 1) b ⊕ AW k b) ⊕ Xs) + ar.bT + ar.bP + ar.A + 3) +
        Fintype.card Xs ∧
    ‖nrun (D.prims (R := R) x) (finCSignedS hS s UJg γ t' ε (privCircS hS δ D η hη γ ar)) ∘L
        (cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
            (SparseStateOverlap.matrixOperator (D.padDataE.matrix x)))‖ ≤ ε ∧
    ‖nrun (D.prims (R := R) x) (finCSignedS hS s UJg γ t' ε (privCircS hS δ D η hη γ ar)) ∘L
        ((cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) -
        ((cleanEmb ∘L sysEmb (io (P := Reg (Fin (k + 1)) R))) ∘L
          cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
            (SparseStateOverlap.matrixOperator (D.padMat x)))‖ ≤ ε := by
  have har' := GeneralSparseODE.arithOK_liftA (Xa := AW k b) ar (oPR (k + 1)) _ ζ har
  obtain ⟨hv, hg, -, -, -⟩ := privSel_spec (R := R) hS hδ (privOpS D η hη γ)
    (privOpS_public D hη γ) (GeneralSparseODE.liftA (Xa := AW k b) ar) hζ har'
  exact sparse_gate_total_signed_s hS hadj hc₀ hc₁ hL D hη UJg hUJg hUJ
    (privCircS hS δ D η hη γ ar) hv hg (δ + 4 * ζ) (by positivity) γ t t' ε ht' hγ hγ1 hε hε1
    hξε x hH hrow hcol (privCircS_privOK hS hδ D hη γ ar hζ har x)

end HeadlineS

end

end SparseHamiltonian.SparseGateAccounting
