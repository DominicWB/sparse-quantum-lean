import ODELowerBoundExtensions.Padding.JointTheorem
import ODELowerBoundExtensions.Padding.Precision

/-!
# Theorem `odel:thm:combined` in one common dimension and on qubit registers

Manuscript: proof of Theorem `odel:thm:combined`
(lines 4001-4009): "The promise class `g ≤ ḡ` contains both the family in Theorem
`odel:thm:joint` and the `g = 1` families in Lemma `odel:lem:herald`. The maximum of their lower
bounds is at least a fixed fraction of their sum. Pad dimensions to a common known size if
desired." Together with the qubit-register remark of line 3904.

The three families of `SparseLowerBounds.ODE.combined` are replaced by their known paddings: the
joint family padded by `PJ` (`jointPadFamilyAt`; with `dense = true` it carries the dense block and
has maximum sparsity exactly `s`, with `dense = false` it is the plain zero padding of
`jointFamilyAt`, equation and words, `jointZeroPad_zeroPad`, `jointZeroPad_table`) and
the mixed and precision families padded by `PM`, `PP` (`mixedPadFamilyAt`,
`precisionPadFamilyAt`). The constant is that of `combined`, `c = log 2/(8192π)`
(`combinedConst`), and the proofs are those of `combined_max` and `combined`, with
`joint_witness_pad`, `mixed_forces_pad`, `precision_forces_pad` and `precision_forces_sqrt_pad`.

* `combined_max_pad` (max form) and `combined_pad` (family form): for any three known paddings;
  `combined_pad_sparsityAttained`: all three padded families have maximum sparsity exactly `s`.
* `card_le_of_combinedDim`: every `Nd ≥ max(3 ḡ² s, 4 s (τ + r + 1))` is at least the three
  dimensions (`joint_instance_props`, `hard_instances`).
* `combined_max_common_dimension`, `combined_common_dimension`: for every `Nd` at least the three
  dimensions, the families padded by `PadTo N_X Nd` all have dimension exactly `Nd` and obey eq.
  `odel:eq:combined`; so the worst case over the class restricted to dimension `Nd` obeys it.
* `combined_qubit_register`, `exists_qubit_register`: the same in dimension `2^q`, for every
  sufficiently large `q`, with the sparsity facts of `combined_common_dimension`.

As in lines 4006-4008 these are worst-case statements: no single instance witnesses all terms, and
the independent bounds are not multiplied. No assertion is made for `Nd` below a family's
dimension ("No assertion is made for an insufficient fixed dimension", lines 3680-3681). The
attribution of the third and fourth sentences of `odel:thm:combined` to the padded families is
`jointPadFamilyAt_g` (`g = Θ(ḡ)`) and `precision_terms_witness_pad` with `herald_pad_props`
(`g = 1`, `D = 0`).

**Forms covered.** The full heralded `SparseLowerBounds.ODE.Solver` of `ODE/Model` (any branch
register `ι`, any garbage space `G`), i.e. `Family.Forces`; controlled calls by the reduction of
the **Controlled calls** paragraph of `ODE/Model`, which has no Lean lemma.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Padding

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit SparseLowerBounds
  SparseLowerBounds.ODE SparseLowerBounds.Readout SparseLowerBounds.Hamiltonian
  LowerBoundRemarks.HamiltonianPadding

-- The nested time-addressed workspaces exceed the default instance size.
set_option synthInstance.maxSize 1024

variable {s : ℕ} {τ gbar ε : ℝ}

/-- **Theorem `odel:thm:combined` for padded families, max form** (as `combined_max`): for any
known paddings `PJ`, `PM`, `PP` and one solver of each padded family (joint, mixed, precision) at
`(s, τ, ḡ, ε)`, the largest value-query count is at least `c (ḡ √s τ + √(sτr) + r)`,
`c = log 2/(8192π)`. -/
theorem combined_max_pad (h : CombinedRange s τ gbar ε) (dense : Bool) (PJ PM PP : Type*)
    [Fintype PJ] [DecidableEq PJ] [Fintype PM] [DecidableEq PM] [Fintype PP] [DecidableEq PP]
    {ιJ ιM ιP GJ GM GP : Type} [Fintype ιJ] [Fintype ιM] [Fintype ιP]
    [NormedAddCommGroup GJ] [InnerProductSpace ℂ GJ] [CompleteSpace GJ]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AJ : Solver ιJ (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge PJ) GJ ε)
    (AM : Solver ιM (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PM) GM ε)
    (AP : Solver ιP (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PP) GP ε) :
    combinedBound s τ gbar ε ≤ max (AJ.prog.labelCount .value : ℝ)
      (max (AM.prog.labelCount .value : ℝ) (AP.prog.labelCount .value)) := by
  have hH := h.toHSRange
  have hJ := ((joint_witness_pad h.toJointRange dense PJ).1.forces ιJ GJ AJ).1
  have hS : 0 ≤ Real.sqrt s * τ := mul_nonneg (Real.sqrt_nonneg _) (by linarith [h.tau_ge])
  have hcJ : cT ≤ jointConst * gbar := by
    have := cT_le_inv_200
    unfold jointConst
    linarith [h.gbar_ge]
  have hT : cT * Real.sqrt s * τ ≤ (AJ.prog.labelCount .value : ℝ) := by
    calc cT * Real.sqrt s * τ = cT * (Real.sqrt s * τ) := by ring
      _ ≤ jointConst * gbar * (Real.sqrt s * τ) := mul_le_mul_of_nonneg_right hcJ hS
      _ = jointConst * gbar * Real.sqrt s * τ := by ring
      _ ≤ _ := hJ
  have hmax := assembly hH hT
    (fun hL => ⟨(precision_forces_pad hH hL PP ιP GP AP).1,
      fun hs' => (precision_forces_sqrt_pad hH hL hs' PP ιP GP AP).1⟩)
    (fun hL hs => (mixed_forces_pad hH hL hs PM ιM GM AM).1)
  have hg : c0 * gbar * (Real.sqrt s * τ) ≤ jointConst * gbar * (Real.sqrt s * τ) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right c0_le_jointConst (by linarith [h.gbar_ge])) hS
  have hle := le_max_left (AJ.prog.labelCount .value : ℝ)
    (max (AM.prog.labelCount .value : ℝ) (AP.prog.labelCount .value))
  have hJ' : jointConst * gbar * (Real.sqrt s * τ) ≤ (AJ.prog.labelCount .value : ℝ) := by
    calc jointConst * gbar * (Real.sqrt s * τ) = jointConst * gbar * Real.sqrt s * τ := by ring
      _ ≤ _ := hJ
  have hsτ : gbar * Real.sqrt s * τ = gbar * (Real.sqrt s * τ) := by ring
  unfold combinedBound
  rw [combinedConst_eq, hsτ]
  linarith [mul_nonneg c0_pos.le hS]

/-- **Theorem `odel:thm:combined` for padded families** (as `combined`): for `s ≥ 32`, `τ ≥ 4`,
`ḡ ≥ 2`, `0 < ε ≤ 1/64` and any known paddings, one of the three padded families is in the class
(`η = 1`, `T = τ`, `g ≤ ḡ`) and forces `c (ḡ √s τ + √(sτr) + r)` value queries (and as many
matrix queries), `c = log 2/(8192π)`. -/
theorem combined_pad (h : CombinedRange s τ gbar ε) (dense : Bool) (PJ PM PP : Type*)
    [Fintype PJ] [DecidableEq PJ] [Fintype PM] [DecidableEq PM] [Fintype PP] [DecidableEq PP] :
    (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge PJ).Witnesses τ gbar ε
        (combinedBound s τ gbar ε) ∨
      (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PM).Witnesses τ gbar ε
        (combinedBound s τ gbar ε) ∨
      (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PP).Witnesses τ gbar ε
        (combinedBound s τ gbar ε) := by
  have hW := (joint_witness_pad h.toJointRange dense PJ).1
  -- Only the mixed and precision components are used; the time padding slot is `PEmpty`.
  have hI := herald_instances_pad h.toHSRange (by linarith [h.gbar_ge] : 1 ≤ gbar)
    (PEmpty : Type) PM PP
  have hf := forces_or_of_max (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge PJ)
    (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PM)
    (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PP)
    (ε := ε) (b := combinedBound s τ gbar ε) (by
      intro ιJ ιM ιP GJ GM GP _ _ _ _ _ _ _ _ _ _ _ _ AJ AM AP
      exact combined_max_pad h dense PJ PM PP AJ AM AP)
  rcases hf with hf | hf | hf
  · exact Or.inl ⟨hW.inClass, hW.time_eq, hf⟩
  · exact Or.inr (Or.inl ⟨hI.2.1.1, hI.2.1.2.1, hf⟩)
  · exact Or.inr (Or.inr ⟨hI.2.2.1, hI.2.2.2.1, hf⟩)

/-- **The three padded families have maximum sparsity exactly `s`** (lines 3662, 3899), the
joint family with its dense block. -/
theorem combined_pad_sparsityAttained (h : CombinedRange s τ gbar ε) (PJ PM PP : Type*)
    [Fintype PJ] [DecidableEq PJ] [Fintype PM] [DecidableEq PM] [Fintype PP] [DecidableEq PP] :
    SparsityAttained (jointPadFamilyAt s τ gbar true h.toJointRange.s_ge h.tau_ge PJ) ∧
      SparsityAttained (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PM) ∧
      SparsityAttained (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PP) := by
  -- Only the mixed and precision components are used; the time padding slot is `PEmpty`.
  have hI := herald_instances_pad h.toHSRange (by linarith [h.gbar_ge] : 1 ≤ gbar)
    (PEmpty : Type) PM PP
  exact ⟨(joint_witness_pad h.toJointRange true PJ).2 rfl, hI.2.1.2.2, hI.2.2.2.2⟩

/-- **A sufficient common dimension**: every `Nd ≥ 3 ḡ² s` and `Nd ≥ 4 s (τ + r + 1)` is at least
the dimension of each of the three unpadded families (`joint_instance_props`,
`hard_instances`). -/
theorem card_le_of_combinedDim (h : CombinedRange s τ gbar ε) {Nd : ℕ}
    (hJ : 3 * gbar ^ 2 * s ≤ (Nd : ℝ)) (hH : 4 * s * (τ + hsR τ ε + 1) ≤ (Nd : ℝ)) :
    Fintype.card (JointIndex (jointM gbar) (jointMu s) s) ≤ Nd ∧
      Fintype.card (SearchIndex (precN τ ε) (hsMu s) s) ≤ Nd ∧
      Fintype.card (ScalarIndex (precN τ ε) s) ≤ Nd := by
  have hJ' := (joint_instance_props (s := s) (by have := h.s_ge; omega) h.gbar_ge).2.2
  have hH' := card_le_of_dim h.toHSRange hH
  exact ⟨Nat.cast_le.mp (hJ'.trans hJ), hH'.2.1, hH'.2.2⟩

/-- **Theorem `odel:thm:combined` in one common dimension, max form** (lines 4005-4006): for
every `Nd` at least the three dimensions, the three families padded by `PadTo N_X Nd` have
dimension exactly `Nd`, and for one solver of each, the largest value-query count is at least
`c (ḡ √s τ + √(sτr) + r)`. -/
theorem combined_max_common_dimension (h : CombinedRange s τ gbar ε) (dense : Bool) (Nd : ℕ)
    (hJ : Fintype.card (JointIndex (jointM gbar) (jointMu s) s) ≤ Nd)
    (hM : Fintype.card (SearchIndex (precN τ ε) (hsMu s) s) ≤ Nd)
    (hP : Fintype.card (ScalarIndex (precN τ ε) s) ≤ Nd)
    {ιJ ιM ιP GJ GM GP : Type} [Fintype ιJ] [Fintype ιM] [Fintype ιP]
    [NormedAddCommGroup GJ] [InnerProductSpace ℂ GJ] [CompleteSpace GJ]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AJ : Solver ιJ (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge
      (PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd)) GJ ε)
    (AM : Solver ιM (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
      (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd)) GM ε)
    (AP : Solver ιP (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
      (PadTo (ScalarIndex (precN τ ε) s) Nd)) GP ε) :
    Fintype.card (JointIndex (jointM gbar) (jointMu s) s ⊕
        PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd) = Nd ∧
      Fintype.card (SearchIndex (precN τ ε) (hsMu s) s ⊕
        PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd) = Nd ∧
      Fintype.card (ScalarIndex (precN τ ε) s ⊕ PadTo (ScalarIndex (precN τ ε) s) Nd) = Nd ∧
      combinedBound s τ gbar ε ≤ max (AJ.prog.labelCount .value : ℝ)
        (max (AM.prog.labelCount .value : ℝ) (AP.prog.labelCount .value)) := by
  exact ⟨card_padTo hJ, card_padTo hM, card_padTo hP, combined_max_pad h dense _ _ _ AJ AM AP⟩

/-- **Theorem `odel:thm:combined` in one common dimension** (family form, lines 4001-4009): for
every `Nd` at least the three dimensions (e.g. `card_le_of_combinedDim`), the three families
padded by `PadTo N_X Nd` have dimension exactly `Nd` and maximum sparsity exactly `s` (the joint
family when `dense = true`), and one of
them is in the class (`η = 1`, `T = τ`, `g ≤ ḡ`) and forces `c (ḡ √s τ + √(sτr) + r)` value
queries. So the worst case over the class in dimension `Nd` obeys eq. `odel:eq:combined`. -/
theorem combined_common_dimension (h : CombinedRange s τ gbar ε) (dense : Bool) (Nd : ℕ)
    (hJ : Fintype.card (JointIndex (jointM gbar) (jointMu s) s) ≤ Nd)
    (hM : Fintype.card (SearchIndex (precN τ ε) (hsMu s) s) ≤ Nd)
    (hP : Fintype.card (ScalarIndex (precN τ ε) s) ≤ Nd) :
    Fintype.card (JointIndex (jointM gbar) (jointMu s) s ⊕
        PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd) = Nd ∧
      Fintype.card (SearchIndex (precN τ ε) (hsMu s) s ⊕
        PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd) = Nd ∧
      Fintype.card (ScalarIndex (precN τ ε) s ⊕ PadTo (ScalarIndex (precN τ ε) s) Nd) = Nd ∧
      ((dense = true → SparsityAttained (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge
          h.tau_ge (PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd))) ∧
        SparsityAttained (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd)) ∧
        SparsityAttained (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (ScalarIndex (precN τ ε) s) Nd))) ∧
      ((jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd)).Witnesses τ gbar ε
          (combinedBound s τ gbar ε) ∨
        (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd)).Witnesses τ gbar ε
          (combinedBound s τ gbar ε) ∨
        (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (ScalarIndex (precN τ ε) s) Nd)).Witnesses τ gbar ε
          (combinedBound s τ gbar ε)) := by
  -- Only the mixed and precision components are used; the time padding slot is `PEmpty`.
  have hI := herald_instances_pad h.toHSRange (by linarith [h.gbar_ge] : 1 ≤ gbar)
    (PEmpty : Type) (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd)
    (PadTo (ScalarIndex (precN τ ε) s) Nd)
  exact ⟨card_padTo hJ, card_padTo hM, card_padTo hP,
    ⟨(joint_witness_pad h.toJointRange dense _).2, hI.2.1.2.2, hI.2.2.2.2⟩,
    combined_pad h dense _ _ _⟩

/-- **Theorem `odel:thm:combined` on a qubit register** (lines 3899-3904, 4005-4006): for every
`q` with `3 ḡ² s ≤ 2^q` and `4 s (τ + r + 1) ≤ 2^q`, the three families padded by
`PadTo N_X (2^q)` have dimension exactly `2^q` and maximum sparsity exactly `s` (the joint family
when `dense = true`), and one of them is in the class and forces `c (ḡ √s τ + √(sτr) + r)` value
queries. The case `Nd = 2^q` of `combined_common_dimension`. -/
theorem combined_qubit_register (h : CombinedRange s τ gbar ε) (dense : Bool) (q : ℕ)
    (hqJ : 3 * gbar ^ 2 * s ≤ (2 : ℝ) ^ q) (hqH : 4 * s * (τ + hsR τ ε + 1) ≤ (2 : ℝ) ^ q) :
    Fintype.card (JointIndex (jointM gbar) (jointMu s) s ⊕
        PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q)) = 2 ^ q ∧
      Fintype.card (SearchIndex (precN τ ε) (hsMu s) s ⊕
        PadTo (SearchIndex (precN τ ε) (hsMu s) s) (2 ^ q)) = 2 ^ q ∧
      Fintype.card (ScalarIndex (precN τ ε) s ⊕
        PadTo (ScalarIndex (precN τ ε) s) (2 ^ q)) = 2 ^ q ∧
      ((dense = true → SparsityAttained (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge
          h.tau_ge (PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q)))) ∧
        SparsityAttained (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) (2 ^ q))) ∧
        SparsityAttained (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (ScalarIndex (precN τ ε) s) (2 ^ q)))) ∧
      ((jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q))).Witnesses τ gbar ε
          (combinedBound s τ gbar ε) ∨
        (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) (2 ^ q))).Witnesses τ gbar ε
          (combinedBound s τ gbar ε) ∨
        (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (ScalarIndex (precN τ ε) s) (2 ^ q))).Witnesses τ gbar ε
          (combinedBound s τ gbar ε)) := by
  obtain ⟨hJ, hM, hP⟩ := card_le_of_combinedDim h (Nd := 2 ^ q) (by push_cast; exact hqJ)
    (by push_cast; exact hqH)
  exact combined_common_dimension h dense (2 ^ q) hJ hM hP

/-- **Every sufficiently large qubit register qualifies**: there is `q₀` such that every
`q ≥ q₀` satisfies the two dimension conditions of `combined_qubit_register`. -/
theorem exists_qubit_register (s : ℕ) (τ gbar ε : ℝ) :
    ∃ q₀ : ℕ, ∀ q, q₀ ≤ q →
      3 * gbar ^ 2 * s ≤ (2 : ℝ) ^ q ∧ 4 * s * (τ + hsR τ ε + 1) ≤ (2 : ℝ) ^ q := by
  obtain ⟨q₀, hq₀⟩ := pow_unbounded_of_one_lt
    (max (3 * gbar ^ 2 * s) (4 * s * (τ + hsR τ ε + 1))) (one_lt_two : (1 : ℝ) < 2)
  refine ⟨q₀, fun q hq => ?_⟩
  have h2 : (2 : ℝ) ^ q₀ ≤ 2 ^ q := pow_le_pow_right₀ one_le_two hq
  exact ⟨(le_max_left _ _).trans (hq₀.le.trans h2), (le_max_right _ _).trans (hq₀.le.trans h2)⟩

end

end ODELowerBoundExtensions.Padding
