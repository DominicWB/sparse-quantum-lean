import ODELowerBoundExtensions.Release.Joint
import ODELowerBoundExtensions.Release.Herald
import ODELowerBoundExtensions.Release.Embed

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Theorem `odel:thm:combined` for retry protocols

Manuscript: Theorem `odel:thm:combined` and its proof. For `s ≥ 32`, `τ ≥ 4`, `ḡ ≥ 2`,
`0 < ε ≤ 1/64` (`CombinedRange`), every **retry-protocol** solver of the time-dependent class
(`RetrySolver` over the sampled-time access, the release's `ODERepeatProtocol.Protocol`
semantics) has worst-case matrix-query complexity

  `Q ≥ c (ḡ √s τ + √(sτr) + r)`,  `c = log 2/(8192π)` (`combinedConst`, unchanged),

where `Q` is the worst-case number of value queries over all transcripts
(`Protocol.worstCost valueWeight`, every attempt and every failure branch counted).

* `combined_max_retry` (max form): for one retry solver of each of the joint, mixed and precision
  families, the largest worst-case value count is at least `combinedBound s τ ḡ ε`. The proof is
  that of `SparseLowerBounds.ODE.combined_max` with the retry bounds `joint_witness_retry`,
  `mixed_forces_retry`, `precision_forces_retry`, `precision_forces_sqrt_retry` and
  `Hamiltonian.assembly`.
* `herald_max_retry`, `herald_witness_retry`, `precision_terms_witness_retry`: eq.
  `odel:eq:hsbound` for retry protocols in max and family form, and the fourth sentence of
  `odel:thm:combined` (the precision terms are witnessed by the `g = 1`
  families), the retry analogues of `herald_max`, `herald_witness`, `precision_terms_witness`.
* `combined_retry` (family form): one of the three families is in the class and retry-forces the
  bound (`forces_or_of_max_retry`, the classical step of `forces_or_of_max`).
* The released `SparseLowerBounds.ODE.combined` is the one-attempt special case: every `Solver` is
  a retry solver with the same counts (`Release/Embed`), so `RetryWitnesses` implies `Witnesses`
  (`retryWitnesses_witnesses`, no hypothesis on the input sets), and each disjunct of
  `combined_retry` implies the corresponding disjunct of `combined`. The released theorem is not
  restated here.

As for `combined`, this is a worst-case statement over the class; the three terms are witnessed by
different families and are not multiplied (proof of Theorem `odel:thm:combined`).
-/

namespace ODELowerBoundExtensions.Release

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit
open AdaptiveHamiltonianLowerBound.Access (valueWeight)

-- The nested time-addressed workspaces exceed the default instance size.
set_option synthInstance.maxSize 1024

/-- **From a max form to a family form for retry protocols** (`forces_or_of_max`): if, for one
retry solver of each of three families, the largest worst-case value count is at least `b`, then
one of the three families retry-forces `b`. -/
theorem forces_or_of_max_retry {X₁ N₁ Z₁ X₂ N₂ Z₂ X₃ N₃ Z₃ : Type*}
    [Fintype N₁] [DecidableEq N₁] [Fintype Z₁] [AddCommGroup Z₁]
    [Fintype N₂] [DecidableEq N₂] [Fintype Z₂] [AddCommGroup Z₂]
    [Fintype N₃] [DecidableEq N₃] [Fintype Z₃] [AddCommGroup Z₃] {K₁ K₂ K₃ s₁ s₂ s₃ : ℕ}
    (F₁ : Family X₁ N₁ Z₁ K₁ s₁) (F₂ : Family X₂ N₂ Z₂ K₂ s₂) (F₃ : Family X₃ N₃ Z₃ K₃ s₃)
    {ε b : ℝ}
    (h : ∀ (ι₁ ι₂ ι₃ E₁ E₂ E₃ G₁ G₂ G₃ : Type) [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
      [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [CompleteSpace E₁] [FiniteDimensional ℂ E₁]
      [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂] [CompleteSpace E₂] [FiniteDimensional ℂ E₂]
      [NormedAddCommGroup E₃] [InnerProductSpace ℂ E₃] [CompleteSpace E₃] [FiniteDimensional ℂ E₃]
      [NormedAddCommGroup G₁] [InnerProductSpace ℂ G₁] [CompleteSpace G₁]
      [NormedAddCommGroup G₂] [InnerProductSpace ℂ G₂] [CompleteSpace G₂]
      [NormedAddCommGroup G₃] [InnerProductSpace ℂ G₃] [CompleteSpace G₃]
      (A₁ : RetrySolver F₁ (F₁.access ι₁) E₁ G₁ ε) (A₂ : RetrySolver F₂ (F₂.access ι₂) E₂ G₂ ε)
      (A₃ : RetrySolver F₃ (F₃.access ι₃) E₃ G₃ ε),
      b ≤ max (A₁.prot.worstCost valueWeight : ℝ)
        (max (A₂.prot.worstCost valueWeight : ℝ) (A₃.prot.worstCost valueWeight))) :
    RetryForces F₁ ε b ∨ RetryForces F₂ ε b ∨ RetryForces F₃ ε b := by
  by_contra hne
  push Not at hne
  obtain ⟨h₁, h₂, h₃⟩ := hne
  unfold RetryForces at h₁ h₂ h₃
  simp only [not_forall] at h₁ h₂ h₃
  obtain ⟨ι₁, _, E₁, G₁, _, _, _, _, _, _, _, A₁, hA₁⟩ := h₁
  obtain ⟨ι₂, _, E₂, G₂, _, _, _, _, _, _, _, A₂, hA₂⟩ := h₂
  obtain ⟨ι₃, _, E₃, G₃, _, _, _, _, _, _, _, A₃, hA₃⟩ := h₃
  have hv : ∀ q, valueWeight q ≤ 1 := fun q => by cases q <;> simp [valueWeight]
  have cheap : ∀ {V C : ℕ}, V ≤ C → ¬ (b ≤ (V : ℝ) ∧ b ≤ (C : ℝ)) → (V : ℝ) < b := by
    intro V C hVC hn
    by_contra hc
    push Not at hc
    exact hn ⟨hc, hc.trans (by exact_mod_cast hVC)⟩
  have hmax := h ι₁ ι₂ ι₃ E₁ E₂ E₃ G₁ G₂ G₃ A₁ A₂ A₃
  have hlt := max_lt (cheap (worstCost_mono A₁.prot hv) hA₁)
    (max_lt (cheap (worstCost_mono A₂.prot hv) hA₂) (cheap (worstCost_mono A₃.prot hv) hA₃))
  linarith

variable {s : ℕ} {τ gbar ε : ℝ}

/-- **Eq. `odel:eq:hsbound` for retry protocols, max form** (Lemma `odel:lem:herald`; the retry
analogue of `SparseLowerBounds.ODE.herald_max`): for one retry solver of each of the three `g = 1`
families (time, mixed, precision) at `(s, τ, ε)`, the largest worst-case value count is at least
`c₀ (√s τ + √(sτr) + r)`, `c₀ = log 2/(4096π)` (`Hamiltonian.assembly`). For `L < 64τ` the time
bound alone carries it (proof of Lemma `odel:lem:herald`). -/
theorem herald_max_retry (h : HSRange τ s ε) {ιT ιM ιP ET EM EP GT GM GP : Type}
    [Fintype ιT] [Fintype ιM] [Fintype ιP]
    [NormedAddCommGroup ET] [InnerProductSpace ℂ ET] [CompleteSpace ET] [FiniteDimensional ℂ ET]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AT : RetrySolver (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]))
      ((timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])).access ιT) ET GT ε)
    (AM : RetrySolver (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
      ((mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])).access ιM) EM GM ε)
    (AP : RetrySolver (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
      ((precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])).access ιP) EP GP ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (AT.prot.worstCost valueWeight : ℝ)
        (max (AM.prot.worstCost valueWeight : ℝ) (AP.prot.worstCost valueWeight)) :=
  assembly h (time_forces_retry h ιT ET GT AT).1
    (fun hL => ⟨(precision_forces_retry h hL ιP EP GP AP).1,
      fun hs' => (precision_forces_sqrt_retry h hL hs' ιP EP GP AP).1⟩)
    (fun hL hs => (mixed_forces_retry h hL hs ιM EM GM AM).1)

/-- **Eq. `odel:eq:hsbound` for retry protocols, family form** (Lemma `odel:lem:herald`; the retry
analogue of `SparseLowerBounds.ODE.herald_witness`): for `τ ≥ 1`, `s ≥ 32`, `0 < ε ≤ 1/64`
(`HSRange`) and any `ḡ ≥ 1`, one of the time, mixed and precision families (homogeneous,
constant-coefficient, `D = 0`, `g = 1`) is in the class (`η = 1`, `T = τ`, `g ≤ ḡ`) and forces every
retry solver to make `c₀ (√s τ + √(sτr) + r)` value queries (and as many queries in total) in the
worst case, `c₀ = log 2/(4096π)`. -/
theorem herald_witness_retry (h : HSRange τ s ε) (hg : 1 ≤ gbar) :
    RetryWitnesses (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      RetryWitnesses (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      RetryWitnesses (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  have hf := forces_or_of_max_retry (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]))
    (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
    (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
    (ε := ε) (b := c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) (by
      intro ιT ιM ιP ET EM EP GT GM GP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AT AM AP
      exact herald_max_retry h AT AM AP)
  rcases hf with hf | hf | hf
  · exact Or.inl ⟨timeFamilyAt_inClass h hg, timeFamilyAt_T h, hf⟩
  · exact Or.inr (Or.inl ⟨mixedFamilyAt_inClass h hg, mixedFamilyAt_T h, hf⟩)
  · exact Or.inr (Or.inr ⟨precisionFamilyAt_inClass h hg, precisionFamilyAt_T h, hf⟩)

/-- **The precision terms of Theorem `odel:thm:combined` for retry protocols are witnessed by
`g = 1` families** (fourth sentence of the theorem, Theorem `odel:thm:combined`; the retry analogue
of `SparseLowerBounds.ODE.precision_terms_witness`): on `HSRange` and for any `ḡ ≥ 1`, one of the
homogeneous constant-coefficient families with `D = 0` and `g = 1` (time, mixed, precision)
retry-witnesses `c₀ (√(sτr) + r)`. -/
theorem precision_terms_witness_retry (h : HSRange τ s ε) (hg : 1 ≤ gbar) :
    RetryWitnesses (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      RetryWitnesses (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      RetryWitnesses (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  have hS : 0 ≤ Real.sqrt s * τ := mul_nonneg (Real.sqrt_nonneg _) h.tau_pos.le
  have hb : c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) :=
    mul_le_mul_of_nonneg_left (by linarith) c0_pos.le
  rcases herald_witness_retry h hg with hw | hw | hw
  · exact Or.inl (hw.mono hb)
  · exact Or.inr (Or.inl (hw.mono hb))
  · exact Or.inr (Or.inr (hw.mono hb))

/-- **Theorem `odel:thm:combined` for retry protocols, max form** (proof of Theorem
`odel:thm:combined`): for one retry solver of each of the three families (joint, mixed, precision)
at `(s, τ, ḡ, ε)`, the largest worst-case value count is at least `c (ḡ √s τ + √(sτr) + r)`,
`c = log 2/(8192π)`. -/
theorem combined_max_retry (h : CombinedRange s τ gbar ε) {ιJ ιM ιP EJ EM EP GJ GM GP : Type}
    [Fintype ιJ] [Fintype ιM] [Fintype ιP]
    [NormedAddCommGroup EJ] [InnerProductSpace ℂ EJ] [CompleteSpace EJ] [FiniteDimensional ℂ EJ]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GJ] [InnerProductSpace ℂ GJ] [CompleteSpace GJ]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AJ : RetrySolver (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge)
      ((jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge).access ιJ) EJ GJ ε)
    (AM : RetrySolver (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]))
      ((mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])).access ιM) EM GM ε)
    (AP : RetrySolver (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]))
      ((precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])).access ιP) EP GP ε) :
    combinedBound s τ gbar ε ≤ max (AJ.prot.worstCost valueWeight : ℝ)
      (max (AM.prot.worstCost valueWeight : ℝ) (AP.prot.worstCost valueWeight)) := by
  have hH := h.toHSRange
  have hJ := ((joint_witness_retry h.toJointRange).forces ιJ EJ GJ AJ).1
  have hS : 0 ≤ Real.sqrt s * τ := mul_nonneg (Real.sqrt_nonneg _) (by linarith [h.tau_ge])
  have hcJ : cT ≤ jointConst * gbar := by
    have := cT_le_inv_200
    unfold jointConst
    linarith [h.gbar_ge]
  have hT : cT * Real.sqrt s * τ ≤ (AJ.prot.worstCost valueWeight : ℝ) := by
    calc cT * Real.sqrt s * τ = cT * (Real.sqrt s * τ) := by ring
      _ ≤ jointConst * gbar * (Real.sqrt s * τ) := mul_le_mul_of_nonneg_right hcJ hS
      _ = jointConst * gbar * Real.sqrt s * τ := by ring
      _ ≤ _ := hJ
  have hmax := assembly hH hT
    (fun hL => ⟨(precision_forces_retry hH hL ιP EP GP AP).1,
      fun hs' => (precision_forces_sqrt_retry hH hL hs' ιP EP GP AP).1⟩)
    (fun hL hs => (mixed_forces_retry hH hL hs ιM EM GM AM).1)
  have hg : c0 * gbar * (Real.sqrt s * τ) ≤ jointConst * gbar * (Real.sqrt s * τ) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right c0_le_jointConst (by linarith [h.gbar_ge])) hS
  have hle := le_max_left (AJ.prot.worstCost valueWeight : ℝ)
    (max (AM.prot.worstCost valueWeight : ℝ) (AP.prot.worstCost valueWeight))
  have hJ' : jointConst * gbar * (Real.sqrt s * τ) ≤ (AJ.prot.worstCost valueWeight : ℝ) := by
    calc jointConst * gbar * (Real.sqrt s * τ) = jointConst * gbar * Real.sqrt s * τ := by ring
      _ ≤ _ := hJ
  have hsτ : gbar * Real.sqrt s * τ = gbar * (Real.sqrt s * τ) := by ring
  unfold combinedBound
  rw [combinedConst_eq, hsτ]
  linarith [mul_nonneg c0_pos.le hS]

/-- **Theorem `odel:thm:combined` for retry protocols** (with its proof): for
`s ≥ 32`, `τ ≥ 4`, `ḡ ≥ 2`, `0 < ε ≤ 1/64`, one of the three families — the joint family of
`odel:thm:joint` (`g = Θ(ḡ)`) or the mixed or precision family of `odel:lem:herald` (`g = 1`) — is
in the class (`η = 1`, `T = τ`, `g ≤ ḡ`) and forces every retry-protocol solver to make at least
`c (ḡ √s τ + √(sτr) + r)` value queries (and as many queries in total) in the worst case,
`c = log 2/(8192π)`. By `retryWitnesses_witnesses` each disjunct implies the corresponding
disjunct of `SparseLowerBounds.ODE.combined`. -/
theorem combined_retry (h : CombinedRange s τ gbar ε) :
    RetryWitnesses (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge) τ gbar ε
        (combinedBound s τ gbar ε) ∨
      RetryWitnesses (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) τ gbar ε
        (combinedBound s τ gbar ε) ∨
      RetryWitnesses (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) τ gbar ε
        (combinedBound s τ gbar ε) := by
  have hH := h.toHSRange
  have hW := joint_witness_retry h.toJointRange
  have hg1 : 1 ≤ gbar := by linarith [h.gbar_ge]
  have hf := forces_or_of_max_retry (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge)
    (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]))
    (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]))
    (ε := ε) (b := combinedBound s τ gbar ε) (by
      intro ιJ ιM ιP EJ EM EP GJ GM GP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AJ AM AP
      exact combined_max_retry h AJ AM AP)
  rcases hf with hf | hf | hf
  · exact Or.inl ⟨hW.inClass, hW.time_eq, hf⟩
  · exact Or.inr (Or.inl ⟨mixedFamilyAt_inClass hH hg1, mixedFamilyAt_T hH, hf⟩)
  · exact Or.inr (Or.inr ⟨precisionFamilyAt_inClass hH hg1, precisionFamilyAt_T hH, hf⟩)

end

end ODELowerBoundExtensions.Release
