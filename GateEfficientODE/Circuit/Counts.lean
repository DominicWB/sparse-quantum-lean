import GateEfficientODE.Circuit.Trial

/-!
# Validity and exact counts of the trial circuits

`prepC` makes exactly `6d` private calls, `12d` calls of `U_J` or `U_J†`, one
call of each source interface and at most

`prepGates = 200 (d + 1)(a + m + r + 1) + 2 (k + 1) + 3 · 2^l (2l + 1)`

elementary gates.  One step adds the two reflections, one seed reflection
and the sign, with at most `reflGates = 6 nz + 4` gates, where
`nz = card (Wire a m r K) + 1 + k + l` is the length of the zero test.  The
trial with `j` steps has exactly `(2j+1) 6d` private calls, `(2j+1) 12d`
calls of `U_J` or `U_J†`, `2j+1` calls of each source interface, `j` seed
reflections, and at most `(2j+1) prepGates + j reflGates` gates
(`trialC_counts`).  Every instruction is valid (`trialC_valid`).
-/

namespace SparseHamiltonian.GateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire anc_injective simCircuit simM simR simK fDeg zMat zMat_unitary
  negOne_unitary simL labLen labWt stepW cap cap_succ simM_spec simR_spec schedule_ge ampI_counts
  ampI_valid gate_bound)
open scoped InnerProduct BigOperators

/-! ### Public facts about the released simulator -/

/-- Validity and counts of the released simulator follow from the public data
alone. -/
theorem sim_public (a : ℕ) (τ Q qbar ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε) :
    (∀ g ∈ simCircuit a τ Q qbar ε, g.Valid Wire.anc) ∧
    GateCircuit.nPriv (simCircuit a τ Q qbar ε) = 6 * fDeg Q τ qbar ε ∧
    GateCircuit.nUJ (simCircuit a τ Q qbar ε) = 12 * fDeg Q τ qbar ε ∧
    GateCircuit.nGates (simCircuit a τ Q qbar ε) ≤
      200 * (fDeg Q τ qbar ε + 1) * (a + simM τ ε + simR Q τ qbar ε + 1) := by
  obtain ⟨hm1, _⟩ := simM_spec τ ε
  obtain ⟨_, _, hr2⟩ := simR_spec Q τ qbar ε
  have hw0 : 0 ≤ stepW τ (simM τ ε) := div_nonneg hτ (Nat.cast_nonneg _)
  have hwq : stepW τ (simM τ ε) ≤ 1 / 4 :=
    (schedule_ge τ (ε / 3) hτ (by positivity) (2 ^ simM τ ε) hm1).2.1
  obtain ⟨_, _, _, hσc, _⟩ := CayleyTransfer.scalar_promises (stepW τ (simM τ ε)) hw0 hwq
  have hunit : CayleyTransfer.c (stepW τ (simM τ ε)) ^ 2 +
      CayleyTransfer.sigma (stepW τ (simM τ ε)) ^ 2 = 1 := by
    linarith
  have hN : 2 * fDeg Q τ qbar ε ≤ cap (simR Q τ qbar ε) + 1 := by
    have := cap_succ (simR Q τ qbar ε)
    have h1 := (simR_spec Q τ qbar ε).1
    omega
  obtain ⟨hc1, hc2, hc3⟩ := ampI_counts (a := a) (m := simM τ ε) (K := simK a Q τ qbar ε)
    (simL Q τ qbar ε) (labLen Q τ qbar ε) (labWt Q τ qbar ε)
    (CayleyTransfer.c (stepW τ (simM τ ε)))
    (CayleyTransfer.sigma (stepW τ (simM τ ε))) (2 * fDeg Q τ qbar ε) hN
  have hgb := gate_bound a (simM τ ε) (simR Q τ qbar ε) (fDeg Q τ qbar ε)
    (2 ^ simR Q τ qbar ε) hr2
  refine ⟨ampI_valid _ _ _ _ _ hunit _, ?_, ?_, ?_⟩
  · unfold simCircuit; rw [hc1]; ring
  · unfold simCircuit; rw [hc2]; ring
  · unfold simCircuit
    refine hc3.trans (le_of_eq_of_le ?_ hgb)
    ring

/-! ### Counting over repeated blocks -/

section Rep

variable {S O : Type*}

theorem countP_replicate_flatten (c : OInstr S O → Bool) (j : ℕ) (gs : List (OInstr S O)) :
    ((List.replicate j gs).flatten).countP c = j * gs.countP c := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [List.replicate_succ, List.flatten_cons, List.countP_append, ih]
      ring

end Rep

namespace Params

variable (p : Params)

/-- The number of zero-test literals. -/
abbrev nz : ℕ := Fintype.card (Wire p.a p.m p.r p.K) + 1 + p.k + p.l

/-- The gate budget of one preparation. -/
def prepGates : ℕ :=
  200 * (p.d + 1) * (p.a + p.m + p.r + 1) + 2 * (p.k + 1) + 3 * (2 ^ p.l * (2 * p.l + 1))

/-- The gate budget of the reflections and the sign of one step. -/
def reflGates : ℕ := 6 * p.nz + 4

theorem select_counts (hτ : 0 ≤ p.tau) (hν : 0 < p.nu) :
    nPriv p.select = 6 * p.d ∧ nUJ p.select = 12 * p.d ∧ (∀ b, nSrc b p.select = 0) ∧
      nSeed p.select = 0 ∧
      nGates p.select ≤ 200 * (p.d + 1) * (p.a + p.m + p.r + 1) := by
  obtain ⟨_, hP, hU, hG⟩ := sim_public p.a p.tau p.Q p.qbar p.nu hτ hν
  obtain ⟨eG, eU, eP, eS, eE⟩ := embI_counts (O := OWire p.k p.l p.f)
    (simCircuit p.a p.tau p.Q p.qbar p.nu)
  refine ⟨?_, ?_, eS, eE, ?_⟩
  · unfold select; rw [eP, hP]
  · unfold select; rw [eU, hU]
  · unfold select; rw [eG]; exact hG

theorem load_counts :
    nPriv p.load = 0 ∧ nUJ p.load = 0 ∧ (∀ b, nSrc b p.load = 1) ∧ nSeed p.load = 0 ∧
      nGates p.load = 0 := by
  refine ⟨rfl, rfl, ?_, rfl, rfl⟩
  intro b
  cases b <;> rfl

theorem srcPrep_length : p.srcPrep.length ≤ p.k + 1 := constT_length _ _ _

theorem lchPrep_length : p.lchPrep.length ≤ 2 ^ p.l * (2 * p.l + 1) := prepT_length_le _ _

theorem lchPhase_length : p.lchPhase.length ≤ 2 ^ p.l * (2 * p.l + 1) := phaseT_length _ _ _

theorem prepC_counts (hτ : 0 ≤ p.tau) (hν : 0 < p.nu) :
    nPriv p.prepC = 6 * p.d ∧ nUJ p.prepC = 12 * p.d ∧ (∀ b, nSrc b p.prepC = 1) ∧
      nSeed p.prepC = 0 ∧ nGates p.prepC ≤ p.prepGates := by
  obtain ⟨sP, sU, sS, sE, sG⟩ := p.select_counts hτ hν
  obtain ⟨lP, lU, lS, lE, lG⟩ := p.load_counts
  obtain ⟨g1U, g1P, g1S, g1E⟩ := ofGates_counts (S := Wire p.a p.m p.r p.K) p.srcPrep
  obtain ⟨g2U, g2P, g2S, g2E⟩ := ofGates_counts (S := Wire p.a p.m p.r p.K) p.lchPrep
  obtain ⟨g3U, g3P, g3S, g3E⟩ := ofGates_counts (S := Wire p.a p.m p.r p.K) p.lchPhase
  have h1 := p.srcPrep_length
  have h2 := p.lchPrep_length
  have h3 := p.lchPhase_length
  unfold prepC
  simp only [nPriv_append, nUJ_append, nSrc_append, nSeed_append, nGates_append,
    nPriv_invList, nUJ_invList, nSrc_invList, nSeed_invList, nGates_invList, nGates_ofGates]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [g1P, g2P, g3P, lP, sP]; omega
  · rw [g1U, g2U, g3U, lU, sU]; omega
  · intro b
    rw [g1S b, g2S b, g3S b, lS b, sS b]
  · rw [g1E, g2E, g3E, lE, sE]
  · rw [lG]
    unfold prepGates
    omega

theorem rgoodG_length : (rgoodG (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k) (l := p.l)
    (f := p.f)).length ≤ 2 * p.nz + 1 := by
  have h := mcGate_length_le (zeroLits (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k)
    (l := p.l) (f := p.f)) poolList (Sum.inr OWire.flg) zMat
  rw [zeroLits_length] at h
  exact h

theorem flagG_length : (flagG (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k) (l := p.l)
    (f := p.f)).length ≤ 2 * p.nz + 1 := by
  have h := mcGate_length_le (zeroLits (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k)
    (l := p.l) (f := p.f)) poolList (Sum.inr OWire.flg) pauliX
  rw [zeroLits_length] at h
  exact h

theorem rseedC_counts :
    nPriv (rseedC (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k) (l := p.l)
      (f := p.f)) = 0 ∧
    nUJ (rseedC (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k) (l := p.l) (f := p.f)) = 0 ∧
    (∀ b, nSrc b (rseedC (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k) (l := p.l)
      (f := p.f)) = 0) ∧
    nSeed (rseedC (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k) (l := p.l)
      (f := p.f)) = 1 ∧
    nGates (rseedC (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k) (l := p.l)
      (f := p.f)) ≤ 2 * (2 * p.nz + 1) := by
  obtain ⟨gU, gP, gS, gE⟩ := ofGates_counts (S := Wire p.a p.m p.r p.K)
    (flagG (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k) (l := p.l) (f := p.f))
  have hl := p.flagG_length
  unfold rseedC
  simp only [nPriv_append, nUJ_append, nSrc_append, nSeed_append, nGates_append, nGates_ofGates]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [gP]; rfl
  · rw [gU]; rfl
  · intro b; rw [gS b]; rfl
  · rw [gE]; rfl
  · have e : nGates [OInstr.seed (S := Wire p.a p.m p.r p.K) [(Sum.inr (OWire.flg (k := p.k)
        (l := p.l) (f := p.f)), true)]] = 0 := rfl
    rw [e]
    omega

theorem stepC_counts (hτ : 0 ≤ p.tau) (hν : 0 < p.nu) :
    nPriv p.stepC = 12 * p.d ∧ nUJ p.stepC = 24 * p.d ∧ (∀ b, nSrc b p.stepC = 2) ∧
      nSeed p.stepC = 1 ∧ nGates p.stepC ≤ 2 * p.prepGates + p.reflGates := by
  obtain ⟨wP, wU, wS, wE, wG⟩ := p.prepC_counts hτ hν
  obtain ⟨rP, rU, rS, rE, rG⟩ := p.rseedC_counts
  obtain ⟨gU, gP, gS, gE⟩ := ofGates_counts (S := Wire p.a p.m p.r p.K)
    (rgoodG (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k) (l := p.l) (f := p.f))
  have hg := p.rgoodG_length
  unfold stepC
  simp only [nPriv_append, nUJ_append, nSrc_append, nSeed_append, nGates_append,
    nPriv_invList, nUJ_invList, nSrc_invList, nSeed_invList, nGates_invList, nGates_ofGates]
  have eN : nGates [OInstr.gate p.negGate] = 1 := rfl
  have eP : nPriv [OInstr.gate p.negGate] = 0 := rfl
  have eU : nUJ [OInstr.gate p.negGate] = 0 := rfl
  have eS : ∀ b, nSrc b [OInstr.gate p.negGate] = 0 := fun _ => rfl
  have eE : nSeed [OInstr.gate p.negGate] = 0 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [gP, wP, rP, eP]; ring
  · rw [gU, wU, rU, eU]; ring
  · intro b; rw [gS b, wS b, rS b, eS b]
  · rw [gE, wE, rE, eE]
  · rw [eN]
    unfold reflGates
    omega

/-- **Exact counts of the trial with `j` amplification steps.** -/
theorem trialC_counts (hτ : 0 ≤ p.tau) (hν : 0 < p.nu) (j : ℕ) :
    nPriv (p.trialC j) = (2 * j + 1) * (6 * p.d) ∧
    nUJ (p.trialC j) = (2 * j + 1) * (12 * p.d) ∧
    (∀ b, nSrc b (p.trialC j) = 2 * j + 1) ∧
    nSeed (p.trialC j) = j ∧
    nGates (p.trialC j) ≤ (2 * j + 1) * p.prepGates + j * p.reflGates := by
  obtain ⟨wP, wU, wS, wE, wG⟩ := p.prepC_counts hτ hν
  obtain ⟨sP, sU, sS, sE, sG⟩ := p.stepC_counts hτ hν
  unfold trialC
  simp only [nPriv_append, nUJ_append, nSrc_append, nSeed_append, nGates_append]
  have rP : nPriv (List.replicate j p.stepC).flatten = j * nPriv p.stepC :=
    countP_replicate_flatten _ j _
  have rU : nUJ (List.replicate j p.stepC).flatten = j * nUJ p.stepC :=
    countP_replicate_flatten _ j _
  have rS : ∀ b, nSrc b (List.replicate j p.stepC).flatten = j * nSrc b p.stepC :=
    fun b => countP_replicate_flatten _ j _
  have rE : nSeed (List.replicate j p.stepC).flatten = j * nSeed p.stepC :=
    countP_replicate_flatten _ j _
  have rG : nGates (List.replicate j p.stepC).flatten = j * nGates p.stepC :=
    countP_replicate_flatten _ j _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [rP, wP, sP]; ring
  · rw [rU, wU, sU]; ring
  · intro b; rw [rS b, wS b, sS b]; ring
  · rw [rE, wE, sE]; ring
  · rw [rG]
    calc nGates p.prepC + j * nGates p.stepC ≤ p.prepGates + j * (2 * p.prepGates + p.reflGates) :=
          Nat.add_le_add wG (Nat.mul_le_mul_left _ sG)
      _ = (2 * j + 1) * p.prepGates + j * p.reflGates := by ring

/-! ### Validity -/

theorem srcMat_unitary (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb) (hT : 0 ≤ p.T) (hB : 0 < p.B) (s : Fin (p.k + 1)) :
    UnitaryMat (p.srcMat s) := by
  cases s using Fin.cases with
  | zero =>
      apply rotC_unitary
      rw [Real.sq_sqrt (div_nonneg hr₀ hB.le), Real.sq_sqrt (div_nonneg (mul_nonneg hT hrb) hB.le),
        ← add_div, div_self hB.ne']
  | succ i => exact hadC_unitary

theorem prepC_valid (hτ : 0 ≤ p.tau) (hν : 0 < p.nu) (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb)
    (hT : 0 ≤ p.T) (hB : 0 < p.B) : ∀ g ∈ p.prepC, g.Valid Wire.anc := by
  have hsrc : ∀ g ∈ ofGates (S := Wire p.a p.m p.r p.K) p.srcPrep, g.Valid Wire.anc :=
    valid_ofGates _ _ (fun g hg => (constT_ok _ _ (p.srcMat_unitary hr₀ hrb hT hB) _ g hg).mono
      (by norm_num))
  have hlch : ∀ g ∈ ofGates (S := Wire p.a p.m p.r p.K) p.lchPrep, g.Valid Wire.anc :=
    valid_ofGates _ _ (fun g hg => (prepT_ok _ lchTS_injective poolList_nodup
      (lchTree_ok p.l_le_pool).disj _ _ g hg).mono (by norm_num))
  have hph : ∀ g ∈ ofGates (S := Wire p.a p.m p.r p.K) p.lchPhase, g.Valid Wire.anc :=
    valid_ofGates _ _ (fun g hg => (ucgT_ok _ lchTS_injective poolList_nodup
      (lchTree_ok p.l_le_pool).disj _ _ _
      (phaseMat_unitary p.l_pos _ (fun w => ODECoherentLCU.norm_coefficientPhase _)) _ g hg).mono
      (by norm_num))
  have hsel : ∀ g ∈ p.select, g.Valid Wire.anc := by
    intro g hg
    simp only [select, List.mem_map] at hg
    obtain ⟨i, hi, rfl⟩ := hg
    exact embI_valid _ i ((sim_public p.a p.tau p.Q p.qbar p.nu hτ hν).1 i hi)
  have hload : ∀ g ∈ p.load, g.Valid Wire.anc := by
    intro g hg
    simp only [load, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> trivial
  intro g hg
  simp only [prepC, List.mem_append] at hg
  rcases hg with ((((h | h) | h) | h) | (h | h) | h)
  · exact hsrc g h
  · exact hlch g h
  · exact hload g h
  · exact hsel g h
  · exact hph g h
  · exact valid_invList _ _ hlch g h
  · exact valid_invList _ _ hsrc g h

theorem stepC_valid (hτ : 0 ≤ p.tau) (hν : 0 < p.nu) (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb)
    (hT : 0 ≤ p.T) (hB : 0 < p.B) : ∀ g ∈ p.stepC, g.Valid Wire.anc := by
  have hW := p.prepC_valid hτ hν hr₀ hrb hT hB
  have hmc : ∀ u, UnitaryMat u → ∀ g ∈ mcGate (zeroLits (a := p.a) (m := p.m) (r := p.r) (K := p.K)
      (k := p.k) (l := p.l) (f := p.f)) poolList (Sum.inr OWire.flg) u, GateOK 2 g :=
    fun u hu => mcGate_valid _ _ _ _ hu poolList_nodup zeroLits_ne_flg
      (fun w hw => by obtain ⟨i, rfl⟩ := (mem_poolList w).mp hw; simp) zeroLits_ne_pool
  have hgood : ∀ g ∈ ofGates (S := Wire p.a p.m p.r p.K) (rgoodG (a := p.a) (m := p.m) (r := p.r)
      (K := p.K) (k := p.k) (l := p.l) (f := p.f)), g.Valid Wire.anc :=
    valid_ofGates _ _ (fun g hg => (hmc zMat zMat_unitary g hg).mono (by norm_num))
  have hflag : ∀ g ∈ ofGates (S := Wire p.a p.m p.r p.K) (flagG (a := p.a) (m := p.m) (r := p.r)
      (K := p.K) (k := p.k) (l := p.l) (f := p.f)), g.Valid Wire.anc :=
    valid_ofGates _ _ (fun g hg => (hmc pauliX pauliX_unitary g hg).mono (by norm_num))
  intro g hg
  simp only [stepC, rseedC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with (((h | h) | ((h | h) | h)) | h) | h
  · exact hgood g h
  · exact valid_invList _ _ hW g h
  · exact hflag g h
  · subst h; show [(Sum.inr OWire.flg, true)].length ≤ 1; simp
  · exact hflag g h
  · exact hW g h
  · subst h
    exact ⟨by simp [negGate], by simp [negGate], negOne_unitary⟩

/-- **Every instruction of every trial is a valid elementary instruction.** -/
theorem trialC_valid (hτ : 0 ≤ p.tau) (hν : 0 < p.nu) (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb)
    (hT : 0 ≤ p.T) (hB : 0 < p.B) (j : ℕ) : ∀ g ∈ p.trialC j, g.Valid Wire.anc := by
  intro g hg
  simp only [trialC, List.mem_append, List.mem_flatten, List.mem_replicate] at hg
  rcases hg with h | ⟨l', ⟨_, rfl⟩, h⟩
  · exact p.prepC_valid hτ hν hr₀ hrb hT hB g h
  · exact p.stepC_valid hτ hν hr₀ hrb hT hB g h

end Params

end

end SparseHamiltonian.GateODE
