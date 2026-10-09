import GateEfficientODE.Time.Trial
import GateEfficientTimeDependent.Theorem
import GateEfficientODE.Circuit.Counts

/-!
# Validity and exact counts of the time-dependent trial circuits

`prepC` makes exactly `6d` slot-selected private calls, `12d` calls of `U_J`
or `U_J†`, one call of the source loading, two calls of the weight
preparation (forward and inverse) and at most

`prepGates = 200 (d + 1)(a + m + r + 1) + 3 · 2^l (2l + 1)`

elementary gates.  One step adds the two reflections, one seed reflection
and the sign, with at most `reflGates = 6 nz + 4` gates, where
`nz = card (Wire a m r K) + 1 + m + l`.  The trial with `j` steps has exactly
`(2j+1) 6d` private calls, `(2j+1) 12d` calls of `U_J` or `U_J†`, `2j+1`
loading calls, `2 (2j+1)` weight-preparation calls, `j` seed reflections, and
at most `(2j+1) prepGates + j reflGates` gates (`trialC_counts`).  Every
instruction is valid (`trialC_valid`).  These facts need only the public
mesh condition `steps tau (nu/3) ≤ 2^m`.
-/

namespace SparseHamiltonian.GateODE.Time

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire zMat zMat_unitary negOne_unitary)
open scoped InnerProduct BigOperators

namespace TParams

variable (p : TParams)

/-- The number of zero-test literals. -/
abbrev nz : ℕ := Fintype.card (Wire p.a p.m p.r p.K) + 1 + p.m + p.l

/-- The gate budget of one preparation. -/
def prepGates : ℕ :=
  200 * (p.d + 1) * (p.a + p.m + p.r + 1) + 3 * (2 ^ p.l * (2 * p.l + 1))

/-- The gate budget of the reflections and the sign of one step. -/
def reflGates : ℕ := 6 * p.nz + 4

theorem select_counts (hτ : 0 ≤ p.tau) (hν : 0 < p.nu)
    (hm : TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m) :
    nPriv p.select = 6 * p.d ∧ nUJ p.select = 12 * p.d ∧ (∀ b, nSrc b p.select = 0) ∧
      nSeed p.select = 0 ∧
      nGates p.select ≤ 200 * (p.d + 1) * (p.a + p.m + p.r + 1) := by
  obtain ⟨_, hP, hU, hG⟩ := SlotSim.simCircuitT_public p.a p.m p.tau p.Q p.qbar p.nu hτ hν hm
  obtain ⟨eG, eU, eP, eS, eE⟩ := embI_counts (O := OWire p.m p.l p.f)
    (SlotSim.simCircuitT p.a p.tau p.Q p.qbar p.nu p.m)
  refine ⟨?_, ?_, eS, eE, ?_⟩
  · unfold select; rw [eP, hP]
  · unfold select; rw [eU, hU]
  · unfold select; rw [eG]; exact hG

theorem lchPrep_length : p.lchPrep.length ≤ 2 ^ p.l * (2 * p.l + 1) := prepT_length_le _ _

theorem lchPhase_length : p.lchPhase.length ≤ 2 ^ p.l * (2 * p.l + 1) := phaseT_length _ _ _

theorem prepC_counts (hτ : 0 ≤ p.tau) (hν : 0 < p.nu)
    (hm : TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m) :
    nPriv p.prepC = 6 * p.d ∧ nUJ p.prepC = 12 * p.d ∧ nSrc false p.prepC = 1 ∧
      nSrc true p.prepC = 2 ∧ nSeed p.prepC = 0 ∧ nGates p.prepC ≤ p.prepGates := by
  obtain ⟨sP, sU, sS, sE, sG⟩ := p.select_counts hτ hν hm
  obtain ⟨g2U, g2P, g2S, g2E⟩ := ofGates_counts (S := Wire p.a p.m p.r p.K) p.lchPrep
  obtain ⟨g3U, g3P, g3S, g3E⟩ := ofGates_counts (S := Wire p.a p.m p.r p.K) p.lchPhase
  have h2 := p.lchPrep_length
  have h3 := p.lchPhase_length
  unfold prepC
  simp only [nPriv_append, nUJ_append, nSrc_append, nSeed_append, nGates_append,
    nPriv_invList, nUJ_invList, nSrc_invList, nSeed_invList, nGates_invList, nGates_ofGates]
  have lP : nPriv p.load = 0 := rfl
  have lU : nUJ p.load = 0 := rfl
  have lF : nSrc false p.load = 1 := rfl
  have lT : nSrc true p.load = 0 := rfl
  have lE : nSeed p.load = 0 := rfl
  have lG : nGates p.load = 0 := rfl
  have wP : nPriv p.wprepC = 0 := rfl
  have wU : nUJ p.wprepC = 0 := rfl
  have wF : nSrc false p.wprepC = 0 := rfl
  have wT : nSrc true p.wprepC = 1 := rfl
  have wE : nSeed p.wprepC = 0 := rfl
  have wG : nGates p.wprepC = 0 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [wP, g2P, g3P, lP, sP]; omega
  · rw [wU, g2U, g3U, lU, sU]; omega
  · rw [wF, g2S false, g3S false, lF, sS false]
  · rw [wT, g2S true, g3S true, lT, sS true]
  · rw [wE, g2E, g3E, lE, sE]
  · rw [wG, lG]
    unfold prepGates
    omega

theorem rgoodG_length : (rgoodG (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m) (l := p.l)
    (f := p.f)).length ≤ 2 * p.nz + 1 := by
  have h := mcGate_length_le (zeroLits (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m)
    (l := p.l) (f := p.f)) poolList (Sum.inr OWire.flg) zMat
  rw [zeroLits_length] at h
  exact h

theorem flagG_length : (flagG (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m) (l := p.l)
    (f := p.f)).length ≤ 2 * p.nz + 1 := by
  have h := mcGate_length_le (zeroLits (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m)
    (l := p.l) (f := p.f)) poolList (Sum.inr OWire.flg) pauliX
  rw [zeroLits_length] at h
  exact h

theorem rseedC_counts :
    nPriv (rseedC (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m) (l := p.l)
      (f := p.f)) = 0 ∧
    nUJ (rseedC (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m) (l := p.l) (f := p.f)) = 0 ∧
    (∀ b, nSrc b (rseedC (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m) (l := p.l)
      (f := p.f)) = 0) ∧
    nSeed (rseedC (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m) (l := p.l)
      (f := p.f)) = 1 ∧
    nGates (rseedC (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m) (l := p.l)
      (f := p.f)) ≤ 2 * (2 * p.nz + 1) := by
  obtain ⟨gU, gP, gS, gE⟩ := ofGates_counts (S := Wire p.a p.m p.r p.K)
    (flagG (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m) (l := p.l) (f := p.f))
  have hl := p.flagG_length
  unfold rseedC
  simp only [nPriv_append, nUJ_append, nSrc_append, nSeed_append, nGates_append, nGates_ofGates]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [gP]; rfl
  · rw [gU]; rfl
  · intro b; rw [gS b]; rfl
  · rw [gE]; rfl
  · have e : nGates [OInstr.seed (S := Wire p.a p.m p.r p.K) [(Sum.inr (OWire.flg (k := p.m)
        (l := p.l) (f := p.f)), true)]] = 0 := rfl
    rw [e]
    omega

theorem stepC_counts (hτ : 0 ≤ p.tau) (hν : 0 < p.nu)
    (hm : TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m) :
    nPriv p.stepC = 12 * p.d ∧ nUJ p.stepC = 24 * p.d ∧ nSrc false p.stepC = 2 ∧
      nSrc true p.stepC = 4 ∧ nSeed p.stepC = 1 ∧
      nGates p.stepC ≤ 2 * p.prepGates + p.reflGates := by
  obtain ⟨wP, wU, wF, wT, wE, wG⟩ := p.prepC_counts hτ hν hm
  obtain ⟨rP, rU, rS, rE, rG⟩ := p.rseedC_counts
  obtain ⟨gU, gP, gS, gE⟩ := ofGates_counts (S := Wire p.a p.m p.r p.K)
    (rgoodG (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m) (l := p.l) (f := p.f))
  have hg := p.rgoodG_length
  unfold stepC
  simp only [nPriv_append, nUJ_append, nSrc_append, nSeed_append, nGates_append,
    nPriv_invList, nUJ_invList, nSrc_invList, nSeed_invList, nGates_invList, nGates_ofGates]
  have eN : nGates [OInstr.gate p.negGate] = 1 := rfl
  have eP : nPriv [OInstr.gate p.negGate] = 0 := rfl
  have eU : nUJ [OInstr.gate p.negGate] = 0 := rfl
  have eS : ∀ b, nSrc b [OInstr.gate p.negGate] = 0 := fun _ => rfl
  have eE : nSeed [OInstr.gate p.negGate] = 0 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gP, wP, rP, eP]; ring
  · rw [gU, wU, rU, eU]; ring
  · rw [gS false, wF, rS false, eS false]
  · rw [gS true, wT, rS true, eS true]
  · rw [gE, wE, rE, eE]
  · rw [eN]
    unfold reflGates
    omega

/-- **Exact counts of the trial with `j` amplification steps.** -/
theorem trialC_counts (hτ : 0 ≤ p.tau) (hν : 0 < p.nu)
    (hm : TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m) (j : ℕ) :
    nPriv (p.trialC j) = (2 * j + 1) * (6 * p.d) ∧
    nUJ (p.trialC j) = (2 * j + 1) * (12 * p.d) ∧
    nSrc false (p.trialC j) = 2 * j + 1 ∧
    nSrc true (p.trialC j) = 2 * (2 * j + 1) ∧
    nSeed (p.trialC j) = j ∧
    nGates (p.trialC j) ≤ (2 * j + 1) * p.prepGates + j * p.reflGates := by
  obtain ⟨wP, wU, wF, wT, wE, wG⟩ := p.prepC_counts hτ hν hm
  obtain ⟨sP, sU, sF, sT, sE, sG⟩ := p.stepC_counts hτ hν hm
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rP, wP, sP]; ring
  · rw [rU, wU, sU]; ring
  · rw [rS false, wF, sF]; ring
  · rw [rS true, wT, sT]; ring
  · rw [rE, wE, sE]; ring
  · rw [rG]
    calc nGates p.prepC + j * nGates p.stepC ≤ p.prepGates + j * (2 * p.prepGates + p.reflGates) :=
          Nat.add_le_add wG (Nat.mul_le_mul_left _ sG)
      _ = (2 * j + 1) * p.prepGates + j * p.reflGates := by ring

/-! ### Validity -/

theorem prepC_valid (hτ : 0 ≤ p.tau) (hν : 0 < p.nu)
    (hm : TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m) : ∀ g ∈ p.prepC, g.Valid Wire.anc := by
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
    exact embI_valid _ i ((SlotSim.simCircuitT_public p.a p.m p.tau p.Q p.qbar p.nu hτ hν hm).1 i hi)
  have hload : ∀ g ∈ p.load, g.Valid Wire.anc := by
    intro g hg
    simp only [load, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    trivial
  have hwp : ∀ g ∈ p.wprepC, g.Valid Wire.anc := by
    intro g hg
    simp only [wprepC, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    trivial
  intro g hg
  simp only [prepC, List.mem_append] at hg
  rcases hg with ((((h | h) | h) | h) | (h | h) | h)
  · exact hwp g h
  · exact hlch g h
  · exact hload g h
  · exact hsel g h
  · exact hph g h
  · exact valid_invList _ _ hlch g h
  · exact valid_invList _ _ hwp g h

theorem stepC_valid (hτ : 0 ≤ p.tau) (hν : 0 < p.nu)
    (hm : TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m) : ∀ g ∈ p.stepC, g.Valid Wire.anc := by
  have hW := p.prepC_valid hτ hν hm
  have hmc : ∀ u, UnitaryMat u → ∀ g ∈ mcGate (zeroLits (a := p.a) (m := p.m) (r := p.r)
      (K := p.K) (k := p.m) (l := p.l) (f := p.f)) poolList (Sum.inr OWire.flg) u, GateOK 2 g :=
    fun u hu => mcGate_valid _ _ _ _ hu poolList_nodup zeroLits_ne_flg
      (fun w hw => by obtain ⟨i, rfl⟩ := (mem_poolList w).mp hw; simp) zeroLits_ne_pool
  have hgood : ∀ g ∈ ofGates (S := Wire p.a p.m p.r p.K) (rgoodG (a := p.a) (m := p.m)
      (r := p.r) (K := p.K) (k := p.m) (l := p.l) (f := p.f)), g.Valid Wire.anc :=
    valid_ofGates _ _ (fun g hg => (hmc zMat zMat_unitary g hg).mono (by norm_num))
  have hflag : ∀ g ∈ ofGates (S := Wire p.a p.m p.r p.K) (flagG (a := p.a) (m := p.m)
      (r := p.r) (K := p.K) (k := p.m) (l := p.l) (f := p.f)), g.Valid Wire.anc :=
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
theorem trialC_valid (hτ : 0 ≤ p.tau) (hν : 0 < p.nu)
    (hm : TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m) (j : ℕ) :
    ∀ g ∈ p.trialC j, g.Valid Wire.anc := by
  intro g hg
  simp only [trialC, List.mem_append, List.mem_flatten, List.mem_replicate] at hg
  rcases hg with h | ⟨l', ⟨_, rfl⟩, h⟩
  · exact p.prepC_valid hτ hν hm g h
  · exact p.stepC_valid hτ hν hm g h

end TParams

end

end SparseHamiltonian.GateODE.Time
