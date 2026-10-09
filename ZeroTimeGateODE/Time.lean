import ZeroTimeGateODE.TimeAssembly
import ZeroTimeGateODE.Constant

/-!
# Zero time or a known zero generator: the native solver, time-dependent coefficients

The time-dependent part of Theorem `ode:thm:gates` solves `x' = -G(u) x + b(u)` on a public
uniform mesh of `M = 2^m` slots, through represented samples `G_r = L_r + i H_r` and forcing
samples `b_r`; its exact target is the left-endpoint exponential recurrence
`GateODE.Time.TParams.target`, within the certified discretisation error of `x(T)`.  At `T = 0`
the recurrence is `x(0)`, and for a known zero generator (public bounds `λ_H = λ_D = 0`, so every
represented sample vanishes) it is the left-endpoint quadrature `x(0) + (T/M) ∑_r b_r`
(`ttarget_zero`), which is exactly the source sum `∑_s z_s` of the released source labels
(`zsrc_sum`).  The direct source assembly `tzprepC loadC wpC` (the supplied weight-preparation
circuit, the loading circuit and the inverse weight-preparation circuit) prepares
`(∑_s z_s) / B`, `B` the released source mass (`tz_decoded`).

`native_ode_time_solver_zero`: on every native ODE register with the released pool, the released
protocol `nprotocol (tzprepC loadC wpC) (2g)` (the released ratio `2g` and accuracy `ε/2`) has
valid trials, `|loadC| + 2 |wpC|` gates and exactly `calls(loadC) + 2 calls(wpC)` calls of every
kind per preparation, at most `80 g` times these in every history (no call of a kind that the
supplied circuits do not call) plus `40 g (4 n + 3)` zero-test gates, and the guarantees
`GateNative.NOutcome` against `x(T)` for every instance satisfying the zero-case conditions
`TZInstanceOK` (the released `InstanceOK` without the conditions on `U_J` and on the private
operations, `tzInstanceOK_of`) with `3 ζs ≤ ν`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.ZeroTimeGateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open GateCircuit.Sim (Wire)
open GateODE (OInstr OWire AW goodF Label cfgOf)
open GateODE.Time (TParams TOracles teval trun gens)
open GatePointerEncoding (wordValue wordEquivFin)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-! ### The zero-case target -/

section Target

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

omit [CompleteSpace P] in
/-- The left-endpoint recurrence with step zero stays at the initial state. -/
theorem recurrence_step_zero (Gs : ℕ → P →L[ℂ] P) (bs : ℕ → P) (y0 : P) (n : ℕ) :
    TimeDependentODE.recurrence Gs bs 0 y0 n = y0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [TimeDependentODE.recurrence_succ, ih, zero_smul, zero_smul, add_zero,
        NormedSpace.exp_zero, one_apply_eq_self]

omit [CompleteSpace P] in
/-- With zero samples the left-endpoint recurrence is the left-endpoint quadrature. -/
theorem recurrence_gen_zero (Gs : ℕ → P →L[ℂ] P) (bs : ℕ → P) (h : ℝ) (y0 : P) (n : ℕ)
    (hG : ∀ r < n, Gs r = 0) :
    TimeDependentODE.recurrence Gs bs h y0 n = y0 + h • ∑ r ∈ Finset.range n, bs r := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [TimeDependentODE.recurrence_succ, ih (fun r hr => hG r (Nat.lt_succ_of_lt hr)),
        hG n (Nat.lt_succ_self n), neg_zero, smul_zero, NormedSpace.exp_zero, one_apply_eq_self,
        Finset.sum_range_succ, smul_add, add_assoc]

omit [CompleteSpace P] in
/-- **The zero-case target**: at `T = 0` or with zero samples on every slot the discretised
target is `x₀ + (T/M) ∑_{r < M} b_r` (at `T = 0` this is `x₀`). -/
theorem ttarget_zero (p : TParams) (Hs Ls : ℕ → P →L[ℂ] P) (x0 : P) (bs : ℕ → P)
    (h : p.T = 0 ∨ ∀ r < p.M, gens Hs Ls r = 0) :
    p.target Hs Ls x0 bs = x0 + (p.T / p.M) • ∑ r ∈ Finset.range p.M, bs r := by
  rcases h with hT | hG
  · rw [GateODE.Time.TParams.target, hT, zero_div, recurrence_step_zero, zero_smul, add_zero]
  · exact recurrence_gen_zero _ _ _ _ _ hG

omit [CompleteSpace P] in
/-- **The source sum**: the released source vectors add up to `x₀ + (T/M) ∑_{r < M} b_r`. -/
theorem zsrc_sum (p : TParams) (x0 : P) (bs : ℕ → P) :
    ∑ s, p.zsrc x0 bs s = x0 + (p.T / p.M) • ∑ r ∈ Finset.range p.M, bs r := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  congr 1
  · simp only [GateODE.Time.TParams.zsrc, Bool.false_eq_true, if_false]
    rw [Finset.sum_eq_single (fun _ => false)]
    · simp
    · intro w _ hw
      rw [if_neg hw]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [GateODE.Time.TParams.zsrc, if_true, Complex.coe_smul]
    rw [← Finset.smul_sum]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun q => bs q) p.M]
    exact Fintype.sum_equiv (wordEquivFin p.m) _ _ (fun w => rfl)

/-- **The decoded vector of the time-dependent direct source assembly**: under the released
weight promise and loading promises, `B · goodF† (trun tzrelC seed) = ∑_s z_s`, `B` the released
source mass. -/
theorem tz_decoded (p : TParams) {a m r K l f : ℕ} (hT : 0 ≤ p.T) (v : P)
    (σ : TOracles a p.m l P) (x0 : P) (bs : ℕ → P) (hB : 0 < p.mass x0 bs)
    (hW : ∀ w : Cfg (Fin (p.m + 1)),
      σ.Wp w (fun _ => false) = ((p.srcAmp x0 bs (w 0, Fin.tail w) : ℝ) : ℂ))
    (hinit : x0 ≠ 0 → σ.J (false, fun _ => false) v = unitDirection x0)
    (hforce : ∀ w : Fin p.m → Bool, bs (wordValue w) ≠ 0 →
      σ.J (true, w) v = unitDirection (bs (wordValue w))) :
    p.mass x0 bs • (goodF†) (trun (a := a) (m := m) (r := r) (K := K) (l := l) (f := f) v σ tzrelC
      (GateODE.seedState v)) = ∑ s, p.zsrc x0 bs s := by
  have hPrep : ∀ s, p.zsrc x0 bs s ≠ 0 → σ.J s v = unitDirection (p.zsrc x0 bs s) := by
    intro s hs
    obtain ⟨c, w⟩ := s
    cases c
    · by_cases hw : w = (fun _ => false)
      · subst hw
        have hx : x0 ≠ 0 := by
          intro h0
          apply hs
          simp [GateODE.Time.TParams.zsrc, h0]
        simp only [GateODE.Time.TParams.zsrc, Bool.false_eq_true, if_false, if_true]
        exact hinit hx
      · exfalso
        apply hs
        simp [GateODE.Time.TParams.zsrc, hw]
    · have hb : bs (wordValue w) ≠ 0 := by
        intro h0
        apply hs
        simp [GateODE.Time.TParams.zsrc, h0]
      have hM0 : 0 ≤ p.T / p.M := div_nonneg hT (Nat.cast_nonneg _)
      have hM : 0 < p.T / p.M := by
        rcases eq_or_lt_of_le hM0 with h0 | h0
        · exfalso
          apply hs
          simp only [GateODE.Time.TParams.zsrc, if_true, ← h0, Complex.ofReal_zero, zero_smul]
        · exact h0
      simp only [GateODE.Time.TParams.zsrc, if_true]
      rw [hforce w hb, Complex.coe_smul, ODEHeraldedSuccess.unitDirection_pos_smul _ hM]
  rw [tzrelC_decoded]
  have hsum : ∑ c : Cfg (Fin (p.m + 1)),
      (star (σ.Wp c (fun _ => false)) * σ.Wp c (fun _ => false)) • σ.J (c 0, Fin.tail c) v =
      ∑ s : Bool × (Fin p.m → Bool), ((p.srcAmp x0 bs s ^ 2 : ℝ) : ℂ) • σ.J s v := by
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (p.m + 1) => Bool))
      (fun s => ((p.srcAmp x0 bs s ^ 2 : ℝ) : ℂ) • σ.J s v)
      (fun c => (star (σ.Wp c (fun _ => false)) * σ.Wp c (fun _ => false)) •
        σ.J (c 0, Fin.tail c) v)]
    intro s
    obtain ⟨b, t⟩ := s
    have h0 : (Fin.consEquiv (fun _ : Fin (p.m + 1) => Bool)) (b, t) 0 = b := rfl
    have ht : Fin.tail ((Fin.consEquiv (fun _ : Fin (p.m + 1) => Bool)) (b, t)) = t := rfl
    rw [hW, h0, ht, RCLike.star_def, Complex.conj_ofReal]
    push_cast
    ring_nf
  rw [hsum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [GateODE.Time.TParams.srcAmp_sq p x0 bs hB s, Complex.coe_smul, smul_smul,
    mul_div_cancel₀ _ hB.ne']
  by_cases hz : p.zsrc x0 bs s = 0
  · rw [hz, norm_zero, zero_smul]
  · rw [hPrep s hz, unitDirection, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz),
      one_smul]

end Target

/-! ### Instance conditions in the zero case -/

section Instance

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **The conditions on an instance in the time-dependent zero case**: the released
`GateODE.Time.TParams.InstanceOK` without the conditions on `U_J` and on the private operations
(`SelectHypT.uj`, `priv`, `clock`) and without the unused `SelectHypT.selfL`: the represented
samples (self-adjoint `H_r`, `L_r ≥ 0`, `‖H_r‖ ≤ λ_H`, `‖L_r‖ ≤ λ_D` on every slot), the
supplied loading `Jl` and weight preparation `Wp` (unitary, with the released promises), the
solution with the regularity and sampling bounds, a nonzero final state, `B ≤ g ‖x(T)‖` and the
discretisation budget. -/
structure TZInstanceOK (p : TParams) (v : P) (Jl : Bool × (Fin p.m → Bool) → P →L[ℂ] P)
    (Wp : Matrix (Cfg (Fin (p.m + 1))) (Cfg (Fin (p.m + 1))) ℂ) (Hs Ls : ℕ → P →L[ℂ] P)
    (G : ℝ → P →L[ℂ] P) (b x : ℝ → P) (bs : ℕ → P) (βG δG βb δb bmax : ℝ) : Prop where
  selfH : ∀ r < p.M, star (Hs r) = Hs r
  normH : ∀ r < p.M, ‖Hs r‖ ≤ p.lamH
  normL : ∀ r < p.M, ‖Ls r‖ ≤ p.lamD
  psd : ∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (Ls r w)).re
  load_unitary : ∀ s, IsUnitary (Jl s)
  prep_left : Wp.conjTranspose * Wp = 1
  prep_right : Wp * Wp.conjTranspose = 1
  prep : ∀ w : Cfg (Fin (p.m + 1)),
    Wp w (fun _ => false) = ((p.srcAmp (x 0) bs (w 0, Fin.tail w) : ℝ) : ℂ)
  init_load : x 0 ≠ 0 → Jl (false, fun _ => false) v = unitDirection (x 0)
  forcing_load : ∀ w : Fin p.m → Bool, bs (wordValue w) ≠ 0 →
    Jl (true, w) v = unitDirection (bs (wordValue w))
  solves : TimeDependentODE.SolvesODE G b x 0 p.T
  accretive : ∀ u ∈ Set.Icc 0 p.T, TimeDependentODE.Accretive (G u)
  lipG : ∀ u ∈ Set.Icc 0 p.T, ∀ u' ∈ Set.Icc 0 p.T, ‖G u - G u'‖ ≤ βG * |u - u'|
  sampleG : ∀ r < p.M, ‖G (r * p.T / p.M) - gens Hs Ls r‖ ≤ δG
  lipb : ∀ u ∈ Set.Icc 0 p.T, ∀ u' ∈ Set.Icc 0 p.T, ‖b u - b u'‖ ≤ βb * |u - u'|
  sampleb : ∀ r < p.M, ‖b (r * p.T / p.M) - bs r‖ ≤ δb
  boundb : ∀ u ∈ Set.Icc 0 p.T, ‖b u‖ ≤ bmax
  βG_nonneg : 0 ≤ βG
  βb_nonneg : 0 ≤ βb
  target_ne : x p.T ≠ 0
  budget : p.mass (x 0) bs ≤ p.g * ‖x p.T‖
  disc : p.discretisation βG δG βb δb bmax ‖x 0‖ ≤ p.ε * p.mass (x 0) bs / (2000 * p.g)

/-- The released instance conditions imply the zero-case conditions. -/
theorem tzInstanceOK_of {p : TParams} {v : P} {σ : TOracles p.a p.m p.l P}
    {Hs Ls : ℕ → P →L[ℂ] P} {G : ℝ → P →L[ℂ] P} {b x : ℝ → P} {bs : ℕ → P}
    {βG δG βb δb bmax : ℝ} (hI : p.InstanceOK v σ Hs Ls G b x bs βG δG βb δb bmax) :
    TZInstanceOK p v σ.J σ.Wp Hs Ls G b x bs βG δG βb δb bmax :=
  ⟨hI.select.selfH, hI.select.normH, hI.select.normL, hI.psd, hI.load_unitary, hI.prep_left,
    hI.prep_right, hI.prep, hI.init_load, hI.forcing_load, hI.solves, hI.accretive, hI.lipG,
    hI.sampleG, hI.lipb, hI.sampleb, hI.boundb, hI.βG_nonneg, hI.βb_nonneg, hI.target_ne,
    hI.budget, hI.disc⟩

omit [CompleteSpace P] in
/-- In the zero case of the public data the represented samples vanish on every slot, or
`T = 0`. -/
theorem tzero_samples (p : TParams) (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1)
    (hlamH : 0 ≤ p.lamH) (hlamD : 0 ≤ p.lamD) (hz : p.T = 0 ∨ p.lamH + p.R * p.lamD = 0)
    (Hs Ls : ℕ → P →L[ℂ] P) (hH : ∀ r < p.M, ‖Hs r‖ ≤ p.lamH) (hL : ∀ r < p.M, ‖Ls r‖ ≤ p.lamD) :
    p.T = 0 ∨ ∀ r < p.M, gens Hs Ls r = 0 := by
  rcases hz with h | h
  · exact Or.inl h
  · right
    have hR : 0 < p.R := GateODE.AnalyticLCHS.radius_pos (p.ratio_ge hg) (p.acc_pos hε)
      (p.acc_le_one hεOne)
    have h2 : 0 ≤ p.R * p.lamD := mul_nonneg hR.le hlamD
    have h3 : p.lamH = 0 := by linarith
    have h4 : p.lamD = 0 := by
      rw [h3, zero_add] at h
      rcases mul_eq_zero.mp h with h5 | h5
      · exact absurd h5 hR.ne'
      · exact h5
    intro r hr
    have e1 : Hs r = 0 := norm_le_zero_iff.mp (h3 ▸ hH r hr)
    have e2 : Ls r = 0 := norm_le_zero_iff.mp (h4 ▸ hL r hr)
    rw [gens, e1, e2, smul_zero, add_zero]

end Instance

/-! ### The solver -/

section Main

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

/-- **The guarantees for one instance of the time-dependent zero case.** -/
theorem native_time_zero_outcome (p : TParams) (a m r K l f bT bP A : ℕ) (hT : 0 ≤ p.T)
    (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεHalf : p.ε ≤ 1 / 2) (hlamH : 0 ≤ p.lamH)
    (hlamD : 0 ≤ p.lamD) (hz : p.T = 0 ∨ p.lamH + p.R * p.lamD = 0)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid)
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (Jl : Bool × (Fin p.m → Bool) → Reg S ℂ →L[ℂ] Reg S ℂ)
    (Wp : Matrix (Cfg (Fin (p.m + 1))) (Cfg (Fin (p.m + 1))) ℂ)
    (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
    (bs : ℕ → Reg S ℂ) (βG δG βb δb bmax ζs : ℝ) (hprim : ∀ j, IsUnitary (prim j))
    (hζs : 0 ≤ ζs) (hload : ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun prim wpC) (liftB (matOp Wp)) ζs) (hbudget : 3 * ζs ≤ p.nu)
    (hI : TZInstanceOK p (seedV (S := S)) Jl Wp Hs Ls G b x bs βG δG βb δb bmax) :
    NOutcome (tzprepC loadC wpC : List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J))
      p.ratio p.ε (p.ratio_ge hg) prim (x p.T) := by
  have hεOne : p.ε ≤ 1 := hεHalf.trans (by norm_num)
  have hprepV := tzprepC_valid (a := a) (m := m) (r := r) (K := K) (k := p.m) (l := l) (f := f)
    (nP := zPool a m r K p.m l f S Zs Z bT bP A) (Z := Z) (bT := bT) (bP := bP) (A := A)
    loadC hloadV wpC hwpV
  let σ : TOracles a p.m l (Reg S ℂ) := ⟨1, fun _ _ => 1, Jl, Wp⟩
  have hσ : σ.Unitary m := ⟨isUnitary_one, fun _ _ _ => isUnitary_one, hI.load_unitary,
    hI.prep_left, hI.prep_right⟩
  have hA := tzprepC_approx (a := a) (m := m) (r := r) (K := K) (k := p.m) (l := l) (f := f)
    (nP := zPool a m r K p.m l f S Zs Z bT bP A) (Z := Z) (bT := bT) (bP := bP) (A := A) prim hprim
    loadC hloadV wpC hwpV seedV σ hσ hζs hload hwp
  -- the target
  have hzero := tzero_samples p hg hε hεOne hlamH hlamD hz Hs Ls hI.normH hI.normL
  have hy : p.target Hs Ls (x 0) bs = ∑ s, p.zsrc (x 0) bs s := by
    rw [ttarget_zero p Hs Ls (x 0) bs hzero, zsrc_sum]
  have hErr := p.discretisation_error hT G b x Hs Ls bs βG δG βb δb bmax hI.βG_nonneg
    hI.βb_nonneg hI.solves hI.accretive hI.lipG hI.sampleG hI.lipb hI.sampleb hI.boundb hI.selfH
    hI.psd hI.normH hI.normL
  obtain ⟨hy0, hbud, hdirY⟩ := TimeDependentODE.Sampling.target_budget (x p.T)
    (p.target Hs Ls (x 0) bs) (p.mass (x 0) bs) p.g p.ε _ hg hε hεOne hI.target_ne hI.budget hErr
    hI.disc
  have hNorm := p.target_norm_le hT Hs Ls hI.selfH hI.psd (x 0) bs
  have hB : 0 < p.mass (x 0) bs := (norm_pos_iff.mpr hy0).trans_le hNorm
  -- the decoded vector
  have hrel := tz_decoded p (a := a) (m := m) (r := r) (K := K) (l := l) (f := f) hT seedV σ
    (x 0) bs hB hI.prep hI.init_load hI.forcing_load
  rw [← hy] at hrel
  have hν : 0 < p.nu := p.nu_pos hg hε
  have hacc : p.acc ≤ 1 / 2 := by
    simp only [GateODE.Time.TParams.acc]
    linarith
  generalize trun (a := a) (m := m) (r := r) (K := K) (l := l) (f := f) seedV σ tzrelC = Urel
    at hA hrel
  have hvec := vector_error_direct (nrun prim (tzprepC loadC wpC :
    List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J))) Urel hA (p.target Hs Ls (x 0) bs)
    (p.mass (x 0) bs) hB.le hrel
  have hvec' : ‖p.mass (x 0) bs • (goodN†) (nrun prim (tzprepC loadC wpC :
      List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J)) sN) - p.target Hs Ls (x 0) bs‖ ≤
      2 * ImprovedODEQueryBudget.precision p.ratio p.acc * p.mass (x 0) bs := by
    refine hvec.trans ?_
    have e : p.nu = ImprovedODEQueryBudget.precision p.ratio p.acc := rfl
    nlinarith
  have hbud' : p.mass (x 0) bs ≤ p.ratio * ‖p.target Hs Ls (x 0) bs‖ := hbud
  have e : p.acc / 500 + p.ε / 1000 = p.ε / 500 := by
    simp only [GateODE.Time.TParams.acc]
    ring
  exact noutcome_direct_retarget (Nat.le_succ _)
    (tzprepC loadC wpC : List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J)) prim hprim
    hprepV (tzprepC_pres loadC wpC prim) (p.target Hs Ls (x 0) bs) (x p.T) (p.mass (x 0) bs)
    p.ratio p.ε p.acc (p.ε / 1000) hy0 hI.target_ne (p.ratio_ge hg) hε (p.acc_pos hε) hacc hB
    hbud' hvec' hdirY e.le

/-- **Zero time or a known zero generator, native gates, time-dependent coefficients** (remark
of Theorem `ode:thm:gates`, time-dependent part: direct source assembly, no matrix calls).

For time-dependent public data `p` with `T ≥ 0`, `g ≥ 1`, `0 < ε ≤ 1/2`, `λ_H, λ_D ≥ 0` and
`T = 0 ∨ λ_H + R λ_D = 0`, and on every native ODE register `ZNW a m r K p.m l f …` whose
source-label word has the `p.m` mesh bits, the released protocol `nprotocol (tzprepC loadC wpC)
(2g)` has valid trials; one preparation uses `|loadC| + 2 |wpC|` elementary gates and exactly
`calls_q(loadC) + 2 calls_q(wpC)` calls of every kind `q`; in every history the protocol uses
at most `40 · 2g` times these per preparation, plus `20 · 2g (4 n + 3)` zero-test gates, and makes
no call of a kind that the supplied circuits do not call.  For every instance with unitary
primitive oracles, loading and weight-preparation circuits within `ζs` of the supplied `J` and
`Wp`, `3 ζs ≤ ν` and the zero-case conditions `TZInstanceOK` (the released instance conditions
without those on `U_J` and the private operations), the protocol has the guarantees `NOutcome`
against `x(T)`. -/
theorem native_ode_time_solver_zero (p : TParams) (a m r K l f bT bP A : ℕ) (hT : 0 ≤ p.T)
    (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεHalf : p.ε ≤ 1 / 2) (hlamH : 0 ≤ p.lamH)
    (hlamD : 0 ≤ p.lamD) (hz : p.T = 0 ∨ p.lamH + p.R * p.lamD = 0)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, ∀ i ∈ trialN (tzprepC loadC wpC :
      List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J)) j, i.Valid) ∧
    nGatesN (tzprepC loadC wpC : List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J)) =
      nGatesN loadC + 2 * nGatesN wpC ∧
    (∀ q : J → Bool, nCallsN q (tzprepC loadC wpC :
      List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J)) =
      nCallsN q loadC + 2 * nCallsN q wpC) ∧
    ((nprotocol (tzprepC loadC wpC : List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J))
        p.ratio (p.ratio_ge hg)).worstCost wGateN : ℝ) ≤
      40 * p.ratio * (nGatesN loadC + 2 * nGatesN wpC : ℕ) +
        20 * p.ratio * (4 * (Fintype.card (AW a m r K p.m l f) + Fintype.card (XW Z bT bP A) +
          Fintype.card Zs + Fintype.card S) + 3) ∧
    (∀ q : J → Bool, ((nprotocol (tzprepC loadC wpC :
        List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J)) p.ratio
          (p.ratio_ge hg)).worstCost (wCallN q) : ℝ) ≤
      40 * p.ratio * (nCallsN q loadC + 2 * nCallsN q wpC : ℕ)) ∧
    (∀ q : J → Bool, nCallsN q loadC = 0 → nCallsN q wpC = 0 →
      (nprotocol (tzprepC loadC wpC : List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J))
        p.ratio (p.ratio_ge hg)).worstCost (wCallN q) = 0) ∧
    Fintype.card (ZNW a m r K p.m l f S Zs Z bT bP A) =
      Fintype.card S + 2 * (Fintype.card (AW a m r K p.m l f) +
        (Fintype.card Z + bT + bP + A + 3) + Fintype.card Zs) + Fintype.card S + 1 ∧
    ∀ (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (Jl : Bool × (Fin p.m → Bool) → Reg S ℂ →L[ℂ] Reg S ℂ)
      (Wp : Matrix (Cfg (Fin (p.m + 1))) (Cfg (Fin (p.m + 1))) ℂ)
      (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
      (bs : ℕ → Reg S ℂ) (βG δG βb δb bmax ζs : ℝ),
      (∀ j, IsUnitary (prim j)) →
      0 ≤ ζs →
      ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun prim wpC) (liftB (matOp Wp)) ζs →
      3 * ζs ≤ p.nu →
      TZInstanceOK p (seedV (S := S)) Jl Wp Hs Ls G b x bs βG δG βb δb bmax →
      NOutcome (tzprepC loadC wpC : List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J))
        p.ratio p.ε (p.ratio_ge hg) prim (x p.T) := by
  have hprepV := tzprepC_valid (a := a) (m := m) (r := r) (K := K) (k := p.m) (l := l) (f := f)
    (nP := zPool a m r K p.m l f S Zs Z bT bP A) (Z := Z) (bT := bT) (bP := bP) (A := A)
    loadC hloadV wpC hwpV
  have hcount := fun q => tzprepC_counts (a := a) (m := m) (r := r) (K := K) (k := p.m) (l := l)
    (f := f) (nP := zPool a m r K p.m l f S Zs Z bT bP A) (Z := Z) (bT := bT) (bP := bP) (A := A)
    loadC wpC q
  have hworst := fun q => nprotocol_worst (tzprepC loadC wpC :
    List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J)) p.ratio (p.ratio_ge hg) q
  refine ⟨fun j => trialN_valid _ hprepV j, (hcount (fun _ => true)).1, fun q => (hcount q).2,
    ?_, ?_, ?_, card_ZNW a m r K p.m l f bT bP A, ?_⟩
  · have h := (hworst (fun _ => true)).1
    rw [(hcount (fun _ => true)).1] at h
    exact h
  · intro q
    have h := (hworst q).2
    rw [(hcount q).2] at h
    exact h
  · intro q h0 h1
    have h := (hworst q).2
    rw [(hcount q).2, h0, h1] at h
    have h' : ((nprotocol (tzprepC loadC wpC :
        List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J)) p.ratio
          (p.ratio_ge hg)).worstCost (wCallN q) : ℝ) ≤ 0 := by simpa using h
    exact_mod_cast le_antisymm h' (Nat.cast_nonneg _)
  · intro prim Jl Wp Hs Ls G b x bs βG δG βb δb bmax ζs hprim hζs hload hwp hbudget hI
    exact native_time_zero_outcome p a m r K l f bT bP A hT hg hε hεHalf hlamH hlamD hz loadC
      hloadV wpC hwpV prim Jl Wp Hs Ls G b x bs βG δG βb δb bmax ζs hprim hζs hload hwp hbudget hI

end Main

end

end SparseHamiltonian.ZeroTimeGateODE
