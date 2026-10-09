import GateEfficientODE.Time.Select

/-!
# LCHS, source quadrature and discretisation of the time-dependent solver

The represented slot generators are `G_r = L_r + i H_r` (`gens`), and the
exact target of the circuit is the left-endpoint exponential recurrence
`y_{r+1} = exp (-(T/2^m) G_r)(y_r + (T/2^m) b_r)` of
`TimeDependentODE.recurrence`.

* Above the real axis every ordered product family grows at most like
  `exp (T λD Im z)` (`productFamily_norm_le_exp`), so the released analytic
  Gaussian grid certifies all branches at once: for every source label `s`
  the padded LCHS sum of the branch evolutions is within `2 ν` of the masked
  propagator `propS s` of the recurrence (`lchs_error`).
* The masked propagators applied to the source vectors sum exactly to the
  recurrence (`source_sum`), whose norm is at most the source mass
  (`target_norm_le`).
* For a Lipschitz generator and forcing with sampled values, the recurrence
  is within the certified error `discretisation` of every solution of
  `x' = -G(u) x + b(u)` (`discretisation_error`).
-/

namespace SparseHamiltonian.GateODE.Time

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GatePointerEncoding (wordValue wordValue_lt_pow wordEquivFin)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Growth of ordered product families -/

/-- Above the real axis the ordered product of the complex-frequency slot
evolutions grows at most like `exp ((∑ τ) λ Im z)`. -/
theorem productFamily_norm_le_exp (Hs Ls : ℕ → P →L[ℂ] P) (τ : ℕ → ℝ) (lam : ℝ) (n : ℕ)
    (hH : ∀ r < n, star (Hs r) = Hs r) (hL : ∀ r < n, star (Ls r) = Ls r)
    (hLn : ∀ r < n, ‖Ls r‖ ≤ lam) (hτ : ∀ r < n, 0 ≤ τ r) (z : ℂ) (hz : 0 ≤ z.im) :
    ‖TimeDependentODE.GaussianLCHS.productFamily Hs Ls τ n z‖ ≤
      Real.exp ((∑ r ∈ Finset.range n, τ r) * (lam * z.im)) := by
  induction n with
  | zero =>
      rw [TimeDependentODE.GaussianLCHS.productFamily_zero, Finset.sum_range_zero, zero_mul,
        Real.exp_zero]
      exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
      rw [TimeDependentODE.GaussianLCHS.productFamily_succ, Finset.sum_range_succ, add_mul,
        Real.exp_add]
      have h1 := AnalyticLCHS.evolution_norm_le_exp (Ls n) (Hs n) (hL n (by omega))
        (hH n (by omega)) lam (hLn n (by omega)) (τ n) (hτ n (by omega)) z hz
      have h2 := ih (fun r hr => hH r (by omega)) (fun r hr => hL r (by omega))
        (fun r hr => hLn r (by omega)) (fun r hr => hτ r (by omega))
      calc _ ≤ ‖ODEComplexFrequency.evolution (Ls n) (Hs n) (τ n) z‖ *
            ‖TimeDependentODE.GaussianLCHS.productFamily Hs Ls τ n z‖ := norm_mul_le _ _
        _ ≤ Real.exp (τ n * (lam * z.im)) *
            Real.exp ((∑ r ∈ Finset.range n, τ r) * (lam * z.im)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
        _ = _ := mul_comm _ _

/-- A slot generator `L + i H` with `L ≥ 0` and `H` self-adjoint is accretive. -/
theorem slot_accretive (H L : P →L[ℂ] P) (hH : star H = H)
    (hPSD : ∀ w : P, 0 ≤ (inner ℂ w (L w)).re) :
    TimeDependentODE.Accretive (L + Complex.I • H) := by
  intro w
  have him := ODEComplexFrequency.inner_im_eq_zero H hH w
  rw [add_apply, smul_apply, inner_add_right, inner_smul_right, Complex.add_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, him]
  simpa using hPSD w

omit [CompleteSpace P] in
/-- The recurrence depends only on the slots before its length. -/
theorem recurrence_congr (Gs Gs' : ℕ → P →L[ℂ] P) (bs bs' : ℕ → P) (h : ℝ) (y0 : P) (n : ℕ)
    (hG : ∀ r < n, Gs r = Gs' r) (hb : ∀ r < n, bs r = bs' r) :
    TimeDependentODE.recurrence Gs bs h y0 n = TimeDependentODE.recurrence Gs' bs' h y0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [TimeDependentODE.recurrence_succ, TimeDependentODE.recurrence_succ,
        ih (fun r hr => hG r (by omega)) (fun r hr => hb r (by omega)), hG n (by omega),
        hb n (by omega)]

/-- The represented slot generators `G_r = L_r + i H_r`. -/
def gens (Hs Ls : ℕ → P →L[ℂ] P) (r : ℕ) : P →L[ℂ] P := Ls r + Complex.I • Hs r

namespace TParams

variable (p : TParams)

/-! ### The slot generators and masked propagators -/

/-- The masked propagator of a source label. -/
def propS (Hs Ls : ℕ → P →L[ℂ] P) (s : Bool × (Fin p.m → Bool)) : P →L[ℂ] P :=
  TimeDependentODE.maskedPropagator (gens Hs Ls) (p.T / p.M) (p.start s) p.M

/-- The discretised target: the exponential left-endpoint recurrence. -/
def target (Hs Ls : ℕ → P →L[ℂ] P) (x0 : P) (bs : ℕ → P) : P :=
  TimeDependentODE.recurrence (gens Hs Ls) bs (p.T / p.M) x0 p.M

theorem sum_dur_le (hT : 0 ≤ p.T) (s : Bool × (Fin p.m → Bool)) :
    ∑ r ∈ Finset.range p.M, p.dur s r ≤ p.T := by
  calc ∑ r ∈ Finset.range p.M, p.dur s r ≤ ∑ _r ∈ Finset.range p.M, p.T / p.M :=
        Finset.sum_le_sum (fun r _ => p.dur_le hT s r)
    _ = p.T := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hM : (p.M : ℝ) ≠ 0 := by exact_mod_cast p.M_pos.ne'
        field_simp

/-- The ordered product family of a source label, for clamped samples. -/
def family (Hs Ls : ℕ → P →L[ℂ] P) (s : Bool × (Fin p.m → Bool)) : ℂ → P →L[ℂ] P :=
  TimeDependentODE.GaussianLCHS.productFamily (SlotSim.clampAt p.M Hs) (SlotSim.clampAt p.M Ls)
    (p.dur s) p.M

omit [CompleteSpace P] in
theorem family_ofReal (Hs Ls : ℕ → P →L[ℂ] P) (s : Bool × (Fin p.m → Bool))
    (w : Fin p.l → Bool) : p.family Hs Ls s (p.nodeW w : ℂ) = p.branchU Hs Ls s w := by
  unfold family branchU TimeDependentODE.GaussianLCHS.productFamily
  apply SlotSim.evolution_eq_of_lt
  intro r hr
  rw [SlotSim.clampAt_of_lt p.M Hs hr, SlotSim.clampAt_of_lt p.M Ls hr]

omit [CompleteSpace P] in
theorem family_neg_I (Hs Ls : ℕ → P →L[ℂ] P) (s : Bool × (Fin p.m → Bool)) :
    p.family Hs Ls s (-Complex.I) = p.propS Hs Ls s := by
  unfold family propS TimeDependentODE.maskedPropagator
  rw [TimeDependentODE.GaussianLCHS.productFamily_neg_I]
  apply SlotSim.evolution_eq_of_lt
  intro r hr
  rw [SlotSim.clampAt_of_lt p.M Hs hr, SlotSim.clampAt_of_lt p.M Ls hr]
  rfl

/-- **Finite LCHS for every source label.** -/
theorem lchs_error (hT : 0 ≤ p.T) (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1)
    (hlamD : 0 ≤ p.lamD) (Hs Ls : ℕ → P →L[ℂ] P) (hH : ∀ r < p.M, star (Hs r) = Hs r)
    (hL : ∀ r < p.M, star (Ls r) = Ls r) (hLn : ∀ r < p.M, ‖Ls r‖ ≤ p.lamD)
    (hPSD : ∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (Ls r w)).re) (s : Bool × (Fin p.m → Bool)) :
    ‖(∑ w, p.coeffW w • p.branchU Hs Ls s w) - p.propS Hs Ls s‖ ≤ 2 * p.nu := by
  have hcl := SlotSim.min_pred_lt p.M_pos
  have hTD : 0 ≤ p.T * p.lamD := mul_nonneg hT hlamD
  have hcert := AnalyticLCHS.table_certificate (V := P) (p.family Hs Ls)
    (fun s z => TimeDependentODE.GaussianLCHS.productFamily_analyticAt _ _ _ _ z)
    (fun s z hz => TimeDependentODE.GaussianLCHS.productFamily_norm_le_one _ _ _ _
      (fun r => hH _ (hcl r)) (fun r => hL _ (hcl r)) (fun r => hPSD _ (hcl r))
      (fun r => p.dur_nonneg hT s r) z hz)
    (p.T * p.lamD) hTD
    (fun s z hz => (productFamily_norm_le_exp _ _ _ p.lamD p.M
      (fun r _ => hH _ (hcl r)) (fun r _ => hL _ (hcl r)) (fun r _ => hLn _ (hcl r))
      (fun r _ => p.dur_nonneg hT s r) z hz).trans (Real.exp_le_exp.mpr (by
        have hsum := p.sum_dur_le hT s
        have hc : 0 ≤ p.lamD * z.im := mul_nonneg hlamD hz
        calc (∑ r ∈ Finset.range p.M, p.dur s r) * (p.lamD * z.im) ≤ p.T * (p.lamD * z.im) :=
              mul_le_mul_of_nonneg_right hsum hc
          _ = p.T * p.lamD * z.im := by ring)))
    p.ratio p.acc (p.ratio_ge hg) (p.acc_pos hε) (p.acc_le_one hεOne)
  have hsum : ∑ w, p.coeffW w • p.branchU Hs Ls s w =
      ∑ i, AnalyticLCHS.coefficients (p.T * p.lamD) p.ratio p.acc i •
        p.family Hs Ls s (AnalyticLCHS.nodes (p.T * p.lamD) p.ratio p.acc i : ℂ) := by
    rw [← p.coeffW_sum (fun k => p.family Hs Ls s (k : ℂ))]
    simp only [p.family_ofReal]
  rw [hsum, ← p.family_neg_I]
  exact hcert.2.2.2 s

/-! ### The source quadrature -/

omit [CompleteSpace P] in
/-- The masked propagators applied to the source vectors sum exactly to the
recurrence. -/
theorem source_sum (Hs Ls : ℕ → P →L[ℂ] P) (x0 : P) (bs : ℕ → P) :
    ∑ s, p.propS Hs Ls s (p.zsrc x0 bs s) = p.target Hs Ls x0 bs := by
  unfold target
  rw [TimeDependentODE.recurrence_eq_sum, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  congr 1
  · simp only [zsrc, Bool.false_eq_true, if_false, propS, start]
    rw [Finset.sum_eq_single (fun _ => false)]
    · simp
    · intro w _ hw
      rw [if_neg hw, map_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [zsrc, if_true, propS, start, Complex.coe_smul]
    rw [← Fin.sum_univ_eq_sum_range (fun q => TimeDependentODE.maskedPropagator (gens Hs Ls)
      (p.T / p.M) q p.M ((p.T / p.M) • bs q)) p.M]
    exact Fintype.sum_equiv (wordEquivFin p.m) _ _ (fun w => rfl)

/-- With accretive slot generators the discretised target is at most the
source mass. -/
theorem target_norm_le (hT : 0 ≤ p.T) (Hs Ls : ℕ → P →L[ℂ] P)
    (hH : ∀ r < p.M, star (Hs r) = Hs r) (hPSD : ∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (Ls r w)).re)
    (x0 : P) (bs : ℕ → P) : ‖p.target Hs Ls x0 bs‖ ≤ p.mass x0 bs := by
  have hcl := SlotSim.min_pred_lt p.M_pos
  rw [← p.source_sum Hs Ls x0 bs, mass, ODESourceBranches.mass]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  have hprop : p.propS Hs Ls s = TimeDependentODE.maskedPropagator
      (SlotSim.clampAt p.M (gens Hs Ls)) (p.T / p.M) (p.start s) p.M := by
    unfold propS TimeDependentODE.maskedPropagator
    apply SlotSim.evolution_eq_of_lt
    intro r hr
    rw [SlotSim.clampAt_of_lt p.M _ hr]
  have hn : ‖p.propS Hs Ls s‖ ≤ 1 := by
    rw [hprop]
    exact TimeDependentODE.maskedPropagator_norm_le_one _
      (fun r => slot_accretive _ _ (hH _ (hcl r)) (hPSD _ (hcl r)))
      _ (div_nonneg hT (Nat.cast_nonneg _)) _ _
  calc ‖p.propS Hs Ls s (p.zsrc x0 bs s)‖ ≤ ‖p.propS Hs Ls s‖ * ‖p.zsrc x0 bs s‖ :=
        le_opNorm _ _
    _ ≤ 1 * ‖p.zsrc x0 bs s‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ = ‖p.zsrc x0 bs s‖ := one_mul _

/-! ### The time discretisation -/

/-- The certified discretisation error of the left-endpoint scheme with
`2^m` slots, for `βG`- and `βb`-Lipschitz paths, sample errors `δG`, `δb`
and forcing bound `bmax`. -/
def discretisation (βG δG βb δb bmax r₀ : ℝ) : ℝ :=
  p.T * ((βG * (p.T / p.M) + δG) * (r₀ + bmax * p.T) + βb * (p.T / p.M) + δb +
    (p.T / p.M) * (p.lamH + p.lamD) * (bmax + δb))

/-- **The discretised target is within the certified discretisation error of
the solution.** -/
theorem discretisation_error (hT : 0 ≤ p.T) (G : ℝ → P →L[ℂ] P) (b x : ℝ → P)
    (Hs Ls : ℕ → P →L[ℂ] P) (bs : ℕ → P) (βG δG βb δb bmax : ℝ) (hβG : 0 ≤ βG)
    (hβb : 0 ≤ βb) (hx : TimeDependentODE.SolvesODE G b x 0 p.T)
    (hG : ∀ u ∈ Set.Icc 0 p.T, TimeDependentODE.Accretive (G u))
    (hGLip : ∀ u ∈ Set.Icc 0 p.T, ∀ u' ∈ Set.Icc 0 p.T, ‖G u - G u'‖ ≤ βG * |u - u'|)
    (hGs : ∀ r < p.M, ‖G (r * p.T / p.M) - gens Hs Ls r‖ ≤ δG)
    (hbLip : ∀ u ∈ Set.Icc 0 p.T, ∀ u' ∈ Set.Icc 0 p.T, ‖b u - b u'‖ ≤ βb * |u - u'|)
    (hbs : ∀ r < p.M, ‖b (r * p.T / p.M) - bs r‖ ≤ δb)
    (hb : ∀ u ∈ Set.Icc 0 p.T, ‖b u‖ ≤ bmax)
    (hH : ∀ r < p.M, star (Hs r) = Hs r) (hPSD : ∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (Ls r w)).re)
    (hHn : ∀ r < p.M, ‖Hs r‖ ≤ p.lamH) (hLn : ∀ r < p.M, ‖Ls r‖ ≤ p.lamD) :
    ‖x p.T - p.target Hs Ls (x 0) bs‖ ≤ p.discretisation βG δG βb δb bmax ‖x 0‖ := by
  have hcl := SlotSim.min_pred_lt p.M_pos
  have hMR : (0 : ℝ) < p.M := by exact_mod_cast p.M_pos
  have hbmax : 0 ≤ bmax := (norm_nonneg _).trans (hb 0 ⟨le_rfl, hT⟩)
  have hδb : 0 ≤ δb := (norm_nonneg _).trans (hbs 0 p.M_pos)
  have hΛ : 0 ≤ p.lamH + p.lamD :=
    add_nonneg ((norm_nonneg _).trans (hHn 0 p.M_pos)) ((norm_nonneg _).trans (hLn 0 p.M_pos))
  have hslot : ∀ r : ℕ, r < p.M → ((r : ℝ) * p.T / p.M) ∈ Set.Icc 0 p.T := by
    intro r hr
    have hrM : (r : ℝ) ≤ p.M := by exact_mod_cast hr.le
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hMR]
    nlinarith
  have htarget : p.target Hs Ls (x 0) bs = TimeDependentODE.recurrence
      (SlotSim.clampAt p.M (gens Hs Ls)) (SlotSim.clampAt p.M bs) (p.T / p.M) (x 0) p.M := by
    unfold target
    exact recurrence_congr _ _ _ _ _ _ _ (fun r hr => (SlotSim.clampAt_of_lt p.M _ hr).symm)
      (fun r hr => (SlotSim.clampAt_of_lt p.M _ hr).symm)
  rw [htarget]
  exact TimeDependentODE.mesh_error hx hT p.M_pos hG (SlotSim.clampAt p.M (gens Hs Ls))
    (fun r => slot_accretive _ _ (hH _ (hcl r)) (hPSD _ (hcl r))) (SlotSim.clampAt p.M bs)
    βG δG βb δb bmax (p.lamH + p.lamD) (bmax + δb) hβG hβb hbmax hΛ (by linarith) hGLip
    (fun r hr => by rw [SlotSim.clampAt_of_lt p.M _ hr]; exact hGs r hr) hbLip
    (fun r hr => by rw [SlotSim.clampAt_of_lt p.M _ hr]; exact hbs r hr) hb
    (fun r hr => by
      rw [SlotSim.clampAt_of_lt p.M _ hr]
      unfold gens
      calc ‖Ls r + Complex.I • Hs r‖ ≤ ‖Ls r‖ + ‖Complex.I • Hs r‖ := norm_add_le _ _
        _ ≤ p.lamD + p.lamH := by
            rw [norm_smul, Complex.norm_I, one_mul]
            exact add_le_add (hLn r hr) (hHn r hr)
        _ = p.lamH + p.lamD := add_comm _ _)
    (fun r hr => by
      rw [SlotSim.clampAt_of_lt p.M _ hr]
      calc ‖bs r‖ = ‖b ((r : ℝ) * p.T / p.M) - (b ((r : ℝ) * p.T / p.M) - bs r)‖ := by
            rw [sub_sub_cancel]
        _ ≤ ‖b ((r : ℝ) * p.T / p.M)‖ + ‖b ((r : ℝ) * p.T / p.M) - bs r‖ := norm_sub_le _ _
        _ ≤ bmax + δb := add_le_add (hb _ (hslot r hr)) (hbs r hr))

end TParams

end

end SparseHamiltonian.GateODE.Time
