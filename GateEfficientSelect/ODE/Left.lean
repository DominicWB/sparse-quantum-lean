import GateEfficientSelect.ODE.Disc

/-!
# The source certificate for the left-endpoint quadrature

The source certificate `ode:eq:gate-source-certificates` is a hypothesis of Theorem
`ode:thm:gates`; the proof of the theorem also specifies "a sufficient positive quadrature for
time-dependent forcing": a power-of-two left-endpoint mesh (manuscript lines 4815-4832). For
the left-endpoint nodes `v q = q T / 2^m` with the weights `T / 2^m` and the forcing samples
`b̃_q` of the released time-dependent solver (`ODE.vLeft`, `ODE.wLeft`), the certificate of
`ODE.BInstanceOK` follows for every solution `x` of `x' = -G(u) x + b(u)` from the Lipschitz
bounds of the generator and the forcing (`quad_leftEndpoint`):

`‖x(T) - ∑_s y_s(T)‖ ≤ discretisation + T (βG T / 2^m + δG) B`,

where `discretisation` is the released certified error of the left-endpoint recurrence
(`GateODE.Time.TParams.discretisation`) and `y_s` are the homogeneous branch solutions of the
certificate. The generator samples of the recurrence are the branch samples of the initial
label, whose branch runs on the whole interval with the addresses `r T / 2^m`.

* `maskedPropagator_eq_shift`: the masked propagator from slot `q` is the ordered product of
  the slots `q, …, 2^m - 1`.
* `homog_disc`: a homogeneous solution on `[a, c]` against the ordered product of `n` frozen
  sample propagators (the released `TimeDependentODE.mesh_error` on the shifted interval).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSelect.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateODE.Time (TParams gens slot_accretive)
open GateCircuit.SlotSim (clampAt clampAt_of_lt min_pred_lt evolution_eq_of_lt)
open GatePointerEncoding (wordValue wordValue_lt_pow)
open TimeDependentODE (SolvesODE Accretive)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

omit [CompleteSpace P] in
/-- The masked propagator from slot `q` is the ordered product of the slots `q, …, M - 1`. -/
theorem maskedPropagator_eq_shift (Gs : ℕ → P →L[ℂ] P) (h : ℝ) (q M : ℕ) (hq : q ≤ M) :
    TimeDependentODE.maskedPropagator Gs h q M =
      TimeDependent.evolution (fun r => NormedSpace.exp (h • (-Gs (q + r)))) (M - q) := by
  induction M, hq using Nat.le_induction with
  | base =>
      rw [TimeDependentODE.maskedPropagator_of_le Gs h (le_refl q), Nat.sub_self,
        TimeDependent.evolution_zero]
  | succ M hqM ih =>
      rw [TimeDependentODE.maskedPropagator_succ_of_le Gs h hqM, ih, Nat.succ_sub hqM,
        TimeDependent.evolution_succ, Nat.add_sub_cancel' hqM]

/-- **A homogeneous solution against frozen samples.** For a solution of `y' = -G(u) y` on
`[a, c]`, an accretive `βG`-Lipschitz generator and accretive samples `Gs r` with
`‖G(a + r (c - a)/n) - Gs r‖ ≤ δG`, the ordered product of the frozen propagators
`exp (-((c - a)/n) Gs r)` is within `(c - a)(βG (c - a)/n + δG) ‖y(a)‖` of `y(c)`. -/
theorem homog_disc (G : ℝ → P →L[ℂ] P) (y : ℝ → P) (a c : ℝ) (hac : a ≤ c) (n : ℕ)
    (hn : 0 < n) (Gs : ℕ → P →L[ℂ] P) (βG δG : ℝ) (hβG : 0 ≤ βG)
    (hy : SolvesODE G (fun _ => 0) y a c)
    (hG : ∀ u ∈ Set.Icc a c, Accretive (G u))
    (hGLip : ∀ u ∈ Set.Icc a c, ∀ u' ∈ Set.Icc a c, ‖G u - G u'‖ ≤ βG * |u - u'|)
    (hGs : ∀ r < n, ‖G (a + r * (c - a) / n) - Gs r‖ ≤ δG)
    (hacc : ∀ r < n, Accretive (Gs r)) :
    ‖y c - TimeDependent.evolution (fun r => NormedSpace.exp (((c - a) / n) • (-Gs r))) n
        (y a)‖ ≤ (c - a) * (βG * ((c - a) / n) + δG) * ‖y a‖ := by
  have hcl := min_pred_lt hn
  have hu : 0 ≤ c - a := sub_nonneg.mpr hac
  have hsh := solvesODE_shift hy
  have hsub : ∀ t ∈ Set.Icc 0 (c - a), a + t ∈ Set.Icc a c := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set Gc := clampAt n Gs with hGc_def
  have hGcacc : ∀ r, Accretive (Gc r) := fun r => hacc _ (hcl r)
  have hΛ : ∀ r < n, ‖Gc r‖ ≤ ∑ q ∈ Finset.range n, ‖Gc q‖ := fun r hr =>
    Finset.single_le_sum (f := fun q => ‖Gc q‖) (fun q _ => norm_nonneg _)
      (Finset.mem_range.mpr hr)
  have hmesh := TimeDependentODE.mesh_error (G := fun t => G (a + t)) (b := fun _ => 0)
    (x := fun t => y (a + t)) (T := c - a) (M := n) hsh hu hn
    (fun t ht => hG _ (hsub t ht)) Gc hGcacc (fun _ => 0) βG δG 0 0 0
    (∑ q ∈ Finset.range n, ‖Gc q‖) 0 hβG le_rfl le_rfl
    (Finset.sum_nonneg (fun q _ => norm_nonneg _)) le_rfl
    (fun t ht t' ht' => by
      have h1 := hGLip _ (hsub t ht) _ (hsub t' ht')
      have e : a + t - (a + t') = t - t' := by ring
      rwa [e] at h1)
    (fun r hr => by
      rw [hGc_def, clampAt_of_lt _ _ hr]
      exact hGs r hr)
    (fun _ _ _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp) hΛ (fun _ _ => by simp)
  have hrec : TimeDependentODE.recurrence Gc (fun _ => 0) ((c - a) / n) (y (a + 0)) n =
      TimeDependent.evolution (fun r => NormedSpace.exp (((c - a) / n) • (-Gs r))) n (y a) := by
    rw [TimeDependentODE.recurrence_eq_sum]
    simp only [smul_zero, map_zero, Finset.sum_const_zero, add_zero]
    unfold TimeDependentODE.maskedPropagator
    congr 1
    apply evolution_eq_of_lt
    intro r hr
    rw [TimeDependentODE.mask_of_le (Nat.zero_le r), mul_one, hGc_def, clampAt_of_lt _ _ hr]
  have hend : a + (c - a) = c := by ring
  simp only [hend] at hmesh
  rw [hrec] at hmesh
  have e0 : a + 0 = a := add_zero a
  rw [e0] at hmesh
  calc _ ≤ (c - a) * ((βG * ((c - a) / n) + δG) * (‖y a‖ + 0 * (c - a)) + 0 * ((c - a) / n) +
        0 + (c - a) / n * (∑ q ∈ Finset.range n, ‖Gc q‖) * 0) := hmesh
    _ = (c - a) * (βG * ((c - a) / n) + δG) * ‖y a‖ := by ring

variable (p : TParams)

/-- The left-endpoint nodes `q T / 2^m`. -/
def vLeft (q : ℕ) : ℝ := q * p.T / p.M

/-- The left-endpoint weights `T / 2^m`. -/
def wLeft (_q : ℕ) : ℝ := p.T / p.M

theorem vLeft_mem (hT : 0 ≤ p.T) : ∀ q < p.M, 0 ≤ vLeft p q ∧ vLeft p q ≤ p.T := by
  intro q hq
  have hMR : (0 : ℝ) < p.M := by exact_mod_cast p.M_pos
  have hqM : (q : ℝ) ≤ p.M := by exact_mod_cast hq.le
  unfold vLeft
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hMR]
  nlinarith

theorem wLeft_nonneg (hT : 0 ≤ p.T) : ∀ q < p.M, 0 ≤ wLeft p q :=
  fun _ _ => div_nonneg hT (Nat.cast_nonneg _)

omit [CompleteSpace P] in
/-- With the left-endpoint weights the forcing vectors are the released forcing samples. -/
theorem bsW_left (hT : 0 < p.T) (bs : ℕ → P) : bsW p (wLeft p) bs = bs := by
  funext q
  unfold bsW wLeft
  have hM : (p.M : ℝ) ≠ 0 := by exact_mod_cast p.M_pos.ne'
  have e : (p.M : ℝ) / p.T * (p.T / p.M) = 1 := by field_simp
  rw [e, Complex.ofReal_one, one_smul]

/-- The start time of a source label at the left-endpoint nodes is its start slot times
`T / 2^m`. -/
theorem startB_left (s : Bool × (Fin p.m → Bool)) :
    startB p (vLeft p) s = (p.start s : ℝ) * p.T / p.M := by
  unfold startB GateODE.Time.TParams.start vLeft
  split_ifs <;> simp

theorem start_lt (s : Bool × (Fin p.m → Bool)) : p.start s < p.M := by
  unfold GateODE.Time.TParams.start
  split_ifs
  · exact wordValue_lt_pow s.2
  · exact p.M_pos

/-- **The source certificate for the left-endpoint quadrature.** For a solution `x` of
`x' = -G(u) x + b(u)` on `[0, T]` with an accretive `βG`-Lipschitz generator and a
`βb`-Lipschitz forcing bounded by `bmax`, forcing samples `b̃_q` with
`‖b(q T / 2^m) - b̃_q‖ ≤ δb`, and branch samples of the initial label (addresses `r T / 2^m`)
with `‖G(r T / 2^m) - (Lb r + i Hb r)‖ ≤ δG`, every family of homogeneous branch solutions of
the left-endpoint quadrature satisfies the source certificate with
`κ = discretisation + T (βG T / 2^m + δG) B`. -/
theorem quad_leftEndpoint (hT : 0 < p.T) (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P)
    (G : ℝ → P →L[ℂ] P) (b x : ℝ → P) (bs : ℕ → P) (ys : Bool × (Fin p.m → Bool) → ℝ → P)
    (βG δG βb δb bmax : ℝ) (hβG : 0 ≤ βG) (hβb : 0 ≤ βb)
    (hx : SolvesODE G b x 0 p.T)
    (hG : ∀ u ∈ Set.Icc 0 p.T, Accretive (G u))
    (hGLip : ∀ u ∈ Set.Icc 0 p.T, ∀ u' ∈ Set.Icc 0 p.T, ‖G u - G u'‖ ≤ βG * |u - u'|)
    (hbLip : ∀ u ∈ Set.Icc 0 p.T, ∀ u' ∈ Set.Icc 0 p.T, ‖b u - b u'‖ ≤ βb * |u - u'|)
    (hb : ∀ u ∈ Set.Icc 0 p.T, ‖b u‖ ≤ bmax)
    (hbs : ∀ r < p.M, ‖b (r * p.T / p.M) - bs r‖ ≤ δb)
    (hH : ∀ r < p.M, star (Hb (false, fun _ => false) r) = Hb (false, fun _ => false) r)
    (hPSD : ∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (Lb (false, fun _ => false) r w)).re)
    (hHn : ∀ r < p.M, ‖Hb (false, fun _ => false) r‖ ≤ p.lamH)
    (hLn : ∀ r < p.M, ‖Lb (false, fun _ => false) r‖ ≤ p.lamD)
    (hGs : ∀ r < p.M, ‖G (addrB p (vLeft p) (false, fun _ => false) r) -
      gens (Hb (false, fun _ => false)) (Lb (false, fun _ => false)) r‖ ≤ δG)
    (hys : ∀ s, SolvesODE G (fun _ => 0) (ys s) (startB p (vLeft p) s) p.T)
    (hys0 : ∀ s, ys s (startB p (vLeft p) s) = p.zsrc (x 0) (bsW p (wLeft p) bs) s) :
    ‖x p.T - ∑ s, ys s p.T‖ ≤ p.discretisation βG δG βb δb bmax ‖x 0‖ +
      p.T * (βG * (p.T / p.M) + δG) * p.mass (x 0) (bsW p (wLeft p) bs) := by
  set Hs := Hb (false, fun _ => false) with hHs_def
  set Ls := Lb (false, fun _ => false) with hLs_def
  have hMR : (0 : ℝ) < p.M := by exact_mod_cast p.M_pos
  have hM0 : (p.M : ℝ) ≠ 0 := hMR.ne'
  have hδG : 0 ≤ δG := (norm_nonneg _).trans (hGs 0 p.M_pos)
  have hbsW := bsW_left p hT bs
  rw [hbsW] at hys0 ⊢
  -- the common-mesh samples are those of the initial label
  have hGs' : ∀ r < p.M, ‖G (r * p.T / p.M) - gens Hs Ls r‖ ≤ δG := by
    intro r hr
    have h1 := hGs r hr
    have e : addrB p (vLeft p) (false, fun _ => false) r = r * p.T / p.M := by
      unfold addrB durB startB
      simp
    rwa [e] at h1
  have hdisc := p.discretisation_error hT.le G b x Hs Ls bs βG δG βb δb bmax hβG hβb hx hG hGLip
    hGs' hbLip hbs hb hH hPSD hHn hLn
  rw [← p.source_sum Hs Ls (x 0) bs] at hdisc
  -- every masked propagator against its homogeneous solution
  have hbr : ∀ s, ‖p.propS Hs Ls s (p.zsrc (x 0) bs s) - ys s p.T‖ ≤
      p.T * (βG * (p.T / p.M) + δG) * ‖p.zsrc (x 0) bs s‖ := by
    intro s
    have hq := start_lt p s
    set q := p.start s with hq_def
    have hn : 0 < p.M - q := Nat.sub_pos_of_lt hq
    have hnR : ((p.M - q : ℕ) : ℝ) = p.M - q := Nat.cast_sub hq.le
    have hqR : (q : ℝ) < p.M := by exact_mod_cast hq
    have ha := startB_left p s
    rw [← hq_def] at ha
    set a := startB p (vLeft p) s with ha_def
    have ha0 : 0 ≤ a := by rw [ha]; positivity
    have haT : a ≤ p.T := by
      rw [ha, div_le_iff₀ hMR]
      nlinarith
    have hstep : (p.T - a) / ((p.M - q : ℕ) : ℝ) = p.T / p.M := by
      rw [hnR, ha]
      have hMq : (p.M : ℝ) - q ≠ 0 := by linarith
      field_simp
    have hd := homog_disc G (ys s) a p.T haT (p.M - q) hn (fun r => gens Hs Ls (q + r)) βG δG hβG
      (hys s) (fun u hu => hG u ⟨ha0.trans hu.1, hu.2⟩)
      (fun u hu u' hu' => hGLip u ⟨ha0.trans hu.1, hu.2⟩ u' ⟨ha0.trans hu'.1, hu'.2⟩)
      (fun r hr => by
        have hqr : q + r < p.M := by omega
        have e : a + r * (p.T - a) / ((p.M - q : ℕ) : ℝ) = ((q + r : ℕ) : ℝ) * p.T / p.M := by
          rw [mul_div_assoc, hstep, ha]
          push_cast
          ring
        rw [e]
        exact hGs' (q + r) hqr)
      (fun r hr => slot_accretive _ _ (hH _ (by omega)) (hPSD _ (by omega)))
    rw [hstep, hys0 s] at hd
    have hprop : p.propS Hs Ls s = TimeDependent.evolution
        (fun r => NormedSpace.exp ((p.T / p.M) • (-gens Hs Ls (q + r)))) (p.M - q) := by
      unfold GateODE.Time.TParams.propS
      rw [maskedPropagator_eq_shift _ _ _ _ hq.le]
    rw [hprop, norm_sub_rev]
    have hk : (p.T - a) * (βG * (p.T / p.M) + δG) ≤ p.T * (βG * (p.T / p.M) + δG) :=
      mul_le_mul_of_nonneg_right (by linarith)
        (add_nonneg (mul_nonneg hβG (div_nonneg hT.le hMR.le)) hδG)
    exact hd.trans (mul_le_mul_of_nonneg_right hk (norm_nonneg _))
  have hsplit : x p.T - ∑ s, ys s p.T =
      (x p.T - ∑ s, p.propS Hs Ls s (p.zsrc (x 0) bs s)) +
        ∑ s, (p.propS Hs Ls s (p.zsrc (x 0) bs s) - ys s p.T) := by
    rw [Finset.sum_sub_distrib]
    abel
  rw [hsplit]
  calc ‖(x p.T - ∑ s, p.propS Hs Ls s (p.zsrc (x 0) bs s)) +
        ∑ s, (p.propS Hs Ls s (p.zsrc (x 0) bs s) - ys s p.T)‖ ≤
      ‖x p.T - ∑ s, p.propS Hs Ls s (p.zsrc (x 0) bs s)‖ +
        ∑ s, ‖p.propS Hs Ls s (p.zsrc (x 0) bs s) - ys s p.T‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ p.discretisation βG δG βb δb bmax ‖x 0‖ +
        ∑ s, p.T * (βG * (p.T / p.M) + δG) * ‖p.zsrc (x 0) bs s‖ :=
        add_le_add hdisc (Finset.sum_le_sum (fun s _ => hbr s))
    _ = p.discretisation βG δG βb δb bmax ‖x 0‖ +
        p.T * (βG * (p.T / p.M) + δG) * p.mass (x 0) bs := by
        rw [← Finset.mul_sum]
        rfl

end

end SparseHamiltonian.GateSelect.ODE
