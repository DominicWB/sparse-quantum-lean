import GateEfficientODE.Time.Words
import GateEfficientODE.Analysis.Input

/-!
# The ideal label preparation of the time-dependent solver

The source labels are `(ini, q)`: the initial label `(false, 0)` carries the
initial state, the forcing label `(true, q)` the forcing sample `b_q`
weighted by the step `T / 2^m`, and the remaining labels carry zero
(`zsrc`).  The source mass `mass x₀ bs = ‖x₀‖ + (T / 2^m) ∑_q ‖b_q‖`
(`mass_eq`) is the left-endpoint quadrature of `‖x₀‖ + ∫ ‖b‖`.  The supplied
weight preparation has first column `sqrt(‖zsrc s‖ / mass)` (`WpPromise`).
Under this promise:

* `inMap = ODEActualSourceError.input branchE zsrc coeffW J`
  (`inMap_eq_input`);
* `outMap = ODEActualSourceError.output branchE zsrc coeffW`
  (`outMap_eq_output`).
-/

namespace SparseHamiltonian.GateODE.Time

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire)
open GatePointerEncoding (wordValue wordEquivFin)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Matrices on exposed wires -/

section Generic

variable {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

omit [CompleteSpace Q] in
theorem matOp_bas (M : Matrix (Cfg A) (Cfg A) ℂ) (c : Cfg A) (q : Q) :
    matOp M (bas c q) = ∑ b, M b c • bas b q := by
  apply PiLp.ext
  intro b'
  rw [matOp_apply, WithLp.ofLp_sum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single c, Finset.sum_eq_single b']
  · simp
  · intro b _ hb
    change M b c • (bas b q) b' = 0
    rw [bas_apply, if_neg (Ne.symm hb), smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro c' _ hc
    rw [bas_apply, if_neg hc, smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- A matrix on the exposed wires applied to a basis vector. -/
theorem localOp_matOp_bas {ι : A → W} (hι : Function.Injective ι) (M : Matrix (Cfg A) (Cfg A) ℂ)
    (x : Cfg W) (q : Q) :
    localOp ι hι (fun _ => matOp M) (bas x q) =
      ∑ b, M b (fun a => x (ι a)) • bas (overwrite ι x b) q := by
  rw [bas_eq_put hι x q, localOp_put, matOp_bas]
  apply PiLp.ext
  intro y
  rw [put_apply, WithLp.ofLp_sum]
  simp only [Finset.sum_apply]
  by_cases h : outPart ι y = outPart ι x
  · rw [if_pos h, WithLp.ofLp_sum]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro b _
    change M b (fun a => x (ι a)) • (bas b q) (fun a => y (ι a)) =
      M b (fun a => x (ι a)) • (bas (overwrite ι x b) q) y
    rw [bas_apply, bas_apply]
    congr 1
    have hiff : (fun a => y (ι a)) = b ↔ y = overwrite ι x b := by
      rw [cfg_eq_iff hι y (overwrite ι x b), outPart_joinCfg,
        show (fun a => overwrite ι x b (ι a)) = b from
          funext (fun a => overwrite_apply_ι hι x b a)]
      exact ⟨fun hb => ⟨h, hb⟩, fun hb => hb.2⟩
    by_cases hb : (fun a => y (ι a)) = b
    · rw [if_pos hb, if_pos (hiff.mp hb)]
    · rw [if_neg hb, if_neg (fun e => hb (hiff.mpr e))]
  · rw [if_neg h, WithLp.ofLp_sum]
    simp only [Finset.sum_apply]
    symm
    apply Finset.sum_eq_zero
    intro b _
    change M b (fun a => x (ι a)) • (bas (overwrite ι x b) q) y = 0
    rw [bas_apply, if_neg, smul_zero]
    intro e
    apply h
    rw [e]
    exact outPart_joinCfg ι _ b

end Generic

section Wires

variable {a m r K k l f : ℕ}

/-- Writing a word on the source wires of the zero configuration. -/
theorem overwrite_src_zero (b : Cfg (Fin (k + 1))) :
    overwrite (srcTS (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f))
      (fun _ => false) b = cfgOf ((b 0, Fin.tail b), fun _ => false) := by
  have hother : ∀ x : AW a m r K k l f, (∀ t, srcTS t ≠ x) →
      overwrite srcTS (fun _ => false) b x = false := fun x hx =>
    overwrite_apply_out srcTS _ b x hx
  funext x
  rcases x with s | o
  · exact hother _ (fun t => by cases t using Fin.cases <;> simp [srcTS])
  · cases o with
    | ini => exact overwrite_apply_ι srcTS_injective _ b 0
    | src i => exact overwrite_apply_ι srcTS_injective _ b i.succ
    | lch j => exact hother _ (fun t => by cases t using Fin.cases <;> simp [srcTS])
    | flg => exact hother _ (fun t => by cases t using Fin.cases <;> simp [srcTS])
    | pool i => exact hother _ (fun t => by cases t using Fin.cases <;> simp [srcTS])

end Wires

namespace TParams

variable (p : TParams)

/-! ### Source vectors and the weight promise -/

/-- Source vectors: the initial state on `(false, 0)`, the forcing sample
`b_q` weighted by `T / 2^m` on `(true, q)`, zero elsewhere. -/
def zsrc (x0 : P) (bs : ℕ → P) (s : Bool × (Fin p.m → Bool)) : P :=
  if s.1 then ((p.T / p.M : ℝ) : ℂ) • bs (wordValue s.2)
  else if s.2 = (fun _ => false) then x0 else 0

/-- The source mass. -/
def mass (x0 : P) (bs : ℕ → P) : ℝ := ODESourceBranches.mass (p.zsrc x0 bs)

/-- Amplitudes of the weight preparation. -/
def srcAmp (x0 : P) (bs : ℕ → P) (s : Bool × (Fin p.m → Bool)) : ℝ :=
  Real.sqrt (‖p.zsrc x0 bs s‖ / p.mass x0 bs)

/-- The promise of the supplied weight preparation: its column at the zero
word carries the amplitudes `sqrt(‖zsrc s‖ / mass)`. -/
def WpPromise (σ : TOracles p.a p.m p.l P) (x0 : P) (bs : ℕ → P) : Prop :=
  ∀ w : Cfg (Fin (p.m + 1)), σ.Wp w (fun _ => false) = ((p.srcAmp x0 bs (w 0, Fin.tail w) : ℝ) : ℂ)

theorem wordValue_zero' : wordValue (fun _ : Fin p.m => false) = 0 := by
  simp [GatePointerEncoding.wordValue]

omit [CompleteSpace P] in
/-- The source mass is the left-endpoint quadrature of `‖x₀‖ + ∫ ‖b‖`. -/
theorem mass_eq (hT : 0 ≤ p.T) (x0 : P) (bs : ℕ → P) :
    p.mass x0 bs = ‖x0‖ + p.T / p.M * ∑ q ∈ Finset.range p.M, ‖bs q‖ := by
  unfold mass ODESourceBranches.mass
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  have h1 : ∑ w : Fin p.m → Bool, ‖p.zsrc x0 bs (true, w)‖ =
      p.T / p.M * ∑ q ∈ Finset.range p.M, ‖bs q‖ := by
    simp only [zsrc, if_true, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hT (Nat.cast_nonneg p.M))]
    rw [← Finset.mul_sum]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun q => ‖bs q‖) p.M]
    exact Fintype.sum_equiv (wordEquivFin p.m) _ _ (fun w => rfl)
  have h2 : ∑ w : Fin p.m → Bool, ‖p.zsrc x0 bs (false, w)‖ = ‖x0‖ := by
    simp only [zsrc, Bool.false_eq_true, if_false]
    rw [Finset.sum_eq_single (fun _ => false)]
    · simp
    · intro w _ hw
      rw [if_neg hw, norm_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1, h2]
  ring

omit [CompleteSpace P] in
theorem srcAmp_nonneg (x0 : P) (bs : ℕ → P) (s : Bool × (Fin p.m → Bool)) :
    0 ≤ p.srcAmp x0 bs s := Real.sqrt_nonneg _

omit [CompleteSpace P] in
theorem srcAmp_sq (x0 : P) (bs : ℕ → P) (hB : 0 < p.mass x0 bs) (s : Bool × (Fin p.m → Bool)) :
    p.srcAmp x0 bs s ^ 2 = ‖p.zsrc x0 bs s‖ / p.mass x0 bs :=
  Real.sq_sqrt (div_nonneg (norm_nonneg _) hB.le)

/-! ### The branch embedding and the label preparation -/

/-- The branch embedding of the joint labels. -/
def branchE : ODEJointLCU.BranchSpace (Label p.m p.l) P →L[ℂ] Reg p.W P := branchEmb cfgOf

theorem branchE_isometry : (p.branchE (P := P))† ∘L p.branchE = 1 :=
  branchEmb_isometry _ cfgOf_injective

/-- The weight preparation on the clean configuration. -/
theorem WP_zero (σ : TOracles p.a p.m p.l P) (x0 : P) (bs : ℕ → P) (hW : p.WpPromise σ x0 bs)
    (u : P) :
    p.WP σ (bas (fun _ => false) u) =
      ∑ s : Bool × (Fin p.m → Bool), ((p.srcAmp x0 bs s : ℝ) : ℂ) •
        bas (cfgOf (s, fun _ => false)) u := by
  change localOp srcTS srcTS_injective (fun _ => matOp σ.Wp) (bas (fun _ => false) u) = _
  rw [localOp_matOp_bas]
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (p.m + 1) => Bool))
    (fun s => ((p.srcAmp x0 bs s : ℝ) : ℂ) • bas (cfgOf (s, fun _ => false)) u)
    (fun w => σ.Wp w (fun _ => false) • bas (overwrite srcTS (fun _ => false) w) u)]
  intro s
  obtain ⟨b, t⟩ := s
  have h0 : (Fin.consEquiv (fun _ : Fin (p.m + 1) => Bool)) (b, t) 0 = b := rfl
  have ht : Fin.tail ((Fin.consEquiv (fun _ : Fin (p.m + 1) => Bool)) (b, t)) = t := rfl
  have hz : (fun t' : Fin (p.m + 1) => (fun _ : p.W => false) (srcTS t')) = fun _ => false := rfl
  rw [hz, hW, overwrite_src_zero, h0, ht]

/-- The LCHS label tree on a source configuration. -/
theorem LP_src (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD)
    (s : Bool × (Fin p.m → Bool)) (u : P) :
    p.LP (bas (cfgOf (s, fun _ => false)) u) =
      ∑ w, ((p.lchAmp w : ℝ) : ℂ) • bas (cfgOf (s, w)) u := by
  have hset : ∀ w : Fin p.l → Bool, setLow (lchTS (a := p.a) (m := p.m) (r := p.r) (K := p.K)
      (k := p.m) (f := p.f)) p.l le_rfl (cfgOf (s, fun _ => false)) w = cfgOf (s, w) := by
    intro w
    have hother : ∀ x : p.W, (∀ t, lchTS t ≠ x) →
        setLow lchTS p.l le_rfl (cfgOf (s, fun _ => false)) w x = cfgOf (s, fun _ => false) x :=
      fun x hx => setLow_apply_other lchTS p.l le_rfl _ w x hx
    funext x
    rcases x with s' | o
    · exact hother _ (fun t => by simp [lchTS])
    · cases o with
      | ini => exact hother _ (fun t => by simp [lchTS])
      | src i => exact hother _ (fun t => by simp [lchTS])
      | lch j => exact setLow_apply_ts lchTS_injective _ w j
      | flg => exact hother _ (fun t => by simp [lchTS])
      | pool i => exact hother _ (fun t => by simp [lchTS])
  rw [LP, treeOp_zero lchTS_injective p.l_pos p.lchAmp (p.lchAmp_sq_sum hg hε hεOne hTD) _
    (fun _ => rfl) u]
  simp only [hset]

theorem load_bas (v : P) (σ : TOracles p.a p.m p.l P) (z : Label p.m p.l) (u : P) :
    trun v σ p.load (bas (cfgOf z) u) = bas (cfgOf z) (σ.J z.1 u) := by
  rw [load, trun_singleton, teval_load, psel_bas]
  rfl

/-- The ideal label preparation as an explicit sum over joint labels. -/
theorem labels_zero (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD)
    (σ : TOracles p.a p.m p.l P) (x0 : P) (bs : ℕ → P) (hW : p.WpPromise σ x0 bs) (u : P) :
    p.LP (p.WP σ (goodF u)) = ∑ z : Label p.m p.l,
      ((p.srcAmp x0 bs z.1 * p.lchAmp z.2 : ℝ) : ℂ) • bas (cfgOf z) u := by
  rw [goodF, basL_apply, p.WP_zero σ x0 bs hW, map_sum]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_smul, p.LP_src hg hε hεOne hTD, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [smul_smul]
  push_cast
  rfl

omit [CompleteSpace P] in
/-- The square roots of the joint probabilities are the products of the
circuit amplitudes. -/
theorem sqrt_probability (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1)
    (hTD : 0 ≤ p.T * p.lamD) (x0 : P) (bs : ℕ → P) (hB : 0 < p.mass x0 bs) (z : Label p.m p.l) :
    Real.sqrt (ODECoherentLCU.coefficientProbability
      (ODEActualSourceError.coefficients (p.zsrc x0 bs) p.coeffW) z) =
      p.srcAmp x0 bs z.1 * p.lchAmp z.2 := by
  have hc := p.coeffW_mass hg hε hεOne hTD
  rw [Real.sqrt_eq_iff_mul_self_eq (ODECoherentLCU.coefficientProbability_nonneg _ _)
    (mul_nonneg (p.srcAmp_nonneg _ _ _) (p.lchAmp_nonneg _))]
  unfold ODECoherentLCU.coefficientProbability
  rw [ODEActualSourceError.coefficientMass_eq _ _ hB hc]
  unfold ODEActualSourceError.coefficients ODESourceCoefficients.productCoeff
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ODESourceBranches.probability_nonneg _ _)]
  unfold ODESourceBranches.probability
  have h1 := p.srcAmp_sq x0 bs hB z.1
  have h2 := p.lchAmp_sq z.2
  unfold mass at h1
  calc ‖p.zsrc x0 bs z.1‖ / ODESourceBranches.mass (p.zsrc x0 bs) * ‖p.coeffW z.2‖ / 3 =
      p.srcAmp x0 bs z.1 ^ 2 * p.lchAmp z.2 ^ 2 := by rw [h1, h2]; ring
    _ = _ := by ring

/-! ### The input and output encodings -/

/-- **The ideal weight and label preparation and loading is the released
source-aware LCU input.** -/
theorem inMap_eq_input (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD)
    (v : P) (σ : TOracles p.a p.m p.l P) (x0 : P) (bs : ℕ → P) (hB : 0 < p.mass x0 bs)
    (hW : p.WpPromise σ x0 bs) :
    p.inMap v σ = ODEActualSourceError.input p.branchE (p.zsrc x0 bs) p.coeffW σ.J := by
  refine ContinuousLinearMap.ext (fun u => ?_)
  simp only [inMap, comp_apply]
  rw [p.labels_zero hg hε hεOne hTD σ x0 bs hW, map_sum]
  simp only [ODEActualSourceError.input, ODEJointSourceLCU.input, comp_apply, branchE,
    branchEmb_apply, ODECoherentLCU.inputEmbedding, WeightedClock.boundary_apply]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_smul, p.load_bas v σ z u, p.sqrt_probability hg hε hεOne hTD x0 bs hB z, bas_smul]

/-- **The ideal output preparation is the released source-aware LCU
output.** -/
theorem outMap_eq_output (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD)
    (σ : TOracles p.a p.m p.l P) (x0 : P) (bs : ℕ → P) (hB : 0 < p.mass x0 bs)
    (hW : p.WpPromise σ x0 bs) :
    p.outMap σ = ODEActualSourceError.output p.branchE (p.zsrc x0 bs) p.coeffW := by
  refine ContinuousLinearMap.ext (fun u => ?_)
  simp only [outMap, comp_apply]
  rw [p.labels_zero hg hε hεOne hTD σ x0 bs hW, map_sum]
  simp only [ODEActualSourceError.output, ODEJointLCU.output, ODEJointLCU.coefficientOutput,
    comp_apply, branchE, branchEmb_apply, ODECoherentLCU.outputEmbedding,
    WeightedClock.boundary_apply]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_smul, PH, phaseOp_adjoint, phaseOp_bas lchTS_injective,
    p.sqrt_probability hg hε hεOne hTD x0 bs hB z]
  have hw : wordOf lchTS (cfgOf (a := p.a) (m := p.m) (r := p.r) (K := p.K) (f := p.f) z) =
      z.2 := rfl
  rw [hw, smul_apply, one_apply_eq_self, bas_smul, bas_smul, smul_smul, smul_smul]
  by_cases hs : p.srcAmp x0 bs z.1 = 0
  · simp [hs]
  · congr 2
    have hpos : 0 < ODESourceBranches.probability (p.zsrc x0 bs) z.1 := by
      have hsq := p.srcAmp_sq x0 bs hB z.1
      have hp : 0 < p.srcAmp x0 bs z.1 := lt_of_le_of_ne (p.srcAmp_nonneg _ _ _) (Ne.symm hs)
      unfold ODESourceBranches.probability
      unfold mass at hsq
      rw [← hsq]
      positivity
    unfold ODEActualSourceError.coefficients ODESourceCoefficients.productCoeff
    rw [coefficientPhase_ofReal_mul _ hpos]

end TParams

end

end SparseHamiltonian.GateODE.Time
