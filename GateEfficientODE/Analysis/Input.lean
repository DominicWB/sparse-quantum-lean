import GateEfficientODE.Analysis.Words

/-!
# The ideal label preparation is the released source-aware LCU encoding

The source labels are `(ini, node word)`, the LCHS labels are words, and the
branch embedding `branchE` places the joint label `(s, w)` on `cfgOf (s, w)`.
With the source vectors `zsrc x₀ b` (the initial state `x₀ / 2^k` on every
node of the initial sector and the weighted forcing `(T / 2^k) b` on every
node of the forcing sector), whose mass is `B = r₀ + T rb`:

* `inMap = ODEActualSourceError.input branchE (zsrc x₀ b) coeffW J`: the
  source rotation tree and the LCHS tree prepare the square roots of the
  joint probabilities, and the loading applies `J₀` or `J_b`
  (`inMap_eq_input`);
* `outMap = ODEActualSourceError.output branchE (zsrc x₀ b) coeffW`: with the
  conjugate coefficient phases (`outMap_eq_output`).

Here `‖x₀‖ = r₀`, `‖b‖ = rb` and `B > 0`.
-/

namespace SparseHamiltonian.GateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire)
open GatePointerEncoding (wordValue)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Generic facts -/

section Generic

variable {W : Type*} [DecidableEq W]

theorem setLow_apply_ts {q : ℕ} {ts : Fin q → W} (hts : Function.Injective ts) (x : Cfg W)
    (w : Fin q → Bool) (i : Fin q) : setLow ts q le_rfl x w (ts i) = w i :=
  setLow_apply_low ts hts q le_rfl x w i

end Generic

theorem coefficientPhase_ofReal_mul (t : ℝ) (ht : 0 < t) (z : ℂ) :
    ODECoherentLCU.coefficientPhase ((t : ℂ) * z) = ODECoherentLCU.coefficientPhase z := by
  by_cases hz : z = 0
  · simp [hz]
  · have htz : (t : ℂ) * z ≠ 0 := mul_ne_zero (by exact_mod_cast ht.ne') hz
    simp only [ODECoherentLCU.coefficientPhase, if_neg hz, if_neg htz, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    push_cast
    field_simp

theorem phaseMat_conjTranspose {q : ℕ} (hq : 0 < q) (φ : (Fin q → Bool) → ℂ)
    (w : Fin q → Bool) :
    (phaseMat hq φ w).conjTranspose = phaseMat hq (fun u => (starRingEnd ℂ) (φ u)) w := by
  funext b c
  simp only [Matrix.conjTranspose_apply, phaseMat]
  by_cases h : b = c
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

theorem phaseOp_adjoint {W : Type*} [Fintype W] [DecidableEq W] {q : ℕ} (ts : Fin q → W)
    (hq : 0 < q) (φ : (Fin q → Bool) → ℂ) :
    (phaseOp (Q := P) ts hq φ)† = phaseOp ts hq (fun u => (starRingEnd ℂ) (φ u)) := by
  unfold phaseOp
  rw [condOp_adjoint]
  congr 1
  funext x
  exact phaseMat_conjTranspose hq φ _

namespace Params

variable (p : Params)

/-! ### Labels and configurations -/

/-- The source amplitude of a source label. -/
def srcAmp (s : Bool × (Fin p.k → Bool)) : ℝ :=
  (if s.1 then Real.sqrt (p.T * p.rb / p.B) else Real.sqrt (p.r₀ / p.B)) *
    ((Real.sqrt 2)⁻¹) ^ p.k

/-- Source vectors: `x₀ / 2^k` on the initial sector and `(T / 2^k) b` on
the forcing sector, at every node. -/
def zsrc (x0 b : P) (s : Bool × (Fin p.k → Bool)) : P :=
  if s.1 then ((p.T / 2 ^ p.k : ℝ) : ℂ) • b else ((1 / 2 ^ p.k : ℝ) : ℂ) • x0

/-- The branch embedding of the joint labels. -/
def branchE : ODEJointLCU.BranchSpace (Label p.k p.l) P →L[ℂ] Reg p.W P := branchEmb cfgOf

theorem branchE_isometry : (p.branchE (P := P))† ∘L p.branchE = 1 :=
  branchEmb_isometry _ cfgOf_injective

theorem setLow_src (w : Fin (p.k + 1) → Bool) :
    setLow (srcTS (a := p.a) (m := p.m) (r := p.r) (K := p.K) (l := p.l) (f := p.f)) (p.k + 1)
      le_rfl (fun _ => false) w = cfgOf ((w 0, Fin.tail w), fun _ => false) := by
  have hother : ∀ x : p.W, (∀ t, srcTS t ≠ x) →
      setLow srcTS (p.k + 1) le_rfl (fun _ => false) w x = false := fun x hx =>
    setLow_apply_other srcTS (p.k + 1) le_rfl (fun _ => false) w x hx
  funext x
  rcases x with s | o
  · exact hother _ (fun t => by cases t using Fin.cases <;> simp [srcTS])
  · cases o with
    | ini => exact setLow_apply_ts srcTS_injective _ w 0
    | src i => exact setLow_apply_ts srcTS_injective _ w i.succ
    | lch j => exact hother _ (fun t => by cases t using Fin.cases <;> simp [srcTS])
    | flg => exact hother _ (fun t => by cases t using Fin.cases <;> simp [srcTS])
    | pool i => exact hother _ (fun t => by cases t using Fin.cases <;> simp [srcTS])

theorem setLow_lch (s : Bool × (Fin p.k → Bool)) (w : Fin p.l → Bool) :
    setLow (lchTS (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k) (f := p.f)) p.l le_rfl
      (cfgOf (s, fun _ => false)) w = cfgOf (s, w) := by
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

theorem srcMat_prod (w : Fin (p.k + 1) → Bool) :
    ∏ i, p.srcMat i (w i) false = ((p.srcAmp (w 0, Fin.tail w) : ℝ) : ℂ) := by
  rw [Fin.prod_univ_succ]
  have h0 : p.srcMat 0 (w 0) false =
      ((if w 0 then Real.sqrt (p.T * p.rb / p.B) else Real.sqrt (p.r₀ / p.B) : ℝ) : ℂ) := by
    simp only [srcMat, Fin.cases_zero]
    cases w 0 <;> rfl
  have hs : ∀ i : Fin p.k, p.srcMat i.succ (w i.succ) false = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
    intro i
    simp only [srcMat, Fin.cases_succ, hadC]
    cases w i.succ <;> rfl
  rw [h0, Finset.prod_congr rfl (fun i _ => hs i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, srcAmp]
  push_cast
  rfl

/-- The source rotation tree on the clean configuration. -/
theorem SP_zero (u : P) :
    p.SP (bas (fun _ => false) u) =
      ∑ s : Bool × (Fin p.k → Bool), ((p.srcAmp s : ℝ) : ℂ) • bas (cfgOf (s, fun _ => false)) u := by
  change treeOp srcTS (fun s _ => p.srcMat s) (bas (fun _ => false) u) = _
  rw [treeOp_bas srcTS srcTS_injective _ (fun _ _ _ _ _ => rfl) _ (fun _ => rfl) u]
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (p.k + 1) => Bool))
    (fun s => ((p.srcAmp s : ℝ) : ℂ) • bas (cfgOf (s, fun _ => false)) u)
    (fun w => (∏ i, p.srcMat i (w i) false) • bas (setLow srcTS (p.k + 1) le_rfl
      (fun _ => false) w) u)]
  intro s
  rw [p.srcMat_prod, p.setLow_src]
  rfl

/-- The LCHS label tree on a source configuration. -/
theorem LP_src (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD)
    (s : Bool × (Fin p.k → Bool)) (u : P) :
    p.LP (bas (cfgOf (s, fun _ => false)) u) =
      ∑ w, ((p.lchAmp w : ℝ) : ℂ) • bas (cfgOf (s, w)) u := by
  rw [LP, treeOp_zero lchTS_injective p.l_pos p.lchAmp (p.lchAmp_sq_sum hg hε hεOne hTD) _
    (fun _ => rfl) u]
  simp only [p.setLow_lch]

omit [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P] in
@[simp] theorem wiring_ini (v : P) :
    (wiring (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k) (l := p.l) (f := p.f) v).ini =
      OWire.ini := rfl

theorem load_bas (v : P) (σ : Oracles p.a (Label p.k p.l) P) (z : Label p.k p.l) (u : P) :
    run (wiring v) σ p.load (bas (cfgOf z) u) = bas (cfgOf z) (σ.J z.1.1 u) := by
  rw [load, run_cons, run_singleton, comp_apply, OInstr.eval_src, OInstr.eval_src, wiring_ini]
  simp only [adjIf, Bool.false_eq_true, if_false]
  obtain ⟨⟨b, s⟩, w⟩ := z
  cases b
  · have h1 : ctrlOK [(Sum.inr OWire.ini, false)]
        (cfgOf (a := p.a) (m := p.m) (r := p.r) (K := p.K) (f := p.f) ((false, s), w)) = true := rfl
    have h2 : ctrlOK [(Sum.inr OWire.ini, true)]
        (cfgOf (a := p.a) (m := p.m) (r := p.r) (K := p.K) (f := p.f) ((false, s), w)) = false := rfl
    rw [pctl_bas, if_pos h1, pctl_bas, h2]
    rfl
  · have h1 : ctrlOK [(Sum.inr OWire.ini, false)]
        (cfgOf (a := p.a) (m := p.m) (r := p.r) (K := p.K) (f := p.f) ((true, s), w)) = false := rfl
    have h2 : ctrlOK [(Sum.inr OWire.ini, true)]
        (cfgOf (a := p.a) (m := p.m) (r := p.r) (K := p.K) (f := p.f) ((true, s), w)) = true := rfl
    rw [pctl_bas, h1, if_neg Bool.false_ne_true, pctl_bas, if_pos h2]

/-- The ideal label preparation as an explicit sum over joint labels. -/
theorem labels_zero (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD)
    (u : P) :
    p.LP (p.SP (goodF u)) = ∑ z : Label p.k p.l,
      ((p.srcAmp z.1 * p.lchAmp z.2 : ℝ) : ℂ) • bas (cfgOf z) u := by
  rw [goodF, basL_apply, p.SP_zero, map_sum]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_smul, p.LP_src hg hε hεOne hTD, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [smul_smul]
  push_cast
  rfl

/-! ### Probabilities -/

omit [CompleteSpace P] in
theorem norm_zsrc (x0 b : P) (hT : 0 ≤ p.T) (h₀ : ‖x0‖ = p.r₀) (hb : ‖b‖ = p.rb)
    (s : Bool × (Fin p.k → Bool)) :
    ‖p.zsrc x0 b s‖ = (if s.1 then p.T * p.rb else p.r₀) / 2 ^ p.k := by
  unfold zsrc
  cases s.1
  · simp only [Bool.false_eq_true, if_false, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      h₀]
    rw [abs_of_nonneg (by positivity)]
    ring
  · simp only [if_true, norm_smul, Complex.norm_real, Real.norm_eq_abs, hb]
    rw [abs_of_nonneg (by positivity)]
    ring

omit [CompleteSpace P] in
theorem mass_zsrc (x0 b : P) (hT : 0 ≤ p.T) (h₀ : ‖x0‖ = p.r₀) (hb : ‖b‖ = p.rb) :
    ODESourceBranches.mass (p.zsrc x0 b) = p.B := by
  unfold ODESourceBranches.mass
  simp only [p.norm_zsrc x0 b hT h₀ hb, Fintype.sum_prod_type, Fintype.sum_bool, if_true,
    Bool.false_eq_true, if_false, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  have h2 : (2 : ℝ) ^ p.k ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem srcAmp_sq (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb) (hT : 0 ≤ p.T) (hB : 0 < p.B)
    (s : Bool × (Fin p.k → Bool)) :
    p.srcAmp s ^ 2 = (if s.1 then p.T * p.rb else p.r₀) / 2 ^ p.k / p.B := by
  have h2 : ((Real.sqrt 2)⁻¹ ^ p.k) ^ 2 = ((2 : ℝ) ^ p.k)⁻¹ := by
    rw [← pow_mul, mul_comm, pow_mul, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), inv_pow]
  unfold srcAmp
  rw [mul_pow, h2]
  cases s.1
  · simp only [Bool.false_eq_true, if_false]
    rw [Real.sq_sqrt (div_nonneg hr₀ hB.le)]
    field_simp
  · simp only [if_true]
    rw [Real.sq_sqrt (div_nonneg (mul_nonneg hT hrb) hB.le)]
    field_simp

theorem srcAmp_nonneg (s : Bool × (Fin p.k → Bool)) : 0 ≤ p.srcAmp s := by
  unfold srcAmp
  apply mul_nonneg
  · split_ifs <;> exact Real.sqrt_nonneg _
  · positivity

omit [CompleteSpace P] in
/-- The square roots of the joint probabilities are the products of the
circuit amplitudes. -/
theorem sqrt_probability (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD)
    (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb) (hT : 0 ≤ p.T) (hB : 0 < p.B) (x0 b : P)
    (h₀ : ‖x0‖ = p.r₀) (hb : ‖b‖ = p.rb) (z : Label p.k p.l) :
    Real.sqrt (ODECoherentLCU.coefficientProbability
      (ODEActualSourceError.coefficients (p.zsrc x0 b) p.coeffW) z) =
      p.srcAmp z.1 * p.lchAmp z.2 := by
  have hmass := p.mass_zsrc x0 b hT h₀ hb
  have hz : 0 < ODESourceBranches.mass (p.zsrc x0 b) := by rw [hmass]; exact hB
  have hc := p.coeffW_mass hg hε hεOne hTD
  rw [Real.sqrt_eq_iff_mul_self_eq (ODECoherentLCU.coefficientProbability_nonneg _ _)
    (mul_nonneg (p.srcAmp_nonneg _) (p.lchAmp_nonneg _))]
  unfold ODECoherentLCU.coefficientProbability
  rw [ODEActualSourceError.coefficientMass_eq _ _ hz hc]
  unfold ODEActualSourceError.coefficients ODESourceCoefficients.productCoeff
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ODESourceBranches.probability_nonneg _ _)]
  unfold ODESourceBranches.probability
  rw [hmass, p.norm_zsrc x0 b hT h₀ hb]
  have h1 := p.srcAmp_sq hr₀ hrb hT hB z.1
  have h2 := p.lchAmp_sq z.2
  calc (if z.1.1 then p.T * p.rb else p.r₀) / 2 ^ p.k / p.B * ‖p.coeffW z.2‖ / 3 =
      p.srcAmp z.1 ^ 2 * p.lchAmp z.2 ^ 2 := by rw [h1, h2]; ring
    _ = _ := by ring

/-! ### The input and output encodings -/

/-- The source interfaces indexed by the source label. -/
def srcJ (σ : Oracles p.a (Label p.k p.l) P) (s : Bool × (Fin p.k → Bool)) : P →L[ℂ] P :=
  σ.J s.1

/-- **The ideal label preparation and loading is the released source-aware
LCU input.** -/
theorem inMap_eq_input (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD)
    (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb) (hT : 0 ≤ p.T) (hB : 0 < p.B) (x0 b : P)
    (h₀ : ‖x0‖ = p.r₀) (hb : ‖b‖ = p.rb) (v : P) (σ : Oracles p.a (Label p.k p.l) P) :
    p.inMap v σ = ODEActualSourceError.input p.branchE (p.zsrc x0 b) p.coeffW (p.srcJ σ) := by
  refine ContinuousLinearMap.ext (fun u => ?_)
  simp only [inMap, comp_apply]
  rw [p.labels_zero hg hε hεOne hTD, map_sum]
  simp only [ODEActualSourceError.input, ODEJointSourceLCU.input, comp_apply, branchE,
    branchEmb_apply, ODECoherentLCU.inputEmbedding, WeightedClock.boundary_apply]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_smul, p.load_bas v σ z u, p.sqrt_probability hg hε hεOne hTD hr₀ hrb hT hB x0 b h₀ hb z,
    bas_smul]
  rfl

/-- **The ideal output preparation is the released source-aware LCU
output.** -/
theorem outMap_eq_output (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD)
    (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb) (hT : 0 ≤ p.T) (hB : 0 < p.B) (x0 b : P)
    (h₀ : ‖x0‖ = p.r₀) (hb : ‖b‖ = p.rb) :
    p.outMap (P := P) = ODEActualSourceError.output p.branchE (p.zsrc x0 b) p.coeffW := by
  refine ContinuousLinearMap.ext (fun u => ?_)
  simp only [outMap, comp_apply]
  rw [p.labels_zero hg hε hεOne hTD, map_sum]
  simp only [ODEActualSourceError.output, ODEJointLCU.output, ODEJointLCU.coefficientOutput,
    comp_apply, branchE, branchEmb_apply, ODECoherentLCU.outputEmbedding,
    WeightedClock.boundary_apply]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_smul, PH, phaseOp_adjoint, phaseOp_bas lchTS_injective,
    p.sqrt_probability hg hε hεOne hTD hr₀ hrb hT hB x0 b h₀ hb z]
  have hw : wordOf lchTS (cfgOf (a := p.a) (m := p.m) (r := p.r) (K := p.K) (f := p.f) z) =
      z.2 := rfl
  rw [hw, smul_apply, one_apply_eq_self, bas_smul, bas_smul, smul_smul, smul_smul]
  by_cases hs : p.srcAmp z.1 = 0
  · simp [hs]
  · congr 2
    have hpos : 0 < ODESourceBranches.probability (p.zsrc x0 b) z.1 := by
      have hsq := p.srcAmp_sq hr₀ hrb hT hB z.1
      have hp : 0 < p.srcAmp z.1 := lt_of_le_of_ne (p.srcAmp_nonneg _) (Ne.symm hs)
      unfold ODESourceBranches.probability
      rw [p.mass_zsrc x0 b hT h₀ hb, p.norm_zsrc x0 b hT h₀ hb]
      rw [← hsq]
      positivity
    unfold ODEActualSourceError.coefficients ODESourceCoefficients.productCoeff
    rw [coefficientPhase_ofReal_mul _ hpos]

end Params

end

end SparseHamiltonian.GateODE
