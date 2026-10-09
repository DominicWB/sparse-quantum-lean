import ODELowerBoundExtensions.Dyson.Compile
import ODELowerBoundExtensions.Dyson.Helpers.TargetCoef
import ODELowerBoundExtensions.Dyson.Helpers.TargetMesh
import TimeDependentExtensions.ODE.Sampling
import TimeDependentODE.Source.Controls

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The Dyson LCU target and its error (`odel:lem:dyson`, lines 4178-4190, 4234-4252)

The forced solution `U(T,0) x₀ + ∫_0^T U(T,u) b(u) du` is compared with the released
exponential left-endpoint scheme on the mesh (`TimeDependentExtensions.ODEMesh.meshRecurrence`,
error `mesh_error`: contractive Duhamel comparison with integrated sample errors and the
source quadrature, lines 4178-4190 and 4237-4239), whose value is the sum over the source
branches `q` of the masked mesh propagators applied to the source vectors
(`meshRecurrence_eq_sum`). Each masked propagator is replaced by its Dyson series truncated at
degree `K` (`Series.lean`), with the same coefficient sequence on every branch; the branch
starting at the cell `q` carries the known attenuation `mask q r` of the earlier cells
(lines 4242-4243, "the factor `((T-u)/T)^k` is a known attenuation").

* `branchRates rate t q r = rate · (t_{r+1} - t_r) · mask(q, r)`, `rate = s Λ`;
* `dysonCoeff`: the LCU coefficients — source weight (`MeshSampling.norms`) times Dyson weight
  times `(-1)^{deg}` on the configurations, and a cancelling pair `± (weight · branchMass)/2`
  on the padding branches (it doubles the coefficient mass, keeping the herald amplitude at
  most `1/2`, and adds nothing to the selected sum);
* `lcuMass`: half the coefficient mass; `mass_le_lcuMass`, `lcuMass_le`: `B ≤ lcuMass ≤ B e^z`
  (lines 4243-4245, "normalisation `O(e^z B)`");
* `lcuTarget`: the selected LCU sum `∑_l dysonCoeff l • branchOperator l (J_{l.1} v)`;
* `lcuTarget_error`: under the certified discretisation of `TimeDependentExtensions.ODE.solver`
  (constant `2000`) and a degree with tail at most `ε/(2000 g)`, the LCU sum is within
  `ε B/(1000 g)` of `x(T)` (lines 4246-4250).

Proof map: `lcuTarget_eq` (the padding pair cancels), `branch_sum_eq` (each source branch is
the truncated Dyson series of its masked mesh propagator, via `Helpers/TargetCoef`), the
certified mesh comparison `mesh_selected_error` (`Helpers/TargetMesh`), `truncated_error` per
branch, and the triangle inequality.
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

open SparseHamiltonian ContinuousLinearMap NativeSparseBlockEncoding Set MeasureTheory
open TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (mask mask_nonneg Accretive SolvesODE)
open TimeDependentExtensions.ODEMesh (meshRecurrence meshPropagator meshRecurrence_eq_sum)
open scoped InnerProduct BigOperators

/-- The first cell of a source branch: `0` for the initial state, `q` for the forcing of cell
`q`. -/
def sourceStart {M : ℕ} : Option (Fin M) → ℕ
  | none => 0
  | some q => q

/-- The rescaled cell durations of a source branch, `rate · Δ_r · mask(q, r)`. -/
def branchRates (rate : ℝ) (t : ℕ → ℝ) {M : ℕ} (q : Option (Fin M)) : ℕ → ℝ :=
  fun r => rate * (t (r + 1) - t r) * mask (sourceStart q) r

/-- The Dyson coefficient mass of a source branch. -/
def branchMass (rate : ℝ) (t : ℕ → ℝ) (K M : ℕ) (q : Option (Fin M)) : ℝ :=
  ∑ c : Cfg K M, coef (branchRates rate t q) c

/-- Half the LCU coefficient mass: `∑_q w_q · branchMass q`, `w = MeshSampling.norms`. -/
def lcuMass (rate : ℝ) (t : ℕ → ℝ) (K M : ℕ) (r₀ : ℝ) (rb : Fin M → ℝ) : ℝ :=
  ∑ q : Option (Fin M), MeshSampling.norms r₀ t rb q * branchMass rate t K M q

/-- **The LCU coefficients** of the Dyson solver. -/
def dysonCoeff (rate : ℝ) (t : ℕ → ℝ) (K M : ℕ) (r₀ : ℝ) (rb : Fin M → ℝ) : Lab K M → ℂ
  | (q, .inl c) =>
      ((MeshSampling.norms r₀ t rb q * coef (branchRates rate t q) c * (-1) ^ c.degree : ℝ) : ℂ)
  | (q, .inr b) =>
      (((if b then -1 else 1) * (MeshSampling.norms r₀ t rb q * branchMass rate t K M q / 2) :
        ℝ) : ℂ)

/-- Branch rates of a nonnegative rate on a monotone mesh are nonnegative. -/
theorem branchRates_nonneg (rate : ℝ) (t : ℕ → ℝ) {M : ℕ} (hrate : 0 ≤ rate) (ht : Monotone t)
    (q : Option (Fin M)) (r : ℕ) : 0 ≤ branchRates rate t q r :=
  mul_nonneg (mul_nonneg hrate (sub_nonneg.mpr (ht (Nat.le_succ r)))) (mask_nonneg _ _)

/-- The modulus of a configuration coefficient: source weight times Dyson weight. -/
theorem norm_dysonCoeff_inl (rate : ℝ) (t : ℕ → ℝ) (K M : ℕ) (r₀ : ℝ) (rb : Fin M → ℝ)
    (hrate : 0 ≤ rate) (h₀ : 0 ≤ r₀) (ht : Monotone t) (hb : ∀ q, 0 ≤ rb q)
    (q : Option (Fin M)) (c : Cfg K M) :
    ‖dysonCoeff rate t K M r₀ rb (q, .inl c)‖ =
      MeshSampling.norms r₀ t rb q * coef (branchRates rate t q) c := by
  have hw := MeshSampling.norms_nonneg r₀ t rb h₀ ht hb q
  have hc := coef_nonneg _ (branchRates_nonneg rate t hrate ht q) c
  simp only [dysonCoeff]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
    abs_of_nonneg (mul_nonneg hw hc)]

/-- The LCU coefficient mass is `2 lcuMass` (the cancelling padding pair doubles it). -/
theorem coefficientMass_dysonCoeff (rate : ℝ) (t : ℕ → ℝ) (K M : ℕ) (r₀ : ℝ)
    (rb : Fin M → ℝ) (hrate : 0 ≤ rate) (h₀ : 0 ≤ r₀) (ht : Monotone t) (hb : ∀ q, 0 ≤ rb q) :
    ODECoherentLCU.coefficientMass (dysonCoeff rate t K M r₀ rb) =
      2 * lcuMass rate t K M r₀ rb := by
  unfold ODECoherentLCU.coefficientMass lcuMass
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Fintype.sum_sum_type, Fintype.sum_bool]
  have hw := MeshSampling.norms_nonneg r₀ t rb h₀ ht hb q
  have hbm : 0 ≤ branchMass rate t K M q :=
    Finset.sum_nonneg fun c _ => coef_nonneg _ (branchRates_nonneg rate t hrate ht q) c
  have h1 : ∑ c : Cfg K M, ‖dysonCoeff rate t K M r₀ rb (q, .inl c)‖ =
      MeshSampling.norms r₀ t rb q * branchMass rate t K M q := by
    unfold branchMass
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ =>
      norm_dysonCoeff_inl rate t K M r₀ rb hrate h₀ ht hb q c
  have hx : 0 ≤ MeshSampling.norms r₀ t rb q * branchMass rate t K M q / 2 := by positivity
  rw [h1]
  simp only [dysonCoeff, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  norm_num
  rw [abs_of_nonneg hx]
  ring

/-- `B ≤ lcuMass`: every branch contains the empty configuration. -/
theorem mass_le_lcuMass (rate : ℝ) (t : ℕ → ℝ) (K M : ℕ) (r₀ : ℝ) (rb : Fin M → ℝ)
    (hrate : 0 ≤ rate) (h₀ : 0 ≤ r₀) (ht : Monotone t) (hb : ∀ q, 0 ≤ rb q) :
    MeshSampling.mass r₀ t rb ≤ lcuMass rate t K M r₀ rb := by
  unfold lcuMass branchMass
  rw [← MeshSampling.sum_norms]
  exact Finset.sum_le_sum fun q _ =>
    le_mul_of_one_le_right (MeshSampling.norms_nonneg r₀ t rb h₀ ht hb q)
      (one_le_sum_coef _ (branchRates_nonneg rate t hrate ht q) K M)

/-- `lcuMass ≤ B e^{rate T}` (lines 4243-4245). -/
theorem lcuMass_le (rate : ℝ) {t : ℕ → ℝ} {T : ℝ} (K : ℕ) {M : ℕ} (hmesh : IsMesh t M T)
    (r₀ : ℝ) (rb : Fin M → ℝ) (hrate : 0 ≤ rate) (h₀ : 0 ≤ r₀) (hb : ∀ q, 0 ≤ rb q) :
    lcuMass rate t K M r₀ rb ≤ MeshSampling.mass r₀ t rb * Real.exp (rate * T) := by
  unfold lcuMass
  rw [← MeshSampling.sum_norms, Finset.sum_mul]
  refine Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left ?_
    (MeshSampling.norms_nonneg r₀ t rb h₀ hmesh.mono hb q)
  unfold branchMass
  refine (sum_coef_le_exp _ (branchRates_nonneg rate t hrate hmesh.mono q) K M).trans
    (Real.exp_le_exp.mpr ?_)
  rw [← hmesh.sum_length, Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  exact mul_le_of_le_one_right (mul_nonneg hrate (hmesh.length_nonneg r)) (by unfold mask; split_ifs <;> norm_num)

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s Ks : ℕ}

/-- **The selected LCU sum** for branch preparations `J q` (depending on the source label). -/
def lcuTarget {K M : ℕ} (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s) (t : ℕ → ℝ)
    (r₀ : ℝ) (rb : Fin M → ℝ) (x : X)
    (J : Option (Fin M) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (v : EuclideanSpace ℂ n) : EuclideanSpace ℂ n :=
  ∑ l : Lab K M, dysonCoeff ((s : ℝ) * D.scale) t K M r₀ rb l •
    branchOperator σ D x l (J l.1 v)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The cancelling padding pair contributes nothing: the LCU sum runs over the
configurations only. -/
theorem lcuTarget_eq {K M : ℕ} (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s)
    (t : ℕ → ℝ) (r₀ : ℝ) (rb : Fin M → ℝ) (x : X)
    (J : Option (Fin M) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (v : EuclideanSpace ℂ n) :
    lcuTarget (K := K) σ D t r₀ rb x J v =
      ∑ q : Option (Fin M), ∑ c : Cfg K M,
        dysonCoeff ((s : ℝ) * D.scale) t K M r₀ rb (q, .inl c) •
          cfgProduct (sampleSeq σ D x) c (J q v) := by
  unfold lcuTarget
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Fintype.sum_sum_type, Fintype.sum_bool]
  have hpad : dysonCoeff ((s : ℝ) * D.scale) t K M r₀ rb (q, .inr true) •
        branchOperator σ D x ((q, .inr true) : Lab K M) (J q v) +
      dysonCoeff ((s : ℝ) * D.scale) t K M r₀ rb (q, .inr false) •
        branchOperator σ D x ((q, .inr false) : Lab K M) (J q v) = 0 := by
    simp [dysonCoeff, branchOperator]
  rw [hpad, add_zero]
  rfl

/-- `‖LCU sum‖ ≤ lcuMass` for unit-norm prepared sources. -/
theorem lcuTarget_norm_le {K M : ℕ} (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s)
    (t : ℕ → ℝ) (r₀ : ℝ) (rb : Fin M → ℝ) (x : X)
    (J : Option (Fin M) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (v : EuclideanSpace ℂ n) (hJ : ∀ q, ‖J q v‖ ≤ 1) (h₀ : 0 ≤ r₀) (ht : Monotone t)
    (hb : ∀ q, 0 ≤ rb q) :
    ‖lcuTarget (K := K) σ D t r₀ rb x J v‖ ≤ lcuMass ((s : ℝ) * D.scale) t K M r₀ rb := by
  have hΛ : 0 ≤ (s : ℝ) * D.scale := mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le
  rw [lcuTarget_eq]
  unfold lcuMass branchMass
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  have hw := MeshSampling.norms_nonneg r₀ t rb h₀ ht hb q
  have hc := coef_nonneg _ (branchRates_nonneg _ t hΛ ht q) c
  rw [norm_smul, norm_dysonCoeff_inl _ t K M r₀ rb hΛ h₀ ht hb q c]
  have hP1 : ‖cfgProduct (sampleSeq σ D x) c‖ ≤ 1 :=
    branchOperator_norm_le σ D x ((q, .inl c) : Lab K M)
  have hP : ‖cfgProduct (sampleSeq σ D x) c (J q v)‖ ≤ 1 :=
    (le_opNorm _ _).trans (by
      nlinarith [hJ q, norm_nonneg (J q v), norm_nonneg (cfgProduct (sampleSeq σ D x) c)])
  calc _ ≤ MeshSampling.norms r₀ t rb q * coef (branchRates ((s : ℝ) * D.scale) t q) c * 1 :=
        mul_le_mul_of_nonneg_left hP (mul_nonneg hw hc)
    _ = _ := mul_one _

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **One source branch**: the configuration terms of branch `q`, applied to a prepared
source `u`, are the truncated Dyson series of the masked mesh propagator (generators
`-Gs r = -(s Λ) A_{σ r}/(s Λ)`) applied to the weighted source `w_q u`. -/
theorem branch_sum_eq {K M : ℕ} (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s)
    (t : ℕ → ℝ) (r₀ : ℝ) (rb : Fin M → ℝ) (x : X)
    (Gs : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hGs : ∀ r < M, Gs r = ((s : ℝ) * D.scale) • sampleSeq σ D x r)
    (q : Option (Fin M)) (u : EuclideanSpace ℂ n) :
    ∑ c : Cfg K M, dysonCoeff ((s : ℝ) * D.scale) t K M r₀ rb (q, .inl c) •
        cfgProduct (sampleSeq σ D x) c u =
      truncated (fun r => (t (r + 1) - t r) * mask (sourceStart q) r) (fun r => -Gs r) K M
        (MeshSampling.norms r₀ t rb q • u) := by
  rw [truncated_eq_of_smul _ ((s : ℝ) * D.scale) (fun r => -Gs r) (sampleSeq σ D x) K M
    (fun r hr => by rw [hGs r hr, neg_smul]), sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hcoef : coef (fun r => (s : ℝ) * D.scale * ((t (r + 1) - t r) *
      mask (sourceStart q) r)) c = coef (branchRates ((s : ℝ) * D.scale) t q) c := by
    unfold branchRates
    simp only [mul_assoc]
  rw [smul_apply, ContinuousLinearMap.map_smul_of_tower, smul_smul, hcoef]
  simp only [dysonCoeff]
  rw [Complex.coe_smul]
  congr 1
  ring

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
set_option maxHeartbeats 1000000 in
/-- **Error of the Dyson LCU target** (lines 4230-4250): with the release's certified
discretisation (sample errors integrated against `r₀ + b_max T`, forcing sample errors and the
left-endpoint quadrature, at most `ε B/(2000 g)`) and a degree `K` whose factorial tail at
`z = s Λ T` is at most `ε/(2000 g)`, the selected LCU sum is within `ε B/(1000 g)` of `x(T)`. -/
theorem lcuTarget_error {K M : ℕ} (hM : 0 < M) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (g ε r₀ : ℝ) (rb : Fin M → ℝ) (hg : 1 ≤ g) (hε : 0 < ε)
    (hK : expTail ((s : ℝ) * D.scale * T) K ≤ ε / (2000 * g))
    (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
    (bs : Fin M → EuclideanSpace ℂ n) (bmax : ℝ)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hAcc : ∀ r : Fin M,
      Accretive (SparseStateOverlap.matrixOperator (D.matrix (x, σ r))))
    (hGint : ∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1)))
    (hbint : ∀ r : Fin M, IntervalIntegrable (b r) volume (t r) (t ((r : ℕ) + 1)))
    (hbmax : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ‖b r u‖ ≤ bmax)
    (hsol : ∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1)))
    (h₀ : ‖sol 0‖ = r₀) (hbs : ∀ r, ‖bs r‖ = rb r)
    (J : Option (Fin M) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (v : EuclideanSpace ℂ n)
    (hJ₀ : sol 0 ≠ 0 → J none v = ODEStateNormalization.unitDirection (sol 0))
    (hJb : ∀ r, bs r ≠ 0 → J (some r) v = ODEStateNormalization.unitDirection (bs r))
    (hcert : (r₀ + bmax * T) * (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
          ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, σ r))‖) +
        (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖b r u - bs r‖) +
        (s : ℝ) * D.scale * (∑ q : Fin M, (t ((q : ℕ) + 1) - t q) ^ 2 * rb q) / 2 ≤
      ε * MeshSampling.mass r₀ t rb / (2000 * g)) :
    ‖lcuTarget (K := K) σ D t r₀ rb x J v - sol T‖ ≤
      ε * MeshSampling.mass r₀ t rb / (1000 * g) := by
  classical
  have ht : Monotone t := hmesh.mono
  have hεg : 0 ≤ ε / (2000 * g) := div_nonneg hε.le (by linarith)
  have hMesh := (mesh_selected_error hM σ D hmesh x G b sol bs bmax r₀ rb hG hAcc hGint hbint
    hbmax hsol h₀ hbs).trans hcert
  set idx : ℕ → Fin M := TimeDependent.Sampled.sampleIndex hM with hidx
  have hidxv : ∀ r : Fin M, idx r = r := fun r => MeshSampling.sampleIndex_of_lt hM r.isLt
  have hidxlt : ∀ r (hr : r < M), idx r = ⟨r, hr⟩ :=
    fun r hr => MeshSampling.sampleIndex_of_lt hM hr
  set Gs : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
    SparseStateOverlap.matrixOperator (D.matrix (x, σ (idx r))) with hGsdef
  set bsq : ℕ → EuclideanSpace ℂ n := fun r => bs (idx r) with hbsqdef
  set Δ : ℕ → ℝ := fun r => t (r + 1) - t r with hΔdef
  have hΔ : ∀ r, 0 ≤ Δ r := fun r => hmesh.length_nonneg r
  have hGsn : ∀ r, ‖Gs r‖ ≤ (s : ℝ) * D.scale := fun r =>
    MeshSampling.generator_norm_le D (fun _ => σ (idx r)) x 0
  have hGsS : ∀ r < M, Gs r = ((s : ℝ) * D.scale) • sampleSeq σ D x r := by
    intro r hr
    show SparseStateOverlap.matrixOperator (D.matrix (x, σ (idx r))) = _
    rw [hidxlt r hr]
    unfold sampleSeq
    rw [dif_pos hr]
    exact matrixOperator_eq_smul D x _
  -- The scheme as a sum over the source labels.
  have hRec : meshRecurrence Gs bsq Δ (sol 0) M =
      ∑ a, meshPropagator Gs Δ (sourceStart a) M (MeshSampling.sources (sol 0) t bs a) := by
    rw [meshRecurrence_eq_sum, Fintype.sum_option]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun q => meshPropagator Gs Δ q M (Δ q • bsq q)) M]
    apply Finset.sum_congr rfl
    intro q _
    simp only [sourceStart, MeshSampling.sources, Δ, bsq, hidxv]
  -- The LCU sum as the truncated series of the branches.
  have hLCU : lcuTarget (K := K) σ D t r₀ rb x J v =
      ∑ a, truncated (fun r => Δ r * mask (sourceStart a) r) (fun r => -Gs r) K M
        (MeshSampling.sources (sol 0) t bs a) := by
    rw [lcuTarget_eq]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [branch_sum_eq σ D t r₀ rb x Gs hGsS q (J q v),
      norms_smul_eq_sources t (sol 0) bs r₀ rb h₀ hbs (fun q => J q v) hJ₀ hJb q]
  -- Each branch: truncation error of the Dyson series.
  have hBranch : ∀ a : Option (Fin M),
      ‖truncated (fun r => Δ r * mask (sourceStart a) r) (fun r => -Gs r) K M -
        meshPropagator Gs Δ (sourceStart a) M‖ ≤ ε / (2000 * g) := by
    intro a
    have ha : ∀ r, 0 ≤ Δ r * mask (sourceStart a) r := fun r =>
      mul_nonneg (hΔ r) (mask_nonneg _ _)
    have hE := truncated_error (fun r => Δ r * mask (sourceStart a) r) ha (fun r => -Gs r) K M
    have hy0 : 0 ≤ ∑ r ∈ Finset.range M, Δ r * mask (sourceStart a) r * ‖-Gs r‖ :=
      Finset.sum_nonneg fun r _ => mul_nonneg (ha r) (norm_nonneg _)
    have hyle : ∑ r ∈ Finset.range M, Δ r * mask (sourceStart a) r * ‖-Gs r‖ ≤
        (s : ℝ) * D.scale * T := by
      rw [← hmesh.sum_length, Finset.mul_sum]
      refine Finset.sum_le_sum fun r _ => ?_
      calc Δ r * mask (sourceStart a) r * ‖-Gs r‖ =
            (Δ r * ‖Gs r‖) * mask (sourceStart a) r := by rw [norm_neg]; ring
        _ ≤ (Δ r * ‖Gs r‖) * 1 :=
            mul_le_mul_of_nonneg_left (by unfold mask; split_ifs <;> norm_num) (mul_nonneg (hΔ r) (norm_nonneg _))
        _ ≤ (s : ℝ) * D.scale * (t (r + 1) - t r) := by
            rw [mul_one, mul_comm]
            exact mul_le_mul_of_nonneg_right (hGsn r) (hΔ r)
    rw [norm_sub_rev]
    exact hE.trans ((expTail_mono K hy0 hyle).trans hK)
  -- The branch errors add up to `ε B/(2000 g)`.
  have hTrunc : ‖lcuTarget (K := K) σ D t r₀ rb x J v - meshRecurrence Gs bsq Δ (sol 0) M‖ ≤
      ε / (2000 * g) * MeshSampling.mass r₀ t rb := by
    rw [hLCU, hRec, ← Finset.sum_sub_distrib, ← MeshSampling.sum_norms, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [← sub_apply,
      ← MeshSampling.sources_norm (sol 0) t ht bs r₀ rb h₀ hbs a]
    exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hBranch a) (norm_nonneg _))
  have hsplit : ‖lcuTarget (K := K) σ D t r₀ rb x J v - sol T‖ ≤
      ‖lcuTarget (K := K) σ D t r₀ rb x J v - meshRecurrence Gs bsq Δ (sol 0) M‖ +
        ‖sol T - meshRecurrence Gs bsq Δ (sol 0) M‖ := by
    rw [norm_sub_rev (sol T)]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  have he1 : ε / (2000 * g) * MeshSampling.mass r₀ t rb =
      ε * MeshSampling.mass r₀ t rb / (2000 * g) := by ring
  have he2 : ε * MeshSampling.mass r₀ t rb / (2000 * g) +
      ε * MeshSampling.mass r₀ t rb / (2000 * g) =
      ε * MeshSampling.mass r₀ t rb / (1000 * g) := by ring
  linarith

end

end ODELowerBoundExtensions.Dyson
