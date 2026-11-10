import DysonFullClass.Perturb
import DysonFullClass.Clip
import DysonFullClass.Select
import DysonFullClass.Atten
import ODELowerBoundExtensions.Dyson.Target
import RepresentedSampleODE.Regular
import GeneralSourceODE.Target

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The Dyson quadrature on arbitrary source nodes: coefficients, decoded vector and error

Manuscript, proof of Lemma `odel:lem:dyson`: for a branch beginning at `u`, the
degree-`k` term is the ordered integral of the represented generator over `u ≤ t₁ ≤ ⋯ ≤ t_k ≤ T`;
"When `u` lies inside a cell, use the remaining length of that first cell. The degree-zero term is
the identity, and the zero-duration branch needs no sampled factors." "If cell `j` occurs `r_j`
times [...] each cell contributes its length to power `r_j`, divided by `r_j!`." "Use the common
coefficient sequence [...] We may pad the retained coefficient mass to `e^z` with cancelling
identity terms, giving the same LCU normalisation on every source branch." "Prepare the weights
with `P_w`, load the stated data vectors, apply the coefficient phase to each source label, and
select the appropriate Dyson block on that label. Apply `P_w†` to the label alone."

Here the cell durations of a source label `a` with start time `u = startTime v a` are
`w_r(u) = max(u, t_{r+1}) - max(u, t_r)` (`meshWidth`), so a node inside a cell uses the partial
first cell, a node at `T` has only the degree-zero term, and the number and placement of nodes is
independent of the mesh.

* `cellGen σ D x r`: the represented generator `G̃_{σ r}` of cell `r` (the Lean sign `ẋ = -G x + b`);
  `cellGen_eq_smul`: it is `s Λ` times the selected block `sampleSeq` (`Λ = D.scale`).
* `nodeSeries`: the degree-`K` truncation of the represented propagator from `u`
  (`truncated (meshWidth u t) (-cellGen)`, `Series.lean`); `nodeSeries_eq_lcu`: its LCU form
  `∑_c coef(s Λ w(u)) c (-1)^{deg c} cfgProduct (sampleSeq) c` (later cells to the left, occupation
  factorials).
* `cellRatio`, `cfgAtten`, `coef_mul_cfgAtten`: the label-dependent factor
  `∏_r (w_r(u)/Δ_r)^{c_r} ∈ [0, 1]` relative to the common Dyson weights `coef(s Λ Δ) c`.
* `dysonTable α t K M N`: the common LCU table, `coef(α Δ) c (-1)^{deg}` on configurations and
  the cancelling padding pair `± (N - cellMass)/2`; `dysonTable_mass`: its mass is the one public
  normalisation `N` (here `N_D = 2 e^z`), independent of the source label and of the hidden
  source norms.
* `dysonAngle`, `cos_dysonAngle`: the public attenuation angles (`arccos` of `cfgAtten`).
* `table_sum_eq`: on every source label, `∑_l cos θ(a, l) d_l Y_l = nodeSeries (startTime v a)`.
* `dysonTarget`: the assembled quadrature `y_K = ∑_a nodeSeries(startTime v a) (z_a)` with the
  actual source vectors `z = sources x₀ bv ω`;
* `dysonTarget_error`: `‖y_K - x(T)‖ ≤ ζ B + B_q ((e^{E} - 1) + ∑_{k>K} z^k/k!)`
  against the original propagator, `E = ∑_r ∫ ‖G_r - G̃_{σ r}‖`, `z = s Λ T`, for every mild
  solution, arbitrary nodes `v_i ∈ [0, T]`, complex weights and represented samples of either sign;
* `dysonTarget_norm_le`: `‖y_K‖ ≤ B_q e^{z}`;
* `herald_window`: the amplitude window `[1/(4 g'), 1/2]` and direction error `ε/500` of
  `(2 B_q e^z)⁻¹ y_K`, with `g' = c_q ḡ e^z`, without assuming `B ≤ B_q`.
-/

namespace DysonFullClass

noncomputable section

open SparseHamiltonian ContinuousLinearMap Set MeasureTheory NativeSparseBlockEncoding
open TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (meshWidth meshWidth_nonneg meshWidth_le
  meshNodeProduct IsMeshPropagator meshScale endMap endMap_apply)
open SparseHamiltonian.GeneralSourceODE (sources phases startTime mass_sources)
open ODELowerBoundExtensions.Dyson
open scoped BigOperators InnerProduct Nat

/-! ### Durations and the attenuation factor -/

section Coefficients

variable {K M : ℕ} {t : ℕ → ℝ} {T : ℝ}

/-- The fraction of cell `r` after the start time `u`: `w_r(u)/Δ_r` (zero on an empty cell). -/
def cellRatio (t : ℕ → ℝ) (u : ℝ) (r : ℕ) : ℝ := meshWidth u t r / (t (r + 1) - t r)

theorem cellRatio_nonneg (hmesh : IsMesh t M T) (u : ℝ) (r : ℕ) : 0 ≤ cellRatio t u r :=
  div_nonneg (meshWidth_nonneg hmesh u r) (hmesh.length_nonneg r)

theorem cellRatio_le_one (hmesh : IsMesh t M T) (u : ℝ) (r : ℕ) : cellRatio t u r ≤ 1 := by
  unfold cellRatio
  rcases (hmesh.length_nonneg r).eq_or_lt with h | h
  · rw [← h, div_zero]; exact zero_le_one
  · exact (div_le_one h).mpr (meshWidth_le hmesh u r)

/-- `Δ_r · (w_r(u)/Δ_r) = w_r(u)`, also on an empty cell. -/
theorem length_mul_cellRatio (hmesh : IsMesh t M T) (u : ℝ) (r : ℕ) :
    (t (r + 1) - t r) * cellRatio t u r = meshWidth u t r := by
  unfold cellRatio
  rcases (hmesh.length_nonneg r).eq_or_lt with h | h
  · rw [← h, zero_mul]
    exact le_antisymm (h ▸ meshWidth_le hmesh u r) (meshWidth_nonneg hmesh u r) |>.symm
  · exact mul_div_cancel₀ _ h.ne'

/-- **The attenuation of a configuration** for start time `u`: `∏_r (w_r(u)/Δ_r)^{c_r}`. -/
def cfgAtten (t : ℕ → ℝ) (u : ℝ) (c : Cfg K M) : ℝ :=
  ∏ r : Fin M, cellRatio t u r ^ (c.1 r : ℕ)

theorem cfgAtten_nonneg (hmesh : IsMesh t M T) (u : ℝ) (c : Cfg K M) : 0 ≤ cfgAtten t u c :=
  Finset.prod_nonneg fun r _ => pow_nonneg (cellRatio_nonneg hmesh u r) _

theorem cfgAtten_le_one (hmesh : IsMesh t M T) (u : ℝ) (c : Cfg K M) : cfgAtten t u c ≤ 1 :=
  Finset.prod_le_one (fun r _ => pow_nonneg (cellRatio_nonneg hmesh u r) _)
    fun r _ => pow_le_one₀ (cellRatio_nonneg hmesh u r) (cellRatio_le_one hmesh u r)

/-- **Occupation weights with a partial first cell**: the common weight times the attenuation is
the Dyson weight of the start time, `coef(α Δ) c · cfgAtten u c = coef(α w(u)) c`. -/
theorem coef_mul_cfgAtten (hmesh : IsMesh t M T) (α u : ℝ) (c : Cfg K M) :
    coef (fun r => α * (t (r + 1) - t r)) c * cfgAtten t u c =
      coef (fun r => α * meshWidth u t r) c := by
  unfold coef cfgAtten
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [div_mul_eq_mul_div, ← mul_pow, mul_assoc, length_mul_cellRatio hmesh u r]

/-- The common Dyson mass `∑_c coef(α Δ) c`. -/
def cellMass (α : ℝ) (t : ℕ → ℝ) (K M : ℕ) : ℝ :=
  ∑ c : Cfg K M, coef (fun r => α * (t (r + 1) - t r)) c

theorem cellMass_nonneg (hmesh : IsMesh t M T) {α : ℝ} (hα : 0 ≤ α) : 0 ≤ cellMass α t K M :=
  Finset.sum_nonneg fun c _ => coef_nonneg _ (fun r => mul_nonneg hα (hmesh.length_nonneg r)) c

/-- `cellMass ≤ e^{α T}`. -/
theorem cellMass_le (hmesh : IsMesh t M T) {α : ℝ} (hα : 0 ≤ α) :
    cellMass α t K M ≤ Real.exp (α * T) := by
  refine (sum_coef_le_exp _ (fun r => mul_nonneg hα (hmesh.length_nonneg r)) K M).trans ?_
  rw [← Finset.mul_sum, hmesh.sum_length]

/-- **The common LCU table**: `coef(α Δ) c (-1)^{deg c}` on the configurations and the cancelling
padding pair `± (N - cellMass)/2`. -/
def dysonTable (α : ℝ) (t : ℕ → ℝ) (K M : ℕ) (N : ℝ) : LabelI K M → ℂ
  | .inl c => ((coef (fun r => α * (t (r + 1) - t r)) c * (-1) ^ c.degree : ℝ) : ℂ)
  | .inr b => (((if b then -1 else 1) * ((N - cellMass α t K M) / 2) : ℝ) : ℂ)

/-- **One public normalisation**: the mass of the common table is `N` whenever `cellMass ≤ N`. -/
theorem dysonTable_mass (hmesh : IsMesh t M T) {α : ℝ} (hα : 0 ≤ α) {N : ℝ}
    (hN : cellMass α t K M ≤ N) :
    ODECoherentLCU.coefficientMass (dysonTable α t K M N) = N := by
  unfold ODECoherentLCU.coefficientMass
  rw [Fintype.sum_sum_type, Fintype.sum_bool]
  have hpad : 0 ≤ (N - cellMass α t K M) / 2 := by linarith
  have h1 : ∑ c : Cfg K M, ‖dysonTable α t K M N (.inl c)‖ = cellMass α t K M := by
    unfold cellMass
    refine Finset.sum_congr rfl fun c _ => ?_
    have hc := coef_nonneg _ (fun r => mul_nonneg hα (hmesh.length_nonneg r)) c
    simp only [dysonTable, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
      abs_one, one_pow, mul_one, abs_of_nonneg hc]
  rw [h1]
  simp only [dysonTable, if_true, Bool.false_eq_true, if_false, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_neg, abs_one, one_mul, abs_of_nonneg hpad]
  ring

/-- **The public attenuation angle** of a source label and an LCU label: `arccos cfgAtten` on the
configurations, zero on the padding branches. -/
def dysonAngle {m : ℕ} (t : ℕ → ℝ) (v : Fin m → ℝ) : Option (Fin m) × LabelI K M → ℝ
  | (a, .inl c) => Real.arccos (cfgAtten t (startTime v a) c)
  | (_, .inr _) => 0

theorem cos_dysonAngle_inl {m : ℕ} (hmesh : IsMesh t M T) (v : Fin m → ℝ) (a : Option (Fin m))
    (c : Cfg K M) :
    Real.cos (dysonAngle t v (a, .inl c)) = cfgAtten t (startTime v a) c :=
  Real.cos_arccos (by linarith [cfgAtten_nonneg hmesh (startTime v a) c])
    (cfgAtten_le_one hmesh (startTime v a) c)

end Coefficients

/-! ### The truncated represented propagator of a node -/

section Series

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {K M : ℕ} {t : ℕ → ℝ} {T : ℝ}

/-- **The node series**: the degree-`K` truncation of the represented propagator from `u`. -/
def nodeSeries (Cs : ℕ → V →L[ℂ] V) (t : ℕ → ℝ) (K M : ℕ) (u : ℝ) : V →L[ℂ] V :=
  truncated (fun r => meshWidth u t r) (fun r => -Cs r) K M

omit [CompleteSpace V] in
/-- **The LCU form of the node series**: if `Cs r = α S r` on the cells, then
`nodeSeries u = ∑_c coef(α w(u)) c (-1)^{deg c} cfgProduct S c`. -/
theorem nodeSeries_eq_lcu (Cs S : ℕ → V →L[ℂ] V) (α : ℝ) (hCs : ∀ r < M, Cs r = α • S r)
    (u : ℝ) :
    nodeSeries Cs t K M u =
      ∑ c : Cfg K M, (coef (fun r => α * meshWidth u t r) c * (-1) ^ c.degree) • cfgProduct S c :=
  truncated_eq_of_smul _ α (fun r => -Cs r) S K M fun r hr => by rw [hCs r hr, neg_smul]

/-- The truncation error of the node series: `‖V(T,u) - nodeSeries u‖ ≤ ∑_{k>K} z^k/k!` for
`‖Cs r‖ ≤ α` and `z = α T`. -/
theorem nodeSeries_error (hmesh : IsMesh t M T) (Cs : ℕ → V →L[ℂ] V) {α : ℝ}
    (hCs : ∀ r, ‖Cs r‖ ≤ α) (u : ℝ) :
    ‖meshNodeProduct Cs t M u - nodeSeries Cs t K M u‖ ≤ expTail (α * T) K := by
  have h := truncated_error (fun r => meshWidth u t r) (fun r => meshWidth_nonneg hmesh u r)
    (fun r => -Cs r) K M
  have hy0 : 0 ≤ ∑ r ∈ Finset.range M, meshWidth u t r * ‖-Cs r‖ :=
    Finset.sum_nonneg fun r _ => mul_nonneg (meshWidth_nonneg hmesh u r) (norm_nonneg _)
  have hyle : ∑ r ∈ Finset.range M, meshWidth u t r * ‖-Cs r‖ ≤ α * T := by
    rw [← hmesh.sum_length, Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    rw [norm_neg, mul_comm α]
    exact mul_le_mul (meshWidth_le hmesh u r) (hCs r) (norm_nonneg _) (hmesh.length_nonneg r)
  exact h.trans (expTail_mono K hy0 hyle)

omit [CompleteSpace V] in
/-- `‖nodeSeries u‖ ≤ e^{α T}` for contraction blocks `S` and `Cs = α S`, `α ≥ 0`. -/
theorem nodeSeries_norm_le (hmesh : IsMesh t M T) (Cs S : ℕ → V →L[ℂ] V) {α : ℝ} (hα : 0 ≤ α)
    (hCs : ∀ r < M, Cs r = α • S r) (hS : ∀ r, ‖S r‖ ≤ 1) (u : ℝ) :
    ‖nodeSeries Cs t K M u‖ ≤ Real.exp (α * T) := by
  rw [nodeSeries_eq_lcu Cs S α hCs u]
  have hw : ∀ r, 0 ≤ α * meshWidth u t r := fun r => mul_nonneg hα (meshWidth_nonneg hmesh u r)
  calc ‖∑ c : Cfg K M, (coef (fun r => α * meshWidth u t r) c * (-1) ^ c.degree) • cfgProduct S c‖
      ≤ ∑ c : Cfg K M, coef (fun r => α * meshWidth u t r) c := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
          abs_of_nonneg (coef_nonneg _ hw c)]
        exact mul_le_of_le_one_right (coef_nonneg _ hw c) (cfgProduct_norm_le_one S hS c)
    _ ≤ Real.exp (∑ r ∈ Finset.range M, α * meshWidth u t r) := sum_coef_le_exp _ hw K M
    _ ≤ Real.exp (α * T) := by
        apply Real.exp_le_exp.mpr
        rw [← hmesh.sum_length, Finset.mul_sum]
        exact Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (meshWidth_le hmesh u r) hα

/-- The selected operator of an LCU label: `cfgProduct S c` on configurations, the identity on the
padding branches. -/
def labelOperator (S : ℕ → V →L[ℂ] V) : LabelI K M → V →L[ℂ] V
  | .inl c => cfgProduct S c
  | .inr _ => 1

omit [CompleteSpace V] in
/-- **The attenuated common table on one source label**: for start time `u`,
`∑_l cos θ(a, l) d_l Y_l = nodeSeries u` with the common table `d = dysonTable (s Λ) t K M N`,
the attenuation angles of `dysonAngle` and the padding pair cancelling. -/
theorem table_sum_eq (hmesh : IsMesh t M T) (Cs S : ℕ → V →L[ℂ] V) (α : ℝ)
    (hCs : ∀ r < M, Cs r = α • S r) (N : ℝ) {m : ℕ} (v : Fin m → ℝ) (a : Option (Fin m)) :
    ∑ l : LabelI K M, ((Real.cos (dysonAngle t v (a, l)) : ℂ) * dysonTable α t K M N l) •
        labelOperator S l =
      nodeSeries Cs t K M (startTime v a) := by
  rw [nodeSeries_eq_lcu Cs S α hCs, Fintype.sum_sum_type, Fintype.sum_bool]
  have hpad : ((Real.cos (dysonAngle t v (a, (.inr true : LabelI K M))) : ℂ) *
        dysonTable α t K M N (.inr true)) • labelOperator S (.inr true : LabelI K M) +
      ((Real.cos (dysonAngle t v (a, (.inr false : LabelI K M))) : ℂ) *
        dysonTable α t K M N (.inr false)) • labelOperator S (.inr false : LabelI K M) = 0 := by
    simp only [dysonAngle, Real.cos_zero, Complex.ofReal_one, one_mul, dysonTable, if_true,
      Bool.false_eq_true, if_false, labelOperator]
    rw [← add_smul]
    push_cast
    ring_nf
    exact zero_smul _ _
  rw [hpad, add_zero]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [labelOperator, dysonTable]
  rw [cos_dysonAngle_inl hmesh v a c, ← coef_mul_cfgAtten hmesh α (startTime v a) c,
    ← Complex.coe_smul]
  congr 1
  push_cast
  ring

end Series

/-! ### The represented cell generators of a time-indexed input -/

section Cells

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s Ks M : ℕ}

/-- The represented generator of cell `r`, `G̃_{σ r} = D.matrix (x, σ r)` (zero beyond the mesh). -/
def cellGen (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s) (x : X) :
    ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  fun r => if h : r < M then SparseStateOverlap.matrixOperator (D.matrix (x, σ ⟨r, h⟩)) else 0

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem cellGen_fin (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s) (x : X) (r : Fin M) :
    cellGen σ D x r = SparseStateOverlap.matrixOperator (D.matrix (x, σ r)) := by
  simp only [cellGen, dif_pos r.isLt, Fin.eta]

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The represented generator is `s Λ` times the selected block. -/
theorem cellGen_eq_smul (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s) (x : X) :
    ∀ r < M, cellGen σ D x r = ((s : ℝ) * D.scale) • sampleSeq σ D x r := by
  intro r hr
  simp only [cellGen, sampleSeq, dif_pos hr]
  exact matrixOperator_eq_smul D x _

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- `‖G̃_{σ r}‖ ≤ s Λ`. -/
theorem cellGen_norm_le (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s) (x : X) (r : ℕ) :
    ‖cellGen σ D x r‖ ≤ (s : ℝ) * D.scale := by
  unfold cellGen
  split_ifs with h
  · exact MeshSampling.generator_norm_le D (fun _ => σ ⟨r, h⟩) x 0
  · rw [norm_zero]
    exact mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le

/-- The selected blocks are contractions. -/
theorem sampleSeq_norm_le (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s) (x : X) (r : ℕ) :
    ‖sampleSeq σ D x r‖ ≤ 1 := by
  unfold sampleSeq
  split_ifs
  · exact sampleOperator_norm_le D x _
  · rw [norm_zero]; exact zero_le_one

/-- **The certified generator error** `E = ∑_r ∫_{t_r}^{t_{r+1}} ‖G_r(u) - G̃_{σ r}‖ du` of the
represented samples (operator norm; time variation and representation error together). -/
def cellError (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s) (x : X) (t : ℕ → ℝ)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) : ℝ :=
  ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
    ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, σ r))‖

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem cellError_nonneg (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s) (x : X)
    {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    0 ≤ cellError σ D x t G :=
  Finset.sum_nonneg fun r _ =>
    intervalIntegral.integral_nonneg (hmesh.mono (Nat.le_succ r)) fun _ _ => norm_nonneg _

end Cells

/-! ### The assembled quadrature and its error -/

section TargetError

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s Ks M : ℕ}

/-- **The assembled Dyson quadrature** `y_K = ∑_a nodeSeries(startTime v a) (z_a)`, with the actual
source vectors `z = sources x₀ bv ω` (`z_none = x₀`, `z_i = ω_i b(v_i)`). -/
def dysonTarget (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s) (x : X) (t : ℕ → ℝ) (K : ℕ)
    {m : ℕ} (v : Fin m → ℝ) (x₀ : EuclideanSpace ℂ n) (bv : Fin m → EuclideanSpace ℂ n)
    (ω : Fin m → ℂ) : EuclideanSpace ℂ n :=
  ∑ a, nodeSeries (cellGen σ D x) t K M (startTime v a) (sources x₀ bv ω a)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
set_option maxHeartbeats 2000000 in
/-- **The error of the assembled quadrature** (proof of Lemma `odel:lem:dyson`):
for accretive integrable true pieces with mesh propagator `U` (classical on every closed cell), a
mild solution, any source nodes `v_i ∈ [0, T]`, complex weights `ω_i`, forcing samples `bv_i` with
the source certificate `‖∑_r ∫ U(T,u) b_r(u) du - ∑_i ω_i U(T, v_i) b(v_i)‖ ≤ ζ B`, and represented
samples of either sign with generator error `E`,
`‖y_K - x(T)‖ ≤ ζ B + B_q ((e^{E} - 1) + ∑_{k>K} z^k/k!)`, `z = s Λ T`, `B_q = mass z`. -/
theorem dysonTarget_error {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T) (hT : 0 ≤ T)
    (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s) (x : X)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGint : RepresentedSampleODE.RegularPieces t G)
    (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (hU : IsMeshPropagator G t T U)
    (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
    (hmild : RepresentedSampleODE.MildSolution t T b sol U)
    {m : ℕ} (v : Fin m → ℝ) (hv : ∀ i, v i ∈ Icc 0 T) (bv : Fin m → EuclideanSpace ℂ n)
    (ω : Fin m → ℂ) (ζ : ℝ)
    (hsrc : ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
        ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t) (K : ℕ) :
    ‖dysonTarget σ D x t K v (sol 0) bv ω - sol T‖ ≤
      ζ * meshScale sol b t + ODESourceBranches.mass (sources (sol 0) bv ω) *
        ((Real.exp (cellError σ D x t G) - 1) + expTail ((s : ℝ) * D.scale * T) K) := by
  classical
  set Cs := cellGen σ D x with hCsdef
  set δ := (Real.exp (cellError σ D x t G) - 1) + expTail ((s : ℝ) * D.scale * T) K with hδ
  -- one branch: the truncated series against the true propagator
  have hbranch : ∀ (u : ℝ), u ∈ Icc 0 T → ∀ w : EuclideanSpace ℂ n,
      ‖nodeSeries Cs t K M u w - U u w T‖ ≤ δ * ‖w‖ := by
    intro u hu w
    have hP := (propagator_perturb hmesh G hG hGint U hU Cs hu w).2
    have hSum : ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖G r u - Cs r‖ = cellError σ D x t G := by
      unfold cellError
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hCsdef, cellGen_fin]
    rw [hSum] at hP
    have hS := nodeSeries_error (K := K) hmesh Cs (cellGen_norm_le σ D x) u
    have hS' : ‖nodeSeries Cs t K M u w - meshNodeProduct Cs t M u w‖ ≤
        expTail ((s : ℝ) * D.scale * T) K * ‖w‖ := by
      have h := (le_opNorm (meshNodeProduct Cs t M u - nodeSeries Cs t K M u) w).trans
        (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
      rw [sub_apply, norm_sub_rev] at h
      exact h
    calc ‖nodeSeries Cs t K M u w - U u w T‖
        ≤ ‖nodeSeries Cs t K M u w - meshNodeProduct Cs t M u w‖ +
            ‖meshNodeProduct Cs t M u w - U u w T‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ expTail ((s : ℝ) * D.scale * T) K * ‖w‖ +
            ‖w‖ * (Real.exp (cellError σ D x t G) - 1) := by
          refine add_le_add hS' ?_
          rw [norm_sub_rev]; exact hP
      _ = δ * ‖w‖ := by rw [hδ]; ring
  -- the propagated source sum
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hlin : ∀ i, U (v i) (ω i • bv i) T = ω i • U (v i) (bv i) T := by
    intro i
    have h := (endMap hmesh hU hG (hv i)).map_smul (ω i) (bv i)
    simpa only [endMap_apply] using h
  have hprop : ‖(U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T) - sol T‖ ≤ ζ * meshScale sol b t := by
    rw [hmild.2]
    have : (U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T) -
        (U 0 (sol 0) T + ∑ r : Fin M, ∫ v in t r..t ((r : ℕ) + 1), U v (b r v) T) =
        -((∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
          ∑ i, ω i • U (v i) (bv i) T) := by abel
    rw [this, norm_neg]
    exact hsrc
  have hsplit : dysonTarget σ D x t K v (sol 0) bv ω - (U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T) =
      (nodeSeries Cs t K M 0 (sol 0) - U 0 (sol 0) T) +
        ∑ i, (nodeSeries Cs t K M (v i) (ω i • bv i) - U (v i) (ω i • bv i) T) := by
    unfold dysonTarget
    rw [Fintype.sum_option, Finset.sum_sub_distrib]
    simp only [startTime, sources, hlin, hCsdef]
    abel
  have hbound : ‖dysonTarget σ D x t K v (sol 0) bv ω - (U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T)‖ ≤
      ODESourceBranches.mass (sources (sol 0) bv ω) * δ := by
    rw [hsplit, mass_sources]
    calc _ ≤ ‖nodeSeries Cs t K M 0 (sol 0) - U 0 (sol 0) T‖ +
          ∑ i, ‖nodeSeries Cs t K M (v i) (ω i • bv i) - U (v i) (ω i • bv i) T‖ :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
      _ ≤ δ * ‖sol 0‖ + ∑ i, δ * ‖ω i • bv i‖ :=
          add_le_add (hbranch 0 h0T _) (Finset.sum_le_sum fun i _ => hbranch (v i) (hv i) _)
      _ = (‖sol 0‖ + ∑ i, ‖ω i‖ * ‖bv i‖) * δ := by
          simp only [norm_smul]
          rw [← Finset.mul_sum]
          ring
  calc ‖dysonTarget σ D x t K v (sol 0) bv ω - sol T‖
      ≤ ‖dysonTarget σ D x t K v (sol 0) bv ω - (U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T)‖ +
          ‖(U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T) - sol T‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ODESourceBranches.mass (sources (sol 0) bv ω) * δ + ζ * meshScale sol b t :=
        add_le_add hbound hprop
    _ = _ := by rw [hδ]; ring

/-- `‖y_K‖ ≤ B_q e^{z}`, `z = s Λ T`. -/
theorem dysonTarget_norm_le {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s) (x : X) (K : ℕ) {m : ℕ}
    (v : Fin m → ℝ) (x₀ : EuclideanSpace ℂ n) (bv : Fin m → EuclideanSpace ℂ n) (ω : Fin m → ℂ) :
    ‖dysonTarget σ D x t K v x₀ bv ω‖ ≤
      ODESourceBranches.mass (sources x₀ bv ω) * Real.exp ((s : ℝ) * D.scale * T) := by
  have hα : 0 ≤ (s : ℝ) * D.scale := mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le
  unfold dysonTarget ODESourceBranches.mass
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (le_opNorm _ _).trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (nodeSeries_norm_le hmesh _ (sampleSeq σ D x) hα
    (cellGen_eq_smul σ D x) (sampleSeq_norm_le σ D x) _) (norm_nonneg _)

end TargetError

/-! ### The amplitude window -/

/-- **Amplitude window and direction error of the decoded Dyson vector** (no `B ≤ m` premise): for
`m > 0`, `B > 0`, `ḡ ≥ 1`, `0 < ε ≤ 1`, `B ≤ ḡ ‖x‖`, `‖y‖ ≤ m` and `‖y - x‖ ≤ ε B/(1000 ḡ)`,
the vector `(2m)⁻¹ y` has norm in `[1/(4 (ḡ m/B)), 1/2]` and direction within `ε/500` of `x`. -/
theorem herald_window {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (y x : E) (m B g ε : ℝ) (hB : 0 < B) (hm : 0 < m) (hg : 1 ≤ g) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hx : B ≤ g * ‖x‖) (hy : ‖y‖ ≤ m)
    (herr : ‖y - x‖ ≤ ε * B / (1000 * g)) :
    1 / (4 * (g * m / B)) ≤ ‖((2 * m : ℝ) : ℂ)⁻¹ • y‖ ∧
      ‖((2 * m : ℝ) : ℂ)⁻¹ • y‖ ≤ 1 / 2 ∧
      ‖ODEStateNormalization.unitDirection (((2 * m : ℝ) : ℂ)⁻¹ • y) -
          ODEStateNormalization.unitDirection x‖ ≤ ε / 500 := by
  have hg0 : 0 < g := by linarith
  have hBg : B / g ≤ ‖x‖ := by
    rw [div_le_iff₀ hg0]; linarith
  have hx0 : 0 < ‖x‖ := lt_of_lt_of_le (div_pos hB hg0) hBg
  have hxne : x ≠ 0 := norm_pos_iff.mp hx0
  have hErrSmall : ‖y - x‖ ≤ B / (2 * g) := by
    refine herr.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hB hg0]
  have hyLower : B / (2 * g) ≤ ‖y‖ := by
    have hTri : ‖x‖ ≤ ‖y‖ + ‖y - x‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub x y 0
      simpa only [sub_zero, norm_sub_rev x y, add_comm] using this
    have hHalf : B / (2 * g) = B / g - B / (2 * g) := by
      field_simp; ring
    linarith
  have hy0 : 0 < ‖y‖ := lt_of_lt_of_le (by positivity) hyLower
  have hyne : y ≠ 0 := norm_pos_iff.mp hy0
  have hScal : ((2 * m : ℝ) : ℂ)⁻¹ • y = ((2 * m)⁻¹ : ℝ) • y := by
    rw [← Complex.ofReal_inv, Complex.coe_smul]
  have hNorm : ‖((2 * m : ℝ) : ℂ)⁻¹ • y‖ = ‖y‖ / (2 * m) := by
    rw [hScal, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hNorm]
    have hEq : 1 / (4 * (g * m / B)) = (B / (2 * g)) / (2 * m) := by
      field_simp; ring
    rw [hEq]
    exact div_le_div_of_nonneg_right hyLower (by positivity)
  · rw [hNorm, div_le_iff₀ (by positivity)]
    linarith
  · rw [hScal, ODEHeraldedSuccess.unitDirection_pos_smul _ (by positivity) y]
    refine (ODEStateNormalization.unitDirection_error_le x y hxne hyne).trans ?_
    rw [div_le_iff₀ hx0]
    have h2 : 2 * (ε * B / (1000 * g)) ≤ ε / 500 * ‖x‖ := by
      rw [div_le_iff₀ hg0] at hBg
      have : 2 * (ε * B / (1000 * g)) = ε * B / (500 * g) := by field_simp; ring
      rw [this, div_le_iff₀ (by positivity)]
      nlinarith
    calc 2 * ‖y - x‖ ≤ 2 * (ε * B / (1000 * g)) := by linarith
      _ ≤ _ := h2

end

end DysonFullClass
