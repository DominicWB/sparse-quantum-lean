import GeneralSourceExtensions.Mesh.Durations
import GeneralSourceExtensions.Mesh.Oracles
import GeneralSourceODE.Theorem

/-!
# The general source interface on nonuniform meshes with integrated certificates

Theorem `ode:thm:time` with the source access of eqs. `ode:eq:source-interface-mass` and
`ode:eq:source-interface-preparation` on an arbitrary mesh `0 = t_0 ≤ ⋯ ≤ t_M = T`
(`TimeDependentExtensions.IsMesh`), with one generator piece `G_r` and one forcing piece `b_r`
per interval (breakpoints at the mesh points), one represented sample `G̃_r = D.matrix (x, r)`
per interval, and the integrated sample-error certificate

  `ΔG = ∑_r ∫_{t_r}^{t_{r+1}} ‖G_r(u) - G̃_r‖ du`   (`sampleError`)

in place of the Lipschitz and pointwise sample bounds of the released uniform-mesh theorem. The
clock runs on `N` uniform slots, slot `k` reading the sample of the interval containing `k T/N`
(`TimeDependentExtensions.MeshSelect`); the public nodes `v_i ∈ [0, T]` need not be mesh points.
The source vectors are `x(0)` and `ω_i b_i` for supplied node forcing values `b_i` (in the
manuscript `b(v_i)`), the source scale is `B = ‖x(0)‖ + ∑_r ∫ ‖b_r‖` (`meshScale`), and the
propagator `U` of the piecewise homogeneous equation is a hypothesis (`IsMeshPropagator`). The
certificate is stated on the propagated source sum,
`‖x(T) - U(T, 0) x(0) - ∑ ω_i U(T, v_i) b_i‖ ≤ ζ B`, as in `GeneralSourceODE.propagated_solver`.

* `refinementError`: the refinement term `ΔR = s Λ ∑_r |c_r T / N - Δ_r|` of the rounding of
  the interval lengths to whole slots, at most `s Λ M T / N` and zero when the mesh points lie on
  the slot grid;
* `mesh_target_error`: the represented target `meshTarget` is within `(ΔG + ΔR) B_q` of the
  propagated source sum;
* `mesh_propagated_solver`: under the slot conditions `8 s ρ T ≤ N`, `3 (√(2s) ρ T)³ ≤ ν N²` and
  the budget `ζ + c_q (ΔG + ΔR) ≤ ε / (2000 ḡ)`, one public trial family over the two counted
  source interfaces satisfies the released complete certificate (`MeshPropagatedOutcome`);
* the same over the actual oracles `P_w`, `U_load`, `P_w†` is `mesh_solver` in `Mesh/Actual.lean`
  (`MeshOutcome`), with the released query bounds; neither `M`, `N`, the mesh nor the
  certificates enter them.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralSourceExtensions.Mesh

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set MeasureTheory
open TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE ratio accuracy radius precision
  lipschitz Index lchsCoefficients retarget)
open SparseHamiltonian.GeneralSourceODE (startTime sources phases phases_norm mass_sources
  phased_isometry phased_prepares nodeTable)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-! ### Scales and certificates -/

/-- The source scale on a mesh, `B = ‖x(0)‖ + ∑_r ∫_{t_r}^{t_{r+1}} ‖b_r‖`. -/
def meshScale {V : Type*} [NormedAddCommGroup V] (sol : ℝ → V) (b : Fin M → ℝ → V)
    (t : ℕ → ℝ) : ℝ :=
  ‖sol 0‖ + ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖b r u‖

/-- The integrated sample-error certificate of the generator pieces. -/
def sampleError (D : Data (X × Fin M) n Z s) (x : X) (t : ℕ → ℝ)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) : ℝ :=
  ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
    ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, r))‖

/-- The refinement of the mesh into `N` slots, per unit of source mass:
`s Λ ∑_{r < M} |c_r T / N - Δ_r|` with `Λ = D.scale` and `c_r` slots in interval `r`
(`roundingError`). It is at most `s Λ M T / N` (`refinementError_le`) and vanishes when the
mesh points lie on the slot grid, for example on the uniform mesh with `N = q M`
(`refinementError_uniform`). -/
def refinementError (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (T : ℝ) (N : ℕ) : ℝ :=
  (s : ℝ) * D.scale * roundingError t T N M

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem meshScale_nonneg {V : Type*} [NormedAddCommGroup V] {t : ℕ → ℝ} {T : ℝ}
    (hmesh : IsMesh t M T) (sol : ℝ → V) (b : Fin M → ℝ → V) : 0 ≤ meshScale sol b t :=
  add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun r _ =>
    intervalIntegral.integral_nonneg (hmesh.mono (Nat.le_succ r)) fun _ _ => norm_nonneg _)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem sampleError_nonneg (D : Data (X × Fin M) n Z s) (x : X) {t : ℕ → ℝ} {T : ℝ}
    (hmesh : IsMesh t M T) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    0 ≤ sampleError D x t G :=
  Finset.sum_nonneg fun r _ =>
    intervalIntegral.integral_nonneg (hmesh.mono (Nat.le_succ r)) fun _ _ => norm_nonneg _

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem refinementError_nonneg (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (T : ℝ) (N : ℕ) :
    0 ≤ refinementError D t T N :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le) (roundingError_nonneg t T N M)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The refinement term is at most `s Λ M T / N`. -/
theorem refinementError_le (D : Data (X × Fin M) n Z s) {t : ℕ → ℝ} {T : ℝ}
    (hmesh : IsMesh t M T) (hT : 0 ≤ T) {N : ℕ} (hN : 0 < N) :
    refinementError D t T N ≤ (s : ℝ) * D.scale * (M * (T / N)) :=
  mul_le_mul_of_nonneg_left (roundingError_le hmesh hT hN)
    (mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- On the uniform mesh `t_r = r T / M` with `N = q M` slots, `q > 0`, the refinement term
vanishes. -/
theorem refinementError_uniform (D : Data (X × Fin M) n Z s) (hM : 0 < M) {T : ℝ} (hT : 0 ≤ T)
    {q : ℕ} (hq : 0 < q) : refinementError D (fun r : ℕ => (r : ℝ) * T / M) T (q * M) = 0 := by
  rw [refinementError, roundingError_uniform hM hT hq, mul_zero]

/-! ### The represented target -/

/-- The represented target: every source branch propagated by the slot product of its public
table, the family of its label at `-i`. -/
def meshTarget (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (T : ℝ) (N : ℕ) {m : ℕ}
    (v : Fin m → ℝ) (x : X) (x₀ : EuclideanSpace ℂ n) (bv : Fin m → EuclideanSpace ℂ n)
    (ω : Fin m → ℂ) : EuclideanSpace ℂ n :=
  ∑ a, tableFamily D (pieceOf t T N hM) N (meshDurations t T v) x a (-Complex.I)
    (sources x₀ bv ω a)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The target norm is at most the source mass. -/
theorem meshTarget_norm_le (D : Data (X × Fin M) n Z s) (hM : 0 < M) {t : ℕ → ℝ} {T : ℝ}
    (hmesh : IsMesh t M T) (hT : 0 ≤ T) (N : ℕ) {m : ℕ} (v : Fin m → ℝ)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (x : X) (x₀ : EuclideanSpace ℂ n) (bv : Fin m → EuclideanSpace ℂ n) (ω : Fin m → ℂ) :
    ‖meshTarget D hM t T N v x x₀ bv ω‖ ≤ ODESourceBranches.mass (sources x₀ bv ω) := by
  unfold meshTarget ODESourceBranches.mass
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  calc
    _ ≤ ‖tableFamily D (pieceOf t T N hM) N (meshDurations t T v) x a (-Complex.I)‖ *
        ‖sources x₀ bv ω a‖ := le_opNorm _ _
    _ ≤ 1 * ‖sources x₀ bv ω a‖ := mul_le_mul_of_nonneg_right
        (tableFamily_norm_le_one D _ N _ (meshDurations_nonneg hmesh hT v) hPSD x a _
          (by simp)) (norm_nonneg _)
    _ = ‖sources x₀ bv ω a‖ := one_mul _

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
set_option maxHeartbeats 2000000 in
/-- **One source branch.** The propagation of `w` from the start time of a label against the
slot product of its public table: at most `(ΔG + ΔR) ‖w‖`, `ΔR = refinementError`. -/
theorem branch_error (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (x : X) {t : ℕ → ℝ} {T : ℝ} {N : ℕ} (hmesh : IsMesh t M T) (hT : 0 ≤ T) (hN : 0 < N)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGint : ∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1)))
    (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (hU : IsMeshPropagator G t T U)
    {m : ℕ} (v : Fin m → ℝ) (a : Option (Fin m)) (ha : startTime v a ∈ Icc 0 T)
    (w : EuclideanSpace ℂ n) :
    ‖U (startTime v a) w T -
        tableFamily D (pieceOf t T N hM) N (meshDurations t T v) x a (-Complex.I) w‖ ≤
      (sampleError D x t G + refinementError D t T N) * ‖w‖ := by
  classical
  set idx : ℕ → Fin M := TimeDependent.Sampled.sampleIndex hM with hidx
  have hidxlt : ∀ r (hr : r < M), idx r = ⟨r, hr⟩ := fun r hr =>
    Fin.ext (Nat.mod_eq_of_lt hr)
  let Gs : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
    SparseStateOverlap.matrixOperator (D.matrix (x, idx r))
  let Gq : ℕ → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r => G (idx r)
  set Λ : ℝ := (s : ℝ) * D.scale with hΛdef
  have hGs : ∀ r, Accretive (Gs r) := fun r =>
    MeshSampling.generator_accretive D (fun _ => idx r) hPSD x 0
  have hGsn : ∀ r, ‖Gs r‖ ≤ Λ := fun r => MeshSampling.generator_norm_le D (fun _ => idx r) x 0
  have hGq : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), Accretive (Gq r u) := by
    intro r hr u hu
    change Accretive (G (idx r) u)
    rw [hidxlt r hr]
    exact hG ⟨r, hr⟩ u hu
  have hGqint : ∀ r < M, IntervalIntegrable (Gq r) volume (t r) (t (r + 1)) := by
    intro r hr
    change IntervalIntegrable (G (idx r)) volume (t r) (t (r + 1))
    rw [hidxlt r hr]
    exact hGint ⟨r, hr⟩
  obtain ⟨h0, hsol⟩ := hU (startTime v a) ha w
  have hsolq : ∀ r < M, startTime v a ≤ t (r + 1) →
      SolvesODE (Gq r) 0 (U (startTime v a) w) (max (startTime v a) (t r)) (t (r + 1)) := by
    intro r hr hst
    change SolvesODE (G (idx r)) 0 (U (startTime v a) w) (max (startTime v a) (t r)) (t (r + 1))
    rw [hidxlt r hr]
    exact hsol ⟨r, hr⟩ hst
  -- The mesh product against the propagator.
  have hNode := node_error_nat hmesh Gq hGq hGqint Gs hGs ha (U (startTime v a) w) hsolq
  rw [h0] at hNode
  have hSum : ∑ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖Gq r u - Gs r‖ =
      sampleError D x t G := by
    rw [← Fin.sum_univ_eq_sum_range (fun r => ∫ u in t r..t (r + 1), ‖Gq r u - Gs r‖) M]
    unfold sampleError
    apply Finset.sum_congr rfl
    intro r _
    simp only [Gq, Gs, hidxlt r r.isLt]
  rw [hSum] at hNode
  -- The slot product against the mesh product.
  have hSlot : tableFamily D (pieceOf t T N hM) N (meshDurations t T v) x a (-Complex.I) =
      TimeDependent.evolution (fun k => NormedSpace.exp
        ((T * meshWidth (startTime v a) t (slotPiece t T N M k) /
            (t (slotPiece t T N M k + 1) - t (slotPiece t T N M k)) / N) •
          (-Gs (slotPiece t T N M k)))) N := by
    rw [tableFamily_neg_I]
    congr 1
    funext k
    have hk : idx (slotPiece t T N M k) = pieceOf t T N hM k :=
      Fin.ext (Nat.mod_eq_of_lt (slotPiece_lt hM k))
    simp only [MeshSampling.generator, Gs, hk]
    rfl
  have hRef := refined_sub_le_of_nonneg hmesh hT hN Gs hGs hGsn v a
  rw [← hSlot] at hRef
  have hRef' : ‖meshNodeProduct Gs t M (startTime v a) w -
      tableFamily D (pieceOf t T N hM) N (meshDurations t T v) x a (-Complex.I) w‖ ≤
        refinementError D t T N * ‖w‖ := by
    rw [← sub_apply]
    refine (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [norm_sub_rev]
    refine hRef.trans (le_of_eq ?_)
    unfold refinementError
    ring
  calc _ ≤ ‖U (startTime v a) w T - meshNodeProduct Gs t M (startTime v a) w‖ +
        ‖meshNodeProduct Gs t M (startTime v a) w -
          tableFamily D (pieceOf t T N hM) N (meshDurations t T v) x a (-Complex.I) w‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖w‖ * sampleError D x t G + refinementError D t T N * ‖w‖ := add_le_add hNode hRef'
    _ = (sampleError D x t G + refinementError D t T N) * ‖w‖ := by ring

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
set_option maxHeartbeats 2000000 in
/-- **The certified distance of the represented target from the propagated source sum.** -/
theorem mesh_target_error (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (x : X) {t : ℕ → ℝ} {T : ℝ} {N : ℕ} (hmesh : IsMesh t M T) (hT : 0 ≤ T) (hN : 0 < N)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGint : ∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1)))
    (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (hU : IsMeshPropagator G t T U)
    {m : ℕ} (v : Fin m → ℝ) (hv : ∀ i, v i ∈ Icc 0 T) (ω : Fin m → ℂ)
    (x₀ : EuclideanSpace ℂ n) (bv : Fin m → EuclideanSpace ℂ n) :
    ‖(U 0 x₀ T + ∑ i, ω i • U (v i) (bv i) T) - meshTarget D hM t T N v x x₀ bv ω‖ ≤
      (sampleError D x t G + refinementError D t T N) *
        ODESourceBranches.mass (sources x₀ bv ω) := by
  set K := sampleError D x t G + refinementError D t T N with hK
  set F := fun a => tableFamily D (pieceOf t T N hM) N (meshDurations t T v) x a (-Complex.I)
    with hF
  have hInit : ‖U 0 x₀ T - F none x₀‖ ≤ K * ‖x₀‖ :=
    branch_error D hM hPSD x hmesh hT hN G hG hGint U hU v none ⟨le_rfl, hT⟩ x₀
  have hNode : ∀ i, ‖ω i • U (v i) (bv i) T - F (some i) (ω i • bv i)‖ ≤
      K * (‖ω i‖ * ‖bv i‖) := by
    intro i
    have h := branch_error D hM hPSD x hmesh hT hN G hG hGint U hU v (some i) (hv i) (bv i)
    have hsplit : ω i • U (v i) (bv i) T - F (some i) (ω i • bv i) =
        ω i • (U (v i) (bv i) T - F (some i) (bv i)) := by
      rw [map_smul, smul_sub]
    rw [hsplit, norm_smul]
    calc ‖ω i‖ * ‖U (v i) (bv i) T - F (some i) (bv i)‖ ≤ ‖ω i‖ * (K * ‖bv i‖) :=
          mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = K * (‖ω i‖ * ‖bv i‖) := by ring
  have hTarget : meshTarget D hM t T N v x x₀ bv ω =
      F none x₀ + ∑ i, F (some i) (ω i • bv i) := by
    unfold meshTarget
    rw [Fintype.sum_option]
    rfl
  have hsplit : (U 0 x₀ T + ∑ i, ω i • U (v i) (bv i) T) - meshTarget D hM t T N v x x₀ bv ω =
      (U 0 x₀ T - F none x₀) + ∑ i, (ω i • U (v i) (bv i) T - F (some i) (ω i • bv i)) := by
    rw [hTarget, Finset.sum_sub_distrib]
    abel
  rw [hsplit, mass_sources]
  calc
    _ ≤ ‖U 0 x₀ T - F none x₀‖ +
        ∑ i, ‖ω i • U (v i) (bv i) T - F (some i) (ω i • bv i)‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ K * ‖x₀‖ + ∑ i, K * (‖ω i‖ * ‖bv i‖) :=
      add_le_add hInit (Finset.sum_le_sum fun i _ => hNode i)
    _ = K * (‖x₀‖ + ∑ i, ‖ω i‖ * ‖bv i‖) := by
      rw [← Finset.mul_sum]
      ring

/-! ### The solver -/

/-- **One public trial family on a mesh** (two counted source interfaces), chosen before every
unknown instance: matrix input, generator and forcing pieces, solution, node forcing values,
propagator and source data. -/
def MeshPropagatedOutcome (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (d : ℕ)
    (E : GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m →L[ℂ]
      MeshNative.MatrixSpace (Index D T (cq * gbar) ε) n Z m M N d)
    (_hE : E† ∘L E = 1)
    (q : ℕ → MultiOracleCircuit.Program
      (MeshNative.physicalOracle (ι := Index D T (cq * gbar) ε) D m N d Pw J (phases ω))),
    (∀ j y, IsUnitary ((q j).eval y)) ∧
    ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bv : Fin m → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) →
      (∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) →
      IsMeshPropagator G t T U →
      GeneralSourceODE.Compiled.WeightPrep (Pw x) (sources (sol 0) bv ω) →
      (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → bv i ≠ 0 → J x (some i) seed =
        ODEStateNormalization.unitDirection (bv i)) →
      ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t →
      ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
      sol T ≠ 0 →
      meshScale sol b t ≤ gbar * ‖sol T‖ →
      ζ + cq * (sampleError D x t G + refinementError D t T N) ≤ ε / (2000 * gbar) →
      ODECompleteTrial.Certificate q
        (ODEGroverAverage.chosenIterations (ratio (cq * gbar)))
        (MeshNative.input D hM (Sum.inr false) m N d
          (ODECompiledSource.seed E
            (GeneralSourceODE.Compiled.seedCoefficients
              (lchsCoefficients D T (cq * gbar) ε)) seed))
        (MeshNative.input D hM (Sum.inr false) m N d ∘L
          ODECompiledSource.output E
            (GeneralSourceODE.Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)))
        x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:time` with the general source interface on a mesh** (two counted source
interfaces). Under uniform sparse energy bounds `η_H`, `η_D`, positivity of every sampled
dissipative part, the slot conditions `8 s ρ T ≤ N` and `3 (√(2s) ρ T)³ ≤ ν N²` at the
amplification ratio `2 c_q ḡ`, and public nodes in `[0, T]`, one public trial family satisfies the
released complete certificate for every instance whose pieces are accretive and
interval-integrable, whose propagator is `U`, whose supplied weight and loading oracles prepare the
source weights and directions, whose coefficient mass is at most `c_q B`, whose propagated source
sum is within `ζ B` of the solution, whose solution is nonzero with `B ≤ ḡ ‖x(T)‖`, and whose budget
`ζ + c_q (ΔG + ΔR)` is at most `ε / (2000 ḡ)` (`ΔR = refinementError ≤ s Λ M T / N`). -/
theorem mesh_propagated_solver (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 < T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : IsMesh t M T)
    (hρ : 0 < etaH + radius (cq * gbar) ε * etaD)
    (hClock : 8 * s * ((etaH + radius (cq * gbar) ε * etaD) * T) ≤ N)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
        precision (cq * gbar) ε * (N : ℝ) ^ 2)
    (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    MeshPropagatedOutcome D hM t N etaH etaD T gbar cq ε v ω Pw J seed := by
  set g : ℝ := cq * gbar with hgdef
  have hg1 : 1 ≤ g := by nlinarith
  have hg' : 1 ≤ ratio g := by unfold ratio; linarith
  have hε' : 0 < accuracy ε := by unfold accuracy; linarith
  have hε'One : accuracy ε ≤ 1 := by unfold accuracy; linarith
  have hε'Half : accuracy ε ≤ 1 / 2 := by unfold accuracy; linarith
  have hν : 0 < precision g ε := ImprovedODEQueryBudget.precision_pos _ _ hg' hε'
  have hνOne : precision g ε ≤ 1 :=
    (ImprovedODEQueryBudget.precision_le_one_ten_thousandth _ _ hg' hε'One).trans
      (by norm_num)
  have hR : 0 ≤ radius g ε := ImprovedODEQueryBudget.radius_nonneg _ _ hg' hε' hε'One
  let σ : ℕ → Fin M := pieceOf t T N hM
  have hu0 : ∀ a r, 0 ≤ meshDurations t T v a r := meshDurations_nonneg hmesh hT.le v
  have huT : ∀ a r, meshDurations t T v a r ≤ T := meshDurations_le hmesh hT.le v
  -- One public Gaussian table for every product family.
  have hL : 0 ≤ lipschitz D T :=
    mul_nonneg hT.le (mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le)
  obtain ⟨_hGrid, hNodes, hMass, hApprox⟩ := TimeDependentODE.GaussianLCHS.table_certificate
    (fun y : X × Option (Fin m) => tableFamily D σ N (meshDurations t T v) y.1 y.2)
    (fun y z => tableFamily_analyticAt D σ N _ y.1 y.2 z)
    (fun y z hz => tableFamily_norm_le_one D σ N _ hu0 hPSD y.1 y.2 z hz)
    (lipschitz D T) hL (fun y k l => tableFamily_lipschitz D σ hN _ hu0 huT y.1 y.2 k l)
    (ratio g) (accuracy ε) hg' hε' hε'One
  have hc : ODECoherentLCU.coefficientMass (lchsCoefficients D T g ε) = 3 :=
    ODECoefficientPadding.coefficientMass_eq _ 3 hMass
  -- One public SELECT program on `N` slots for the public node and duration tables.
  let i0 : Index D T g ε := Sum.inr false
  obtain ⟨γ, _hγ, _hγOne, _hWidth, hTables⟩ :=
    MeshSelect.select (ι := GeneralSourceODE.Native.Label (Index D T g ε) m) D hM σ hN
      (GeneralSourceODE.Native.dummy hM i0 m) etaH etaD (radius g ε) T (precision g ε)
      hH hDiss hρ hT hν hνOne hrH hcH hrD hcD hClock hCayley
  have hk : ∀ a, |nodeTable D T g ε m a| ≤ radius g ε := fun a =>
    ODECoefficientPadding.paddedNodes_bound _ _ hR hNodes a.2
  have hu : ∀ (a : GeneralSourceODE.Native.Label (Index D T g ε) m) (r : Fin M),
      0 ≤ meshTable t T v a r := fun a r => hu0 a.1 r
  have huT' : ∀ (a : GeneralSourceODE.Native.Label (Index D T g ε) m) (r : Fin M),
      meshTable t T v a r ≤ T := fun a r => huT a.1 r
  obtain ⟨p, hCount, hE, hAct⟩ := hTables (nodeTable D T g ε m) (meshTable t T v) hk hu huT'
  let d := TimeDependentODE.Select.degree (s : ℝ) γ (etaH + radius g ε * etaD) T
    (precision g ε) N
  let E : GeneralSourceODE.Native.SourceSpace (Index D T g ε) n m →L[ℂ]
      MeshNative.MatrixSpace (Index D T g ε) n Z m M N d :=
    MeshSelect.alignedInput D hM σ (GeneralSourceODE.Native.dummy hM i0 m) N γ
      (etaH + radius g ε * etaD) T (precision g ε)
  have hEiso : E† ∘L E = 1 := hE
  let pN : MultiOracleCircuit.Program
      (MeshNative.matrixOracle (ι := Index D T g ε) D m N d) := p
  let c := lchsCoefficients D T g ε
  have hcpos : 0 < ODECoherentLCU.coefficientMass c := by
    change 0 < ODECoherentLCU.coefficientMass (lchsCoefficients D T g ε)
    rw [hc]
    norm_num
  have hsc : 0 < ODECoherentLCU.coefficientMass
      (GeneralSourceODE.Compiled.seedCoefficients (N := m) c) := by
    rw [GeneralSourceODE.Compiled.seedCoefficients_mass]
    exact hcpos
  have hSeedUnit := ODECompiledSource.seed_unit E
    (GeneralSourceODE.Compiled.seedCoefficients c) hEiso hsc seed hSeed
  have hOutput := ODECompiledSource.output_isometry E
    (GeneralSourceODE.Compiled.seedCoefficients c) hEiso hsc
  let q := MeshNative.publicTrials D hM i0 m N d pN Pw J (phases ω) E hEiso c seed
    hSeedUnit hOutput
  have hq : (pN.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ)
      (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
      (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) :=
    ODEFinitePropagator.query_bound p.count (s : ℝ) etaH etaD T (ratio g) (accuracy ε)
      (Nat.cast_nonneg s) hH hDiss hT.le hg' hε' hε'One hCount
  have hOracle := MeshNative.physicalOracle_unitary (ι := Index D T g ε) D m N d Pw hPw J hJ
    (phases ω) (phases_norm ω)
  refine ⟨d, E, hEiso, q, fun j y => (q j).eval_unitary hOracle y, ?_⟩
  intro x G b sol bv U ζ hG hGint _hsol hU hW hLoad₀ hLoad hMassB hCert hTarget hB hBudget
  -- The represented target.
  let z := sources (sol 0) bv ω
  let y := meshTarget D hM t T N v x (sol 0) bv ω
  set Bs := meshScale sol b t with hBs
  have hTargetErr := mesh_target_error D hM hPSD x hmesh hT.le hN G hG hGint U hU v hv ω
    (sol 0) bv
  set K : ℝ := sampleError D x t G + refinementError D t T N with hK
  have hK0 : 0 ≤ K := add_nonneg (sampleError_nonneg D x hmesh G)
    (refinementError_nonneg D t T N)
  have hBs0 : 0 ≤ Bs := meshScale_nonneg hmesh sol b
  have hErr : ‖sol T - y‖ ≤ (ζ + cq * K) * Bs := by
    have hsplit : sol T - y =
        (sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T) +
          ((U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T) - y) := by
      abel
    rw [hsplit]
    have hMassK : K * ODESourceBranches.mass z ≤ cq * K * Bs := by
      calc
        K * ODESourceBranches.mass z ≤ K * (cq * Bs) := mul_le_mul_of_nonneg_left hMassB hK0
        _ = cq * K * Bs := by ring
    calc
      _ ≤ ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ +
          ‖(U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T) - y‖ := norm_add_le _ _
      _ ≤ ζ * Bs + K * ODESourceBranches.mass z := add_le_add hCert hTargetErr
      _ ≤ ζ * Bs + cq * K * Bs := add_le_add le_rfl hMassK
      _ = (ζ + cq * K) * Bs := by ring
  have hErrBudget : (ζ + cq * K) * Bs ≤ ε * Bs / (2000 * gbar) := by
    have h := mul_le_mul_of_nonneg_right hBudget hBs0
    calc
      (ζ + cq * K) * Bs ≤ ε / (2000 * gbar) * Bs := h
      _ = ε * Bs / (2000 * gbar) := by ring
  obtain ⟨hy, hBy, hDir⟩ := TimeDependentODE.Sampling.target_budget (sol T) y Bs gbar ε _ hg
    hε hεOne hTarget hB hErr hErrBudget
  have hNorm : ‖y‖ ≤ ODESourceBranches.mass z :=
    meshTarget_norm_le D hM hmesh hT.le N v hPSD x (sol 0) bv ω
  have hz : 0 < ODESourceBranches.mass z := ODESourceBranches.mass_pos_of_solution z y hy hNorm
  have hBudget' : ODESourceBranches.mass z ≤ ratio g * ‖y‖ := by
    have hcq0 : 0 ≤ cq := by linarith
    calc
      ODESourceBranches.mass z ≤ cq * Bs := hMassB
      _ ≤ cq * (2 * gbar * ‖y‖) := mul_le_mul_of_nonneg_left hBy hcq0
      _ = ratio g * ‖y‖ := by rw [hgdef]; unfold ratio; ring
  -- Hypotheses of the released actual-source certificate.
  have hJph : ∀ a, (GeneralSourceODE.Compiled.phased (J x) (phases ω) a)† ∘L
      GeneralSourceODE.Compiled.phased (J x) (phases ω) a = 1 :=
    phased_isometry (J x) (hJ x) ω
  have hPrep := phased_prepares (J x) (sol 0) bv ω seed hLoad₀ hLoad
  have hSim : ‖pN.eval x ∘L E - E ∘L WeightedClock.diagonal
      (fun a' : Option (Fin m) × Index D T g ε =>
        MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x
          (a'.1, a'.2))‖ ≤ ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) :=
    (hAct x).2
  have hLCHS : ∀ a', ‖(∑ i, lchsCoefficients D T g ε i •
      MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x (a', i)) -
        tableFamily D σ N (meshDurations t T v) x a' (-Complex.I)‖ ≤
          2 * ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) := by
    intro a'
    have hsum : (∑ i, lchsCoefficients D T g ε i •
        MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x (a', i)) =
          ∑ j, TimeDependentODE.GaussianLCHS.coefficients (lipschitz D T) (ratio g)
              (accuracy ε) j •
            tableFamily D σ N (meshDurations t T v) x a'
              (TimeDependentODE.GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j :
                ℂ) := by
      have hbr : ∀ i, MeshSelect.branchEvolution D σ N (nodeTable D T g ε m)
          (meshTable t T v) x (a', i) =
            tableFamily D σ N (meshDurations t T v) x a' (nodeTable D T g ε m (a', i) : ℂ) :=
        fun i => branchEvolution_eq_tableFamily D σ N (meshDurations t T v) x
          (nodeTable D T g ε m) a' i
      simp only [hbr]
      exact TimeDependentODE.Sampling.padded_sum _ _ _
    rw [hsum]
    exact hApprox (x, a')
  have hQuad : ‖(∑ a', tableFamily D σ N (meshDurations t T v) x a' (-Complex.I) (z a')) - y‖ ≤
      ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) * ODESourceBranches.mass z := by
    have hsum : (∑ a', tableFamily D σ N (meshDurations t T v) x a' (-Complex.I) (z a')) = y :=
      rfl
    rw [hsum, sub_self, norm_zero]
    exact mul_nonneg hν.le (ODESourceBranches.mass_nonneg z)
  have hCertS : ODEActualSourceError.Certificate E z c
      (GeneralSourceODE.Compiled.phased (J x) (phases ω)) (pN.eval x) seed y (ratio g)
        (accuracy ε) :=
    ODEActualSourceError.actual_source_certificate E hEiso z c hc
      (GeneralSourceODE.Compiled.phased (J x) (phases ω)) hJph seed hSeed hPrep (pN.eval x)
      (hAct x).1
      (fun a' i => MeshSelect.branchEvolution D σ N (nodeTable D T g ε m)
        (meshTable t T v) x (a', i))
      (fun a' => tableFamily D σ N (meshDurations t T v) x a' (-Complex.I)) y (ratio g)
      (accuracy ε) hy hg' hε' hε'Half hNorm hBudget' hSim hLCHS hQuad
  -- The released primitive trial certificate, then the solution direction.
  have hTrial := MeshNative.trial_certificate D hM i0 m N d pN Pw hPw J hJ (phases ω)
    (phases_norm ω) E hEiso z c hcpos seed y hSeed
    (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
    (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) (ratio g) (accuracy ε) hg' x
    hz hW hCertS hq hSeedUnit hOutput
  have hFinal := retarget (η' := ε / 500) hTrial hDir (by unfold accuracy; linarith)
  exact ODECompleteTrial.of_trialCertificate
    (fun j => (q j).eval_unitary hOracle x) hε.le hTarget hFinal

end

end SparseHamiltonian.GeneralSourceExtensions.Mesh
