import ODELowerBoundExtensions.Release.Kernel
import LinearSystemLowerBound.Weight.TreeBound

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Lossless purification of a retry protocol

Manuscript lines 3795-3797 (the bounded-error step of Lemma `odel:lem:outer`): an expectation gap
of a contraction between two final states bounds their overlap
(`PositiveAdversary.norm_inner_le_of_gap`). For a retry protocol the output is mixed, so the step
needs genuine vectors whose Gram matrix is the protocol kernel (`Release/Kernel`) and a contraction
that reads the heralded output from them. This module constructs them, with no loss in the
constant (an inductive scalar bound over the attempts would lose a factor growing with the
number of attempts).

**Construction** (`purification_step`, by induction on the protocol). Fix an orthonormal basis of
the finite-dimensional workspace `K` (`stdOrthonormalBasis`, `d = finrank K`). An attempt with
trial family `t` (`M` labels, seed `ψ`, circuits `V^j`, output isometry `F`) has the purified
state `φ_x = (1/√M) Σ_j |j⟩ ⊗ V_x^j ψ ∈ ℂ^M ⊗ K` (`trialVec`, Gram kernel `trialKernel`). Given a
purification `(H, Ψ, R)` of the continuation `k`, the new space is `ℂ^{M × d} ⊗ H`
(`Joint (Fin M × Fin d) H`), the new state is `φ_x ⊗ Ψ_x` written in the coordinates of `K`
(`tens`, `inner_tens`: `⟪φ ⊗ u, φ' ⊗ u'⟫ = ⟪φ, φ'⟫ ⟪u, u'⟫`), and the new readout is
`R' = (1 ⊗ F B F†) ⊗ 1_H + (1 ⊗ (1 - F F†)) ⊗ R`: the success branch is read by `B`, the failure
branch passes to the continuation. The two terms act on orthogonal ranges (`F B F† = Π F B F† Π`
with `Π = F F†`, and `1 - Π` commutes with `1 ⊗ R`), so `‖R'‖ ≤ 1`. The recursion
`successDensity (freshTrial t k) = oneTrialDensity t + (1 - meanSuccess t) • successDensity k`
(`ODERepeatProtocol.Protocol.successDensity`, `TrialFamily.oneTrialDensity_eq_kraus`) gives
`Re ⟪Ψ'_x, R' Ψ'_x⟫ = corr B (successDensity x)` (`LinearSystemLowerBound.corr`, `Re tr(B ρ)`).
The base case `abort` is `H = ℂ`, `Ψ = 1`, `R = 0`.

The operators `1 ⊗ G ⊗ 1_H` are written in the coordinates of `K` (`coordMatrix`, `coordLift`,
norm bound `norm_coordLift_apply_le` through `Helpers.Joint.sum_norm_sq_mulVec_le`); `1 ⊗ R` is
`Joint.fiber (fun _ => R)`. `H` need not be complete.

`exists_purification`: for unitary circuits, finite-dimensional `K` and `E` and any contraction
`B`, there are a Hilbert space `H`, unit vectors `Ψ : X → H` with Gram matrix `kernel p` and a
contraction `R` with `Re ⟪Ψ_x, R Ψ_x⟫ = corr B (p.successDensity x)` for every input.
-/

namespace ODELowerBoundExtensions.Release

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit
open LinearSystemLowerBound (corr corr_add corr_smul_real)
open scoped InnerProduct InnerProductSpace Matrix.Norms.L2Operator

variable {E K X L : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {O : L → X → K →L[ℂ] K}

/-- **Tensor with the workspace coordinates**: `v ⊗ u` for `v ∈ ℂ^J ⊗ K` and `u ∈ H`, written in
the coordinates of `K` (`stdOrthonormalBasis`) as an element of `ℂ^{J × d} ⊗ H`. -/
def tens [FiniteDimensional ℂ K] {J H : Type*} [Fintype J] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (v : Joint J K) (u : H) : Joint (J × Fin (Module.finrank ℂ K)) H :=
  WithLp.toLp 2 (fun ji => ((stdOrthonormalBasis ℂ K).repr (v ji.1) ji.2) • u)

omit [CompleteSpace K] in
/-- `⟪v ⊗ u, v' ⊗ u'⟫ = ⟪v, v'⟫ ⟪u, u'⟫`. -/
theorem inner_tens [FiniteDimensional ℂ K] {J H : Type*} [Fintype J] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (v v' : Joint J K) (u u' : H) :
    ⟪tens v u, tens v' u'⟫_ℂ = ⟪v, v'⟫_ℂ * ⟪u, u'⟫_ℂ := by
  set b := stdOrthonormalBasis ℂ K
  simp only [tens, PiLp.inner_apply, inner_smul_left, inner_smul_right,
    Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← b.sum_inner_mul_inner (v j) (v' j), Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [b.repr_apply_apply, b.repr_apply_apply, inner_conj_symm]
  ring

omit [CompleteSpace K] in
/-- `‖v ⊗ u‖ = ‖v‖ ‖u‖`. -/
theorem norm_tens [FiniteDimensional ℂ K] {J H : Type*} [Fintype J] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (v : Joint J K) (u : H) : ‖tens v u‖ = ‖v‖ * ‖u‖ := by
  have h := inner_tens v v u u
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖tens v u‖ ^ 2 = (‖v‖ * ‖u‖) ^ 2 := by
    rw [mul_pow]; exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h'

/-- **Coordinate matrix** of a workspace operator `G` in the basis `stdOrthonormalBasis`:
`G_{i i'} = ⟪b_i, G b_{i'}⟫`. -/
def coordMatrix [FiniteDimensional ℂ K] (G : K →L[ℂ] K) :
    Matrix (Fin (Module.finrank ℂ K)) (Fin (Module.finrank ℂ K)) ℂ :=
  Matrix.of fun i i' => ⟪stdOrthonormalBasis ℂ K i, G (stdOrthonormalBasis ℂ K i')⟫_ℂ

omit [CompleteSpace K] in
/-- The coordinate matrix has `L²` operator norm at most `‖G‖`. -/
theorem norm_coordMatrix_le [FiniteDimensional ℂ K] (G : K →L[ℂ] K) :
    ‖coordMatrix G‖ ≤ ‖G‖ := by
  set b := stdOrthonormalBasis ℂ K
  have hrep : ∀ v, Matrix.toEuclideanCLM (𝕜 := ℂ) (coordMatrix G) v = b.repr (G (b.repr.symm v)) := by
    intro v
    ext i
    rw [b.repr_apply_apply, ← b.sum_repr_symm v]
    simp [coordMatrix, Matrix.mulVec, dotProduct, map_sum, map_smul, inner_sum, inner_smul_right,
      mul_comm, b]
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  rw [hrep, LinearIsometryEquiv.norm_map]
  calc ‖G (b.repr.symm v)‖ ≤ ‖G‖ * ‖b.repr.symm v‖ := G.le_opNorm _
    _ = ‖G‖ * ‖v‖ := by rw [LinearIsometryEquiv.norm_map]

/-- **`1_J ⊗ G ⊗ 1_H`** on `ℂ^{J × d} ⊗ H`, in the coordinates of `K`:
`(coordLift G f)(j, i) = Σ_{i'} G_{i i'} f(j, i')`. -/
def coordLift [FiniteDimensional ℂ K] {J H : Type*} [Fintype J] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (G : K →L[ℂ] K) :
    Joint (J × Fin (Module.finrank ℂ K)) H →L[ℂ] Joint (J × Fin (Module.finrank ℂ K)) H :=
  Joint.mk fun a => ∑ i', coordMatrix G a.2 i' • Joint.proj (a.1, i')

section CoordLift

variable [FiniteDimensional ℂ K] {J H : Type*} [Fintype J] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]

omit [CompleteSpace K] in
/-- Components of `1_J ⊗ G ⊗ 1_H`. -/
theorem coordLift_apply (G : K →L[ℂ] K) (f : Joint (J × Fin (Module.finrank ℂ K)) H)
    (j : J) (i : Fin (Module.finrank ℂ K)) :
    coordLift G f (j, i) = ∑ i', coordMatrix G i i' • f (j, i') := by
  simp [coordLift]

omit [CompleteSpace K] in
/-- `(1 ⊗ G ⊗ 1)(v ⊗ u) = (1 ⊗ G) v ⊗ u`. -/
theorem coordLift_tens (G : K →L[ℂ] K) (v : Joint J K) (u : H) :
    coordLift G (tens v u) = tens (Joint.fiber (fun _ => G) v) u := by
  set b := stdOrthonormalBasis ℂ K
  ext ⟨j, i⟩
  simp only [coordLift_apply, tens, PiLp.toLp_apply, Joint.fiber_apply, smul_smul,
    ← Finset.sum_smul]
  congr 1
  conv_rhs => rw [b.repr_apply_apply, ← b.sum_repr (v j)]
  simp [coordMatrix, map_sum, map_smul, inner_sum, inner_smul_right, mul_comm, b]

omit [CompleteSpace K] in
/-- A workspace operator acting on the `H` factor: `(1 ⊗ R)(v ⊗ u) = v ⊗ R u`. -/
theorem fiber_tens (R : H →L[ℂ] H) (v : Joint J K) (u : H) :
    Joint.fiber (fun _ => R) (tens v u) = tens v (R u) := by
  ext a
  simp [tens, map_smul]

omit [CompleteSpace K] in
/-- `1 ⊗ G ⊗ 1` commutes with `1 ⊗ 1 ⊗ R`. -/
theorem coordLift_fiber (G : K →L[ℂ] K) (R : H →L[ℂ] H)
    (f : Joint (J × Fin (Module.finrank ℂ K)) H) :
    coordLift G (Joint.fiber (fun _ => R) f) = Joint.fiber (fun _ => R) (coordLift G f) := by
  ext ⟨j, i⟩
  simp [coordLift_apply, map_sum, map_smul]

omit [CompleteSpace K] in
/-- `coordLift` is multiplicative. -/
theorem coordLift_comp (G G' : K →L[ℂ] K) (f : Joint (J × Fin (Module.finrank ℂ K)) H) :
    coordLift (G ∘L G') f = coordLift G (coordLift G' f) := by
  set b := stdOrthonormalBasis ℂ K
  ext ⟨j, i⟩
  simp only [coordLift_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i'' _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp only [coordMatrix, Matrix.of_apply, ContinuousLinearMap.comp_apply]
  conv_lhs => rw [← b.sum_repr' (G' (b i''))]
  simp [map_sum, map_smul, inner_sum, inner_smul_right, mul_comm, b]

/-- `coordLift` intertwines adjoints: `⟪(1 ⊗ G ⊗ 1) f, f'⟫ = ⟪f, (1 ⊗ G† ⊗ 1) f'⟫`. -/
theorem inner_coordLift (G : K →L[ℂ] K) (f f' : Joint (J × Fin (Module.finrank ℂ K)) H) :
    ⟪coordLift G f, f'⟫_ℂ = ⟪f, coordLift (G†) f'⟫_ℂ := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, coordLift_apply, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
  congr 1
  simp only [coordMatrix, Matrix.of_apply, ContinuousLinearMap.adjoint_inner_right,
    inner_conj_symm]

omit [CompleteSpace K] in
/-- `‖(1 ⊗ G ⊗ 1) f‖ ≤ ‖G‖ ‖f‖`. -/
theorem norm_coordLift_apply_le (G : K →L[ℂ] K) (f : Joint (J × Fin (Module.finrank ℂ K)) H) :
    ‖coordLift G f‖ ≤ ‖G‖ * ‖f‖ := by
  have h : ‖coordLift G f‖ ^ 2 ≤ (‖G‖ * ‖f‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type,
      Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [coordLift_apply]
    calc _ ≤ ‖coordMatrix G‖ ^ 2 * ∑ i, ‖f (j, i)‖ ^ 2 :=
          SparseLowerBounds.Helpers.Joint.sum_norm_sq_mulVec_le (coordMatrix G)
            (fun i => f (j, i))
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (norm_coordMatrix_le G) 2)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

end CoordLift

/-- **The purified state of one fresh attempt** on input `x`:
`(1/√M) Σ_j |j⟩ ⊗ V_x^j ψ`. -/
def trialVec (t : ODERepeatProtocol.TrialFamily O E) (x : X) : Joint (Fin t.choices) K :=
  WithLp.toLp 2 (fun j => (((Real.sqrt t.choices)⁻¹ : ℝ) : ℂ) • (t.circuit j).eval x t.seed)

/-- The Gram matrix of the attempt states is the trial kernel. -/
theorem inner_trialVec (t : ODERepeatProtocol.TrialFamily O E) (x x' : X) :
    ⟪trialVec t x, trialVec t x'⟫_ℂ = trialKernel t x x' := by
  have hs : (starRingEnd ℂ) (((Real.sqrt t.choices)⁻¹ : ℝ) : ℂ) * (((Real.sqrt t.choices)⁻¹ : ℝ) : ℂ)
      = (t.choices : ℂ)⁻¹ := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (Nat.cast_nonneg _)]
    push_cast; rfl
  simp only [trialVec, trialKernel, PiLp.inner_apply, inner_smul_left, inner_smul_right,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, mul_comm (((Real.sqrt t.choices)⁻¹ : ℝ) : ℂ), hs]

/-- The expectation of `1 ⊗ G` in an attempt state:
`⟪φ_x, (1 ⊗ G) φ_x⟫ = (1/M) Σ_j ⟪V_x^j ψ, G V_x^j ψ⟫`. -/
theorem inner_trialVec_fiber (t : ODERepeatProtocol.TrialFamily O E) (G : K →L[ℂ] K) (x : X) :
    ⟪trialVec t x, Joint.fiber (fun _ => G) (trialVec t x)⟫_ℂ =
      (t.choices : ℂ)⁻¹ * ∑ j, ⟪(t.circuit j).eval x t.seed, G ((t.circuit j).eval x t.seed)⟫_ℂ := by
  have hs : (starRingEnd ℂ) (((Real.sqrt t.choices)⁻¹ : ℝ) : ℂ) * (((Real.sqrt t.choices)⁻¹ : ℝ) : ℂ)
      = (t.choices : ℂ)⁻¹ := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (Nat.cast_nonneg _)]
    push_cast; rfl
  simp only [trialVec, PiLp.inner_apply, Joint.fiber_apply, map_smul, inner_smul_left,
    inner_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, mul_comm (((Real.sqrt t.choices)⁻¹ : ℝ) : ℂ), hs]

/-- For unitary circuits the attempt state is a unit vector. -/
theorem norm_trialVec (hO : ∀ l x, IsUnitary (O l x)) (t : ODERepeatProtocol.TrialFamily O E)
    (x : X) : ‖trialVec t x‖ = 1 := by
  have h := inner_trialVec t x x
  have hj : ∀ j, ⟪(t.circuit j).eval x t.seed, (t.circuit j).eval x t.seed⟫_ℂ = 1 := by
    intro j
    rw [inner_self_eq_norm_sq_to_K, ((t.circuit j).eval x).norm_map_iff_adjoint_comp_self.mpr
      ((t.circuit j).eval_unitary hO x).1, t.seed_unit]
    simp
  have hM : (t.choices : ℂ) ≠ 0 := by exact_mod_cast t.choices_pos.ne'
  simp only [trialKernel, hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, inv_mul_cancel₀ hM, inner_self_eq_norm_sq_to_K] at h
  have h2 : ((‖trialVec t x‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; exact h
  have h' : ‖trialVec t x‖ ^ 2 = 1 ^ 2 := by rw [one_pow]; exact Complex.ofReal_injective h2
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 h'

/-- **One step of the purification**: a purification of the continuation `k` (unit vectors with
Gram matrix `kernel k`, a contraction reading `corr B (k.successDensity x)`) extends to a
purification of `freshTrial t k` on `ℂ^{M × d} ⊗ H`. -/
theorem purification_step [FiniteDimensional ℂ K] [FiniteDimensional ℂ E]
    (hO : ∀ l x, IsUnitary (O l x)) (t : ODERepeatProtocol.TrialFamily O E)
    (k : ODERepeatProtocol.Protocol O E) (B : E →L[ℂ] E) (hB : ‖B‖ ≤ 1)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Ψ : X → H) (R : H →L[ℂ] H)
    (hΨ : ∀ x, ‖Ψ x‖ = 1) (hR : ‖R‖ ≤ 1) (hG : ∀ x x', ⟪Ψ x, Ψ x'⟫_ℂ = kernel k x x')
    (hC : ∀ x, (⟪Ψ x, R (Ψ x)⟫_ℂ).re = corr B (k.successDensity x)) :
    ∃ (Ψ' : X → Joint (Fin t.choices × Fin (Module.finrank ℂ K)) H)
      (R' : Joint (Fin t.choices × Fin (Module.finrank ℂ K)) H →L[ℂ]
        Joint (Fin t.choices × Fin (Module.finrank ℂ K)) H),
      (∀ x, ‖Ψ' x‖ = 1) ∧ ‖R'‖ ≤ 1 ∧
        (∀ x x', ⟪Ψ' x, Ψ' x'⟫_ℂ = kernel (.freshTrial t k) x x') ∧
        ∀ x, (⟪Ψ' x, R' (Ψ' x)⟫_ℂ).re =
          corr B ((ODERepeatProtocol.Protocol.freshTrial t k).successDensity x) := by
  classical
  set F := t.output with hFdef
  have hF : F† ∘L F = 1 := t.output_isometry
  have hFF : ∀ v, (F†) (F v) = v := fun v => by
    simpa using congrArg (fun A : E →L[ℂ] E => A v) hF
  have hFn : ‖F‖ ≤ 1 := F.opNorm_le_bound zero_le_one fun v => by
    rw [F.norm_map_iff_adjoint_comp_self.mpr hF v, one_mul]
  have hFan : ‖F†‖ ≤ 1 := by rw [LinearIsometryEquiv.norm_map]; exact hFn
  set Pr : K →L[ℂ] K := F ∘L F† with hPr
  set G₀ : K →L[ℂ] K := F ∘L B ∘L F† with hG₀
  have hPrPr : Pr ∘L Pr = Pr := by ext v; simp [hPr, hFF]
  have hG₀Pr : G₀ ∘L Pr = G₀ := by ext v; simp [hG₀, hPr, hFF]
  have hPrG₀ : Pr ∘L G₀ = G₀ := by ext v; simp [hG₀, hPr, hFF]
  have hPrA : Pr† = Pr := by simp [hPr, ContinuousLinearMap.adjoint_comp]
  have hG₀n : ‖G₀‖ ≤ 1 :=
    calc ‖G₀‖ ≤ ‖F‖ * (‖B‖ * ‖F†‖) :=
          (F.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (B.opNorm_comp_le _) (norm_nonneg _))
      _ ≤ 1 * (1 * 1) := by gcongr
      _ = 1 := by ring
  let P : Joint (Fin t.choices × Fin (Module.finrank ℂ K)) H →L[ℂ]
      Joint (Fin t.choices × Fin (Module.finrank ℂ K)) H := coordLift Pr
  let A : Joint (Fin t.choices × Fin (Module.finrank ℂ K)) H →L[ℂ]
      Joint (Fin t.choices × Fin (Module.finrank ℂ K)) H := coordLift G₀
  let Rt : Joint (Fin t.choices × Fin (Module.finrank ℂ K)) H →L[ℂ]
      Joint (Fin t.choices × Fin (Module.finrank ℂ K)) H := Joint.fiber (fun _ => R)
  have hPP : ∀ f, P (P f) = P f := fun f => by
    simp only [P]; rw [← coordLift_comp, hPrPr]
  have hAP : ∀ f, A (P f) = A f := fun f => by
    simp only [A, P]; rw [← coordLift_comp, hG₀Pr]
  have hPA : ∀ f, P (A f) = A f := fun f => by
    simp only [A, P]; rw [← coordLift_comp, hPrG₀]
  have hPs : ∀ f f', ⟪P f, f'⟫_ℂ = ⟪f, P f'⟫_ℂ := fun f f' => by
    simp only [P]; rw [inner_coordLift, hPrA]
  have hPR : ∀ f, P (Rt f) = Rt (P f) := fun f => coordLift_fiber _ _ _
  have hRt : ∀ f, ‖Rt f‖ ≤ ‖f‖ := fun f =>
    (Rt.le_opNorm f).trans (mul_le_of_le_one_left (norm_nonneg _)
      (Joint.norm_fiber_le (fun _ => R) zero_le_one fun _ => hR))
  let R' : Joint (Fin t.choices × Fin (Module.finrank ℂ K)) H →L[ℂ]
      Joint (Fin t.choices × Fin (Module.finrank ℂ K)) H := A + (1 - P) ∘L Rt
  have hR'apply : ∀ f, R' f = A f + (Rt f - P (Rt f)) := fun f => rfl
  have pyth : ∀ a c : Joint (Fin t.choices × Fin (Module.finrank ℂ K)) H, ⟪a, c⟫_ℂ = 0 →
      ‖a + c‖ ^ 2 = ‖a‖ ^ 2 + ‖c‖ ^ 2 := fun a c h => by
    simpa only [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) a c h
  refine ⟨fun x => tens (trialVec t x) (Ψ x), R', fun x => ?_, ?_,
    fun x x' => ?_, fun x => ?_⟩
  · rw [norm_tens, norm_trialVec hO, hΨ, one_mul]
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    rw [one_mul]
    have hR'f : R' f = A f + Rt (f - P f) := by
      rw [hR'apply, map_sub, hPR]
    have horth : ⟪A f, Rt (f - P f)⟫_ℂ = 0 := by
      rw [← hPA f, hPs, hPR, map_sub, hPP, sub_self, map_zero, inner_zero_right]
    have horth' : ⟪P f, f - P f⟫_ℂ = 0 := by
      rw [inner_sub_right, hPs, hPs, hPP, sub_self]
    have hf : ‖f‖ ^ 2 = ‖P f‖ ^ 2 + ‖f - P f‖ ^ 2 := by
      rw [← pyth _ _ horth', add_sub_cancel]
    have hA : ‖A f‖ ≤ ‖P f‖ := by
      rw [← hAP]
      exact (norm_coordLift_apply_le G₀ (P f)).trans (mul_le_of_le_one_left (norm_nonneg _) hG₀n)
    have h2 : ‖R' f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
      rw [hR'f, pyth _ _ horth, hf]
      gcongr
      exact hRt _
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  · rw [inner_tens, inner_trialVec, hG]
    rfl
  · have hu : ⟪Ψ x, Ψ x⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hΨ]; simp
    have hφ : ⟪trialVec t x, trialVec t x⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, norm_trialVec hO]; simp
    have hexp : ⟪tens (trialVec t x) (Ψ x), R' (tens (trialVec t x) (Ψ x))⟫_ℂ =
        ⟪trialVec t x, Joint.fiber (fun _ => G₀) (trialVec t x)⟫_ℂ * ⟪Ψ x, Ψ x⟫_ℂ +
          ⟪trialVec t x, trialVec t x⟫_ℂ * ⟪Ψ x, R (Ψ x)⟫_ℂ -
          ⟪trialVec t x, Joint.fiber (fun _ => Pr) (trialVec t x)⟫_ℂ * ⟪Ψ x, R (Ψ x)⟫_ℂ := by
      rw [hR'apply]
      simp only [A, P, Rt, fiber_tens, coordLift_tens, inner_add_right, inner_sub_right,
        inner_tens]
      ring
    have hG₀φ : ⟪trialVec t x, Joint.fiber (fun _ => G₀) (trialVec t x)⟫_ℂ =
        (t.choices : ℂ)⁻¹ * ∑ j, ⟪t.amplitude x j, B (t.amplitude x j)⟫_ℂ := by
      rw [inner_trialVec_fiber]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hG₀, ContinuousLinearMap.comp_apply, ODERepeatProtocol.TrialFamily.amplitude]
      exact (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
    have hPrj : ∀ j, ⟪(t.circuit j).eval x t.seed, Pr ((t.circuit j).eval x t.seed)⟫_ℂ =
        ((t.probability x j : ℝ) : ℂ) := by
      intro j
      rw [hPr, ContinuousLinearMap.comp_apply,
        ← ContinuousLinearMap.adjoint_inner_left F ((F†) ((t.circuit j).eval x t.seed)),
        inner_self_eq_norm_sq_to_K]
      simp [ODERepeatProtocol.TrialFamily.probability, ODERepeatProtocol.TrialFamily.amplitude,
        hFdef]
    have hPrφ : ⟪trialVec t x, Joint.fiber (fun _ => Pr) (trialVec t x)⟫_ℂ =
        ((t.meanSuccess x : ℝ) : ℂ) := by
      rw [inner_trialVec_fiber]
      simp only [hPrj, ODERepeatProtocol.TrialFamily.meanSuccess]
      push_cast
      ring
    rw [hexp, hG₀φ, hPrφ, hu, hφ, ODERepeatProtocol.Protocol.successDensity, corr_add,
      corr_smul_real, ← hC x, t.oneTrialDensity_eq_kraus]
    have hM : ((t.choices : ℂ))⁻¹ = (((t.choices : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [hM, corr_smul_real, LinearSystemLowerBound.corr_sum]
    simp only [LinearSystemLowerBound.corr_pure, mul_one, one_mul, Complex.sub_re, Complex.add_re,
      Complex.re_ofReal_mul, Complex.re_sum]
    ring

/-- **Lossless purification of a retry protocol**: unit vectors `Ψ_x` in a Hilbert space with
Gram matrix the protocol kernel, and a contraction `R` whose expectation on `Ψ_x` is the
heralded correlation `corr B (p.successDensity x) = Re tr(B ρ_x)` of any contraction `B`. -/
theorem exists_purification [FiniteDimensional ℂ K] [FiniteDimensional ℂ E]
    (hO : ∀ l x, IsUnitary (O l x)) (p : ODERepeatProtocol.Protocol O E) (B : E →L[ℂ] E)
    (hB : ‖B‖ ≤ 1) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (Ψ : X → H)
      (R : H →L[ℂ] H),
      (∀ x, ‖Ψ x‖ = 1) ∧ ‖R‖ ≤ 1 ∧ (∀ x x', ⟪Ψ x, Ψ x'⟫_ℂ = kernel p x x') ∧
        ∀ x, (⟪Ψ x, R (Ψ x)⟫_ℂ).re = corr B (p.successDensity x) := by
  induction p with
  | abort =>
    refine ⟨ℂ, inferInstance, inferInstance, fun _ => 1, 0, fun _ => by simp, by simp,
      fun _ _ => ?_, fun x => ?_⟩
    · simp [kernel]
    · rw [ODERepeatProtocol.Protocol.successDensity, LinearSystemLowerBound.corr_zero]
      simp
  | freshTrial t k ih =>
    obtain ⟨H, _, _, Ψ, R, hΨ, hR, hG, hC⟩ := ih
    obtain ⟨Ψ', R', hΨ', hR', hG', hC'⟩ := purification_step hO t k B hB Ψ R hΨ hR hG hC
    exact ⟨_, inferInstance, inferInstance, Ψ', R', hΨ', hR', hG', hC'⟩

end

end ODELowerBoundExtensions.Release
