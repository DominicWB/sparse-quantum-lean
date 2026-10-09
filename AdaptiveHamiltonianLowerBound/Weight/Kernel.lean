import LinearSystemLowerBound.Weight.TreeBound
import SparseLowerBounds.Query.Joint

set_option autoImplicit false

/-!
# Kernel potentials for an arbitrary one-coordinate weight

The weight-growth argument for adaptive protocols of the linear-system lower bound
(`LinearSystemLowerBound.tree_xor`) is written for one fixed weight. Its structure only uses
that the weight is an invertible Hermitian matrix `a` on one hidden register `ℂ^m`, acting on
all hidden registers as `W = a^{⊗ι}` (`kron a`), with row sums one, and the norm
`μ ≥ ‖a⁻¹ Z a⁻¹‖` of the conjugated parity. This file states it for every such weight; the
Hamiltonian-simulation lower bound uses the search weight `w = P_u + a² P_v + a R` of Lemma
`hsl:lem:search` (manuscript lines 2151-2203).

For hidden inputs `j : ι → Fin m` (`n = |ι|` one-hot strings of length `m`):

* `WGrowth a O C`: `‖W Õ ψ‖² ≤ C ‖W ψ‖²` for every family `ψ = (ψ_j)` (the joint operator
  `Õ ψ = (O j ψ_j)_j`); closed under products, block-diagonal operators on spectator branches,
  fixed isometric layouts, and circuits (`wgrowth_program`: growth `C ^ cost`).
* `wpot a G = Re Σ_{j,j'} (WᴴW)_{jj'} G_{jj'}`: the weighted norm of the purified state with
  Gram kernel `G` (`wpot_hadamard_gram_eq`); a fresh run multiplies it by at most
  `C ^ cost` (`wpot_run`), a measured run splits it (`wpot_split`).
* `wparity_kernel_bound`: `|Σ_j σ_j G_jj Re⟨φ_j, M φ_j⟩| ≤ μ^{|ι|} wpot a (G ⊙ gram φ)` for
  `‖M‖ ≤ 1` and the parity `σ_j` (the paper's `‖W⁻¹ Z^{⊗n} W⁻¹‖ ≤ μⁿ`).
* `wtree_xor`: for every released adaptive protocol `T` (`SparseLinearSystems.Protocol.Tree`:
  fresh measured runs, classical branching, random trial labels, repeated trials) over a family
  whose labels have growth `C ^ w l` in both directions,
  `|Σ_j σ_j Re tr(M ρ_j)| ≤ μ^{|ι|} C^{worstCost} m^{|ι|}`, where `ρ_j` is the unnormalised
  heralded output on input `j` and `σ_j = (-1)^{j_1 + ⋯}` the parity (`parSign`).

The proofs follow `LinearSystemLowerBound/Weight/{Growth,Kernel,TreeBound}.lean` with the
weight as a parameter; the weight-independent lemmas of that library are reused.
-/

namespace AdaptiveHamiltonianLowerBound

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct Matrix ComplexOrder
open scoped Matrix.Norms.L2Operator
open SparseHamiltonian SparseLinearSystems.Protocol ContinuousLinearMap
open LinearSystemLowerBound

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-! ### Weight growth -/

section Growth

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- **Weight growth** of an input-dependent operator family for the weight `a^{⊗ι}`. -/
def WGrowth (a : Matrix (Fin m) (Fin m) ℂ) (O : (ι → Fin m) → K →L[ℂ] K) (C : ℝ) : Prop :=
  ∀ ψ : Fam (ι → Fin m) K, ‖act (kron a) (joint O ψ)‖ ^ 2 ≤ C * ‖act (kron a) ψ‖ ^ 2

theorem wgrowth_const (a : Matrix (Fin m) (Fin m) ℂ) (U : K →L[ℂ] K) (hU : ∀ v, ‖U v‖ = ‖v‖) :
    WGrowth (ι := ι) a (fun _ => U) 1 := by
  intro ψ
  rw [act_joint_const, norm_joint _ (fun _ => hU), one_mul]

theorem wgrowth_mono {a : Matrix (Fin m) (Fin m) ℂ} {O : (ι → Fin m) → K →L[ℂ] K} {C C' : ℝ}
    (h : WGrowth a O C) (hCC : C ≤ C') : WGrowth a O C' :=
  fun ψ => (h ψ).trans (mul_le_mul_of_nonneg_right hCC (sq_nonneg _))

theorem wgrowth_congr {a : Matrix (Fin m) (Fin m) ℂ} {O O' : (ι → Fin m) → K →L[ℂ] K} {C : ℝ}
    (h : WGrowth a O C) (hO : ∀ x, O x = O' x) : WGrowth a O' C := by
  have : O = O' := funext hO
  rw [← this]
  exact h

theorem wgrowth_mul {a : Matrix (Fin m) (Fin m) ℂ} {O O' : (ι → Fin m) → K →L[ℂ] K} {C C' : ℝ}
    (hO : WGrowth a O C) (hO' : WGrowth a O' C') (hC : 0 ≤ C) :
    WGrowth a (fun j => O j * O' j) (C * C') := by
  intro ψ
  rw [joint_comp]
  calc _ ≤ C * ‖act (kron a) (joint O' ψ)‖ ^ 2 := hO _
    _ ≤ C * (C' * ‖act (kron a) ψ‖ ^ 2) := mul_le_mul_of_nonneg_left (hO' ψ) hC
    _ = C * C' * ‖act (kron a) ψ‖ ^ 2 := by ring

/-- **Block-diagonal operators** (spectator branches, controlled and masked calls). -/
theorem wgrowth_diagonal {S : Type*} [Fintype S] (a : Matrix (Fin m) (Fin m) ℂ)
    (O : S → (ι → Fin m) → K →L[ℂ] K) (C : ℝ) (hO : ∀ s, WGrowth a (O s) C) :
    WGrowth a (fun j => WeightedClock.diagonal (fun s : S => O s j)) C := by
  intro ψ
  rw [norm_sq_blk, norm_sq_blk, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  have h : blk s (joint (fun j => WeightedClock.diagonal (fun s : S => O s j)) ψ) =
      joint (O s) (blk s ψ) := by
    ext j
    simp only [blk, joint_apply, PiLp.toLp_apply, WeightedClock.diagonal_apply]
  rw [blk_act, h, blk_act]
  exact hO s _

/-- **Fixed isometric layouts** preserve weight growth. -/
theorem wgrowth_conj [CompleteSpace K] {K' : Type*} [NormedAddCommGroup K']
    [InnerProductSpace ℂ K'] [CompleteSpace K'] (a : Matrix (Fin m) (Fin m) ℂ)
    (Φ : K ≃ₗᵢ[ℂ] K') (O : (ι → Fin m) → K →L[ℂ] K) (C : ℝ)
    (hO : WGrowth a O C) : WGrowth a (fun j => Φ.conjStarAlgEquiv (O j)) C := by
  intro ψ'
  set ψ : Fam (ι → Fin m) K := WithLp.toLp 2 (fun j => Φ.symm (ψ' j))
  have hψ' : ψ' = WithLp.toLp 2 (fun j => Φ (ψ j)) := by
    ext j
    simp [ψ]
  have hjoint : joint (fun j => Φ.conjStarAlgEquiv (O j)) ψ' =
      WithLp.toLp 2 (fun j => Φ ((joint O ψ) j)) := by
    ext j
    simp [ψ, joint_apply]
  have hpush : ∀ φ : Fam (ι → Fin m) K, act (kron a)
      (WithLp.toLp 2 (fun j => Φ (φ j)) : Fam (ι → Fin m) K') =
      WithLp.toLp 2 (fun j => Φ ((act (kron a) φ) j)) := by
    intro φ
    ext j
    simp only [act_apply, map_sum, map_smul]
  have hnorm : ∀ φ : Fam (ι → Fin m) K,
      ‖(WithLp.toLp 2 (fun j => Φ (φ j)) : Fam (ι → Fin m) K')‖ = ‖φ‖ := by
    intro φ
    have h2 : ‖(WithLp.toLp 2 (fun j => Φ (φ j)) : Fam (ι → Fin m) K')‖ ^ 2 = ‖φ‖ ^ 2 := by
      rw [norm_sq_fam, norm_sq_fam]
      simp
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
  rw [hjoint, hpush, hnorm, hψ', hpush, hnorm]
  exact hO ψ

/-- **Circuits.** If every label has weight growth `C ^ w l` in both directions, a circuit
has growth `C ^ cost`. -/
theorem wgrowth_program [CompleteSpace K] {L : Type*} (a : Matrix (Fin m) (Fin m) ℂ)
    (O : L → (ι → Fin m) → K →L[ℂ] K) (w : L → ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hO : ∀ l, WGrowth a (O l) (C ^ w l)) (hO' : ∀ l, WGrowth a (fun j => star (O l j)) (C ^ w l))
    (p : MultiOracleCircuit.Program O) :
    WGrowth a (fun j => p.eval j) (C ^ p.cost w) := by
  induction p with
  | fixed U hU =>
      simp only [MultiOracleCircuit.Program.eval_fixed, MultiOracleCircuit.Program.cost_fixed,
        pow_zero]
      exact wgrowth_const a U (isUnitary_norm hU)
  | query l => exact hO l
  | queryAdjoint l => exact hO' l
  | seq p q hp hq =>
      simp only [MultiOracleCircuit.Program.eval_seq, MultiOracleCircuit.Program.cost_seq,
        pow_add]
      exact wgrowth_mul hp hq (pow_nonneg hC _)

end Growth

/-! ### The potential of a kernel -/

section Potential

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- `WᴴW` for the weight `W = a^{⊗ι}`. -/
def wsqOf (ι : Type*) [Fintype ι] [DecidableEq ι] (a : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (ι → Fin m) (ι → Fin m) ℂ :=
  (kron a)ᴴ * kron a

/-- **The potential of a kernel** for the weight `a^{⊗ι}`: the weighted norm of the purified
state. -/
def wpot (a : Matrix (Fin m) (Fin m) ℂ) (G : Matrix (ι → Fin m) (ι → Fin m) ℂ) : ℝ :=
  (∑ j, ∑ j', wsqOf ι a j j' * G j j').re

theorem wpot_add (a : Matrix (Fin m) (Fin m) ℂ) (G H : Matrix (ι → Fin m) (ι → Fin m) ℂ) :
    wpot a (G + H) = wpot a G + wpot a H := by
  simp only [wpot, Matrix.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re]

/-- **Factorisation.** For `G = BᴴB` the potential of `G ⊙ gram v` is a sum of weighted
norms of single families. -/
theorem wpot_hadamard_gram_eq (a : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (ι → Fin m) (ι → Fin m) ℂ) (v : Fam (ι → Fin m) K) :
    wpot a ((star B * B) ⊙ Matrix.gram ℂ (fun j => v j)) =
      ∑ k, ‖act (kron a) (scale (B k) v)‖ ^ 2 := by
  set g : (ι → Fin m) → (ι → Fin m) → (ι → Fin m) → ℂ := fun k j j' =>
    wsqOf ι a j j' * ((starRingEnd ℂ) (B k j) * B k j' * ⟪v j, v j'⟫_ℂ)
  have h : ∀ k, ‖act (kron a) (scale (B k) v)‖ ^ 2 = (∑ j, ∑ j', g k j j').re := by
    intro k
    rw [norm_sq_act_eq]
    congr 1
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro j' _
    simp only [g, scale_apply, inner_smul_left, inner_smul_right, wsqOf]
    ring
  have hswap : (∑ k, ∑ j, ∑ j', g k j j') = ∑ j, ∑ j', ∑ k, g k j j' := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_comm]
  simp only [h]
  rw [← Complex.re_sum, hswap, wpot]
  congr 1
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro j' _
  simp only [g, Matrix.hadamard_apply, Matrix.gram_apply, Matrix.mul_apply, Matrix.star_apply,
    RCLike.star_def, Finset.sum_mul, Finset.mul_sum]

theorem wpot_hadamard_gram_nonneg (a : Matrix (Fin m) (Fin m) ℂ)
    {G : Matrix (ι → Fin m) (ι → Fin m) ℂ} (hG : G.PosSemidef) (v : Fam (ι → Fin m) K) :
    0 ≤ wpot a (G ⊙ Matrix.gram ℂ (fun j => v j)) := by
  obtain ⟨B, rfl⟩ := exists_factor hG
  rw [wpot_hadamard_gram_eq]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

theorem wpot_nonneg (a : Matrix (Fin m) (Fin m) ℂ) {G : Matrix (ι → Fin m) (ι → Fin m) ℂ}
    (hG : G.PosSemidef) : 0 ≤ wpot a G := by
  have h : G = G ⊙ Matrix.gram ℂ (fun _ : ι → Fin m => (1 : ℂ)) := by
    ext j j'
    simp [Matrix.hadamard_apply, Matrix.gram_apply]
  rw [h]
  exact wpot_hadamard_gram_nonneg a hG (WithLp.toLp 2 (fun _ => (1 : ℂ)))

/-- **Weight growth of the potential.** -/
theorem wpot_growth (a : Matrix (Fin m) (Fin m) ℂ) {G : Matrix (ι → Fin m) (ι → Fin m) ℂ}
    (hG : G.PosSemidef) {O : (ι → Fin m) → K →L[ℂ] K} {C : ℝ} (hO : WGrowth a O C)
    (v : Fam (ι → Fin m) K) :
    wpot a (G ⊙ Matrix.gram ℂ (fun j => joint O v j)) ≤
      C * wpot a (G ⊙ Matrix.gram ℂ (fun j => v j)) := by
  obtain ⟨B, rfl⟩ := exists_factor hG
  rw [wpot_hadamard_gram_eq, wpot_hadamard_gram_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [← joint_scale]
  exact hO _

/-- One fresh run multiplies the potential of the kernel by at most `C ^ cost`. -/
theorem wpot_run [CompleteSpace K] {L : Type*} {O : L → (ι → Fin m) → K →L[ℂ] K}
    (a : Matrix (Fin m) (Fin m) ℂ) {G : Matrix (ι → Fin m) (ι → Fin m) ℂ} (hG : G.PosSemidef)
    (w : L → ℕ) {C : ℝ} (hC : 0 ≤ C) (hO : ∀ l, WGrowth a (O l) (C ^ w l))
    (hO' : ∀ l, WGrowth a (fun j => star (O l j)) (C ^ w l))
    (p : MultiOracleCircuit.Program O) (seed : K) (hseed : ‖seed‖ = 1) :
    wpot a (G ⊙ Matrix.gram ℂ (fun j => p.eval j seed)) ≤ C ^ p.cost w * wpot a G := by
  have h := wpot_growth a hG (wgrowth_program a O w C hC hO hO' p)
    (WithLp.toLp 2 (fun _ => seed) : Fam (ι → Fin m) K)
  simp only [joint_apply] at h
  rwa [hadamard_gram_const G seed hseed] at h

/-- A measured run splits the potential. -/
theorem wpot_split [CompleteSpace K] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (a : Matrix (Fin m) (Fin m) ℂ) {G : Matrix (ι → Fin m) (ι → Fin m) ℂ}
    (Fl : E →L[ℂ] K) (hF : Fl† ∘L Fl = 1) (v : (ι → Fin m) → K) :
    wpot a (G ⊙ Matrix.gram ℂ (fun j => (Fl†) (v j))) +
        wpot a (G ⊙ Matrix.gram ℂ (fun j => v j - Fl ((Fl†) (v j)))) =
      wpot a (G ⊙ Matrix.gram ℂ v) := by
  rw [gram_split Fl hF v, Matrix.hadamard_add, wpot_add]

/-- **The potential of the trivial kernel** is the number of inputs when the weight has row
sums one (it fixes the uniform vector). -/
theorem wpot_onesKernel (a : Matrix (Fin m) (Fin m) ℂ)
    (hrow : a *ᵥ (fun _ => (1 : ℂ)) = fun _ => 1) :
    wpot a (onesKernel ι m) = (m : ℝ) ^ Fintype.card ι := by
  have hr : ∀ q, ∑ q', a q q' = 1 := by
    intro q
    have h := congrFun hrow q
    simpa [Matrix.mulVec, dotProduct] using h
  set one : Fam (ι → Fin m) ℂ := WithLp.toLp 2 (fun _ => (1 : ℂ))
  have hact : ∀ j, act (kron a) one j = 1 := by
    intro j
    simp only [act_apply, one, smul_eq_mul, mul_one]
    rw [kron_row_sum]
    simp [hr]
  have hpot : wpot a (onesKernel ι m) = ‖act (kron a) one‖ ^ 2 := by
    rw [norm_sq_act_eq, wpot]
    congr 1
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro j' _
    simp [onesKernel, one, wsqOf]
  rw [hpot, norm_sq_fam]
  simp only [hact, norm_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_pi,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  rw [Finset.prod_const, Finset.card_univ]

end Potential

/-! ### The parity bound -/

section Parity

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- A matrix on one hidden register acts on families with at most its `L²` operator norm. -/
theorem norm_act_le (k : Matrix (Fin m) (Fin m) ℂ) (φ : Fam (Fin m) K) :
    ‖act k φ‖ ≤ ‖k‖ * ‖φ‖ := by
  set T : SparseLowerBounds.Joint (Fin m) K →L[ℂ] SparseLowerBounds.Joint (Fin m) K :=
    SparseLowerBounds.Joint.kernel k with hT
  have hk : act k φ = T φ := by
    ext q
    rw [hT, SparseLowerBounds.Joint.kernel_apply, act_apply]
  have hTk : ‖T‖ ≤ ‖k‖ := SparseLowerBounds.Joint.norm_kernel_le k
  rw [hk]
  calc ‖T φ‖ ≤ ‖T‖ * ‖φ‖ := T.le_opNorm φ
    _ ≤ ‖k‖ * ‖φ‖ := mul_le_mul_of_nonneg_right hTk (norm_nonneg _)

/-- **Parity bound for one family**: for an invertible Hermitian weight `a` with
`‖a⁻¹ Z a⁻¹‖ ≤ μ` and a contraction `M`,
`|Σ_j σ_j Re⟨φ_j, M φ_j⟩| ≤ μ^{|ι|} ‖W φ‖²`. -/
theorem wparity_bound (a : Matrix (Fin m) (Fin m) ℂ) (ha : a.IsHermitian) (hau : IsUnit a)
    {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : ‖a⁻¹ * parityMat m * a⁻¹‖ ≤ μ) (M : K →L[ℂ] K)
    (hM : ∀ v, ‖M v‖ ≤ ‖v‖) (φ : Fam (ι → Fin m) K) :
    |∑ j, parSign j * (⟪φ j, M (φ j)⟫_ℂ).re| ≤ μ ^ Fintype.card ι * ‖act (kron a) φ‖ ^ 2 := by
  have hdet : IsUnit a.det := (Matrix.isUnit_iff_isUnit_det a).mp hau
  have hinv : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a hdet
  have hinvH : (a⁻¹)ᴴ = a⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, ha.eq]
  set ξ := act (kron a) φ with hξ
  have hφ : φ = act (kron a⁻¹) ξ := by
    rw [hξ, ← act_mul, kron_mul, hinv, kron_one, act_one]
  set k := a⁻¹ * parityMat m * a⁻¹
  set χ := act (kron k) (joint (fun _ => M) ξ)
  have hsum : ∑ j, parSign j * (⟪φ j, M (φ j)⟫_ℂ).re = (⟪ξ, χ⟫_ℂ).re := by
    have h1 : ∑ j, parSign j * (⟪φ j, M (φ j)⟫_ℂ).re =
        (⟪φ, act (kron (parityMat m)) (joint (fun _ => M) φ)⟫_ℂ).re := by
      rw [inner_fam, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [act_kron_parity_apply, joint_apply, inner_smul_right, Complex.re_ofReal_mul]
    have h2 : act (kron (parityMat m)) (joint (fun _ => M) φ) =
        act (kron (parityMat m)) (act (kron a⁻¹) (joint (fun _ => M) ξ)) := by
      rw [hφ, ← act_joint_const]
    rw [h1, h2]
    conv_lhs => rw [hφ]
    rw [inner_act, kron_conjTranspose, hinvH, ← act_mul, ← act_mul, kron_mul, kron_mul]
  rw [hsum]
  have hone : ∀ ψ : Fam (Fin m) K, ‖act k ψ‖ ^ 2 ≤ μ ^ 2 * ‖ψ‖ ^ 2 := by
    intro ψ
    have h := norm_act_le k ψ
    have h' : ‖act k ψ‖ ≤ μ * ‖ψ‖ :=
      h.trans (mul_le_mul_of_nonneg_right hμ (norm_nonneg _))
    calc ‖act k ψ‖ ^ 2 ≤ (μ * ‖ψ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h' 2
      _ = μ ^ 2 * ‖ψ‖ ^ 2 := by ring
  have hχ : ‖χ‖ ^ 2 ≤ (μ ^ 2) ^ Fintype.card ι * ‖joint (fun _ => M) ξ‖ ^ 2 :=
    norm_sq_act_kron_le k (μ ^ 2) (sq_nonneg μ) hone _ ι rfl _
  have hMξ : ‖joint (fun _ => M) ξ‖ ≤ ‖ξ‖ := by
    have h2 : ‖joint (fun _ => M) ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
      rw [norm_sq_fam, norm_sq_fam]
      exact Finset.sum_le_sum fun j _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hM (ξ j)) 2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  have hχ' : ‖χ‖ ≤ μ ^ Fintype.card ι * ‖ξ‖ := by
    have hpos : 0 ≤ μ ^ Fintype.card ι * ‖ξ‖ := by positivity
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) hpos two_ne_zero).mp
    calc ‖χ‖ ^ 2 ≤ (μ ^ 2) ^ Fintype.card ι * ‖joint (fun _ => M) ξ‖ ^ 2 := hχ
      _ ≤ (μ ^ 2) ^ Fintype.card ι * ‖ξ‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (norm_nonneg _) hMξ 2
      _ = (μ ^ Fintype.card ι * ‖ξ‖) ^ 2 := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 (Fintype.card ι)]
  calc |(⟪ξ, χ⟫_ℂ).re| ≤ ‖⟪ξ, χ⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖ξ‖ * ‖χ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ξ‖ * (μ ^ Fintype.card ι * ‖ξ‖) :=
      mul_le_mul_of_nonneg_left hχ' (norm_nonneg _)
    _ = μ ^ Fintype.card ι * ‖ξ‖ ^ 2 := by ring

/-- **Parity bound for a kernel.** -/
theorem wparity_kernel_bound (a : Matrix (Fin m) (Fin m) ℂ) (ha : a.IsHermitian)
    (hau : IsUnit a) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : ‖a⁻¹ * parityMat m * a⁻¹‖ ≤ μ)
    {G : Matrix (ι → Fin m) (ι → Fin m) ℂ} (hG : G.PosSemidef) (M : K →L[ℂ] K)
    (hM : ∀ v, ‖M v‖ ≤ ‖v‖) (φ : Fam (ι → Fin m) K) :
    |∑ j, parSign j * ((G j j).re * (⟪φ j, M (φ j)⟫_ℂ).re)| ≤
      μ ^ Fintype.card ι * wpot a (G ⊙ Matrix.gram ℂ (fun j => φ j)) := by
  obtain ⟨B, rfl⟩ := exists_factor hG
  rw [wpot_hadamard_gram_eq, Finset.mul_sum]
  have hdiag : ∀ j, ((star B * B) j j).re * (⟪φ j, M (φ j)⟫_ℂ).re =
      ∑ k, (⟪scale (B k) φ j, M (scale (B k) φ j)⟫_ℂ).re := by
    intro j
    simp only [Matrix.mul_apply, Matrix.star_apply, scale_apply, map_smul, inner_smul_left,
      inner_smul_right, RCLike.star_def]
    rw [Complex.re_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [← mul_assoc, Complex.mul_conj', ← Complex.ofReal_pow, Complex.re_ofReal_mul,
      Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hswap : ∑ j, parSign j * (((star B * B) j j).re * (⟪φ j, M (φ j)⟫_ℂ).re) =
      ∑ k, ∑ j, parSign j * (⟪scale (B k) φ j, M (scale (B k) φ j)⟫_ℂ).re := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [hdiag, Finset.mul_sum]
  rw [hswap]
  calc |∑ k, ∑ j, parSign j * (⟪scale (B k) φ j, M (scale (B k) φ j)⟫_ℂ).re|
      ≤ ∑ k, |∑ j, parSign j * (⟪scale (B k) φ j, M (scale (B k) φ j)⟫_ℂ).re| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun k _ => wparity_bound a ha hau hμ0 hμ M hM _

end Parity

/-! ### Final protocols and adaptive trees -/

section Trees

variable {K F E L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
  {O : L → (ι → Fin m) → K →L[ℂ] K}

/-- **Kernel bound for a final protocol.** -/
theorem wprotocol_bound (a : Matrix (Fin m) (Fin m) ℂ) (ha : a.IsHermitian) (hau : IsUnit a)
    {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : ‖a⁻¹ * parityMat m * a⁻¹‖ ≤ μ)
    (hU : ∀ l j, OracleCircuit.IsUnitary (O l j))
    (w : L → ℕ) (C : ℝ) (hC : 1 ≤ C) (hO : ∀ l, WGrowth a (O l) (C ^ w l))
    (hO' : ∀ l, WGrowth a (fun j => star (O l j)) (C ^ w l))
    (M : E →L[ℂ] E) (hM : ∀ v, ‖M v‖ ≤ ‖v‖) :
    ∀ (p : ODERepeatProtocol.Protocol O E) (G : Matrix (ι → Fin m) (ι → Fin m) ℂ),
      G.PosSemidef →
      |parityFun G (fun j => corr M (p.successDensity j))| ≤
        μ ^ Fintype.card ι * C ^ p.worstCost w * wpot a G := by
  have hC0 : 0 ≤ C := by linarith
  intro p
  induction p with
  | abort =>
      intro G hG
      simp only [ODERepeatProtocol.Protocol.successDensity, corr_zero, parityFun, mul_zero,
        Finset.sum_const_zero, abs_zero]
      exact mul_nonneg (by positivity) (wpot_nonneg a hG)
  | freshTrial t k ih =>
      intro G hG
      have hch : (0 : ℝ) < t.choices := by exact_mod_cast t.choices_pos
      set v : Fin t.choices → (ι → Fin m) → K := fun c j => (t.circuit c).eval j t.seed
      set av : Fin t.choices → Fam (ι → Fin m) E :=
        fun c => WithLp.toLp 2 (fun j => (t.output†) (v c j))
      set qv : Fin t.choices → (ι → Fin m) → K :=
        fun c j => v c j - t.output ((t.output†) (v c j))
      have hvnorm : ∀ c j, ‖v c j‖ = 1 := by
        intro c j
        rw [isUnitary_norm ((t.circuit c).eval_unitary hU j), t.seed_unit]
      have hcorr : ∀ j, corr M ((ODERepeatProtocol.Protocol.freshTrial t k).successDensity j) =
          ∑ c, ((t.choices : ℝ)⁻¹ * (⟪av c j, M (av c j)⟫_ℂ).re +
            (t.choices : ℝ)⁻¹ * (‖qv c j‖ ^ 2 * corr M (k.successDensity j))) := by
        intro j
        have hmean : 1 - t.meanSuccess j = (t.choices : ℝ)⁻¹ * ∑ c, ‖qv c j‖ ^ 2 := by
          have hfw : ∀ c, ‖qv c j‖ ^ 2 = 1 - t.probability j c := by
            intro c
            rw [← failure_weight t.output t.output_isometry (v c j) (hvnorm c j)]
            rfl
          simp only [hfw, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, mul_one]
          rw [ODERepeatProtocol.TrialFamily.meanSuccess]
          field_simp
        have h1 : ((t.choices : ℂ))⁻¹ = (((t.choices : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul,
          ODERepeatProtocol.Protocol.successDensity, corr_add, corr_smul_real,
          ODERepeatProtocol.TrialFamily.oneTrialDensity_eq_kraus, h1, corr_smul_real, corr_sum,
          hmean]
        simp only [corr_pure, ODERepeatProtocol.TrialFamily.amplitude, av, v]
        ring
      have hsplit : parityFun G
          (fun j => corr M ((ODERepeatProtocol.Protocol.freshTrial t k).successDensity j)) =
          ∑ c, (t.choices : ℝ)⁻¹ * (parityFun G (fun j => (⟪av c j, M (av c j)⟫_ℂ).re) +
            parityFun (G ⊙ Matrix.gram ℂ (qv c)) (fun j => corr M (k.successDensity j))) := by
        simp only [hcorr]
        rw [parityFun_sum]
        apply Finset.sum_congr rfl
        intro c _
        rw [parityFun_add, parityFun_mul, parityFun_mul, parityFun_hadamard_gram, mul_add]
      rw [hsplit]
      have hbound : ∀ c, |parityFun G (fun j => (⟪av c j, M (av c j)⟫_ℂ).re) +
          parityFun (G ⊙ Matrix.gram ℂ (qv c)) (fun j => corr M (k.successDensity j))| ≤
          μ ^ Fintype.card ι * C ^ (t.maxCost w + k.worstCost w) * wpot a G := by
        intro c
        have hA := wparity_kernel_bound a ha hau hμ0 hμ hG M hM (av c)
        have hB := ih (G ⊙ Matrix.gram ℂ (qv c)) (hadamard_gram_posSemidef hG (qv c))
        have hpa : 0 ≤ wpot a (G ⊙ Matrix.gram ℂ (fun j => av c j)) :=
          wpot_hadamard_gram_nonneg a hG (av c)
        have hpq : 0 ≤ wpot a (G ⊙ Matrix.gram ℂ (qv c)) :=
          wpot_hadamard_gram_nonneg a hG (WithLp.toLp 2 (qv c))
        have hsum : wpot a (G ⊙ Matrix.gram ℂ (fun j => av c j)) +
            wpot a (G ⊙ Matrix.gram ℂ (qv c)) = wpot a (G ⊙ Matrix.gram ℂ (v c)) :=
          wpot_split a t.output t.output_isometry (v c)
        have hrun : wpot a (G ⊙ Matrix.gram ℂ (v c)) ≤ C ^ (t.circuit c).cost w * wpot a G :=
          wpot_run a hG w hC0 hO hO' (t.circuit c) t.seed t.seed_unit
        have hcost : C ^ (t.circuit c).cost w ≤ C ^ t.maxCost w :=
          pow_le_pow_right₀ hC (t.cost_le_maxCost w c)
        have hk1 : 1 ≤ C ^ k.worstCost w := one_le_pow₀ hC
        have hpG : 0 ≤ wpot a G := wpot_nonneg a hG
        have hμn : 0 ≤ μ ^ Fintype.card ι := by positivity
        calc _ ≤ |parityFun G (fun j => (⟪av c j, M (av c j)⟫_ℂ).re)| +
              |parityFun (G ⊙ Matrix.gram ℂ (qv c)) (fun j => corr M (k.successDensity j))| :=
              abs_add_le _ _
          _ ≤ μ ^ Fintype.card ι * wpot a (G ⊙ Matrix.gram ℂ (fun j => av c j)) +
              μ ^ Fintype.card ι * C ^ k.worstCost w * wpot a (G ⊙ Matrix.gram ℂ (qv c)) :=
              add_le_add hA hB
          _ ≤ μ ^ Fintype.card ι * C ^ k.worstCost w *
              (wpot a (G ⊙ Matrix.gram ℂ (fun j => av c j)) +
                wpot a (G ⊙ Matrix.gram ℂ (qv c))) := by
              nlinarith [mul_le_mul_of_nonneg_left hk1 (mul_nonneg hμn hpa)]
          _ ≤ μ ^ Fintype.card ι * C ^ k.worstCost w *
              (C ^ (t.circuit c).cost w * wpot a G) := by
              rw [hsum]
              exact mul_le_mul_of_nonneg_left hrun (by positivity)
          _ ≤ μ ^ Fintype.card ι * C ^ k.worstCost w * (C ^ t.maxCost w * wpot a G) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_right hcost hpG
          _ = μ ^ Fintype.card ι * C ^ (t.maxCost w + k.worstCost w) * wpot a G := by
              rw [pow_add]; ring
      calc |∑ c, (t.choices : ℝ)⁻¹ * (parityFun G (fun j => (⟪av c j, M (av c j)⟫_ℂ).re) +
            parityFun (G ⊙ Matrix.gram ℂ (qv c)) (fun j => corr M (k.successDensity j)))|
          ≤ ∑ c, |(t.choices : ℝ)⁻¹ * (parityFun G (fun j => (⟪av c j, M (av c j)⟫_ℂ).re) +
            parityFun (G ⊙ Matrix.gram ℂ (qv c)) (fun j => corr M (k.successDensity j)))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _c : Fin t.choices, (t.choices : ℝ)⁻¹ *
            (μ ^ Fintype.card ι * C ^ (t.maxCost w + k.worstCost w) * wpot a G) := by
            apply Finset.sum_le_sum
            intro c _
            rw [abs_mul, abs_of_pos (inv_pos.mpr hch)]
            exact mul_le_mul_of_nonneg_left (hbound c) (inv_nonneg.mpr hch.le)
        _ = μ ^ Fintype.card ι *
            C ^ (ODERepeatProtocol.Protocol.freshTrial t k).worstCost w * wpot a G := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ODERepeatProtocol.Protocol.worstCost]
            field_simp

/-- **Kernel bound for an adaptive protocol.** -/
theorem wtree_bound (a : Matrix (Fin m) (Fin m) ℂ) (ha : a.IsHermitian) (hau : IsUnit a)
    {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : ‖a⁻¹ * parityMat m * a⁻¹‖ ≤ μ)
    (hU : ∀ l j, OracleCircuit.IsUnitary (O l j))
    (w : L → ℕ) (C : ℝ) (hC : 1 ≤ C) (hO : ∀ l, WGrowth a (O l) (C ^ w l))
    (hO' : ∀ l, WGrowth a (fun j => star (O l j)) (C ^ w l))
    (M : E →L[ℂ] E) (hM : ∀ v, ‖M v‖ ≤ ‖v‖) :
    ∀ (T : Tree O F E) (G : Matrix (ι → Fin m) (ι → Fin m) ℂ), G.PosSemidef →
      |parityFun G (fun j => corr M (T.successDensity j))| ≤
        μ ^ Fintype.card ι * C ^ T.worstCost w * wpot a G := by
  have hC0 : 0 ≤ C := by linarith
  intro T
  induction T with
  | final p =>
      intro G hG
      exact wprotocol_bound a ha hau hμ0 hμ hU w C hC hO hO' M hM p G hG
  | test t s f ihs ihf =>
      intro G hG
      set v : (ι → Fin m) → K := fun j => t.circuit.eval j t.seed
      set qv : (ι → Fin m) → K := fun j => v j - t.flag ((t.flag†) (v j))
      have hvnorm : ∀ j, ‖v j‖ = 1 := by
        intro j
        rw [isUnitary_norm (t.circuit.eval_unitary hU j), t.seed_unit]
      have hsd : ∀ j, corr M ((Tree.test t s f).successDensity j) =
          ‖(t.flag†) (v j)‖ ^ 2 * corr M (s.successDensity j) +
            ‖qv j‖ ^ 2 * corr M (f.successDensity j) := by
        intro j
        have hfw := failure_weight t.flag t.flag_isometry (v j) (hvnorm j)
        change corr M ((algebraMap ℝ ℂ (t.probability j)) • s.successDensity j +
          (algebraMap ℝ ℂ (1 - t.probability j)) • f.successDensity j) = _
        have hfw' : ‖qv j‖ ^ 2 = 1 - ‖(t.flag†) (v j)‖ ^ 2 := hfw.symm
        rw [corr_add]
        erw [corr_smul_real, corr_smul_real]
        simp only [Algebra.algebraMap_self, RingHom.id_apply, TestRun.probability]
        rw [hfw']
      have hsplit : parityFun G (fun j => corr M ((Tree.test t s f).successDensity j)) =
          parityFun (G ⊙ Matrix.gram ℂ (fun j => (t.flag†) (v j)))
            (fun j => corr M (s.successDensity j)) +
          parityFun (G ⊙ Matrix.gram ℂ qv) (fun j => corr M (f.successDensity j)) := by
        simp only [hsd]
        rw [parityFun_add, parityFun_hadamard_gram, parityFun_hadamard_gram]
      rw [hsplit]
      have hGs := hadamard_gram_posSemidef hG (fun j => (t.flag†) (v j))
      have hGf := hadamard_gram_posSemidef hG qv
      have hS := ihs _ hGs
      have hF := ihf _ hGf
      have hps : 0 ≤ wpot a (G ⊙ Matrix.gram ℂ (fun j => (t.flag†) (v j))) := wpot_nonneg a hGs
      have hpf : 0 ≤ wpot a (G ⊙ Matrix.gram ℂ qv) := wpot_nonneg a hGf
      have hsum := wpot_split a (G := G) t.flag t.flag_isometry v
      have hrun : wpot a (G ⊙ Matrix.gram ℂ v) ≤ C ^ t.circuit.cost w * wpot a G :=
        wpot_run a hG w hC0 hO hO' t.circuit t.seed t.seed_unit
      have hms : C ^ s.worstCost w ≤ C ^ max (s.worstCost w) (f.worstCost w) :=
        pow_le_pow_right₀ hC (le_max_left _ _)
      have hmf : C ^ f.worstCost w ≤ C ^ max (s.worstCost w) (f.worstCost w) :=
        pow_le_pow_right₀ hC (le_max_right _ _)
      have hμn : 0 ≤ μ ^ Fintype.card ι := by positivity
      have hpG : 0 ≤ wpot a G := wpot_nonneg a hG
      set Cm := C ^ max (s.worstCost w) (f.worstCost w)
      calc _ ≤ |parityFun (G ⊙ Matrix.gram ℂ (fun j => (t.flag†) (v j)))
              (fun j => corr M (s.successDensity j))| +
            |parityFun (G ⊙ Matrix.gram ℂ qv) (fun j => corr M (f.successDensity j))| :=
            abs_add_le _ _
        _ ≤ μ ^ Fintype.card ι * C ^ s.worstCost w *
              wpot a (G ⊙ Matrix.gram ℂ (fun j => (t.flag†) (v j))) +
            μ ^ Fintype.card ι * C ^ f.worstCost w * wpot a (G ⊙ Matrix.gram ℂ qv) :=
            add_le_add hS hF
        _ ≤ μ ^ Fintype.card ι * Cm *
              (wpot a (G ⊙ Matrix.gram ℂ (fun j => (t.flag†) (v j))) +
                wpot a (G ⊙ Matrix.gram ℂ qv)) := by
            nlinarith [mul_le_mul_of_nonneg_left hms (mul_nonneg hμn hps),
              mul_le_mul_of_nonneg_left hmf (mul_nonneg hμn hpf)]
        _ ≤ μ ^ Fintype.card ι * Cm * (C ^ t.circuit.cost w * wpot a G) := by
            rw [hsum]
            exact mul_le_mul_of_nonneg_left hrun (by positivity)
        _ = μ ^ Fintype.card ι * C ^ (Tree.test t s f).worstCost w * wpot a G := by
            simp only [Cm, Tree.worstCost, pow_add]
            ring

/-- **Parity bound for adaptive protocols, any weight.** For an invertible Hermitian weight
with row sums one and `‖a⁻¹ Z a⁻¹‖ ≤ μ`, an oracle family whose labels have weight growth
`C ^ w l` (both directions) and a contraction `M` on the output space,
`|Σ_j σ_j Re tr(M σ_j)| ≤ μ^{|ι|} C^{worstCost} m^{|ι|}`. -/
theorem wtree_xor (a : Matrix (Fin m) (Fin m) ℂ) (ha : a.IsHermitian) (hau : IsUnit a)
    (hrow : a *ᵥ (fun _ => (1 : ℂ)) = fun _ => 1)
    {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : ‖a⁻¹ * parityMat m * a⁻¹‖ ≤ μ)
    (hU : ∀ l j, OracleCircuit.IsUnitary (O l j))
    (w : L → ℕ) (C : ℝ) (hC : 1 ≤ C) (hO : ∀ l, WGrowth a (O l) (C ^ w l))
    (hO' : ∀ l, WGrowth a (fun j => star (O l j)) (C ^ w l))
    (M : E →L[ℂ] E) (hM : ∀ v, ‖M v‖ ≤ ‖v‖) (T : Tree O F E) :
    |∑ j, parSign j * corr M (T.successDensity j)| ≤
      μ ^ Fintype.card ι * C ^ T.worstCost w * (m : ℝ) ^ Fintype.card ι := by
  have h := wtree_bound a ha hau hμ0 hμ hU w C hC hO hO' M hM T (onesKernel ι m)
    onesKernel_posSemidef
  rw [wpot_onesKernel a hrow] at h
  have hpf : parityFun (onesKernel ι m) (fun j => corr M (T.successDensity j)) =
      ∑ j, parSign j * corr M (T.successDensity j) := by
    simp [parityFun, onesKernel]
  rwa [hpf] at h

end Trees

end

end AdaptiveHamiltonianLowerBound
