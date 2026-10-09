import LinearSystemLowerBound.Weight.OneCoordinate
import SparseHamiltonian.MultiOracleCircuit
import SparseHamiltonian.WeightedClock

/-!
# Weight growth of oracle families

For hidden inputs `j : ι → Fin m` and an input-dependent family of operators `O j` on a
workspace `K`, the joint operator acts on families `ψ = (ψ_j)` by `(Õ ψ)_j = O j ψ_j`.  It has
**weight growth** `C` (`Growth O C`) if `‖W Õ ψ‖² ≤ C ‖W ψ‖²` for every family, where
`W = w^{⊗ι}` (`kron (weight m)`) is the weight of the multiplicative adversary.

* `growth_const`: an input-independent norm-preserving operator has growth `1`.
* `growth_bit`: an operator depending only on the bit `[j c = q₀]` (norm-preserving `V₀`,
  `V₁`) has growth `(1 + 2/√m)²`; this is the paper's estimate `‖w D w⁻¹‖ ≤ 1 + 2/√m`,
  extended to arbitrary single-bit responses.
* `growth_mul`, `growth_diagonal`, `growth_conj`: products, block-diagonal operators on
  spectator branches, and fixed isometric layouts.
* `growth_program`: a circuit has growth `C ^ cost` when each label has growth `C ^ w l` in
  both directions.
-/

namespace LinearSystemLowerBound

noncomputable section
open scoped BigOperators InnerProductSpace Matrix
open SparseHamiltonian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- **Weight growth** of an input-dependent operator family. -/
def Growth (O : (ι → Fin m) → K →L[ℂ] K) (C : ℝ) : Prop :=
  ∀ ψ : Fam (ι → Fin m) K,
    ‖act (kron (weight m)) (joint O ψ)‖ ^ 2 ≤ C * ‖act (kron (weight m)) ψ‖ ^ 2

theorem growth_const (U : K →L[ℂ] K) (hU : ∀ v, ‖U v‖ = ‖v‖) :
    Growth (ι := ι) (m := m) (fun _ => U) 1 := by
  intro ψ
  rw [act_joint_const, norm_joint _ (fun _ => hU), one_mul]

theorem growth_mono {O : (ι → Fin m) → K →L[ℂ] K} {C C' : ℝ} (h : Growth O C)
    (hCC : C ≤ C') : Growth O C' :=
  fun ψ => (h ψ).trans (mul_le_mul_of_nonneg_right hCC (sq_nonneg _))

theorem growth_mul {O O' : (ι → Fin m) → K →L[ℂ] K} {C C' : ℝ} (hO : Growth O C)
    (hO' : Growth O' C') (hC : 0 ≤ C) : Growth (fun j => O j * O' j) (C * C') := by
  intro ψ
  rw [joint_comp]
  calc _ ≤ C * ‖act (kron (weight m)) (joint O' ψ)‖ ^ 2 := hO _
    _ ≤ C * (C' * ‖act (kron (weight m)) ψ‖ ^ 2) := mul_le_mul_of_nonneg_left (hO' ψ) hC
    _ = C * C' * ‖act (kron (weight m)) ψ‖ ^ 2 := by ring

/-- **Single-bit queries.**  An operator acting as `V₁` when `j c = q₀` and as `V₀`
otherwise has weight growth `(1 + 2/√m)²`. -/
theorem growth_bit (hm : m ≠ 0) (c : ι) (q₀ : Fin m) (V₀ V₁ : K →L[ℂ] K)
    (h₀ : ∀ v, ‖V₀ v‖ = ‖v‖) (h₁ : ∀ v, ‖V₁ v‖ = ‖v‖) :
    Growth (fun j : ι → Fin m => if j c = q₀ then V₁ else V₀) ((1 + 2 / Real.sqrt m) ^ 2) := by
  intro ψ
  set O : (ι → Fin m) → K →L[ℂ] K := fun j => if j c = q₀ then V₁ else V₀
  rw [kron_eq_splitMat c, norm_sq_act_splitMat, norm_sq_act_splitMat, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  have hfib : ∀ q', act (kron (weight m)) (fiber c (joint O ψ) q') =
      joint (fun _ => bitOp q₀ V₀ V₁ q') (act (kron (weight m)) (fiber c ψ q')) := by
    intro q'
    have h : fiber c (joint O ψ) q' = joint (fun _ => bitOp q₀ V₀ V₁ q') (fiber c ψ q') := by
      ext r'
      simp only [fiber_apply, joint_apply, O, splitEquiv_self, bitOp]
    rw [h, act_joint_const]
  have hin : (WithLp.toLp 2 (fun q' => act (kron (weight m)) (fiber c (joint O ψ) q') r) :
      Fam (Fin m) K) =
      joint (bitOp q₀ V₀ V₁)
        (WithLp.toLp 2 (fun q' => act (kron (weight m)) (fiber c ψ q') r)) := by
    ext q'
    simp only [joint_apply]
    rw [hfib]
    rfl
  rw [hin]
  have h := weight_growth_bit hm q₀ V₀ V₁ h₀ h₁
    (WithLp.toLp 2 (fun q' => act (kron (weight m)) (fiber c ψ q') r) : Fam (Fin m) K)
  calc _ ≤ ((1 + 2 / Real.sqrt m) * ‖act (weight m)
        (WithLp.toLp 2 (fun q' => act (kron (weight m)) (fiber c ψ q') r) :
          Fam (Fin m) K)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by ring

/-! ### Block-diagonal operators -/

section Diagonal

variable {S : Type*} [Fintype S]

/-- The block of a family of block vectors. -/
def blk (s : S) (φ : Fam (ι → Fin m) (PiLp 2 (fun _ : S => K))) : Fam (ι → Fin m) K :=
  WithLp.toLp 2 (fun j => φ j s)

omit [InnerProductSpace ℂ K] [Fintype S] in
theorem piLp_sum_apply {X : Type*} (t : Finset X) (f : X → PiLp 2 (fun _ : S => K)) (s : S) :
    (∑ x ∈ t, f x) s = ∑ x ∈ t, f x s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]

theorem blk_act (s : S) (A : Matrix (ι → Fin m) (ι → Fin m) ℂ)
    (φ : Fam (ι → Fin m) (PiLp 2 (fun _ : S => K))) :
    blk s (act A φ) = act A (blk s φ) := by
  ext j
  simp only [blk, act_apply, PiLp.toLp_apply, piLp_sum_apply, PiLp.smul_apply]

omit [InnerProductSpace ℂ K] in
theorem norm_sq_blk (φ : Fam (ι → Fin m) (PiLp 2 (fun _ : S => K))) :
    ‖φ‖ ^ 2 = ∑ s, ‖blk s φ‖ ^ 2 := by
  rw [norm_sq_fam]
  simp only [norm_sq_fam, blk]
  rw [Finset.sum_comm]

/-- **Block-diagonal operators.**  If every block has growth `C`, so does the
block-diagonal operator (spectator branches, controlled and masked calls). -/
theorem growth_diagonal (O : S → (ι → Fin m) → K →L[ℂ] K) (C : ℝ)
    (hO : ∀ s, Growth (O s) C) :
    Growth (fun j => WeightedClock.diagonal (fun s : S => O s j)) C := by
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

end Diagonal

/-! ### Fixed layouts -/

section Conj

variable [CompleteSpace K] {K' : Type*} [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
  [CompleteSpace K']

/-- **Fixed isometric layouts** preserve weight growth. -/
theorem growth_conj (Φ : K ≃ₗᵢ[ℂ] K') (O : (ι → Fin m) → K →L[ℂ] K) (C : ℝ)
    (hO : Growth O C) : Growth (fun j => Φ.conjStarAlgEquiv (O j)) C := by
  intro ψ'
  set ψ : Fam (ι → Fin m) K := WithLp.toLp 2 (fun j => Φ.symm (ψ' j))
  have hψ' : ψ' = WithLp.toLp 2 (fun j => Φ (ψ j)) := by
    ext j
    simp [ψ]
  have hjoint : joint (fun j => Φ.conjStarAlgEquiv (O j)) ψ' =
      WithLp.toLp 2 (fun j => Φ ((joint O ψ) j)) := by
    ext j
    simp [ψ, joint_apply]
  have hpush : ∀ φ : Fam (ι → Fin m) K, act (kron (weight m))
      (WithLp.toLp 2 (fun j => Φ (φ j)) : Fam (ι → Fin m) K') =
      WithLp.toLp 2 (fun j => Φ ((act (kron (weight m)) φ) j)) := by
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

end Conj

/-! ### Circuits -/

section Programs

variable [CompleteSpace K]

theorem isUnitary_norm {U : K →L[ℂ] K} (hU : OracleCircuit.IsUnitary U) (v : K) :
    ‖U v‖ = ‖v‖ :=
  (U.norm_map_iff_adjoint_comp_self.mpr hU.1) v

/-- **Circuits.**  If every label has weight growth `C ^ w l` in the forward and inverse
direction, a circuit has growth `C ^ cost`. -/
theorem growth_program {L : Type*} (O : L → (ι → Fin m) → K →L[ℂ] K) (w : L → ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hO : ∀ l, Growth (O l) (C ^ w l))
    (hO' : ∀ l, Growth (fun j => star (O l j)) (C ^ w l))
    (p : MultiOracleCircuit.Program O) :
    Growth (fun j => p.eval j) (C ^ p.cost w) := by
  induction p with
  | fixed U hU =>
      simp only [MultiOracleCircuit.Program.eval_fixed, MultiOracleCircuit.Program.cost_fixed,
        pow_zero]
      exact growth_const U (isUnitary_norm hU)
  | query l => exact hO l
  | queryAdjoint l => exact hO' l
  | seq p q hp hq =>
      simp only [MultiOracleCircuit.Program.eval_seq, MultiOracleCircuit.Program.cost_seq,
        pow_add]
      exact growth_mul hp hq (pow_nonneg hC _)

end Programs

end

end LinearSystemLowerBound
