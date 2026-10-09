import GateEfficientODE.Model.Instr

/-!
# The block estimate for coherent selection

A label register is a set of configurations of the unexposed wires.  The
branch embedding `branchEmb c` places the label `z` and a payload vector on
the configuration `c z`, with every exposed wire clear.  An operator that
acts on the exposed wires according to the configuration of the others
(`localOp`) is within `ε` of the direct sum of target operators on the
branch space, as soon as every block is within `ε` of its target on the
clear column (`localOp_branch_error`).  The released full-output simulation
bound is exactly such a block estimate.
-/

namespace SparseHamiltonian.GateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open scoped InnerProduct BigOperators

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- The single-configuration embedding of the payload. -/
def basL (x : Cfg W) : Q →L[ℂ] Reg W Q :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Cfg W => Q)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun y => if y = x then (1 : Q →L[ℂ] Q) else 0)

omit [DecidableEq W] [CompleteSpace Q] in
@[simp] theorem basL_apply (x : Cfg W) (q : Q) : basL x q = bas x q := by
  apply PiLp.ext
  intro y
  simp only [basL, comp_apply, bas_apply]
  split_ifs with h <;> simp [h]

theorem basL_adjoint_comp (x : Cfg W) : (basL (Q := Q) x)† ∘L basL x = 1 := by
  have h : ∀ q : Q, ‖basL (W := W) (Q := Q) x q‖ = ‖q‖ := fun q => by rw [basL_apply, norm_bas]
  exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (basL (W := W) (Q := Q) x)).mp h

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [Fintype W] [DecidableEq A] in
theorem cfg_eq_iff {ι : A → W} (hι : Function.Injective ι) (y c : Cfg W) :
    y = c ↔ outPart ι y = outPart ι c ∧ (fun a => y (ι a)) = (fun a => c (ι a)) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    have h := (splitCfg ι hι).injective (Prod.ext h1 h2 : splitCfg ι hι y = splitCfg ι hι c)
    exact h

omit [CompleteSpace Q] in
/-- A basis vector is the `put` of its exposed basis column. -/
theorem bas_eq_put {ι : A → W} (hι : Function.Injective ι) (c : Cfg W) (q : Q) :
    bas c q = put ι hι c (bas (fun a => c (ι a)) q) := by
  apply PiLp.ext
  intro y
  rw [put_apply, bas_apply]
  by_cases h1 : outPart ι y = outPart ι c
  · rw [if_pos h1, bas_apply]
    by_cases h2 : (fun a => y (ι a)) = (fun a => c (ι a))
    · rw [if_pos ((cfg_eq_iff hι y c).mpr ⟨h1, h2⟩), if_pos h2]
    · rw [if_neg (fun h => h2 ((cfg_eq_iff hι y c).mp h).2), if_neg h2]
  · rw [if_neg h1, if_neg (fun h => h1 ((cfg_eq_iff hι y c).mp h).1)]

omit [CompleteSpace Q] in
theorem put_sub {ι : A → W} (hι : Function.Injective ι) (x : Cfg W) (φ φ' : Reg A Q) :
    put ι hι x (φ - φ') = put ι hι x φ - put ι hι x φ' := by
  simp only [put, Pi.single_sub, WithLp.toLp_sub, map_sub]

variable {Λ : Type*} [Fintype Λ]

/-- Branch `z` with payload `φ z` on the configuration `c z`. -/
def branchEmb (c : Λ → Cfg W) : ODEJointLCU.BranchSpace Λ Q →L[ℂ] Reg W Q :=
  ∑ z, basL (c z) ∘L PiLp.proj 2 (fun _ : Λ => Q) z

omit [CompleteSpace Q] in
theorem branchEmb_apply (c : Λ → Cfg W) (φ : ODEJointLCU.BranchSpace Λ Q) :
    branchEmb c φ = ∑ z, bas (c z) (φ z) := by
  simp [branchEmb, basL_apply]

/-- Distinct configurations give an isometric branch embedding. -/
theorem branchEmb_isometry (c : Λ → Cfg W) (hc : Function.Injective c) :
    (branchEmb (Q := Q) c)† ∘L branchEmb c = 1 := by
  have hnorm : ∀ φ : ODEJointLCU.BranchSpace Λ Q, ‖branchEmb (Q := Q) c φ‖ = ‖φ‖ := by
    intro φ
    rw [branchEmb_apply]
    have hsq : ‖∑ z, bas (c z) (φ z)‖ ^ 2 = ‖φ‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
      have hcoord : ∀ y : Cfg W, (∑ z, bas (c z) (φ z)) y =
          ∑ z, if y = c z then φ z else 0 := by
        intro y
        rw [WithLp.ofLp_sum, Finset.sum_apply]
        rfl
      simp only [hcoord]
      have hsq' : ∀ y : Cfg W, ‖∑ z, (if y = c z then φ z else 0)‖ ^ 2 =
          ∑ z, if y = c z then ‖φ z‖ ^ 2 else 0 := by
        intro y
        by_cases hy : ∃ z, y = c z
        · obtain ⟨z, rfl⟩ := hy
          rw [Finset.sum_eq_single z, Finset.sum_eq_single z, if_pos rfl, if_pos rfl]
          · intro z' _ hz'; rw [if_neg (fun h => hz' (hc h).symm)]
          · intro h; exact absurd (Finset.mem_univ z) h
          · intro z' _ hz'; rw [if_neg (fun h => hz' (hc h).symm)]
          · intro h; exact absurd (Finset.mem_univ z) h
        · push Not at hy
          rw [Finset.sum_eq_zero (fun z _ => if_neg (hy z)),
            Finset.sum_eq_zero (fun z _ => if_neg (hy z))]
          simp
      simp only [hsq']
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_ite_eq']
      simp
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (branchEmb (Q := Q) c)).mp hnorm

/-- **Block estimate.**  If the exposed-wire operator selected by every label
configuration is within `ε` of the target on the clear column, the selected
operator is within `ε` of the direct sum of targets on the branch space. -/
theorem localOp_branch_error {ι : A → W} (hι : Function.Injective ι)
    (F : Cfg W → (Reg A Q →L[ℂ] Reg A Q)) (c : Λ → Cfg W)
    (hclear : ∀ z a, c z (ι a) = false)
    (hsep : ∀ z z', outPart ι (c z) = outPart ι (c z') → z = z')
    (U : Λ → Q →L[ℂ] Q) (ε : ℝ) (hε : 0 ≤ ε)
    (hblock : ∀ z, ‖F (clearCfg ι (c z)) ∘L basL (W := A) (Q := Q) (fun _ => false) -
      basL (W := A) (Q := Q) (fun _ => false) ∘L U z‖ ≤ ε) :
    ‖localOp ι hι F ∘L branchEmb c - branchEmb c ∘L WeightedClock.diagonal U‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro φ
  have hcol : ∀ z, (fun a => c z (ι a)) = (fun _ => false) := fun z => funext (hclear z)
  have hrep : (localOp ι hι F ∘L branchEmb c - branchEmb c ∘L WeightedClock.diagonal U) φ =
      ∑ z, put ι hι (c z) ((F (clearCfg ι (c z)) ∘L basL (W := A) (Q := Q) (fun _ => false) -
        basL (W := A) (Q := Q) (fun _ => false) ∘L U z) (φ z)) := by
    rw [sub_apply, comp_apply, comp_apply, branchEmb_apply, branchEmb_apply, map_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z _
    rw [bas_eq_put hι (c z), bas_eq_put hι (c z), hcol z, localOp_put, ← put_sub]
    congr 1
    simp only [sub_apply, comp_apply, basL_apply, WeightedClock.diagonal_apply]
  rw [hrep]
  have hsq : ‖∑ z, put ι hι (c z) ((F (clearCfg ι (c z)) ∘L
        basL (W := A) (Q := Q) (fun _ => false) -
        basL (W := A) (Q := Q) (fun _ => false) ∘L U z) (φ z))‖ ^ 2 ≤ (ε * ‖φ‖) ^ 2 := by
    rw [norm_sum_put_sq hι c hsep, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z _
    rw [← mul_pow]
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hblock z) (norm_nonneg _)))
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hε (norm_nonneg _))).mp hsq

end

end SparseHamiltonian.GateODE
