import GateOptimalBinary.SignedNative
import GateOptimalBinary.ClipLocal
import LargeSparsityCore.NativeTwoNormCore

/-!
# Operator tools for the clipped regime

Generic facts used by the clipped regime (`ClipIface`):

* the one-qubit operations `condOp t u` form an algebra in `u` (`condOp_zero`, `condOp_add`,
  `condOp_sub`, `condOp_smul`), with `‖condOp t u‖ ≤ C` when every `u x` has Frobenius norm at
  most `C` (`norm_condOp_le`);
* `condOp_inner`: a one-qubit operation on a wire of a block is the block operation read from the
  configuration of the block and the other wires; `condOp_one_fblk`: on the middle wire of three,
  chosen by the first, it is a flag-diagonal block (`fblk`); `condOp_eq_fblk` combines the two;
* `spectral_conj'`, `conj_isometry'`, `norm_conj_le'`: the block structure
  `LargeSparsityCore.CayleyBlocks.Spectral`, unitarity and norms are invariant under conjugation
  by a unitary between two spaces;
* `norm_le_of_re_inner`: a self-adjoint operator with `|Re⟪Tv, v⟫| ≤ W ‖v‖²` has norm at most `W`.

References to the manuscript use its labels.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace GateOptimalBinary

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim SparseHamiltonian.GateNative
  GateOptimalPrecision
open SparseHamiltonian.GateODE (overwrite_apply_ι overwrite_apply_out)
open LargeSparsityCore.CayleyBlocks (Spectral R1)
open scoped InnerProduct Matrix

/-! ### One-qubit operations -/

section CondOp

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

theorem condOp_zero (t : W) : condOp (Q := Q) t (fun _ => 0) = 0 := by
  ext ψ x
  simp [condOp_apply]

theorem condOp_add (t : W) (u v : Cfg W → Matrix Bool Bool ℂ) :
    condOp (Q := Q) t u + condOp t v = condOp t (fun x => u x + v x) := by
  ext ψ x
  simp only [add_apply, PiLp.add_apply, condOp_apply, Matrix.add_apply, add_smul,
    Finset.sum_add_distrib]

theorem condOp_sub (t : W) (u v : Cfg W → Matrix Bool Bool ℂ) :
    condOp (Q := Q) t u - condOp t v = condOp t (fun x => u x - v x) := by
  ext ψ x
  simp only [sub_apply, PiLp.sub_apply, condOp_apply, Matrix.sub_apply, sub_smul,
    Finset.sum_sub_distrib]

theorem condOp_smul (t : W) (r : ℂ) (u : Cfg W → Matrix Bool Bool ℂ) :
    r • condOp (Q := Q) t u = condOp t (fun x => r • u x) := by
  ext ψ x
  simp only [smul_apply, PiLp.smul_apply, condOp_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.smul_sum, mul_smul]

theorem condOp_one' (t : W) : condOp (Q := Q) t (fun _ => (1 : Matrix Bool Bool ℂ)) = 1 :=
  condOp_one t

/-- **The norm of a one-qubit operation** is at most a bound on the Frobenius norms of its
matrices. -/
theorem norm_condOp_le (t : W) (u : Cfg W → Matrix Bool Bool ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ x, frob2 (u x) ≤ C) : ‖condOp (Q := Q) t u‖ ≤ C := by
  have h := norm_condOp_sub_le (Q := Q) t u (fun _ => 0) C hC
    (fun x => by rw [sub_zero]; exact hu x)
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro ψ
  have := h ψ (fun _ h' => absurd trivial h')
  rwa [condOp_zero, zero_apply, sub_zero] at this

/-- **A one-qubit operation on a wire of a block** is the block operation read from the
configuration of the block and of the other wires. -/
theorem condOp_inner {A : Type*} [Fintype A] [DecidableEq A] {e : A → W}
    (he : Function.Injective e) (t : A) (u : Cfg W → Matrix Bool Bool ℂ) :
    condOp (Q := Q) (e t) u = localOp e he (fun x => condOp t (fun y => u (overwrite e x y))) := by
  ext ψ y
  rw [condOp_apply, localOp_apply, condOp_apply]
  have hcfg : ∀ b, overwrite e y (Function.update (fun a => y (e a)) t b) =
      Function.update y (e t) b := by
    intro b
    funext w
    by_cases hw : ∃ a, e a = w
    · obtain ⟨a, rfl⟩ := hw
      rw [overwrite_apply_ι he]
      by_cases hat : a = t
      · subst hat
        simp
      · rw [Function.update_of_ne hat, Function.update_of_ne (fun h => hat (he h))]
    · push Not at hw
      rw [overwrite_apply_out e y _ w hw, Function.update_of_ne (fun h => hw t h.symm)]
  have hu' : u (overwrite e (clearCfg e y) (Function.update (fun a => y (e a)) t false)) =
      u (Function.update y (e t) false) := by
    rw [clearCfg, overwrite_overwrite, hcfg false]
  apply Finset.sum_congr rfl
  intro b _
  rw [hu', slice_apply, hcfg b]

/-- **The flag-controlled orientation operation on three local qubits** is a flag-diagonal
block. -/
theorem condOp_one_fblk (B : Bool → Matrix Bool Bool ℂ) :
    condOp (Q := Q) (1 : Fin 3) (fun y => B (y 0)) = matOp (blk (fblk B)) := by
  apply GateOptimalPrecision.ext_bas
  intro c q
  rw [condOp_bas, matOp_blk_bas]
  obtain ⟨⟨c0, c1, c2⟩, rfl⟩ : ∃ p, c = eQ.symm p := ⟨eQ c, (eQ.symm_apply_apply c).symm⟩
  simp only [eQ_symm_update1, Equiv.apply_symm_apply, Fintype.sum_prod_type, Fintype.sum_bool,
    fblk_apply]
  cases c0 <;> cases c1 <;> cases c2 <;> simp [eQ_symm_apply]

/-- **A one-qubit operation on the middle of three local qubits**, chosen by the first and by the
other wires but not by the third, is the flag-diagonal block of its matrices. -/
theorem condOp_eq_fblk {e : Fin 3 → W} (he : Function.Injective e) (u : Cfg W → Matrix Bool Bool ℂ)
    (hz : ∀ x v, u (Function.update x (e 2) v) = u x) :
    condOp (Q := Q) (e 1) u = localOp e he (fun x => matOp (blk (fblk (fun f =>
      u (overwrite e x ![f, false, false]))))) := by
  rw [condOp_inner he 1 u]
  congr 1
  funext x
  rw [← condOp_one_fblk]
  apply condOp_congr
  intro y
  have h : overwrite e x ![Function.update y 1 false 0, false, false] =
      Function.update (overwrite e x (Function.update y 1 false)) (e 2) false := by
    funext w
    by_cases hw : ∃ i, e i = w
    · obtain ⟨i, rfl⟩ := hw
      simp only [overwrite_apply_ι he, Function.update_apply, he.eq_iff]
      fin_cases i <;> simp
    · push Not at hw
      rw [overwrite_apply_out _ _ _ _ hw, Function.update_of_ne (fun h' => hw 2 h'.symm),
        overwrite_apply_out _ _ _ _ hw]
  show u (overwrite e x (Function.update y 1 false)) =
    u (overwrite e x ![Function.update y 1 false 0, false, false])
  rw [h, hz]

end CondOp

/-! ### Conjugation between two spaces -/

section Conj

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [CompleteSpace V']

theorem conj_comp' {W : V' →L[ℂ] V} (hW2 : W ∘L W† = 1) (A B : V →L[ℂ] V) :
    (W† ∘L A ∘L W) ∘L (W† ∘L B ∘L W) = W† ∘L (A ∘L B) ∘L W := by
  calc (W† ∘L A ∘L W) ∘L (W† ∘L B ∘L W) = W† ∘L A ∘L (W ∘L W†) ∘L B ∘L W := by
        simp only [comp_assoc]
    _ = _ := by rw [hW2, LargeSparsityCore.CayleyBlocks.one_comp]; simp only [comp_assoc]

theorem conj_one' {W : V' →L[ℂ] V} (hW1 : W† ∘L W = 1) : W† ∘L (1 : V →L[ℂ] V) ∘L W = 1 := by
  rw [LargeSparsityCore.CayleyBlocks.one_comp, hW1]

/-- **The block structure is invariant under conjugation by a unitary between two spaces.** -/
theorem spectral_conj' {K D Pp Pm : V →L[ℂ] V} {q : ℝ} (h : Spectral K D Pp Pm q)
    (U : V' →L[ℂ] V) (hU1 : U† ∘L U = 1) (hU2 : U ∘L U† = 1) :
    Spectral (U† ∘L K ∘L U) (U† ∘L D ∘L U) (U† ∘L Pp ∘L U) (U† ∘L Pm ∘L U) q := by
  have key := conj_comp' hU2
  have hadj : ∀ A : V →L[ℂ] V, IsSelfAdjoint A → IsSelfAdjoint (U† ∘L A ∘L U) := by
    intro A hA
    change (U† ∘L A ∘L U)† = U† ∘L A ∘L U
    rw [adjoint_comp, adjoint_comp, adjoint_adjoint, hA.adjoint_eq, comp_assoc]
  have hone := conj_one' hU1
  have hR1 : R1 (U† ∘L K ∘L U) = U† ∘L R1 K ∘L U := by
    simp only [R1, comp_smul, smul_comp, comp_add, add_comp, hone]
  have hsub : ∀ A : V →L[ℂ] V, 1 - U† ∘L A ∘L U = U† ∘L (1 - A) ∘L U := by
    intro A
    rw [sub_comp, comp_sub, hone]
  refine ⟨hadj K h.self, ?_, ?_, hadj Pp h.pp_adj, hadj Pm h.pm_adj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [key, h.pp_idem]
  · rw [key, h.pm_idem]
  · rw [key, h.pp_pm, zero_comp, comp_zero]
  · rw [key, h.pm_pp, zero_comp, comp_zero]
  · rw [key, h.k_pp, smul_comp, comp_smul]
  · rw [key, h.k_pm, smul_comp, comp_smul]
  · rw [hR1, hsub, key, h.cayley_right, hone]
  · rw [hR1, hsub, key, h.cayley_left, hone]

theorem conj_isometry' {U : V' →L[ℂ] V} (hU1 : U† ∘L U = 1) (hU2 : U ∘L U† = 1)
    {A : V →L[ℂ] V} (hA : A† ∘L A = 1) : (U† ∘L A ∘L U)† ∘L (U† ∘L A ∘L U) = 1 := by
  have e : (U† ∘L A ∘L U)† = U† ∘L A† ∘L U := by
    rw [adjoint_comp, adjoint_comp, adjoint_adjoint, comp_assoc]
  rw [e, conj_comp' hU2, hA, conj_one' hU1]

theorem norm_conj_le' (U : V' →L[ℂ] V) (A : V →L[ℂ] V) (hU : U† ∘L U = 1) :
    ‖U† ∘L A ∘L U‖ ≤ ‖A‖ := by
  have hUn : ‖U‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro v
    have hh := (norm_map_iff_adjoint_comp_self U).mpr hU v
    simpa only [one_mul] using hh.le
  have hUa : ‖U†‖ ≤ 1 := by rw [LinearIsometryEquiv.norm_map]; exact hUn
  calc ‖U† ∘L A ∘L U‖ ≤ ‖U†‖ * (‖A‖ * ‖U‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _)
          (norm_nonneg _))
    _ ≤ 1 * (‖A‖ * 1) := by gcongr
    _ = ‖A‖ := by ring

theorem R1_conj' {U : V' →L[ℂ] V} (hU1 : U† ∘L U = 1) (K : V →L[ℂ] V) :
    R1 (U† ∘L K ∘L U) = U† ∘L R1 K ∘L U := by
  simp only [R1, comp_smul, smul_comp, comp_add, add_comp, conj_one' hU1]

theorem bulk_conj' {U : V' →L[ℂ] V} (hU1 : U† ∘L U = 1) (A B : V →L[ℂ] V) :
    LargeSparsityCore.CayleyBlocks.bulk (U† ∘L A ∘L U) (U† ∘L B ∘L U) =
      U† ∘L LargeSparsityCore.CayleyBlocks.bulk A B ∘L U := by
  rw [LargeSparsityCore.CayleyBlocks.bulk, LargeSparsityCore.CayleyBlocks.bulk, sub_comp,
    sub_comp, comp_sub, comp_sub, conj_one' hU1]

end Conj

/-- **A self-adjoint operator with bounded quadratic form** has norm at most the bound. -/
theorem norm_le_of_re_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v, |RCLike.re (inner ℂ (T v) v)| ≤ C * ‖v‖ ^ 2) : ‖T‖ ≤ C := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hT.isSymmetric]
  apply ciSup_le
  intro v
  by_cases hv : v = 0
  · subst hv
    simp [ContinuousLinearMap.rayleighQuotient, hC]
  · have hv2 : 0 < ‖v‖ ^ 2 := by positivity
    rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply, abs_div,
      abs_of_pos hv2, div_le_iff₀ hv2]
    exact h v


end

end GateOptimalBinary
