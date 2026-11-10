import GateOptimalPrecision.LocalFactor
import GateEfficientNative.Native.Private
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Three-qubit blocks on the gate register

The stable signed factor `U(c)` of the paragraph "A stable constant-dimensional signed factor" of
Section `gate:sec:native` (`uMat`) is a matrix on the three-qubit index `Q3 = f × (o × z)`. This
module places such matrices on three wires of a register with any payload:

* `eQ`, `blk`: the configurations of three wires are the index `Q3`, and `blk M` is `M` on these
  configurations (`blk_mul`, `blk_one`, `blk_conjTranspose`);
* `norm_matOp_le`: a matrix with `‖M v‖ ≤ C ‖v‖` on configurations acts with norm at most `C` on
  every payload (by a positive semidefinite decomposition of `C² - M†M`); `norm_matOp_blk_le`:
  `‖matOp (blk M)‖ ≤ ‖M‖` for the L2 operator norm of `M`;
* `condOp_zero_eq_blk`, `condOp_one_eq_blk`, `gateOp_tof_eq_blk`: a one-qubit matrix on the flag
  or the orientation qubit, and the Toffoli gate `f, o → z`, are `blk (u ⊗ I)`, `blk (I ⊗ u ⊗ I)`
  and `blk tofMat`;
* `condOp_outer`: a one-qubit operation on a wire of a block, chosen by the configuration outside
  the block, is the block operation selected by that configuration.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace GateOptimalPrecision

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open GateODE (put put_apply localOp_put bas_eq_put overwrite_apply_ι overwrite_apply_out)
open scoped InnerProduct InnerProductSpace BigOperators ComplexConjugate Kronecker Matrix
  ComplexOrder

/-! ### Linearity of `matOp` -/

section MatOp

variable {A : Type*} [Fintype A] [DecidableEq A]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

omit [CompleteSpace Q] in
theorem matOp_zero' : matOp (Q := Q) (0 : Matrix (Cfg A) (Cfg A) ℂ) = 0 := by
  ext ψ b
  simp [matOp_apply]

omit [CompleteSpace Q] in
theorem matOp_add' (M N : Matrix (Cfg A) (Cfg A) ℂ) :
    matOp (Q := Q) (M + N) = matOp M + matOp N := by
  ext ψ b
  simp only [matOp_apply, add_apply, PiLp.add_apply, Matrix.add_apply, add_smul,
    Finset.sum_add_distrib]

omit [CompleteSpace Q] in
theorem matOp_sub' (M N : Matrix (Cfg A) (Cfg A) ℂ) :
    matOp (Q := Q) (M - N) = matOp M - matOp N := by
  ext ψ b
  simp only [matOp_apply, sub_apply, PiLp.sub_apply, Matrix.sub_apply, sub_smul,
    Finset.sum_sub_distrib]

omit [CompleteSpace Q] in
theorem matOp_smul' (c : ℂ) (M : Matrix (Cfg A) (Cfg A) ℂ) :
    matOp (Q := Q) (c • M) = c • matOp M := by
  ext ψ b
  simp only [matOp_apply, smul_apply, PiLp.smul_apply, Matrix.smul_apply, smul_eq_mul,
    mul_smul, Finset.smul_sum]

omit [CompleteSpace Q] in
theorem matOp_sum' {ι : Type*} (s : Finset ι) (M : ι → Matrix (Cfg A) (Cfg A) ℂ) :
    matOp (Q := Q) (∑ i ∈ s, M i) = ∑ i ∈ s, matOp (M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, matOp_zero']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, matOp_add', ih]

/-- `‖matOp M ψ‖² = Re⟪ψ, matOp (M†M) ψ⟫`. -/
theorem norm_matOp_sq (M : Matrix (Cfg A) (Cfg A) ℂ) (ψ : Reg A Q) :
    ‖matOp M ψ‖ ^ 2 = RCLike.re ⟪ψ, matOp (Mᴴ * M) ψ⟫_ℂ := by
  rw [← matOp_mul, ← matOp_adjoint, comp_apply, adjoint_inner_right]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm

/-- **The payload bound**: a matrix with `‖M v‖ ≤ C ‖v‖` on configurations acts with norm at most
`C` on every payload. -/
theorem norm_matOp_le (M : Matrix (Cfg A) (Cfg A) ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ v : Cfg A → ℂ, ∑ b, ‖(M *ᵥ v) b‖ ^ 2 ≤ C ^ 2 * ∑ c, ‖v c‖ ^ 2) (ψ : Reg A Q) :
    ‖matOp M ψ‖ ≤ C * ‖ψ‖ := by
  set P : Matrix (Cfg A) (Cfg A) ℂ := ((C ^ 2 : ℝ) : ℂ) • 1 - Mᴴ * M with hP
  have hdot : ∀ v : Cfg A → ℂ, star v ⬝ᵥ ((Mᴴ * M) *ᵥ v) =
      ((∑ b, ‖(M *ᵥ v) b‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Complex.conj_mul']
    push_cast
    ring
  have hdot1 : ∀ v : Cfg A → ℂ, star v ⬝ᵥ v = ((∑ c, ‖v c‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Complex.conj_mul']
    push_cast
    ring
  have hPh : P.IsHermitian := by
    rw [hP]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    congr 1
    rw [show star ((C ^ 2 : ℝ) : ℂ) = ((C ^ 2 : ℝ) : ℂ) from Complex.conj_ofReal _]
  have hPsd : P.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hPh (fun v => ?_)
    rw [hP, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, hdot, hdot1, smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    exact Complex.zero_le_real.mpr (by linarith [hM v])
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hPsd
  set k₀ : Cfg A := fun _ => false
  set B : Fin m → Matrix (Cfg A) (Cfg A) ℂ :=
    fun i => Matrix.of fun k c => if k = k₀ then star (v i c) else 0 with hB
  have hBB : ∀ i, Matrix.vecMulVec (v i) (star (v i)) = (B i)ᴴ * B i := by
    intro i
    ext c c'
    simp only [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hB,
      Matrix.of_apply, Pi.star_apply]
    rw [Finset.sum_eq_single k₀]
    · simp
    · intro k _ hk
      simp [hk]
    · intro h
      exact absurd (Finset.mem_univ k₀) h
  have hre : RCLike.re ⟪ψ, matOp P ψ⟫_ℂ = C ^ 2 * ‖ψ‖ ^ 2 - ‖matOp M ψ‖ ^ 2 := by
    rw [norm_matOp_sq M ψ, hP, matOp_sub', matOp_smul', matOp_one, sub_apply, inner_sub_right,
      smul_apply, one_apply_eq_self, inner_smul_right, map_sub]
    congr 1
    rw [inner_self_eq_norm_sq_to_K]
    have e : ((C ^ 2 : ℝ) : ℂ) * ((‖ψ‖ : ℂ) ^ 2) = ((C ^ 2 * ‖ψ‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    show RCLike.re (((C ^ 2 : ℝ) : ℂ) * ((‖ψ‖ : ℂ) ^ 2)) = C ^ 2 * ‖ψ‖ ^ 2
    rw [e]
    exact Complex.ofReal_re _
  have hnn : 0 ≤ RCLike.re ⟪ψ, matOp P ψ⟫_ℂ := by
    rw [hv, matOp_sum', sum_apply, inner_sum, map_sum]
    apply Finset.sum_nonneg
    intro i _
    rw [hBB i, ← norm_matOp_sq]
    positivity
  have hsq : ‖matOp M ψ‖ ^ 2 ≤ (C * ‖ψ‖) ^ 2 := by
    rw [mul_pow]
    linarith
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp hsq

end MatOp

/-! ### Three-wire blocks -/

section Block

/-- The configurations of three wires as the three-qubit index `f × (o × z)`. -/
def eQ : Cfg (Fin 3) ≃ Q3 where
  toFun x := (x 0, (x 1, x 2))
  invFun q := ![q.1, q.2.1, q.2.2]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv q := rfl

/-- A three-qubit matrix on the configurations of three wires. -/
def blk (M : Matrix Q3 Q3 ℂ) : Matrix (Cfg (Fin 3)) (Cfg (Fin 3)) ℂ := M.submatrix eQ eQ

theorem blk_mul (M N : Matrix Q3 Q3 ℂ) : blk (M * N) = blk M * blk N :=
  (Matrix.submatrix_mul_equiv M N eQ eQ eQ).symm

theorem blk_one : blk (1 : Matrix Q3 Q3 ℂ) = 1 := Matrix.submatrix_one_equiv eQ

theorem blk_conjTranspose (M : Matrix Q3 Q3 ℂ) : (blk M)ᴴ = blk Mᴴ :=
  Matrix.conjTranspose_submatrix M eQ eQ

theorem blk_sub (M N : Matrix Q3 Q3 ℂ) : blk (M - N) = blk M - blk N := rfl

variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

open scoped Matrix.Norms.L2Operator in
/-- **The norm of a block**: `‖matOp (blk M) ψ‖ ≤ ‖M‖ ‖ψ‖` for the L2 operator norm of `M`. -/
theorem norm_matOp_blk_le (M : Matrix Q3 Q3 ℂ) (ψ : Reg (Fin 3) Q) :
    ‖matOp (blk M) ψ‖ ≤ ‖M‖ * ‖ψ‖ := by
  apply norm_matOp_le _ (norm_nonneg _)
  intro v
  have h1 : blk M *ᵥ v = (M *ᵥ (v ∘ eQ.symm)) ∘ eQ := Matrix.submatrix_mulVec_equiv M v eQ eQ
  rw [h1]
  have hs1 : ∑ b, ‖((M *ᵥ (v ∘ eQ.symm)) ∘ eQ) b‖ ^ 2 = ∑ q, ‖(M *ᵥ (v ∘ eQ.symm)) q‖ ^ 2 :=
    Fintype.sum_equiv eQ _ _ (fun _ => rfl)
  have hs2 : ∑ c, ‖v c‖ ^ 2 = ∑ q, ‖(v ∘ eQ.symm) q‖ ^ 2 :=
    Fintype.sum_equiv eQ _ _ (fun c => by simp)
  rw [hs1, hs2]
  have h := Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 (v ∘ eQ.symm))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa using h2

omit [CompleteSpace Q] in
theorem matOp_bas' {A : Type*} [Fintype A] [DecidableEq A] (M : Matrix (Cfg A) (Cfg A) ℂ)
    (c : Cfg A) (q : Q) : matOp M (bas c q) = ∑ b, M b c • bas b q := by
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

omit [CompleteSpace Q] in
theorem matOp_blk_bas (M : Matrix Q3 Q3 ℂ) (c : Cfg (Fin 3)) (q : Q) :
    matOp (blk M) (bas c q) = ∑ p : Q3, M p (eQ c) • bas (eQ.symm p) q := by
  rw [matOp_bas', ← Equiv.sum_comp eQ.symm]
  apply Finset.sum_congr rfl
  intro p _
  simp only [blk, Matrix.submatrix_apply, Equiv.apply_symm_apply]

theorem eQ_symm_apply (p : Q3) (i : Fin 3) :
    eQ.symm p i = ![p.1, p.2.1, p.2.2] i := rfl

theorem eQ_symm_update0 (b c0 c1 c2 : Bool) :
    Function.update (eQ.symm (c0, (c1, c2))) 0 b = eQ.symm (b, (c1, c2)) := by
  funext i
  fin_cases i <;> rfl

theorem eQ_symm_update1 (b c0 c1 c2 : Bool) :
    Function.update (eQ.symm (c0, (c1, c2))) 1 b = eQ.symm (c0, (b, c2)) := by
  funext i
  fin_cases i <;> rfl

omit [CompleteSpace Q] in
/-- Agreement on all basis vectors is equality. -/
theorem ext_bas {A : Type*} [Fintype A] [DecidableEq A] {C O : Reg A Q →L[ℂ] Reg A Q}
    (h : ∀ c q, C (bas c q) = O (bas c q)) : C = O := by
  have hA : Agrees (fun _ => True) C O := agrees_of_bas (fun x _ q => h x q)
  ext ψ
  exact congrFun (congrArg WithLp.ofLp (hA ψ (fun x hx => absurd trivial hx))) _

/-- A one-qubit matrix on the flag `f` (wire `0`) of a block is `blk (u ⊗ I)`. -/
theorem condOp_zero_eq_blk (u : Matrix Bool Bool ℂ) :
    condOp (Q := Q) (0 : Fin 3) (fun _ => u) =
      matOp (blk (u ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ))) := by
  apply ext_bas
  intro c q
  rw [condOp_bas, matOp_blk_bas]
  obtain ⟨⟨c0, c1, c2⟩, rfl⟩ : ∃ p, c = eQ.symm p := ⟨eQ c, (eQ.symm_apply_apply c).symm⟩
  simp only [eQ_symm_update0, Equiv.apply_symm_apply, Fintype.sum_prod_type, Fintype.sum_bool,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  cases c0 <;> cases c1 <;> cases c2 <;> simp [eQ_symm_apply]

/-- A one-qubit matrix on the orientation qubit `o` (wire `1`) of a block is `blk (I ⊗ u ⊗ I)`. -/
theorem condOp_one_eq_blk (u : Matrix Bool Bool ℂ) :
    condOp (Q := Q) (1 : Fin 3) (fun _ => u) =
      matOp (blk ((1 : Matrix Bool Bool ℂ) ⊗ₖ (u ⊗ₖ (1 : Matrix Bool Bool ℂ)))) := by
  apply ext_bas
  intro c q
  rw [condOp_bas, matOp_blk_bas]
  obtain ⟨⟨c0, c1, c2⟩, rfl⟩ : ∃ p, c = eQ.symm p := ⟨eQ c, (eQ.symm_apply_apply c).symm⟩
  simp only [eQ_symm_update1, Equiv.apply_symm_apply, Fintype.sum_prod_type, Fintype.sum_bool,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  cases c0 <;> cases c1 <;> cases c2 <;> simp [eQ_symm_apply]

/-- The Toffoli gate `f, o → z` on a block is `blk tofMat`. -/
theorem gateOp_tof_eq_blk :
    gateOp (Q := Q) [((0 : Fin 3), true), (1, true)] 2 pauliX = matOp (blk tofMat) := by
  apply ext_bas
  intro c q
  rw [gateOp_pauliX_bas _ _ (by decide), matOp_blk_bas]
  obtain ⟨⟨c0, c1, c2⟩, rfl⟩ : ∃ p, c = eQ.symm p := ⟨eQ c, (eQ.symm_apply_apply c).symm⟩
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type, Fintype.sum_bool, tofMat, cnotMat,
    Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, eij_apply, xMat]
  have hflip : ∀ b0 b1 b2 : Bool, flipCfg [((0 : Fin 3), true), (1, true)] 2
      (eQ.symm (b0, (b1, b2))) = eQ.symm (b0, (b1, xor b2 (b0 && b1))) := by
    intro b0 b1 b2
    funext i
    fin_cases i <;> cases b0 <;> cases b1 <;> cases b2 <;> rfl
  rw [hflip]
  cases c0 <;> cases c1 <;> cases c2 <;> simp

/-- **A one-qubit operation on a block wire**, chosen by the configuration outside the block, is
the block operation selected by that configuration. -/
theorem condOp_outer {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
    {e : A → W} (he : Function.Injective e) (t : A) (u : Cfg W → Matrix Bool Bool ℂ)
    (hu : ∀ x x' : Cfg W, (∀ w, (∀ a, e a ≠ w) → x w = x' w) → u x = u x') :
    condOp (Q := Q) (e t) u = localOp e he (fun x => condOp t (fun _ => u x)) := by
  ext ψ y
  rw [condOp_apply, localOp_apply, condOp_apply]
  have hu' : u (clearCfg e y) = u (Function.update y (e t) false) := by
    apply hu
    intro w hw
    rw [clearCfg_apply_out e y w hw, Function.update_of_ne (fun h => hw t h.symm)]
  apply Finset.sum_congr rfl
  intro b _
  have hcfg : overwrite e y (Function.update (fun a => y (e a)) t b) =
      Function.update y (e t) b := by
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
  rw [hu', slice_apply, hcfg]

end Block

end

end GateOptimalPrecision
