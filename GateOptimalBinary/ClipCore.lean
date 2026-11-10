import GateOptimalBinary.ClipMoments

/-!
# The core data of the clipped joint representation

The hypotheses `LargeSparsityCore.Core.CoreData` of the clipped regime (`twonorm:eq:joint-moments`,
`twonorm:eq:weights`) and the clipped interface `GateOptimalPrecision.ClippedIface` built from the
binary sparse-access data (`clippedIface`).

Every operator is the conjugate by the frame `W = A F` (`cj`) of a one-qubit operation on the
orientation controlled by the branch, the flag and the edge (`ClipIface`). Its compression by the
boundary `J = U_J ι₀` is the qubit lift of the compression by the sparse boundary `J₀` of an
edgewise operator (`cj_compress`), which is evaluated here:

* `P_±`: `|c₂| Π_±/2` (`edgeOp_P`, `edgeOp_M`);
* `K²`: `2q²(|c₁|² + |c₂|) I` (`edgeOp_KK`), and `P₀ K² P₀`: `2q²|c₁|² I` (`edgeOp_B`);
* `K`: `q E(c₁ + c₂) = (q/μ) E(H_e)` for `|H_e| ≤ μ` (`edgeOp_K`, `clip_compress_K`).

With `ρ = η²/μ²` and `sμ² = ση²` (`LargeSparsityCore.Native.ratio_div`), the row and column sums of
`ClipMoments` give `‖P_± J‖² ≤ β/(2σ) = s_w²`, `‖K P₀ J‖² ≤ 2q²/σ = s_m²` and
`‖K J‖² ≤ 2q²(1 + β)/σ` (`clip_coreData`). The bulk bound `‖R₁(K) P₀‖ ≤ Q₀` holds because off the
success branch the value is `2q c₁` with `β|c₁| ≤ 1`, or `0` (`clip_bulk_le`).

References to the manuscript use its labels.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace GateOptimalBinary

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary GateOptimalPrecision
open NativeSparseBlockEncoding (Data Query)
open NativeSignedFactor (phase norm_phase)
open LargeSparsityCore.CayleyBlocks (Spectral R1)
open scoped InnerProduct Matrix

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-! ### Conjugation by the frame -/

/-- Conjugation by the frame `W = A F`, read on the flat register. -/
abbrev cj (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X)
    (T : Reg (PRf k) R →L[ℂ] Reg (PRf k) R) :
    Anc (k + 3 + 1) (Reg (Fin k) R) →L[ℂ] Anc (k + 3 + 1) (Reg (Fin k) R) :=
  unconj ((WF (R := R) D en μ β x)† ∘L T ∘L WF D en μ β x)

theorem cj_eq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X)
    (T : Reg (PRf k) R →L[ℂ] Reg (PRf k) R) :
    cj D en μ β x T = (WFa (R := R) D en μ β x)† ∘L T ∘L WFa D en μ β x :=
  unconj_WF D en μ β x T

theorem cj_comp (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X)
    (A B : Reg (PRf k) R →L[ℂ] Reg (PRf k) R) :
    cj D en μ β x A ∘L cj D en μ β x B = cj D en μ β x (A ∘L B) := by
  rw [cj_eq, cj_eq, cj_eq]
  exact conj_comp' (WFa_comp_adj (R := R) D en μ β x) A B

theorem cj_one (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X) :
    cj D en μ β x (1 : Reg (PRf k) R →L[ℂ] Reg (PRf k) R) = 1 := by
  rw [cj_eq]
  exact conj_one' (WFa_adj_comp (R := R) D en μ β x)

theorem cj_R1 (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X)
    (A : Reg (PRf k) R →L[ℂ] Reg (PRf k) R) :
    R1 (cj D en μ β x A) = cj D en μ β x (R1 A) := by
  rw [cj_eq, cj_eq]
  exact R1_conj' (WFa_adj_comp (R := R) D en μ β x) A

theorem cj_bulk (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X)
    (A B : Reg (PRf k) R →L[ℂ] Reg (PRf k) R) :
    LargeSparsityCore.CayleyBlocks.bulk (cj D en μ β x A) (cj D en μ β x B) =
      cj D en μ β x (LargeSparsityCore.CayleyBlocks.bulk A B) := by
  rw [cj_eq, cj_eq, cj_eq]
  exact bulk_conj' (WFa_adj_comp (R := R) D en μ β x) A B

theorem norm_cj_le (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X)
    (A : Reg (PRf k) R →L[ℂ] Reg (PRf k) R) : ‖cj D en μ β x A‖ ≤ ‖A‖ := by
  rw [cj_eq]
  exact norm_conj_le' _ A (WFa_adj_comp (R := R) D en μ β x)

/-! ### The compressions of the joint operators -/

/-- The compression by `J₀` of an edgewise operator. -/
abbrev Cedge (D : Data X n (Cfg (VW b)) s) (x : X)
    (G : n × n → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  (FixedLocatorConjugation.fixedBoundary D.slot)† ∘L
    ((FixedLocatorConjugation.locator D x)† ∘L OrientedEdgeCayley.lift G ∘L
      FixedLocatorConjugation.locator D x) ∘L FixedLocatorConjugation.fixedBoundary D.slot

/-- The edgewise operator of a located operation (`clip_compress`). -/
abbrev edgeOp (D : Data X n (Cfg (VW b)) s) (μ β : ℝ) (x : X)
    (uE : Bool → Bool → n × n → Matrix Bool Bool ℂ) (e : n × n) : Matrix Bool Bool ℂ :=
  (2⁻¹ : ℂ) • (uE false false e + ((1 - ‖cl2 D μ β x e‖ : ℝ) : ℂ) • uE true false e +
    ((‖cl2 D μ β x e‖ : ℝ) : ℂ) • (piP (cl2 D μ β x e) * uE true true e * piP (cl2 D μ β x e) +
      piM (cl2 D μ β x e) * uE true true e * piM (cl2 D μ β x e)))

/-- **The compression of a located operation** by the joint boundary, with the edgewise operator
evaluated. -/
theorem cj_compress (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (sb : ℕ) (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    (μ β : ℝ) (uE : Bool → Bool → n × n → Matrix Bool Bool ℂ) (G : n × n → Matrix Bool Bool ℂ)
    (hG : ∀ e, edgeOp D μ β x uE e = G e) :
    (clJ (R := R) k sb hsb)† ∘L
        cj D en μ β x (condOp (locF k 1) (fun y => uE (y (gW k)) (y (locF k 0)) (edgeC en y))) ∘L
        clJ k sb hsb =
      qlift (R := R) en (Cedge D x (fun e => qop (G e))) := by
  have h := clip_compress (R := R) D en x sb hsb hs hrange μ β uE
  have hf : (fun e => qop (G e)) = (fun e => qop (edgeOp D μ β x uE e)) :=
    funext fun e => by rw [hG e]
  rw [hf]
  exact h

/-- The norm of the compression of a located operation whose edgewise operators are bounded
quadratic forms. -/
theorem norm_cj_compress_le (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (sb : ℕ) (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    (μ β : ℝ) (uE : Bool → Bool → n × n → Matrix Bool Bool ℂ) (G : n × n → Matrix Bool Bool ℂ)
    (hG : ∀ e, edgeOp D μ β x uE e = G e) (hGs : ∀ e, (G e)ᴴ = G e) (a : n × n → ℝ)
    (ha : ∀ e, 0 ≤ a e)
    (hGa : ∀ e y, 0 ≤ RCLike.re (inner ℂ (qop (G e) y) y) ∧
      RCLike.re (inner ℂ (qop (G e) y) y) ≤ a e * ‖y‖ ^ 2)
    {W : ℝ} (hW : 0 ≤ W) (hR : ∀ i, ∑ j, a (i, j) ≤ W) (hC : ∀ j, ∑ i, a (i, j) ≤ W) :
    ‖(clJ (R := R) k sb hsb)† ∘L
        cj D en μ β x (condOp (locF k 1) (fun y => uE (y (gW k)) (y (locF k 0)) (edgeC en y))) ∘L
        clJ k sb hsb‖ ≤ W / s := by
  rw [cj_compress D en x sb hsb hs hrange μ β uE G hG]
  exact (norm_qlift_le en _).trans
    (norm_edge_compress_le D x _ (fun e => qop_isSelfAdjoint (hGs e)) a ha hGa hW hR hC)

/-! ### The edgewise operators -/

/-- The success projection `[g = 1][f = 1] Π_+` of an edge. -/
abbrev uP (D : Data X n (Cfg (VW b)) s) (μ β : ℝ) (x : X) (g f : Bool) (e : n × n) :
    Matrix Bool Bool ℂ :=
  if g && f then piP (cl2 D μ β x e) else 0

/-- The success projection `[g = 1][f = 1] Π_-` of an edge. -/
abbrev uM (D : Data X n (Cfg (VW b)) s) (μ β : ℝ) (x : X) (g f : Bool) (e : n × n) :
    Matrix Bool Bool ℂ :=
  if g && f then piM (cl2 D μ β x e) else 0

/-- The generator `E(y)` of an edge. -/
abbrev uK (D : Data X n (Cfg (VW b)) s) (μ β q : ℝ) (x : X) (g f : Bool) (e : n × n) :
    Matrix Bool Bool ℂ :=
  eMat (yC q g f (cl1 D μ β x e) (cl2 D μ β x e))

/-- The square of the generator of an edge. -/
abbrev uKK (D : Data X n (Cfg (VW b)) s) (μ β q : ℝ) (x : X) (g f : Bool) (e : n × n) :
    Matrix Bool Bool ℂ :=
  uK D μ β q x g f e * uK D μ β q x g f e

/-- The bulk part `P₀ E(y)² P₀` of the square of the generator of an edge. -/
abbrev uB (D : Data X n (Cfg (VW b)) s) (μ β q : ℝ) (x : X) (g f : Bool) (e : n × n) :
    Matrix Bool Bool ℂ :=
  (1 - uP D μ β x g f e - uM D μ β x g f e) *
    (uK D μ β q x g f e * (uK D μ β q x g f e * (1 - uP D μ β x g f e - uM D μ β x g f e)))

theorem pinch_smul (c r : ℂ) (Y : Matrix Bool Bool ℂ) :
    piP c * (r • Y) * piP c + piM c * (r • Y) * piM c =
      r • (piP c * Y * piP c + piM c * Y * piM c) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add]

theorem pinch_smul_one (c r : ℂ) :
    piP c * (r • (1 : Matrix Bool Bool ℂ)) * piP c + piM c * (r • 1) * piM c = r • 1 := by
  rw [pinch_smul, pinch_one]

theorem eMat_add (z w : ℂ) : eMat (z + w) = eMat z + eMat w := by
  ext i j
  cases i <;> cases j <;> simp [eMat, map_add]

theorem abs_mul_abs_sq (q : ℝ) : (((|2| * |q| : ℝ)) : ℂ) ^ 2 = ((4 * q ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.ofReal_pow, ← abs_mul, sq_abs]
  congr 1
  ring

theorem edgeOp_P (D : Data X n (Cfg (VW b)) s) (μ β : ℝ) (x : X) (e : n × n) :
    edgeOp D μ β x (uP D μ β x) e = (((‖cl2 D μ β x e‖ / 2 : ℝ)) : ℂ) • piP (cl2 D μ β x e) := by
  simp only [edgeOp, uP, Bool.and_false, Bool.and_self, Bool.false_eq_true,
    if_false, if_true, smul_zero, add_zero, zero_add, pinch_piP, smul_smul]
  congr 1
  push_cast
  ring

theorem edgeOp_M (D : Data X n (Cfg (VW b)) s) (μ β : ℝ) (x : X) (e : n × n) :
    edgeOp D μ β x (uM D μ β x) e = (((‖cl2 D μ β x e‖ / 2 : ℝ)) : ℂ) • piM (cl2 D μ β x e) := by
  simp only [edgeOp, uM, Bool.and_false, Bool.and_self, Bool.false_eq_true,
    if_false, if_true, smul_zero, add_zero, zero_add, pinch_piM, smul_smul]
  congr 1
  push_cast
  ring

theorem edgeOp_KK (D : Data X n (Cfg (VW b)) s) (μ β q : ℝ) (x : X) (e : n × n) :
    edgeOp D μ β x (uKK D μ β q x) e =
      (((2 * q ^ 2 * (‖cl1 D μ β x e‖ ^ 2 + ‖cl2 D μ β x e‖) : ℝ)) : ℂ) • 1 := by
  simp only [edgeOp, uKK, uK, yC, Bool.false_eq_true, if_false, if_true, eMat_mul_self, eMat_zero,
    Matrix.zero_mul, smul_zero, add_zero, pinch_smul_one, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, norm_phase, mul_one]
  rw [Complex.ofReal_mul, mul_pow, abs_mul_abs_sq, smul_smul, ← add_smul, smul_smul]
  congr 1
  push_cast
  ring

theorem edgeOp_B (D : Data X n (Cfg (VW b)) s) (μ β q : ℝ) (x : X) (e : n × n) :
    edgeOp D μ β x (uB D μ β q x) e =
      (((2 * q ^ 2 * ‖cl1 D μ β x e‖ ^ 2 : ℝ)) : ℂ) • 1 := by
  have h0 : (1 : Matrix Bool Bool ℂ) - piP (cl2 D μ β x e) - piM (cl2 D μ β x e) = 0 := by
    rw [sub_sub, piP_add_piM, sub_self]
  simp only [edgeOp, uB, uP, uM, uK, yC, Bool.and_false, Bool.and_self, Bool.false_eq_true,
    if_false, if_true, sub_zero, h0, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one,
    Matrix.one_mul, eMat_zero, eMat_mul_self, smul_zero, add_zero, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  rw [Complex.ofReal_mul, mul_pow, abs_mul_abs_sq, smul_smul]
  congr 1
  push_cast
  ring

theorem edgeOp_K (D : Data X n (Cfg (VW b)) s) (μ β q : ℝ) (x : X) (e : n × n) :
    edgeOp D μ β x (uK D μ β q x) e =
      ((q : ℝ) : ℂ) • eMat (cl1 D μ β x e + cl2 D μ β x e) := by
  simp only [edgeOp, uK, yC, Bool.false_eq_true, if_false, if_true, eMat_zero, smul_zero,
    add_zero, eMat_real_mul, pinch_smul, pinch_eMat_phase]
  rw [eMat_add, eMat_eq (cl2 D μ β x e), smul_comm ((‖cl2 D μ β x e‖ : ℝ) : ℂ) ((2 * q : ℝ) : ℂ),
    ← smul_add, smul_smul]
  congr 1
  push_cast
  ring

/-! ### The located operators as one-qubit operations -/

theorem LK_eq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X) :
    LK (R := R) D en μ β q x =
      condOp (locF k 1) (fun y => uK D μ β q x (y (gW k)) (y (locF k 0)) (edgeC en y)) := rfl

theorem LP_eq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X) :
    LP (R := R) D en μ β x =
      condOp (locF k 1) (fun y => uP D μ β x (y (gW k)) (y (locF k 0)) (edgeC en y)) := rfl

theorem LM_eq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X) :
    LM (R := R) D en μ β x =
      condOp (locF k 1) (fun y => uM D μ β x (y (gW k)) (y (locF k 0)) (edgeC en y)) := rfl

theorem LKK_eq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X) :
    LK (R := R) D en μ β q x ∘L LK D en μ β q x =
      condOp (locF k 1) (fun y => uKK D μ β q x (y (gW k)) (y (locF k 0)) (edgeC en y)) := by
  rw [LK_eq]
  exact condOp_comp' _ _ _

theorem Lbulk_eq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X) :
    LargeSparsityCore.CayleyBlocks.bulk (LP (R := R) D en μ β x) (LM D en μ β x) =
      condOp (locF k 1) (fun y => 1 - uP D μ β x (y (gW k)) (y (locF k 0)) (edgeC en y) -
        uM D μ β x (y (gW k)) (y (locF k 0)) (edgeC en y)) := by
  rw [LargeSparsityCore.CayleyBlocks.bulk, LP_eq, LM_eq, ← condOp_one' (Q := R) (locF k 1),
    condOp_sub, condOp_sub]

theorem LB_eq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X) :
    LargeSparsityCore.CayleyBlocks.bulk (LP (R := R) D en μ β x) (LM D en μ β x) ∘L
        (LK D en μ β q x ∘L (LK D en μ β q x ∘L
          LargeSparsityCore.CayleyBlocks.bulk (LP (R := R) D en μ β x) (LM D en μ β x))) =
      condOp (locF k 1) (fun y => uB D μ β q x (y (gW k)) (y (locF k 0)) (edgeC en y)) := by
  rw [Lbulk_eq, LK_eq, condOp_comp', condOp_comp', condOp_comp']

theorem LR1_bulk_eq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X) :
    R1 (LK (R := R) D en μ β q x) ∘L
        LargeSparsityCore.CayleyBlocks.bulk (LP (R := R) D en μ β x) (LM D en μ β x) =
      condOp (locF k 1) (fun y =>
        ((2⁻¹ : ℂ) • (1 + Complex.I • uK D μ β q x (y (gW k)) (y (locF k 0)) (edgeC en y))) *
          (1 - uP D μ β x (y (gW k)) (y (locF k 0)) (edgeC en y) -
            uM D μ β x (y (gW k)) (y (locF k 0)) (edgeC en y))) := by
  rw [Lbulk_eq, R1, LK_eq, condOp_smul, ← condOp_one' (Q := R) (locF k 1), condOp_add,
    condOp_smul, condOp_comp']

theorem clK_eq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X) :
    clK (R := R) D en μ β q x = cj D en μ β x (LK D en μ β q x) := rfl

theorem clPp_eq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X) :
    clPp (R := R) D en μ β x = cj D en μ β x (LP D en μ β x) := rfl

theorem clPm_eq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X) :
    clPm (R := R) D en μ β x = cj D en μ β x (LM D en μ β x) := rfl

/-! ### The bulk bound -/

theorem frob2_R1 (z : ℂ) :
    frob2 ((2⁻¹ : ℂ) • (1 + Complex.I • eMat z)) = Real.sqrt ((1 + ‖z‖ ^ 2) / 2) := by
  unfold frob2
  congr 1
  simp [eMat, Matrix.one_apply, Complex.norm_I]
  ring

theorem frob2_R1_bulk_le (q : ℝ) {Q : ℝ} (hQ : 1 ≤ Q) (g f : Bool) (c₁ c₂ : ℂ)
    (hy : (g && f) = false → ‖yC q g f c₁ c₂‖ ≤ Q) :
    frob2 (((2⁻¹ : ℂ) • (1 + Complex.I • eMat (yC q g f c₁ c₂))) *
      (1 - (if g && f then piP c₂ else 0) - (if g && f then piM c₂ else 0))) ≤ Q := by
  cases hgf : (g && f)
  · simp only [Bool.false_eq_true, if_false, sub_zero, Matrix.mul_one]
    rw [frob2_R1]
    have h1 := hy hgf
    have h0 := norm_nonneg (yC q g f c₁ c₂)
    have h2 : (1 + ‖yC q g f c₁ c₂‖ ^ 2) / 2 ≤ Q ^ 2 := by nlinarith
    calc Real.sqrt ((1 + ‖yC q g f c₁ c₂‖ ^ 2) / 2) ≤ Real.sqrt (Q ^ 2) := Real.sqrt_le_sqrt h2
      _ = Q := Real.sqrt_sq (by linarith)
  · simp only [if_true, sub_sub, piP_add_piM, sub_self, Matrix.mul_zero]
    simp only [frob2, Matrix.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Finset.sum_const_zero, Real.sqrt_zero]
    linarith

/-- **The bulk bound** `‖R₁(K) P₀‖ ≤ Q₀`: off the success branch the value is `2q c₁` with
`β|c₁| ≤ 1`, or `0`. -/
theorem clip_bulk_le (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) {μ β q Q : ℝ}
    (x : X) (hQ : 1 ≤ Q) (hμ : 0 < μ) (hβ : 0 < β) (hq : 0 ≤ q) (hQq : 2 * q / β ≤ Q) :
    ‖R1 (clK (R := R) D en μ β q x) ∘L
        LargeSparsityCore.CayleyBlocks.bulk (clPp (R := R) D en μ β x) (clPm D en μ β x)‖ ≤ Q := by
  rw [clK_eq, clPp_eq, clPm_eq, cj_R1, cj_bulk, cj_comp]
  refine (norm_cj_le D en μ β x _).trans ?_
  rw [LR1_bulk_eq]
  apply norm_condOp_le _ _ (by linarith)
  intro y
  apply frob2_R1_bulk_le q hQ
  intro hgf
  cases hg : y (gW k)
  · simp only [yC, Bool.false_eq_true, if_false]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hc : β * ‖cl1 D μ β x (edgeC en y)‖ ≤ 1 :=
      LargeSparsityCore.Native.mul_norm_cclip_le hμ hβ.le _
    have h2 : 2 * q * ‖cl1 D μ β x (edgeC en y)‖ ≤ 2 * q / β := by
      rw [le_div_iff₀ hβ]
      nlinarith [norm_nonneg (cl1 D μ β x (edgeC en y))]
    linarith
  · have hf : y (locF k 0) = false := by simpa [hg] using hgf
    simp only [yC, hf, if_true, Bool.false_eq_true, if_false, norm_zero]
    linarith

/-! ### The moments -/

/-- `‖A J‖² = ‖J† A† A J‖`. -/
theorem norm_mul_self_comp {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : F →L[ℂ] F) (J : E →L[ℂ] F) :
    ‖A ∘L J‖ * ‖A ∘L J‖ = ‖J† ∘L (A† ∘L A) ∘L J‖ := by
  rw [← norm_adjoint_comp_self, adjoint_comp]
  simp only [comp_assoc]

theorem smul_proj_conjTranspose (r : ℝ) {P : Matrix Bool Bool ℂ} (hP : Pᴴ = P) :
    ((r : ℂ) • P)ᴴ = (r : ℂ) • P := by
  rw [Matrix.conjTranspose_smul, hP, Complex.star_def, Complex.conj_ofReal]

/-- `‖J† P₊ J‖ ≤ βρ/(2s)`. -/
theorem clip_P_le (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (sb : ℕ) (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {μ η β : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ‖(clJ (R := R) k sb hsb)† ∘L cj D en μ β x (LP D en μ β x) ∘L clJ k sb hsb‖ ≤
      β / 2 * (η ^ 2 / μ ^ 2) / s := by
  rw [LP_eq]
  refine norm_cj_compress_le D en x sb hsb hs hrange μ β (uP D μ β x) _ (edgeOp_P D μ β x)
    (fun e => smul_proj_conjTranspose _ (piP_conjTranspose _)) (fun e => ‖cl2 D μ β x e‖ / 2)
    (fun e => by positivity)
    (fun e y => quad_smul_proj (by positivity) (piP_conjTranspose _) (piP_mul_piP _) y)
    (by positivity) (fun i => ?_) (fun j => ?_)
  · have h := cl2_row_le D hμ hβ x hrow i
    rw [← Finset.sum_div]
    linarith
  · have h := cl2_col_le D hμ hβ x hcol j
    rw [← Finset.sum_div]
    linarith

/-- `‖J† P₋ J‖ ≤ βρ/(2s)`. -/
theorem clip_M_le (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (sb : ℕ) (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {μ η β : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ‖(clJ (R := R) k sb hsb)† ∘L cj D en μ β x (LM D en μ β x) ∘L clJ k sb hsb‖ ≤
      β / 2 * (η ^ 2 / μ ^ 2) / s := by
  rw [LM_eq]
  refine norm_cj_compress_le D en x sb hsb hs hrange μ β (uM D μ β x) _ (edgeOp_M D μ β x)
    (fun e => smul_proj_conjTranspose _ (piM_conjTranspose _)) (fun e => ‖cl2 D μ β x e‖ / 2)
    (fun e => by positivity)
    (fun e y => quad_smul_proj (by positivity) (piM_conjTranspose _) (piM_mul_piM _) y)
    (by positivity) (fun i => ?_) (fun j => ?_)
  · have h := cl2_row_le D hμ hβ x hrow i
    rw [← Finset.sum_div]
    linarith
  · have h := cl2_col_le D hμ hβ x hcol j
    rw [← Finset.sum_div]
    linarith

theorem smul_one_conjTranspose (r : ℝ) :
    ((r : ℂ) • (1 : Matrix Bool Bool ℂ))ᴴ = (r : ℂ) • 1 :=
  smul_proj_conjTranspose r Matrix.conjTranspose_one

/-- `‖J† K² J‖ ≤ 2q²(1 + β)ρ/s`. -/
theorem clip_KK_le (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (sb : ℕ) (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {μ η β : ℝ} (q : ℝ) (hμ : 0 < μ) (hβ : 0 ≤ β)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ‖(clJ (R := R) k sb hsb)† ∘L cj D en μ β x (LK D en μ β q x ∘L LK D en μ β q x) ∘L
        clJ k sb hsb‖ ≤ 2 * q ^ 2 * (1 + β) * (η ^ 2 / μ ^ 2) / s := by
  rw [LKK_eq]
  have hq2 : 0 ≤ 2 * q ^ 2 := by positivity
  refine norm_cj_compress_le D en x sb hsb hs hrange μ β (uKK D μ β q x) _ (edgeOp_KK D μ β q x)
    (fun e => smul_one_conjTranspose _)
    (fun e => 2 * q ^ 2 * (‖cl1 D μ β x e‖ ^ 2 + ‖cl2 D μ β x e‖)) (fun e => by positivity)
    (fun e y => quad_smul_one (by positivity) y) (by positivity) (fun i => ?_) (fun j => ?_)
  · have h1 := cl1_row_le D hμ hβ x hrow i
    have h2 := cl2_row_le D hμ hβ x hrow i
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    calc 2 * q ^ 2 * (∑ j, ‖cl1 D μ β x (i, j)‖ ^ 2 + ∑ j, ‖cl2 D μ β x (i, j)‖) ≤
          2 * q ^ 2 * (η ^ 2 / μ ^ 2 + β * (η ^ 2 / μ ^ 2)) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) hq2
      _ = 2 * q ^ 2 * (1 + β) * (η ^ 2 / μ ^ 2) := by ring
  · have h1 := cl1_col_le D hμ hβ x hcol j
    have h2 := cl2_col_le D hμ hβ x hcol j
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    calc 2 * q ^ 2 * (∑ i, ‖cl1 D μ β x (i, j)‖ ^ 2 + ∑ i, ‖cl2 D μ β x (i, j)‖) ≤
          2 * q ^ 2 * (η ^ 2 / μ ^ 2 + β * (η ^ 2 / μ ^ 2)) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) hq2
      _ = 2 * q ^ 2 * (1 + β) * (η ^ 2 / μ ^ 2) := by ring

/-- `‖J† P₀ K² P₀ J‖ ≤ 2q²ρ/s`. -/
theorem clip_B_le (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (sb : ℕ) (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {μ η β : ℝ} (q : ℝ) (hμ : 0 < μ) (hβ : 0 ≤ β)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ‖(clJ (R := R) k sb hsb)† ∘L cj D en μ β x
        (LargeSparsityCore.CayleyBlocks.bulk (LP (R := R) D en μ β x) (LM D en μ β x) ∘L
          (LK D en μ β q x ∘L (LK D en μ β q x ∘L
            LargeSparsityCore.CayleyBlocks.bulk (LP (R := R) D en μ β x) (LM D en μ β x)))) ∘L
        clJ k sb hsb‖ ≤ 2 * q ^ 2 * (η ^ 2 / μ ^ 2) / s := by
  rw [LB_eq]
  have hq2 : 0 ≤ 2 * q ^ 2 := by positivity
  refine norm_cj_compress_le D en x sb hsb hs hrange μ β (uB D μ β q x) _ (edgeOp_B D μ β q x)
    (fun e => smul_one_conjTranspose _)
    (fun e => 2 * q ^ 2 * ‖cl1 D μ β x e‖ ^ 2) (fun e => by positivity)
    (fun e y => quad_smul_one (by positivity) y) (by positivity) (fun i => ?_) (fun j => ?_)
  · rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (cl1_row_le D hμ hβ x hrow i) hq2
  · rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (cl1_col_le D hμ hβ x hcol j) hq2

/-! ### The core data -/

theorem clJ_isometry (sb : ℕ) (hsb : sb ≤ k) :
    (clJ (R := R) k sb hsb)† ∘L clJ k sb hsb = 1 := by
  have hU := (UJop_isUnitary (R := R) (clUJg k sb hsb) (clUJg_ok (k := k) sb hsb)).1
  rw [star_eq_adjoint, mul_def] at hU
  calc (clJ (R := R) k sb hsb)† ∘L clJ k sb hsb =
        (iota0 (a := k + 3 + 1) (P := Reg (Fin k) R))† ∘L
          ((UJop (R := R) (clUJg k sb hsb))† ∘L UJop (R := R) (clUJg k sb hsb)) ∘L
            iota0 (a := k + 3 + 1) (P := Reg (Fin k) R) := by
        rw [clJ, adjoint_comp]
        simp only [comp_assoc]
    _ = 1 := by rw [hU, LargeSparsityCore.CayleyBlocks.one_comp, iota0_isometry]

/-- `‖K J‖² ≤ 2q²(1 + β)ρ/s`. -/
theorem clip_second_sq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (sb : ℕ) (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {μ η β q : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ‖clK (R := R) D en μ β q x ∘L clJ k sb hsb‖ ^ 2 ≤
      2 * q ^ 2 * (1 + β) * (η ^ 2 / μ ^ 2) / s := by
  have hsp := clip_spectral (R := R) D en μ β q x
  rw [sq, norm_mul_self_comp, hsp.self.adjoint_eq, clK_eq, cj_comp]
  exact clip_KK_le D en x sb hsb hs hrange q hμ hβ hrow hcol

/-- `‖P₊ J‖² ≤ βρ/(2s)`. -/
theorem clip_isoP_sq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (sb : ℕ) (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {μ η β : ℝ} (q : ℝ) (hμ : 0 < μ) (hβ : 0 ≤ β)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ‖clPp (R := R) D en μ β x ∘L clJ k sb hsb‖ ^ 2 ≤ β / 2 * (η ^ 2 / μ ^ 2) / s := by
  have hsp := clip_spectral (R := R) D en μ β q x
  rw [sq, norm_mul_self_comp, hsp.pp_adj.adjoint_eq, hsp.pp_idem, clPp_eq]
  exact clip_P_le D en x sb hsb hs hrange hμ hβ hrow hcol

/-- `‖P₋ J‖² ≤ βρ/(2s)`. -/
theorem clip_isoM_sq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (sb : ℕ) (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {μ η β : ℝ} (q : ℝ) (hμ : 0 < μ) (hβ : 0 ≤ β)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ‖clPm (R := R) D en μ β x ∘L clJ k sb hsb‖ ^ 2 ≤ β / 2 * (η ^ 2 / μ ^ 2) / s := by
  have hsp := clip_spectral (R := R) D en μ β q x
  rw [sq, norm_mul_self_comp, hsp.pm_adj.adjoint_eq, hsp.pm_idem, clPm_eq]
  exact clip_M_le D en x sb hsb hs hrange hμ hβ hrow hcol

/-- `‖K P₀ J‖² ≤ 2q²ρ/s`. -/
theorem clip_moment_sq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (sb : ℕ) (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {μ η β q : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ‖clK (R := R) D en μ β q x ∘L
        LargeSparsityCore.CayleyBlocks.bulk (clPp (R := R) D en μ β x) (clPm D en μ β x) ∘L
          clJ k sb hsb‖ ^ 2 ≤ 2 * q ^ 2 * (η ^ 2 / μ ^ 2) / s := by
  have hsp := clip_spectral (R := R) D en μ β q x
  rw [sq, ← comp_assoc, norm_mul_self_comp, adjoint_comp (clK (R := R) D en μ β q x),
    hsp.self.adjoint_eq, hsp.bulk_adj.adjoint_eq, clK_eq, clPp_eq, clPm_eq, cj_bulk,
    comp_assoc, cj_comp, cj_comp,
    ← comp_assoc (cj (R := R) D en μ β x _) (cj (R := R) D en μ β x _), cj_comp,
    comp_assoc (LargeSparsityCore.CayleyBlocks.bulk (LP (R := R) D en μ β x) (LM D en μ β x))]
  exact clip_B_le D en x sb hsb hs hrange q hμ hβ hrow hcol

theorem le_of_sq_le_sq' {a c : ℝ} (hc : 0 ≤ c) (h : a ^ 2 ≤ c ^ 2) (ha : 0 ≤ a) : a ≤ c :=
  (mul_self_le_mul_self_iff ha hc).mpr (by rw [← sq, ← sq]; exact h)

/-- **The clipped joint representation satisfies the hypotheses of the abstract core**
(`twonorm:eq:joint-moments`, `twonorm:eq:weights`) with the moment parameter `σ` (`sμ² = ση²`) and
`β = h`. -/
theorem clip_coreData (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (sb : ℕ) (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {σ θ ε μ η : ℝ} (Rg : LargeSparsityCore.Parameters.Regime σ θ ε) (hμ : 0 < μ)
    (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    LargeSparsityCore.Core.CoreData σ θ ε
      (clK (R := R) D en μ (LargeSparsityCore.Parameters.hval θ ε)
        (LargeSparsityCore.Parameters.qval σ θ ε) x)
      (clD (R := R) D en μ (LargeSparsityCore.Parameters.hval θ ε)
        (LargeSparsityCore.Parameters.qval σ θ ε) x)
      (clPp (R := R) D en μ (LargeSparsityCore.Parameters.hval θ ε) x)
      (clPm (R := R) D en μ (LargeSparsityCore.Parameters.hval θ ε) x)
      (clJ (R := R) k sb hsb) := by
  have hh : 0 < LargeSparsityCore.Parameters.hval θ ε := Rg.h_pos
  have hq : 0 < LargeSparsityCore.Parameters.qval σ θ ε := Rg.q_pos
  have hσ0 : 0 < σ := by linarith [Rg.one_le_s]
  have hrat := fun c : ℝ => LargeSparsityCore.Native.ratio_div D.slots_pos hμ hσ c
  have hJ := clJ_isometry (R := R) (k := k) sb hsb
  have hKK := clip_second_sq (R := R) D en x sb hsb hs hrange hμ hh.le
    (q := LargeSparsityCore.Parameters.qval σ θ ε) hrow hcol
  rw [hrat] at hKK
  have hKn : ‖clK (R := R) D en μ (LargeSparsityCore.Parameters.hval θ ε)
      (LargeSparsityCore.Parameters.qval σ θ ε) x ∘L clJ k sb hsb‖ ≤ 1 :=
    le_of_sq_le_sq' zero_le_one (hKK.trans (by rw [one_pow]; exact Rg.second_le_one))
      (by positivity)
  refine ⟨clip_spectral D en μ _ _ x, clD_isometry D en μ _ _ x, hJ, ?_, ?_, ?_, ?_, hKK, ?_⟩
  · -- the bulk bound
    have hQ := Rg.Q0_ge
    exact clip_bulk_le D en x (by linarith) hμ hh hq.le le_rfl
  · -- `‖P₊ J‖ ≤ s_w`
    refine le_of_sq_le_sq' (LargeSparsityCore.Parameters.sw_nonneg σ θ ε) ?_ (by positivity)
    refine (clip_isoP_sq D en x sb hsb hs hrange (LargeSparsityCore.Parameters.qval σ θ ε) hμ
      hh.le hrow hcol).trans (le_of_eq ?_)
    rw [Rg.sw_sq, hrat]
    ring
  · -- `‖P₋ J‖ ≤ s_w`
    refine le_of_sq_le_sq' (LargeSparsityCore.Parameters.sw_nonneg σ θ ε) ?_ (by positivity)
    refine (clip_isoM_sq D en x sb hsb hs hrange (LargeSparsityCore.Parameters.qval σ θ ε) hμ
      hh.le hrow hcol).trans (le_of_eq ?_)
    rw [Rg.sw_sq, hrat]
    ring
  · -- `‖K P₀ J‖ ≤ s_m`
    refine le_of_sq_le_sq' (LargeSparsityCore.Parameters.sm_nonneg σ θ ε) ?_ (by positivity)
    refine (clip_moment_sq D en x sb hsb hs hrange hμ hh.le hrow hcol).trans (le_of_eq ?_)
    rw [LargeSparsityCore.Parameters.sm, Real.sq_sqrt (by positivity), hrat]
  · -- the boundary bound
    have hJa : ‖(clJ (R := R) k sb hsb)†‖ ≤ 1 := by
      rw [LinearIsometryEquiv.norm_map]
      exact LargeSparsityCore.Core.norm_le_one_of_isometry hJ
    refine (opNorm_comp_le _ _).trans ?_
    calc ‖(clJ (R := R) k sb hsb)†‖ * ‖clK (R := R) D en μ (LargeSparsityCore.Parameters.hval θ ε)
          (LargeSparsityCore.Parameters.qval σ θ ε) x ∘L clJ k sb hsb‖ ≤ 1 * 1 :=
          mul_le_mul hJa hKn (by positivity) zero_le_one
      _ = 1 := one_mul 1

/-! ### The compression -/

theorem qop_eMat (z : ℂ) : qop (eMat z) = ExactEdgeCayley.generator z := by
  apply ContinuousLinearMap.ext
  intro v
  ext b
  change (Matrix.toEuclideanCLM (𝕜 := ℂ) (eMat z) v).ofLp b = (ExactEdgeCayley.generator z v) b
  rw [Matrix.ofLp_toEuclideanCLM]
  cases b <;> simp [Matrix.mulVec, dotProduct, eMat]

/-- **The compression of the private Hermitian operator** (`twonorm:eq:joint-moments`):
`J† K J = H/α` with `α = sμ/q`, for a Hermitian matrix with entries of modulus at most `μ`
(`c₁ + c₂ = H_e/μ`). -/
theorem clip_compress_K (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (sb : ℕ) (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {μ β q : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β) (hq : 0 < q) (hH : (D.matrix x).IsHermitian)
    (hent : ∀ i j, ‖D.matrix x i j‖ ≤ μ) :
    (clJ (R := R) k sb hsb)† ∘L clK (R := R) D en μ β q x ∘L clJ k sb hsb =
      ((((s : ℝ) * μ / q : ℝ)) : ℂ)⁻¹ • sysH (R := R) D en x := by
  set M : Matrix n n ℂ := fun i j => D.matrix x i j * (μ : ℂ)⁻¹ with hM
  have hc : ∀ e : n × n, cl1 D μ β x e + cl2 D μ β x e = M e.1 e.2 := by
    intro e
    rw [cl1, cl2, LargeSparsityCore.Native.cclip_add_ccorr hμ hβ (hent e.1 e.2), div_eq_mul_inv]
  have hG : ∀ e, edgeOp D μ β x (uK D μ β q x) e = ((q : ℝ) : ℂ) • eMat (M e.1 e.2) := by
    intro e
    rw [edgeOp_K, hc]
  rw [clK_eq, LK_eq, cj_compress D en x sb hsb hs hrange μ β (uK D μ β q x) _ hG]
  have hL : (fun e : n × n => qop (((q : ℝ) : ℂ) • eMat (M e.1 e.2))) =
      fun e => ((q : ℝ) : ℂ) • ExactEdgeCayley.generator (M e.1 e.2) := by
    funext e
    rw [qop_smul, qop_eMat]
  have hMH : M.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [hM, star_mul', hH.apply i j, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hrow : ∀ i j, M i j ≠ 0 → SparseSlotStates.selected (D.rowloc x) i j := by
    intro i j h
    apply D.row_covers x i j
    intro h0
    exact h (by simp [hM, h0])
  have hcol : ∀ i j, M i j ≠ 0 → SparseSlotStates.selected (D.colloc x) j i := by
    intro i j h
    apply D.column_covers x i j
    intro h0
    exact h (by simp [hM, h0])
  have hcomp := SparseEdgeMoments.generator_compression D.slots_pos M hMH (D.rowloc x)
    (D.colloc x) hrow hcol
  rw [SparseEdgeMoments.generator, smul_comp, comp_smul] at hcomp
  have hs0 : (Real.sqrt (s : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast D.slots_pos)
    exact_mod_cast this.ne'
  have hr : (Real.sqrt (s : ℝ) : ℂ) * (Real.sqrt (s : ℝ) : ℂ) = (s : ℂ) := by
    have h : Real.sqrt (s : ℝ) * Real.sqrt (s : ℝ) = (s : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg s)
    exact_mod_cast h
  have hX : (SparseEdgeMoments.boundary (D.rowloc x) (D.colloc x))† ∘L
      SparseEdgeMoments.entryGenerator M ∘L SparseEdgeMoments.boundary (D.rowloc x) (D.colloc x) =
      (s : ℂ)⁻¹ • SparseStateOverlap.matrixOperator M := by
    calc (SparseEdgeMoments.boundary (D.rowloc x) (D.colloc x))† ∘L
          SparseEdgeMoments.entryGenerator M ∘L SparseEdgeMoments.boundary (D.rowloc x) (D.colloc x)
        = (Real.sqrt (s : ℝ) : ℂ)⁻¹ • ((Real.sqrt (s : ℝ) : ℂ) •
            ((SparseEdgeMoments.boundary (D.rowloc x) (D.colloc x))† ∘L
              SparseEdgeMoments.entryGenerator M ∘L
                SparseEdgeMoments.boundary (D.rowloc x) (D.colloc x))) := by
          rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
      _ = (s : ℂ)⁻¹ • SparseStateOverlap.matrixOperator M := by
          rw [hcomp, smul_smul, ← mul_inv, hr]
  have hMop : SparseStateOverlap.matrixOperator M =
      (μ : ℂ)⁻¹ • SparseStateOverlap.matrixOperator (D.matrix x) := by
    rw [hM, NativeSignedFactor.matrixOperator_mul_const]
  have hB := FixedLocatorConjugation.locator_boundary D x
  have hC : Cedge D x (fun e => ((q : ℝ) : ℂ) • ExactEdgeCayley.generator (M e.1 e.2)) =
      ((q : ℝ) : ℂ) • ((s : ℂ)⁻¹ • SparseStateOverlap.matrixOperator M) := by
    rw [Cedge, OrientedEdgeCayley.lift_smul, OrientedEdgeCayley.lift_generator, ← hX, ← hB,
      adjoint_comp]
    simp only [comp_smul, smul_comp, comp_assoc]
  rw [hL, hC, hMop, qlift_smul, qlift_smul, qlift_smul, smul_smul, smul_smul]
  congr 1
  have hs1 : (0 : ℝ) < s := by exact_mod_cast D.slots_pos
  have hμ0 : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hs2 : (s : ℂ) ≠ 0 := by exact_mod_cast hs1.ne'
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast
  field_simp

/-! ### The clipped interface -/

/-- **The clipped joint interface from binary sparse oracles** (`twonorm:eq:joint-moments`). For
an input whose matrix is Hermitian with row and column Euclidean norms at most `η` and entries of
modulus at most `μ`, and `σ` with `s μ² = σ η²`, in the regime `Regime σ θ ε`: the boundary `U_J`
from Hadamard gates (`clUJg`) on `k + 4` ancillas, the private Cayley unitary `D` and the
operators `K`, `P_±` conjugated by the frame `W = A F` (`clK`, `clD`, `clPp`, `clPm`), with
`β = h` and `q`. -/
def clippedIface (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ) (hsb : sb ≤ k)
    (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {σ θ ε μ η : ℝ} (Rg : LargeSparsityCore.Parameters.Regime σ θ ε) (hμ : 0 < μ)
    (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2) (x : X) (hH : (D.matrix x).IsHermitian)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (hent : ∀ i j, ‖D.matrix x i j‖ ≤ μ) :
    ClippedIface (Reg (Fin k) R) σ θ ε (s * μ / LargeSparsityCore.Parameters.qval σ θ ε)
      (sysH (R := R) D en x) where
  a := k + 3 + 1
  UJ := UJop (R := R) (clUJg k sb hsb)
  D := clD (R := R) D en μ (LargeSparsityCore.Parameters.hval θ ε)
    (LargeSparsityCore.Parameters.qval σ θ ε) x
  K := clK (R := R) D en μ (LargeSparsityCore.Parameters.hval θ ε)
    (LargeSparsityCore.Parameters.qval σ θ ε) x
  Pp := clPp (R := R) D en μ (LargeSparsityCore.Parameters.hval θ ε) x
  Pm := clPm (R := R) D en μ (LargeSparsityCore.Parameters.hval θ ε) x
  unitaryJ := UJop_isUnitary _ (clUJg_ok (k := k) sb hsb)
  unitaryD := clD_isUnitary D en μ _ _ x
  core := clip_coreData D en x sb hsb hs hrange Rg hμ hσ hrow hcol
  compress := clip_compress_K D en x sb hsb hs hrange hμ Rg.h_pos.le Rg.q_pos hH hent

end

end GateOptimalBinary
