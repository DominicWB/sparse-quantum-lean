import GateOptimalBinary.ClipLayout

/-!
# The clipped regime from binary sparse oracles

The clipped-transducer regime of Theorem `gate:thm:main` uses the interface
`GateOptimalPrecision.ClippedIface`: a boundary `U_J`, a private Hermitian operator `K` and its
Cayley transform `D`, and the isolated projections `P_±`, with the hypotheses
`LargeSparsityCore.Core.CoreData` of the large-sparsity core and `J†KJ = H/α`, `α = sμ/q`
(`twonorm:eq:joint`, `twonorm:eq:joint-moments`, `twonorm:eq:weights`; Section `gate:sec:native`,
paragraph "Sparse preparation and the joint private operation"). It is constructed here from the
binary sparse oracles of `GateEfficientBinary`, on `k + 4` ancilla qubits (`PRf k`):

* the entries are clipped at the scale `μ` with `β = h` (`cl1 = c₁`, `cl2 = c₂`,
  `LargeSparsityCore.Native.cclip`, `ccorr`); `c₁ + c₂ = H_e/μ` for `|H_e| ≤ μ`, `β|c₁| ≤ 1` and
  `|c₂| ≤ β|H_e|²/μ²`;
* the frame `W = A F` (`WF`): the lifted locator `F` (`FL`) and, on the correction branch, the
  stable signed factor `U(c₂)` on the flag, the orientation and the sign (`AF`; `U(0) = I` on the
  bulk branch);
* in the frame the private operators act on the orientation qubit only, chosen by the branch, the
  flag and the edge (`LK`, `LD`, `LP`, `LM`): `K = 2q E(y)` and `D = D(y)` (the edge rotation) for
  `y = [g = 0] 2q c₁ + [g = 1][f = 1] 2q e^{iφ}`, and `P_± = [g = 1][f = 1] Π_±`;
* `clK`, `clD`, `clPp`, `clPm`: the interface operators, `K = W†ΛW`, `D = W†λ(Λ)W`,
  `P_± = W†Π_±W`; `clip_spectral`: the block structure `CayleyBlocks.Spectral`, from the Cayley
  relations of the edge rotation;
* `clip_compress`: the compression of a located operation by the boundary is the qubit lift of
  an edge compression by the sparse boundary `J₀`, with the local factor entering only through
  its action on the initial block (`uMat_fblk_block`).

The moments and the interface itself are in `ClipCore`.

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
open SparseHamiltonian.GateNative (edgeMat)
open NativeSignedFactor (phase norm_phase)
open LargeSparsityCore.CayleyBlocks (Spectral R1)
open SparseHamiltonian.GateODE (overwrite_apply_ι overwrite_apply_out)
open scoped InnerProduct Matrix

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-! ### Entries and values -/

/-- The edge held by a configuration of the clipped register. -/
def edgeC (en : Cfg (Fin k) ≃ n) (y : Cfg (PRf k)) : n × n :=
  phiE en (fun e => y (ιF k (ixPR k e)))

/-- The clipped entry `c₁ = (H_e/μ)/(1 + β|H_e|/μ)` (`twonorm:eq:clip`). -/
def cl1 (D : Data X n (Cfg (VW b)) s) (μ β : ℝ) (x : X) (e : n × n) : ℂ :=
  LargeSparsityCore.Native.cclip μ β (D.matrix x e.1 e.2)

/-- The correction entry `c₂ = H_e/μ - c₁`, clipped to the unit disk. -/
def cl2 (D : Data X n (Cfg (VW b)) s) (μ β : ℝ) (x : X) (e : n × n) : ℂ :=
  LargeSparsityCore.Native.ccorr μ β (D.matrix x e.1 e.2)

theorem norm_cl2_le (D : Data X n (Cfg (VW b)) s) (μ β : ℝ) (x : X) (e : n × n) :
    ‖cl2 D μ β x e‖ ≤ 1 :=
  LargeSparsityCore.Native.norm_ccorr_le_one _

/-- The value of the edge rotation of the joint private operation: `2q c₁` on the bulk branch,
`2q e^{iφ}` on the success flag of the correction branch, `0` on its failure flag. -/
def yC (q : ℝ) (g f : Bool) (c₁ c₂ : ℂ) : ℂ :=
  if g then (if f then ((2 * q : ℝ) : ℂ) * phase c₂ else 0) else ((2 * q : ℝ) : ℂ) * c₁

/-- The branch, the flag and the edge of a configuration select the value. -/
def yCfg (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X)
    (y : Cfg (PRf k)) : ℂ :=
  yC q (y (gW k)) (y (locF k 0)) (cl1 D μ β x (edgeC en y)) (cl2 D μ β x (edgeC en y))

/-- The success indicator `[g = 1][f = 1]`. -/
def sucC (y : Cfg (PRf k)) : Bool := y (gW k) && y (locF k 0)

/-- The factor entry: `c₂` on the correction branch, `0` on the bulk branch. -/
def cF (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X)
    (y : Cfg (PRf k)) : ℂ :=
  if y (gW k) then cl2 D μ β x (edgeC en y) else 0

theorem norm_cF_le (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X)
    (y : Cfg (PRf k)) : ‖cF D en μ β x y‖ ≤ 1 := by
  unfold cF
  split_ifs
  · exact norm_cl2_le D μ β x _
  · simp

/-! ### The located operators -/

/-- The located generator `Λ_K = 2q E(y)` on the orientation. -/
def LK (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X) :
    Reg (PRf k) R →L[ℂ] Reg (PRf k) R :=
  condOp (locF k 1) (fun y => eMat (yCfg D en μ β q x y))

/-- The located Cayley operator `λ(Λ_K) = D(y)`, the edge rotation. -/
def LD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X) :
    Reg (PRf k) R →L[ℂ] Reg (PRf k) R :=
  condOp (locF k 1) (fun y => edgeMat (yCfg D en μ β q x y))

/-- The located isolated projection `[g = 1][f = 1] Π_+`. -/
def LP (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X) :
    Reg (PRf k) R →L[ℂ] Reg (PRf k) R :=
  condOp (locF k 1) (fun y => if sucC y then piP (cl2 D μ β x (edgeC en y)) else 0)

/-- The located isolated projection `[g = 1][f = 1] Π_-`. -/
def LM (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X) :
    Reg (PRf k) R →L[ℂ] Reg (PRf k) R :=
  condOp (locF k 1) (fun y => if sucC y then piM (cl2 D μ β x (edgeC en y)) else 0)

/-- The stable signed factor `U(c₂)` on the correction branch. -/
def AF (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X) :
    Reg (PRf k) R →L[ℂ] Reg (PRf k) R :=
  localOp (locF k) (locF k).injective (fun y => matOp (blk (uMat (cF D en μ β x y))))

/-- The lifted locator on the clipped register. -/
def FL (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    Reg (PRf k) R →L[ℂ] Reg (PRf k) R :=
  localOp (ιS k) (ιS_injective k) (fun _ => FuF (R := R) D en x)

/-- **The frame** `W = A F`. -/
def WF (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X) :
    Reg (PRf k) R →L[ℂ] Reg (PRf k) R :=
  AF (R := R) D en μ β x ∘L FL D en x

theorem AF_isUnitary (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X) :
    IsUnitary (AF (R := R) D en μ β x) :=
  localOp_isUnitary _ _ (fun y => matOp_isUnitary _
    (blk_uMat_unitary (norm_cF_le D en μ β x y)).1 (blk_uMat_unitary (norm_cF_le D en μ β x y)).2)

theorem FL_isUnitary (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    IsUnitary (FL (R := R) D en x) :=
  localOp_isUnitary _ _ (fun _ => FuF_isUnitary D en x)

theorem WF_isUnitary (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X) :
    IsUnitary (WF (R := R) D en μ β x) := by
  have h := (AF_isUnitary (R := R) D en μ β x).mul (FL_isUnitary (R := R) D en x)
  rwa [mul_def] at h

/-! ### The block structure of the located operators -/

theorem condOp_comp' (t : PRf k) (u v : Cfg (PRf k) → Matrix Bool Bool ℂ) :
    condOp (Q := R) t u ∘L condOp t v = condOp t (fun y => u y * v y) :=
  condOp_comp t u v

theorem yCfg_suc (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X)
    (y : Cfg (PRf k)) (h : sucC y = true) :
    yCfg D en μ β q x y = ((2 * q : ℝ) : ℂ) * phase (cl2 D μ β x (edgeC en y)) := by
  unfold sucC at h
  rw [Bool.and_eq_true] at h
  unfold yCfg yC
  rw [if_pos h.1, if_pos h.2]

theorem eMat_yC_piP (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X)
    (y : Cfg (PRf k)) :
    eMat (yCfg D en μ β q x y) * (if sucC y then piP (cl2 D μ β x (edgeC en y)) else 0) =
      (((2 * q : ℝ) : ℝ) : ℂ) • (if sucC y then piP (cl2 D μ β x (edgeC en y)) else 0) := by
  by_cases h : sucC y = true
  · rw [if_pos h, yCfg_suc D en μ β q x y h, eMat_real_mul, Matrix.smul_mul,
      eMat_phase_mul_piP]
  · rw [if_neg h, Matrix.mul_zero, smul_zero]

theorem eMat_yC_piM (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X)
    (y : Cfg (PRf k)) :
    eMat (yCfg D en μ β q x y) * (if sucC y then piM (cl2 D μ β x (edgeC en y)) else 0) =
      (((-(2 * q) : ℝ) : ℝ) : ℂ) • (if sucC y then piM (cl2 D μ β x (edgeC en y)) else 0) := by
  by_cases h : sucC y = true
  · rw [if_pos h, yCfg_suc D en μ β q x y h, eMat_real_mul, Matrix.smul_mul,
      eMat_phase_mul_piM, smul_neg, ← neg_smul]
    push_cast
    rfl
  · rw [if_neg h, Matrix.mul_zero, smul_zero]

/-- **The block structure of the located operators** (`CayleyBlocks.Spectral`). -/
theorem located_spectral (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ)
    (x : X) :
    Spectral (LK (R := R) D en μ β q x) (LD (R := R) D en μ β q x) (LP (R := R) D en μ β x)
      (LM (R := R) D en μ β x) q := by
  have hsa : ∀ u : Cfg (PRf k) → Matrix Bool Bool ℂ, (∀ y, (u y)ᴴ = u y) →
      IsSelfAdjoint (condOp (Q := R) (locF k 1) u) := by
    intro u hu
    change (condOp (Q := R) (locF k 1) u)† = _
    rw [condOp_adjoint]
    congr 1
    funext y
    exact hu y
  have hP : ∀ y : Cfg (PRf k), (if sucC y then piP (cl2 D μ β x (edgeC en y)) else 0)ᴴ =
      if sucC y then piP (cl2 D μ β x (edgeC en y)) else 0 := by
    intro y
    split_ifs
    · exact piP_conjTranspose _
    · exact Matrix.conjTranspose_zero
  have hM : ∀ y : Cfg (PRf k), (if sucC y then piM (cl2 D μ β x (edgeC en y)) else 0)ᴴ =
      if sucC y then piM (cl2 D μ β x (edgeC en y)) else 0 := by
    intro y
    split_ifs
    · exact piM_conjTranspose _
    · exact Matrix.conjTranspose_zero
  have hone : (1 : Reg (PRf k) R →L[ℂ] Reg (PRf k) R) = condOp (locF k 1) (fun _ => 1) :=
    (condOp_one _).symm
  have hR1 : R1 (LK (R := R) D en μ β q x) = condOp (locF k 1)
      (fun y => (2 : ℂ)⁻¹ • (1 + Complex.I • eMat (yCfg D en μ β q x y))) := by
    rw [R1, LK, condOp_smul, hone, condOp_add, condOp_smul]
  have hsub : 1 - LD (R := R) D en μ β q x =
      condOp (locF k 1) (fun y => 1 - edgeMat (yCfg D en μ β q x y)) := by
    rw [LD, hone, condOp_sub]
  refine ⟨hsa _ (fun y => eMat_conjTranspose _), ?_, ?_, hsa _ hP, hsa _ hM, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [LP, condOp_comp]
    congr 1
    funext y
    split_ifs
    · exact piP_mul_piP _
    · exact Matrix.zero_mul _
  · rw [LM, condOp_comp]
    congr 1
    funext y
    split_ifs
    · exact piM_mul_piM _
    · exact Matrix.zero_mul _
  · rw [LP, LM, condOp_comp, ← condOp_zero (Q := R) (locF k 1)]
    congr 1
    funext y
    split_ifs
    · exact piP_mul_piM _
    · exact Matrix.zero_mul _
  · rw [LP, LM, condOp_comp, ← condOp_zero (Q := R) (locF k 1)]
    congr 1
    funext y
    split_ifs
    · exact piM_mul_piP _
    · exact Matrix.zero_mul _
  · rw [LK, LP, condOp_comp, condOp_smul]
    congr 1
    funext y
    exact eMat_yC_piP D en μ β q x y
  · rw [LK, LM, condOp_comp, condOp_smul]
    congr 1
    funext y
    exact eMat_yC_piM D en μ β q x y
  · rw [hR1, hsub, condOp_comp, ← condOp_one (Q := R) (locF k 1)]
    congr 1
    funext y
    exact cayley_mul_R1 _
  · rw [hR1, hsub, condOp_comp, ← condOp_one (Q := R) (locF k 1)]
    congr 1
    funext y
    exact R1_mul_cayley _

theorem LD_isometry (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X) :
    (LD (R := R) D en μ β q x)† ∘L LD (R := R) D en μ β q x = 1 := by
  rw [LD, condOp_adjoint, condOp_comp, ← condOp_one (Q := R) (locF k 1)]
  congr 1
  funext y
  exact edgeMat_unitary _

/-! ### The interface operators -/

/-- The frame from the ancilla register. -/
abbrev WFa (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X) :
    Anc (k + 3 + 1) (Reg (Fin k) R) →L[ℂ] Reg (PRf k) R :=
  WF (R := R) D en μ β x ∘L (fl (W := Fin (k + 3 + 1)) (S := Fin k) (R := R))

theorem unconj_WF (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X)
    (T : Reg (PRf k) R →L[ℂ] Reg (PRf k) R) :
    unconj ((WF (R := R) D en μ β x)† ∘L T ∘L WF D en μ β x) =
      (WFa (R := R) D en μ β x)† ∘L T ∘L WFa D en μ β x := by
  rw [unconj_eq, WFa, adjoint_comp, fl_adjoint]
  simp only [comp_assoc]

theorem WFa_adj_comp (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X) :
    (WFa (R := R) D en μ β x)† ∘L WFa D en μ β x = 1 := by
  have h := (WF_isUnitary (R := R) D en μ β x).1
  rw [star_eq_adjoint, mul_def] at h
  rw [WFa, adjoint_comp, fl_adjoint]
  calc ((unfl (W := Fin (k + 3 + 1)) (S := Fin k) (R := R)) ∘L (WF (R := R) D en μ β x)†) ∘L
        (WF (R := R) D en μ β x ∘L (fl (W := Fin (k + 3 + 1)) (S := Fin k) (R := R)))
      = (unfl (W := Fin (k + 3 + 1)) (S := Fin k) (R := R)) ∘L
          ((WF (R := R) D en μ β x)† ∘L WF (R := R) D en μ β x) ∘L
          (fl (W := Fin (k + 3 + 1)) (S := Fin k) (R := R)) := by
        simp only [comp_assoc]
    _ = 1 := by rw [h, one_def, id_comp, unfl_fl]

theorem WFa_comp_adj (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X) :
    WFa (R := R) D en μ β x ∘L (WFa D en μ β x)† = 1 := by
  have h := (WF_isUnitary (R := R) D en μ β x).2
  rw [star_eq_adjoint, mul_def] at h
  rw [WFa, adjoint_comp, fl_adjoint]
  calc (WF (R := R) D en μ β x ∘L (fl (W := Fin (k + 3 + 1)) (S := Fin k) (R := R))) ∘L
        ((unfl (W := Fin (k + 3 + 1)) (S := Fin k) (R := R)) ∘L (WF (R := R) D en μ β x)†)
      = WF (R := R) D en μ β x ∘L ((fl (W := Fin (k + 3 + 1)) (S := Fin k) (R := R)) ∘L
          (unfl (W := Fin (k + 3 + 1)) (S := Fin k) (R := R))) ∘L (WF (R := R) D en μ β x)† := by
        simp only [comp_assoc]
    _ = 1 := by rw [fl_unfl, LargeSparsityCore.CayleyBlocks.one_comp, h]

/-- **The private Hermitian operator** `K = W† Λ_K W`. -/
def clK (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X) :
    Anc (k + 3 + 1) (Reg (Fin k) R) →L[ℂ] Anc (k + 3 + 1) (Reg (Fin k) R) :=
  unconj ((WF (R := R) D en μ β x)† ∘L LK D en μ β q x ∘L WF D en μ β x)

/-- **The private Cayley unitary** `D = W† D(y) W`. -/
def clD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X) :
    Anc (k + 3 + 1) (Reg (Fin k) R) →L[ℂ] Anc (k + 3 + 1) (Reg (Fin k) R) :=
  unconj ((WF (R := R) D en μ β x)† ∘L LD D en μ β q x ∘L WF D en μ β x)

/-- The isolated projection `P_+`. -/
def clPp (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X) :
    Anc (k + 3 + 1) (Reg (Fin k) R) →L[ℂ] Anc (k + 3 + 1) (Reg (Fin k) R) :=
  unconj ((WF (R := R) D en μ β x)† ∘L LP D en μ β x ∘L WF D en μ β x)

/-- The isolated projection `P_-`. -/
def clPm (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X) :
    Anc (k + 3 + 1) (Reg (Fin k) R) →L[ℂ] Anc (k + 3 + 1) (Reg (Fin k) R) :=
  unconj ((WF (R := R) D en μ β x)† ∘L LM D en μ β x ∘L WF D en μ β x)

/-- **The block structure of the joint private operators.** -/
theorem clip_spectral (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X) :
    Spectral (clK (R := R) D en μ β q x) (clD (R := R) D en μ β q x) (clPp (R := R) D en μ β x)
      (clPm (R := R) D en μ β x) q := by
  rw [clK, clD, clPp, clPm, unconj_WF, unconj_WF, unconj_WF, unconj_WF]
  exact spectral_conj' (located_spectral D en μ β q x) _ (WFa_adj_comp D en μ β x)
    (WFa_comp_adj D en μ β x)

theorem clD_isometry (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X) :
    (clD (R := R) D en μ β q x)† ∘L clD (R := R) D en μ β q x = 1 := by
  rw [clD, unconj_WF]
  exact conj_isometry' (WFa_adj_comp D en μ β x) (WFa_comp_adj D en μ β x)
    (LD_isometry D en μ β q x)

theorem clD_isUnitary (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X) :
    IsUnitary (clD (R := R) D en μ β q x) := by
  rw [clD]
  apply unconj_isUnitary
  have hW := WF_isUnitary (R := R) D en μ β x
  have hD : IsUnitary (LD (R := R) D en μ β q x) := by
    rw [LD]
    exact condOp_isUnitary _ _ (fun y => ⟨edgeMat_unitary _, mul_eq_one_comm.1 (edgeMat_unitary _)⟩)
  have hWa : IsUnitary ((WF (R := R) D en μ β x)†) := by
    simpa [star_eq_adjoint] using hW.adjoint
  have h := (hWa.mul hD).mul hW
  rwa [mul_def, mul_def] at h

/-! ### The compression by the boundary -/

/-- **The boundary of the clipped regime** `J = U_J ι₀`. -/
abbrev clJ (k sb : ℕ) (hsb : sb ≤ k) : Reg (Fin k) R →L[ℂ] Anc (k + 3 + 1) (Reg (Fin k) R) :=
  UJop (R := R) (clUJg k sb hsb) ∘L iota0 (a := k + 3 + 1) (P := Reg (Fin k) R)

theorem gW_ne_locF (k : ℕ) (i : Fin 3) : locF k i ≠ gW k := ιS_ne_gW k _

theorem edge_ne_locF (k : ℕ) (i : Fin 3) (e : EW k) : locF k i ≠ ιF k (ixPR k e) :=
  fun h => locU_ne_ixPR k i e ((ιS_injective k) h)

omit [Fintype n] [DecidableEq n] in
theorem edgeC_overwrite_locF (en : Cfg (Fin k) ≃ n) (y : Cfg (PRf k)) (d : Cfg (Fin 3)) :
    edgeC en (overwrite (locF k) y d) = edgeC en y := by
  unfold edgeC
  congr 1
  funext e
  exact overwrite_apply_out _ _ _ _ (fun i => edge_ne_locF k i e)

omit [Fintype n] [DecidableEq n] in
theorem edgeC_update_locF (en : Cfg (Fin k) ≃ n) (y : Cfg (PRf k)) (i : Fin 3) (v : Bool) :
    edgeC en (Function.update y (locF k i) v) = edgeC en y := by
  unfold edgeC
  congr 1
  funext e
  exact Function.update_of_ne (fun h => edge_ne_locF k i e h.symm) _ _

omit [Fintype n] [DecidableEq n] in
/-- A located operation on the orientation, chosen by the branch, the flag and the edge, as a
flag-diagonal block on the local qubits. -/
theorem located_fblk (en : Cfg (Fin k) ≃ n) (uE : Bool → Bool → n × n → Matrix Bool Bool ℂ) :
    condOp (Q := R) (locF k 1) (fun y => uE (y (gW k)) (y (locF k 0)) (edgeC en y)) =
      localOp (locF k) (locF k).injective (fun y => matOp (blk (fblk (fun f =>
        uE (y (gW k)) f (edgeC en y))))) := by
  rw [condOp_eq_fblk (locF k).injective _ (fun y v => by
    rw [Function.update_of_ne (gW_ne_locF k 2).symm, edgeC_update_locF,
      Function.update_of_ne (fun h => absurd ((locF k).injective h) (by decide))])]
  congr 1
  funext y
  congr 3
  funext f
  rw [overwrite_apply_out _ _ _ _ (gW_ne_locF k), edgeC_overwrite_locF,
    overwrite_apply_ι (locF k).injective]
  rfl

theorem AF_sandwich (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X)
    (B : Cfg (PRf k) → Bool → Matrix Bool Bool ℂ) :
    (AF (R := R) D en μ β x)† ∘L localOp (locF k) (locF k).injective
        (fun y => matOp (blk (fblk (B y)))) ∘L AF D en μ β x =
      localOp (locF k) (locF k).injective (fun y => matOp (blk ((uMat (cF D en μ β x y))ᴴ *
        fblk (B y) * uMat (cF D en μ β x y)))) := by
  rw [AF, localOp_adjoint, localOp_comp, localOp_comp]
  congr 1
  funext y
  rw [matOp_adjoint, matOp_mul, matOp_mul, blk_mul, blk_mul, blk_conjTranspose, Matrix.mul_assoc]

omit [Fintype n] [DecidableEq n] in
theorem edgeC_extG_extU (en : Cfg (Fin k) ≃ n) (g : Bool) (c : Cfg (PR k)) :
    edgeC en (extG g (clearCfg (locU k) (extU c))) = phiE en (fun e => c (ixPR k e)) := by
  unfold edgeC
  congr 1
  funext e
  change extG g (clearCfg (locU k) (extU c)) (ιS k (ιU k (ixPR k e))) = _
  rw [extG_ιS, clearCfg_apply_out _ _ _ (fun a => locU_ne_ixPR k a e), extU_ιU]

theorem cF_extG (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X)
    (g : Bool) (c : Cfg (PR k)) :
    cF D en μ β x (extG g (clearCfg (locU k) (extU c))) =
      if g then cl2 D μ β x (phiE en (fun e => c (ixPR k e))) else 0 := by
  unfold cF
  rw [extG_g, edgeC_extG_extU]

/-- **The compression of a located operation by the clipped boundary**: the qubit lift of the
compression by `J₀` of the edgewise operation
`½ (u₀₀ + (1 - |c₂|) u₁₀ + |c₂| (Π₊ u₁₁ Π₊ + Π₋ u₁₁ Π₋))` (`u_{gf}` the matrix of the branch
`g` and the flag `f`). -/
theorem clip_compress (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (sb : ℕ) (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    (μ β : ℝ) (uE : Bool → Bool → n × n → Matrix Bool Bool ℂ) :
    (clJ (R := R) k sb hsb)† ∘L
        unconj ((WF (R := R) D en μ β x)† ∘L
          condOp (locF k 1) (fun y => uE (y (gW k)) (y (locF k 0)) (edgeC en y)) ∘L
          WF D en μ β x) ∘L clJ k sb hsb =
      qlift (R := R) en ((FixedLocatorConjugation.fixedBoundary D.slot)† ∘L
        ((FixedLocatorConjugation.locator D x)† ∘L OrientedEdgeCayley.lift (fun e => qop
          ((2⁻¹ : ℂ) • (uE false false e + ((1 - ‖cl2 D μ β x e‖ : ℝ) : ℂ) • uE true false e +
            ((‖cl2 D μ β x e‖ : ℝ) : ℂ) • (piP (cl2 D μ β x e) * uE true true e *
              piP (cl2 D μ β x e) + piM (cl2 D μ β x e) * uE true true e * piM (cl2 D μ β x e)))))
          ∘L FixedLocatorConjugation.locator D x) ∘L
        FixedLocatorConjugation.fixedBoundary D.slot) := by
  rw [clJ, clip_boundary_reduce sb hsb]
  have hW : WF (R := R) D en μ β x ∘L ιGp k = AF (R := R) D en μ β x ∘L ιGp k ∘L FuF D en x := by
    rw [WF, comp_assoc, FL, localOp_ιGp]
  have h1 : (ιGp (R := R) k)† ∘L ((WF (R := R) D en μ β x)† ∘L
      condOp (locF k 1) (fun y => uE (y (gW k)) (y (locF k 0)) (edgeC en y)) ∘L
      WF D en μ β x) ∘L ιGp k =
      (FuF (R := R) D en x)† ∘L ((ιGp (R := R) k)† ∘L ((AF (R := R) D en μ β x)† ∘L
        condOp (locF k 1) (fun y => uE (y (gW k)) (y (locF k 0)) (edgeC en y)) ∘L
        AF D en μ β x) ∘L ιGp k) ∘L FuF D en x := by
    calc (ιGp (R := R) k)† ∘L ((WF (R := R) D en μ β x)† ∘L
          condOp (locF k 1) (fun y => uE (y (gW k)) (y (locF k 0)) (edgeC en y)) ∘L
          WF D en μ β x) ∘L ιGp k
        = (WF (R := R) D en μ β x ∘L ιGp k)† ∘L
            condOp (locF k 1) (fun y => uE (y (gW k)) (y (locF k 0)) (edgeC en y)) ∘L
            (WF (R := R) D en μ β x ∘L ιGp k) := by
          simp only [adjoint_comp, comp_assoc]
      _ = _ := by
          rw [hW]
          simp only [adjoint_comp, comp_assoc]
  rw [h1, located_fblk, AF_sandwich, ιGp_compress]
  apply sg_boundary_compress D en x sb hsb hs hrange
  intro c b b'
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, blk, Matrix.submatrix_apply,
    cF_extG, extG_g, edgeC_extG_extU, Bool.false_eq_true, ↓reduceIte]
  have hq : ∀ b : Bool, eQ (ff b) = (false, (b, false)) := fun b => rfl
  rw [hq, hq, uMat_zero, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    uMat_fblk_block (norm_cl2_le D μ β x _), fblk_apply]
  simp only [and_self, if_true, Matrix.add_apply]
  ring

end

end GateOptimalBinary
