import GateEfficientBinary.Sparse.LiftNorm

/-!
# Gate circuits act on the qubits only: transfer from payload `ℂ` to any payload

An elementary gate acts on the computational configurations of its wires and leaves the payload
Hilbert space untouched: on every payload `Q` it is the configuration matrix `gateMat` tensored
with the identity (`gateOp_eq_matOp`), and so is every gate list (`gRun_eq_matOp`). The
projection onto the vectors supported on a set `S` of configurations is likewise a matrix
(`projS`).

`approxOn_payload`: approximate agreement `ApproxOn S` between two such matrix operators, proved
for the payload `ℂ` (finite matrices, as in the synthesis literature), holds for every payload
Hilbert space, with the same error. The proof writes the error on `S`-supported vectors as the
qubit lift of an operator on `ℓ²` (`GateBinary.qlift`), which does not increase norms
(`GateBinary.norm_qlift_le`). `approxOn_gRun_payload` is the form for gate lists.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSynth

noncomputable section
open ContinuousLinearMap GateCircuit GateNative
open GateBinary (toMat qlift qlift_eq norm_qlift_le matOp_add matOp_smul)
open scoped InnerProduct

variable {W : Type*} [Fintype W] [DecidableEq W]

/-! ### Matrices of gates -/

section Mat

variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

omit [CompleteSpace Q] in
theorem matOp_sub_gen (M N : Matrix (Cfg W) (Cfg W) ℂ) :
    matOp (Q := Q) (M - N) = matOp M - matOp N := by
  rw [sub_eq_add_neg, sub_eq_add_neg, matOp_add, ← neg_one_smul ℂ N, matOp_smul]
  congr 1
  exact neg_one_smul ℂ (matOp (Q := Q) N)

/-- The configuration matrix of a controlled one-qubit gate. -/
def gateMat (cs : List (W × Bool)) (t : W) (u : Matrix Bool Bool ℂ) :
    Matrix (Cfg W) (Cfg W) ℂ :=
  fun x y => if ctrlOK cs x then (if y = Function.update x t (y t) then u (x t) (y t) else 0)
    else (if y = x then 1 else 0)

/-- A controlled one-qubit gate is its configuration matrix, on every payload. -/
theorem gateOp_eq_matOp (cs : List (W × Bool)) (t : W) (u : Matrix Bool Bool ℂ)
    (ht : ∀ c ∈ cs, c.1 ≠ t) : gateOp (Q := Q) cs t u = matOp (gateMat cs t u) := by
  ext ψ x
  rw [gateOp_apply cs t u ht, matOp_apply]
  by_cases hc : ctrlOK cs x = true
  · rw [if_pos hc]
    simp only [gateMat, hc, if_true]
    have hinj : Function.Injective (fun b : Bool => Function.update x t b) := by
      intro b b' h
      have := congrFun h t
      simpa using this
    symm
    calc (∑ y : Cfg W, (if y = Function.update x t (y t) then u (x t) (y t) else 0) • ψ y)
        = ∑ y ∈ Finset.univ.image (fun b : Bool => Function.update x t b),
            (if y = Function.update x t (y t) then u (x t) (y t) else 0) • ψ y := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro y _ hy
          have hne : y ≠ Function.update x t (y t) := fun h =>
            hy (Finset.mem_image.mpr ⟨y t, Finset.mem_univ _, h.symm⟩)
          rw [if_neg hne, zero_smul]
      _ = ∑ b : Bool, (if Function.update x t b = Function.update x t ((Function.update x t b) t)
            then u (x t) ((Function.update x t b) t) else 0) • ψ (Function.update x t b) :=
          Finset.sum_image (fun b _ b' _ h => hinj h)
      _ = ∑ b : Bool, u (x t) b • ψ (Function.update x t b) := by
          apply Finset.sum_congr rfl
          intro b _
          simp
  · rw [if_neg hc]
    simp only [gateMat, hc, Bool.false_eq_true, if_false]
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      rw [if_neg hy, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ x) h

/-- The configuration matrix of a gate list (the head acts first). -/
def gsMat : List (Gate W) → Matrix (Cfg W) (Cfg W) ℂ
  | [] => 1
  | g :: gs => gsMat gs * gateMat g.cs g.t g.u

/-- A gate list is its configuration matrix, on every payload. -/
theorem gRun_eq_matOp (gs : List (Gate W)) (h : ∀ g ∈ gs, ∀ c ∈ g.cs, c.1 ≠ g.t) :
    gRun (Q := Q) gs = matOp (gsMat gs) := by
  induction gs with
  | nil => exact matOp_one.symm
  | cons g gs ih =>
      rw [gRun_cons, ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg')), Gate.op,
        gateOp_eq_matOp g.cs g.t g.u (h g List.mem_cons_self), matOp_mul, gsMat]

/-- The projection onto the vectors supported on `S`. -/
def projS (S : Cfg W → Prop) : Reg W Q →L[ℂ] Reg W Q :=
  open Classical in matOp (Matrix.diagonal (fun x => if S x then (1 : ℂ) else 0))

omit [CompleteSpace Q] in
theorem projS_apply (S : Cfg W → Prop) (ψ : Reg W Q) (x : Cfg W) :
    projS (Q := Q) S ψ x = open Classical in if S x then ψ x else 0 := by
  classical
  rw [projS, matOp_apply, Finset.sum_eq_single x]
  · by_cases hx : S x <;> simp [Matrix.diagonal_apply_eq, hx]
  · intro y _ hy
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hy), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ x) h

omit [CompleteSpace Q] in
theorem projS_supp (S : Cfg W → Prop) {ψ : Reg W Q} (hψ : Supp S ψ) : projS S ψ = ψ := by
  classical
  ext x
  rw [projS_apply]
  by_cases hx : S x
  · rw [if_pos hx]
  · rw [if_neg hx, hψ x hx]

omit [CompleteSpace Q] in
theorem supp_projS (S : Cfg W → Prop) (ψ : Reg W Q) : Supp S (projS S ψ) := by
  classical
  intro x hx
  rw [projS_apply, if_neg hx]

omit [CompleteSpace Q] in
theorem norm_projS_le (S : Cfg W → Prop) (ψ : Reg W Q) : ‖projS S ψ‖ ≤ ‖ψ‖ := by
  classical
  have hsq : ‖projS S ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum
    intro x _
    rw [projS_apply]
    split_ifs
    · exact le_rfl
    · simp
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

end Mat

/-! ### From payload `ℂ` to every payload -/

section Transfer

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The `ℓ²` matrix of a matrix operator on the payload `ℂ` is the matrix itself. -/
theorem toMat_matOp (M : Matrix (Cfg W) (Cfg W) ℂ) :
    toMat (Equiv.refl (Cfg W)) (matOp (Q := ℂ) M) = M := by
  funext c c'
  simp only [toMat, Equiv.refl_apply]
  rw [matOp_apply, Finset.sum_eq_single c']
  · simp
  · intro d _ hd
    simp [hd]
  · intro h
    exact absurd (Finset.mem_univ c') h

/-- **Payload transfer.** Approximate agreement on `S`-supported vectors between two matrix
operators, for the payload `ℂ`, holds for every payload with the same error. -/
theorem approxOn_payload (S : Cfg W → Prop) (M N : Matrix (Cfg W) (Cfg W) ℂ) {δ : ℝ}
    (hδ : 0 ≤ δ) (h : ApproxOn (Q := ℂ) S (matOp M) (matOp N) δ) :
    ApproxOn (Q := R) S (matOp M) (matOp N) δ := by
  classical
  set D : Matrix (Cfg W) (Cfg W) ℂ := Matrix.diagonal (fun x => if S x then (1 : ℂ) else 0)
  -- The error on `S`-supported vectors, for the payload `ℂ`.
  set A : Reg W ℂ →L[ℂ] Reg W ℂ := matOp ((M - N) * D) with hA
  have hAeq : ∀ φ : Reg W ℂ, A φ = matOp M (projS S φ) - matOp N (projS S φ) := by
    intro φ
    rw [hA, ← matOp_mul, matOp_sub_gen, comp_apply, sub_apply]
    rfl
  have hAn : ‖A‖ ≤ δ := by
    apply ContinuousLinearMap.opNorm_le_bound _ hδ
    intro φ
    rw [hAeq]
    exact (h _ (supp_projS S φ)).trans (mul_le_mul_of_nonneg_left (norm_projS_le S φ) hδ)
  intro ψ hψ
  have hq : qlift (R := R) (Equiv.refl (Cfg W)) A = matOp ((M - N) * D) := by
    rw [qlift_eq, hA, toMat_matOp]
  have e : matOp (Q := R) M ψ - matOp N ψ = qlift (R := R) (Equiv.refl (Cfg W)) A ψ := by
    rw [hq, ← matOp_mul, matOp_sub_gen, comp_apply, sub_apply]
    change matOp (Q := R) M ψ - matOp N ψ = matOp M (projS S ψ) - matOp N (projS S ψ)
    rw [projS_supp S hψ]
  rw [e]
  calc ‖qlift (R := R) (Equiv.refl (Cfg W)) A ψ‖
      ≤ ‖qlift (R := R) (Equiv.refl (Cfg W)) A‖ * ‖ψ‖ := le_opNorm _ _
    _ ≤ ‖A‖ * ‖ψ‖ := mul_le_mul_of_nonneg_right (norm_qlift_le _ _) (norm_nonneg _)
    _ ≤ δ * ‖ψ‖ := mul_le_mul_of_nonneg_right hAn (norm_nonneg _)

/-- **Payload transfer for gate lists.** -/
theorem approxOn_gRun_payload (S : Cfg W → Prop) (gs hs : List (Gate W))
    (hg : ∀ g ∈ gs, ∀ c ∈ g.cs, c.1 ≠ g.t) (hh : ∀ g ∈ hs, ∀ c ∈ g.cs, c.1 ≠ g.t) {δ : ℝ}
    (hδ : 0 ≤ δ) (h : ApproxOn (Q := ℂ) S (gRun gs) (gRun hs) δ) :
    ApproxOn (Q := R) S (gRun gs) (gRun hs) δ := by
  rw [gRun_eq_matOp gs hg, gRun_eq_matOp hs hh] at h ⊢
  exact approxOn_payload S _ _ hδ h

end Transfer

end

end SparseHamiltonian.GateSynth
