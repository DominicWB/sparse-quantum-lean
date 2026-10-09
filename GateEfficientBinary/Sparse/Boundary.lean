import GateEfficientBinary.Sparse.Native
import GateEfficientNative.Hamiltonian.Macro

/-!
# The boundary preparation `U_J` from Hadamard gates

The fixed boundary of the sparse Cayley operation (`FixedNativeCayleySimulation.boundary`) maps
the system index `i` to the uniform superposition `(2s)^{-1/2} ∑_{o, m} |o, (i, slot m)⟩` over
both orientations `o` and the `s` slots `m`. When `s = 2^σ` and the slots are exactly the index
words supported on the lowest `σ` bits, it is prepared from the clean ancillas by Hadamard gates
on the orientation wire and on the lowest `σ` wires of the second index (`hadUJ`).

* `gRun_hadList_bas`: Hadamard gates on distinct clean wires write the uniform superposition of
  those wires;
* `embQ`: the zero-ancilla embedding `|i⟩ ↦ |0, (i, 0)⟩` of the system index into the oriented
  edge space; `iota0_unconj_qlift`: compressing a lifted edge operator to clean ancillas is the
  system lift of its compression by `embQ`;
* `hadUJ_iota0`: `U_J ι₀` is the lift of `J E†` on clean ancillas, for the fixed boundary `J`;
* `boundary_lift`: `(U_J ι₀)† Â (U_J ι₀)` is the system lift of `J† A J`, for every operator `A`
  on the oriented edge space and its lift `Â`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinary

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateCircuit.Sim (iota0 iota0_apply iota0_adjoint_apply)
open SparseHamiltonian.OracleCircuit
open NativeSparseBlockEncoding (Data)
open scoped InnerProduct

/-! ### Hadamard gates on clean wires -/

section Had

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The Hadamard gate on the wire `w`. -/
def hadGate (w : W) : Gate W := ⟨[], w, hadC⟩

/-- The amplitude `1/√2`. -/
def hamp : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem hadC_false (b : Bool) : hadC b false = hamp := by
  cases b <;> rfl

omit [Fintype W] [DecidableEq W] in
theorem hadGate_ok (w : W) : GateOK 3 (hadGate w) :=
  ⟨by simp [hadGate], by simp [hadGate], hadC_unitary⟩

theorem hadGate_bas (w : W) (y : Cfg W) (hy : y w = false) (q : R) :
    (hadGate (W := W) w).op (bas y q) = hamp • (bas y q + bas (Function.update y w true) q) := by
  rw [Gate.op, gateOp, condOp_bas]
  have hu : Function.update y w false = y := by
    rw [← hy, Function.update_eq_self]
  simp only [hadGate, ctrlOK_nil, if_true, hy, hadC_false, Fintype.sum_bool, hu, smul_add]
  rw [add_comm]

/-- **Hadamard gates on distinct clean wires** write the uniform superposition of these wires:
the amplitude of `y'` is `2^{-|ws|/2}` when `y'` agrees with `y` off the wires `ws`, else `0`. -/
theorem gRun_hadList_bas (ws : List W) (hws : ws.Nodup) (y : Cfg W)
    (hy : ∀ w ∈ ws, y w = false) (q : R) (y' : Cfg W) :
    gRun (ws.map hadGate) (bas y q) y' =
      if (∀ v, v ∉ ws → y' v = y v) then hamp ^ ws.length • q else 0 := by
  induction ws generalizing y with
  | nil =>
      by_cases h : y' = y
      · subst h
        simp
      · have h' : ¬ ∀ v, v ∉ ([] : List W) → y' v = y v := fun hv =>
          h (funext fun v => hv v List.not_mem_nil)
        rw [if_neg h']
        simp [h]
  | cons w ws ih =>
      have hw : w ∉ ws := (List.nodup_cons.1 hws).1
      have hws' : ws.Nodup := (List.nodup_cons.1 hws).2
      have hyw : y w = false := hy w List.mem_cons_self
      have hy1 : ∀ v ∈ ws, y v = false := fun v hv => hy v (List.mem_cons_of_mem w hv)
      have hy2 : ∀ v ∈ ws, Function.update y w true v = false := fun v hv => by
        rw [Function.update_of_ne (fun h : v = w => hw (h ▸ hv))]
        exact hy1 v hv
      rw [List.map_cons, gRun_cons, comp_apply, hadGate_bas w y hyw q, map_smul, map_add,
        PiLp.smul_apply, PiLp.add_apply, ih hws' y hy1, ih hws' _ hy2]
      simp only [List.length_cons, pow_succ]
      by_cases hC : ∀ v, v ∉ w :: ws → y' v = y v
      · rw [if_pos hC]
        cases hyw' : y' w
        · have hA : ∀ v, v ∉ ws → y' v = y v := by
            intro v hv
            by_cases hvw : v = w
            · subst hvw
              rw [hyw', hyw]
            · exact hC v (by simp [hvw, hv])
          have hB : ¬ ∀ v, v ∉ ws → y' v = Function.update y w true v := by
            intro h
            have := h w hw
            rw [hyw', Function.update_self] at this
            exact absurd this (by decide)
          rw [if_pos hA, if_neg hB, add_zero, smul_smul, mul_comm]
        · have hA : ¬ ∀ v, v ∉ ws → y' v = y v := by
            intro h
            have := h w hw
            rw [hyw', hyw] at this
            exact absurd this (by decide)
          have hB : ∀ v, v ∉ ws → y' v = Function.update y w true v := by
            intro v hv
            by_cases hvw : v = w
            · subst hvw
              rw [hyw', Function.update_self]
            · rw [Function.update_of_ne hvw]
              exact hC v (by simp [hvw, hv])
          rw [if_neg hA, if_pos hB, zero_add, smul_smul, mul_comm]
      · rw [if_neg hC]
        obtain ⟨v, hv, hne⟩ : ∃ v, v ∉ w :: ws ∧ y' v ≠ y v := by
          by_contra h
          apply hC
          intro v hv
          by_contra hne
          exact h ⟨v, hv, hne⟩
        have hvw : v ≠ w := fun h => hv (h ▸ List.mem_cons_self)
        have hvs : v ∉ ws := fun h => hv (List.mem_cons_of_mem w h)
        have hA : ¬ ∀ v, v ∉ ws → y' v = y v := fun h => hne (h v hvs)
        have hB : ¬ ∀ v, v ∉ ws → y' v = Function.update y w true v := fun h => by
          have := h v hvs
          rw [Function.update_of_ne hvw] at this
          exact hne this
        rw [if_neg hA, if_neg hB, add_zero, smul_zero]

end Had

/-! ### The wires and gates of `U_J` -/

section UJ

variable {k : ℕ}

/-- The `j`-th lowest wire of the second index. -/
def slotWire (σ : ℕ) (hσ : σ ≤ k) (j : Fin σ) : PR k :=
  ixPR k (Sum.inr ⟨j.val, lt_of_lt_of_le j.isLt hσ⟩)

/-- The wires of the boundary preparation: the orientation wire and the lowest `σ` wires of the
second index. -/
def hadWires (k σ : ℕ) (hσ : σ ≤ k) : List (PR k) :=
  oPR k :: (List.finRange σ).map (slotWire σ hσ)

/-- **The gates of `U_J`**: one Hadamard gate on every wire of `hadWires`. -/
def hadUJ (k σ : ℕ) (hσ : σ ≤ k) : List (Gate (PR k)) :=
  (hadWires k σ hσ).map hadGate

theorem slotWire_injective (σ : ℕ) (hσ : σ ≤ k) : Function.Injective (slotWire σ hσ) := by
  intro j j' h
  have h' := ixPR_injective k h
  simp only [Sum.inr.injEq, Fin.mk.injEq] at h'
  exact Fin.ext h'

theorem hadWires_nodup (σ : ℕ) (hσ : σ ≤ k) : (hadWires k σ hσ).Nodup := by
  refine List.nodup_cons.2 ⟨?_, (List.nodup_finRange σ).map (slotWire_injective σ hσ)⟩
  intro h
  obtain ⟨j, _, hj⟩ := List.mem_map.1 h
  exact ixPR_ne_o k _ hj

theorem hadUJ_ok (σ : ℕ) (hσ : σ ≤ k) : ∀ g ∈ hadUJ k σ hσ, GateOK 3 g := by
  intro g hg
  obtain ⟨w, _, rfl⟩ := List.mem_map.1 hg
  exact hadGate_ok w

theorem hadUJ_length (σ : ℕ) (hσ : σ ≤ k) : (hadUJ k σ hσ).length = σ + 1 := by
  simp [hadUJ, hadWires]

theorem mem_hadWires (σ : ℕ) (hσ : σ ≤ k) (v : PR k) :
    v ∈ hadWires k σ hσ ↔ v = oPR k ∨ ∃ j : Fin k, j.val < σ ∧ v = ixPR k (Sum.inr j) := by
  simp only [hadWires, List.mem_cons, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro (h | ⟨j, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨j.val, lt_of_lt_of_le j.isLt hσ⟩, j.isLt, rfl⟩
  · rintro (h | ⟨j, hj, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨j.val, hj⟩, rfl⟩

/-- The index words supported on the lowest `σ` bits. -/
def lowWord (σ : ℕ) (u : Fin σ → Bool) : Cfg (Fin k) :=
  fun i => if h : i.val < σ then u ⟨i.val, h⟩ else false

theorem exists_lowWord_iff (σ : ℕ) (d : Cfg (Fin k)) :
    (∃ u : Fin σ → Bool, d = lowWord σ u) ↔ ∀ i : Fin k, σ ≤ i.val → d i = false := by
  constructor
  · rintro ⟨u, rfl⟩ i hi
    simp [lowWord, show ¬ i.val < σ by omega]
  · intro h
    refine ⟨fun j => if hj : j.val < k then d ⟨j.val, hj⟩ else false, ?_⟩
    funext i
    by_cases hi : i.val < σ
    · simp [lowWord, hi]
    · simp only [lowWord, hi, dif_neg, not_false_eq_true]
      exact h i (by omega)

end UJ

/-! ### The zero-ancilla embedding -/

section Emb

variable {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ}

/-- The zero-ancilla embedding `|i⟩ ↦ |0, (i, 0)⟩` of the system index into the oriented edge
space. -/
def embQ (en : Cfg (Fin k) ≃ n) :
    EuclideanSpace ℂ n →L[ℂ] SparseEdgeMoments.OrientedSpace n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2
        (Sum.elim (fun e => if e.2 = zIdx en then v e.1 else 0) (fun _ => 0))
      map_add' := by
        intro v w
        ext e
        rcases e with e | e
        · by_cases h : e.2 = zIdx en <;> simp [h]
        · simp
      map_smul' := by
        intro c v
        ext e
        rcases e with e | e
        · by_cases h : e.2 = zIdx en <;> simp [h]
        · simp }

theorem embQ_apply_inl (en : Cfg (Fin k) ≃ n) (v : EuclideanSpace ℂ n) (e : n × n) :
    embQ en v (Sum.inl e) = if e.2 = zIdx en then v e.1 else 0 := rfl

theorem embQ_apply_inr (en : Cfg (Fin k) ≃ n) (v : EuclideanSpace ℂ n) (e : n × n) :
    embQ en v (Sum.inr e) = 0 := rfl

theorem embQ_single (en : Cfg (Fin k) ≃ n) (i : n) :
    embQ en (EuclideanSpace.single i 1) = EuclideanSpace.single (Sum.inl (i, zIdx en)) 1 := by
  ext e
  rcases e with ⟨i', j'⟩ | e
  · rw [embQ_apply_inl]
    by_cases hj : j' = zIdx en
    · by_cases hi : i' = i <;> simp [hi, hj]
    · simp [hj]
  · rw [embQ_apply_inr]
    simp

theorem embQ_adjoint_apply (en : Cfg (Fin k) ≃ n) (w : SparseEdgeMoments.OrientedSpace n)
    (i : n) : (((embQ en)†) w) i = w (Sum.inl (i, zIdx en)) := by
  have h1 := EuclideanSpace.inner_single_left i (1 : ℂ) (((embQ en)†) w)
  rw [adjoint_inner_right, embQ_single, EuclideanSpace.inner_single_left] at h1
  simpa using h1.symm

theorem embQ_isometry (en : Cfg (Fin k) ≃ n) : (embQ en)† ∘L embQ en = 1 := by
  ext v i
  rw [comp_apply, embQ_adjoint_apply, embQ_apply_inl]
  simp

theorem fixedBoundary_single_inl {s : ℕ} (slot : Fin s ↪ n) (i i' j' : n) :
    FixedLocatorConjugation.fixedBoundary slot (EuclideanSpace.single i 1) (Sum.inl (i', j')) =
      SparseEdgeMoments.boundaryWeight s * (if i' = i ∧ (∃ m, slot m = j') then 1 else 0) := by
  simp only [FixedLocatorConjugation.fixedBoundary, smul_apply, PiLp.smul_apply,
    SparseEdgeMoments.stack_inl, SparseEdgeMoments.rowIncidence_apply,
    SparseSlotStates.selected, Finset.mem_image, Finset.mem_univ, true_and, smul_eq_mul]
  by_cases hi : i' = i <;> by_cases hj : ∃ m, slot m = j' <;> simp [hi, hj]

theorem fixedBoundary_single_inr {s : ℕ} (slot : Fin s ↪ n) (i i' j' : n) :
    FixedLocatorConjugation.fixedBoundary slot (EuclideanSpace.single i 1) (Sum.inr (i', j')) =
      SparseEdgeMoments.boundaryWeight s * (if i' = i ∧ (∃ m, slot m = j') then 1 else 0) := by
  simp only [FixedLocatorConjugation.fixedBoundary, smul_apply, PiLp.smul_apply,
    SparseEdgeMoments.stack_inr, SparseEdgeMoments.rowIncidence_apply,
    SparseSlotStates.selected, Finset.mem_image, Finset.mem_univ, true_and, smul_eq_mul]
  by_cases hi : i' = i <;> by_cases hj : ∃ m, slot m = j' <;> simp [hi, hj]

end Emb

/-! ### The boundary on clean ancillas -/

section Lift

variable {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

omit [CompleteSpace R] in
theorem iota0_bas (c : Cfg (Fin k)) (q : R) :
    iota0 (a := k + 1) (P := Reg (Fin k) R) (bas c q) = bas (fun _ => false) (bas c q) := by
  apply PiLp.ext
  intro x
  rw [iota0_apply, bas_apply]

omit [CompleteSpace R] in
theorem fl_bas {W S : Type*} [Fintype W] [DecidableEq W] [Fintype S] [DecidableEq S]
    (x : Cfg W) (c : Cfg S) (q : R) :
    fl (bas x (bas c q) : Reg W (Reg S R)) = bas (Sum.elim x c) q := by
  apply PiLp.ext
  intro y
  change flat W S R (bas x (bas c q)) y = _
  rw [flat_apply, bas_apply, bas_apply]
  have hy : (y = Sum.elim x c) ↔
      ((fun w => y (Sum.inl w)) = x ∧ (fun s => y (Sum.inr s)) = c) := by
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      funext v
      rcases v with w | s
      · exact congrFun h1 w
      · exact congrFun h2 s
  by_cases h1 : (fun w => y (Sum.inl w)) = x
  · rw [if_pos h1, bas_apply]
    by_cases h2 : (fun s => y (Sum.inr s)) = c
    · rw [if_pos h2, if_pos (hy.2 ⟨h1, h2⟩)]
    · rw [if_neg h2, if_neg (fun h => h2 (hy.1 h).2)]
  · rw [if_neg h1, if_neg (fun h => h1 (hy.1 h).1)]
    simp

omit [Fintype n] [DecidableEq n] in
theorem phiPR_zero (en : Cfg (Fin k) ≃ n) (c : Cfg (Fin k)) :
    phiPR en (Sum.elim (fun _ => false) c) = Sum.inl (en c, zIdx en) := rfl

/-- **Clean ancillas.** Compressing a lifted operator of the oriented edge space to clean
ancillas is the system lift of its compression by the zero-ancilla embedding. -/
theorem iota0_unconj_qlift (en : Cfg (Fin k) ≃ n)
    (B : SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n) :
    (iota0 (a := k + 1) (P := Reg (Fin k) R))† ∘L unconj (qlift (R := R) (phiPR en) B) ∘L
        iota0 = qlift en ((embQ en)† ∘L B ∘L embQ en) := by
  apply ext_bas_clm
  intro c q
  apply PiLp.ext
  intro c'
  rw [comp_apply, comp_apply, iota0_adjoint_apply, iota0_bas, qlift_bas_apply]
  change (flat (Fin (k + 1)) (Fin k) R).symm
    (qlift (R := R) (phiPR en) B (fl (bas (fun _ => false) (bas c q)))) _ c' = _
  rw [flat_symm_apply, fl_bas, qlift_bas_apply, phiPR_zero, phiPR_zero, comp_apply, comp_apply,
    embQ_adjoint_apply, embQ_single]

/-- The boundary map `J E†` of the oriented edge space. -/
def bdryP {s : ℕ} (slot : Fin s ↪ n) (en : Cfg (Fin k) ≃ n) :
    SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n :=
  FixedLocatorConjugation.fixedBoundary slot ∘L (embQ en)†

theorem bdryP_embQ {s : ℕ} (slot : Fin s ↪ n) (en : Cfg (Fin k) ≃ n) :
    bdryP slot en ∘L embQ en = FixedLocatorConjugation.fixedBoundary slot := by
  rw [bdryP, comp_assoc, embQ_isometry, one_def, comp_id]

theorem embQ_adjoint_single (en : Cfg (Fin k) ≃ n) (i : n) :
    ((embQ en)†) (EuclideanSpace.single (Sum.inl (i, zIdx en)) 1) =
      EuclideanSpace.single i 1 := by
  ext i'
  rw [embQ_adjoint_apply]
  by_cases h : i' = i <;> simp [h]

theorem off_hadWires_iff (σ : ℕ) (hσ : σ ≤ k) (c : Cfg (Fin k)) (y' : Cfg (PR k)) :
    (∀ v, v ∉ hadWires k σ hσ → y' v = Sum.elim (fun _ => false) c v) ↔
      ((fun j => y' (ixPR k (Sum.inl j))) = c ∧
        ∀ i : Fin k, σ ≤ i.val → y' (ixPR k (Sum.inr i)) = false) := by
  constructor
  · intro h
    refine ⟨funext fun j => ?_, fun i hi => ?_⟩
    · refine h (Sum.inr j) (fun hm => ?_)
      rcases (mem_hadWires σ hσ _).1 hm with h' | ⟨j', _, h'⟩
      · simp [oPR] at h'
      · simp [ixPR] at h'
    · refine h _ (fun hm => ?_)
      rcases (mem_hadWires σ hσ _).1 hm with h' | ⟨j', hj', h'⟩
      · exact ixPR_ne_o k _ h'
      · have := ixPR_injective k h'
        simp only [Sum.inr.injEq] at this
        subst this
        omega
  · rintro ⟨h1, h2⟩ v hv
    rcases v with i | j
    · obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
      · exact absurd ((mem_hadWires σ hσ _).2 (Or.inl rfl)) hv
      · by_cases hj : j.val < σ
        · exact absurd ((mem_hadWires σ hσ _).2 (Or.inr ⟨j, hj, rfl⟩)) hv
        · exact h2 j (by omega)
    · exact congrFun h1 j

theorem hamp_pow (σ : ℕ) :
    hamp ^ (σ + 1) = SparseEdgeMoments.boundaryWeight (2 ^ σ) := by
  unfold hamp SparseEdgeMoments.boundaryWeight
  rw [← Complex.ofReal_pow]
  congr 1
  have h2 : (2 : ℝ) * ((2 ^ σ : ℕ) : ℝ) = (Real.sqrt 2 ^ (σ + 1)) ^ 2 := by
    rw [← pow_mul, mul_comm (σ + 1) 2, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast
    ring
  rw [h2, Real.sqrt_sq (by positivity), inv_pow]

/-- **`U_J` on clean ancillas** is the lift of `J E†`, when `s = 2^σ` and the slots are the
index words supported on the lowest `σ` bits. -/
theorem hadUJ_iota0 (σ : ℕ) (hσ : σ ≤ k) (en : Cfg (Fin k) ≃ n) {s : ℕ} (slot : Fin s ↪ n)
    (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u)) :
    UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R) =
      unconj (qlift (R := R) (phiPR en) (bdryP slot en)) ∘L iota0 := by
  apply ext_bas_clm'
  intro c q
  rw [comp_apply, comp_apply, iota0_bas]
  change unfl (gRun (Q := R) (hadUJ k σ hσ) (fl (bas (fun _ => false) (bas c q)))) =
    unfl (qlift (R := R) (phiPR en) (bdryP slot en) (fl (bas (fun _ => false) (bas c q))))
  rw [fl_bas]
  congr 1
  have hclean : ∀ w ∈ hadWires k σ hσ, Sum.elim (fun _ => false) c w = false := by
    intro w hw
    rcases (mem_hadWires σ hσ w).1 hw with rfl | ⟨j, _, rfl⟩
    · rfl
    · rfl
  apply PiLp.ext
  intro y'
  rw [hadUJ, gRun_hadList_bas _ (hadWires_nodup σ hσ) _ hclean q y', qlift_bas_apply,
    phiPR_zero, bdryP, comp_apply, embQ_adjoint_single]
  have hlen : (hadWires k σ hσ).length = σ + 1 := by simp [hadWires]
  rw [hlen, hamp_pow, ← hs]
  have hcond : (en (fun j => y' (ixPR k (Sum.inl j))) = en c ∧
      ∃ m, slot m = en (fun j => y' (ixPR k (Sum.inr j)))) ↔
      ((fun j => y' (ixPR k (Sum.inl j))) = c ∧
        ∀ i : Fin k, σ ≤ i.val → y' (ixPR k (Sum.inr i)) = false) := by
    rw [en.injective.eq_iff, hrange, ← exists_lowWord_iff]
    simp only [en.injective.eq_iff]
  have key : FixedLocatorConjugation.fixedBoundary slot (EuclideanSpace.single (en c) 1)
      (phiPR en y') = SparseEdgeMoments.boundaryWeight s *
        (if (fun j => y' (ixPR k (Sum.inl j))) = c ∧
          ∀ i : Fin k, σ ≤ i.val → y' (ixPR k (Sum.inr i)) = false then 1 else 0) := by
    rw [phiPR_apply]
    by_cases ho : y' (oPR k) = true
    · rw [if_pos ho, phiE_apply, fixedBoundary_single_inr]
      exact congrArg _ (if_congr hcond rfl rfl)
    · rw [if_neg ho, phiE_apply, fixedBoundary_single_inl]
      exact congrArg _ (if_congr hcond rfl rfl)
  rw [key]
  by_cases hA : (fun j => y' (ixPR k (Sum.inl j))) = c ∧
      ∀ i : Fin k, σ ≤ i.val → y' (ixPR k (Sum.inr i)) = false
  · rw [if_pos ((off_hadWires_iff σ hσ c y').2 hA), if_pos hA, mul_one]
  · rw [if_neg (fun h => hA ((off_hadWires_iff σ hσ c y').1 h)), if_neg hA, mul_zero, zero_smul]

theorem hadUJ_iota0_adjoint (σ : ℕ) (hσ : σ ≤ k) (en : Cfg (Fin k) ≃ n) {s : ℕ}
    (slot : Fin s ↪ n) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u)) :
    (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R))† =
      (iota0 (a := k + 1) (P := Reg (Fin k) R))† ∘L
        unconj (qlift (R := R) (phiPR en) ((bdryP slot en)†)) := by
  rw [hadUJ_iota0 σ hσ en slot hs hrange, adjoint_comp, ← unconj_adjoint, ← qlift_adjoint]

theorem unconj_qlift_sandwich (en : Cfg (Fin k) ≃ n) {s : ℕ} (slot : Fin s ↪ n)
    (A : SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n) :
    unconj (qlift (R := R) (phiPR en) ((bdryP slot en)†)) ∘L
      (unconj (qlift (R := R) (phiPR en) A) ∘L
        (unconj (qlift (R := R) (phiPR en) (bdryP slot en)) ∘L
          iota0 (a := k + 1) (P := Reg (Fin k) R))) =
      unconj (qlift (R := R) (phiPR en) ((bdryP slot en)† ∘L A ∘L bdryP slot en)) ∘L
        iota0 (a := k + 1) (P := Reg (Fin k) R) := by
  rw [qlift_comp, qlift_comp, unconj_comp, unconj_comp]
  simp only [comp_assoc]

theorem iota0_bdryP_compress (en : Cfg (Fin k) ≃ n) {s : ℕ} (slot : Fin s ↪ n)
    (A : SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n) :
    (iota0 (a := k + 1) (P := Reg (Fin k) R))† ∘L
      (unconj (qlift (R := R) (phiPR en) ((bdryP slot en)† ∘L A ∘L bdryP slot en)) ∘L
        iota0 (a := k + 1) (P := Reg (Fin k) R)) =
      qlift en ((FixedLocatorConjugation.fixedBoundary slot)† ∘L A ∘L
        FixedLocatorConjugation.fixedBoundary slot) := by
  rw [iota0_unconj_qlift, ← bdryP_embQ slot en, adjoint_comp]
  simp only [comp_assoc]

/-- **The lifted boundary.** On clean ancillas, `(U_J ι₀)† Â (U_J ι₀)` is the system lift of
`J† A J`, for every operator `A` of the oriented edge space and its lift `Â`. -/
theorem boundary_lift (σ : ℕ) (hσ : σ ≤ k) (en : Cfg (Fin k) ≃ n) {s : ℕ} (slot : Fin s ↪ n)
    (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (A : SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n) :
    (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R))† ∘L
        unconj (qlift (R := R) (phiPR en) A) ∘L
          (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R)) =
      qlift en ((FixedLocatorConjugation.fixedBoundary slot)† ∘L A ∘L
        FixedLocatorConjugation.fixedBoundary slot) := by
  rw [hadUJ_iota0_adjoint σ hσ en slot hs hrange, hadUJ_iota0 σ hσ en slot hs hrange,
    comp_assoc, unconj_qlift_sandwich, iota0_bdryP_compress]

end Lift

end

end SparseHamiltonian.GateBinary
