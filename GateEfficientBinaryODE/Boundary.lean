import GateEfficientBinaryODE.Decoder

/-!
# The four-sector boundary preparation `U_J` from Hadamard gates

The boundary of the four sectors (`bdry4`) maps the system index `i` to the uniform
superposition `(8s)^{-1/2} ∑_{p, o, t, m} |p, o, t, (i, slot m)⟩` over the parts, the
orientations, the tags and the `s` slots. When `s = 2^σ` and the slots are exactly the index
words supported on the lowest `σ` bits, it is prepared from clean ancillas by Hadamard gates on
the orientation, the tag and the part wire and on the lowest `σ` wires of the second index
(`hadUJ4`, `σ + 3` gates).

* `embQ4`: the zero-ancilla embedding `|i⟩ ↦ |0, 0, (i, 0)⟩` (Hamiltonian part, orientation `0`,
  tag `0`); `iota0_unconj_qlift4`: compressing a lifted four-sector operator to clean ancillas is
  the system lift of its compression by `embQ4`;
* `hadUJ4_iota0`: `U_J ι₀` is the lift of `bdry4 · embQ4†` on clean ancillas;
* `boundary_lift4`: `(U_J ι₀)† Â (U_J ι₀)` is the system lift of `bdry4† A bdry4`, for every
  four-sector operator `A` and its lift `Â`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary
open SparseHamiltonian.GateCircuit.Sim (iota0 iota0_apply iota0_adjoint_apply)
open SparseHamiltonian.OracleCircuit
open NativeSparseBlockEncoding (Data)
open scoped InnerProduct

/-! ### The wires and gates of `U_J` -/

section UJ

variable {k : ℕ}

/-- The `j`-th lowest wire of the second index. -/
def slotWire4 (σ : ℕ) (hσ : σ ≤ k) (j : Fin σ) : PR4 k :=
  ix4 k (Sum.inr ⟨j.val, lt_of_lt_of_le j.isLt hσ⟩)

/-- The wires of the boundary preparation: orientation, tag, part and the lowest `σ` wires of the
second index. -/
def hadWires4 (k σ : ℕ) (hσ : σ ≤ k) : List (PR4 k) :=
  oW k :: tW k :: pW k :: (List.finRange σ).map (slotWire4 σ hσ)

/-- **The gates of `U_J`**: one Hadamard gate on every wire of `hadWires4`. -/
def hadUJ4 (k σ : ℕ) (hσ : σ ≤ k) : List (Gate (PR4 k)) :=
  (hadWires4 k σ hσ).map hadGate

theorem slotWire4_injective (σ : ℕ) (hσ : σ ≤ k) : Function.Injective (slotWire4 σ hσ) := by
  intro j j' h
  have h' := ix4_injective k h
  simp only [Sum.inr.injEq, Fin.mk.injEq] at h'
  exact Fin.ext h'

theorem hadWires4_nodup (σ : ℕ) (hσ : σ ≤ k) : (hadWires4 k σ hσ).Nodup := by
  have hs : ((List.finRange σ).map (slotWire4 σ hσ)).Nodup :=
    (List.nodup_finRange σ).map (slotWire4_injective σ hσ)
  have hix : ∀ w ∈ (List.finRange σ).map (slotWire4 σ hσ), ∃ e, w = ix4 k e := by
    intro w hw
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hw
    exact ⟨_, rfl⟩
  refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, hs⟩⟩⟩
  · simp only [List.mem_cons, not_or]
    refine ⟨oW_ne_tW, oW_ne_pW, fun h => ?_⟩
    obtain ⟨e, he⟩ := hix _ h
    exact ix4_ne_oW e he.symm
  · simp only [List.mem_cons, not_or]
    refine ⟨tW_ne_pW, fun h => ?_⟩
    obtain ⟨e, he⟩ := hix _ h
    exact ix4_ne_tW e he.symm
  · intro h
    obtain ⟨e, he⟩ := hix _ h
    exact ix4_ne_pW e he.symm

theorem hadUJ4_ok (σ : ℕ) (hσ : σ ≤ k) : ∀ g ∈ hadUJ4 k σ hσ, GateOK 3 g := by
  intro g hg
  obtain ⟨w, _, rfl⟩ := List.mem_map.1 hg
  exact hadGate_ok w

theorem hadUJ4_length (σ : ℕ) (hσ : σ ≤ k) : (hadUJ4 k σ hσ).length = σ + 3 := by
  simp [hadUJ4, hadWires4]

theorem mem_hadWires4 (σ : ℕ) (hσ : σ ≤ k) (v : PR4 k) :
    v ∈ hadWires4 k σ hσ ↔
      v = oW k ∨ v = tW k ∨ v = pW k ∨ ∃ j : Fin k, j.val < σ ∧ v = ix4 k (Sum.inr j) := by
  simp only [hadWires4, List.mem_cons, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro (h | h | h | ⟨j, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨⟨j.val, lt_of_lt_of_le j.isLt hσ⟩, j.isLt, rfl⟩))
  · rintro (h | h | h | ⟨j, hj, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨⟨j.val, hj⟩, rfl⟩))

end UJ

/-! ### The zero-ancilla embedding -/

section Emb

variable {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ}

/-- The zero-ancilla embedding `|i⟩ ↦ |0, 0, (i, 0)⟩` of the system index into the four-sector
space. -/
def embQ4 (en : Cfg (Fin k) ≃ n) : EuclideanSpace ℂ n →L[ℂ] Space4 n :=
  (flat4 (n := n)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    LinearMap.toContinuousLinearMap
      { toFun := fun v => WithLp.toLp 2 (fun z : I4 n =>
          if z.1 = false ∧ z.2.1 = false then
            Sum.elim (fun e : n × n => if e.2 = zIdx en then v e.1 else 0) (fun _ => 0) z.2.2
          else 0)
        map_add' := by
          intro v w
          ext ⟨p, o, e⟩
          rcases e with e | e
          · by_cases h : p = false ∧ o = false <;> by_cases h' : e.2 = zIdx en <;> simp [h, h']
          · by_cases h : p = false ∧ o = false <;> simp [h]
        map_smul' := by
          intro c v
          ext ⟨p, o, e⟩
          rcases e with e | e
          · by_cases h : p = false ∧ o = false <;> by_cases h' : e.2 = zIdx en <;> simp [h, h']
          · by_cases h : p = false ∧ o = false <;> simp [h] }

theorem embQ4_apply (en : Cfg (Fin k) ≃ n) (v : EuclideanSpace ℂ n) (p o : Bool)
    (e : (n × n) ⊕ (n × n)) :
    embQ4 en v p o e = if p = false ∧ o = false then
      Sum.elim (fun e : n × n => if e.2 = zIdx en then v e.1 else 0) (fun _ => 0) e else 0 := rfl

theorem embQ4_single (en : Cfg (Fin k) ≃ n) (i : n) :
    embQ4 en (EuclideanSpace.single i 1) =
      (flat4 (n := n)).symm (EuclideanSpace.single (false, false, Sum.inl (i, zIdx en)) 1) := by
  apply PiLp.ext
  intro p
  apply PiLp.ext
  intro o
  apply PiLp.ext
  intro e
  rw [embQ4_apply, flat4_symm_single]
  rcases e with ⟨i', j'⟩ | e
  · by_cases hpo : p = false ∧ o = false
    · obtain ⟨rfl, rfl⟩ := hpo
      by_cases hj : j' = zIdx en
      · by_cases hi : i' = i <;> simp [hi, hj]
      · simp [hj]
    · rw [if_neg hpo, if_neg]
      intro h
      simp only [Prod.mk.injEq] at h
      exact hpo ⟨h.1, h.2.1⟩
  · simp

theorem embQ4_adjoint_apply (en : Cfg (Fin k) ≃ n) (w : Space4 n) (i : n) :
    (((embQ4 en)†) w) i = w false false (Sum.inl (i, zIdx en)) := by
  have h1 := EuclideanSpace.inner_single_left i (1 : ℂ) (((embQ4 en)†) w)
  rw [adjoint_inner_right, embQ4_single] at h1
  have h2 : inner ℂ ((flat4 (n := n)).symm
      (EuclideanSpace.single (false, false, Sum.inl (i, zIdx en)) 1)) w =
      inner ℂ (EuclideanSpace.single ((false, false, Sum.inl (i, zIdx en)) : I4 n) (1 : ℂ))
        (flat4 w) := by
    rw [← LinearIsometryEquiv.inner_map_map flat4, LinearIsometryEquiv.apply_symm_apply]
  rw [h2, EuclideanSpace.inner_single_left, flat4_apply] at h1
  simpa using h1.symm

theorem embQ4_adjoint_single (en : Cfg (Fin k) ≃ n) (i : n) :
    ((embQ4 en)†) ((flat4 (n := n)).symm
      (EuclideanSpace.single (false, false, Sum.inl (i, zIdx en)) 1)) =
      EuclideanSpace.single i 1 := by
  ext i'
  rw [embQ4_adjoint_apply, flat4_symm_single]
  by_cases h : i' = i <;> simp [h]

theorem embQ4_isometry (en : Cfg (Fin k) ≃ n) : (embQ4 en)† ∘L embQ4 en = 1 := by
  ext v i
  rw [comp_apply, embQ4_adjoint_apply, embQ4_apply]
  simp

end Emb

/-! ### The boundary on clean ancillas -/

section Lift

variable {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

omit [CompleteSpace R] in
theorem iota0_bas4 (c : Cfg (Fin k)) (q : R) :
    iota0 (a := k + 3) (P := Reg (Fin k) R) (bas c q) = bas (fun _ => false) (bas c q) := by
  apply PiLp.ext
  intro x
  rw [iota0_apply, bas_apply]

omit [Fintype n] [DecidableEq n] in
theorem phi4_zero (en : Cfg (Fin k) ≃ n) (c : Cfg (Fin k)) :
    phi4 en (Sum.elim (fun _ => false) c) = (false, false, Sum.inl (en c, zIdx en)) := rfl

/-- **Clean ancillas.** Compressing a lifted four-sector operator to clean ancillas is the
system lift of its compression by the zero-ancilla embedding. -/
theorem iota0_unconj_qlift4 (en : Cfg (Fin k) ≃ n) (B : Space4 n →L[ℂ] Space4 n) :
    (iota0 (a := k + 3) (P := Reg (Fin k) R))† ∘L unconj (qlift4 (R := R) en B) ∘L
        iota0 = qlift en ((embQ4 en)† ∘L B ∘L embQ4 en) := by
  apply ext_bas_clm
  intro c q
  apply PiLp.ext
  intro c'
  rw [comp_apply, comp_apply, iota0_adjoint_apply, iota0_bas4, qlift_bas_apply]
  change (flat (Fin (k + 3)) (Fin k) R).symm
    (qlift4 (R := R) en B (fl (bas (fun _ => false) (bas c q)))) _ c' = _
  rw [flat_symm_apply, fl_bas, qlift4_bas_apply, phi4_zero, comp_apply, comp_apply,
    embQ4_adjoint_apply, embQ4_single]
  rfl

/-- The boundary map `bdry4 E†` of the four-sector space. -/
def bdryP4 {X Z : Type*} {s : ℕ} (D : Data X n Z s) (en : Cfg (Fin k) ≃ n) :
    Space4 n →L[ℂ] Space4 n :=
  bdry4 D ∘L (embQ4 en)†

theorem bdryP4_embQ4 {X Z : Type*} {s : ℕ} (D : Data X n Z s) (en : Cfg (Fin k) ≃ n) :
    bdryP4 D en ∘L embQ4 en = bdry4 D := by
  rw [bdryP4, comp_assoc, embQ4_isometry, one_def, comp_id]

theorem off_hadWires4_iff (σ : ℕ) (hσ : σ ≤ k) (c : Cfg (Fin k)) (y' : Cfg (PR4 k)) :
    (∀ v, v ∉ hadWires4 k σ hσ → y' v = Sum.elim (fun _ => false) c v) ↔
      ((fun j => y' (ix4 k (Sum.inl j))) = c ∧
        ∀ i : Fin k, σ ≤ i.val → y' (ix4 k (Sum.inr i)) = false) := by
  constructor
  · intro h
    refine ⟨funext fun j => ?_, fun i hi => ?_⟩
    · refine h (Sum.inr j) (fun hm => ?_)
      rcases (mem_hadWires4 σ hσ _).1 hm with h' | h' | h' | ⟨j', _, h'⟩
      · simp [oW] at h'
      · simp [tW] at h'
      · simp [pW] at h'
      · simp [ix4] at h'
    · refine h _ (fun hm => ?_)
      rcases (mem_hadWires4 σ hσ _).1 hm with h' | h' | h' | ⟨j', hj', h'⟩
      · exact ix4_ne_oW _ h'
      · exact ix4_ne_tW _ h'
      · exact ix4_ne_pW _ h'
      · have := ix4_injective k h'
        simp only [Sum.inr.injEq] at this
        subst this
        omega
  · rintro ⟨h1, h2⟩ v hv
    rcases v with ⟨i, hi⟩ | j
    · rcases i with _ | _ | _ | i
      · exact absurd ((mem_hadWires4 σ hσ _).2 (Or.inl rfl)) hv
      · exact absurd ((mem_hadWires4 σ hσ _).2 (Or.inr (Or.inl rfl))) hv
      · exact absurd ((mem_hadWires4 σ hσ _).2 (Or.inr (Or.inr (Or.inl rfl)))) hv
      · by_cases hj : i < σ
        · exact absurd ((mem_hadWires4 σ hσ _).2
            (Or.inr (Or.inr (Or.inr ⟨⟨i, by omega⟩, hj, rfl⟩)))) hv
        · exact h2 ⟨i, by omega⟩ (by simp; omega)
    · exact congrFun h1 j

theorem hamp_pow4 (σ : ℕ) :
    hamp ^ (σ + 3) = ((Real.sqrt (1 / 2) : ℝ) : ℂ) *
      SparseEdgeMoments.boundaryWeight (2 * 2 ^ σ) := by
  unfold hamp SparseEdgeMoments.boundaryWeight
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
  congr 1
  have h2 : Real.sqrt (2 ^ (σ + 3)) = Real.sqrt 2 ^ (σ + 3) := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity), ← mul_pow,
      Real.mul_self_sqrt (by norm_num)]
  have h3 : Real.sqrt (1 / 2) * (Real.sqrt (2 * ((2 * 2 ^ σ : ℕ) : ℝ)))⁻¹ =
      (Real.sqrt (2 ^ (σ + 3)))⁻¹ := by
    rw [← Real.sqrt_inv, ← Real.sqrt_mul (by norm_num), ← Real.sqrt_inv]
    congr 1
    push_cast
    rw [pow_add]
    field_simp
  rw [h3, h2, inv_pow]

theorem fixedBoundary4_single {s : ℕ} (slot : Fin s ↪ n) (i : n) (o : Bool) (i' j' : n)
    (t : Bool) :
    ODETaggedLocators.fixedBoundary slot (EuclideanSpace.single i 1) o
        (if t then Sum.inr (i', j') else Sum.inl (i', j')) =
      SparseEdgeMoments.boundaryWeight (2 * s) *
        (if i' = i ∧ (∃ m, slot m = j') then 1 else 0) := by
  have hsel : ∀ a, SparseSlotStates.selected (fun _ : n => (slot : Fin s → n)) a j' ↔
      ∃ m, slot m = j' := by
    intro a
    simp [SparseSlotStates.selected]
  cases o <;> cases t <;>
    simp only [ODETaggedLocators.fixedBoundary, smul_apply, PiLp.smul_apply,
      ODETaggedMoments.pair_false, ODETaggedMoments.pair_true, ODETaggedLocators.fixedFrame,
      SparseEdgeMoments.stack_inl, SparseEdgeMoments.stack_inr,
      SparseEdgeMoments.rowIncidence_apply, smul_eq_mul, Bool.false_eq_true, if_false,
      if_true] <;>
    by_cases hi : i' = i <;> by_cases hj : ∃ m, slot m = j' <;> simp [hi, hj, hsel]

/-- **`U_J` on clean ancillas** is the lift of `bdry4 E†`, when `s = 2^σ` and the slots are the
index words supported on the lowest `σ` bits. -/
theorem hadUJ4_iota0 {X Z : Type*} {s : ℕ} (D : Data X n Z s) (σ : ℕ) (hσ : σ ≤ k)
    (en : Cfg (Fin k) ≃ n) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u)) :
    UJop (R := R) (hadUJ4 k σ hσ) ∘L iota0 (a := k + 3) (P := Reg (Fin k) R) =
      unconj (qlift4 (R := R) en (bdryP4 D en)) ∘L iota0 := by
  apply ext_bas_clm'
  intro c q
  rw [comp_apply, comp_apply, iota0_bas4, UJop, unconj, comp_apply, comp_apply, comp_apply,
    comp_apply, fl_bas]
  congr 1
  have hclean : ∀ w ∈ hadWires4 k σ hσ, Sum.elim (fun _ => false) c w = false := by
    intro w hw
    rcases (mem_hadWires4 σ hσ w).1 hw with rfl | rfl | rfl | ⟨j, _, rfl⟩ <;> rfl
  apply PiLp.ext
  intro y'
  rw [hadUJ4, gRun_hadList_bas _ (hadWires4_nodup σ hσ) _ hclean q y', qlift4_bas_apply,
    phi4_zero, bdryP4, comp_apply, embQ4_adjoint_single]
  have hlen : (hadWires4 k σ hσ).length = σ + 3 := by simp [hadWires4]
  rw [hlen, hamp_pow4, ← hs]
  have hcond : (en (fun j => y' (ix4 k (Sum.inl j))) = en c ∧
      ∃ m, D.slot m = en (fun j => y' (ix4 k (Sum.inr j)))) ↔
      ((fun j => y' (ix4 k (Sum.inl j))) = c ∧
        ∀ i : Fin k, σ ≤ i.val → y' (ix4 k (Sum.inr i)) = false) := by
    rw [en.injective.eq_iff, hrange, ← exists_lowWord_iff]
    simp only [en.injective.eq_iff]
  have key : bdry4 D (EuclideanSpace.single (en c) 1) (y' (pW k)) (y' (oW k)) (te en y') =
      ((Real.sqrt (1 / 2) : ℝ) : ℂ) * (SparseEdgeMoments.boundaryWeight (2 * s) *
        (if (fun j => y' (ix4 k (Sum.inl j))) = c ∧
          ∀ i : Fin k, σ ≤ i.val → y' (ix4 k (Sum.inr i)) = false then 1 else 0)) := by
    simp only [bdry4, WeightedClock.boundary_apply, PiLp.smul_apply, smul_eq_mul]
    congr 1
    unfold te
    have h := fixedBoundary4_single D.slot (en c) (y' (oW k))
      (phiE en (fun e => y' (ix4 k e))).1 (phiE en (fun e => y' (ix4 k e))).2 (y' (tW k))
    rw [Prod.mk.eta] at h
    rw [show ODEFixedTaggedMoments.boundary D = ODETaggedLocators.fixedBoundary D.slot from rfl,
      h, phiE_apply]
    exact congrArg _ (if_congr hcond rfl rfl)
  rw [key, ← mul_assoc]
  by_cases hA : (fun j => y' (ix4 k (Sum.inl j))) = c ∧
      ∀ i : Fin k, σ ≤ i.val → y' (ix4 k (Sum.inr i)) = false
  · rw [if_pos ((off_hadWires4_iff σ hσ c y').2 hA), if_pos hA, mul_one]
  · rw [if_neg (fun h => hA ((off_hadWires4_iff σ hσ c y').1 h)), if_neg hA, mul_zero,
      zero_smul]

/-- **The lifted boundary.** On clean ancillas, `(U_J ι₀)† Â (U_J ι₀)` is the system lift of
`bdry4† A bdry4`, for every four-sector operator `A` and its lift `Â`. -/
theorem boundary_lift4 {X Z : Type*} {s : ℕ} (D : Data X n Z s) (σ : ℕ) (hσ : σ ≤ k)
    (en : Cfg (Fin k) ≃ n) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (A : Space4 n →L[ℂ] Space4 n) :
    (UJop (R := R) (hadUJ4 k σ hσ) ∘L iota0 (a := k + 3) (P := Reg (Fin k) R))† ∘L
        unconj (qlift4 (R := R) en A) ∘L
          (UJop (R := R) (hadUJ4 k σ hσ) ∘L iota0 (a := k + 3) (P := Reg (Fin k) R)) =
      qlift en ((bdry4 D)† ∘L A ∘L bdry4 D) := by
  rw [hadUJ4_iota0 D σ hσ en hs hrange, adjoint_comp, ← unconj_adjoint, ← qlift4_adjoint]
  have h1 : unconj (qlift4 (R := R) en ((bdryP4 D en)†)) ∘L
      (unconj (qlift4 (R := R) en A) ∘L
        (unconj (qlift4 (R := R) en (bdryP4 D en)) ∘L
          iota0 (a := k + 3) (P := Reg (Fin k) R))) =
      unconj (qlift4 (R := R) en ((bdryP4 D en)† ∘L A ∘L bdryP4 D en)) ∘L
        iota0 (a := k + 3) (P := Reg (Fin k) R) := by
    rw [qlift4_comp, qlift4_comp, unconj_comp, unconj_comp]
    simp only [comp_assoc]
  rw [comp_assoc, h1, iota0_unconj_qlift4, ← bdryP4_embQ4 D en, adjoint_comp]
  simp only [comp_assoc]

end Lift

end

end SparseHamiltonian.GateBinaryODE
