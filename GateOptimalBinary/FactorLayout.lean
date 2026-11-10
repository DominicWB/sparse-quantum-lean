import GateOptimalBinary.Bounded

/-!
# The register of the signed factor

The signed factor `U_B` of the signed-factor regime (Section `gate:sec:native`, paragraph "A
stable constant-dimensional signed factor") acts on the oriented edge register of the bounded
regime and two more qubits, the success flag `f` and the sign `z`. With `k` system wires the factor
has `k + 3` ancilla wires (`GU k`, flat with the system wires): the ancillas `0, …, k` of the
bounded private register `GateBinary.PR k` (orientation wire `0`, second index `1, …, k`; `ιU`),
the flag `f = k + 1` (`fW`) and the sign `z = k + 2` (`zW`).

* `ι2`: the bounded register with clean flag and sign, `ψ ↦ ψ ⊗ |0⟩_f|0⟩_z`; an isometry
  (`ι2_isometry`); an operator on the bounded wires commutes with it (`localOp_ι2`); the clean
  embedding of the system register factors through it (`fl_iota0_ι2`);
* `diag_comm_localOp`: a diagonal operator commutes with an operator on wires it does not read;
  `diag_eq_localOp`: a diagonal operator reading only some wires acts on these wires;
  `conj_dg`: the flat form of `GateOptimalPrecision.dg`;
* `locU`: the local qubits `(f, o, z)` of the factor; `ι2_compress`: compressing an operator on
  the local qubits to clean flag and sign is the one-qubit operation on the orientation given by
  the `(f, z) = (0, 0)` block (`ff`).

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
open SparseHamiltonian.GateODE (put put_apply localOp_put bas_eq_put overwrite_apply_ι
  overwrite_apply_out)
open scoped InnerProduct

/-! ### Wires -/

/-- The flat register of the signed factor: `k + 3` ancilla wires and `k` system wires. -/
abbrev GU (k : ℕ) := Fin (k + 3) ⊕ Fin k

/-- The flag wire `f = k + 1`. -/
def fW (k : ℕ) : Fin (k + 3) := ⟨k + 1, by omega⟩

/-- The sign wire `z = k + 2`. -/
def zW (k : ℕ) : Fin (k + 3) := ⟨k + 2, by omega⟩

theorem fW_ne_zW (k : ℕ) : fW k ≠ zW k := by
  simp [fW, zW, Fin.ext_iff]

/-- The ancillas of the bounded private register among the ancillas of the factor. -/
def cU (k : ℕ) : Fin (k + 1) → Fin (k + 3) := Fin.castLE (by omega)

theorem cU_injective (k : ℕ) : Function.Injective (cU k) := Fin.castLE_injective _

@[simp] theorem cU_val (k : ℕ) (i : Fin (k + 1)) : (cU k i).val = i.val := rfl

theorem cU_ne_fW (k : ℕ) (i : Fin (k + 1)) : cU k i ≠ fW k := by
  intro h
  have := congrArg Fin.val h
  simp [fW] at this
  omega

theorem cU_ne_zW (k : ℕ) (i : Fin (k + 1)) : cU k i ≠ zW k := by
  intro h
  have := congrArg Fin.val h
  simp [zW] at this
  omega

/-- Every ancilla wire of the factor is a bounded ancilla, the flag or the sign. -/
theorem fin_cases_U (k : ℕ) (i : Fin (k + 3)) :
    (∃ i' : Fin (k + 1), i = cU k i') ∨ i = fW k ∨ i = zW k := by
  by_cases h : i.val < k + 1
  · exact Or.inl ⟨⟨i.val, h⟩, Fin.ext rfl⟩
  · right
    have : i.val = k + 1 ∨ i.val = k + 2 := by omega
    rcases this with h1 | h1
    · exact Or.inl (Fin.ext h1)
    · exact Or.inr (Fin.ext h1)

/-- The bounded private register inside the factor register. -/
def ιU (k : ℕ) : PR k → GU k := mapId (cU k)

theorem ιU_injective (k : ℕ) : Function.Injective (ιU k) := mapId_injective (cU_injective k)

/-- `ιU` as an embedding. -/
def ιUe (k : ℕ) : PR k ↪ GU k := ⟨ιU k, ιU_injective k⟩

@[simp] theorem ιU_inl (k : ℕ) (i : Fin (k + 1)) : ιU k (Sum.inl i) = Sum.inl (cU k i) := rfl

@[simp] theorem ιU_inr (k : ℕ) (j : Fin k) : ιU k (Sum.inr j) = Sum.inr j := rfl

theorem ιU_ne_f (k : ℕ) (p : PR k) : ιU k p ≠ Sum.inl (fW k) := by
  rcases p with i | j
  · intro h
    exact cU_ne_fW k i (Sum.inl_injective h)
  · simp

theorem ιU_ne_z (k : ℕ) (p : PR k) : ιU k p ≠ Sum.inl (zW k) := by
  rcases p with i | j
  · intro h
    exact cU_ne_zW k i (Sum.inl_injective h)
  · simp

/-- The wires outside the bounded register are the flag and the sign. -/
theorem out_ιU_iff (k : ℕ) (w : GU k) :
    (∀ p, ιU k p ≠ w) ↔ (w = Sum.inl (fW k) ∨ w = Sum.inl (zW k)) := by
  constructor
  · intro h
    rcases w with i | j
    · rcases fin_cases_U k i with ⟨i', rfl⟩ | rfl | rfl
      · exact absurd rfl (h (Sum.inl i'))
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact absurd rfl (h (Sum.inr j))
  · rintro (rfl | rfl) p
    · exact ιU_ne_f k p
    · exact ιU_ne_z k p

/-- The orientation wire of the factor register, the image of `GateBinary.oPR`. -/
theorem ιU_oPR (k : ℕ) : ιU k (oPR k) = Sum.inl 0 := rfl

/-! ### Clean flag and sign -/

/-- The configuration with bounded part `c` and clean flag and sign. -/
def extU {k : ℕ} (c : Cfg (PR k)) : Cfg (GU k) := overwrite (ιU k) (fun _ => false) c

theorem extU_ιU {k : ℕ} (c : Cfg (PR k)) (p : PR k) : extU c (ιU k p) = c p :=
  overwrite_apply_ι (ιU_injective k) _ c p

theorem extU_f {k : ℕ} (c : Cfg (PR k)) : extU c (Sum.inl (fW k)) = false :=
  overwrite_apply_out _ _ c _ (ιU_ne_f k)

theorem extU_z {k : ℕ} (c : Cfg (PR k)) : extU c (Sum.inl (zW k)) = false :=
  overwrite_apply_out _ _ c _ (ιU_ne_z k)

theorem extU_comp {k : ℕ} (c : Cfg (PR k)) : (fun p => extU c (ιU k p)) = c :=
  funext (extU_ιU c)

theorem extU_injective {k : ℕ} : Function.Injective (extU (k := k)) := by
  intro c c' h
  rw [← extU_comp c, ← extU_comp c', h]

/-- A configuration with clean flag and sign is the extension of its bounded part. -/
theorem eq_extU {k : ℕ} (y : Cfg (GU k)) (hf : y (Sum.inl (fW k)) = false)
    (hz : y (Sum.inl (zW k)) = false) : y = extU (fun p => y (ιU k p)) := by
  funext w
  by_cases hw : ∃ p, ιU k p = w
  · obtain ⟨p, rfl⟩ := hw
    rw [extU_ιU]
  · push Not at hw
    rcases (out_ιU_iff k w).1 hw with rfl | rfl
    · rw [extU_f, hf]
    · rw [extU_z, hz]

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The bounded register with clean flag and sign**: `ψ ↦ ψ ⊗ |0⟩_f |0⟩_z`. -/
def ι2 (k : ℕ) : Reg (PR k) R →L[ℂ] Reg (GU k) R :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Cfg (GU k) => R)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun y =>
      if y (Sum.inl (fW k)) = false ∧ y (Sum.inl (zW k)) = false then
        coord (fun p => y (ιU k p)) else 0)

omit [CompleteSpace R] in
theorem ι2_apply {k : ℕ} (ψ : Reg (PR k) R) (y : Cfg (GU k)) :
    ι2 k ψ y = if y (Sum.inl (fW k)) = false ∧ y (Sum.inl (zW k)) = false then
      ψ (fun p => y (ιU k p)) else 0 := by
  change (if y (Sum.inl (fW k)) = false ∧ y (Sum.inl (zW k)) = false then
    coord (fun p => y (ιU k p)) else 0) ψ = _
  split_ifs <;> rfl

omit [CompleteSpace R] in
theorem ι2_bas {k : ℕ} (c : Cfg (PR k)) (q : R) : ι2 k (bas c q) = bas (extU c) q := by
  apply PiLp.ext
  intro y
  rw [ι2_apply]
  simp only [bas_apply]
  by_cases h : y (Sum.inl (fW k)) = false ∧ y (Sum.inl (zW k)) = false
  · rw [if_pos h]
    by_cases hc : (fun p => y (ιU k p)) = c
    · rw [if_pos hc, if_pos]
      rw [eq_extU y h.1 h.2, hc]
    · rw [if_neg hc, if_neg]
      intro hy
      apply hc
      rw [hy]
      exact extU_comp c
  · rw [if_neg h, if_neg]
    intro hy
    apply h
    rw [hy]
    exact ⟨extU_f c, extU_z c⟩

theorem ι2_adjoint_apply {k : ℕ} (φ : Reg (GU k) R) (c : Cfg (PR k)) :
    (((ι2 k)†) φ) c = φ (extU c) := by
  apply ext_inner_right ℂ
  intro r
  rw [← inner_bas_right c r (((ι2 k)†) φ), adjoint_inner_left, ι2_bas, inner_bas_right]

theorem ι2_isometry (k : ℕ) : (ι2 (R := R) k)† ∘L ι2 k = 1 := by
  ext ψ c
  rw [comp_apply, ι2_adjoint_apply, ι2_apply, if_pos ⟨extU_f c, extU_z c⟩, extU_comp]
  rfl

omit [CompleteSpace R] in
/-- `ι2` places a vector at the outside configuration with clean flag and sign. -/
theorem ι2_eq_put {k : ℕ} (ψ : Reg (PR k) R) :
    ι2 k ψ = put (ιU k) (ιU_injective k) (fun _ => false) ψ := by
  apply PiLp.ext
  intro y
  rw [ι2_apply, put_apply]
  have hiff : (y (Sum.inl (fW k)) = false ∧ y (Sum.inl (zW k)) = false) ↔
      outPart (ιU k) y = outPart (ιU k) (fun _ => false) := by
    constructor
    · rintro ⟨hf, hz⟩
      funext ⟨w, hw⟩
      rcases (out_ιU_iff k w).1 hw with rfl | rfl
      · exact hf
      · exact hz
    · intro h
      exact ⟨congrFun h ⟨Sum.inl (fW k), ιU_ne_f k⟩, congrFun h ⟨Sum.inl (zW k), ιU_ne_z k⟩⟩
  by_cases h : y (Sum.inl (fW k)) = false ∧ y (Sum.inl (zW k)) = false
  · rw [if_pos h, if_pos (hiff.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]

/-- **An operator on the bounded wires** commutes with clean flag and sign. -/
theorem localOp_ι2 {k : ℕ} (T : Reg (PR k) R →L[ℂ] Reg (PR k) R) :
    localOp (ιU k) (ιU_injective k) (fun _ => T) ∘L ι2 k = ι2 k ∘L T := by
  ext ψ
  rw [comp_apply, comp_apply, ι2_eq_put, ι2_eq_put, localOp_put]

omit [CompleteSpace R] in
/-- The clean embedding of the system register factors through `ι2`. -/
theorem fl_iota0_ι2 (k : ℕ) :
    (fl (W := Fin (k + 3)) (S := Fin k) (R := R)) ∘L iota0 (a := k + 3) (P := Reg (Fin k) R) =
      ι2 k ∘L (fl (W := Fin (k + 1)) (S := Fin k) (R := R)) ∘L
        iota0 (a := k + 1) (P := Reg (Fin k) R) := by
  ext q y
  rw [comp_apply, comp_apply, comp_apply, ι2_apply]
  change flat (Fin (k + 3)) (Fin k) R (iota0 q) y = _
  rw [flat_apply, iota0_apply]
  have hanc : ((fun w => y (Sum.inl w)) = zw (k + 3)) ↔
      ((y (Sum.inl (fW k)) = false ∧ y (Sum.inl (zW k)) = false) ∧
        (fun w => (fun p => y (ιU k p)) (Sum.inl w)) = zw (k + 1)) := by
    constructor
    · intro h
      refine ⟨⟨congrFun h (fW k), congrFun h (zW k)⟩, funext fun i => congrFun h (cU k i)⟩
    · rintro ⟨⟨hf, hz⟩, h⟩
      funext i
      rcases fin_cases_U k i with ⟨i', rfl⟩ | rfl | rfl
      · exact congrFun h i'
      · exact hf
      · exact hz
  by_cases h1 : y (Sum.inl (fW k)) = false ∧ y (Sum.inl (zW k)) = false
  · rw [if_pos h1]
    change _ = flat (Fin (k + 1)) (Fin k) R (iota0 q) (fun p => y (ιU k p))
    rw [flat_apply, iota0_apply]
    by_cases h2 : (fun w => (fun p => y (ιU k p)) (Sum.inl w)) = zw (k + 1)
    · rw [if_pos (hanc.2 ⟨h1, h2⟩), if_pos h2]
      rfl
    · rw [if_neg (fun h => h2 (hanc.1 h).2), if_neg h2]
      rfl
  · rw [if_neg h1, if_neg (fun h => h1 (hanc.1 h).1)]
    rfl

/-! ### Diagonal operators -/

section Diagonal

variable {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

omit [CompleteSpace Q] in
theorem matOp_diagonal_apply (d : Cfg W → ℂ) (ψ : Reg W Q) (y : Cfg W) :
    matOp (Matrix.diagonal d) ψ y = d y • ψ y := by
  rw [matOp_apply, Finset.sum_eq_single y]
  · simp
  · intro c _ hc
    simp [Matrix.diagonal_apply_ne _ (Ne.symm hc)]
  · intro h
    exact absurd (Finset.mem_univ y) h

/-- **A diagonal operator commutes with an operator on wires it does not read.** -/
theorem diag_comm_localOp (d : Cfg W → ℂ) {ι : A → W} (hι : Function.Injective ι)
    (F : Cfg W → (Reg A Q →L[ℂ] Reg A Q)) (hd : ∀ y c, d (overwrite ι y c) = d y) :
    matOp (Matrix.diagonal d) ∘L localOp ι hι F = localOp ι hι F ∘L matOp (Matrix.diagonal d) := by
  ext ψ y
  rw [comp_apply, comp_apply, matOp_diagonal_apply, localOp_apply, localOp_apply]
  have hs : slice ι (matOp (Q := Q) (Matrix.diagonal d) ψ) y = d y • slice ι ψ y := by
    apply PiLp.ext
    intro c
    rw [slice_apply, matOp_diagonal_apply, PiLp.smul_apply, slice_apply, hd]
  rw [hs, map_smul, PiLp.smul_apply]

/-- **A diagonal operator reading only the wires of `ι`** acts on these wires. -/
theorem diag_eq_localOp (d : Cfg W → ℂ) {ι : A → W} (hι : Function.Injective ι)
    (e : Cfg A → ℂ) (hd : ∀ y, d y = e (fun a => y (ι a))) :
    matOp (Q := Q) (Matrix.diagonal d) = localOp ι hι (fun _ => matOp (Matrix.diagonal e)) := by
  ext ψ y
  rw [matOp_diagonal_apply, localOp_apply, matOp_diagonal_apply, slice_apply,
    overwrite_self hι, hd]

end Diagonal

omit [CompleteSpace R] in
/-- The flat form of a diagonal operator on the ancillas. -/
theorem conj_dg {a : ℕ} {S : Type*} [Fintype S] [DecidableEq S] (d : Cfg (Fin a) → ℂ) :
    conj (dg (P := Reg S R) d) =
      matOp (Matrix.diagonal (fun y : Cfg (Fin a ⊕ S) => d (fun w => y (Sum.inl w)))) := by
  ext φ y
  rw [conj_apply, dg_apply, matOp_diagonal_apply, PiLp.smul_apply, flat_symm_apply]
  have hy : (Sum.elim (fun w => y (Sum.inl w)) fun s => y (Sum.inr s)) = y :=
    funext (fun v => by rcases v with w | s <;> rfl)
  rw [hy]

/-! ### The local qubits of the factor -/

/-- The local qubits of the factor: the flag `f`, the orientation `o` and the sign `z`. -/
def locU (k : ℕ) : Fin 3 → GU k := ![Sum.inl (fW k), Sum.inl 0, Sum.inl (zW k)]

theorem locU_injective (k : ℕ) : Function.Injective (locU k) := by
  intro i j h
  have h0 : (0 : Fin (k + 3)) ≠ fW k := by simp [fW, Fin.ext_iff]
  have h0' : (0 : Fin (k + 3)) ≠ zW k := by simp [zW, Fin.ext_iff]
  have hfz := fW_ne_zW k
  fin_cases i <;> fin_cases j <;> simp_all [locU]

@[simp] theorem locU_zero (k : ℕ) : locU k 0 = Sum.inl (fW k) := rfl
@[simp] theorem locU_one (k : ℕ) : locU k 1 = Sum.inl 0 := rfl
@[simp] theorem locU_two (k : ℕ) : locU k 2 = Sum.inl (zW k) := rfl

/-- The configuration `(f, o, z) = (0, b, 0)` of the local qubits. -/
def ff (b : Bool) : Cfg (Fin 3) := ![false, b, false]

theorem locU_ne_ixPR (k : ℕ) (i : Fin 3) (e : EW k) : locU k i ≠ ιU k (ixPR k e) := by
  fin_cases i
  · exact (ιU_ne_f k _).symm
  · intro h
    have h' : ιU k (oPR k) = ιU k (ixPR k e) := h
    exact ixPR_ne_o k e ((ιU_injective k) h').symm
  · exact (ιU_ne_z k _).symm

/-- Clean flag and sign, and the local qubits overwritten by `(0, b, 0)`. -/
theorem overwrite_locU_extU {k : ℕ} (c : Cfg (PR k)) (b : Bool) :
    overwrite (locU k) (extU c) (ff b) = extU (Function.update c (oPR k) b) := by
  funext w
  by_cases hw : ∃ i, locU k i = w
  · obtain ⟨i, rfl⟩ := hw
    rw [overwrite_apply_ι (locU_injective k)]
    fin_cases i
    · simp [ff, extU_f]
    · change b = extU (Function.update c (oPR k) b) (ιU k (oPR k))
      rw [extU_ιU, Function.update_self]
    · simp [ff, extU_z]
  · push Not at hw
    rw [overwrite_apply_out _ _ _ _ hw]
    have hf : w ≠ Sum.inl (fW k) := fun h => hw 0 (by rw [h]; rfl)
    have hz : w ≠ Sum.inl (zW k) := fun h => hw 2 (by rw [h]; rfl)
    obtain ⟨p, rfl⟩ : ∃ p, ιU k p = w := by
      by_contra hp
      push Not at hp
      rcases (out_ιU_iff k w).1 hp with h | h
      · exact hf h
      · exact hz h
    have hpo : p ≠ oPR k := fun h => hw 1 (by rw [h]; rfl)
    rw [extU_ιU, extU_ιU, Function.update_of_ne hpo]

/-- The local qubits of an extended configuration. -/
theorem extU_locU {k : ℕ} (c : Cfg (PR k)) :
    (fun i => extU c (locU k i)) = ff (c (oPR k)) := by
  funext i
  fin_cases i
  · simp [ff, extU_f]
  · change extU c (ιU k (oPR k)) = c (oPR k)
    rw [extU_ιU]
  · simp [ff, extU_z]

/-- Clearing the local qubits of an extended configuration does not depend on its orientation. -/
theorem clearCfg_locU_extU {k : ℕ} (c : Cfg (PR k)) (b : Bool) :
    clearCfg (locU k) (extU (Function.update c (oPR k) b)) = clearCfg (locU k) (extU c) := by
  have h : extU (Function.update c (oPR k) b) = overwrite (locU k) (extU c) (ff b) :=
    (overwrite_locU_extU c b).symm
  rw [h]
  simp only [clearCfg, overwrite, outPart_joinCfg]

/-- Sums over the configurations of the three local qubits. -/
theorem sum_cfg3 {M : Type*} [AddCommMonoid M] (g : Cfg (Fin 3) → M) :
    ∑ d, g d = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, g ![a, b, c] := by
  rw [← eQ.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

/-- **Compressing an operator on the local qubits** to clean flag and sign gives the one-qubit
operation on the orientation with the `(f, z) = (0, 0)` block. -/
theorem ι2_compress {k : ℕ} (M : Cfg (GU k) → Matrix (Cfg (Fin 3)) (Cfg (Fin 3)) ℂ) :
    (ι2 (R := R) k)† ∘L localOp (locU k) (locU_injective k) (fun y => matOp (M y)) ∘L ι2 k =
      condOp (oPR k) (fun c => fun b b' => M (clearCfg (locU k) (extU c)) (ff b) (ff b')) := by
  apply ext_bas_clm
  intro c q
  apply PiLp.ext
  intro c'
  rw [comp_apply, comp_apply, ι2_adjoint_apply, ι2_bas, localOp_apply, matOp_apply,
    condOp_apply, extU_locU]
  simp only [slice_apply, bas_apply, clearCfg_locU_extU]
  rw [sum_cfg3]
  have hd : ∀ a b' c'' : Bool, (overwrite (locU k) (extU c') ![a, b', c''] = extU c) ↔
      (a = false ∧ c'' = false ∧ Function.update c' (oPR k) b' = c) := by
    intro a b' c''
    constructor
    · intro h
      have ha := congrFun h (locU k 0)
      have hc := congrFun h (locU k 2)
      rw [overwrite_apply_ι (locU_injective k)] at ha hc
      simp only [locU_zero, locU_two, extU_f, extU_z] at ha hc
      simp only [Matrix.cons_val_zero] at ha
      change c'' = false at hc
      subst ha hc
      refine ⟨rfl, rfl, extU_injective ?_⟩
      rw [← h]
      exact (overwrite_locU_extU c' b').symm
    · rintro ⟨rfl, rfl, h⟩
      rw [← h]
      exact overwrite_locU_extU c' b'
  simp only [hd]
  simp [ff]

end

end GateOptimalBinary
