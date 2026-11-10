import GateOptimalBinary.ClipOps

/-!
# The register of the clipped regime

The joint private operation of the clipped regime (Section `gate:sec:native`; `twonorm:eq:joint`)
acts on the factor register `GU k` of the signed-factor regime (`k + 3` ancillas: the bounded
oriented edge register, the flag `f` and the sign `z`) and one more qubit, the branch `g`, which
selects the clipped bulk (`g = 0`) or the correction factor (`g = 1`). The register is
`PRf k = Fin (k + 3 + 1) ⊕ Fin k` of `SignedNative`: the branch is wire `0` (`gW`) and the factor
register sits on the wires `1, …, k + 3` (`ιS`).

* `ιG0`, `ιGp`: the factor register with the branch in `|0⟩` and in `|+⟩ = (|0⟩ + |1⟩)/√2`; the
  Hadamard gate on the branch maps the first to the second (`hadGate_ιG0`);
* `clUJg`: the boundary preparation of the clipped regime, the Hadamard gates of the bounded
  regime on the bounded wires and one Hadamard gate on the branch, preparing
  `J = (J₀, J_c)/√2` with both parts sharing the edge register; `clip_boundary_reduce`: the
  compression by `J` is the compression by the signed-factor boundary of `ιGp† T ιGp`;
* `ιGp_compress`: compressing an operation on the three local qubits `(f, o, z)`, chosen by the
  branch and the other wires, to `|+⟩_g` averages the two branches;
* `sg_boundary_compress`: the compression by the signed-factor boundary of a located operation
  on the local qubits is the qubit lift of the compression of the edgewise operation by the
  sparse boundary `J₀`.

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
open SparseHamiltonian.GateODE (put put_apply localOp_put bas_eq_put overwrite_apply_ι
  overwrite_apply_out)
open scoped InnerProduct Matrix

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-! ### The branch wire -/

/-- The branch wire `g` (wire `0`). -/
abbrev gW (k : ℕ) : PRf k := Sum.inl 0

theorem ιS_ne_gW (k : ℕ) (w : GU k) : ιS k w ≠ gW k := by
  rcases w with i | j
  · intro h
    exact Fin.succ_ne_zero i (Sum.inl_injective h)
  · intro h
    cases h

/-- Every wire outside the factor register is the branch. -/
theorem out_ιS_iff (k : ℕ) (v : PRf k) : (∀ w, ιS k w ≠ v) ↔ v = gW k := by
  constructor
  · intro h
    rcases v with i | j
    · by_cases hi : i = 0
      · rw [hi]
      · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hi
        exact absurd rfl (h (Sum.inl i'))
    · exact absurd rfl (h (Sum.inr j))
  · rintro rfl w
    exact ιS_ne_gW k w

/-- `ιS` as an embedding. -/
def ιSe (k : ℕ) : GU k ↪ PRf k := ⟨ιS k, ιS_injective k⟩

/-- The configuration with branch `g` and factor part `c`. -/
def extG {k : ℕ} (g : Bool) (c : Cfg (GU k)) : Cfg (PRf k) := overwrite (ιS k) (fun _ => g) c

theorem extG_ιS {k : ℕ} (g : Bool) (c : Cfg (GU k)) (w : GU k) : extG g c (ιS k w) = c w :=
  overwrite_apply_ι (ιS_injective k) _ c w

theorem extG_g {k : ℕ} (g : Bool) (c : Cfg (GU k)) : extG g c (gW k) = g :=
  overwrite_apply_out _ _ c _ (ιS_ne_gW k)

theorem extG_comp {k : ℕ} (g : Bool) (c : Cfg (GU k)) : (fun w => extG g c (ιS k w)) = c :=
  funext (extG_ιS g c)

theorem eq_extG {k : ℕ} (y : Cfg (PRf k)) : y = extG (y (gW k)) (fun w => y (ιS k w)) := by
  funext v
  by_cases hv : ∃ w, ιS k w = v
  · obtain ⟨w, rfl⟩ := hv
    rw [extG_ιS]
  · push Not at hv
    rw [(out_ιS_iff k v).1 hv, extG_g]

theorem extG_injective {k : ℕ} {g g' : Bool} {c c' : Cfg (GU k)} (h : extG g c = extG g' c') :
    g = g' ∧ c = c' := by
  refine ⟨?_, ?_⟩
  · rw [← extG_g g c, ← extG_g g' c', h]
  · rw [← extG_comp g c, ← extG_comp g' c', h]

theorem extG_locF {k : ℕ} (g : Bool) (c : Cfg (GU k)) :
    (fun i => extG g c (locF k i)) = fun i => c (locU k i) :=
  funext fun i => extG_ιS g c (locU k i)

theorem locF_apply (k : ℕ) (i : Fin 3) : locF k i = ιS k (locU k i) := rfl

theorem overwrite_locF_extG {k : ℕ} (g : Bool) (c : Cfg (GU k)) (d : Cfg (Fin 3)) :
    overwrite (locF k) (extG g c) d = extG g (overwrite (locU k) c d) := by
  funext v
  by_cases hv : ∃ w, ιS k w = v
  · obtain ⟨w, rfl⟩ := hv
    rw [extG_ιS]
    by_cases hw : ∃ i, locU k i = w
    · obtain ⟨i, rfl⟩ := hw
      rw [← locF_apply, overwrite_apply_ι (locF k).injective, overwrite_apply_ι (locU_injective k)]
    · push Not at hw
      have hw' : ∀ i, locF k i ≠ ιS k w := fun i h => hw i ((ιS_injective k) h)
      rw [overwrite_apply_out _ _ _ _ hw', overwrite_apply_out _ _ _ _ hw, extG_ιS]
  · push Not at hv
    have hv' : ∀ i, locF k i ≠ v := fun i h => hv _ h
    rw [overwrite_apply_out _ _ _ _ hv', (out_ιS_iff k v).1 hv, extG_g, extG_g]

theorem clearCfg_locF_extG {k : ℕ} (g : Bool) (c : Cfg (GU k)) :
    clearCfg (locF k) (extG g c) = extG g (clearCfg (locU k) c) :=
  overwrite_locF_extG g c _

/-! ### The branch in `|0⟩` and in `|+⟩` -/

/-- The factor register with the branch in `|0⟩`. -/
def ιG0 (k : ℕ) : Reg (GU k) R →L[ℂ] Reg (PRf k) R :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Cfg (PRf k) => R)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun y =>
      if y (gW k) = false then coord (fun w => y (ιS k w)) else 0)

omit [CompleteSpace R] in
theorem ιG0_apply {k : ℕ} (ψ : Reg (GU k) R) (y : Cfg (PRf k)) :
    ιG0 k ψ y = if y (gW k) = false then ψ (fun w => y (ιS k w)) else 0 := by
  change (if y (gW k) = false then coord (fun w => y (ιS k w)) else 0) ψ = _
  split_ifs <;> rfl

omit [CompleteSpace R] in
theorem outPart_ιS_iff {k : ℕ} (y : Cfg (PRf k)) (g : Bool) :
    outPart (ιS k) y = outPart (ιS k) (fun _ => g) ↔ y (gW k) = g := by
  constructor
  · intro h
    exact congrFun h ⟨gW k, ιS_ne_gW k⟩
  · intro h
    funext ⟨v, hv⟩
    have hv' := (out_ιS_iff k v).1 hv
    subst hv'
    exact h

omit [CompleteSpace R] in
theorem ιG0_eq_put {k : ℕ} (ψ : Reg (GU k) R) :
    ιG0 k ψ = put (ιS k) (ιS_injective k) (fun _ => false) ψ := by
  apply PiLp.ext
  intro y
  rw [ιG0_apply, put_apply]
  by_cases h : y (gW k) = false
  · rw [if_pos h, if_pos ((outPart_ιS_iff y false).2 h)]
  · rw [if_neg h, if_neg (fun h' => h ((outPart_ιS_iff y false).1 h'))]

theorem localOp_ιG0 {k : ℕ} (T : Reg (GU k) R →L[ℂ] Reg (GU k) R) :
    localOp (ιS k) (ιS_injective k) (fun _ => T) ∘L ιG0 k = ιG0 k ∘L T := by
  ext ψ
  rw [comp_apply, comp_apply, ιG0_eq_put, ιG0_eq_put, localOp_put]

omit [CompleteSpace R] in
theorem ιG0_bas {k : ℕ} (c : Cfg (GU k)) (q : R) : ιG0 k (bas c q) = bas (extG false c) q := by
  rw [ιG0_eq_put, put_bas]
  rfl

/-- The factor register with the branch in `|+⟩ = (|0⟩ + |1⟩)/√2`. -/
def ιGp (k : ℕ) : Reg (GU k) R →L[ℂ] Reg (PRf k) R :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Cfg (PRf k) => R)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun y => hamp • coord (fun w => y (ιS k w)))

omit [CompleteSpace R] in
theorem ιGp_apply {k : ℕ} (ψ : Reg (GU k) R) (y : Cfg (PRf k)) :
    ιGp k ψ y = hamp • ψ (fun w => y (ιS k w)) := rfl

omit [CompleteSpace R] in
theorem ιGp_eq {k : ℕ} (ψ : Reg (GU k) R) :
    ιGp k ψ = hamp • (put (ιS k) (ιS_injective k) (fun _ => false) ψ +
      put (ιS k) (ιS_injective k) (fun _ => true) ψ) := by
  apply PiLp.ext
  intro y
  rw [ιGp_apply, PiLp.smul_apply, PiLp.add_apply, put_apply, put_apply]
  cases h : y (gW k)
  · rw [if_pos ((outPart_ιS_iff y false).2 h), if_neg (fun h' => by
      rw [(outPart_ιS_iff y true).1 h'] at h
      cases h), add_zero]
  · rw [if_neg (fun h' => by
      rw [(outPart_ιS_iff y false).1 h'] at h
      cases h), if_pos ((outPart_ιS_iff y true).2 h), zero_add]

theorem localOp_ιGp {k : ℕ} (T : Reg (GU k) R →L[ℂ] Reg (GU k) R) :
    localOp (ιS k) (ιS_injective k) (fun _ => T) ∘L ιGp k = ιGp k ∘L T := by
  ext ψ
  rw [comp_apply, comp_apply, ιGp_eq, ιGp_eq, map_smul, map_add, localOp_put, localOp_put]

omit [CompleteSpace R] in
theorem ιGp_bas {k : ℕ} (c : Cfg (GU k)) (q : R) :
    ιGp k (bas c q) = hamp • (bas (extG false c) q + bas (extG true c) q) := by
  rw [ιGp_eq, put_bas, put_bas]
  rfl

theorem hamp_real : (starRingEnd ℂ) hamp = hamp := Complex.conj_ofReal _

theorem hamp_mul_hamp : hamp * hamp = (2⁻¹ : ℂ) := by
  unfold hamp
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  push_cast
  rfl

theorem ιGp_adjoint_apply {k : ℕ} (φ : Reg (PRf k) R) (c : Cfg (GU k)) :
    (((ιGp k)†) φ) c = hamp • (φ (extG false c) + φ (extG true c)) := by
  apply ext_inner_right ℂ
  intro r
  rw [← inner_bas_right c r (((ιGp k)†) φ), adjoint_inner_left, ιGp_bas, inner_smul_right,
    inner_add_right, inner_bas_right, inner_bas_right, inner_smul_left, hamp_real, inner_add_left]

/-- The Hadamard gate on the branch puts it in `|+⟩`. -/
theorem hadGate_ιG0 (k : ℕ) : (hadGate (gW k)).op ∘L ιG0 (R := R) k = ιGp k := by
  apply ext_bas_clm'
  intro c q
  rw [comp_apply, ιG0_bas, hadGate_bas _ _ (extG_g false c), ιGp_bas]
  congr 3
  funext v
  by_cases hv : v = gW k
  · subst hv
    rw [Function.update_self, extG_g]
  · rw [Function.update_of_ne hv]
    obtain ⟨w, rfl⟩ : ∃ w, ιS k w = v := by
      by_contra h
      push Not at h
      exact hv ((out_ιS_iff k v).1 h)
    rw [extG_ιS, extG_ιS]

/-- **Compressing an operation on the local qubits** to the branch `|+⟩` averages the
branches. -/
theorem ιGp_compress {k : ℕ} (N : Cfg (PRf k) → Matrix (Cfg (Fin 3)) (Cfg (Fin 3)) ℂ) :
    (ιGp (R := R) k)† ∘L localOp (locF k) (locF k).injective (fun y => matOp (N y)) ∘L
        ιGp k =
      localOp (locU k) (locU_injective k)
        (fun y => matOp ((2⁻¹ : ℂ) • (N (extG false y) + N (extG true y)))) := by
  apply ext_bas_clm
  intro c q
  apply PiLp.ext
  intro c'
  have hL : ∀ g : Bool, (localOp (locF k) (locF k).injective (fun y => matOp (N y))
      (ιGp k (bas c q))) (extG g c') =
      hamp • ∑ d, N (extG g (clearCfg (locU k) c')) (fun i => c' (locU k i)) d •
        (bas c q) (overwrite (locU k) c' d) := by
    intro g
    rw [localOp_apply, matOp_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [slice_apply, ιGp_apply, overwrite_locF_extG, extG_comp, clearCfg_locF_extG, extG_locF,
      smul_comm]
  rw [comp_apply, comp_apply, ιGp_adjoint_apply, hL, hL, localOp_apply, matOp_apply,
    ← smul_add, smul_smul, hamp_mul_hamp, ← Finset.sum_add_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [slice_apply, ← add_smul, smul_smul]
  congr 1

/-! ### The boundary preparation -/

/-- **The gates of `U_J`** in the clipped regime: the Hadamard gates of the bounded regime on
the bounded wires and one Hadamard gate on the branch. -/
def clUJg (k sb : ℕ) (hsb : sb ≤ k) : List (Gate (PRf k)) :=
  (sgUJg k sb hsb).map (GateODE.Gate.map (ιSe k)) ++ [hadGate (gW k)]

theorem clUJg_ok (sb : ℕ) (hsb : sb ≤ k) : ∀ g ∈ clUJg k sb hsb, GateOK 3 g := by
  intro g hg
  rcases List.mem_append.1 hg with hg | hg
  · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact gateOK_map (ιS_injective k) (sgUJg_ok sb hsb g' hg')
  · rw [List.mem_singleton] at hg
    subst hg
    exact hadGate_ok _

theorem clUJg_length (sb : ℕ) (hsb : sb ≤ k) : (clUJg k sb hsb).length = sb + 2 := by
  rw [clUJg, List.length_append, List.length_map, sgUJg_length, List.length_singleton]

theorem gRun_clUJg_ιG0 (sb : ℕ) (hsb : sb ≤ k) :
    gRun (Q := R) (clUJg k sb hsb) ∘L ιG0 k = ιGp k ∘L gRun (Q := R) (sgUJg k sb hsb) := by
  rw [clUJg, gRun_append, gRun_map_gates (ιSe k)]
  have h1 : gRun (Q := R) [hadGate (gW k)] = (hadGate (gW k)).op := by
    rw [gRun_cons, gRun_nil, one_def, id_comp]
  rw [h1, comp_assoc]
  change (hadGate (gW k)).op ∘L (localOp (ιS k) (ιS_injective k)
    (fun _ => gRun (Q := R) (sgUJg k sb hsb)) ∘L ιG0 k) = _
  rw [localOp_ιG0, ← comp_assoc, hadGate_ιG0]

omit [CompleteSpace R] in
/-- The clean embedding of the system register factors through `ιG0`. -/
theorem fl_iota0_ιG0 (k : ℕ) :
    (fl (W := Fin (k + 3 + 1)) (S := Fin k) (R := R)) ∘L
        iota0 (a := k + 3 + 1) (P := Reg (Fin k) R) =
      ιG0 k ∘L (fl (W := Fin (k + 3)) (S := Fin k) (R := R)) ∘L
        iota0 (a := k + 3) (P := Reg (Fin k) R) := by
  ext q y
  rw [comp_apply, comp_apply, comp_apply, ιG0_apply]
  change flat (Fin (k + 3 + 1)) (Fin k) R (iota0 q) y = _
  rw [flat_apply, iota0_apply]
  have hanc : ((fun w => y (Sum.inl w)) = zw (k + 3 + 1)) ↔
      (y (gW k) = false ∧ (fun w => (fun v => y (ιS k v)) (Sum.inl w)) = zw (k + 3)) := by
    constructor
    · intro h
      exact ⟨congrFun h 0, funext fun i => congrFun h i.succ⟩
    · rintro ⟨h0, h⟩
      funext i
      by_cases hi : i = 0
      · subst hi
        exact h0
      · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hi
        exact congrFun h i'
  by_cases h1 : y (gW k) = false
  · rw [if_pos h1]
    change _ = flat (Fin (k + 3)) (Fin k) R (iota0 q) (fun v => y (ιS k v))
    rw [flat_apply, iota0_apply]
    by_cases h2 : (fun w => (fun v => y (ιS k v)) (Sum.inl w)) = zw (k + 3)
    · rw [if_pos (hanc.2 ⟨h1, h2⟩), if_pos h2]
      rfl
    · rw [if_neg (fun h => h2 (hanc.1 h).2), if_neg h2]
      rfl
  · rw [if_neg h1, if_neg (fun h => h1 (hanc.1 h).1)]
    rfl

/-- **The compression by the clipped boundary** is the compression by the signed-factor boundary
of `ιGp† T ιGp`. -/
theorem clip_boundary_reduce (sb : ℕ) (hsb : sb ≤ k) (T : Reg (PRf k) R →L[ℂ] Reg (PRf k) R) :
    (UJop (R := R) (clUJg k sb hsb) ∘L iota0 (a := k + 3 + 1) (P := Reg (Fin k) R))† ∘L
        unconj T ∘L (UJop (R := R) (clUJg k sb hsb) ∘L iota0 (a := k + 3 + 1)) =
      (UJop (R := R) (sgUJg k sb hsb) ∘L iota0 (a := k + 3) (P := Reg (Fin k) R))† ∘L
        unconj ((ιGp k)† ∘L T ∘L ιGp k) ∘L (UJop (R := R) (sgUJg k sb hsb) ∘L iota0) := by
  rw [UJop_eq_unconj, UJop_eq_unconj, unconj_sandwich, unconj_sandwich, iota0_unconj,
    iota0_unconj, fl_iota0_ιG0]
  have h := gRun_clUJg_ιG0 (R := R) sb hsb
  calc ((ιG0 k ∘L (fl (W := Fin (k + 3)) (S := Fin k) (R := R)) ∘L
          iota0 (a := k + 3) (P := Reg (Fin k) R))† ∘L
        ((gRun (Q := R) (clUJg k sb hsb))† ∘L T ∘L gRun (Q := R) (clUJg k sb hsb)) ∘L
        ιG0 k ∘L (fl (W := Fin (k + 3)) (S := Fin k) (R := R)) ∘L
          iota0 (a := k + 3) (P := Reg (Fin k) R))
      = ((gRun (Q := R) (clUJg k sb hsb) ∘L ιG0 k) ∘L
          (fl (W := Fin (k + 3)) (S := Fin k) (R := R)) ∘L iota0 (a := k + 3)
          (P := Reg (Fin k) R))† ∘L T ∘L ((gRun (Q := R) (clUJg k sb hsb) ∘L ιG0 k) ∘L
          (fl (W := Fin (k + 3)) (S := Fin k) (R := R)) ∘L
          iota0 (a := k + 3) (P := Reg (Fin k) R)) := by
        simp only [adjoint_comp, comp_assoc]
    _ = _ := by
        rw [h]
        simp only [adjoint_comp, comp_assoc]

/-! ### The signed-factor boundary on located operations -/

/-- A matrix as an operator on the orientation qubit. -/
def qop (M : Matrix Bool Bool ℂ) : ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) M

theorem qmat_qop (M : Matrix Bool Bool ℂ) : qmat (qop M) = M := by
  funext b c
  simp only [qmat, qop]
  change (Matrix.toEuclideanCLM (𝕜 := ℂ) M (EuclideanSpace.single c 1)).ofLp b = M b c
  rw [Matrix.ofLp_toEuclideanCLM]
  simp [Matrix.mulVec, dotProduct]

/-- **The compression by the signed-factor boundary of a located operation on the local
qubits**: the qubit lift of the compression by `J₀` of its edgewise operation `G_e` on the
orientation, read at clean flag and sign. -/
theorem sg_boundary_compress (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (sb : ℕ) (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    (N : Cfg (GU k) → Matrix (Cfg (Fin 3)) (Cfg (Fin 3)) ℂ) (Ne : n × n → Matrix Bool Bool ℂ)
    (hN : ∀ c b b', N (clearCfg (locU k) (extU c)) (ff b) (ff b') =
      Ne (phiE en (fun e => c (ixPR k e))) b b') :
    (UJop (R := R) (sgUJg k sb hsb) ∘L iota0 (a := k + 3) (P := Reg (Fin k) R))† ∘L
        unconj ((FuF (R := R) D en x)† ∘L
          localOp (locU k) (locU_injective k) (fun y => matOp (N y)) ∘L FuF D en x) ∘L
        (UJop (R := R) (sgUJg k sb hsb) ∘L iota0) =
      qlift (R := R) en ((FixedLocatorConjugation.fixedBoundary D.slot)† ∘L
        ((FixedLocatorConjugation.locator D x)† ∘L
          OrientedEdgeCayley.lift (fun e => qop (Ne e)) ∘L FixedLocatorConjugation.locator D x) ∘L
        FixedLocatorConjugation.fixedBoundary D.slot) := by
  rw [UJop_eq_unconj, unconj_sandwich, iota0_unconj_ι2]
  have h1 : gRun (Q := R) (sgUJg k sb hsb) ∘L ι2 k = ι2 k ∘L gRun (Q := R) (hadUJ k sb hsb) := by
    rw [gRun_sgUJg, localOp_ι2]
  have h2 : FuF (R := R) D en x ∘L ι2 k =
      ι2 k ∘L qlift (R := R) (phiPR en) (FixedLocatorConjugation.locator D x) :=
    localOp_ι2 _
  have hX : (ι2 (R := R) k)† ∘L localOp (locU k) (locU_injective k) (fun y => matOp (N y)) ∘L
      ι2 k = qlift (R := R) (phiPR en) (OrientedEdgeCayley.lift (fun e => qop (Ne e))) := by
    rw [ι2_compress, qlift_lift]
    apply condOp_congr
    intro c
    funext b b'
    rw [qmat_qop, ← hN]
  have e : (ι2 (R := R) k)† ∘L ((gRun (Q := R) (sgUJg k sb hsb))† ∘L
      ((FuF (R := R) D en x)† ∘L localOp (locU k) (locU_injective k) (fun y => matOp (N y)) ∘L
        FuF D en x) ∘L gRun (Q := R) (sgUJg k sb hsb)) ∘L ι2 k =
      (qlift (R := R) (phiPR en) (FixedLocatorConjugation.locator D x) ∘L
          gRun (Q := R) (hadUJ k sb hsb))† ∘L
        qlift (R := R) (phiPR en) (OrientedEdgeCayley.lift (fun e => qop (Ne e))) ∘L
        (qlift (R := R) (phiPR en) (FixedLocatorConjugation.locator D x) ∘L
          gRun (Q := R) (hadUJ k sb hsb)) := by
    rw [← hX]
    calc (ι2 (R := R) k)† ∘L ((gRun (Q := R) (sgUJg k sb hsb))† ∘L
          ((FuF (R := R) D en x)† ∘L localOp (locU k) (locU_injective k)
            (fun y => matOp (N y)) ∘L FuF D en x) ∘L gRun (Q := R) (sgUJg k sb hsb)) ∘L ι2 k
        = (FuF (R := R) D en x ∘L gRun (Q := R) (sgUJg k sb hsb) ∘L ι2 k)† ∘L
            localOp (locU k) (locU_injective k) (fun y => matOp (N y)) ∘L
            (FuF (R := R) D en x ∘L gRun (Q := R) (sgUJg k sb hsb) ∘L ι2 k) := by
          simp only [adjoint_comp, comp_assoc]
      _ = _ := by
          have hF : FuF (R := R) D en x ∘L gRun (Q := R) (sgUJg k sb hsb) ∘L ι2 k =
              ι2 k ∘L (qlift (R := R) (phiPR en) (FixedLocatorConjugation.locator D x) ∘L
                gRun (Q := R) (hadUJ k sb hsb)) := by
            rw [h1, ← comp_assoc, h2, comp_assoc]
          rw [hF]
          simp only [adjoint_comp, comp_assoc]
  rw [e]
  exact sg_tail D en x sb hsb hs hrange _

end

end GateOptimalBinary
