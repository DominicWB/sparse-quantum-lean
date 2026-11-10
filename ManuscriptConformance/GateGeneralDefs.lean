import ManuscriptConformance.GateDefs
import GeneralSparseAccess.PadSpec
import GeneralSparseAccess.Keep

/-!
# Sparse access of general size in the gate theorems

The package's gate endpoints take sparse data in the binary format (`BinaryFormat`: `N = 2^k`,
`s = 2^{s_b}`, slots enumerated by the low index words). This file transfers them to the sparse
access of the manuscript in general sizes (`GeneralSparseAccess.QData`: an `N × N` matrix with
`s`-sparse lists, `1 ≤ s ≤ N ≤ 2^k`, locators prescribed on valid list inputs only, any action
elsewhere):

* `padFormat`: for a public word `z₀` with `val z₀ = 0`, the padded data `D.padData z₀ hz₀`
  (`k + 1`-bit index words, `2^⌈log₂ s⌉` slots) are in the binary format when the words are
  decoded as `c₀(X + iY)`, `b > 0`, `c₀ > 0`; the theorems use the all-zero word
  (`BinaryDecoder.zero`);
* `genCirc hS ζ N s z₀ Cc`: from a circuit `Cc` over the gate set calling the padded primitives,
  the circuit calling the supplied primitives — every call replaced by its implementation
  (`GeneralSparseAccess.implP`: at most three supplied calls and `implG k b` elementary gates on
  shared clean ancillas `GeneralSparseAccess.AW k b`), then the gates outside the gate set
  synthesised at accuracy `ζ` (`GeneralSparseAccess.keepC`, on the synthesis ancillas `Xs`);
* `genCirc_spec`: validity, every gate in the gate set, at most three supplied calls per call of
  `Cc`, at most `nGatesN Cc + implG k b · nCallsN (fun _ => true) Cc · (1 + L ζ)` gates;
* `genCirc_error`: on the system wires `genSys Xs sys` (the low `k` index wires of the padded
  system register, every other wire clean), the full-output error against the evolution of the
  padded matrix `D.padMat x` (the matrix on the valid indices, zero on the other index words) is at
  most the full-output error of `Cc` against the evolution of the padded data, plus
  `nGatesN (subst …) · ζ`.

The clean embedding along system wires composes (`cleanAlong_trans`), is the package's clean
embedding along `Sum.inl` (`cleanAlong_inl`) and is an isometry (`norm_cleanAlong`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateSynth SparseHamiltonian.GateBinary SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateODE (overwrite_apply_ι overwrite_apply_out)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

/-! ### The clean embedding along system wires -/

section CleanAlong

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R]

/-- **The clean embeddings along system wires compose.** -/
theorem cleanAlong_trans {S T W : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    [Fintype W] [DecidableEq W] (e₁ : S ↪ T) (e₂ : T ↪ W) :
    cleanAlong (R := R) (e₁.trans e₂) = cleanAlong e₂ ∘L cleanAlong e₁ := by
  refine ContinuousLinearMap.ext fun ψ => PiLp.ext fun y => ?_
  rw [comp_apply, cleanAlong_apply, cleanAlong_apply, cleanAlong_apply]
  by_cases h1 : ∀ w, (∀ t, e₂ t ≠ w) → y w = false
  · rw [if_pos h1]
    by_cases h2 : ∀ t, (∀ s, e₁ s ≠ t) → y (e₂ t) = false
    · rw [if_pos h2, if_pos]
      · rfl
      · intro w hw
        by_cases hr : ∃ t, e₂ t = w
        · obtain ⟨t, rfl⟩ := hr
          exact h2 t (fun s hs => hw s (congrArg e₂ hs))
        · exact h1 w (fun t ht => hr ⟨t, ht⟩)
    · rw [if_neg h2, if_neg]
      intro h
      apply h2
      intro t ht
      exact h (e₂ t) (fun s hs => ht s (e₂.injective hs))
  · rw [if_neg h1, if_neg]
    intro h
    apply h1
    intro w hw
    exact h w (fun s hs => hw (e₁ s) hs)

/-- **The clean embedding along `Sum.inl` is the package's clean embedding.** -/
theorem cleanAlong_inl {B X : Type*} [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X] :
    cleanAlong (R := R) (⟨Sum.inl, Sum.inl_injective⟩ : B ↪ B ⊕ X) = cleanEmb (X := X) := by
  refine ContinuousLinearMap.ext fun ψ => PiLp.ext fun y => ?_
  rw [cleanAlong_apply, cleanEmb_apply]
  by_cases h : ∀ x, y (Sum.inr x) = false
  · rw [if_pos, if_pos (funext h)]
    · rfl
    · intro w hw
      rcases w with b | x
      · exact absurd rfl (hw b)
      · exact h x
  · rw [if_neg, if_neg]
    · intro h'
      exact h (fun x => congrFun h' x)
    · intro h'
      exact h (fun x => h' (Sum.inr x) (fun b hb => Sum.inl_ne_inr hb))

/-- **The clean embedding along system wires is an isometry.** -/
theorem norm_cleanAlong {S W : Type*} [Fintype S] [DecidableEq S] [Fintype W] [DecidableEq W]
    (sys : S ↪ W) (ψ : Reg S R) : ‖cleanAlong sys ψ‖ = ‖ψ‖ := by
  have hsq : ‖cleanAlong sys ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    have hinj : ∀ d ∈ (Finset.univ : Finset (Cfg S)), ∀ d' ∈ (Finset.univ : Finset (Cfg S)),
        overwrite sys (fun _ => false) d = overwrite sys (fun _ => false) d' → d = d' := by
      intro d _ d' _ h
      funext s
      have := congrFun h (sys s)
      rwa [overwrite_apply_ι sys.injective, overwrite_apply_ι sys.injective] at this
    have hclean : ∀ d : Cfg S, ∀ w, (∀ s, sys s ≠ w) →
        overwrite sys (fun _ => false) d w = false := fun d w hw => by
      rw [overwrite_apply_out _ _ _ _ hw]
    have hval : ∀ d : Cfg S, (fun s => overwrite sys (fun _ => false) d (sys s)) = d :=
      fun d => funext fun s => overwrite_apply_ι sys.injective _ d s
    calc ∑ y, ‖cleanAlong sys ψ y‖ ^ 2
        = ∑ y ∈ Finset.univ.image (fun d : Cfg S => overwrite sys (fun _ => false) d),
            ‖cleanAlong sys ψ y‖ ^ 2 := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro y _ hy
          rw [cleanAlong_apply, if_neg]
          · simp
          · intro h
            apply hy
            refine Finset.mem_image.mpr ⟨fun s => y (sys s), Finset.mem_univ _, ?_⟩
            funext w
            by_cases hw : ∃ s, sys s = w
            · obtain ⟨s, rfl⟩ := hw
              exact overwrite_apply_ι sys.injective _ _ s
            · rw [overwrite_apply_out _ _ _ _ (fun s hs => hw ⟨s, hs⟩)]
              exact (h w (fun s hs => hw ⟨s, hs⟩)).symm
      _ = ∑ d, ‖cleanAlong sys ψ (overwrite sys (fun _ => false) d)‖ ^ 2 :=
          Finset.sum_image hinj
      _ = ∑ d, ‖ψ d‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro d _
          rw [cleanAlong_apply, if_pos (hclean d), hval d]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem norm_cleanAlong_le {S W : Type*} [Fintype S] [DecidableEq S] [Fintype W]
    [DecidableEq W] (sys : S ↪ W) : ‖(cleanAlong (R := R) sys : Reg S R →L[ℂ] Reg W R)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun ψ => by rw [one_mul, norm_cleanAlong])

/-- The clean embedding of the low `k` wires of a `k + 1`-bit index register: the marker clean. -/
theorem cleanAlong_castSucc_apply {k : ℕ} (ψ : Reg (Fin k) R) (y : Cfg (Fin (k + 1))) :
    cleanAlong (R := R) (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) ψ y =
      if mark y = false then ψ (lo y) else 0 := by
  rw [cleanAlong_apply]
  have hc : (∀ w, (∀ s, (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) s ≠ w) → y w = false) ↔
      mark y = false := by
    constructor
    · intro h
      exact h (Fin.last k) (fun s hs => (Fin.castSucc_lt_last s).ne hs)
    · intro h w hw
      rcases Fin.eq_castSucc_or_eq_last w with ⟨s, rfl⟩ | h'
      · exact absurd rfl (hw s)
      · rw [h']
        exact h
  by_cases h : mark y = false
  · rw [if_pos (hc.mpr h), if_pos h]
    rfl
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]

end CleanAlong

/-! ### Sums over the words with a clear marker -/

theorem sum_mark_false {k : ℕ} {M : Type*} [AddCommMonoid M] (g : Cfg (Fin k) → M) :
    ∑ y : Cfg (Fin (k + 1)), (if mark y = false then g (lo y) else 0) = ∑ d, g d := by
  have hinj : ∀ d ∈ (Finset.univ : Finset (Cfg (Fin k))),
      ∀ d' ∈ (Finset.univ : Finset (Cfg (Fin k))), idx false d = idx false d' → d = d' :=
    fun d _ d' _ h => (idx_injective h).2
  calc ∑ y : Cfg (Fin (k + 1)), (if mark y = false then g (lo y) else 0)
      = ∑ y ∈ Finset.univ.image (idx false), (if mark y = false then g (lo y) else 0) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro y _ hy
        rw [if_neg]
        intro h
        apply hy
        exact Finset.mem_image.mpr ⟨lo y, Finset.mem_univ _, (idx_eq_iff _ _ _).mpr ⟨h.symm, rfl⟩⟩
    _ = ∑ d, (if mark (idx false d) = false then g (lo (idx false d)) else 0) :=
        Finset.sum_image hinj
    _ = ∑ d, g d := Finset.sum_congr rfl (fun d _ => by rw [mk_idx, if_pos rfl, lo_idx])

/-! ### The evolution of the padded data on the clean marker -/

section Evolution

variable {X : Type*} {N s k b : ℕ} (D : QData X N s k b)
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

omit [CompleteSpace R] in
/-- **The padded data on the clean marker is the padded matrix.** -/
theorem matOp_padData_comp (z₀ : Cfg (VW b)) (hz₀ : D.val z₀ = 0) (x : X) :
    matOp (Q := R) ((D.padData z₀ hz₀).matrix x) ∘L
        cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) =
      cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) ∘L matOp (D.padMat x) := by
  refine ContinuousLinearMap.ext fun ψ => PiLp.ext fun y => ?_
  simp only [comp_apply, matOp_apply, cleanAlong_castSucc_apply, QData.padData_matrix_mark]
  by_cases hy : mark y = false
  · rw [if_pos hy, ← sum_mark_false (fun d => D.padMat x (lo y) d • ψ d)]
    apply Finset.sum_congr rfl
    intro y' _
    by_cases hy' : mark y' = false
    · rw [if_pos ⟨hy, hy'⟩, if_pos hy', if_pos hy']
    · rw [if_neg (fun h => hy' h.2), if_neg hy', if_neg hy', zero_smul]
  · rw [if_neg hy]
    apply Finset.sum_eq_zero
    intro y' _
    rw [if_neg (fun h => hy h.1), zero_smul]

/-- **The evolution of the padded data on the clean marker is the evolution of the padded
matrix.** -/
theorem exp_padData_comp (z₀ : Cfg (VW b)) (hz₀ : D.val z₀ = 0) (x : X) (t : ℝ) :
    NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
        (SparseStateOverlap.matrixOperator ((D.padData z₀ hz₀).matrix x))) ∘L
        cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) =
      cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) ∘L
        NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
          (SparseStateOverlap.matrixOperator (D.padMat x))) := by
  apply exp_comp_of_comp
  rw [qlift_refl_matrixOperator, qlift_refl_matrixOperator, smul_comp, comp_smul,
    matOp_padData_comp]

end Evolution

/-! ### Full-output errors as operator norms -/

/-- **A full-output error bound is an operator-norm bound.** -/
theorem norm_le_of_fullOutputError {P K : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] {A : K →L[ℂ] K} {J : P →L[ℂ] K}
    {V : P →L[ℂ] P} {ε : ℝ} (h : FullOutputError A J V ε) (hε : 0 ≤ ε) :
    ‖A ∘L J - J ∘L V‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro ψ
  by_cases hψ : ψ = 0
  · rw [hψ, map_zero, norm_zero, norm_zero, mul_zero]
  · have hn : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
    have hu : ‖((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ‖ = 1 := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
        inv_mul_cancel₀ hn.ne']
    have h1 := h _ hu
    have e : A (J (((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ)) - J (V (((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ)) =
        ((‖ψ‖⁻¹ : ℝ) : ℂ) • ((A ∘L J - J ∘L V) ψ) := by
      simp only [map_smul, sub_apply, comp_apply, smul_sub]
    rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
      inv_mul_le_iff₀ hn] at h1
    linarith

/-- **A full-output error bound on every vector.** -/
theorem fullOutputError_apply_le {P K : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] {A : K →L[ℂ] K} {J : P →L[ℂ] K}
    {V : P →L[ℂ] P} {ε : ℝ} (h : FullOutputError A J V ε) (hε : 0 ≤ ε) (φ : P) :
    ‖A (J φ) - J (V φ)‖ ≤ ε * ‖φ‖ := by
  have e : A (J φ) - J (V φ) = (A ∘L J - J ∘L V) φ := rfl
  rw [e]
  exact (le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_le_of_fullOutputError h hε) (norm_nonneg _))

/-! ### The binary format of the padded data -/

section Format

theorem ofBits_false (w : ℕ) : ofBits (fun _ => false) w = 0#w := by
  rw [← ofBits_getLsbD (0#w)]
  apply ofBits_congr
  intro i _
  simp

theorem twos_false {B : Type*} {b : ℕ} (r : Fin b → B) : twos r (fun _ : B => false) = 0 := by
  unfold twos
  have h : (fun j => if h : j < b then (fun _ : B => false) (r ⟨j, h⟩) else false) =
      fun _ => false := by
    funext j
    split_ifs <;> rfl
  rw [h, ofBits_false, BitVec.toInt_zero]

/-- The zero word decodes to `0`. -/
theorem gauss_false {b : ℕ} : gauss (b := b) (fun _ => false) = 0 := by
  unfold gauss
  rw [twos_false, twos_false]
  simp

/-- **The padded data are in the binary format** for a decoder `c₀(X + iY)`. -/
theorem padFormat {X : Type*} {N s k b : ℕ} (D : QData X N s k b) (z₀ : Cfg (VW b))
    (hz₀ : D.val z₀ = 0) {c0 : ℝ} (hb : 0 < b) (hc0 : 0 < c0)
    (hdec : ∀ z, D.val z = (c0 : ℂ) * gauss z) :
    formal_binaryInput (D.padData z₀ hz₀) (Equiv.refl _) (sbP s) c0 :=
  ⟨(sbP_le D.s_le_pow).trans (Nat.le_succ k), rfl, fun j => pslot_range D.s_le_pow j, hb, hc0,
    fun _ z => hdec z⟩

end Format

/-! ### The circuit of general sparse data -/

section Gen

variable {𝒢 : Set Kind} {Xs : Type*} [Fintype Xs] [DecidableEq Xs] {L : ℝ → ℕ}
variable {W : Type*} [Fintype W] [DecidableEq W] {k b : ℕ}

theorem card_AW (k b : ℕ) : Fintype.card (GeneralSparseAccess.AW k b) = 6 * k + 6 + 2 * b := by
  simp only [GeneralSparseAccess.AW, EW, VW, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  ring

/-- **The system wires of the general circuit**: the low `k` index wires of the padded system
register. -/
def genSys (Xs : Type*) (sys : Fin (k + 1) ↪ W) : Fin k ↪ (W ⊕ GeneralSparseAccess.AW k b) ⊕ Xs :=
  (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)).trans (sys.trans
    ((⟨Sum.inl, Sum.inl_injective⟩ : W ↪ W ⊕ GeneralSparseAccess.AW k b).trans ⟨Sum.inl, Sum.inl_injective⟩))

/-- **The circuit of general sparse data** from a circuit `Cc` of the padded data: every call
replaced by its implementation (`implP`), then the gates outside the gate set synthesised at
accuracy `ζ` (`keepC`). -/
def genCirc (hS : Synthesis 𝒢 Xs L) (ζ : ℝ) (N s : ℕ) (z₀ : Cfg (VW b))
    (Cc : List (NInstr W (PY (k + 1) b) Query)) :
    List (NInstr ((W ⊕ GeneralSparseAccess.AW k b) ⊕ Xs) (PY k b) Query) :=
  keepC hS ζ (subst (implP N s z₀) Cc)

theorem cleanAlong_genSys {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R]
    (sys : Fin (k + 1) ↪ W) :
    cleanAlong (R := R) (genSys (b := b) Xs sys) =
      cleanEmb (X := Xs) ∘L (cleanEmb (X := GeneralSparseAccess.AW k b) ∘L
        (cleanAlong sys ∘L cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)))) := by
  unfold genSys
  rw [cleanAlong_trans, cleanAlong_trans, cleanAlong_trans, cleanAlong_inl, cleanAlong_inl]
  simp only [comp_assoc]

/-- **Validity, gate set and counts of the circuit of general sparse data.** -/
theorem genCirc_spec {N s : ℕ} (z₀ : Cfg (VW b)) (hS : Synthesis 𝒢 Xs L) {ζ : ℝ} (hζ : 0 < ζ)
    (Cc : List (NInstr W (PY (k + 1) b) Query)) (hv : ∀ i ∈ Cc, i.Valid)
    (hg : ∀ g, NInstr.gate g ∈ Cc → GateOf 𝒢 g) :
    (∀ i ∈ genCirc hS ζ N s z₀ Cc, i.Valid) ∧
      (∀ g, NInstr.gate g ∈ genCirc hS ζ N s z₀ Cc → GateOf 𝒢 g) ∧
      nCallsN (fun _ => true) (genCirc hS ζ N s z₀ Cc) ≤ 3 * nCallsN (fun _ => true) Cc ∧
      nGatesN (genCirc hS ζ N s z₀ Cc) ≤
        nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc * (1 + L ζ) ∧
      nGatesN (subst (implP N s z₀) Cc) ≤ nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc := by
  have hC2v := valid_subst (valid_implP (k := k) (b := b) N s z₀) Cc hv
  obtain ⟨hv', hg', hgates, hcalls⟩ := keepC_spec hS hζ _ hC2v
  have hsubG := nGatesN_subst_le (implP N s z₀) (implG k b) (nGatesN_implP_le N s z₀) Cc
  have hout := nGatesOut_subst_le 𝒢 (implP N s z₀) (implG k b) (nGatesN_implP_le N s z₀) Cc hg
  have hcall := nCallsN_subst_le (kindOK_implP (k := k) (b := b) N s z₀) (fun _ => true) Cc
  refine ⟨hv', hg', ?_, ?_, hsubG⟩
  · unfold genCirc
    rw [hcalls]
    exact hcall
  · unfold genCirc
    calc nGatesN (keepC hS ζ (subst (implP N s z₀) Cc))
        ≤ nGatesN (subst (implP N s z₀) Cc) + nGatesOut 𝒢 (subst (implP N s z₀) Cc) * L ζ :=
          hgates
      _ ≤ (nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc) +
            (implG k b * nCallsN (fun _ => true) Cc) * L ζ :=
          Nat.add_le_add hsubG (Nat.mul_le_mul_right _ hout)
      _ = nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc * (1 + L ζ) := by ring

/-- **The full-output error of the circuit of general sparse data**: at most the full-output
error of `Cc` on the padded data plus `nGatesN (subst …) · ζ`, against the evolution of the padded
matrix on the low index wires. -/
theorem genCirc_error {X : Type*} {N s : ℕ} (D : QData X N s k b) (z₀ : Cfg (VW b))
    (hz₀ : D.val z₀ = 0) (hS : Synthesis 𝒢 Xs L) {ζ : ℝ} (hζ : 0 < ζ) (sys : Fin (k + 1) ↪ W)
    (Cc : List (NInstr W (PY (k + 1) b) Query)) (hv : ∀ i ∈ Cc, i.Valid)
    {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R] (x : X)
    (t ε : ℝ) (hε : 0 ≤ ε)
    (h : FullOutputError (nrun (GateBinary.prims (R := R) (D.padData z₀ hz₀) (Equiv.refl _) x) Cc)
      (cleanAlong sys) (NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
        (SparseStateOverlap.matrixOperator ((D.padData z₀ hz₀).matrix x)))) ε) :
    FullOutputError (nrun (D.prims (R := R) x) (genCirc hS ζ N s z₀ Cc))
      (cleanAlong (genSys Xs sys))
      (NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
        (SparseStateOverlap.matrixOperator (D.padMat x))))
      (ε + nGatesN (subst (implP N s z₀) Cc) * ζ) := by
  apply fullOutputError_of_norm
  have hprim : ∀ j, IsUnitary (D.prims (R := R) x j) := D.prims_isUnitary x
  have hprim' : ∀ j, IsUnitary (GateBinary.prims (R := R) (D.padData z₀ hz₀) (Equiv.refl _) x j) :=
    GateBinary.prims_isUnitary _ _ x
  have hok := implOK (R := R) D z₀ hz₀ x
  have hsub := nrun_subst_cleanEmb (D.prims x) _ hprim hprim' hok Cc
  have hC2v := valid_subst hok.valid Cc hv
  have hE2n : ∀ p : Reg (Fin k) R, ‖(cleanEmb (X := GeneralSparseAccess.AW k b) ∘L (cleanAlong sys ∘L
      cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)))) p‖ ≤ ‖p‖ := fun p => by
    rw [comp_apply, comp_apply, norm_cleanEmb, norm_cleanAlong, norm_cleanAlong]
  have hkeep := keepC_error (D.prims (R := R) x) hS hζ _ hC2v hprim _ hE2n
    (NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
      (SparseStateOverlap.matrixOperator (D.padMat x))))
  rw [cleanAlong_genSys]
  unfold genCirc
  refine hkeep.trans (add_le_add ?_ le_rfl)
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro p
  have h1 := DFunLike.congr_fun hsub
    (cleanAlong sys (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) p))
  have h2 := DFunLike.congr_fun (exp_padData_comp (R := R) D z₀ hz₀ x t) p
  simp only [comp_apply] at h1 h2
  simp only [sub_apply, comp_apply]
  rw [h1, ← h2, ← map_sub, norm_cleanEmb]
  calc _ ≤ ε * ‖cleanAlong (R := R) (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) p‖ :=
        fullOutputError_apply_le h hε _
    _ = ε * ‖p‖ := by rw [norm_cleanAlong]

end Gen

end

end ManuscriptConformance
