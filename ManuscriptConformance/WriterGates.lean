import ManuscriptConformance.WriterGateAccess
import ManuscriptConformance.GateGeneral

/-!
# Conformance: the general-size gate theorems with a writer (handover item B4)

Theorems `hs:thm:gates` and `gate:thm:main` for sparse access of general size
(`gate_thm_main_general`, `hs_thm_gates_general`) with the value oracle given by a reversible
writer of the stored words specified on valid clean inputs only (`GeneralSparseAccess.QData.Writer`:
`W|i, j, 0⟩ = c_{ij}|i, j, w_{ij}⟩` for `i, j < N`, any phases, any unitary action elsewhere;
Section `hs:sec:control`), instead of the XOR oracle on every pair of index words.

* `genCircW hS ζ N s z₀ Cc`: from a circuit `Cc` of the padded data, every call replaced by its
  implementation in the writer model (`GeneralSparseAccess.implPW`: the padded locators of
  `implP`; the padded value oracle with the writer and its inverse in the places of the two XOR
  calls, the copy masked by the validity flag), then the gates outside the gate set synthesised at
  accuracy `ζ`;
* `genCircW_spec`, `genCircW_error`: the validity, gate set, call and gate counts and the
  full-output error of `genCirc_spec`, `genCirc_error`, for every writer.

The endpoints `hs_thm_gates_general_writer` and `gate_thm_main_general_writer` have the hypotheses,
constants and bounds of the released theorems; the circuit is fixed before the writer and the
instance, and the error clause holds for every writer with the specification. The writer calls
are counted with the locator calls among the primitive sparse queries; each padded value call
makes one writer call and one inverse writer call, the two XOR calls of the released
implementation.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateSynth SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget
  SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.OracleCircuit
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

/-! ### The circuit of general sparse data in the writer model -/

section GenW

variable {𝒢 : Set Kind} {Xs : Type*} [Fintype Xs] [DecidableEq Xs] {L : ℝ → ℕ}
variable {W : Type*} [Fintype W] [DecidableEq W] {k b : ℕ}

/-- **The circuit of general sparse data in the writer model** from a circuit `Cc` of the padded
data: every call replaced by its implementation from the locators and the writer (`implPW`), then
the gates outside the gate set synthesised at accuracy `ζ` (`keepC`). -/
def genCircW (hS : Synthesis 𝒢 Xs L) (ζ : ℝ) (N s : ℕ) (z₀ : Cfg (VW b))
    (Cc : List (NInstr W (PY (k + 1) b) Query)) :
    List (NInstr ((W ⊕ GeneralSparseAccess.AW k b) ⊕ Xs) (PY k b) Query) :=
  keepC hS ζ (subst (implPW N s z₀) Cc)

/-- **Validity, gate set and counts of the circuit in the writer model**, as for `genCirc`. -/
theorem genCircW_spec {N s : ℕ} (z₀ : Cfg (VW b)) (hS : Synthesis 𝒢 Xs L) {ζ : ℝ} (hζ : 0 < ζ)
    (Cc : List (NInstr W (PY (k + 1) b) Query)) (hv : ∀ i ∈ Cc, i.Valid)
    (hg : ∀ g, NInstr.gate g ∈ Cc → GateOf 𝒢 g) :
    (∀ i ∈ genCircW hS ζ N s z₀ Cc, i.Valid) ∧
      (∀ g, NInstr.gate g ∈ genCircW hS ζ N s z₀ Cc → GateOf 𝒢 g) ∧
      nCallsN (fun _ => true) (genCircW hS ζ N s z₀ Cc) ≤ 3 * nCallsN (fun _ => true) Cc ∧
      nGatesN (genCircW hS ζ N s z₀ Cc) ≤
        nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc * (1 + L ζ) ∧
      nGatesN (subst (implPW N s z₀) Cc) ≤ nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc := by
  have hC2v := valid_subst (valid_implPW (k := k) (b := b) N s z₀) Cc hv
  obtain ⟨hv', hg', hgates, hcalls⟩ := keepC_spec hS hζ _ hC2v
  have hsubG := nGatesN_subst_le (implPW N s z₀) (implG k b) (nGatesN_implPW_le N s z₀) Cc
  have hout := nGatesOut_subst_le 𝒢 (implPW N s z₀) (implG k b) (nGatesN_implPW_le N s z₀) Cc hg
  have hcall := nCallsN_subst_le (kindOK_implPW (k := k) (b := b) N s z₀) (fun _ => true) Cc
  refine ⟨hv', hg', ?_, ?_, hsubG⟩
  · unfold genCircW
    rw [hcalls]
    exact hcall
  · unfold genCircW
    calc nGatesN (keepC hS ζ (subst (implPW N s z₀) Cc))
        ≤ nGatesN (subst (implPW N s z₀) Cc) + nGatesOut 𝒢 (subst (implPW N s z₀) Cc) * L ζ :=
          hgates
      _ ≤ (nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc) +
            (implG k b * nCallsN (fun _ => true) Cc) * L ζ :=
          Nat.add_le_add hsubG (Nat.mul_le_mul_right _ hout)
      _ = nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc * (1 + L ζ) := by ring

/-- **The full-output error of the circuit in the writer model**: for every writer of the stored
words on valid clean inputs, at most the full-output error of `Cc` on the padded data plus
`nGatesN (subst …) · ζ`, against the evolution of the padded matrix on the low index wires. -/
theorem genCircW_error {X : Type*} {N s : ℕ} (D : QData X N s k b) (Wr : D.Writer)
    (z₀ : Cfg (VW b)) (hz₀ : D.val z₀ = 0) (hS : Synthesis 𝒢 Xs L) {ζ : ℝ} (hζ : 0 < ζ)
    (sys : Fin (k + 1) ↪ W) (Cc : List (NInstr W (PY (k + 1) b) Query)) (hv : ∀ i ∈ Cc, i.Valid)
    {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R] (x : X)
    (t ε : ℝ) (hε : 0 ≤ ε)
    (h : FullOutputError (nrun (GateBinary.prims (R := R) (D.padData z₀ hz₀) (Equiv.refl _) x) Cc)
      (cleanAlong sys) (NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
        (SparseStateOverlap.matrixOperator ((D.padData z₀ hz₀).matrix x)))) ε) :
    FullOutputError (nrun (Wr.prims (R := R) x) (genCircW hS ζ N s z₀ Cc))
      (cleanAlong (genSys Xs sys))
      (NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
        (SparseStateOverlap.matrixOperator (D.padMat x))))
      (ε + nGatesN (subst (implPW N s z₀) Cc) * ζ) := by
  apply fullOutputError_of_norm
  have hprim : ∀ j, IsUnitary (Wr.prims (R := R) x j) := Wr.prims_isUnitary x
  have hprim' : ∀ j, IsUnitary (GateBinary.prims (R := R) (D.padData z₀ hz₀) (Equiv.refl _) x j) :=
    GateBinary.prims_isUnitary _ _ x
  have hok := implOKW (R := R) Wr z₀ hz₀ x
  have hsub := nrun_subst_cleanEmb (Wr.prims x) _ hprim hprim' hok Cc
  have hC2v := valid_subst hok.valid Cc hv
  have hE2n : ∀ p : Reg (Fin k) R, ‖(cleanEmb (X := GeneralSparseAccess.AW k b) ∘L (cleanAlong sys ∘L
      cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)))) p‖ ≤ ‖p‖ := fun p => by
    rw [comp_apply, comp_apply, norm_cleanEmb, norm_cleanAlong, norm_cleanAlong]
  have hkeep := keepC_error (Wr.prims (R := R) x) hS hζ _ hC2v hprim _ hE2n
    (NormedSpace.exp ((-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
      (SparseStateOverlap.matrixOperator (D.padMat x))))
  rw [cleanAlong_genSys]
  unfold genCircW
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

end GenW

/-! ### Theorem `hs:thm:gates` in general sizes with a writer -/

universe u w

set_option maxHeartbeats 4000000 in
/-- **Theorem `hs:thm:gates`, eq. `hs:eq:gate-binary`, for sparse access of general size with a
writer** (handover item B4). The hypotheses, constants and bounds of `hs_thm_gates_general`:
for a finite gate set admitting single-qubit synthesis of length at most `c₁ log(1/ζ) + c₀` and an
exact decomposition of its controlled one-qubit gates, there is a constant `C` such that for
sparse data of general size decoded as `c0 (X + iY)` (`formal_binaryDecoder`) with `b_data`-bit
components and descriptions (`comp_bits`), every time `t` and `0 < ε ≤ 1/2`, one circuit over the
gate set, the supplied locators and a value writer, fixed before the writer and the instance, uses
at most `6635520 Q_base` primitive sparse queries (locator calls, writer calls and inverse writer
calls), at most `C Q_base (𝔟 + 1)⁴` gates, and for **every writer of the stored words on valid
clean inputs** (`GeneralSparseAccess.QData.Writer`: `W|i, j, 0⟩ = c_{ij}|i, j, w_{ij}⟩` for
`i, j < N`, any phases, any unitary action on invalid index words and dirty targets) and every
instance whose matrix is Hermitian with row and column Euclidean norms at most `η` has full-output
error at most `ε` on the clean embedding of the index register, against the evolution of the matrix
extended by zero to the index words `≥ N`, with an untouched reference. Formal restrictions:
`formal_binaryDecoder` (review item B2). -/
theorem hs_thm_gates_general_writer {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (Kd : ℕ) {𝒢 : Set Kind}
    {X₁ X₂ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ}
    (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b) (bd : ℕ)
        (c0 η t ε : ℝ),
        2 ^ k < 2 * N → formal_binaryDecoder D c0 → comp_bits b bd [c0, η] →
        0 < η → 0 < ε → ε ≤ 1 / 2 →
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (sys : Fin k ↪ W)
          (Cc : List (NInstr W (PY k b) NativeSparseBlockEncoding.Query)),
          (∀ i ∈ Cc, i.Valid) ∧ (∀ g, NInstr.gate g ∈ Cc → GateOf 𝒢 g) ∧
          (nCallsN (fun _ => true) Cc : ℝ) ≤ 6635520 * mainBound s (η * |t|) ε ∧
          (nGatesN Cc : ℝ) ≤ C * mainBound s (η * |t|) ε *
            (bitH bd N (mainBound s (η * |t|) ε) ε + 1) ^ 4 ∧
          ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
            (Wr : GeneralSparseAccess.QData.Writer D) (x : X),
            (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            FullOutputError (nrun (Wr.prims (R := R) x) Cc) (cleanAlong sys)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) (Equiv.refl _) (SparseStateOverlap.matrixOperator (D.padMat x)))) ε := by
  obtain ⟨L', c₀', c₁', hc₀', hc₁', hS, hL'⟩ := synthesis_of_parts hc₀ hc₁
    ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  obtain ⟨C₀', hC₀', hbin⟩ := hs_thm_gates.{u, 0, w} hc₀ hc₁ Kd ext_singleQubitSynthesis
    ext_singleQubitLength ext_controlDecomposition
  -- one constant for the gates and the calls of the circuit of the padded data
  set C₀ : ℝ := C₀' + 552960 with hC₀def
  have hC₀ : 0 < C₀ := by rw [hC₀def]; linarith
  have hC₀le : C₀' ≤ C₀ := by rw [hC₀def]; linarith
  have hC₀c : (552960 : ℝ) ≤ C₀ := by rw [hC₀def]; linarith
  set a : ℝ := 4 * 6 ^ 4 with ha
  set cG : ℝ := (a + 256 * (1 + (c₁' * (Real.log (2 * ((a + 256) * C₀ + 2)) + ((4 : ℕ) : ℝ) + 1) +
    c₀'))) * C₀ with hcG
  have hcG0 : 0 ≤ cG := by
    have : 0 ≤ Real.log (2 * ((a + 256) * C₀ + 2)) := Real.log_nonneg (by nlinarith)
    positivity
  set C : ℝ := cG + 1 with hC
  refine ⟨C, by rw [hC]; linarith, ?_⟩
  intro X N s k b D bd c0 η t ε hk hF hbits hη hε hε2
  have hz₀ := hF.zero
  have hεh : 0 < ε / 2 := by positivity
  have hε1 : ε ≤ 1 := by linarith
  obtain ⟨W, _, _, sys, Cc, hv, hg, hcalls, hgates, herr⟩ :=
    hbin (D.padData (fun _ => false) hz₀) (Equiv.refl _) (sbP s) bd c0 η t (ε / 2)
      (padFormat D _ hz₀ hF.hb hF.hc0 hF.dec) hbits hη hεh (by linarith)
  -- the parameters
  set τ : ℝ := η * |t| with hτdef
  have hτ : 0 ≤ τ := by positivity
  set q := mainBound s τ ε with hqdef
  have hq2 : 1 / 2 ≤ q := by rw [hqdef, ← shape_eq_mainBound]; exact shape_ge_half s hτ hε hε2
  have hq0 : 0 < q := by linarith
  set q' := mainBound (sP s) τ (ε / 2) with hq'def
  have hq'q : q' ≤ 4 * q := mainBound_pad_le D.slots_pos hτ hε hε2
  have hq'0 : 0 ≤ q' := by
    have := shape_ge_half (sP s) hτ hεh (by linarith)
    rw [shape_eq_mainBound] at this
    linarith
  set B := bitH bd N q ε + 1 with hBdef
  have hY1 : 1 ≤ (q + 1) / ε := by rw [le_div_iff₀ hε]; linarith
  have hlogY : 0 ≤ Real.logb 2 ((q + 1) / ε) := Real.logb_nonneg one_lt_two hY1
  have hlogN : 0 ≤ Real.logb 2 ((N : ℝ) + 1) :=
    Real.logb_nonneg one_lt_two (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  have hB1 : 1 ≤ B := by rw [hBdef]; unfold bitH; linarith
  have hBY : Real.logb 2 ((q + 1) / ε) ≤ B := by rw [hBdef]; unfold bitH; linarith
  have hBk : (k : ℝ) ≤ B := by
    have := k_le_logb hk
    rw [hBdef]; unfold bitH; linarith
  have hBb : (b : ℝ) ≤ B := by
    have : (b : ℝ) ≤ bd := by exact_mod_cast hbits.1
    rw [hBdef]; unfold bitH; linarith
  -- the word of the padded data
  have hcard : Fintype.card (Cfg (Fin (k + 1))) = 2 ^ (k + 1) := card_eq_two_pow (Equiv.refl _)
  have hB' : bitH bd (Fintype.card (Cfg (Fin (k + 1)))) q' (ε / 2) + 1 ≤ 6 * B := by
    rw [hcard]
    have h1 := logb_pow_succ_le hk
    have h2 := logb_scale_le hq'0 hq'q hε
    rw [hBdef]
    unfold bitH
    linarith
  have hB'0 : 0 ≤ bitH bd (Fintype.card (Cfg (Fin (k + 1)))) q' (ε / 2) + 1 := by
    have := bitH_nonneg bd (Fintype.card (Cfg (Fin (k + 1)))) hq'0 hεh (by linarith)
    linarith
  -- the counts of the circuit of the padded data
  have hq'c : (552960 : ℝ) * q' ≤ 552960 * (4 * q) := mul_le_mul_of_nonneg_left hq'q (by norm_num)
  have hnC : (nCallsN (fun _ => true) Cc : ℝ) ≤ 4 * C₀ * q := by
    have h1 : (552960 : ℝ) * (4 * q) ≤ C₀ * (4 * q) :=
      mul_le_mul_of_nonneg_right hC₀c (by linarith)
    linarith
  have hnG : (nGatesN Cc : ℝ) ≤ a * C₀ * q * B ^ 4 := by
    have h1 : (bitH bd (Fintype.card (Cfg (Fin (k + 1)))) q' (ε / 2) + 1) ^ 4 ≤ (6 * B) ^ 4 :=
      pow_le_pow_left₀ hB'0 hB' 4
    have h2 : C₀' * q' * (bitH bd (Fintype.card (Cfg (Fin (k + 1)))) q' (ε / 2) + 1) ^ 4 ≤
        C₀ * (4 * q) * (6 * B) ^ 4 :=
      mul_le_mul (mul_le_mul hC₀le hq'q hq'0 hC₀.le) h1 (by positivity) (by positivity)
    have e : C₀ * (4 * q) * (6 * B) ^ 4 = a * C₀ * q * B ^ 4 := by rw [ha]; ring
    linarith
  have hG : (implG k b : ℝ) ≤ 64 * B := by
    unfold implG
    push_cast
    linarith
  -- the accuracy of the synthesis
  set n := nGatesN (subst (implPW N s (fun _ => false)) Cc) with hn
  set ζ : ℝ := ε / 2 / ((n : ℝ) + 1) with hζ
  have hζ0 : 0 < ζ := by positivity
  obtain ⟨hv', hg', hcalls', hgates', hn'⟩ :=
    genCircW_spec (N := N) (s := s) (fun _ => false) hS hζ0 Cc hv hg
  refine ⟨(W ⊕ GeneralSparseAccess.AW k b) ⊕ (X₂ ⊕ X₁), inferInstance, inferInstance,
    genSys (X₂ ⊕ X₁) sys, genCircW hS ζ N s (fun _ => false) Cc, hv', hg', ?_, ?_, ?_⟩
  · -- the calls
    have h1 : (nCallsN (fun _ => true) (genCircW hS ζ N s (fun _ => false) Cc) : ℝ) ≤
        3 * nCallsN (fun _ => true) Cc := by exact_mod_cast hcalls'
    linarith
  · -- the gates
    have h1 : (nGatesN (genCircW hS ζ N s (fun _ => false) Cc) : ℝ) ≤
        ((nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc * (1 + L' ζ) : ℕ) : ℝ) := by
      exact_mod_cast hgates'
    have h2 : ((nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc * (1 + L' ζ) : ℕ) : ℝ) ≤
        (a + 256 * (1 + (c₁' * (Real.log (2 * ((a + 256) * C₀ + 2)) + ((4 : ℕ) : ℝ) + 1) +
          c₀'))) * C₀ * q * B ^ 4 :=
      gen_gates_le (K := 4) (by norm_num) hq2 hB1 hC₀.le (by positivity) hc₀' hc₁' hε hε1
        hBY hnG hnC hG hn' hL'
    have h3 : cG * q * B ^ 4 ≤ C * q * B ^ 4 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hq0.le
      linarith
    have e : (a + 256 * (1 + (c₁' * (Real.log (2 * ((a + 256) * C₀ + 2)) + ((4 : ℕ) : ℝ) + 1) +
        c₀'))) * C₀ * q * B ^ 4 = cG * q * B ^ 4 := by rw [hcG]
    linarith
  · -- the error
    intro R _ _ _ Wr x hH hrow hcol
    have h1 := herr (R := R) x (D.padData_isHermitian _ hz₀ x hH) (D.padData_row_le _ hz₀ x hrow)
      (D.padData_col_le _ hz₀ x hcol)
    have h2 := genCircW_error D Wr (fun _ => false) hz₀ hS hζ0 sys Cc hv x t (ε / 2) hεh.le h1
    intro ψ hψ
    refine (h2 ψ hψ).trans ?_
    have h3 : (n : ℝ) * ζ ≤ ε / 2 := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      rw [hζ, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith


/-! ### Theorem `gate:thm:main` in general sizes with a writer -/

section Main

set_option maxHeartbeats 8000000 in
/-- **Theorem `gate:thm:main` for sparse access of general size with a writer** (handover item
B4). The hypotheses, constants and bounds of `gate_thm_main_general` (computational assumptions
on the scalar arithmetic, the finite gate set with single-qubit synthesis and exact controlled
decompositions, `formal_binaryDecoder`, `comp_bits`, the arithmetic at the public scales
`genClipBeta`, `genClipScale`, `μ ≤ η ≤ √s μ`, `η²|t|/μ ≥ 1`, `0 < ε ≤ 1/64`): one circuit over the
gate set, the supplied locators and a value writer, fixed before the writer and the instance,
uses at most `288·10¹² Q_μ` primitive sparse queries (locator calls, writer calls and inverse
writer calls), at most `C Q_μ (𝔟 + 1)^K` gates and at most `k + C (𝔟 + 1)^K` qubits, and for
**every writer of the stored words on valid clean inputs** (`GeneralSparseAccess.QData.Writer`) and
every instance whose matrix is Hermitian with row and column Euclidean norms at most `η` and entries
of modulus at most `μ` has full-output error at most `ε` on the clean embedding of the index
register, against the evolution of the matrix extended by zero to the index words `≥ N`, with an
untouched reference of any finite dimension. Formal restrictions: `formal_binaryDecoder` (review
item B2). -/
theorem gate_thm_main_general_writer (cA : ℝ) (dA : ℕ) (hcA : 0 ≤ cA) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (Kd : ℕ) {𝒢 : Set Kind} {X₁ X₂ : Type} [Fintype X₁] [DecidableEq X₁]
    [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ}
    (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b) (bd : ℕ)
        (c0 η μ t ε : ℝ),
        2 ^ k < 2 * N → formal_binaryDecoder D c0 → comp_bits b bd [c0, η, μ] →
        comp_signedArith cA dA bd k b (c0 / μ) →
        comp_clipArith cA dA bd k b μ (genClipBeta η μ t ε) (genClipScale s η μ t ε) c0 →
        μ ≤ η → η ≤ Real.sqrt s * μ → 1 ≤ η ^ 2 * |t| / μ → 0 < ε → ε ≤ 1 / 64 →
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (sys : Fin k ↪ W)
          (Cc : List (NInstr W (PY k b) NativeSparseBlockEncoding.Query)),
          (∀ i ∈ Cc, i.Valid) ∧ (∀ g, NInstr.gate g ∈ Cc → GateOf 𝒢 g) ∧
          (nCallsN (fun _ => true) Cc : ℝ) ≤ 288 * 10 ^ 12 * twoNormBound s η μ t ε ∧
          (nGatesN Cc : ℝ) ≤ C * twoNormBound s η μ t ε *
            (gateWord bd N s (twoNormBound s η μ t ε) ε + 1) ^ K ∧
          (Fintype.card W : ℝ) ≤
            k + C * (gateWord bd N s (twoNormBound s η μ t ε) ε + 1) ^ K ∧
          ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
            [FiniteDimensional ℂ R] (Wr : GeneralSparseAccess.QData.Writer D)
            (x : X),
            (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) → (∀ i j, ‖D.matrix x i j‖ ≤ μ) →
            FullOutputError (nrun (Wr.prims (R := R) x) Cc) (cleanAlong sys)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) (Equiv.refl _) (SparseStateOverlap.matrixOperator (D.padMat x)))) ε := by
  obtain ⟨L', c₀', c₁', hc₀', hc₁', hS, hL'⟩ := synthesis_of_parts hc₀ hc₁
    ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  obtain ⟨C₀', K, hC₀', hbin⟩ := gate_thm_main.{u, 0, w} cA dA hcA hc₀ hc₁ Kd
    ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  -- one constant for the gates, the qubits and the calls of the circuit of the padded data
  set C₀ : ℝ := C₀' + 24 * 10 ^ 12 with hC₀def
  have hC₀ : 0 < C₀ := by rw [hC₀def]; linarith
  have hC₀le : C₀' ≤ C₀ := by rw [hC₀def]; linarith
  have hC₀c : (24 * 10 ^ 12 : ℝ) ≤ C₀ := by rw [hC₀def]; linarith
  set K' := max K 2 with hK'
  set a : ℝ := 4 * 7 ^ K' with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  set cG : ℝ := (a + 256 * (1 + (c₁' * (Real.log (2 * ((a + 256) * C₀ + 2)) + (K' : ℝ) + 1) +
    c₀'))) * C₀ with hcG
  have hcG0 : 0 ≤ cG := by
    have h0 : 0 ≤ (a + 256) * C₀ := by positivity
    have : 0 ≤ Real.log (2 * ((a + 256) * C₀ + 2)) := Real.log_nonneg (by linarith)
    positivity
  set C : ℝ := cG + 7 ^ K' * C₀ + 16 + Fintype.card (X₂ ⊕ X₁) with hC
  have hX0 : (0 : ℝ) ≤ Fintype.card (X₂ ⊕ X₁) := Nat.cast_nonneg _
  have h7C : 0 ≤ 7 ^ K' * C₀ := by positivity
  refine ⟨C, K', by rw [hC]; linarith, ?_⟩
  intro X N s k b D bd c0 η μ t ε hk hF hbits hsa hca hμη hηs hθ hε hε64
  have hz₀ := hF.zero
  have hεh : 0 < ε / 2 := by positivity
  have hε1 : ε ≤ 1 := by linarith
  have hε2 : ε ≤ 1 / 2 := by linarith
  -- the parameters
  have hμ0 : 0 < μ := by
    by_contra h
    have h' : μ ≤ 0 := not_lt.mp h
    have : η ^ 2 * |t| / μ ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg η) (abs_nonneg t)) h'
    linarith
  have hη0 : 0 < η := lt_of_lt_of_le hμ0 hμη
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hsP : ((sP s : ℕ) : ℝ) ≤ 2 * (s : ℝ) := by
    have h' : ((sP s : ℕ) : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast (sP_lt D.slots_pos).le
    push_cast at h'
    exact h'
  have hηs' : η ≤ Real.sqrt (sP s) * μ := by
    have h1 : Real.sqrt s ≤ Real.sqrt (sP s) :=
      Real.sqrt_le_sqrt (by exact_mod_cast le_sP s)
    have := mul_le_mul_of_nonneg_right h1 hμ0.le
    linarith
  obtain ⟨W, _, _, sys, Cc, hv, hg, hcalls, hgates, hwires, herr⟩ :=
    hbin (D.padData (fun _ => false) hz₀) (Equiv.refl _) (sbP s) bd c0 η μ t (ε / 2)
      (padFormat D _ hz₀ hF.hb hF.hc0 hF.dec) hbits (comp_signedArith_succ hcA hsa)
      (comp_clipArith_succ hcA hca) hμη hηs' hθ hεh (by linarith)
  set Q := twoNormBound s η μ t ε with hQdef
  set Q' := twoNormBound (sP s) η μ t (ε / 2) with hQ'def
  have hQ1 : 1 ≤ Q := by
    have h1 : η / μ ≤ Real.sqrt s := by rw [div_le_iff₀ hμ0]; linarith
    have h2 : η ^ 2 * |t| / μ = η / μ * (η * |t|) := by field_simp
    have h3 : η / μ * (η * |t|) ≤ Real.sqrt s * (η * |t|) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h4 := le_twoNormBound (s := s) (t := t) hs0 hη0.le hμ0.le hε hε1
    nlinarith
  have hQ'0 : 0 ≤ Q' := by
    have := le_twoNormBound (s := sP s) (t := t) (Nat.cast_nonneg _) hη0.le hμ0.le hεh (by linarith)
    have : 0 ≤ Real.sqrt (sP s) * η * |t| := by positivity
    linarith
  have hQ'Q : Q' ≤ 4 * Q := by
    have h1 := twoNormBound_le_of_le (t := t) hs0 (Nat.cast_nonneg _) hsP hη0.le hμ0.le hεh
      (by linarith)
    have h2 : twoNormBound s η μ t (ε / 2) ≤ 2 * twoNormBound s η μ t ε := by
      rw [← qmu_eq, ← qmu_eq]
      exact GateOptimalPrecision.Qmu_half_le hη0.le hμ0 (by linarith) hε hε2
    linarith
  -- the budget word
  set B := gateWord bd N s Q ε + 1 with hBdef
  have hY1 : 1 ≤ (Q + 1) / ε := by rw [le_div_iff₀ hε]; linarith
  have hlogY : 0 ≤ Real.logb 2 ((Q + 1) / ε) := Real.logb_nonneg one_lt_two hY1
  have hlogN : 0 ≤ Real.logb 2 ((N : ℝ) + 1) :=
    Real.logb_nonneg one_lt_two (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hlogs : 0 ≤ Real.logb 2 ((s : ℝ) + 1) := Real.logb_nonneg one_lt_two (by linarith)
  have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  have hB1 : 1 ≤ B := by rw [hBdef]; unfold gateWord; linarith
  have hBY : Real.logb 2 ((Q + 1) / ε) ≤ B := by rw [hBdef]; unfold gateWord; linarith
  have hBk : (k : ℝ) ≤ B := by
    have := k_le_logb hk
    rw [hBdef]; unfold gateWord; linarith
  have hBb : (b : ℝ) ≤ B := by
    have : (b : ℝ) ≤ bd := by exact_mod_cast hbits.1
    rw [hBdef]; unfold gateWord; linarith
  have hBK : 1 ≤ B ^ K' := one_le_pow₀ hB1
  have hB1K : B ≤ B ^ K' := le_self_pow₀ hB1 (by omega)
  -- the word of the padded data
  have hcard : Fintype.card (Cfg (Fin (k + 1))) = 2 ^ (k + 1) := card_eq_two_pow (Equiv.refl _)
  have hB' : gateWord bd (Fintype.card (Cfg (Fin (k + 1)))) (sP s) Q' (ε / 2) + 1 ≤ 7 * B := by
    rw [hcard]
    have h1 := logb_pow_succ_le hk
    have h2 := logb_scale_le hQ'0 hQ'Q hε
    have h3 := logb_sP_le D.slots_pos
    rw [hBdef]
    unfold gateWord
    linarith
  have hB'0 : 0 ≤ gateWord bd (Fintype.card (Cfg (Fin (k + 1)))) (sP s) Q' (ε / 2) + 1 := by
    have hY' : 1 ≤ (Q' + 1) / (ε / 2) := by rw [le_div_iff₀ hεh]; linarith
    have h1 := Real.logb_nonneg one_lt_two hY'
    have hc0 : (0 : ℝ) ≤ ((Fintype.card (Cfg (Fin (k + 1))) : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : 0 ≤ Real.logb 2 (((Fintype.card (Cfg (Fin (k + 1))) : ℕ) : ℝ) + 1) :=
      Real.logb_nonneg one_lt_two (by linarith)
    have hs0' : (0 : ℝ) ≤ ((sP s : ℕ) : ℝ) := Nat.cast_nonneg _
    have h3 : 0 ≤ Real.logb 2 (((sP s : ℕ) : ℝ) + 1) :=
      Real.logb_nonneg one_lt_two (by linarith)
    unfold gateWord
    linarith
  have hpow : (gateWord bd (Fintype.card (Cfg (Fin (k + 1)))) (sP s) Q' (ε / 2) + 1) ^ K ≤
      7 ^ K' * B ^ K' := by
    calc (gateWord bd (Fintype.card (Cfg (Fin (k + 1)))) (sP s) Q' (ε / 2) + 1) ^ K
        ≤ (7 * B) ^ K := pow_le_pow_left₀ hB'0 hB' K
      _ = 7 ^ K * B ^ K := mul_pow _ _ _
      _ ≤ 7 ^ K' * B ^ K' :=
          mul_le_mul (pow_le_pow_right₀ (by norm_num) (le_max_left K 2))
            (pow_le_pow_right₀ hB1 (le_max_left K 2)) (by positivity) (by positivity)
  -- the counts of the circuit of the padded data
  have hQ'c : (24 * 10 ^ 12 : ℝ) * Q' ≤ 24 * 10 ^ 12 * (4 * Q) :=
    mul_le_mul_of_nonneg_left hQ'Q (by norm_num)
  have hnC : (nCallsN (fun _ => true) Cc : ℝ) ≤ 4 * C₀ * Q := by
    have h1 : (24 * 10 ^ 12 : ℝ) * (4 * Q) ≤ C₀ * (4 * Q) :=
      mul_le_mul_of_nonneg_right hC₀c (by linarith)
    linarith
  have hnG : (nGatesN Cc : ℝ) ≤ a * C₀ * Q * B ^ K' := by
    have h2 : C₀' * Q' * (gateWord bd (Fintype.card (Cfg (Fin (k + 1)))) (sP s) Q' (ε / 2) + 1) ^ K ≤
        C₀ * (4 * Q) * (7 ^ K' * B ^ K') :=
      mul_le_mul (mul_le_mul hC₀le hQ'Q hQ'0 hC₀.le) hpow (by positivity) (by positivity)
    have e : C₀ * (4 * Q) * (7 ^ K' * B ^ K') = a * C₀ * Q * B ^ K' := by rw [ha]; ring
    linarith
  have hG : (implG k b : ℝ) ≤ 64 * B := by
    unfold implG
    push_cast
    linarith
  -- the accuracy of the synthesis
  set n := nGatesN (subst (implPW N s (fun _ => false)) Cc) with hn
  set ζ : ℝ := ε / 2 / ((n : ℝ) + 1) with hζ
  have hζ0 : 0 < ζ := by positivity
  obtain ⟨hv', hg', hcalls', hgates', hn'⟩ :=
    genCircW_spec (N := N) (s := s) (fun _ => false) hS hζ0 Cc hv hg
  refine ⟨(W ⊕ GeneralSparseAccess.AW k b) ⊕ (X₂ ⊕ X₁), inferInstance, inferInstance,
    genSys (X₂ ⊕ X₁) sys, genCircW hS ζ N s (fun _ => false) Cc, hv', hg', ?_, ?_, ?_, ?_⟩
  · -- the calls
    have h1 : (nCallsN (fun _ => true) (genCircW hS ζ N s (fun _ => false) Cc) : ℝ) ≤
        3 * nCallsN (fun _ => true) Cc := by exact_mod_cast hcalls'
    linarith
  · -- the gates
    have h1 : (nGatesN (genCircW hS ζ N s (fun _ => false) Cc) : ℝ) ≤
        ((nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc * (1 + L' ζ) : ℕ) : ℝ) := by
      exact_mod_cast hgates'
    have h2 : ((nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc * (1 + L' ζ) : ℕ) : ℝ) ≤
        (a + 256 * (1 + (c₁' * (Real.log (2 * ((a + 256) * C₀ + 2)) + (K' : ℝ) + 1) +
          c₀'))) * C₀ * Q * B ^ K' :=
      gen_gates_le (K := K') (le_max_right K 2) (by linarith) hB1 hC₀.le (by positivity) hc₀'
        hc₁' hε hε1 hBY hnG hnC hG hn' hL'
    have h3 : cG * Q * B ^ K' ≤ C * Q * B ^ K' := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      linarith
    have e : (a + 256 * (1 + (c₁' * (Real.log (2 * ((a + 256) * C₀ + 2)) + (K' : ℝ) + 1) +
        c₀'))) * C₀ * Q * B ^ K' = cG * Q * B ^ K' := by rw [hcG]
    linarith
  · -- the qubits
    have hcW : Fintype.card ((W ⊕ GeneralSparseAccess.AW k b) ⊕ (X₂ ⊕ X₁)) =
        Fintype.card W + (6 * k + 6 + 2 * b) + Fintype.card (X₂ ⊕ X₁) := by
      rw [Fintype.card_sum, Fintype.card_sum, card_AW]
    rw [hcW]
    push_cast
    have h1 : (Fintype.card W : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + C₀ * (7 ^ K' * B ^ K') := by
      have h1a := mul_le_mul_of_nonneg_left hpow hC₀'.le
      have h1b : C₀' * (7 ^ K' * B ^ K') ≤ C₀ * (7 ^ K' * B ^ K') :=
        mul_le_mul_of_nonneg_right hC₀le (by positivity)
      linarith
    push_cast at h1
    have h2 : 6 * (k : ℝ) + 7 + 2 * b ≤ 15 * B ^ K' := by nlinarith
    have h3 : (Fintype.card (X₂ ⊕ X₁) : ℝ) ≤ Fintype.card (X₂ ⊕ X₁) * B ^ K' :=
      le_mul_of_one_le_right hX0 hBK
    have h4 : C₀ * (7 ^ K' * B ^ K') + 15 * B ^ K' + Fintype.card (X₂ ⊕ X₁) * B ^ K' ≤
        C * B ^ K' := by
      have e : C₀ * (7 ^ K' * B ^ K') + 15 * B ^ K' + Fintype.card (X₂ ⊕ X₁) * B ^ K' =
          (7 ^ K' * C₀ + 15 + Fintype.card (X₂ ⊕ X₁)) * B ^ K' := by ring
      rw [e]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    linarith
  · -- the error
    intro R _ _ _ _ Wr x hH hrow hcol hent
    have h1 := herr (R := R) x (D.padData_isHermitian _ hz₀ x hH) (D.padData_row_le _ hz₀ x hrow)
      (D.padData_col_le _ hz₀ x hcol) (D.padData_entry_le _ hz₀ x hμ0.le hent)
    have h2 := genCircW_error D Wr (fun _ => false) hz₀ hS hζ0 sys Cc hv x t (ε / 2) hεh.le h1
    intro ψ hψ
    refine (h2 ψ hψ).trans ?_
    have h3 : (n : ℝ) * ζ ≤ ε / 2 := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      rw [hζ, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith

end Main

end

end ManuscriptConformance
