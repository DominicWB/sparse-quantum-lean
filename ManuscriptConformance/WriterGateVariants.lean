import ManuscriptConformance.WriterGatesDecoder
import ManuscriptConformance.GateDecoderTiny
import ManuscriptConformance.GateDecoderBinary

/-!
# Conformance: the variants of the general-decoder gate theorems with a writer

The `tiny`, `tables` and `of_decoder` variants of the general-decoder Hamiltonian gate theorems
(`GateDecoderTiny`, `GateDecoderTables`, `GateDecoderBinary`) apply `hs_thm_gates_decoder` and
`gate_thm_main_decoder`. Their writer forms (handover item B4) apply the writer forms
`hs_thm_gates_decoder_writer`, `gate_thm_main_decoder_writer` (`WriterGatesDecoder`) in the same
way, for the primitives `Wr.prims x` of every writer of the stored words specified on the clean
inputs of the valid index pairs only:

* `QData.Writer.dropTiny`, `Writer.prims_dropTiny`: a writer of `D` is a writer of the data
  `D.dropTiny small` with the thresholded decoder (the same table), with the same primitives;
* `hs_thm_gates_decoder_tiny_writer`, `gate_thm_main_decoder_tiny_writer`,
  `hs_thm_gates_decoder_tables_writer`, `gate_thm_main_decoder_tables_writer`,
  `hs_thm_gates_general_of_decoder_writer`, `gate_thm_main_general_of_decoder_writer`: the
  hypotheses, constants, bounds and error clauses of the released variants.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

namespace SparseHamiltonian.GeneralSparseAccess.QData.Writer

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary SparseHamiltonian.GeneralDecoder
open SparseHamiltonian.OracleCircuit
open NativeSparseBlockEncoding (Query)

variable {X : Type*} {N s k b : ℕ} {D : QData X N s k b}

/-- **A writer of the stored words is a writer for the thresholded decoder**: the data
`D.dropTiny small` have the table of `D`. -/
def dropTiny (Wr : D.Writer) (small : Cfg (VW b) → Bool) : (D.dropTiny small).Writer where
  op := Wr.op
  phase := Wr.phase
  unitary := Wr.unitary
  write := Wr.write

/-- The writer for the thresholded decoder has the primitives of the writer. -/
theorem prims_dropTiny (Wr : D.Writer) (small : Cfg (VW b) → Bool) {R : Type*}
    [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R] (x : X) :
    (Wr.dropTiny small).prims (R := R) x = Wr.prims (R := R) x := by
  funext j
  cases j <;> rfl

end

end SparseHamiltonian.GeneralSparseAccess.QData.Writer

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit
  SparseHamiltonian.GateNative SparseHamiltonian.GateSynth SparseHamiltonian.GateBinary
  SparseHamiltonian.GateBitBudget SparseHamiltonian.GeneralSparseAccess
  SparseHamiltonian.GeneralDecoder
open GateOptimalPrecision (FactorArithOK)
open GateOptimalBinary (bitsFor clipBT clipBP)
open SparseHamiltonian.SparseValuePrecision (matrixOperator_star_eq)
open scoped InnerProduct

universe u v w

set_option maxHeartbeats 8000000 in
/-- **Theorem `hs:thm:gates` for general decoders without the phase of tiny entries, with a
writer** (handover item B4): `hs_thm_gates_decoder_tiny` for the primitives `Wr.prims x` of every
writer of the stored words on valid clean inputs (`hs_thm_gates_decoder_writer` for the
thresholded data `D.dropTiny small`, which has the same table, through `Writer.dropTiny`). -/
theorem hs_thm_gates_decoder_tiny_writer (cA : ℝ) (dA : ℕ) (hcA : 0 ≤ cA) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (Kd : ℕ) {𝒢 : Set Kind}
    {X₁ X₂ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ}
    (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b) (bd : ℕ)
        (η t ε : ℝ) (small : Cfg (VW b) → Bool) (τ : ℝ),
        2 ^ k < 2 * N → b ≤ bd → 0 ≤ τ →
        (∀ w, small w = true → ‖D.val w‖ ≤ τ) →
        (∀ w w', D.val w' = star (D.val w) → small w' = small w) →
        comp_rotArith cA dA bd k b (dropVal small D.val) (1 / η) (Real.sqrt (2 * s) / η) →
        0 < η → 0 < ε → ε ≤ 1 / 2 →
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (sys : Fin k ↪ W)
          (Cc : List (NInstr W (PY k b) NativeSparseBlockEncoding.Query)),
          (∀ i ∈ Cc, i.Valid) ∧ (∀ g, NInstr.gate g ∈ Cc → GateOf 𝒢 g) ∧
          (nCallsN (fun _ => true) Cc : ℝ) ≤ 6635520 * mainBound s (η * |t|) ε ∧
          (nGatesN Cc : ℝ) ≤ C * mainBound s (η * |t|) ε *
            (bitH bd N (mainBound s (η * |t|) ε) ε + 1) ^ K ∧
          ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
            (Wr : GeneralSparseAccess.QData.Writer D) (x : X),
            (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            FullOutputError (nrun (Wr.prims (R := R) x) Cc) (cleanAlong sys)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) (Equiv.refl _) (SparseStateOverlap.matrixOperator (D.padMat x))))
              (ε + |t| * ((s : ℝ) * τ)) := by
  obtain ⟨C, K, hC, h⟩ := hs_thm_gates_decoder_writer.{u, w} cA dA hcA hc₀ hc₁ Kd
    ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  refine ⟨C, K, hC, ?_⟩
  intro X N s k b D bd η t ε small τ hk hbd hτ hsm hsym hdec hη hε hε2
  obtain ⟨W, hW, hWd, sys, Cc, hv, hg, hcalls, hgates, herr⟩ :=
    h (D.dropTiny small) bd η t ε hk hbd hdec hη hε hε2
  refine ⟨W, hW, hWd, sys, Cc, hv, hg, hcalls, hgates, ?_⟩
  intro R _ _ _ Wr x hH hrow hcol
  have h' := herr (R := R) (Wr.dropTiny small) x (D.dropTiny_isHermitian hsym x hH)
    (D.dropTiny_row small x hrow) (D.dropTiny_col small x hcol)
  rw [GeneralSparseAccess.QData.Writer.prims_dropTiny] at h'
  exact fullOutputError_dropTiny D hτ hsm hsym sys _ x hH t ε h'

set_option maxHeartbeats 8000000 in
/-- **Theorem `gate:thm:main` for general decoders without the phase of tiny entries, with a
writer**: `gate_thm_main_decoder_tiny` for the primitives `Wr.prims x` of every writer of the
stored words on valid clean inputs (`gate_thm_main_decoder_writer` for `D.dropTiny small`). -/
theorem gate_thm_main_decoder_tiny_writer (cA : ℝ) (dA : ℕ) (hcA : 0 ≤ cA) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (Kd : ℕ) {𝒢 : Set Kind} {X₁ X₂ : Type} [Fintype X₁]
    [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ}
    (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b) (bd : ℕ)
        (η μ t ε : ℝ) (small : Cfg (VW b) → Bool) (τ : ℝ),
        2 ^ k < 2 * N → b ≤ bd → 0 ≤ τ →
        (∀ w, small w = true → ‖D.val w‖ ≤ τ) →
        (∀ w w', D.val w' = star (D.val w) → small w' = small w) →
        comp_rotArith cA dA bd k b (dropVal small D.val) (1 / η) (Real.sqrt (2 * s) / η) →
        comp_signedArithV cA dA bd k b (dropVal small D.val) μ →
        comp_clipArithV cA dA bd k b (dropVal small D.val) μ (genClipBeta η μ t ε)
          (genClipScale s η μ t ε) →
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
            [FiniteDimensional ℂ R] (Wr : GeneralSparseAccess.QData.Writer D) (x : X),
            (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) → (∀ i j, ‖D.matrix x i j‖ ≤ μ) →
            FullOutputError (nrun (Wr.prims (R := R) x) Cc) (cleanAlong sys)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) (Equiv.refl _) (SparseStateOverlap.matrixOperator (D.padMat x))))
              (ε + |t| * ((s : ℝ) * τ)) := by
  obtain ⟨C, K, hC, h⟩ := gate_thm_main_decoder_writer.{u, w} cA dA hcA hc₀ hc₁ Kd
    ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  refine ⟨C, K, hC, ?_⟩
  intro X N s k b D bd η μ t ε small τ hk hbd hτ hsm hsym hdec hsg hcl hμη hημ hτμ hε hε2
  obtain ⟨W, hW, hWd, sys, Cc, hv, hg, hcalls, hgates, hcard, herr⟩ :=
    h (D.dropTiny small) bd η μ t ε hk hbd hdec hsg hcl hμη hημ hτμ hε hε2
  refine ⟨W, hW, hWd, sys, Cc, hv, hg, hcalls, hgates, hcard, ?_⟩
  intro R _ _ _ _ Wr x hH hrow hcol hent
  have h' := herr (R := R) (Wr.dropTiny small) x (D.dropTiny_isHermitian hsym x hH)
    (D.dropTiny_row small x hrow)
    (D.dropTiny_col small x hcol) (D.dropTiny_entry small x hent)
  rw [GeneralSparseAccess.QData.Writer.prims_dropTiny] at h'
  exact fullOutputError_dropTiny D hτ hsm hsym sys _ x hH t ε h'

set_option maxHeartbeats 4000000 in
/-- **Fixed-width variant of Theorem `hs:thm:gates` with a writer**: `hs_thm_gates_decoder_tables`
for the primitives `Wr.prims x` of every writer of the stored words on valid clean inputs
(`hs_thm_gates_decoder_writer` with the lookup tables of `comp_rotArith_tables`). -/
theorem hs_thm_gates_decoder_tables_writer (b₀ : ℕ) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (Kd : ℕ) {𝒢 : Set Kind}
    {X₁ X₂ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ}
    (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b) (bd : ℕ)
        (η t ε : ℝ),
        b ≤ b₀ → 2 ^ k < 2 * N → b ≤ bd → 0 < η → 0 < ε → ε ≤ 1 / 2 →
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (sys : Fin k ↪ W)
          (Cc : List (NInstr W (PY k b) NativeSparseBlockEncoding.Query)),
          (∀ i ∈ Cc, i.Valid) ∧ (∀ g, NInstr.gate g ∈ Cc → GateOf 𝒢 g) ∧
          (nCallsN (fun _ => true) Cc : ℝ) ≤ 6635520 * mainBound s (η * |t|) ε ∧
          (nGatesN Cc : ℝ) ≤ C * mainBound s (η * |t|) ε *
            (bitH bd N (mainBound s (η * |t|) ε) ε + 1) ^ K ∧
          ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
            (Wr : GeneralSparseAccess.QData.Writer D) (x : X),
            (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            FullOutputError (nrun (Wr.prims (R := R) x) Cc) (cleanAlong sys)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) (Equiv.refl _) (SparseStateOverlap.matrixOperator (D.padMat x)))) ε := by
  obtain ⟨C, K, hC, h⟩ := hs_thm_gates_decoder_writer.{u, w} (tableConst b₀) 1
    (tableConst_nonneg b₀)
    hc₀ hc₁ Kd ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  refine ⟨C, K, hC, ?_⟩
  intro X N s k b D bd η t ε hb hk hbd hη hε hε2
  exact h D bd η t ε hk hbd
    (comp_rotArith_cmono (tableConst_mono hb) (comp_rotArith_tables _ _ _ _ _ _)) hη hε hε2

set_option maxHeartbeats 4000000 in
/-- **Fixed-width variant of Theorem `gate:thm:main` with a writer**:
`gate_thm_main_decoder_tables` for the primitives `Wr.prims x` of every writer of the stored
words on valid clean inputs. -/
theorem gate_thm_main_decoder_tables_writer (b₀ : ℕ) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (Kd : ℕ) {𝒢 : Set Kind} {X₁ X₂ : Type} [Fintype X₁] [DecidableEq X₁]
    [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ}
    (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b) (bd : ℕ)
        (η μ t ε : ℝ),
        b ≤ b₀ → 2 ^ k < 2 * N → b ≤ bd →
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
            [FiniteDimensional ℂ R] (Wr : GeneralSparseAccess.QData.Writer D) (x : X),
            (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) → (∀ i j, ‖D.matrix x i j‖ ≤ μ) →
            FullOutputError (nrun (Wr.prims (R := R) x) Cc) (cleanAlong sys)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) (Equiv.refl _) (SparseStateOverlap.matrixOperator (D.padMat x)))) ε := by
  obtain ⟨C, K, hC, h⟩ := gate_thm_main_decoder_writer.{u, w} (tableConst b₀) 1
    (tableConst_nonneg b₀)
    hc₀ hc₁ Kd ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  refine ⟨C, K, hC, ?_⟩
  intro X N s k b D bd η μ t ε hb hk hbd hμη hηs hθ hε hε64
  exact h D bd η μ t ε hk hbd
    (comp_rotArith_cmono (tableConst_mono hb) (comp_rotArith_tables _ _ _ _ _ _))
    (comp_signedArithV_cmono (tableConst_mono hb) (comp_signedArithV_tables _ _ _ _ _))
    (comp_clipArithV_cmono (tableConst_mono hb) (comp_clipArithV_tables _ _ _ _ _ _ _))
    hμη hηs hθ hε hε64

set_option maxHeartbeats 4000000 in
/-- **`hs_thm_gates_decoder_writer` under the hypotheses of `hs_thm_gates_general`**:
`hs_thm_gates_general_of_decoder` for the primitives `Wr.prims x` of every writer of the stored
words on valid clean inputs. -/
theorem hs_thm_gates_general_of_decoder_writer {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (Kd : ℕ)
    {𝒢 : Set Kind} {X₁ X₂ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂]
    {L : ℝ → ℕ} (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b) (bd : ℕ)
        (c0 η t ε : ℝ),
        2 ^ k < 2 * N → formal_binaryDecoder D c0 → comp_bits b bd [c0, η] →
        0 < η → 0 < ε → ε ≤ 1 / 2 →
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (sys : Fin k ↪ W)
          (Cc : List (NInstr W (PY k b) NativeSparseBlockEncoding.Query)),
          (∀ i ∈ Cc, i.Valid) ∧ (∀ g, NInstr.gate g ∈ Cc → GateOf 𝒢 g) ∧
          (nCallsN (fun _ => true) Cc : ℝ) ≤ 6635520 * mainBound s (η * |t|) ε ∧
          (nGatesN Cc : ℝ) ≤ C * mainBound s (η * |t|) ε *
            (bitH bd N (mainBound s (η * |t|) ε) ε + 1) ^ K ∧
          ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
            (Wr : GeneralSparseAccess.QData.Writer D) (x : X),
            (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            FullOutputError (nrun (Wr.prims (R := R) x) Cc) (cleanAlong sys)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) (Equiv.refl _) (SparseStateOverlap.matrixOperator (D.padMat x)))) ε := by
  obtain ⟨C, K, hC, h⟩ := hs_thm_gates_decoder_writer.{u, w} (2 * 10 ^ 7) 3 (by norm_num) hc₀ hc₁ Kd
    ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  refine ⟨C, K, hC, ?_⟩
  intro X N s k b D bd c0 η t ε hk hF hbits hη hε hε2
  have hrot := comp_rotArith_binary D hF hbits hη
  obtain ⟨hbd, -, -⟩ := hbits
  exact h D bd η t ε hk hbd hrot hη hε hε2

set_option maxHeartbeats 4000000 in
/-- **`gate_thm_main_decoder_writer` under the hypotheses of `gate_thm_main_general`**:
`gate_thm_main_general_of_decoder` for the primitives `Wr.prims x` of every writer of the stored
words on valid clean inputs. -/
theorem gate_thm_main_general_of_decoder_writer (cA : ℝ) (dA : ℕ) (hcA : 0 ≤ cA) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (Kd : ℕ) {𝒢 : Set Kind} {X₁ X₂ : Type} [Fintype X₁]
    [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ}
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
            [FiniteDimensional ℂ R] (Wr : GeneralSparseAccess.QData.Writer D) (x : X),
            (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) → (∀ i j, ‖D.matrix x i j‖ ≤ μ) →
            FullOutputError (nrun (Wr.prims (R := R) x) Cc) (cleanAlong sys)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) (Equiv.refl _) (SparseStateOverlap.matrixOperator (D.padMat x)))) ε := by
  obtain ⟨C, K, hC, h⟩ := gate_thm_main_decoder_writer.{u, w} (max cA (2 * 10 ^ 7)) (max dA 3)
    (le_max_of_le_left hcA) hc₀ hc₁ Kd ext_singleQubitSynthesis ext_singleQubitLength
    ext_controlDecomposition
  refine ⟨C, K, hC, ?_⟩
  intro X N s k b D bd c0 η μ t ε hk hF hbits hsa hca hμη hηs hθ hε hε64
  have hμ0 : 0 < μ := by
    by_contra hμ
    have h' : μ ≤ 0 := not_lt.mp hμ
    have : η ^ 2 * |t| / μ ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg η) (abs_nonneg t)) h'
    linarith
  have hη : 0 < η := lt_of_lt_of_le hμ0 hμη
  obtain ⟨hbd, hc0b, hηb, -⟩ := hbits
  have hbits' : comp_bits b bd [c0, η] := ⟨hbd, hc0b, hηb⟩
  exact h D bd η μ t ε hk hbd
    (comp_rotArith_cmono (le_max_right _ _)
      (comp_rotArith_dmono (by norm_num) (le_max_right _ _) (comp_rotArith_binary D hF hbits' hη)))
    (comp_signedArithV_cmono (le_max_left _ _)
      (comp_signedArithV_dmono hcA (le_max_left _ _) (comp_signedArithV_binary D hF hsa)))
    (comp_clipArithV_cmono (le_max_left _ _)
      (comp_clipArithV_dmono hcA (le_max_left _ _) (comp_clipArithV_binary D hF hca)))
    hμη hηs hθ hε hε64

end

end ManuscriptConformance
