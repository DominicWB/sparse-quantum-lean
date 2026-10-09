import GeneralODE.Solver.Source
import SparseODE.ODESourceQueryBudget

/-!
# Composing the solver with the history encoding and the preparation

The solver circuit is compiled to the native oracles.  Its two logical
labels, the masked history unitary and the masked preparation, are each
implemented by the released whole-program native control: every native call
of the history program and of the preparation is replaced by three ordinary
calls on one common clean encoding.  The required basis-image property holds
because the history oracles inherit it from the native oracles and the source
oracles fix every basis vector whose slot is neither `0` nor the forcing slot.

The compiled program has the solver's semantics on the clean encoding, with
`U` the history unitary and `B` the preparation.  Each logical call costs
three times the corresponding native cost: `3 K` calls of the block-encoding
program per history call, and three calls of each source per preparation.
-/

namespace SparseHamiltonian.GeneralODE.Solver

noncomputable section
open ContinuousLinearMap OracleCircuit Registers History
open scoped InnerProduct BigOperators ComplexConjugate
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem MultiOracleCircuit.Program.cost_zero {K X L : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O) :
    p.cost (fun _ => 0) = 0 := by
  have h := MultiOracleCircuit.Program.cost_le_count_mul p (fun _ => 0) 0 (fun _ => le_rfl)
  omega

variable {n PB X L : Type} [Fintype n] [DecidableEq n] [Fintype PB] [DecidableEq PB]

/-- All oracles on the solver's oracle register: the native labels on the `K`
copies of the block-encoding register, and the two source labels. -/
def totalOracle (H : HistData n PB) (O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    ((Fin H.K × L) ⊕ Bool) → X →
      EuclideanSpace ℂ (H.Sys × H.Anc) →L[ℂ] EuclideanSpace ℂ (H.Sys × H.Anc) :=
  Sum.elim (histOracle H O) (sourceOracle (m := H.m) (a := H.Anc) J₀ Jb)

theorem totalOracle_unitary (H : HistData n PB)
    (O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hO : ∀ l x, IsUnitary (O l x))
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x)) :
    ∀ l x, IsUnitary (totalOracle H O J₀ Jb l x)
  | .inl il, x => histOracle_unitary H O hO il x
  | .inr b, x => sourceOracle_unitary J₀ Jb hJ₀ hJb b x

/-- A slot different from `0` and from the forcing slot. -/
def refSlot (m : ℕ) (hm : 1 ≤ m) : Slot m := some ⟨1, by omega⟩

theorem refSlot_ne_slot0 (m : ℕ) (hm : 1 ≤ m) : refSlot m hm ≠ slot0 m := by
  simp [refSlot, slot0]

theorem refSlot_ne_none (m : ℕ) (hm : 1 ≤ m) : refSlot m hm ≠ none := by
  simp [refSlot]

/-- The reference basis vector of the native control compiler. -/
def refBasis (H : HistData n PB) (hm : 1 ≤ H.m) : H.Sys × H.Anc :=
  H.validBasis (refSlot H.m hm, H.i0)

/-- Images of the reference vector. -/
def totalImage (H : HistData n PB) (O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB)
    (img : L → X → PB)
    (hO : ∀ l x, O l x (EuclideanSpace.single H.pb0 1) = EuclideanSpace.single (img l x) 1)
    (hm : 1 ≤ H.m) : ((Fin H.K × L) ⊕ Bool) → X → H.Sys × H.Anc
  | .inl il, x => Classical.choose (histOracle_valid H O img hO (refSlot H.m hm, H.i0) il x)
  | .inr _, _ => refBasis H hm

theorem totalOracle_valid (H : HistData n PB)
    (O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (img : L → X → PB)
    (hO : ∀ l x, O l x (EuclideanSpace.single H.pb0 1) = EuclideanSpace.single (img l x) 1)
    (hm : 1 ≤ H.m) :
    ∀ l x, totalOracle H O J₀ Jb l x (EuclideanSpace.single (refBasis H hm) 1) =
      EuclideanSpace.single (totalImage H O img hO hm l x) 1
  | .inl il, x => Classical.choose_spec (histOracle_valid H O img hO (refSlot H.m hm, H.i0) il x)
  | .inr b, x => sourceOracle_single J₀ Jb (refSlot H.m hm) (refSlot_ne_slot0 H.m hm)
      (refSlot_ne_none H.m hm) H.i0 _ b x

/-- The history program in the total vocabulary. -/
def uProgram (H : HistData n PB) {O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB}
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (qP : MultiOracleCircuit.Program O) :
    MultiOracleCircuit.Program (totalOracle H O J₀ Jb) :=
  MultiOracleCircuit.Program.relabel Sum.inl (histProgram H qP)

/-- The preparation program in the total vocabulary. -/
def bProgram (H : HistData n PB) (O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (μ r₀ rb : ℝ) (hr : 0 < μ ^ 2 * rb ^ 2 + r₀ ^ 2) :
    MultiOracleCircuit.Program (totalOracle H O J₀ Jb) :=
  MultiOracleCircuit.Program.relabel Sum.inr
    (prepProgram (m := H.m) (a := H.Anc) J₀ Jb μ r₀ rb hr)

theorem uProgram_eval (H : HistData n PB)
    {O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB}
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (qP : MultiOracleCircuit.Program O) (x : X) :
    (uProgram H J₀ Jb qP).eval x = H.unitary (qP.eval x) := by
  unfold uProgram
  rw [MultiOracleCircuit.Program.eval_relabel]
  exact histProgram_eval H qP x

theorem bProgram_eval (H : HistData n PB)
    (O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (μ r₀ rb : ℝ) (hr : 0 < μ ^ 2 * rb ^ 2 + r₀ ^ 2) (x : X) :
    (bProgram H O J₀ Jb μ r₀ rb hr).eval x =
      (prepProgram (m := H.m) (a := H.Anc) J₀ Jb μ r₀ rb hr).eval x := by
  unfold bProgram
  rw [MultiOracleCircuit.Program.eval_relabel]
  rfl

section Composition

variable (H : HistData n PB) (O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB)
  (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
  (hm : 1 ≤ H.m) (qP : MultiOracleCircuit.Program O)
  (μ r₀ rb : ℝ) (hr : 0 < μ ^ 2 * rb ^ 2 + r₀ ^ 2)

/-- The oracle input seen by the solver. -/
def solverInput (x : X) : Input H.Sys H.Anc :=
  ((uProgram H J₀ Jb qP).eval x, (bProgram H O J₀ Jb μ r₀ rb hr).eval x)

/-- The native implementation of each logical solver label. -/
def letters {w : ℕ} (ctrl : Fin w → Bool) (b : Bool) :
    MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := Fin w) (totalOracle H O J₀ Jb)) :=
  NativeWholeProgramMask.program (totalOracle H O J₀ Jb) (refBasis H hm) ctrl
    (if b then bProgram H O J₀ Jb μ r₀ rb hr else uProgram H J₀ Jb qP)

/-- The compiled solver. -/
def composed {w : ℕ} (ctrl : Fin w → Bool)
    (S : MultiOracleCircuit.Program (solverOracle H.Sys H.Anc w ctrl)) :
    MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := Fin w) (totalOracle H O J₀ Jb)) :=
  EncodedLabeledProgram.compile
    (NativeMaskedOracle.input (ι := Fin w) (refBasis H hm)).toContinuousLinearMap
    (NativeMaskedOracle.input (ι := Fin w) (refBasis H hm)).adjoint_comp_self
    (letters H O J₀ Jb hm qP μ r₀ rb hr ctrl)
    (S.reindex (solverInput H O J₀ Jb qP μ r₀ rb hr))

theorem solverInput_unitary (hO : ∀ l x, IsUnitary (O l x))
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x)) (x : X) :
    IsUnitary (solverInput H O J₀ Jb qP μ r₀ rb hr x).1 ∧
      IsUnitary (solverInput H O J₀ Jb qP μ r₀ rb hr x).2 :=
  ⟨(uProgram H J₀ Jb qP).eval_unitary (totalOracle_unitary H O J₀ Jb hO hJ₀ hJb) x,
    (bProgram H O J₀ Jb μ r₀ rb hr).eval_unitary (totalOracle_unitary H O J₀ Jb hO hJ₀ hJb) x⟩

/-- The compiled solver has the solver's semantics on the common clean encoding. -/
theorem composed_eval (img : L → X → PB)
    (hvalidO : ∀ l x, O l x (EuclideanSpace.single H.pb0 1) = EuclideanSpace.single (img l x) 1)
    (hO : ∀ l x, IsUnitary (O l x))
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x))
    {w : ℕ} (ctrl : Fin w → Bool)
    (S : MultiOracleCircuit.Program (solverOracle H.Sys H.Anc w ctrl)) (x : X) :
    (composed H O J₀ Jb hm qP μ r₀ rb hr ctrl S).eval x ∘L
        (NativeMaskedOracle.input (ι := Fin w) (refBasis H hm)).toContinuousLinearMap =
      (NativeMaskedOracle.input (ι := Fin w) (refBasis H hm)).toContinuousLinearMap ∘L
        S.eval (solverInput H O J₀ Jb qP μ r₀ rb hr x) := by
  have hF := totalOracle_unitary H O J₀ Jb hO hJ₀ hJb
  have h := EncodedLabeledProgram.compile_eval
    (NativeMaskedOracle.input (ι := Fin w) (refBasis H hm)).toContinuousLinearMap
    (NativeMaskedOracle.input (ι := Fin w) (refBasis H hm)).adjoint_comp_self
    (letters H O J₀ Jb hm qP μ r₀ rb hr ctrl)
    (fun l y => NativeMaskedOracle.oracle_unitary (totalOracle H O J₀ Jb l) (hF l) y)
    (fun b y => solverOracle_unitary w ctrl _
      (solverInput_unitary H O J₀ Jb qP μ r₀ rb hr hO hJ₀ hJb y).1
      (solverInput_unitary H O J₀ Jb qP μ r₀ rb hr hO hJ₀ hJb y).2 b)
    (fun b y => by
      have hi := NativeWholeProgramMask.program_intertwines (totalOracle H O J₀ Jb) hF
        (refBasis H hm) (totalImage H O img hvalidO hm) (totalOracle_valid H O J₀ Jb img hvalidO hm)
        ctrl (if b then bProgram H O J₀ Jb μ r₀ rb hr else uProgram H J₀ Jb qP) y
      unfold letters
      rw [hi]
      unfold solverOracle solverInput
      cases b <;> rfl)
    (S.reindex (solverInput H O J₀ Jb qP μ r₀ rb hr)) x
  rw [MultiOracleCircuit.Program.eval_reindex] at h
  exact h

/-- Native matrix cost: three times `K` times the block-encoding cost per
history call; preparation calls use no matrix query. -/
theorem composed_matrix_cost {w : ℕ} (ctrl : Fin w → Bool)
    (S : MultiOracleCircuit.Program (solverOracle H.Sys H.Anc w ctrl)) (wt : L → ℕ) :
    (composed H O J₀ Jb hm qP μ r₀ rb hr ctrl S).cost
        (ODESourceQueryBudget.matrixWeight (fun il : Fin H.K × L => wt il.2)) ≤
      S.count * (3 * (H.K * qP.cost wt)) := by
  unfold composed
  rw [EncodedLabeledProgram.compile_cost, MultiOracleCircuit.Program.cost_reindex]
  apply MultiOracleCircuit.Program.cost_le_count_mul
  intro b
  unfold letters
  rw [NativeWholeProgramMask.program_cost]
  cases b
  · simp only [Bool.false_eq_true, if_false]
    unfold uProgram
    rw [MultiOracleCircuit.Program.cost_relabel]
    exact le_of_eq (congrArg (fun t => 3 * t) (histProgram_cost H qP wt))
  · simp only [if_true]
    unfold bProgram
    rw [MultiOracleCircuit.Program.cost_relabel]
    have h0 := MultiOracleCircuit.Program.cost_zero
      (prepProgram (m := H.m) (a := H.Anc) J₀ Jb μ r₀ rb hr)
    change 3 * (prepProgram (m := H.m) (a := H.Anc) J₀ Jb μ r₀ rb hr).cost (fun _ => 0) ≤ _
    rw [h0]
    omega

/-- Each source is called at most three times per logical preparation call. -/
theorem composed_source_cost {w : ℕ} (ctrl : Fin w → Bool)
    (S : MultiOracleCircuit.Program (solverOracle H.Sys H.Anc w ctrl)) (b' : Bool) :
    (composed H O J₀ Jb hm qP μ r₀ rb hr ctrl S).cost
        (ODESourceQueryBudget.sourceWeight b') ≤ S.count * 3 := by
  unfold composed
  rw [EncodedLabeledProgram.compile_cost, MultiOracleCircuit.Program.cost_reindex]
  apply MultiOracleCircuit.Program.cost_le_count_mul
  intro b
  unfold letters
  rw [NativeWholeProgramMask.program_cost]
  cases b
  · simp only [Bool.false_eq_true, if_false]
    unfold uProgram
    rw [MultiOracleCircuit.Program.cost_relabel]
    have h0 := MultiOracleCircuit.Program.cost_zero (histProgram H qP)
    change 3 * (histProgram H qP).cost (fun _ => 0) ≤ 3
    rw [h0]
    omega
  · simp only [if_true]
    unfold bProgram
    rw [MultiOracleCircuit.Program.cost_relabel]
    change 3 * (ODESourceQueryBudget.sourceWeight (L := Fin H.K × L) b' (Sum.inr true) +
      (ODESourceQueryBudget.sourceWeight (L := Fin H.K × L) b' (Sum.inr false) + 0)) ≤ 3
    cases b' <;> simp [ODESourceQueryBudget.sourceWeight]

end Composition

end

end SparseHamiltonian.GeneralODE.Solver
