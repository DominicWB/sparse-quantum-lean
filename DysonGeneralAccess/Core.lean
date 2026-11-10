import DysonGeneralAccess.Assemble

set_option autoImplicit false

/-!
# One heralded program from an amplified trial family over any access

Manuscript, proof of Lemma `odel:lem:dyson`: "Amplify the actual circuit using its own inverse. A
direct trial covers amplitudes above `1/2` with constant probability; for smaller amplitudes,
randomised amplification with a bounded schedule of `O(e^z ḡ)` calls does so. Mixing the two
trials and repeating a constant number of times gives heralded success probability at least `2/3`
without changing the conditional direction." The
released trial families carry the complete certificate `ODECompleteTrial.Certificate` of the
four-attempt retry wrapper; `DysonSingleProgram` turns such a family into one program over the ODE
lower-bound access. This module does it over an arbitrary unitary access `O` (for instance the
Dyson access with source interfaces, labels `Sum.inr`) and for an arbitrary relation of valid
instances, which is what the general access of Lemma `odel:lem:dyson` needs.

* `attempts`: the four-attempt stage with coherent cutoffs (`Coherent.trial`,
  `Parallel.Stage.four`) of a preparation `a` and fixed unitaries `U₁ U₂ U₃`, with the
  first-success herald and readout of the output isometry;
* `cost_attempts`: its program costs `4 (2(M - 1) + 1)` times the preparation, for every weight;
* `good_attempts`: it reproduces the released four-attempt wrapper
  `ODERepeatProtocol.fourTrials` of a trial family with the amplification shape of `a`;
* `single`: the heralded single program (`Model.HeraldedSolver`) for every relation `Valid`
  whose instances all carry the released complete certificate; `single_success`: its heralded
  success is the released success mass; `single_matrix_le`: its weighted count is at most the
  released worst-case matrix count `1274019840 g' queryShape s' Θ ℓ`.
-/

namespace DysonGeneralAccess.Core

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit Model
open DysonSingleProgram DysonSingleProgram.Register DysonSingleProgram.Parallel
open scoped InnerProduct InnerProductSpace

variable {X L : Type*} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [CompleteSpace W] [FiniteDimensional ℂ W] {N : Type} [Fintype N] [DecidableEq N]
  {O : L → X → W →L[ℂ] W}

/-- **The four-attempt stage of a preparation**: four attempts with coherent cutoffs (label
register `Fin M`, seed `Coherent.labelSeed M ψ`), each on its own register, with the
first-success herald and readout of the output isometry `out`. -/
def attempts (M : ℕ) (a : MultiOracleCircuit.Program O) {U₁ U₂ U₃ : W →L[ℂ] W}
    (h₁ : IsUnitary U₁) (h₂ : IsUnitary U₂) (h₃ : IsUnitary U₃) (ψ : W)
    (out : EuclideanSpace ℂ N →L[ℂ] W) (i₀ : N) : Stage O M N :=
  Stage.four (Coherent.trial M a h₁ h₂ h₃) (Coherent.labelSeed M ψ) out i₀

/-- **The calls of the four attempts**: `4 (2(M - 1) + 1)` times those of the preparation, for
every weight. -/
theorem cost_attempts (M : ℕ) (a : MultiOracleCircuit.Program O) {U₁ U₂ U₃ : W →L[ℂ] W}
    (h₁ : IsUnitary U₁) (h₂ : IsUnitary U₂) (h₃ : IsUnitary U₃) (ψ : W)
    (out : EuclideanSpace ℂ N →L[ℂ] W) (i₀ : N) (w : L → ℕ) :
    (Assemble.flatProg (attempts M a h₁ h₂ h₃ ψ out i₀)).cost w =
      4 * ((2 * (M - 1) + 1) * a.cost w) := by
  unfold attempts
  rw [Assemble.cost_flatProg, Cost.cost_four, Cost.cost_trial]

/-- **The four attempts reproduce the released wrapper**: for a trial family `q` with the
amplification shape of `a`, the stage `attempts` reproduces
`ODERepeatProtocol.fourTrials q M ψ out` (`Parallel.Stage.Good`). -/
theorem good_attempts (hO : ∀ l x, IsUnitary (O l x)) {Lq : Type*} {Oq : Lq → X → W →L[ℂ] W}
    (q : ℕ → MultiOracleCircuit.Program Oq) (M : ℕ) (hM : 0 < M) (ψ : W) (hψ : ‖ψ‖ = 1)
    (out : EuclideanSpace ℂ N →L[ℂ] W) (hout : out.adjoint ∘L out = 1) (i₀ : N)
    (a : MultiOracleCircuit.Program O) (wq : Lq → ℕ) (wa : L → ℕ) {U₁ U₂ U₃ : W →L[ℂ] W}
    (hshape : GroverShape q wq a wa U₁ U₂ U₃) :
    (attempts M a hshape.unitary₁ hshape.unitary₂ hshape.unitary₃ ψ out i₀).Good
      (Coherent.labelSeed M ψ) (ODERepeatProtocol.fourTrials q M hM ψ hψ out hout) :=
  Stage.good_four hO (Coherent.trial M a _ _ _) (Coherent.labelSeed M ψ)
    (Coherent.norm_labelSeed M hM ψ hψ) q hM ψ hψ out hout
    (fun x => Coherent.trial_eval_labelSeed M a q wq wa hshape hO hM ψ hψ out hout x) i₀

/-- **The heralded single program of an amplified trial family** (proof of Lemma
`odel:lem:dyson`, amplification step): for a trial family `q` over a source-labelled access with
the amplification shape of a preparation `a` over `O`, and a relation `Valid` all of whose
instances carry the released complete certificate, the program `flatProg (attempts …)` over
`fiberOracle (I × Fin M) O` is a heralded single program for `Valid` (`ofGood` of
`good_attempts`). -/
def single (hO : ∀ l x, IsUnitary (O l x)) {Lq : Type*} {Oq : (Lq ⊕ Bool) → X → W →L[ℂ] W}
    (q : ℕ → MultiOracleCircuit.Program Oq) (M : ℕ) (hM : 0 < M) (ψ : W) (hψ : ‖ψ‖ = 1)
    (out : EuclideanSpace ℂ N →L[ℂ] W) (hout : out.adjoint ∘L out = 1) (i₀ : N)
    (a : MultiOracleCircuit.Program O) (wa : L → ℕ) {U₁ U₂ U₃ : W →L[ℂ] W}
    (hshape : GroverShape q (ODESourceQueryBudget.matrixWeight (fun _ => 1)) a wa U₁ U₂ U₃)
    (Valid : X → EuclideanSpace ℂ N → Prop) (s' Θ ell g' ε : ℝ)
    (hcert : ∀ x y, Valid x y → ODECompleteTrial.Certificate q M ψ out x y s' Θ ell g' ε) :
    HeraldedSolver
      (fiberOracle ((attempts M a hshape.unitary₁ hshape.unitary₂ hshape.unitary₃ ψ out i₀).I ×
        Fin M) O) Valid
      (Joint (attempts M a hshape.unitary₁ hshape.unitary₂ hshape.unitary₃ ψ out i₀).Γ
        (Joint (Fin M) W)) ε :=
  Assemble.ofGood _ (Coherent.labelSeed M ψ) (Coherent.norm_labelSeed M hM ψ hψ)
    (ODERepeatProtocol.fourTrials q M hM ψ hψ out hout) Valid ε
    (good_attempts hO q M hM ψ hψ out hout i₀ a _ wa hshape)
    (fun x y hv => (hcert x y hv).success_two_thirds)
    (fun x y hv B hB hB1 => DysonSingleProgram.certificate_observable (hcert x y hv) B hB hB1)

variable (hO : ∀ l x, IsUnitary (O l x)) {Lq : Type*} {Oq : (Lq ⊕ Bool) → X → W →L[ℂ] W}
    (q : ℕ → MultiOracleCircuit.Program Oq) (M : ℕ) (hM : 0 < M) (ψ : W) (hψ : ‖ψ‖ = 1)
    (out : EuclideanSpace ℂ N →L[ℂ] W) (hout : out.adjoint ∘L out = 1) (i₀ : N)
    (a : MultiOracleCircuit.Program O) (wa : L → ℕ) {U₁ U₂ U₃ : W →L[ℂ] W}
    (hshape : GroverShape q (ODESourceQueryBudget.matrixWeight (fun _ => 1)) a wa U₁ U₂ U₃)
    (Valid : X → EuclideanSpace ℂ N → Prop) (s' Θ ell g' ε : ℝ)
    (hcert : ∀ x y, Valid x y → ODECompleteTrial.Certificate q M ψ out x y s' Θ ell g' ε)

/-- `single` runs the flattened four-attempt program. -/
@[simp] theorem single_prog :
    (single hO q M hM ψ hψ out hout i₀ a wa hshape Valid s' Θ ell g' ε hcert).prog =
      Assemble.flatProg (attempts M a hshape.unitary₁ hshape.unitary₂ hshape.unitary₃ ψ out i₀) :=
  Assemble.ofGood_prog _ _ _ _ _ _ _ _ _

/-- **The calls of `single`**: `4 (2(M - 1) + 1)` times those of the preparation, for every
weight. -/
theorem single_cost (w : L → ℕ) :
    (single hO q M hM ψ hψ out hout i₀ a wa hshape Valid s' Θ ell g' ε hcert).prog.cost w =
      4 * ((2 * (M - 1) + 1) * a.cost w) := by
  rw [single_prog, cost_attempts]

/-- **The heralded success of `single` is the released success mass** of the four-attempt
wrapper, on every input. -/
theorem single_success (x : X) :
    ‖(single hO q M hM ψ hψ out hout i₀ a wa hshape Valid s' Θ ell g' ε hcert).herald
        ((single hO q M hM ψ hψ out hout i₀ a wa hshape Valid s' Θ ell g' ε hcert).prog.eval x
          (single hO q M hM ψ hψ out hout i₀ a wa hshape Valid s' Θ ell g' ε hcert).seed)‖ ^ 2 =
      (ODERepeatProtocol.fourTrials q M hM ψ hψ out hout).successMass x := by
  unfold single
  rw [Assemble.ofGood_success]

/-- **The query bound of `single`**: once one valid instance exists, its `wa`-weighted count is
at most the released worst-case matrix count `1274019840 g' queryShape s' Θ ℓ` of the
four-attempt wrapper. -/
theorem single_matrix_le (x : X) (y : EuclideanSpace ℂ N) (hv : Valid x y) :
    ((single hO q M hM ψ hψ out hout i₀ a wa hshape Valid s' Θ ell g' ε hcert).prog.cost wa : ℝ) ≤
      1274019840 * g' * ImprovedODEQueryBudget.queryShape s' Θ ell := by
  have hq := (hcert x y hv).trial.matrix_queries (M - 1) (by omega)
  rw [hshape.cost_eq (M - 1)] at hq
  rw [single_cost hO q M hM ψ hψ out hout i₀ a wa hshape Valid s' Θ ell g' ε hcert wa]
  push_cast at hq ⊢
  linarith

end

end DysonGeneralAccess.Core
