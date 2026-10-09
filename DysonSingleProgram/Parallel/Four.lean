import DysonSingleProgram.Parallel.Readout

set_option autoImplicit false

/-!
# Four attempts in one program

Manuscript lines 4111-4113 (Section `odel:sec:main`, output model) and 4687-4689 (proof of Lemma
`odel:lem:dyson`). The released wrapper makes at most four fresh attempts
(`ODERepeatProtocol.fourTrials`, `ODECompleteTrial.algorithm`). `Stage.four C μ Fo i₀` makes all
four attempts on separate registers in one program, with the first-success herald and readout;
it reproduces `repeatTrials t 4` (`Stage.good_four`) with exactly four times the calls of one
attempt (`Stage.count_four`, `Stage.labelCount_four`).
-/

namespace DysonSingleProgram.Parallel

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit Register
open ODELowerBoundExtensions.Release (trialVec)
open scoped InnerProduct

variable {X L : Type*} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [CompleteSpace W] [FiniteDimensional ℂ W] {M : ℕ} {N : Type} [Fintype N] [DecidableEq N]
  {O : L → X → W →L[ℂ] W}

/-- **The four-attempt stage**: four steps from the empty stage. -/
def Stage.four (C : MultiOracleCircuit.Program (fiberOracle (Fin M) O)) (μ : Joint (Fin M) W)
    (Fo : EuclideanSpace ℂ N →L[ℂ] W) (i₀ : N) : Stage O M N :=
  ((((Stage.base i₀).step C μ Fo).step C μ Fo).step C μ Fo).step C μ Fo

/-- The four-attempt program makes four times the calls of one attempt. -/
theorem Stage.count_four (C : MultiOracleCircuit.Program (fiberOracle (Fin M) O))
    (μ : Joint (Fin M) W) (Fo : EuclideanSpace ℂ N →L[ℂ] W) (i₀ : N) :
    (Stage.four C μ Fo i₀).prog.count = 4 * C.count := by
  have h0 : (Stage.base (O := O) (M := M) i₀).prog.count = 0 :=
    MultiOracleCircuit.Program.count_identity
  rw [Stage.four, Stage.count_step, Stage.count_step, Stage.count_step, Stage.count_step, h0]
  ring

/-- The four-attempt program makes four times the calls of one attempt, label by label. -/
theorem Stage.labelCount_four [DecidableEq L]
    (C : MultiOracleCircuit.Program (fiberOracle (Fin M) O))
    (μ : Joint (Fin M) W) (Fo : EuclideanSpace ℂ N →L[ℂ] W) (i₀ : N) (l : L) :
    (Stage.four C μ Fo i₀).prog.labelCount l = 4 * C.labelCount l := by
  have h0 : (Stage.base (O := O) (M := M) i₀).prog.labelCount l = 0 := rfl
  rw [Stage.four, Stage.labelCount_step, Stage.labelCount_step, Stage.labelCount_step,
    Stage.labelCount_step, h0]
  ring

/-- **The four-attempt program reproduces the released four-attempt wrapper**: if `C` prepares
the purified released attempt of `t = ofCircuits q M ψ Fo` from the unit seed `μ`, the stage
`Stage.four C μ Fo i₀` reproduces `repeatTrials t 4`. -/
theorem Stage.good_four {Lq : Type*} {Oq : Lq → X → W →L[ℂ] W} (hO : ∀ l x, IsUnitary (O l x))
    (C : MultiOracleCircuit.Program (fiberOracle (Fin M) O))
    (μ : Joint (Fin M) W) (hμ : ‖μ‖ = 1) (q : ℕ → MultiOracleCircuit.Program Oq) (hM : 0 < M)
    (ψ : W) (hψ : ‖ψ‖ = 1) (Fo : EuclideanSpace ℂ N →L[ℂ] W) (hFo : Fo.adjoint ∘L Fo = 1)
    (hC : ∀ x, C.eval x μ = trialVec (ODERepeatProtocol.ofCircuits q M hM ψ hψ Fo hFo) x)
    (i₀ : N) :
    (Stage.four C μ Fo i₀).Good μ
      (ODERepeatProtocol.fourTrials q M hM ψ hψ Fo hFo) := by
  have hrep : ODERepeatProtocol.fourTrials q M hM ψ hψ Fo hFo =
      .freshTrial (ODERepeatProtocol.ofCircuits q M hM ψ hψ Fo hFo)
        (.freshTrial (ODERepeatProtocol.ofCircuits q M hM ψ hψ Fo hFo)
          (.freshTrial (ODERepeatProtocol.ofCircuits q M hM ψ hψ Fo hFo)
            (.freshTrial (ODERepeatProtocol.ofCircuits q M hM ψ hψ Fo hFo) .abort))) := rfl
  rw [hrep]
  exact Stage.good_step hO _ C μ hμ q hM ψ hψ Fo hFo hC _ <|
    Stage.good_step hO _ C μ hμ q hM ψ hψ Fo hFo hC _ <|
    Stage.good_step hO _ C μ hμ q hM ψ hψ Fo hFo hC _ <|
    Stage.good_step hO _ C μ hμ q hM ψ hψ Fo hFo hC _ <| Stage.good_base i₀ μ

end

end DysonSingleProgram.Parallel
