import DysonSingleProgram.Parallel.Swap

set_option autoImplicit false

/-!
# Attempts on separate registers, first-success herald and readout

Manuscript: Section `odel:sec:main` (output model) and the proof of Lemma
`odel:lem:dyson`: the solver produces a success flag of probability at
least `2/3`; conditional on success its output density is within trace distance `ε` of the
normalised solution. The released wrapper makes at most four fresh attempts and keeps the first
success (`ODERepeatProtocol.Protocol.repeatTrials t 4`). A single program makes all attempts, each
on its own register, and reads the first successful one.

A `Stage` after some attempts: a program over the main attempt register `V = ℂ^M ⊗ W` (oracle
`O` on `W`, cutoff label spectator) with spectator register `I` (parked attempts), the product
seed `Σ_i ω_i |i⟩ ⊗ μ`, a herald projection and an isometric readout onto system `ℂ^N` ⊗
garbage `ℂ^Γ ⊗ V`.

`Stage.step S C μ Fo` adds one attempt in front: the attempt program `C` runs on the main
register, `swapMain` parks its result and restores the seed `μ` of the main register, then the
previous stage runs (`Register.reflatten`, `Register.spectate`). With the success projector
`Π = Fo Fo†` of the attempt's output isometry `Fo`:

* herald `Π_1 + (1 - Π_1) P` (`heraldStep`): the first parked attempt succeeded, or it failed
  and the previous herald `P` holds (the herald is the OR of the attempt flags);
* readout (`outStep`): on `Π_1`, the decoded output `Fo†` of the first parked attempt in the
  system register, everything else garbage (`succRead`); on `1 - Π_1`, the previous readout
  (`failRead`); the two ranges go to orthogonal garbage sectors. The first-success selection is
  part of this fixed, query-free readout isometry.

`Stage.base i₀` (no attempt, herald `0`) and four steps give the single program of
`Parallel/Four.lean`. The fixed layout `Parallel.Stage.layout` and the stage's program over the
class's access, `Parallel.Stage.toAccessProg`, are defined in `DysonSingleProgram/Solver.lean`.

The step is the program form of the vector-level purification step
`ODELowerBoundExtensions.Release.purification_step` (the space `ℂ^{M × d} ⊗ H`, the new state
`trialVec ⊗ Ψ` in `coordLift` coordinates, the split `(1 ⊗ F B F†) ⊗ 1 + (1 ⊗ (1 - F F†)) ⊗ R`).
That step produces one contraction per observable; the single-program class
`SparseLowerBounds.ODE.Solver` needs one herald projection and one isometric readout serving all
observables, which `heraldStep` and `outStep` provide.
-/

namespace DysonSingleProgram.Parallel

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit Register
open ODELowerBoundExtensions.Release (coordLift tens jointFlatten jointSwap)
open scoped InnerProduct

variable {X L : Type*} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W] {M : ℕ} {N : Type} [Fintype N] [DecidableEq N]

/-- **A stage of the parallel attempts**: spectator register `I`, a program over the main
attempt register with spectator `I`, the weights `ω` of the product seed `Σ_i ω_i |i⟩ ⊗ μ`, a
herald and a readout onto system ⊗ garbage `ℂ^Γ ⊗ (ℂ^M ⊗ W)`. -/
structure Stage (O : L → X → W →L[ℂ] W) (M : ℕ) (N : Type) [Fintype N] where
  /-- The spectator register of the parked attempts. -/
  I : Type
  [fin : Fintype I]
  /-- The program. -/
  prog : MultiOracleCircuit.Program (fiberOracle I (fiberOracle (Fin M) O))
  /-- The weights of the product seed. -/
  weight : I → ℂ
  /-- The success flag. -/
  herald : Joint I (Joint (Fin M) W) →L[ℂ] Joint I (Joint (Fin M) W)
  /-- The garbage register. -/
  Γ : Type
  [gfin : Fintype Γ]
  /-- The readout onto system ⊗ garbage. -/
  out : Joint I (Joint (Fin M) W) →L[ℂ] SysGarb N (Joint Γ (Joint (Fin M) W))

attribute [instance] Stage.fin Stage.gfin

variable {O : L → X → W →L[ℂ] W}

/-- The product seed `Σ_i ω_i |i⟩ ⊗ μ` of a stage. -/
def Stage.seed (S : Stage O M N) (μ : Joint (Fin M) W) : Joint S.I (Joint (Fin M) W) :=
  WithLp.toLp 2 fun i => S.weight i • μ

/-- The readout of the empty stage: the main register as garbage, system `|i₀⟩`. -/
def baseOut (i₀ : N) :
    Joint Unit (Joint (Fin M) W) →L[ℂ] SysGarb N (Joint Unit (Joint (Fin M) W)) :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : N => Joint Unit (Joint (Fin M) W))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun i => if i = i₀ then 1 else 0

/-- **The stage without attempts**: identity program, herald `0`. -/
def Stage.base (i₀ : N) : Stage O M N where
  I := Unit
  prog := MultiOracleCircuit.Program.identity
  weight := fun _ => 1
  herald := 0
  Γ := Unit
  out := baseOut i₀

/-- **The herald after one more attempt**: `Π ⊗ 1 + (1 - Π) ⊗ P` with `Π = Fo Fo†` on the parked
attempt. -/
def heraldStep {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Fo : E →L[ℂ] W) (P : H →L[ℂ] H) :
    Joint (Coord M W) H →L[ℂ] Joint (Coord M W) H :=
  coordLift (Fo ∘L Fo.adjoint) + coordLift (1 - Fo ∘L Fo.adjoint) ∘L Joint.fiber (fun _ => P)

/-- **The success readout**: the decoded output `Fo†` of the parked attempt, system index
first, the cutoff label and the remaining registers as garbage:
`(succRead f) i j = Σ_c (Fo† b_c)_i f(j, c)`. -/
def succRead (Fo : EuclideanSpace ℂ N →L[ℂ] W) (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] : Joint (Coord M W) H →L[ℂ] SysGarb N (Joint (Fin M) H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : N => Joint (Fin M) H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun i =>
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin M => H)).symm.toContinuousLinearMap ∘L
        ContinuousLinearMap.pi fun j =>
          ∑ c : Fin (Module.finrank ℂ W),
            ((Fo.adjoint (stdOrthonormalBasis ℂ W c)) i) • Joint.proj (j, c)

/-- **The failure readout**: the previous readout on the remaining registers, the parked attempt
as garbage. -/
def failRead {H G : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] (out : H →L[ℂ] SysGarb N G) :
    Joint (Coord M W) H →L[ℂ] SysGarb N (Joint (Coord M W) G) :=
  (jointSwap (Coord M W) N G).toLinearIsometry.toContinuousLinearMap ∘L
    (PiLp.continuousLinearEquiv 2 ℂ
        (fun _ : Coord M W => SysGarb N G)).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.pi fun a => out ∘L Joint.proj a

/-- **The readout after one more attempt**: success readout on `Π ⊗ 1` into the garbage sector
`inl` (`ℂ^{M × I} ⊗ V`), previous readout on `(1 - Π) ⊗ 1` into the sector `inr`
(`ℂ^{Coord × Γ} ⊗ V`). -/
def outStep {I Γ : Type} [Fintype I] [Fintype Γ] (Fo : EuclideanSpace ℂ N →L[ℂ] W)
    (out : Joint I (Joint (Fin M) W) →L[ℂ] SysGarb N (Joint Γ (Joint (Fin M) W))) :
    Joint (Coord M W) (Joint I (Joint (Fin M) W)) →L[ℂ]
      SysGarb N (Joint ((Fin M × I) ⊕ (Coord M W × Γ)) (Joint (Fin M) W)) :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : N =>
        Joint ((Fin M × I) ⊕ (Coord M W × Γ)) (Joint (Fin M) W))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun i =>
      (PiLp.continuousLinearEquiv 2 ℂ
          (fun _ : (Fin M × I) ⊕ (Coord M W × Γ) => Joint (Fin M) W)).symm.toContinuousLinearMap ∘L
        ContinuousLinearMap.pi (Sum.elim
          (fun b : Fin M × I => Joint.proj b.2 ∘L Joint.proj b.1 ∘L Joint.proj i ∘L
            succRead Fo (Joint I (Joint (Fin M) W)) ∘L coordLift (Fo ∘L Fo.adjoint))
          (fun c : Coord M W × Γ => Joint.proj c.2 ∘L Joint.proj c.1 ∘L Joint.proj i ∘L
            failRead out ∘L coordLift (1 - Fo ∘L Fo.adjoint)))

/-- **One more attempt in front of a stage**: run `C` on the main register, park its result
(`swapMain`), run the previous stage; herald `heraldStep`, readout `outStep`, in the flattened
spectator register `Coord M W × I`. -/
def Stage.step (S : Stage O M N) (C : MultiOracleCircuit.Program (fiberOracle (Fin M) O))
    (μ : Joint (Fin M) W) (Fo : EuclideanSpace ℂ N →L[ℂ] W) : Stage O M N where
  I := Coord M W × S.I
  prog := reflatten (Coord M W) S.I
    (.seq (spectate (Coord M W) S.prog)
      (.seq (.fixed (swapMain S.I) (swapMain_unitary S.I))
        (spectate (Coord M W) (spectate S.I C))))
  weight := fun ai => coordV ai.1 μ * S.weight ai.2
  herald := (jointFlatten (Coord M W) S.I (Joint (Fin M) W)).symm.conjStarAlgEquiv
    (heraldStep Fo S.herald)
  Γ := (Fin M × S.I) ⊕ (Coord M W × S.Γ)
  out := outStep Fo S.out ∘L
    (jointFlatten (Coord M W) S.I (Joint (Fin M) W)).toLinearIsometry.toContinuousLinearMap

omit [DecidableEq N] in
/-- The step adds the calls of one attempt. -/
theorem Stage.count_step (S : Stage O M N) (C : MultiOracleCircuit.Program (fiberOracle (Fin M) O))
    (μ : Joint (Fin M) W) (Fo : EuclideanSpace ℂ N →L[ℂ] W) :
    (S.step C μ Fo).prog.count = S.prog.count + C.count := by
  show (reflatten (Coord M W) S.I _).count = _
  rw [count_reflatten]
  simp

omit [DecidableEq N] in
/-- The step adds the calls of one attempt, label by label. -/
theorem Stage.labelCount_step [DecidableEq L] (S : Stage O M N)
    (C : MultiOracleCircuit.Program (fiberOracle (Fin M) O)) (μ : Joint (Fin M) W)
    (Fo : EuclideanSpace ℂ N →L[ℂ] W) (l : L) :
    (S.step C μ Fo).prog.labelCount l = S.prog.labelCount l + C.labelCount l := by
  show (reflatten (Coord M W) S.I _).labelCount l = _
  rw [labelCount_reflatten]
  simp

omit [DecidableEq N] in
/-- **The step's program on the step's seed**: the new attempt is parked in front of the
previous stage's output, `flatten⁻¹ (C(x) μ ⊗ S(x) seed)`. -/
theorem Stage.eval_step_seed (S : Stage O M N)
    (C : MultiOracleCircuit.Program (fiberOracle (Fin M) O)) (μ : Joint (Fin M) W)
    (Fo : EuclideanSpace ℂ N →L[ℂ] W) (x : X) :
    (S.step C μ Fo).prog.eval x ((S.step C μ Fo).seed μ) =
      (jointFlatten (Coord M W) S.I (Joint (Fin M) W)).symm
        (tens (C.eval x μ) (S.prog.eval x (S.seed μ))) := by
  set e := jointFlatten (Coord M W) S.I (Joint (Fin M) W)
  have hseed : e ((S.step C μ Fo).seed μ) = tens μ (S.seed μ) := by
    ext a i : 2
    simp [e, Stage.seed, Stage.step, tens, coordV_apply, smul_smul]
  have hC : Joint.fiber (fun _ : S.I => C.eval x) (S.seed μ) =
      WithLp.toLp 2 fun i => S.weight i • C.eval x μ := by
    ext i : 1
    simp [Stage.seed, map_smul]
  show (reflatten (Coord M W) S.I _).eval x _ = _
  rw [eval_reflatten, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm]
  congr 1
  simp only [MultiOracleCircuit.Program.eval_seq, MultiOracleCircuit.Program.eval_fixed,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, eval_spectate]
  rw [hseed, ODELowerBoundExtensions.Release.fiber_tens, hC, swapMain_tens,
    ODELowerBoundExtensions.Release.fiber_tens]
  rfl

end

end DysonSingleProgram.Parallel
