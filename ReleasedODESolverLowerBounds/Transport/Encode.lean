import DeferredMeasurementLowerBounds.Access.Transport
import DeferredMeasurementLowerBounds.Access.Control
import SparseLowerBounds.Adaptive.Access

set_option autoImplicit false

/-!
# Absorbing the spectator lift into a larger physical oracle

Manuscript Section `odel:sec:main`, lines 3669-3673 (value oracle and locators, "their inverses
and controls"), lines 3685-3686 ("Initial and source preparation contain no hidden input
information") and line 2364 (deferred measurement).

The controlled-call circuits of the deferral (`DeferredMeasurementLowerBounds.Access.selCircuit`,
`ctrlCircuits`) are programs over the call forms of the spectator lift `1_J ⊗ B`
(`DeferredMeasurementLowerBounds.Access.ctrlTarget B J`). The physical oracles grant calls of one
oracle `B'` only. Labels are `L ⊕ Bool`: matrix labels `Sum.inl l` and the two source interfaces
`Sum.inr b`.

* `Absorbs B B' J`: an isometry `ℂ^J ⊗ W → W'` that intertwines `1_J ⊗ B (inl l) x` with
  `B' (inl l) x` for every matrix label and input (for the physical oracles:
  `Access.meshOracle_absorb`, `Access.constOracle_absorb`).
* `Absorbs.enc`: its control-wise lift `Joint Bool (ℂ^J ⊗ W) → Joint Bool W'`, an isometry.
* `Absorbs.circuit`: every call form of a matrix label of the spectator lift is the same call
  form of `B'`; every call form of a source label, which does not depend on the input
  (`hsrc`), is the known unitary `SubspaceOracle.lift` of its operator (no oracle call).
* `Absorbs.compileProg`: the encoded compilation (`EncodedLabeledProgram.compile`) of a program
  over `ctrlTarget B J` into a program over `callFamily B'`; it acts on the encoded subspace as
  the original program (`compileProg_eval`) and has the same weighted cost for every weight that
  vanishes on the source labels (`compileProg_cost`).
-/

namespace ReleasedODESolverLowerBounds.Transport

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open DeferredMeasurementLowerBounds.Access (ctrlTarget)
open AdaptiveODELowerBound.Access (CallForm callFamily)
open scoped InnerProduct

variable {X L : Type*} {W W' : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [CompleteSpace W] [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [CompleteSpace W']

/-- **Absorption of the spectator register `J`**: an isometry `ℂ^J ⊗ W → W'` intertwining
`1_J ⊗ B (inl l) x` with `B' (inl l) x` for every matrix label `l` and input `x`. -/
structure Absorbs (B : L ⊕ Bool → X → W →L[ℂ] W) (B' : L ⊕ Bool → X → W' →L[ℂ] W')
    (J : Type) [Fintype J] where
  /-- The absorbing isometry. -/
  emb : Joint J W →L[ℂ] W'
  /-- The absorbing map is an isometry. -/
  emb_isometry : emb† ∘L emb = 1
  /-- The absorbing map intertwines the spectator lift of every matrix label with the larger
  oracle. -/
  intertwine : ∀ l x, B' (Sum.inl l) x ∘L emb = emb ∘L Joint.fiber (fun _ : J => B (Sum.inl l) x)

variable {B : L ⊕ Bool → X → W →L[ℂ] W} {B' : L ⊕ Bool → X → W' →L[ℂ] W'} {J : Type} [Fintype J]

/-- The control-wise lift of the absorbing isometry. -/
def Absorbs.enc (h : Absorbs B B' J) : Joint Bool (Joint J W) →L[ℂ] Joint Bool W' :=
  SparseLowerBounds.Adaptive.Access.jointMap Bool h.emb

/-- The control-wise lift of the absorbing isometry is an isometry. -/
theorem Absorbs.enc_isometry (h : Absorbs B B' J) : h.enc† ∘L h.enc = 1 :=
  SparseLowerBounds.Adaptive.Access.jointMap_isometry Bool h.emb h.emb_isometry

/-- The call forms of the spectator lift are unitary
(`AdaptiveODELowerBound.Access.callFamily_unitary` for the unitary spectator lift). -/
theorem ctrlTarget_unitary (hB : ∀ l x, IsUnitary (B l x)) (c : (L ⊕ Bool) × CallForm) (x : X) :
    IsUnitary (ctrlTarget B J c x) :=
  AdaptiveODELowerBound.Access.callFamily_unitary
    (fun l x => PhaseCircuit.isUnitary_fiber _ fun _ => hB l x) c x

/-- Every call form intertwines the control-wise lift of a map that intertwines the operator and
its adjoint. -/
theorem formOp_comp_jointMap {P : Type} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [CompleteSpace P] {U' : W' →L[ℂ] W'} {U : P →L[ℂ] P} {E : P →L[ℂ] W'}
    (h1 : U' ∘L E = E ∘L U) (h2 : star U' ∘L E = E ∘L star U) (f : CallForm) :
    AdaptiveODELowerBound.Access.formOp f U' ∘L SparseLowerBounds.Adaptive.Access.jointMap Bool E =
      SparseLowerBounds.Adaptive.Access.jointMap Bool E ∘L
        AdaptiveODELowerBound.Access.formOp f U := by
  refine ContinuousLinearMap.ext fun Ψ => PiLp.ext fun d => ?_
  have e1 := DFunLike.congr_fun h1 (Ψ d)
  have e2 := DFunLike.congr_fun h2 (Ψ d)
  simp only [comp_apply] at e1 e2
  cases f <;> cases d <;>
    simp [AdaptiveODELowerBound.Access.formOp, AdaptiveODELowerBound.Access.ctrlOp,
      SparseLowerBounds.Adaptive.Access.jointMap_apply, e1, e2]

/-- **The circuit of a call form of the spectator lift** over the call forms of `B'`: one call of
the same form for a matrix label, the known lifted unitary for a source label (`x₀` is any
input; the source labels do not depend on it). -/
def Absorbs.circuit (h : Absorbs B B' J) (hB : ∀ l x, IsUnitary (B l x)) (x₀ : X) :
    (L ⊕ Bool) × CallForm → MultiOracleCircuit.Program (callFamily B')
  | (Sum.inl l, f) => .query (Sum.inl l, f)
  | (Sum.inr b, f) => .fixed (SubspaceOracle.lift h.enc (ctrlTarget B J (Sum.inr b, f) x₀))
      (SubspaceOracle.lift_unitary h.enc h.enc_isometry _ (ctrlTarget_unitary hB _ x₀))

/-- The circuits act on the encoded subspace as the call forms of the spectator lift. -/
theorem Absorbs.circuit_eval (h : Absorbs B B' J) (hB : ∀ l x, IsUnitary (B l x))
    (hB' : ∀ l x, IsUnitary (B' l x)) (hsrc : ∀ b x x', B (Sum.inr b) x = B (Sum.inr b) x')
    (x₀ x : X) (c : (L ⊕ Bool) × CallForm) :
    (h.circuit hB x₀ c).eval x ∘L h.enc = h.enc ∘L ctrlTarget B J c x := by
  obtain ⟨l | b, f⟩ := c
  · have hU : IsUnitary (Joint.fiber fun _ : J => B (Sum.inl l) x) :=
      PhaseCircuit.isUnitary_fiber _ fun _ => hB _ x
    exact formOp_comp_jointMap (h.intertwine l x)
      (EncodedOracle.adjoint_intertwines _ _ h.emb (hB' _ x) hU (h.intertwine l x)) f
  · have hx : ctrlTarget B J (Sum.inr b, f) x = ctrlTarget B J (Sum.inr b, f) x₀ := by
      simp only [ctrlTarget, callFamily, hsrc b x x₀]
    rw [hx]
    exact EncodedOracle.lift_comp h.enc h.enc_isometry _

/-- A circuit costs the weight of its label, for a weight that vanishes on the source labels. -/
theorem Absorbs.circuit_cost (h : Absorbs B B' J) (hB : ∀ l x, IsUnitary (B l x)) (x₀ : X)
    (w : L ⊕ Bool → ℕ) (hw : ∀ b, w (Sum.inr b) = 0) (c : (L ⊕ Bool) × CallForm) :
    (h.circuit hB x₀ c).cost (fun c' => w c'.1) = w c.1 := by
  obtain ⟨l | b, f⟩ := c
  · rfl
  · exact (hw b).symm

/-- **The encoded compilation** of a program over the call forms of the spectator lift into a
program over the call forms of `B'`. -/
def Absorbs.compileProg (h : Absorbs B B' J) (hB : ∀ l x, IsUnitary (B l x)) (x₀ : X)
    (p : MultiOracleCircuit.Program (ctrlTarget B J)) :
    MultiOracleCircuit.Program (callFamily B') :=
  EncodedLabeledProgram.compile h.enc h.enc_isometry (h.circuit hB x₀) p

/-- **The compiled program acts on the encoded subspace as the original program.** -/
theorem Absorbs.compileProg_eval (h : Absorbs B B' J) (hB : ∀ l x, IsUnitary (B l x))
    (hB' : ∀ l x, IsUnitary (B' l x)) (hsrc : ∀ b x x', B (Sum.inr b) x = B (Sum.inr b) x')
    (x₀ : X) (p : MultiOracleCircuit.Program (ctrlTarget B J)) (x : X) :
    (h.compileProg hB x₀ p).eval x ∘L h.enc = h.enc ∘L p.eval x :=
  EncodedLabeledProgram.compile_eval h.enc h.enc_isometry (h.circuit hB x₀)
    (AdaptiveODELowerBound.Access.callFamily_unitary hB') (ctrlTarget_unitary hB)
    (fun c x => h.circuit_eval hB hB' hsrc x₀ x c) p x

/-- **The compiled program has the weighted cost of the original program**, for a weight that
vanishes on the source labels. -/
theorem Absorbs.compileProg_cost (h : Absorbs B B' J) (hB : ∀ l x, IsUnitary (B l x)) (x₀ : X)
    (w : L ⊕ Bool → ℕ) (hw : ∀ b, w (Sum.inr b) = 0)
    (p : MultiOracleCircuit.Program (ctrlTarget B J)) :
    (h.compileProg hB x₀ p).cost (fun c => w c.1) = p.cost (fun c => w c.1) := by
  rw [Absorbs.compileProg, EncodedLabeledProgram.compile_cost]
  congr 1
  funext c
  exact h.circuit_cost hB x₀ w hw c

end

end ReleasedODESolverLowerBounds.Transport
