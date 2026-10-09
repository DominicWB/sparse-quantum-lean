import DeferredMeasurementLowerBounds.Access.Control
import DeferredMeasurementLowerBounds.Access.Transport
import SparseLowerBounds.Helpers.HsRelease.PhaseAccess

set_option autoImplicit false

/-!
# Record-selected calls of a Boolean phase oracle

The search lower bounds of the package (`UnitaryImplementationExtensions.Search`, from the
positive-weight adversary `SparseLowerBounds.PositiveAdversary.count_ge`) are stated for
single-family unitary programs (`OracleCircuit.Program`) over a Boolean phase oracle
`P.phase y` of any projection family `P`, on any workspace.

For a measured algorithm over one phase-oracle label, every deferred selection label is one
call of the phase oracle of the controlled spectator family
`ctrlFamily (P.spectate R)` (whose phase oracle is `ctrl(1_R ⊗ P.phase y)`,
`phase_ctrlSpectate`) between two control flips of the unselected records, on the active
sector (`phaseCircuit_eval`); the direction does not matter since a phase oracle is its own
inverse. A counted pattern costs at most one call (`phaseCircuit_count`). The compiled deferred
program is a one-label program; `MultiOracleCircuit.Program.compile` with the single query turns
it into a single-family program with the same evaluation and count.
-/

namespace DeferredMeasurementLowerBounds.Access

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open DeferredMeasurementLowerBounds.Model DeferredMeasurementLowerBounds.Deferral
open AdaptiveODELowerBound.Access (ctrlFamily ctrlOp activeEmbed)
open scoped InnerProduct

variable {K X I : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [Fintype I]

variable {R : Type} [Fintype R]

/-- The phase oracle of the controlled spectator family is the controlled spectated phase
oracle. -/
theorem phase_ctrlSpectate (P : ProjFamily K I) (y : I → Bool) :
    (ctrlFamily (P.spectate R)).phase y = ctrlOp (Joint.fiber fun _ : R => P.phase y) := by
  rw [AdaptiveODELowerBound.Access.phase_ctrlFamily,
    SparseLowerBounds.Hamiltonian.HsRelease.phase_spectate]

/-- **The circuit of a record-selected phase call**: one call of the controlled spectated phase
oracle between two control flips, or nothing for an empty pattern. -/
def phaseCircuit (P : ProjFamily K I) (y : X → I → Bool) {L' : Type*} (π : Pat L' R) :
    MultiOracleCircuit.Program
      (fun (_ : Unit) (x : X) => (ctrlFamily (P.spectate R)).phase (y x)) :=
  if ∃ r, π r ≠ none then
    .seq (.fixed _ (sectorFlip_unitary fun r => decide (π r = none)))
      (.seq (.query ()) (.fixed _ (sectorFlip_unitary fun r => decide (π r = none))))
  else MultiOracleCircuit.Program.identity

/-- **The circuit acts on the active sector as the record-selected phase call**, for any labels
that all call the phase oracle. -/
theorem phaseCircuit_eval (P : ProjFamily K I) (y : X → I → Bool) {L' : Type*}
    (O : L' → X → K →L[ℂ] K) (hO : ∀ l x, O l x = P.phase (y x)) (π : Pat L' R) (x : X) :
    (phaseCircuit P y π).eval x ∘L activeEmbed (Joint R K) =
      activeEmbed (Joint R K) ∘L patOp O π x := by
  unfold phaseCircuit
  split_ifs with h
  · have hS : (fun r => decide (π r = none)) = fun r => !decide (π r ≠ none) := by
      funext r
      simp
    have hpat : patOp O π x =
        MaskedProgram.masked (fun r => decide (π r ≠ none)) (P.phase (y x)) := by
      ext Ψ r
      rw [patOp, Joint.fiber_apply, MaskedProgram.masked_apply]
      rcases hr : π r with _ | ⟨l, b⟩
      · simp [callOpt]
      · cases b <;> simp [callOpt, queryOp, hO, ProjFamily.star_phase]
    simp only [MultiOracleCircuit.Program.eval_seq, MultiOracleCircuit.Program.eval_fixed,
      MultiOracleCircuit.Program.eval_query]
    rw [hpat, hS, phase_ctrlSpectate, ← masked_by_ctrl, mul_assoc]
  · push Not at h
    have hpat : patOp O π x = 1 := by
      rw [patOp]
      have hf : (fun r => callOpt O (π r) x) = fun _ => (1 : K →L[ℂ] K) := by
        funext r
        rw [h r]
        rfl
      rw [hf, Joint.fiber_one]
    rw [hpat, MultiOracleCircuit.Program.eval_identity]
    rfl

/-- A record-selected phase call costs at most one call. -/
theorem phaseCircuit_count (P : ProjFamily K I) (y : X → I → Bool) {L' : Type*}
    (π : Pat L' R) : (phaseCircuit P y π).count ≤ 1 := by
  unfold phaseCircuit
  split_ifs <;> simp

/-- An empty pattern costs nothing. -/
theorem phaseCircuit_count_none (P : ProjFamily K I) (y : X → I → Bool) {L' : Type*}
    (π : Pat L' R) (h : ∀ r, π r = none) : (phaseCircuit P y π).count = 0 := by
  unfold phaseCircuit
  rw [if_neg (by push Not; exact h)]
  rfl

/-- The circuits of the deferred labels of a one-label phase family (every call counted). -/
def phaseCircuits (P : ProjFamily K I) (y : X → I → Bool) :
    SelLabel (fun _ : Unit => True) R → MultiOracleCircuit.Program
      (fun (_ : Unit) (x : X) => (ctrlFamily (P.spectate R)).phase (y x))
  | .inl π => phaseCircuit P y π
  | .inr π => phaseCircuit P y π

/-- The circuits act on the active sector as the deferred labels. -/
theorem phaseCircuits_eval (P : ProjFamily K I) (y : X → I → Bool)
    (c : SelLabel (fun _ : Unit => True) R) (x : X) :
    (phaseCircuits P y c).eval x ∘L activeEmbed (Joint R K) =
      activeEmbed (Joint R K) ∘L
        selFamily (fun (_ : Unit) (x : X) => P.phase (y x)) (fun _ => True) R c x := by
  cases c with
  | inl π => exact phaseCircuit_eval P y _ (fun _ _ => rfl) π x
  | inr π => exact phaseCircuit_eval P y _ (fun _ _ => rfl) π x

/-- A deferred label costs at most its selection weight. -/
theorem phaseCircuits_count (P : ProjFamily K I) (y : X → I → Bool)
    (c : SelLabel (fun _ : Unit => True) R) : (phaseCircuits P y c).count ≤ selWeight c := by
  cases c with
  | inl π => exact phaseCircuit_count P y π
  | inr π =>
      show (phaseCircuit P y π).count ≤ 0
      rw [phaseCircuit_count_none P y π]
      intro r
      rcases hr : π r with _ | ⟨⟨l, hl⟩, b⟩
      · rfl
      · exact absurd trivial hl

end

end DeferredMeasurementLowerBounds.Access
