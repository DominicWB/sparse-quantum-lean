import ChebyshevLinearSystem.Chiral
import SparseLinearSystems.Circuit.Step
import ChebyshevFilter.SignedWalk

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

/-!
# Signed walk steps on the released physical oracle family (Lemma `qls:lem:signedwalk`)

The released circuit layer implements, for a public label `(σ, r, m)`, the walk `W_{σ,r}` on
the counter values selected by the mask `m` (`Step.logOracle`) by the program
`Step.stepProg`: fixed gates, one masked native Cayley circuit (54 sparse primitive calls)
and two masked controlled-source calls, exactly on the clean subspace
(`Step.stepProg_intertwines`, proved from the factorisation `LogicalWalk.WwO_factor`).

A *signed* label `(σ, r, dir)` asks, on every counter value `j`, for `W` (`dir j = some true`),
`W†` (`dir j = some false`) or nothing (`dir j = none`) (`signedLog`). Its implementation
`signedStepProg` is

`Y_- · stepProg(σ, r, active) · Y_-`,

where `active` selects the counter values with a step of either direction (`activeMask`) and
`Y_-` applies the fixed reversal gate `Y = Z R` of `Chiral.lean` on the inverse-step counter
values only (`flipGate`). On an inverse branch it acts as `Y W Y = W†` (`flip_WwO`), on a
forward branch as `W`, and on an inactive branch as `1` (`signed_eq`). Hence
(`signedStepProg_intertwines`, `signedStepProg_cost`):

* the signed step applies `W`, `W†` or `1` according to the direction register, exactly on
  the clean subspace, for entangled register and payload states alike;
* it makes exactly the oracle calls of one forward step, label by label: `54` matrix-oracle
  calls and `2` calls of the controlled source preparation; the controls are fixed gates.
-/

namespace ChebyshevLinearSystem

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseLinearSystems OracleCircuit LogicalWalk
  CounterFilter Step
open scoped InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-! ### Signed logical labels -/

/-- Signed logical labels: regularisation angle, norm guess and a direction (`W`, `W†` or
nothing) for every counter value. -/
abbrev SLbl (T : ℕ) := ℝ × ℝ × (Fin (T + 1) → Option Bool)

/-- The counter values receiving a step of either direction. -/
def activeMask {T : ℕ} (dir : Fin (T + 1) → Option Bool) : Fin (T + 1) → Bool :=
  fun j => (dir j).isSome

/-- The counter values receiving an inverse step. -/
def inverseMask {T : ℕ} (dir : Fin (T + 1) → Option Bool) : Fin (T + 1) → Bool :=
  fun j => decide (dir j = some false)

/-- **The signed walk on the counter register**: `W_{σ,r}`, `W_{σ,r}†` or `1` on every counter
value, according to the direction register. -/
def signedLog (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (T : ℕ) : SLbl T → X → Ctr T (PrivO n) →L[ℂ] Ctr T (PrivO n) :=
  fun l x => WeightedClock.diagonal (fun j => ChebyshevFilter.dirOp (WwO D Ub sv l.1 l.2.1 x)
    (l.2.2 j))

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem signedLog_unitary (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (T : ℕ) : ∀ l x, IsUnitary (signedLog D Ub sv T l x) :=
  fun l x => ChebyshevFilter.diagonal_isUnitary _
    (fun _ => ChebyshevFilter.dirOp_isUnitary (WwO_unitary D Ub sv l.1 l.2.1 x) _)

/-! ### The reversal gate -/

omit [DecidableEq n] in
theorem parO_unitary : IsUnitary (parO (n := n)) := by
  have h : star (parO (n := n)) = parO := by rw [star_eq_adjoint, parO_adjoint]
  exact ⟨by rw [h, parO_mul_self], by rw [h, parO_mul_self]⟩

theorem reflectionO_unitary (D : NativeSparseBlockEncoding.Data X n Z s) :
    IsUnitary (WalkGap.reflection (JwO D).toContinuousLinearMap) := by
  have hs : star (WalkGap.reflection (JwO D).toContinuousLinearMap) =
      WalkGap.reflection (JwO D).toContinuousLinearMap := by
    rw [star_eq_adjoint, WalkGap.reflection_adjoint]
  have hm := WalkGap.reflection_mul_self _ (LinearIsometry.adjoint_comp_self (JwO D))
  exact ⟨by rw [hs, hm], by rw [hs, hm]⟩

theorem flipO_unitary (D : NativeSparseBlockEncoding.Data X n Z s) : IsUnitary (flipO D) :=
  parO_unitary.mul (reflectionO_unitary D)

/-- The reversal gate `Y = Z R` on the inverse-step counter values, `1` elsewhere. -/
def flipGate (D : NativeSparseBlockEncoding.Data X n Z s) {T : ℕ}
    (dir : Fin (T + 1) → Option Bool) : Ctr T (PrivO n) →L[ℂ] Ctr T (PrivO n) :=
  MaskedProgram.masked (inverseMask dir) (flipO D)

theorem flipGate_unitary (D : NativeSparseBlockEncoding.Data X n Z s) {T : ℕ}
    (dir : Fin (T + 1) → Option Bool) : IsUnitary (flipGate D dir) :=
  MaskedProgram.masked_unitary _ _ (flipO_unitary D)

/-- **The signed step as an operator**: the forward walk on the active counter values,
conjugated by the reversal gate on the inverse-step values, is the signed walk. -/
theorem signed_eq (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (T : ℕ) (σ r : ℝ) (dir : Fin (T + 1) → Option Bool) (x : X) :
    flipGate D dir * (logOracle D Ub sv T (σ, r, activeMask dir) x * flipGate D dir) =
      signedLog D Ub sv T (σ, r, dir) x := by
  simp only [flipGate, logOracle, MaskedProgram.masked, signedLog, ChebyshevFilter.diagonal_mul]
  congr 1
  funext j
  rcases h : dir j with _ | _ | _
  · simp [inverseMask, activeMask, h, ChebyshevFilter.dirOp]
  · simp only [inverseMask, activeMask, h, decide_true, if_true, Option.isSome_some,
      ChebyshevFilter.dirOp]
    rw [← mul_assoc]
    exact flip_WwO D Ub sv σ r x
  · simp [inverseMask, activeMask, h, ChebyshevFilter.dirOp]

/-! ### The signed step program -/

/-- **The signed walk step** (Lemma `qls:lem:signedwalk`): the reversal gate on the inverse
branches, the released forward step on all active branches, and the reversal gate again. It
is a program over the released physical oracle family. -/
def signedStepProg (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (T : ℕ) (l : SLbl T) : MultiOracleCircuit.Program (physOracle D Ub T) :=
  .seq (fixedStep D Ub T (flipGate D l.2.2) (flipGate_unitary D l.2.2))
    (.seq (stepProg D Ub sv T (l.1, l.2.1, activeMask l.2.2))
      (fixedStep D Ub T (flipGate D l.2.2) (flipGate_unitary D l.2.2)))

/-- **Lemma `qls:lem:signedwalk`, action**: the signed step applies `W`, `W†` or `1` according
to the direction register, exactly on the clean subspace. -/
theorem signedStepProg_intertwines (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (T : ℕ) (l : SLbl T)
    (x : X) : (signedStepProg D Ub sv T l).eval x ∘L E D T = E D T ∘L signedLog D Ub sv T l x := by
  obtain ⟨σ, r, dir⟩ := l
  rw [← signed_eq]
  simp only [signedStepProg, MultiOracleCircuit.Program.eval_seq]
  apply intertwine_mul (fixedStep_intertwines D Ub T _ _ x)
  apply intertwine_mul (stepProg_intertwines D Ub hUb sv T _ x)
  exact fixedStep_intertwines D Ub T _ _ x

/-- **Lemma `qls:lem:signedwalk`, cost**: the signed step makes exactly the oracle calls of one
forward step, label by label, whatever the counter mask of that forward step. -/
theorem signedStepProg_cost (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (T : ℕ) (l : SLbl T) (m : Fin (T + 1) → Bool) (w : Lbl → ℕ) :
    (signedStepProg D Ub sv T l).cost w = (stepProg D Ub sv T (l.1, l.2.1, m)).cost w := by
  simp only [signedStepProg, MultiOracleCircuit.Program.cost_seq, fixedStep,
    MultiOracleCircuit.Program.cost_fixed, zero_add, add_zero]
  rw [stepProg_cost, stepProg_cost]

theorem signedStepProg_cost_mat (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (T : ℕ) (l : SLbl T) :
    (signedStepProg D Ub sv T l).cost wMat = 54 := by
  rw [signedStepProg_cost D Ub sv T l (fun _ => true), stepProg_cost_mat]

theorem signedStepProg_cost_src (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (T : ℕ) (l : SLbl T) :
    (signedStepProg D Ub sv T l).cost wSrc = 2 := by
  rw [signedStepProg_cost D Ub sv T l (fun _ => true), stepProg_cost_src]

/-- **Lemma `qls:lem:signedwalk`** for the released walk: for every direction register the
signed step acts as `W_{σ,r}`, `W_{σ,r}†` or `1` on each counter value, exactly on the clean
subspace, and its weighted cost equals that of an active forward step for every weighting of
the physical oracle labels (`54` matrix-oracle calls and `2` source calls). -/
theorem signed_walk_step (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (T : ℕ) (σ r : ℝ)
    (dir : Fin (T + 1) → Option Bool) :
    (∀ x, (signedStepProg D Ub sv T (σ, r, dir)).eval x ∘L E D T =
      E D T ∘L WeightedClock.diagonal (fun j =>
        ChebyshevFilter.dirOp (WwO D Ub sv σ r x) (dir j))) ∧
    (∀ w, (signedStepProg D Ub sv T (σ, r, dir)).cost w =
      (stepProg D Ub sv T (σ, r, fun _ => true)).cost w) ∧
    (signedStepProg D Ub sv T (σ, r, dir)).cost wMat = 54 ∧
    (signedStepProg D Ub sv T (σ, r, dir)).cost wSrc = 2 :=
  ⟨fun x => signedStepProg_intertwines D Ub hUb sv T _ x,
    fun w => signedStepProg_cost D Ub sv T _ _ w, signedStepProg_cost_mat D Ub sv T _,
    signedStepProg_cost_src D Ub sv T _⟩

end

end ChebyshevLinearSystem
