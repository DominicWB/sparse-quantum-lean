import ChebyshevFilter.Circuit
import SparseHamiltonian.MultiOracleCircuit

set_option autoImplicit false

/-!
# Coherent choice of walk direction (Lemma `qls:lem:signedwalk`)

The walk has the conjugated form `W = R D`, `D = V† C V` (equation
`qls:eq:commonconjugator`): `V(x)` is a program over named oracles (matrix and
state-preparation calls), and the reflection `R` and the rotation `C` are known unitaries
(`conjWalk`). An active forward step is the program `R · V† · C · V`
(`forwardProg`).

With a direction register `ι` whose branches ask for `W`, `W†` or nothing
(`dir : ι → Option Bool`), the signed step (equation `qls:eq:signedstep`) is

`R_+ · V† · (C on +, C† on -, 1 inactive) · V · R_-`,

where `R_+` applies `R` on the forward branches and `R_-` applies `R†` on the inverse ones
(`R† = R` for the reflection of the manuscript), and `V`, `V†` run on the payload with the
direction register as a spectator (`lift`, oracle family `spectator`). Then

* `signedProg_eval`: the signed step acts as `W`, `W†` and `1` on the three kinds of
  branch, for entangled direction and payload states alike;
* `signedProg_cost`: it makes exactly the oracle calls of one forward step, label by label;
  the controls are fixed gates only.

Composing the `d` signed steps of the LCU circuit gives `lcuProg`: its success block is
`F_{b,d}(W)` (`lcuProg_compression`) and its cost is `d` times the cost of one forward step
(`lcuProg_cost`).
-/

namespace ChebyshevFilter

noncomputable section
open ContinuousLinearMap SparseHamiltonian OracleCircuit
open scoped InnerProduct

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X L : Type*} {ι : Type*} [Fintype ι]

/-! ### Diagonal operators on the direction register -/

omit [CompleteSpace K] [Fintype ι] in
theorem diagonal_mul (A B : ι → K →L[ℂ] K) :
    WeightedClock.diagonal A * WeightedClock.diagonal B =
      WeightedClock.diagonal (fun i => A i * B i) := by
  rw [mul_def, WeightedClock.diagonal_comp]
  rfl

theorem star_diagonal (A : ι → K →L[ℂ] K) :
    star (WeightedClock.diagonal A) = WeightedClock.diagonal (fun i => star (A i)) := by
  rw [star_eq_adjoint, WeightedClock.diagonal_adjoint]
  rfl

omit [CompleteSpace K] [Fintype ι] in
theorem diagonal_one' : WeightedClock.diagonal (fun _ : ι => (1 : K →L[ℂ] K)) = 1 :=
  WeightedClock.diagonal_one

theorem diagonal_isUnitary (A : ι → K →L[ℂ] K) (hA : ∀ i, IsUnitary (A i)) :
    IsUnitary (WeightedClock.diagonal A) := by
  constructor
  · rw [star_diagonal, diagonal_mul]
    simp only [(hA _).1]
    exact diagonal_one'
  · rw [star_diagonal, diagonal_mul]
    simp only [(hA _).2]
    exact diagonal_one'

/-! ### Lifting programs to the direction register -/

/-- Every named oracle acting on the payload, with the direction register as a spectator. -/
abbrev spectator (ι : Type*) [Fintype ι] (O : L → X → K →L[ℂ] K) :
    L → X → (PiLp 2 (fun _ : ι => K) →L[ℂ] PiLp 2 (fun _ : ι => K)) :=
  fun l x => WeightedClock.diagonal (fun _ : ι => O l x)

variable {O : L → X → K →L[ℂ] K}

/-- Run a program on the payload with the direction register as a spectator. -/
def lift : MultiOracleCircuit.Program O → MultiOracleCircuit.Program (spectator ι O)
  | .fixed U hU => .fixed (WeightedClock.diagonal (fun _ : ι => U))
      (diagonal_isUnitary _ (fun _ => hU))
  | .query l => .query l
  | .queryAdjoint l => .queryAdjoint l
  | .seq p q => .seq (lift p) (lift q)

theorem lift_eval (p : MultiOracleCircuit.Program O) (x : X) :
    (lift (ι := ι) p).eval x = WeightedClock.diagonal (fun _ : ι => p.eval x) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l =>
    simp only [lift, MultiOracleCircuit.Program.eval_queryAdjoint]
    exact star_diagonal _
  | seq p q hp hq =>
    simp only [lift, MultiOracleCircuit.Program.eval_seq, hp, hq]
    exact diagonal_mul _ _

theorem lift_cost (p : MultiOracleCircuit.Program O) (w : L → ℕ) :
    (lift (ι := ι) p).cost w = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [lift, MultiOracleCircuit.Program.cost_seq, hp, hq]

/-! ### Forward and signed steps -/

/-- The walk `W(x) = R V(x)† C V(x)` (`W = R D`, `D = V† C V`). -/
def conjWalk (R C : K →L[ℂ] K) (pV : MultiOracleCircuit.Program O) (x : X) : K →L[ℂ] K :=
  R * (star (pV.eval x) * (C * pV.eval x))

/-- **An active forward step**: `V`, then `C`, then `V†`, then `R`. -/
def forwardProg (R C : K →L[ℂ] K) (hR : IsUnitary R) (hC : IsUnitary C)
    (pV : MultiOracleCircuit.Program O) : MultiOracleCircuit.Program O :=
  .seq (.fixed R hR) (.seq pV.adjoint (.seq (.fixed C hC) pV))

theorem forwardProg_eval (R C : K →L[ℂ] K) (hR : IsUnitary R) (hC : IsUnitary C)
    (pV : MultiOracleCircuit.Program O) (x : X) :
    (forwardProg R C hR hC pV).eval x = conjWalk R C pV x := by
  simp only [forwardProg, conjWalk, MultiOracleCircuit.Program.eval_seq,
    MultiOracleCircuit.Program.eval_fixed, MultiOracleCircuit.Program.eval_adjoint]

theorem forwardProg_cost (R C : K →L[ℂ] K) (hR : IsUnitary R) (hC : IsUnitary C)
    (pV : MultiOracleCircuit.Program O) (w : L → ℕ) :
    (forwardProg R C hR hC pV).cost w = 2 * pV.cost w := by
  simp only [forwardProg, MultiOracleCircuit.Program.cost_seq,
    MultiOracleCircuit.Program.cost_fixed, MultiOracleCircuit.Program.cost_adjoint]
  ring

theorem conjWalk_unitary (R C : K →L[ℂ] K) (hR : IsUnitary R) (hC : IsUnitary C)
    (pV : MultiOracleCircuit.Program O) (hO : ∀ l x, IsUnitary (O l x)) (x : X) :
    IsUnitary (conjWalk R C pV x) := by
  rw [← forwardProg_eval R C hR hC pV x]
  exact (forwardProg R C hR hC pV).eval_unitary hO x

theorem dirOp_isUnitary {C : K →L[ℂ] K} (hC : IsUnitary C) (o : Option Bool) :
    IsUnitary (dirOp C o) := by
  rcases o with _ | _ | _
  · exact isUnitary_one
  · change IsUnitary (C†)
    rw [← star_eq_adjoint]
    exact hC.adjoint
  · exact hC

/-- `R` on the forward branches. -/
def fwdGate (R : K →L[ℂ] K) (dir : ι → Option Bool) :
    PiLp 2 (fun _ : ι => K) →L[ℂ] PiLp 2 (fun _ : ι => K) :=
  WeightedClock.diagonal (fun i => if dir i = some true then R else 1)

/-- `R†` on the inverse branches. -/
def bwdGate (R : K →L[ℂ] K) (dir : ι → Option Bool) :
    PiLp 2 (fun _ : ι => K) →L[ℂ] PiLp 2 (fun _ : ι => K) :=
  WeightedClock.diagonal (fun i => if dir i = some false then star R else 1)

/-- `C` on the forward branches, `C†` on the inverse ones, `1` on inactive ones. -/
def midGate (C : K →L[ℂ] K) (dir : ι → Option Bool) :
    PiLp 2 (fun _ : ι => K) →L[ℂ] PiLp 2 (fun _ : ι => K) :=
  WeightedClock.diagonal (fun i => dirOp C (dir i))

theorem fwdGate_unitary {R : K →L[ℂ] K} (hR : IsUnitary R) (dir : ι → Option Bool) :
    IsUnitary (fwdGate R dir) :=
  diagonal_isUnitary _ (fun i => by split_ifs; exacts [hR, isUnitary_one])

theorem bwdGate_unitary {R : K →L[ℂ] K} (hR : IsUnitary R) (dir : ι → Option Bool) :
    IsUnitary (bwdGate R dir) :=
  diagonal_isUnitary _ (fun i => by split_ifs; exacts [hR.adjoint, isUnitary_one])

theorem midGate_unitary {C : K →L[ℂ] K} (hC : IsUnitary C) (dir : ι → Option Bool) :
    IsUnitary (midGate C dir) :=
  diagonal_isUnitary _ (fun i => dirOp_isUnitary hC (dir i))

/-- **The signed step** `R_+ V† (C on +, C† on -, 1 inactive) V R_-` (equation
`qls:eq:signedstep`). -/
def signedProg (R C : K →L[ℂ] K) (hR : IsUnitary R) (hC : IsUnitary C)
    (pV : MultiOracleCircuit.Program O) (dir : ι → Option Bool) :
    MultiOracleCircuit.Program (spectator ι O) :=
  .seq (.fixed (fwdGate R dir) (fwdGate_unitary hR dir))
    (.seq (lift pV).adjoint
      (.seq (.fixed (midGate C dir) (midGate_unitary hC dir))
        (.seq (lift pV) (.fixed (bwdGate R dir) (bwdGate_unitary hR dir)))))

/-- **Lemma `qls:lem:signedwalk`, action**: the signed step applies `W` on forward branches,
`W†` on inverse branches and `1` on inactive branches. -/
theorem signedProg_eval (R C : K →L[ℂ] K) (hR : IsUnitary R) (hC : IsUnitary C)
    (pV : MultiOracleCircuit.Program O) (hO : ∀ l x, IsUnitary (O l x))
    (dir : ι → Option Bool) (x : X) :
    (signedProg R C hR hC pV dir).eval x =
      WeightedClock.diagonal (fun i => dirOp (conjWalk R C pV x) (dir i)) := by
  have hV := pV.eval_unitary hO x
  simp only [signedProg, MultiOracleCircuit.Program.eval_seq,
    MultiOracleCircuit.Program.eval_fixed, MultiOracleCircuit.Program.eval_adjoint, lift_eval,
    fwdGate, bwdGate, midGate, star_diagonal, diagonal_mul]
  congr 1
  funext i
  rcases h : dir i with _ | _ | _
  · rw [if_neg (by decide), if_neg (by decide), one_mul, mul_one]
    exact hV.1
  · rw [if_neg (by decide), if_pos rfl, one_mul]
    change star (pV.eval x) * (C† * (pV.eval x * star R)) = (conjWalk R C pV x)†
    rw [← star_eq_adjoint, ← star_eq_adjoint, conjWalk, star_mul, star_mul, star_mul, star_star]
    simp only [mul_assoc]
  · rw [if_pos rfl, if_neg (by decide), mul_one]
    rfl

/-- **Lemma `qls:lem:signedwalk`, cost**: the signed step makes exactly the oracle calls of
one active forward step, label by label. -/
theorem signedProg_cost (R C : K →L[ℂ] K) (hR : IsUnitary R) (hC : IsUnitary C)
    (pV : MultiOracleCircuit.Program O) (dir : ι → Option Bool) (w : L → ℕ) :
    (signedProg R C hR hC pV dir).cost w = (forwardProg R C hR hC pV).cost w := by
  simp only [signedProg, forwardProg, MultiOracleCircuit.Program.cost_seq,
    MultiOracleCircuit.Program.cost_fixed, MultiOracleCircuit.Program.cost_adjoint, lift_cost]
  omega

/-! ### The LCU circuit as a program -/

/-- The first `l` signed steps of the LCU circuit for `F_{b,d}`, the first applied first. -/
def lcuProg (R C : K →L[ℂ] K) (hR : IsUnitary R) (hC : IsUnitary C)
    (pV : MultiOracleCircuit.Program O) (d : ℕ) :
    ℕ → MultiOracleCircuit.Program (spectator (Fin (2 * d + 1)) O)
  | 0 => MultiOracleCircuit.Program.identity
  | l + 1 => .seq (signedProg R C hR hC pV (stepDir d (l + 1))) (lcuProg R C hR hC pV d l)

theorem lcuProg_eval (R C : K →L[ℂ] K) (hR : IsUnitary R) (hC : IsUnitary C)
    (pV : MultiOracleCircuit.Program O) (hO : ∀ l x, IsUnitary (O l x)) (d l : ℕ) (x : X) :
    (lcuProg R C hR hC pV d l).eval x = signedSteps (conjWalk R C pV x) d l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [lcuProg, MultiOracleCircuit.Program.eval_seq, ih, signedProg_eval R C hR hC pV hO,
      signedSteps]
    rfl

/-- **The cost of the LCU circuit**: `l` signed steps cost `l` forward steps. -/
theorem lcuProg_cost (R C : K →L[ℂ] K) (hR : IsUnitary R) (hC : IsUnitary C)
    (pV : MultiOracleCircuit.Program O) (d l : ℕ) (w : L → ℕ) :
    (lcuProg R C hR hC pV d l).cost w = l * (forwardProg R C hR hC pV).cost w := by
  induction l with
  | zero => simp [lcuProg]
  | succ l ih =>
    rw [lcuProg, MultiOracleCircuit.Program.cost_seq, ih, signedProg_cost, Nat.succ_mul]
    ring

/-- **The LCU circuit with `d` signed steps** has success block exactly `F_{b,d}(W(x))`. -/
theorem lcuProg_compression (R C : K →L[ℂ] K) (hR : IsUnitary R) (hC : IsUnitary C)
    (pV : MultiOracleCircuit.Program O) (hO : ∀ l x, IsUnitary (O l x)) {b : ℝ}
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1) (d : ℕ) (x : X) :
    ((seed (V := K) b d)†) ∘L ((lcuProg R C hR hC pV d d).eval x ∘L seed b d) =
      filterOp (conjWalk R C pV x) b d := by
  rw [lcuProg_eval R C hR hC pV hO, lcu_compression _ hb]

end

end ChebyshevFilter
