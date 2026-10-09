import GateEfficientHamiltonian.GateWalshHilbert
/-!
The Hilbert-space adjoint below is realised by the literal reversed list
of elementary gates.  It is not a new whole-register primitive.  This
connects the inverse needed by amplitude amplification to its physical
one-qubit implementation.
-/

namespace SparseHamiltonian.GateWalshHilbert

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {r : ℕ}

/-- The two orientations of one known one-qubit rotation. -/
def signedGate : GateWalshInverse.Gate r → ScalarSpace r →L[ℂ] ScalarSpace r
  | .forward j => gate j
  | .backward j => (gate j)†

theorem signedGate_inverse (g : GateWalshInverse.Gate r) :
    signedGate g.inverse = (signedGate g)† := by
  cases g <;> simp [GateWalshInverse.Gate.inverse, signedGate]

/-- The Hilbert adjoint also has the literal conjugate-transpose one-bit
matrix action.  Uniqueness of the inverse uses full-space gate correctness,
not a restriction to states reached from the clean input. -/
theorem signedGate_apply (g : GateWalshInverse.Gate r)
    (v : ScalarSpace r) (x : Word r) :
    signedGate g v x = g.eval (fun y => v y) x := by
  cases g with
  | forward j => exact gate_apply j v x
  | backward j =>
      have hg : gate j (((gate j)†) v) = v :=
        congrArg (fun U : ScalarSpace r →L[ℂ] ScalarSpace r => U v)
          (gate_unitary j).2
      have hc : (GateWalshInverse.Gate.forward j).eval
          (fun y => ((gate j)†) v y) = fun y => v y := by
        funext y
        change GateWalshWords.Gate.eval j (fun z => ((gate j)†) v z) y = v y
        rw [← gate_apply, hg]
      have hi := congrArg
        (fun U : GateWalshInverse.State r →ₗ[ℂ] GateWalshInverse.State r =>
          U (fun y => ((gate j)†) v y))
        (GateWalshInverse.Gate.inverse_comp (GateWalshInverse.Gate.forward j))
      change (GateWalshInverse.Gate.backward j).eval
        ((GateWalshInverse.Gate.forward j).eval (fun y => ((gate j)†) v y)) =
          (fun y => ((gate j)†) v y) at hi
      rw [hc] at hi
      exact (congrFun hi x).symm

def signedRun : List (GateWalshInverse.Gate r) →
    ScalarSpace r →L[ℂ] ScalarSpace r
  | [] => 1
  | g :: gs => signedRun gs * signedGate g

theorem signedRun_apply (gs : List (GateWalshInverse.Gate r))
    (v : ScalarSpace r) (x : Word r) :
    signedRun gs v x = GateWalshInverse.run gs (fun y => v y) x := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
      change signedRun gs (signedGate g v) x =
        GateWalshInverse.run gs (g.eval (fun y => v y)) x
      rw [ih]
      have he : (fun y => signedGate g v y) = g.eval (fun y => v y) := by
        funext y
        exact signedGate_apply g v y
      rw [he]

theorem signedRun_append (gs hs : List (GateWalshInverse.Gate r)) :
    signedRun (gs ++ hs) = signedRun hs * signedRun gs := by
  induction gs with
  | nil => simp [signedRun]
  | cons g gs ih => simp [signedRun, ih, mul_assoc]

/-- Reversing and adjointing every elementary gate gives the operator
adjoint on the whole Hilbert space. -/
theorem signedRun_inverse (gs : List (GateWalshInverse.Gate r)) :
    signedRun (GateWalshInverse.inverse gs) = (signedRun gs)† := by
  induction gs with
  | nil => simp [GateWalshInverse.inverse, signedRun]
  | cons g gs ih =>
      rw [GateWalshInverse.inverse_cons, signedRun_append]
      simp only [signedRun, one_mul, ih, signedGate_inverse]
      change star (signedGate g) * star (signedRun gs) =
        star (signedRun gs * signedGate g)
      rw [star_mul]

theorem signedRun_forward (js : List (Fin r)) :
    signedRun (js.map GateWalshInverse.Gate.forward) = run js := by
  induction js with
  | nil => rfl
  | cons j js ih => simp [signedRun, run, signedGate, ih]

theorem signedRun_circuit (r : ℕ) :
    signedRun (GateWalshInverse.circuit r) = wordTransform r := by
  rw [GateWalshInverse.circuit, signedRun_forward]
  rfl

theorem signedRun_inverseCircuit (r : ℕ) :
    signedRun (GateWalshInverse.inverseCircuit r) = (wordTransform r)† := by
  rw [GateWalshInverse.inverseCircuit, signedRun_inverse, signedRun_circuit]

/-- Both the forward transform and its adjoint have actual lists of `r`
one-qubit gates; the inverse acts on every input, without a clean-state
restriction. -/
theorem wordTransform_adjoint_implementation (r : ℕ) :
    signedRun (GateWalshInverse.circuit r) = wordTransform r ∧
    signedRun (GateWalshInverse.inverseCircuit r) = (wordTransform r)† ∧
    (GateWalshInverse.circuit r).length = r ∧
    (GateWalshInverse.inverseCircuit r).length = r := by
  exact ⟨signedRun_circuit r, signedRun_inverseCircuit r,
    GateWalshInverse.circuit_length r, GateWalshInverse.inverseCircuit_length r⟩

end
end SparseHamiltonian.GateWalshHilbert
