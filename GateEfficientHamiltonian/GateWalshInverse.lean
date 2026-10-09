import GateEfficientHamiltonian.GateWalshNormalisation
/-!
# Literal inverse gates for the Walsh word circuit

The inverse is implemented by reversing the list of one-qubit rotations and
replacing each rotation by its conjugate transpose.  The identities below
hold on the entire binary-word amplitude space.  In particular they do not
assume that the input is the all-zero word or a uniform state.
-/

namespace SparseHamiltonian.GateWalshInverse

noncomputable section
open scoped BigOperators

abbrev Word (r : ℕ) := GateWalshWords.Word r
abbrev State (r : ℕ) := GateWalshWords.State r

variable {r : ℕ}

/-- The coordinate action of one specified two-by-two matrix on one wire.
This definition introduces no whole-register gate. -/
def localMatrix (j : Fin r) (a : Matrix Bool Bool ℂ) :
    State r →ₗ[ℂ] State r where
  toFun f x := ∑ b : Bool, a (x j) b * f (Function.update x j b)
  map_add' := by
    intro f g
    funext x
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c f
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring

/-- Literal matrix multiplication on a single word wire, including all
amplitudes of the other wires. -/
theorem localMatrix_comp (j : Fin r) (a b : Matrix Bool Bool ℂ) :
    (localMatrix j a).comp (localMatrix j b) = localMatrix j (a * b) := by
  apply LinearMap.ext
  intro f
  funext x
  change (∑ p : Bool, a (x j) p *
      (∑ q : Bool, b ((Function.update x j p) j) q *
        f (Function.update (Function.update x j p) j q))) =
    ∑ q : Bool, (a * b) (x j) q * f (Function.update x j q)
  simp only [Function.update_self, Function.update_idem,
    Matrix.mul_apply, Fintype.sum_bool]
  ring

theorem localMatrix_one (j : Fin r) :
    localMatrix j (1 : Matrix Bool Bool ℂ) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext x
  change (∑ b : Bool, (1 : Matrix Bool Bool ℂ) (x j) b *
    f (Function.update x j b)) = f x
  simp [Matrix.one_apply]

/-- Both orientations are actual one-qubit gates in the exact-rotation
model.  Backward means the conjugate transpose of the same known matrix. -/
inductive Gate (r : ℕ) where
  | forward : Fin r → Gate r
  | backward : Fin r → Gate r

def Gate.eval : Gate r → State r →ₗ[ℂ] State r
  | .forward j => localMatrix j GateWalshWords.coefficients
  | .backward j =>
      localMatrix j (Matrix.conjTranspose GateWalshWords.coefficients)

def Gate.inverse : Gate r → Gate r
  | .forward j => .backward j
  | .backward j => .forward j

@[simp] theorem Gate.inverse_inverse (g : Gate r) : g.inverse.inverse = g := by
  cases g <;> rfl

@[simp] theorem Gate.forward_eval (j : Fin r) :
    (Gate.forward j).eval = GateWalshWords.Gate.eval j := rfl

/-- Every backward gate is the genuine inverse on the full word space. -/
theorem Gate.inverse_comp (g : Gate r) :
    g.inverse.eval.comp g.eval = LinearMap.id := by
  cases g with
  | forward j =>
      change (localMatrix j (Matrix.conjTranspose GateWalshWords.coefficients)).comp
        (localMatrix j GateWalshWords.coefficients) = LinearMap.id
      rw [localMatrix_comp, GateWalshWords.coefficients_unitary.1, localMatrix_one]
  | backward j =>
      change (localMatrix j GateWalshWords.coefficients).comp
        (localMatrix j (Matrix.conjTranspose GateWalshWords.coefficients)) =
          LinearMap.id
      rw [localMatrix_comp, GateWalshWords.coefficients_unitary.2, localMatrix_one]

theorem Gate.comp_inverse (g : Gate r) :
    g.eval.comp g.inverse.eval = LinearMap.id := by
  simpa only [Gate.inverse_inverse] using g.inverse.inverse_comp

/-- Execute the actual elementary gates from left to right. -/
def run : List (Gate r) → State r →ₗ[ℂ] State r
  | [] => LinearMap.id
  | g :: gs => (run gs).comp g.eval

@[simp] theorem run_nil : run ([] : List (Gate r)) = LinearMap.id := rfl

@[simp] theorem run_append (gs hs : List (Gate r)) :
    run (gs ++ hs) = (run hs).comp (run gs) := by
  induction gs with
  | nil => simp [run]
  | cons g gs ih => simp [run, ih, LinearMap.comp_assoc]

/-- Reverse the physical gate order and invert each elementary rotation. -/
def inverse (gs : List (Gate r)) : List (Gate r) :=
  gs.reverse.map Gate.inverse

@[simp] theorem inverse_nil : inverse ([] : List (Gate r)) = [] := rfl

@[simp] theorem inverse_cons (g : Gate r) (gs : List (Gate r)) :
    inverse (g :: gs) = inverse gs ++ [g.inverse] := by
  simp [inverse]

@[simp] theorem inverse_length (gs : List (Gate r)) :
    (inverse gs).length = gs.length := by
  simp [inverse]

/-- Full-space left inverse of the literal word circuit. -/
theorem run_inverse_comp (gs : List (Gate r)) :
    (run (inverse gs)).comp (run gs) = LinearMap.id := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      rw [inverse_cons, run_append]
      apply LinearMap.ext
      intro v
      simp only [run, LinearMap.comp_apply, LinearMap.id_apply]
      have hv := congrArg (fun A : State r →ₗ[ℂ] State r => A (g.eval v)) ih
      change run (inverse gs) (run gs (g.eval v)) = g.eval v at hv
      rw [hv]
      exact congrArg (fun A : State r →ₗ[ℂ] State r => A v) g.inverse_comp

/-- Full-space right inverse, independent of any clean-state promise. -/
theorem run_comp_inverse (gs : List (Gate r)) :
    (run gs).comp (run (inverse gs)) = LinearMap.id := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      rw [inverse_cons, run_append]
      apply LinearMap.ext
      intro v
      simp only [run, LinearMap.comp_apply, LinearMap.id_apply]
      have hv := congrArg (fun A : State r →ₗ[ℂ] State r =>
        A (run (inverse gs) v)) g.comp_inverse
      change g.eval (g.inverse.eval (run (inverse gs) v)) = run (inverse gs) v at hv
      rw [hv]
      exact congrArg (fun A : State r →ₗ[ℂ] State r => A v) ih

/-- The forward-only list has exactly the original Walsh semantics. -/
theorem run_forward (gs : List (GateWalshWords.Gate r)) :
    run (gs.map Gate.forward) = GateWalshWords.run gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.map_cons, run, GateWalshWords.run, Gate.forward_eval, ih]

def circuit (r : ℕ) : List (Gate r) :=
  (GateWalshWords.circuit r le_rfl).map Gate.forward

def inverseCircuit (r : ℕ) : List (Gate r) := inverse (circuit r)

theorem circuit_length (r : ℕ) : (circuit r).length = r := by
  simp [circuit, GateWalshWords.circuit_length]

theorem inverseCircuit_length (r : ℕ) : (inverseCircuit r).length = r := by
  simp [inverseCircuit, circuit_length]

theorem circuit_prepares_constant :
    run (circuit r) GateWalshWords.zeroState =
      fun _ : Word r => (GateWalshWords.half : ℂ) ^ r := by
  rw [circuit, run_forward]
  exact GateWalshWords.circuit_prepares_constant

/-- The actual reversed `r`-gate list unprepares the exact flat word state. -/
theorem inverseCircuit_unprepares_constant :
    run (inverseCircuit r) (fun _ : Word r => (GateWalshWords.half : ℂ) ^ r) =
      GateWalshWords.zeroState := by
  rw [← circuit_prepares_constant]
  exact congrArg (fun A : State r →ₗ[ℂ] State r => A GateWalshWords.zeroState)
    (run_inverse_comp (circuit r))

/-- The forward list and its literal reverse are inverse on every state,
with exactly `r` one-qubit rotations in each direction. -/
theorem circuit_inverse_and_counts :
    (run (inverseCircuit r)).comp (run (circuit r)) = LinearMap.id ∧
    (run (circuit r)).comp (run (inverseCircuit r)) = LinearMap.id ∧
    (circuit r).length = r ∧ (inverseCircuit r).length = r := by
  exact ⟨run_inverse_comp (circuit r), run_comp_inverse (circuit r),
    circuit_length r, inverseCircuit_length r⟩

end
end SparseHamiltonian.GateWalshInverse
