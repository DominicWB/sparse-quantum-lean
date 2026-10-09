import GateEfficientHamiltonian.GateConstantCompare
/-!
# Literal Walsh preparation on the binary word register

Each gate below is one known one-qubit real rotation.  Its matrix is the
plane rotation with both parameters equal to `1/sqrt 2`; consequently its
first column is the positive Hadamard column.  The circuit applies one such
gate to every word bit.  The semantics is given coordinatewise on the full
finite word space, so no whole-register uniform-state primitive is assumed.
-/

namespace SparseHamiltonian.GateWalshWords

noncomputable section
open scoped BigOperators

abbrev Word (r : ℕ) := GatePrivatePointer.Word r
abbrev State (r : ℕ) := Word r → ℂ

/-- The positive Hadamard-column coefficient. -/
def half : ℝ := 1 / GateDyadicBoundary.rootDenominator 1

theorem half_unit : half ^ 2 + half ^ 2 = 1 := by
  simpa [half] using GateDyadicUnitary.input_parameter_unit 1

def coefficients : Matrix Bool Bool ℂ :=
  GateDyadicUnitary.rotationCoefficients half half

theorem coefficients_unitary :
    GatePrefixCircuit.Coefficients.IsUnitary coefficients :=
  GateDyadicUnitary.rotationCoefficients_unitary _ _ half_unit

/-- One literal one-qubit gate, represented only by the bit it acts on. -/
abbrev Gate (r : ℕ) := Fin r

/-- Row action of the known one-qubit matrix on coordinate amplitudes. -/
def Gate.eval (j : Gate r) : State r →ₗ[ℂ] State r where
  toFun f x := ∑ b : Bool, coefficients (x j) b * f (Function.update x j b)
  map_add' := by
    intro f g
    funext x
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro a f
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, 
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring

/-- Execute gates from left to right. -/
def run : List (Gate r) → State r →ₗ[ℂ] State r
  | [] => LinearMap.id
  | g :: gs => (run gs).comp (Gate.eval g)

@[simp] theorem run_nil : run ([] : List (Gate r)) = LinearMap.id := rfl

@[simp] theorem run_append (gs hs : List (Gate r)) :
    run (gs ++ hs) = (run hs).comp (run gs) := by
  induction gs with
  | nil => simp [run]
  | cons g gs ih => simp [run, ih, LinearMap.comp_assoc]

/-- The first `n` bit rotations in increasing little-endian order. -/
def circuit : (n : ℕ) → n ≤ r → List (Gate r)
  | 0, _ => []
  | n + 1, h => circuit n (by omega) ++ [⟨n, by omega⟩]

theorem circuit_length (n : ℕ) (h : n ≤ r) :
    (circuit n h).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [circuit, ih]

/-- Bits at and above `n` remain zero after the first `n` rotations. -/
def highZero (n : ℕ) (x : Word r) : Prop :=
  ∀ j : Fin r, n ≤ j.val → x j = false

theorem highZero_update_false_iff (n : ℕ) (h : n < r) (x : Word r) :
    highZero n (Function.update x (⟨n, h⟩ : Fin r) false) ↔
      highZero (n + 1) x := by
  constructor
  · intro hz k hk
    have hne : k ≠ (⟨n, h⟩ : Fin r) := by
      intro he
      have hv : k.val = n := congrArg Fin.val he
      omega
    have hx := hz k (by omega)
    rw [Function.update_of_ne hne] at hx
    exact hx
  · intro hz k hk
    by_cases hkj : k = (⟨n, h⟩ : Fin r)
    · subst k
      simp only [Function.update_self]
    · have hstrict : n + 1 ≤ k.val := by
        have hval : k.val ≠ n := by
          intro he
          exact hkj (Fin.ext he)
        omega
      rw [Function.update_of_ne hkj]
      exact hz k hstrict

theorem not_highZero_update_true (n : ℕ) (h : n < r) (x : Word r) :
    ¬ highZero n (Function.update x (⟨n, h⟩ : Fin r) true) := by
  intro hz
  have := hz (⟨n, h⟩ : Fin r) le_rfl
  simp at this

/-- Coordinate invariant after the first `n` gates. -/
def partialState (n : ℕ) (x : Word r) : ℂ := by
  classical
  exact if highZero n x then (half : ℂ) ^ n else 0

def zeroWord (r : ℕ) : Word r := fun _ => false

def zeroState (x : Word r) : ℂ := if x = zeroWord r then 1 else 0

theorem highZero_zero_iff (x : Word r) :
    highZero 0 x ↔ x = zeroWord r := by
  constructor
  · intro hz
    funext j
    exact hz j (Nat.zero_le _)
  · rintro rfl
    intro j hj
    rfl

theorem partial_zero : partialState (r := r) 0 = zeroState := by
  funext x
  simp [partialState, zeroState, highZero_zero_iff]

/-- One additional known rotation extends the flat prefix by one bit. -/
theorem gate_partial (n : ℕ) (h : n < r) :
    Gate.eval (⟨n, h⟩ : Gate r) (partialState (r := r) n) =
      partialState (r := r) (n + 1) := by
  funext x
  by_cases hz : highZero (n + 1) x
  · cases hx : x (⟨n, h⟩ : Fin r) <;>
      simp [Gate.eval, coefficients, GateDyadicUnitary.rotationCoefficients,
        partialState, highZero_update_false_iff n h x,
        not_highZero_update_true n h x, hz, pow_succ, hx] <;> ring
  · cases hx : x (⟨n, h⟩ : Fin r) <;>
      simp [Gate.eval, coefficients, GateDyadicUnitary.rotationCoefficients,
        partialState, highZero_update_false_iff n h x,
        not_highZero_update_true n h x, hz, hx]

/-- The actual list of the first `n` one-qubit gates prepares the proved
partial-flat coordinate state. -/
theorem circuit_prepares_partial (n : ℕ) (h : n ≤ r) :
    run (circuit n h) zeroState = partialState (r := r) n := by
  induction n with
  | zero =>
      simp [circuit, partial_zero]
  | succ n ih =>
      have hn : n < r := by omega
      rw [circuit, run_append]
      simp only [run, LinearMap.id_comp, LinearMap.comp_apply]
      rw [ih]
      exact gate_partial n hn

theorem highZero_width (x : Word r) : highZero r x := by
  intro j hj
  omega

/-- After exactly `r` elementary rotations every word has the same positive
amplitude `(1/sqrt 2)^r`. -/
theorem circuit_prepares_constant :
    run (circuit r le_rfl) zeroState =
      fun _ : Word r => (half : ℂ) ^ r := by
  rw [circuit_prepares_partial]
  funext x
  simp [partialState, highZero_width]

end
end SparseHamiltonian.GateWalshWords
