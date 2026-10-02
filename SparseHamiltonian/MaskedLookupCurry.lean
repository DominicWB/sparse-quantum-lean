import SparseHamiltonian.MaskedLookup

/-!
# Masked ordinary queries on Hilbert direct sums

A fixed regrouping separates a finite spectator label from address, target, and
scratch registers.  The full-space two-query identity becomes a literal block
diagonal SELECT of forward, inverse, or identity lookup operators. All masks
continue to use one common ordinary lookup oracle.
-/

namespace SparseHamiltonian.MaskedLookupCurry
noncomputable section
open ContinuousLinearMap LookupOracle

variable {X I A Z : Type*} [Fintype I] [Fintype A] [Fintype Z] [AddCommGroup Z]

/-- Address and target, followed by an arbitrary scratch value register. -/
abbrev Local (A Z : Type*) := (A × Z) × Z

/-- The payload Hilbert space after separating the spectator register. -/
abbrev Payload (A Z : Type*) [Fintype A] [Fintype Z] := EuclideanSpace ℂ (Local A Z)

/-- A fixed curry map, independent of masks and oracle tables. -/
def curry : EuclideanSpace ℂ (MaskedLookup.Workspace I A Z) ≃ₗᵢ[ℂ]
    PiLp 2 (fun _ : I => Payload A Z) :=
  RegisterEquivalences.workspaceCurry I (A × Z) Z

omit [AddCommGroup Z] in
@[simp] theorem curry_apply
    (v : EuclideanSpace ℂ (MaskedLookup.Workspace I A Z)) (i : I) (a : A) (z y : Z) :
    curry v i ((a, z), y) = v ((i, a, z), y) := rfl

omit [AddCommGroup Z] in
@[simp] theorem curry_symm_apply
    (v : PiLp 2 (fun _ : I => Payload A Z)) (i : I) (a : A) (z y : Z) :
    curry.symm v ((i, a, z), y) = v i ((a, z), y) := rfl

/-- Weighted ordinary lookup on one payload, acting trivially on scratch. -/
def localSigned (w : ℤ) (f : X → A → Z) (x : X) : Payload A Z →L[ℂ] Payload A Z :=
  (permutationUnitary
    (Equiv.prodCongr (basisEquiv (fun x a => w • f x a) x) (Equiv.refl Z))).toLinearIsometry.toContinuousLinearMap

@[simp] theorem localSigned_apply (w : ℤ) (f : X → A → Z) (x : X)
    (v : Payload A Z) (a : A) (z y : Z) :
    localSigned w f x v ((a, z), y) = v ((a, z - w • f x a), y) := rfl

/-- Every weighted payload lookup is an actual unitary. -/
theorem localSigned_unitary (w : ℤ) (f : X → A → Z) (x : X) :
    OracleCircuit.IsUnitary (localSigned w f x) :=
  permutationUnitary_unitary _

/-- An inactive payload query is exactly identity, on all scratch states. -/
@[simp] theorem localSigned_zero (f : X → A → Z) (x : X) :
    localSigned 0 f x = 1 := by
  ext v w
  rcases w with ⟨⟨a, z⟩, y⟩
  simp

/-- The negative unit weight is the adjoint of the forward payload query. -/
theorem localSigned_neg_one (f : X → A → Z) (x : X) :
    localSigned (-1) f x = star (localSigned 1 f x) := by
  unfold localSigned
  rw [ContinuousLinearMap.star_eq_adjoint, permutationUnitary_adjoint,
    ← permutationUnitary_symm]
  ext v w
  rcases w with ⟨⟨a, z⟩, y⟩
  change v ((a, z - (-1 : ℤ) • f x a), y) = v ((a, z + (1 : ℤ) • f x a), y)
  simp

omit [Fintype I] in
/-- Mixed forward, inverse, and idle locations give the expected local operator. -/
theorem localSigned_direction (active inverse : I → Bool) (f : X → A → Z)
    (x : X) (i : I) :
    localSigned (MaskedLookup.directionWeight active inverse i) f x =
      if active i then (if inverse i then star (localSigned 1 f x)
        else localSigned 1 f x) else 1 := by
  cases ha : active i <;> cases hi : inverse i <;>
    simp [MaskedLookup.directionWeight, ha, hi, localSigned_neg_one]

/-- The one common ordinary-lookup oracle, expressed in the direct-sum layout. -/
def oracle (f : X → A → Z) (x : X) :
    PiLp 2 (fun _ : I => Payload A Z) →L[ℂ] PiLp 2 (fun _ : I => Payload A Z) :=
  curry.conjStarAlgEquiv (MaskedLookup.oracle f x)

/-- The common oracle adds the table to scratch; target and labels are spectators. -/
@[simp] theorem oracle_apply (f : X → A → Z) (x : X)
    (v : PiLp 2 (fun _ : I => Payload A Z)) (i : I) (a : A) (z y : Z) :
    oracle f x v i ((a, z), y) = v i ((a, z), y - f x a) := rfl

/-- The common oracle in this layout remains a genuine unitary. -/
theorem oracle_unitary (f : X → A → Z) (x : X) :
    OracleCircuit.IsUnitary (oracle (I := I) f x) :=
  (MaskedLookup.oracle_unitary (I := I) f x).transport (curry (I := I) (A := A) (Z := Z))

/-- Regrouping turns the complete circuit into the literal diagonal SELECT. -/
theorem circuit_eq_diagonal (m : I → ℤ) (f : X → A → Z) (x : X) :
    curry.conjStarAlgEquiv (MaskedLookup.circuit m f x) =
      WeightedClock.diagonal (fun i => localSigned (m i) f x) := by
  ext v i w
  rcases w with ⟨⟨a, z⟩, y⟩
  rw [MaskedLookup.circuit_eq_signed]
  rfl

/-- Arbitrarily many simultaneous integer masks require two common-oracle calls. -/
theorem diagonal_two_queries (m : I → ℤ) (f : X → A → Z) :
    OracleCircuit.Implements (oracle f)
      (fun x => WeightedClock.diagonal (fun i => localSigned (m i) f x)) 2 := by
  have h := (MaskedLookup.circuit_two_queries m f).transport curry
  exact h.congr fun x => circuit_eq_diagonal m f x

/-- Simultaneous forward, inverse, and idle branches use two ordinary queries. -/
theorem direction_diagonal_two_queries (active inverse : I → Bool) (f : X → A → Z) :
    OracleCircuit.Implements (oracle f)
      (fun x => WeightedClock.diagonal (fun i =>
        if active i then (if inverse i then star (localSigned 1 f x)
          else localSigned 1 f x) else 1)) 2 := by
  have h := diagonal_two_queries (MaskedLookup.directionWeight active inverse) f
  apply h.congr
  intro x
  congr 1
  funext i
  exact localSigned_direction active inverse f x i

/-- Simultaneous active/idle branches use two ordinary queries. -/
theorem masked_diagonal_two_queries (active : I → Bool) (f : X → A → Z) :
    OracleCircuit.Implements (oracle f)
      (fun x => WeightedClock.diagonal (fun i =>
        if active i then localSigned 1 f x else 1)) 2 := by
  have h := direction_diagonal_two_queries active (fun _ => false) f
  simpa only [Bool.false_eq_true, ↓reduceIte] using h

end
end SparseHamiltonian.MaskedLookupCurry
