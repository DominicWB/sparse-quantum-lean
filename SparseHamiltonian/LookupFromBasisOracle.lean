import SparseHamiltonian.FilteredSparseLookup

/-!
# Additive table lookup from an in-place basis oracle

Only the oracle's action on a specified collection of valid basis inputs is
used. Its unitary extension on other states can be arbitrary. A fixed preparation
and fixed classical label-copy operation give a compute/copy/uncompute circuit
with two calls, including one inverse call, to the same spectator-extended oracle.
-/

namespace SparseHamiltonian.LookupFromBasisOracle

noncomputable section
open ContinuousLinearMap OracleCircuit LookupOracle
open scoped BigOperators InnerProduct

section Spectators
variable {S B X : Type*} [Fintype S] [Fintype B]

/-- One call to the given unitary, with a fixed spectator register. -/
def spectator (F : EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) :
    EuclideanSpace ℂ (S × B) →L[ℂ] EuclideanSpace ℂ (S × B) :=
  (RegisterEquivalences.productFlatten S B).conjStarAlgEquiv
    (WeightedClock.diagonal (fun _ : S => F))

/-- A valid basis transition remains valid with arbitrary fixed spectators. -/
theorem spectator_single [DecidableEq S] [DecidableEq B]
    (F : EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (b c : B) (z : ℂ) (hF : F (EuclideanSpace.single b z) = EuclideanSpace.single c z)
    (s : S) :
    spectator (S := S) F (EuclideanSpace.single (s, b) z) =
      EuclideanSpace.single (s, c) z := by
  ext t
  rcases t with ⟨s', b'⟩
  have hf : ((RegisterEquivalences.productFlatten S B).symm
      (EuclideanSpace.single (s, b) z)) s' =
      if s' = s then EuclideanSpace.single b z else 0 := by
    ext j
    by_cases hs : s' = s
    · subst s'
      simp [PiLp.single_apply]
    · simp [hs]
  change F (((RegisterEquivalences.productFlatten S B).symm
    (EuclideanSpace.single (s, b) z)) s') b' = _
  rw [hf]
  by_cases hs : s' = s
  · subst s'
    simp [hF, PiLp.single_apply]
  · simp [hs]

/-- Spectator extension preserves two-sided unitarity. -/
theorem spectator_unitary (F : EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : IsUnitary F) : IsUnitary (spectator (S := S) F) := by
  have hDiag : IsUnitary (WeightedClock.diagonal (fun _ : S => F)) := by
    have hl : F† ∘L F = 1 := hF.1
    have hr : F ∘L F† = 1 := hF.2
    constructor
    · change (WeightedClock.diagonal (fun _ : S => F))† ∘L
        WeightedClock.diagonal (fun _ : S => F) = 1
      rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
      simp only [hl, WeightedClock.diagonal_one]
    · change WeightedClock.diagonal (fun _ : S => F) ∘L
        (WeightedClock.diagonal (fun _ : S => F))† = 1
      rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
      simp only [hr, WeightedClock.diagonal_one]
  exact hDiag.transport (RegisterEquivalences.productFlatten S B)

end Spectators

section Circuit
variable {A B Z X : Type*} [Fintype A] [Fintype B] [Fintype Z] [AddCommGroup Z]

/-- The logical address and value register with one oracle work register. -/
abbrev Workspace (A B Z : Type*) := (A × Z) × B

/-- Fixed, address-controlled preparation of the promised valid oracle inputs. -/
def prepareEquiv (prep : A → B ≃ B) : Workspace A B Z ≃ Workspace A B Z where
  toFun v := (v.1, prep v.1.1 v.2)
  invFun v := (v.1, (prep v.1.1).symm v.2)
  left_inv v := by simp
  right_inv v := by simp

/-- Copy a known classical label of the oracle output into the target register. -/
def copyEquiv (value : B → Z) : Workspace A B Z ≃ Workspace A B Z where
  toFun v := ((v.1.1, v.1.2 + value v.2), v.2)
  invFun v := ((v.1.1, v.1.2 - value v.2), v.2)
  left_inv v := by simp
  right_inv v := by simp

/-- One physical in-place oracle call with address and target as spectators. -/
def oracle (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (x : X) :
    EuclideanSpace ℂ (Workspace A B Z) →L[ℂ] EuclideanSpace ℂ (Workspace A B Z) :=
  spectator (S := A × Z) (F x)

/-- The complete circuit; the oracle-free gates have no unknown-input argument. -/
def program (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (prep : A → B ≃ B) (value : B → Z) : Program (oracle (A := A) (Z := Z) F) :=
  .seq (.fixed _ (permutationUnitary_unitary (prepareEquiv (Z := Z) prep).symm))
    (.seq .queryAdjoint (.seq (.fixed _ (permutationUnitary_unitary (copyEquiv (A := A) value)))
      (.seq .query (.fixed _ (permutationUnitary_unitary (prepareEquiv (Z := Z) prep))))))

/-- Exactly one forward oracle call and one inverse oracle call occur. -/
@[simp] theorem program_count (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (prep : A → B ≃ B) (value : B → Z) : (program F prep value).count = 2 := rfl

omit [AddCommGroup Z] in
/-- The physical primitive is unitary on all workspace states. -/
theorem oracle_unitary (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (x : X) : IsUnitary (oracle (A := A) (Z := Z) F x) :=
  spectator_unitary (F x) (hF x)

/-- On a clean work register, only the promised basis transitions are queried.
No permutation behavior is assumed on any other basis vector. -/
theorem program_single [DecidableEq A] [DecidableEq B] [DecidableEq Z]
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (prep : A → B ≃ B) (value : B → Z)
    (b₀ : B) (encode : A → B) (image : X → A → B)
    (hprep : ∀ a, prep a b₀ = encode a)
    (hvalid : ∀ x a, F x (EuclideanSpace.single (encode a) 1) =
      EuclideanSpace.single (image x a) 1) (x : X) (a : A) (z : Z) :
    (program F prep value).eval x (EuclideanSpace.single ((a, z), b₀) 1) =
      EuclideanSpace.single ((a, z + value (image x a)), b₀) 1 := by
  have hForward (z' : Z) :
      oracle F x (EuclideanSpace.single ((a, z'), encode a) 1) =
        EuclideanSpace.single ((a, z'), image x a) 1 :=
    spectator_single (F x) (encode a) (image x a) 1 (hvalid x a) (a, z')
  have hReverse (z' : Z) :
      ((oracle F x)†) (EuclideanSpace.single ((a, z'), image x a) 1) =
        EuclideanSpace.single ((a, z'), encode a) 1 := by
    rw [← hForward z']
    exact congrArg (fun G => G (EuclideanSpace.single ((a, z'), encode a) 1))
      (oracle_unitary F hF x).1
  change (permutationUnitary (prepareEquiv (Z := Z) prep).symm)
    (((oracle F x)†) ((permutationUnitary (copyEquiv (A := A) value))
      (oracle F x ((permutationUnitary (prepareEquiv (Z := Z) prep))
        (EuclideanSpace.single ((a, z), b₀) 1))))) = _
  rw [permutationUnitary_single]
  change (permutationUnitary (prepareEquiv (Z := Z) prep).symm)
    (((oracle F x)†) ((permutationUnitary (copyEquiv (A := A) value))
      (oracle F x (EuclideanSpace.single ((a, z), prep a b₀) 1)))) = _
  rw [hprep, hForward, permutationUnitary_single]
  change (permutationUnitary (prepareEquiv (Z := Z) prep).symm)
    (((oracle F x)†) (EuclideanSpace.single ((a, z + value (image x a)), image x a) 1)) = _
  rw [hReverse, permutationUnitary_single]
  congr 1
  change ((a, z + value (image x a)), (prep a).symm (encode a)) = _
  rw [← hprep, Equiv.symm_apply_apply]

/-- Basis correctness extends coherently to every logical input, using a fixed
clean encoding with the stated computational-basis action. -/
theorem program_intertwines [DecidableEq A] [DecidableEq B] [DecidableEq Z]
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (prep : A → B ≃ B) (value : B → Z)
    (b₀ : B) (encode : A → B) (image : X → A → B)
    (hprep : ∀ a, prep a b₀ = encode a)
    (hvalid : ∀ x a, F x (EuclideanSpace.single (encode a) 1) =
      EuclideanSpace.single (image x a) 1)
    (E : EuclideanSpace ℂ (A × Z) →ₗᵢ[ℂ] EuclideanSpace ℂ (Workspace A B Z))
    (hE : ∀ a z, E (EuclideanSpace.single (a, z) 1) =
      EuclideanSpace.single ((a, z), b₀) 1) (x : X) :
    (program F prep value).eval x ∘L E.toContinuousLinearMap =
      E.toContinuousLinearMap ∘L
        (LookupOracle.unitary (fun x a => value (image x a)) x).toLinearIsometry.toContinuousLinearMap := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (A × Z) ℂ).toBasis.ext
  intro az
  rcases az with ⟨a, z⟩
  change (program F prep value).eval x
    (E ((EuclideanSpace.basisFun (A × Z) ℂ) (a, z))) =
      E ((LookupOracle.unitary (fun x a => value (image x a)) x)
        ((EuclideanSpace.basisFun (A × Z) ℂ) (a, z)))
  rw [EuclideanSpace.basisFun_apply, hE,
    program_single F hF prep value b₀ encode image hprep hvalid x a z]
  symm
  change E ((permutationUnitary (basisEquiv (fun x a => value (image x a)) x))
    (EuclideanSpace.single (a, z) 1)) = _
  rw [permutationUnitary_single]
  exact hE a (z + value (image x a))

/-- Two calls to an arbitrary valid-basis oracle implement additive lookup on
one fixed clean subspace; no promise is imposed outside valid oracle inputs. -/
theorem two_query_certificate [DecidableEq A] [DecidableEq B] [DecidableEq Z]
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (prep : A → B ≃ B) (value : B → Z)
    (b₀ : B) (encode : A → B) (image : X → A → B)
    (hprep : ∀ a, prep a b₀ = encode a)
    (hvalid : ∀ x a, F x (EuclideanSpace.single (encode a) 1) =
      EuclideanSpace.single (image x a) 1)
    (E : EuclideanSpace ℂ (A × Z) →ₗᵢ[ℂ] EuclideanSpace ℂ (Workspace A B Z))
    (hE : ∀ a z, E (EuclideanSpace.single (a, z) 1) =
      EuclideanSpace.single ((a, z), b₀) 1) :
    EncodedOracle.ImplementsOn (oracle (A := A) (Z := Z) F)
      (fun x => (LookupOracle.unitary (fun x a => value (image x a)) x).toLinearIsometry.toContinuousLinearMap)
      E.toContinuousLinearMap 2 :=
  ⟨program F prep value,
    program_intertwines F hF prep value b₀ encode image hprep hvalid E hE, le_rfl⟩

omit [AddCommGroup Z] in
/-- The actual clean-state isometry has the required basis action. -/
theorem cleanEmbedding_single [DecidableEq A] [DecidableEq B] [DecidableEq Z]
    (b₀ : B) (a : A) (z : Z) :
    CleanValueEmbedding.embedding (K := ℂ) (I := A × Z) b₀
      (EuclideanSpace.single (a, z) 1) = EuclideanSpace.single ((a, z), b₀) 1 := by
  ext t
  rcases t with ⟨⟨a', z'⟩, b⟩
  by_cases hb : b = b₀
  · subst b
    simp [PiLp.single_apply]
  · simp [hb]

/-- Canonical two-query extraction of a classical label from an arbitrary
in-place unitary basis oracle. The preparation is the known swap taking the
fixed clean basis label to `encode a`; no further implementation or encoding
premise is required. -/
theorem two_query_lookup [DecidableEq A] [DecidableEq B] [DecidableEq Z]
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (value : B → Z)
    (b₀ : B) (encode : A → B) (image : X → A → B)
    (hvalid : ∀ x a, F x (EuclideanSpace.single (encode a) 1) =
      EuclideanSpace.single (image x a) 1) :
    EncodedOracle.ImplementsOn (oracle (A := A) (Z := Z) F)
      (fun x => (LookupOracle.unitary (fun x a => value (image x a)) x).toLinearIsometry.toContinuousLinearMap)
      (CleanValueEmbedding.embedding (K := ℂ) (I := A × Z) b₀).toContinuousLinearMap 2 := by
  exact two_query_certificate F hF (fun a => Equiv.swap b₀ (encode a)) value b₀
    encode image (fun a => Equiv.swap_apply_left b₀ (encode a)) hvalid
    (CleanValueEmbedding.embedding b₀) (cleanEmbedding_single b₀)

end Circuit

end
end SparseHamiltonian.LookupFromBasisOracle
