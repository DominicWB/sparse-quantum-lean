import GeneralODE.Block.Power
import GeneralODE.Analysis.History

/-!
# The history-matrix circuit: registers and the block formula

The history block encoding uses a term register (`id`, `step`, `src` and two
junk labels), a power register `P`, the history slot register and the system.
Slot-dependent coefficient states `φ_in(s)`, `φ_out(s)` on `Term × P` prepare
and unprepare the linear combination; a term-selected unitary `R_t` acts on the
slot register after a power circuit whose block is `|k, s⟩⟨k, s| ⊗ P_k`.  The
block of the composite is
`(B y)(s') = ∑_{t,k,s} conj(φ_out(s')(t,k)) φ_in(s)(t,k) (R_t)_{s's} P_k y(s)`.
-/

namespace SparseHamiltonian.GeneralODE.Registers

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators ComplexConjugate

/-- Matrix entry of an operator on a Euclidean space. -/
def entry {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (R : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ κ) (j : κ) (i : ι) : ℂ :=
  R (EuclideanSpace.single i 1) j

theorem apply_eq_sum_entry {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (R : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ κ) (v : EuclideanSpace ℂ ι) (j : κ) :
    R v j = ∑ i, v i * entry R j i := by
  have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℂ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  simp [entry, Finset.sum_apply]

/-- Term labels of the history linear combination. -/
inductive Term
  | id
  | step
  | src
  | junkIn
  | junkOut
  deriving DecidableEq, Fintype

theorem sum_term {M : Type*} [AddCommMonoid M] (f : Term → M) :
    ∑ t, f t = f .id + f .step + f .src + f .junkIn + f .junkOut := by
  have h : (Finset.univ : Finset Term) = {.id, .step, .src, .junkIn, .junkOut} := by decide
  rw [h]
  simp [Finset.sum_insert]
  abel

section Layout

variable {S P n : Type} [Fintype S] [DecidableEq S] [Fintype P] [DecidableEq P]
  [Fintype n] [DecidableEq n]

variable (S P n) in
/-- Register reordering for the coefficient map. -/
def coefFrame : S × ((Term × P) × n) ≃ Term × ((P × S) × n) where
  toFun q := (q.2.1.1, ((q.2.1.2, q.1), q.2.2))
  invFun q := (q.2.1.2, ((q.1, q.2.1.1), q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Coefficient map `|s⟩ ⊗ v ↦ ∑_{t,k} φ(s)(t,k) |t⟩ ⊗ |k, s⟩ ⊗ v`. -/
def coefMap (φ : S → EuclideanSpace ℂ (Term × P)) :
    EuclideanSpace ℂ (S × n) →L[ℂ] EuclideanSpace ℂ (Term × ((P × S) × n)) :=
  (LookupOracle.permutationUnitary (coefFrame S P n)).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    selMap (fun s => ketL (ν := n) (φ s))

omit [DecidableEq S] [DecidableEq P] [DecidableEq n] in
theorem coefMap_apply (φ : S → EuclideanSpace ℂ (Term × P)) (w : EuclideanSpace ℂ (S × n))
    (t : Term) (k : P) (s : S) (i : n) :
    coefMap φ w (t, ((k, s), i)) = φ s (t, k) * w (s, i) := rfl

/-- The adjoint of the coefficient map. -/
def coefAdj (φ : S → EuclideanSpace ℂ (Term × P)) :
    EuclideanSpace ℂ (Term × ((P × S) × n)) →L[ℂ] EuclideanSpace ℂ (S × n) :=
  selMap (fun s => braL (ν := n) (φ s)) ∘L
    (LookupOracle.permutationUnitary (coefFrame S P n)).symm.toContinuousLinearEquiv.toContinuousLinearMap

omit [DecidableEq S] [DecidableEq P] [DecidableEq n] in
theorem coefAdj_apply (φ : S → EuclideanSpace ℂ (Term × P))
    (z : EuclideanSpace ℂ (Term × ((P × S) × n))) (s : S) (i : n) :
    coefAdj φ z (s, i) = ∑ t, ∑ k, conj (φ s (t, k)) * z (t, ((k, s), i)) := by
  change braL (φ s) (slice ((LookupOracle.permutationUnitary (coefFrame S P n)).symm z) s) i = _
  rw [braL_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro t _
  apply Finset.sum_congr rfl; intro k _
  rw [slice_apply, permutationUnitary_symm_apply]
  rfl

omit [DecidableEq S] [DecidableEq P] [DecidableEq n] in
theorem coefMap_adjoint (φ : S → EuclideanSpace ℂ (Term × P)) :
    (coefMap (n := n) φ)† = coefAdj φ := by
  unfold coefMap coefAdj
  rw [adjoint_comp, selMap_adjoint, LinearIsometryEquiv.adjoint_eq_symm]
  simp only [ketL_adjoint]

omit [DecidableEq S] [DecidableEq P] [DecidableEq n] in
theorem coefMap_isometry (φ : S → EuclideanSpace ℂ (Term × P)) (hφ : ∀ s, ‖φ s‖ = 1) :
    (coefMap (n := n) φ)† ∘L coefMap φ = 1 := by
  unfold coefMap
  rw [adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm]
  have hperm : ((LookupOracle.permutationUnitary (coefFrame S P n)).symm.toContinuousLinearEquiv.toContinuousLinearMap) ∘L
      (LookupOracle.permutationUnitary (coefFrame S P n)).toContinuousLinearEquiv.toContinuousLinearMap = 1 := by
    ext1 v; simp
  calc (selMap (fun s => ketL (ν := n) (φ s)))† ∘L
        ((LookupOracle.permutationUnitary (coefFrame S P n)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          (LookupOracle.permutationUnitary (coefFrame S P n)).toContinuousLinearEquiv.toContinuousLinearMap ∘L
            selMap (fun s => ketL (ν := n) (φ s)))
      = (selMap (fun s => ketL (ν := n) (φ s)))† ∘L selMap (fun s => ketL (ν := n) (φ s)) := by
        rw [← comp_assoc _ _ (selMap _), hperm, one_comp_eq]
    _ = 1 := selMap_isometry _ (fun s => ketL_isometry (φ s) (hφ s))

variable (S P n) in
/-- Frame for actions on the slot inside `(P × S) × n`. -/
def slotFrame : (P × S) × n ≃ (P × n) × S where
  toFun q := ((q.1.1, q.2), q.1.2)
  invFun q := ((q.1.1, q.2), q.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Action of a slot unitary inside `(P × S) × n`. -/
def liftSlot (R : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) :
    EuclideanSpace ℂ ((P × S) × n) →L[ℂ] EuclideanSpace ℂ ((P × S) × n) :=
  onFactor (slotFrame S P n) R

omit [DecidableEq P] [DecidableEq n] in
theorem liftSlot_apply (R : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S)
    (w : EuclideanSpace ℂ ((P × S) × n)) (k : P) (s' : S) (i : n) :
    liftSlot R w ((k, s'), i) = ∑ s, w ((k, s), i) * entry R s' s := by
  rw [liftSlot, onFactor_apply, apply_eq_sum_entry]
  rfl

omit [DecidableEq P] [DecidableEq n] in
/-- The block formula of the history combination. -/
theorem block_formula (φin φout : S → EuclideanSpace ℂ (Term × P))
    (R : Term → (EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S))
    (Pk : P → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n))
    (y : EuclideanSpace ℂ (S × n)) (s' : S) (i : n) :
    ((coefMap φout)† ∘L selMap (fun t => liftSlot (n := n) (P := P) (R t)) ∘L
        specHom Term ((P × S) × n) (selMap (fun c : P × S => Pk c.1)) ∘L coefMap φin) y (s', i) =
      ∑ t, ∑ k, conj (φout s' (t, k)) *
        ∑ s, (φin s (t, k) * Pk k (slice y s) i) * entry (R t) s' s := by
  rw [coefMap_adjoint]
  simp only [comp_apply]
  rw [coefAdj_apply]
  apply Finset.sum_congr rfl; intro t _
  apply Finset.sum_congr rfl; intro k _
  congr 1
  rw [selMap_apply, liftSlot_apply]
  apply Finset.sum_congr rfl; intro s _
  congr 1
  rw [slice_apply, specHom_eq, spectator_apply, selMap_apply]
  have hsl : slice (WithLp.toLp 2 (fun b : (P × S) × n => coefMap φin y (t, b)) :
      EuclideanSpace ℂ ((P × S) × n)) (k, s) = φin s (t, k) • slice y s := by
    ext j; simp [coefMap_apply]
  simp only at hsl ⊢
  rw [hsl, map_smul]
  rfl

end Layout

end

end SparseHamiltonian.GeneralODE.Registers
