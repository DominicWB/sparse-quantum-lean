import SparseHamiltonian.WeightedClock
import SparseHamiltonian.OracleCircuit
import TimeDependentHamiltonian.Chronology.Colligation

set_option autoImplicit false

/-!
# Products of block encodings with fresh encoding ancillas (`odel:lem:dyson`)

The proof of Lemma `odel:lem:dyson` says "apply each `U_{j_l}` with a fresh zero work register
`a_l`";
"Distinct work registers prevent a failed earlier factor from returning to the selected block
through a later factor." On a payload space `H` with a public isometric encoding
`e : P → H` (`e† e = 1`), a slot unitary `A` represents the compression `e† A e`. A product of
`K` slots does not compress to the product of the compressions, because the unencoded part of
one slot leaks into the next. A fresh flag bit per slot removes the leak: after slot `j` the
known **flag split** keeps the encoded part `Π = e e†` and moves the unencoded part `(1 - Π)`
to the branch with flag `j` flipped. Flags are never cleared, so the all-zero-flag encoded
component after `K` slots is exactly the product of the compressions.

The construction is coherent over a branch register `Λ` (the LCU label): the slot operators
`A j l` may depend on the label `l`, and every operator here is a fixed (input-independent)
gate apart from the slot operators themselves.

* `flagSplit e j`: the known flag split of slot `j` (unitary, `flagSplit_unitary`);
* `zeroFlags e`: the isometric encoding of the branch space at all flags zero;
* `layer e A j = flagSplit e j ∘ diag_l (A l)` (identity for `j ≥ K`);
* `flagged_compression`: `zeroFlags† (∏_{j<K} layer e (A j) j) zeroFlags =
  diag_l (∏_{j<K} e† A j l e)` for **arbitrary** slot operators.
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

open SparseHamiltonian ContinuousLinearMap OracleCircuit
open SparseHamiltonian.TimeDependent (evolution)
open scoped BigOperators InnerProduct

/-- One flag bit per slot. -/
abbrev Flags (K : ℕ) : Type := Fin K → Bool

/-- The flagged branch space: branch label, slot flags and payload. -/
abbrev FlagSpace (Λ H : Type*) [Fintype Λ] [NormedAddCommGroup H] (K : ℕ) : Type _ :=
  PiLp 2 (fun _ : Λ × Flags K => H)

variable {Λ H P : Type*} [Fintype Λ] [DecidableEq Λ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- Flip the flag of slot `j` (an involution of the branch-and-flag register). -/
def flipEquiv {K : ℕ} (j : Fin K) : Λ × Flags K ≃ Λ × Flags K where
  toFun ω := (ω.1, Function.update ω.2 j (!ω.2 j))
  invFun ω := (ω.1, Function.update ω.2 j (!ω.2 j))
  left_inv ω := by
    rcases ω with ⟨l, f⟩
    ext i
    · rfl
    · by_cases h : i = j
      · subst h; simp
      · simp [Function.update_of_ne h]
  right_inv ω := by
    rcases ω with ⟨l, f⟩
    ext i
    · rfl
    · by_cases h : i = j
      · subst h; simp
      · simp [Function.update_of_ne h]

omit [Fintype Λ] [DecidableEq Λ] in
/-- Flipping the flag of slot `j` twice is the identity. -/
theorem flipEquiv_flipEquiv {K : ℕ} (j : Fin K) (ω : Λ × Flags K) :
    flipEquiv j (flipEquiv j ω) = ω :=
  (flipEquiv j).left_inv ω

/-- The orthogonal projection `Π = e e†` onto the encoded subspace. -/
def encodedProjector (e : P →L[ℂ] H) : H →L[ℂ] H := e ∘L e†

/-- An isometric encoding is left-inverted by its adjoint, pointwise. -/
theorem adjoint_apply_self (e : P →L[ℂ] H) (he : e† ∘L e = 1) (x : P) : (e†) (e x) = x := by
  simpa using ContinuousLinearMap.ext_iff.mp he x

/-- `Π = e e†` is idempotent for an isometric encoding. -/
theorem encodedProjector_idem (e : P →L[ℂ] H) (he : e† ∘L e = 1) (v : H) :
    encodedProjector e (encodedProjector e v) = encodedProjector e v := by
  simp only [encodedProjector, comp_apply, adjoint_apply_self e he]

/-- `Π = e e†` is self-adjoint. -/
theorem encodedProjector_adjoint (e : P →L[ℂ] H) :
    (encodedProjector e)† = encodedProjector e := by
  rw [encodedProjector, adjoint_comp, adjoint_adjoint]

/-- `1 - Π` is self-adjoint. -/
theorem one_sub_encodedProjector_adjoint (e : P →L[ℂ] H) :
    (1 - encodedProjector e)† = 1 - encodedProjector e := by
  rw [← star_eq_adjoint, star_sub, star_one, star_eq_adjoint, encodedProjector_adjoint]

/-- **The flag split of slot `j`**: on branch `(l, f)` the new value is
`Π v(l, f) + (1 - Π) v(l, flip_j f)`. A known gate. -/
def flagSplit {K : ℕ} (e : P →L[ℂ] H) (j : Fin K) : FlagSpace Λ H K →L[ℂ] FlagSpace Λ H K :=
  WeightedClock.diagonal (fun _ : Λ × Flags K => encodedProjector e) +
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ H (flipEquiv (Λ := Λ) j)).toLinearIsometry.toContinuousLinearMap
      ∘L WeightedClock.diagonal (fun _ : Λ × Flags K => 1 - encodedProjector e)

omit [DecidableEq Λ] in
/-- The flag split, pointwise: `Π v(ω) + (1 - Π) v(flip_j ω)`. -/
theorem flagSplit_apply {K : ℕ} (e : P →L[ℂ] H) (j : Fin K) (ψ : FlagSpace Λ H K)
    (ω : Λ × Flags K) :
    flagSplit e j ψ ω =
      encodedProjector e (ψ ω) + (1 - encodedProjector e) (ψ (flipEquiv j ω)) := rfl

omit [DecidableEq Λ] in
/-- The flag split is self-adjoint. -/
theorem flagSplit_adjoint {K : ℕ} (e : P →L[ℂ] H) (j : Fin K) :
    (flagSplit (Λ := Λ) e j)† = flagSplit e j := by
  have hS : ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ H
      (flipEquiv (Λ := Λ) j)).toLinearIsometry.toContinuousLinearMap)† =
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ H
        (flipEquiv (Λ := Λ) j)).toLinearIsometry.toContinuousLinearMap := by
    have h := LinearIsometryEquiv.adjoint_eq_symm
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ H (flipEquiv (Λ := Λ) j))
    rw [LinearIsometryEquiv.piLpCongrLeft_symm] at h
    exact h
  have hcomm : ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ H
      (flipEquiv (Λ := Λ) j)).toLinearIsometry.toContinuousLinearMap) ∘L
        WeightedClock.diagonal (fun _ : Λ × Flags K => 1 - encodedProjector e) =
      WeightedClock.diagonal (fun _ : Λ × Flags K => 1 - encodedProjector e) ∘L
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ H
          (flipEquiv (Λ := Λ) j)).toLinearIsometry.toContinuousLinearMap) := by
    ext ψ ω
    rfl
  rw [flagSplit, map_add, adjoint_comp, WeightedClock.diagonal_adjoint,
    WeightedClock.diagonal_adjoint, encodedProjector_adjoint,
    one_sub_encodedProjector_adjoint, hS, ← hcomm]

omit [DecidableEq Λ] in
/-- The flag split is an involution. -/
theorem flagSplit_mul_self {K : ℕ} (e : P →L[ℂ] H) (he : e† ∘L e = 1) (j : Fin K) :
    flagSplit (Λ := Λ) e j * flagSplit e j = 1 := by
  refine ContinuousLinearMap.ext fun ψ => PiLp.ext fun ω => ?_
  rw [mul_apply_eq_comp, flagSplit_apply, flagSplit_apply, flagSplit_apply, flipEquiv_flipEquiv]
  simp only [map_add, sub_apply, one_apply_eq_self, map_sub, encodedProjector_idem e he]
  abel

omit [DecidableEq Λ] in
/-- The flag split is unitary for an isometric encoding. -/
theorem flagSplit_unitary {K : ℕ} (e : P →L[ℂ] H) (he : e† ∘L e = 1) (j : Fin K) :
    IsUnitary (flagSplit (Λ := Λ) e j) := by
  rw [IsUnitary, star_eq_adjoint, flagSplit_adjoint, flagSplit_mul_self e he]
  exact ⟨rfl, rfl⟩

/-- **The encoding at all flags zero**: `w ↦ ((l, f) ↦ if f = 0 then e (w l) else 0)`. -/
def zeroFlags {K : ℕ} (e : P →L[ℂ] H) : PiLp 2 (fun _ : Λ => P) →L[ℂ] FlagSpace Λ H K :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Λ × Flags K => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun ω : Λ × Flags K =>
      if ω.2 = (fun _ => false) then
        e ∘L (ContinuousLinearMap.proj ω.1 ∘L
          (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Λ => P)).toContinuousLinearMap)
      else 0)

omit [DecidableEq Λ] [CompleteSpace H] [CompleteSpace P] in
/-- The all-zero-flag encoding, pointwise. -/
theorem zeroFlags_apply {K : ℕ} (e : P →L[ℂ] H) (w : PiLp 2 (fun _ : Λ => P))
    (ω : Λ × Flags K) :
    zeroFlags e w ω = if ω.2 = (fun _ => false) then e (w ω.1) else 0 := by
  by_cases h : ω.2 = (fun _ => false) <;> simp [zeroFlags, h]

omit [DecidableEq Λ] in
/-- The adjoint of the all-zero-flag encoding reads the all-zero-flag branch and decodes it. -/
theorem zeroFlags_adjoint_apply {K : ℕ} (e : P →L[ℂ] H) (v : FlagSpace Λ H K) (l : Λ) :
    ((zeroFlags (Λ := Λ) (K := K) e)†) v l = (e†) (v (l, fun _ => false)) := by
  have key : ((zeroFlags (Λ := Λ) (K := K) e)†) v =
      WithLp.toLp 2 (fun l : Λ => (e†) (v (l, fun _ => false))) := by
    refine ext_inner_right ℂ fun w => ?_
    rw [adjoint_inner_left, PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [zeroFlags_apply, apply_ite, adjoint_inner_left]
  rw [key]

omit [DecidableEq Λ] in
/-- The all-zero-flag embedding is an isometry. -/
theorem zeroFlags_isometry {K : ℕ} (e : P →L[ℂ] H) (he : e† ∘L e = 1) :
    (zeroFlags (Λ := Λ) (K := K) e)† ∘L zeroFlags e = 1 := by
  refine ContinuousLinearMap.ext fun w => PiLp.ext fun l => ?_
  rw [comp_apply, zeroFlags_adjoint_apply, zeroFlags_apply, if_pos rfl, one_apply_eq_self]
  exact adjoint_apply_self e he _

/-- One flagged layer: the slot operators on every branch, then the flag split of slot `j`;
the identity for `j ≥ K`. -/
def layer {K : ℕ} (e : P →L[ℂ] H) (A : Λ → H →L[ℂ] H) (j : ℕ) :
    FlagSpace Λ H K →L[ℂ] FlagSpace Λ H K :=
  if h : j < K then
    flagSplit e ⟨j, h⟩ ∘L WeightedClock.diagonal (fun ω : Λ × Flags K => A ω.1)
  else 1

omit [DecidableEq Λ] in
/-- A flagged layer `j < K`, pointwise: `Π A_l v(l, f) + (1 - Π) A_l v(flip_j (l, f))`. -/
theorem layer_apply {K : ℕ} (e : P →L[ℂ] H) (A : Λ → H →L[ℂ] H) {j : ℕ} (hj : j < K)
    (ψ : FlagSpace Λ H K) (ω : Λ × Flags K) :
    layer (K := K) e A j ψ ω = encodedProjector e (A ω.1 (ψ ω)) +
      (1 - encodedProjector e) (A ω.1 (ψ (flipEquiv ⟨j, hj⟩ ω))) := by
  rw [layer, dif_pos hj]
  rfl

omit [DecidableEq Λ] in
/-- **Invariant of the flagged layers.** After `m ≤ K` layers applied to an all-zero-flag
input: (i) every branch with a raised flag among the slots `m, …, K-1` is zero; (ii) the
all-zero-flag branch `l` is the encoding of `∏_{j<m} e† A_j(l) e` applied to the input. -/
theorem flagged_invariant {K : ℕ} (e : P →L[ℂ] H)
    (A : ℕ → Λ → H →L[ℂ] H) (w : PiLp 2 (fun _ : Λ => P)) :
    ∀ m ≤ K,
      (∀ ω : Λ × Flags K, (∃ i : Fin K, m ≤ (i : ℕ) ∧ ω.2 i = true) →
        evolution (fun j => layer (K := K) e (A j) j) m (zeroFlags e w) ω = 0) ∧
      ∀ l : Λ, evolution (fun j => layer (K := K) e (A j) j) m (zeroFlags e w)
          (l, fun _ => false) = e (evolution (fun j => e† ∘L A j l ∘L e) m (w l)) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨fun ω ⟨i, _, hi⟩ => ?_, fun l => ?_⟩
    · have hf : ω.2 ≠ fun _ => false := fun h => by simp [h] at hi
      rw [TimeDependent.evolution_zero, one_apply_eq_self, zeroFlags_apply, if_neg hf]
    · rw [TimeDependent.evolution_zero, TimeDependent.evolution_zero, one_apply_eq_self, one_apply_eq_self,
        zeroFlags_apply, if_pos rfl]
  | succ m ih =>
    intro hm
    have hmK : m < K := hm
    obtain ⟨ih1, ih2⟩ := ih (Nat.le_of_succ_le hm)
    refine ⟨fun ω ⟨i, hi, hωi⟩ => ?_, fun l => ?_⟩
    · rw [TimeDependent.evolution_succ, mul_apply_eq_comp, layer_apply e _ hmK,
        ih1 ω ⟨i, by omega, hωi⟩]
      have hne : i ≠ ⟨m, hmK⟩ := fun h => by rw [h] at hi; simp at hi
      have hflip : (flipEquiv ⟨m, hmK⟩ ω).2 i = true := by
        show Function.update ω.2 ⟨m, hmK⟩ (!ω.2 ⟨m, hmK⟩) i = true
        rw [Function.update_of_ne hne]
        exact hωi
      rw [ih1 _ ⟨i, by omega, hflip⟩]
      simp
    · rw [TimeDependent.evolution_succ, mul_apply_eq_comp, layer_apply e _ hmK]
      have h0 : evolution (fun j => layer (K := K) e (A j) j) m (zeroFlags e w)
          (flipEquiv ⟨m, hmK⟩ (l, fun _ => false)) = 0 :=
        ih1 _ ⟨⟨m, hmK⟩, le_rfl, by simp [flipEquiv]⟩
      rw [h0, map_zero, map_zero, add_zero, ih2 l, TimeDependent.evolution_succ, mul_apply_eq_comp]
      rfl

omit [DecidableEq Λ] in
/-- **Fresh encoding ancillas** (proof of Lemma `odel:lem:dyson`): the all-zero-flag compression of
`K` flagged layers is the branchwise product of the slot compressions, for arbitrary slot
operators. -/
theorem flagged_compression {K : ℕ} (e : P →L[ℂ] H) (he : e† ∘L e = 1)
    (A : ℕ → Λ → H →L[ℂ] H) :
    (zeroFlags (Λ := Λ) (K := K) e)† ∘L evolution (fun j => layer e (A j) j) K ∘L
        zeroFlags e =
      WeightedClock.diagonal (fun l : Λ => evolution (fun j => e† ∘L A j l ∘L e) K) := by
  refine ContinuousLinearMap.ext fun w => PiLp.ext fun l => ?_
  rw [comp_apply, comp_apply, zeroFlags_adjoint_apply,
    (flagged_invariant e A w K le_rfl).2 l, adjoint_apply_self e he,
    WeightedClock.diagonal_apply]

end

end ODELowerBoundExtensions.Dyson
