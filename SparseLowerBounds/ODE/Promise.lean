import SparseLowerBounds.Query.PositiveAdversary

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The joint search-parity promise problem

Manuscript: the joint search-parity problem before Lemma `odel:lem:outer`, introduced as "a query
problem in which search and parity occur in the same adversary argument". An
input consists of hidden positions `j_{ak} ∈ ℤ_m` for candidates
`a ∈ {1, …, M}` and stages `k ∈ {1, …, n}` (`Positions M n m`). The membership
oracle answers the bit `[z = j_{ak}]` at query `(a, k, z)` (`membership`, Boolean
strings on `Fin M × Fin n × Fin m`). Candidate `a` has parity
`σ_a = (-1)^{Σ_k j_{ak}}` (the release-library `parity` of `Query/PhaseOracle`);
the promise is that exactly one candidate `a_*` is odd (`Promised`,
`oddCand`). The task is to decide whether `a_*` lies in the first or the
second half of the candidates; `halfSign` is the `±1` answer.

This module is shared by the adversary (`ODE/JointGraph`, `ODE/JointAdversary`),
the ODE encoding (`ODE/JointInstance`, `ODE/JointCompile`) and the theorem
(`ODE/JointTheorem`).
-/

namespace SparseLowerBounds.ODE

noncomputable section

/-- Hidden positions `j_{ak}`: candidate `a`, stage `k`, position in `ℤ_m`
(Section `odel:sec:main`). -/
abbrev Positions (M n m : ℕ) : Type := Fin M → Fin n → Fin m

/-- Candidate `a` of `j` is odd: `σ_a = -1`, i.e. `Σ_k j_{ak}` is odd (Section `odel:sec:main`). -/
def IsOddCand {M n m : ℕ} (j : Positions M n m) (a : Fin M) : Prop :=
  Odd (∑ k, (j a k : ℕ))

instance {M n m : ℕ} (j : Positions M n m) (a : Fin M) : Decidable (IsOddCand j a) := by
  unfold IsOddCand; infer_instance

/-- **The promised inputs** (Section `odel:sec:main`): exactly one candidate is odd. -/
def Promised (M n m : ℕ) : Type := {j : Positions M n m // ∃! a, IsOddCand j a}

instance (M n m : ℕ) : Fintype (Promised M n m) := by
  classical
  unfold Promised
  infer_instance

instance (M n m : ℕ) : DecidableEq (Promised M n m) := Classical.decEq _

variable {M n m : ℕ}

/-- The unique odd candidate `a_*` of a promised input. -/
def oddCand (x : Promised M n m) : Fin M := x.2.exists.choose

theorem oddCand_spec (x : Promised M n m) : IsOddCand x.1 (oddCand x) :=
  x.2.exists.choose_spec

/-- A candidate is odd exactly when it is `a_*`. -/
theorem isOddCand_iff (x : Promised M n m) (a : Fin M) : IsOddCand x.1 a ↔ a = oddCand x :=
  ⟨fun h => x.2.unique h (oddCand_spec x), fun h => h ▸ oddCand_spec x⟩

/-- The parity `σ_a` of the release library is `-1` exactly at `a_*`. -/
theorem parity_eq_neg_one_iff (j : Positions M n m) (a : Fin M) :
    parity (j a) = -1 ↔ IsOddCand j a := by
  unfold parity IsOddCand
  constructor
  · intro h
    rcases Nat.even_or_odd (∑ k, (j a k : ℕ)) with he | ho
    · rw [he.neg_one_pow] at h; norm_num at h
    · exact ho
  · intro h; exact h.neg_one_pow

/-- Every candidate other than `a_*` has parity `+1`. -/
theorem parity_eq_one_of_ne (x : Promised M n m) {a : Fin M} (ha : a ≠ oddCand x) :
    parity (x.1 a) = 1 := by
  have hne : ¬ IsOddCand x.1 a := fun h => ha ((isOddCand_iff x a).mp h)
  unfold IsOddCand at hne
  unfold parity
  exact (Nat.not_odd_iff_even.mp hne).neg_one_pow

theorem parity_oddCand (x : Promised M n m) : parity (x.1 (oddCand x)) = -1 :=
  (parity_eq_neg_one_iff _ _).mpr (oddCand_spec x)

/-- **The membership bits** `y_X(a, k, z) = [j_{ak} = z]` (Section `odel:sec:main`). -/
def membership (x : Promised M n m) (i : Fin M × Fin n × Fin m) : Bool :=
  decide (x.1 i.1 i.2.1 = i.2.2)

/-- The answer of the decision problem (Section `odel:sec:main`): `+1` if `a` is in the first
half of the candidates (`a < M/2`), `-1` otherwise. -/
def halfSign (M : ℕ) (a : Fin M) : ℝ := if (a : ℕ) < M / 2 then 1 else -1

theorem abs_halfSign (a : Fin M) : |halfSign M a| = 1 := by
  unfold halfSign; split_ifs <;> norm_num

theorem halfSign_sq (a : Fin M) : halfSign M a ^ 2 = 1 := by
  unfold halfSign; split_ifs <;> norm_num

/-- Promised inputs exist when there is a candidate, a stage and an odd position. -/
theorem nonempty_promised (hM : 1 ≤ M) (hn : 1 ≤ n) (hm : 2 ≤ m) :
    Nonempty (Promised M n m) := by
  classical
  let a0 : Fin M := ⟨0, hM⟩
  let k0 : Fin n := ⟨0, hn⟩
  let j : Positions M n m := fun a k => if a = a0 ∧ k = k0 then ⟨1, hm⟩ else ⟨0, by omega⟩
  have hsum : ∀ a, (∑ k, (j a k : ℕ)) = if a = a0 then 1 else 0 := by
    intro a
    by_cases ha : a = a0
    · rw [if_pos ha, Finset.sum_eq_single k0]
      · simp [j, ha]
      · intro k _ hk; simp [j, hk]
      · simp
    · rw [if_neg ha]
      refine Finset.sum_eq_zero fun k _ => ?_
      simp [j, ha]
  refine ⟨⟨j, a0, ?_, fun a ha => ?_⟩⟩
  · show Odd (∑ k, (j a0 k : ℕ))
    rw [hsum, if_pos rfl]; exact odd_one
  · have ha' : Odd (∑ k, (j a k : ℕ)) := ha
    rw [hsum] at ha'
    by_contra hne
    rw [if_neg hne] at ha'
    exact Nat.not_odd_zero ha'

end

end SparseLowerBounds.ODE
end
