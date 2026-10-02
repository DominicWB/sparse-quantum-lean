import SparseHamiltonian.SynchronizedSelect

/-!
# Query accounting for the actual coherent reuse and smoothing construction

Each branch is the proved product of local slot interactions. Padding completed
branches by identity synchronizes SELECT in at most twice the filter degree.
The final theorem derives a uniform amplified program with cost at most `6*d*q`
from certificates for its entire synchronized layers. These layer certificates
are explicit implementation obligations, not assumed costs of individual branches.
-/

namespace SparseHamiltonian.ReuseQuery

noncomputable section
open ContinuousLinearMap OracleCircuit ReuseSchedule SynchronizedSelect
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The concrete slot interaction, or identity once that branch has finished. -/
def slotStep (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) (n r : ℕ) :
    Space n P V →L[ℂ] Space n P V :=
  if h : r < n then slotInteraction A B C D ⟨r, h⟩ else 1

omit [CompleteSpace P] [CompleteSpace V] in
/-- The product convention agrees exactly with the constructed reuse recurrence. -/
theorem product_slotStep (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) (n k : ℕ) :
    product (slotStep A B C D n) k = schedulePrefix A B C D n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      by_cases hk : k < n
      · simp only [product_succ, slotStep, schedulePrefix, dif_pos hk, ih]
        rfl
      · simp only [product_succ, slotStep, schedulePrefix, dif_neg hk, one_mul, ih]

omit [CompleteSpace P] [CompleteSpace V] in
theorem fullReuse_eq_product (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) (n : ℕ) :
    CoherentReuse.fullReuse A B C D n = product (slotStep A B C D n) n := by
  rw [product_slotStep, schedulePrefix_eq_fullReuse]

omit [CompleteSpace P] [CompleteSpace V] in
/-- Identity padding does not alter the already truncated concrete slot step. -/
theorem padded_slotStep (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) (n r : ℕ) :
    (if r < n then slotStep A B C D n r else 1) = slotStep A B C D n r := by
  by_cases hr : r < n
  · exact if_pos hr
  · simp only [if_neg hr, slotStep, dif_neg hr]

/-- One actual SELECT layer acts on all unfinished branches simultaneously. -/
def reuseLayer (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) (d r : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := V) d) →L[ℂ]
      PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := V) d) :=
  WeightedClock.diagonal (fun i => slotStep A B C D (ReuseWeights.length d i) r)

omit [CompleteSpace P] [CompleteSpace V] in
/-- The actual smoothing SELECT has a synchronized schedule of `2*d` layers. -/
theorem circuit_eq_product (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) (d : ℕ) (hd : 0 < d) :
    SmoothingLCU.circuit A B C D d = product (reuseLayer A B C D d) (2 * d) := by
  have h := schedule_eq
    (fun i : ReuseWeights.Index d => slotStep A B C D (ReuseWeights.length d i))
    (ReuseWeights.length d) (2 * d) (ReuseWeights.length_le d hd)
  change product (fun r => WeightedClock.diagonal
    (fun i : ReuseWeights.Index d => if r < ReuseWeights.length d i then
      slotStep A B C D (ReuseWeights.length d i) r else 1)) (2 * d) = _ at h
  simp only [padded_slotStep, ← fullReuse_eq_product] at h
  exact h.symm

/-- Uniform implementations of the whole layers compose to the actual SELECT,
with no multiplicative factor equal to the number of LCU branches. -/
theorem circuit_implements {X : Type*}
    (d q : ℕ) (hd : 0 < d)
    (O : X → PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := V) d) →L[ℂ]
      PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := V) d))
    (A : X → P →L[ℂ] P) (B : X → V →L[ℂ] P)
    (C : X → P →L[ℂ] V) (D : X → V →L[ℂ] V)
    (hLayer : ∀ r < 2 * d,
      Implements O (fun x => reuseLayer (A x) (B x) (C x) (D x) d r) q) :
    Implements O (fun x => SmoothingLCU.circuit (A x) (B x) (C x) (D x) d) (2 * d * q) := by
  have h := implements_product_uniform O
    (fun r x => reuseLayer (A x) (B x) (C x) (D x) d r) q (2 * d) hLayer
  exact h.congr (fun x => (circuit_eq_product (A x) (B x) (C x) (D x) d hd).symm)

/-- The implemented smoothing isometry has a uniform program with at most
`6*d*q` calls when each complete synchronized layer is implemented with `q`
calls. Input preparations are fixed independently of the unknown oracle input. -/
theorem implementation_query_certificate
    [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    {X : Type*} (L k : ℕ) (hL : 1 ≤ L) (hd : 0 < k * (L - 1))
    (O : X → PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := V) (k * (L - 1))) →L[ℂ]
      PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := V) (k * (L - 1))))
    (A : X → P →L[ℂ] P) (B : X → V →L[ℂ] P)
    (C : X → P →L[ℂ] V) (D : X → V →L[ℂ] V)
    (hStep : ∀ x p v, ‖A x p + B x v‖ ^ 2 + ‖D x v + C x p‖ ^ 2 =
      ‖p‖ ^ 2 + ‖v‖ ^ 2)
    (q : ℕ)
    (hLayer : ∀ r < 2 * (k * (L - 1)), Implements O
      (fun x => reuseLayer (A x) (B x) (C x) (D x) (k * (L - 1)) r) q) :
    ∃ p : Program O, p.count ≤ 6 * (k * (L - 1)) * q ∧ ∀ x,
      p.eval x ∘L SmoothingLCU.input (P := P) (V := V)
        (AveragingPolynomial.filter L k).coeff (k * (L - 1)) =
          AmplifiedSmoothing.implementation L k (A x) (B x) (C x) (D x) := by
  obtain ⟨p, hp, hEval⟩ := AmplificationQuery.implementation_query_certificate
    L k hL hd O A B C D hStep (2 * (k * (L - 1)) * q)
      (circuit_implements (k * (L - 1)) q hd O A B C D hLayer)
  refine ⟨p, ?_, hEval⟩
  convert hp using 1
  ring

end
end SparseHamiltonian.ReuseQuery
