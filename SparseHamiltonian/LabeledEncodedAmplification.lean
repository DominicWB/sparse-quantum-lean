import SparseHamiltonian.LabeledEncodedOracle

/-!
# Labeled physical implementations of coherent reuse and amplification

These certificates allow a physical oracle workspace larger than the logical
LCU space. Correctness is required only on a fixed encoded subspace. All branch
layers still require one uniform implementation of the entire layer.
-/

namespace SparseHamiltonian.LabeledEncodedAmplification

noncomputable section
open ContinuousLinearMap OracleCircuit LabeledEncodedOracle AmplificationQuery
open scoped InnerProduct

variable {Label : Type*}
variable {H P K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The same three-SELECT query bound holds when SELECT is implemented only
on the image of a fixed encoding into a larger physical workspace. -/
theorem threeSelect_implementsOn {X : Type*} {O : Label → X → K →L[ℂ] K}
    {S : X → P →L[ℂ] P} {q : ℕ} (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (hO : ∀ l x, IsUnitary (O l x)) (hS : ∀ x, IsUnitary (S x))
    (I J : H →L[ℂ] P) (hI : I† ∘L I = 1) (hJ : J† ∘L J = 1)
    (hImpl : ImplementsOn O S E q) :
    ImplementsOn O (fun x => threeSelect (S x) I J) E (3 * q) := by
  have hLogical := threeSelect_implements I J hI hJ (Implements.query (O := S))
  simpa only [Nat.mul_one] using ImplementsOn.trans hE hO hS hImpl hLogical

omit [CompleteSpace P] in
/-- Encoded implementations of whole layers compose with an explicit sum of
query allowances. No oracle action is assumed on the orthogonal complement. -/
theorem implementsOn_product {X : Type*} (O : Label → X → K →L[ℂ] K)
    (A : ℕ → X → P →L[ℂ] P) (E : P →L[ℂ] K) (q : ℕ → ℕ) (n : ℕ)
    (h : ∀ r < n, ImplementsOn O (A r) E (q r)) :
    ImplementsOn O (fun x => SynchronizedSelect.product (fun r => A r x) n) E
      (∑ r ∈ Finset.range n, q r) := by
  induction n with
  | zero => simpa only [SynchronizedSelect.product_zero, Finset.range_zero,
      Finset.sum_empty] using (ImplementsOn.identity (O := O) (E := E))
  | succ n hn =>
      have hPrev := hn (fun r hr => h r (Nat.lt_trans hr (Nat.lt_succ_self n)))
      have hLast := h n (Nat.lt_succ_self n)
      simpa only [SynchronizedSelect.product_succ, Finset.sum_range_succ,
        Nat.add_comm] using hLast.mul hPrev

omit [CompleteSpace P] in
/-- Uniform whole-layer query allowances add to the number of layers times
the allowance, including for encoded physical implementations. -/
theorem implementsOn_product_uniform {X : Type*} (O : Label → X → K →L[ℂ] K)
    (A : ℕ → X → P →L[ℂ] P) (E : P →L[ℂ] K) (q n : ℕ)
    (h : ∀ r < n, ImplementsOn O (A r) E q) :
    ImplementsOn O (fun x => SynchronizedSelect.product (fun r => A r x) n) E (n * q) := by
  simpa using implementsOn_product O A E (fun _ => q) n h

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace P] [CompleteSpace V] in
/-- The actual coherent smoothing SELECT compiles from encoded implementations
of its synchronized layers, using at most twice the degree many layers. -/
theorem circuit_implementsOn {X : Type*}
    (d q : ℕ) (hd : 0 < d) (O : Label → X → K →L[ℂ] K)
    (E : PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := V) d) →L[ℂ] K)
    (A : X → P →L[ℂ] P) (B : X → V →L[ℂ] P)
    (C : X → P →L[ℂ] V) (D : X → V →L[ℂ] V)
    (hLayer : ∀ r < 2 * d, ImplementsOn O
      (fun x => ReuseQuery.reuseLayer (A x) (B x) (C x) (D x) d r) E q) :
    ImplementsOn O (fun x => SmoothingLCU.circuit (A x) (B x) (C x) (D x) d)
      E (2 * d * q) := by
  have h := implementsOn_product_uniform O
    (fun r x => ReuseQuery.reuseLayer (A x) (B x) (C x) (D x) d r) E q (2 * d) hLayer
  exact h.congr (fun x => (ReuseQuery.circuit_eq_product (A x) (B x) (C x) (D x) d hd).symm)

/-- A physical program implements the complete amplified output on encoded
input. No preparation operation depending on unknown matrix entries is free. -/
theorem implementation_query_certificate
    [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    {X : Type*} (L k : ℕ) (hL : 1 ≤ L) (hd : 0 < k * (L - 1))
    (O : Label → X → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (E : PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := V) (k * (L - 1))) →L[ℂ] K)
    (hE : E† ∘L E = 1)
    (A : X → P →L[ℂ] P) (B : X → V →L[ℂ] P)
    (C : X → P →L[ℂ] V) (D : X → V →L[ℂ] V)
    (hStep : ∀ x p v, ‖A x p + B x v‖ ^ 2 + ‖D x v + C x p‖ ^ 2 =
      ‖p‖ ^ 2 + ‖v‖ ^ 2)
    (q : ℕ)
    (hLayer : ∀ r < 2 * (k * (L - 1)), ImplementsOn O
      (fun x => ReuseQuery.reuseLayer (A x) (B x) (C x) (D x) (k * (L - 1)) r) E q) :
    ∃ p : MultiOracleCircuit.Program O, p.count ≤ 6 * (k * (L - 1)) * q ∧ ∀ x,
      p.eval x ∘L (E ∘L SmoothingLCU.input (P := P) (V := V)
        (AveragingPolynomial.filter L k).coeff (k * (L - 1))) =
      E ∘L AmplifiedSmoothing.implementation L k (A x) (B x) (C x) (D x) := by
  have hmass := ReuseWeights.concrete_absolute_mass L k hL hd
  have hCircuit := circuit_implementsOn (k * (L - 1)) q hd O E A B C D hLayer
  have hUnit (x : X) : IsUnitary
      (SmoothingLCU.circuit (A x) (B x) (C x) (D x) (k * (L - 1))) :=
    SmoothingLCU.circuit_unitary (A x) (B x) (C x) (D x) (hStep x) _
  obtain ⟨p, hp, hq⟩ := threeSelect_implementsOn E hE hO hUnit
    (SmoothingLCU.input (P := P) (V := V) (AveragingPolynomial.filter L k).coeff (k * (L - 1)))
    (SmoothingLCU.output (P := P) (V := V) (AveragingPolynomial.filter L k).coeff (k * (L - 1)))
    (SmoothingLCU.input_isometry (P := P) (V := V) _ _ hd hmass)
    (SmoothingLCU.output_isometry (P := P) (V := V) _ _ hd hmass) hCircuit
  refine ⟨p, ?_, fun x => ?_⟩
  · calc
      p.count ≤ 3 * (2 * (k * (L - 1)) * q) := hq
      _ = 6 * (k * (L - 1)) * q := by ring
  · rw [← comp_assoc, hp, comp_assoc,
      implementation_eq_threeSelect L k (A x) (B x) (C x) (D x) (hStep x)]

end
end SparseHamiltonian.LabeledEncodedAmplification
