import SparseLowerBounds.Imports

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Boolean oracles in phase form

A Boolean oracle for a string `y : I → Bool` is
`phase P y = 1 - 2 Σ_{i, y i} P i`, for a fixed family `P` of pairwise
orthogonal orthogonal projections on an arbitrary Hilbert workspace `K`.

This one form covers the usual Boolean access models (manuscript lines
5132-5133 and 2143-2146). The XOR oracle `|i, z⟩ ↦ |i, z ⊕ y i⟩` equals
`phase P y` with `P i = |i⟩⟨i| ⊗ |−⟩⟨−|`, because `X = 1 - 2 |−⟩⟨−|` on the
response qubit (the Hadamard-basis form used by the manuscript); any other
fixed basis change is a free gate of an `OracleCircuit.Program`. A controlled
oracle multiplies each `P i` by the
control projector, and garbage or spectator registers tensor each `P i` with
the identity. All of these are again projection families, so lower bounds
proved for `phase` apply to them.

One-hot inputs (`oneHotOracle`): `n` strings of length `m`, string `k` marked
at position `j k`, so `I = Fin n × Fin m` and `y (k, a) = (j k = a)`. The
hidden parity is `parity j = (-1)^{Σ_k j k}`.
-/

namespace SparseLowerBounds

noncomputable section
open SparseHamiltonian OracleCircuit

/-- A family of pairwise orthogonal orthogonal (star) projections on `K`. -/
structure ProjFamily (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (I : Type*) where
  /-- The projection selecting query position `i`. -/
  proj : I → K →L[ℂ] K
  isStarProjection : ∀ i, IsStarProjection (proj i)
  orthogonal : ∀ i i', i ≠ i' → proj i * proj i' = 0

namespace ProjFamily

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {I : Type*} [Fintype I] (P : ProjFamily K I)

omit [Fintype I] in
theorem proj_mul_proj [DecidableEq I] (i i' : I) :
    P.proj i * P.proj i' = if i = i' then P.proj i else 0 := by
  split_ifs with h
  · subst h; exact (P.isStarProjection i).isIdempotentElem
  · exact P.orthogonal i i' h

omit [Fintype I] in
theorem proj_mul_sum [DecidableEq I] (S : Finset I) (i : I) :
    P.proj i * ∑ i' ∈ S, P.proj i' = if i ∈ S then P.proj i else 0 := by
  rw [Finset.mul_sum]
  simp_rw [P.proj_mul_proj i]
  rw [Finset.sum_ite_eq]

omit [Fintype I] in
theorem sum_mul_proj [DecidableEq I] (S : Finset I) (i : I) :
    (∑ i' ∈ S, P.proj i') * P.proj i = if i ∈ S then P.proj i else 0 := by
  rw [Finset.sum_mul]
  have h : ∀ i' ∈ S, P.proj i' * P.proj i = if i = i' then P.proj i else 0 := by
    intro i' _
    rw [P.proj_mul_proj i' i]
    by_cases h : i = i'
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq]

omit [Fintype I] in
theorem isSelfAdjoint_sum_proj (S : Finset I) :
    IsSelfAdjoint (∑ i ∈ S, P.proj i) :=
  isSelfAdjoint_sum S fun i _ => (P.isStarProjection i).isSelfAdjoint

omit [Fintype I] in
theorem sum_proj_mul_self (S : Finset I) :
    (∑ i ∈ S, P.proj i) * (∑ i ∈ S, P.proj i) = ∑ i ∈ S, P.proj i := by
  classical
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i hi => by rw [P.proj_mul_sum S i, if_pos hi]

omit [Fintype I] in
theorem isStarProjection_sum (S : Finset I) :
    IsStarProjection (∑ i ∈ S, P.proj i) :=
  ⟨P.sum_proj_mul_self S, P.isSelfAdjoint_sum_proj S⟩

omit [Fintype I] [CompleteSpace K] in
theorem one_sub_two_smul_mul_self {A : K →L[ℂ] K} (hA : A * A = A) :
    (1 - (2 : ℂ) • A) * (1 - (2 : ℂ) • A) = 1 := by
  rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, smul_mul_smul_comm, hA]
  rw [show (2 : ℂ) * 2 = 2 + 2 by norm_num, add_smul]
  abel

/-- The phase oracle `1 - 2 Σ_{i, y i} P i` of a Boolean string `y`. -/
def phase (y : I → Bool) : K →L[ℂ] K :=
  1 - (2 : ℂ) • ∑ i ∈ Finset.univ.filter (fun i => y i = true), P.proj i

/-- The projection onto the part of the workspace that makes no query. -/
def rest : K →L[ℂ] K := 1 - ∑ i, P.proj i

theorem isSelfAdjoint_phase (y : I → Bool) : IsSelfAdjoint (P.phase y) := by
  unfold phase
  rw [two_smul]
  exact (IsSelfAdjoint.one _).sub ((P.isSelfAdjoint_sum_proj _).add (P.isSelfAdjoint_sum_proj _))

/-- Phase oracles are involutions. -/
theorem phase_mul_self (y : I → Bool) : P.phase y * P.phase y = 1 :=
  one_sub_two_smul_mul_self (P.sum_proj_mul_self _)

theorem isUnitary_phase (y : I → Bool) : IsUnitary (P.phase y) := by
  have h := (P.isSelfAdjoint_phase y).star_eq
  exact ⟨by rw [h, P.phase_mul_self], by rw [h, P.phase_mul_self]⟩

/-- An inverse query is the same query. -/
theorem star_phase (y : I → Bool) : star (P.phase y) = P.phase y :=
  (P.isSelfAdjoint_phase y).star_eq

theorem isStarProjection_rest : IsStarProjection P.rest :=
  (P.isStarProjection_sum Finset.univ).one_sub

theorem proj_mul_rest (i : I) : P.proj i * P.rest = 0 := by
  classical
  rw [rest, mul_sub, mul_one, P.proj_mul_sum, if_pos (Finset.mem_univ i), sub_self]

theorem rest_mul_proj (i : I) : P.rest * P.proj i = 0 := by
  classical
  rw [rest, sub_mul, one_mul, P.sum_mul_proj, if_pos (Finset.mem_univ i), sub_self]

end ProjFamily

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {n m : ℕ}

/-- The Boolean membership oracle of `n` one-hot strings of length `m`, string
`k` marked at `j k`: `O_j = phase P (fun (k, a) => j k = a)`. -/
def oneHotOracle (P : ProjFamily K (Fin n × Fin m)) (j : Fin n → Fin m) : K →L[ℂ] K :=
  P.phase fun ka => decide (j ka.1 = ka.2)

/-- `O_j = 1 - 2 Σ_k P (k, j k)`. -/
theorem oneHotOracle_eq (P : ProjFamily K (Fin n × Fin m)) (j : Fin n → Fin m) :
    oneHotOracle P j = 1 - (2 : ℂ) • ∑ k, P.proj (k, j k) := by
  unfold oneHotOracle ProjFamily.phase
  congr 2
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [decide_eq_true_eq]
  rw [Finset.sum_ite_eq]
  simp

theorem isUnitary_oneHotOracle (P : ProjFamily K (Fin n × Fin m)) (j : Fin n → Fin m) :
    IsUnitary (oneHotOracle P j) :=
  P.isUnitary_phase _

theorem star_oneHotOracle (P : ProjFamily K (Fin n × Fin m)) (j : Fin n → Fin m) :
    star (oneHotOracle P j) = oneHotOracle P j :=
  P.star_phase _

/-- The Boolean oracle of an arbitrary `n`-bit string (used for the search
gadgets of `part:hsl`). -/
def bitOracle (P : ProjFamily K (Fin n)) (x : Fin n → Bool) : K →L[ℂ] K :=
  P.phase x

/-- The hidden parity `σ(j) = (-1)^{j_1 + ⋯ + j_n}` of `qlsl:lem:xor` and
`hsl:lem:search` (lines 5125-5131 and 2143). -/
def parity (j : Fin n → Fin m) : ℝ := (-1) ^ (∑ k, (j k : ℕ))

theorem parity_eq_prod (j : Fin n → Fin m) : parity j = ∏ k, (-1 : ℝ) ^ (j k : ℕ) :=
  (Finset.prod_pow_eq_pow_sum _ _ _).symm

theorem abs_parity (j : Fin n → Fin m) : |parity j| = 1 := by
  simp [parity]

end

end SparseLowerBounds
end
