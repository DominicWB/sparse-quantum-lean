import SparseHamiltonian.ChronologicalClockFactorization

/-!
# Uniform oracle programs

A program has fixed unitary gates and calls to a supplied oracle or its adjoint.
In particular a free gate is a single operator, not an input-dependent family.
The model grants inverse queries, but grants no controlled-query or direct-sum
query primitive. Such access must be supplied by a separate implementation.
-/

namespace SparseHamiltonian.OracleCircuit

noncomputable section

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X : Type*}

/-- Both unitary identities, including surjectivity in infinite dimension. -/
def IsUnitary (U : K →L[ℂ] K) : Prop := star U * U = 1 ∧ U * star U = 1

@[simp] theorem isUnitary_one : IsUnitary (1 : K →L[ℂ] K) := by
  constructor <;> simp

theorem IsUnitary.adjoint {U : K →L[ℂ] K} (h : IsUnitary U) : IsUnitary (star U) := by
  simpa only [IsUnitary, star_star] using And.intro h.2 h.1

theorem IsUnitary.mul {U V : K →L[ℂ] K} (hU : IsUnitary U) (hV : IsUnitary V) :
    IsUnitary (U * V) := by
  constructor
  · calc
      star (U * V) * (U * V) = star V * (star U * U) * V := by
        simp only [star_mul, mul_assoc]
      _ = 1 := by rw [hU.1, mul_one, hV.1]
  · calc
      (U * V) * star (U * V) = U * (V * star V) * star U := by
        simp only [star_mul, mul_assoc]
      _ = 1 := by rw [hV.2, mul_one, hU.2]

/-- Syntactic programs over one oracle family on a fixed Hilbert workspace.
The argument of `fixed` is independent of the oracle input. -/
inductive Program (O : X → K →L[ℂ] K) where
  | fixed (U : K →L[ℂ] K) (unitary : IsUnitary U)
  | query
  | queryAdjoint
  | seq (p q : Program O)

namespace Program

variable {O : X → K →L[ℂ] K}

/-- Operators multiply in their usual order: `seq p q` executes `q` first. -/
def eval : Program O → X → K →L[ℂ] K
  | .fixed U _, _ => U
  | .query, x => O x
  | .queryAdjoint, x => star (O x)
  | .seq p q, x => eval p x * eval q x

/-- Number of oracle or inverse-oracle calls. -/
def count : Program O → ℕ
  | .fixed _ _ => 0
  | .query => 1
  | .queryAdjoint => 1
  | .seq p q => count p + count q

@[simp] theorem eval_fixed (U : K →L[ℂ] K) (hU : IsUnitary U) (x : X) :
    eval (.fixed U hU : Program O) x = U := rfl
@[simp] theorem eval_query (x : X) : eval (.query : Program O) x = O x := rfl
@[simp] theorem eval_queryAdjoint (x : X) :
    eval (.queryAdjoint : Program O) x = star (O x) := rfl
@[simp] theorem eval_seq (p q : Program O) (x : X) :
    eval (.seq p q) x = eval p x * eval q x := rfl
@[simp] theorem count_fixed (U : K →L[ℂ] K) (hU : IsUnitary U) :
    count (.fixed U hU : Program O) = 0 := rfl
@[simp] theorem count_query : count (.query : Program O) = 1 := rfl
@[simp] theorem count_queryAdjoint : count (.queryAdjoint : Program O) = 1 := rfl
@[simp] theorem count_seq (p q : Program O) : count (.seq p q) = count p + count q := rfl

/-- Every evaluation is unitary when every oracle is unitary. -/
theorem eval_unitary (p : Program O) (hO : ∀ x, IsUnitary (O x)) (x : X) :
    IsUnitary (p.eval x) := by
  induction p with
  | fixed U hU => exact hU
  | query => exact hO x
  | queryAdjoint => exact (hO x).adjoint
  | seq p q hp hq => exact hp.mul hq

/-- Empty computation. -/
def identity : Program O := .fixed 1 isUnitary_one

@[simp] theorem eval_identity (x : X) : eval (identity : Program O) x = 1 := rfl
@[simp] theorem count_identity : count (identity : Program O) = 0 := rfl

/-- Reversing a circuit exchanges oracle calls with their adjoints. -/
def adjoint : Program O → Program O
  | .fixed U hU => .fixed (star U) hU.adjoint
  | .query => .queryAdjoint
  | .queryAdjoint => .query
  | .seq p q => .seq (adjoint q) (adjoint p)

@[simp] theorem eval_adjoint (p : Program O) (x : X) :
    p.adjoint.eval x = star (p.eval x) := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => simp [adjoint]
  | seq p q hp hq => simp only [adjoint, eval_seq, hp, hq, star_mul]

@[simp] theorem count_adjoint (p : Program O) : p.adjoint.count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => rfl
  | seq p q hp hq => simp only [adjoint, count_seq, hp, hq, Nat.add_comm]

/-- Repetition without adding any further oracle primitive. -/
def pow (p : Program O) : ℕ → Program O
  | 0 => identity
  | n + 1 => .seq (pow p n) p

@[simp] theorem eval_pow (p : Program O) (n : ℕ) (x : X) :
    (p.pow n).eval x = p.eval x ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n hn => simp only [pow, eval_seq, hn, pow_succ]

@[simp] theorem count_pow (p : Program O) (n : ℕ) :
    (p.pow n).count = n * p.count := by
  induction n with
  | zero => simp [pow]
  | succ n hn => simp only [pow, count_seq, hn, Nat.succ_mul]

/-- A zero-query program cannot acquire dependence on the unknown input. -/
theorem eval_eq_of_count_zero (p : Program O) (h : p.count = 0) (x y : X) :
    p.eval x = p.eval y := by
  induction p with
  | fixed U hU => rfl
  | query => simp at h
  | queryAdjoint => simp at h
  | seq p q hp hq =>
      have hh : p.count = 0 ∧ q.count = 0 := Nat.add_eq_zero_iff.mp h
      simp only [eval_seq, hp hh.1, hq hh.2]

/-- Replace each oracle letter by an implementing circuit, and each inverse
letter by its adjoint. This is a genuine compilation, not a new primitive. -/
def substitute {F : X → K →L[ℂ] K} : Program F → Program O → Program O
  | .fixed U hU, _ => .fixed U hU
  | .query, q => q
  | .queryAdjoint, q => q.adjoint
  | .seq p t, q => .seq (substitute p q) (substitute t q)

@[simp] theorem count_substitute {F : X → K →L[ℂ] K}
    (p : Program F) (q : Program O) :
    (p.substitute q).count = p.count * q.count := by
  induction p with
  | fixed U hU => simp [substitute]
  | query => simp [substitute]
  | queryAdjoint => simp [substitute]
  | seq p t hp ht => simp only [substitute, count_seq, hp, ht, Nat.add_mul]

theorem eval_substitute {F : X → K →L[ℂ] K}
    (p : Program F) (q : Program O) (hq : ∀ x, q.eval x = F x) (x : X) :
    (p.substitute q).eval x = p.eval x := by
  induction p with
  | fixed U hU => rfl
  | query => exact hq x
  | queryAdjoint => simp only [substitute, eval_adjoint, hq, eval_queryAdjoint]
  | seq p t hp ht => simp only [substitute, eval_seq, hp, ht]

/-- Evaluation sees the unknown input only through the oracle operator. -/
theorem eval_eq_of_oracle_eq (p : Program O) {x y : X} (h : O x = O y) :
    p.eval x = p.eval y := by
  induction p with
  | fixed U hU => rfl
  | query => exact h
  | queryAdjoint => exact congrArg star h
  | seq p q hp hq => simp only [eval_seq, hp, hq]

end Program

/-- An exact, uniform implementation with at most `q` oracle calls. -/
def Implements (O F : X → K →L[ℂ] K) (q : ℕ) : Prop :=
  ∃ p : Program O, (∀ x, p.eval x = F x) ∧ p.count ≤ q

namespace Implements

variable {O F G : X → K →L[ℂ] K} {q r : ℕ}

/-- A fixed unitary family is free. -/
theorem fixed (U : K →L[ℂ] K) (hU : IsUnitary U) :
    Implements O (fun _ => U) 0 := ⟨.fixed U hU, fun _ => rfl, le_rfl⟩

theorem identity : Implements O (fun _ => 1) 0 := fixed 1 isUnitary_one

theorem query : Implements O O 1 := ⟨.query, fun _ => rfl, le_rfl⟩

theorem queryAdjoint : Implements O (fun x => star (O x)) 1 :=
  ⟨.queryAdjoint, fun _ => rfl, le_rfl⟩

theorem mono (h : Implements O F q) (hqr : q ≤ r) : Implements O F r := by
  obtain ⟨p, hp, hq⟩ := h
  exact ⟨p, hp, hq.trans hqr⟩

theorem congr (h : Implements O F q) (hFG : ∀ x, F x = G x) : Implements O G q := by
  obtain ⟨p, hp, hq⟩ := h
  exact ⟨p, fun x => (hp x).trans (hFG x), hq⟩

theorem adjoint (h : Implements O F q) : Implements O (fun x => star (F x)) q := by
  obtain ⟨p, hp, hq⟩ := h
  exact ⟨p.adjoint, fun x => by simp only [Program.eval_adjoint, hp],
    by simpa only [Program.count_adjoint] using hq⟩

theorem mul (hF : Implements O F q) (hG : Implements O G r) :
    Implements O (fun x => F x * G x) (q + r) := by
  obtain ⟨p, hp, hq⟩ := hF
  obtain ⟨t, ht, hr⟩ := hG
  exact ⟨.seq p t, fun x => by simp only [Program.eval_seq, hp, ht],
    Nat.add_le_add hq hr⟩

theorem pow (h : Implements O F q) (n : ℕ) :
    Implements O (fun x => F x ^ n) (n * q) := by
  obtain ⟨p, hp, hq⟩ := h
  exact ⟨p.pow n, fun x => by simp only [Program.eval_pow, hp],
    by simpa only [Program.count_pow] using Nat.mul_le_mul_left n hq⟩

theorem unitary (h : Implements O F q) (hO : ∀ x, IsUnitary (O x)) (x : X) :
    IsUnitary (F x) := by
  obtain ⟨p, hp, _⟩ := h
  rw [← hp x]
  exact p.eval_unitary hO x

/-- This rules out counting a general unknown input-dependent gate as free. -/
theorem independent_of_zero (h : Implements O F 0) (x y : X) : F x = F y := by
  obtain ⟨p, hp, hq⟩ := h
  rw [← hp x, ← hp y]
  exact p.eval_eq_of_count_zero (Nat.eq_zero_of_le_zero hq) x y

/-- Uniform circuit compilation multiplies, rather than hides, the cost of
an implemented oracle. The outer implementation is expressed in calls to `F`. -/
theorem trans (hF : Implements O F q) (hG : Implements F G r) :
    Implements O G (r * q) := by
  obtain ⟨p, hp, hq⟩ := hF
  obtain ⟨t, ht, hr⟩ := hG
  refine ⟨t.substitute p, fun x => (t.eval_substitute p hp x).trans (ht x), ?_⟩
  simpa only [Program.count_substitute] using Nat.mul_le_mul hr hq

end Implements

end

end SparseHamiltonian.OracleCircuit
