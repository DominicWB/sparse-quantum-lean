import SparseHamiltonian.GeneralLookupSimulation

/-!
# Uniform programs with several explicitly named oracles

All oracle families act on one Hilbert workspace. A query carries one fixed
label from the syntax; there is no coherent selection of labels and no
controlled-oracle primitive. The model allows inverse queries and counts them
at the same cost as forward queries. Labels may form any type, in particular a
finite type. Weighted cost keeps different implementations of the named
oracles visible when a program is compiled to one base oracle.
-/

namespace SparseHamiltonian.MultiOracleCircuit

noncomputable section

open OracleCircuit

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X L : Type*}

/-- A fixed gate is independent of both the unknown input and the query label.
Each query instruction names one oracle; it does not supply coherent SELECT. -/
inductive Program (O : L → X → K →L[ℂ] K) where
  | fixed (U : K →L[ℂ] K) (unitary : IsUnitary U)
  | query (label : L)
  | queryAdjoint (label : L)
  | seq (p q : Program O)

namespace Program

variable {O : L → X → K →L[ℂ] K}

/-- `seq p q` executes `q` first, following operator multiplication. -/
def eval : Program O → X → K →L[ℂ] K
  | .fixed U _, _ => U
  | .query l, x => O l x
  | .queryAdjoint l, x => star (O l x)
  | .seq p q, x => eval p x * eval q x

/-- Total number of queries, including inverse queries. -/
def count : Program O → ℕ
  | .fixed _ _ => 0
  | .query _ => 1
  | .queryAdjoint _ => 1
  | .seq p q => count p + count q

/-- Exact additive query cost for an assigned cost of each named oracle. -/
def cost : Program O → (L → ℕ) → ℕ
  | .fixed _ _, _ => 0
  | .query l, w => w l
  | .queryAdjoint l, w => w l
  | .seq p q, w => cost p w + cost q w

/-- Number of occurrences of one oracle label, in either direction. -/
def labelCount [DecidableEq L] (p : Program O) (l : L) : ℕ :=
  p.cost (fun k => if k = l then 1 else 0)

@[simp] theorem eval_fixed (U : K →L[ℂ] K) (hU : IsUnitary U) (x : X) :
    eval (.fixed U hU : Program O) x = U := rfl
@[simp] theorem eval_query (l : L) (x : X) :
    eval (.query l : Program O) x = O l x := rfl
@[simp] theorem eval_queryAdjoint (l : L) (x : X) :
    eval (.queryAdjoint l : Program O) x = star (O l x) := rfl
@[simp] theorem eval_seq (p q : Program O) (x : X) :
    eval (.seq p q) x = eval p x * eval q x := rfl
@[simp] theorem count_fixed (U : K →L[ℂ] K) (hU : IsUnitary U) :
    count (.fixed U hU : Program O) = 0 := rfl
@[simp] theorem count_query (l : L) : count (.query l : Program O) = 1 := rfl
@[simp] theorem count_queryAdjoint (l : L) : count (.queryAdjoint l : Program O) = 1 := rfl
@[simp] theorem count_seq (p q : Program O) : count (.seq p q) = count p + count q := rfl
@[simp] theorem cost_fixed (U : K →L[ℂ] K) (hU : IsUnitary U) (w : L → ℕ) :
    cost (.fixed U hU : Program O) w = 0 := rfl
@[simp] theorem cost_query (l : L) (w : L → ℕ) :
    cost (.query l : Program O) w = w l := rfl
@[simp] theorem cost_queryAdjoint (l : L) (w : L → ℕ) :
    cost (.queryAdjoint l : Program O) w = w l := rfl
@[simp] theorem cost_seq (p q : Program O) (w : L → ℕ) :
    cost (.seq p q) w = cost p w + cost q w := rfl

@[simp] theorem cost_const (p : Program O) (q : ℕ) :
    p.cost (fun _ => q) = p.count * q := by
  induction p with
  | fixed U hU => simp
  | query l => simp
  | queryAdjoint l => simp
  | seq p t hp ht => simp only [cost_seq, count_seq, hp, ht, Nat.add_mul]

/-- Increasing any oracle's assigned cost can only increase program cost. -/
theorem cost_mono (p : Program O) {w v : L → ℕ} (h : ∀ l, w l ≤ v l) :
    p.cost w ≤ p.cost v := by
  induction p with
  | fixed U hU => exact le_rfl
  | query l => exact h l
  | queryAdjoint l => exact h l
  | seq p q hp hq => exact Nat.add_le_add hp hq

@[simp] theorem labelCount_fixed [DecidableEq L] (U : K →L[ℂ] K)
    (hU : IsUnitary U) (l : L) :
    labelCount (.fixed U hU : Program O) l = 0 := rfl
@[simp] theorem labelCount_query [DecidableEq L] (k l : L) :
    labelCount (.query k : Program O) l = if k = l then 1 else 0 := rfl
@[simp] theorem labelCount_queryAdjoint [DecidableEq L] (k l : L) :
    labelCount (.queryAdjoint k : Program O) l = if k = l then 1 else 0 := rfl
@[simp] theorem labelCount_seq [DecidableEq L] (p q : Program O) (l : L) :
    labelCount (.seq p q) l = labelCount p l + labelCount q l := rfl

/-- On a finite label set, cost is exactly the sum of the separately counted
queries times their assigned costs. -/
theorem cost_eq_sum_labelCount [Fintype L] [DecidableEq L]
    (p : Program O) (w : L → ℕ) :
    p.cost w = ∑ l, p.labelCount l * w l := by
  induction p with
  | fixed U hU => simp
  | query l => simp
  | queryAdjoint l => simp
  | seq p q hp hq =>
      simp only [cost_seq, labelCount_seq, Nat.add_mul, Finset.sum_add_distrib, hp, hq]

theorem count_eq_sum_labelCount [Fintype L] [DecidableEq L] (p : Program O) :
    p.count = ∑ l, p.labelCount l := by
  simpa using p.cost_eq_sum_labelCount (fun _ => 1)

theorem eval_unitary (p : Program O) (hO : ∀ l x, IsUnitary (O l x)) (x : X) :
    IsUnitary (p.eval x) := by
  induction p with
  | fixed U hU => exact hU
  | query l => exact hO l x
  | queryAdjoint l => exact (hO l x).adjoint
  | seq p q hp hq => exact hp.mul hq

def identity : Program O := .fixed 1 isUnitary_one

@[simp] theorem eval_identity (x : X) : eval (identity : Program O) x = 1 := rfl
@[simp] theorem count_identity : count (identity : Program O) = 0 := rfl
@[simp] theorem cost_identity (w : L → ℕ) : cost (identity : Program O) w = 0 := rfl

/-- Reverse the program and exchange forward and inverse calls. -/
def adjoint : Program O → Program O
  | .fixed U hU => .fixed (star U) hU.adjoint
  | .query l => .queryAdjoint l
  | .queryAdjoint l => .query l
  | .seq p q => .seq (adjoint q) (adjoint p)

@[simp] theorem eval_adjoint (p : Program O) (x : X) :
    p.adjoint.eval x = star (p.eval x) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => simp [adjoint]
  | seq p q hp hq => simp only [adjoint, eval_seq, hp, hq, star_mul]

@[simp] theorem count_adjoint (p : Program O) : p.adjoint.count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [adjoint, count_seq, hp, hq, Nat.add_comm]

@[simp] theorem cost_adjoint (p : Program O) (w : L → ℕ) :
    p.adjoint.cost w = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [adjoint, cost_seq, hp, hq, Nat.add_comm]

@[simp] theorem labelCount_adjoint [DecidableEq L] (p : Program O) (l : L) :
    p.adjoint.labelCount l = p.labelCount l := p.cost_adjoint _

/-- Embed a single-oracle program by giving every query its explicit label. -/
def embed (l : L) : OracleCircuit.Program (O l) → Program O
  | .fixed U hU => .fixed U hU
  | .query => .query l
  | .queryAdjoint => .queryAdjoint l
  | .seq p q => .seq (embed l p) (embed l q)

@[simp] theorem eval_embed (l : L) (p : OracleCircuit.Program (O l)) (x : X) :
    (embed l p).eval x = p.eval x := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => rfl
  | seq p q hp hq => simp only [embed, eval_seq, OracleCircuit.Program.eval_seq, hp, hq]

@[simp] theorem count_embed (l : L) (p : OracleCircuit.Program (O l)) :
    (embed l p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => rfl
  | seq p q hp hq => simp only [embed, count_seq, OracleCircuit.Program.count_seq, hp, hq]

@[simp] theorem cost_embed (l : L) (p : OracleCircuit.Program (O l)) (w : L → ℕ) :
    (embed l p).cost w = p.count * w l := by
  induction p with
  | fixed U hU => simp [embed]
  | query => simp [embed]
  | queryAdjoint => simp [embed]
  | seq p q hp hq =>
      simp only [embed, cost_seq, OracleCircuit.Program.count_seq, hp, hq, Nat.add_mul]

/-- Rename the explicit query labels into a common oracle vocabulary.
The source family is exactly the restriction along the supplied label map. -/
def relabel {M : Type*} {F : M → X → K →L[ℂ] K} (r : L → M) :
    Program (fun l => F (r l)) → Program F
  | .fixed U hU => .fixed U hU
  | .query l => .query (r l)
  | .queryAdjoint l => .queryAdjoint (r l)
  | .seq p q => .seq (relabel r p) (relabel r q)

@[simp] theorem eval_relabel {M : Type*} {F : M → X → K →L[ℂ] K}
    (r : L → M) (p : Program (fun l => F (r l))) (x : X) :
    (relabel r p).eval x = p.eval x := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [relabel, eval_seq, hp, hq]

@[simp] theorem count_relabel {M : Type*} {F : M → X → K →L[ℂ] K}
    (r : L → M) (p : Program (fun l => F (r l))) :
    (relabel r p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [relabel, count_seq, hp, hq]

@[simp] theorem cost_relabel {M : Type*} {F : M → X → K →L[ℂ] K}
    (r : L → M) (p : Program (fun l => F (r l))) (w : M → ℕ) :
    (relabel r p).cost w = p.cost (fun l => w (r l)) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [relabel, cost_seq, hp, hq]

/-- Replace each named oracle by a program over another named oracle family.
This is syntactic substitution: inverse queries use the adjoint of the supplied
program, and every call in that program remains visible to the target counter. -/
def substitute {M : Type*} {Q : M → X → K →L[ℂ] K} :
    Program O → (L → Program Q) → Program Q
  | .fixed U hU, _ => .fixed U hU
  | .query l, circuits => circuits l
  | .queryAdjoint l, circuits => (circuits l).adjoint
  | .seq p q, circuits => .seq (substitute p circuits) (substitute q circuits)

/-- Substitution counts exactly all target-oracle calls that it inserts. -/
@[simp] theorem count_substitute {M : Type*} {Q : M → X → K →L[ℂ] K}
    (p : Program O) (circuits : L → Program Q) :
    (p.substitute circuits).count = p.cost (fun l => (circuits l).count) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => exact count_adjoint _
  | seq p q hp hq => simp only [substitute, count_seq, cost_seq, hp, hq]

/-- Every target label's assigned cost is retained through substitution. -/
@[simp] theorem cost_substitute {M : Type*} {Q : M → X → K →L[ℂ] K}
    (p : Program O) (circuits : L → Program Q) (w : M → ℕ) :
    (p.substitute circuits).cost w = p.cost (fun l => (circuits l).cost w) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => exact cost_adjoint _ _
  | seq p q hp hq => simp only [substitute, cost_seq, hp, hq]

/-- Per-label exact implementations give exact semantics after substitution. -/
theorem eval_substitute {M : Type*} {Q : M → X → K →L[ℂ] K}
    (p : Program O) (circuits : L → Program Q)
    (h : ∀ l x, (circuits l).eval x = O l x) (x : X) :
    (p.substitute circuits).eval x = p.eval x := by
  induction p with
  | fixed U hU => rfl
  | query l => exact h l x
  | queryAdjoint l => simp only [substitute, eval_adjoint, h, eval_queryAdjoint]
  | seq p q hp hq => simp only [substitute, eval_seq, hp, hq]

/-- Compile each labeled query into an actual program over a common base
oracle. Inverse queries use the syntactic adjoint of that implementation. -/
def compile {Q : X → K →L[ℂ] K} :
    Program O → (L → OracleCircuit.Program Q) → OracleCircuit.Program Q
  | .fixed U hU, _ => .fixed U hU
  | .query l, circuits => circuits l
  | .queryAdjoint l, circuits => (circuits l).adjoint
  | .seq p q, circuits => .seq (compile p circuits) (compile q circuits)

/-- Compilation has exactly the sum of the costs of the inserted programs. -/
@[simp] theorem count_compile {Q : X → K →L[ℂ] K}
    (p : Program O) (circuits : L → OracleCircuit.Program Q) :
    (p.compile circuits).count = p.cost (fun l => (circuits l).count) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => exact OracleCircuit.Program.count_adjoint _
  | seq p q hp hq =>
      simp only [compile, OracleCircuit.Program.count_seq, cost_seq, hp, hq]

theorem eval_compile {Q : X → K →L[ℂ] K}
    (p : Program O) (circuits : L → OracleCircuit.Program Q)
    (h : ∀ l x, (circuits l).eval x = O l x) (x : X) :
    (p.compile circuits).eval x = p.eval x := by
  induction p with
  | fixed U hU => rfl
  | query l => exact h l x
  | queryAdjoint l =>
      simp only [compile, OracleCircuit.Program.eval_adjoint, h, eval_queryAdjoint]
  | seq p q hp hq =>
      simp only [compile, OracleCircuit.Program.eval_seq, eval_seq, hp, hq]

/-- Each separately supplied implementation contributes its advertised cost
every time its label occurs. No combined oracle is assumed. -/
theorem implements_compile {Q : X → K →L[ℂ] K}
    (p : Program O) (w : L → ℕ)
    (h : ∀ l, OracleCircuit.Implements Q (O l) (w l)) :
    OracleCircuit.Implements Q p.eval (p.cost w) := by
  classical
  choose circuits heval hcount using h
  exact ⟨p.compile circuits, p.eval_compile circuits heval,
    by rw [count_compile]; exact p.cost_mono hcount⟩

/-- A common per-query implementation budget multiplies the explicit number
of source queries. -/
theorem implements_compile_uniform {Q : X → K →L[ℂ] K}
    (p : Program O) (q : ℕ)
    (h : ∀ l, OracleCircuit.Implements Q (O l) q) :
    OracleCircuit.Implements Q p.eval (p.count * q) := by
  simpa using p.implements_compile (fun _ => q) h

/-- A zero-query program cannot depend on the unknown input. -/
theorem eval_eq_of_count_zero (p : Program O) (h : p.count = 0) (x y : X) :
    p.eval x = p.eval y := by
  induction p with
  | fixed U hU => rfl
  | query l => simp at h
  | queryAdjoint l => simp at h
  | seq p q hp hq =>
      have hh : p.count = 0 ∧ q.count = 0 := Nat.add_eq_zero_iff.mp h
      simp only [eval_seq, hp hh.1, hq hh.2]

theorem eval_eq_of_oracle_eq (p : Program O) {x y : X}
    (h : ∀ l, O l x = O l y) : p.eval x = p.eval y := by
  induction p with
  | fixed U hU => rfl
  | query l => exact h l
  | queryAdjoint l => exact congrArg star (h l)
  | seq p q hp hq => simp only [eval_seq, hp, hq]

end Program

/-- An exact, input-uniform implementation with a total query budget. -/
def Implements (O : L → X → K →L[ℂ] K) (F : X → K →L[ℂ] K) (q : ℕ) : Prop :=
  ∃ p : Program O, (∀ x, p.eval x = F x) ∧ p.count ≤ q

namespace Implements

variable {O : L → X → K →L[ℂ] K} {F G : X → K →L[ℂ] K} {q r : ℕ}

theorem fixed (U : K →L[ℂ] K) (hU : IsUnitary U) :
    Implements O (fun _ => U) 0 := ⟨.fixed U hU, fun _ => rfl, le_rfl⟩

theorem identity : Implements O (fun _ => 1) 0 := fixed 1 isUnitary_one

theorem query (l : L) : Implements O (O l) 1 := ⟨.query l, fun _ => rfl, le_rfl⟩

theorem queryAdjoint (l : L) : Implements O (fun x => star (O l x)) 1 :=
  ⟨.queryAdjoint l, fun _ => rfl, le_rfl⟩

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

theorem embed (l : L) (h : OracleCircuit.Implements (O l) F q) : Implements O F q := by
  obtain ⟨p, hp, hq⟩ := h
  exact ⟨Program.embed l p, fun x => by simpa using hp x,
    by simpa using hq⟩

theorem unitary (h : Implements O F q) (hO : ∀ l x, IsUnitary (O l x)) (x : X) :
    IsUnitary (F x) := by
  obtain ⟨p, hp, _⟩ := h
  rw [← hp x]
  exact p.eval_unitary hO x

theorem independent_of_zero (h : Implements O F 0) (x y : X) : F x = F y := by
  obtain ⟨p, hp, hq⟩ := h
  rw [← hp x, ← hp y]
  exact p.eval_eq_of_count_zero (Nat.eq_zero_of_le_zero hq) x y

/-- Compile a total-budget implementation using separate exact implementations
of every named oracle, each with the stated common base-oracle cost. -/
theorem compile {Q : X → K →L[ℂ] K} (hF : Implements O F r)
    (hO : ∀ l, OracleCircuit.Implements Q (O l) q) :
    OracleCircuit.Implements Q F (r * q) := by
  obtain ⟨p, hp, hr⟩ := hF
  exact ((p.implements_compile_uniform q hO).congr hp).mono (Nat.mul_le_mul_right q hr)

end Implements

end

end SparseHamiltonian.MultiOracleCircuit
