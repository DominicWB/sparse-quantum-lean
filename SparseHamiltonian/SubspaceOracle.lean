import SparseHamiltonian.ReuseSchedule

/-!
# Uniform programs embedded in a fixed subspace

An oracle can be extended to a larger Hilbert space by acting as identity on
the orthogonal complement of a fixed isometric embedding. A syntactic compiler
preserves exact evaluation and query count relative to this extended oracle
interface. No equivalence with a primitive sparse oracle is assumed.
-/

namespace SparseHamiltonian.SubspaceOracle

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Apply `U` on the embedded subspace and identity on its complement. -/
def lift (E : P →L[ℂ] K) (U : P →L[ℂ] P) : K →L[ℂ] K :=
  1 + E ∘L (U - 1) ∘L E†

/-- Extending an identity operation gives identity on the whole workspace. -/
theorem lift_one (E : P →L[ℂ] K) : lift E 1 = 1 := by
  simp [lift]

/-- The extension preserves multiplication for an isometric embedding. -/
theorem lift_mul (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (U W : P →L[ℂ] P) : lift E (U * W) = lift E U * lift E W := by
  have hEv (v : P) : (E†) (E v) = v := by
    have h := congrArg (fun A : P →L[ℂ] P => A v) hE
    simpa only [comp_apply, one_def, id_apply] using h
  change lift E (U ∘L W) = lift E U ∘L lift E W
  ext x
  simp only [lift, comp_apply, add_apply, sub_apply, one_def, id_apply,
    map_add, map_sub, hEv]
  abel

/-- Extension commutes with Hilbert adjoints. -/
theorem lift_adjoint (E : P →L[ℂ] K) (U : P →L[ℂ] P) :
    (lift E U)† = lift E (U†) := by
  simp [lift, adjoint_comp, comp_assoc]

/-- A two-sided unitary extends to a two-sided unitary on the full space. -/
theorem lift_unitary (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (U : P →L[ℂ] P) (hU : IsUnitary U) : IsUnitary (lift E U) := by
  have hLeft : U† * U = 1 := hU.1
  have hRight : U * U† = 1 := hU.2
  constructor
  · change (lift E U)† * lift E U = 1
    rw [lift_adjoint, ← lift_mul E hE, hLeft, lift_one]
  · change lift E U * (lift E U)† = 1
    rw [lift_adjoint, ← lift_mul E hE, hRight, lift_one]

/-- A fixed unitary routing operation conjugates the embedded subspace. -/
theorem lift_conjugate (E : P →L[ℂ] K) (R : K →L[ℂ] K)
    (hR : IsUnitary R) (U : P →L[ℂ] P) :
    lift (R ∘L E) U = R * lift E U * star R := by
  have hRv (x : K) : R ((R†) x) = x := by
    have h := congrArg (fun A : K →L[ℂ] K => A x) hR.2
    exact h
  change lift (R ∘L E) U = R ∘L lift E U ∘L R†
  ext x
  simp only [lift, comp_apply, adjoint_comp, add_apply, sub_apply, one_def,
    id_apply, map_add, hRv]

variable {X : Type*} {O : X → P →L[ℂ] P}

/-- Lift a uniform program, including its fixed gates, into the fixed subspace.
Each original query becomes one query to the explicitly extended interface. -/
def liftProgram (E : P →L[ℂ] K) (hE : E† ∘L E = 1) :
    Program O → Program (fun x => lift E (O x))
  | .fixed U hU => .fixed _ (lift_unitary E hE U hU)
  | .query => .query
  | .queryAdjoint => .queryAdjoint
  | .seq p q => .seq (liftProgram E hE p) (liftProgram E hE q)

/-- The subspace compiler preserves exact query count. -/
theorem liftProgram_count (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (p : Program O) : (liftProgram E hE p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => rfl
  | seq p q hp hq => simp only [liftProgram, Program.count_seq, hp, hq]

/-- The compiled program evaluates to the subspace extension of the original
evaluation, uniformly over the unknown oracle input. -/
theorem liftProgram_eval (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (p : Program O) (x : X) :
    (liftProgram E hE p).eval x = lift E (p.eval x) := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => exact lift_adjoint E _
  | seq p q hp hq =>
      simp only [liftProgram, Program.eval_seq, hp, hq]
      exact (lift_mul E hE _ _).symm

/-- Uniform implementation certificates lift at unchanged cost relative to
the subspace-extended oracle. -/
theorem lift_implements {F : X → P →L[ℂ] P} {q : ℕ}
    (h : Implements O F q) (E : P →L[ℂ] K) (hE : E† ∘L E = 1) :
    Implements (fun x => lift E (O x)) (fun x => lift E (F x)) q := by
  obtain ⟨p, hp, hq⟩ := h
  refine ⟨liftProgram E hE p, ?_, ?_⟩
  · intro x
    rw [liftProgram_eval, hp]
  · simpa only [liftProgram_count] using hq

/-- Fixed routing uses the same reference oracle interface: a different
embedded subspace does not require granting a different query primitive. -/
theorem routed_lift_implements {F : X → P →L[ℂ] P} {q : ℕ}
    (h : Implements O F q) (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (R : K →L[ℂ] K) (hR : IsUnitary R) :
    Implements (fun x => lift E (O x)) (fun x => lift (R ∘L E) (F x)) q := by
  have hLeft := Implements.fixed (O := fun x => lift E (O x)) R hR
  have hRight := Implements.fixed (O := fun x => lift E (O x)) (star R) hR.adjoint
  have hProduct := ((hLeft.mul (lift_implements h E hE)).mul hRight).congr
    (fun x => (lift_conjugate E R hR (F x)).symm)
  simpa only [Nat.zero_add, Nat.add_zero] using hProduct

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace K] in
/-- The coordinate interaction is exactly the subspace lift of its local
two-register block, with an embedding independent of all four blocks. -/
theorem slotInteraction_eq_lift (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) {n : ℕ} (r : Fin n) :
    ReuseSchedule.slotInteraction A B C D r =
      lift (ReuseSchedule.slotEmbedding r) (GlobalColligation.blockMap D C B A) :=
  ReuseSchedule.slotInteraction_eq_lift A B C D r

omit [CompleteSpace K] in
/-- A genuine local block implementation compiles into a slot interaction at
the same cost, relative to the explicitly subspace-extended oracle. -/
theorem slotInteraction_implements
    (O : X → WithLp 2 (V × P) →L[ℂ] WithLp 2 (V × P))
    (A : X → P →L[ℂ] P) (B : X → V →L[ℂ] P)
    (C : X → P →L[ℂ] V) (D : X → V →L[ℂ] V) {q n : ℕ}
    (h : Implements O (fun x => GlobalColligation.blockMap (D x) (C x) (B x) (A x)) q)
    (r : Fin n) :
    Implements (fun x => lift (ReuseSchedule.slotEmbedding r) (O x))
      (fun x => ReuseSchedule.slotInteraction (A x) (B x) (C x) (D x) r) q := by
  exact (lift_implements h (ReuseSchedule.slotEmbedding r)
    (ReuseSchedule.slotEmbedding_adjoint_comp r)).congr
      (fun x => (slotInteraction_eq_lift (A x) (B x) (C x) (D x) r).symm)

end
end SparseHamiltonian.SubspaceOracle
