import SparseHamiltonian.ActiveClockQuery

/-!
# Oracle programs on an encoded subspace

The logical and physical Hilbert spaces may differ. A physical circuit need
only act correctly on the image of a fixed isometric encoding. Its action on
the orthogonal complement is unrestricted. The encoding is independent of the
unknown oracle input; its preparation cost is not granted by this interface.
-/

namespace SparseHamiltonian.EncodedOracle

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X : Type*}

/-- A uniform physical program implementing a logical family on the image of
one fixed encoding. The isometry property is supplied separately when needed. -/
def ImplementsOn (O : X → K →L[ℂ] K) (F : X → P →L[ℂ] P)
    (E : P →L[ℂ] K) (q : ℕ) : Prop :=
  ∃ p : Program O, (∀ x, p.eval x ∘L E = E ∘L F x) ∧ p.count ≤ q

/-- A subspace lift acts as the logical gate on encoded vectors. -/
theorem lift_comp (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (U : P →L[ℂ] P) : SubspaceOracle.lift E U ∘L E = E ∘L U := by
  have hEv (v : P) : (E†) (E v) = v := by
    have h := congrArg (fun A : P →L[ℂ] P => A v) hE
    simpa only [comp_apply, one_def, id_apply] using h
  ext v
  simp only [SubspaceOracle.lift, comp_apply, add_apply, one_def, id_apply,
    sub_apply, hEv, map_sub]
  abel

/-- Intertwining unitaries also intertwines their inverses. This uses both
surjectivity of the logical gate and isometry of the physical gate. -/
theorem adjoint_intertwines (U : K →L[ℂ] K) (F : P →L[ℂ] P)
    (E : P →L[ℂ] K) (hU : IsUnitary U) (hF : IsUnitary F)
    (h : U ∘L E = E ∘L F) : star U ∘L E = E ∘L star F := by
  have hUv (v : K) : (star U) (U v) = v := by
    exact congrArg (fun A : K →L[ℂ] K => A v) hU.1
  have hFv (v : P) : F ((star F) v) = v := by
    exact congrArg (fun A : P →L[ℂ] P => A v) hF.2
  have hv (v : P) : U (E v) = E (F v) := by
    exact congrArg (fun A : P →L[ℂ] K => A v) h
  ext v
  change (star U) (E v) = E ((star F) v)
  calc
    (star U) (E v) = (star U) (E (F ((star F) v))) := by rw [hFv]
    _ = (star U) (U (E ((star F) v))) := by rw [hv]
    _ = E ((star F) v) := hUv _

namespace ImplementsOn

variable {O : X → K →L[ℂ] K} {F G : X → P →L[ℂ] P}
  {E : P →L[ℂ] K} {q r : ℕ}

/-- Fixed logical unitaries extend to fixed physical unitaries. -/
theorem fixed (hE : E† ∘L E = 1) (U : P →L[ℂ] P) (hU : IsUnitary U) :
    ImplementsOn O (fun _ => U) E 0 :=
  ⟨.fixed (SubspaceOracle.lift E U) (SubspaceOracle.lift_unitary E hE U hU),
    fun _ => lift_comp E hE U, le_rfl⟩

omit [CompleteSpace P] in
/-- The identity needs no oracle calls, for any fixed encoding. -/
theorem identity : ImplementsOn O (fun _ => 1) E 0 := by
  refine ⟨Program.identity, fun _ => ?_, le_rfl⟩
  simp only [Program.eval_identity, one_def, id_comp, comp_id]

omit [CompleteSpace P] in
/-- The same physical circuit establishes every larger query allowance. -/
theorem mono (h : ImplementsOn O F E q) (hqr : q ≤ r) :
    ImplementsOn O F E r := by
  obtain ⟨p, hp, hq⟩ := h
  exact ⟨p, hp, hq.trans hqr⟩

omit [CompleteSpace P] in
/-- Pointwise equal logical families have the same implementation. -/
theorem congr (h : ImplementsOn O F E q) (hFG : ∀ x, F x = G x) :
    ImplementsOn O G E q := by
  obtain ⟨p, hp, hq⟩ := h
  exact ⟨p, fun x => by rw [← hFG x]; exact hp x, hq⟩

omit [CompleteSpace P] in
/-- Composition does not require control over the complement of the encoding. -/
theorem mul (hF : ImplementsOn O F E q) (hG : ImplementsOn O G E r) :
    ImplementsOn O (fun x => F x * G x) E (q + r) := by
  obtain ⟨p, hp, hq⟩ := hF
  obtain ⟨t, ht, hr⟩ := hG
  refine ⟨.seq p t, fun x => ?_, Nat.add_le_add hq hr⟩
  change (p.eval x ∘L t.eval x) ∘L E = E ∘L (F x ∘L G x)
  rw [comp_assoc, ht, ← comp_assoc, hp, comp_assoc]

/-- The inverse physical program implements the inverse logical action. -/
theorem adjoint (h : ImplementsOn O F E q)
    (hO : ∀ x, IsUnitary (O x)) (hF : ∀ x, IsUnitary (F x)) :
    ImplementsOn O (fun x => star (F x)) E q := by
  obtain ⟨p, hp, hq⟩ := h
  refine ⟨p.adjoint, fun x => ?_, by simpa only [Program.count_adjoint] using hq⟩
  rw [Program.eval_adjoint]
  exact adjoint_intertwines _ _ E (p.eval_unitary hO x) (hF x) (hp x)

omit [CompleteSpace P] in
/-- Repeating an encoded implementation multiplies its query allowance. -/
theorem pow (h : ImplementsOn O F E q) (n : ℕ) :
    ImplementsOn O (fun x => F x ^ n) E (n * q) := by
  induction n with
  | zero => simpa only [pow_zero, Nat.zero_mul] using (identity (O := O) (E := E))
  | succ n hn => simpa only [pow_succ, Nat.succ_mul] using hn.mul h

omit [CompleteSpace P] in
/-- An exact full-space implementation is also an encoded implementation. -/
theorem of_full {G : X → K →L[ℂ] K} (hG : Implements O G q)
    (hGF : ∀ x, G x ∘L E = E ∘L F x) : ImplementsOn O F E q := by
  obtain ⟨p, hp, hq⟩ := hG
  exact ⟨p, fun x => by rw [hp]; exact hGF x, hq⟩

/-- A zero-query implementation cannot encode unknown input dependence. -/
theorem independent_of_zero (h : ImplementsOn O F E 0)
    (hE : E† ∘L E = 1) (x y : X) : F x = F y := by
  obtain ⟨p, hp, hq⟩ := h
  have hh : E ∘L F x = E ∘L F y := by
    rw [← hp x, ← hp y, p.eval_eq_of_count_zero (Nat.eq_zero_of_le_zero hq) x y]
  have hh' := congrArg (fun A => E† ∘L A) hh
  simpa only [← comp_assoc, hE, one_def, id_comp] using hh'

end ImplementsOn

/-- Compile a logical program into the physical workspace. Every fixed gate
is lifted using the same fixed encoding; oracle letters use the supplied
physical program, and inverse letters its syntactic adjoint. -/
def compile {O : X → K →L[ℂ] K} {F : X → P →L[ℂ] P}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1) (p : Program O) :
    Program F → Program O
  | .fixed U hU => .fixed _ (SubspaceOracle.lift_unitary E hE U hU)
  | .query => p
  | .queryAdjoint => p.adjoint
  | .seq a b => .seq (compile E hE p a) (compile E hE p b)

/-- Compiling through an encoded oracle has an exact multiplicative count. -/
theorem compile_count {O : X → K →L[ℂ] K} {F : X → P →L[ℂ] P}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1) (p : Program O) (a : Program F) :
    (compile E hE p a).count = a.count * p.count := by
  induction a with
  | fixed U hU => simp [compile]
  | query => simp [compile]
  | queryAdjoint => simp [compile]
  | seq a b ha hb => simp only [compile, Program.count_seq, ha, hb, Nat.add_mul]

/-- The compiled circuit is correct on the encoded subspace. The physical
oracle need not act as identity on its orthogonal complement. -/
theorem compile_eval {O : X → K →L[ℂ] K} {F : X → P →L[ℂ] P}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1) (p : Program O)
    (hO : ∀ x, IsUnitary (O x)) (hF : ∀ x, IsUnitary (F x))
    (hp : ∀ x, p.eval x ∘L E = E ∘L F x) (a : Program F) (x : X) :
    (compile E hE p a).eval x ∘L E = E ∘L a.eval x := by
  induction a with
  | fixed U hU => exact lift_comp E hE U
  | query => exact hp x
  | queryAdjoint =>
      change p.adjoint.eval x ∘L E = E ∘L star (F x)
      rw [Program.eval_adjoint]
      exact adjoint_intertwines _ _ E (p.eval_unitary hO x) (hF x) (hp x)
  | seq a b ha hb =>
      change ((compile E hE p a).eval x ∘L (compile E hE p b).eval x) ∘L E =
        E ∘L (a.eval x ∘L b.eval x)
      rw [comp_assoc, hb, ← comp_assoc, ha, comp_assoc]

/-- A logical implementation can be compiled through a physical implementation
on a fixed encoded subspace, with all query costs exposed. -/
theorem ImplementsOn.trans {O : X → K →L[ℂ] K} {F G : X → P →L[ℂ] P}
    {E : P →L[ℂ] K} {q r : ℕ} (hE : E† ∘L E = 1)
    (hO : ∀ x, IsUnitary (O x)) (hF : ∀ x, IsUnitary (F x))
    (hFimpl : ImplementsOn O F E q) (hGimpl : Implements F G r) :
    ImplementsOn O G E (r * q) := by
  obtain ⟨p, hp, hq⟩ := hFimpl
  obtain ⟨a, ha, hr⟩ := hGimpl
  refine ⟨compile E hE p a, fun x => ?_, ?_⟩
  · rw [compile_eval E hE p hO hF hp a x, ha]
  · rw [compile_count]
    exact Nat.mul_le_mul hr hq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Successive encodings compose without imposing any action outside their
valid subspaces. Each outer oracle call is replaced by the physical program. -/
theorem ImplementsOn.trans_encoded [CompleteSpace H]
    {O : X → K →L[ℂ] K} {F : X → P →L[ℂ] P} {G : X → H →L[ℂ] H}
    {E : P →L[ℂ] K} {J : H →L[ℂ] P} {q r : ℕ}
    (hE : E† ∘L E = 1) (hO : ∀ x, IsUnitary (O x))
    (hF : ∀ x, IsUnitary (F x))
    (hFimpl : ImplementsOn O F E q) (hGimpl : ImplementsOn F G J r) :
    ImplementsOn O G (E ∘L J) (r * q) := by
  obtain ⟨p, hp, hq⟩ := hFimpl
  obtain ⟨a, ha, hr⟩ := hGimpl
  refine ⟨compile E hE p a, fun x => ?_, ?_⟩
  · rw [← comp_assoc, compile_eval E hE p hO hF hp a x,
      comp_assoc, ha, comp_assoc]
  · rw [compile_count]
    exact Nat.mul_le_mul hr hq

/-- An isometric encoding preserves the operator norm of every output map. -/
theorem norm_comp_eq (E : P →L[ℂ] K) (hE : E† ∘L E = 1) (A : H →L[ℂ] P) :
    ‖E ∘L A‖ = ‖A‖ := by
  have hNorm := E.norm_map_iff_adjoint_comp_self.mpr hE
  apply le_antisymm
  · apply (E ∘L A).opNorm_le_bound (norm_nonneg A)
    intro v
    simpa only [comp_apply, hNorm] using A.le_opNorm v
  · apply A.opNorm_le_bound (norm_nonneg (E ∘L A))
    intro v
    simpa only [comp_apply, hNorm] using (E ∘L A).le_opNorm v

/-- Correct encoded execution preserves the full-output operator error exactly. -/
theorem error_eq (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (U : K →L[ℂ] K) (F : P →L[ℂ] P) (h : U ∘L E = E ∘L F)
    (J T : H →L[ℂ] P) :
    ‖U ∘L (E ∘L J) - E ∘L T‖ = ‖F ∘L J - T‖ := by
  rw [← comp_assoc, h, comp_assoc, ← comp_sub]
  exact norm_comp_eq E hE _

/-- Correctness only on the prepared input already preserves the full-output
error; a full logical unitary intertwining equation is unnecessary here. -/
theorem output_error_eq (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (U : K →L[ℂ] K) (J S T : H →L[ℂ] P)
    (h : U ∘L (E ∘L J) = E ∘L S) :
    ‖U ∘L (E ∘L J) - E ∘L T‖ = ‖S - T‖ := by
  rw [h, ← comp_sub]
  exact norm_comp_eq E hE _

/-- An exact implementation certificate on prepared inputs transfers any
logical error estimate without changing the query allowance. -/
theorem output_error_certificate {O : X → K →L[ℂ] K}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (J S T : X → H →L[ℂ] P) (q : ℕ) (ε : ℝ)
    (h : ∃ p : Program O, p.count ≤ q ∧
      ∀ x, p.eval x ∘L (E ∘L J x) = E ∘L S x)
    (hError : ∀ x, ‖S x - T x‖ ≤ ε) :
    ∃ p : Program O, p.count ≤ q ∧
      ∀ x, ‖p.eval x ∘L (E ∘L J x) - E ∘L T x‖ ≤ ε := by
  obtain ⟨p, hp, heval⟩ := h
  refine ⟨p, hp, fun x => ?_⟩
  rw [output_error_eq E hE (p.eval x) (J x) (S x) (T x) (heval x)]
  exact hError x

/-- A logical full-output error guarantee transfers to the physical program
on encoded input, without paying or assuming an encoding preparation cost. -/
theorem ImplementsOn.error_certificate {O : X → K →L[ℂ] K}
    {F : X → P →L[ℂ] P} {E : P →L[ℂ] K} {q : ℕ}
    (h : ImplementsOn O F E q) (hE : E† ∘L E = 1)
    (J T : X → H →L[ℂ] P) (ε : ℝ) (hError : ∀ x, ‖F x ∘L J x - T x‖ ≤ ε) :
    ∃ p : Program O, p.count ≤ q ∧
      ∀ x, ‖p.eval x ∘L (E ∘L J x) - E ∘L T x‖ ≤ ε := by
  obtain ⟨p, hp, hq⟩ := h
  refine ⟨p, hq, fun x => ?_⟩
  rw [error_eq E hE (p.eval x) (F x) (hp x)]
  exact hError x

end
end SparseHamiltonian.EncodedOracle
