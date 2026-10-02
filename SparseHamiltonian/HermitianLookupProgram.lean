import SparseHamiltonian.HermitianDilation

/-!
# Counted lookup programs for Hermitian dilations

An arbitrary source lookup program is controlled on one Boolean branch and
its inverse on the other. A fixed branch swap gives a full-space Hermitian
involution. A fixed register regrouping exchanges target and scratch so the
result uses an ordinary lookup on an expanded address, at unchanged count.
-/

namespace SparseHamiltonian.HermitianLookupProgram

noncomputable section
open ContinuousLinearMap OracleCircuit MaskedLookupCurry
open scoped InnerProduct

variable {X A Z : Type*} [Fintype A] [Fintype Z] [AddCommGroup Z]

/-- Treat the Boolean dilation label as an extra address spectator. -/
def expandedTable (f : X → A → Z) (x : X) (a : Bool × A) : Z := f x a.2

omit [Fintype A] [Fintype Z] [AddCommGroup Z] in
/-- Group the Boolean label with the address and exchange target and scratch. -/
def registerBasisEquiv : (Bool × Local A Z) ≃ Local (Bool × A) Z where
  toFun v := (((v.1, v.2.1.1), v.2.2), v.2.1.2)
  invFun v := (v.1.1.1, ((v.1.1.2, v.2), v.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The exact fixed Hilbert register change; it is independent of oracle data. -/
def registerEquiv : PiLp 2 (fun _ : Bool => Payload A Z) ≃ₗᵢ[ℂ] Payload (Bool × A) Z :=
  (RegisterEquivalences.productFlatten Bool (Local A Z)).trans
    (LookupOracle.permutationUnitary registerBasisEquiv)

omit [AddCommGroup Z] in
@[simp] theorem registerEquiv_apply
    (v : PiLp 2 (fun _ : Bool => Payload A Z)) (b : Bool) (a : A) (z y : Z) :
    registerEquiv v (((b, a), z), y) = v b ((a, y), z) := rfl

omit [AddCommGroup Z] in
@[simp] theorem registerEquiv_symm_apply
    (v : Payload (Bool × A) Z) (b : Bool) (a : A) (z y : Z) :
    registerEquiv.symm v b ((a, z), y) = v (((b, a), y), z) := rfl

/-- The transported common scratch oracle is one ordinary target lookup on the
expanded address. This is an exact operator identity on arbitrary scratch states. -/
theorem registerEquiv_oracle (f : X → A → Z) (x : X) :
    (registerEquiv (A := A) (Z := Z)).conjStarAlgEquiv (oracle (I := Bool) f x) =
      localSigned 1 (expandedTable f) x := by
  ext v w
  rcases w with ⟨⟨⟨b, a⟩, z⟩, y⟩
  change v (((b, a), z - f x a), y) =
    v (((b, a), z - (1 : ℤ) • expandedTable f x (b, a)), y)
  simp [expandedTable]

omit [AddCommGroup Z] in
/-- Forward control on the false branch and inverse control on the true branch,
followed by the fixed swap, give the exact Hermitian dilation. -/
theorem dilation_eq_masked (U : Payload A Z →L[ℂ] Payload A Z) :
    HermitianDilation.dilation U =
      MaskedProgram.masked Bool.not U * MaskedProgram.masked id (star U) *
        HermitianDilation.swap := by
  ext v b
  cases b <;> simp [HermitianDilation.dilation_apply_false,
    HermitianDilation.dilation_apply_true, MaskedProgram.masked_apply,
    HermitianDilation.swap_apply, ContinuousLinearMap.star_eq_adjoint]

/-- Choose the uniform controlled circuit supplied by the two-query compiler. -/
def controlledProgram (f : X → A → Z) (active : Bool → Bool)
    (p : Program (localSigned 1 f)) : Program (oracle (I := Bool) f) :=
  Classical.choose (LookupProgramControl.program_certificate f active p)

/-- Exact full-space semantics of the selected controlled source circuit. -/
theorem controlledProgram_eval (f : X → A → Z) (active : Bool → Bool)
    (p : Program (localSigned 1 f)) (x : X) :
    (controlledProgram f active p).eval x = MaskedProgram.masked active (p.eval x) :=
  (Classical.choose_spec (LookupProgramControl.program_certificate f active p)).1 x

/-- The selected control compiler obeys its proved ordinary-query bound. -/
theorem controlledProgram_count (f : X → A → Z) (active : Bool → Bool)
    (p : Program (localSigned 1 f)) : (controlledProgram f active p).count ≤ 2 * p.count :=
  (Classical.choose_spec (LookupProgramControl.program_certificate f active p)).2

/-- The concrete uniform circuit uses two independently compiled complementary
controls and one fixed swap; inverse queries are syntactic program adjoints. -/
def dilationProgram (f : X → A → Z) (p : Program (localSigned 1 f)) :
    Program (oracle (I := Bool) f) :=
  .seq (.seq
    (controlledProgram f Bool.not p)
    (controlledProgram f id p.adjoint))
    (.fixed HermitianDilation.swap HermitianDilation.swap_unitary)

/-- The compiled program implements the Hermitian dilation on the entire space. -/
theorem dilationProgram_eval (f : X → A → Z) (p : Program (localSigned 1 f)) (x : X) :
    (dilationProgram f p).eval x = HermitianDilation.dilation (p.eval x) := by
  simp only [dilationProgram, Program.eval_seq, Program.eval_fixed, controlledProgram_eval,
    Program.eval_adjoint, dilation_eq_masked]

/-- Controlling each source query costs two calls for each of the two masks. -/
theorem dilationProgram_count (f : X → A → Z) (p : Program (localSigned 1 f)) :
    (dilationProgram f p).count ≤ 4 * p.count := by
  have hForward := controlledProgram_count f Bool.not p
  have hInverse := controlledProgram_count f id p.adjoint
  simp only [Program.count_adjoint] at hInverse
  simp only [dilationProgram, Program.count_seq, Program.count_fixed]
  omega

/-- The actual counted circuit squares to identity on every physical vector. -/
theorem dilationProgram_involution (f : X → A → Z) (p : Program (localSigned 1 f))
    (x : X) (v : PiLp 2 (fun _ : Bool => Payload A Z)) :
    (dilationProgram f p).eval x ((dilationProgram f p).eval x v) = v := by
  rw [dilationProgram_eval]
  exact HermitianDilation.dilation_involution (p.eval x)
    (p.eval_unitary (localSigned_unitary 1 f) x) v

/-- The ordinary scratch oracle becomes one ordinary target query after the
fixed regrouping. Substitution uses the proved oracle identity, not a new primitive. -/
def expandedProgram (f : X → A → Z) (p : Program (localSigned 1 f)) :
    Program (localSigned 1 (expandedTable f)) :=
  ((dilationProgram f p).transport registerEquiv).substitute .query

/-- Exact source-program semantics survive the fixed register regrouping. -/
theorem expandedProgram_eval (f : X → A → Z) (p : Program (localSigned 1 f)) (x : X) :
    (expandedProgram f p).eval x = (registerEquiv (A := A) (Z := Z)).conjStarAlgEquiv
      (HermitianDilation.dilation (p.eval x)) := by
  rw [expandedProgram, Program.eval_substitute]
  · rw [Program.eval_transport, dilationProgram_eval]
  · intro y
    exact (registerEquiv_oracle f y).symm

/-- Regrouping and renaming the oracle preserve the fourfold query bound. -/
theorem expandedProgram_count (f : X → A → Z) (p : Program (localSigned 1 f)) :
    (expandedProgram f p).count ≤ 4 * p.count := by
  simpa only [expandedProgram, Program.count_substitute, Program.count_query,
    Program.count_transport, Nat.mul_one] using dilationProgram_count f p

/-- The expanded-address program remains a full-workspace involution. -/
theorem expandedProgram_involution (f : X → A → Z) (p : Program (localSigned 1 f))
    (x : X) (v : Payload (Bool × A) Z) :
    (expandedProgram f p).eval x ((expandedProgram f p).eval x v) = v := by
  rw [expandedProgram_eval]
  change registerEquiv (HermitianDilation.dilation (p.eval x)
    (registerEquiv.symm (registerEquiv (HermitianDilation.dilation (p.eval x)
      (registerEquiv.symm v))))) = v
  rw [LinearIsometryEquiv.symm_apply_apply,
    HermitianDilation.dilation_involution (p.eval x) (p.eval_unitary (localSigned_unitary 1 f) x),
    LinearIsometryEquiv.apply_symm_apply]

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- A fixed source block embedding, plus preparation, and register regrouping
combine to an isometry of the original public space into the expanded payload. -/
def expandedEmbedding (E : P →ₗᵢ[ℂ] Payload A Z) : P →ₗᵢ[ℂ] Payload (Bool × A) Z :=
  registerEquiv.toLinearIsometry.comp (HermitianDilation.plusIsometry.comp E)

/-- The expanded program's compressed block is the Hermitian part of the
original source-program block. The encoding is independent of oracle data. -/
theorem expandedProgram_compression (f : X → A → Z) (p : Program (localSigned 1 f))
    (E : P →ₗᵢ[ℂ] Payload A Z) (x : X) :
    (expandedEmbedding E).toContinuousLinearMap† ∘L (expandedProgram f p).eval x ∘L
        (expandedEmbedding E).toContinuousLinearMap =
      HermitianDilation.hermitianPart
        (E.toContinuousLinearMap† ∘L p.eval x ∘L E.toContinuousLinearMap) := by
  rw [expandedProgram_eval]
  have hTransport :
      (expandedEmbedding E).toContinuousLinearMap† ∘L
        registerEquiv.conjStarAlgEquiv (HermitianDilation.dilation (p.eval x)) ∘L
        (expandedEmbedding E).toContinuousLinearMap =
      (HermitianDilation.encodedPlus E.toContinuousLinearMap)† ∘L
        HermitianDilation.dilation (p.eval x) ∘L
        HermitianDilation.encodedPlus E.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    apply ext_inner_right ℂ
    intro w
    simp only [comp_apply, adjoint_inner_left]
    change inner ℂ (registerEquiv (HermitianDilation.dilation (p.eval x)
      (registerEquiv.symm (registerEquiv (HermitianDilation.encodedPlus E.toContinuousLinearMap v)))))
      (registerEquiv (HermitianDilation.encodedPlus E.toContinuousLinearMap w)) = _
    rw [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.inner_map_map]
  rw [hTransport, HermitianDilation.encodedPlus_compression]

/-- Hermitian dilation and the query-preserving register change do not worsen
block-encoding error against a self-adjoint target. -/
theorem expandedProgram_compression_error (f : X → A → Z)
    (p : Program (localSigned 1 f)) (E : P →ₗᵢ[ℂ] Payload A Z) (x : X)
    (H : P →L[ℂ] P) (hH : H† = H) (δ : ℝ)
    (hError : ‖E.toContinuousLinearMap† ∘L p.eval x ∘L E.toContinuousLinearMap - H‖ ≤ δ) :
    ‖(expandedEmbedding E).toContinuousLinearMap† ∘L (expandedProgram f p).eval x ∘L
        (expandedEmbedding E).toContinuousLinearMap - H‖ ≤ δ := by
  rw [expandedProgram_compression]
  exact (HermitianDilation.hermitianPart_error _ H hH).trans hError

end
end SparseHamiltonian.HermitianLookupProgram
