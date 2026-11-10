import AdaptiveODELowerBound.Access.Calls
import SparseLowerBounds.Query.Ancilla
import SparseLowerBounds.Adaptive.Access
import SparseHamiltonian.EncodedOracle
import SparseLowerBounds.Helpers.HsRelease.PhaseAccess

set_option autoImplicit false

/-!
# Call forms cost no more Boolean queries than the call

Manuscript: the construction before Theorem `odel:thm:joint` ("A value query computes one relevant
membership bit, writes the known entry and uncomputes the bit. It therefore uses at most two
membership queries, also for inverse and controlled calls") and the chain construction of Section
`part:hsl`.

If every label `l` of a unitary family `O` is implemented on an encoding `Enc` by at most
`w l` queries of a Boolean phase oracle `x ↦ P.phase (y x)` (`EncodedOracle.ImplementsOn`),
then every call form of `l` (`callFamily O`: plain, inverse, controlled, controlled inverse) is
implemented by at most `w l` queries of **one** Boolean phase oracle, on **one** encoding, for all
labels and forms at once (`implementsOn_callFamily`):

* the Boolean family is `callBoolean P = 1_c ⊗ |1⟩⟨1|_d ⊗ P_i` on an outer register `c` (the
  workspace control) and an inner query-control register `d` (`ctrlFamily`, `ProjFamily.spectate`);
  its phase oracle is `1_c ⊗ ctrl_d(P.phase y)` (`phase_ctrlFamily` and the released
  `SparseLowerBounds.Hamiltonian.HsRelease.phase_spectate`);
* the encoding is `callEncoding Enc : |c⟩ ⊗ v ↦ |c⟩ ⊗ |1⟩_d ⊗ Enc v`;
* a plain call runs the `d`-controlled implementing program (the package's mask compiler
  `SparseHamiltonian.MaskedProgram.compile` with the identity mask on `d`: every gate and every
  query controlled by `d`, the same number of queries, `compile_eval`, `compile_count`), which
  acts as the original program since `d = 1` on encoded vectors; a controlled call conjugates it
  by the fixed unitary that sets `d = c` on encoded vectors, so that on `c = 0` the program acts
  as the identity; inverse forms are the inverse programs (`EncodedOracle.ImplementsOn.adjoint`).
-/

namespace AdaptiveODELowerBound.Access

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit
open SparseLowerBounds.Adaptive.Access (jointMap)
open scoped InnerProduct InnerProductSpace

variable {B I : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- **The controlled projection family** `|1⟩⟨1|_d ⊗ P_i` on query control ⊗ `B`. -/
def ctrlFamily (P : ProjFamily B I) : ProjFamily (Joint Bool B) I where
  proj i := Joint.fiber fun d => if d then P.proj i else 0
  isStarProjection i := by
    have hP := P.isStarProjection i
    refine ⟨?_, ?_⟩
    · show Joint.fiber _ * Joint.fiber _ = _
      rw [Joint.fiber_mul]
      congr 1
      funext d
      cases d
      · exact zero_mul _
      · exact hP.isIdempotentElem.eq
    · show star (Joint.fiber _) = _
      rw [Joint.star_fiber]
      congr 1
      funext d
      cases d
      · exact star_zero _
      · exact hP.isSelfAdjoint.star_eq
  orthogonal i i' h := by
    show Joint.fiber _ * Joint.fiber _ = 0
    rw [Joint.fiber_mul]
    ext Ψ d
    cases d
    · simp [Joint.fiber_apply]
    · simp [Joint.fiber_apply, P.orthogonal i i' h]

/-- The phase oracle of the controlled family is the controlled phase oracle. -/
theorem phase_ctrlFamily [Fintype I] (P : ProjFamily B I) (y : I → Bool) :
    (ctrlFamily P).phase y = ctrlOp (P.phase y) := by
  ext Ψ d
  rw [ctrlOp, MaskedProgram.masked_apply, PhaseCircuit.phase_eq_hitProj,
    PhaseCircuit.phase_eq_hitProj]
  change Ψ d - ((2 : ℂ) • PhaseCircuit.hitProj (ctrlFamily P) y Ψ) d = _
  rw [PiLp.smul_apply, PhaseCircuit.hitProj_apply, PhaseCircuit.joint_sum_apply]
  cases d
  · simp [ctrlFamily, Joint.fiber_apply]
  · simp [ctrlFamily, Joint.fiber_apply, PhaseCircuit.hitProj_apply]

/-- **The active embedding** `v ↦ |1⟩_d ⊗ v`. It plays the role of the clean-ancilla encoding
`SparseLowerBounds.ancillaEmbed` (`v ↦ |0⟩ ⊗ v` on `Joint (Fin 2)`) for the query-control
register `d : Bool`, on which the controlled program and the controlled family are active at
`d = true` (the convention of `ctrlOp` and of the mask compiler with the identity mask). -/
def activeEmbed (B : Type*) [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] :
    B →L[ℂ] Joint Bool B :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Bool => B)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun d => if d then ContinuousLinearMap.id ℂ B else 0)

/-- The active embedding places the vector on the active branch `d = true`. -/
theorem activeEmbed_apply (v : B) (d : Bool) :
    activeEmbed B v d = if d then v else 0 := by
  change (if d then ContinuousLinearMap.id ℂ B else 0) v = _
  split_ifs <;> rfl

/-- The active embedding is an isometry. -/
theorem activeEmbed_isometry : (activeEmbed B)† ∘L activeEmbed B = 1 := by
  ext v
  refine ext_inner_left ℂ fun w => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    PiLp.inner_apply, Fintype.sum_bool]
  simp only [activeEmbed_apply]
  simp

/-- The controlled operator intertwines the active embedding:
`ctrl(V) (|1⟩ ⊗ v) = |1⟩ ⊗ V v`. -/
theorem ctrlOp_comp_activeEmbed (V : B →L[ℂ] B) :
    ctrlOp V ∘L activeEmbed B = activeEmbed B ∘L V := by
  ext v d
  cases d <;> simp [ctrlOp, activeEmbed_apply]

/-- **The control flip** `X_d ⊗ 1`: it exchanges the two branches of the query-control register. -/
def flipD (B : Type*) [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] :
    Joint Bool B →L[ℂ] Joint Bool B :=
  Joint.mk fun d => Joint.proj (!d)

/-- The control flip reads the other branch. -/
@[simp] theorem flipD_apply (Ψ : Joint Bool B) (d : Bool) : flipD B Ψ d = Ψ (!d) := rfl

/-- The control flip is an involution. -/
theorem flipD_mul_self : flipD B * flipD B = 1 := by
  ext Ψ d
  simp

/-- The control flip is self-adjoint. -/
theorem star_flipD : star (flipD B) = flipD B := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro Φ Ψ
  simp only [PiLp.inner_apply, flipD_apply, Fintype.sum_bool, Bool.not_true, Bool.not_false]
  exact add_comm _ _

/-- The control flip is unitary. -/
theorem flipD_unitary : IsUnitary (flipD B) :=
  ⟨by rw [star_flipD, flipD_mul_self], by rw [star_flipD, flipD_mul_self]⟩

/-- **The control alignment** `|0⟩⟨0|_c ⊗ X_d + |1⟩⟨1|_c ⊗ 1`: on encoded vectors (`d = 1`) it sets
the query control `d` to the workspace control `c`. -/
def alignCtrl (B : Type*) [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] :
    Joint Bool (Joint Bool B) →L[ℂ] Joint Bool (Joint Bool B) :=
  Joint.fiber fun c => if c then 1 else flipD B

/-- The control alignment is unitary. -/
theorem alignCtrl_unitary : IsUnitary (alignCtrl B) :=
  PhaseCircuit.isUnitary_fiber _ fun c => by
    cases c
    · exact flipD_unitary
    · exact ⟨by simp, by simp⟩

/-- **The Boolean family of the call forms**: `1_c ⊗ |1⟩⟨1|_d ⊗ P_i`. -/
def callBoolean (P : ProjFamily B I) : ProjFamily (Joint Bool (Joint Bool B)) I :=
  (ctrlFamily P).spectate Bool

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- **The encoding of the call forms**: `|c⟩ ⊗ v ↦ |c⟩ ⊗ |1⟩_d ⊗ Enc v`. -/
def callEncoding (Enc : W →L[ℂ] B) : Joint Bool W →L[ℂ] Joint Bool (Joint Bool B) :=
  jointMap Bool (activeEmbed B ∘L Enc)

/-- The call encoding of an isometry is an isometry. -/
theorem callEncoding_isometry (Enc : W →L[ℂ] B) (hEnc : Enc† ∘L Enc = 1) :
    (callEncoding Enc)† ∘L callEncoding Enc = 1 := by
  have hA : (activeEmbed B ∘L Enc)† ∘L (activeEmbed B ∘L Enc) = 1 := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc ((activeEmbed B)†), activeEmbed_isometry,
      ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, hEnc]
  exact Adaptive.Access.jointMap_isometry Bool _ hA

omit [CompleteSpace W] in
/-- The controlled oracle letter `x ↦ ctrl_d(P.phase (y x))` implements on `|1⟩_d ⊗ Enc` whatever
the oracle letter `x ↦ P.phase (y x)` implements on `Enc`, with the same number of queries: run the
`d`-controlled program (`MaskedProgram.compile` with the identity mask). -/
theorem implementsOn_active [Fintype I] (P : ProjFamily B I) {X : Type*} (y : X → I → Bool)
    {Enc : W →L[ℂ] B} {F : X → W →L[ℂ] W} {q : ℕ}
    (h : EncodedOracle.ImplementsOn (fun x => P.phase (y x)) F Enc q) :
    EncodedOracle.ImplementsOn (fun x => ctrlOp (P.phase (y x))) F (activeEmbed B ∘L Enc) q := by
  change EncodedOracle.ImplementsOn
    (fun x => MaskedProgram.masked (fun d : Bool => d) (P.phase (y x))) F _ q
  obtain ⟨p, hp, hc⟩ := h
  refine ⟨MaskedProgram.compile (fun d : Bool => d) p, fun x => ?_, ?_⟩
  · rw [MaskedProgram.compile_eval]
    change (ctrlOp (p.eval x) ∘L activeEmbed B) ∘L Enc = _
    rw [ctrlOp_comp_activeEmbed, ContinuousLinearMap.comp_assoc, hp x,
      ← ContinuousLinearMap.comp_assoc]
  · rw [MaskedProgram.compile_count]
    exact hc

/-- The plain form: `1_c ⊗ F x` is implemented on `callEncoding Enc` by the outer oracle letter
`x ↦ 1_c ⊗ ctrl_d(P.phase (y x))`, with the same number of queries. -/
theorem implementsOn_plainForm [Fintype I] (P : ProjFamily B I) {X : Type*} (y : X → I → Bool)
    {Enc : W →L[ℂ] B} {F : X → W →L[ℂ] W} {q : ℕ}
    (h : EncodedOracle.ImplementsOn (fun x => P.phase (y x)) F Enc q) :
    EncodedOracle.ImplementsOn (fun x => Joint.fiber fun _ : Bool => ctrlOp (P.phase (y x)))
      (fun x => formOp .plain (F x)) (callEncoding Enc) q :=
  Adaptive.Access.implementsOn_spectate Bool (implementsOn_active P y h)

/-- The controlled form: `ctrl_c(F x)` is implemented on `callEncoding Enc` by the outer oracle
letter `x ↦ 1_c ⊗ ctrl_d(P.phase (y x))`, with the same number of queries: the `d`-controlled
program conjugated by the control alignment `alignCtrl`. -/
theorem implementsOn_controlledForm [Fintype I] (P : ProjFamily B I) {X : Type*}
    (y : X → I → Bool) {Enc : W →L[ℂ] B} {F : X → W →L[ℂ] W} {q : ℕ}
    (h : EncodedOracle.ImplementsOn (fun x => P.phase (y x)) F Enc q) :
    EncodedOracle.ImplementsOn (fun x => Joint.fiber fun _ : Bool => ctrlOp (P.phase (y x)))
      (fun x => formOp .controlled (F x)) (callEncoding Enc) q := by
  change EncodedOracle.ImplementsOn
    (fun x => Joint.fiber fun _ : Bool => MaskedProgram.masked (fun d : Bool => d) (P.phase (y x)))
    _ _ q
  obtain ⟨p, hp, hc⟩ := h
  have hp' : ∀ x v, p.eval x (Enc v) = Enc (F x v) := fun x v =>
    DFunLike.congr_fun (hp x) v
  refine ⟨.seq (.fixed (alignCtrl B) alignCtrl_unitary)
    (.seq (Helpers.Adaptive.Access.liftProgram Bool (MaskedProgram.compile (fun d : Bool => d) p))
      (.fixed (alignCtrl B) alignCtrl_unitary)), fun x => ?_, ?_⟩
  · rw [Program.eval_seq, Program.eval_seq, Program.eval_fixed,
      Helpers.Adaptive.Access.eval_liftProgram, MaskedProgram.compile_eval]
    ext Ψ c d
    cases c <;> cases d <;>
      simp [alignCtrl, callEncoding, formOp, ctrlOp, Adaptive.Access.jointMap_apply,
        activeEmbed_apply, hp']
  · simpa only [Program.count_seq, Program.count_fixed, Helpers.Adaptive.Access.count_liftProgram,
      MaskedProgram.compile_count, zero_add, add_zero] using hc

/-- The controlled operator of an adjoint is the adjoint of the controlled operator. -/
theorem star_ctrlOp (U : W →L[ℂ] W) : star (ctrlOp U) = ctrlOp (star U) := by
  simp only [ctrlOp, ContinuousLinearMap.star_eq_adjoint, MaskedProgram.masked_adjoint]

/-- **Call forms cost no more Boolean queries than the call** (the construction before Theorem
`odel:thm:joint` and the chain construction of Section `part:hsl`): if every label `l` of the
unitary family `O` is implemented on the encoding `Enc` by at most `w l` queries of the Boolean
phase oracle `x ↦ P.phase (y x)`, then every call form of every label (`callFamily O`) is
implemented on `callEncoding Enc` by at most `w l` queries of the single Boolean phase oracle
`x ↦ (callBoolean P).phase (y x)`. -/
theorem implementsOn_callFamily [Fintype I] (P : ProjFamily B I) {X : Type*} (y : X → I → Bool)
    (Enc : W →L[ℂ] B) {L : Type*} (O : L → X → W →L[ℂ] W)
    (hO : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun x => P.phase (y x)) (O l) Enc (w l))
    (c : L × CallForm) :
    EncodedOracle.ImplementsOn (fun x => (callBoolean P).phase (y x)) (callFamily O c)
      (callEncoding Enc) (w c.1) := by
  obtain ⟨l, f⟩ := c
  have hQ : (fun x => (callBoolean P).phase (y x)) =
      fun x => Joint.fiber (fun _ : Bool => ctrlOp (P.phase (y x))) :=
    funext fun x => by
      rw [callBoolean, Hamiltonian.HsRelease.phase_spectate, phase_ctrlFamily]
  rw [hQ]
  have hu : ∀ x, IsUnitary (Joint.fiber fun _ : Bool => ctrlOp (P.phase (y x))) := fun x =>
    PhaseCircuit.isUnitary_fiber _ fun _ =>
      MaskedProgram.masked_unitary _ _ (P.isUnitary_phase (y x))
  have hplain := implementsOn_plainForm P y (hw l)
  have hctrl := implementsOn_controlledForm P y (hw l)
  cases f
  · exact hplain
  · refine (hplain.adjoint hu fun x => formOp_unitary .plain (hO l x)).congr fun x => ?_
    exact Joint.star_fiber _
  · exact hctrl
  · refine (hctrl.adjoint hu fun x => formOp_unitary .controlled (hO l x)).congr fun x => ?_
    exact star_ctrlOp _

end

end AdaptiveODELowerBound.Access
