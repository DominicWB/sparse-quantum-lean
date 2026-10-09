import GeneralODE.Theorem

/-!
# Theorem `ode:thm:general` at `T = 0`: direct state preparation

The released theorem `general` (`GeneralODE/Theorem.lean`) treats `T > 0`.  At
`T = 0` the target is `x(0) = x₀` (`ODEConstantForcing.solution_zero`), and the
paper notes that this case is direct state preparation.  This file formalises
that remark in the same physical oracle model
`physicalOracle D J₀ Jb N Tn d m K w`, for every choice of the parameters with
at least one solver branch (`w ≥ 1`).

**The protocol** (`ZeroTime.protocol`).  The fixed input state is the seed in
the system register at history slot `0`, with the history ancilla in a fixed
clean basis state, the released native control workspace in its clean packet
(`NativeControlledOracle.packet`) and the branch register in branch `w₀`
(`ZeroTime.decoder`).  One uncontrolled physical call of the initial-state
interface (label `false`) applies `J₀ x` on slot `0`, so the state becomes the
same encoding of `J₀ x seed = x₀/‖x₀‖` (`ZeroTime.query_decoder`).  The output
decoder is the fixed isometry of that encoding, so the decoded output is exactly
`x₀/‖x₀‖`, of norm one.  The released damping qubit, randomized amplification
(gain `1`) and four-attempt wrapper (`Amplify.protocol`, `Amplify.outcome`)
turn this exact preparation into the guarantee `Amplify.Outcome`.  By
`Amplify.protocol_worstCost` every history makes at most `40 · 1` times the
calls of the one-query program (`ZeroTime.prepare`): no native matrix query, no
forcing call and at most `40` initial-state calls.  The public norms are not
used, and nothing from outside the paper (in particular no `BlockSolver`) is
needed at `T = 0`.

**Main theorems.**
* `general_zero`: for all parameters with `w ≥ 1` there is one protocol, chosen
  before the input, that in every history (including four failures) makes no
  native matrix query, no call of the forcing interface and at most `40` calls
  of the initial-state interface; for every input with `x₀ ≠ 0` and
  `J₀ x seed = x₀/‖x₀‖` and every `ε ≥ 0` it succeeds with probability at least
  `175/256 > 2/3`, and its conditional output is a density operator within
  trace distance `ε` of `x(0)/‖x(0)‖`.
* `general_nonneg`: Theorem `ode:thm:general` for every `T ≥ 0`, with the
  parameters of `Plan` and the hypotheses of `general`.  For `T > 0` it is
  `general`; for `T = 0` the budgets are `0` matrix queries, `0` forcing calls
  and `40` initial-state calls, and the instance hypothesis `x(0) ≠ 0` gives
  `x₀ ≠ 0`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralODE

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Registers History
  ODEStateNormalization Solver NativeBlock SparseStateOverlap LCU
open scoped InnerProduct
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ZeroTime

section Generic

/-- A unit vector is its own direction. -/
theorem unitDirection_of_norm_eq_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E} (hu : ‖u‖ = 1) : unitDirection u = u := by
  rw [unitDirection, hu, inv_one, one_smul]

/-- A physical native query acts on the payload of a branch state of a clean packet. -/
theorem oracle_branch_packet {ι B X : Type} [Fintype ι] [Fintype B] [DecidableEq B]
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (x : X) (a : EuclideanSpace ℂ ι)
    (c : Bool) (d r : B) (v : EuclideanSpace ℂ B) :
    NativeMaskedOracle.oracle (ι := ι) F x (branchState a (NativeControlledOracle.packet c d r v)) =
      branchState a (NativeControlledOracle.packet c d r (F x v)) := by
  apply PiLp.ext
  intro i
  change MaskedProgram.masked (fun _ : ι => true) (NativeControlledOracle.oracle F x)
      (branchState a (NativeControlledOracle.packet c d r v)) i = _
  simp only [MaskedProgram.masked_apply, branchState_apply, if_true, map_smul,
    NativeControlledOracle.oracle_packet]

/-- `J` on slot `tgt` acts on the system factor of `|tgt⟩ ⊗ u`. -/
theorem slotControlled_ketL {n : Type} [Fintype n] {m : ℕ} (tgt : Slot m)
    (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (u : EuclideanSpace ℂ n) :
    slotControlled tgt J (ketL (EuclideanSpace.single tgt 1) u) =
      ketL (EuclideanSpace.single tgt 1) (J u) := by
  have hsl : slice (ketL (EuclideanSpace.single tgt (1 : ℂ)) u) tgt = u := by
    ext j
    simp
  ext ⟨s', i⟩
  rw [slotControlled_apply]
  by_cases h : s' = tgt
  · subst h
    rw [if_pos rfl, hsl, ketL_apply]
    simp
  · rw [if_neg h, ketL_apply, ketL_apply]
    simp [h]

/-- The initial-state source oracle applies `J₀ x` to the system at slot `0`. -/
theorem sourceOracle_false_embed {n a X : Type} [Fintype n] [Fintype a] [DecidableEq a]
    {m : ℕ} (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (a₀ : a) (x : X)
    (u : EuclideanSpace ℂ n) :
    sourceOracle (m := m) (a := a) J₀ Jb false x
        (embed a₀ (ketL (EuclideanSpace.single (slot0 m) 1) u)) =
      embed a₀ (ketL (EuclideanSpace.single (slot0 m) 1) (J₀ x u)) := by
  change actLeft (α := a) (slotControlled (slot0 m) (J₀ x))
      (ketR (EuclideanSpace.single a₀ 1) (ketL (EuclideanSpace.single (slot0 m) 1) u)) = _
  rw [actLeft_ketR, slotControlled_ketL]
  rfl

end Generic

variable {n : Type} [Fintype n] [DecidableEq n]
variable {X Z : Type} [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- The payload register of the physical oracles: history slot, system and
history ancilla. -/
abbrev Payload (n Z : Type) [Fintype n] [Fintype Z] (N Tn d m K : ℕ) :=
  (Slot m × n) × HistAnc n (FlatBasis N n Z Tn d) m K

/-- The physical oracle family without the damping qubit. -/
abbrev maskedOracle (D : Data X n Z s)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (N Tn d m K w : ℕ) :
    ((Fin K × Query) ⊕ Bool) → X →
      NativeMaskedOracle.Physical (Fin w) (Payload n Z N Tn d m K) →L[ℂ]
        NativeMaskedOracle.Physical (Fin w) (Payload n Z N Tn d m K) :=
  NativeMaskedProgram.oracle (ι := Fin w)
    (Sum.elim
      (fun il x => ((specHom (Slot m × n) (HistAnc n (FlatBasis N n Z Tn d) m K)).comp
          (specHom Term ((Ctl m K × n) × PowAnc (FlatBasis N n Z Tn d) m K)))
        (powOracle (facOracle (n := n) m K (flatOracle D N Tn d)) K il x))
      (sourceOracle (m := m) (a := HistAnc n (FlatBasis N n Z Tn d) m K) J₀ Jb))

omit [DecidableEq Z] in
/-- The physical oracles are the masked oracles with the damping qubit as a spectator. -/
theorem physicalOracle_eq (D : Data X n Z s)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (N Tn d m K w : ℕ) :
    physicalOracle D J₀ Jb N Tn d m K w = Amplify.liftOracle (maskedOracle D J₀ Jb N Tn d m K w) :=
  rfl

omit [DecidableEq Z] in
/-- All physical oracles are unitary. -/
theorem maskedOracle_unitary (D : Data X n Z s)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y)) (N Tn d m K w : ℕ) :
    ∀ l y, IsUnitary (maskedOracle D J₀ Jb N Tn d m K w l y) := by
  intro l y
  apply NativeMaskedOracle.oracle_unitary
  intro y'
  rcases l with il | b
  · exact isUnitary_map _ (powOracle_unitary _
      (fun l' y'' => isUnitary_map _ (flatOracle_unitary D N Tn d l' y'')) K il y')
  · exact sourceOracle_unitary J₀ Jb hJ₀ hJb b y'

/-- A fixed clean basis label of the history ancilla. -/
def ancClean (D : Data X n Z s) (N Tn d m K : ℕ) (i₀ : n) :
    HistAnc n (FlatBasis N n Z Tn d) m K :=
  (Term.id, ((((0 : Fin (K + 1)), (none : Slot m)), i₀),
    powClean (m := m) (K := K) (flatClean D N Tn d)))

/-- A fixed payload label, used as dummy and reference of the native control
workspace. -/
def payloadClean (D : Data X n Z s) (N Tn d m K : ℕ) (i₀ : n) : Payload n Z N Tn d m K :=
  ((slot0 m, i₀), ancClean D N Tn d m K i₀)

/-- The fixed encoding of the system register:
`u ↦ |w₀⟩ ⊗ packet(|slot 0⟩ ⊗ u ⊗ |a₀⟩)`.  It is both the input encoding of
the seed and the output decoder. -/
def decoder (D : Data X n Z s) (N Tn d m K : ℕ) {w : ℕ} (w₀ : Fin w) (i₀ : n) :
    EuclideanSpace ℂ n →L[ℂ] NativeMaskedOracle.Physical (Fin w) (Payload n Z N Tn d m K) :=
  branchState (EuclideanSpace.single w₀ 1) ∘L
    ((NativeControlledOracle.packet false (payloadClean D N Tn d m K i₀)
        (payloadClean D N Tn d m K i₀)).toContinuousLinearMap ∘L
      (embed (ancClean D N Tn d m K i₀) ∘L ketL (EuclideanSpace.single (slot0 m) 1)))

/-- The decoder in coordinates. -/
theorem decoder_apply (D : Data X n Z s) (N Tn d m K : ℕ) {w : ℕ} (w₀ : Fin w) (i₀ : n)
    (u : EuclideanSpace ℂ n) :
    decoder D N Tn d m K w₀ i₀ u =
      branchState (EuclideanSpace.single w₀ 1)
        (NativeControlledOracle.packet false (payloadClean D N Tn d m K i₀)
          (payloadClean D N Tn d m K i₀)
          (embed (ancClean D N Tn d m K i₀) (ketL (EuclideanSpace.single (slot0 m) 1) u))) :=
  rfl

/-- The decoder is an isometry. -/
theorem decoder_isometry (D : Data X n Z s) (N Tn d m K : ℕ) {w : ℕ} (w₀ : Fin w) (i₀ : n) :
    (decoder D N Tn d m K w₀ i₀)† ∘L decoder D N Tn d m K w₀ i₀ = 1 :=
  isometry_comp _ _ (branchState_isometry _ (by simp))
    (isometry_comp _ _ (LinearIsometry.adjoint_comp_self _)
      (isometry_comp _ _ (embed_isometry _) (ketL_isometry _ (by simp))))

/-- The decoder preserves norms. -/
theorem norm_decoder (D : Data X n Z s) (N Tn d m K : ℕ) {w : ℕ} (w₀ : Fin w) (i₀ : n)
    (u : EuclideanSpace ℂ n) : ‖decoder D N Tn d m K w₀ i₀ u‖ = ‖u‖ :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr (decoder_isometry D N Tn d m K w₀ i₀) u

/-- The adjoint of the decoder inverts it. -/
theorem decoder_adjoint_apply (D : Data X n Z s) (N Tn d m K : ℕ) {w : ℕ} (w₀ : Fin w)
    (i₀ : n) (u : EuclideanSpace ℂ n) :
    ((decoder D N Tn d m K w₀ i₀)†) (decoder D N Tn d m K w₀ i₀ u) = u := by
  have h := congrArg (fun T : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n => T u)
    (decoder_isometry D N Tn d m K w₀ i₀)
  simpa using h

/-- One physical call of the initial-state interface maps the encoding of `u` to
the encoding of `J₀ x u`. -/
theorem query_decoder (D : Data X n Z s)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (N Tn d m K : ℕ) {w : ℕ}
    (w₀ : Fin w) (i₀ : n) (x : X) (u : EuclideanSpace ℂ n) :
    maskedOracle D J₀ Jb N Tn d m K w (Sum.inr false) x (decoder D N Tn d m K w₀ i₀ u) =
      decoder D N Tn d m K w₀ i₀ (J₀ x u) := by
  have h := oracle_branch_packet (ι := Fin w)
    (sourceOracle (m := m) (a := HistAnc n (FlatBasis N n Z Tn d) m K) J₀ Jb false) x
    (EuclideanSpace.single w₀ 1) false (payloadClean D N Tn d m K i₀)
    (payloadClean D N Tn d m K i₀)
    (embed (ancClean D N Tn d m K i₀) (ketL (EuclideanSpace.single (slot0 m) 1) u))
  rw [sourceOracle_false_embed] at h
  rw [decoder_apply, decoder_apply]
  exact h

/-- The preparation program: one call of the initial-state interface. -/
def prepare (D : Data X n Z s) (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (N Tn d m K w : ℕ) : MultiOracleCircuit.Program (maskedOracle D J₀ Jb N Tn d m K w) :=
  .query (Sum.inr false)

omit [DecidableEq Z] in
/-- The preparation program makes exactly one query. -/
theorem prepare_count (D : Data X n Z s)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (N Tn d m K w : ℕ) :
    (prepare D J₀ Jb N Tn d m K w).count = 1 :=
  rfl

omit [DecidableEq Z] in
/-- The one query of the preparation program has the label `false` of the
initial-state interface. -/
theorem prepare_cost (D : Data X n Z s)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (N Tn d m K w : ℕ)
    (wt : ((Fin K × Query) ⊕ Bool) → ℕ) :
    (prepare D J₀ Jb N Tn d m K w).cost wt = wt (Sum.inr false) :=
  rfl

/-- The norm of the encoded seed. -/
theorem norm_seed (D : Data X n Z s) (N Tn d m K : ℕ) {w : ℕ} (w₀ : Fin w) (i₀ : n)
    (seed : EuclideanSpace ℂ n) (hseed : ‖seed‖ = 1) :
    ‖decoder D N Tn d m K w₀ i₀ seed‖ = 1 :=
  (norm_decoder D N Tn d m K w₀ i₀ seed).trans hseed

/-- **The protocol at `T = 0`**: the encoded seed, one call of `J₀`, the fixed
decoder, damping, randomized amplification with gain `1` and at most four
attempts.  It depends only on the public data. -/
def protocol (D : Data X n Z s) (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (hseed : ‖seed‖ = 1) (N Tn d m K : ℕ) {w : ℕ} (w₀ : Fin w)
    (i₀ : n) :
    ODERepeatProtocol.Protocol (physicalOracle D J₀ Jb N Tn d m K w) (EuclideanSpace ℂ n) :=
  Amplify.protocol (prepare D J₀ Jb N Tn d m K w) (decoder D N Tn d m K w₀ i₀)
    (decoder_isometry D N Tn d m K w₀ i₀) (decoder D N Tn d m K w₀ i₀ seed)
    (norm_seed D N Tn d m K w₀ i₀ seed hseed) 1 le_rfl

/-- Worst-case weighted cost: at most `40` times the weight of the initial-state
interface. -/
theorem protocol_worstCost_le (D : Data X n Z s)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (seed : EuclideanSpace ℂ n)
    (hseed : ‖seed‖ = 1) (N Tn d m K : ℕ) {w : ℕ} (w₀ : Fin w) (i₀ : n)
    (wt : ((Fin K × Query) ⊕ Bool) → ℕ) :
    ((protocol D J₀ Jb seed hseed N Tn d m K w₀ i₀).worstCost wt : ℝ) ≤
      40 * (wt (Sum.inr false) : ℝ) := by
  have h := Amplify.protocol_worstCost (prepare D J₀ Jb N Tn d m K w)
    (decoder D N Tn d m K w₀ i₀) (decoder_isometry D N Tn d m K w₀ i₀)
    (decoder D N Tn d m K w₀ i₀ seed) (norm_seed D N Tn d m K w₀ i₀ seed hseed) 1 le_rfl wt
  rw [mul_one, prepare_cost] at h
  exact h

/-- No native matrix query in any history. -/
theorem protocol_matrix (D : Data X n Z s)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (seed : EuclideanSpace ℂ n)
    (hseed : ‖seed‖ = 1) (N Tn d m K : ℕ) {w : ℕ} (w₀ : Fin w) (i₀ : n) :
    (protocol D J₀ Jb seed hseed N Tn d m K w₀ i₀).worstCost
      (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = 0 := by
  have h := protocol_worstCost_le D J₀ Jb seed hseed N Tn d m K w₀ i₀
    (ODESourceQueryBudget.matrixWeight (fun _ => 1))
  have h0 : ODESourceQueryBudget.matrixWeight (L := Fin K × Query) (fun _ => 1)
      (Sum.inr false) = 0 := rfl
  rw [h0, Nat.cast_zero, mul_zero] at h
  exact_mod_cast le_antisymm h (Nat.cast_nonneg _)

/-- No call of the forcing interface in any history. -/
theorem protocol_forcing (D : Data X n Z s)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (seed : EuclideanSpace ℂ n)
    (hseed : ‖seed‖ = 1) (N Tn d m K : ℕ) {w : ℕ} (w₀ : Fin w) (i₀ : n) :
    (protocol D J₀ Jb seed hseed N Tn d m K w₀ i₀).worstCost
      (ODESourceQueryBudget.sourceWeight true) = 0 := by
  have h := protocol_worstCost_le D J₀ Jb seed hseed N Tn d m K w₀ i₀
    (ODESourceQueryBudget.sourceWeight true)
  have h0 : ODESourceQueryBudget.sourceWeight (L := Fin K × Query) true (Sum.inr false) = 0 :=
    rfl
  rw [h0, Nat.cast_zero, mul_zero] at h
  exact_mod_cast le_antisymm h (Nat.cast_nonneg _)

/-- At most `40` calls of the initial-state interface in any history. -/
theorem protocol_initial (D : Data X n Z s)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (seed : EuclideanSpace ℂ n)
    (hseed : ‖seed‖ = 1) (N Tn d m K : ℕ) {w : ℕ} (w₀ : Fin w) (i₀ : n) :
    (protocol D J₀ Jb seed hseed N Tn d m K w₀ i₀).worstCost
      (ODESourceQueryBudget.sourceWeight false) ≤ 40 := by
  have h := protocol_worstCost_le D J₀ Jb seed hseed N Tn d m K w₀ i₀
    (ODESourceQueryBudget.sourceWeight false)
  have h1 : ODESourceQueryBudget.sourceWeight (L := Fin K × Query) false (Sum.inr false) = 1 :=
    rfl
  rw [h1, Nat.cast_one, mul_one] at h
  exact_mod_cast h

/-- **Correctness at `T = 0`.** For every input with `x₀ ≠ 0` and
`J₀ x seed = x₀/‖x₀‖`, and every `ε ≥ 0`, the guarantee `Amplify.Outcome` holds
for the target `x(0)`. -/
theorem protocol_outcome (D : Data X n Z s)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y)) (seed : EuclideanSpace ℂ n)
    (hseed : ‖seed‖ = 1) (N Tn d m K : ℕ) {w : ℕ} (w₀ : Fin w) (i₀ : n) (x : X)
    (v b : EuclideanSpace ℂ n) (hv : v ≠ 0) (hJv : J₀ x seed = unitDirection v) (ε : ℝ)
    (hε : 0 ≤ ε) :
    Amplify.Outcome (protocol D J₀ Jb seed hseed N Tn d m K w₀ i₀) x
      (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b 0) ε := by
  rw [ODEConstantForcing.solution_zero]
  have hdec : ((decoder D N Tn d m K w₀ i₀)†)
      ((prepare D J₀ Jb N Tn d m K w).eval x (decoder D N Tn d m K w₀ i₀ seed)) =
        unitDirection v := by
    change ((decoder D N Tn d m K w₀ i₀)†) (maskedOracle D J₀ Jb N Tn d m K w (Sum.inr false) x
      (decoder D N Tn d m K w₀ i₀ seed)) = _
    rw [query_decoder, decoder_adjoint_apply, hJv]
  have hunit : ‖unitDirection v‖ = 1 := unitDirection_norm v hv
  refine Amplify.outcome (prepare D J₀ Jb N Tn d m K w)
    (maskedOracle_unitary D J₀ Jb hJ₀ hJb N Tn d m K w) (decoder D N Tn d m K w₀ i₀)
    (decoder_isometry D N Tn d m K w₀ i₀) (decoder D N Tn d m K w₀ i₀ seed)
    (norm_seed D N Tn d m K w₀ i₀ seed hseed) 1 le_rfl x v hv ε ?_ ?_
  · rw [hdec, hunit]
    norm_num
  · refine ⟨1, norm_one, ?_⟩
    rw [hdec, one_smul, unitDirection_of_norm_eq_one hunit, sub_self, norm_zero]
    exact hε

end ZeroTime

variable {n : Type} [Fintype n] [DecidableEq n]
variable {X Z : Type} [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

omit [DecidableEq n] in
/-- A unit seed forces a nonempty system index set. -/
theorem nonempty_of_norm_seed {seed : EuclideanSpace ℂ n} (hseed : ‖seed‖ = 1) : Nonempty n := by
  by_contra h
  rw [not_nonempty_iff] at h
  have h0 : seed = 0 := by
    ext i
    exact (IsEmpty.false i).elim
  rw [h0, norm_zero] at hseed
  exact zero_ne_one hseed

/-- **Theorem `ode:thm:general`, the case `T = 0`** (direct state preparation).
In the physical oracle model with any parameters and at least one branch, one
protocol (`ZeroTime.protocol`: one call of `J₀` on the encoded seed, damped and
amplified), chosen before the input, makes in every history no native matrix
query, no forcing call and at most `40` calls of the initial-state interface;
for every input with `x₀ ≠ 0` and `J₀ x seed = x₀/‖x₀‖` and every `ε ≥ 0` it
succeeds with probability at least `175/256 > 2/3`, with conditional output a
density operator within trace distance `ε` of `x(0)/‖x(0)‖`. -/
theorem general_zero (D : Data X n Z s) (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hseed : ‖seed‖ = 1) (N Tn d m K w : ℕ) (hw : 0 < w) :
    ∃ prot : ODERepeatProtocol.Protocol (physicalOracle D J₀ Jb N Tn d m K w)
        (EuclideanSpace ℂ n),
      prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = 0 ∧
      prot.worstCost (ODESourceQueryBudget.sourceWeight true) = 0 ∧
      prot.worstCost (ODESourceQueryBudget.sourceWeight false) ≤ 40 ∧
      ∀ (x : X) (v b : EuclideanSpace ℂ n), v ≠ 0 → J₀ x seed = unitDirection v →
        ∀ ε : ℝ, 0 ≤ ε →
          Amplify.Outcome prot x
            (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b 0) ε := by
  obtain ⟨i₀⟩ := nonempty_of_norm_seed hseed
  refine ⟨ZeroTime.protocol D J₀ Jb seed hseed N Tn d m K (⟨0, hw⟩ : Fin w) i₀,
    ZeroTime.protocol_matrix D J₀ Jb seed hseed N Tn d m K _ i₀,
    ZeroTime.protocol_forcing D J₀ Jb seed hseed N Tn d m K _ i₀,
    ZeroTime.protocol_initial D J₀ Jb seed hseed N Tn d m K _ i₀, ?_⟩
  intro x v b hv hJv ε hε
  exact ZeroTime.protocol_outcome D J₀ Jb hJ₀ hJb seed hseed N Tn d m K _ i₀ x v b hv hJv ε hε

/-- **Theorem `ode:thm:general` for every `T ≥ 0`.**  With the parameters of
`Plan` and the hypotheses of `general`, one protocol, chosen before the input,
makes at most `matrixBudget` native matrix queries and `sourceBudget` calls of
each source interface for `T > 0`, and no matrix query, no forcing call and at
most `40` initial-state calls for `T = 0`; on every input satisfying the
instance hypotheses of `Outcome` it has the guarantee `Amplify.Outcome`. -/
theorem general_nonneg (f : ℝ → ℝ → ℝ) (q₀ : ℝ) (hsolver : BlockSolver f q₀)
    (hq₀ : 0 < q₀) (hq₀1 : q₀ ≤ 1) (D : Data X n Z s) (Λ T Cbar g ε r₀ rb : ℝ)
    (hΛ : 0 < Λ) (hT : 0 ≤ T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hA : ∀ x, ‖matrixOperator (D.matrix x)‖ ≤ Λ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hseed : ‖seed‖ = 1) :
    ∃ (Tn d w : ℕ) (prot : ODERepeatProtocol.Protocol
        (physicalOracle D J₀ Jb (Plan.arcDegree Λ T Cbar g ε) Tn d (Plan.steps Λ T)
          (Plan.degree Λ T Cbar g ε) w) (EuclideanSpace ℂ n)),
      (prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
          (if T = 0 then 0 else matrixBudget f q₀ s Λ T Cbar g ε) ∧
      (∀ b : Bool, (prot.worstCost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤
          (if T = 0 then (if b then 0 else 40) else sourceBudget f q₀ Λ T Cbar g ε)) ∧
      ∀ (x : X) (v b : EuclideanSpace ℂ n), ‖v‖ = r₀ → ‖b‖ = rb →
        (v ≠ 0 → J₀ x seed = unitDirection v) → (b ≠ 0 → Jb x seed = unitDirection b) →
        (∀ t, 0 ≤ t → t ≤ T →
          ‖NormedSpace.exp (t • ODEPublicSourceMesh.generator D x)‖ ≤ Cbar) →
        (∀ t, 0 ≤ t → t ≤ T →
          ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b t‖ ≤
            g * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖) →
        ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 →
        Amplify.Outcome prot x
          (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T) ε := by
  by_cases hT0 : T = 0
  · subst hT0
    obtain ⟨prot, h1, h2, h3, h4⟩ := general_zero D J₀ Jb hJ₀ hJb seed hseed
      (Plan.arcDegree Λ 0 Cbar g ε) 0 0 (Plan.steps Λ 0) (Plan.degree Λ 0 Cbar g ε) 1 one_pos
    refine ⟨0, 0, 1, prot, ?_, ?_, ?_⟩
    · rw [if_pos rfl, h1, Nat.cast_zero]
    · intro b
      rw [if_pos rfl]
      cases b
      · rw [if_neg Bool.false_ne_true]
        exact_mod_cast h3
      · rw [if_pos rfl, h2, Nat.cast_zero]
    · intro x v b _ _ hJv _ _ _ hne
      have hv : v ≠ 0 := by rwa [ODEConstantForcing.solution_zero] at hne
      exact h4 x v b hv (hJv hv) ε hε.le
  · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
    obtain ⟨Tn, d, w, prot, h1, h2, h3⟩ := general f q₀ hsolver hq₀ hq₀1 D Λ T Cbar g ε r₀ rb
      hΛ hTpos hC hg hε hε1 hA J₀ Jb hJ₀ hJb seed hseed
    refine ⟨Tn, d, w, prot, ?_, ?_, h3⟩
    · rw [if_neg hT0]
      exact h1
    · intro b
      rw [if_neg hT0]
      exact h2 b

end

end SparseHamiltonian.GeneralODE
