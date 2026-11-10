import DysonSingleProgram.Explicit.Compile
import ODELowerBoundExtensions.Dyson.Theorem

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Lemma `odel:lem:dyson` with the amplification shape of its trials

Manuscript: Lemma `odel:lem:dyson`, eq. `odel:eq:dyson` and the proof. The released
statement `ODELowerBoundExtensions.Dyson.dyson` asserts the existence of one public trial family
satisfying the complete certificate `ODECompleteTrial.Certificate`. Its trial family is the
compiled counted amplification of the Dyson preparation (proof of Lemma `odel:lem:dyson`):
`ODECoordinateNativeControl.compile … (TimeDependentODE.SourceTD.publicLogicalTrials … j)`.

`GroverOutcome` is the second half of `Dyson.Outcome` with, in addition, the amplification shape
of the trial family (`GroverShape`, preparation and three fixed unitaries, matrix counts); the
first half (the bound `dysonBound`) is `bound_le_dysonBound` (from the released `shape_eq`,
`lcuMass_le`, `cost_le_dysonBound`). `dyson_grover` proves it under the hypotheses of
`Dyson.dyson`, with the same public trial family, seed and output (`Explicit.groverShape_compile`
for the shape; the certificate as in the proof of `Dyson.dyson`).

`outcome_of_groverOutcome`: `GroverOutcome` with the bound of eq. `odel:eq:dyson` gives
`Dyson.Outcome` (forget the preparation, the fixed unitaries and the shape); `dyson_of_grover`
recovers the conclusion of `Dyson.dyson` from `dyson_grover` and `bound_le_dysonBound`, without
`Dyson.dyson`.
-/

namespace DysonSingleProgram.Explicit

noncomputable section

open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set
open MeasureTheory TimeDependentExtensions ODELowerBoundExtensions.Dyson
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE)
open scoped InnerProduct BigOperators

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s Ks : ℕ}

/-- **The outcome of Lemma `odel:lem:dyson` with the amplification shape**: one public trial
family over the Dyson access, with a public preparation program and three fixed unitaries giving
its amplification shape (matrix counts), unitary trials, a public seed and output, satisfying the
released complete certificate for every valid instance of the time-dependent class. -/
def GroverOutcome (D : Data (X × Fin Ks) n Z s) {M : ℕ} (σ : Fin M → Fin Ks) (t : ℕ → ℝ)
    (T g ε r₀ : ℝ) (rb : Fin M → ℝ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (q : ℕ → MultiOracleCircuit.Program (oracle D (dysonDegree D T g ε) M J₀ Jb))
    (ψ : DysonSpace Ks n Z (dysonDegree D T g ε) M)
    (F : EuclideanSpace ℂ n →L[ℂ] DysonSpace Ks n Z (dysonDegree D T g ε) M)
    (a : MultiOracleCircuit.Program (oracle D (dysonDegree D T g ε) M J₀ Jb))
    (U₁ U₂ U₃ : DysonSpace Ks n Z (dysonDegree D T g ε) M →L[ℂ]
      DysonSpace Ks n Z (dysonDegree D T g ε) M),
    GroverShape q (ODESourceQueryBudget.matrixWeight (fun _ => 1)) a
      (ODESourceQueryBudget.matrixWeight (fun _ => 1)) U₁ U₂ U₃ ∧
    (∀ j x, IsUnitary ((q j).eval x)) ∧
    ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bs : Fin M → EuclideanSpace ℂ n) (bmax : ℝ),
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      (∀ r : Fin M, Accretive (SparseStateOverlap.matrixOperator (D.matrix (x, σ r)))) →
      (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) →
      (∀ r : Fin M, IntervalIntegrable (b r) volume (t r) (t ((r : ℕ) + 1))) →
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ‖b r u‖ ≤ bmax) →
      (∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) →
      ‖sol 0‖ = r₀ → (∀ r, ‖bs r‖ = rb r) →
      (sol 0 ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ r, bs r ≠ 0 → Jb x r seed = ODEStateNormalization.unitDirection (bs r)) →
      MeshSampling.mass r₀ t rb ≤ g * ‖sol T‖ →
      (r₀ + bmax * T) * (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
          ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, σ r))‖) +
        (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖b r u - bs r‖) +
        (s : ℝ) * D.scale * (∑ q : Fin M, (t ((q : ℕ) + 1) - t q) ^ 2 * rb q) / 2 ≤
          ε * MeshSampling.mass r₀ t rb / (2000 * g) →
      ODECompleteTrial.Certificate q
        (ODEGroverAverage.chosenIterations (ampFactor D t T g ε r₀ rb)) ψ F x (sol T)
        (s : ℝ) 0 (shapeLength D T g ε) (ampFactor D t T g ε r₀ rb) ε

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **Lemma `odel:lem:dyson` with the amplification shape** (Lemma `odel:lem:dyson`): under the
hypotheses of `ODELowerBoundExtensions.Dyson.dyson`, the released Dyson trial family has the
amplification shape and satisfies the released complete certificate on every valid instance. -/
theorem dyson_grover (D : Data (X × Fin Ks) n Z s) {M : ℕ} (hM : 0 < M) (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T g ε r₀ : ℝ) (rb : Fin M → ℝ) (hmesh : IsMesh t M T) (hT : 0 < T)
    (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) (h₀ : 0 ≤ r₀) (hb : ∀ r, 0 ≤ rb r)
    (hB : 0 < MeshSampling.mass r₀ t rb)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x r, IsUnitary (Jb x r))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    GroverOutcome D σ t T g ε r₀ rb J₀ Jb seed := by
  have hKs : 0 < Ks := Fin.pos (σ ⟨0, hM⟩)
  have hrate : 0 < rate D := mul_pos (Nat.cast_pos.mpr D.slots_pos) D.scale_pos
  have hz : 0 < rate D * T := mul_pos hrate hT
  have ht : Monotone t := hmesh.mono
  have hlcu : MeshSampling.mass r₀ t rb ≤ lcuMass (rate D) t (dysonDegree D T g ε) M r₀ rb :=
    mass_le_lcuMass (rate D) t _ M r₀ rb hrate.le h₀ ht hb
  have hamp : ampFactor D t T g ε r₀ rb =
      g * (lcuMass (rate D) t (dysonDegree D T g ε) M r₀ rb / MeshSampling.mass r₀ t rb) :=
    mul_div_assoc _ _ _
  have hg' : 1 ≤ ampFactor D t T g ε r₀ rb := by
    rw [hamp]
    have h1 : 1 ≤ lcuMass (rate D) t (dysonDegree D T g ε) M r₀ rb / MeshSampling.mass r₀ t rb :=
      (one_le_div hB).mpr hlcu
    nlinarith
  obtain ⟨i₀⟩ : Nonempty n := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have h0 : seed = 0 := by
      ext i
      exact isEmptyElim i
    rw [h0, norm_zero] at hSeed
    exact zero_ne_one hSeed
  obtain ⟨p, hp⟩ : ∃ p, p = select hM hKs σ D (dysonDegree D T g ε) := ⟨_, rfl⟩
  obtain ⟨E, hEe⟩ : ∃ E, E = encoding (M := M) hKs D (dysonDegree D T g ε) := ⟨_, rfl⟩
  have hE : E† ∘L E = 1 := by rw [hEe]; exact encoding_isometry hKs D _
  obtain ⟨d, hde⟩ : ∃ d, d = dysonCoeff (rate D) t (dysonDegree D T g ε) M r₀ rb := ⟨_, rfl⟩
  have hdm : ODECoherentLCU.coefficientMass d =
      2 * lcuMass (rate D) t (dysonDegree D T g ε) M r₀ rb := by
    rw [hde]; exact coefficientMass_dysonCoeff (rate D) t _ M r₀ rb hrate.le h₀ ht hb
  have hd : 0 < ODECoherentLCU.coefficientMass d := by rw [hdm]; linarith
  have hO : ∀ l x, IsUnitary (matrixOracle (Omega (dysonDegree D T g ε) M) D l x) :=
    matrixOracle_unitary (Omega (dysonDegree D T g ε) M) D
  let ω₀ : Omega (dysonDegree D T g ε) M := ((none, Sum.inr false), fun _ => false)
  let a0 : Lab (dysonDegree D T g ε) M × n := ((none, Sum.inr false), i₀)
  have hψs : ‖ODECompiledSource.seed E d seed‖ = 1 :=
    ODECompiledSource.seed_unit E d hE hd seed hSeed
  have hFs : (ODECompiledSource.output E d)† ∘L ODECompiledSource.output E d = 1 :=
    ODECompiledSource.output_isometry E d hE hd
  refine ⟨fun j => ODECoordinateNativeControl.compile (sourceLayout (dysonDegree D T g ε) M n)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (Omega (dysonDegree D T g ε) M))
      (matrixOracle (Omega (dysonDegree D T g ε) M) D)
      (TimeDependentODE.SourceTD.sourceFamily (ι := LabelI (dysonDegree D T g ε) M) J₀ Jb)
      a0 (matrixClean hKs D ω₀)
      (TimeDependentODE.SourceTD.publicLogicalTrials p J₀ Jb E hE d seed hψs hFs j),
    ODECoordinateNativeControl.input (sourceLayout (dysonDegree D T g ε) M n)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (Omega (dysonDegree D T g ε) M))
      a0 (matrixClean hKs D ω₀) (ODECompiledSource.seed E d seed),
    ODECoordinateNativeControl.input (sourceLayout (dysonDegree D T g ε) M n)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (Omega (dysonDegree D T g ε) M))
      a0 (matrixClean hKs D ω₀) ∘L ODECompiledSource.output E d,
    ODECoordinateNativeControl.compile (sourceLayout (dysonDegree D T g ε) M n)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (Omega (dysonDegree D T g ε) M))
      (matrixOracle (Omega (dysonDegree D T g ε) M) D)
      (TimeDependentODE.SourceTD.sourceFamily (ι := LabelI (dysonDegree D T g ε) M) J₀ Jb)
      a0 (matrixClean hKs D ω₀) (TimeDependentODE.SourceTD.program p J₀ Jb E hE),
    SubspaceOracle.lift (ODECoordinateNativeControl.input (sourceLayout (dysonDegree D T g ε) M n)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (Omega (dysonDegree D T g ε) M))
      a0 (matrixClean hKs D ω₀)) (-1),
    SubspaceOracle.lift (ODECoordinateNativeControl.input (sourceLayout (dysonDegree D T g ε) M n)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (Omega (dysonDegree D T g ε) M))
      a0 (matrixClean hKs D ω₀))
      (PhaseSubspaceGates.phase (ODEGroverRay.projector (ODECompiledSource.seed E d seed)) (-1)),
    SubspaceOracle.lift (ODECoordinateNativeControl.input (sourceLayout (dysonDegree D T g ε) M n)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (Omega (dysonDegree D T g ε) M))
      a0 (matrixClean hKs D ω₀))
      (PhaseSubspaceGates.phase (ODEHeraldedSuccess.successProjector
        (ODECompiledSource.output E d)) (-1)), ?_, ?_, ?_⟩
  · exact groverShape_compile
      (ODECoordinateNativeControl.input (sourceLayout (dysonDegree D T g ε) M n)
        (matrixLayout (n := n) (Z := Z) (Ks := Ks) (Omega (dysonDegree D T g ε) M))
        a0 (matrixClean hKs D ω₀))
      (ODECoordinateNativeControl.input_isometry (sourceLayout (dysonDegree D T g ε) M n)
        (matrixLayout (n := n) (Z := Z) (Ks := Ks) (Omega (dysonDegree D T g ε) M))
        a0 (matrixClean hKs D ω₀))
      (ODECoordinateNativeControl.letter (sourceLayout (dysonDegree D T g ε) M n)
        (matrixLayout (n := n) (Z := Z) (Ks := Ks) (Omega (dysonDegree D T g ε) M))
        (matrixOracle (Omega (dysonDegree D T g ε) M) D)
        (TimeDependentODE.SourceTD.sourceFamily (ι := LabelI (dysonDegree D T g ε) M) J₀ Jb)
        (matrixClean hKs D ω₀))
      (TimeDependentODE.SourceTD.program p J₀ Jb E hE)
      (ODEGroverRay.projector (ODECompiledSource.seed E d seed))
      (ODEHeraldedSuccess.successProjector (ODECompiledSource.output E d))
      (ODEGroverRay.projector_isOrthogonalProjection _ hψs)
      (ODEHeraldedSuccess.successProjector_isOrthogonalProjection _ hFs)
      (ODESourceQueryBudget.matrixWeight (fun _ => 1))
  · intro j x
    exact MultiOracleCircuit.Program.eval_unitary _
      (ODECoordinateNativeControl.physicalOracle_unitary _ _ _ _ hO
        (TimeDependentODE.SourceTD.sourceFamily_unitary J₀ Jb hJ₀ hJb)) x
  intro x G b sol bs bmax hG hAcc hGint hbint hbmax hsol hs0 hbs hJ0 hJb' hmass hcert
  have htarget : sol T ≠ 0 := by
    intro h
    rw [h, norm_zero, mul_zero] at hmass
    linarith
  have hJn : ∀ q, ‖TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x) q seed‖ ≤ 1 := by
    intro q
    cases q with
    | none => exact le_of_eq ((ContinuousLinearMap.norm_map_of_mem_unitary
      (Unitary.mem_iff.mpr (hJ₀ x)) seed).trans hSeed)
    | some r => exact le_of_eq ((ContinuousLinearMap.norm_map_of_mem_unitary
      (Unitary.mem_iff.mpr (hJb x r)) seed).trans hSeed)
  have hdec : ODEJointSourceLCU.decoded E d
      (fun a => TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x) a.1) (p.eval x) seed =
      ((2 * lcuMass (rate D) t (dysonDegree D T g ε) M r₀ rb : ℝ) : ℂ)⁻¹ •
        lcuTarget (K := dysonDegree D T g ε) σ D t r₀ rb x
          (TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x)) seed := by
    rw [hp, hEe, decoded_select hM hKs σ D _ x d hd, hdm, hde]
    rfl
  have hy : ‖lcuTarget (K := dysonDegree D T g ε) σ D t r₀ rb x
      (TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x)) seed‖ ≤
      lcuMass (rate D) t (dysonDegree D T g ε) M r₀ rb :=
    lcuTarget_norm_le σ D t r₀ rb x _ seed hJn h₀ ht hb
  have herr := lcuTarget_error (K := dysonDegree D T g ε) hM σ D hmesh g ε r₀ rb hg hε
    (expTail_truncDegree_le _ g ε hz hg hε hε1) x G b sol bs bmax hG hAcc hGint hbint hbmax
    hsol hs0 hbs (TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x)) seed hJ0 hJb' hcert
  obtain ⟨h1, h2, h3⟩ := herald_bounds _ (sol T) _ _ g ε hB hlcu hg hε hε1 hmass hy herr
  have hcount : 10 * (p.count : ℝ) ≤
      106168320 * ImprovedODEQueryBudget.queryShape (s : ℝ) 0 (shapeLength D T g ε) := by
    rw [hp, select_count, queryShape_zero]
    unfold shapeLength
    push_cast
    apply le_of_eq
    ring
  exact certificate_of_herald p hO J₀ Jb hJ₀ hJb E hE d hd seed hSeed
    (sourceLayout (dysonDegree D T g ε) M n)
    (matrixLayout (n := n) (Z := Z) (Ks := Ks) (Omega (dysonDegree D T g ε) M))
    a0 (matrixClean hKs D ω₀) (matrixImage hKs D ω₀) (matrix_valid hKs D ω₀)
    (s : ℝ) (shapeLength D T g ε) (ampFactor D t T g ε r₀ rb) ε hg' hε.le hcount x (sol T)
    htarget (by rw [hdec]; exact h1) (by rw [hdec]; exact h2) (by rw [hdec]; exact h3)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **The bound of eq. `odel:eq:dyson` on the released query shape**: the first conjunct of
`ODELowerBoundExtensions.Dyson.Outcome`, from the released `shape_eq`, `lcuMass_le` and
`cost_le_dysonBound` (not from `Dyson.dyson`). -/
theorem bound_le_dysonBound (D : Data (X × Fin Ks) n Z s) {M : ℕ} (t : ℕ → ℝ) (T g ε r₀ : ℝ)
    (rb : Fin M → ℝ) (hmesh : IsMesh t M T) (hT : 0 < T) (hg : 1 ≤ g) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (h₀ : 0 ≤ r₀) (hb : ∀ r, 0 ≤ rb r) (hB : 0 < MeshSampling.mass r₀ t rb) :
    1274019840 * ampFactor D t T g ε r₀ rb *
        ImprovedODEQueryBudget.queryShape (s : ℝ) 0 (shapeLength D T g ε) ≤
      dysonBound (rate D * T) g ε := by
  have hrate : 0 < rate D := mul_pos (Nat.cast_pos.mpr D.slots_pos) D.scale_pos
  have hlcu' : lcuMass (rate D) t (dysonDegree D T g ε) M r₀ rb ≤
      MeshSampling.mass r₀ t rb * Real.exp (rate D * T) :=
    lcuMass_le (rate D) _ hmesh r₀ rb hrate.le h₀ hb
  rw [shape_eq, ampFactor, mul_div_assoc]
  exact cost_le_dysonBound (rate D * T) g ε _ (mul_pos hrate hT) hg hε hε1
    ((div_le_iff₀ hB).mpr (by rw [mul_comm]; exact hlcu'))

omit [DecidableEq Z] in
/-- **`GroverOutcome` contains the released outcome**: with the bound of eq. `odel:eq:dyson`
(the first conjunct of `ODELowerBoundExtensions.Dyson.Outcome`), forgetting the preparation, the
three fixed unitaries and the amplification shape gives `Dyson.Outcome`. -/
theorem outcome_of_groverOutcome (D : Data (X × Fin Ks) n Z s) {M : ℕ} (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T g ε r₀ : ℝ) (rb : Fin M → ℝ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n)
    (hbound : 1274019840 * ampFactor D t T g ε r₀ rb *
        ImprovedODEQueryBudget.queryShape (s : ℝ) 0 (shapeLength D T g ε) ≤
      dysonBound (rate D * T) g ε)
    (h : GroverOutcome D σ t T g ε r₀ rb J₀ Jb seed) :
    Outcome D σ t T g ε r₀ rb J₀ Jb seed := by
  obtain ⟨q, ψ, F, _, _, _, _, _, hU, hcert⟩ := h
  exact ⟨hbound, q, ψ, F, hU, hcert⟩

/-- **The released Lemma `odel:lem:dyson` from its explicit form**: under the hypotheses of
`ODELowerBoundExtensions.Dyson.dyson`, `Dyson.Outcome` follows from `dyson_grover` and
`bound_le_dysonBound` (no use of `Dyson.dyson`). The trial family of `dyson_grover` is therefore
a trial family for `Dyson.dyson`. -/
theorem dyson_of_grover (D : Data (X × Fin Ks) n Z s) {M : ℕ} (hM : 0 < M) (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T g ε r₀ : ℝ) (rb : Fin M → ℝ) (hmesh : IsMesh t M T) (hT : 0 < T)
    (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) (h₀ : 0 ≤ r₀) (hb : ∀ r, 0 ≤ rb r)
    (hB : 0 < MeshSampling.mass r₀ t rb)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x r, IsUnitary (Jb x r))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    Outcome D σ t T g ε r₀ rb J₀ Jb seed :=
  outcome_of_groverOutcome D σ t T g ε r₀ rb J₀ Jb seed
    (bound_le_dysonBound D t T g ε r₀ rb hmesh hT hg hε hε1 h₀ hb hB)
    (dyson_grover D hM σ t T g ε r₀ rb hmesh hT hg hε hε1 h₀ hb hB J₀ Jb hJ₀ hJb seed hSeed)

end

end DysonSingleProgram.Explicit
