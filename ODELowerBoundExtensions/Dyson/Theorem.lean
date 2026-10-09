import ODELowerBoundExtensions.Dyson.Target
import ODELowerBoundExtensions.Dyson.Herald
import ODELowerBoundExtensions.Dyson.Trials

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Lemma `odel:lem:dyson`: the fixed-parameter precision obstruction (Dyson solver)

Manuscript, lines 4155-4254 (Lemma
`odel:lem:dyson`, eq. `odel:eq:dyson`, proof): under the coherent time access, certified time
discretisation and source preparation of Theorem `ode:thm:time`, there is a generic
sparse-oracle solver with `Q_A = O(ḡ e^z [1 + z + L_g/log(e + L_g/z)])` matrix queries,
`z = s η T`, `L_g = log(C ḡ/ε)`.

**Input class** (the data and certificate shape of `TimeDependentExtensions.ODE.solver`,
generalised by the cell-to-sample map `σ`, with per-instance accretivity of the used samples in
place of the release's energy bounds): time-indexed native data
`D : Data (X × Fin Kₛ) n Z s` (entries bounded by the public `Λ = D.scale`, the `η` of the
lemma), a public mesh `t` with `M` cells and a public reversible cell-to-sample map
`σ : Fin M → Fin Kₛ` ("coherent matrix access on every finite mesh selected from the public
regularity certificate", lines 4156-4159, 4191-4196), public source norms `r₀`, `rb`, the
supplied source interfaces `J₀`, `Jb` and seed. An instance has generator pieces `G_r(u)`,
forcing pieces `b_r(u)`, a solution with `B ≤ g ‖x(T)‖`, accretive samples, and the released
integrated certificate (constant `2000`, without the slot-refinement term, which the Dyson
solver does not need). `dyson_release_class` (`Corollaries.lean`) proves the inclusion: every
instance accepted by the released `TimeDependentExtensions.ODE.Outcome` (`σ = id`, under its
public PSD promise) is accepted by `Outcome`.

**Access** (`oracle`): built with the release builder `ODECoordinateNativeControl.physicalOracle`
used by `MeshSource.physicalOracle`, from the supplied source family
`TimeDependentODE.SourceTD.sourceFamily` and the masked coherent sampled-time native access
(`Access.lean`) in place of the release's aligned Cayley access (`MeshSource.matrixOracle`). Both
are `SparseLowerBounds.ODE.Family.access` up to fixed spectators
(`Release.physicalOracle_normal_form`, `familyLayout_matrix`). All gates are known; register sizes
depend on the mesh and on `K` (as the lemma allows); queries do not.

**Algorithm**: the Dyson LCU of degree `K = truncDegree z g ε` (`Series`, `Slots`, `Flagged`,
`Select`, `Compile`), the released source loading, randomized amplification with cutoff
`chosenIterations g'`, `g' = ampFactor = g · lcuMass/B ≤ g e^z`, and the released four-attempt
wrapper (`Trials`).

**Conclusion** (`Outcome`): one public trial family satisfies the released complete certificate
`ODECompleteTrial.Certificate` (success `≥ 2/3`, conditional density within trace distance `ε`)
for every valid instance, and its worst-case matrix-query bound
`1274019840 g' · queryShape s 0 (K/589824) = 2160 g' K` is at most
`dysonBound z g ε = 16000 g e^z (1 + z + L_g/log(e + L_g/z))` (eq. `odel:eq:dyson`).
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set
open MeasureTheory TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE)
open scoped InnerProduct BigOperators

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s Ks : ℕ}

/-- The block-encoding normalisation `α = s Λ` (`α = s η`, line 4172). -/
def rate (D : Data (X × Fin Ks) n Z s) : ℝ := (s : ℝ) * D.scale

/-- The public truncation degree at `z = s Λ T`. -/
def dysonDegree (D : Data (X × Fin Ks) n Z s) (T g ε : ℝ) : ℕ := truncDegree (rate D * T) g ε

/-- The public amplification parameter `g' = g · lcuMass / B` (`1 ≤ g'/g ≤ e^z`). -/
def ampFactor (D : Data (X × Fin Ks) n Z s) {M : ℕ} (t : ℕ → ℝ) (T g ε r₀ : ℝ)
    (rb : Fin M → ℝ) : ℝ :=
  g * lcuMass (rate D) t (dysonDegree D T g ε) M r₀ rb / MeshSampling.mass r₀ t rb

/-- The shape parameter `ℓ = K/589824` of the released certificate at `Θ = 0`. -/
def shapeLength (D : Data (X × Fin Ks) n Z s) (T g ε : ℝ) : ℝ :=
  (dysonDegree D T g ε : ℝ) / 589824

/-- Flat coordinates of the source-branch space. -/
def sourceLayout (K M : ℕ) (n : Type*) [Fintype n] [DecidableEq n] :
    ODECompiledSource.Branch (LabelI K M) (EuclideanSpace ℂ n) M ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Lab K M × n) :=
  RegisterEquivalences.productFlatten (Lab K M) n

/-- The physical workspace of the Dyson solver. -/
abbrev DysonSpace (Ks : ℕ) (n Z : Type*) [Fintype n] [Fintype Z] (K M : ℕ) : Type _ :=
  ODESectorTensor.Physical (Lab K M × n)
    (Omega K M × NativeControlledOracle.Workspace (PBasis Ks n Z))

/-- **The Dyson access**: the release builder `ODECoordinateNativeControl.physicalOracle` applied
to the masked coherent sampled-time native calls (labels `inl`) and the two supplied source
interfaces (labels `inr`). -/
abbrev oracle (D : Data (X × Fin Ks) n Z s) (K M : ℕ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    Query ⊕ Bool → X → DysonSpace Ks n Z K M →L[ℂ] DysonSpace Ks n Z K M :=
  ODECoordinateNativeControl.physicalOracle (sourceLayout K M n)
    (matrixLayout (n := n) (Z := Z) (Ks := Ks) (Omega K M)) (matrixOracle (Omega K M) D)
    (TimeDependentODE.SourceTD.sourceFamily (ι := LabelI K M) J₀ Jb)

/-- **The outcome of Lemma `odel:lem:dyson`**: the paper-form bound on the released query shape,
and one public trial family, seed and output satisfying the released complete certificate for
every valid instance of the time-dependent class. -/
def Outcome (D : Data (X × Fin Ks) n Z s) {M : ℕ} (σ : Fin M → Fin Ks) (t : ℕ → ℝ)
    (T g ε r₀ : ℝ) (rb : Fin M → ℝ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  1274019840 * ampFactor D t T g ε r₀ rb *
      ImprovedODEQueryBudget.queryShape (s : ℝ) 0 (shapeLength D T g ε) ≤
    dysonBound (rate D * T) g ε ∧
  ∃ (q : ℕ → MultiOracleCircuit.Program (oracle D (dysonDegree D T g ε) M J₀ Jb))
    (ψ : DysonSpace Ks n Z (dysonDegree D T g ε) M)
    (F : EuclideanSpace ℂ n →L[ℂ] DysonSpace Ks n Z (dysonDegree D T g ε) M),
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

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The released worst-case shape at `Θ = 0` is `2160 g' K`. -/
theorem shape_eq (D : Data (X × Fin Ks) n Z s) {M : ℕ} (t : ℕ → ℝ) (T g ε r₀ : ℝ)
    (rb : Fin M → ℝ) :
    1274019840 * ampFactor D t T g ε r₀ rb *
        ImprovedODEQueryBudget.queryShape (s : ℝ) 0 (shapeLength D T g ε) =
      2160 * ampFactor D t T g ε r₀ rb * (dysonDegree D T g ε : ℝ) := by
  rw [queryShape_zero]
  unfold shapeLength
  ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **Lemma `odel:lem:dyson`** (lines 4155-4254): for every public time-indexed native input on
a mesh with a public cell-to-sample map, every `T > 0`, `g ≥ 1`, `0 < ε ≤ 1`, nonnegative public
source norms with positive mass, unitary source interfaces and a unit seed, the Dyson solver
satisfies `Outcome`: the released complete certificate on every valid instance, with worst-case
matrix queries at most `16000 ḡ e^z (1 + z + L_g/log(e + L_g/z))`, `z = s Λ T`,
`L_g = log(4000 ḡ/ε)` (eq. `odel:eq:dyson`). -/
theorem dyson (D : Data (X × Fin Ks) n Z s) {M : ℕ} (hM : 0 < M) (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T g ε r₀ : ℝ) (rb : Fin M → ℝ) (hmesh : IsMesh t M T) (hT : 0 < T)
    (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) (h₀ : 0 ≤ r₀) (hb : ∀ r, 0 ≤ rb r)
    (hB : 0 < MeshSampling.mass r₀ t rb)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x r, IsUnitary (Jb x r))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    Outcome D σ t T g ε r₀ rb J₀ Jb seed := by
  have hKs : 0 < Ks := Fin.pos (σ ⟨0, hM⟩)
  have hrate : 0 < rate D := mul_pos (Nat.cast_pos.mpr D.slots_pos) D.scale_pos
  have hz : 0 < rate D * T := mul_pos hrate hT
  have ht : Monotone t := hmesh.mono
  have hlcu : MeshSampling.mass r₀ t rb ≤ lcuMass (rate D) t (dysonDegree D T g ε) M r₀ rb :=
    mass_le_lcuMass (rate D) t _ M r₀ rb hrate.le h₀ ht hb
  have hlcu' : lcuMass (rate D) t (dysonDegree D T g ε) M r₀ rb ≤
      MeshSampling.mass r₀ t rb * Real.exp (rate D * T) :=
    lcuMass_le (rate D) _ hmesh r₀ rb hrate.le h₀ hb
  have hamp : ampFactor D t T g ε r₀ rb =
      g * (lcuMass (rate D) t (dysonDegree D T g ε) M r₀ rb / MeshSampling.mass r₀ t rb) :=
    mul_div_assoc _ _ _
  have hg' : 1 ≤ ampFactor D t T g ε r₀ rb := by
    rw [hamp]
    have h1 : 1 ≤ lcuMass (rate D) t (dysonDegree D T g ε) M r₀ rb / MeshSampling.mass r₀ t rb :=
      (one_le_div hB).mpr hlcu
    nlinarith
  refine ⟨?_, ?_⟩
  · rw [shape_eq, hamp]
    exact cost_le_dysonBound (rate D * T) g ε _ hz hg hε hε1
      ((div_le_iff₀ hB).mpr (by rw [mul_comm]; exact hlcu'))
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
  refine ⟨fun j => ODECoordinateNativeControl.compile (sourceLayout (dysonDegree D T g ε) M n)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (Omega (dysonDegree D T g ε) M))
      (matrixOracle (Omega (dysonDegree D T g ε) M) D)
      (TimeDependentODE.SourceTD.sourceFamily (ι := LabelI (dysonDegree D T g ε) M) J₀ Jb)
      a0 (matrixClean hKs D ω₀)
      (TimeDependentODE.SourceTD.publicLogicalTrials p J₀ Jb E hE d seed
        (ODECompiledSource.seed_unit E d hE hd seed hSeed)
        (ODECompiledSource.output_isometry E d hE hd) j),
    ODECoordinateNativeControl.input (sourceLayout (dysonDegree D T g ε) M n)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (Omega (dysonDegree D T g ε) M))
      a0 (matrixClean hKs D ω₀) (ODECompiledSource.seed E d seed),
    ODECoordinateNativeControl.input (sourceLayout (dysonDegree D T g ε) M n)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (Omega (dysonDegree D T g ε) M))
      a0 (matrixClean hKs D ω₀) ∘L ODECompiledSource.output E d, ?_, ?_⟩
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

end

end ODELowerBoundExtensions.Dyson
