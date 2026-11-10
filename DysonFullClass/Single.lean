import DysonFullClass.Theorem
import DysonGeneralAccess.Core
import GeneralSourceODE.Oracles
import ODELowerBoundExtensions.Dyson.Family.Mesh

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Lemma `odel:lem:dyson` on the full class: one heralded program, separate source primitives

Manuscript, proof of Lemma `odel:lem:dyson`: "Amplify the actual circuit using its own inverse. A
direct trial covers amplitudes above `1/2` with constant probability; for smaller amplitudes,
randomised amplification with a bounded schedule of `O(e^z ḡ)` calls does so. Mixing the two
trials and repeating a constant number of times gives heralded success probability at least `2/3`
without changing the conditional direction." The public
trial family of `Theorem.full_dyson_shape` is the compiled amplification of one public
preparation; this module turns it into

* `FullSingleOutcome`, `full_single`: **one heralded program** (`DysonGeneralAccess.Model.
  HeraldedSolver`) over the full-class access with spectator registers, for the valid instances
  `FullValid` (success at least `2/3`, conditional accuracy `ε` of the reduced output, readout
  isometry and herald projection fixed before the instance), making at most
  `dysonBound z (c_q ḡ) ε` matrix queries (row, column and value calls, inverses included) and at
  most `40 g'` calls of each supplied source interface (`g' = c_q ḡ e^z`), over the whole program;
* `fullActualOracle`, `fullImplementation`: the access with the supplied source operations as
  three separate primitives `P_w`, `U_load`, `P_w†` (and the public phase gate as a fixed gate);
  `fullImplementation_eval`: the two counted interfaces of `fullOracle` are exactly
  `P_w; U_load; phases` and `P_w†` on these primitives;
* `full_actual`: the released four-attempt protocol over these primitives, with the separate
  worst-case counts of `GeneralSourceODE.Oracles.ActualCertificate` (matrix queries
  `1274019840 g' queryShape s 0 (K/589824) = 2160 g' K`, at most `40 g'` calls of each of `P_w`,
  `U_load`, `P_w†` and `120 g'` source calls in all), for every valid instance.
-/

namespace DysonFullClass

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set
open MeasureTheory TimeDependentExtensions
open SparseHamiltonian.GeneralSourceODE (sources phases phases_norm SourceCall)
open ODELowerBoundExtensions.Dyson
open DysonSingleProgram DysonSingleProgram.Register DysonGeneralAccess DysonGeneralAccess.Model
open scoped InnerProduct BigOperators

variable {X n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s Ks M m : ℕ}

omit [DecidableEq Z] in
theorem fullOracle_unitary (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    {Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))} (hPw : ∀ x, IsUnitary (Pw x))
    {J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n}
    (hJ : ∀ x a, IsUnitary (J x a)) (ω : Fin m → ℂ) :
    ∀ l x, IsUnitary (fullOracle D K M m Pw J ω l x) :=
  ODECoordinateNativeControl.physicalOracle_unitary _ _ _ _
    (matrixOracle_unitary (OmegaG (FLab K M m) K) D)
    (GeneralSourceODE.Compiled.sourceFamily_unitary hPw hJ (phases_norm ω))

/-! ### One heralded program -/

/-- **The single-program outcome on the full class**: a spectator register `Jt`, a garbage
space `G` and one heralded program over `fiberOracle Jt (fullOracle D₀ K M m P_w U_load ω)`
(`K = fullDegree`), with success at least `2/3` and conditional accuracy `ε` on every valid
instance, at most `dysonBound z (c_q ḡ) ε = 16000 c_q ḡ e^z (1 + z + L/log(e + L/z))` matrix
queries (`z = s η T`, `L = log(4000 c_q ḡ/ε)`) and at most `40 c_q ḡ e^z` calls of each counted
source interface. -/
def FullSingleOutcome (D₀ : Data (X × Fin Ks) n Z s) {M : ℕ} (σ : Fin M → Fin Ks) (t : ℕ → ℝ)
    (T η g cq ε : ℝ) (hη : 0 < η) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (Jt : Type) (_ : Fintype Jt) (G : Type) (_ : NormedAddCommGroup G)
    (_ : InnerProductSpace ℂ G) (_ : CompleteSpace G)
    (A : HeraldedSolver (fiberOracle Jt (fullOracle D₀ (fullDegree s η T g cq ε) M m Pw J ω))
      (FullValid D₀ σ t T η g cq ε hη v ω Pw J seed) G ε),
    (A.prog.cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
      dysonBound (zParam s η T) (cq * g) ε ∧
    ∀ b : Bool, (A.prog.cost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤
      40 * fullAmp s η T g cq

/-- **Lemma `odel:lem:dyson` on the full time-dependent class, single-program form**: for every
public specification (time-indexed native access `D₀`, mesh `t` with cell-to-sample map `σ`,
`η > 0`, `T > 0`, `ḡ ≥ 1`, `c_q ≥ 1`, `0 < ε ≤ 1`, nodes `v_i ∈ [0, T]`, weights `ω_i`, unitary
supplied source interfaces and a unit seed) one heralded program solves every valid instance of
`FullValid`, with at most `dysonBound (s η T) (c_q ḡ) ε` matrix queries and at most `40 c_q ḡ e^z`
calls of each source interface over the whole program. -/
theorem full_single (D₀ : Data (X × Fin Ks) n Z s) (hM : 0 < M) (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T η g cq ε : ℝ) (hmesh : IsMesh t M T) (hT : 0 < T) (hη : 0 < η)
    (hg : 1 ≤ g) (hcq : 1 ≤ cq) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (v : Fin m → ℝ) (hv : ∀ i, v i ∈ Icc 0 T) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a)) (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    FullSingleOutcome D₀ σ t T η g cq ε hη v ω Pw J seed := by
  classical
  obtain ⟨i₀⟩ : Nonempty n := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have h0 : seed = 0 := by
      ext i
      exact isEmptyElim i
    rw [h0, norm_zero] at hSeed
    exact zero_ne_one hSeed
  have hs : 0 < s := D₀.slots_pos
  have hcqg : 1 ≤ cq * g := by nlinarith
  have hg1 := one_le_fullAmp (s := s) hη.le hT.le hg hcq
  have hO := fullOracle_unitary D₀ (fullDegree s η T g cq ε) M m hPw hJ ω
  by_cases hV : ∃ x y, FullValid D₀ σ t T η g cq ε hη v ω Pw J seed x y
  · obtain ⟨x₀, y₀, hv₀⟩ := hV
    obtain ⟨q, ψ, F, a, U₁, U₂, U₃, hshape, hshapeS, hψ, hF, -, hcert⟩ :=
      full_dyson_shape D₀ hM σ t T η g cq ε hmesh hT hη hg hcq hε hε1 v hv ω Pw hPw J hJ seed
        hSeed
    have c := hcert x₀ y₀ hv₀
    refine ⟨_, _, _, _, _, _, Core.single hO q _ c.trial.cutoff_pos ψ hψ F hF i₀ a
      (ODESourceQueryBudget.matrixWeight (fun _ => 1)) hshape
      (FullValid D₀ σ t T η g cq ε hη v ω Pw J seed) (s : ℝ) 0
      (fullShape (fullDegree s η T g cq ε)) (fullAmp s η T g cq) ε hcert, ?_, ?_⟩
    · exact (Core.single_matrix_le hO q _ c.trial.cutoff_pos ψ hψ F hF i₀ a _ hshape _ _ _ _ _ _
        hcert x₀ y₀ hv₀).trans (full_bound hs hT hη hg hcq hε hε1)
    · intro b
      rw [Core.single_cost]
      have hpos := c.trial.cutoff_pos
      have hq := c.trial.source_queries
        (ODEGroverAverage.chosenIterations (fullAmp s η T g cq) - 1) (by omega) b
      rw [(hshapeS b).cost_eq] at hq
      push_cast at hq ⊢
      linarith
  · push Not at hV
    refine ⟨Unit, inferInstance,
      SparseLowerBounds.Joint Unit (FSpace Ks n Z (fullDegree s η T g cq ε) M m),
      inferInstance, inferInstance, inferInstance, HeraldedSolver.trivial i₀ hV, ?_, ?_⟩
    · rw [HeraldedSolver.trivial_prog, MultiOracleCircuit.Program.cost_identity, Nat.cast_zero]
      exact dysonBound_nonneg (zParam_pos hs hη hT).le hcqg hε hε1
    · intro b
      rw [HeraldedSolver.trivial_prog, MultiOracleCircuit.Program.cost_identity, Nat.cast_zero]
      linarith

/-! ### The supplied source operations as separate primitives -/

/-- **The actual primitive oracles of the full-class solver**: the masked native calls of `D`
(labels `inl`, exactly those of `fullOracle`) and the three supplied source operations `P_w`,
`U_load`, `P_w†` with their supported enable control (labels `inr`). -/
def fullActualOracle (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    Query ⊕ SourceCall → X → FSpace Ks n Z K M m →L[ℂ] FSpace Ks n Z K M m :=
  Sum.elim
    (fun l => NativeMaskedOracle.oracle
      (ι := GeneralSourceODE.Native.SourceBasis (FIota K M) n m)
      (fun x => (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)).conjStarAlgEquiv
        (matrixOracle (OmegaG (FLab K M m) K) D l x)))
    (fun k x => ODESectorTensor.sourcePhysical
      (B := OmegaG (FLab K M m) K × NativeControlledOracle.Workspace (PBasis Ks n Z))
      ((GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m).conjStarAlgEquiv
        (GeneralSourceODE.Oracles.sourceOperation (ι := FIota K M) Pw J k x)))

omit [DecidableEq Z] in
theorem fullActualOracle_unitary (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    {Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))} (hPw : ∀ x, IsUnitary (Pw x))
    {J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n}
    (hJ : ∀ x a, IsUnitary (J x a)) :
    ∀ l x, IsUnitary (fullActualOracle D K M m Pw J l x) := by
  intro l x
  cases l with
  | inl l =>
      exact NativeMaskedOracle.oracle_unitary _
        (fun y => (matrixOracle_unitary (OmegaG (FLab K M m) K) D l y).transport
          (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K))) x
  | inr k =>
      exact ODESectorTensor.sourcePhysical_unitary _
        ((GeneralSourceODE.Oracles.sourceOperation_unitary hPw hJ k x).transport
          (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m))

/-- The public phase gate `ω_i/|ω_i|` on the enabled source sector (a fixed gate). -/
def fullPhaseGate (K M m : ℕ) (φ : Option (Fin m) → ℂ) :
    FSpace Ks n Z K M m →L[ℂ] FSpace Ks n Z K M m :=
  ODESectorTensor.sourcePhysical
    (B := OmegaG (FLab K M m) K × NativeControlledOracle.Workspace (PBasis Ks n Z))
    ((GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m).conjStarAlgEquiv
      (GeneralSourceODE.Weights.phaseGate (ι := FIota K M) (P := EuclideanSpace ℂ n) φ))

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem fullPhaseGate_unitary (K M m : ℕ) {φ : Option (Fin m) → ℂ} (hφ : ∀ a, ‖φ a‖ = 1) :
    IsUnitary (fullPhaseGate (Ks := Ks) (n := n) (Z := Z) K M m φ) :=
  ODESectorTensor.sourcePhysical_unitary _
    ((GeneralSourceODE.Weights.phaseGate_unitary φ hφ).transport
      (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m))

/-- **Each counted interface call as a program over the separate primitives**: a matrix call is
itself; the preparation is `P_w`, then `U_load`, then the public phases; the unpreparation is
`P_w†`. -/
def fullImplementation (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (ω : Fin m → ℂ) :
    Query ⊕ Bool → MultiOracleCircuit.Program (fullActualOracle D K M m Pw J)
  | .inl l => .query (.inl l)
  | .inr false => .seq (.fixed (fullPhaseGate K M m (phases ω))
        (fullPhaseGate_unitary K M m (phases_norm ω)))
      (.seq (.query (.inr .load)) (.query (.inr .weight)))
  | .inr true => .query (.inr .unweight)

/-- **The implementations are exact**: on every input, each counted interface of `fullOracle`
is the evaluation of its program over the separate primitives. -/
theorem fullImplementation_eval (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (ω : Fin m → ℂ)
    (l : Query ⊕ Bool) (x : X) :
    (fullImplementation D K M m Pw J ω l).eval x = fullOracle D K M m Pw J ω l x := by
  rcases l with l | b
  · rfl
  · cases b with
    | true => rfl
    | false =>
        change fullPhaseGate K M m (phases ω) *
            (ODESectorTensor.sourcePhysical
              (B := OmegaG (FLab K M m) K × NativeControlledOracle.Workspace (PBasis Ks n Z))
              ((GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m).conjStarAlgEquiv
                (GeneralSourceODE.Weights.loader (J x))) *
            ODESectorTensor.sourcePhysical
              (B := OmegaG (FLab K M m) K × NativeControlledOracle.Workspace (PBasis Ks n Z))
              ((GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m).conjStarAlgEquiv
                (GeneralSourceODE.Weights.act (Pw x)))) =
          ODESectorTensor.sourcePhysical
            (B := OmegaG (FLab K M m) K × NativeControlledOracle.Workspace (PBasis Ks n Z))
            ((GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m).conjStarAlgEquiv
              (GeneralSourceODE.Compiled.prep (Pw x) (J x) (phases ω)))
        rw [fullPhaseGate, ← GeneralSourceODE.Oracles.sourcePhysical_mul,
          ← GeneralSourceODE.Oracles.sourcePhysical_mul, ← map_mul, ← map_mul]
        rfl

omit [DecidableEq Z] in
theorem fullImplementation_matrix (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (ω : Fin m → ℂ)
    (l : Query ⊕ Bool) :
    (fullImplementation D K M m Pw J ω l).cost GeneralSourceODE.Oracles.matrixCalls =
      ODESourceQueryBudget.matrixWeight (fun _ => 1) l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq Z] in
theorem fullImplementation_weight (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (ω : Fin m → ℂ)
    (l : Query ⊕ Bool) :
    (fullImplementation D K M m Pw J ω l).cost (GeneralSourceODE.Oracles.calls .weight) =
      ODESourceQueryBudget.sourceWeight false l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq Z] in
theorem fullImplementation_load (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (ω : Fin m → ℂ)
    (l : Query ⊕ Bool) :
    (fullImplementation D K M m Pw J ω l).cost (GeneralSourceODE.Oracles.calls .load) =
      ODESourceQueryBudget.sourceWeight false l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq Z] in
theorem fullImplementation_unweight (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (ω : Fin m → ℂ)
    (l : Query ⊕ Bool) :
    (fullImplementation D K M m Pw J ω l).cost (GeneralSourceODE.Oracles.calls .unweight) =
      ODESourceQueryBudget.sourceWeight true l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq Z] in
theorem fullImplementation_source (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (ω : Fin m → ℂ)
    (l : Query ⊕ Bool) :
    (fullImplementation D K M m Pw J ω l).cost GeneralSourceODE.Oracles.sourceCalls =
      2 * ODESourceQueryBudget.sourceWeight false l +
        ODESourceQueryBudget.sourceWeight true l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

/-- The trial family over the separate primitives: every counted interface call replaced by its
implementation. -/
def fullActualTrials (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (ω : Fin m → ℂ)
    (q : ℕ → MultiOracleCircuit.Program (fullOracle D K M m Pw J ω)) :
    ℕ → MultiOracleCircuit.Program (fullActualOracle D K M m Pw J) :=
  fun j => (q j).substitute (fullImplementation D K M m Pw J ω)

set_option maxHeartbeats 4000000 in
/-- **Lemma `odel:lem:dyson` on the full class with the source operations as separate
primitives**: one public trial family over `fullActualOracle D₀` (masked native calls, `P_w`,
`U_load`, `P_w†`), with `chosenIterations g'` choices, fixed before the instance, such that four
fresh trials satisfy `ActualCertificate` on every valid instance: success at least `2/3`
(indeed `175/256`), conditional trace distance at most `ε` after discarding the work registers,
worst-case `1274019840 g' queryShape s 0 (K/589824) = 2160 g' K` matrix queries, at most `40 g'`
calls of each of `P_w`, `U_load`, `P_w†` and `120 g'` source calls, `g' = c_q ḡ e^z`. -/
theorem full_actual (D₀ : Data (X × Fin Ks) n Z s) (hM : 0 < M) (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T η g cq ε : ℝ) (hmesh : IsMesh t M T) (hT : 0 < T) (hη : 0 < η)
    (hg : 1 ≤ g) (hcq : 1 ≤ cq) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (v : Fin m → ℝ) (hv : ∀ i, v i ∈ Icc 0 T) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a)) (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    ∃ tf : ODERepeatProtocol.TrialFamily
        (fullActualOracle D₀ (fullDegree s η T g cq ε) M m Pw J) (EuclideanSpace ℂ n),
      tf.choices = ODEGroverAverage.chosenIterations (fullAmp s η T g cq) ∧
      (∀ j x, IsUnitary ((tf.circuit j).eval x)) ∧
      ∀ x y, FullValid D₀ σ t T η g cq ε hη v ω Pw J seed x y →
        GeneralSourceODE.Oracles.ActualCertificate (ODERepeatProtocol.Protocol.repeatTrials tf 4)
          x y (s : ℝ) 0 (fullShape (fullDegree s η T g cq ε)) (fullAmp s η T g cq) ε := by
  obtain ⟨q, ψ, F, -, -, -, -, -, -, hψ, hF, -, hC⟩ := full_dyson_shape D₀ hM σ t T η g cq ε
    hmesh hT hη hg hcq hε hε1 v hv ω Pw hPw J hJ seed hSeed
  have hg1 := one_le_fullAmp (s := s) hη.le hT.le hg hcq
  obtain ⟨hMpos, -, -⟩ := ODEGroverAverage.chosenIterations_bounds (fullAmp s η T g cq) hg1
  have hO' := fullActualOracle_unitary D₀ (fullDegree s η T g cq ε) M m hPw hJ
  let q' := fullActualTrials D₀ (fullDegree s η T g cq ε) M m Pw J ω q
  refine ⟨ODERepeatProtocol.ofCircuits q'
    (ODEGroverAverage.chosenIterations (fullAmp s η T g cq)) hMpos ψ hψ F hF, rfl,
    fun j x => (q' j.val).eval_unitary hO' x, ?_⟩
  intro x y hv'
  have hEval : ∀ j, (q' j).eval x = (q j).eval x := fun j =>
    MultiOracleCircuit.Program.eval_substitute (q j) _
      (fullImplementation_eval D₀ (fullDegree s η T g cq ε) M m Pw J ω) x
  have hCost : ∀ (w : Query ⊕ SourceCall → ℕ) (j : ℕ), (q' j).cost w = (q j).cost (fun l =>
      (fullImplementation D₀ (fullDegree s η T g cq ε) M m Pw J ω l).cost w) :=
    fun w j => MultiOracleCircuit.Program.cost_substitute (q j) _ w
  exact GeneralSourceODE.Oracles.actual_certificate (hC x y hv') q' hMpos hψ hF hEval
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (fullImplementation_matrix D₀ _ M m Pw J ω)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (fullImplementation_weight D₀ _ M m Pw J ω)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (fullImplementation_load D₀ _ M m Pw J ω)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (fullImplementation_unweight D₀ _ M m Pw J ω)))
    (fun j => by
      rw [hCost, funext (fullImplementation_source D₀ _ M m Pw J ω),
        GeneralSourceODE.Oracles.cost_add, NativeHermitianDilation.cost_scale])

end

end DysonFullClass
