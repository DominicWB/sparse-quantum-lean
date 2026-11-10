import ManuscriptConformance.DysonLoaderColumns
import DysonFullClass.Single

/-!
# The full-class Dyson solver with a loader on its clean columns: one program, separate primitives

The released single-program and separate-primitive forms of Lemma `odel:lem:dyson` on the full
class (`DysonFullClass.full_single`, `DysonFullClass.full_actual`) are derived from
`full_dyson_shape`. Here they are derived in the same way from `full_dyson_shape_columns`, for a
unitary loader `Lo` on the whole branch register specified only on its clean columns
(`FullValidColumns`).

* `fullOracleL_unitary`: the access `fullOracleL` with the loader `Lo` is unitary.
* `FullSingleOutcomeColumns`, `full_single_columns`: **one heralded program** over the access with
  the loader `Lo` and spectator registers, for the valid instances `FullValidColumns`: success at
  least `2/3`, conditional accuracy `ε` of the reduced output, readout isometry and herald
  projection fixed before the instance, at most `dysonBound z (c_q ḡ) ε` matrix queries and at most
  `40 g'` calls of each counted source interface over the whole program (`g' = c_q ḡ e^z`).
* `fullActualOracleL`, `fullImplementationL`: the access with the supplied source operations as
  three separate primitives `P_w`, `Lo`, `P_w†` (and the public phase gate as a fixed gate);
  `fullImplementationL_eval`: the two counted interfaces of `fullOracleL` are exactly
  `P_w; Lo; phases` and `P_w†` on these primitives; the five count lemmas.
* `full_actual_columns`: the released four-attempt protocol over these primitives, with the
  separate worst-case counts of `GeneralSourceODE.Oracles.ActualCertificate` (matrix queries
  `1274019840 g' queryShape s 0 (K/589824) = 2160 g' K`, at most `40 g'` calls of each of `P_w`,
  `Lo`, `P_w†` and `120 g'` source calls in all), for every valid instance.

The trials call `Lo` and its inverse (through the literal inverse of the preparation) and the
supplied `P_w†`; `Lo` is not assumed to preserve the labels away from the clean columns. Scope: the
exact case of item D1. `DysonFullClass.full_approx` (approximate preparations) keeps the
label-controlled loader, and the released label-controlled forms are unchanged.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 4096

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
/-- The access of the full-class solver with the loader `Lo` is unitary when `P_w` and `Lo` are. -/
theorem fullOracleL_unitary (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    {Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))} (hPw : ∀ x, IsUnitary (Pw x))
    {Lo : X → GeneralSourceODE.Native.SourceSpace (FIota K M) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (FIota K M) n m} (hLo : ∀ x, IsUnitary (Lo x))
    (ω : Fin m → ℂ) :
    ∀ l x, IsUnitary (fullOracleL D K M m Pw Lo ω l x) :=
  ODECoordinateNativeControl.physicalOracle_unitary _ _ _ _
    (matrixOracle_unitary (OmegaG (FLab K M m) K) D)
    (GeneralSourceODE.Compiled.sourceFamilyL_unitary hPw hLo (phases_norm ω))

/-! ### One heralded program -/

/-- **The single-program outcome on the full class with the loader `Lo`**: `FullSingleOutcome`
over `fullOracleL D₀ K M m P_w Lo ω` (`K = fullDegree`) for the valid instances of
`FullValidColumns`: a spectator register `Jt`, a garbage space `G` and one heralded program with
success at least `2/3` and conditional accuracy `ε` on every valid instance, at most
`dysonBound z (c_q ḡ) ε = 16000 c_q ḡ e^z (1 + z + L/log(e + L/z))` matrix queries
(`z = s η T`, `L = log(4000 c_q ḡ/ε)`) and at most `40 c_q ḡ e^z` calls of each counted source
interface. -/
def FullSingleOutcomeColumns (D₀ : Data (X × Fin Ks) n Z s) {M : ℕ} (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T η g cq ε : ℝ) (hη : 0 < η) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (FIota (fullDegree s η T g cq ε) M) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (FIota (fullDegree s η T g cq ε) M) n m)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (Jt : Type) (_ : Fintype Jt) (G : Type) (_ : NormedAddCommGroup G)
    (_ : InnerProductSpace ℂ G) (_ : CompleteSpace G)
    (A : HeraldedSolver (fiberOracle Jt (fullOracleL D₀ (fullDegree s η T g cq ε) M m Pw Lo ω))
      (FullValidColumns D₀ σ t T η g cq ε hη v ω Pw Lo seed) G ε),
    (A.prog.cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
      dysonBound (zParam s η T) (cq * g) ε ∧
    ∀ b : Bool, (A.prog.cost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤
      40 * fullAmp s η T g cq

/-- **Lemma `odel:lem:dyson` on the full time-dependent class, single-program form, with a loader
specified on its clean columns only (item D1, exact case)**: `full_single` with the counted
interfaces over the supplied `P_w` and a unitary loader `Lo` on the whole branch register. For
every public specification one heralded program solves every valid instance of
`FullValidColumns`, with at most `dysonBound (s η T) (c_q ḡ) ε` matrix queries and at most
`40 c_q ḡ e^z` calls of each source interface over the whole program. The proof is that of
`full_single`, from `full_dyson_shape_columns`. -/
theorem full_single_columns (D₀ : Data (X × Fin Ks) n Z s) (hM : 0 < M) (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T η g cq ε : ℝ) (hmesh : IsMesh t M T) (hT : 0 < T) (hη : 0 < η)
    (hg : 1 ≤ g) (hcq : 1 ≤ cq) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (v : Fin m → ℝ) (hv : ∀ i, v i ∈ Icc 0 T) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (FIota (fullDegree s η T g cq ε) M) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (FIota (fullDegree s η T g cq ε) M) n m)
    (hLo : ∀ x, IsUnitary (Lo x)) (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    FullSingleOutcomeColumns D₀ σ t T η g cq ε hη v ω Pw Lo seed := by
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
  have hO := fullOracleL_unitary D₀ (fullDegree s η T g cq ε) M m hPw hLo ω
  by_cases hV : ∃ x y, FullValidColumns D₀ σ t T η g cq ε hη v ω Pw Lo seed x y
  · obtain ⟨x₀, y₀, hv₀⟩ := hV
    obtain ⟨q, ψ, F, a, U₁, U₂, U₃, hshape, hshapeS, hψ, hF, -, hcert⟩ :=
      full_dyson_shape_columns D₀ hM σ t T η g cq ε hmesh hT hη hg hcq hε hε1 v hv ω Pw hPw Lo
        hLo seed hSeed
    have c := hcert x₀ y₀ hv₀
    refine ⟨_, _, _, _, _, _, Core.single hO q _ c.trial.cutoff_pos ψ hψ F hF i₀ a
      (ODESourceQueryBudget.matrixWeight (fun _ => 1)) hshape
      (FullValidColumns D₀ σ t T η g cq ε hη v ω Pw Lo seed) (s : ℝ) 0
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

/-! ### The supplied source operations `P_w`, `Lo`, `P_w†` as separate primitives -/

/-- **The actual primitive oracles of the full-class solver with the loader `Lo`**: the masked
native calls of `D` (labels `inl`, exactly those of `fullOracleL`) and the three supplied source
operations `P_w`, `Lo`, `P_w†` with their supported enable control (labels `inr`). -/
def fullActualOracleL (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (FIota K M) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (FIota K M) n m) :
    Query ⊕ SourceCall → X → FSpace Ks n Z K M m →L[ℂ] FSpace Ks n Z K M m :=
  Sum.elim
    (fun l => NativeMaskedOracle.oracle
      (ι := GeneralSourceODE.Native.SourceBasis (FIota K M) n m)
      (fun x => (matrixLayout (n := n) (Z := Z) (Ks := Ks)
        (OmegaG (FLab K M m) K)).conjStarAlgEquiv (matrixOracle (OmegaG (FLab K M m) K) D l x)))
    (fun k x => ODESectorTensor.sourcePhysical
      (B := OmegaG (FLab K M m) K × NativeControlledOracle.Workspace (PBasis Ks n Z))
      ((GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m).conjStarAlgEquiv
        (GeneralSourceODE.Oracles.sourceOperationL (ι := FIota K M) Pw Lo k x)))

omit [DecidableEq Z] in
theorem fullActualOracleL_unitary (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    {Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))} (hPw : ∀ x, IsUnitary (Pw x))
    {Lo : X → GeneralSourceODE.Native.SourceSpace (FIota K M) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (FIota K M) n m} (hLo : ∀ x, IsUnitary (Lo x)) :
    ∀ l x, IsUnitary (fullActualOracleL D K M m Pw Lo l x) := by
  intro l x
  cases l with
  | inl l =>
      exact NativeMaskedOracle.oracle_unitary _
        (fun y => (matrixOracle_unitary (OmegaG (FLab K M m) K) D l y).transport
          (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K))) x
  | inr k =>
      exact ODESectorTensor.sourcePhysical_unitary _
        ((GeneralSourceODE.Oracles.sourceOperationL_unitary hPw hLo k x).transport
          (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m))

/-- **Each counted interface call as a program over the separate primitives**: a matrix call is
itself; the preparation is `P_w`, then `Lo`, then the public phases; the unpreparation is
`P_w†`. -/
def fullImplementationL (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (FIota K M) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (FIota K M) n m) (ω : Fin m → ℂ) :
    Query ⊕ Bool → MultiOracleCircuit.Program (fullActualOracleL D K M m Pw Lo)
  | .inl l => .query (.inl l)
  | .inr false => .seq (.fixed (fullPhaseGate K M m (phases ω))
        (fullPhaseGate_unitary K M m (phases_norm ω)))
      (.seq (.query (.inr .load)) (.query (.inr .weight)))
  | .inr true => .query (.inr .unweight)

/-- **The implementations are exact**: on every input, each counted interface of `fullOracleL`
is the evaluation of its program over the separate primitives. -/
theorem fullImplementationL_eval (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (FIota K M) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (FIota K M) n m) (ω : Fin m → ℂ)
    (l : Query ⊕ Bool) (x : X) :
    (fullImplementationL D K M m Pw Lo ω l).eval x = fullOracleL D K M m Pw Lo ω l x := by
  rcases l with l | b
  · rfl
  · cases b with
    | true => rfl
    | false =>
        change fullPhaseGate K M m (phases ω) *
            (ODESectorTensor.sourcePhysical
              (B := OmegaG (FLab K M m) K × NativeControlledOracle.Workspace (PBasis Ks n Z))
              ((GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m).conjStarAlgEquiv
                (Lo x)) *
            ODESectorTensor.sourcePhysical
              (B := OmegaG (FLab K M m) K × NativeControlledOracle.Workspace (PBasis Ks n Z))
              ((GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m).conjStarAlgEquiv
                (GeneralSourceODE.Weights.act (Pw x)))) =
          ODESectorTensor.sourcePhysical
            (B := OmegaG (FLab K M m) K × NativeControlledOracle.Workspace (PBasis Ks n Z))
            ((GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m).conjStarAlgEquiv
              (GeneralSourceODE.Compiled.prepL (Pw x) (Lo x) (phases ω)))
        rw [fullPhaseGate, ← GeneralSourceODE.Oracles.sourcePhysical_mul,
          ← GeneralSourceODE.Oracles.sourcePhysical_mul, ← map_mul, ← map_mul]
        rfl

omit [DecidableEq Z] in
theorem fullImplementationL_matrix (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (FIota K M) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (FIota K M) n m) (ω : Fin m → ℂ)
    (l : Query ⊕ Bool) :
    (fullImplementationL D K M m Pw Lo ω l).cost GeneralSourceODE.Oracles.matrixCalls =
      ODESourceQueryBudget.matrixWeight (fun _ => 1) l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq Z] in
theorem fullImplementationL_weight (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (FIota K M) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (FIota K M) n m) (ω : Fin m → ℂ)
    (l : Query ⊕ Bool) :
    (fullImplementationL D K M m Pw Lo ω l).cost (GeneralSourceODE.Oracles.calls .weight) =
      ODESourceQueryBudget.sourceWeight false l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq Z] in
theorem fullImplementationL_load (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (FIota K M) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (FIota K M) n m) (ω : Fin m → ℂ)
    (l : Query ⊕ Bool) :
    (fullImplementationL D K M m Pw Lo ω l).cost (GeneralSourceODE.Oracles.calls .load) =
      ODESourceQueryBudget.sourceWeight false l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq Z] in
theorem fullImplementationL_unweight (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (FIota K M) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (FIota K M) n m) (ω : Fin m → ℂ)
    (l : Query ⊕ Bool) :
    (fullImplementationL D K M m Pw Lo ω l).cost (GeneralSourceODE.Oracles.calls .unweight) =
      ODESourceQueryBudget.sourceWeight true l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq Z] in
theorem fullImplementationL_source (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (FIota K M) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (FIota K M) n m) (ω : Fin m → ℂ)
    (l : Query ⊕ Bool) :
    (fullImplementationL D K M m Pw Lo ω l).cost GeneralSourceODE.Oracles.sourceCalls =
      2 * ODESourceQueryBudget.sourceWeight false l +
        ODESourceQueryBudget.sourceWeight true l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

/-- The trial family over the separate primitives `P_w`, `Lo`, `P_w†`: every counted interface
call replaced by its implementation. -/
def fullActualTrialsL (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (FIota K M) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (FIota K M) n m) (ω : Fin m → ℂ)
    (q : ℕ → MultiOracleCircuit.Program (fullOracleL D K M m Pw Lo ω)) :
    ℕ → MultiOracleCircuit.Program (fullActualOracleL D K M m Pw Lo) :=
  fun j => (q j).substitute (fullImplementationL D K M m Pw Lo ω)

set_option maxHeartbeats 4000000 in
/-- **Lemma `odel:lem:dyson` on the full class with the source operations as separate primitives
and a loader specified on its clean columns only (item D1, exact case)**: `full_actual` for a
unitary loader `Lo` on the whole branch register. One public trial family over
`fullActualOracleL D₀` (masked native calls, `P_w`, `Lo`, `P_w†`), with `chosenIterations g'`
choices, fixed before the instance, such that four fresh trials satisfy `ActualCertificate` on
every valid instance of `FullValidColumns`: success at least `2/3` (indeed `175/256`), conditional
trace distance at most `ε` after discarding the work registers, worst-case
`1274019840 g' queryShape s 0 (K/589824) = 2160 g' K` matrix queries, at most `40 g'` calls of each
of `P_w`, `Lo`, `P_w†` and `120 g'` source calls, `g' = c_q ḡ e^z`. The proof is that of
`full_actual`, from `full_dyson_shape_columns`. -/
theorem full_actual_columns (D₀ : Data (X × Fin Ks) n Z s) (hM : 0 < M) (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T η g cq ε : ℝ) (hmesh : IsMesh t M T) (hT : 0 < T) (hη : 0 < η)
    (hg : 1 ≤ g) (hcq : 1 ≤ cq) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (v : Fin m → ℝ) (hv : ∀ i, v i ∈ Icc 0 T) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (FIota (fullDegree s η T g cq ε) M) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (FIota (fullDegree s η T g cq ε) M) n m)
    (hLo : ∀ x, IsUnitary (Lo x)) (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    ∃ tf : ODERepeatProtocol.TrialFamily
        (fullActualOracleL D₀ (fullDegree s η T g cq ε) M m Pw Lo) (EuclideanSpace ℂ n),
      tf.choices = ODEGroverAverage.chosenIterations (fullAmp s η T g cq) ∧
      (∀ j x, IsUnitary ((tf.circuit j).eval x)) ∧
      ∀ x y, FullValidColumns D₀ σ t T η g cq ε hη v ω Pw Lo seed x y →
        GeneralSourceODE.Oracles.ActualCertificate (ODERepeatProtocol.Protocol.repeatTrials tf 4)
          x y (s : ℝ) 0 (fullShape (fullDegree s η T g cq ε)) (fullAmp s η T g cq) ε := by
  obtain ⟨q, ψ, F, -, -, -, -, -, -, hψ, hF, -, hC⟩ := full_dyson_shape_columns D₀ hM σ t T η g
    cq ε hmesh hT hη hg hcq hε hε1 v hv ω Pw hPw Lo hLo seed hSeed
  have hg1 := one_le_fullAmp (s := s) hη.le hT.le hg hcq
  obtain ⟨hMpos, -, -⟩ := ODEGroverAverage.chosenIterations_bounds (fullAmp s η T g cq) hg1
  have hO' := fullActualOracleL_unitary D₀ (fullDegree s η T g cq ε) M m hPw hLo
  let q' := fullActualTrialsL D₀ (fullDegree s η T g cq ε) M m Pw Lo ω q
  refine ⟨ODERepeatProtocol.ofCircuits q'
    (ODEGroverAverage.chosenIterations (fullAmp s η T g cq)) hMpos ψ hψ F hF, rfl,
    fun j x => (q' j.val).eval_unitary hO' x, ?_⟩
  intro x y hv'
  have hEval : ∀ j, (q' j).eval x = (q j).eval x := fun j =>
    MultiOracleCircuit.Program.eval_substitute (q j) _
      (fullImplementationL_eval D₀ (fullDegree s η T g cq ε) M m Pw Lo ω) x
  have hCost : ∀ (w : Query ⊕ SourceCall → ℕ) (j : ℕ), (q' j).cost w = (q j).cost (fun l =>
      (fullImplementationL D₀ (fullDegree s η T g cq ε) M m Pw Lo ω l).cost w) :=
    fun w j => MultiOracleCircuit.Program.cost_substitute (q j) _ w
  exact GeneralSourceODE.Oracles.actual_certificate (hC x y hv') q' hMpos hψ hF hEval
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (fullImplementationL_matrix D₀ _ M m Pw Lo ω)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (fullImplementationL_weight D₀ _ M m Pw Lo ω)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (fullImplementationL_load D₀ _ M m Pw Lo ω)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (fullImplementationL_unweight D₀ _ M m Pw Lo ω)))
    (fun j => by
      rw [hCost, funext (fullImplementationL_source D₀ _ M m Pw Lo ω),
        GeneralSourceODE.Oracles.cost_add, NativeHermitianDilation.cost_scale])

end

end DysonFullClass
