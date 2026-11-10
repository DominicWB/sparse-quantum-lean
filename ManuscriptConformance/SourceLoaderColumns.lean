import GeneralSourceODE.Theorem
import GeneralODE.Block.HistoryEncoding
import ManuscriptConformance.PrepColumn

/-!
# The general-source ODE solver with a loader specified on its clean columns only (item D1)

The released general-source solver `GeneralSourceODE.solver` (`ode:thm:time` with the source
interface of `ode:eq:source-interface-preparation`) takes the loading oracle as a label-controlled
family `U_load = ∑_a |a⟩⟨a| ⊗ J_a`. Here the loading oracle is an arbitrary unitary `Lo` on the
whole branch register (source label, LCHS label and data), specified only on its clean columns
`|a, t⟩|seed⟩` of the labels that carry source weight:

`Lo |a, t⟩|seed⟩ = |a, t⟩ |x(0)/‖x(0)‖⟩` for `a = none`, and `|a, t⟩ |b(v_i)/‖b(v_i)‖⟩` for
`a = some i` with `ω_i ≠ 0`, `b(v_i) ≠ 0`.

Nothing is assumed about `Lo` on any other vector, in particular not that it preserves the labels.

* `Compiled.prepL`, `Compiled.sourceFamilyL`: the counted interfaces with the loader `Lo`
  (`sourceFamily_eq_sourceFamilyL`: the released ones are the case `Lo = loader J`;
  `sourceFamilyL_true`, `sourceFamilyL_false`, `sourceFamily_true`, `sourceFamily_false`).
* `Compiled.program_seed_congr`: the column of the source-loaded program on the public seed depends
  on the preparation call only through its value on the seed branch state.
* `Compiled.amplified_seed_congr`: the amplified trials, which call the preparation and its
  literal inverse, act on the seed through that column only (`U R_ψ U† = R_{Uψ}`).
* `Native.publicTrialsS`, `publicTrialsS_seed_congr`, `publicTrialsS_matrix_cost`,
  `publicTrialsS_source_cost`: the same after the released primitive-control compiler, with the
  same counts.
* `Weights.act_seedInput`, `Weights.clean_congr`, `Weights.loader_single`: after `P_w`, the seed
  branch state is a combination of clean columns `|b⟩|seed⟩` with weights
  `⟨a|P_w|none⟩ · √c_t`, so `Lo` and `loader J` agree on it when they agree on the clean columns
  of positive weight.
* `Oracles.actualOracleL`, `implementationL`, `actualTrialsL`: the actual oracles `P_w`, `Lo`,
  `P_w†`, counted separately (`actualOracle_eq_actualOracleL`).
* `Oracles.actual_certificate_seed`: the released transfer of the complete certificate, with
  evaluations agreeing on the seed only.
* `Oracles.columns_certificate`: the complete certificate of the label-controlled family
  transfers to the four-attempt protocol over `P_w`, `Lo`, `P_w†` when `Lo` and `loader J` agree
  on the seed branch state after `P_w`.
* `propagated_solver_public`: `GeneralSourceODE.propagated_solver` with its public trial family
  `Native.publicTrials` exposed (the released proof, with the conclusion naming the family).
* `columnLoader`: a label-controlled family with the clean columns of `Lo`.
* `solver_columns` (`OutcomeColumns`): the guarantee of `GeneralSourceODE.solver` (success at
  least `2/3`, conditional trace distance at most `ε`, the same matrix-query bound and at most
  `40 g'` calls of each of `P_w`, `Lo` and `P_w†`) for every unitary loader with the stated clean
  columns. The trial family is fixed before the instance, from public data and the supplied
  `P_w`, `Lo`.

Scope: the exact case of item D1 for the general-source ODE endpoint. Approximate columns are not
treated. The released label-controlled form is unchanged.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralSourceODE

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct BigOperators

set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 2000000

/-! ### Clean columns of the branch register -/

namespace Weights

variable {σ ι P : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P]

omit [Fintype σ] [Fintype ι] in
theorem single_smul (b : σ × ι) (r : ℂ) (v : P) :
    (PiLp.single 2 b (r • v) : Space σ ι P) = r • PiLp.single 2 b v := by
  ext b'
  by_cases h : b' = b
  · subst h
    simp
  · simp [h]

omit [Fintype σ] [Fintype ι] in
/-- A clean branch state `∑_b α_b |b⟩|v⟩` is the combination of the clean columns. -/
theorem clean_eq_sum [Fintype σ] [Fintype ι] (α : σ × ι → ℂ) (v : P) :
    (WithLp.toLp 2 (fun b => α b • v) : Space σ ι P) = ∑ b, α b • PiLp.single 2 b v := by
  ext b'
  rw [PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single b']
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- **Two operators agreeing on the clean columns of positive weight agree on the clean state.** -/
theorem clean_congr (L L' : Space σ ι P →L[ℂ] Space σ ι P) (α : σ × ι → ℂ) (v : P)
    (h : ∀ b, α b ≠ 0 → L (PiLp.single 2 b v) = L' (PiLp.single 2 b v)) :
    L (WithLp.toLp 2 (fun b => α b • v)) = L' (WithLp.toLp 2 (fun b => α b • v)) := by
  rw [clean_eq_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : α b = 0
  · simp [hb]
  · rw [map_smul, map_smul, h b hb]

/-- The label-controlled loader on a clean column. -/
theorem loader_single (J : σ → P →L[ℂ] P) (b : σ × ι) (v : P) :
    loader (ι := ι) J (PiLp.single 2 b v) = PiLp.single 2 b (J b.1 v) := by
  ext b'
  by_cases h : b' = b
  · subst h
    simp [loader, WeightedClock.diagonal_apply]
  · simp [loader, WeightedClock.diagonal_apply, h]

variable [CompleteSpace P]

omit [CompleteSpace P] [DecidableEq ι] in
/-- **After `P_w`, the public seed branch state is clean**: its column `|a, t⟩|v⟩` has weight
`⟨a|P_w|none⟩ · √c_t`. -/
theorem act_seedInput {N : ℕ} (Q : LabelOp (Option (Fin N))) (c : ι → ℂ) (v : P) :
    act (ι := ι) Q (ODEJointLCU.coefficientInput (Compiled.seedCoefficients (N := N) c) v) =
      WithLp.toLp 2 (fun b : Option (Fin N) × ι => (amp Q b.1 none *
        (Real.sqrt (ODECoherentLCU.coefficientProbability
          (Compiled.seedCoefficients (N := N) c) (none, b.2)) : ℂ)) • v) := by
  ext b
  rw [act_apply, PiLp.toLp_apply]
  simp only [ODEJointLCU.coefficientInput, ODECoherentLCU.inputEmbedding,
    WeightedClock.boundary_apply, one_apply_eq_self]
  rw [Finset.sum_eq_single none]
  · rw [smul_smul]
  · intro a' _ ha'
    have h0 : ODECoherentLCU.coefficientProbability (Compiled.seedCoefficients (N := N) c)
        (a', b.2) = 0 := by
      simp [ODECoherentLCU.coefficientProbability, Compiled.seedCoefficients,
        ODESourceCoefficients.productCoeff, pointWeight, ha']
    simp [h0]
  · simp

end Weights

/-! ### The counted interfaces with a loader on the whole branch register -/

namespace Compiled

variable {ι P K X L : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : ℕ} {O : L → X → K →L[ℂ] K}

/-- The preparation call with a loading unitary `Lo` on the whole branch register. -/
def prepL (Pw : Weights.LabelOp (Option (Fin N))) (Lo : Branch ι P N →L[ℂ] Branch ι P N)
    (φ : Option (Fin N) → ℂ) : Branch ι P N →L[ℂ] Branch ι P N :=
  Weights.phaseGate φ ∘L Lo ∘L Weights.act Pw

/-- The two counted interfaces with the loader `Lo`. -/
def sourceFamilyL (Pw : X → Weights.LabelOp (Option (Fin N)))
    (Lo : X → Branch ι P N →L[ℂ] Branch ι P N) (φ : Option (Fin N) → ℂ) :
    Bool → X → Branch ι P N →L[ℂ] Branch ι P N :=
  fun b x => if b then Weights.act ((Pw x)†) else prepL (Pw x) (Lo x) φ

omit [CompleteSpace P] in
/-- The released interfaces are those with the label-controlled loader. -/
theorem sourceFamily_eq_sourceFamilyL (Pw : X → Weights.LabelOp (Option (Fin N)))
    (J : X → Option (Fin N) → P →L[ℂ] P) (φ : Option (Fin N) → ℂ) :
    sourceFamily (ι := ι) Pw J φ = sourceFamilyL Pw (fun x => Weights.loader (J x)) φ := rfl

omit [CompleteSpace P] in
theorem sourceFamilyL_true (Pw : X → Weights.LabelOp (Option (Fin N)))
    (Lo : X → Branch ι P N →L[ℂ] Branch ι P N) (φ : Option (Fin N) → ℂ) (x : X) :
    sourceFamilyL Pw Lo φ true x = Weights.act ((Pw x)†) := rfl

omit [CompleteSpace P] in
theorem sourceFamilyL_false (Pw : X → Weights.LabelOp (Option (Fin N)))
    (Lo : X → Branch ι P N →L[ℂ] Branch ι P N) (φ : Option (Fin N) → ℂ) (x : X) :
    sourceFamilyL Pw Lo φ false x = prepL (Pw x) (Lo x) φ := rfl

omit [CompleteSpace P] in
theorem sourceFamily_true (Pw : X → Weights.LabelOp (Option (Fin N)))
    (J : X → Option (Fin N) → P →L[ℂ] P) (φ : Option (Fin N) → ℂ) (x : X) :
    sourceFamily (ι := ι) Pw J φ true x = Weights.act ((Pw x)†) := rfl

omit [CompleteSpace P] in
theorem sourceFamily_false (Pw : X → Weights.LabelOp (Option (Fin N)))
    (J : X → Option (Fin N) → P →L[ℂ] P) (φ : Option (Fin N) → ℂ) (x : X) :
    sourceFamily (ι := ι) Pw J φ false x = prep (Pw x) (J x) φ := rfl

theorem prepL_unitary {Pw : Weights.LabelOp (Option (Fin N))} (hPw : IsUnitary Pw)
    {Lo : Branch ι P N →L[ℂ] Branch ι P N} (hLo : IsUnitary Lo)
    {φ : Option (Fin N) → ℂ} (hφ : ∀ a, ‖φ a‖ = 1) :
    IsUnitary (prepL (ι := ι) Pw Lo φ) := by
  unfold prepL
  exact ((Weights.phaseGate_unitary φ hφ).mul hLo).mul (Weights.act_unitary hPw)

theorem sourceFamilyL_unitary {Pw : X → Weights.LabelOp (Option (Fin N))}
    (hPw : ∀ x, IsUnitary (Pw x)) {Lo : X → Branch ι P N →L[ℂ] Branch ι P N}
    (hLo : ∀ x, IsUnitary (Lo x)) {φ : Option (Fin N) → ℂ} (hφ : ∀ a, ‖φ a‖ = 1) :
    ∀ b x, IsUnitary (sourceFamilyL (ι := ι) Pw Lo φ b x) := by
  intro b x
  cases b with
  | false => exact prepL_unitary (hPw x) (hLo x) hφ
  | true => exact Weights.act_unitary (adjoint_unitary (hPw x))

/-- **The column of the source-loaded program on the public seed** depends on the preparation
call only through its value on the seed branch state, and on the unpreparation call. -/
theorem program_seed_congr (p : MultiOracleCircuit.Program O)
    (S S' : Bool → X → Branch ι P N →L[ℂ] Branch ι P N)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1) (d : Option (Fin N) × ι → ℂ) (v : P) (x : X)
    (htrue : S true x = S' true x)
    (hfalse : S false x (ODEJointLCU.coefficientInput d v) =
      S' false x (ODEJointLCU.coefficientInput d v)) :
    (program p S E hE).eval x (ODECompiledSource.seed E d v) =
      (program p S' E hE).eval x (ODECompiledSource.seed E d v) := by
  have hr : ODESourceTransport.route E (ODECompiledSource.seed E d v) =
      ODESourceTransport.sourceEmbedding (ODEJointLCU.coefficientInput d v) := by
    have h := congrArg
      (fun A : Branch ι P N →L[ℂ] ODESourceTransport.Space (Branch ι P N) K =>
        A (ODEJointLCU.coefficientInput d v)) (ODESourceTransport.route_encoded E hE)
    simp only [comp_apply] at h
    exact h
  have hs : ∀ (T : Branch ι P N →L[ℂ] Branch ι P N) (w : Branch ι P N),
      ODESourceTransport.sourceGate (K := K) T (ODESourceTransport.sourceEmbedding w) =
        ODESourceTransport.sourceEmbedding (T w) := fun T w =>
    congrArg (fun A : Branch ι P N →L[ℂ] ODESourceTransport.Space (Branch ι P N) K => A w)
      (ODESourceTransport.sourceGate_source T)
  rw [program_eval, program_eval]
  simp only [mul_apply_eq_comp, hr, hs, hfalse, htrue]

/-- **The amplified trials depend on the source interfaces only through the seed column**: they
call the program and its literal inverse, and `U R_ψ U† = R_{Uψ}`. -/
theorem amplified_seed_congr (p : MultiOracleCircuit.Program O) (hO : ∀ l x, IsUnitary (O l x))
    (S S' : Bool → X → Branch ι P N →L[ℂ] Branch ι P N) (hS : ∀ b x, IsUnitary (S b x))
    (hS' : ∀ b x, IsUnitary (S' b x)) (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (F : P →L[ℂ] ODESourceTransport.Space (Branch ι P N) K) (hF : F† ∘L F = 1)
    (ψ : ODESourceTransport.Space (Branch ι P N) K) (hψ : ‖ψ‖ = 1) (x : X)
    (h : (program p S E hE).eval x ψ = (program p S' E hE).eval x ψ) (j : ℕ) :
    (ODECountedAmplification.program (program p S E hE) F hF ψ hψ j).eval x ψ =
      (ODECountedAmplification.program (program p S' E hE) F hF ψ hψ j).eval x ψ := by
  rw [ODECountedAmplification.state_eq _ F hF ψ hψ j x (program_unitary p hO S hS E hE x),
    ODECountedAmplification.state_eq _ F hF ψ hψ j x (program_unitary p hO S' hS' E hE x)]
  unfold ODEGroverActual.trial ODEGroverActual.actualG
  rw [h]

end Compiled

/-! ### The public trial family for any pair of counted interfaces -/

namespace Native

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s M m : ℕ}

/-- The primitive oracles with the counted interfaces `S`. -/
abbrev physicalOracleS (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (S : Bool → X → SourceSpace ι n m →L[ℂ] SourceSpace ι n m) :
    Query ⊕ Bool → X → PhysicalSpace ι n Z m M d →L[ℂ] PhysicalSpace ι n Z m M d :=
  ODECoordinateNativeControl.physicalOracle
    (A := SourceBasis ι n m) (B := MatrixBasis ι n Z m M d)
    (H := SourceSpace ι n m) (K := MatrixSpace ι n Z m M d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) m)
    (matrixLayout (ι := ι) (n := n) (Z := Z) m M d)
    (matrixOracle (ι := ι) D m d) S

/-- The compiled public trial family of `publicTrials`, for any counted interfaces `S`. -/
def publicTrialsS (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m d : ℕ)
    (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D m d))
    (S : Bool → X → SourceSpace ι n m →L[ℂ] SourceSpace ι n m)
    (E : SourceSpace ι n m →L[ℂ] MatrixSpace ι n Z m M d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E (Compiled.seedCoefficients c) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      ODECompiledSource.output E (Compiled.seedCoefficients c) = 1) :
    ℕ → MultiOracleCircuit.Program (physicalOracleS (ι := ι) D m d S) :=
  fun j => ODECoordinateNativeControl.compile
    (A := SourceBasis ι n m) (B := MatrixBasis ι n Z m M d)
    (H := SourceSpace ι n m) (K := MatrixSpace ι n Z m M d) (X := X) (L := Query)
    (sourceLayout (ι := ι) (n := n) m)
    (matrixLayout (ι := ι) (n := n) (Z := Z) m M d)
    (matrixOracle (ι := ι) D m d) S
    (sourceBasis D i0 m) (matrixBasis D hM i0 m d)
    (ODECountedAmplification.program (Compiled.program p S E hE)
      (ODECompiledSource.output E (Compiled.seedCoefficients c)) hOutput
      (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed) hSeed j)

/-- The released public trial family is the case of the label-controlled interfaces. -/
theorem publicTrials_eq_publicTrialsS (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι)
    (m d : ℕ) (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D m d))
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ)
    (E : SourceSpace ι n m →L[ℂ] MatrixSpace ι n Z m M d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E (Compiled.seedCoefficients c) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      ODECompiledSource.output E (Compiled.seedCoefficients c) = 1) :
    publicTrials D hM i0 m d p Pw J φ E hE c seed hSeed hOutput =
      publicTrialsS D hM i0 m d p (sourceFamily Pw J φ) E hE c seed hSeed hOutput := rfl

/-- **The compiled trials depend on the counted interfaces only through the seed column.** -/
theorem publicTrialsS_seed_congr (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι)
    (m d : ℕ) (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D m d))
    (S S' : Bool → X → SourceSpace ι n m →L[ℂ] SourceSpace ι n m)
    (hS : ∀ b x, IsUnitary (S b x)) (hS' : ∀ b x, IsUnitary (S' b x))
    (E : SourceSpace ι n m →L[ℂ] MatrixSpace ι n Z m M d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E (Compiled.seedCoefficients c) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      ODECompiledSource.output E (Compiled.seedCoefficients c) = 1) (x : X)
    (htrue : S true x = S' true x)
    (hfalse : S false x (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed) =
      S' false x (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed)) (j : ℕ) :
    (publicTrialsS D hM i0 m d p S E hE c seed hSeed hOutput j).eval x
        (input D hM i0 m d (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed)) =
      (publicTrialsS D hM i0 m d p S' E hE c seed hSeed hOutput j).eval x
        (input D hM i0 m d (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed)) := by
  have key : ∀ (T : Bool → X → SourceSpace ι n m →L[ℂ] SourceSpace ι n m)
      (_hT : ∀ b x, IsUnitary (T b x)),
      (publicTrialsS D hM i0 m d p T E hE c seed hSeed hOutput j).eval x ∘L input D hM i0 m d =
        input D hM i0 m d ∘L
          (ODECountedAmplification.program (Compiled.program p T E hE)
            (ODECompiledSource.output E (Compiled.seedCoefficients c)) hOutput
            (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed) hSeed j).eval x := by
    intro T hT
    exact ODECoordinateNativeControl.compile_eval
      (A := SourceBasis ι n m) (B := MatrixBasis ι n Z m M d)
      (H := SourceSpace ι n m) (K := MatrixSpace ι n Z m M d) (X := X) (L := Query)
      (sourceLayout (ι := ι) (n := n) m)
      (matrixLayout (ι := ι) (n := n) (Z := Z) m M d)
      (matrixOracle (ι := ι) D m d) T (matrixOracle_unitary (ι := ι) D m d) hT
      (sourceBasis D i0 m) (matrixBasis D hM i0 m d) (matrixImage D hM i0 m d)
      (matrix_valid D hM i0 m d)
      (ODECountedAmplification.program (Compiled.program p T E hE)
        (ODECompiledSource.output E (Compiled.seedCoefficients c)) hOutput
        (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed) hSeed j) x
  have key' : ∀ (T : Bool → X → SourceSpace ι n m →L[ℂ] SourceSpace ι n m)
      (_hT : ∀ b x, IsUnitary (T b x)),
      (publicTrialsS D hM i0 m d p T E hE c seed hSeed hOutput j).eval x
          (input D hM i0 m d (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed)) =
        input D hM i0 m d
          ((ODECountedAmplification.program (Compiled.program p T E hE)
            (ODECompiledSource.output E (Compiled.seedCoefficients c)) hOutput
            (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed) hSeed j).eval x
            (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed)) := by
    intro T hT
    rw [← comp_apply, key T hT, comp_apply]
  rw [key' S hS, key' S' hS',
    Compiled.amplified_seed_congr p (matrixOracle_unitary (ι := ι) D m d) S S' hS hS' E hE _
      hOutput _ hSeed x
      (Compiled.program_seed_congr p S S' E hE _ seed x htrue hfalse) j]

/-- Matrix counts of the compiled trials, for any counted interfaces. -/
theorem publicTrialsS_matrix_cost (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι)
    (m d : ℕ) (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D m d))
    (S : Bool → X → SourceSpace ι n m →L[ℂ] SourceSpace ι n m)
    (E : SourceSpace ι n m →L[ℂ] MatrixSpace ι n Z m M d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E (Compiled.seedCoefficients c) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      ODECompiledSource.output E (Compiled.seedCoefficients c) = 1) (w : Query → ℕ) (j : ℕ) :
    (publicTrialsS D hM i0 m d p S E hE c seed hSeed hOutput j).cost
        (ODESourceQueryBudget.matrixWeight w) = 3 * ((2 * j + 1) * p.cost w) := by
  unfold publicTrialsS
  rw [ODECoordinateNativeControl.compile_matrix_cost, ODECountedAmplification.cost_eq,
    Compiled.program_matrix_cost]

/-- Interface counts of the compiled trials, for any counted interfaces. -/
theorem publicTrialsS_source_cost (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι)
    (m d : ℕ) (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D m d))
    (S : Bool → X → SourceSpace ι n m →L[ℂ] SourceSpace ι n m)
    (E : SourceSpace ι n m →L[ℂ] MatrixSpace ι n Z m M d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E (Compiled.seedCoefficients c) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      ODECompiledSource.output E (Compiled.seedCoefficients c) = 1) (b : Bool) (j : ℕ) :
    (publicTrialsS D hM i0 m d p S E hE c seed hSeed hOutput j).cost
        (ODESourceQueryBudget.sourceWeight b) = 2 * j + 1 := by
  unfold publicTrialsS
  rw [ODECoordinateNativeControl.compile_source_cost, ODECountedAmplification.cost_eq,
    Compiled.program_source_cost, mul_one]

end Native


/-! ### The actual oracles `P_w`, `Lo`, `P_w†` -/

namespace Oracles

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s M m : ℕ}

/-- The supplied source operations with the loader `Lo` on the whole branch register. -/
def sourceOperationL (Pw : X → Weights.LabelOp (Option (Fin m)))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m) :
    SourceCall → X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m
  | .weight, x => Weights.act (Pw x)
  | .load, x => Lo x
  | .unweight, x => Weights.act ((Pw x)†)

omit [DecidableEq ι] [DecidableEq n] in
theorem sourceOperationL_unitary {Pw : X → Weights.LabelOp (Option (Fin m))}
    (hPw : ∀ x, IsUnitary (Pw x))
    {Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m}
    (hLo : ∀ x, IsUnitary (Lo x)) :
    ∀ k x, IsUnitary (sourceOperationL (ι := ι) Pw Lo k x)
  | .weight, x => Weights.act_unitary (hPw x)
  | .load, x => hLo x
  | .unweight, x => Weights.act_unitary (Compiled.adjoint_unitary (hPw x))

/-- The actual primitive oracles with the loader `Lo`: the coherent sampled-time matrix calls,
and `P_w`, `Lo`, `P_w†`, each with its enable control. -/
def actualOracleL (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m) :
    Query ⊕ SourceCall → X →
      Native.PhysicalSpace ι n Z m M d →L[ℂ] Native.PhysicalSpace ι n Z m M d :=
  Sum.elim
    (fun l => NativeMaskedOracle.oracle (ι := Native.SourceBasis ι n m)
      (fun x => (Native.matrixLayout (ι := ι) (n := n) (Z := Z) m M d).conjStarAlgEquiv
        (Native.matrixOracle (ι := ι) D m d l x)))
    (fun k x => ODESectorTensor.sourcePhysical (B := Native.MatrixBasis ι n Z m M d)
      ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv
        (sourceOperationL Pw Lo k x)))

omit [DecidableEq ι] [DecidableEq Z] in
/-- The released actual oracles are those with the label-controlled loader. -/
theorem actualOracle_eq_actualOracleL (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    actualOracle (ι := ι) D m d Pw J =
      actualOracleL D m d Pw (fun x => Weights.loader (J x)) := by
  funext l x
  rcases l with l | k
  · rfl
  · cases k <;> rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem actualOracleL_unitary (D : Data (X × Fin M) n Z s) (m d : ℕ)
    {Pw : X → Weights.LabelOp (Option (Fin m))} (hPw : ∀ x, IsUnitary (Pw x))
    {Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m}
    (hLo : ∀ x, IsUnitary (Lo x)) :
    ∀ l x, IsUnitary (actualOracleL (ι := ι) D m d Pw Lo l x) := by
  intro l x
  cases l with
  | inl l =>
      exact NativeMaskedOracle.oracle_unitary _
        (fun y => (Native.matrixOracle_unitary (ι := ι) D m d l y).transport
          (Native.matrixLayout (ι := ι) (n := n) (Z := Z) m M d)) x
  | inr k =>
      exact ODESectorTensor.sourcePhysical_unitary _
        ((sourceOperationL_unitary hPw hLo k x).transport
          (Native.sourceLayout (ι := ι) (n := n) m))

/-- Each counted interface call as a program over the actual oracles with the loader `Lo`:
`P_w`, then `Lo`, then the public phases; and `P_w†`. -/
def implementationL (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) :
    Query ⊕ Bool → MultiOracleCircuit.Program (actualOracleL (ι := ι) D m d Pw Lo)
  | .inl l => .query (.inl l)
  | .inr false => .seq (.fixed (phaseGate m M d φ) (phaseGate_unitary m M d hφ))
      (.seq (.query (.inr .load)) (.query (.inr .weight)))
  | .inr true => .query (.inr .unweight)

/-- The implementations are exact. -/
theorem implementationL_eval (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) (x : X) :
    (implementationL (ι := ι) D m d Pw Lo φ hφ l).eval x =
      Native.physicalOracleS (ι := ι) D m d (Compiled.sourceFamilyL Pw Lo φ) l x := by
  rcases l with l | b
  · rfl
  · cases b with
    | true => rfl
    | false =>
        change phaseGate m M d φ *
            (ODESectorTensor.sourcePhysical (B := Native.MatrixBasis ι n Z m M d)
              ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv (Lo x)) *
            ODESectorTensor.sourcePhysical (B := Native.MatrixBasis ι n Z m M d)
              ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv
                (Weights.act (Pw x)))) =
          ODESectorTensor.sourcePhysical (B := Native.MatrixBasis ι n Z m M d)
            ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv
              (Compiled.prepL (Pw x) (Lo x) φ))
        rw [phaseGate, ← sourcePhysical_mul, ← sourcePhysical_mul, ← map_mul, ← map_mul]
        rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem implementationL_matrix (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) :
    (implementationL (ι := ι) D m d Pw Lo φ hφ l).cost matrixCalls =
      ODESourceQueryBudget.matrixWeight (fun _ => 1) l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem implementationL_weight (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) :
    (implementationL (ι := ι) D m d Pw Lo φ hφ l).cost (calls .weight) =
      ODESourceQueryBudget.sourceWeight false l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem implementationL_load (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) :
    (implementationL (ι := ι) D m d Pw Lo φ hφ l).cost (calls .load) =
      ODESourceQueryBudget.sourceWeight false l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem implementationL_unweight (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) :
    (implementationL (ι := ι) D m d Pw Lo φ hφ l).cost (calls .unweight) =
      ODESourceQueryBudget.sourceWeight true l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem implementationL_source (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) :
    (implementationL (ι := ι) D m d Pw Lo φ hφ l).cost sourceCalls =
      2 * ODESourceQueryBudget.sourceWeight false l +
        ODESourceQueryBudget.sourceWeight true l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

/-- The trial family over the actual oracles with the loader `Lo`. -/
def actualTrialsL (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1)
    (q : ℕ → MultiOracleCircuit.Program
      (Native.physicalOracleS (ι := ι) D m d (Compiled.sourceFamilyL Pw Lo φ))) :
    ℕ → MultiOracleCircuit.Program (actualOracleL (ι := ι) D m d Pw Lo) :=
  fun j => (q j).substitute (implementationL D m d Pw Lo φ hφ)

section Certificate

variable {P R Y : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [FiniteDimensional ℂ P]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The released complete certificate transfers through evaluations on the seed only**: as
`actual_certificate`, with the trial evaluations agreeing on the public seed instead of as
operators. -/
theorem actual_certificate_seed {L : Type*} {O : (L ⊕ Bool) → Y → R →L[ℂ] R}
    {O' : Query ⊕ SourceCall → Y → R →L[ℂ] R}
    {q : ℕ → MultiOracleCircuit.Program O} {M : ℕ} {ψ : R} {F : P →L[ℂ] R} {y : Y}
    {target : P} {s Θ ell g ε : ℝ}
    (hCert : ODECompleteTrial.Certificate q M ψ F y target s Θ ell g ε)
    (q' : ℕ → MultiOracleCircuit.Program O') (hM : 0 < M) (hψ : ‖ψ‖ = 1) (hF : F† ∘L F = 1)
    (hEval : ∀ j, (q' j).eval y ψ = (q j).eval y ψ)
    (hMatrix : ∀ j, (q' j).cost matrixCalls =
      (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)))
    (hWeight : ∀ j, (q' j).cost (calls .weight) =
      (q j).cost (ODESourceQueryBudget.sourceWeight false))
    (hLoad : ∀ j, (q' j).cost (calls .load) =
      (q j).cost (ODESourceQueryBudget.sourceWeight false))
    (hUnweight : ∀ j, (q' j).cost (calls .unweight) =
      (q j).cost (ODESourceQueryBudget.sourceWeight true))
    (hSource : ∀ j, (q' j).cost sourceCalls =
      2 * (q j).cost (ODESourceQueryBudget.sourceWeight false) +
        (q j).cost (ODESourceQueryBudget.sourceWeight true)) :
    ActualCertificate (ODERepeatProtocol.fourTrials q' M hM ψ hψ F hF) y target s Θ ell g ε := by
  obtain ⟨hSucc, hDens⟩ := ODERepeatProtocol.fourTrials_law_congr q' q M hM ψ hψ F hF y y
    (fun j _ => hEval j)
  have hAlg : ODECompleteTrial.algorithm hCert.trial =
      ODERepeatProtocol.fourTrials q M hM ψ hψ F hF := rfl
  have hSucc' : (ODERepeatProtocol.fourTrials q' M hM ψ hψ F hF).successMass y =
      (ODECompleteTrial.algorithm hCert.trial).successMass y := by
    rw [hAlg]
    exact hSucc
  have hDens' : (ODERepeatProtocol.fourTrials q' M hM ψ hψ F hF).conditionalDensity y =
      (ODECompleteTrial.algorithm hCert.trial).conditionalDensity y := by
    rw [hAlg]
    exact hDens
  have hTrial := hCert.trial
  refine
    { success_lower := ?_
      success_two_thirds := ?_
      matrix_queries := ?_
      weight_calls := ?_
      load_calls := ?_
      unweight_calls := ?_
      source_calls := ?_
      output_density := ?_
      conditional_error := ?_ }
  · rw [hSucc']
    exact hCert.success_lower
  · rw [hSucc']
    exact hCert.success_two_thirds
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q' M hM ψ hψ F hF matrixCalls
      (318504960 * g * ImprovedODEQueryBudget.queryShape s Θ ell)
      (fun j hj => by rw [hMatrix j]; exact hTrial.matrix_queries j hj)
    calc
      _ ≤ 4 * (318504960 * g * ImprovedODEQueryBudget.queryShape s Θ ell) := h
      _ = 1274019840 * g * ImprovedODEQueryBudget.queryShape s Θ ell := by ring
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q' M hM ψ hψ F hF (calls .weight)
      (10 * g) (fun j hj => by rw [hWeight j]; exact hTrial.source_queries j hj false)
    linarith
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q' M hM ψ hψ F hF (calls .load)
      (10 * g) (fun j hj => by rw [hLoad j]; exact hTrial.source_queries j hj false)
    linarith
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q' M hM ψ hψ F hF (calls .unweight)
      (10 * g) (fun j hj => by rw [hUnweight j]; exact hTrial.source_queries j hj true)
    linarith
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q' M hM ψ hψ F hF sourceCalls
      (30 * g) (fun j hj => by
        rw [hSource j]
        push_cast
        have h1 := hTrial.source_queries j hj false
        have h2 := hTrial.source_queries j hj true
        linarith)
    linarith
  · rw [hDens']
    exact hCert.output_density
  · rw [hDens']
    exact hCert.conditional_error

end Certificate

section Columns

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s M m : ℕ}

/-- **The complete certificate transfers from a label-controlled loader to any loader with the
same value on the seed branch state after `P_w`.** If the public trial family with the
label-controlled interfaces `loader J` has the released complete certificate, then the
four-attempt protocol over the actual oracles `P_w`, `Lo`, `P_w†` has the complete certificate
`ActualCertificate`, for every unitary `Lo` with
`Lo (P_w ⊗ 1)|seed state⟩ = loader J (P_w ⊗ 1)|seed state⟩`. -/
theorem columns_certificate (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m d : ℕ)
    (p : MultiOracleCircuit.Program (Native.matrixOracle (ι := ι) D m d))
    (Pw : X → Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (hLo : ∀ x, IsUnitary (Lo x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a)) (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1)
    (E : Native.SourceSpace ι n m →L[ℂ] Native.MatrixSpace ι n Z m M d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E (Compiled.seedCoefficients c) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      ODECompiledSource.output E (Compiled.seedCoefficients c) = 1)
    (x : X) {Mc : ℕ} (hMc : 0 < Mc) {target : EuclideanSpace ℂ n} {s' Θ ell g ε : ℝ}
    (hψ : ‖Native.input D hM i0 m d
      (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed)‖ = 1)
    (hF : (Native.input D hM i0 m d ∘L
        ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      (Native.input D hM i0 m d ∘L ODECompiledSource.output E (Compiled.seedCoefficients c)) = 1)
    (hCert : ODECompleteTrial.Certificate
      (Native.publicTrials D hM i0 m d p Pw J φ E hE c seed hSeed hOutput) Mc
      (Native.input D hM i0 m d (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed))
      (Native.input D hM i0 m d ∘L ODECompiledSource.output E (Compiled.seedCoefficients c))
      x target s' Θ ell g ε)
    (hagree : Lo x (Weights.act (Pw x)
        (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed)) =
      Weights.loader (J x) (Weights.act (Pw x)
        (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed))) :
    ActualCertificate (ODERepeatProtocol.fourTrials (actualTrialsL D m d Pw Lo φ hφ
        (Native.publicTrialsS D hM i0 m d p (Compiled.sourceFamilyL Pw Lo φ) E hE c seed hSeed
          hOutput)) Mc hMc _ hψ _ hF) x target s' Θ ell g ε := by
  rw [Native.publicTrials_eq_publicTrialsS] at hCert
  have hfalse : Compiled.sourceFamilyL (ι := ι) Pw Lo φ false x
      (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed) =
      Native.sourceFamily (ι := ι) Pw J φ false x
        (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed) := by
    rw [Compiled.sourceFamilyL_false, Native.sourceFamily, Compiled.sourceFamily_false]
    unfold Compiled.prepL Compiled.prep
    simp only [comp_apply]
    rw [hagree]
  have hEval : ∀ j, (actualTrialsL D m d Pw Lo φ hφ
      (Native.publicTrialsS D hM i0 m d p (Compiled.sourceFamilyL Pw Lo φ) E hE c seed hSeed
        hOutput) j).eval x =
      (Native.publicTrialsS D hM i0 m d p (Compiled.sourceFamilyL Pw Lo φ) E hE c seed hSeed
        hOutput j).eval x := fun j =>
    MultiOracleCircuit.Program.eval_substitute _ _ (implementationL_eval D m d Pw Lo φ hφ) x
  apply actual_certificate_seed hCert _ hMc hψ hF
  · intro j
    rw [hEval j]
    have h := Native.publicTrialsS_seed_congr D hM i0 m d p (Compiled.sourceFamilyL Pw Lo φ)
      (Native.sourceFamily Pw J φ)
      (Compiled.sourceFamilyL_unitary hPw hLo hφ) (Compiled.sourceFamily_unitary hPw hJ hφ)
      E hE c seed hSeed hOutput x
      ((Compiled.sourceFamilyL_true Pw Lo φ x).trans (Compiled.sourceFamily_true Pw J φ x).symm)
      hfalse j
    convert h using 2
  · intro j
    simp only [actualTrialsL, MultiOracleCircuit.Program.cost_substitute, implementationL_matrix,
      Native.publicTrialsS_matrix_cost]
  · intro j
    simp only [actualTrialsL, MultiOracleCircuit.Program.cost_substitute, implementationL_weight,
      Native.publicTrialsS_source_cost]
  · intro j
    simp only [actualTrialsL, MultiOracleCircuit.Program.cost_substitute, implementationL_load,
      Native.publicTrialsS_source_cost]
  · intro j
    simp only [actualTrialsL, MultiOracleCircuit.Program.cost_substitute,
      implementationL_unweight, Native.publicTrialsS_source_cost]
  · intro j
    simp only [actualTrialsL, MultiOracleCircuit.Program.cost_substitute]
    rw [funext (implementationL_source D m d Pw Lo φ hφ), cost_add,
      NativeHermitianDilation.cost_scale]
    simp only [Native.publicTrialsS_source_cost]

end Columns

end Oracles


/-! ### The released solver with its public trial family exposed -/

section Solver

open Set TimeDependentODE

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- `GeneralSourceODE.PropagatedOutcome` with its public trial family named: the compiled family
`Native.publicTrials` of the SELECT program `p`, the supplied `P_w`, `J`, the public phases, the
clean encoding `E`, the LCHS coefficients and the seed. -/
def PublicOutcome (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (d : ℕ)
    (E : Native.SourceSpace (Index D T (cq * gbar) ε) n m →L[ℂ]
      Native.MatrixSpace (Index D T (cq * gbar) ε) n Z m M d)
    (hE : E† ∘L E = 1)
    (p : MultiOracleCircuit.Program (Native.matrixOracle (ι := Index D T (cq * gbar) ε) D m d))
    (hSeedU : ‖ODECompiledSource.seed E
      (Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E
        (Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)))† ∘L
      ODECompiledSource.output E
        (Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)) = 1),
    ∀ (x : X) (G : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b sol : ℝ → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (βG δG ζ : ℝ), 0 ≤ βG →
      (∀ u ∈ Icc 0 T, Accretive (G u)) →
      (∀ u ∈ Icc 0 T, ∀ w ∈ Icc 0 T, ‖G u - G w‖ ≤ βG * |u - w|) →
      (∀ r : Fin M, ‖G ((r : ℕ) * T / M) -
        SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δG) →
      SolvesODE G b sol 0 T →
      IsPropagator G U T →
      Compiled.WeightPrep (Pw x) (sources (sol 0) (fun i => b (v i)) ω) →
      (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → b (v i) ≠ 0 → J x (some i) seed =
        ODEStateNormalization.unitDirection (b (v i))) →
      ODESourceBranches.mass (sources (sol 0) (fun i => b (v i)) ω) ≤
        cq * sourceScale sol b T →
      ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (b (v i)) T‖ ≤
        ζ * sourceScale sol b T →
      sol T ≠ 0 →
      sourceScale sol b T ≤ gbar * ‖sol T‖ →
      ζ + cq * (T * (βG * (T / M) + δG)) ≤ ε / (2000 * gbar) →
      ODECompleteTrial.Certificate
        (Native.publicTrials (ι := Index D T (cq * gbar) ε) D hM (Sum.inr false) m d p Pw J
          (phases ω) E hE (lchsCoefficients D T (cq * gbar) ε) seed hSeedU hOutput)
        (ODEGroverAverage.chosenIterations (ratio (cq * gbar)))
        (Native.input (ι := Index D T (cq * gbar) ε) D hM (Sum.inr false) m d
          (ODECompiledSource.seed E
            (Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)) seed))
        (Native.input (ι := Index D T (cq * gbar) ε) D hM (Sum.inr false) m d ∘L
          ODECompiledSource.output E
            (Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)))
        x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε

set_option maxHeartbeats 4000000 in
/-- **`GeneralSourceODE.propagated_solver` with its public trial family exposed.** The released
proof; only the conclusion names the trial family (`PublicOutcome`), which `PropagatedOutcome`
leaves existential. -/
theorem propagated_solver_public (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 < T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hρ : 0 < etaH + radius (cq * gbar) ε * etaD)
    (hMesh : 8 * s * ((etaH + radius (cq * gbar) ε * etaD) * T) ≤ M)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
        precision (cq * gbar) ε * (M : ℝ) ^ 2)
    (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    PublicOutcome D hM etaH etaD T gbar cq ε v ω Pw J seed := by
  set g : ℝ := cq * gbar with hgdef
  have hg1 : 1 ≤ g := by nlinarith
  have hg' : 1 ≤ ratio g := by unfold ratio; linarith
  have hε' : 0 < accuracy ε := by unfold accuracy; linarith
  have hε'One : accuracy ε ≤ 1 := by unfold accuracy; linarith
  have hε'Half : accuracy ε ≤ 1 / 2 := by unfold accuracy; linarith
  have hν : 0 < precision g ε := ImprovedODEQueryBudget.precision_pos _ _ hg' hε'
  have hνOne : precision g ε ≤ 1 :=
    (ImprovedODEQueryBudget.precision_le_one_ten_thousandth _ _ hg' hε'One).trans
      (by norm_num)
  have hR : 0 ≤ radius g ε := ImprovedODEQueryBudget.radius_nonneg _ _ hg' hε' hε'One
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  -- One public Gaussian table for every product family.
  have hL : 0 ≤ lipschitz D T :=
    mul_nonneg hT.le (mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le)
  obtain ⟨_hGrid, hNodes, hMass, hApprox⟩ := GaussianLCHS.table_certificate
    (fun y : X × Option (Fin m) => family D hM T v y.1 y.2)
    (fun y z => family_analyticAt D hM T v y.1 y.2 z)
    (fun y z hz => family_norm_le_one D hM T hT.le v hPSD y.1 y.2 z hz)
    (lipschitz D T) hL (fun y k l => family_lipschitz D hM T hT.le v y.1 y.2 k l)
    (ratio g) (accuracy ε) hg' hε' hε'One
  have hc : ODECoherentLCU.coefficientMass (lchsCoefficients D T g ε) = 3 :=
    ODECoefficientPadding.coefficientMass_eq _ 3 hMass
  -- One public SELECT program for the public node and duration tables.
  let i0 : Index D T g ε := Sum.inr false
  obtain ⟨γ, _hγ, _hγOne, _hWidth, hTables⟩ :=
    Select.select (ι := Native.Label (Index D T g ε) m) D hM
      (Native.dummy hM i0 m) etaH etaD (radius g ε) T (precision g ε)
      hH hDiss hρ hT hν hνOne hrH hcH hrD hcD hMesh hCayley
  have hk : ∀ a, |nodeTable D T g ε m a| ≤ radius g ε := fun a =>
    ODECoefficientPadding.paddedNodes_bound _ _ hR hNodes a.2
  have hu : ∀ (a : Native.Label (Index D T g ε) m) (r : Fin M),
      0 ≤ durationTable T v a r := fun a r => durations_nonneg hT.le v a.1 r
  have huT : ∀ (a : Native.Label (Index D T g ε) m) (r : Fin M),
      durationTable T v a r ≤ T := fun a r => durations_le hT.le hM v a.1 r
  obtain ⟨p, hCount, hE, hAct⟩ := hTables (nodeTable D T g ε m) (durationTable T v) hk hu huT
  let d := Select.degree (s : ℝ) γ (etaH + radius g ε * etaD) T (precision g ε) M
  let E : Native.SourceSpace (Index D T g ε) n m →L[ℂ]
      Native.MatrixSpace (Index D T g ε) n Z m M d :=
    Select.alignedInput D hM (Native.dummy hM i0 m) γ (etaH + radius g ε * etaD) T
      (precision g ε)
  have hEiso : E† ∘L E = 1 := hE
  let pN : MultiOracleCircuit.Program
      (Native.matrixOracle (ι := Index D T g ε) D m d) := p
  let c := lchsCoefficients D T g ε
  have hcpos : 0 < ODECoherentLCU.coefficientMass c := by
    change 0 < ODECoherentLCU.coefficientMass (lchsCoefficients D T g ε)
    rw [hc]
    norm_num
  have hsc : 0 < ODECoherentLCU.coefficientMass (Compiled.seedCoefficients (N := m) c) := by
    rw [Compiled.seedCoefficients_mass]
    exact hcpos
  have hSeedUnit := ODECompiledSource.seed_unit E (Compiled.seedCoefficients c) hEiso hsc
    seed hSeed
  have hOutput := ODECompiledSource.output_isometry E (Compiled.seedCoefficients c) hEiso hsc
  let q := Native.publicTrials D hM i0 m d pN Pw J (phases ω) E hEiso c seed
    hSeedUnit hOutput
  have hq : (pN.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ)
      (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
      (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) :=
    ODEFinitePropagator.query_bound p.count (s : ℝ) etaH etaD T (ratio g) (accuracy ε)
      (Nat.cast_nonneg s) hH hDiss hT.le hg' hε' hε'One hCount
  have hOracle := Native.physicalOracle_unitary (ι := Index D T g ε) D m d Pw hPw J hJ
    (phases ω) (phases_norm ω)
  refine ⟨d, E, hEiso, pN, hSeedUnit, hOutput, ?_⟩
  intro x G b sol U βG δG ζ hβG hG hGLip hGs _hsol hU hW hLoad₀ hLoad hMassB hCert
    hTarget hB hBudget
  -- The propagated target of the represented samples.
  let Gs := Sampling.generator D hM x
  have hGsAcc : ∀ r, Accretive (Gs r) := Sampling.generator_accretive D hM hPSD x
  let bv : Fin m → EuclideanSpace ℂ n := fun i => b (v i)
  let z := sources (sol 0) bv ω
  let y := nodeTarget Gs T M v (sol 0) bv ω
  set Bs := sourceScale sol b T with hBs
  have hδG : 0 ≤ δG := (norm_nonneg _).trans (hGs ⟨0, hM⟩)
  have hGs' : ∀ r < M, ‖G (r * T / M) - Gs r‖ ≤ δG := by
    intro r hr
    have hidx : TimeDependent.Sampled.sampleIndex hM r = ⟨r, hr⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hr)
    change ‖G (r * T / M) - SparseStateOverlap.matrixOperator
      (D.matrix (x, TimeDependent.Sampled.sampleIndex hM r))‖ ≤ δG
    rw [hidx]
    exact hGs ⟨r, hr⟩
  have hTargetErr := target_error hT.le hM v hv ω G hG Gs hGsAcc βG δG hβG hδG hGLip hGs'
    U hU (sol 0) bv
  set K : ℝ := βG * (T / M) + δG with hK
  have hK0 : 0 ≤ K := add_nonneg (mul_nonneg hβG (div_nonneg hT.le hMR.le)) hδG
  have hBs0 : 0 ≤ Bs :=
    add_nonneg (norm_nonneg _) (intervalIntegral.integral_nonneg hT.le fun u _ => norm_nonneg _)
  have hErr : ‖sol T - y‖ ≤ (ζ + cq * (T * K)) * Bs := by
    have hsplit : sol T - y =
        (sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (b (v i)) T) +
          ((U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T) - y) := by
      simp only [bv]
      abel
    rw [hsplit]
    have hMassK : T * K * ODESourceBranches.mass z ≤ cq * (T * K) * Bs := by
      have hTK : 0 ≤ T * K := mul_nonneg hT.le hK0
      calc
        T * K * ODESourceBranches.mass z ≤ T * K * (cq * Bs) :=
          mul_le_mul_of_nonneg_left hMassB hTK
        _ = cq * (T * K) * Bs := by ring
    calc
      _ ≤ ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (b (v i)) T‖ +
          ‖(U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T) - y‖ := norm_add_le _ _
      _ ≤ ζ * Bs + T * K * ODESourceBranches.mass z := add_le_add hCert hTargetErr
      _ ≤ ζ * Bs + cq * (T * K) * Bs := add_le_add le_rfl hMassK
      _ = (ζ + cq * (T * K)) * Bs := by ring
  have hErrBudget : (ζ + cq * (T * K)) * Bs ≤ ε * Bs / (2000 * gbar) := by
    have h := mul_le_mul_of_nonneg_right hBudget hBs0
    calc
      (ζ + cq * (T * K)) * Bs ≤ ε / (2000 * gbar) * Bs := h
      _ = ε * Bs / (2000 * gbar) := by ring
  obtain ⟨hy, hBy, hDir⟩ := Sampling.target_budget (sol T) y Bs gbar ε _ hg hε hεOne
    hTarget hB hErr hErrBudget
  have hNorm : ‖y‖ ≤ ODESourceBranches.mass z :=
    nodeTarget_norm_le Gs hGsAcc hT.le M v (sol 0) bv ω
  have hz : 0 < ODESourceBranches.mass z := ODESourceBranches.mass_pos_of_solution z y hy hNorm
  have hBudget' : ODESourceBranches.mass z ≤ ratio g * ‖y‖ := by
    have hcq0 : 0 ≤ cq := by linarith
    calc
      ODESourceBranches.mass z ≤ cq * Bs := hMassB
      _ ≤ cq * (2 * gbar * ‖y‖) := mul_le_mul_of_nonneg_left hBy hcq0
      _ = ratio g * ‖y‖ := by rw [hgdef]; unfold ratio; ring
  -- Hypotheses of the released actual-source certificate.
  have hJph : ∀ a, (Compiled.phased (J x) (phases ω) a)† ∘L
      Compiled.phased (J x) (phases ω) a = 1 :=
    phased_isometry (J x) (hJ x) ω
  have hPrep := phased_prepares (J x) (sol 0) bv ω seed hLoad₀ hLoad
  have hSim : ‖pN.eval x ∘L E - E ∘L WeightedClock.diagonal
      (fun a' : Option (Fin m) × Index D T g ε =>
        Select.branchEvolution D hM (nodeTable D T g ε m) (durationTable T v) x
          (a'.1, a'.2))‖ ≤ ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) :=
    (hAct x).2
  have hLCHS : ∀ a', ‖(∑ i, lchsCoefficients D T g ε i •
      Select.branchEvolution D hM (nodeTable D T g ε m) (durationTable T v) x (a', i)) -
        family D hM T v x a' (-Complex.I)‖ ≤
          2 * ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) := by
    intro a'
    have hsum : (∑ i, lchsCoefficients D T g ε i •
        Select.branchEvolution D hM (nodeTable D T g ε m) (durationTable T v) x (a', i)) =
          ∑ j, GaussianLCHS.coefficients (lipschitz D T) (ratio g) (accuracy ε) j •
            family D hM T v x a'
              (GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j : ℂ) := by
      simp only [branchEvolution_eq_family]
      exact Sampling.padded_sum _ _ _
    rw [hsum]
    exact hApprox (x, a')
  have hQuad : ‖(∑ a', family D hM T v x a' (-Complex.I) (z a')) - y‖ ≤
      ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) * ODESourceBranches.mass z := by
    have hsum : (∑ a', family D hM T v x a' (-Complex.I) (z a')) = y := by
      apply Finset.sum_congr rfl
      intro a' _
      rw [family_neg_I]
    rw [hsum, sub_self, norm_zero]
    exact mul_nonneg hν.le (ODESourceBranches.mass_nonneg z)
  have hCertS : ODEActualSourceError.Certificate E z c
      (Compiled.phased (J x) (phases ω)) (pN.eval x) seed y (ratio g) (accuracy ε) :=
    ODEActualSourceError.actual_source_certificate E hEiso z c hc
      (Compiled.phased (J x) (phases ω)) hJph seed hSeed hPrep (pN.eval x) (hAct x).1
      (fun a' i => Select.branchEvolution D hM (nodeTable D T g ε m)
        (durationTable T v) x (a', i))
      (fun a' => family D hM T v x a' (-Complex.I)) y (ratio g) (accuracy ε)
      hy hg' hε' hε'Half hNorm hBudget' hSim hLCHS hQuad
  -- The released primitive trial certificate, then the solution direction.
  have hTrial := Native.trial_certificate D hM i0 m d pN Pw hPw J hJ (phases ω)
    (phases_norm ω) E hEiso z c hcpos seed y hSeed
    (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
    (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) (ratio g) (accuracy ε) hg' x
    hz hW hCertS hq hSeedUnit hOutput
  have hFinal := retarget (η' := ε / 500) hTrial hDir (by unfold accuracy; linarith)
  exact ODECompleteTrial.of_trialCertificate
    (fun j => (q j).eval_unitary hOracle x) hε.le hTarget hFinal

/-! ### A label-controlled family with the clean columns of a loader -/

/-- Two unit vectors are related by a unitary. -/
theorem exists_unitary_map {ν : Type*} [Fintype ν] (s u : EuclideanSpace ℂ ν) (hs : ‖s‖ = 1)
    (hu : ‖u‖ = 1) :
    ∃ W : EuclideanSpace ℂ ν →L[ℂ] EuclideanSpace ℂ ν, IsUnitary W ∧ W s = u := by
  obtain ⟨W, hW, hWA⟩ := GeneralODE.Registers.exists_unitary_comp (P := EuclideanSpace ℂ Unit)
    (V := EuclideanSpace ℂ ν) (GeneralODE.Registers.lineMap s) (GeneralODE.Registers.lineMap u)
    (GeneralODE.Registers.lineMap_isometry s hs) (GeneralODE.Registers.lineMap_isometry u hu)
  refine ⟨W, hW, ?_⟩
  have h := congrArg (fun T : EuclideanSpace ℂ Unit →L[ℂ] EuclideanSpace ℂ ν =>
    T (EuclideanSpace.single () 1)) hWA
  simpa [GeneralODE.Registers.lineMap_apply] using h

/-- A unitary carrying the seed to `u` when both are unit vectors, and the identity otherwise. -/
def loadUnitary {ν : Type*} [Fintype ν] (seed u : EuclideanSpace ℂ ν) :
    EuclideanSpace ℂ ν →L[ℂ] EuclideanSpace ℂ ν :=
  if h : ‖seed‖ = 1 ∧ ‖u‖ = 1 then Classical.choose (exists_unitary_map seed u h.1 h.2) else 1

theorem loadUnitary_unitary {ν : Type*} [Fintype ν] (seed u : EuclideanSpace ℂ ν) :
    IsUnitary (loadUnitary seed u) := by
  unfold loadUnitary
  split_ifs with h
  · exact (Classical.choose_spec (exists_unitary_map seed u h.1 h.2)).1
  · exact isUnitary_one

theorem loadUnitary_apply {ν : Type*} [Fintype ν] (seed u : EuclideanSpace ℂ ν)
    (hs : ‖seed‖ = 1) (hu : ‖u‖ = 1) : loadUnitary seed u seed = u := by
  unfold loadUnitary
  rw [dif_pos ⟨hs, hu⟩]
  exact (Classical.choose_spec (exists_unitary_map seed u hs hu)).2

/-- The label-controlled family read off the clean columns of the loader `Lo` at the clock label
`τ₀`: on label `a`, a unitary carrying the seed to the data of `Lo |a, τ₀⟩|seed⟩`. It is used only
inside the proof of `solver_columns`; the circuits call `Lo`. -/
def columnLoader {ι ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype ν] {m : ℕ}
    (Lo : X → Native.SourceSpace ι ν m →L[ℂ] Native.SourceSpace ι ν m)
    (seed : EuclideanSpace ℂ ν) (τ₀ : ι) :
    X → Option (Fin m) → EuclideanSpace ℂ ν →L[ℂ] EuclideanSpace ℂ ν :=
  fun x a => loadUnitary seed ((Lo x (PiLp.single 2 (a, τ₀) seed)) (a, τ₀))

/-! ### The solver with a loader specified on its clean columns -/

/-- **The guarantee of `GeneralSourceODE.solver` for a loader specified on its clean columns.**
One public trial family over the actual oracles `P_w`, `Lo`, `P_w†` and the coherent sampled-time
matrix oracle, chosen before every unknown instance. The loader `Lo` is a unitary on the whole
branch register; the instance hypotheses fix it only on the clean columns `|a, τ⟩|seed⟩` of the
source labels with nonzero source vectors, where it must prepare `x(0)/‖x(0)‖` and
`b(v_i)/‖b(v_i)‖` and keep the labels. All other hypotheses and the guarantee are those of
`GeneralSourceODE.Outcome`. -/
def OutcomeColumns (D : Data (X × Fin M) n Z s) (etaH etaD T gbar cq ε : ℝ) {m : ℕ}
    (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (Lo : X → Native.SourceSpace (Index D T (cq * gbar) ε) n m →L[ℂ]
      Native.SourceSpace (Index D T (cq * gbar) ε) n m)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (d : ℕ) (t : ODERepeatProtocol.TrialFamily
      (Oracles.actualOracleL (ι := Index D T (cq * gbar) ε) D m d Pw Lo) (EuclideanSpace ℂ n)),
    t.choices = ODEGroverAverage.chosenIterations (ratio (cq * gbar)) ∧
    (∀ j y, IsUnitary ((t.circuit j).eval y)) ∧
    ∀ (x : X) (G : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b sol : ℝ → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (βG δG ζ : ℝ), 0 ≤ βG →
      (∀ u ∈ Icc 0 T, Accretive (G u)) →
      (∀ u ∈ Icc 0 T, ∀ w ∈ Icc 0 T, ‖G u - G w‖ ≤ βG * |u - w|) →
      (∀ r : Fin M, ‖G ((r : ℕ) * T / M) -
        SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δG) →
      ContinuousOn b (Icc 0 T) →
      SolvesODE G b sol 0 T →
      IsPropagator G U T →
      Compiled.WeightPrep (Pw x) (sources (sol 0) (fun i => b (v i)) ω) →
      (sol 0 ≠ 0 → ∀ τ : Index D T (cq * gbar) ε,
        Lo x (PiLp.single 2 (none, τ) seed) =
          PiLp.single 2 (none, τ) (ODEStateNormalization.unitDirection (sol 0))) →
      (∀ i, ω i ≠ 0 → b (v i) ≠ 0 → ∀ τ : Index D T (cq * gbar) ε,
        Lo x (PiLp.single 2 (some i, τ) seed) =
          PiLp.single 2 (some i, τ) (ODEStateNormalization.unitDirection (b (v i)))) →
      ODESourceBranches.mass (sources (sol 0) (fun i => b (v i)) ω) ≤
        cq * sourceScale sol b T →
      ‖(∫ u in (0 : ℝ)..T, U u (b u) T) - ∑ i, ω i • U (v i) (b (v i)) T‖ ≤
        ζ * sourceScale sol b T →
      sol T ≠ 0 →
      sourceScale sol b T ≤ gbar * ‖sol T‖ →
      ζ + cq * (T * (βG * (T / M) + δG)) ≤ ε / (2000 * gbar) →
      Oracles.ActualCertificate (ODERepeatProtocol.Protocol.repeatTrials t 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε

set_option maxHeartbeats 4000000 in
/-- **Time-dependent dissipative sparse ODE solver with the general source interface
(`ode:thm:time`) and a loader specified on its clean columns only (item D1, exact case).** Under
the hypotheses of `GeneralSourceODE.solver`, with the label-controlled `U_load` replaced by any
unitary `Lo` on the whole branch register: one public family of trial circuits over the coherent
sampled-time matrix oracle and the supplied `P_w`, `Lo` and `P_w†` gives, by four fresh trials,
`x(T)/‖x(T)‖` with conditional trace distance at most `ε` and success probability at least `2/3`,
with at most `1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)` matrix queries and at most `40 g'` calls of
each of `P_w`, `Lo` and `P_w†` in every history, for every instance satisfying the hypotheses of
`GeneralSourceODE.Outcome` with the loading hypotheses stated on the clean columns of `Lo`.

The trials call `Lo` and its inverse. Their outputs depend on `Lo` only through its clean columns
of positive weight: `Native.publicTrialsS_seed_congr`, `Weights.act_seedInput` and
`Weights.clean_congr`. The certificate is then that of the released proof for the
label-controlled family `columnLoader Lo` with the same columns. -/
theorem solver_columns (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 < T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hρ : 0 < etaH + radius (cq * gbar) ε * etaD)
    (hMesh : 8 * s * ((etaH + radius (cq * gbar) ε * etaD) * T) ≤ M)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
        precision (cq * gbar) ε * (M : ℝ) ^ 2)
    (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (Lo : X → Native.SourceSpace (Index D T (cq * gbar) ε) n m →L[ℂ]
      Native.SourceSpace (Index D T (cq * gbar) ε) n m)
    (hLo : ∀ x, IsUnitary (Lo x))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    OutcomeColumns D etaH etaD T gbar cq ε v ω Pw Lo seed := by
  -- A label-controlled family with the clean columns of `Lo`; it is not called by the circuits.
  let J := columnLoader Lo seed (Sum.inr false)
  have hJ : ∀ x a, IsUnitary (J x a) := fun x a => loadUnitary_unitary _ _
  obtain ⟨d, E, hE, p, hSeedU, hOut, hCert⟩ := propagated_solver_public D hM etaH etaD T gbar cq
    ε v ω hH hDiss hT hg hcq hε hεOne hρ hMesh hCayley hv hrH hcH hrD hcD hPSD Pw hPw J hJ
    seed hSeed
  have hg1 : 1 ≤ ratio (cq * gbar) := by
    unfold ratio
    nlinarith
  obtain ⟨hMpos, -, -⟩ := ODEGroverAverage.chosenIterations_bounds (ratio (cq * gbar)) hg1
  have hcpos : 0 < ODECoherentLCU.coefficientMass (lchsCoefficients D T (cq * gbar) ε) := by
    have hL : 0 ≤ lipschitz D T :=
      mul_nonneg hT.le (mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le)
    have hε' : 0 < accuracy ε := by unfold accuracy; linarith
    have hε'One : accuracy ε ≤ 1 := by unfold accuracy; linarith
    obtain ⟨-, -, hMass, -⟩ := GaussianLCHS.table_certificate
      (fun y : X × Option (Fin m) => family D hM T v y.1 y.2)
      (fun y z => family_analyticAt D hM T v y.1 y.2 z)
      (fun y z hz => family_norm_le_one D hM T hT.le v hPSD y.1 y.2 z hz)
      (lipschitz D T) hL (fun y k l => family_lipschitz D hM T hT.le v y.1 y.2 k l)
      (ratio (cq * gbar)) (accuracy ε) hg1 hε' hε'One
    have hc : ODECoherentLCU.coefficientMass (lchsCoefficients D T (cq * gbar) ε) = 3 :=
      ODECoefficientPadding.coefficientMass_eq _ 3 hMass
    rw [hc]
    norm_num
  -- The public seed and output flag on the primitive workspace.
  have hψ := Native.seed_unit (ι := Index D T (cq * gbar) ε) D hM (Sum.inr false) m d E hE
    (lchsCoefficients D T (cq * gbar) ε) hcpos seed hSeed
  have hF := Native.output_isometry (ι := Index D T (cq * gbar) ε) D hM (Sum.inr false) m d E hE
    (lchsCoefficients D T (cq * gbar) ε) hcpos
  have hActual := Oracles.actualOracleL_unitary (ι := Index D T (cq * gbar) ε) D m d hPw hLo
  refine ⟨d, ODERepeatProtocol.ofCircuits (Oracles.actualTrialsL D m d Pw Lo (phases ω)
      (phases_norm ω) (Native.publicTrialsS (ι := Index D T (cq * gbar) ε) D hM (Sum.inr false) m d
        p (Compiled.sourceFamilyL Pw Lo (phases ω)) E hE (lchsCoefficients D T (cq * gbar) ε) seed
        hSeedU hOut))
    (ODEGroverAverage.chosenIterations (ratio (cq * gbar))) hMpos _ hψ _ hF, rfl,
    fun j y => MultiOracleCircuit.Program.eval_unitary _ hActual y, ?_⟩
  intro x G b sol U βG δG ζ hβG hG hGLip hGs hbc hsol hU hW hCol₀ hCol hMassB hInt
    hTarget hB hBudget
  -- The clean columns of `J` are those of `Lo`.
  have hcolJ : ∀ (a : Option (Fin m)) (u : EuclideanSpace ℂ n), u ≠ 0 →
      (∀ τ : Index D T (cq * gbar) ε, Lo x (PiLp.single 2 (a, τ) seed) =
        PiLp.single 2 (a, τ) (ODEStateNormalization.unitDirection u)) →
      J x a seed = ODEStateNormalization.unitDirection u := by
    intro a u hu h
    change loadUnitary seed ((Lo x (PiLp.single 2 (a, Sum.inr false) seed))
      (a, Sum.inr false)) seed = _
    rw [h (Sum.inr false), PiLp.single_eq_same]
    exact loadUnitary_apply seed _ hSeed (ODEStateNormalization.unitDirection_norm u hu)
  have hLoad₀ : sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0) :=
    fun h0 => hcolJ none (sol 0) h0 (hCol₀ h0)
  have hLoad : ∀ i, ω i ≠ 0 → b (v i) ≠ 0 → J x (some i) seed =
      ODEStateNormalization.unitDirection (b (v i)) :=
    fun i hω hb => hcolJ (some i) (b (v i)) hb (hCol i hω hb)
  -- Duhamel's formula turns the vector-integral certificate into the
  -- propagated-sum certificate.
  have hΛ : ∀ u ∈ Icc 0 T, ‖G u‖ ≤ ‖G 0‖ + βG * T := by
    intro u hu
    have h := hGLip u hu 0 ⟨le_rfl, hT.le⟩
    rw [sub_zero, abs_of_nonneg hu.1] at h
    calc
      ‖G u‖ = ‖G 0 + (G u - G 0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖G 0‖ + ‖G u - G 0‖ := norm_add_le _ _
      _ ≤ ‖G 0‖ + βG * T := add_le_add le_rfl (h.trans (mul_le_mul_of_nonneg_left hu.2 hβG))
  have hD := duhamel hT.le hU hG _ hΛ hbc hsol
  have hCertP : ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (b (v i)) T‖ ≤
      ζ * sourceScale sol b T := by
    rw [← hD]
    exact hInt
  -- The certificate of the label-controlled family `J`.
  have hC := hCert x G b sol U βG δG ζ hβG hG hGLip hGs hsol hU hW hLoad₀ hLoad hMassB
    hCertP hTarget hB hBudget
  -- `Lo` and the label-controlled `J` agree on the seed branch state after `P_w`.
  have hagree : Lo x (Weights.act (Pw x) (ODEJointLCU.coefficientInput
      (Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)) seed)) =
      Weights.loader (J x) (Weights.act (Pw x) (ODEJointLCU.coefficientInput
        (Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)) seed)) := by
    rw [Weights.act_seedInput]
    apply Weights.clean_congr
    intro bb hbb
    rw [Weights.loader_single]
    have hamp : Weights.amp (Pw x) bb.1 none ≠ 0 := fun h => hbb (by simp [h])
    rw [hW bb.1] at hamp
    have hz : sources (sol 0) (fun i => b (v i)) ω bb.1 ≠ 0 := by
      intro h0
      apply hamp
      simp [ODESourceBranches.probability, h0]
    rcases bb with ⟨a, τ⟩
    cases a with
    | none =>
        have h0 : sol 0 ≠ 0 := hz
        dsimp only
        rw [hCol₀ h0 τ, hLoad₀ h0]
    | some i =>
        have h0 : ω i • b (v i) ≠ 0 := hz
        obtain ⟨hω, hb⟩ := smul_ne_zero_iff.mp h0
        dsimp only
        rw [hCol i hω hb τ, hLoad i hω hb]
  exact Oracles.columns_certificate (ι := Index D T (cq * gbar) ε) D hM (Sum.inr false) m d p
    Pw hPw Lo hLo J hJ (phases ω) (phases_norm ω) E hE (lchsCoefficients D T (cq * gbar) ε) seed
    hSeedU hOut x hMpos hψ hF hC hagree

end Solver

end

end SparseHamiltonian.GeneralSourceODE
