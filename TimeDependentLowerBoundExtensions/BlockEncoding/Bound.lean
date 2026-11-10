import TimeDependentLowerBoundExtensions.BlockEncoding.Access

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Theorem `hsl:thm:main` for calls of time-indexed block encodings

The lower bound of Theorem `hsl:thm:main` applies to the time-dependent class with time-independent
hard instances (the manuscript, the paragraphs after the proof of Theorem `hs:thm:time`). Eqs.
`hs:eq:blockspecial` and `hs:eq:blockadditive` give only an upper bound in calls of a supplied
block encoding, and the text after eq. `hs:eq:blockadditive` compares the two access models
through their normalisations: a standard sparse block encoding has `α_BE = sη`. The manuscript
states no lower bound in block-encoding calls.

This module transfers Theorem `hsl:thm:main` to calls of the Hermitian dilation of the
released six-query sparse block encoding (`beOp`, normalisation `beAlpha = s·scale`, matching
`α_BE = sη`). The algorithms are programs over the released block-encoding oracle family
`TimeDependentExtensions.BlockEncoding.alignedOracle O N α T ε'` (any number `M` of samples,
slot count `N` and schedule), run on the constant Hermitian block encodings `beConst D M` of the
time, mixed and precision families (`O_r = beOp D x` for every `r`, `J = beJ D`,
`α_BE = beAlpha D`), with any isometric input encoding. The bound is stated in the sparse
parameters of the hard families; the factor `8` (each call costs at most `16` Boolean queries,
`nonempty_alignedAccess`, against `2` per value call of the native lower bound) and the choice
of this dilation are properties of the reduction, not constants of the manuscript.

* `BECriterion`: the error criterion of `TimeDependentExtensions.BlockEncoding.simulation` (every
  family of self-adjoint, interval-integrable pieces whose integrated sample errors against
  `α_BE J† O_r J` are at most `ε / 9`, every propagator from the identity, error at most `ε`
  at time `T`);
* `beCriterion_endpoint`: on the constant hard data the constant pieces are admissible with zero
  sample error (`blockSample_beOp`), so the criterion gives the endpoint error against
  `exp(-iτH_x)`;
* `main_max_block_endpoint`, `main_max_block`:
  `c₀ (√s τ + √(sτr) + r) ≤ 8 · max(Q_T, Q_M, Q_P)`,
  `Q` the number of block-encoding calls (inverses included);
* `main_max_block_primitive`: the same bound for programs over the controlled time-indexed oracle
  `TimeDependentExtensions.BlockEncoding.primitive` itself (coherent and controlled access to the
  `O_r`, eqs. `hs:eq:blockspecial` and `hs:eq:blockadditive`), endpoint form;
* `main_max_calls_block`: the same bound for programs over all call forms (plain, inverse,
  controlled, controlled inverse; `AdaptiveODELowerBound.Access.callFamily`) of the released
  aligned family, endpoint form.
-/

namespace TimeDependentLowerBoundExtensions.BlockEncoding

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit ContinuousLinearMap
open SparseHamiltonian.TimeDependent (SolvesOn)
open SparseLowerBounds SparseLowerBounds.Hamiltonian HsRelease
open TimeDependentHamiltonianLowerBound (constProp)
open MeasureTheory Set
open scoped InnerProduct InnerProductSpace

/-! ### The criterion of the released block-encoding theorem -/

section Criterion

variable {X n B₀ : Type*} [Fintype n] [DecidableEq n] [Fintype B₀] [DecidableEq B₀] {M : ℕ}
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **The error criterion of `TimeDependentExtensions.BlockEncoding.simulation`** for a run
`run x` with input encoding `ι` (the same encoding at both ends), samples `O`, boundary `J`,
normalisation `α`, mesh `t` with `M` intervals, final time `T` and error `ε`: for every
instance, every family of self-adjoint, interval-integrable pieces whose integrated sample
errors `∑_r ∫ ‖H_r(u) - α J† O_r J‖ du` are at most `ε / 9`, and every propagator `U` of that
path from the identity, `‖run x ∘ ι - ι ∘ U(T)‖ ≤ ε`. -/
def BECriterion (run : X → K →L[ℂ] K) (ι : EuclideanSpace ℂ n →L[ℂ] K)
    (O : X → Fin M → EuclideanSpace ℂ B₀ →L[ℂ] EuclideanSpace ℂ B₀)
    (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ B₀) (α : ℝ) (t : ℕ → ℝ) (T ε : ℝ) : Prop :=
  ∀ x, ∀ (Hp : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (U : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
    (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), star (Hp r u) = Hp r u) →
    (∀ r : Fin M, IntervalIntegrable (Hp r) volume (t r) (t ((r : ℕ) + 1))) →
    ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
        ‖Hp r u - TimeDependentExtensions.BlockEncoding.blockSample (O x r) J α‖ ≤ ε / 9 →
    U 0 = 1 →
    (∀ r : Fin M, SolvesOn (Hp r) U (t r) (t ((r : ℕ) + 1))) →
    ‖run x ∘L ι - ι ∘L U T‖ ≤ ε

end Criterion

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

/-- **The criterion on the constant hard data gives the endpoint error**: the constant pieces
`H_r(u) = H_x` are self-adjoint, integrable and have zero sample error against
`α_BE J† (beOp D x) J = H_x`, and `exp(-iuH_x)` is a propagator from the identity on every mesh
interval. -/
theorem beCriterion_endpoint {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (D : Data X N Z s) (hH : ∀ x, (D.matrix x).IsHermitian) (M : ℕ)
    (t : ℕ → ℝ) {τ ε : ℝ} (hε : 0 ≤ ε) (run : X → K →L[ℂ] K)
    (ι : EuclideanSpace ℂ N →L[ℂ] K)
    (hcrit : BECriterion run ι (beConst D M) (beJ D) (beAlpha D) t τ ε) (x : X) :
    ‖run x ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  have hS : ∀ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
      ‖SparseStateOverlap.matrixOperator (D.matrix x) -
        TimeDependentExtensions.BlockEncoding.blockSample (beConst D M x r) (beJ D)
          (beAlpha D)‖ = 0 := by
    intro r
    simp only [beConst, blockSample_beOp D hH x, sub_self, norm_zero,
      intervalIntegral.integral_zero]
  have h := hcrit x (fun _ _ => SparseStateOverlap.matrixOperator (D.matrix x))
    (constProp (SparseStateOverlap.matrixOperator (D.matrix x)))
    (fun _ _ _ => SparseHamiltonian.SparseValuePrecision.matrixOperator_star_eq _ (hH x))
    (fun _ => intervalIntegrable_const)
    (by rw [Finset.sum_eq_zero (fun r _ => hS r)]; linarith)
    (TimeDependentHamiltonianLowerBound.constProp_zero _)
    (fun _ => TimeDependentHamiltonianLowerBound.solvesOn_constProp _ _ _)
  exact h

/-! ### The three hard families -/

variable {τ ε : ℝ}

/-- The workspace of the aligned block-encoding family on the time family. -/
abbrev BETimeWork (τ : ℝ) (s M N : ℕ) (α T ε' : ℝ) : Type :=
  TimeDependentExtensions.BlockEncoding.Workspace
    (BEBasis (SearchIndex (timeN τ) (hsMu s) s)
      (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)))
    M N α T ε'

/-- The workspace of the aligned block-encoding family on the mixed family. -/
abbrev BEMixedWork (τ ε : ℝ) (s M N : ℕ) (α T ε' : ℝ) : Type :=
  TimeDependentExtensions.BlockEncoding.Workspace
    (BEBasis (SearchIndex (precN τ ε) (hsMu s) s) (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)))
    M N α T ε'

/-- The workspace of the aligned block-encoding family on the precision family. -/
abbrev BEPrecisionWork (τ ε : ℝ) (s M N : ℕ) (α T ε' : ℝ) : Type :=
  TimeDependentExtensions.BlockEncoding.Workspace
    (BEBasis (ScalarIndex (precN τ ε) s) (Word (scalarBits (precN τ ε) s τ))) M N α T ε'

/-- **Theorem `hsl:thm:main` for calls of time-indexed block encodings, endpoint form** (eq.
`hsl:eq:main`, `c₀ = log 2/(4096π)`): for any three programs over the released aligned
block-encoding families of the constant Hermitian block encodings of the time, mixed and
precision families (any numbers of samples, slot counts and schedules) and isometric
encodings, each with endpoint error `ε` against `exp(-iτH_x)`,
`c₀ (√s τ + √(sτr) + r) ≤ 8 · max(Q_T, Q_M, Q_P)`, `Q = p.count` the number of block-encoding
calls, inverses included. The factor `8` is a property of the reduction (`beOp`), not a
constant of the manuscript. -/
theorem main_max_block_endpoint (h : HSRange τ s ε) (MT MM MP NT NM NP : ℕ)
    (αT TT εT αM TM εM αP TP εP : ℝ)
    (pT : MultiOracleCircuit.Program (TimeDependentExtensions.BlockEncoding.alignedOracle
      (beConst (timeData τ s h.s_ge) MT) NT αT TT εT))
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      BETimeWork τ s MT NT αT TT εT) (hιT : ιT† ∘L ιT = 1)
    (hsimT : ∀ j, ‖pT.eval j ∘L ιT - ιT ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((timeData τ s h.s_ge).matrix j))‖ ≤ ε)
    (pM : MultiOracleCircuit.Program (TimeDependentExtensions.BlockEncoding.alignedOracle
      (beConst (mixedMainData τ ε s h.s_ge) MM) NM αM TM εM))
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      BEMixedWork τ ε s MM NM αM TM εM) (hιM : ιM† ∘L ιM = 1)
    (hsimM : ∀ j, ‖pM.eval j ∘L ιM - ιM ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((mixedMainData τ ε s h.s_ge).matrix j))‖ ≤ ε)
    (pP : MultiOracleCircuit.Program (TimeDependentExtensions.BlockEncoding.alignedOracle
      (beConst (precisionMainData τ ε s h.s_ge) MP) NP αP TP εP))
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
      BEPrecisionWork τ ε s MP NP αP TP εP) (hιP : ιP† ∘L ιP = 1)
    (hsimP : ∀ x, ‖pP.eval x ∘L ιP - ιP ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((precisionMainData τ ε s h.s_ge).matrix x))‖ ≤ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      8 * max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  have hs := h.s_ge
  have key := Core.main_max_uniform_weight h 16
    (TimeDependentExtensions.BlockEncoding.alignedOracle (beConst (timeData τ s h.s_ge) MT)
      NT αT TT εT)
    (alignedOracle_beConst_unitary _ MT NT αT TT εT)
    (nonempty_alignedAccess (timeData τ s h.s_ge)
      (searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)) MT NT αT TT εT)
    pT ιT hιT hsimT
    (TimeDependentExtensions.BlockEncoding.alignedOracle
      (beConst (mixedMainData τ ε s h.s_ge) MM) NM αM TM εM)
    (alignedOracle_beConst_unitary _ MM NM αM TM εM)
    (nonempty_alignedAccess (mixedMainData τ ε s h.s_ge)
      (searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)) MM NM αM TM εM)
    pM ιM hιM hsimM
    (TimeDependentExtensions.BlockEncoding.alignedOracle
      (beConst (precisionMainData τ ε s h.s_ge) MP) NP αP TP εP)
    (alignedOracle_beConst_unitary _ MP NP αP TP εP)
    (nonempty_alignedAccess (precisionMainData τ ε s h.s_ge) (scalarAccess (by omega))
      MP NP αP TP εP)
    pP ιP hιP hsimP
  push_cast at key
  linarith

/-- **Theorem `hsl:thm:main` for calls of time-indexed block encodings** (eq. `hsl:eq:main`): an
extension of the remark after the proof of Theorem `hs:thm:time` (time-independent hard instances)
to calls of a Hermitian block encoding of the hard instances, which the manuscript does not state;
the normalisation `beAlpha = s·scale` matches `α_BE = sη` (the text after eq.
`hs:eq:blockadditive`) and the factor `8` comes from the reduction. For any three programs
over the released aligned block-encoding families of the constant Hermitian block encodings of the
time, mixed and precision families (any numbers of samples, slot counts and schedules) and isometric
encodings, each meeting the error criterion of `TimeDependentExtensions.BlockEncoding.simulation`
(`BECriterion`, boundary `beJ`, normalisation `beAlpha`, any mesh `t`, final time `τ`, error `ε`),
`c₀ (√s τ + √(sτr) + r) ≤ 8 · max(Q_T, Q_M, Q_P)`. -/
theorem main_max_block (h : HSRange τ s ε) (MT MM MP NT NM NP : ℕ)
    (αT TT εT αM TM εM αP TP εP : ℝ)
    (tT tM tP : ℕ → ℝ)
    (pT : MultiOracleCircuit.Program (TimeDependentExtensions.BlockEncoding.alignedOracle
      (beConst (timeData τ s h.s_ge) MT) NT αT TT εT))
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      BETimeWork τ s MT NT αT TT εT) (hιT : ιT† ∘L ιT = 1)
    (hT : BECriterion pT.eval ιT (beConst (timeData τ s h.s_ge) MT) (beJ (timeData τ s h.s_ge))
      (beAlpha (timeData τ s h.s_ge)) tT τ ε)
    (pM : MultiOracleCircuit.Program (TimeDependentExtensions.BlockEncoding.alignedOracle
      (beConst (mixedMainData τ ε s h.s_ge) MM) NM αM TM εM))
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      BEMixedWork τ ε s MM NM αM TM εM) (hιM : ιM† ∘L ιM = 1)
    (hM : BECriterion pM.eval ιM (beConst (mixedMainData τ ε s h.s_ge) MM)
      (beJ (mixedMainData τ ε s h.s_ge)) (beAlpha (mixedMainData τ ε s h.s_ge)) tM τ ε)
    (pP : MultiOracleCircuit.Program (TimeDependentExtensions.BlockEncoding.alignedOracle
      (beConst (precisionMainData τ ε s h.s_ge) MP) NP αP TP εP))
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
      BEPrecisionWork τ ε s MP NP αP TP εP) (hιP : ιP† ∘L ιP = 1)
    (hP : BECriterion pP.eval ιP (beConst (precisionMainData τ ε s h.s_ge) MP)
      (beJ (precisionMainData τ ε s h.s_ge)) (beAlpha (precisionMainData τ ε s h.s_ge)) tP τ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      8 * max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  exact main_max_block_endpoint h MT MM MP NT NM NP αT TT εT αM TM εM αP TP εP pT ιT hιT
    (beCriterion_endpoint _ (hard_instances h).1.isHermitian MT tT h.eps_pos.le pT.eval ιT hT)
    pM ιM hιM
    (beCriterion_endpoint _ (hard_instances h).2.1.isHermitian MM tM h.eps_pos.le pM.eval ιM hM)
    pP ιP hιP
    (beCriterion_endpoint _ (hard_instances h).2.2.1.isHermitian MP tP h.eps_pos.le pP.eval ιP
      hP)

/-! ### The controlled time-indexed oracle and the call forms -/

/-- The workspace of the controlled time-indexed oracle on the time family. -/
abbrev BETimePrim (τ : ℝ) (s M : ℕ) : Type :=
  EuclideanSpace ℂ (TimeDependentExtensions.BlockEncoding.Basis
    (BEBasis (SearchIndex (timeN τ) (hsMu s) s)
      (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ))) M)

/-- The workspace of the controlled time-indexed oracle on the mixed family. -/
abbrev BEMixedPrim (τ ε : ℝ) (s M : ℕ) : Type :=
  EuclideanSpace ℂ (TimeDependentExtensions.BlockEncoding.Basis
    (BEBasis (SearchIndex (precN τ ε) (hsMu s) s)
      (Word (searchBits (precN τ ε) (hsMu s) s 1 τ))) M)

/-- The workspace of the controlled time-indexed oracle on the precision family. -/
abbrev BEPrecisionPrim (τ ε : ℝ) (s M : ℕ) : Type :=
  EuclideanSpace ℂ (TimeDependentExtensions.BlockEncoding.Basis
    (BEBasis (ScalarIndex (precN τ ε) s) (Word (scalarBits (precN τ ε) s τ))) M)

/-- **Theorem `hsl:thm:main` for the controlled time-indexed oracle, endpoint form** (eq.
`hsl:eq:main`; an extension of the remark after the proof of Theorem `hs:thm:time` to the access
model of eqs. `hs:eq:blockspecial` and `hs:eq:blockadditive`, coherent and
controlled access to Hermitian unitaries `O_r`): for any three programs over
`TimeDependentExtensions.BlockEncoding.primitive (beConst D M)` (`|c, r⟩ ⊗ v ↦ |c, r⟩ ⊗ O_r^c v`,
any number `M` of samples) on the time, mixed and precision families and isometric encodings, each
with endpoint error `ε` against `exp(-iτH_x)`, `c₀ (√s τ + √(sτr) + r) ≤ 8 · max(Q_T, Q_M, Q_P)`,
`Q = p.count`, inverses included. The factor `8` comes from the reduction. -/
theorem main_max_block_primitive (h : HSRange τ s ε) (MT MM MP : ℕ)
    (pT : MultiOracleCircuit.Program
      (TimeDependentExtensions.BlockEncoding.primitive (beConst (timeData τ s h.s_ge) MT)))
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ] BETimePrim τ s MT)
    (hιT : ιT† ∘L ιT = 1)
    (hsimT : ∀ j, ‖pT.eval j ∘L ιT - ιT ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((timeData τ s h.s_ge).matrix j))‖ ≤ ε)
    (pM : MultiOracleCircuit.Program (TimeDependentExtensions.BlockEncoding.primitive
      (beConst (mixedMainData τ ε s h.s_ge) MM)))
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ] BEMixedPrim τ ε s MM)
    (hιM : ιM† ∘L ιM = 1)
    (hsimM : ∀ j, ‖pM.eval j ∘L ιM - ιM ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((mixedMainData τ ε s h.s_ge).matrix j))‖ ≤ ε)
    (pP : MultiOracleCircuit.Program (TimeDependentExtensions.BlockEncoding.primitive
      (beConst (precisionMainData τ ε s h.s_ge) MP)))
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ] BEPrecisionPrim τ ε s MP)
    (hιP : ιP† ∘L ιP = 1)
    (hsimP : ∀ x, ‖pP.eval x ∘L ιP - ιP ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((precisionMainData τ ε s h.s_ge).matrix x))‖ ≤ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      8 * max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  have hs := h.s_ge
  have key := Core.main_max_uniform_weight h 16
    (TimeDependentExtensions.BlockEncoding.primitive (beConst (timeData τ s h.s_ge) MT))
    (TimeDependentExtensions.BlockEncoding.primitive_unitary _
      (fun x _ => beOp_unitary (timeData τ s h.s_ge) x))
    (nonempty_primitiveAccess (timeData τ s h.s_ge)
      (searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)) MT)
    pT ιT hιT hsimT
    (TimeDependentExtensions.BlockEncoding.primitive (beConst (mixedMainData τ ε s h.s_ge) MM))
    (TimeDependentExtensions.BlockEncoding.primitive_unitary _
      (fun x _ => beOp_unitary (mixedMainData τ ε s h.s_ge) x))
    (nonempty_primitiveAccess (mixedMainData τ ε s h.s_ge)
      (searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)) MM)
    pM ιM hιM hsimM
    (TimeDependentExtensions.BlockEncoding.primitive
      (beConst (precisionMainData τ ε s h.s_ge) MP))
    (TimeDependentExtensions.BlockEncoding.primitive_unitary _
      (fun x _ => beOp_unitary (precisionMainData τ ε s h.s_ge) x))
    (nonempty_primitiveAccess (precisionMainData τ ε s h.s_ge) (scalarAccess (by omega)) MP)
    pP ιP hιP hsimP
  push_cast at key
  linarith

/-- **Theorem `hsl:thm:main` for all call forms of the aligned block-encoding family, endpoint
form** (eq. `hsl:eq:main`; an extension of the manuscript's the paragraphs after the proof of
Theorem `hs:thm:time`): for any three programs over the plain, inverse, controlled and
controlled-inverse calls (`AdaptiveODELowerBound.Access.callFamily`) of the released aligned
block-encoding families of `beConst D M` on the time, mixed and precision families (any numbers of
samples, slot counts and schedules) and isometric encodings, each with endpoint error `ε` against
`exp(-iτH_x)`, `c₀ (√s τ + √(sτr) + r) ≤ 8 · max(Q_T, Q_M, Q_P)`, `Q = p.count`, every call form
counted once. The factor `8` comes from the reduction. -/
theorem main_max_calls_block (h : HSRange τ s ε) (MT MM MP NT NM NP : ℕ)
    (αT TT εT αM TM εM αP TP εP : ℝ)
    (pT : MultiOracleCircuit.Program (AdaptiveODELowerBound.Access.callFamily
      (TimeDependentExtensions.BlockEncoding.alignedOracle
        (beConst (timeData τ s h.s_ge) MT) NT αT TT εT)))
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      Joint Bool (BETimeWork τ s MT NT αT TT εT)) (hιT : ιT† ∘L ιT = 1)
    (hsimT : ∀ j, ‖pT.eval j ∘L ιT - ιT ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((timeData τ s h.s_ge).matrix j))‖ ≤ ε)
    (pM : MultiOracleCircuit.Program (AdaptiveODELowerBound.Access.callFamily
      (TimeDependentExtensions.BlockEncoding.alignedOracle
        (beConst (mixedMainData τ ε s h.s_ge) MM) NM αM TM εM)))
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      Joint Bool (BEMixedWork τ ε s MM NM αM TM εM)) (hιM : ιM† ∘L ιM = 1)
    (hsimM : ∀ j, ‖pM.eval j ∘L ιM - ιM ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((mixedMainData τ ε s h.s_ge).matrix j))‖ ≤ ε)
    (pP : MultiOracleCircuit.Program (AdaptiveODELowerBound.Access.callFamily
      (TimeDependentExtensions.BlockEncoding.alignedOracle
        (beConst (precisionMainData τ ε s h.s_ge) MP) NP αP TP εP)))
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
      Joint Bool (BEPrecisionWork τ ε s MP NP αP TP εP)) (hιP : ιP† ∘L ιP = 1)
    (hsimP : ∀ x, ‖pP.eval x ∘L ιP - ιP ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((precisionMainData τ ε s h.s_ge).matrix x))‖ ≤ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      8 * max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  have hs := h.s_ge
  have AT : Nonempty (PhaseAccess (Fin (timeN τ) × Fin (2 ^ hsMu s)) oneHotPattern
      (AdaptiveODELowerBound.Access.callFamily
        (TimeDependentExtensions.BlockEncoding.alignedOracle
          (beConst (timeData τ s h.s_ge) MT) NT αT TT εT)) (fun _ => 16)) := by
    obtain ⟨A⟩ := nonempty_alignedAccess (timeData τ s h.s_ge)
      (searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)) MT NT αT TT εT
    exact ⟨Core.callAccess A (alignedOracle_beConst_unitary _ MT NT αT TT εT)⟩
  have AM : Nonempty (PhaseAccess (Fin (precN τ ε) × Fin (2 ^ hsMu s)) oneHotPattern
      (AdaptiveODELowerBound.Access.callFamily
        (TimeDependentExtensions.BlockEncoding.alignedOracle
          (beConst (mixedMainData τ ε s h.s_ge) MM) NM αM TM εM)) (fun _ => 16)) := by
    obtain ⟨A⟩ := nonempty_alignedAccess (mixedMainData τ ε s h.s_ge)
      (searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)) MM NM αM TM εM
    exact ⟨Core.callAccess A (alignedOracle_beConst_unitary _ MM NM αM TM εM)⟩
  have AP : Nonempty (PhaseAccess (Fin (precN τ ε)) bitPattern
      (AdaptiveODELowerBound.Access.callFamily
        (TimeDependentExtensions.BlockEncoding.alignedOracle
          (beConst (precisionMainData τ ε s h.s_ge) MP) NP αP TP εP)) (fun _ => 16)) := by
    obtain ⟨A⟩ := nonempty_alignedAccess (precisionMainData τ ε s h.s_ge)
      (scalarAccess (by omega)) MP NP αP TP εP
    exact ⟨Core.callAccess A (alignedOracle_beConst_unitary _ MP NP αP TP εP)⟩
  have key := Core.main_max_uniform_weight h 16 _
    (AdaptiveODELowerBound.Access.callFamily_unitary
      (alignedOracle_beConst_unitary _ MT NT αT TT εT))
    AT pT ιT hιT hsimT _
    (AdaptiveODELowerBound.Access.callFamily_unitary
      (alignedOracle_beConst_unitary _ MM NM αM TM εM))
    AM pM ιM hιM hsimM _
    (AdaptiveODELowerBound.Access.callFamily_unitary
      (alignedOracle_beConst_unitary _ MP NP αP TP εP))
    AP pP ιP hιP hsimP
  push_cast at key
  linarith

end

end TimeDependentLowerBoundExtensions.BlockEncoding
