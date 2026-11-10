import ManuscriptConformance.Defs
import SparseHamiltonian.ManuscriptPrecision
import ZeroTimeRemarks.Hamiltonian
import ZeroTimeRemarks.TimeUniform
import OptimalLowerBounds.Optimal
import TwoNormSimulation.TwoNorm
import OptimalSparseSimulation.UnitaryBound
import UnitaryImplementationExtensions.LowerBound

/-!
# Conformance: Hamiltonian simulation and unitary implementation

Theorems `hs:thm:main`, `hs:thm:time`, `hs:thm:optimal`, `hs:thm:two-norm` and Corollaries
`hs:cor:unitary`, `hs:cor:unitary-optimal` of the manuscript, each restated from the
manuscript's own statement and derived from the package. The query model is the package's: one
fixed program over the primitive oracles of the sparse data (inverse calls counted), fixed before
the unknown instance `x`, acting on a known clean encoding of the input.

None of these statements needs a hypothesis beyond the manuscript's, except the finer mesh of `hs_thm_time` (summary table). Where Lean is more general
(no sparsity or norm promise on the exact time-dependent path, `N = 1` allowed
for unitaries), the extra generality is noted in the docstring.
-/

set_option autoImplicit false

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Set
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

universe u v w

/-! ### Theorem `hs:thm:main` -/

set_option maxHeartbeats 1000000 in
/-- **Theorem `hs:thm:main`: baseline sparse Hamiltonian simulation.**
For Hermitian `H = D.matrix x` with at most `s` nonzero entries per row and column (the slots of
the sparse data `D`) and row and column Euclidean norms at most `η > 0`, `t ∈ ℝ` and
`0 < ε ≤ 1/2`, one unitary program over the primitive sparse oracles (entry value and phase-one
in-place locators, inverses counted), fixed before the instance, has full-output error at most
`ε` (eq. `hs:eq:fullerror`, also with an untouched reference) and uses
`O(√s η|t| + √(s η|t| log(1/ε)) + log(1/ε))` queries (eq. `hs:eq:mainbound`); the absolute
constant is `995328`. Formal restrictions: none. -/
theorem hs_thm_main :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (D : Data X n Z s) (η t ε : ℝ),
        0 < η → 0 < ε → ε ≤ 1 / 2 →
        (∀ x, (D.matrix x).IsHermitian) →
        (∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
        (∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
        ∃ (γ : ℝ) (p : MultiOracleCircuit.Program (ImprovedSparseHamiltonian.oracle D γ η t ε)),
          (p.count : ℝ) ≤ C * mainBound s (η * |t|) ε ∧
          (ImprovedSparseHamiltonian.input D γ η t ε)† ∘L
            ImprovedSparseHamiltonian.input D γ η t ε = 1 ∧
          ∀ x, IsUnitary (p.eval x) ∧
            FullOutputError (p.eval x) (ImprovedSparseHamiltonian.input D γ η t ε)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                SparseStateOverlap.matrixOperator (D.matrix x))) ε ∧
            ∀ (R : Type) [Fintype R], ReferenceOutputError R (p.eval x)
              (ImprovedSparseHamiltonian.input D γ η t ε)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                SparseStateOverlap.matrixOperator (D.matrix x))) ε := by
  refine ⟨995328, by norm_num, ?_⟩
  intro X n Z _ _ _ _ _ s D η t ε hη hε hε2 hH hrow hcol
  obtain ⟨γ, -, -, -, p, hc, hin, hp⟩ :=
    ImprovedSparseHamiltonian.simulation_log_one D η t ε hη hε hε2 hH hrow hcol
  exact ⟨γ, p, hc, hin, fun x => ⟨(hp x).1, fullOutputError_of_norm (hp x).2,
    referenceOutputError_of_norm (hp x).2⟩⟩

set_option maxHeartbeats 1000000 in
/-- **Theorem `hs:thm:main`, spectral-norm promise** ("A supplied spectral-norm bound
`‖H‖ ≤ Λ` permits `η = Λ`"): the same, without the untouched reference, with `‖H‖ ≤ Λ` in place of the row and column norm
promises. -/
theorem hs_thm_main_spectral :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (D : Data X n Z s) (Λ t ε : ℝ),
        0 < Λ → 0 < ε → ε ≤ 1 / 2 →
        (∀ x, (D.matrix x).IsHermitian) →
        (∀ x, ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ Λ) →
        ∃ (γ : ℝ) (p : MultiOracleCircuit.Program (ImprovedSparseHamiltonian.oracle D γ Λ t ε)),
          (p.count : ℝ) ≤ C * mainBound s (Λ * |t|) ε ∧
          (ImprovedSparseHamiltonian.input D γ Λ t ε)† ∘L
            ImprovedSparseHamiltonian.input D γ Λ t ε = 1 ∧
          ∀ x, IsUnitary (p.eval x) ∧
            FullOutputError (p.eval x) (ImprovedSparseHamiltonian.input D γ Λ t ε)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                SparseStateOverlap.matrixOperator (D.matrix x))) ε := by
  refine ⟨995328, by norm_num, ?_⟩
  intro X n Z _ _ _ _ _ s D Λ t ε hΛ hε hε2 hH hN
  obtain ⟨γ, -, -, -, p, hc, hin, hp⟩ :=
    ImprovedSparseHamiltonian.simulation_spectral_log_one D Λ t ε hΛ hε hε2 hH hN
  exact ⟨γ, p, hc, hin, fun x => ⟨(hp x).1, fullOutputError_of_norm (hp x).2⟩⟩

set_option maxHeartbeats 1000000 in
/-- **Theorem `hs:thm:main`, zero time or a known zero Hamiltonian** ("For `t = 0` or a known
zero Hamiltonian, the identity circuit suffices"): with a supplied norm bound `η ≥ 0`, if
`t = 0` or `η = 0`, a program with no query is exact. -/
theorem hs_thm_main_zero :
    ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
      [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (D : Data X n Z s) (η t ε : ℝ),
      t = 0 ∨ η = 0 →
      (∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
      ∃ (γ : ℝ) (p : MultiOracleCircuit.Program (ImprovedSparseHamiltonian.oracle D γ η t ε)),
        p.count = 0 ∧
        (ImprovedSparseHamiltonian.input D γ η t ε)† ∘L
          ImprovedSparseHamiltonian.input D γ η t ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          FullOutputError (p.eval x) (ImprovedSparseHamiltonian.input D γ η t ε)
            (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))) 0 := by
  intro X n Z _ _ _ _ _ s D η t ε hZ hrow
  obtain ⟨γ, -, -, -, p, hc, hin, hp⟩ :=
    ZeroTimeRemarks.Hamiltonian.simulation_zero D η t ε hZ hrow
  exact ⟨γ, p, hc, hin, fun x => ⟨(hp x).1, fullOutputError_of_norm (hp x).2.le⟩⟩

/-! ### Theorem `hs:thm:time` -/

/-- The package's mesh conditions for `hs:thm:time` (`4 s η T ≤ M`, `9 β T² ≤ ε M`,
`9 (√s η T)³ ≤ ε M²`) hold for every sufficiently fine uniform mesh. The manuscript leaves the mesh
to the proof ("On the mesh chosen in the proof"); eq. `hs:eq:timegrid` of that proof asks
`4 α T ≤ M`, `6 β T² ≤ ε M` and `(Λ T)³ ≤ ε M²` (`Λ = √s η`). The first package condition is a
`γ`-free form of the clock condition `4 α T ≤ M`; the other two differ only in their constants. -/
theorem hs_thm_time_mesh_exists (s η T β ε : ℝ) (hs : 0 ≤ s) (hη : 0 ≤ η) (hT : 0 ≤ T)
    (hβ : 0 ≤ β) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      0 < M ∧ 4 * s * (η * T) ≤ M ∧ 9 * β * T ^ 2 ≤ ε * M ∧
        9 * (Real.sqrt s * (η * T)) ^ 3 ≤ ε * (M : ℝ) ^ 2 := by
  set a : ℝ := 4 * s * (η * T)
  set b : ℝ := 9 * β * T ^ 2 / ε
  set c : ℝ := 9 * (Real.sqrt s * (η * T)) ^ 3 / ε
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hc : 0 ≤ c := by positivity
  refine ⟨⌈a + b + c⌉₊ + 1, fun M hM => ?_⟩
  have hceil : a + b + c ≤ (M : ℝ) := by
    have h1 := Nat.le_ceil (a + b + c)
    have h2 : ((⌈a + b + c⌉₊ + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hM
    push_cast at h2
    linarith
  have hM1 : (1 : ℝ) ≤ M := by
    have h2 : ((⌈a + b + c⌉₊ + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hM
    push_cast at h2
    linarith [Nat.cast_nonneg (α := ℝ) ⌈a + b + c⌉₊]
  refine ⟨by exact_mod_cast (show (0 : ℝ) < M by linarith), by linarith, ?_, ?_⟩
  · have : b ≤ M := by linarith
    have h := (div_le_iff₀ hε).mp this
    linarith
  · have : c ≤ (M : ℝ) ^ 2 := by nlinarith
    have h := (div_le_iff₀ hε).mp this
    linarith

set_option maxHeartbeats 1000000 in
/-- **Theorem `hs:thm:time`: time-dependent sparse simulation.** For
`T ≥ 0`, `0 < ε ≤ 1/2`, a Hermitian path `H(u)` on `[0, T]` with operator-norm Lipschitz bound
`β`, coherent sampled-time access to Hermitian samples `H̃_r` on the uniform mesh of `M` points
(chosen by the proof: the package's three mesh conditions, eq. `hs:eq:timegrid` up to constants and
a `γ`-free clock condition, met by every large `M`, `hs_thm_time_mesh_exists`) with at most `s`
nonzero entries per row and column, row and column Euclidean norms at most `η > 0` and
`‖H̃_r - H(t_r)‖ ≤ δ`, `T δ ≤ ε/12`: one unitary program over the primitive sparse oracles, fixed
before the instance, approximates the time-ordered propagator `U_H(T, 0)` (characterised as the
solution of `U' = -i H U`, `U(0) = 1`) with full-output error at most `ε` and uses
`O(√s ηT + √(s ηT log(1/ε)) + log(1/ε))` queries, inverse calls included; the constant `995328`
multiplies neither `M` nor `β`. Lean asks the sparsity and norm promises of the represented samples
only, not of the exact path. Formal restrictions: the finer mesh above; coarser meshes admitted by eq. `hs:eq:timegrid` are not covered (summary table). -/
theorem hs_thm_time :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s M : ℕ} (D : Data (X × Fin M) n Z s)
        (H : X → ℝ → Matrix n n ℂ) (η T β δ ε : ℝ),
        0 < η → 0 ≤ T → 0 ≤ β → 0 < ε → ε ≤ 1 / 2 → ∀ (hM : 0 < M),
        4 * s * (η * T) ≤ M → 9 * β * T ^ 2 ≤ ε * M →
        9 * (Real.sqrt s * (η * T)) ^ 3 ≤ ε * (M : ℝ) ^ 2 →
        (∀ y, (D.matrix y).IsHermitian) →
        (∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2) →
        (∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2) →
        (∀ x, ∀ u ∈ Icc 0 T, (H x u).IsHermitian) →
        (∀ x, ∀ u ∈ Icc 0 T, ∀ v ∈ Icc 0 T,
          ‖SparseStateOverlap.matrixOperator (H x u) -
            SparseStateOverlap.matrixOperator (H x v)‖ ≤ β * |u - v|) →
        (∀ x (r : Fin M), ‖SparseStateOverlap.matrixOperator (H x (r * T / M)) -
          SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δ) →
        T * δ ≤ ε / 12 →
        ∃ (γ : ℝ) (p : MultiOracleCircuit.Program (TimeDependent.oracle D γ η T ε)),
          (p.count : ℝ) ≤ C * mainBound s (η * T) ε ∧
          (TimeDependent.input D hM γ η T ε)† ∘L TimeDependent.input D hM γ η T ε = 1 ∧
          ∀ x, IsUnitary (p.eval x) ∧
            ∀ U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n), U 0 = 1 →
              TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator (H x u)) U 0 T →
              FullOutputError (p.eval x) (TimeDependent.input D hM γ η T ε) (U T) ε ∧
              ∀ (R : Type) [Fintype R],
                ReferenceOutputError R (p.eval x) (TimeDependent.input D hM γ η T ε) (U T) ε := by
  refine ⟨995328, by norm_num, ?_⟩
  intro X n Z _ _ _ _ _ s M D H η T β δ ε hη hT hβ hε hε2 hM hMesh hFreeze hCayley hHs hrow
    hcol hPath hLip hVal hBudget
  obtain ⟨γ, -, -, -, p, hc, hin, hp⟩ := TimeDependent.simulation D H η T β δ ε hη hT hβ hε hε2
    hM hMesh hFreeze hCayley hHs hrow hcol hPath hLip hVal hBudget
  exact ⟨γ, p, hc, hin, fun x => ⟨(hp x).1, fun U hU0 hU =>
    ⟨fullOutputError_of_norm ((hp x).2 U hU0 hU),
      referenceOutputError_of_norm ((hp x).2 U hU0 hU)⟩⟩⟩

set_option maxHeartbeats 1000000 in
/-- **Theorem `hs:thm:time`, zero time or a known zero Hamiltonian** ("For zero evolution time or
a Hamiltonian known to vanish throughout the evolution ... without any matrix queries"): under the
hypotheses of `hs_thm_time` with a supplied bound `η ≥ 0`, if `T = 0` or `η = 0`, a program with
no query has full-output error at most `ε`. -/
theorem hs_thm_time_zero :
    ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
      [AddCommGroup Z] [DecidableEq Z] {s M : ℕ} (D : Data (X × Fin M) n Z s)
      (H : X → ℝ → Matrix n n ℂ) (η T β δ ε : ℝ),
      0 ≤ η → 0 ≤ T → 0 ≤ β → 0 < ε → ε ≤ 1 / 2 → ∀ (hM : 0 < M),
      4 * s * (η * T) ≤ M → 9 * β * T ^ 2 ≤ ε * M →
      9 * (Real.sqrt s * (η * T)) ^ 3 ≤ ε * (M : ℝ) ^ 2 →
      (∀ y, (D.matrix y).IsHermitian) →
      (∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2) →
      (∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2) →
      (∀ x, ∀ u ∈ Icc 0 T, (H x u).IsHermitian) →
      (∀ x, ∀ u ∈ Icc 0 T, ∀ v ∈ Icc 0 T,
        ‖SparseStateOverlap.matrixOperator (H x u) -
          SparseStateOverlap.matrixOperator (H x v)‖ ≤ β * |u - v|) →
      (∀ x (r : Fin M), ‖SparseStateOverlap.matrixOperator (H x (r * T / M)) -
        SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δ) →
      T * δ ≤ ε / 12 → T = 0 ∨ η = 0 →
      ∃ (γ : ℝ) (p : MultiOracleCircuit.Program (TimeDependent.oracle D γ η T ε)),
        p.count = 0 ∧
        (TimeDependent.input D hM γ η T ε)† ∘L TimeDependent.input D hM γ η T ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ U : ℝ → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n), U 0 = 1 →
            TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator (H x u)) U 0 T →
            FullOutputError (p.eval x) (TimeDependent.input D hM γ η T ε) (U T) ε := by
  intro X n Z _ _ _ _ _ s M D H η T β δ ε hη hT hβ hε hε2 hM hMesh hFreeze hCayley hHs hrow
    hcol hPath hLip hVal hBudget hZ
  obtain ⟨γ, -, -, -, p, hc, hin, hp⟩ := ZeroTimeRemarks.TimeUniform.simulation_nonneg D H η T β
    δ ε hη hT hβ hε hε2 hM hMesh hFreeze hCayley hHs hrow hcol hPath hLip hVal hBudget
  rw [if_pos hZ] at hc
  refine ⟨γ, p, by exact_mod_cast le_antisymm hc (Nat.cast_nonneg _), hin, fun x =>
    ⟨(hp x).1, fun U hU0 hU => fullOutputError_of_norm ((hp x).2 U hU0 hU)⟩⟩

/-! ### Theorem `hs:thm:optimal` -/

/-- The precision ratio of the package is the manuscript's `L / h`. -/
theorem rb_eq (τ ε : ℝ) : SignedFactorSimulation.rb τ ε = logInv ε / hRatio τ ε := rfl

/-- The query bound of the package's optimal simulation in the manuscript's form. -/
theorem optimal_bound_eq (s : ℕ) (τ ε : ℝ) :
    OptimalSparseSimulation.bound s τ ε = 2 * 10 ^ 12 * optimalBound s τ ε := by
  unfold OptimalSparseSimulation.bound optimalBound
  rw [rb_eq, mul_div_assoc]

set_option maxHeartbeats 1000000 in
/-- **Theorem `hs:thm:optimal`, upper bound (eq.
`hs:eq:optimal-bound`).** Under the sparse access and norm promises of `hs:thm:main`, for
`η|t| ≥ 1` and `0 < ε ≤ 1/64`, one unitary program over the primitive sparse oracles with
spectators, on a known isometric encoding, fixed before the instance, has full-output error at most
`ε` (also with an untouched reference) and uses
`O(√s η|t| + √(s η|t| L / log(e + L/(η|t|))) + L / log(e + L/(η|t|)))` queries; the absolute
constant is `2·10¹²`. Formal restrictions: none. -/
theorem hs_thm_optimal :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
        [DecidableEq Z] {s : ℕ} (D : Data X n Z s) (η t ε : ℝ),
        1 ≤ η * |t| → 0 < ε → ε ≤ 1 / 64 →
        (∀ x, (D.matrix x).IsHermitian) →
        (∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
        (∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
        ∃ (ι : Type) (_ : Fintype ι)
          (J : EuclideanSpace ℂ n →L[ℂ] PiLp 2 (fun _ : ι => NativeSignedFactor.Phys n Z))
          (p : MultiOracleCircuit.Program
            (CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle D))),
          J† ∘L J = 1 ∧ (p.count : ℝ) ≤ C * optimalBound s (η * |t|) ε ∧
          ∀ x, IsUnitary (p.eval x) ∧
            FullOutputError (p.eval x) J (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))) ε ∧
            ∀ (R : Type) [Fintype R], ReferenceOutputError R (p.eval x) J
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                SparseStateOverlap.matrixOperator (D.matrix x))) ε := by
  refine ⟨2 * 10 ^ 12, by norm_num, ?_⟩
  intro X n Z _ _ _ _ _ s D η t ε hτ hε hε1 hH hrow hcol
  obtain ⟨ι, hι, J, p, hJ, hc, hp⟩ :=
    OptimalSparseSimulation.optimal_simulation D hτ hε hε1 hH hrow hcol
  rw [optimal_bound_eq] at hc
  exact ⟨ι, hι, J, p, hJ, hc, fun x => ⟨(hp x).1, fullOutputError_of_norm (hp x).2,
    referenceOutputError_of_norm (hp x).2⟩⟩

/-- The lower-bound ratio of the package is the manuscript's `L / h`. -/
theorem hsR_eq (τ ε : ℝ) : SparseLowerBounds.Hamiltonian.hsR τ ε = logInv ε / hRatio τ ε := rfl

/-- The three-term shape of `hsl:eq:main` is `optimalBound`. -/
theorem lower_shape_eq (s : ℕ) (τ ε : ℝ) :
    Real.sqrt s * τ + Real.sqrt (s * τ * SparseLowerBounds.Hamiltonian.hsR τ ε) +
        SparseLowerBounds.Hamiltonian.hsR τ ε = optimalBound s τ ε := by
  unfold optimalBound
  rw [hsR_eq, mul_div_assoc]

set_option maxHeartbeats 2000000 in
/-- **Theorem `hs:thm:optimal`, worst-case complexity (eq. `hs:eq:optimal-theta`).** For
`τ ≥ 1`, `s ≥ 32` and `0 < ε ≤ 1/64`, in the query model of the upper bound (one program over the
primitive oracles with spectators on a known isometric encoding, fixed before the instance,
full-output error `ε`; `NativeSignedFactor.Simulates`), at normalised time `τ` (`η = 1`):
every sparse Hermitian input with row and column norms at most one is simulated with at most
`C · S` queries, and some such input (of dimension growing with the parameters) needs at least
`c · S` queries in every simulation, `S = optimalBound s τ ε`; `c = log 2/(4096π)`,
`C = 2·10¹²`. Formal restrictions: none; this is the specialisation `η = 1`, `t = τ > 0` of
the `Θ` statement. For general `η > 0` and either sign of `t` it follows from
`OptimalLowerBounds.two_norm_theta` at `m = 1` and `c = sign(t) η` (sparsity `s · 1 = s`,
`μ = η`, `c t = η|t|`), with `hs_thm_optimal` for the upper bound. -/
theorem hs_thm_optimal_theta :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (τ ε : ℝ) (s : ℕ), 1 ≤ τ → 32 ≤ s → 0 < ε → ε ≤ 1 / 64 →
        (∀ {X : Type} {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
          [DecidableEq Z] (D : Data X n Z s),
          (∀ x, (D.matrix x).IsHermitian) →
          (∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1) → (∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) →
          NativeSignedFactor.Simulates (NativeSignedFactor.physOracle D)
            (fun x => SparseStateOverlap.matrixOperator (D.matrix x)) τ ε
            (C * optimalBound s τ ε)) ∧
        ∃ (X n Z : Type) (_ : Fintype n) (_ : DecidableEq n) (_ : Fintype Z) (_ : AddCommGroup Z)
          (D : Data X n Z s),
          (∀ x, (D.matrix x).IsHermitian) ∧
          (∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1) ∧ (∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) ∧
          ∀ q : ℝ, NativeSignedFactor.Simulates (NativeSignedFactor.physOracle D)
            (fun x => SparseStateOverlap.matrixOperator (D.matrix x)) τ ε q →
            c * optimalBound s τ ε ≤ q := by
  refine ⟨SparseLowerBounds.Hamiltonian.c0, 2 * 10 ^ 12, ?_, by norm_num, ?_⟩
  · unfold SparseLowerBounds.Hamiltonian.c0
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  intro τ ε s hτ hs hε hε1
  have hR : SparseLowerBounds.Hamiltonian.HSRange τ s ε := ⟨hτ, hs, hε, hε1⟩
  refine ⟨fun D hH hrow hcol => ?_, ?_⟩
  · have hτ' : 1 ≤ (1 : ℝ) * |τ| := by rw [one_mul, abs_of_pos (by linarith)]; exact hτ
    have key := OptimalSparseSimulation.optimal_simulation D (η := 1) (t := τ) hτ' hε hε1 hH
      (fun x i => by rw [one_pow]; exact hrow x i) (fun x j => by rw [one_pow]; exact hcol x j)
    rwa [one_mul, abs_of_pos (by linarith : (0 : ℝ) < τ), optimal_bound_eq] at key
  · obtain ⟨hlow, -⟩ := OptimalLowerBounds.optimal_theta hR
    obtain ⟨hT, hM, hP, -⟩ := SparseLowerBounds.Hamiltonian.hard_instances hR
    rw [lower_shape_eq] at hlow
    rcases le_max_iff.mp hlow with h1 | h23
    · exact ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _,
        hT.isHermitian, hT.row_norm_le, hT.col_norm_le, fun q hq =>
          h1.trans (OptimalLowerBounds.simulationCost_le _ hq)⟩
    · rcases le_max_iff.mp h23 with h2 | h3
      · exact ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _,
          hM.isHermitian, hM.row_norm_le, hM.col_norm_le, fun q hq =>
            h2.trans (OptimalLowerBounds.simulationCost_le _ hq)⟩
      · exact ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _,
          hP.isHermitian, hP.row_norm_le, hP.col_norm_le, fun q hq =>
            h3.trans (OptimalLowerBounds.simulationCost_le _ hq)⟩

/-! ### Theorem `hs:thm:two-norm` -/

/-- The two-norm query bound of the package in the manuscript's form. -/
theorem twoNorm_bound_eq (s : ℕ) (η μ t ε : ℝ) :
    TwoNormSimulation.bound s η μ t ε = 2 * 10 ^ 12 * twoNormBound s η μ t ε := by
  have e : Real.log (1 / ε) / (η ^ 2 * |t| / μ) = μ * logInv ε / (η ^ 2 * |t|) := by
    unfold logInv
    rw [div_div_eq_mul_div, mul_comm]
  unfold TwoNormSimulation.bound twoNormBound SignedFactorSimulation.rb TwoNormSimulation.thetaT
  rw [e]
  have h2 : (s : ℝ) * μ * |t| * (Real.log (1 / ε) /
      Real.log (Real.exp 1 + μ * logInv ε / (η ^ 2 * |t|))) =
      (s : ℝ) * μ * |t| * logInv ε / Real.log (Real.exp 1 + μ * logInv ε / (η ^ 2 * |t|)) :=
    (mul_div_assoc _ _ _).symm
  rw [h2]
  rfl

set_option maxHeartbeats 1000000 in
/-- **Theorem `hs:thm:two-norm` (eq. `hs:eq:two-norm-bound`).** Under the
assumptions of `hs:thm:main` and an entry bound `μ` with `‖H‖_max ≤ μ ≤ η ≤ √s μ`
(eq. `hs:eq:two-norm-promises`), for `η²|t|/μ ≥ 1` and `0 < ε ≤ 1/64`, one unitary program over the
primitive oracles with spectators, fixed before the instance, has full-output error at most `ε`
(also with an untouched reference) and uses
`O(√s η|t| + √(sμ|t| L / log(e + μL/(η²|t|))) + L / log(e + μL/(η²|t|)))` queries; the absolute
constant is `2·10¹²`. Formal restrictions: none. -/
theorem hs_thm_two_norm :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
        [DecidableEq Z] {s : ℕ} (D : Data X n Z s) (η μ t ε : ℝ),
        μ ≤ η → η ≤ Real.sqrt s * μ → 1 ≤ η ^ 2 * |t| / μ → 0 < ε → ε ≤ 1 / 64 →
        (∀ x, (D.matrix x).IsHermitian) →
        (∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
        (∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
        (∀ x i j, ‖D.matrix x i j‖ ≤ μ) →
        ∃ (ι : Type) (_ : Fintype ι)
          (J : EuclideanSpace ℂ n →L[ℂ] PiLp 2 (fun _ : ι => NativeSignedFactor.Phys n Z))
          (p : MultiOracleCircuit.Program
            (CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle D))),
          J† ∘L J = 1 ∧ (p.count : ℝ) ≤ C * twoNormBound s η μ t ε ∧
          ∀ x, IsUnitary (p.eval x) ∧
            FullOutputError (p.eval x) J (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))) ε ∧
            ∀ (R : Type) [Fintype R], ReferenceOutputError R (p.eval x) J
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                SparseStateOverlap.matrixOperator (D.matrix x))) ε := by
  refine ⟨2 * 10 ^ 12, by norm_num, ?_⟩
  intro X n Z _ _ _ _ _ s D η μ t ε hμη hηs hθ hε hε1 hH hrow hcol hent
  obtain ⟨ι, hι, J, p, hJ, hc, hp⟩ :=
    TwoNormSimulation.two_norm_simulation D hμη hηs hθ hε hε1 hH hrow hcol hent
  rw [twoNorm_bound_eq] at hc
  exact ⟨ι, hι, J, p, hJ, hc, fun x => ⟨(hp x).1, fullOutputError_of_norm (hp x).2,
    referenceOutputError_of_norm (hp x).2⟩⟩

/-! ### Corollaries `hs:cor:unitary` and `hs:cor:unitary-optimal` -/

/-- The unitary query shape of the package in the manuscript's form. -/
theorem unitary_bound_eq (N : ℕ) (ε : ℝ) :
    Real.sqrt (N * Real.log (1 / ε)) + OptimalSparseSimulation.hybridTerm N ε =
      unitaryBound N ε := rfl

set_option maxHeartbeats 1000000 in
/-- **Corollary `hs:cor:unitary`, exact entries.** For a unitary
`U = D.matrix x` of dimension `N` with a reversible entry-value oracle and `0 < ε ≤ 1/2`, one
unitary program over the entry oracle alone (no location oracle; inverse calls counted), fixed
before the instance, has full-output error at most `ε` against `U` (also with an untouched
reference) and uses `O(√(N log(1/ε)) + log(1/ε)/log(e + log(1/ε)/N))` entry calls
(eq. `hs:eq:unitarybound`); the absolute constant is `5·10¹³`. Lean allows `N = 1`. Formal
restrictions: none. -/
theorem hs_cor_unitary :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
        [DecidableEq Z] [Nonempty n] (D : UnitaryEntryData.Data X n Z) (ε : ℝ),
        0 < ε → ε ≤ 1 / 2 →
        ∃ (ι : Type) (_ : Fintype ι)
          (J : EuclideanSpace ℂ n →L[ℂ]
            PiLp 2 (fun _ : ι => NativeSignedFactor.Phys (UnitaryEntryData.Index n) Z))
          (p : OracleCircuit.Program
            (OptimalSparseSimulation.entryOracle (UnitaryPrecision.Table.ofData D) ι)),
          J† ∘L J = 1 ∧ (p.count : ℝ) ≤ C * unitaryBound (Fintype.card n) ε ∧
          ∀ x, IsUnitary (p.eval x) ∧
            FullOutputError (p.eval x) J (SparseStateOverlap.matrixOperator (D.matrix x)) ε ∧
            ∀ (R : Type) [Fintype R], ReferenceOutputError R (p.eval x) J
              (SparseStateOverlap.matrixOperator (D.matrix x)) ε := by
  refine ⟨5 * 10 ^ 13, by norm_num, ?_⟩
  intro X n Z _ _ _ _ _ _ D ε hε hε2
  obtain ⟨ι, hι, J, p, hJ, hc, hp⟩ := OptimalSparseSimulation.unitary_bound D ε hε hε2
  rw [unitary_bound_eq] at hc
  exact ⟨ι, hι, J, p, hJ, hc, fun x => ⟨(hp x).1, fullOutputError_of_norm (hp x).2,
    referenceOutputError_of_norm (hp x).2⟩⟩

set_option maxHeartbeats 1000000 in
/-- **Corollary `hs:cor:unitary`, inexact entries**: the same when the entry oracle supplies a
table `T` whose entries are within `ε/(πN)` of those of the unitary `U(x)`. -/
theorem hs_cor_unitary_inexact :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
        [DecidableEq Z] [Nonempty n] (T : UnitaryPrecision.Table X n Z) (U : X → Matrix n n ℂ),
        (∀ x, IsUnitary (SparseStateOverlap.matrixOperator (U x))) → ∀ (ε : ℝ),
        0 < ε → ε ≤ 1 / 2 →
        (∀ x i j, ‖T.matrix x i j - U x i j‖ ≤ ε / (Real.pi * Fintype.card n)) →
        ∃ (ι : Type) (_ : Fintype ι)
          (J : EuclideanSpace ℂ n →L[ℂ]
            PiLp 2 (fun _ : ι => NativeSignedFactor.Phys (UnitaryEntryData.Index n) Z))
          (p : OracleCircuit.Program (OptimalSparseSimulation.entryOracle T ι)),
          J† ∘L J = 1 ∧ (p.count : ℝ) ≤ C * unitaryBound (Fintype.card n) ε ∧
          ∀ x, IsUnitary (p.eval x) ∧
            FullOutputError (p.eval x) J (SparseStateOverlap.matrixOperator (U x)) ε ∧
            ∀ (R : Type) [Fintype R], ReferenceOutputError R (p.eval x) J
              (SparseStateOverlap.matrixOperator (U x)) ε := by
  refine ⟨5 * 10 ^ 13, by norm_num, ?_⟩
  intro X n Z _ _ _ _ _ _ T U hU ε hε hε2 hT
  obtain ⟨ι, hι, J, p, hJ, hc, hp⟩ := OptimalSparseSimulation.unitary_bound_inexact T U hU ε hε
    hε2 hT
  rw [unitary_bound_eq] at hc
  exact ⟨ι, hι, J, p, hJ, hc, fun x => ⟨(hp x).1, fullOutputError_of_norm (hp x).2,
    referenceOutputError_of_norm (hp x).2⟩⟩

set_option maxHeartbeats 2000000 in
/-- **Corollary `hs:cor:unitary`, constant-error worst-case complexity `Θ(√N)`.** At every
fixed error `0 < ε ≤ 1/2` there are absolute constants (depending on `ε` only) such that every
unitary of dimension `N` with exact entries is implemented with at most `C √N` entry calls, and
every program over the same entry oracle that implements all permutation unitaries
`U_m = (δ_{j+k,m})` of the search family on `N ≥ 2` points within operator-norm error `ε` on an
isometric encoding makes at least `c √N` calls. Model: the entry oracle of
`UnitaryImplementationExtensions.General` (the released entry call with spectators). Formal
restrictions: none. -/
theorem hs_cor_unitary_theta (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Nonempty n]
        [Fintype Z] [AddCommGroup Z] [DecidableEq Z] (D : UnitaryEntryData.Data X n Z),
        ∃ (γ : ℝ) (p : OracleCircuit.Program (UnitaryImplementationExtensions.General.oracle D γ ε)),
          (p.count : ℝ) ≤ C * Real.sqrt (Fintype.card n) ∧
          (UnitaryImplementationExtensions.General.input D γ ε)† ∘L
            UnitaryImplementationExtensions.General.input D γ ε = 1 ∧
          ∀ x, IsUnitary (p.eval x) ∧
            FullOutputError (p.eval x) (UnitaryImplementationExtensions.General.input D γ ε)
              (SparseStateOverlap.matrixOperator (D.matrix x)) ε) ∧
      ∀ (N : ℕ) [NeZero N], 2 ≤ N → ∀ (γ : ℝ)
        (q : OracleCircuit.Program (UnitaryImplementationExtensions.General.oracle
          (UnitaryImplementationExtensions.SearchFamily.searchData N) γ ε))
        (J : EuclideanSpace ℂ (Fin N) →L[ℂ]
          UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ 1 (Real.pi / 2) ε),
        J† ∘L J = 1 →
        (∀ m, ‖q.eval m ∘L J - J ∘L SparseStateOverlap.matrixOperator
          (UnitaryImplementationExtensions.SearchFamily.searchMatrix N m)‖ ≤ ε) →
        c * Real.sqrt N ≤ q.count := by
  have hL : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
  set k : ℝ := 1 - 2 * ε * Real.sqrt (1 - ε ^ 2 / 4)
  have hk : 0 < k := UnitaryImplementationExtensions.Search.near_factor_pos hε.le hε2
  refine ⟨k / (2 * Real.sqrt 2), UnitaryImplementationExtensions.General.exactConstant *
    (Real.sqrt (Real.log (1 / ε)) + Real.log (1 / ε) + 1), by positivity, ?_, ?_, ?_⟩
  · have := UnitaryImplementationExtensions.General.exactConstant_pos
    positivity
  · intro X n Z _ _ _ _ _ _ D
    obtain ⟨γ, -, -, p, hc, hin, hp⟩ := UnitaryImplementationExtensions.General.implementation
      D ε hε hε2
    refine ⟨γ, p, hc.trans ?_, hin, fun x => ⟨(hp x).1, fullOutputError_of_norm (hp x).2⟩⟩
    have hN : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Fintype.card_pos
    have hsq : 1 ≤ Real.sqrt (Fintype.card n : ℝ) := Real.one_le_sqrt.mpr hN
    have hc0 := UnitaryImplementationExtensions.General.exactConstant_pos
    rw [Real.sqrt_mul (Nat.cast_nonneg _)]
    have h1 : Real.log (1 / ε) ≤ Real.log (1 / ε) * Real.sqrt (Fintype.card n : ℝ) := by
      nlinarith
    have h2 : 0 ≤ Real.sqrt (Real.log (1 / ε)) := Real.sqrt_nonneg _
    have h3 : 0 ≤ Real.sqrt (Fintype.card n : ℝ) := Real.sqrt_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left (show Real.sqrt (Fintype.card n : ℝ) *
      Real.sqrt (Real.log (1 / ε)) + Real.log (1 / ε) ≤ (Real.sqrt (Real.log (1 / ε)) +
        Real.log (1 / ε) + 1) * Real.sqrt (Fintype.card n : ℝ) by nlinarith) hc0.le]
  · intro N _ hN γ q J hJ hErr
    obtain ⟨-, -, hlow⟩ := UnitaryImplementationExtensions.LowerBound.theta_of_error hN ε hε hε2
    have h := hlow γ q J hJ hErr
    have hsq := UnitaryImplementationExtensions.LowerBound.sqrt_le_sqrt_two_mul hN
    have hs2 : 0 < Real.sqrt 2 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    calc k * Real.sqrt N ≤ k * (Real.sqrt 2 * Real.sqrt ((N : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left hsq hk.le
      _ = Real.sqrt 2 * (k * Real.sqrt ((N : ℝ) - 1)) := by ring
      _ ≤ Real.sqrt 2 * (2 * q.count) := mul_le_mul_of_nonneg_left h hs2.le
      _ = q.count * (2 * Real.sqrt 2) := by ring

/-- The refined unitary query shape of the package in the manuscript's form. -/
theorem unitary_optimal_bound_eq (N ε : ℝ) :
    Real.sqrt (N * OptimalSparseSimulation.rho ε) + OptimalSparseSimulation.rho ε =
      unitaryOptimalBound N ε := by
  unfold unitaryOptimalBound OptimalSparseSimulation.rho logInv
  rw [mul_div_assoc]

set_option maxHeartbeats 1000000 in
/-- **Corollary `hs:cor:unitary-optimal`, exact entries.** Under the
assumptions of `hs:cor:unitary`, one unitary program over the entry oracle alone, fixed before the
instance, has full-output error at most `ε` (also with an untouched reference) and uses
`O(√(N L / log(e + L)) + L / log(e + L))` entry calls, `L = log(1/ε)`
(eq. `hs:eq:unitary-optimal-bound`); the absolute constant is `5·10¹³`. Formal restrictions:
none. -/
theorem hs_cor_unitary_optimal :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
        [DecidableEq Z] [Nonempty n] (D : UnitaryEntryData.Data X n Z) (ε : ℝ),
        0 < ε → ε ≤ 1 / 2 →
        ∃ (ι : Type) (_ : Fintype ι)
          (J : EuclideanSpace ℂ n →L[ℂ]
            PiLp 2 (fun _ : ι => NativeSignedFactor.Phys (UnitaryEntryData.Index n) Z))
          (p : OracleCircuit.Program
            (OptimalSparseSimulation.entryOracle (UnitaryPrecision.Table.ofData D) ι)),
          J† ∘L J = 1 ∧ (p.count : ℝ) ≤ C * unitaryOptimalBound (Fintype.card n) ε ∧
          ∀ x, IsUnitary (p.eval x) ∧
            FullOutputError (p.eval x) J (SparseStateOverlap.matrixOperator (D.matrix x)) ε ∧
            ∀ (R : Type) [Fintype R], ReferenceOutputError R (p.eval x) J
              (SparseStateOverlap.matrixOperator (D.matrix x)) ε := by
  refine ⟨5 * 10 ^ 13, by norm_num, ?_⟩
  intro X n Z _ _ _ _ _ _ D ε hε hε2
  obtain ⟨ι, hι, J, p, hJ, hc, hp⟩ := OptimalSparseSimulation.unitary_optimal D ε hε hε2
  rw [unitary_optimal_bound_eq] at hc
  exact ⟨ι, hι, J, p, hJ, hc, fun x => ⟨(hp x).1, fullOutputError_of_norm (hp x).2,
    referenceOutputError_of_norm (hp x).2⟩⟩

set_option maxHeartbeats 1000000 in
/-- **Corollary `hs:cor:unitary-optimal`, inexact entries** (entries within `ε/(πN)`). The
constant-error complexity `Θ(√N)` is that of `hs_cor_unitary_theta`: at fixed `ε` the refined
bound is `O(√N)`, and the search-family lower bound holds in the entry-oracle model of
`UnitaryImplementationExtensions.General`; Lean has no lower bound stated for the spectator form
`OptimalSparseSimulation.entryOracle` of the refined circuit itself. -/
theorem hs_cor_unitary_optimal_inexact :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
        [DecidableEq Z] [Nonempty n] (T : UnitaryPrecision.Table X n Z) (U : X → Matrix n n ℂ),
        (∀ x, IsUnitary (SparseStateOverlap.matrixOperator (U x))) → ∀ (ε : ℝ),
        0 < ε → ε ≤ 1 / 2 →
        (∀ x i j, ‖T.matrix x i j - U x i j‖ ≤ ε / (Real.pi * Fintype.card n)) →
        ∃ (ι : Type) (_ : Fintype ι)
          (J : EuclideanSpace ℂ n →L[ℂ]
            PiLp 2 (fun _ : ι => NativeSignedFactor.Phys (UnitaryEntryData.Index n) Z))
          (p : OracleCircuit.Program (OptimalSparseSimulation.entryOracle T ι)),
          J† ∘L J = 1 ∧ (p.count : ℝ) ≤ C * unitaryOptimalBound (Fintype.card n) ε ∧
          ∀ x, IsUnitary (p.eval x) ∧
            FullOutputError (p.eval x) J (SparseStateOverlap.matrixOperator (U x)) ε ∧
            ∀ (R : Type) [Fintype R], ReferenceOutputError R (p.eval x) J
              (SparseStateOverlap.matrixOperator (U x)) ε := by
  refine ⟨5 * 10 ^ 13, by norm_num, ?_⟩
  intro X n Z _ _ _ _ _ _ T U hU ε hε hε2 hT
  obtain ⟨ι, hι, J, p, hJ, hc, hp⟩ :=
    OptimalSparseSimulation.unitary_optimal_inexact T U hU ε hε hε2 hT
  rw [unitary_optimal_bound_eq] at hc
  exact ⟨ι, hι, J, p, hJ, hc, fun x => ⟨(hp x).1, fullOutputError_of_norm (hp x).2,
    referenceOutputError_of_norm (hp x).2⟩⟩

end

end ManuscriptConformance
