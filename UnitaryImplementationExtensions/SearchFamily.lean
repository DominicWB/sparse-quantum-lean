import SparseHamiltonian.UnitaryImplementation
import UnitaryImplementationExtensions.Search

set_option autoImplicit false

/-!
# The search family of unitaries

The hard family of the lower-bound part of corollary `hs:cor:unitary` of the
manuscript (lines 1833-1840): for a marked element `m` of `Fin N` (addition
modulo `N`), `(U_m)_{jk} = 1` if `j + k = m` and `0` otherwise. Each `U_m` is a
permutation matrix and `U_m |0⟩ = |m⟩`. As exact entry data (`searchData`) its
entries are single bits `searchTable N m (j, k) ∈ ZMod 2`, and the entry at
`(j, k)` is one equality test `j + k = m`, i.e. one query to a search oracle.

`count_ge_of_phase` is the lower bound in the Boolean phase form: any program
whose oracle is the phase oracle of the marked strings of some position map,
and which implements `U_m` on an isometric encoding with operator-norm error
`ε₀ ≤ 1` for every `m`, makes at least
`(1 - 2 ε₀ sqrt (1 - ε₀²/4)) sqrt (N - 1) / 2` queries, since its outputs on
`|0⟩` are unit vectors within `ε₀` of the orthonormal states `|m⟩`
(`Search.norm_inner_le_of_near`, `Search.count_ge`). The factor is positive for
`0 ≤ ε₀ ≤ 1/2` (`Search.near_factor_pos`).
-/

namespace UnitaryImplementationExtensions.SearchFamily

noncomputable section
open SparseHamiltonian SparseLowerBounds
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct InnerProductSpace

/-- The search unitary `(U_m)_{jk} = [j + k = m]`, addition modulo `N`. -/
def searchMatrix (N : ℕ) (m : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => if j + k = m then 1 else 0

/-- The one-bit entry table of the search family. -/
def searchTable (N : ℕ) (m : Fin N) (a : Fin N × Fin N) : ZMod 2 :=
  if a.1 + a.2 = m then 1 else 0

/-- The reflection `j ↦ m - j` of `Fin (N + 1)`, an involution. -/
def reflect (N : ℕ) (m : Fin (N + 1)) : Equiv.Perm (Fin (N + 1)) where
  toFun j := m - j
  invFun j := m - j
  left_inv j := sub_sub_cancel m j
  right_inv j := sub_sub_cancel m j

/-- The search matrix acts as the basis permutation of the reflection `j ↦ m - j`. -/
theorem matrixOperator_eq_reflect (N : ℕ) (m : Fin (N + 1)) :
    SparseStateOverlap.matrixOperator (searchMatrix (N + 1) m) =
      (LookupOracle.permutationUnitary (reflect N m)).toLinearIsometry.toContinuousLinearMap := by
  ext v j
  rw [SparseStateOverlap.matrixOperator_apply]
  change _ = v (m - j)
  simp only [searchMatrix, ← eq_sub_iff_add_eq', ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The search matrix is a permutation matrix, hence unitary. -/
theorem searchMatrix_unitary (N : ℕ) (m : Fin N) :
    IsUnitary (SparseStateOverlap.matrixOperator (searchMatrix N m)) := by
  cases N with
  | zero => exact m.elim0
  | succ N =>
    rw [matrixOperator_eq_reflect]
    exact LookupOracle.permutationUnitary_unitary (reflect N m)

/-- The fixed one-bit decoder. -/
def searchDecode {N : ℕ} (_a : Fin N × Fin N) (z : ZMod 2) : ℂ :=
  if z = 1 then 1 else 0

/-- The search family as exact reversible entry data with one-bit values. -/
def searchData (N : ℕ) : UnitaryEntryData.Data (Fin N) (Fin N) (ZMod 2) where
  matrix := searchMatrix N
  unitary := searchMatrix_unitary N
  table := searchTable N
  decode := searchDecode
  scale := 1
  scale_pos := one_pos
  decode_bound := by
    intro a z
    unfold searchDecode
    split_ifs <;> simp
  decoded := by
    intro x i j
    by_cases h : i + j = x <;> simp [searchDecode, searchTable, searchMatrix, h]

/-- A table bit is one exactly at the marked anti-diagonal. -/
theorem searchTable_eq_one_iff (N : ℕ) (m : Fin N) (a : Fin N × Fin N) :
    searchTable N m a = 1 ↔ a.1 + a.2 = m := by
  unfold searchTable
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    decide

/-- The search unitary sends `|0⟩` to the marked element. -/
theorem searchMatrix_single_zero (N : ℕ) [NeZero N] (m : Fin N) :
    SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1) =
      EuclideanSpace.single m 1 := by
  ext i
  rw [SparseSpectralEnergy.matrixOperator_single]
  simp [searchMatrix]

/-- **Lower bound from prepared states.** If the oracle of a program is the
phase oracle of the marked strings of a position map `c`, and the program maps
the encoded `|0⟩` to within `ε₀` of the encoded `|m⟩` on every instance `m`, for
an isometric encoding `J`, with `ε₀ ≤ 1`, then it makes at least
`(1 - 2 ε₀ sqrt (1 - ε₀²/4)) sqrt (N - 1) / 2` queries, inverse queries
included. The factor is positive on `0 ≤ ε₀ ≤ 1/2` (`Search.near_factor_pos`);
it stays positive up to `ε₀ < sqrt (2 - sqrt 3) ≈ 0.5176`. -/
theorem count_ge_of_outputs {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {I : Type*} [Fintype I] {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (P : ProjFamily K I) (c : I → Fin N)
    {O : Fin N → K →L[ℂ] K} (hO : ∀ m, O m = P.phase (Search.markedString c m))
    (q : OracleCircuit.Program O)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] K) (hJ : J† ∘L J = 1) {ε₀ : ℝ} (hε₀ : ε₀ ≤ 1)
    (hOut : ∀ m, ‖q.eval m (J (EuclideanSpace.single 0 1)) -
      J (EuclideanSpace.single m 1)‖ ≤ ε₀) :
    (1 - 2 * ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4)) * Real.sqrt ((N : ℝ) - 1) ≤
      2 * q.count := by
  classical
  have hIso : ∀ x, ‖J x‖ = ‖x‖ :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self J).mpr hJ
  have hInner : ∀ x y, ⟪J x, J y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro x y
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply, hJ,
      one_apply_eq_self]
  have hu : ∀ m : Fin N, ‖J (EuclideanSpace.single m 1)‖ = 1 := by
    intro m
    rw [hIso]
    simp
  have horth : ∀ m m' : Fin N, m ≠ m' →
      ⟪J (EuclideanSpace.single m 1), J (EuclideanSpace.single m' 1)⟫_ℂ = 0 := by
    intro m m' h
    rw [hInner, EuclideanSpace.inner_single_left]
    simp [h]
  have hU : ∀ m, IsUnitary (O m) := fun m => by
    rw [hO m]
    exact P.isUnitary_phase _
  have hEval : ∀ m, ‖q.eval m (J (EuclideanSpace.single 0 1))‖ = 1 := by
    intro m
    rw [(ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr (q.eval_unitary hU m).1]
    exact hu 0
  by_cases hκ : 0 ≤ 1 - 2 * ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4)
  · refine Search.count_ge hN P c hO q (J (EuclideanSpace.single 0 1)) (hu 0).le hκ ?_
    intro m m' hne
    have h := Search.norm_inner_le_of_near hε₀ (hEval m) (hEval m') (hu m) (hu m')
      (horth m m' hne) (hOut m) (hOut m')
    rw [hu 0]
    linarith
  · have h1 : (1 - 2 * ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4)) * Real.sqrt ((N : ℝ) - 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.mp hκ)) (Real.sqrt_nonneg _)
    have h2 : (0 : ℝ) ≤ 2 * q.count := by positivity
    linarith

/-- **Lower bound in phase form.** If the oracle of a program is the phase
oracle of the marked strings of a position map `c`, and the program implements
every search unitary `U_m` on an isometric encoding `J` with operator-norm error
at most `ε₀ ≤ 1`, then it makes at least
`(1 - 2 ε₀ sqrt (1 - ε₀²/4)) sqrt (N - 1) / 2` queries, inverse queries
included. -/
theorem count_ge_of_phase {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {I : Type*} [Fintype I] {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (P : ProjFamily K I) (c : I → Fin N)
    {O : Fin N → K →L[ℂ] K} (hO : ∀ m, O m = P.phase (Search.markedString c m))
    (q : OracleCircuit.Program O)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] K) (hJ : J† ∘L J = 1) {ε₀ : ℝ} (hε₀ : ε₀ ≤ 1)
    (hErr : ∀ m, ‖q.eval m ∘L J - J ∘L
      SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤ ε₀) :
    (1 - 2 * ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4)) * Real.sqrt ((N : ℝ) - 1) ≤
      2 * q.count := by
  refine count_ge_of_outputs hN P c hO q J hJ hε₀ (fun m => ?_)
  have h := (q.eval m ∘L J - J ∘L
    SparseStateOverlap.matrixOperator (searchMatrix N m)).le_opNorm (EuclideanSpace.single 0 1)
  have h1 : ‖(EuclideanSpace.single (0 : Fin N) (1 : ℂ) : EuclideanSpace ℂ (Fin N))‖ = 1 := by
    simp
  rw [h1, mul_one] at h
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    searchMatrix_single_zero] at h
  exact h.trans (hErr m)

end
end UnitaryImplementationExtensions.SearchFamily
