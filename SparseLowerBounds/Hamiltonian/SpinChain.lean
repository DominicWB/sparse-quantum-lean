import SparseLowerBounds.Helpers.SpinChain.Weight

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The public spin chain `B_n`

Manuscript lines 2218-2232 (eqs. `hsl:eq:spin`, `hsl:eq:spinamp`). On
`ℂ^{n+1}` with basis `|0⟩, …, |n⟩`, a path Hamiltonian with real weights `c`
is `Σ_k c_k (|k+1⟩⟨k| + |k⟩⟨k+1|)` (`pathMatrix`). The spin chain uses
`b_k = √((k+1)(n-k))/n` (`spinWeight`), the restriction of `n⁻¹ Σ_j X_j` to
the symmetric subspace of `n` qubits.

* `‖B_n‖ = 1` (`norm_spinMatrix`); more generally a path with weights
  `0 ≤ c_k ≤ b_k` has norm at most one (`norm_pathMatrix_le`, the
  nonnegativity argument of lines 2263-2270: Schur test with the positive
  eigenvector `√binom(n,k)`);
* the endpoint amplitude `⟨n| e^{-iτ a B_n} |0⟩ = (-i)^n sin(aτ/n)^n`
  (`endAmp_scaled`, eq. `hsl:eq:spinamp`). A Lean-friendly proof: the explicit
  vector `f_k(t) = √binom(n,k) cos(at/n)^{n-k} (-i sin(at/n))^k` solves
  `f' = -i a B_n f`, `f(0) = |0⟩`, and `t ↦ e^{ita B_n} f(t)` has zero derivative;
* a path with weights within `δ` of `c` is within `2δ` in operator norm
  (`norm_pathMatrix_sub_le`, row sums, line 2271).

Evolution is `evolve H τ = exp(-iτH)` in exactly the release's endpoint form
`NormedSpace.exp ((-Complex.I * τ) • SparseStateOverlap.matrixOperator H)`
(`ImprovedSparseHamiltonian.simulation_log_one`). Matrices carry the `L²`
operator norm (`Matrix.Norms.L2Operator`).
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace

/-- The spin-chain weight `b_k = √((k+1)(n-k))/n` (eq. `hsl:eq:spin`); it is
`0` for `k ≥ n` (natural subtraction). -/
def spinWeight (n k : ℕ) : ℝ := Real.sqrt (((k + 1) * (n - k) : ℕ) : ℝ) / n

/-- The path Hamiltonian `Σ_{k<n} c_k (|k+1⟩⟨k| + |k⟩⟨k+1|)` on `ℂ^{n+1}`. -/
def pathMatrix (n : ℕ) (c : ℕ → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j + 1 then (c j : ℂ) else if (j : ℕ) = i + 1 then (c i : ℂ) else 0

/-- `B_n` (eq. `hsl:eq:spin`). -/
def spinMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := pathMatrix n (spinWeight n)

/-- `exp(-iτH)` on `ℂ^S`, in the release's endpoint form. -/
def evolve {S : Type*} [Fintype S] [DecidableEq S] (H : Matrix S S ℂ) (τ : ℝ) :
    EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S :=
  NormedSpace.exp ((-Complex.I * (τ : ℂ)) • SparseHamiltonian.SparseStateOverlap.matrixOperator H)

/-- The endpoint amplitude `⟨n| e^{-iτ B} |0⟩` of a path with weights `c`. -/
def endAmp (n : ℕ) (c : ℕ → ℝ) (τ : ℝ) : ℂ :=
  evolve (pathMatrix n c) τ (EuclideanSpace.single 0 1) (Fin.last n)

/-! ### Matrices as bounded operators, and the Schrödinger flow

Generic facts about the release's `matrixOperator` and about `evolve`, used by
every module of the spin-chain cluster. -/

section Operator

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The release's bounded operator of a square matrix is Mathlib's star-algebra
equivalence `Matrix.toEuclideanCLM`; it transports products, adjoints, sums and
exponentials. Restated from `LinearSystems.matrixOperator_eq_toEuclideanCLM`
(`LinearSystems/Instance`) so that this module keeps shallow imports. -/
theorem matrixOperator_eq_toEuclideanCLM (M : Matrix S S ℂ) :
    SparseHamiltonian.SparseStateOverlap.matrixOperator M =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S) M := by
  ext v i
  rw [SparseHamiltonian.SparseStateOverlap.matrixOperator_apply]
  rfl

/-- `‖matrixOperator M‖ = ‖M‖` for the `L²` operator norm of matrices (as
`LinearSystems.norm_matrixOperator`). -/
theorem norm_matrixOperator (M : Matrix S S ℂ) :
    ‖SparseHamiltonian.SparseStateOverlap.matrixOperator M‖ = ‖M‖ := by
  rw [matrixOperator_eq_toEuclideanCLM]
  rfl

/-- A Hermitian matrix gives a self-adjoint operator, in the `star H = H` form
required by `HamiltonianStability.evolution_error_le`. -/
theorem star_matrixOperator_of_isHermitian {H : Matrix S S ℂ} (hH : H.IsHermitian) :
    star (SparseHamiltonian.SparseStateOverlap.matrixOperator H) =
      SparseHamiltonian.SparseStateOverlap.matrixOperator H := by
  rw [matrixOperator_eq_toEuclideanCLM, ← map_star, Matrix.star_eq_conjTranspose, hH.eq]

/-- `evolve H τ = exp(τ • (-iH))`, the real-parameter form of Mathlib's
`hasDerivAt_exp_smul_const`. -/
theorem evolve_eq_exp_smul (H : Matrix S S ℂ) (τ : ℝ) :
    evolve H τ = NormedSpace.exp
      (τ • ((-Complex.I) • SparseHamiltonian.SparseStateOverlap.matrixOperator H)) := by
  exact Helpers.SpinChain.flow_eq_exp_smul _ τ

theorem evolve_zero (H : Matrix S S ℂ) : evolve H 0 = 1 := by
  exact Helpers.SpinChain.flow_zero _

/-- The flow property `e^{-i(s+t)H} = e^{-isH} e^{-itH}`. -/
theorem evolve_add (H : Matrix S S ℂ) (s t : ℝ) : evolve H (s + t) = evolve H s * evolve H t := by
  exact Helpers.SpinChain.flow_add _ s t

/-- `d/dt e^{-itH} = e^{-itH} (-iH)`. -/
theorem hasDerivAt_evolve (H : Matrix S S ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => evolve H u)
      (evolve H t * ((-Complex.I) • SparseHamiltonian.SparseStateOverlap.matrixOperator H)) t := by
  exact Helpers.SpinChain.hasDerivAt_flow _ t

/-- Evolution under a Hermitian matrix is unitary. -/
theorem evolve_mem_unitary {H : Matrix S S ℂ} (hH : H.IsHermitian) (τ : ℝ) :
    evolve H τ ∈ unitary (EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) := by
  exact Helpers.SpinChain.flow_mem_unitary _ (star_matrixOperator_of_isHermitian hH) τ

/-- Scaling the Hamiltonian by a real `a` rescales time: `e^{-iτ(aH)} = e^{-i(aτ)H}`. -/
theorem evolve_smul (H : Matrix S S ℂ) (a τ : ℝ) :
    evolve ((a : ℂ) • H) τ = evolve H (a * τ) := by
  have h : SparseHamiltonian.SparseStateOverlap.matrixOperator ((a : ℂ) • H) =
      (a : ℂ) • SparseHamiltonian.SparseStateOverlap.matrixOperator H := by
    rw [matrixOperator_eq_toEuclideanCLM, matrixOperator_eq_toEuclideanCLM, map_smul]
  unfold evolve
  rw [h]
  exact Helpers.SpinChain.flow_smul _ a τ

/-- For a solution `f' = -iHf`, the curve `t ↦ e^{itH} f(t)` is stationary
(the uniqueness step of the explicit-solution proof of eq. `hsl:eq:spinamp`,
lines 2226-2232). -/
theorem hasDerivAt_evolve_neg_apply (H : Matrix S S ℂ) {f : ℝ → EuclideanSpace ℂ S}
    (hf : ∀ t, HasDerivAt f
      ((-Complex.I) • SparseHamiltonian.SparseStateOverlap.matrixOperator H (f t)) t)
    (t : ℝ) : HasDerivAt (fun u : ℝ => evolve H (-u) (f u)) 0 t := by
  exact Helpers.SpinChain.hasDerivAt_flow_neg_apply _ hf t

/-- **Uniqueness of the Schrödinger flow**: a curve with `f' = -iHf` is
`f(τ) = e^{-iτH} f(0)`. -/
theorem evolve_apply_eq_of_hasDerivAt (H : Matrix S S ℂ) {f : ℝ → EuclideanSpace ℂ S}
    (hf : ∀ t, HasDerivAt f
      ((-Complex.I) • SparseHamiltonian.SparseStateOverlap.matrixOperator H (f t)) t)
    (τ : ℝ) : evolve H τ (f 0) = f τ := by
  exact Helpers.SpinChain.flow_apply_eq_of_hasDerivAt _ hf τ

/-- **Schur test** for the `L²` operator norm: if `|A_{ij}| ≤ w_{ij}` with `w`
symmetric and `Σ_j w_{ij} v_j ≤ r v_i` for a positive vector `v`, then
`‖A‖ ≤ r`. With `v_k = √binom(n,k)` this is the nonnegativity argument of
lines 2263-2270; with `v = 1` it is the row-sum bound of line 2271 and the
padding-block bound of lines 2480-2481. (`0 ≤ r` is needed for an empty index type.) -/
theorem norm_le_of_schur (A : Matrix S S ℂ) (w : S → S → ℝ) (hw : ∀ i j, w i j = w j i)
    (hA : ∀ i j, ‖A i j‖ ≤ w i j) (v : S → ℝ) (hv : ∀ i, 0 < v i) {r : ℝ} (hr : 0 ≤ r)
    (hwv : ∀ i, ∑ j, w i j * v j ≤ r * v i) : ‖A‖ ≤ r := by
  exact Helpers.SpinChain.norm_le_of_schur A w hw hA v hv hr hwv

end Operator

/-! ### Path matrices and spin weights -/

/-- A real rescaling of the weights rescales the path: `a B = B_{a c}`. -/
theorem pathMatrix_smul (n : ℕ) (a : ℝ) (c : ℕ → ℝ) :
    pathMatrix n (fun k => a * c k) = (a : ℂ) • pathMatrix n c := by
  ext i j
  simp only [pathMatrix, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- The difference of two paths is the path of the weight differences. -/
theorem pathMatrix_sub (n : ℕ) (c c' : ℕ → ℝ) :
    pathMatrix n c - pathMatrix n c' = pathMatrix n (fun k => c k - c' k) := by
  ext i j
  simp only [pathMatrix, Matrix.of_apply, Matrix.sub_apply]
  split_ifs <;> simp

theorem spinWeight_nonneg (n k : ℕ) : 0 ≤ spinWeight n k := by
  exact Helpers.SpinChain.weight_nonneg n k

/-- `b_k ≤ 1`: `(k+1)(n-k) ≤ ((n+1)/2)² ≤ n²`. -/
theorem spinWeight_le_one (n k : ℕ) : spinWeight n k ≤ 1 := by
  exact Helpers.SpinChain.weight_le_one n k

/-- Every genuine edge weight is positive (line 2277). -/
theorem spinWeight_pos {n k : ℕ} (hk : k < n) : 0 < spinWeight n k := by
  exact Helpers.SpinChain.weight_pos hk

/-- `b_k ≥ 1/√n` for `k < n`, since `(k+1)(n-k) - n = k(n-k-1) ≥ 0`; this is
the `½ min_k b_k ≥ 1/(2√n)` behind the rounding precision of eq. `hsl:eq:round`. -/
theorem inv_sqrt_le_spinWeight {n k : ℕ} (hk : k < n) : (Real.sqrt n)⁻¹ ≤ spinWeight n k := by
  exact Helpers.SpinChain.inv_sqrt_le_weight hk

/-- Two consecutive weights meet at a vertex with squared mass at most one:
`b_k² + b_{k+1}² ≤ 1` (for every `n, k`; `n² - n - 2j(n-j) ≥ 0` with
`j = k+1 < n`). This gives row/column Euclidean norms at most one for the
chains (lines 2113-2114, 2282-2283). -/
theorem spinWeight_sq_add_sq_le (n k : ℕ) : spinWeight n k ^ 2 + spinWeight n (k + 1) ^ 2 ≤ 1 := by
  exact Helpers.SpinChain.weight_sq_add_sq_le n k

/-- The ladder identity `n b_k √binom(n,k) = (k+1) √binom(n,k+1)`, from
`(n-k) binom(n,k) = (k+1) binom(n,k+1)`. -/
theorem spinWeight_mul_sqrt_choose {n k : ℕ} (hk : k < n) :
    (n : ℝ) * spinWeight n k * Real.sqrt (n.choose k) = (k + 1) * Real.sqrt (n.choose (k + 1)) := by
  exact Helpers.SpinChain.weight_mul_sqrt_choose hk

/-- The ladder identity `n b_k √binom(n,k+1) = (n-k) √binom(n,k)`. -/
theorem spinWeight_mul_sqrt_choose_succ {n k : ℕ} (hk : k < n) :
    (n : ℝ) * spinWeight n k * Real.sqrt (n.choose (k + 1)) = ((n : ℝ) - k) * Real.sqrt (n.choose k) := by
  exact Helpers.SpinChain.weight_mul_sqrt_choose_succ hk

variable {n : ℕ}

theorem isHermitian_pathMatrix (n : ℕ) (c : ℕ → ℝ) : (pathMatrix n c).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, pathMatrix, Matrix.of_apply]
  split_ifs <;> first | omega | simp [Complex.conj_ofReal]

/-- Evolution under a Hermitian matrix preserves norms. -/
theorem norm_evolve_apply {S : Type*} [Fintype S] [DecidableEq S] {H : Matrix S S ℂ}
    (hH : H.IsHermitian) (τ : ℝ) (v : EuclideanSpace ℂ S) : ‖evolve H τ v‖ = ‖v‖ := by
  exact ContinuousLinearMap.norm_map_of_mem_unitary (evolve_mem_unitary hH τ) v

/-! ### Entry norms and row sums (proof helpers) -/

/-- Entry norms of a path matrix. -/
theorem norm_pathMatrix_apply (c : ℕ → ℝ) (i j : Fin (n + 1)) :
    ‖pathMatrix n c i j‖ =
      if (i : ℕ) = j + 1 then |c j| else if (j : ℕ) = i + 1 then |c i| else 0 := by
  simp only [pathMatrix, Matrix.of_apply]
  split_ifs <;> simp

theorem norm_pathMatrix_symm (c : ℕ → ℝ) (i j : Fin (n + 1)) :
    ‖pathMatrix n c i j‖ = ‖pathMatrix n c j i‖ := by
  rw [← (isHermitian_pathMatrix n c).apply i j, norm_star]

/-- Weighted absolute row sums of a path: the two neighbour terms. -/
theorem sum_norm_pathMatrix_mul (c : ℕ → ℝ) (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    ∑ j, ‖pathMatrix n c i j‖ * v j =
      (if h : 0 < (i : ℕ) then |c (i - 1)| * v ⟨i - 1, by omega⟩ else 0) +
        (if h : (i : ℕ) < n then |c i| * v ⟨i + 1, by omega⟩ else 0) := by
  simp only [norm_pathMatrix_apply, ite_mul, zero_mul]
  exact Helpers.SpinChain.sum_path (fun j => |c j| * v j) (fun j => |c i| * v j) i

/-! ### The explicit solution behind eq. `hsl:eq:spinamp` -/

/-- The explicit solution of `f' = -i a B_n f`, `f(0) = |0⟩`:
`f_k(t) = √binom(n,k) cos(at/n)^{n-k} (-i sin(at/n))^k`, the symmetric-subspace
restriction of `(cos θ |0⟩ - i sin θ |1⟩)^{⊗n}` with `θ = at/n` (lines
2231-2232: each qubit contributes `-i sin(τ/n)` between `|0⟩` and `|1⟩`). -/
def spinSolution (n : ℕ) (a t : ℝ) : EuclideanSpace ℂ (Fin (n + 1)) :=
  WithLp.toLp 2 fun k =>
    ((Real.sqrt (n.choose (k : ℕ)) : ℝ) : ℂ) * ((Real.cos (a * t / n) : ℝ) : ℂ) ^ (n - (k : ℕ)) *
      (-Complex.I * ((Real.sin (a * t / n) : ℝ) : ℂ)) ^ (k : ℕ)

/-- The explicit solution starts at `|0⟩`. -/
theorem spinSolution_zero (n : ℕ) (a : ℝ) : spinSolution n a 0 = EuclideanSpace.single 0 1 := by
  ext k
  simp only [spinSolution, PiLp.toLp_apply, mul_zero, zero_div, Real.cos_zero, Real.sin_zero,
    Complex.ofReal_one, Complex.ofReal_zero, one_pow, mul_one, PiLp.single_apply]
  by_cases hk : k = 0
  · subst hk
    simp
  · have hk' : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    simp [hk, zero_pow hk']

/-- Its endpoint component is `(-i)^n sin(at/n)^n`. -/
theorem spinSolution_last (n : ℕ) (a t : ℝ) :
    spinSolution n a t (Fin.last n) = (-Complex.I) ^ n * ((Real.sin (a * t / n) ^ n : ℝ) : ℂ) := by
  simp only [spinSolution, PiLp.toLp_apply, Fin.val_last, Nat.choose_self, Nat.sub_self, pow_zero,
    mul_one, Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, one_mul, mul_pow, Complex.ofReal_pow]

/-- The explicit vector solves `f' = -i (a B_n) f` (componentwise, using the
ladder identities `spinWeight_mul_sqrt_choose(_succ)`). -/
theorem hasDerivAt_spinSolution (_hn : 1 ≤ n) (a t : ℝ) :
    HasDerivAt (spinSolution n a)
      ((-Complex.I) • SparseHamiltonian.SparseStateOverlap.matrixOperator
        (pathMatrix n fun k => a * spinWeight n k) (spinSolution n a t)) t := by
  have hθ : HasDerivAt (fun u : ℝ => a * u / n) (a / n) t := by
    simpa using ((hasDerivAt_id t).const_mul a).div_const (n : ℝ)
  have hpi : HasDerivAt (fun u => WithLp.ofLp (spinSolution n a u))
      (fun k : Fin (n + 1) => ((Real.sqrt (n.choose (k : ℕ)) : ℝ) : ℂ) * ((a / n : ℝ) : ℂ) *
        (-Complex.I) *
        (((n - (k : ℕ) : ℕ) : ℂ) * ((Real.cos (a * t / n) : ℝ) : ℂ) ^ (n - (k : ℕ) - 1) *
            (-Complex.I * ((Real.sin (a * t / n) : ℝ) : ℂ)) ^ ((k : ℕ) + 1) +
          ((k : ℕ) : ℂ) * ((Real.cos (a * t / n) : ℝ) : ℂ) ^ (n - (k : ℕ) + 1) *
            (-Complex.I * ((Real.sin (a * t / n) : ℝ) : ℂ)) ^ ((k : ℕ) - 1))) t :=
    hasDerivAt_pi.2 fun k => Helpers.SpinChain.hasDerivAt_trigMonomial hθ _ _ _
  refine ((PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt t hpi).congr_deriv ?_
  ext k
  simp only [ContinuousLinearEquiv.coe_coe, PiLp.continuousLinearEquiv_symm_apply,
    PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul,
    SparseHamiltonian.SparseStateOverlap.matrixOperator_apply, pathMatrix, Matrix.of_apply,
    ite_mul, zero_mul]
  rw [Helpers.SpinChain.sum_path]
  simp only [spinSolution, PiLp.toLp_apply, dite_eq_ite]
  exact Helpers.SpinChain.spin_row a _ _ (Nat.lt_succ_iff.1 k.isLt)

/-- **Eq. `hsl:eq:spinamp`, endpoint amplitude**, for the scaled chain `a B_n`:
`⟨n| e^{-iτ a B_n} |0⟩ = (-i)^n sin(aτ/n)^n` (lines 2226-2232). -/
theorem endAmp_scaled (hn : 1 ≤ n) (a τ : ℝ) :
    endAmp n (fun k => a * spinWeight n k) τ =
      (-Complex.I) ^ n * ((Real.sin (a * τ / n) ^ n : ℝ) : ℂ) := by
  unfold endAmp
  rw [← spinSolution_zero n a, evolve_apply_eq_of_hasDerivAt _ (hasDerivAt_spinSolution hn a) τ,
    spinSolution_last]

/-! ### Norms: the positive eigenvector `√binom(n,k)` -/

/-- The positive eigenvector `v_k = √binom(n,k)` of `B_n` (the restriction of
`|+⟩^{⊗n}`); the Schur-test weight of the nonnegativity argument (lines
2263-2270). -/
def binomVec (n : ℕ) : Fin (n + 1) → ℝ := fun k => Real.sqrt (n.choose (k : ℕ))

theorem binomVec_pos (n : ℕ) (k : Fin (n + 1)) : 0 < binomVec n k := by
  exact Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.choose_pos (Nat.lt_succ_iff.1 k.isLt)))

theorem sum_norm_spinMatrix_mul_binomVec_aux (hn : 1 ≤ n) (i : Fin (n + 1)) :
    ∑ j, ‖spinMatrix n i j‖ * binomVec n j = binomVec n i := by
  rw [spinMatrix, sum_norm_pathMatrix_mul]
  simp only [binomVec, abs_of_nonneg (spinWeight_nonneg _ _), dite_eq_ite]
  exact Helpers.SpinChain.binom_row hn i (Nat.lt_succ_iff.1 i.isLt)

/-- `B_n v = v` for `v_k = √binom(n,k)`, `n ≥ 1`. -/
theorem spinMatrix_mulVec_binomVec (hn : 1 ≤ n) :
    spinMatrix n *ᵥ (fun k => (binomVec n k : ℂ)) = fun k => (binomVec n k : ℂ) := by
  funext i
  have h := sum_norm_spinMatrix_mul_binomVec_aux hn i
  have hent : ∀ j, spinMatrix n i j = ((‖spinMatrix n i j‖ : ℝ) : ℂ) := by
    intro j
    simp only [spinMatrix, pathMatrix, Matrix.of_apply]
    split_ifs <;> simp [abs_of_nonneg (spinWeight_nonneg _ _)]
  simp only [Matrix.mulVec, dotProduct]
  rw [← h, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.ofReal_mul, ← hent j]

/-- The real form of `B_n v = v` used in the Schur test (`B_n` is entrywise
nonnegative). -/
theorem sum_norm_spinMatrix_mul_binomVec (hn : 1 ≤ n) (i : Fin (n + 1)) :
    ∑ j, ‖spinMatrix n i j‖ * binomVec n j = binomVec n i := by
  exact sum_norm_spinMatrix_mul_binomVec_aux hn i

/-- **Eq. `hsl:eq:spinamp`, norm**: `‖B_n‖ = 1` for `n ≥ 1`. -/
theorem norm_spinMatrix (hn : 1 ≤ n) : ‖spinMatrix n‖ = 1 := by
  refine le_antisymm ?_ ?_
  · refine Helpers.SpinChain.norm_le_of_schur _ (fun i j => ‖spinMatrix n i j‖)
      (fun i j => norm_pathMatrix_symm _ i j) (fun _ _ => le_rfl) (binomVec n) (binomVec_pos n)
      zero_le_one fun i => ?_
    rw [one_mul, sum_norm_spinMatrix_mul_binomVec hn i]
  · refine Helpers.SpinChain.one_le_norm_of_mulVec_eq _ (fun k => (binomVec n k : ℂ)) ?_
      (spinMatrix_mulVec_binomVec hn)
    intro h
    have h0 := congrFun h 0
    simp only [Pi.zero_apply, Complex.ofReal_eq_zero] at h0
    exact (binomVec_pos n 0).ne' h0

/-- The nonnegativity argument (lines 2263-2270): weights `0 ≤ c_k ≤ b_k`
give a path of norm at most one. -/
theorem norm_pathMatrix_le {c : ℕ → ℝ} (hc0 : ∀ k, 0 ≤ c k)
    (hc : ∀ k, k < n → c k ≤ spinWeight n k) : ‖pathMatrix n c‖ ≤ 1 := by
  refine Helpers.SpinChain.norm_le_of_schur _ (fun i j => ‖spinMatrix n i j‖)
    (fun i j => norm_pathMatrix_symm _ i j) (fun i j => ?_) (binomVec n) (binomVec_pos n)
    zero_le_one fun i => ?_
  · have hi := i.isLt
    have hj := j.isLt
    rw [spinMatrix, norm_pathMatrix_apply, norm_pathMatrix_apply]
    split_ifs with h1 h2
    · rw [abs_of_nonneg (hc0 _), abs_of_nonneg (spinWeight_nonneg _ _)]
      exact hc _ (by omega)
    · rw [abs_of_nonneg (hc0 _), abs_of_nonneg (spinWeight_nonneg _ _)]
      exact hc _ (by omega)
    · exact le_rfl
  · rw [one_mul]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hi : (i : ℕ) = 0 := by have := i.isLt; omega
      rw [spinMatrix, sum_norm_pathMatrix_mul]
      simp only [hi, lt_irrefl, dite_false, add_zero]
      exact (binomVec_pos 0 i).le
    · exact (sum_norm_spinMatrix_mul_binomVec hn i).le

/-- Row sums of a path (line 2271): each row meets at most two edges, so with
`|c_k| ≤ δ` every absolute row sum is at most `2δ` (the `v = 1` input of
`norm_le_of_schur`; with `pathMatrix_sub` it gives `norm_pathMatrix_sub_le`). -/
theorem sum_norm_pathMatrix_le {c : ℕ → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ k, k < n → |c k| ≤ δ) (i : Fin (n + 1)) :
    ∑ j, ‖pathMatrix n c i j‖ ≤ 2 * δ := by
  have hi := i.isLt
  calc ∑ j, ‖pathMatrix n c i j‖ = ∑ j, ‖pathMatrix n c i j‖ * 1 := by simp
    _ = _ := sum_norm_pathMatrix_mul c (fun _ => 1) i
    _ ≤ δ + δ := by
      refine add_le_add ?_ ?_
      · split_ifs with h
        · simp only [mul_one]
          exact hδ _ (by omega)
        · exact hδ0
      · split_ifs with h
        · simp only [mul_one]
          exact hδ _ h
        · exact hδ0
    _ = 2 * δ := by ring

/-- Row sums (line 2271): `‖B - B'‖ ≤ 2δ` when the weights differ by at most `δ`. -/
theorem norm_pathMatrix_sub_le {c c' : ℕ → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ k, k < n → |c k - c' k| ≤ δ) : ‖pathMatrix n c - pathMatrix n c'‖ ≤ 2 * δ := by
  rw [pathMatrix_sub]
  refine Helpers.SpinChain.norm_le_of_schur _
    (fun i j => ‖pathMatrix n (fun k => c k - c' k) i j‖) (fun i j => norm_pathMatrix_symm _ i j)
    (fun _ _ => le_rfl) (fun _ => 1) (fun _ => one_pos) (by linarith) fun i => ?_
  simp only [mul_one]
  exact sum_norm_pathMatrix_le hδ0 hδ i

end

end SparseLowerBounds.Hamiltonian
end
