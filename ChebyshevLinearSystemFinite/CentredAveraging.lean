import ChebyshevLinearSystemFinite.Cost
import ChebyshevLinearSystem.Run
import SparseLinearSystems.Circuit.Run

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

/-!
# Centred averaging (Remark `qls:rem:averaging`) and the query comparison of Remark
`qls:rem:constants`

Let `f(W) = ∑_{j=0}^{d} a_j W^j` with `a_j ≥ 0`, `∑_j a_j = 1` (a real polynomial `p` with
nonnegative coefficients, `p(1) = 1` and `deg p ≤ d`; `polyOp p W`), and put `m = ⌊d/2⌋`
(`lowHalf`) and `c = ⌈d/2⌉` (`highHalf`), so `m + c = d`, `c = m` for even `d` and `c = m + 1`
for odd `d`.

**Centring.** For a unitary `W` and any `P` with `W P = P`, `W^{-m} P = P`
(`wpow_neg_mul_of_fixed`), hence `W^{-m} f(W) - P = W^{-m}(f(W) - P)` (`centred_sub_eq`) and,
`W^{-m}` being unitary, the error relative to `P` and the selected-vector norm are unchanged:
`‖(W^{-m} f(W) - P) x‖ = ‖(f(W) - P) x‖`, `‖W^{-m} f(W) x‖ = ‖f(W) x‖` and
`‖W^{-m} f(W) - P‖ = ‖f(W) - P‖` (`norm_centred_sub_apply`, `norm_centred_apply`,
`opNorm_centred_sub`). For the averaging filter `f_N(W)^k` at the fixed-space projector this
gives `‖(W^{-m} f_N(W)^k - P) x‖ ≤ (N b)^{-k} ‖x‖` and equation `qls:eq:filterprobability` for
the centred filter (`centred_filter_error`).

**The circuit.** `W^{-m} f(W) = ∑_{|z| ≤ c} a_{z+m} W^z` (`centred_sum`; the exponents
`j - m` lie in `[-m, d - m] ⊆ [-c, c]`, and for odd `d` the branch `z = -c` carries weight zero,
`centCoeff_neg_highHalf`). On the released counter register `ℂ^{T+1} ⊗ V` with `2c ≤ T`, the
coefficient seed `v ↦ ∑_j √a_{j-c+m} |j⟩ ⊗ v` (`centSeedT`, the released
`WeightedClock.boundary`) is an isometry (`centSeedT_isometry`), and after the `c` signed steps of
`ChebyshevLinearSystem` (`signedStepsT`: `W` on branches with `j - c ≥ l`, `W†` on those with
`j - c ≤ -l`, inactive otherwise) its compression is exactly `W^{-m} f(W)`
(`centT_compression`). The physical circuit is the released signed-step run
`ChebyshevLinearSystem.runPhys … c` on the physical oracle family (native sparse primitives and
the controlled source preparation): its success block is `W_{σ,r}(x)^{-m} f(W_{σ,r}(x))` on
every input, the block of its literal adjoint program is the adjoint, and both make
`54 c` matrix-oracle and `2 c` source calls (`centred_run`, `centred_test_amplitude`). For
`d = 0` the circuit has no step and the block is the identity (`centred_run_zero`). For the
averaging filter `f_N(W)^k` (`d = k (N - 1)`) the centred circuit uses `⌈k(N-1)/2⌉` signed
steps (`centred_averaging_run`).

**The query comparison** (Remark `qls:rem:constants`). The released forward run with `t` steps
(`SparseLinearSystems.Run.runPhys`) and the signed run with `t` steps both make `54 t`
matrix-oracle and `2 t` source calls (`step_costs`). With the conservative averaging length
`n_av = ⌈100π/ω⌉`, `ω = g/(512√s)` (`nAv`), the forward averaging schedule uses
`q_av = n_av - 1` steps (`qAv`); composing with the established step comparisons:

* single test: the actual Chebyshev run of `d^fin_σ(1/100)` signed steps makes fewer than
  `1/1400` of the matrix-oracle (and source) calls of the actual forward run of `q_av` steps
  (`test_query_comparison`);
* repeated stage: for `δ ≤ 1/100` and `k = ⌈log(1/δ)/log 100⌉`, the Chebyshev run of
  `d^fin_σ(δ)` signed steps against the forward run of `k q_av` steps, the repeated averaging
  schedule (`final_query_comparison`);
* the prescribed budgets, holding the numbers of tests and attempts fixed: the signed-step
  budget `walkStepsF` of the finite-degree protocol against the same budget with every test
  degree replaced by `q_av(σ_j)` and the final degree by `k q_av(1/κ)` (`walkStepsAv`,
  `walkSteps_ratio`, `budget_query_comparison`).

`averaging_schedules` states the three schedules of one averaging filter `f_{n_av}(W)^k` side by
side on the released walk, with their exact success amplitudes and costs: the forward run of
`k q_av` steps, the centred run of `⌈k q_av/2⌉` signed steps (for `k = 1`,
`⌈q_av/2⌉ = ⌈(n_av - 1)/2⌉`) and a Chebyshev run. The comparison concerns the stated
conservative forward averaging schedule and the stated Chebyshev schedule only; the centred
averaging counts are exposed separately, and the factors `700` for the centred single test
and the centred repeated stage (`centred_test_ratio`, `centred_final_ratio`) are derived here
and are not claims of the manuscript. Nothing here compares optimised gate counts, execution
times or other solvers, and the released `SparseLinearSystems` protocol (filter length
`⌈100/b⌉`) is not the conservative schedule.
-/

namespace ChebyshevLinearSystemFinite.CentredAveraging

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseLinearSystems OracleCircuit LogicalWalk
  CounterFilter Step Augmented ChebyshevFilter ChebyshevLinearSystem Endpoint
open scoped InnerProduct

/-! ### The two halves of the degree -/

/-- The centring shift `m = ⌊d/2⌋`. -/
def lowHalf (d : ℕ) : ℕ := d / 2

/-- The number of signed steps `c = ⌈d/2⌉`. -/
def highHalf (d : ℕ) : ℕ := (d + 1) / 2

theorem lowHalf_add_highHalf (d : ℕ) : lowHalf d + highHalf d = d := by
  unfold lowHalf highHalf
  omega

theorem lowHalf_le_highHalf (d : ℕ) : lowHalf d ≤ highHalf d := by
  unfold lowHalf highHalf
  omega

theorem highHalf_le_succ_lowHalf (d : ℕ) : highHalf d ≤ lowHalf d + 1 := by
  unfold lowHalf highHalf
  omega

/-- For even `d`, `c = m`. -/
theorem highHalf_eq_of_even {d : ℕ} (h : d % 2 = 0) : highHalf d = lowHalf d := by
  unfold lowHalf highHalf
  omega

/-- For odd `d`, `c = m + 1`. -/
theorem highHalf_eq_of_odd {d : ℕ} (h : d % 2 = 1) : highHalf d = lowHalf d + 1 := by
  unfold lowHalf highHalf
  omega

theorem halves_zero : lowHalf 0 = 0 ∧ highHalf 0 = 0 := ⟨rfl, rfl⟩

/-- `d ≤ 2c ≤ d + 1` and `c ≤ d`. -/
theorem highHalf_bounds (d : ℕ) : d ≤ 2 * highHalf d ∧ 2 * highHalf d ≤ d + 1 ∧ highHalf d ≤ d := by
  unfold highHalf
  omega

theorem Icc_low_sub (d : ℕ) :
    Finset.Icc (-(lowHalf d : ℤ)) (highHalf d) ⊆ Finset.Icc (-(highHalf d : ℤ)) (highHalf d) := by
  intro z hz
  rw [Finset.mem_Icc] at hz ⊢
  have := lowHalf_le_highHalf d
  omega

/-! ### Signed powers of a unitary -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem adjoint_pow_mul_pow {W : V →L[ℂ] V} (hW : W† * W = 1) (j : ℕ) :
    (W†) ^ j * W ^ j = 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc (W†) ^ (j + 1) * W ^ (j + 1) = (W†) ^ j * ((W† * W) * W ^ j) := by
          rw [pow_succ, pow_succ']
          simp only [mul_assoc]
      _ = 1 := by rw [hW, one_mul, ih]

/-- `W^{-m} W^j = W^{j - m}` for an isometry `W`. -/
theorem wpow_neg_mul_pow {W : V →L[ℂ] V} (hW : W† * W = 1) (m j : ℕ) :
    wpow W (-(m : ℤ)) * W ^ j = wpow W ((j : ℤ) - m) := by
  rw [wpow_neg_natCast]
  rcases le_total m j with h | h
  · obtain ⟨e, rfl⟩ : ∃ e, j = m + e := ⟨j - m, by omega⟩
    rw [pow_add, ← mul_assoc, adjoint_pow_mul_pow hW, one_mul,
      show ((m + e : ℕ) : ℤ) - m = (e : ℤ) by push_cast; ring, wpow_natCast]
  · obtain ⟨e, rfl⟩ : ∃ e, m = e + j := ⟨m - j, by omega⟩
    rw [pow_add, mul_assoc, adjoint_pow_mul_pow hW, mul_one,
      show (j : ℤ) - ((e + j : ℕ) : ℤ) = -(e : ℤ) by push_cast; ring, wpow_neg_natCast]

theorem isometry_of_isUnitary {W : V →L[ℂ] V} (hW : IsUnitary W) : W† * W = 1 := by
  rw [← star_eq_adjoint]
  exact hW.1

theorem coisometry_of_isUnitary {W : V →L[ℂ] V} (hW : IsUnitary W) : W * W† = 1 := by
  rw [← star_eq_adjoint]
  exact hW.2

theorem norm_pow_apply_of_isometry {W : V →L[ℂ] V} (hW : W† * W = 1) (n : ℕ) (v : V) :
    ‖(W ^ n) v‖ = ‖v‖ := by
  apply (W ^ n).norm_map_iff_adjoint_comp_self.mpr
  rw [← star_eq_adjoint, star_pow, star_eq_adjoint, ← mul_def]
  exact adjoint_pow_mul_pow hW n

/-- Signed powers of a unitary are isometric. -/
theorem norm_wpow_apply {W : V →L[ℂ] V} (hW : IsUnitary W) (z : ℤ) (v : V) :
    ‖wpow W z v‖ = ‖v‖ := by
  unfold wpow
  split_ifs
  · exact norm_pow_apply_of_isometry (isometry_of_isUnitary hW) _ v
  · have h : (W†)† * W† = 1 := by rw [adjoint_adjoint]; exact coisometry_of_isUnitary hW
    exact norm_pow_apply_of_isometry h _ v

/-! ### Centring preserves the error and the selected norm -/

/-- `W^{-m} P = P` when `W P = P` and `W` is an isometry. -/
theorem wpow_neg_mul_of_fixed {W P : V →L[ℂ] V} (hW : W† * W = 1) (hP : W * P = P) (m : ℕ) :
    wpow W (-(m : ℤ)) * P = P := by
  rw [wpow_neg_natCast]
  have h1 : W† * P = P := by
    conv_lhs => rw [← hP]
    rw [← mul_assoc, hW, one_mul]
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, mul_assoc, h1, ih]

/-- **Centring keeps the error operator**: `W^{-m} F - P = W^{-m} (F - P)`. -/
theorem centred_sub_eq {W P : V →L[ℂ] V} (hW : W† * W = 1) (hP : W * P = P) (m : ℕ)
    (F : V →L[ℂ] V) : wpow W (-(m : ℤ)) * F - P = wpow W (-(m : ℤ)) * (F - P) := by
  rw [mul_sub, wpow_neg_mul_of_fixed hW hP]

/-- The error relative to `P` is unchanged on every vector. -/
theorem norm_centred_sub_apply {W P : V →L[ℂ] V} (hW : IsUnitary W) (hP : W * P = P) (m : ℕ)
    (F : V →L[ℂ] V) (v : V) : ‖(wpow W (-(m : ℤ)) * F - P) v‖ = ‖(F - P) v‖ := by
  rw [centred_sub_eq (isometry_of_isUnitary hW) hP, mul_apply_eq_comp,
    norm_wpow_apply hW]

/-- The selected vector keeps its norm (the success probability is unchanged). -/
theorem norm_centred_apply {W : V →L[ℂ] V} (hW : IsUnitary W) (m : ℕ) (F : V →L[ℂ] V) (v : V) :
    ‖(wpow W (-(m : ℤ)) * F) v‖ = ‖F v‖ := by
  rw [mul_apply_eq_comp, norm_wpow_apply hW]

/-- The operator-norm error relative to `P` is unchanged. -/
theorem opNorm_centred_sub {W P : V →L[ℂ] V} (hW : IsUnitary W) (hP : W * P = P) (m : ℕ)
    (F : V →L[ℂ] V) : ‖wpow W (-(m : ℤ)) * F - P‖ = ‖F - P‖ :=
  opNorm_ext _ _ (fun v => norm_centred_sub_apply hW hP m F v)

omit [CompleteSpace V] in
theorem mul_fixedProj [FiniteDimensional ℂ V] (W : V →L[ℂ] V) :
    W * UnitaryFilter.fixedProj W = UnitaryFilter.fixedProj W := by
  ext v
  rw [mul_apply_eq_comp]
  exact UnitaryFilter.mem_fixedSpace.mp (Submodule.starProjection_apply_mem _ v)

/-- **The centred averaging filter** `W^{-m} f_N(W)^k`: its error relative to the fixed-space
projector is at most `(N b)^{-k} ‖x‖` and it satisfies equation `qls:eq:filterprobability`,
for every shift `m`. -/
theorem centred_filter_error [FiniteDimensional ℂ V] {W : V →L[ℂ] V} (hW : IsUnitary W) (b : ℝ)
    (hb : 0 < b) (hgap : ∀ (z : ℂ) (v : V), v ≠ 0 → W v = z • v → z ≠ 1 → 2 * b ≤ ‖z - 1‖)
    (N : ℕ) (hN : 0 < N) (k m : ℕ) (x : V) :
    ‖(wpow W (-(m : ℤ)) * UnitaryFilter.filter W N k - UnitaryFilter.fixedProj W) x‖ ≤
        (1 / (N * b)) ^ k * ‖x‖ ∧
      ‖(wpow W (-(m : ℤ)) * UnitaryFilter.filter W N k) x‖ ^ 2 =
        ‖UnitaryFilter.fixedProj W x‖ ^ 2 +
          ‖(wpow W (-(m : ℤ)) * UnitaryFilter.filter W N k - UnitaryFilter.fixedProj W) x‖ ^ 2 := by
  have hU : UnitaryFilter.Unitary W := ⟨hW.1, hW.2⟩
  rw [norm_centred_sub_apply hW (mul_fixedProj W), norm_centred_apply hW, sub_apply]
  exact ⟨UnitaryFilter.filter_sub_proj_le hU b hb hgap N hN k x,
    UnitaryFilter.filter_norm_sq hU b hb hgap N hN k x⟩

/-! ### Polynomials with nonnegative coefficients and their centred coefficients -/

/-- `f(W) = ∑_j a_j W^j` for the real polynomial `p = ∑_j a_j X^j`. -/
def polyOp (p : Polynomial ℝ) (W : V →L[ℂ] V) : V →L[ℂ] V :=
  Polynomial.aeval W (p.map (algebraMap ℝ ℂ))

omit [CompleteSpace V] in
theorem polyOp_eq_sum (p : Polynomial ℝ) {d : ℕ} (hp : p.natDegree ≤ d) (W : V →L[ℂ] V) :
    polyOp p W = ∑ j ∈ Finset.range (d + 1), ((p.coeff j : ℝ) : ℂ) • W ^ j := by
  have hdeg : (p.map (algebraMap ℝ ℂ)).natDegree < d + 1 :=
    lt_of_le_of_lt (Polynomial.natDegree_map_le.trans hp) (Nat.lt_succ_self d)
  rw [polyOp, Polynomial.aeval_eq_sum_range' hdeg W]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.coeff_map]
  rfl

omit [CompleteSpace V] in
/-- The averaging filter is `polyOp` of `q_N^k`. -/
theorem polyOp_avg (W : V →L[ℂ] V) (N k : ℕ) :
    polyOp (avgPoly N ^ k) W = UnitaryFilter.filter W N k := by
  rw [polyOp, Polynomial.map_pow, ← avgPolyC_eq_map, map_pow, aeval_avgPolyC]
  rfl

/-- The coefficient of `W^z` in `W^{-m} f(W)`: `a_{z+m}`, and zero for `z < -m`. -/
def centCoeff (d : ℕ) (p : Polynomial ℝ) (z : ℤ) : ℝ :=
  if 0 ≤ z + lowHalf d then p.coeff (z + lowHalf d).toNat else 0

theorem centCoeff_nonneg {d : ℕ} {p : Polynomial ℝ} (hpos : ∀ j, 0 ≤ p.coeff j) (z : ℤ) :
    0 ≤ centCoeff d p z := by
  unfold centCoeff
  split_ifs
  · exact hpos _
  · exact le_rfl

/-- The centred coefficients vanish outside `[-m, c]`. -/
theorem centCoeff_eq_zero {d : ℕ} {p : Polynomial ℝ} (hp : p.natDegree ≤ d) {z : ℤ}
    (hz : z ∉ Finset.Icc (-(lowHalf d : ℤ)) (highHalf d)) : centCoeff d p z = 0 := by
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hz
  have hd := lowHalf_add_highHalf d
  unfold centCoeff
  split_ifs with h
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    omega
  · rfl

theorem centCoeff_shift (d : ℕ) (p : Polynomial ℝ) (j : ℕ) :
    centCoeff d p ((j : ℤ) - lowHalf d) = p.coeff j := by
  unfold centCoeff
  rw [if_pos (by omega)]
  congr 1
  omega

/-- **Inactive branch** for odd `d`: the power `-c` carries weight zero. -/
theorem centCoeff_neg_highHalf {d : ℕ} (p : Polynomial ℝ) (h : d % 2 = 1) :
    centCoeff d p (-(highHalf d : ℤ)) = 0 := by
  have := highHalf_eq_of_odd h
  unfold centCoeff
  rw [if_neg (by omega)]

/-- Reindexing: a function supported on `[-m, c]` has the same sum over `[-c, c]` as over the
shifted exponents `j - m`, `0 ≤ j ≤ d`. -/
theorem sum_centred {M : Type*} [AddCommMonoid M] (d : ℕ) (f : ℤ → M)
    (hf : ∀ z, z ∉ Finset.Icc (-(lowHalf d : ℤ)) (highHalf d) → f z = 0) :
    ∑ z ∈ Finset.Icc (-(highHalf d : ℤ)) (highHalf d), f z =
      ∑ j ∈ Finset.range (d + 1), f ((j : ℤ) - lowHalf d) := by
  have hd := lowHalf_add_highHalf d
  rw [← Finset.sum_subset (Icc_low_sub d) (fun z _ hz => hf z hz)]
  symm
  apply Finset.sum_bij (fun (j : ℕ) _ => (j : ℤ) - lowHalf d)
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.mem_Icc]
    omega
  · intro a _ b _ h
    have h' : (a : ℤ) - lowHalf d = (b : ℤ) - lowHalf d := h
    omega
  · intro z hz
    rw [Finset.mem_Icc] at hz
    refine ⟨(z + lowHalf d).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · show (((z + lowHalf d).toNat : ℕ) : ℤ) - lowHalf d = z
      omega
  · intro j _
    rfl

/-- The centred coefficients sum to one. -/
theorem sum_centCoeff {d : ℕ} {p : Polynomial ℝ} (hp : p.natDegree ≤ d) (h1 : p.eval 1 = 1) :
    ∑ z ∈ Finset.Icc (-(highHalf d : ℤ)) (highHalf d), centCoeff d p z = 1 := by
  rw [sum_centred d (centCoeff d p) (fun z hz => centCoeff_eq_zero hp hz)]
  calc ∑ j ∈ Finset.range (d + 1), centCoeff d p ((j : ℤ) - lowHalf d)
      = ∑ j ∈ Finset.range (d + 1), p.coeff j :=
        Finset.sum_congr rfl (fun j _ => centCoeff_shift d p j)
    _ = 1 := by
        rw [← h1, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp)]
        simp

/-- **The centred Laurent form**: `∑_{|z| ≤ c} a_{z+m} W^z = W^{-m} f(W)` for an isometry
`W`; the exponents `j - m` of `f` lie in `[-m, d - m] ⊆ [-c, c]`. -/
theorem centred_sum {W : V →L[ℂ] V} (hW : W† * W = 1) {d : ℕ} {p : Polynomial ℝ}
    (hp : p.natDegree ≤ d) :
    ∑ z ∈ Finset.Icc (-(highHalf d : ℤ)) (highHalf d), ((centCoeff d p z : ℝ) : ℂ) • wpow W z =
      wpow W (-(lowHalf d : ℤ)) * polyOp p W := by
  rw [sum_centred d (fun z => ((centCoeff d p z : ℝ) : ℂ) • wpow W z)
      (fun z hz => by rw [centCoeff_eq_zero hp hz, Complex.ofReal_zero, zero_smul]),
    polyOp_eq_sum p hp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_smul_comm, wpow_neg_mul_pow hW, centCoeff_shift]

/-! ### The circuit on the released counter register -/

/-- **The centred coefficient seed** `v ↦ ∑_j √a_{j-c+m} |j⟩ ⊗ v` on `ℂ^{T+1} ⊗ V`, where
register value `j` carries the power `j - c` (`powT c`). -/
def centSeedT (d : ℕ) (p : Polynomial ℝ) (T : ℕ) : V →L[ℂ] Ctr T V :=
  WeightedClock.boundary (fun j : Fin (T + 1) => centCoeff d p (powT (highHalf d) j))
    (fun _ => 1)

theorem sum_centCoeff_powT {d : ℕ} {p : Polynomial ℝ} (hp : p.natDegree ≤ d)
    (h1 : p.eval 1 = 1) {T : ℕ} (hT : 2 * highHalf d ≤ T) :
    ∑ j : Fin (T + 1), centCoeff d p (powT (highHalf d) j) = 1 := by
  rw [sum_powT_of_support _ T (highHalf d) hT
    (fun z hz => centCoeff_eq_zero hp (fun h => hz (Icc_low_sub d h)))]
  exact sum_centCoeff hp h1

/-- **Normalisation one**: the centred seed is an isometry. -/
theorem centSeedT_isometry {d : ℕ} {p : Polynomial ℝ} (hp : p.natDegree ≤ d)
    (hpos : ∀ j, 0 ≤ p.coeff j) (h1 : p.eval 1 = 1) {T : ℕ} (hT : 2 * highHalf d ≤ T) :
    ((centSeedT (V := V) d p T)†) ∘L centSeedT d p T = 1 := by
  have hJ : ∀ _ : Fin (T + 1), ((1 : V →L[ℂ] V)†).comp (1 : V →L[ℂ] V) = 1 :=
    fun _ => by rw [adjoint_one_eq]; rfl
  exact WeightedClock.boundary_isometry _ (fun j => centCoeff_nonneg hpos _)
    (sum_centCoeff_powT hp h1 hT) _ hJ

theorem centSeedT_norm {d : ℕ} {p : Polynomial ℝ} (hp : p.natDegree ≤ d)
    (hpos : ∀ j, 0 ≤ p.coeff j) (h1 : p.eval 1 = 1) {T : ℕ} (hT : 2 * highHalf d ≤ T) (v : V) :
    ‖centSeedT (V := V) d p T v‖ = ‖v‖ :=
  ((centSeedT (V := V) d p T).norm_map_iff_adjoint_comp_self.mpr
    (centSeedT_isometry hp hpos h1 hT)) v

/-- **The centred LCU circuit**: the `c = ⌈d/2⌉` signed steps, compressed to the centred seed,
give exactly `W^{-m} f(W)`, `m = ⌊d/2⌋`. -/
theorem centT_compression {W : V →L[ℂ] V} (hW : W† * W = 1) {d : ℕ} {p : Polynomial ℝ}
    (hp : p.natDegree ≤ d) (hpos : ∀ j, 0 ≤ p.coeff j) {T : ℕ} (hT : 2 * highHalf d ≤ T) :
    ((centSeedT (V := V) d p T)†) ∘L
        (signedStepsT W T (highHalf d) (highHalf d) ∘L centSeedT d p T) =
      wpow W (-(lowHalf d : ℤ)) * polyOp p W := by
  have hsupp : ∀ z, z ∉ Finset.Icc (-(highHalf d : ℤ)) (highHalf d) →
      ((centCoeff d p z : ℝ) : ℂ) • wpow W z = 0 := by
    intro z hz
    rw [centCoeff_eq_zero hp (fun h => hz (Icc_low_sub d h)), Complex.ofReal_zero, zero_smul]
  rw [centSeedT, signedStepsT_eq, WeightedClock.boundary_compression _
    (fun j => centCoeff_nonneg hpos _), ← centred_sum hW hp,
    ← sum_powT_of_support (fun z => ((centCoeff d p z : ℝ) : ℂ) • wpow W z) T (highHalf d) hT
      hsupp]
  apply Finset.sum_congr rfl
  intro j _
  rw [adjoint_one_eq]
  by_cases hj : powT (highHalf d) j ∈ Finset.Icc (-(highHalf d : ℤ)) (highHalf d)
  · rw [Finset.mem_Icc] at hj
    rw [show clampPow (highHalf d) (powT (highHalf d) j) = powT (highHalf d) j by
      rw [clampPow]; omega]
    rfl
  · rw [centCoeff_eq_zero hp (fun h => hj (Icc_low_sub d h)), Complex.ofReal_zero, zero_smul,
      zero_smul]

/-! ### The physical centred circuit -/

section Physical

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- The seed `E (ψ_c ⊗ J e)` of the centred circuit. -/
def centSeedVec (D : NativeSparseBlockEncoding.Data X n Z s) (d : ℕ) (p : Polynomial ℝ)
    (T : ℕ) : Phys n Z T :=
  E D T (centSeedT d p T (JwO D eVec))

/-- The flag `v ↦ E (ψ_c ⊗ v)` of the centred circuit. -/
def centFlag (D : NativeSparseBlockEncoding.Data X n Z s) (d : ℕ) (p : Polynomial ℝ) (T : ℕ) :
    PrivO n →L[ℂ] Phys n Z T :=
  E D T ∘L centSeedT d p T

theorem centSeedVec_norm (D : NativeSparseBlockEncoding.Data X n Z s) {d : ℕ}
    {p : Polynomial ℝ} (hp : p.natDegree ≤ d) (hpos : ∀ j, 0 ≤ p.coeff j) (h1 : p.eval 1 = 1)
    {T : ℕ} (hT : 2 * highHalf d ≤ T) : ‖centSeedVec D d p T‖ = 1 := by
  rw [centSeedVec, Run.E_norm, centSeedT_norm hp hpos h1 hT, LinearIsometry.norm_map,
    Run.norm_eVec]

theorem centFlag_isometry (D : NativeSparseBlockEncoding.Data X n Z s) {d : ℕ}
    {p : Polynomial ℝ} (hp : p.natDegree ≤ d) (hpos : ∀ j, 0 ≤ p.coeff j) (h1 : p.eval 1 = 1)
    {T : ℕ} (hT : 2 * highHalf d ≤ T) : (centFlag D d p T)† ∘L centFlag D d p T = 1 := by
  rw [centFlag, adjoint_comp, comp_assoc, ← comp_assoc _ _ (centSeedT d p T), E_isometry,
    Run.one_comp', centSeedT_isometry hp hpos h1 hT]

/-- The success block of the centred run is `W^{-m} f(W)` for the released walk. -/
theorem centred_block (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) {d : ℕ} {p : Polynomial ℝ}
    (hp : p.natDegree ≤ d) (hpos : ∀ j, 0 ≤ p.coeff j) {T : ℕ} (hT : 2 * highHalf d ≤ T)
    (σ r : ℝ) (x : X) :
    ((centFlag D d p T)†) ∘L
        ((ChebyshevLinearSystem.runPhys D Ub sv T σ r (highHalf d)).eval x ∘L centFlag D d p T) =
      wpow (WwO D Ub sv σ r x) (-(lowHalf d : ℤ)) * polyOp p (WwO D Ub sv σ r x) := by
  have hW := isometry_of_isUnitary (WwO_unitary D Ub sv σ r x)
  ext v
  have hrun := congrArg (fun A : Ctr T (PrivO n) →L[ℂ] Phys n Z T => A (centSeedT d p T v))
    (runPhys_intertwines D Ub hUb sv T σ r (highHalf d) x)
  simp only [comp_apply] at hrun
  have hc := congrArg (fun A : PrivO n →L[ℂ] PrivO n => A v) (centT_compression hW hp hpos hT)
  simp only [comp_apply] at hc
  rw [comp_apply, comp_apply, centFlag, comp_apply, hrun, adjoint_comp, comp_apply,
    Run.E_adjoint_apply, hc]

/-- The block of the literal adjoint program is the adjoint of the centred filter. -/
theorem centred_block_adjoint (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) {d : ℕ} {p : Polynomial ℝ}
    (hp : p.natDegree ≤ d) (hpos : ∀ j, 0 ≤ p.coeff j) {T : ℕ} (hT : 2 * highHalf d ≤ T)
    (σ r : ℝ) (x : X) :
    ((centFlag D d p T)†) ∘L
        ((ChebyshevLinearSystem.runPhys D Ub sv T σ r (highHalf d)).adjoint.eval x ∘L
          centFlag D d p T) =
      (wpow (WwO D Ub sv σ r x) (-(lowHalf d : ℤ)) * polyOp p (WwO D Ub sv σ r x))† := by
  rw [MultiOracleCircuit.Program.eval_adjoint, star_eq_adjoint,
    ← centred_block D Ub hUb sv hp hpos hT σ r x, adjoint_comp, adjoint_comp, adjoint_adjoint,
    comp_assoc]

/-- **The centred circuit on the released physical oracle family**: for a real polynomial `p`
of degree at most `d` with nonnegative coefficients and `p(1) = 1`, and a register with
`2⌈d/2⌉ ≤ T`, the flag has normalisation one, the success block of the `⌈d/2⌉` signed steps is
`W^{-⌊d/2⌋} f(W)` and that of its literal adjoint the adjoint, on every input, and both programs
make `54 ⌈d/2⌉` matrix-oracle and `2 ⌈d/2⌉` source calls. -/
theorem centred_run (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) {d : ℕ} {p : Polynomial ℝ}
    (hp : p.natDegree ≤ d) (hpos : ∀ j, 0 ≤ p.coeff j) (h1 : p.eval 1 = 1) {T : ℕ}
    (hT : 2 * highHalf d ≤ T) (σ r : ℝ) :
    (centFlag D d p T)† ∘L centFlag D d p T = 1 ∧
      (∀ x, ((centFlag D d p T)†) ∘L
          ((ChebyshevLinearSystem.runPhys D Ub sv T σ r (highHalf d)).eval x ∘L
            centFlag D d p T) =
        wpow (WwO D Ub sv σ r x) (-(lowHalf d : ℤ)) * polyOp p (WwO D Ub sv σ r x)) ∧
      (∀ x, ((centFlag D d p T)†) ∘L
          ((ChebyshevLinearSystem.runPhys D Ub sv T σ r (highHalf d)).adjoint.eval x ∘L
            centFlag D d p T) =
        (wpow (WwO D Ub sv σ r x) (-(lowHalf d : ℤ)) * polyOp p (WwO D Ub sv σ r x))†) ∧
      (ChebyshevLinearSystem.runPhys D Ub sv T σ r (highHalf d)).cost wMat = highHalf d * 54 ∧
      (ChebyshevLinearSystem.runPhys D Ub sv T σ r (highHalf d)).cost wSrc = highHalf d * 2 ∧
      (ChebyshevLinearSystem.runPhys D Ub sv T σ r (highHalf d)).adjoint.cost wMat =
        highHalf d * 54 ∧
      (ChebyshevLinearSystem.runPhys D Ub sv T σ r (highHalf d)).adjoint.cost wSrc =
        highHalf d * 2 := by
  refine ⟨centFlag_isometry D hp hpos h1 hT, fun x => centred_block D Ub hUb sv hp hpos hT σ r x,
    fun x => centred_block_adjoint D Ub hUb sv hp hpos hT σ r x,
    ChebyshevLinearSystem.runPhys_cost_mat D Ub sv T σ r _,
    ChebyshevLinearSystem.runPhys_cost_src D Ub sv T σ r _, ?_, ?_⟩
  · rw [MultiOracleCircuit.Program.cost_adjoint, ChebyshevLinearSystem.runPhys_cost_mat]
  · rw [MultiOracleCircuit.Program.cost_adjoint, ChebyshevLinearSystem.runPhys_cost_src]

/-- The decoded test amplitude of the centred run is `W^{-m} f(W) J e`. -/
theorem centred_test_amplitude (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) {d : ℕ} {p : Polynomial ℝ}
    (hp : p.natDegree ≤ d) (hpos : ∀ j, 0 ≤ p.coeff j) {T : ℕ} (hT : 2 * highHalf d ≤ T)
    (σ r : ℝ) (x : X) :
    ((centFlag D d p T)†)
        ((ChebyshevLinearSystem.runPhys D Ub sv T σ r (highHalf d)).eval x (centSeedVec D d p T)) =
      (wpow (WwO D Ub sv σ r x) (-(lowHalf d : ℤ)) * polyOp p (WwO D Ub sv σ r x))
        ((JwO D).toContinuousLinearMap eVec) := by
  have h := congrArg (fun A : PrivO n →L[ℂ] PrivO n => A (JwO D eVec))
    (centred_block D Ub hUb sv hp hpos hT σ r x)
  simp only [comp_apply] at h
  rw [centSeedVec, show E D T (centSeedT d p T (JwO D eVec)) = centFlag D d p T (JwO D eVec) from rfl,
    LinearIsometry.coe_toContinuousLinearMap]
  exact h

/-- **`d = 0`**: no signed step, no oracle call, and the block is the identity. -/
theorem centred_run_zero (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) {p : Polynomial ℝ} (hp : p.natDegree ≤ 0)
    (hpos : ∀ j, 0 ≤ p.coeff j) (h1 : p.eval 1 = 1) {T : ℕ} (σ r : ℝ) (x : X) :
    highHalf 0 = 0 ∧
      (ChebyshevLinearSystem.runPhys D Ub sv T σ r (highHalf 0)).cost wMat = 0 ∧
      ((centFlag D 0 p T)†) ∘L
          ((ChebyshevLinearSystem.runPhys D Ub sv T σ r (highHalf 0)).eval x ∘L
            centFlag D 0 p T) = 1 := by
  have hT : 2 * highHalf 0 ≤ T := by rw [halves_zero.2]; omega
  refine ⟨halves_zero.2, by rw [ChebyshevLinearSystem.runPhys_cost_mat, halves_zero.2], ?_⟩
  rw [centred_block D Ub hUb sv hp hpos hT σ r x, halves_zero.1, Nat.cast_zero, neg_zero,
    wpow_zero', one_mul, polyOp_eq_sum p hp]
  have hc : p.coeff 0 = 1 := by
    rw [← h1, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp)]
    simp
  simp [hc]

/-- **The centred averaging filter** `W^{-⌊k(N-1)/2⌋} f_N(W)^k` with `⌈k(N-1)/2⌉` signed steps
of the released walk: normalisation-one flag, exact success block on every input, `54` matrix and
`2` source calls per signed step; its error relative to the fixed-space projector and its success
norm are those of `f_N(W)^k` (`centred_filter_error`). -/
theorem centred_averaging_run (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) {N : ℕ} (hN : 0 < N)
    (k : ℕ) {T : ℕ} (hT : 2 * highHalf (k * (N - 1)) ≤ T) (σ r : ℝ) :
    (centFlag D (k * (N - 1)) (avgPoly N ^ k) T)† ∘L centFlag D (k * (N - 1)) (avgPoly N ^ k) T
        = 1 ∧
      (∀ x, ((centFlag D (k * (N - 1)) (avgPoly N ^ k) T)†) ∘L
          ((ChebyshevLinearSystem.runPhys D Ub sv T σ r (highHalf (k * (N - 1)))).eval x ∘L
            centFlag D (k * (N - 1)) (avgPoly N ^ k) T) =
        wpow (WwO D Ub sv σ r x) (-(lowHalf (k * (N - 1)) : ℤ)) *
          UnitaryFilter.filter (WwO D Ub sv σ r x) N k) ∧
      (ChebyshevLinearSystem.runPhys D Ub sv T σ r (highHalf (k * (N - 1)))).cost wMat =
        highHalf (k * (N - 1)) * 54 ∧
      (ChebyshevLinearSystem.runPhys D Ub sv T σ r (highHalf (k * (N - 1)))).cost wSrc =
        highHalf (k * (N - 1)) * 2 := by
  have hp := filterPoly_natDegree_le N k
  have hpos : ∀ j, 0 ≤ (avgPoly N ^ k).coeff j := fun j => coef_nonneg N k j
  have h1 : (avgPoly N ^ k).eval 1 = 1 := by
    rw [Polynomial.eval_pow, avgPoly_eval_one N hN, one_pow]
  obtain ⟨hF, hB, -, hM, hS, -, -⟩ := centred_run D Ub hUb sv hp hpos h1 hT σ r
  refine ⟨hF, fun x => ?_, hM, hS⟩
  rw [hB x, polyOp_avg]

end Physical

/-! ### The query comparison of Remark `qls:rem:constants` -/

/-- The conservative averaging length `n_av = ⌈100π/ω⌉` at `ω = g/(512√s)`. -/
def nAv (s g : ℝ) : ℕ := ⌈51200 * Real.pi * Real.sqrt s / g⌉₊

/-- `q_av = n_av - 1`: the forward averaging schedule has one step fewer than its length. -/
theorem qAv_eq (s g : ℝ) : qAv s g = nAv s g - 1 := rfl

theorem nAv_pos {s g : ℝ} (hs : 0 < s) (hg0 : 0 < g) : 0 < nAv s g := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have := Real.pi_pos
  exact Nat.ceil_pos.mpr (by positivity)

/-- The prescribed signed-step budget with the conservative averaging schedules: every test of
stage `j` costs `q_av(σ_j)` steps and every final attempt the repeated schedule `k q_av(1/κ)`,
`k = ⌈log(1000/ε)/log 100⌉`, with the numbers of tests and attempts of `walkStepsF`. -/
def walkStepsAv (s : ℕ) (κ ε : ℝ) : ℕ :=
  (∑ q ∈ Finset.range (stagesM κ),
    5 * (reps κ ε (stagesM κ - q) * qAv (s : ℝ) (sig (stageOf κ (stagesM κ - q))))) +
    1000 * (kStages (ε / 1000) * qAv (s : ℝ) (1 / κ))

theorem one_le_sqrt_of_pos {s : ℕ} (hs : 0 < s) : (1 : ℝ) ≤ Real.sqrt s := by
  rw [Real.one_le_sqrt]
  exact_mod_cast hs

/-- The test comparison in `ℕ`: `1400 d^fin_σ(1/100) < q_av`. -/
theorem test_ratio_nat {s : ℕ} (hs : 0 < s) {g : ℝ} (hg0 : 0 < g) (hg : g ≤ Real.sqrt s) :
    1400 * finDegree (s : ℝ) g (1 / 100) < qAv (s : ℝ) g := by
  have h := averaging_ratio (s := (s : ℝ)) (by exact_mod_cast hs) hg0 hg
  exact_mod_cast h

/-- The repeated-stage comparison in `ℕ`: `1400 d^fin_σ(δ) < k q_av`. -/
theorem final_ratio_nat {s : ℕ} (hs : 0 < s) {g δ : ℝ} (hg0 : 0 < g) (hg : g ≤ Real.sqrt s)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 100) :
    1400 * finDegree (s : ℝ) g δ < kStages δ * qAv (s : ℝ) g := by
  have h := averaging_ratio_final (s := (s : ℝ)) (by exact_mod_cast hs) hg0 hg hδ0 hδ1
  exact_mod_cast h

/-- **The prescribed budgets**, holding the numbers of tests and attempts fixed:
`1400 walkStepsF < walkStepsAv`, term by term. -/
theorem walkSteps_ratio (s : ℕ) (hs : 0 < s) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 10) : 1400 * walkStepsF s κ ε < walkStepsAv s κ ε := by
  have hsq := one_le_sqrt_of_pos hs
  have hstage : ∀ q, 1400 * (5 * (reps κ ε (stagesM κ - q) * dTestF s (stageOf κ (stagesM κ - q))))
      ≤ 5 * (reps κ ε (stagesM κ - q) * qAv (s : ℝ) (sig (stageOf κ (stagesM κ - q)))) := by
    intro q
    have h := test_ratio_nat hs (sig_pos (stageOf κ (stagesM κ - q)))
      ((sig_le_one _).trans hsq)
    rw [dTestF_eq]
    have h' : 1400 * finDegree (s : ℝ) (sig (stageOf κ (stagesM κ - q))) (1 / 100) ≤
        qAv (s : ℝ) (sig (stageOf κ (stagesM κ - q))) := h.le
    calc 1400 * (5 * (reps κ ε (stagesM κ - q) *
            finDegree (s : ℝ) (sig (stageOf κ (stagesM κ - q))) (1 / 100)))
        = 5 * (reps κ ε (stagesM κ - q) *
            (1400 * finDegree (s : ℝ) (sig (stageOf κ (stagesM κ - q))) (1 / 100))) := by ring
      _ ≤ 5 * (reps κ ε (stagesM κ - q) * qAv (s : ℝ) (sig (stageOf κ (stagesM κ - q)))) :=
          Nat.mul_le_mul_left 5 (Nat.mul_le_mul_left _ h')
  have hκ0 : 0 < 1 / κ := by positivity
  have hκs : 1 / κ ≤ Real.sqrt s := by
    have : 1 / κ ≤ 1 := by rw [div_le_one (by linarith)]; exact hκ
    linarith
  have hfin := final_ratio_nat hs hκ0 hκs (by positivity : (0 : ℝ) < ε / 1000)
    (by linarith : ε / 1000 ≤ 1 / 100)
  rw [← dFinF_eq] at hfin
  unfold walkStepsF walkStepsAv
  rw [Nat.mul_add, Finset.mul_sum]
  have hsum := Finset.sum_le_sum (fun q (_ : q ∈ Finset.range (stagesM κ)) => hstage q)
  omega

/-- The centred single test in `ℕ` (derived here; the manuscript states only the forward
comparison): `700 d^fin_σ(1/100) < ⌈q_av/2⌉`. -/
theorem centred_test_ratio {s : ℕ} (hs : 0 < s) {g : ℝ} (hg0 : 0 < g) (hg : g ≤ Real.sqrt s) :
    700 * finDegree (s : ℝ) g (1 / 100) < highHalf (qAv (s : ℝ) g) := by
  have h := test_ratio_nat hs hg0 hg
  have hb := (highHalf_bounds (qAv (s : ℝ) g)).1
  omega

/-- The centred repeated stage in `ℕ` (derived here, as `centred_test_ratio`): for
`0 < δ ≤ 1/100` and `k = ⌈log(1/δ)/log 100⌉`, `700 d^fin_σ(δ) < ⌈k q_av/2⌉`, the signed steps of
the centred run of the repeated averaging filter `f_{n_av}(W)^k` (`averaging_schedules`), and
`700 d^fin_σ(δ) < k ⌈q_av/2⌉`, the signed steps of `k` separately centred stages. -/
theorem centred_final_ratio {s : ℕ} (hs : 0 < s) {g δ : ℝ} (hg0 : 0 < g) (hg : g ≤ Real.sqrt s)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 100) :
    700 * finDegree (s : ℝ) g δ < highHalf (kStages δ * qAv (s : ℝ) g) ∧
      700 * finDegree (s : ℝ) g δ < kStages δ * highHalf (qAv (s : ℝ) g) := by
  have h := final_ratio_nat hs hg0 hg hδ0 hδ1
  have hb := (highHalf_bounds (kStages δ * qAv (s : ℝ) g)).1
  have hq := Nat.mul_le_mul_left (kStages δ) (highHalf_bounds (qAv (s : ℝ) g)).1
  have he : kStages δ * (2 * highHalf (qAv (s : ℝ) g)) =
      2 * (kStages δ * highHalf (qAv (s : ℝ) g)) := by ring
  constructor <;> omega

/-- **The prescribed matrix-oracle and source budgets**: `54` and `2` calls per step on both
sides, so `1400 · 54 walkStepsF < 54 walkStepsAv` and `1400 · 2 walkStepsF < 2 walkStepsAv`. -/
theorem budget_query_comparison (s : ℕ) (hs : 0 < s) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 10) :
    1400 * (walkStepsF s κ ε * 54) < walkStepsAv s κ ε * 54 ∧
      1400 * (walkStepsF s κ ε * 2) < walkStepsAv s κ ε * 2 := by
  have h := walkSteps_ratio s hs κ ε hκ hε hε1
  constructor <;> omega

section Comparison

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- **Equal per-step costs**: `t` forward steps (`SparseLinearSystems.Run.runPhys`) and `t`
signed steps (`ChebyshevLinearSystem.runPhys`) of the released walk make the same calls, `54 t`
matrix-oracle and `2 t` source calls. -/
theorem step_costs (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (T : ℕ) (σ r σ' r' : ℝ) (t : ℕ) :
    (Run.runPhys D Ub sv T σ r t).cost wMat = t * 54 ∧
      (ChebyshevLinearSystem.runPhys D Ub sv T σ' r' t).cost wMat = t * 54 ∧
      (Run.runPhys D Ub sv T σ r t).cost wSrc = t * 2 ∧
      (ChebyshevLinearSystem.runPhys D Ub sv T σ' r' t).cost wSrc = t * 2 :=
  ⟨Run.runPhys_cost_mat D Ub sv T σ r t, ChebyshevLinearSystem.runPhys_cost_mat D Ub sv T σ' r' t,
    Run.runPhys_cost_src D Ub sv T σ r t, ChebyshevLinearSystem.runPhys_cost_src D Ub sv T σ' r' t⟩

/-- **Single test** (Remark `qls:rem:constants`): the actual Chebyshev run of
`d^fin_σ(1/100)` signed steps makes fewer than `1/1400` of the matrix-oracle and of the source
calls of the actual forward run of `q_av` steps. -/
theorem test_query_comparison (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (T : ℕ) (σ r σ' r' : ℝ) {g : ℝ} (hg0 : 0 < g)
    (hg : g ≤ Real.sqrt s) :
    1400 * (ChebyshevLinearSystem.runPhys D Ub sv T σ r
        (finDegree (s : ℝ) g (1 / 100))).cost wMat <
        (Run.runPhys D Ub sv T σ' r' (qAv (s : ℝ) g)).cost wMat ∧
      1400 * (ChebyshevLinearSystem.runPhys D Ub sv T σ r
        (finDegree (s : ℝ) g (1 / 100))).cost wSrc <
        (Run.runPhys D Ub sv T σ' r' (qAv (s : ℝ) g)).cost wSrc := by
  have h := test_ratio_nat D.slots_pos hg0 hg
  rw [ChebyshevLinearSystem.runPhys_cost_mat, ChebyshevLinearSystem.runPhys_cost_src,
    Run.runPhys_cost_mat, Run.runPhys_cost_src]
  constructor <;> omega

/-- **Repeated stage** (Remark `qls:rem:constants`): for `0 < δ ≤ 1/100` and
`k = ⌈log(1/δ)/log 100⌉`, the actual Chebyshev run of `d^fin_σ(δ)` signed steps makes fewer than
`1/1400` of the calls of the actual forward run of `k q_av` steps (the repeated averaging
schedule). -/
theorem final_query_comparison (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (T : ℕ) (σ r σ' r' : ℝ) {g δ : ℝ} (hg0 : 0 < g)
    (hg : g ≤ Real.sqrt s) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 100) :
    1400 * (ChebyshevLinearSystem.runPhys D Ub sv T σ r (finDegree (s : ℝ) g δ)).cost wMat <
        (Run.runPhys D Ub sv T σ' r' (kStages δ * qAv (s : ℝ) g)).cost wMat ∧
      1400 * (ChebyshevLinearSystem.runPhys D Ub sv T σ r (finDegree (s : ℝ) g δ)).cost wSrc <
        (Run.runPhys D Ub sv T σ' r' (kStages δ * qAv (s : ℝ) g)).cost wSrc := by
  have h := final_ratio_nat D.slots_pos hg0 hg hδ0 hδ1
  rw [ChebyshevLinearSystem.runPhys_cost_mat, ChebyshevLinearSystem.runPhys_cost_src,
    Run.runPhys_cost_mat, Run.runPhys_cost_src]
  constructor <;> omega

/-- **The three schedules of one filter on the released walk**, for the repeated averaging filter
`f_{n_av}(W)^k` (`k = 1`: a single test) on a register with `k q_av + 1 ≤ T`, and any
`b ∈ (-1, 1)` and Chebyshev degree `d` with `2d ≤ T`:

* the forward averaging run of `k q_av` steps has decoded test amplitude `f_{n_av}(W)^k J e`;
* the centred averaging run of `⌈k q_av/2⌉` signed steps has
  `W^{-⌊k q_av/2⌋} f_{n_av}(W)^k J e`;
* the Chebyshev run of `d` signed steps has `F_{b,d}(W) J e`;

and they make `54 k q_av`, `54 ⌈k q_av/2⌉` and `54 d` matrix-oracle calls (`2 k q_av`,
`2 ⌈k q_av/2⌉` and `2 d` source calls). -/
theorem averaging_schedules (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) {T : ℕ} (σ r : ℝ)
    {g : ℝ} (hg0 : 0 < g) (k : ℕ) (hT : k * qAv (s : ℝ) g + 1 ≤ T) {b : ℝ}
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1) {d : ℕ} (hd : 2 * d ≤ T) (x : X) :
    ((Run.testFlag D (nAv (s : ℝ) g) k T)†)
        ((Run.runPhys D Ub sv T σ r (k * qAv (s : ℝ) g)).eval x
          (Run.seedVec D (nAv (s : ℝ) g) k T)) =
        UnitaryFilter.filter (WwO D Ub sv σ r x) (nAv (s : ℝ) g) k (JwO D eVec) ∧
      ((centFlag D (k * qAv (s : ℝ) g) (avgPoly (nAv (s : ℝ) g) ^ k) T)†)
          ((ChebyshevLinearSystem.runPhys D Ub sv T σ r (highHalf (k * qAv (s : ℝ) g))).eval x
            (centSeedVec D (k * qAv (s : ℝ) g) (avgPoly (nAv (s : ℝ) g) ^ k) T)) =
        (wpow (WwO D Ub sv σ r x) (-(lowHalf (k * qAv (s : ℝ) g) : ℤ)) *
            UnitaryFilter.filter (WwO D Ub sv σ r x) (nAv (s : ℝ) g) k)
          ((JwO D).toContinuousLinearMap eVec) ∧
      ((ChebyshevLinearSystem.testFlag D b T d)†)
          ((ChebyshevLinearSystem.runPhys D Ub sv T σ r d).eval x
            (ChebyshevLinearSystem.seedVec D b T d)) =
        filterOp (WwO D Ub sv σ r x) b d ((JwO D).toContinuousLinearMap eVec) ∧
      (Run.runPhys D Ub sv T σ r (k * qAv (s : ℝ) g)).cost wMat = k * qAv (s : ℝ) g * 54 ∧
      (ChebyshevLinearSystem.runPhys D Ub sv T σ r (highHalf (k * qAv (s : ℝ) g))).cost wMat =
        highHalf (k * qAv (s : ℝ) g) * 54 ∧
      (ChebyshevLinearSystem.runPhys D Ub sv T σ r d).cost wMat = d * 54 ∧
      (Run.runPhys D Ub sv T σ r (k * qAv (s : ℝ) g)).cost wSrc = k * qAv (s : ℝ) g * 2 ∧
      (ChebyshevLinearSystem.runPhys D Ub sv T σ r (highHalf (k * qAv (s : ℝ) g))).cost wSrc =
        highHalf (k * qAv (s : ℝ) g) * 2 ∧
      (ChebyshevLinearSystem.runPhys D Ub sv T σ r d).cost wSrc = d * 2 := by
  have hs : (0 : ℝ) < s := by exact_mod_cast D.slots_pos
  have hN := nAv_pos hs hg0
  have hdeg : k * (nAv (s : ℝ) g - 1) = k * qAv (s : ℝ) g := by rw [qAv_eq]
  have hc := (highHalf_bounds (k * qAv (s : ℝ) g)).2.1
  have hTc : 2 * highHalf (k * (nAv (s : ℝ) g - 1)) ≤ T := by rw [hdeg]; omega
  refine ⟨Run.test_amplitudeO D Ub hUb sv (nAv (s : ℝ) g) k T (k * qAv (s : ℝ) g)
      (le_of_eq hdeg) (by omega) σ r x, ?_,
    ChebyshevLinearSystem.test_amplitude D Ub hUb sv hb hd σ r x,
    Run.runPhys_cost_mat D Ub sv T σ r _, ChebyshevLinearSystem.runPhys_cost_mat D Ub sv T σ r _,
    ChebyshevLinearSystem.runPhys_cost_mat D Ub sv T σ r _,
    Run.runPhys_cost_src D Ub sv T σ r _, ChebyshevLinearSystem.runPhys_cost_src D Ub sv T σ r _,
    ChebyshevLinearSystem.runPhys_cost_src D Ub sv T σ r _⟩
  have hp : (avgPoly (nAv (s : ℝ) g) ^ k).natDegree ≤ k * qAv (s : ℝ) g :=
    (filterPoly_natDegree_le _ k).trans (le_of_eq hdeg)
  have hpos : ∀ j, 0 ≤ (avgPoly (nAv (s : ℝ) g) ^ k).coeff j := fun j => coef_nonneg _ k j
  rw [centred_test_amplitude D Ub hUb sv hp hpos (by omega) σ r x, polyOp_avg]

end Comparison

end

end ChebyshevLinearSystemFinite.CentredAveraging
