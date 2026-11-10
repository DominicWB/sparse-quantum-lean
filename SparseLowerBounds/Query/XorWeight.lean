import SparseLowerBounds.Helpers.XorWeight.Matrix

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The XOR weight and Lemma `qlsl:lem:xor`

On one hidden-position register `ℂ^m`, with `u = m^{-1/2} Σ_b |b⟩` and
`P_u = |u⟩⟨u|`, the manuscript (proof of Lemma `qlsl:lem:xor`) uses the weight
`w = 2I - P_u`, whose inverse is `(I + P_u)/2`. It is Hermitian and fixes `u`.
The adversary constants are (proof of Lemma `qlsl:lem:xor`)

* `‖w D_a w⁻¹‖ ≤ 1 + 2/√m` for every position `a`, from
  `‖[P_u, D_a]‖ = 2√(m-1)/m ≤ 2/√m` and `‖w⁻¹‖ = 1`;
* `‖w⁻¹ Z w⁻¹‖ ≤ 1/2` for even `m`, since `v = Z u ⊥ u` and `w⁻¹ Z w⁻¹`
  is `[[0, 1/2], [1/2, 0]]` on `span {u, v}` and `Z/4` on its complement
  (eq. `qlsl:eq:paritynorm`).

With the generic adversary (`Adversary.program_correlation_le`) these give
Lemma `qlsl:lem:xor` in observable form (`xor_lemma`), also
for classical mixtures of programs (`xor_lemma_mixture`).
-/

namespace SparseLowerBounds.XorWeight

noncomputable section
open SparseHamiltonian OracleCircuit Adversary
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

/-- `P_u = |u⟩⟨u|` for the uniform unit vector `u`: every entry is `1/m`. -/
def Pu (m : ℕ) : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun _ _ => (m : ℂ)⁻¹

/-- The XOR weight `w = 2I - P_u` (proof of Lemma `qlsl:lem:xor`). -/
def w (m : ℕ) : Matrix (Fin m) (Fin m) ℂ := (2 : ℂ) • 1 - Pu m

/-- The explicit inverse `(I + P_u)/2` of the weight. -/
def wInv (m : ℕ) : Matrix (Fin m) (Fin m) ℂ := (2 : ℂ)⁻¹ • (1 + Pu m)

theorem isHermitian_w (m : ℕ) : (w m).IsHermitian := by
  have hP : (Pu m)ᴴ = Pu m := Helpers.XorWeight.star_P m
  unfold Matrix.IsHermitian
  rw [w, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hP]
  simp

theorem w_mul_wInv (m : ℕ) : w m * wInv m = 1 :=
  Helpers.XorWeight.two_sub_mul_inv (Pu m) (Helpers.XorWeight.P_mul_P m)

theorem wInv_mul_w (m : ℕ) : wInv m * w m = 1 :=
  Helpers.XorWeight.inv_mul_two_sub (Pu m) (Helpers.XorWeight.P_mul_P m)

theorem isUnit_w (m : ℕ) : IsUnit (w m) :=
  ⟨⟨w m, wInv m, w_mul_wInv m, wInv_mul_w m⟩, rfl⟩

theorem inv_w (m : ℕ) : (w m)⁻¹ = wInv m :=
  Matrix.inv_eq_right_inv (w_mul_wInv m)

/-- `w u = u`: every row of `w` sums to one. -/
theorem w_mulVec_one (m : ℕ) : w m *ᵥ (fun _ => 1) = fun _ => 1 := by
  have hP : Pu m *ᵥ (fun _ => 1) = fun _ => 1 := Helpers.XorWeight.P_mulVec_one m
  rw [w, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hP]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  norm_num

/-- `‖[P_u, D_a]‖ ≤ 2/√m` (the exact value is `2√(m-1)/m`, proof of Lemma `qlsl:lem:xor`). -/
theorem norm_commutator_le {m : ℕ} (a : Fin m) :
    ‖Pu m * reflect a - reflect a * Pu m‖ ≤ 2 / Real.sqrt m :=
  Helpers.XorWeight.norm_commutator_le a

/-- `‖w⁻¹‖ ≤ 1`. -/
theorem norm_wInv_le (m : ℕ) : ‖wInv m‖ ≤ 1 :=
  Helpers.XorWeight.norm_wInv_le m

/-- **Per-query weight growth** (proof of Lemma `qlsl:lem:xor`): `‖w D_a w⁻¹‖ ≤ 1 + 2/√m`.
No hypothesis on `m` is needed: for `m = 0` there is no position `a`. -/
theorem norm_conj_D_le {m : ℕ} (a : Fin m) :
    ‖w m * reflect a * (w m)⁻¹‖ ≤ 1 + 2 / Real.sqrt m := by
  rw [inv_w]
  have hkey : w m * reflect a * wInv m =
      reflect a + (reflect a * Pu m - Pu m * reflect a) * wInv m := by
    have h1 : w m * reflect a = reflect a * w m + (reflect a * Pu m - Pu m * reflect a) := by
      simp only [w, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      abel
    rw [h1, add_mul, mul_assoc, w_mul_wInv, mul_one]
  have hC : ‖reflect a * Pu m - Pu m * reflect a‖ ≤ 2 / Real.sqrt m := by
    rw [← norm_neg, neg_sub]
    exact norm_commutator_le a
  have hD : ‖reflect a‖ ≤ 1 := Helpers.XorWeight.norm_D_le a
  rw [hkey]
  calc ‖reflect a + (reflect a * Pu m - Pu m * reflect a) * wInv m‖
      ≤ ‖reflect a‖ + ‖reflect a * Pu m - Pu m * reflect a‖ * ‖wInv m‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_mul_le _ _))
    _ ≤ 1 + 2 / Real.sqrt m * 1 :=
        add_le_add hD (mul_le_mul hC (norm_wInv_le m) (norm_nonneg _) (by positivity))
    _ = 1 + 2 / Real.sqrt m := by ring

/-- **Eq. `qlsl:eq:paritynorm`**: `‖w⁻¹ Z w⁻¹‖ ≤ 1/2` for even `m`
(equality for `m ≥ 2`). Evenness is necessary: for `m = 1` the norm is `1`. -/
theorem norm_conj_Z_le {m : ℕ} (hm : Even m) : ‖(w m)⁻¹ * parityZ m * (w m)⁻¹‖ ≤ 1 / 2 := by
  rw [inv_w]
  exact Helpers.XorWeight.norm_conj_Z_le hm

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `(1 + 2/√m)^{2t} ≤ e^{4t/√m}`. -/
theorem lam_pow_le (m t : ℕ) :
    (1 + 2 / Real.sqrt m) ^ (2 * t) ≤ Real.exp (4 * t / Real.sqrt m) := by
  calc (1 + 2 / Real.sqrt m) ^ (2 * t) ≤ Real.exp (2 / Real.sqrt m) ^ (2 * t) := by
        gcongr
        linarith [Real.add_one_le_exp (2 / Real.sqrt m)]
    _ = Real.exp (4 * t / Real.sqrt m) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

/-- The final arithmetic of eq. `qlsl:eq:xor`. -/
theorem final_of_bound {n m t : ℕ} (hm0 : 0 < m) {β : ℝ} (hβ : 0 < β)
    (h : β ≤ ((2 : ℝ) ^ n)⁻¹ * Real.exp (4 * t / Real.sqrt m)) :
    β ≤ ((2 : ℝ) ^ n)⁻¹ * Real.exp (4 * t / Real.sqrt m) ∧
      Real.sqrt m / 4 * (n * Real.log 2 + Real.log β) ≤ t := by
  refine ⟨h, ?_⟩
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm0)
  have h1 := Real.log_le_log hβ h
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_inv, Real.log_pow,
    Real.log_exp] at h1
  have h2 : n * Real.log 2 + Real.log β ≤ 4 * t / Real.sqrt m := by linarith
  calc Real.sqrt m / 4 * (n * Real.log 2 + Real.log β)
      ≤ Real.sqrt m / 4 * (4 * t / Real.sqrt m) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = t := by field_simp

/-- The mixture bound `β ≤ 2^{-n} e^{4t/√m}` (the common core of `xor_lemma` and
`xor_lemma_mixture`). -/
theorem mixture_bound {n m : ℕ} (hm : Even m) (hm0 : 0 < m)
    (P : ProjFamily K (Fin n × Fin m)) {k : ℕ} (q : Fin k → Program (oneHotOracle P))
    (prob : Fin k → ℝ) (hprob : ∀ c, 0 ≤ prob c) (hprob1 : ∑ c, prob c = 1)
    {t : ℕ} (ht : ∀ c, (q c).count ≤ t)
    (φ₀ : K) (hφ₀ : ‖φ₀‖ ≤ 1) (M : K →L[ℂ] K) (hM : ‖M‖ ≤ 1) {β : ℝ}
    (hcorr : ∀ j, β ≤ parity j * ∑ c, prob c * (⟪(q c).eval j φ₀, M ((q c).eval j φ₀)⟫_ℂ).re) :
    β ≤ ((2 : ℝ) ^ n)⁻¹ * Real.exp (4 * t / Real.sqrt m) := by
  have hlam1 : 1 ≤ 1 + 2 / Real.sqrt m := by
    have : 0 ≤ 2 / Real.sqrt m := by positivity
    linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmn : (0 : ℝ) < (m : ℝ) ^ n := pow_pos hmR n
  set B : ℝ := ((2 : ℝ) ^ n)⁻¹ * (1 + 2 / Real.sqrt m) ^ (2 * t) with hB
  have hprog : ∀ c, ‖∑ j, (parity j : ℂ) * ⟪(q c).eval j φ₀, M ((q c).eval j φ₀)⟫_ℂ‖ ≤
      (m : ℝ) ^ n * B := by
    intro c
    have key := program_correlation_le P (w m) (isHermitian_w m) (isUnit_w m) (w_mulVec_one m)
      hlam1 (fun a => norm_conj_D_le a) (q c) φ₀ hφ₀ M hM
    have hZ : ‖(w m)⁻¹ * parityZ m * (w m)⁻¹‖ ^ n ≤ (1 / 2) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_conj_Z_le hm) n
    have hL : (1 + 2 / Real.sqrt m) ^ (2 * (q c).count) ≤ (1 + 2 / Real.sqrt m) ^ (2 * t) :=
      pow_le_pow_right₀ hlam1 (by have := ht c; omega)
    have hbound : ‖((m : ℂ) ^ n)⁻¹ *
        ∑ j, (parity j : ℂ) * ⟪(q c).eval j φ₀, M ((q c).eval j φ₀)⟫_ℂ‖ ≤ B := by
      calc _ ≤ _ := key
        _ ≤ (1 / 2) ^ n * (1 + 2 / Real.sqrt m) ^ (2 * t) :=
          mul_le_mul hZ hL (by positivity) (by positivity)
        _ = B := by rw [hB, one_div, inv_pow]
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast] at hbound
    have := mul_le_mul_of_nonneg_left hbound hmn.le
    rwa [← mul_assoc, mul_inv_cancel₀ hmn.ne', one_mul] at this
  have hre : ∀ c, ∑ j, parity j * (⟪(q c).eval j φ₀, M ((q c).eval j φ₀)⟫_ℂ).re ≤
      (m : ℝ) ^ n * B := by
    intro c
    refine le_trans (le_of_eq ?_) ((Complex.re_le_norm _).trans (hprog c))
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.re_ofReal_mul]
  have hswap : ∑ j, parity j * ∑ c, prob c * (⟪(q c).eval j φ₀, M ((q c).eval j φ₀)⟫_ℂ).re =
      ∑ c, prob c * ∑ j, parity j * (⟪(q c).eval j φ₀, M ((q c).eval j φ₀)⟫_ℂ).re := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => by ring
  have hmix : ∑ c, prob c * ∑ j, parity j * (⟪(q c).eval j φ₀, M ((q c).eval j φ₀)⟫_ℂ).re ≤
      (m : ℝ) ^ n * B := by
    calc _ ≤ ∑ c, prob c * ((m : ℝ) ^ n * B) :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hre c) (hprob c)
      _ = (m : ℝ) ^ n * B := by rw [← Finset.sum_mul, hprob1, one_mul]
  have hsum : (m : ℝ) ^ n * β ≤
      ∑ j, parity j * ∑ c, prob c * (⟪(q c).eval j φ₀, M ((q c).eval j φ₀)⟫_ℂ).re := by
    calc (m : ℝ) ^ n * β = ∑ _j : Fin n → Fin m, β := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ _ := Finset.sum_le_sum fun j _ => hcorr j
  have hβB : β ≤ B := le_of_mul_le_mul_left (hsum.trans (hswap ▸ hmix)) hmn
  calc β ≤ B := hβB
    _ ≤ ((2 : ℝ) ^ n)⁻¹ * Real.exp (4 * t / Real.sqrt m) := by
        rw [hB]
        gcongr
        exact lam_pow_le m t

/-- **Lemma `qlsl:lem:xor`** (Lemma `qlsl:lem:xor`), observable form. Let `m` be
even and positive. A Boolean one-hot program `q` with at most `t` queries
(inverse queries included), run on an input-independent seed `φ₀`,
`‖φ₀‖ ≤ 1`, and measured with an output observable `M`, `‖M‖ ≤ 1`, whose
parity correlation is at least `β > 0` on **every** hidden input `j`
(success probability `(1 + β)/2` for the parity `F`, with `M` the `±1`
output observable) satisfies `β ≤ 2^{-n} e^{4t/√m}` and
`t ≥ (√m/4)(n ln 2 + ln β)` (eq. `qlsl:eq:xor`).

Hypotheses are as weak as the proof allows: `M` need not be self-adjoint
(only `Re ⟪φ, M φ⟫` enters, and `Re` of an expectation of `M` is that of
the Hermitian contraction `(M + M†)/2`), `β ≤ 1` is implied, and `0 < m`
excludes the vacuous case of no hidden inputs. -/
theorem xor_lemma {n m : ℕ} (hm : Even m) (hm0 : 0 < m) (P : ProjFamily K (Fin n × Fin m))
    (q : Program (oneHotOracle P)) {t : ℕ} (ht : q.count ≤ t)
    (φ₀ : K) (hφ₀ : ‖φ₀‖ ≤ 1) (M : K →L[ℂ] K) (hM : ‖M‖ ≤ 1) {β : ℝ} (hβ : 0 < β)
    (hcorr : ∀ j, β ≤ parity j * (⟪q.eval j φ₀, M (q.eval j φ₀)⟫_ℂ).re) :
    β ≤ ((2 : ℝ) ^ n)⁻¹ * Real.exp (4 * t / Real.sqrt m) ∧
      Real.sqrt m / 4 * (n * Real.log 2 + Real.log β) ≤ t := by
  refine final_of_bound hm0 hβ ?_
  refine mixture_bound hm hm0 P (fun _ : Fin 1 => q) (fun _ => 1) (fun _ => zero_le_one)
    (by simp) (fun _ => ht) φ₀ hφ₀ M hM (fun j => ?_)
  simpa using hcorr j

/-- **Lemma `qlsl:lem:xor` for classical mixtures of programs** (Lemma `qlsl:lem:xor`; the
purification remark of the proof of Lemma `qlsl:lem:xor`). A finite family of Boolean one-hot
programs `q c`, each with at most `t` queries, chosen with probabilities `prob c` (`prob ≥ 0`,
`Σ prob = 1`), run on a common seed and measured with a common observable, whose **mixture** parity
correlation is at least `β > 0` on every hidden input obeys the same bounds as `xor_lemma`. The
correlation is linear in the output state, so this follows from `Adversary.program_correlation_le`
branch by branch.

This is the form needed for the release's repeat-until-success trials: an
`ODERepeatProtocol.TrialFamily` with `choices > 1` picks one of several
circuits uniformly at random, which is a classical mixture and, without
controlled queries, not one `MultiOracleCircuit.Program` of the same count.
`xor_lemma` covers a trial family directly only when `choices = 1`. -/
theorem xor_lemma_mixture {n m : ℕ} (hm : Even m) (hm0 : 0 < m)
    (P : ProjFamily K (Fin n × Fin m)) {k : ℕ} (q : Fin k → Program (oneHotOracle P))
    (prob : Fin k → ℝ) (hprob : ∀ c, 0 ≤ prob c) (hprob1 : ∑ c, prob c = 1)
    {t : ℕ} (ht : ∀ c, (q c).count ≤ t)
    (φ₀ : K) (hφ₀ : ‖φ₀‖ ≤ 1) (M : K →L[ℂ] K) (hM : ‖M‖ ≤ 1) {β : ℝ} (hβ : 0 < β)
    (hcorr : ∀ j, β ≤ parity j * ∑ c, prob c * (⟪(q c).eval j φ₀, M ((q c).eval j φ₀)⟫_ℂ).re) :
    β ≤ ((2 : ℝ) ^ n)⁻¹ * Real.exp (4 * t / Real.sqrt m) ∧
      Real.sqrt m / 4 * (n * Real.log 2 + Real.log β) ≤ t :=
  final_of_bound hm0 hβ (mixture_bound hm hm0 P q prob hprob hprob1 ht φ₀ hφ₀ M hM hcorr)

end

end SparseLowerBounds.XorWeight
end
