import SparseLowerBounds.Helpers.SearchWeight.Arith

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The search weight and Lemma `hsl:lem:search`

Manuscript: Lemma `hsl:lem:search` and its proof. On one hidden-position register `ℂ^m` (`m` even)
let `u = m^{-1/2} Σ_b |b⟩`, `Z |b⟩ = (-1)^b |b⟩`, `v = Z u` and
`R = I - P_u - P_v`. For a real `a ≥ 1` the weight is (proof of Lemma `hsl:lem:search`)

  `w = P_u + a² P_v + a R`,  `w⁻¹ = P_u + a⁻² P_v + a⁻¹ R`.

It is Hermitian, fixes `u` (row sums one), and (proof of Lemma `hsl:lem:search`)

* `w⁻¹ Z w⁻¹ = a⁻² Z`, so `‖w⁻¹ Z w⁻¹‖ ≤ a⁻²` (`conj_Z`, `norm_conj_Z_le`);
* `‖w D_b w⁻¹‖ ≤ 1 + 4√2 a/√m + 4a²/m ≤ 1 + 12 a/√m` for `1 ≤ a ≤ √m`
  (`norm_conj_D_le`).

Evenness of `m` gives `⟪u, v⟫ = 0`, which all three facts use.

With the generic adversary (`Adversary.program_correlation_le`) and the choice
`a = 2 β₀^{-1/(2n)}` this proves Lemma `hsl:lem:search` (eq.
`hsl:eq:searchbound`) for the **average** correlation over uniformly random
hidden positions (`search_lemma`), and its worst-case corollary
(`search_lemma_worst`). `β₀ ≤ 1` is not assumed: it follows from `‖M‖ ≤ 1`,
`‖φ₀‖ ≤ 1` and unitarity of the program.

## Proof route (helper statements)

1. *Projector algebra.* `P_u`, `P_v`, `R` are pairwise orthogonal idempotents
   summing to `1` (`Pu_mul_Pv`, …, `Rest_mul_Rest`; evenness enters through
   `Σ_b (-1)^b = 0`), so `w`, `wInv` multiply coefficientwise
   (`orth_combo_mul`). `Z P_u Z = P_v`, `Z P_v Z = P_u`, `Z R = R Z`
   (`parityZ_mul_Pu_mul_parityZ`, …) give `conj_Z`.
2. *The query block* (proof of Lemma `hsl:lem:search`). With `e = (w/a - I)|b⟩` and
   `f = (a w⁻¹ - I)|b⟩` (`eVec`, `fVec`): `w D_b w⁻¹ = D_b - 2(e⟨b| + |b⟩f† + e f†)`
   (`conj_D_eq`); `e = (a⁻¹-1) P_u|b⟩ + (a-1) P_v|b⟩` (`eVec_eq`), so
   `‖e‖, ‖f‖ ≤ √2 a/√m` (`norm_e_le`, `norm_f_le`), whence the display bound
   (`norm_conj_D_le_fine`) and `1 + 12a/√m` (`fine_le_twelve`).
3. *Final arithmetic* (proof of Lemma `hsl:lem:search`). `(1 + 12a/√m)^{2q} ≤ e^{24aq/√m}`
   (`lam_pow_le`); the average correlation is at most `a^{-2n} e^{24aq/√m}`
   (`avg_corr_le`) and at most `1` (`avg_corr_le_one`); with
   `a = searchA n β₀ = 2β₀^{-1/(2n)}` (`one_le_searchA`, `searchA_le_sqrt`)
   the logarithm gives eq. `hsl:eq:searchbound` (`search_final`).

Vector norms are Euclidean: `‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin m))‖`
(the default norm on `Fin m → ℂ` is the sup norm).
-/

namespace SparseLowerBounds.SearchWeight

noncomputable section
open SparseHamiltonian OracleCircuit Adversary
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

/-- `P_v = |v⟩⟨v|` for the alternating unit vector `v = Z u`: entries `(-1)^{a+b}/m`. -/
def Pv (m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun a b => (-1 : ℂ) ^ ((a : ℕ) + b) / m

/-- `R = I - P_u - P_v`. -/
def Rest (m : ℕ) : Matrix (Fin m) (Fin m) ℂ := 1 - XorWeight.Pu m - Pv m

/-- The search weight `w = P_u + a² P_v + a R` (proof of Lemma `hsl:lem:search`). -/
def w (m : ℕ) (a : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  XorWeight.Pu m + ((a : ℂ) ^ 2) • Pv m + (a : ℂ) • Rest m

/-- The explicit inverse `P_u + a⁻² P_v + a⁻¹ R`. -/
def wInv (m : ℕ) (a : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  XorWeight.Pu m + ((a : ℂ) ^ 2)⁻¹ • Pv m + (a : ℂ)⁻¹ • Rest m

/-- The vector `e = (w/a - I)|b⟩` of the proof of Lemma `hsl:lem:search`. -/
def eVec (m : ℕ) (a : ℝ) (b : Fin m) : Fin m → ℂ :=
  ((a : ℂ)⁻¹ • w m a - 1) *ᵥ (Pi.single b (1 : ℂ) : Fin m → ℂ)

/-- The vector `f = (a w⁻¹ - I)|b⟩` of the proof of Lemma `hsl:lem:search`. -/
def fVec (m : ℕ) (a : ℝ) (b : Fin m) : Fin m → ℂ :=
  ((a : ℂ) • wInv m a - 1) *ᵥ (Pi.single b (1 : ℂ) : Fin m → ℂ)

/-- The weight parameter `a = 2 β₀^{-1/(2n)}` chosen in the proof of Lemma `hsl:lem:search`. -/
def searchA (n : ℕ) (β₀ : ℝ) : ℝ := 2 * β₀ ^ (-(1 : ℝ) / (2 * (n : ℝ)))

variable {m : ℕ}

/-! ### Projector algebra -/

/-- Three pairwise orthogonal idempotents multiply coefficientwise: the
algebra behind `w * wInv = 1` and `wInv * w = 1`. -/
theorem orth_combo_mul {A : Type*} [Ring A] [Algebra ℂ A] {p q r : A}
    (hp : p * p = p) (hq : q * q = q) (hr : r * r = r)
    (hpq : p * q = 0) (hqp : q * p = 0) (hpr : p * r = 0) (hrp : r * p = 0)
    (hqr : q * r = 0) (hrq : r * q = 0) (α β α' β' : ℂ) :
    (p + α • q + β • r) * (p + α' • q + β' • r) = p + (α * α') • q + (β * β') • r := by
  simpa only [one_smul, one_mul] using
    Helpers.SearchWeight.orth_combo_mul3 hp hq hr hpq hqp hpr hrp hqr hrq 1 α β 1 α' β'

/-- `P_v` is Hermitian. -/
theorem isHermitian_Pv (m : ℕ) : (Pv m).IsHermitian := by
  exact Helpers.SearchWeight.star_V m

/-- `P_v² = P_v` (`v` is a unit vector; vacuous for `m = 0`). -/
theorem Pv_mul_Pv (m : ℕ) : Pv m * Pv m = Pv m := by
  exact Helpers.SearchWeight.V_mul_V m

/-- `P_u P_v = 0` for even `m` (`⟪u, v⟫ = m⁻¹ Σ_b (-1)^b = 0`). -/
theorem Pu_mul_Pv (hm : Even m) : XorWeight.Pu m * Pv m = 0 := by
  exact Helpers.SearchWeight.P_mul_V hm

/-- `P_v P_u = 0` for even `m`. -/
theorem Pv_mul_Pu (hm : Even m) : Pv m * XorWeight.Pu m = 0 := by
  exact Helpers.SearchWeight.V_mul_P hm

theorem Pu_mul_Rest (hm : Even m) : XorWeight.Pu m * Rest m = 0 := by
  exact Helpers.SearchWeight.P_mul_R hm

theorem Rest_mul_Pu (hm : Even m) : Rest m * XorWeight.Pu m = 0 := by
  exact Helpers.SearchWeight.R_mul_P hm

theorem Pv_mul_Rest (hm : Even m) : Pv m * Rest m = 0 := by
  exact Helpers.SearchWeight.V_mul_R hm

theorem Rest_mul_Pv (hm : Even m) : Rest m * Pv m = 0 := by
  exact Helpers.SearchWeight.R_mul_V hm

/-- `R² = R` for even `m`. -/
theorem Rest_mul_Rest (hm : Even m) : Rest m * Rest m = Rest m := by
  exact Helpers.SearchWeight.R_mul_R hm

/-- `R` is Hermitian. -/
theorem isHermitian_Rest (m : ℕ) : (Rest m).IsHermitian := by
  exact Helpers.SearchWeight.star_R m

/-- `P_v u = 0` for even `m`: the rows of `P_v` sum to zero. -/
theorem Pv_mulVec_one (hm : Even m) : Pv m *ᵥ (fun _ => 1) = 0 := by
  exact Helpers.SearchWeight.V_mulVec_one hm

/-- `R u = 0` for even `m`. -/
theorem Rest_mulVec_one (hm : Even m) : Rest m *ᵥ (fun _ => 1) = 0 := by
  exact Helpers.SearchWeight.R_mulVec_one hm

/-- `Z² = 1`. -/
theorem parityZ_mul_parityZ (m : ℕ) : parityZ m * parityZ m = 1 := by
  exact Helpers.XorWeight.Z_mul_Z m

/-- `Z P_u Z = P_v` (proof of Lemma `hsl:lem:search`: `Z` maps `u` to `v`). -/
theorem parityZ_mul_Pu_mul_parityZ (m : ℕ) : parityZ m * XorWeight.Pu m * parityZ m = Pv m := by
  exact Helpers.SearchWeight.Z_P_Z m

/-- `Z P_v Z = P_u`. -/
theorem parityZ_mul_Pv_mul_parityZ (m : ℕ) : parityZ m * Pv m * parityZ m = XorWeight.Pu m := by
  exact Helpers.SearchWeight.Z_V_Z m

/-- `Z P_u = P_v Z`. -/
theorem parityZ_mul_Pu (m : ℕ) : parityZ m * XorWeight.Pu m = Pv m * parityZ m := by
  exact Helpers.SearchWeight.Z_mul_P m

/-- `Z P_v = P_u Z`. -/
theorem parityZ_mul_Pv (m : ℕ) : parityZ m * Pv m = XorWeight.Pu m * parityZ m := by
  exact Helpers.SearchWeight.Z_mul_V m

/-- `Z R = R Z` (proof of Lemma `hsl:lem:search`: `Z` preserves `R`). -/
theorem parityZ_mul_Rest (m : ℕ) : parityZ m * Rest m = Rest m * parityZ m := by
  exact Helpers.SearchWeight.Z_mul_R m

/-! ### The weight -/

theorem isHermitian_w (m : ℕ) (a : ℝ) : (w m a).IsHermitian := by
  exact Helpers.SearchWeight.star_W m a

theorem w_mul_wInv (hm : Even m) {a : ℝ} (ha : a ≠ 0) : w m a * wInv m a = 1 := by
  exact Helpers.SearchWeight.W_mul_WInv hm ha

theorem wInv_mul_w (hm : Even m) {a : ℝ} (ha : a ≠ 0) : wInv m a * w m a = 1 := by
  exact Helpers.SearchWeight.WInv_mul_W hm ha

/-- `w⁻¹` is Hermitian (`a` is real). -/
theorem isHermitian_wInv (m : ℕ) (a : ℝ) : (wInv m a).IsHermitian := by
  exact Helpers.SearchWeight.star_WInv m a

theorem isUnit_w (hm : Even m) {a : ℝ} (ha : a ≠ 0) : IsUnit (w m a) := by
  exact ⟨⟨w m a, wInv m a, w_mul_wInv hm ha, wInv_mul_w hm ha⟩, rfl⟩

theorem inv_w (hm : Even m) {a : ℝ} (ha : a ≠ 0) : (w m a)⁻¹ = wInv m a := by
  exact Matrix.inv_eq_right_inv (w_mul_wInv hm ha)

/-- `w u = u`: every row of `w` sums to one (`P_v u = R u = 0` for even `m`). -/
theorem w_mulVec_one (hm : Even m) (a : ℝ) : w m a *ᵥ (fun _ => 1) = fun _ => 1 := by
  exact Helpers.SearchWeight.W_mulVec_one hm a

/-- `w⁻¹ Z w⁻¹ = a⁻² Z` (proof of Lemma `hsl:lem:search`): `Z` swaps `u` and `v` and preserves
`R`. -/
theorem conj_Z (hm : Even m) {a : ℝ} (ha : a ≠ 0) :
    (w m a)⁻¹ * parityZ m * (w m a)⁻¹ = ((a : ℂ) ^ 2)⁻¹ • parityZ m := by
  rw [inv_w hm ha]
  exact Helpers.SearchWeight.WInv_Z_WInv hm a

theorem norm_conj_Z_le (hm : Even m) {a : ℝ} (ha : 0 < a) :
    ‖(w m a)⁻¹ * parityZ m * (w m a)⁻¹‖ ≤ (a ^ 2)⁻¹ := by
  rw [conj_Z hm ha.ne']
  calc ‖((a : ℂ) ^ 2)⁻¹ • parityZ m‖ ≤ ‖((a : ℂ) ^ 2)⁻¹‖ * ‖parityZ m‖ := norm_smul_le _ _
    _ ≤ ‖((a : ℂ) ^ 2)⁻¹‖ * 1 := by gcongr; exact Helpers.XorWeight.norm_Z_le m
    _ = (a ^ 2)⁻¹ := by
        rw [mul_one, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ### The query block (proof of Lemma `hsl:lem:search`) -/

/-- `e = (a⁻¹ - 1) P_u|b⟩ + (a - 1) P_v|b⟩` (from `R - I = -P_u - P_v`). -/
theorem eVec_eq {a : ℝ} (ha : a ≠ 0) (b : Fin m) :
    eVec m a b = (((a : ℂ)⁻¹ - 1) • XorWeight.Pu m + ((a : ℂ) - 1) • Pv m) *ᵥ
      (Pi.single b (1 : ℂ) : Fin m → ℂ) := by
  exact Helpers.SearchWeight.E_eq ha b

/-- `f = (a - 1) P_u|b⟩ + (a⁻¹ - 1) P_v|b⟩`. -/
theorem fVec_eq {a : ℝ} (ha : a ≠ 0) (b : Fin m) :
    fVec m a b = (((a : ℂ) - 1) • XorWeight.Pu m + ((a : ℂ)⁻¹ - 1) • Pv m) *ᵥ
      (Pi.single b (1 : ℂ) : Fin m → ℂ) := by
  exact Helpers.SearchWeight.F_eq ha b

/-- For even `m`, `‖x P_u|b⟩ + y P_v|b⟩‖² = (|x|² + |y|²)/m`: `P_u|b⟩ = u/√m`
and `P_v|b⟩ = ±v/√m` with `u ⊥ v`. -/
theorem norm_combo_sq (hm : Even m) (b : Fin m) (x y : ℂ) :
    ‖(WithLp.toLp 2 ((x • XorWeight.Pu m + y • Pv m) *ᵥ (Pi.single b (1 : ℂ) : Fin m → ℂ)) :
      EuclideanSpace ℂ (Fin m))‖ ^ 2 = (‖x‖ ^ 2 + ‖y‖ ^ 2) / m := by
  exact Helpers.SearchWeight.norm_combo_sq hm b x y

/-- `‖e‖ ≤ √2 a/√m` for `a ≥ 1` (proof of Lemma `hsl:lem:search`). -/
theorem norm_e_le (hm : Even m) {a : ℝ} (ha : 1 ≤ a) (b : Fin m) :
    ‖(WithLp.toLp 2 (eVec m a b) : EuclideanSpace ℂ (Fin m))‖ ≤ Real.sqrt 2 * a / Real.sqrt m := by
  exact Helpers.SearchWeight.norm_E_le hm ha b

/-- `‖f‖ ≤ √2 a/√m` for `a ≥ 1` (proof of Lemma `hsl:lem:search`). -/
theorem norm_f_le (hm : Even m) {a : ℝ} (ha : 1 ≤ a) (b : Fin m) :
    ‖(WithLp.toLp 2 (fVec m a b) : EuclideanSpace ℂ (Fin m))‖ ≤ Real.sqrt 2 * a / Real.sqrt m := by
  exact Helpers.SearchWeight.norm_F_le hm ha b

/-- Entrywise conjugation preserves the Euclidean norm. -/
theorem norm_toLp_star (v : Fin m → ℂ) :
    ‖(WithLp.toLp 2 (star v) : EuclideanSpace ℂ (Fin m))‖ =
      ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin m))‖ := by
  exact Helpers.SearchWeight.norm_toLp_star v

/-- The rank-one matrix `x yᵀ` has L2 operator norm at most `‖x‖ ‖y‖`
(Cauchy-Schwarz for the bilinear pairing `Σ_i y_i z_i`). -/
theorem norm_vecMulVec_le (x y : Fin m → ℂ) :
    ‖Matrix.vecMulVec x y‖ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin m))‖ *
      ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin m))‖ := by
  exact Helpers.SearchWeight.norm_vecMulVec_le x y

/-- **The conjugated query block** (proof of Lemma `hsl:lem:search`):
`w D_b w⁻¹ = D_b - 2(e⟨b| + |b⟩f† + e f†)`, from `w|b⟩ = a(e + |b⟩)` and
`⟨b|w⁻¹ = a⁻¹(f + |b⟩)†` (`w⁻¹` Hermitian, `a` real). -/
theorem conj_D_eq (hm : Even m) {a : ℝ} (ha : a ≠ 0) (b : Fin m) :
    w m a * reflect b * (w m a)⁻¹ = reflect b - (2 : ℂ) •
      (Matrix.vecMulVec (eVec m a b) (Pi.single b (1 : ℂ) : Fin m → ℂ) +
        Matrix.vecMulVec (Pi.single b (1 : ℂ) : Fin m → ℂ) (star (fVec m a b)) +
        Matrix.vecMulVec (eVec m a b) (star (fVec m a b))) := by
  exact Helpers.SearchWeight.conj_D_eq hm ha b

/-- The display bound of the proof of Lemma `hsl:lem:search` (first inequality):
`‖w D_b w⁻¹‖ ≤ 1 + 4√2 a/√m + 4a²/m` for `a ≥ 1`. -/
theorem norm_conj_D_le_fine (hm : Even m) {a : ℝ} (ha : 1 ≤ a) (b : Fin m) :
    ‖w m a * reflect b * (w m a)⁻¹‖ ≤ 1 + 4 * Real.sqrt 2 * a / Real.sqrt m + 4 * a ^ 2 / m := by
  exact Helpers.SearchWeight.norm_conj_D_le_fine hm ha b

/-- The second inequality of that display: `4√2 a/√m + 4a²/m ≤ 12 a/√m` for
`0 ≤ a ≤ √m` (also at `m = 0`, where it forces `a = 0`). -/
theorem fine_le_twelve {a : ℝ} (ha : 0 ≤ a) (ham : a ≤ Real.sqrt m) :
    1 + 4 * Real.sqrt 2 * a / Real.sqrt m + 4 * a ^ 2 / m ≤ 1 + 12 * a / Real.sqrt m := by
  exact Helpers.SearchWeight.fine_le_twelve ha ham

/-- **Per-query weight growth** (proof of Lemma `hsl:lem:search`): for `1 ≤ a ≤ √m`,
`‖w D_b w⁻¹‖ ≤ 1 + 12 a/√m`. -/
theorem norm_conj_D_le (hm : Even m) {a : ℝ} (ha : 1 ≤ a) (ham : a ≤ Real.sqrt m) (b : Fin m) :
    ‖w m a * reflect b * (w m a)⁻¹‖ ≤ 1 + 12 * a / Real.sqrt m := by
  exact (norm_conj_D_le_fine hm ha b).trans (fine_le_twelve (by linarith) ham)

/-! ### Final arithmetic (proof of Lemma `hsl:lem:search`) -/

/-- `(1 + 12a/√m)^{2q} ≤ e^{24aq/√m}` (proof of Lemma `hsl:lem:search`). -/
theorem lam_pow_le {a : ℝ} (ha : 0 ≤ a) (m q : ℕ) :
    (1 + 12 * a / Real.sqrt m) ^ (2 * q) ≤ Real.exp (24 * a * q / Real.sqrt m) := by
  exact Helpers.SearchWeight.lam_pow_le ha m q

/-- `0 < m` follows from the hypothesis `m ≥ 4 β₀^{-1/n}` with `β₀ > 0`. -/
theorem pos_of_hmβ {n : ℕ} {β₀ : ℝ} (hβ₀ : 0 < β₀) (hmβ : 4 * β₀ ^ (-(1 : ℝ) / n) ≤ m) :
    0 < m := by
  have h : (0 : ℝ) < m :=
    lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos hβ₀ _)) hmβ
  exact_mod_cast h

/-- `a² = 4 β₀^{-1/n}` for the choice `a = 2β₀^{-1/(2n)}` (every `n`, using
Lean's `x/0 = 0` at `n = 0`). -/
theorem searchA_sq {n : ℕ} {β₀ : ℝ} (hβ₀ : 0 < β₀) :
    searchA n β₀ ^ 2 = 4 * β₀ ^ (-(1 : ℝ) / n) := by
  exact Helpers.SearchWeight.searchA_sq hβ₀

/-- `a ≥ 1` once `β₀ ≤ 1`. -/
theorem one_le_searchA {n : ℕ} {β₀ : ℝ} (hβ₀ : 0 < β₀) (hβ1 : β₀ ≤ 1) : 1 ≤ searchA n β₀ := by
  exact Helpers.SearchWeight.one_le_searchA hβ₀ hβ1

/-- `a ≤ √m` is the hypothesis `m ≥ 4 β₀^{-1/n}` (proof of Lemma `hsl:lem:search`: "the hypothesis
on `m` gives `a^2 = 4β₀^{-1/n} ≤ m`"). -/
theorem searchA_le_sqrt {n : ℕ} {β₀ : ℝ} (hβ₀ : 0 < β₀) (hmβ : 4 * β₀ ^ (-(1 : ℝ) / n) ≤ m) :
    searchA n β₀ ≤ Real.sqrt m := by
  exact Helpers.SearchWeight.searchA_le_sqrt hβ₀ hmβ

/-- `a^{-2n} = 4^{-n} β₀` for `n ≥ 1` (false at `n = 0`). -/
theorem searchA_sq_inv_pow {n : ℕ} (hn : 1 ≤ n) {β₀ : ℝ} (hβ₀ : 0 < β₀) :
    ((searchA n β₀ ^ 2)⁻¹) ^ n = ((4 : ℝ) ^ n)⁻¹ * β₀ := by
  exact Helpers.SearchWeight.searchA_sq_inv_pow hn hβ₀

/-- **The logarithm step** (proof of Lemma `hsl:lem:search`): from
`β₀ ≤ a^{-2n} e^{24at/√m}` with `a = 2β₀^{-1/(2n)}` follow `24at/√m ≥ 2n log 2`
and `t ≥ (log 2/24) n √m β₀^{1/(2n)}`. -/
theorem search_final {n : ℕ} (hn : 1 ≤ n) {β₀ t : ℝ} (hβ₀ : 0 < β₀)
    (h : β₀ ≤ ((searchA n β₀ ^ 2)⁻¹) ^ n * Real.exp (24 * searchA n β₀ * t / Real.sqrt m)) :
    Real.log 2 / 24 * n * Real.sqrt m * β₀ ^ (1 / (2 * (n : ℝ))) ≤ t := by
  exact Helpers.SearchWeight.search_final hn hβ₀ h

/-- A pointwise lower bound is a lower bound for the uniform average over the
`mⁿ` hidden inputs. -/
theorem le_avg_of_forall_le {n : ℕ} (hm0 : 0 < m) {f : (Fin n → Fin m) → ℝ} {β : ℝ}
    (h : ∀ j, β ≤ f j) : β ≤ ((m : ℝ) ^ n)⁻¹ * ∑ j, f j := by
  have hmn : (0 : ℝ) < (m : ℝ) ^ n := pow_pos (by exact_mod_cast hm0) n
  rw [le_inv_mul_iff₀ hmn]
  calc (m : ℝ) ^ n * β = ∑ _j : Fin n → Fin m, β := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ∑ j, f j := Finset.sum_le_sum fun j _ => h j

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The real average correlation is the real part of the complex one. -/
theorem avg_re_le_norm {n : ℕ} (c : (Fin n → Fin m) → ℂ) :
    ((m : ℝ) ^ n)⁻¹ * ∑ j, parity j * (c j).re ≤
      ‖((m : ℂ) ^ n)⁻¹ * ∑ j, (parity j : ℂ) * c j‖ := by
  refine le_trans (le_of_eq ?_) (Complex.re_le_norm _)
  rw [show ((m : ℂ) ^ n)⁻¹ = ((((m : ℝ) ^ n)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_ofReal_mul]

/-- The average parity correlation of a program is at most one (`‖M‖ ≤ 1`,
`‖φ₀‖ ≤ 1`, programs are unitary: `Program.eval_unitary`). This is what makes
`β₀ ≤ 1` automatic. -/
theorem avg_corr_le_one {n : ℕ} (P : ProjFamily K (Fin n × Fin m))
    (q : Program (oneHotOracle P)) (φ₀ : K) (hφ₀ : ‖φ₀‖ ≤ 1) (M : K →L[ℂ] K) (hM : ‖M‖ ≤ 1) :
    ((m : ℝ) ^ n)⁻¹ * ∑ j, parity j * (⟪q.eval j φ₀, M (q.eval j φ₀)⟫_ℂ).re ≤ 1 := by
  have key := program_correlation_le P (1 : Matrix (Fin m) (Fin m) ℂ) Matrix.isHermitian_one
    isUnit_one (Matrix.one_mulVec _) le_rfl
    (fun b => by rw [inv_one, one_mul, mul_one]; exact Helpers.XorWeight.norm_D_le b)
    q φ₀ hφ₀ M hM
  rw [inv_one, one_mul, mul_one, one_pow, mul_one] at key
  have hZ : ‖parityZ m‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) (Helpers.XorWeight.norm_Z_le m)
  exact (avg_re_le_norm _).trans (key.trans hZ)

/-- **The adversary bound for the search weight** (proof of Lemma `hsl:lem:search`): for
`1 ≤ a ≤ √m` and even `m`, the average parity correlation is at most
`a^{-2n} e^{24aq/√m}` (`Adversary.program_correlation_le` with `λ = 1 + 12a/√m`,
`conj_Z`, `norm_conj_D_le`, `lam_pow_le`). -/
theorem avg_corr_le {n : ℕ} (hm : Even m) {a : ℝ} (ha : 1 ≤ a) (ham : a ≤ Real.sqrt m)
    (P : ProjFamily K (Fin n × Fin m)) (q : Program (oneHotOracle P)) (φ₀ : K)
    (hφ₀ : ‖φ₀‖ ≤ 1) (M : K →L[ℂ] K) (hM : ‖M‖ ≤ 1) :
    ((m : ℝ) ^ n)⁻¹ * ∑ j, parity j * (⟪q.eval j φ₀, M (q.eval j φ₀)⟫_ℂ).re ≤
      ((a ^ 2)⁻¹) ^ n * Real.exp (24 * a * q.count / Real.sqrt m) := by
  have ha0 : a ≠ 0 := (by linarith : (0 : ℝ) < a).ne'
  have hlam0 : 0 ≤ 12 * a / Real.sqrt m := div_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hlam : 1 ≤ 1 + 12 * a / Real.sqrt m := by linarith
  have key := program_correlation_le P (w m a) (isHermitian_w m a) (isUnit_w hm ha0)
    (w_mulVec_one hm a) hlam (fun b => norm_conj_D_le hm ha ham b) q φ₀ hφ₀ M hM
  have hZ : ‖(w m a)⁻¹ * parityZ m * (w m a)⁻¹‖ ^ n ≤ ((a ^ 2)⁻¹) ^ n :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_conj_Z_le hm (by linarith)) n
  have hL := lam_pow_le (by linarith : (0 : ℝ) ≤ a) m q.count
  refine (avg_re_le_norm _).trans (key.trans ?_)
  exact mul_le_mul hZ hL (pow_nonneg (by linarith) _) (by positivity)

/-- **Lemma `hsl:lem:search`** (Lemma `hsl:lem:search`, eq. `hsl:eq:searchbound`),
observable form. Let `m` be even. A Boolean one-hot program `q` (inverse
queries counted), run on an input-independent seed `φ₀` with `‖φ₀‖ ≤ 1` and
read with an input-independent operator `M`, `‖M‖ ≤ 1`, whose parity
correlation **averaged over uniformly random hidden positions** is at least
`β₀ > 0`, with `m ≥ 4 β₀^{-1/n}`, makes
`q ≥ (log 2/24) n √m β₀^{1/(2n)}` queries. -/
theorem search_lemma {n : ℕ} (hm : Even m) (P : ProjFamily K (Fin n × Fin m))
    (q : Program (oneHotOracle P)) (φ₀ : K) (hφ₀ : ‖φ₀‖ ≤ 1) (M : K →L[ℂ] K) (hM : ‖M‖ ≤ 1)
    {β₀ : ℝ} (hβ₀ : 0 < β₀) (hmβ : 4 * β₀ ^ (-(1 : ℝ) / n) ≤ m)
    (hcorr : β₀ ≤ ((m : ℝ) ^ n)⁻¹ *
      ∑ j, parity j * (⟪q.eval j φ₀, M (q.eval j φ₀)⟫_ℂ).re) :
    Real.log 2 / 24 * n * Real.sqrt m * β₀ ^ (1 / (2 * (n : ℝ))) ≤ q.count := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hβ1 : β₀ ≤ 1 := hcorr.trans (avg_corr_le_one P q φ₀ hφ₀ M hM)
  have ha1 := one_le_searchA (n := n) hβ₀ hβ1
  have ham := searchA_le_sqrt hβ₀ hmβ
  exact search_final hn hβ₀ (hcorr.trans (avg_corr_le hm ha1 ham P q φ₀ hφ₀ M hM))

/-- Worst-case form of `search_lemma`: correlation at least `β₀` on every
hidden input. -/
theorem search_lemma_worst {n : ℕ} (hm : Even m) (P : ProjFamily K (Fin n × Fin m))
    (q : Program (oneHotOracle P)) (φ₀ : K) (hφ₀ : ‖φ₀‖ ≤ 1) (M : K →L[ℂ] K) (hM : ‖M‖ ≤ 1)
    {β₀ : ℝ} (hβ₀ : 0 < β₀) (hmβ : 4 * β₀ ^ (-(1 : ℝ) / n) ≤ m)
    (hcorr : ∀ j, β₀ ≤ parity j * (⟪q.eval j φ₀, M (q.eval j φ₀)⟫_ℂ).re) :
    Real.log 2 / 24 * n * Real.sqrt m * β₀ ^ (1 / (2 * (n : ℝ))) ≤ q.count := by
  exact search_lemma hm P q φ₀ hφ₀ M hM hβ₀ hmβ
    (le_avg_of_forall_le (pos_of_hmβ hβ₀ hmβ) hcorr)

end

end SparseLowerBounds.SearchWeight
end
