import ManuscriptConformance.ActualRuns
import ManuscriptConformance.GateODETimeCertValid
import DysonFullClass.Coverage
import DysonFullClass.Examples

/-!
# Conformance: certificates on the opposite branches `K_{±k} = H ± k D`

Manuscript: proof of Lemma `odel:lem:dyson` ("The same control follows if the input gives these
bounds for `K_{±k} = H ± kD` on a common mesh, for two opposite frequencies"), and the sample
certificates of Theorem `ode:thm:time` and of the time-dependent Theorem `ode:thm:gates`.

## Notation

True generator pieces `G_r(u) = D(u) + i H(u)` and represented samples `G̃_r = D̃_r + i H̃_r`
(`D = dissipativePart`, `H = hamiltonianPart`, `K_k = lchsHamiltonian · k = k D + H`). Both
branches are taken of the **same** represented samples `G̃_r` on the **same** mesh `t`. For `k > 0`
the branch errors are `ΔK_± = K_{±k}(G_r(u) - G̃_r) = (H - H̃) ± k (D - D̃)` (`lchs_sub_eq`; up to
sign this is the paper's `(H̃ - H) ± k (D̃ - D)`, `norm_branch_eq`), and the integrated branch
errors are `E_± = ∑_r ∫_{t_r}^{t_{r+1}} ‖ΔK_±(u)‖ du` (`branchErr t G G̃ (±k)`, including the
variation of the true pieces within each cell); `branchSum t G G̃ k = E₊ + E₋`.

## The conversion

* `hamiltonianPart_eq_branches`, `dissipativePart_eq_branches`: `ΔH = (ΔK₊ + ΔK₋)/2` and
  `ΔD = (ΔK₊ - ΔK₋)/(2k)` (operator identities; `k ≠ 0`, so no bound on `D` is inferred from
  `k = 0`);
* `norm_hamiltonianPart_le_branches`, `norm_dissipativePart_le_branches`, `norm_le_branches`:
  `‖ΔH‖ ≤ (‖ΔK₊‖ + ‖ΔK₋‖)/2`, `‖ΔD‖ ≤ (‖ΔK₊‖ + ‖ΔK₋‖)/(2k)` and
  `‖ΔG‖ ≤ (1 + 1/k)(‖ΔK₊‖ + ‖ΔK₋‖)/2` for `k > 0` (no commutation, no positivity of the samples);
* `branch_intervalIntegrable`: the branch errors are interval integrable whenever the true pieces
  are (`RepresentedSampleODE.RegularPieces`, a hypothesis of every endpoint below);
* `dissErr_le_branchSum`, `sampleErr_le_branchSum`: `E_D ≤ (E₊ + E₋)/(2k)` and
  `E_G ≤ (1 + 1/k)(E₊ + E₋)/2` on every mesh (nonuniform meshes, and samples whose sparse supports
  change from cell to cell, included) and on every Hilbert space.

## Composition into the endpoints

Each branch endpoint takes the branch certificate (no supplied generator-error conclusion) and
concludes for the existing protocol, with the existing counts. With `S = E₊ + E₋` at the selected
branch frequency `k > 0` of the certificate, the sufficient budgets are those of the original
endpoint after `ΔG ≤ (1 + 1/k) S/2`, `ΔD ≤ S/(2k)`, so `ΔG + 2ΔD ≤ (1 + 3/k) S/2`
(`budgets_of_branch`):

| endpoint | branch endpoint | branch budgets |
|---|---|---|
| `ode_thm_time`, `ode_thm_time_approx`, `ode_thm_time_actual` | `ode_thm_time_branch`, `ode_thm_time_approx_branch`, `ode_thm_time_actual_branch` | `ζ + c_q ((1 + 3/k) S/2 + 2 ΔR) ≤ ε/(2000 ḡ)` and `6 R (S/(2k) + ΔR) ≤ ν` (`time_budgets_of_branch`) |
| `ode_thm_gates_time_cert`, `ode_thm_gates_time_decoder_cert`, `ode_thm_gates_time_cert_valid`, `ode_thm_gates_time_decoder_cert_valid` | the same names with `_branch` | `ζ + 2 ((1 + 3/k) S/2) ≤ ε/(2000 ḡ)` and `6 R' S/(2k) ≤ ν'` (`gate_budgets_of_branch`) |
| `DysonFullClass.fullValidAt_of_raw` | `fullValidAt_of_branch_raw`, `fullValid_of_branch_raw` | `2 s ((1 + 1/k) S/2) ≤ log(1 + δ_m)` on the raw samples `D₀.matrix (x, σ r)` |
| `DysonFullClass.fullValidAt_of_clipped` | `fullValidAt_of_branch_clipped` | `(1 + 1/k) S/2 ≤ log(1 + δ_m)` on the clipped samples |

Here `ΔR = Mesh.refinementError D t T N`, `R = TimeDependentODE.radius (c_q ḡ) ε` and
`ν = TimeDependentODE.precision (c_q ḡ) ε` are the radius and precision of the formal solver of
`ode:thm:time`, and `R' = TimeDependentODE.radius (2ḡ) ε`, `ν' = TimeDependentODE.precision (2ḡ) ε`
those of the time-dependent gate solver. The branch frequency `k` and the solver radius are kept
separate: no `k` is identified with a radius. At `k = R'` the second gate budget reads `3 S ≤ ν'`
and the first `ζ + (1 + 3/R') S ≤ ε/(2000 ḡ)`.

**Constants.** The formal gate endpoints allocate `ζ + 2 (ΔG + 2 ΔD) ≤ ε/(2000 ḡ)` and
`6 R' ΔD ≤ ν'` (`ode_thm_gates_time_cert`); through the conversion these are implied by
`ζ + (1 + 3/k)(E₊ + E₋) ≤ ε/(2000 ḡ)` and `(3 R'/k)(E₊ + E₋) ≤ ν'`. The paper's proof of
`ode:thm:gates` instead certifies one decoded generator for every `|k| ≤ R` with the factor
`√(1 + R²)`, and Lemma `odel:lem:dyson` uses two opposite frequencies with `k ≥ 1`; the formal
endpoints accept every `k > 0` with the constants above. The full-class Dyson coverage keeps the
factor `2s` of the clipping step and the parameter `z = s η T` of `DysonFullClass` unchanged.

The time endpoints `ode_thm_time_branch`, `ode_thm_time_approx_branch` and
`ode_thm_time_actual_branch` state, for one protocol (resp. trial family) chosen from the public
data, both the guarantee of the original endpoint and the guarantee from branch certificates, so
the branch guarantee is about the protocol of the existing endpoint. The gate endpoints name their
protocol explicitly (`nprotocol …`), as the original ones do. `fullValid_of_branch_raw` gives
`FullValid`, the validity relation of the full-class solver `DysonFullClass.full_single` and of
the fixed-parameter corollaries `full_fixed`, `full_no_uniform`.

## Test (non-accretive represented sample)

`growC_values`, `nonaccretive_branch_accepted`: the true piece `0` (accretive) and the represented
sample `G̃ = -a·1` (`DysonFullClass.Examples.growC`, not accretive for `a > 0`) on the uniform mesh
of `[0, T]` have `E₊ = E₋ = k a T`, `ΔD = a T = (E₊ + E₋)/(2k)` (the dissipative bound is attained)
and `ΔG = a T ≤ (1 + 1/k)(E₊ + E₋)/2`; the branch budgets of the gate endpoints hold under explicit
conditions on `a`, and the conversion produces the original sample budgets for this sample.

## Not covered

* Certificates on a whole frequency grid: the endpoints use one pair `±k`; certificates on other
  frequencies are not combined.
* The conversion needs the same represented samples for both branches; separately decoded branch
  samples are not covered.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

namespace ManuscriptConformance

noncomputable section

universe u v w

/-! ### The operator identities and bounds -/

section Operator

open ContinuousLinearMap MeasureTheory
open SparseHamiltonian.ODEHermitianReduction (dissipativePart hamiltonianPart lchsHamiltonian)
open scoped InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- `K_k(A) + K_{-k}(A) = 2 H(A)`. -/
theorem lchs_add_neg (A : V →L[ℂ] V) (k : ℝ) :
    lchsHamiltonian A k + lchsHamiltonian A (-k) = (2 : ℂ) • hamiltonianPart A := by
  simp only [lchsHamiltonian, Complex.ofReal_neg]
  module

/-- `K_k(A) - K_{-k}(A) = 2k D(A)`. -/
theorem lchs_sub_neg (A : V →L[ℂ] V) (k : ℝ) :
    lchsHamiltonian A k - lchsHamiltonian A (-k) = (2 * (k : ℂ)) • dissipativePart A := by
  simp only [lchsHamiltonian, Complex.ofReal_neg]
  module

/-- **`ΔH = (ΔK₊ + ΔK₋)/2`**: the Hamiltonian part from the two opposite branches. -/
theorem hamiltonianPart_eq_branches (A : V →L[ℂ] V) (k : ℝ) :
    hamiltonianPart A = (2 : ℂ)⁻¹ • (lchsHamiltonian A k + lchsHamiltonian A (-k)) := by
  rw [lchs_add_neg, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- **`ΔD = (ΔK₊ - ΔK₋)/(2k)`** for `k ≠ 0` (the case `k = 0` gives no bound on `D`). -/
theorem dissipativePart_eq_branches (A : V →L[ℂ] V) {k : ℝ} (hk : k ≠ 0) :
    dissipativePart A = (2 * (k : ℂ))⁻¹ • (lchsHamiltonian A k - lchsHamiltonian A (-k)) := by
  have h : (2 * (k : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hk)
  rw [lchs_sub_neg, smul_smul, inv_mul_cancel₀ h, one_smul]

/-- The branch error of `A - B` is `(H(A) - H(B)) + k (D(A) - D(B))`. -/
theorem lchs_sub_eq (A B : V →L[ℂ] V) (k : ℝ) :
    lchsHamiltonian (A - B) k = (hamiltonianPart A - hamiltonianPart B) +
      (k : ℂ) • (dissipativePart A - dissipativePart B) := by
  rw [SparseHamiltonian.ODEHermitianReduction.lchsHamiltonian_sub]
  simp only [lchsHamiltonian]
  module

/-- **The paper's branch errors**: `‖K_k(G - G̃)‖ = ‖(H̃ - H) + k (D̃ - D)‖`. -/
theorem norm_branch_eq (A B : V →L[ℂ] V) (k : ℝ) :
    ‖lchsHamiltonian (A - B) k‖ = ‖(hamiltonianPart B - hamiltonianPart A) +
      (k : ℂ) • (dissipativePart B - dissipativePart A)‖ := by
  rw [lchs_sub_eq, ← norm_neg]
  congr 1
  module

/-- `‖H(A)‖ ≤ (‖K_k(A)‖ + ‖K_{-k}(A)‖)/2`. -/
theorem norm_hamiltonianPart_le_branches (A : V →L[ℂ] V) (k : ℝ) :
    ‖hamiltonianPart A‖ ≤ (‖lchsHamiltonian A k‖ + ‖lchsHamiltonian A (-k)‖) / 2 := by
  rw [hamiltonianPart_eq_branches A k, norm_smul]
  have h2 : ‖(2 : ℂ)⁻¹‖ = 2⁻¹ := by simp
  have h := norm_add_le (lchsHamiltonian A k) (lchsHamiltonian A (-k))
  rw [h2]
  linarith

/-- `‖D(A)‖ ≤ (‖K_k(A)‖ + ‖K_{-k}(A)‖)/(2k)` for `k > 0`. -/
theorem norm_dissipativePart_le_branches (A : V →L[ℂ] V) {k : ℝ} (hk : 0 < k) :
    ‖dissipativePart A‖ ≤ (‖lchsHamiltonian A k‖ + ‖lchsHamiltonian A (-k)‖) / (2 * k) := by
  rw [dissipativePart_eq_branches A hk.ne', norm_smul]
  have h2 : ‖(2 * (k : ℂ))⁻¹‖ = (2 * k)⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
    norm_num
  rw [h2, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by positivity)

/-- **`‖ΔG‖ ≤ (1 + 1/k)(‖ΔK₊‖ + ‖ΔK₋‖)/2`** for `k > 0`: from `G = D + i H`. -/
theorem norm_le_branches (A : V →L[ℂ] V) {k : ℝ} (hk : 0 < k) :
    ‖A‖ ≤ (1 + 1 / k) * (‖lchsHamiltonian A k‖ + ‖lchsHamiltonian A (-k)‖) / 2 := by
  have hD := norm_dissipativePart_le_branches A hk
  have hH := norm_hamiltonianPart_le_branches A k
  have hdec : ‖A‖ ≤ ‖dissipativePart A‖ + ‖hamiltonianPart A‖ :=
    calc ‖A‖ = ‖dissipativePart A + Complex.I • hamiltonianPart A‖ := by
          rw [SparseHamiltonian.ODEHermitianReduction.decomposition]
      _ ≤ ‖dissipativePart A‖ + ‖Complex.I • hamiltonianPart A‖ := norm_add_le _ _
      _ = ‖dissipativePart A‖ + ‖hamiltonianPart A‖ := by
          rw [norm_smul, Complex.norm_I, one_mul]
  have hk0 := hk.ne'
  have he : (1 + 1 / k) * (‖lchsHamiltonian A k‖ + ‖lchsHamiltonian A (-k)‖) / 2 =
      (‖lchsHamiltonian A k‖ + ‖lchsHamiltonian A (-k)‖) / (2 * k) +
        (‖lchsHamiltonian A k‖ + ‖lchsHamiltonian A (-k)‖) / 2 := by
    field_simp
    ring
  rw [he]
  linarith

/-- The branch error of an integrable operator path minus a constant is integrable. -/
theorem branch_intervalIntegrable {G : ℝ → V →L[ℂ] V} {a b : ℝ}
    (hG : IntervalIntegrable G volume a b) (C : V →L[ℂ] V) (k : ℝ) :
    IntervalIntegrable (fun u => ‖lchsHamiltonian (G u - C) k‖) volume a b := by
  have h1 : IntervalIntegrable (fun u => G u - C) volume a b := hG.sub intervalIntegrable_const
  have hadj : Continuous (fun A : V →L[ℂ] V => A†) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := V) (F := V)).continuous
  have hc : Continuous (fun A : V →L[ℂ] V => ‖lchsHamiltonian A k‖) := by
    simp only [lchsHamiltonian, dissipativePart, SparseHamiltonian.HermitianDilation.hermitianPart,
      hamiltonianPart]
    exact ((((continuous_id.add hadj).const_smul ((2 : ℂ)⁻¹)).const_smul (k : ℂ)).add
      ((continuous_id.sub hadj).const_smul (-Complex.I / 2))).norm
  refine (h1.norm.const_mul (SparseHamiltonian.ODEHermitianReduction.phaseScale k)).mono_fun'
    (hc.comp_aestronglyMeasurable h1.aestronglyMeasurable_restrict_uIoc) ?_
  filter_upwards with u
  simp only [norm_norm]
  exact SparseHamiltonian.ODEHermitianReduction.norm_lchsHamiltonian_le _ _

/-- On one cell: `∫ ‖D(F - C)‖ ≤ (∫ ‖K_k(F - C)‖ + ∫ ‖K_{-k}(F - C)‖)/(2k)`. -/
theorem cell_dissipative_le_branches {F : ℝ → V →L[ℂ] V} {a b : ℝ} (hab : a ≤ b)
    (hF : IntervalIntegrable F volume a b) (C : V →L[ℂ] V) {k : ℝ} (hk : 0 < k) :
    ∫ u in a..b, ‖dissipativePart (F u - C)‖ ≤
      ((∫ u in a..b, ‖lchsHamiltonian (F u - C) k‖) +
        ∫ u in a..b, ‖lchsHamiltonian (F u - C) (-k)‖) / (2 * k) := by
  have hp := branch_intervalIntegrable hF C k
  have hm := branch_intervalIntegrable hF C (-k)
  rw [← intervalIntegral.integral_add hp hm, ← intervalIntegral.integral_div]
  exact intervalIntegral.integral_mono_on hab
    (SparseHamiltonian.MeshCertificateODE.dissipativePart_intervalIntegrable hF C)
    ((hp.add hm).div_const _) fun u _ => norm_dissipativePart_le_branches _ hk

/-- On one cell: `∫ ‖F - C‖ ≤ (1 + 1/k)(∫ ‖K_k(F - C)‖ + ∫ ‖K_{-k}(F - C)‖)/2`. -/
theorem cell_norm_le_branches {F : ℝ → V →L[ℂ] V} {a b : ℝ} (hab : a ≤ b)
    (hF : IntervalIntegrable F volume a b) (C : V →L[ℂ] V) {k : ℝ} (hk : 0 < k) :
    ∫ u in a..b, ‖F u - C‖ ≤
      (1 + 1 / k) * ((∫ u in a..b, ‖lchsHamiltonian (F u - C) k‖) +
        ∫ u in a..b, ‖lchsHamiltonian (F u - C) (-k)‖) / 2 := by
  have hp := branch_intervalIntegrable hF C k
  have hm := branch_intervalIntegrable hF C (-k)
  rw [← intervalIntegral.integral_add hp hm, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_div]
  exact intervalIntegral.integral_mono_on hab (hF.sub intervalIntegrable_const).norm
    (((hp.add hm).const_mul _).div_const _) fun u _ => norm_le_branches _ hk

end Operator

/-! ### The integrated branch errors -/

section Integrated

open ContinuousLinearMap MeasureTheory TimeDependentExtensions SparseHamiltonian
open SparseHamiltonian.ODEHermitianReduction (dissipativePart hamiltonianPart lchsHamiltonian)
open SparseHamiltonian.MeshCertificateODE (sampleErr dissErr)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] {M : ℕ}

/-- **The integrated branch error** `E_k = ∑_r ∫_{t_r}^{t_{r+1}} ‖K_k(G_r(u) - G̃_r)‖ du` of the
samples `G̃_r` against the pieces `G_r` (operator norm; within-cell variation of `G_r` and
representation error together). -/
def branchErr (t : ℕ → ℝ) (G : Fin M → ℝ → V →L[ℂ] V) (Gt : Fin M → V →L[ℂ] V) (k : ℝ) : ℝ :=
  ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖lchsHamiltonian (G r u - Gt r) k‖

/-- **The opposite-branch certificate** `E₊ + E₋` at `±k`, of the same samples on the same mesh. -/
def branchSum (t : ℕ → ℝ) (G : Fin M → ℝ → V →L[ℂ] V) (Gt : Fin M → V →L[ℂ] V) (k : ℝ) : ℝ :=
  branchErr t G Gt k + branchErr t G Gt (-k)

theorem branchErr_nonneg {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → V →L[ℂ] V) (Gt : Fin M → V →L[ℂ] V) (k : ℝ) : 0 ≤ branchErr t G Gt k :=
  Finset.sum_nonneg fun r _ =>
    intervalIntegral.integral_nonneg (hmesh.mono (Nat.le_succ r)) fun _ _ => norm_nonneg _

/-- **`E_D ≤ (E₊ + E₋)/(2k)`** for regular pieces, `k > 0`. -/
theorem dissErr_le_branchSum {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → V →L[ℂ] V) (Gt : Fin M → V →L[ℂ] V)
    (hreg : RepresentedSampleODE.RegularPieces t G) {k : ℝ} (hk : 0 < k) :
    dissErr t G Gt ≤ branchSum t G Gt k / (2 * k) := by
  unfold dissErr branchSum branchErr
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  exact Finset.sum_le_sum fun r _ =>
    cell_dissipative_le_branches (hmesh.mono (Nat.le_succ r)) (hreg r) (Gt r) hk

/-- **`E_G ≤ (1 + 1/k)(E₊ + E₋)/2`** for regular pieces, `k > 0`. -/
theorem sampleErr_le_branchSum {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → V →L[ℂ] V) (Gt : Fin M → V →L[ℂ] V)
    (hreg : RepresentedSampleODE.RegularPieces t G) {k : ℝ} (hk : 0 < k) :
    sampleErr t G Gt ≤ (1 + 1 / k) * branchSum t G Gt k / 2 := by
  unfold sampleErr branchSum branchErr
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_le_sum fun r _ =>
    cell_norm_le_branches (hmesh.mono (Nat.le_succ r)) (hreg r) (Gt r) hk

/-- **The budget arithmetic**: from `ΔG ≤ (1 + 1/k) S/2` and `ΔD ≤ S/(2k)`, the budgets
`ζ + c ((1 + 3/k) S/2 + 2ρ) ≤ A` and `6 R (S/(2k) + ρ) ≤ B` give `ζ + c (ΔG + 2ΔD + 2ρ) ≤ A` and
`6 R (ΔD + ρ) ≤ B`. -/
theorem budgets_of_branch {SG SD S k c R ζ ρ A B : ℝ} (hk : 0 < k) (hc : 0 ≤ c) (hR : 0 ≤ R)
    (hG : SG ≤ (1 + 1 / k) * S / 2) (hD : SD ≤ S / (2 * k))
    (h1 : ζ + c * ((1 + 3 / k) * S / 2 + 2 * ρ) ≤ A) (h2 : 6 * R * (S / (2 * k) + ρ) ≤ B) :
    ζ + c * (SG + 2 * SD + 2 * ρ) ≤ A ∧ 6 * R * (SD + ρ) ≤ B := by
  have hk0 := hk.ne'
  have he : (1 + 3 / k) * S / 2 = (1 + 1 / k) * S / 2 + 2 * (S / (2 * k)) := by
    field_simp
    ring
  have h3 : SG + 2 * SD + 2 * ρ ≤ (1 + 3 / k) * S / 2 + 2 * ρ := by rw [he]; linarith
  have h4 : SD + ρ ≤ S / (2 * k) + ρ := by linarith
  have h5 := mul_le_mul_of_nonneg_left h3 hc
  have h6 := mul_le_mul_of_nonneg_left h4 (by linarith : (0 : ℝ) ≤ 6 * R)
  exact ⟨by linarith, by linarith⟩

/-- **The gate sample budgets from branch certificates**: on any mesh, the branch budgets
`ζ + 2 ((1 + 3/k)(E₊ + E₋)/2) ≤ ε/(2000 ḡ)` and `6 R' (E₊ + E₋)/(2k) ≤ ν'` give the sample
budgets `ζ + 2 (ΔG + 2ΔD) ≤ ε/(2000 ḡ)` and `6 R' ΔD ≤ ν'` of the time-dependent gate endpoints
(`R'`, `ν'` the radius and precision of the formal solver at `2ḡ`). -/
theorem gate_budgets_of_branch {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → V →L[ℂ] V) (Gt : Fin M → V →L[ℂ] V)
    (hreg : RepresentedSampleODE.RegularPieces t G) {gbar ε ζ k : ℝ} (hg : 1 ≤ gbar)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hk : 0 < k)
    (h1 : ζ + 2 * ((1 + 3 / k) * branchSum t G Gt k / 2) ≤ ε / (2000 * gbar))
    (h2 : 6 * TimeDependentODE.radius (2 * gbar) ε * (branchSum t G Gt k / (2 * k)) ≤
      TimeDependentODE.precision (2 * gbar) ε) :
    ζ + 2 * (sampleErr t G Gt + 2 * dissErr t G Gt) ≤ ε / (2000 * gbar) ∧
      6 * TimeDependentODE.radius (2 * gbar) ε * dissErr t G Gt ≤
        TimeDependentODE.precision (2 * gbar) ε := by
  have hR : 0 ≤ TimeDependentODE.radius (2 * gbar) ε :=
    ImprovedODEQueryBudget.radius_nonneg (2 * (2 * gbar)) (ε / 2) (by linarith) (by linarith)
      (by linarith)
  have hG := sampleErr_le_branchSum hmesh G Gt hreg hk
  have hD := dissErr_le_branchSum hmesh G Gt hreg hk
  have hk0 := hk.ne'
  have he : (1 + 3 / k) * branchSum t G Gt k / 2 =
      (1 + 1 / k) * branchSum t G Gt k / 2 + 2 * (branchSum t G Gt k / (2 * k)) := by
    field_simp
    ring
  refine ⟨by linarith, ?_⟩
  have h3 := mul_le_mul_of_nonneg_left hD
    (by linarith : (0 : ℝ) ≤ 6 * TimeDependentODE.radius (2 * gbar) ε)
  linarith

end Integrated

/-! ### The native time-dependent samples -/

section Native

open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Set
open SparseHamiltonian.GeneralSourceExtensions TimeDependentExtensions
open SparseHamiltonian.MeshCertificateODE (sampleErr dissErr)

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- `E₊ + E₋` of the samples `D.matrix (x, r)` of time-indexed native access, the samples of
`Mesh.sampleError` and `RepresentedSampleODE.dissipativeError`. -/
def sampleBranchError (D : Data (X × Fin M) n Z s) (x : X) (t : ℕ → ℝ)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (k : ℝ) : ℝ :=
  branchSum t G (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) k

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem sampleError_eq_sampleErr (D : Data (X × Fin M) n Z s) (x : X) (t : ℕ → ℝ)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    Mesh.sampleError D x t G =
      sampleErr t G (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) := rfl

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem dissipativeError_eq_dissErr (D : Data (X × Fin M) n Z s) (x : X) (t : ℕ → ℝ)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    RepresentedSampleODE.dissipativeError D x t G =
      dissErr t G (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) := rfl

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **The budgets of `ode:thm:time` from branch certificates**: the branch budgets
`ζ + c_q ((1 + 3/k)(E₊ + E₋)/2 + 2 ΔR) ≤ ε/(2000 ḡ)` and `6 R ((E₊ + E₋)/(2k) + ΔR) ≤ ν` give the
budgets `ζ + c_q (ΔG + 2ΔD + 2ΔR) ≤ ε/(2000 ḡ)` and `6 R (ΔD + ΔR) ≤ ν` of `ode_thm_time`, with the
same refinement error `ΔR` and the radius `R` and precision `ν` of the formal solver. -/
theorem time_budgets_of_branch (D : Data (X × Fin M) n Z s) (x : X) {t : ℕ → ℝ} {T : ℝ}
    (hmesh : IsMesh t M T) (N : ℕ) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hreg : RepresentedSampleODE.RegularPieces t G) {gbar cq ε ζ k : ℝ} (hg : 1 ≤ gbar)
    (hcq : 1 ≤ cq) (hε : 0 < ε) (hε1 : ε ≤ 1) (hk : 0 < k)
    (h1 : ζ + cq * ((1 + 3 / k) * sampleBranchError D x t G k / 2 +
        2 * Mesh.refinementError D t T N) ≤ ε / (2000 * gbar))
    (h2 : 6 * TimeDependentODE.radius (cq * gbar) ε *
        (sampleBranchError D x t G k / (2 * k) + Mesh.refinementError D t T N) ≤
      TimeDependentODE.precision (cq * gbar) ε) :
    ζ + cq * (Mesh.sampleError D x t G + 2 * RepresentedSampleODE.dissipativeError D x t G +
        2 * Mesh.refinementError D t T N) ≤ ε / (2000 * gbar) ∧
      6 * TimeDependentODE.radius (cq * gbar) ε *
          (RepresentedSampleODE.dissipativeError D x t G + Mesh.refinementError D t T N) ≤
        TimeDependentODE.precision (cq * gbar) ε := by
  have hR : 0 ≤ TimeDependentODE.radius (cq * gbar) ε :=
    ImprovedODEQueryBudget.radius_nonneg (2 * (cq * gbar)) (ε / 2) (by nlinarith) (by linarith)
      (by linarith)
  have hG : Mesh.sampleError D x t G ≤ (1 + 1 / k) * sampleBranchError D x t G k / 2 :=
    sampleErr_le_branchSum hmesh G (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r)))
      hreg hk
  have hD : RepresentedSampleODE.dissipativeError D x t G ≤
      sampleBranchError D x t G k / (2 * k) :=
    dissErr_le_branchSum hmesh G (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r)))
      hreg hk
  exact budgets_of_branch hk (by linarith) hR hG hD h1 h2

end Native

/-! ### Theorem `ode:thm:time` from branch certificates -/

section Time

open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Set
open SparseHamiltonian.GeneralSourceExtensions
open scoped InnerProduct InnerProductSpace

set_option maxHeartbeats 16000000 in
/-- **Theorem `ode:thm:time` from branch certificates.** For the protocol of `ode_thm_time`
(chosen from the public data before the instance): the guarantee of `ode_thm_time`, and the same
conclusions and counts on every instance whose two sampling budgets are replaced by budgets on the
integrated branch errors `E_± = ∑_r ∫ ‖K_{±k}(G_r(u) - G̃_r)‖` of the same represented samples
`G̃_r = D.matrix (x, r)` at a branch frequency `kb > 0` of the certificate
(`sampleBranchError = E₊ + E₋`): `ζ + c_q ((1 + 3/kb)(E₊ + E₋)/2 + 2 ΔR) ≤ ε/(2000 ḡ)` and
`6 R ((E₊ + E₋)/(2 kb) + ΔR) ≤ ν`, `R`, `ν` the radius and precision of the formal solver and `ΔR`
the refinement error of `ode_thm_time` (`time_budgets_of_branch`). The represented samples may be
non-accretive. -/
theorem ode_thm_time_branch :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s M : ℕ} (D : Data (X × Fin M) n Z s), 0 < M →
        ∀ (t : ℕ → ℝ) (N : ℕ), 0 < N →
        ∀ (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ),
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 1 ≤ gbar → 1 ≤ cq → 0 < ε → ε ≤ 1 →
        TimeDependentExtensions.IsMesh t M T →
        8 * s * ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T) ≤ N →
        3 * (Real.sqrt (2 * (s : ℝ)) *
          ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
          TimeDependentODE.precision (cq * gbar) ε * (N : ℝ) ^ 2 →
        (∀ i, v i ∈ Icc 0 T) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        ∀ (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))), (∀ x, IsUnitary (Pw x)) →
        ∀ (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
        (∀ x a, IsUnitary (J x a)) →
        ∀ seed : EuclideanSpace ℂ n, ‖seed‖ = 1 →
        ∃ (d : ℕ) (A : ODERepeatProtocol.Protocol
            (MeshOracles.actualOracle (ι := TimeDependentODE.Index D T (cq * gbar) ε) D m N d Pw J)
            (EuclideanSpace ℂ n)),
          (∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
            (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
            (bv : Fin m → EuclideanSpace ℂ n)
            (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces t G →
            RepresentedSampleODE.MildSolution t T b sol U →
            formal_classicalPropagator G t T U →
            GeneralSourceODE.Compiled.WeightPrep (Pw x) (GeneralSourceODE.sources (sol 0) bv ω) →
            (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
            (∀ i, ω i ≠ 0 → bv i ≠ 0 →
              J x (some i) seed = ODEStateNormalization.unitDirection (bv i)) →
            ODESourceBranches.mass (GeneralSourceODE.sources (sol 0) bv ω) ≤
              cq * Mesh.meshScale sol b t →
            ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
                ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * Mesh.meshScale sol b t →
            sol T ≠ 0 →
            Mesh.meshScale sol b t ≤ gbar * ‖sol T‖ →
            ζ + cq * (Mesh.sampleError D x t G + 2 * RepresentedSampleODE.dissipativeError D x t G +
                2 * Mesh.refinementError D t T N) ≤ ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (cq * gbar) ε *
                (RepresentedSampleODE.dissipativeError D x t G + Mesh.refinementError D t T N) ≤
              TimeDependentODE.precision (cq * gbar) ε →
            HeraldedOutput A x (ODEStateNormalization.unitDirection (sol T)) ε ∧
            (A.worstCost GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤
              C * (cq * gbar) * (Real.sqrt s * (T * etaH + T * etaD *
                  Real.log (40000 * cq * gbar / ε)) +
                Real.sqrt (s * (T * etaH + T * etaD * Real.log (40000 * cq * gbar / ε)) *
                  Real.log (40000 * cq * gbar / ε)) + Real.log (40000 * cq * gbar / ε)) ∧
            (A.worstCost GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ C * (cq * gbar)) ∧
          ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
            (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
            (bv : Fin m → EuclideanSpace ℂ n)
            (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ kb : ℝ), 0 < kb →
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces t G →
            RepresentedSampleODE.MildSolution t T b sol U →
            formal_classicalPropagator G t T U →
            GeneralSourceODE.Compiled.WeightPrep (Pw x) (GeneralSourceODE.sources (sol 0) bv ω) →
            (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
            (∀ i, ω i ≠ 0 → bv i ≠ 0 →
              J x (some i) seed = ODEStateNormalization.unitDirection (bv i)) →
            ODESourceBranches.mass (GeneralSourceODE.sources (sol 0) bv ω) ≤
              cq * Mesh.meshScale sol b t →
            ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
                ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * Mesh.meshScale sol b t →
            sol T ≠ 0 →
            Mesh.meshScale sol b t ≤ gbar * ‖sol T‖ →
            ζ + cq * ((1 + 3 / kb) * sampleBranchError D x t G kb / 2 +
                2 * Mesh.refinementError D t T N) ≤ ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (cq * gbar) ε *
                (sampleBranchError D x t G kb / (2 * kb) + Mesh.refinementError D t T N) ≤
              TimeDependentODE.precision (cq * gbar) ε →
            HeraldedOutput A x (ODEStateNormalization.unitDirection (sol T)) ε ∧
            (A.worstCost GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤
              C * (cq * gbar) * (Real.sqrt s * (T * etaH + T * etaD *
                  Real.log (40000 * cq * gbar / ε)) +
                Real.sqrt (s * (T * etaH + T * etaD * Real.log (40000 * cq * gbar / ε)) *
                  Real.log (40000 * cq * gbar / ε)) + Real.log (40000 * cq * gbar / ε)) ∧
            (A.worstCost GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ C * (cq * gbar) := by
  obtain ⟨C, hC, h⟩ := ode_thm_time.{u, v, w}
  refine ⟨C, hC, ?_⟩
  intro X n Z _ _ _ _ _ s M D hM t N hN etaH etaD T gbar cq ε m v ω hH hDiss hT hg hcq hε hεOne
    hmesh hClock hCayley hv hrH hcH hrD hcD Pw hPw J hJ seed hSeed
  obtain ⟨d, A, hA⟩ := h D hM t N hN etaH etaD T gbar cq ε v ω hH hDiss hT hg hcq hε hεOne hmesh
    hClock hCayley hv hrH hcH hrD hcD Pw hPw J hJ seed hSeed
  refine ⟨d, A, hA, fun x G b sol bv U ζ kb hkb hG hreg hsol hUm hW hL0 hL hMass hInt hTarget hB
    hB1 hB2 => ?_⟩
  obtain ⟨c1, c2⟩ := time_budgets_of_branch D x hmesh N G hreg hg hcq hε hεOne hkb hB1 hB2
  exact hA x G b sol bv U ζ hG hreg hsol hUm hW hL0 hL hMass hInt hTarget hB c1 c2

set_option maxHeartbeats 16000000 in
/-- **Theorem `ode:thm:time`, approximate source preparations, from branch certificates**: for
the protocol of `ode_thm_time_approx`, its guarantee and the same conclusions on every instance
with the sampling budgets on the branch errors, as in `ode_thm_time_branch`. -/
theorem ode_thm_time_approx_branch :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s M : ℕ} (D : Data (X × Fin M) n Z s), 0 < M →
        ∀ (t : ℕ → ℝ) (N : ℕ), 0 < N →
        ∀ (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ),
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 1 ≤ gbar → 1 ≤ cq → 0 < ε → ε ≤ 1 →
        TimeDependentExtensions.IsMesh t M T →
        8 * s * ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T) ≤ N →
        3 * (Real.sqrt (2 * (s : ℝ)) *
          ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
          TimeDependentODE.precision (cq * gbar) ε * (N : ℝ) ^ 2 →
        (∀ i, v i ∈ Icc 0 T) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        ∀ {W : Type} [Fintype W] [DecidableEq W] (w₀ : W)
          (Pw : X → CleanWorkODE.LabelW m W →L[ℂ] CleanWorkODE.LabelW m W),
        (∀ x, IsUnitary (Pw x)) →
        ∀ (J : X → CleanWorkODE.LoadW m n W →L[ℂ] CleanWorkODE.LoadW m n W),
        (∀ x, IsUnitary (J x)) →
        ∀ seed : EuclideanSpace ℂ n, ‖seed‖ = 1 →
        ∃ (d : ℕ) (A : ODERepeatProtocol.Protocol
            (CleanWorkODE.actualOracleW (ι := TimeDependentODE.Index D T (cq * gbar) ε) D m N d
              Pw J)
            (EuclideanSpace ℂ n)),
          (∀ (x : X) (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
            (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (δ : ℝ)
            (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
            (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
            (bv : Fin m → EuclideanSpace ℂ n)
            (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
            IsUnitary P → (∀ a, IsUnitary (L a)) → 0 ≤ δ →
            cleanInputError w₀ (Pw x) P δ →
            cleanInputError w₀ (J x) (CleanWorkODE.ctrlL L) δ →
            60 * (cq * gbar) * δ ≤ 1 / 400 → 60 * (cq * gbar) * δ ≤ ε / 20 →
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces t G →
            RepresentedSampleODE.MildSolution t T b sol U →
            formal_classicalPropagator G t T U →
            GeneralSourceODE.Compiled.WeightPrep P (GeneralSourceODE.sources (sol 0) bv ω) →
            (sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0)) →
            (∀ i, ω i ≠ 0 → bv i ≠ 0 →
              L (some i) seed = ODEStateNormalization.unitDirection (bv i)) →
            ODESourceBranches.mass (GeneralSourceODE.sources (sol 0) bv ω) ≤
              cq * Mesh.meshScale sol b t →
            ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
                ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * Mesh.meshScale sol b t →
            sol T ≠ 0 →
            Mesh.meshScale sol b t ≤ gbar * ‖sol T‖ →
            ζ + cq * (Mesh.sampleError D x t G + 2 * RepresentedSampleODE.dissipativeError D x t G +
                2 * Mesh.refinementError D t T N) ≤ ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (cq * gbar) ε *
                (RepresentedSampleODE.dissipativeError D x t G + Mesh.refinementError D t T N) ≤
              TimeDependentODE.precision (cq * gbar) ε →
            HeraldedOutput A x (ODEStateNormalization.unitDirection (sol T)) ε ∧
            (A.worstCost GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤
              C * (cq * gbar) * (Real.sqrt s * (T * etaH + T * etaD *
                  Real.log (40000 * cq * gbar / ε)) +
                Real.sqrt (s * (T * etaH + T * etaD * Real.log (40000 * cq * gbar / ε)) *
                  Real.log (40000 * cq * gbar / ε)) + Real.log (40000 * cq * gbar / ε)) ∧
            (A.worstCost GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ C * (cq * gbar)) ∧
          ∀ (x : X) (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
            (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (δ : ℝ)
            (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
            (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
            (bv : Fin m → EuclideanSpace ℂ n)
            (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ kb : ℝ), 0 < kb →
            IsUnitary P → (∀ a, IsUnitary (L a)) → 0 ≤ δ →
            cleanInputError w₀ (Pw x) P δ →
            cleanInputError w₀ (J x) (CleanWorkODE.ctrlL L) δ →
            60 * (cq * gbar) * δ ≤ 1 / 400 → 60 * (cq * gbar) * δ ≤ ε / 20 →
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces t G →
            RepresentedSampleODE.MildSolution t T b sol U →
            formal_classicalPropagator G t T U →
            GeneralSourceODE.Compiled.WeightPrep P (GeneralSourceODE.sources (sol 0) bv ω) →
            (sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0)) →
            (∀ i, ω i ≠ 0 → bv i ≠ 0 →
              L (some i) seed = ODEStateNormalization.unitDirection (bv i)) →
            ODESourceBranches.mass (GeneralSourceODE.sources (sol 0) bv ω) ≤
              cq * Mesh.meshScale sol b t →
            ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
                ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * Mesh.meshScale sol b t →
            sol T ≠ 0 →
            Mesh.meshScale sol b t ≤ gbar * ‖sol T‖ →
            ζ + cq * ((1 + 3 / kb) * sampleBranchError D x t G kb / 2 +
                2 * Mesh.refinementError D t T N) ≤ ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (cq * gbar) ε *
                (sampleBranchError D x t G kb / (2 * kb) + Mesh.refinementError D t T N) ≤
              TimeDependentODE.precision (cq * gbar) ε →
            HeraldedOutput A x (ODEStateNormalization.unitDirection (sol T)) ε ∧
            (A.worstCost GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤
              C * (cq * gbar) * (Real.sqrt s * (T * etaH + T * etaD *
                  Real.log (40000 * cq * gbar / ε)) +
                Real.sqrt (s * (T * etaH + T * etaD * Real.log (40000 * cq * gbar / ε)) *
                  Real.log (40000 * cq * gbar / ε)) + Real.log (40000 * cq * gbar / ε)) ∧
            (A.worstCost GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ C * (cq * gbar) := by
  obtain ⟨C, hC, h⟩ := ode_thm_time_approx.{u, v, w}
  refine ⟨C, hC, ?_⟩
  intro X n Z _ _ _ _ _ s M D hM t N hN etaH etaD T gbar cq ε m v ω hH hDiss hT hg hcq hε hεOne
    hmesh hClock hCayley hv hrH hcH hrD hcD W _ _ w₀ Pw hPw J hJ seed hSeed
  obtain ⟨d, A, hA⟩ := h D hM t N hN etaH etaD T gbar cq ε v ω hH hDiss hT hg hcq hε hεOne hmesh
    hClock hCayley hv hrH hcH hrD hcD w₀ Pw hPw J hJ seed hSeed
  refine ⟨d, A, hA, fun x P L δ G b sol bv U ζ kb hkb hP hL hδ hPc hJc hδ1 hδε hG hreg hsol hUm hW
      hL0
    hL' hMass hInt hTarget hB hB1 hB2 => ?_⟩
  obtain ⟨c1, c2⟩ := time_budgets_of_branch D x hmesh N G hreg hg hcq hε hεOne hkb hB1 hB2
  exact hA x P L δ G b sol bv U ζ hP hL hδ hPc hJc hδ1 hδε hG hreg hsol hUm hW hL0 hL' hMass
    hInt hTarget hB c1 c2

set_option maxHeartbeats 16000000 in
/-- **Theorem `ode:thm:time` with the accuracy of every actual successful run, from branch
certificates** (exact source preparations): for the trial family of `ode_thm_time_actual`, its
guarantee and the same conclusions (heralded output, `TrialsClose`, `HistoriesClose`, counts) on
every instance with the sampling budgets on the branch errors, as in `ode_thm_time_branch`. -/
theorem ode_thm_time_actual_branch :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s M : ℕ} (D : Data (X × Fin M) n Z s), 0 < M →
        ∀ (t : ℕ → ℝ) (N : ℕ), 0 < N →
        ∀ (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ),
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 1 ≤ gbar → 1 ≤ cq → 0 < ε → ε ≤ 1 →
        TimeDependentExtensions.IsMesh t M T →
        8 * s * ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T) ≤ N →
        3 * (Real.sqrt (2 * (s : ℝ)) *
          ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
          TimeDependentODE.precision (cq * gbar) ε * (N : ℝ) ^ 2 →
        (∀ i, v i ∈ Icc 0 T) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        ∀ (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))), (∀ x, IsUnitary (Pw x)) →
        ∀ (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
        (∀ x a, IsUnitary (J x a)) →
        ∀ seed : EuclideanSpace ℂ n, ‖seed‖ = 1 →
        ∃ (d : ℕ) (tf : ODERepeatProtocol.TrialFamily
            (MeshOracles.actualOracle (ι := TimeDependentODE.Index D T (cq * gbar) ε) D m N d Pw J)
            (EuclideanSpace ℂ n)),
          (∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
            (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
            (bv : Fin m → EuclideanSpace ℂ n)
            (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces t G →
            RepresentedSampleODE.MildSolution t T b sol U →
            formal_classicalPropagator G t T U →
            GeneralSourceODE.Compiled.WeightPrep (Pw x) (GeneralSourceODE.sources (sol 0) bv ω) →
            (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
            (∀ i, ω i ≠ 0 → bv i ≠ 0 →
              J x (some i) seed = ODEStateNormalization.unitDirection (bv i)) →
            ODESourceBranches.mass (GeneralSourceODE.sources (sol 0) bv ω) ≤
              cq * Mesh.meshScale sol b t →
            ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
                ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * Mesh.meshScale sol b t →
            sol T ≠ 0 →
            Mesh.meshScale sol b t ≤ gbar * ‖sol T‖ →
            ζ + cq * (Mesh.sampleError D x t G + 2 * RepresentedSampleODE.dissipativeError D x t G +
                2 * Mesh.refinementError D t T N) ≤ ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (cq * gbar) ε *
                (RepresentedSampleODE.dissipativeError D x t G + Mesh.refinementError D t T N) ≤
              TimeDependentODE.precision (cq * gbar) ε →
            HeraldedOutput (ODERepeatProtocol.Protocol.repeatTrials tf 4) x
              (ODEStateNormalization.unitDirection (sol T)) ε ∧
            TrialsClose tf x (sol T) ε ∧ HistoriesClose tf x (sol T) ε ∧
            ((ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
              GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤
              C * (cq * gbar) * (Real.sqrt s * (T * etaH + T * etaD *
                  Real.log (40000 * cq * gbar / ε)) +
                Real.sqrt (s * (T * etaH + T * etaD * Real.log (40000 * cq * gbar / ε)) *
                  Real.log (40000 * cq * gbar / ε)) + Real.log (40000 * cq * gbar / ε)) ∧
            ((ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
              GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ C * (cq * gbar)) ∧
          ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
            (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
            (bv : Fin m → EuclideanSpace ℂ n)
            (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ kb : ℝ), 0 < kb →
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces t G →
            RepresentedSampleODE.MildSolution t T b sol U →
            formal_classicalPropagator G t T U →
            GeneralSourceODE.Compiled.WeightPrep (Pw x) (GeneralSourceODE.sources (sol 0) bv ω) →
            (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
            (∀ i, ω i ≠ 0 → bv i ≠ 0 →
              J x (some i) seed = ODEStateNormalization.unitDirection (bv i)) →
            ODESourceBranches.mass (GeneralSourceODE.sources (sol 0) bv ω) ≤
              cq * Mesh.meshScale sol b t →
            ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
                ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * Mesh.meshScale sol b t →
            sol T ≠ 0 →
            Mesh.meshScale sol b t ≤ gbar * ‖sol T‖ →
            ζ + cq * ((1 + 3 / kb) * sampleBranchError D x t G kb / 2 +
                2 * Mesh.refinementError D t T N) ≤ ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (cq * gbar) ε *
                (sampleBranchError D x t G kb / (2 * kb) + Mesh.refinementError D t T N) ≤
              TimeDependentODE.precision (cq * gbar) ε →
            HeraldedOutput (ODERepeatProtocol.Protocol.repeatTrials tf 4) x
              (ODEStateNormalization.unitDirection (sol T)) ε ∧
            TrialsClose tf x (sol T) ε ∧ HistoriesClose tf x (sol T) ε ∧
            ((ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
              GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤
              C * (cq * gbar) * (Real.sqrt s * (T * etaH + T * etaD *
                  Real.log (40000 * cq * gbar / ε)) +
                Real.sqrt (s * (T * etaH + T * etaD * Real.log (40000 * cq * gbar / ε)) *
                  Real.log (40000 * cq * gbar / ε)) + Real.log (40000 * cq * gbar / ε)) ∧
            ((ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
              GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ C * (cq * gbar) := by
  obtain ⟨C, hC, h⟩ := ode_thm_time_actual.{u, v, w}
  refine ⟨C, hC, ?_⟩
  intro X n Z _ _ _ _ _ s M D hM t N hN etaH etaD T gbar cq ε m v ω hH hDiss hT hg hcq hε hεOne
    hmesh hClock hCayley hv hrH hcH hrD hcD Pw hPw J hJ seed hSeed
  obtain ⟨d, tf, hA⟩ := h D hM t N hN etaH etaD T gbar cq ε v ω hH hDiss hT hg hcq hε hεOne hmesh
    hClock hCayley hv hrH hcH hrD hcD Pw hPw J hJ seed hSeed
  refine ⟨d, tf, hA, fun x G b sol bv U ζ kb hkb hG hreg hsol hUm hW hL0 hL hMass hInt hTarget hB
    hB1 hB2 => ?_⟩
  obtain ⟨c1, c2⟩ := time_budgets_of_branch D x hmesh N G hreg hg hcq hε hεOne hkb hB1 hB2
  exact hA x G b sol bv U ζ hG hreg hsol hUm hW hL0 hL hMass hInt hTarget hB c1 c2

end Time

/-! ### The time-dependent Theorem `ode:thm:gates` from branch certificates -/

section Gates

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit
  SparseHamiltonian.GateNative SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget
  SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GeneralSparseODE (GPubT markEmb padLift primsTG validEmb validLift
  norm_validEmb accretive_validLift)
open SparseHamiltonian.GeneralDecoderODE (BinDecode DW prepTD)
open SparseHamiltonian.GateBinaryODETime (PubT)
open SparseHamiltonian.ZeroTimeGateODE (BTPublicOK0 BTZeroCase)
open SparseHamiltonian.MeshCertificateODE (umesh quadSum quadAmp quadMass sampleErr dissErr liftV)
open SparseHamiltonian.GeneralSourceExtensions (Mesh.meshScale)
open GatePointerEncoding (wordValue)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

set_option maxHeartbeats 16000000 in
/-- **Theorem `ode:thm:gates` (time-dependent, manuscript certificates) from branch
certificates.** The public protocol `nprotocol …` of `ode_thm_gates_time_cert` with its gate,
qubit and call bounds, and on every instance whose sample budgets are replaced by budgets on the
integrated branch errors `E_± = ∑_r ∫ ‖K_{±kb}(G_r(u) - G̃_r)‖` of the same represented samples
`G̃_r = padLift D (x, r)` on the same uniform mesh, at a branch frequency `kb > 0` of the
certificate (`branchSum = E₊ + E₋`): `ζ + 2 ((1 + 3/kb)(E₊ + E₋)/2) ≤ ε/(2000 ḡ)` and
`6 R' (E₊ + E₋)/(2 kb) ≤ ν'`, `R'`, `ν'` the radius and precision of the formal solver
(`gate_budgets_of_branch`), the conclusions of `ode_thm_gates_time_cert`. The constants differ
from the paper's allocation; see the module docstring. -/
theorem ode_thm_gates_time_cert_branch :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (bd : ℕ) (c0 etaH etaD T gbar ε : ℝ) (m : ℕ)
        (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b),
        odeMeshG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε ≤ m →
        2 ^ k < 2 * N → formal_binaryDecoder D c0 → comp_bits b bd [c0, T, etaH, etaD] →
        ∀ (hg : formal_gbarOne gbar) {Zs : Type} [Fintype Zs] [DecidableEq Zs]
          (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
          (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)),
          (∀ i ∈ loadC, i.Valid) → (∀ i ∈ wpC, i.Valid) →
          0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 →
          (∀ j, ∀ i ∈ trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep N
            (fun _ => false) loadC wpC) j, i.Valid) ∧
          ((nprotocol ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep N
              (fun _ => false) loadC wpC) (2 * (2 * gbar))
              (one_le_two_mul (one_le_two_mul hg))).worstCost wGateN : ℝ) ≤
            C * gbar * (odeShape s T etaH etaD gbar ε *
                (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
              ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
          (odeQubitsTG (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m) Zs : ℝ) ≤
            C * (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
              C * Fintype.card Zs ∧
          (∀ c : Query → Bool,
            ((nprotocol ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep N
              (fun _ => false) loadC wpC) (2 * (2 * gbar))
                (one_le_two_mul (one_le_two_mul hg))).worstCost (wCallN c) : ℝ) ≤
            (if T = 0 ∨ etaH + etaD = 0 then 0 else
              C * gbar * odeShape s T etaH etaD gbar ε *
                ((if c Query.rowLocation then 1 else 0) +
                  (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))) +
            C * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
          ∀ x : X,
            (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaH ^ 2) →
            (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaH ^ 2) →
            (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaD ^ 2) →
            (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaD ^ 2) →
            ∀ (Jl : Bool × (Fin m → Bool) → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
              (Wp : Matrix (Cfg (Fin (m + 1))) (Cfg (Fin (m + 1))) ℂ)
              (G : Fin (2 ^ m) → ℝ → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
              (bf : Fin (2 ^ m) → ℝ → Reg (Fin k) ℂ) (sol : ℝ → Reg (Fin k) ℂ)
              (bs : ℕ → Reg (Fin k) ℂ) (U : ℝ → Reg (Fin k) ℂ → ℝ → Reg (Fin k) ℂ) (ζ ζs kb : ℝ),
            0 < kb → 0 ≤ ζs →
            ApproxOn CleanX (nrun (primsTG D x) loadC) (liftB (loadIdeal Jl)) ζs →
            ApproxOn CleanX (nrun (primsTG D x) wpC) (liftB (matOp Wp)) ζs →
            ζs ≤ ImprovedODEQueryBudget.precision gbar ε →
            (∀ c, OracleCircuit.IsUnitary (Jl c)) → Wp.conjTranspose * Wp = 1 →
            Wp * Wp.conjTranspose = 1 →
            (∀ w : Cfg (Fin (m + 1)), Wp w (fun _ => false) =
              ((quadAmp T m (sol 0) bs (w 0, Fin.tail w) : ℝ) : ℂ)) →
            (sol 0 ≠ 0 → Jl (false, fun _ => false) (seedV (S := Fin k)) =
              ODEStateNormalization.unitDirection (sol 0)) →
            (∀ w : Fin m → Bool, bs (wordValue w) ≠ 0 → Jl (true, w) (seedV (S := Fin k)) =
              ODEStateNormalization.unitDirection (bs (wordValue w))) →
            (∀ r : Fin (2 ^ m), ∀ u ∈ Set.Icc (umesh T (2 ^ m) r) (umesh T (2 ^ m) ((r : ℕ) + 1)),
              TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces (umesh T (2 ^ m)) G →
            RepresentedSampleODE.MildSolution (umesh T (2 ^ m)) T bf sol U →
            formal_classicalPropagator G (umesh T (2 ^ m)) T U →
            sol T ≠ 0 →
            Mesh.meshScale sol bf (umesh T (2 ^ m)) ≤ gbar * ‖sol T‖ →
            quadMass T m (sol 0) bs ≤ 2 * Mesh.meshScale sol bf (umesh T (2 ^ m)) →
            ‖sol T - quadSum T (2 ^ m) U (sol 0) bs‖ ≤ ζ * Mesh.meshScale sol bf (umesh T (2 ^ m)) →
            ζ + 2 * ((1 + 3 / kb) *
                branchSum (umesh T (2 ^ m)) G (fun r => padLift D (x, r)) kb / 2) ≤
              ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (2 * gbar) ε *
                (branchSum (umesh T (2 ^ m)) G (fun r => padLift D (x, r)) kb / (2 * kb)) ≤
              TimeDependentODE.precision (2 * gbar) ε →
            HeraldedOutput (nprotocol ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε
                m).prep N (fun _ => false) loadC wpC) (2 * (2 * gbar))
                (one_le_two_mul (one_le_two_mul hg)))
              (primsTG D x) (ODEStateNormalization.unitDirection
                (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (sol T))) ε ∧
            ∀ j : ℕ, ((goodN)†) (nrun (primsTG D x)
                (trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep N
                  (fun _ => false) loadC wpC) j) sN) ≠ 0 →
              ∃ ω : ℂ, ‖ω‖ = 1 ∧
                ‖ω • ODEStateNormalization.unitDirection (((goodN)†)
                    (nrun (primsTG D x) (trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T
                      (2 * gbar) ε m).prep N (fun _ => false) loadC wpC) j) sN)) -
                  ODEStateNormalization.unitDirection
                    (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (sol T))‖ ≤ ε := by
  obtain ⟨C, hC, h⟩ := ode_thm_gates_time_cert.{u}
  refine ⟨C, hC, ?_⟩
  intro X N s k b bd c0 etaH etaD T gbar ε m D hm hk hF hbits hg Zs _ _ loadC wpC hloadV hwpV hH
    hD hT hε hε2
  obtain ⟨h1, h2, h3, h4, h5⟩ := h bd c0 etaH etaD T gbar ε m D hm hk hF hbits hg loadC wpC hloadV
      hwpV hH hD hT
    hε hε2
  refine ⟨h1, h2, h3, h4, fun x hrH hcH hrD hcD Jl Wp G bf sol bs U ζ ζs kb hkb hζs hload hwp hacc
      hJl hWl hWr hWp
    hinit hforce hacc' hreg hmild hprop hne hscale hmass hsrc hbB hbrB => ?_⟩
  obtain ⟨c1, c2⟩ := gate_budgets_of_branch
    (MeshCertificateODE.isMesh_umesh hT (Nat.two_pow_pos m)) G (fun r => padLift D (x, r)) hreg
    hg hε hε2 hkb hbB hbrB
  exact h5 x hrH hcH hrD hcD Jl Wp G bf sol bs U ζ ζs hζs hload hwp hacc hJl hWl hWr hWp hinit
    hforce hacc' hreg hmild hprop hne hscale hmass hsrc c1 c2

set_option maxHeartbeats 16000000 in
/-- **Theorem `ode:thm:gates` (time-dependent, binary entry decoder, manuscript certificates)
from branch certificates**: the protocol and bounds of `ode_thm_gates_time_decoder_cert`, with the
sample budgets on the branch errors as in `ode_thm_gates_time_cert_branch`. -/
theorem ode_thm_gates_time_decoder_cert_branch :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b b' A : ℕ} (bd : ℕ) (c0 etaH etaD T gbar ε : ℝ) (m : ℕ)
        (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b) (dc : BinDecode b b' A),
        odeMeshG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε ≤ m →
        2 ^ k < 2 * N → BinaryEntryDecoding D dc c0 → comp_bits b' bd [c0, T, etaH, etaD] →
        ∀ (hg : formal_gbarOne gbar) {Zs : Type} [Fintype Zs] [DecidableEq Zs]
          (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
          (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)),
          (∀ i ∈ loadC, i.Valid) → (∀ i ∈ wpC, i.Valid) →
          0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 →
          (∀ j, ∀ i ∈ trialN (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N
            dc loadC wpC) j, i.Valid) ∧
          ((nprotocol (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
              loadC wpC) (2 * (2 * gbar)) (one_le_two_mul (one_le_two_mul hg))).worstCost
                wGateN : ℝ) ≤
            C * gbar * (odeShape s T etaH etaD gbar ε *
                ((bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
                  dc.cost) +
              ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
          (odeQubitsTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) dc Zs : ℝ) ≤
            C * (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
              C * Fintype.card Zs + C * dc.wires ∧
          (∀ c : Query → Bool,
            ((nprotocol (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
              loadC wpC) (2 * (2 * gbar)) (one_le_two_mul (one_le_two_mul hg))).worstCost
                (wCallN c) : ℝ) ≤
            (if T = 0 ∨ etaH + etaD = 0 then 0 else
              C * gbar * odeShape s T etaH etaD gbar ε *
                ((if c Query.rowLocation then 1 else 0) +
                  (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))) +
            C * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
          ∀ x : X,
            (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaH ^ 2) →
            (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaH ^ 2) →
            (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaD ^ 2) →
            (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaD ^ 2) →
            ∀ (Jl : Bool × (Fin m → Bool) → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
              (Wp : Matrix (Cfg (Fin (m + 1))) (Cfg (Fin (m + 1))) ℂ)
              (G : Fin (2 ^ m) → ℝ → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
              (bf : Fin (2 ^ m) → ℝ → Reg (Fin k) ℂ) (sol : ℝ → Reg (Fin k) ℂ)
              (bs : ℕ → Reg (Fin k) ℂ) (U : ℝ → Reg (Fin k) ℂ → ℝ → Reg (Fin k) ℂ) (ζ ζs kb : ℝ),
            0 < kb → 0 ≤ ζs →
            ApproxOn CleanX (nrun (primsTG D x) loadC) (liftB (loadIdeal Jl)) ζs →
            ApproxOn CleanX (nrun (primsTG D x) wpC) (liftB (matOp Wp)) ζs →
            ζs ≤ ImprovedODEQueryBudget.precision gbar ε →
            (∀ c, OracleCircuit.IsUnitary (Jl c)) → Wp.conjTranspose * Wp = 1 →
            Wp * Wp.conjTranspose = 1 →
            (∀ w : Cfg (Fin (m + 1)), Wp w (fun _ => false) =
              ((quadAmp T m (sol 0) bs (w 0, Fin.tail w) : ℝ) : ℂ)) →
            (sol 0 ≠ 0 → Jl (false, fun _ => false) (seedV (S := Fin k)) =
              ODEStateNormalization.unitDirection (sol 0)) →
            (∀ w : Fin m → Bool, bs (wordValue w) ≠ 0 → Jl (true, w) (seedV (S := Fin k)) =
              ODEStateNormalization.unitDirection (bs (wordValue w))) →
            (∀ r : Fin (2 ^ m), ∀ u ∈ Set.Icc (umesh T (2 ^ m) r) (umesh T (2 ^ m) ((r : ℕ) + 1)),
              TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces (umesh T (2 ^ m)) G →
            RepresentedSampleODE.MildSolution (umesh T (2 ^ m)) T bf sol U →
            formal_classicalPropagator G (umesh T (2 ^ m)) T U →
            sol T ≠ 0 →
            Mesh.meshScale sol bf (umesh T (2 ^ m)) ≤ gbar * ‖sol T‖ →
            quadMass T m (sol 0) bs ≤ 2 * Mesh.meshScale sol bf (umesh T (2 ^ m)) →
            ‖sol T - quadSum T (2 ^ m) U (sol 0) bs‖ ≤ ζ * Mesh.meshScale sol bf (umesh T (2 ^ m)) →
            ζ + 2 * ((1 + 3 / kb) *
                branchSum (umesh T (2 ^ m)) G (fun r => padLift D (x, r)) kb / 2) ≤
              ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (2 * gbar) ε *
                (branchSum (umesh T (2 ^ m)) G (fun r => padLift D (x, r)) kb / (2 * kb)) ≤
              TimeDependentODE.precision (2 * gbar) ε →
            HeraldedOutput (nprotocol (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar)
                ε m) N dc loadC wpC) (2 * (2 * gbar)) (one_le_two_mul (one_le_two_mul hg)))
              (primsTG D x) (ODEStateNormalization.unitDirection
                (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (sol T))) ε ∧
            ∀ j : ℕ, ((goodN)†) (nrun (primsTG D x)
                (trialN (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
                  loadC wpC) j) sN) ≠ 0 →
              ∃ ω : ℂ, ‖ω‖ = 1 ∧
                ‖ω • ODEStateNormalization.unitDirection (((goodN)†)
                    (nrun (primsTG D x) (trialN (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T
                      (2 * gbar) ε m) N dc loadC wpC) j) sN)) -
                  ODEStateNormalization.unitDirection
                    (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (sol T))‖ ≤ ε := by
  obtain ⟨C, hC, h⟩ := ode_thm_gates_time_decoder_cert.{u}
  refine ⟨C, hC, ?_⟩
  intro X N s k b b' A bd c0 etaH etaD T gbar ε m D dc hm hk hF hbits hg Zs _ _ loadC wpC hloadV
    hwpV hH hD hT hε hε2
  obtain ⟨h1, h2, h3, h4, h5⟩ := h bd c0 etaH etaD T gbar ε m D dc hm hk hF hbits hg loadC wpC
      hloadV hwpV hH hD hT
    hε hε2
  refine ⟨h1, h2, h3, h4, fun x hrH hcH hrD hcD Jl Wp G bf sol bs U ζ ζs kb hkb hζs hload hwp hacc
      hJl hWl hWr hWp
    hinit hforce hacc' hreg hmild hprop hne hscale hmass hsrc hbB hbrB => ?_⟩
  obtain ⟨c1, c2⟩ := gate_budgets_of_branch
    (MeshCertificateODE.isMesh_umesh hT (Nat.two_pow_pos m)) G (fun r => padLift D (x, r)) hreg
    hg hε hε2 hkb hbB hbrB
  exact h5 x hrH hcH hrD hcD Jl Wp G bf sol bs U ζ ζs hζs hload hwp hacc hJl hWl hWr hWp hinit
    hforce hacc' hreg hmild hprop hne hscale hmass hsrc c1 c2

set_option maxHeartbeats 16000000 in
/-- **`ode_thm_gates_time_cert_valid` from branch certificates** (problems on `ℂ^N`): the same
protocol and conclusions, with the sample budgets on the branch errors of the represented samples
`D.matrix (x, r)` on `ℂ^N` as in `ode_thm_gates_time_cert_branch`. -/
theorem ode_thm_gates_time_cert_valid_branch {X : Type u} {N s k b : ℕ} (bd : ℕ)
    (c0 etaH etaD T gbar ε : ℝ) (m : ℕ) (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b)
    (hm : odeMeshG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε ≤ m) (hk : 2 ^ k < 2 * N)
    (hF : formal_binaryDecoder D c0) (hbits : comp_bits b bd [c0, T, etaH, etaD])
    (hg : formal_gbarOne gbar) {Zs : Type} [Fintype Zs] [DecidableEq Zs]
    (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
    (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))
    (hloadV : ∀ i ∈ loadC, i.Valid) (hwpV : ∀ i ∈ wpC, i.Valid)
    (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hT : 0 ≤ T) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ etaD ^ 2)
    (Jl : Bool × (Fin m → Bool) → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
    (Wp : Matrix (Cfg (Fin (m + 1))) (Cfg (Fin (m + 1))) ℂ)
    (G : Fin (2 ^ m) → ℝ → EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (bf : Fin (2 ^ m) → ℝ → EuclideanSpace ℂ (Fin N)) (sol : ℝ → EuclideanSpace ℂ (Fin N))
    (bs : ℕ → EuclideanSpace ℂ (Fin N))
    (U : ℝ → EuclideanSpace ℂ (Fin N) → ℝ → EuclideanSpace ℂ (Fin N)) (ζ ζs : ℝ) (hζs0 : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsTG D x) loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsTG D x) wpC) (liftB (matOp Wp)) ζs)
    (hacc : ζs ≤ ImprovedODEQueryBudget.precision gbar ε)
    (hJl : ∀ c, OracleCircuit.IsUnitary (Jl c)) (hWl : Wp.conjTranspose * Wp = 1)
    (hWr : Wp * Wp.conjTranspose = 1)
    (hWp : ∀ w : Cfg (Fin (m + 1)), Wp w (fun _ => false) =
      ((quadAmp T m (sol 0) bs (w 0, Fin.tail w) : ℝ) : ℂ))
    (hinit : sol 0 ≠ 0 → Jl (false, fun _ => false) (seedV (S := Fin k)) =
      ODEStateNormalization.unitDirection (validEmb N k (sol 0)))
    (hforce : ∀ w : Fin m → Bool, bs (wordValue w) ≠ 0 → Jl (true, w) (seedV (S := Fin k)) =
      ODEStateNormalization.unitDirection (validEmb N k (bs (wordValue w))))
    (hacc' : ∀ r : Fin (2 ^ m), ∀ u ∈ Set.Icc (umesh T (2 ^ m) r) (umesh T (2 ^ m) ((r : ℕ) + 1)),
      TimeDependentODE.Accretive (G r u))
    (hreg : RepresentedSampleODE.RegularPieces (umesh T (2 ^ m)) G)
    (hmild : RepresentedSampleODE.MildSolution (umesh T (2 ^ m)) T bf sol U)
    (hprop : formal_classicalPropagator G (umesh T (2 ^ m)) T U) (hne : sol T ≠ 0)
    (hscale : Mesh.meshScale sol bf (umesh T (2 ^ m)) ≤ gbar * ‖sol T‖)
    (hmass : quadMass T m (sol 0) bs ≤ 2 * Mesh.meshScale sol bf (umesh T (2 ^ m)))
    (hsrc : ‖sol T - quadSum T (2 ^ m) U (sol 0) bs‖ ≤
      ζ * Mesh.meshScale sol bf (umesh T (2 ^ m)))
    (kb : ℝ) (hkb : 0 < kb)
    (hbudB : ζ + 2 * ((1 + 3 / kb) * branchSum (umesh T (2 ^ m)) G
        (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) kb / 2) ≤
      ε / (2000 * gbar))
    (hbranchB : 6 * TimeDependentODE.radius (2 * gbar) ε * (branchSum (umesh T (2 ^ m)) G
        (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) kb / (2 * kb)) ≤
      TimeDependentODE.precision (2 * gbar) ε) :
    HeraldedOutput (nprotocol ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep
        N (fun _ => false) loadC wpC) (2 * (2 * gbar)) (one_le_two_mul (one_le_two_mul hg)))
      (primsTG D x) (ODEStateNormalization.unitDirection
        (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (validEmb N k (sol T)))) ε ∧
    ∀ j : ℕ, ((goodN)†) (nrun (primsTG D x)
        (trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep N
          (fun _ => false) loadC wpC) j) sN) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • ODEStateNormalization.unitDirection (((goodN)†)
            (nrun (primsTG D x) (trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T
              (2 * gbar) ε m).prep N (fun _ => false) loadC wpC) j) sN)) -
          ODEStateNormalization.unitDirection
            (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (validEmb N k (sol T)))‖ ≤ ε := by
  obtain ⟨c1, c2⟩ := gate_budgets_of_branch
    (MeshCertificateODE.isMesh_umesh hT (Nat.two_pow_pos m)) G
    (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) hreg hg hε hε2 hkb hbudB hbranchB
  exact ode_thm_gates_time_cert_valid bd c0 etaH etaD T gbar ε m D hm hk hF hbits hg loadC wpC
    hloadV hwpV hH hD hT hε hε2 x hrH hcH hrD hcD Jl Wp G bf sol bs U ζ ζs hζs0 hload hwp hacc hJl
    hWl hWr hWp hinit hforce hacc' hreg hmild hprop hne hscale hmass hsrc c1 c2

set_option maxHeartbeats 16000000 in
/-- **`ode_thm_gates_time_decoder_cert_valid` from branch certificates** (problems on `ℂ^N`,
binary entry decoder). -/
theorem ode_thm_gates_time_decoder_cert_valid_branch {X : Type u} {N s k b b' A : ℕ} (bd : ℕ)
    (c0 etaH etaD T gbar ε : ℝ) (m : ℕ) (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b)
    (dc : BinDecode b b' A) (hm : odeMeshG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε ≤ m)
    (hk : 2 ^ k < 2 * N) (hF : BinaryEntryDecoding D dc c0)
    (hbits : comp_bits b' bd [c0, T, etaH, etaD]) (hg : formal_gbarOne gbar) {Zs : Type}
    [Fintype Zs] [DecidableEq Zs]
    (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
    (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))
    (hloadV : ∀ i ∈ loadC, i.Valid) (hwpV : ∀ i ∈ wpC, i.Valid)
    (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hT : 0 ≤ T) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ etaD ^ 2)
    (Jl : Bool × (Fin m → Bool) → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
    (Wp : Matrix (Cfg (Fin (m + 1))) (Cfg (Fin (m + 1))) ℂ)
    (G : Fin (2 ^ m) → ℝ → EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (bf : Fin (2 ^ m) → ℝ → EuclideanSpace ℂ (Fin N)) (sol : ℝ → EuclideanSpace ℂ (Fin N))
    (bs : ℕ → EuclideanSpace ℂ (Fin N))
    (U : ℝ → EuclideanSpace ℂ (Fin N) → ℝ → EuclideanSpace ℂ (Fin N)) (ζ ζs : ℝ) (hζs0 : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsTG D x) loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsTG D x) wpC) (liftB (matOp Wp)) ζs)
    (hacc : ζs ≤ ImprovedODEQueryBudget.precision gbar ε)
    (hJl : ∀ c, OracleCircuit.IsUnitary (Jl c)) (hWl : Wp.conjTranspose * Wp = 1)
    (hWr : Wp * Wp.conjTranspose = 1)
    (hWp : ∀ w : Cfg (Fin (m + 1)), Wp w (fun _ => false) =
      ((quadAmp T m (sol 0) bs (w 0, Fin.tail w) : ℝ) : ℂ))
    (hinit : sol 0 ≠ 0 → Jl (false, fun _ => false) (seedV (S := Fin k)) =
      ODEStateNormalization.unitDirection (validEmb N k (sol 0)))
    (hforce : ∀ w : Fin m → Bool, bs (wordValue w) ≠ 0 → Jl (true, w) (seedV (S := Fin k)) =
      ODEStateNormalization.unitDirection (validEmb N k (bs (wordValue w))))
    (hacc' : ∀ r : Fin (2 ^ m), ∀ u ∈ Set.Icc (umesh T (2 ^ m) r) (umesh T (2 ^ m) ((r : ℕ) + 1)),
      TimeDependentODE.Accretive (G r u))
    (hreg : RepresentedSampleODE.RegularPieces (umesh T (2 ^ m)) G)
    (hmild : RepresentedSampleODE.MildSolution (umesh T (2 ^ m)) T bf sol U)
    (hprop : formal_classicalPropagator G (umesh T (2 ^ m)) T U) (hne : sol T ≠ 0)
    (hscale : Mesh.meshScale sol bf (umesh T (2 ^ m)) ≤ gbar * ‖sol T‖)
    (hmass : quadMass T m (sol 0) bs ≤ 2 * Mesh.meshScale sol bf (umesh T (2 ^ m)))
    (hsrc : ‖sol T - quadSum T (2 ^ m) U (sol 0) bs‖ ≤
      ζ * Mesh.meshScale sol bf (umesh T (2 ^ m)))
    (kb : ℝ) (hkb : 0 < kb)
    (hbudB : ζ + 2 * ((1 + 3 / kb) * branchSum (umesh T (2 ^ m)) G
        (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) kb / 2) ≤
      ε / (2000 * gbar))
    (hbranchB : 6 * TimeDependentODE.radius (2 * gbar) ε * (branchSum (umesh T (2 ^ m)) G
        (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) kb / (2 * kb)) ≤
      TimeDependentODE.precision (2 * gbar) ε) :
    HeraldedOutput (nprotocol (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar)
        ε m) N dc loadC wpC) (2 * (2 * gbar)) (one_le_two_mul (one_le_two_mul hg)))
      (primsTG D x) (ODEStateNormalization.unitDirection
        (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (validEmb N k (sol T)))) ε ∧
    ∀ j : ℕ, ((goodN)†) (nrun (primsTG D x)
        (trialN (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
          loadC wpC) j) sN) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • ODEStateNormalization.unitDirection (((goodN)†)
            (nrun (primsTG D x) (trialN (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T
              (2 * gbar) ε m) N dc loadC wpC) j) sN)) -
          ODEStateNormalization.unitDirection
            (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (validEmb N k (sol T)))‖ ≤ ε := by
  obtain ⟨c1, c2⟩ := gate_budgets_of_branch
    (MeshCertificateODE.isMesh_umesh hT (Nat.two_pow_pos m)) G
    (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) hreg hg hε hε2 hkb hbudB hbranchB
  exact ode_thm_gates_time_decoder_cert_valid bd c0 etaH etaD T gbar ε m D dc hm hk hF hbits hg
    loadC wpC hloadV hwpV hH hD hT hε hε2 x hrH hcH hrD hcD Jl Wp G bf sol bs U ζ ζs hζs0 hload
    hwp hacc hJl hWl hWr hWp hinit hforce hacc' hreg hmild hprop hne hscale hmass hsrc c1 c2

end Gates

/-! ### Lemma `odel:lem:dyson` on the full class: coverage from branch certificates -/

section Dyson

open SparseHamiltonian ContinuousLinearMap NativeSparseBlockEncoding Set MeasureTheory
open TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (meshScale IsMeshPropagator)
open SparseHamiltonian.GeneralSourceODE (sources)
open SparseHamiltonian.GeneralSourceODE.Compiled (WeightPrep)
open DysonFullClass (FullValidAt FullValid cellError clipData opMatrix)
open scoped InnerProduct

variable {X n Z : Type} [Fintype n] [DecidableEq n] {s Ks M m : ℕ}

/-- `E₊ + E₋` of the cell samples `D.matrix (x, σ r)` (the samples of `DysonFullClass.cellError`). -/
def cellBranchError (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s) (x : X) (t : ℕ → ℝ)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (k : ℝ) : ℝ :=
  branchSum t G (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, σ r))) k

/-- **`E_G ≤ (1 + 1/k)(E₊ + E₋)/2` for the cell samples**. -/
theorem cellError_le_branch (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s) (x : X)
    {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hreg : RepresentedSampleODE.RegularPieces t G) {k : ℝ} (hk : 0 < k) :
    cellError σ D x t G ≤ (1 + 1 / k) * cellBranchError σ D x t G k / 2 :=
  sampleErr_le_branchSum hmesh G
    (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, σ r))) hreg hk

/-- **Coverage from a branch certificate on the clipped samples**: as
`DysonFullClass.fullValidAt_of_clipped`, with the certificate
`(1 + 1/kb)(E₊ + E₋)/2 ≤ log(1 + δ_m)` on the branches `±kb` (`kb > 0`) of the clipped represented
samples in place of `E ≤ log(1 + δ_m)`. -/
theorem fullValidAt_of_branch_clipped (D₀ : Data (X × Fin Ks) n Z s) (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T η g cq ε : ℝ) (hη : 0 < η) (hmesh : IsMesh t M T) (v : Fin m → ℝ)
    (ω : Fin m → ℂ) (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (x : X)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
    (bv : Fin m → EuclideanSpace ℂ n) (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n)
    (ζ δm : ℝ)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGint : RepresentedSampleODE.RegularPieces t G)
    (hmild : RepresentedSampleODE.MildSolution t T b sol U)
    (hU : IsMeshPropagator G t T U)
    (hW : WeightPrep P (sources (sol 0) bv ω))
    (hL₀ : sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0))
    (hLb : ∀ i, ω i ≠ 0 → bv i ≠ 0 → L (some i) seed = ODEStateNormalization.unitDirection (bv i))
    (hmass : ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t)
    (hsrc : ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
        ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t)
    (hsol : sol T ≠ 0) (hB : meshScale sol b t ≤ g * ‖sol T‖)
    (hcq : 0 ≤ cq) (hδm : 0 ≤ δm) (kb : ℝ) (hkb : 0 < kb)
    (hE : (1 + 1 / kb) * cellBranchError σ (clipData D₀ η hη) x t G kb / 2 ≤ Real.log (1 + δm))
    (hbud : ζ + cq * δm ≤ ε / (2000 * g)) :
    FullValidAt D₀ σ t T η g cq ε hη v ω P L seed x (sol T) :=
  DysonFullClass.fullValidAt_of_clipped D₀ σ t T η g cq ε hη v ω P L seed x G b sol bv U ζ δm hG
    hGint hmild hU hW hL₀ hLb hmass hsrc hsol hB hcq hδm
    ((cellError_le_branch σ (clipData D₀ η hη) x hmesh G hGint hkb).trans hE) hbud

/-- **Coverage from a branch certificate on the raw samples**: as
`DysonFullClass.fullValidAt_of_raw` (true entries at most `η`, `s`-sparse true pieces), with the
certificate `2 s ((1 + 1/kb)(E₊ + E₋)/2) ≤ log(1 + δ_m)` on the branches `±kb` (`kb > 0`) of the
unclipped represented samples `D₀.matrix (x, σ r)` in place of `2 s E_raw ≤ log(1 + δ_m)` (the
factor `2s` of the clipping step is kept). -/
theorem fullValidAt_of_branch_raw (D₀ : Data (X × Fin Ks) n Z s) (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T η g cq ε : ℝ) (hη : 0 < η) (hmesh : IsMesh t M T) (v : Fin m → ℝ)
    (ω : Fin m → ℂ) (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (x : X)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
    (bv : Fin m → EuclideanSpace ℂ n) (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n)
    (ζ δm : ℝ)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGint : RepresentedSampleODE.RegularPieces t G)
    (hmild : RepresentedSampleODE.MildSolution t T b sol U)
    (hU : IsMeshPropagator G t T U)
    (hW : WeightPrep P (sources (sol 0) bv ω))
    (hL₀ : sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0))
    (hLb : ∀ i, ω i ≠ 0 → bv i ≠ 0 → L (some i) seed = ODEStateNormalization.unitDirection (bv i))
    (hmass : ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t)
    (hsrc : ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
        ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t)
    (hsol : sol T ≠ 0) (hB : meshScale sol b t ≤ g * ‖sol T‖)
    (hent : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ∀ i j, ‖opMatrix (G r u) i j‖ ≤ η)
    (hrow : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ∀ i,
      (Finset.univ.filter fun j => opMatrix (G r u) i j ≠ 0).card ≤ s)
    (hcol : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ∀ j,
      (Finset.univ.filter fun i => opMatrix (G r u) i j ≠ 0).card ≤ s)
    (hcq : 0 ≤ cq) (hδm : 0 ≤ δm) (kb : ℝ) (hkb : 0 < kb)
    (hE : 2 * s * ((1 + 1 / kb) * cellBranchError σ D₀ x t G kb / 2) ≤ Real.log (1 + δm))
    (hbud : ζ + cq * δm ≤ ε / (2000 * g)) :
    FullValidAt D₀ σ t T η g cq ε hη v ω P L seed x (sol T) :=
  DysonFullClass.fullValidAt_of_raw D₀ σ t T η g cq ε hη hmesh v ω P L seed x G b sol bv U ζ δm
    hG hGint hmild hU hW hL₀ hLb hmass hsrc hsol hB hent hrow hcol hcq hδm
    ((mul_le_mul_of_nonneg_left (cellError_le_branch σ D₀ x hmesh G hGint hkb)
      (by positivity)).trans hE) hbud

/-- **The validity relation of the full-class solver from a raw branch certificate**: the
instance satisfies `FullValid` (with the supplied interfaces `P_w(x)`, `U_load(x)`), the relation on
which `DysonFullClass.full_single`, `full_fixed` and `full_no_uniform` give their guarantees. -/
theorem fullValid_of_branch_raw (D₀ : Data (X × Fin Ks) n Z s) (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T η g cq ε : ℝ) (hη : 0 < η) (hmesh : IsMesh t M T) (v : Fin m → ℝ)
    (ω : Fin m → ℂ) (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (x : X)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
    (bv : Fin m → EuclideanSpace ℂ n) (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n)
    (ζ δm : ℝ)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGint : RepresentedSampleODE.RegularPieces t G)
    (hmild : RepresentedSampleODE.MildSolution t T b sol U)
    (hU : IsMeshPropagator G t T U)
    (hW : WeightPrep (Pw x) (sources (sol 0) bv ω))
    (hL₀ : sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0))
    (hLb : ∀ i, ω i ≠ 0 → bv i ≠ 0 →
      J x (some i) seed = ODEStateNormalization.unitDirection (bv i))
    (hmass : ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t)
    (hsrc : ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
        ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t)
    (hsol : sol T ≠ 0) (hB : meshScale sol b t ≤ g * ‖sol T‖)
    (hent : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ∀ i j, ‖opMatrix (G r u) i j‖ ≤ η)
    (hrow : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ∀ i,
      (Finset.univ.filter fun j => opMatrix (G r u) i j ≠ 0).card ≤ s)
    (hcol : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ∀ j,
      (Finset.univ.filter fun i => opMatrix (G r u) i j ≠ 0).card ≤ s)
    (hcq : 0 ≤ cq) (hδm : 0 ≤ δm) (kb : ℝ) (hkb : 0 < kb)
    (hE : 2 * s * ((1 + 1 / kb) * cellBranchError σ D₀ x t G kb / 2) ≤ Real.log (1 + δm))
    (hbud : ζ + cq * δm ≤ ε / (2000 * g)) :
    FullValid D₀ σ t T η g cq ε hη v ω Pw J seed x (sol T) :=
  fullValidAt_of_branch_raw D₀ σ t T η g cq ε hη hmesh v ω (Pw x) (J x) seed x G b sol bv U ζ δm
    hG hGint hmild hU hW hL₀ hLb hmass hsrc hsol hB hent hrow hcol hcq hδm kb hkb hE hbud

end Dyson

/-! ### Test: a non-accretive represented sample -/

section Test

open ContinuousLinearMap MeasureTheory TimeDependentExtensions SparseHamiltonian
open SparseHamiltonian.ODEHermitianReduction (dissipativePart hamiltonianPart lchsHamiltonian)
open SparseHamiltonian.MeshCertificateODE (umesh umesh_succ_sub sampleErr dissErr)
open SparseHamiltonian.TimeDependentODE (Accretive)
open DysonFullClass.Examples (growC growC_not_accretive)
open scoped InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The true pieces of the test: `G_r(u) = 0` on every cell of the uniform mesh with `2^m` cells
(accretive). -/
def testPieces (m : ℕ) : Fin (2 ^ m) → ℝ → V →L[ℂ] V := fun _ _ => 0

/-- The represented samples of the test: `G̃_r = growC a = -a·1` on every cell (not accretive for
`a > 0`). -/
def testSamples (m : ℕ) (a : ℝ) : Fin (2 ^ m) → V →L[ℂ] V := fun _ => growC a

/-- The parts of `G - G̃ = 0 - growC a = a·1`: `D = a·1`, `H = 0`, `K_k = (k a)·1`. -/
theorem growC_parts (a k : ℝ) :
    dissipativePart ((0 : V →L[ℂ] V) - growC a) = (a : ℂ) • 1 ∧
      hamiltonianPart ((0 : V →L[ℂ] V) - growC a) = 0 ∧
      lchsHamiltonian ((0 : V →L[ℂ] V) - growC a) k = ((k * a : ℝ) : ℂ) • 1 := by
  have h0 : (0 : V →L[ℂ] V) - growC a = (a : ℂ) • 1 := by simp [growC]
  have hadj : ((a : ℂ) • (1 : V →L[ℂ] V))† = (a : ℂ) • 1 := by
    rw [map_smulₛₗ, Complex.conj_ofReal, ← ContinuousLinearMap.star_eq_adjoint, star_one]
  have hD : dissipativePart ((a : ℂ) • (1 : V →L[ℂ] V)) = (a : ℂ) • 1 := by
    simp only [dissipativePart, SparseHamiltonian.HermitianDilation.hermitianPart, hadj]
    module
  have hH : hamiltonianPart ((a : ℂ) • (1 : V →L[ℂ] V)) = 0 := by
    simp only [hamiltonianPart, hadj, sub_self, smul_zero]
  refine ⟨by rw [h0, hD], by rw [h0, hH], ?_⟩
  rw [h0]
  simp only [lchsHamiltonian, hD, hH, add_zero, smul_smul, Complex.ofReal_mul]

omit [CompleteSpace V] in
theorem norm_real_smul_one [Nontrivial V] (c : ℝ) : ‖(c : ℂ) • (1 : V →L[ℂ] V)‖ = |c| := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, norm_one, mul_one]

/-- The cells of the uniform mesh of `[0, T]` with `2^m` cells have total length `T`. -/
theorem umesh_sum_const (T c : ℝ) (m : ℕ) :
    ∑ r : Fin (2 ^ m), ∫ _u in umesh T (2 ^ m) r..umesh T (2 ^ m) ((r : ℕ) + 1), c = T * c := by
  simp only [intervalIntegral.integral_const, umesh_succ_sub, smul_eq_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h : ((2 ^ m : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- **The branch errors of the non-accretive sample**: true piece `0`, represented sample
`G̃ = growC a = -a·1` on the uniform mesh of `[0, T]`: `E₊ = E₋ = k a T`, `ΔD = a T`, `ΔG = a T`.
The dissipative bound `ΔD ≤ (E₊ + E₋)/(2k)` is attained. -/
theorem growC_values [Nontrivial V] {a k T : ℝ} (ha : 0 ≤ a) (hk : 0 < k) (m : ℕ) :
    branchErr (umesh T (2 ^ m)) (testPieces (V := V) m) (testSamples (V := V) m a) k =
        k * a * T ∧
      branchErr (umesh T (2 ^ m)) (testPieces (V := V) m) (testSamples (V := V) m a) (-k) =
        k * a * T ∧
      dissErr (umesh T (2 ^ m)) (testPieces (V := V) m) (testSamples (V := V) m a) = a * T ∧
      sampleErr (umesh T (2 ^ m)) (testPieces (V := V) m) (testSamples (V := V) m a) =
        a * T := by
  have hK : ∀ k' : ℝ, ‖lchsHamiltonian ((0 : V →L[ℂ] V) - growC a) k'‖ = |k' * a| := fun k' => by
    rw [(growC_parts a k').2.2, norm_real_smul_one]
  have hD : ‖dissipativePart ((0 : V →L[ℂ] V) - growC a)‖ = a := by
    rw [(growC_parts a 0).1, norm_real_smul_one, abs_of_nonneg ha]
  have hG : ‖(0 : V →L[ℂ] V) - growC a‖ = a := by
    rw [show (0 : V →L[ℂ] V) - growC a = (a : ℂ) • 1 by simp [growC], norm_real_smul_one,
      abs_of_nonneg ha]
  have hp : |k * a| = k * a := abs_of_nonneg (mul_nonneg hk.le ha)
  have hm : |-k * a| = k * a := by rw [abs_mul, abs_neg, abs_of_pos hk, abs_of_nonneg ha]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold branchErr testPieces testSamples
    simp only [hK, hp]
    rw [umesh_sum_const]
    ring
  · unfold branchErr testPieces testSamples
    simp only [hK, hm]
    rw [umesh_sum_const]
    ring
  · unfold dissErr testPieces testSamples
    simp only [hD]
    rw [umesh_sum_const]
    ring
  · unfold sampleErr testPieces testSamples
    simp only [hG]
    rw [umesh_sum_const]
    ring

/-- **A non-accretive represented sample is accepted by the branch interface**: for the true
piece `0` (accretive) and the represented sample `G̃ = -a·1` (`a > 0`, not accretive) on the
uniform mesh with `2^m` cells, the branch budgets of `ode_thm_gates_time_cert_branch` at any
`kb > 0` hold as soon as `ζ + 2 (kb + 3) a T ≤ ε/(2000 ḡ)` and `6 R' a T ≤ ν'`, and the conversion
`gate_budgets_of_branch` then gives the sample budgets of `ode_thm_gates_time_cert` for this
sample. -/
theorem nonaccretive_branch_accepted [Nontrivial V] {a kb T gbar ε ζ : ℝ} (ha : 0 < a)
    (hkb : 0 < kb) (hT : 0 ≤ T) (m : ℕ) (hg : 1 ≤ gbar) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (h1 : ζ + 2 * ((kb + 3) * a * T) ≤ ε / (2000 * gbar))
    (h2 : 6 * TimeDependentODE.radius (2 * gbar) ε * (a * T) ≤
      TimeDependentODE.precision (2 * gbar) ε) :
    (∀ (r : Fin (2 ^ m)) (u : ℝ), Accretive (testPieces (V := V) m r u)) ∧
      ¬ Accretive (growC (V := V) a) ∧
      ζ + 2 * ((1 + 3 / kb) * branchSum (umesh T (2 ^ m)) (testPieces (V := V) m)
          (testSamples (V := V) m a) kb / 2) ≤ ε / (2000 * gbar) ∧
      6 * TimeDependentODE.radius (2 * gbar) ε * (branchSum (umesh T (2 ^ m))
          (testPieces (V := V) m) (testSamples (V := V) m a) kb / (2 * kb)) ≤
        TimeDependentODE.precision (2 * gbar) ε ∧
      ζ + 2 * (sampleErr (umesh T (2 ^ m)) (testPieces (V := V) m) (testSamples (V := V) m a) +
          2 * dissErr (umesh T (2 ^ m)) (testPieces (V := V) m) (testSamples (V := V) m a)) ≤
        ε / (2000 * gbar) ∧
      6 * TimeDependentODE.radius (2 * gbar) ε *
          dissErr (umesh T (2 ^ m)) (testPieces (V := V) m) (testSamples (V := V) m a) ≤
        TimeDependentODE.precision (2 * gbar) ε := by
  obtain ⟨hp, hm, -, -⟩ := growC_values (V := V) (T := T) ha.le hkb m
  have hS : branchSum (umesh T (2 ^ m)) (testPieces (V := V) m) (testSamples (V := V) m a) kb =
      2 * (kb * a * T) := by
    unfold branchSum
    rw [hp, hm]
    ring
  have hk0 := hkb.ne'
  have hb1 : ζ + 2 * ((1 + 3 / kb) * branchSum (umesh T (2 ^ m)) (testPieces (V := V) m)
      (testSamples (V := V) m a) kb / 2) ≤ ε / (2000 * gbar) := by
    rw [hS]
    have he : (1 + 3 / kb) * (2 * (kb * a * T)) / 2 = (kb + 3) * a * T := by
      field_simp
    rw [he]
    exact h1
  have hb2 : 6 * TimeDependentODE.radius (2 * gbar) ε * (branchSum (umesh T (2 ^ m))
      (testPieces (V := V) m) (testSamples (V := V) m a) kb / (2 * kb)) ≤
      TimeDependentODE.precision (2 * gbar) ε := by
    rw [hS]
    have he : 2 * (kb * a * T) / (2 * kb) = a * T := by
      field_simp
    rw [he]
    exact h2
  have hreg : RepresentedSampleODE.RegularPieces (umesh T (2 ^ m))
      (testPieces (V := V) m) := fun _ => intervalIntegrable_const
  obtain ⟨c1, c2⟩ := gate_budgets_of_branch
    (MeshCertificateODE.isMesh_umesh hT (Nat.two_pow_pos m)) _ _ hreg hg hε hε2 hkb hb1 hb2
  exact ⟨fun _ _ => by intro v; simp [testPieces], growC_not_accretive ha, hb1, hb2, c1, c2⟩

end Test

end

end ManuscriptConformance
