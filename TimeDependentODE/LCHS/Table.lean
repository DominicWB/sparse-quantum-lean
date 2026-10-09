import TimeDependentODE.LCHS.Products

/-!
# A public Gaussian frequency table for contractive entire families

Let `F y : ℂ → V →L[ℂ] V`, indexed by an arbitrary label `y`, be entire and
contractive on the closed lower half-plane, with a common Lipschitz constant
`L` on the real frequency axis. With the public width `w = width g ε`, radius
`R = radius g ε` and precision `ν = precision g ε`:

* `weighted_lipschitz`: each Gaussian-weighted integrand `k ↦ kernel w k • F y k`
  is Lipschitz with constant `lipschitzConstant w + (exp 1 / π) * L`
  (`weightedLipschitz L g ε`);
* `gridSize`, `nodes`, `coefficients`: one uniform left-endpoint grid on
  `[-R, R]` and its Gaussian coefficients. They depend only on `L`, `g` and
  `ε`, never on the label `y`;
* `table_certificate`: the grid size is positive, every node lies in
  `[-R, R]`, the coefficient mass is at most `3`, and for every label
  `‖∑ i, coefficients i • F y (nodes i) - F y (-I)‖ ≤ 2 ν`.

The quadrature error comes from `ODEUniformQuadrature.family_certificate`
applied to the whole weighted family; the continuous error is the generic
truncated Gaussian LCHS estimate `truncated_error`; the coefficient mass uses
the released scalar Gaussian mass budget. This is the generic version of
`ODEFiniteLCHSConstruction.public_table` and
`ODEGaussianFiniteTable.public_table_from_dissipativity`.
-/

namespace SparseHamiltonian.TimeDependentODE.GaussianLCHS

noncomputable section
open scoped BigOperators Interval

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

omit [CompleteSpace V] in
/-- Gaussian weighting of a contractive family with real-axis Lipschitz
constant `L` gives a Lipschitz integrand with the explicit constant
`lipschitzConstant w + (exp 1 / π) * L`. -/
theorem weighted_lipschitz (F : ℂ → V →L[ℂ] V)
    (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1) (L : ℝ)
    (hLip : ∀ k l : ℝ, ‖F (k : ℂ) - F (l : ℂ)‖ ≤ L * |k - l|)
    (w : ℝ) (hw : 0 < w) (k l : ℝ) :
    ‖ODEGaussianKernel.kernel w k • F (k : ℂ) - ODEGaussianKernel.kernel w l • F (l : ℂ)‖ ≤
      (ODEGaussianKernel.lipschitzConstant w + (Real.exp 1 / Real.pi) * L) * |k - l| := by
  have hSplit : ODEGaussianKernel.kernel w k • F (k : ℂ) -
        ODEGaussianKernel.kernel w l • F (l : ℂ) =
      (ODEGaussianKernel.kernel w k - ODEGaussianKernel.kernel w l) • F (k : ℂ) +
        ODEGaussianKernel.kernel w l • (F (k : ℂ) - F (l : ℂ)) := by
    rw [sub_smul, smul_sub]
    abel
  rw [hSplit]
  calc
    _ ≤ ‖(ODEGaussianKernel.kernel w k - ODEGaussianKernel.kernel w l) • F (k : ℂ)‖ +
        ‖ODEGaussianKernel.kernel w l • (F (k : ℂ) - F (l : ℂ))‖ := norm_add_le _ _
    _ = ‖ODEGaussianKernel.kernel w k - ODEGaussianKernel.kernel w l‖ * ‖F (k : ℂ)‖ +
        ‖ODEGaussianKernel.kernel w l‖ * ‖F (k : ℂ) - F (l : ℂ)‖ := by
      rw [norm_smul, norm_smul]
    _ ≤ (ODEGaussianKernel.lipschitzConstant w * |k - l|) * 1 +
        (Real.exp 1 / Real.pi) * (L * |k - l|) := by
      apply add_le_add
      · exact mul_le_mul (ODEGaussianKernel.kernel_lipschitz w hw k l)
          (real_norm_le_one F hBound k) (norm_nonneg _)
          (mul_nonneg (ODEGaussianKernel.lipschitzConstant_nonneg w hw) (abs_nonneg _))
      · exact mul_le_mul (ODEGaussianKernel.norm_kernel_le w l hw) (hLip k l)
          (norm_nonneg _) (by positivity)
    _ = (ODEGaussianKernel.lipschitzConstant w + (Real.exp 1 / Real.pi) * L) * |k - l| := by
      ring

/-- Public Lipschitz envelope of every Gaussian-weighted integrand at the
public width `width g ε`, for a family with real-axis Lipschitz constant `L`. -/
def weightedLipschitz (L g ε : ℝ) : ℝ :=
  ODEGaussianKernel.lipschitzConstant (ODEGaussianParameters.width g ε) +
    (Real.exp 1 / Real.pi) * L

theorem weightedLipschitz_nonneg (L g ε : ℝ) (hL : 0 ≤ L)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    0 ≤ weightedLipschitz L g ε := by
  have hK := ODEGaussianKernel.lipschitzConstant_nonneg (ODEGaussianParameters.width g ε)
    (ODEGaussianParameters.width_pos g ε hg hε hεOne)
  unfold weightedLipschitz
  positivity

/-- Public grid size; depends only on `L`, `g`, `ε`. It is the uniform mesh
size for the larger of the weighted-family and the scalar-kernel Lipschitz
constants on `[-R, R]`, `R = radius g ε`, at precision `precision g ε`. -/
def gridSize (L g ε : ℝ) : ℕ :=
  ODEUniformQuadrature.meshSize (-ImprovedODEQueryBudget.radius g ε)
    (ImprovedODEQueryBudget.radius g ε)
    (max (weightedLipschitz L g ε)
      (ODEGaussianKernel.lipschitzConstant (ODEGaussianParameters.width g ε)))
    (ImprovedODEQueryBudget.precision g ε)

/-- Uniform left endpoints on `[-R, R]`, `R = radius g ε`. -/
def nodes (L g ε : ℝ) : Fin (gridSize L g ε) → ℝ :=
  ODEUniformQuadrature.node (-ImprovedODEQueryBudget.radius g ε)
    (ImprovedODEQueryBudget.radius g ε) (gridSize L g ε)

/-- Left-endpoint quadrature coefficients of the Gaussian kernel of width
`width g ε` on the public grid. -/
def coefficients (L g ε : ℝ) : Fin (gridSize L g ε) → ℂ :=
  ODEUniformQuadrature.coefficient (ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε))
    (-ImprovedODEQueryBudget.radius g ε) (ImprovedODEQueryBudget.radius g ε) (gridSize L g ε)

omit [CompleteSpace V] in
/-- The coefficient-weighted sum of the family at the nodes is the uniform
left-endpoint sum of its Gaussian-weighted integrand. -/
theorem table_sum_eq_uniformSum (F : ℂ → V →L[ℂ] V) (L g ε : ℝ) :
    (∑ i, coefficients L g ε i • F (nodes L g ε i : ℂ)) =
      ODEUniformQuadrature.uniformSum
        (fun k : ℝ => ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε) k • F (k : ℂ))
        (-ImprovedODEQueryBudget.radius g ε) (ImprovedODEQueryBudget.radius g ε)
        (gridSize L g ε) :=
  ODEUniformQuadrature.weightedSum_eq_uniformSum
    (ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε)) (fun k : ℝ => F (k : ℂ))
    (-ImprovedODEQueryBudget.radius g ε) (ImprovedODEQueryBudget.radius g ε) (gridSize L g ε)

/-- One public Gaussian table serves every member of a contractive entire
family with a common real-axis Lipschitz constant: positive size, nodes in
`[-R, R]`, coefficient mass at most `3`, and error at most `2 ν` at `-I`. -/
theorem table_certificate {Y : Type*} (F : Y → ℂ → V →L[ℂ] V)
    (hF : ∀ y z, AnalyticAt ℂ (F y) z) (hBound : ∀ y (z : ℂ), z.im ≤ 0 → ‖F y z‖ ≤ 1)
    (L : ℝ) (hL : 0 ≤ L) (hLip : ∀ y (k l : ℝ), ‖F y (k : ℂ) - F y (l : ℂ)‖ ≤ L * |k - l|)
    (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    0 < gridSize L g ε ∧
      (∀ i, |nodes L g ε i| ≤ ImprovedODEQueryBudget.radius g ε) ∧
      ODECoherentLCU.coefficientMass (coefficients L g ε) ≤ 3 ∧
      ∀ y, ‖(∑ i, coefficients L g ε i • F y (nodes L g ε i : ℂ)) - F y (-Complex.I)‖ ≤
        2 * ImprovedODEQueryBudget.precision g ε := by
  have hw : 0 < ODEGaussianParameters.width g ε :=
    ODEGaussianParameters.width_pos g ε hg hε hεOne
  have hR : 0 ≤ ImprovedODEQueryBudget.radius g ε :=
    ImprovedODEQueryBudget.radius_nonneg g ε hg hε hεOne
  have hν : 0 < ImprovedODEQueryBudget.precision g ε :=
    ImprovedODEQueryBudget.precision_pos g ε hg hε
  obtain ⟨hN, hNodes, hQuadrature, hMass⟩ := ODEUniformQuadrature.family_certificate
    (fun y (k : ℝ) =>
      ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε) k • F y (k : ℂ))
    (fun y => integrand_continuous (F y) (hF y) (ODEGaussianParameters.width g ε))
    (weightedLipschitz L g ε) (weightedLipschitz_nonneg L g ε hL hg hε hεOne)
    (fun y k l => weighted_lipschitz (F y) (hBound y) L (hLip y)
      (ODEGaussianParameters.width g ε) hw k l)
    (ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε))
    (ODEGaussianKernel.kernel_continuous (ODEGaussianParameters.width g ε))
    (ODEGaussianKernel.lipschitzConstant (ODEGaussianParameters.width g ε))
    (ODEGaussianKernel.lipschitzConstant_nonneg (ODEGaussianParameters.width g ε) hw)
    (ODEGaussianKernel.kernel_lipschitz (ODEGaussianParameters.width g ε) hw)
    (ImprovedODEQueryBudget.radius g ε) (ImprovedODEQueryBudget.precision g ε) hR hν
  refine ⟨hN, hNodes, ?_, ?_⟩
  · have hTable : ODECoherentLCU.coefficientMass (coefficients L g ε) ≤
        (∫ k in (-ImprovedODEQueryBudget.radius g ε)..(ImprovedODEQueryBudget.radius g ε),
          ‖ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε) k‖) +
          ImprovedODEQueryBudget.precision g ε := hMass
    have hBudget := ODEGaussianMass.kernel_mass_budget (ODEGaussianParameters.width g ε)
      (ImprovedODEQueryBudget.radius g ε) g ε hw hR hg hεOne
    linarith
  · intro y
    have hGrid : ‖ODEUniformQuadrature.uniformSum
          (fun k : ℝ =>
            ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε) k • F y (k : ℂ))
          (-ImprovedODEQueryBudget.radius g ε) (ImprovedODEQueryBudget.radius g ε)
          (gridSize L g ε) -
        ∫ k in (-ImprovedODEQueryBudget.radius g ε)..(ImprovedODEQueryBudget.radius g ε),
          ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε) k • F y (k : ℂ)‖ ≤
        ImprovedODEQueryBudget.precision g ε := hQuadrature y
    rw [table_sum_eq_uniformSum]
    calc
      _ ≤ ‖ODEUniformQuadrature.uniformSum
              (fun k : ℝ =>
                ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε) k • F y (k : ℂ))
              (-ImprovedODEQueryBudget.radius g ε) (ImprovedODEQueryBudget.radius g ε)
              (gridSize L g ε) -
            ∫ k in (-ImprovedODEQueryBudget.radius g ε)..(ImprovedODEQueryBudget.radius g ε),
              ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε) k • F y (k : ℂ)‖ +
          ‖(∫ k in (-ImprovedODEQueryBudget.radius g ε)..(ImprovedODEQueryBudget.radius g ε),
              ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε) k • F y (k : ℂ)) -
            F y (-Complex.I)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ImprovedODEQueryBudget.precision g ε + ImprovedODEQueryBudget.precision g ε :=
        add_le_add hGrid (truncated_error (F y) (hF y) (hBound y) g ε hg hε hεOne)
      _ = 2 * ImprovedODEQueryBudget.precision g ε := by ring

end
end SparseHamiltonian.TimeDependentODE.GaussianLCHS
