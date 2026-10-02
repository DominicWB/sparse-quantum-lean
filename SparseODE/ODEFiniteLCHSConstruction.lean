import SparseODE.ODEWeightedLCHS

/-!
# Public finite LCHS tables from continuous-kernel estimates

This theorem constructs the finite frequency table accepted by the verified
actual-ODE circuit. The mesh and scalar coefficients depend only on the
kernel, public sparse-data scale, final time and requested precision. They
are independent of both the unknown matrix input and the selected duration.

The continuous truncated-integral approximation and kernel bounds remain
explicit analytic hypotheses. In particular this theorem does not assert
the still-unproved Gaussian representation or its tail estimate.

-/

namespace SparseHamiltonian.ODEFiniteLCHSConstruction

noncomputable section
open NativeSparseBlockEncoding ODEUniformQuadrature ODEWeightedLCHS
open scoped BigOperators Interval

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- The known Lipschitz envelope for every weighted native evolution. -/
def frequencyBudget (D : Data X n Z s) (T K M : ℝ) : ℝ :=
  K + M * T * ((s : ℝ) * D.scale)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem frequencyBudget_nonneg (D : Data X n Z s) (T K M : ℝ)
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hM : 0 ≤ M) :
    0 ≤ frequencyBudget D T K M := by
  exact add_nonneg hK
    (mul_nonneg (mul_nonneg hM hT) (mul_nonneg (Nat.cast_nonneg _) D.scale_pos.le))

/-- The mesh is computed before the unknown input and propagation duration.
The same cardinality controls the operator error and the coefficient mass. -/
def gridSize (D : Data X n Z s) (T K M g ε : ℝ) : ℕ :=
  meshSize (-ImprovedODEQueryBudget.radius g ε)
    (ImprovedODEQueryBudget.radius g ε)
    (max (frequencyBudget D T K M) K) (ImprovedODEQueryBudget.precision g ε)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- An explicit public frequency grid gives the previous finite-LCHS
predicate, simultaneously for every unknown input. The continuous kernel's
mass has a precision-sized reserve for its scalar quadrature error. -/
theorem public_table (D : Data X n Z s) (T K M g ε : ℝ)
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (f : ℝ → ℂ) (hf : Continuous f)
    (hLip : ∀ k l, ‖f k - f l‖ ≤ K * |k - l|)
    (hBound : ∀ k, ‖f k‖ ≤ M)
    (hMass : (∫ k in (-ImprovedODEQueryBudget.radius g ε)..
        (ImprovedODEQueryBudget.radius g ε), ‖f k‖) ≤
      3 - ImprovedODEQueryBudget.precision g ε)
    (hTruncated : ∀ (x : X) (u : ℝ), 0 ≤ u → u ≤ T →
      ‖(∫ k in (-ImprovedODEQueryBudget.radius g ε)..
          (ImprovedODEQueryBudget.radius g ε), nativeWeighted D x u f k) -
        NormedSpace.exp (u • ODEPublicSourceMesh.generator D x)‖ ≤
          ImprovedODEQueryBudget.precision g ε) :
    let R := ImprovedODEQueryBudget.radius g ε
    let N := gridSize D T K M g ε
    0 < N ∧
      (∀ i : Fin N, |node (-R) R N i| ≤ R) ∧
      ODECoherentLCU.coefficientMass (coefficient f (-R) R N) ≤ 3 ∧
      (∀ x : X, ODEActualPrimitiveEndpoint.FiniteLCHS D
        (node (-R) R N) (coefficient f (-R) R N) T g ε x) := by
  let R := ImprovedODEQueryBudget.radius g ε
  let ν := ImprovedODEQueryBudget.precision g ε
  let N := gridSize D T K M g ε
  let Y := X × Set.Icc (0 : ℝ) T
  let F : Y → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
    fun y => nativeWeighted D y.1 y.2.val f
  have hF : ∀ y : Y, Continuous (F y) :=
    fun y => native_weighted_continuous D y.1 y.2.val f hf
  have hFLip : ∀ (y : Y) (k l : ℝ),
      ‖F y k - F y l‖ ≤ frequencyBudget D T K M * |k - l| := by
    intro y k l
    exact native_weighted_error D y.1 T y.2.val f K M
      y.2.property.1 y.2.property.2 hK hM hLip hBound k l
  have hR : 0 ≤ R := ImprovedODEQueryBudget.radius_nonneg g ε hg hε hεOne
  have hν : 0 < ν := ImprovedODEQueryBudget.precision_pos g ε hg hε
  have hGrid := family_certificate F hF (frequencyBudget D T K M)
    (frequencyBudget_nonneg D T K M hT hK hM) hFLip
    f hf K hK hLip R ν hR hν
  change 0 < N ∧
    (∀ i : Fin N, |node (-R) R N i| ≤ R) ∧
    (∀ y : Y, ‖uniformSum (F y) (-R) R N - ∫ k in (-R)..R, F y k‖ ≤ ν) ∧
    ODECoherentLCU.coefficientMass (coefficient f (-R) R N) ≤
      (∫ k in (-R)..R, ‖f k‖) + ν at hGrid
  refine ⟨hGrid.1, hGrid.2.1, ?_, ?_⟩
  · have hm := hGrid.2.2.2
    change (∫ k in (-R)..R, ‖f k‖) ≤ 3 - ν at hMass
    linarith
  · intro x u hu huT
    have hQuadrature := hGrid.2.2.1 (x, ⟨u, hu, huT⟩)
    change ‖uniformSum (nativeWeighted D x u f) (-R) R N -
      ∫ k in (-R)..R, nativeWeighted D x u f k‖ ≤ ν at hQuadrature
    have hSum : ODENativeLCU.finiteSum D (node (-R) R N) (fun _ => u)
        (coefficient f (-R) R N) x =
        uniformSum (nativeWeighted D x u f) (-R) R N := by
      change (∑ i : Fin N, coefficient f (-R) R N i •
        nativeEvolution D x u (node (-R) R N i)) =
          uniformSum (nativeWeighted D x u f) (-R) R N
      exact weightedSum_eq_uniformSum f (nativeEvolution D x u) (-R) R N
    change ‖ODENativeLCU.finiteSum D (node (-R) R N) (fun _ => u)
      (coefficient f (-R) R N) x -
        NormedSpace.exp (u • ODEPublicSourceMesh.generator D x)‖ ≤ 2 * ν
    rw [hSum]
    calc
      _ ≤ ‖uniformSum (nativeWeighted D x u f) (-R) R N -
            ∫ k in (-R)..R, nativeWeighted D x u f k‖ +
          ‖(∫ k in (-R)..R, nativeWeighted D x u f k) -
            NormedSpace.exp (u • ODEPublicSourceMesh.generator D x)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ν + ν := add_le_add hQuadrature (hTruncated x u hu huT)
      _ = 2 * ν := by ring

end
end SparseHamiltonian.ODEFiniteLCHSConstruction
