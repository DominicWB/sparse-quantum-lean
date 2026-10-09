import TimeDependentODE.Theorem
import TimeDependentODE.Continuous.Existence

/-!
# Admissible meshes for the time-dependent ODE solver

The public SELECT mesh conditions of `solver` hold for every mesh size at
least `meshSize` (`mesh_conditions`). The certified discretisation error is
the sample-error term plus a term decaying as `1 / M`
(`discretisation_eq`), so the relative budget
`discretisation ≤ ε B / (2000 g)` holds for small sample errors on fine
meshes. Existence of a solution for Lipschitz paths is
`exists_solvesODE_of_lipschitz`.
-/

namespace SparseHamiltonian.TimeDependentODE

noncomputable section

/-- An explicit mesh size meeting both public SELECT mesh conditions. -/
def meshSize (s : ℕ) (τ ν : ℝ) : ℕ :=
  ⌈8 * s * τ + Real.sqrt (3 * (Real.sqrt (2 * (s : ℝ)) * τ) ^ 3 / ν)⌉₊ + 1

/-- Every mesh size at least `meshSize s τ ν` satisfies the clock condition
`8 s τ ≤ M` and the Cayley condition `3 (√(2s) τ)³ ≤ ν M²`, `τ = ρ T`. -/
theorem mesh_conditions (s : ℕ) (τ ν : ℝ) (hτ : 0 ≤ τ) (hν : 0 < ν) (M : ℕ)
    (hM : meshSize s τ ν ≤ M) :
    0 < M ∧ 8 * s * τ ≤ M ∧ 3 * (Real.sqrt (2 * (s : ℝ)) * τ) ^ 3 ≤ ν * (M : ℝ) ^ 2 := by
  set A : ℝ := 8 * s * τ
  set C : ℝ := Real.sqrt (3 * (Real.sqrt (2 * (s : ℝ)) * τ) ^ 3 / ν)
  have hA : 0 ≤ A := by positivity
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hceil := Nat.le_ceil (A + C)
  have hSize : A + C ≤ meshSize s τ ν := by
    have hcast : ((⌈A + C⌉₊ + 1 : ℕ) : ℝ) = (⌈A + C⌉₊ : ℝ) + 1 := by push_cast; ring
    change A + C ≤ ((⌈A + C⌉₊ + 1 : ℕ) : ℝ)
    rw [hcast]
    linarith
  have hMR : (meshSize s τ ν : ℝ) ≤ M := by exact_mod_cast hM
  refine ⟨lt_of_lt_of_le (Nat.succ_pos _) hM, by linarith, ?_⟩
  have hCle : C ≤ M := by linarith
  have hsq : C ^ 2 = 3 * (Real.sqrt (2 * (s : ℝ)) * τ) ^ 3 / ν := by
    simp only [C]
    rw [Real.sq_sqrt (by positivity)]
  have h2 : C ^ 2 ≤ (M : ℝ) ^ 2 := pow_le_pow_left₀ hC hCle 2
  have h3 := mul_le_mul_of_nonneg_left h2 hν.le
  have hνC : ν * C ^ 2 = 3 * (Real.sqrt (2 * (s : ℝ)) * τ) ^ 3 := by
    rw [hsq]
    field_simp
  linarith

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s M : ℕ}

/-- The certified discretisation error: the sample-error term plus a term
decaying as `1 / M`. -/
theorem discretisation_eq (D : NativeSparseBlockEncoding.Data (X × Fin M) n Z s)
    (T βG δG βb δb bmax r₀ : ℝ) :
    Sampling.discretisation D T βG δG βb δb bmax r₀ =
      T * (δG * (r₀ + bmax * T) + δb) +
        T ^ 2 / M * (βG * (r₀ + bmax * T) + βb + (s : ℝ) * D.scale * (bmax + δb)) := by
  unfold Sampling.discretisation
  ring

end

end SparseHamiltonian.TimeDependentODE
