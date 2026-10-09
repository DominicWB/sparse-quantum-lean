import TimeDependentODE.Solver.Families
import TimeDependentODE.Solver.Coefficients

/-!
# The discretised target and its certified relation to the solution

The source register loads the initial state and the weighted forcing samples
(`sources`). Their masked propagators sum exactly to the left-endpoint
exponential recurrence (`target_eq_recurrence`), whose distance from the
continuous solution is the certified discretisation error of
`TimeDependentODE.mesh_error` (`discretisation_error`). Under a public
relative budget this target is nonzero, retains half of the solution norm,
and has the solution's direction up to `ε / 1000` (`target_budget`).
-/

namespace SparseHamiltonian.TimeDependentODE.Sampling

noncomputable section
open ContinuousLinearMap NativeSparseBlockEncoding
open scoped BigOperators InnerProduct

section Generic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {M : ℕ}

/-- Source vectors: the initial state and the forcing samples weighted by the
step `h`. -/
def sources (y0 : V) (h : ℝ) (bs : Fin M → V) : Option (Fin M) → V
  | none => y0
  | some q => h • bs q

/-- Forcing samples on chronological slots. -/
def forcing (bs : Fin M → V) (r : ℕ) : V :=
  if hr : r < M then bs ⟨r, hr⟩ else 0

/-- The discretised target: the masked propagators applied to the sources. -/
def target (Gs : ℕ → V →L[ℂ] V) (h : ℝ) (y0 : V) (bs : Fin M → V) : V :=
  ∑ a, maskedPropagator Gs h (start a) M (sources y0 h bs a)

omit [CompleteSpace V] in
/-- The source sum is exactly the exponential recurrence. -/
theorem target_eq_recurrence (Gs : ℕ → V →L[ℂ] V) (h : ℝ) (y0 : V) (bs : Fin M → V) :
    target Gs h y0 bs = recurrence Gs (forcing bs) h y0 M := by
  rw [recurrence_eq_sum, target, Fintype.sum_option]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range
    (fun q => maskedPropagator Gs h q M (h • forcing bs q)) M]
  apply Finset.sum_congr rfl
  intro q _
  simp only [start, sources, forcing, Fin.is_lt, dif_pos, Fin.eta]

/-- With accretive slot generators, the target norm is at most the source mass. -/
theorem target_norm_le (Gs : ℕ → V →L[ℂ] V) (hGs : ∀ r, Accretive (Gs r)) (h : ℝ)
    (hh : 0 ≤ h) (y0 : V) (bs : Fin M → V) :
    ‖target Gs h y0 bs‖ ≤ ODESourceBranches.mass (sources y0 h bs) := by
  unfold target ODESourceBranches.mass
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  calc
    ‖maskedPropagator Gs h (start a) M (sources y0 h bs a)‖ ≤
        ‖maskedPropagator Gs h (start a) M‖ * ‖sources y0 h bs a‖ := le_opNorm _ _
    _ ≤ 1 * ‖sources y0 h bs a‖ := mul_le_mul_of_nonneg_right
        (maskedPropagator_norm_le_one Gs hGs h hh (start a) M) (norm_nonneg _)
    _ = ‖sources y0 h bs a‖ := one_mul _

omit [CompleteSpace V] in
/-- Source vectors of public norms. -/
theorem sources_norm (y0 : V) (T : ℝ) (hT : 0 ≤ T) (bs : Fin M → V) (r₀ : ℝ)
    (rb : Fin M → ℝ) (h₀ : ‖y0‖ = r₀) (hb : ∀ q, ‖bs q‖ = rb q) (a : Option (Fin M)) :
    ‖sources y0 (T / M) bs a‖ = PublicSource.norms r₀ T rb a := by
  cases a with
  | none => exact h₀
  | some q =>
      simp only [sources, PublicSource.norms, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hT (Nat.cast_nonneg M)), hb q]

end Generic

section Normalization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A positive weight does not change the direction. -/
theorem unitDirection_smul (c : ℝ) (hc : 0 < c) (v : E) :
    ODEStateNormalization.unitDirection (c • v) = ODEStateNormalization.unitDirection v := by
  unfold ODEStateNormalization.unitDirection
  rw [norm_smul, Real.norm_of_nonneg hc.le, smul_smul, mul_inv, mul_comm c⁻¹, mul_assoc,
    inv_mul_cancel₀ hc.ne', mul_one]

/-- Under the public relative budget, the target is nonzero, retains half
of the solution norm, and has the solution's direction up to `ε / 1000`. -/
theorem target_budget (xT y : E) (B g ε err : ℝ) (hg : 1 ≤ g) (hε : 0 < ε)
    (hεOne : ε ≤ 1) (hx : xT ≠ 0) (hB : B ≤ g * ‖xT‖) (hErr : ‖xT - y‖ ≤ err)
    (hBudget : err ≤ ε * B / (2000 * g)) :
    y ≠ 0 ∧ B ≤ 2 * g * ‖y‖ ∧
      ‖ODEStateNormalization.unitDirection y - ODEStateNormalization.unitDirection xT‖ ≤
        ε / 1000 := by
  have hg0 : 0 < g := by linarith
  have hxN : 0 < ‖xT‖ := norm_pos_iff.mpr hx
  have hRel : ‖y - xT‖ ≤ ε / 2000 * ‖xT‖ := by
    rw [norm_sub_rev]
    have hScale : ε * B / (2000 * g) ≤ ε * (g * ‖xT‖) / (2000 * g) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hB hε.le
    have hEq : ε * (g * ‖xT‖) / (2000 * g) = ε / 2000 * ‖xT‖ := by
      field_simp
    linarith
  obtain ⟨hy, hDir⟩ :=
    ODEStateNormalization.relative_error xT y (ε / 2000) hx (by linarith) hRel
  have hLower := ODEStateNormalization.approximate_norm_lower xT y (ε / 2000) hRel
  have hHalf : ‖xT‖ ≤ 2 * ‖y‖ := by nlinarith
  refine ⟨hy, ?_, by linarith⟩
  calc
    B ≤ g * ‖xT‖ := hB
    _ ≤ g * (2 * ‖y‖) := mul_le_mul_of_nonneg_left hHalf hg0.le
    _ = 2 * g * ‖y‖ := by ring

end Normalization

section Sampled

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s M : ℕ}

/-- Certified discretisation error of the exponential left-endpoint scheme
on the uniform mesh, with the public operator-norm bound `s D.scale` of the
sampled generators and the forcing-sample bound `bmax + δb`. -/
def discretisation (D : Data (X × Fin M) n Z s) (T βG δG βb δb bmax r₀ : ℝ) : ℝ :=
  T * ((βG * (T / M) + δG) * (r₀ + bmax * T) + βb * (T / M) + δb +
    (T / M) * ((s : ℝ) * D.scale) * (bmax + δb))

/-- The target of the represented samples is within the certified
discretisation error of every solution of the continuous problem. -/
theorem discretisation_error (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (x : X) (T : ℝ) (hT : 0 ≤ T)
    (G : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (b sol : ℝ → EuclideanSpace ℂ n) (bs : Fin M → EuclideanSpace ℂ n)
    (βG δG βb δb bmax : ℝ) (hβG : 0 ≤ βG) (hβb : 0 ≤ βb)
    (hG : ∀ u ∈ Set.Icc 0 T, Accretive (G u))
    (hGLip : ∀ u ∈ Set.Icc 0 T, ∀ v ∈ Set.Icc 0 T, ‖G u - G v‖ ≤ βG * |u - v|)
    (hGs : ∀ r : Fin M, ‖G ((r : ℕ) * T / M) -
      SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δG)
    (hbLip : ∀ u ∈ Set.Icc 0 T, ∀ v ∈ Set.Icc 0 T, ‖b u - b v‖ ≤ βb * |u - v|)
    (hbs : ∀ r : Fin M, ‖b ((r : ℕ) * T / M) - bs r‖ ≤ δb)
    (hb : ∀ u ∈ Set.Icc 0 T, ‖b u‖ ≤ bmax) (hsol : SolvesODE G b sol 0 T) :
    ‖sol T - target (generator D hM x) (T / M) (sol 0) bs‖ ≤
      discretisation D T βG δG βb δb bmax ‖sol 0‖ := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hbmax : 0 ≤ bmax := (norm_nonneg _).trans (hb 0 ⟨le_rfl, hT⟩)
  have hδb : 0 ≤ δb := (norm_nonneg _).trans (hbs ⟨0, hM⟩)
  have hΛ : 0 ≤ (s : ℝ) * D.scale := mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le
  have hslot : ∀ r : ℕ, r < M → ((r : ℝ) * T / M) ∈ Set.Icc 0 T := by
    intro r hr
    have hrM : (r : ℝ) ≤ M := by exact_mod_cast hr.le
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hMR]
    nlinarith
  rw [target_eq_recurrence]
  exact mesh_error hsol hT hM hG (generator D hM x) (generator_accretive D hM hPSD x)
    (forcing bs) βG δG βb δb bmax ((s : ℝ) * D.scale) (bmax + δb) hβG hβb hbmax hΛ
    (by linarith) hGLip
    (fun r hr => by
      have hidx : TimeDependent.Sampled.sampleIndex hM r = ⟨r, hr⟩ :=
        Fin.ext (Nat.mod_eq_of_lt hr)
      unfold generator
      rw [hidx]
      exact hGs ⟨r, hr⟩)
    hbLip
    (fun r hr => by
      unfold forcing
      rw [dif_pos hr]
      exact hbs ⟨r, hr⟩)
    hb (fun r _ => generator_norm_le D hM x r)
    (fun r hr => by
      unfold forcing
      rw [dif_pos hr]
      calc
        ‖bs ⟨r, hr⟩‖ = ‖b ((r : ℝ) * T / M) - (b ((r : ℝ) * T / M) - bs ⟨r, hr⟩)‖ := by
          rw [sub_sub_cancel]
        _ ≤ ‖b ((r : ℝ) * T / M)‖ + ‖b ((r : ℝ) * T / M) - bs ⟨r, hr⟩‖ := norm_sub_le _ _
        _ ≤ bmax + δb := add_le_add (hb _ (hslot r hr)) (hbs ⟨r, hr⟩))

end Sampled

end

end SparseHamiltonian.TimeDependentODE.Sampling
