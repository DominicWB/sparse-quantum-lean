import SparseHamiltonian.CanonicalWeightedClock

/-!
# Constructing a local catalyst from the private resolvent

The private stationary response is constructed from a right inverse of the
local denominator. The energy law then proves that its public action is an
isometry. The clock endpoint estimate gives its weighted cost.
-/

namespace SparseHamiltonian.CatalystConstruction

noncomputable section

open ContinuousLinearMap
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The private fixed response to a public input. -/
def catalyst (S : V →L[ℂ] V) (A : P →L[ℂ] V) : P →L[ℂ] V := S ∘L A

/-- Public action after substituting the stationary private response. -/
def publicAction (u : P →L[ℂ] P) (B : V →L[ℂ] P)
    (S : V →L[ℂ] V) (A : P →L[ℂ] V) : P →L[ℂ] P := u + B ∘L catalyst S A

/-- A right inverse constructs the private transduction identity. -/
theorem private_transduction (D S : V →L[ℂ] V) (A : P →L[ℂ] V)
    (hS : (1 - D) ∘L S = 1) : A + D ∘L catalyst S A = catalyst S A := by
  have h : S - D ∘L S = 1 := by
    simpa only [sub_comp, one_def, id_comp] using hS
  have hDS : D ∘L S = S - 1 := by
    rw [← h]
    abel
  simp only [catalyst, ← comp_assoc, hDS, sub_comp, one_def, id_comp]
  abel

/-- The constructed public action is precisely the public transduction block. -/
theorem public_transduction (u : P →L[ℂ] P) (B : V →L[ℂ] P)
    (S : V →L[ℂ] V) (A : P →L[ℂ] V) :
    u + B ∘L catalyst S A = publicAction u B S A := rfl

/-- A left inverse makes the stationary catalyst unique. -/
theorem catalyst_unique (D S : V →L[ℂ] V) (A Γ : P →L[ℂ] V)
    (hS : S ∘L (1 - D) = 1) (hPrivate : A + D ∘L Γ = Γ) :
    Γ = catalyst S A := by
  have hStation : (1 - D) ∘L Γ = A := by
    simp only [sub_comp, one_def, id_comp]
    exact (eq_sub_of_add_eq hPrivate).symm
  calc
    Γ = S ∘L ((1 - D) ∘L Γ) := by
      rw [← comp_assoc, hS, one_def, id_comp]
    _ = catalyst S A := by rw [hStation]; rfl

/-- The eliminated public action is unique whenever the private denominator
has a left inverse. -/
theorem publicAction_eq_of_transduction (D S : V →L[ℂ] V) (A Γ : P →L[ℂ] V)
    (u U : P →L[ℂ] P) (B : V →L[ℂ] P)
    (hS : S ∘L (1 - D) = 1) (hPrivate : A + D ∘L Γ = Γ)
    (hPublic : u + B ∘L Γ = U) : U = publicAction u B S A := by
  rw [← hPublic, catalyst_unique D S A Γ hS hPrivate]
  rfl

/-- Energy conservation plus a stationary private response makes the public
action an isometry, without requiring surjectivity. -/
theorem publicAction_norm_map (D S : V →L[ℂ] V) (A : P →L[ℂ] V)
    (u : P →L[ℂ] P) (B : V →L[ℂ] P) (hS : (1 - D) ∘L S = 1)
    (hStep : ∀ x p, ‖D x + A p‖ ^ 2 + ‖u p + B x‖ ^ 2 =
      ‖x‖ ^ 2 + ‖p‖ ^ 2) (p : P) : ‖publicAction u B S A p‖ = ‖p‖ := by
  have h := hStep (catalyst S A p) p
  have hPrivate := congrArg (fun L : P →L[ℂ] V => L p) (private_transduction D S A hS)
  simp only [add_apply, comp_apply] at hPrivate
  have hEq : D (catalyst S A p) + A p = catalyst S A p := by
    simpa only [add_comm] using hPrivate
  rw [hEq] at h
  have hsq : ‖publicAction u B S A p‖ ^ 2 = ‖p‖ ^ 2 := by
    change ‖u p + B (catalyst S A p)‖ ^ 2 = ‖p‖ ^ 2
    linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The clock endpoint estimate gives a weighted catalyst bound. -/
theorem catalyst_norm_sq_le (S : V →L[ℂ] V) (J : P →L[ℂ] V)
    (σ w b qbar : ℝ) (hw : 0 ≤ w)
    (hσ : σ ^ 2 ≤ 2 * w) (hbq : b ^ 2 ≤ qbar / 2)
    (hSJ : ‖S ∘L J‖ ≤ 12 * b / 7) :
    ‖catalyst S ((σ : ℂ) • J)‖ ^ 2 ≤ (144 / 49 : ℝ) * w * qbar := by
  have hNorm : ‖catalyst S ((σ : ℂ) • J)‖ ^ 2 = σ ^ 2 * ‖S ∘L J‖ ^ 2 := by
    simp only [catalyst, comp_smul, norm_smul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hEnd : ‖S ∘L J‖ ^ 2 ≤ (12 * b / 7) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hSJ 2
  rw [hNorm]
  calc
    σ ^ 2 * ‖S ∘L J‖ ^ 2 ≤ (2 * w) * ((12 * b / 7) ^ 2) :=
      mul_le_mul hσ hEnd (sq_nonneg _) (by positivity)
    _ = (288 / 49 : ℝ) * w * b ^ 2 := by ring
    _ ≤ (288 / 49 : ℝ) * w * (qbar / 2) :=
      mul_le_mul_of_nonneg_left hbq (by positivity)
    _ = (144 / 49 : ℝ) * w * qbar := by ring

end

end SparseHamiltonian.CatalystConstruction
