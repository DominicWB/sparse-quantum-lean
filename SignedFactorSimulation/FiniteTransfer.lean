import SignedFactorSimulation.Coefficients
import SignedFactorSimulation.Factor
import SparseHamiltonian.ClockCatalyst
import SparseHamiltonian.LocalRotation
import SparseHamiltonian.CayleyTransfer

/-!
# The exact finite transfer (`opt:eq:finite-transfer`, `opt:eq:finite-F`)

One boundary rotation `G_v` couples the public space `P` to one private slot through the known
isometry `E`, with `c = (1 - v/2)/(1 + v/2)`, `χ = 1 - c` and `σ² = 2v/(1 + v/2)²`
(`CayleyTransfer.c`, `kappa`, `sigma`). The local unitary is `S_v = G_v (I ⊕ P)`. With the
private operator `P` replaced by `wP`, its public action is the Cayley step

  `u(w) = (I - (v/2) Ω(w)) (I + (v/2) Ω(w))⁻¹`,  `Ω(w) = E†(I + wP)(I - wP)⁻¹E`

(`local_catalyst`), and the chronological cascade of `m` such slots, the released network
(`GlobalResolvent.globalPrivateBlock` with its public exit and stacked response), has the
causal transfer `u(w)^m` (`transfer_cascade`).

The proof is the paper's block elimination: the local catalyst `Γ = σ(1 + v/2) R E Y`, with
`R = (I - wP)⁻¹` and `Y = (I + (v/2)Ω)⁻¹`, solves the private equation and its public action is
`u(w)`; the released chronological transduction (`global_catalyst_transduction`,
`catalyst_public_transduction`) stacks it along the cascade. Since the private block of the
cascade is linear in the private operator (`globalPrivateBlock_smul`) and is a contraction
(`norm_globalPrivateBlock_le`), the stacked catalyst is the actual resolvent `(I - w D_g)⁻¹ C_g`
for `|w| < 1`.
-/

set_option autoImplicit false

namespace SignedFactorSimulation

noncomputable section

open Complex ContinuousLinearMap OptimalPrecision
open SparseHamiltonian SparseHamiltonian.ChronologicalResolvent
  SparseHamiltonian.ChronologicalCatalyst SparseHamiltonian.GlobalResolvent
  SparseHamiltonian.GlobalColligation
open scoped InnerProduct InnerProductSpace

section Generic

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

theorem one_comp' (f : X →L[ℂ] Y) : (1 : Y →L[ℂ] Y) ∘L f = f := id_comp f

theorem comp_one' (f : X →L[ℂ] Y) : f ∘L (1 : X →L[ℂ] X) = f := comp_id f

end Generic

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-! ### Invertibility of `I + t G` for accretive `G` -/

/-- For an accretive `G` and `t ≥ 0`, `I + t G` is invertible (finite dimension). -/
theorem isUnit_one_add_smul [FiniteDimensional ℂ P] (G : P →L[ℂ] P)
    (hG : ∀ x, 0 ≤ (⟪x, G x⟫_ℂ).re) {t : ℝ} (ht : 0 ≤ t) :
    IsUnit (1 + (t : ℂ) • G) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  have hinj : Function.Injective ⇑((1 : P →L[ℂ] P) + (t : ℂ) • G) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h := congrArg (fun y => (⟪x, y⟫_ℂ).re) hx
    simp only [add_apply, one_apply_eq_self, smul_apply, inner_add_right,
      inner_smul_right, inner_zero_right, zero_re, add_re, re_ofReal_mul] at h
    have h1 : 0 ≤ t * (⟪x, G x⟫_ℂ).re := mul_nonneg ht (hG x)
    have h2 : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [h2] at h
    have : ‖x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x‖]
    simpa using this
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := ((1 + (t : ℂ) • G : P →L[ℂ] P) :
    P →ₗ[ℂ] P))).mp hinj⟩

/-! ### Linearity of the cascade in the private operator -/

omit [CompleteSpace P] [CompleteSpace V] in
theorem chronologicalOperator_smul (w : ℂ) (R : V →L[ℂ] V) (A : P →L[ℂ] V) (u : P →L[ℂ] P)
    (B : V →L[ℂ] P) (T : ℕ) :
    chronologicalOperator (w • R) A u (w • B) T = w • chronologicalOperator R A u B T := by
  ext x i
  simp only [chronologicalOperator, BlockOperator.blocks_apply, smul_apply, PiLp.smul_apply,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [chronologicalBlock]
  split_ifs <;> simp

omit [CompleteSpace P] [CompleteSpace V] in
theorem publicExit_smul (w : ℂ) (u : P →L[ℂ] P) (B : V →L[ℂ] P) (T : ℕ) :
    publicExit u (w • B) T = w • publicExit u B T := by
  simp only [publicExit, smul_comp, comp_smul, Finset.smul_sum]

theorem localPrivateBlock_smul (w : ℂ) (D : V →L[ℂ] V) (J : P →L[ℂ] V) (κ : ℝ) :
    localPrivateBlock (w • D) J κ = w • localPrivateBlock D J κ := by
  simp only [localPrivateBlock, comp_smul]

theorem globalPrivateBlock_smul (w : ℂ) (D : V →L[ℂ] V) (J : P →L[ℂ] V) (c κ σ : ℝ)
    (T : ℕ) :
    globalPrivateBlock (w • D) J c κ σ T = w • globalPrivateBlock D J c κ σ T := by
  rw [globalPrivateBlock, globalPrivateBlock, localPrivateBlock_smul,
    show (-(σ : ℂ)) • (J† ∘L (w • D)) = w • ((-(σ : ℂ)) • (J† ∘L D)) by
      rw [comp_smul, smul_comm], chronologicalOperator_smul]

/-! ### The contraction property of the cascade -/

/-- The private block of the cascade is a contraction for an isometric private operator. -/
theorem norm_globalPrivateBlock_le (D : V →L[ℂ] V) (J : P →L[ℂ] V) (c κ σ : ℝ)
    (hκ : κ = 1 - c) (hσ : σ ^ 2 = 1 - c ^ 2) (hD : D† ∘L D = 1) (hJ : J† ∘L J = 1)
    (T : ℕ) : ‖globalPrivateBlock D J c κ σ T‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  have h := chronological_full_energy (localPrivateBlock D J κ) ((σ : ℂ) • J) ((c : ℂ) • 1)
    ((-(σ : ℂ)) • (J† ∘L D)) (LocalRotation.local_step_energy D J c κ σ hκ hσ hD hJ) T 0 x
  simp only [map_zero, zero_add, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at h
  have h' : ‖globalPrivateBlock D J c κ σ T x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [globalPrivateBlock]; nlinarith [sq_nonneg ‖publicExit ((c : ℂ) • 1)
      ((-(σ : ℂ)) • (J† ∘L D)) T x‖]
  rw [one_mul]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h'

/-! ### The local catalyst -/

/-- The scalar relations of the Cayley couplings. -/
theorem cayley_scalars {v : ℝ} (hv : 0 ≤ v) :
    CayleyTransfer.kappa v = 1 - CayleyTransfer.c v ∧
      CayleyTransfer.sigma v ^ 2 = 1 - CayleyTransfer.c v ^ 2 ∧
      ((CayleyTransfer.sigma v : ℂ) * (CayleyTransfer.sigma v * (1 + v / 2))) =
        2 * CayleyTransfer.kappa v ∧
      (CayleyTransfer.kappa v : ℂ) * (1 + v / 2) = 2 * (v / 2) ∧
      (CayleyTransfer.c v : ℂ) * (1 + v / 2) = 1 - v / 2 := by
  have h2 : (1 + v / 2 : ℝ) ≠ 0 := by positivity
  have hs := CayleyTransfer.sigma_sq v hv
  refine ⟨BaseTransfer.cayley_kappa_relation v hv,
    hs.trans (BaseTransfer.cayley_sigma_relation v hv), ?_, ?_, ?_⟩
  · have e : CayleyTransfer.sigma v * (CayleyTransfer.sigma v * (1 + v / 2)) =
        2 * CayleyTransfer.kappa v := by
      rw [← mul_assoc, ← sq, hs, CayleyTransfer.kappa]
      field_simp
    exact_mod_cast e
  · have e : CayleyTransfer.kappa v * (1 + v / 2) = 2 * (v / 2) := by
      rw [CayleyTransfer.kappa]; field_simp
    exact_mod_cast e
  · have e : CayleyTransfer.c v * (1 + v / 2) = 1 - v / 2 := by
      rw [CayleyTransfer.c]; field_simp
    exact_mod_cast e

omit [CompleteSpace V] in
/-- `R = I + Q R` for a right inverse `R` of `I - Q`. -/
theorem resolvent_split {Q R : V →L[ℂ] V} (hR' : (1 - Q) ∘L R = 1) : R = 1 + Q ∘L R := by
  have h := hR'
  rw [sub_comp, one_comp'] at h
  rw [← h]; abel

/-- `Ω = E†(I + Q)RE = I + 2X` with `X = E† Q R E`. -/
theorem omega_split {Q R : V →L[ℂ] V} {E : P →L[ℂ] V} (hE : E† ∘L E = 1)
    (hR' : (1 - Q) ∘L R = 1) :
    E† ∘L (1 + Q) ∘L R ∘L E = 1 + (2 : ℂ) • (E† ∘L Q ∘L R ∘L E) := by
  have hRQ := resolvent_split hR'
  have h1 : E† ∘L R ∘L E = 1 + E† ∘L Q ∘L R ∘L E := by
    conv_lhs => rw [hRQ]
    rw [add_comp, comp_add, one_comp', hE]
    simp only [comp_assoc]
  rw [add_comp, one_comp', comp_add, h1, two_smul]
  abel

/-- `(I - (I - κEE†)Q) R = I + κ E E† Q R`. -/
theorem private_step {Q R : V →L[ℂ] V} (E : P →L[ℂ] V) (κ : ℝ) (hR' : (1 - Q) ∘L R = 1) :
    (1 - localPrivateBlock Q E κ) ∘L R = 1 + (κ : ℂ) • (E ∘L E† ∘L Q ∘L R) := by
  have h : R - Q ∘L R = 1 := by
    have h := hR'; rwa [sub_comp, one_comp'] at h
  simp only [localPrivateBlock, sub_comp, one_comp', smul_comp, comp_assoc]
  rw [← h]
  abel

/-- The local catalyst with abstract scalars `c, κ, σ`, `a = 1 + t`, `s = σ a`. -/
theorem local_catalyst_abstract (Q R : V →L[ℂ] V) (E : P →L[ℂ] V)
    (hE : E† ∘L E = 1) (hR' : (1 - Q) ∘L R = 1) (Y : P →L[ℂ] P)
    (c σ t a s : ℂ) (κ : ℝ) (ha : a ≠ 0) (hat : a = 1 + t)
    (hκa : (κ : ℂ) * a = 2 * t) (hca : c * a = 1 - t) (hs : s = σ * a)
    (hσs : σ * s = 2 * κ)
    (hY : (1 + t • (E† ∘L (1 + Q) ∘L R ∘L E)) ∘L Y = 1) :
    σ • E + localPrivateBlock Q E κ ∘L (s • (R ∘L E ∘L Y)) = s • (R ∘L E ∘L Y) ∧
    c • (1 : P →L[ℂ] P) + ((-σ) • (E† ∘L Q)) ∘L (s • (R ∘L E ∘L Y)) =
      (1 - t • (E† ∘L (1 + Q) ∘L R ∘L E)) ∘L Y := by
  rw [omega_split hE hR'] at hY ⊢
  set X := E† ∘L Q ∘L R ∘L E with hX
  -- `(I + κ X) Y = a⁻¹`
  have hKY : ((1 : P →L[ℂ] P) + (κ : ℂ) • X) ∘L Y = a⁻¹ • (1 : P →L[ℂ] P) := by
    have e : (1 : P →L[ℂ] P) + (κ : ℂ) • X = a⁻¹ • (1 + t • (1 + (2 : ℂ) • X)) := by
      have hk : (κ : ℂ) = a⁻¹ * (2 * t) := by rw [← hκa]; field_simp
      have h1 : a⁻¹ * (1 + t) = 1 := by rw [← hat, inv_mul_cancel₀ ha]
      rw [hk]
      simp only [smul_add, smul_smul]
      match_scalars
      · linear_combination -h1
      · ring
    rw [e, smul_comp, hY]
  constructor
  · have hpriv := private_step E κ hR'
    have key : (1 - localPrivateBlock Q E κ) ∘L (s • (R ∘L E ∘L Y)) = σ • E := by
      have e1 : (1 - localPrivateBlock Q E κ) ∘L (R ∘L E ∘L Y) =
          E ∘L (((1 : P →L[ℂ] P) + (κ : ℂ) • X) ∘L Y) := by
        rw [← comp_assoc, hpriv, hX]
        simp only [add_comp, one_comp', smul_comp, comp_add, comp_smul, comp_assoc]
      rw [comp_smul, e1, hKY, comp_smul, comp_one', smul_smul, hs, mul_assoc,
        mul_inv_cancel₀ ha, mul_one]
    rw [← key]
    simp only [sub_comp, one_comp']
    abel
  · have hct : c * t + t = κ := by
      have h0 : a * (c * t + t - κ) = 0 := by linear_combination t * hca - hκa + t * hat
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h ha
      · linear_combination h
    have e1 : ((-σ) • (E† ∘L Q)) ∘L (s • (R ∘L E ∘L Y)) = ((-(2 * (κ : ℂ))) • X) ∘L Y := by
      rw [← hσs, hX]
      simp only [smul_comp, comp_smul, smul_smul, comp_assoc]
      congr 1
      ring
    have e2 : c • (1 : P →L[ℂ] P) = (c • (1 + t • (1 + (2 : ℂ) • X))) ∘L Y := by
      rw [smul_comp, hY]
    have e3 : c • (1 + t • (1 + (2 : ℂ) • X)) + (-(2 * (κ : ℂ))) • X =
        1 - t • (1 + (2 : ℂ) • X) := by
      simp only [smul_add, smul_smul]
      match_scalars
      · linear_combination hca - c * hat
      · linear_combination 2 * hct
    rw [e1, e2, ← add_comp, e3]

/-- The Cayley step `(I - (v/2) G)(I + (v/2) G)⁻¹`. -/
def cayStep (v : ℝ) (G : P →L[ℂ] P) : P →L[ℂ] P :=
  (1 - ((v / 2 : ℝ) : ℂ) • G) ∘L Ring.inverse (1 + ((v / 2 : ℝ) : ℂ) • G)

/-- The generator `Ω(w) = E†(I + wP)(I - wP)⁻¹E` of a private operator. -/
def gen (Pr : V →L[ℂ] V) (E : P →L[ℂ] V) (w : ℂ) : P →L[ℂ] P :=
  E† ∘L (1 + w • Pr) ∘L Ring.inverse (1 - w • Pr) ∘L E

theorem isUnit_one_sub_smul {Pr : V →L[ℂ] V} (hPr : Pr† ∘L Pr = 1) {w : ℂ} (hw : ‖w‖ < 1) :
    IsUnit (1 - w • Pr) := by
  have hn : ‖Pr‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [Pr.norm_map_iff_adjoint_comp_self.mpr hPr, one_mul]
  have h : ‖w • Pr‖ < 1 := by
    calc ‖w • Pr‖ ≤ ‖w‖ * ‖Pr‖ := norm_smul_le w Pr
      _ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hn (norm_nonneg w)
      _ < 1 := by rw [mul_one]; exact hw
  have hu := (Units.oneSub _ h).isUnit
  rwa [Units.val_oneSub] at hu

/-- **The global transfer of the cascade** (`opt:eq:finite-F`): the causal transfer of the
chronological cascade of `m` boundary rotations around the isometric private operator `Pr` is
the `m`-th power of the Cayley step of `Ω(w) = E†(I + w Pr)(I - w Pr)⁻¹E`, for `|w| < 1` and
accretive `Ω(w)`. -/
theorem transfer_cascade [FiniteDimensional ℂ P] {v : ℝ} (hv : 0 ≤ v)
    (Pr : V →L[ℂ] V) (hPr : Pr† ∘L Pr = 1) (E : P →L[ℂ] V) (hE : E† ∘L E = 1)
    (m : ℕ) {w : ℂ} (hw : ‖w‖ < 1) (hacc : ∀ x, 0 ≤ (⟪x, gen Pr E w x⟫_ℂ).re) :
    transfer (((CayleyTransfer.c v : ℂ) • (1 : P →L[ℂ] P)) ^ m)
        (publicExit ((CayleyTransfer.c v : ℂ) • 1)
          ((-(CayleyTransfer.sigma v : ℂ)) • (E† ∘L Pr)) m)
        (stackedResponse ((CayleyTransfer.sigma v : ℂ) • E) ((CayleyTransfer.c v : ℂ) • 1) m)
        (globalPrivateBlock Pr E (CayleyTransfer.c v) (CayleyTransfer.kappa v)
          (CayleyTransfer.sigma v) m) w =
      cayStep v (gen Pr E w) ^ m := by
  obtain ⟨hκc, hσc, hσs, hκa, hca⟩ := cayley_scalars hv
  set c := CayleyTransfer.c v
  set κ := CayleyTransfer.kappa v
  set σ := CayleyTransfer.sigma v
  -- the resolvent of the private operator
  set Q : V →L[ℂ] V := w • Pr with hQ
  set R : V →L[ℂ] V := Ring.inverse (1 - Q) with hRdef
  have hRunit := isUnit_one_sub_smul hPr hw
  have hR' : (1 - Q) ∘L R = 1 := Ring.mul_inverse_cancel _ hRunit
  -- the generator and its Cayley denominator
  set G := gen Pr E w with hG
  have hGeq : G = E† ∘L (1 + Q) ∘L R ∘L E := rfl
  set Y := Ring.inverse (1 + ((v / 2 : ℝ) : ℂ) • G) with hYdef
  have hYunit := isUnit_one_add_smul G hacc (t := v / 2) (by positivity)
  have hY : (1 + ((v / 2 : ℝ) : ℂ) • (E† ∘L (1 + Q) ∘L R ∘L E)) ∘L Y = 1 :=
    Ring.mul_inverse_cancel _ hYunit
  -- the local catalyst
  have ha : (1 + (v : ℂ) / 2) ≠ 0 := by
    have : (1 + v / 2 : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  obtain ⟨hPrivate, hPublic⟩ := local_catalyst_abstract Q R E hE hR' Y (c : ℂ) (σ : ℂ)
    (((v / 2 : ℝ) : ℂ)) (1 + (v : ℂ) / 2) ((σ : ℂ) * (1 + (v : ℂ) / 2)) κ ha
    (by push_cast; ring) (by rw [hκa]; push_cast; ring) (by rw [hca]; push_cast; ring) rfl
    hσs hY
  set Γ := ((σ : ℂ) * (1 + (v : ℂ) / 2)) • (R ∘L E ∘L Y)
  set U := (1 - ((v / 2 : ℝ) : ℂ) • (E† ∘L (1 + Q) ∘L R ∘L E)) ∘L Y
  have hUeq : U = cayStep v G := rfl
  -- the global transduction for the private operator `Q = w Pr`
  have hGlob := global_catalyst_transduction Q E c κ σ Γ U m hPrivate hPublic
  have hPub := catalyst_public_transduction Γ U ((c : ℂ) • 1)
    ((-(σ : ℂ)) • (E† ∘L Q)) hPublic m
  rw [globalPrivateBlock_smul] at hGlob
  rw [show (-(σ : ℂ)) • (E† ∘L Q) = w • ((-(σ : ℂ)) • (E† ∘L Pr)) by
    rw [hQ, comp_smul, smul_comm], publicExit_smul] at hPub
  -- the stacked catalyst is the resolvent applied to the stacked response
  set Dg := globalPrivateBlock Pr E c κ σ m
  set Cg := stackedResponse ((σ : ℂ) • E) ((c : ℂ) • 1) m
  set S := stackedResponse Γ U m
  have hDg : ‖w • Dg‖ < 1 := by
    calc ‖w • Dg‖ ≤ ‖w‖ * ‖Dg‖ := opNorm_smul_le w Dg
      _ ≤ ‖w‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_globalPrivateBlock_le Pr E c κ σ hκc hσc hPr hE m)
            (norm_nonneg w)
      _ < 1 := by rw [mul_one]; exact hw
  have hunit : IsUnit (1 - w • Dg) := by
    have hu := (Units.oneSub (w • Dg) (by exact hDg)).isUnit
    rwa [Units.val_oneSub] at hu
  have hS : S = Ring.inverse (1 - w • Dg) ∘L Cg := by
    have h1 : (1 - w • Dg) ∘L S = Cg := by
      rw [sub_comp, one_comp']
      calc S - (w • Dg) ∘L S = (Cg + (w • Dg) ∘L S) - (w • Dg) ∘L S := by rw [hGlob]
        _ = Cg := by abel
    calc S = (Ring.inverse (1 - w • Dg) * (1 - w • Dg)) ∘L S := by
          rw [Ring.inverse_mul_cancel _ hunit, one_comp']
      _ = Ring.inverse (1 - w • Dg) ∘L Cg := by
          rw [mul_def, comp_assoc, h1]
  rw [transfer, ← hUeq, ← hPub, hS]
  simp only [smul_comp]

end

end SignedFactorSimulation
