import SignedFactorSimulation.FiniteTransfer

/-!
# The cascade of the factor interface

For the factor interface (`Known`) and the private unitary `P = U† G U`, the chronological
cascade of `m` boundary rotations of step `v` has the colligation `(cascA, cascB, cascC,
cascD)`. On the unit disk its causal transfer is the `m`-th power of the Cayley step of the
three-phase generator,

  `F_m(w) = u(w)^m`,  `u(w) = (I - (v/2)Ω(w))(I + (v/2)Ω(w))⁻¹`,  `Ω = Tail.Omega q C D`

(`transfer_cascade_factor`, `opt:eq:finite-transfer`, `opt:eq:finite-F`), the transfer is
holomorphic on the unit disk (`differentiableOn_transfer_cascade`), and the uniform clock of
`n` reuses of the cascade is `Ces_n(F_m)` (`successfulBlock_cascade`).
-/

set_option autoImplicit false

namespace SignedFactorSimulation

noncomputable section

open Complex ContinuousLinearMap OptimalPrecision OptimalPrecision.Tail
open SparseHamiltonian SparseHamiltonian.ChronologicalResolvent
  SparseHamiltonian.ChronologicalCatalyst SparseHamiltonian.GlobalResolvent
  SparseHamiltonian.GlobalColligation
open scoped InnerProduct InnerProductSpace ComplexOrder

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-! ### Holomorphy of the transfer -/

omit [CompleteSpace P] in
/-- The causal transfer of a colligation with contractive private block is holomorphic on the
unit disk. -/
theorem differentiableOn_transfer (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V)
    (D : V →L[ℂ] V) (hD : ‖D‖ ≤ 1) : DifferentiableOn ℂ (transfer A B C D) (Metric.ball 0 1) := by
  intro w hw
  have hw' : ‖w‖ < 1 := by simpa using hw
  have h : ‖w • D‖ < 1 := by
    calc ‖w • D‖ ≤ ‖w‖ * ‖D‖ := opNorm_smul_le w D
      _ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hD (norm_nonneg w)
      _ < 1 := by rw [mul_one]; exact hw'
  have hunit : IsUnit (1 - w • D) := by
    have hu := (Units.oneSub (w • D) h).isUnit
    rwa [Units.val_oneSub] at hu
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (1 : V →L[ℂ] V) - z • D) w :=
    (differentiableAt_const _).sub (differentiableAt_id.smul_const D)
  have hinv : DifferentiableAt ℂ (fun z : ℂ => Ring.inverse (1 - z • D)) w := by
    exact (differentiableAt_inverse hunit).comp w h1
  have hR : DifferentiableAt ℂ (fun z : ℂ => B ∘L Ring.inverse (1 - z • D) ∘L C) w := by
    exact ((sandwich B C).differentiableAt (x := Ring.inverse (1 - w • D))).comp w hinv
  have h2 : DifferentiableAt ℂ (fun z : ℂ => z • (B ∘L Ring.inverse (1 - z • D) ∘L C)) w :=
    differentiableAt_fun_id.fun_smul hR
  have h3 : DifferentiableAt ℂ (transfer A B C D) w := (differentiableAt_const A).add h2
  exact h3.differentiableWithinAt

/-! ### The cascade colligation -/

/-- The public block `c^m` of the cascade. -/
def cascA (v : ℝ) (m : ℕ) : P →L[ℂ] P := ((CayleyTransfer.c v : ℂ) • (1 : P →L[ℂ] P)) ^ m

/-- The private-to-public block of the cascade. -/
def cascB (Pr : V →L[ℂ] V) (E : P →L[ℂ] V) (v : ℝ) (m : ℕ) :
    BlockOperator.H m V →L[ℂ] P :=
  publicExit ((CayleyTransfer.c v : ℂ) • 1) ((-(CayleyTransfer.sigma v : ℂ)) • (E† ∘L Pr)) m

/-- The public-to-private block of the cascade. -/
def cascC (E : P →L[ℂ] V) (v : ℝ) (m : ℕ) : P →L[ℂ] BlockOperator.H m V :=
  stackedResponse ((CayleyTransfer.sigma v : ℂ) • E) ((CayleyTransfer.c v : ℂ) • 1) m

/-- The private block of the cascade. -/
def cascD (Pr : V →L[ℂ] V) (E : P →L[ℂ] V) (v : ℝ) (m : ℕ) :
    BlockOperator.H m V →L[ℂ] BlockOperator.H m V :=
  globalPrivateBlock Pr E (CayleyTransfer.c v) (CayleyTransfer.kappa v)
    (CayleyTransfer.sigma v) m

theorem norm_cascD_le {Pr : V →L[ℂ] V} (hPr : Pr† ∘L Pr = 1) {E : P →L[ℂ] V}
    (hE : E† ∘L E = 1) {v : ℝ} (hv : 0 ≤ v) (m : ℕ) : ‖cascD Pr E v m‖ ≤ 1 := by
  obtain ⟨hκc, hσc, -, -, -⟩ := cayley_scalars hv
  exact norm_globalPrivateBlock_le Pr E _ _ _ hκc hσc hPr hE m

/-- The causal transfer `F_m` of the cascade. -/
def cascTransfer (Pr : V →L[ℂ] V) (E : P →L[ℂ] V) (v : ℝ) (m : ℕ) (w : ℂ) : P →L[ℂ] P :=
  transfer (cascA v m) (cascB Pr E v m) (cascC E v m) (cascD Pr E v m) w

theorem differentiableOn_cascTransfer {Pr : V →L[ℂ] V} (hPr : Pr† ∘L Pr = 1)
    {E : P →L[ℂ] V} (hE : E† ∘L E = 1) {v : ℝ} (hv : 0 ≤ v) (m : ℕ) :
    DifferentiableOn ℂ (cascTransfer Pr E v m) (Metric.ball 0 1) := by
  unfold cascTransfer
  exact differentiableOn_transfer _ _ _ _ (norm_cascD_le hPr hE hv m)

/-- The uniform clock of `n` reuses of the cascade is `Ces_n(F_m)`. -/
theorem successfulBlock_cascade (Pr : V →L[ℂ] V) (E : P →L[ℂ] V) (v : ℝ) (m n : ℕ) :
    CoherentReuse.successfulBlock (cascA v m) (cascB Pr E v m) (cascC E v m)
      (cascD Pr E v m) n = ces (cascTransfer Pr E v m) n :=
  successfulBlock_eq_ces _ _ _ _ n

/-! ### The factor -/

namespace Known

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
variable (K : Known P W)

theorem one_sub_proj_isPositive : (1 - K.proj).IsPositive := by
  have h : 1 - K.proj = (1 - K.proj)† ∘L (1 - K.proj) := by
    rw [map_sub, adjoint_one, K.proj_adjoint]
    change 1 - K.proj = (1 - K.proj) * (1 - K.proj)
    rw [K.compl_mul_compl]
  rw [h]
  exact isPositive_adjoint_comp_self _

/-- `I - D` is positive: `I - D = E†U†(I - Π)UE`. -/
theorem one_sub_Dop_isPositive {U : W →L[ℂ] W} (hU : U† * U = 1) :
    (1 - K.Dop U).IsPositive := by
  have h : 1 - K.Dop U = (U ∘L K.E)† ∘L (1 - K.proj) ∘L (U ∘L K.E) := by
    rw [← K.compress_one U hU, ← K.compress_proj, ← K.compress_sub]
    simp only [compress, adjoint_comp]
    rfl
  rw [h]
  exact K.one_sub_proj_isPositive.adjoint_conj _

theorem Dop_add_Cop_isPositive (U : W →L[ℂ] W) : (K.Dop U + K.Cop U).IsPositive := by
  rw [K.Dop_add_Cop]; exact K.one_add_Z_isPositive.adjoint_conj _

theorem Dop_sub_Cop_isPositive (U : W →L[ℂ] W) : (K.Dop U - K.Cop U).IsPositive := by
  rw [K.Dop_sub_Cop]; exact K.one_sub_Z_isPositive.adjoint_conj _

theorem priv_adjoint_comp {q : ℝ} {U : W →L[ℂ] W} (hU : OracleCircuit.IsUnitary U) :
    (K.priv q U)† ∘L K.priv q U = 1 :=
  (K.priv_isUnitary q hU).1

/-- The generator of the private unitary is the three-phase generator (`opt:eq:omega`). -/
theorem gen_priv {q : ℝ} (hq : 0 < q) {U : W →L[ℂ] W} (hU : OracleCircuit.IsUnitary U) {w : ℂ}
    (hw : ‖w‖ < 1) : gen (K.priv q U) K.E w = Omega q (K.Cop U) (K.Dop U) w := by
  rw [← K.omega_eq hq hU hw, gen, mul_def, comp_assoc]

/-- **The transfer of the factor cascade** (`opt:eq:finite-F`): on the unit disk,
`F_m(w) = u(w)^m` with the Cayley step of `Ω = Tail.Omega q C D`. -/
theorem transfer_cascade_factor [FiniteDimensional ℂ P] {q : ℝ} (hq : 0 < q)
    {U : W →L[ℂ] W} (hU : OracleCircuit.IsUnitary U) {v : ℝ} (hv : 0 ≤ v) (m : ℕ) {w : ℂ}
    (hw : ‖w‖ < 1) :
    cascTransfer (K.priv q U) K.E v m w = cayStep v (Omega q (K.Cop U) (K.Dop U) w) ^ m := by
  have hacc : ∀ x, 0 ≤ (⟪x, gen (K.priv q U) K.E w x⟫_ℂ).re := by
    intro x
    rw [K.gen_priv hq hU hw]
    exact re_inner_Omega_nonneg hq (K.one_sub_Dop_isPositive hU.1)
      (K.Dop_add_Cop_isPositive U) (K.Dop_sub_Cop_isPositive U) hw x
  rw [← K.gen_priv hq hU hw]
  unfold cascTransfer cascA cascB cascC cascD
  exact transfer_cascade hv (K.priv q U) (K.priv_adjoint_comp hU) K.E K.E_isometry m hw hacc

end Known

end

end SignedFactorSimulation
