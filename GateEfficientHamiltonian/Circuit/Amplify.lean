import GateEfficientHamiltonian.Circuit.Ideal

/-!
# Amplification and the error of the ideal circuit

The clean embedding `io` places the system on the all-zero configuration.  One
oblivious amplification round of the ideal LCU circuit is
`AMP = -(L ∘ Z ∘ L† ∘ Z ∘ L)` with the clean-subspace reflection `Z`; on clean
inputs it is the released reflection round `reflectedAmplification io (L ∘ io)`
(`AMP_io`).

The successful block `io† L io` equals the successful block of the released
amplified smoothing construction (`block_eq`), so by `amplified_error_le` the
two amplified circuits have the same full-output error against the Cayley
power.  Together with the released filter and Cayley estimates this gives the
error bound `amp_error` of the ideal circuit against the exact exponential.
-/

namespace SparseHamiltonian.GateCircuit.Sim

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators
open ChronologicalResolvent GlobalColligation ChronologicalCatalyst GlobalResolvent
  CoherentReuse

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### The clean embedding and the clean reflection -/

/-- The all-zero configuration. -/
abbrev cfg0 : Cfg (Wire a m r K) := fun _ => false

/-- The clean embedding: every wire is zero. -/
def io : P →L[ℂ] Reg (Wire a m r K) P :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Cfg (Wire a m r K) => P)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun x => if x = cfg0 then (1 : P →L[ℂ] P) else 0)

omit [CompleteSpace P] in
theorem io_apply (ψ : P) : io (a := a) (m := m) (r := r) (K := K) ψ = bas cfg0 ψ := by
  apply PiLp.ext
  intro x
  simp only [io, comp_apply, bas_apply]
  split_ifs with h <;> simp [h]

theorem io_adjoint_apply (v : Reg (Wire a m r K) P) :
    ((io (a := a) (m := m) (r := r) (K := K) (P := P))†) v = v cfg0 := by
  apply ext_inner_right ℂ
  intro p
  rw [adjoint_inner_left, io_apply, inner_bas_right]

theorem io_isometry : (io (a := a) (m := m) (r := r) (K := K) (P := P))† ∘L io = 1 := by
  ext p
  rw [comp_apply, io_adjoint_apply, io_apply, bas_apply, if_pos rfl]
  rfl

omit [CompleteSpace P] in
theorem io_norm_le : ‖io (a := a) (m := m) (r := r) (K := K) (P := P)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro p
  rw [one_mul, io_apply, norm_bas]

/-- Reflection about the clean subspace. -/
def ZR : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P := rangeReflection io

theorem ZR_apply (ψ : Reg (Wire a m r K) P) :
    ZR ψ = (2 : ℂ) • bas cfg0 (ψ cfg0) - ψ := by
  simp only [ZR, rangeReflection, sub_apply, smul_apply, comp_apply, io_adjoint_apply, io_apply,
    one_apply_eq_self]

theorem ZR_isUnitary : IsUnitary (ZR (a := a) (m := m) (r := r) (K := K) (P := P)) := by
  have h : ZR (a := a) (m := m) (r := r) (K := K) (P := P) ∘L ZR = 1 :=
    rangeReflection_comp_self _ io_isometry
  have ha : (ZR (a := a) (m := m) (r := r) (K := K) (P := P))† = ZR :=
    rangeReflection_adjoint _
  constructor
  · rw [star_eq_adjoint, ha, mul_def, h]
  · rw [star_eq_adjoint, ha, mul_def, h]

theorem preserves_ZR : Preserves Clean (ZR (a := a) (m := m) (r := r) (K := K) (P := P)) := by
  intro ψ hψ x hx
  have hx0 : x ≠ cfg0 := by
    intro h
    apply hx
    rw [h]
    intro w _
    rfl
  rw [ZR_apply]
  simp [bas_apply, hx0, hψ x hx]

theorem pres2_ZR : Pres2 Clean (ZR (a := a) (m := m) (r := r) (K := K) (P := P)) := by
  refine ⟨preserves_ZR, ?_⟩
  rw [show (ZR (a := a) (m := m) (r := r) (K := K) (P := P))† = ZR from rangeReflection_adjoint _]
  exact preserves_ZR

/-! ### One amplification round of the ideal LCU circuit -/

variable {L : ℕ}

/-- The ideal amplified circuit. -/
def AMP (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ)
    (UJ D : Vsp a P →L[ℂ] Vsp a P) (N : ℕ) : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P :=
  -(LCU hL nOf wt c σ UJ D N ∘L ZR ∘L (LCU hL nOf wt c σ UJ D N)† ∘L ZR ∘L
    LCU hL nOf wt c σ UJ D N)

theorem AMP_io (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ)
    (UJ D : Vsp a P →L[ℂ] Vsp a P) (N : ℕ)
    (hLCU : LCU (K := K) (m := m) hL nOf wt c σ UJ D N ∘L (LCU hL nOf wt c σ UJ D N)† = 1) :
    AMP (K := K) (m := m) hL nOf wt c σ UJ D N ∘L io =
      reflectedAmplification io (LCU hL nOf wt c σ UJ D N ∘L io) := by
  set X := LCU (K := K) (m := m) hL nOf wt c σ UJ D N
  have e : X ∘L ((1 : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P) ∘L X†) = X ∘L X† := by
    ext v; rfl
  have h1 : rangeReflection (X ∘L io) = X ∘L ZR ∘L X† := by
    simp only [rangeReflection, ZR, adjoint_comp, comp_sub, sub_comp, comp_smul, smul_comp,
      comp_assoc]
    rw [e, hLCU]
  rw [reflectedAmplification, h1]
  simp only [AMP, neg_comp, comp_assoc]
  rfl

theorem isometry_comp {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : F →L[ℂ] G) (B : E →L[ℂ] F) (hA : A† ∘L A = 1) (hB : B† ∘L B = 1) :
    (A ∘L B)† ∘L (A ∘L B) = 1 := by
  rw [adjoint_comp, comp_assoc, ← comp_assoc (A†) A B, hA]
  exact hB

/-- The successful block of the ideal LCU circuit as an operator. -/
theorem lcu_compression (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (N : ℕ)
    (hn : ∀ ℓ, 0 < nOf ℓ ∧ nOf ℓ ≤ N) (hN : N ≤ cap r) (hr : 0 < r)
    (wt : Fin L → ℝ) (hwt : ∑ ℓ, |wt ℓ| = 2) (c κ σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1)
    (hκ : κ = 1 - c) (UJ D : Vsp a P →L[ℂ] Vsp a P) (hUJ : UJ ∘L UJ† = 1) :
    (io (a := a) (m := m) (r := r) (K := K) (P := P))† ∘L
        (LCU (K := K) (m := m) hL nOf wt c σ UJ D N ∘L io) =
      ∑ ℓ, ((wt ℓ / 2 : ℝ) : ℂ) • successfulBlock (V := HV a m P) (blkA c (2 ^ m))
        (netB (m := m) c σ UJ ∘L diagV D) (netC (m := m) c σ UJ)
        (netG (m := m) c κ σ UJ ∘L diagV D) (nOf ℓ) := by
  ext ψ
  apply ext_inner_left ℂ
  intro ψ'
  rw [comp_apply, adjoint_inner_right, comp_apply, io_apply, io_apply]
  exact lcu_block hL nOf N hn hN hr wt hwt c κ σ hunit hκ UJ D hUJ ψ ψ'

/-! ### The released amplified smoothing block -/

/-- The released successful block is the signed sum of reuse blocks. -/
theorem smoothing_block_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] (coef : ℕ → ℝ) (d : ℕ) (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (G : V →L[ℂ] V) :
    SmoothingLCU.successfulBlock coef d A B C G =
      (2 : ℂ)⁻¹ • ∑ i, (ReuseWeights.weight coef d i : ℂ) •
        CoherentReuse.successfulBlock A B C G (ReuseWeights.length d i) := by
  unfold SmoothingLCU.successfulBlock SmoothingLCU.output SmoothingLCU.circuit SmoothingLCU.input
  rw [CoherentLCU.branch_successful_compression]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact fullReuse_compression A B C G (ReuseWeights.length d i)

/-- Branch labels: the released finite branch index, numbered. -/
abbrev labEquiv (d : ℕ) : ReuseWeights.Index d ≃ Fin ((d + 1) + (d + 1)) := finSumFinEquiv

omit [CompleteSpace P] in
theorem reindex_block (d : ℕ) (wI : ReuseWeights.Index d → ℝ) (nI : ReuseWeights.Index d → ℕ)
    (F : ℕ → P →L[ℂ] P) :
    ∑ ℓ : Fin ((d + 1) + (d + 1)), ((wI ((labEquiv d).symm ℓ) / 2 : ℝ) : ℂ) •
        F (nI ((labEquiv d).symm ℓ)) =
      (2 : ℂ)⁻¹ • ∑ i, (wI i : ℂ) • F (nI i) := by
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv (labEquiv d).symm _ _ (fun ℓ => ?_)
  rw [smul_smul]
  congr 1
  push_cast
  ring

/-! ### Scalar schedule for a dyadic number of slots -/

theorem schedule_ge (τ δ : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (T : ℕ)
    (hT : TimeSchedule.steps τ δ ≤ T) :
    0 ≤ τ / (T : ℝ) ∧ τ / (T : ℝ) ≤ 1 / 4 ∧ (T : ℝ) * (τ / T) ^ 3 ≤ δ ∧
      (T : ℝ) * (τ / T) = τ := by
  have hS := TimeSchedule.steps_pos τ δ
  have hTpos : (0 : ℝ) < T := by exact_mod_cast lt_of_lt_of_le hS hT
  have hTge : (TimeSchedule.steps τ δ : ℝ) ≤ T := by exact_mod_cast hT
  have h4 := TimeSchedule.four_time_le_steps τ δ
  have hsq := TimeSchedule.sqrt_error_le_steps τ δ
  refine ⟨div_nonneg hτ hTpos.le, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hTpos]; linarith
  · have hratio : 0 ≤ τ ^ 3 / δ := div_nonneg (pow_nonneg hτ 3) hδ.le
    have h1 : τ ^ 3 / δ ≤ (T : ℝ) ^ 2 := by
      calc τ ^ 3 / δ = (Real.sqrt (τ ^ 3 / δ)) ^ 2 := (Real.sq_sqrt hratio).symm
        _ ≤ (T : ℝ) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hsq.trans hTge) 2
    have h2 : τ ^ 3 ≤ δ * (T : ℝ) ^ 2 := by
      have := (div_le_iff₀ hδ).mp h1; linarith
    have h3 : (T : ℝ) * (τ / T) ^ 3 = τ ^ 3 / (T : ℝ) ^ 2 := by field_simp
    rw [h3, div_le_iff₀ (by positivity)]
    linarith
  · field_simp

/-! ### Parameters of the simulator -/

/-- Cayley step for `2^m` time slots. -/
def stepW (τ : ℝ) (m : ℕ) : ℝ := τ / ((2 ^ m : ℕ) : ℝ)

/-- Filter repetitions for the error budget `ε / 3`. -/
abbrev fDepth (Q τ qbar ε : ℝ) : ℕ := SharpFilterSchedule.depth Q (τ * qbar) (ε / 3)

/-- Filter degree. -/
abbrev fDeg (Q τ qbar ε : ℝ) : ℕ := fDepth Q τ qbar ε * (SharpFilterSchedule.length Q - 1)

/-- Smoothing coefficients. -/
abbrev fCoef (Q τ qbar ε : ℝ) : ℕ → ℝ :=
  (AveragingPolynomial.filter (SharpFilterSchedule.length Q) (fDepth Q τ qbar ε)).coeff

/-- Signed branch weights, numbered. -/
def labWt (Q τ qbar ε : ℝ) : Fin ((fDeg Q τ qbar ε + 1) + (fDeg Q τ qbar ε + 1)) → ℝ :=
  fun ℓ => ReuseWeights.weight (fCoef Q τ qbar ε) (fDeg Q τ qbar ε)
    ((labEquiv (fDeg Q τ qbar ε)).symm ℓ)

/-- Branch reuse lengths, numbered. -/
def labLen (Q τ qbar ε : ℝ) : Fin ((fDeg Q τ qbar ε + 1) + (fDeg Q τ qbar ε + 1)) → ℕ :=
  fun ℓ => ReuseWeights.length (fDeg Q τ qbar ε) ((labEquiv (fDeg Q τ qbar ε)).symm ℓ)

theorem fDeg_eq (Q τ qbar ε : ℝ) :
    fDeg Q τ qbar ε = SharpFilterSchedule.degree Q (τ * qbar) (ε / 3) := rfl

theorem fDeg_pos (Q τ qbar ε : ℝ) (hQ : 1 ≤ Q) : 0 < fDeg Q τ qbar ε :=
  SharpFilterSchedule.degree_pos Q _ _ hQ

theorem labLen_spec (Q τ qbar ε : ℝ) (hQ : 1 ≤ Q) (ℓ) :
    0 < labLen Q τ qbar ε ℓ ∧ labLen Q τ qbar ε ℓ ≤ 2 * fDeg Q τ qbar ε :=
  ⟨ReuseWeights.length_pos _ (fDeg_pos Q τ qbar ε hQ) _,
    ReuseWeights.length_le _ (fDeg_pos Q τ qbar ε hQ) _⟩

theorem labWt_mass (Q τ qbar ε : ℝ) (hQ : 1 ≤ Q) : ∑ ℓ, |labWt Q τ qbar ε ℓ| = 2 := by
  have hL : 1 ≤ SharpFilterSchedule.length Q := by
    apply Nat.one_le_ceil_iff.mpr
    have := SharpFilterSchedule.length_ge Q
    linarith
  have h := ReuseWeights.concrete_absolute_mass (SharpFilterSchedule.length Q)
    (fDepth Q τ qbar ε) hL (fDeg_pos Q τ qbar ε hQ)
  rw [← h]
  exact Fintype.sum_equiv (labEquiv (fDeg Q τ qbar ε)).symm _ _ (fun ℓ => rfl)

/-! ### The released bounds in the transducer-block notation -/

/-- The released local energy identity for the transducer blocks. -/
theorem released_step (D : Vsp a P →L[ℂ] Vsp a P) (J : P →L[ℂ] Vsp a P) (w : ℝ)
    (hw0 : 0 ≤ w) (hwq : w ≤ 1 / 4) (hD : D† ∘L D = 1) (hJ : J† ∘L J = 1) (T : ℕ) (p : P)
    (v : BlockOperator.H T (Vsp a P)) :
    ‖blkA (CayleyTransfer.c w) T p + blkB (CayleyTransfer.c w) (CayleyTransfer.sigma w) J D T v‖ ^ 2 +
      ‖blkG (CayleyTransfer.c w) (CayleyTransfer.kappa w) (CayleyTransfer.sigma w) J D T v +
        blkC (CayleyTransfer.c w) (CayleyTransfer.sigma w) J T p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2 := by
  obtain ⟨_, _, hκc, hσc, _⟩ := CayleyTransfer.scalar_promises w hw0 hwq
  have h := chronological_full_energy
    (localPrivateBlock D J (CayleyTransfer.kappa w)) (((CayleyTransfer.sigma w : ℝ) : ℂ) • J)
    (((CayleyTransfer.c w : ℝ) : ℂ) • 1) ((-((CayleyTransfer.sigma w : ℝ) : ℂ)) • (J† ∘L D))
    (LocalRotation.local_step_energy D J _ _ _ hκc hσc hD hJ) T p v
  change ‖blkA (CayleyTransfer.c w) T p + blkB (CayleyTransfer.c w) (CayleyTransfer.sigma w) J D T v‖ ^ 2 +
      ‖blkC (CayleyTransfer.c w) (CayleyTransfer.sigma w) J T p +
        blkG (CayleyTransfer.c w) (CayleyTransfer.kappa w) (CayleyTransfer.sigma w) J D T v‖ ^ 2 =
      ‖p‖ ^ 2 + ‖v‖ ^ 2 at h
  rw [add_comm (blkG _ _ _ J D T v)]
  exact h

set_option maxRecDepth 8192 in
/-- The released amplified simulation, with an explicit clock budget `W`. -/
theorem released_bound (D R1 : Vsp a P →L[ℂ] Vsp a P) (J : P →L[ℂ] Vsp a P) (H : P →L[ℂ] P)
    (w Q b qbar : ℝ) (T : ℕ) (hQ : 1 ≤ Q) (hw : 0 ≤ w) (hwQuarter : w ≤ 1 / 4)
    (hD : D† ∘L D = 1) (hJ : J† ∘L J = 1)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : J† ∘L R1 ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L J‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (δ : ℝ) (hδ : 0 < δ) (hδOne : δ ≤ 1) (W : ℝ) (hW : (T : ℝ) * w * qbar = W) :
    ∃ U R : P →L[ℂ] P, CayleyTransfer.cayleyDenominator w H ∘L R = 1 ∧
      U = CayleyTransfer.cayleyNumerator w H ∘L R ∧ (U ^ T)† ∘L (U ^ T) = 1 ∧
      ‖AmplifiedSmoothing.implementation (SharpFilterSchedule.length Q)
          (SharpFilterSchedule.depth Q W δ) (blkA (CayleyTransfer.c w) T)
          (blkB (CayleyTransfer.c w) (CayleyTransfer.sigma w) J D T)
          (blkC (CayleyTransfer.c w) (CayleyTransfer.sigma w) J T)
          (blkG (CayleyTransfer.c w) (CayleyTransfer.kappa w) (CayleyTransfer.sigma w) J D T) -
        SmoothingLCU.output (P := P) (V := BlockOperator.H T (Vsp a P))
          (AveragingPolynomial.filter (SharpFilterSchedule.length Q)
            (SharpFilterSchedule.depth Q W δ)).coeff
          (SharpFilterSchedule.depth Q W δ * (SharpFilterSchedule.length Q - 1)) ∘L U ^ T‖ ≤
        2 * δ ∧
      (SharpFilterSchedule.degree Q W δ : ℝ) ≤ 128 * (W + Q * (1 + Real.log (1 / δ))) := by
  subst hW
  obtain ⟨_Γ, U, R, hRR, _hRL, hCay, hUi, _hUc, _hCost, _hIso, hImpl, hDeg⟩ :=
    SharpClockSimulation.exists_precise_implementation D R1 J H w Q b qbar T hQ hw hwQuarter
      hD hJ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ δ hδ hδOne
  exact ⟨U, R, hRR, hCay, hUi, hImpl, hDeg⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- **Error of the ideal amplified circuit.**  With `2^m` slots at least the
released subdivision count, a reuse register with `2d + 2 ≤ 2^r`, and the
clock hypotheses of the released analysis for `J = U_J ι₀`, the ideal amplified
circuit approximates the exact evolution on clean inputs within `ε`; the
filter degree obeys the released bound. -/
theorem amp_error (UJ D R1 : Vsp a P →L[ℂ] Vsp a P) (H : P →L[ℂ] P)
    (hUJ : IsUnitary UJ) (hDu : IsUnitary D)
    (τ Q b qbar ε : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : (UJ ∘L iota0)† ∘L R1 ∘L (UJ ∘L iota0) = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hm : TimeSchedule.steps τ (ε / 3) ≤ 2 ^ m) (hr : 0 < r)
    (hL : (fDeg Q τ qbar ε + 1) + (fDeg Q τ qbar ε + 1) ≤ 2 ^ r) :
    ‖AMP (K := K) (m := m) hL (labLen Q τ qbar ε) (labWt Q τ qbar ε)
        (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) UJ D
        (2 * fDeg Q τ qbar ε) ∘L io -
      io ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤ ε ∧
    (fDeg Q τ qbar ε : ℝ) ≤ 128 * (τ * qbar + Q * (1 + Real.log (1 / (ε / 3)))) := by
  have hδ : 0 < ε / 3 := by positivity
  have hδ1 : ε / 3 ≤ 1 := by linarith
  obtain ⟨hw0, hwq, hcub, hTw⟩ := schedule_ge τ (ε / 3) hτ hδ (2 ^ m) hm
  change 0 ≤ stepW τ m at hw0
  change stepW τ m ≤ 1 / 4 at hwq
  change ((2 ^ m : ℕ) : ℝ) * stepW τ m ^ 3 ≤ ε / 3 at hcub
  change ((2 ^ m : ℕ) : ℝ) * stepW τ m = τ at hTw
  have hD : D† ∘L D = 1 := unitary_adj_comp hDu
  have hUJc : UJ ∘L UJ† = 1 := unitary_comp_adj hUJ
  have hJ : (UJ ∘L iota0)† ∘L (UJ ∘L iota0) = 1 :=
    isometry_comp UJ iota0 (unitary_adj_comp hUJ) iota0_isometry
  obtain ⟨U, R, hRR, hCay, hUi, hImpl, hDeg⟩ :=
    released_bound D R1 (UJ ∘L iota0) H (stepW τ m) Q b qbar (2 ^ m) hQ hw0 hwq hD hJ hRight
      hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ (ε / 3) hδ hδ1 (τ * qbar) (by rw [hTw])
  obtain ⟨_, _, hκc, hσc, _⟩ := CayleyTransfer.scalar_promises (stepW τ m) hw0 hwq
  have hunit : CayleyTransfer.c (stepW τ m) ^ 2 + CayleyTransfer.sigma (stepW τ m) ^ 2 = 1 := by
    linarith
  have hLf : 1 ≤ SharpFilterSchedule.length Q := by
    apply Nat.one_le_ceil_iff.mpr
    have := SharpFilterSchedule.length_ge Q
    linarith
  have hd0 : 0 < fDeg Q τ qbar ε := fDeg_pos Q τ qbar ε hQ
  have hJrel := SmoothingLCU.output_isometry (P := P) (V := HV a m P) (fCoef Q τ qbar ε)
    (fDeg Q τ qbar ε) hd0 (ReuseWeights.concrete_absolute_mass _ _ hLf hd0)
  have hTrel := AmplifiedSmoothing.prepared_isometry (SharpFilterSchedule.length Q)
    (fDepth Q τ qbar ε) hLf hd0 _ _ _ _
    (released_step D (UJ ∘L iota0) (stepW τ m) hw0 hwq hD hJ (2 ^ m))
  -- the ideal LCU circuit
  have hn : ∀ ℓ, 0 < labLen Q τ qbar ε ℓ ∧ labLen Q τ qbar ε ℓ ≤ 2 * fDeg Q τ qbar ε :=
    labLen_spec Q τ qbar ε hQ
  have hN : 2 * fDeg Q τ qbar ε ≤ cap r := by
    have := cap_succ r
    omega
  have hLCUu := LCU_isUnitary (K := K) (m := m) hL (labLen Q τ qbar ε) (labWt Q τ qbar ε)
    (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) hunit UJ D hUJ hDu
    (2 * fDeg Q τ qbar ε)
  have hT' := isometry_comp (E := P) (F := Reg (Wire a m r K) P) (G := Reg (Wire a m r K) P) _
    (io (a := a) (m := m) (r := r) (K := K) (P := P)) (unitary_adj_comp hLCUu) io_isometry
  have hB := lcu_compression (K := K) (m := m) hL (labLen Q τ qbar ε) (2 * fDeg Q τ qbar ε) hn hN
    hr (labWt Q τ qbar ε) (labWt_mass Q τ qbar ε hQ) (CayleyTransfer.c (stepW τ m))
    (CayleyTransfer.kappa (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) hunit hκc UJ D hUJc
  rw [blkB_net, blkC_net, blkG_net _ _ _ UJ D hUJc] at hB
  have hB' : (io (a := a) (m := m) (r := r) (K := K) (P := P))† ∘L
      (LCU (K := K) (m := m) hL (labLen Q τ qbar ε) (labWt Q τ qbar ε)
        (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) UJ D
        (2 * fDeg Q τ qbar ε) ∘L io) =
      (SmoothingLCU.output (P := P) (V := HV a m P) (fCoef Q τ qbar ε) (fDeg Q τ qbar ε))† ∘L
        AmplifiedSmoothing.prepared (SharpFilterSchedule.length Q) (fDepth Q τ qbar ε)
          (blkA (CayleyTransfer.c (stepW τ m)) (2 ^ m))
          (blkB (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m))
            (UJ ∘L iota0) D (2 ^ m))
          (blkC (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m))
            (UJ ∘L iota0) (2 ^ m))
          (blkG (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.kappa (stepW τ m))
            (CayleyTransfer.sigma (stepW τ m)) (UJ ∘L iota0) D (2 ^ m)) := by
    rw [hB]
    change _ = SmoothingLCU.successfulBlock (fCoef Q τ qbar ε) (fDeg Q τ qbar ε) _ _ _ _
    rw [smoothing_block_eq]
    exact reindex_block (fDeg Q τ qbar ε) _ _ (fun n => successfulBlock _ _ _ _ n)
  have hAmp := GateBlockTransfer.amplified_error_le (P := P)
    (K := PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := HV a m P) (fDeg Q τ qbar ε)))
    (K' := Reg (Wire a m r K) P)
    (SmoothingLCU.output (P := P) (V := HV a m P) (fCoef Q τ qbar ε) (fDeg Q τ qbar ε))
    (AmplifiedSmoothing.prepared (SharpFilterSchedule.length Q) (fDepth Q τ qbar ε)
      (blkA (CayleyTransfer.c (stepW τ m)) (2 ^ m))
      (blkB (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m))
        (UJ ∘L iota0) D (2 ^ m))
      (blkC (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m))
        (UJ ∘L iota0) (2 ^ m))
      (blkG (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.kappa (stepW τ m))
        (CayleyTransfer.sigma (stepW τ m)) (UJ ∘L iota0) D (2 ^ m)))
    (io (a := a) (m := m) (r := r) (K := K) (P := P))
    (LCU (K := K) (m := m) hL (labLen Q τ qbar ε) (labWt Q τ qbar ε)
        (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) UJ D
        (2 * fDeg Q τ qbar ε) ∘L io)
    hJrel hTrel io_isometry hT' hB' (U ^ (2 ^ m)) hUi
  have hAmp2 := hAmp.trans hImpl
  -- Cayley powers against the exponential
  have hRR' : CayleyTransfer.cayleyDenominator (stepW τ m) H * R = 1 := by
    rw [mul_def]; exact hRR
  have hCayErr := CayleyApproximation.hamiltonian_cayley_error H R (stepW τ m) hw0
    (by linarith) hSelf hH hRR' (2 ^ m)
  have hTwC : ((2 ^ m : ℕ) : ℂ) * (stepW τ m : ℂ) = (τ : ℂ) := by exact_mod_cast hTw
  have hScalar : -Complex.I * ((2 ^ m : ℕ) : ℂ) * (stepW τ m : ℂ) = -Complex.I * (τ : ℂ) := by
    rw [mul_assoc, hTwC]
  have hUT : (CayleyTransfer.cayleyNumerator (stepW τ m) H * R) ^ (2 ^ m) = U ^ (2 ^ m) := by
    rw [hCay, mul_def]
  rw [hUT, hScalar] at hCayErr
  have hTarget : ‖U ^ (2 ^ m) - NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤ ε / 3 :=
    hCayErr.trans hcub
  refine ⟨?_, hDeg⟩
  -- assemble
  rw [AMP_io hL _ _ _ _ UJ D _ (unitary_comp_adj hLCUu)]
  calc _ ≤ ‖reflectedAmplification io (LCU (K := K) (m := m) hL (labLen Q τ qbar ε)
          (labWt Q τ qbar ε) (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m))
          UJ D (2 * fDeg Q τ qbar ε) ∘L io) - io ∘L U ^ (2 ^ m)‖ +
          ‖io ∘L U ^ (2 ^ m) - io ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * (ε / 3) + ε / 3 := by
        apply add_le_add hAmp2
        rw [← comp_sub]
        calc ‖io ∘L (U ^ (2 ^ m) - NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H))‖
            ≤ ‖(io (a := a) (m := m) (r := r) (K := K) (P := P))‖ *
                ‖U ^ (2 ^ m) - NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ :=
              opNorm_comp_le _ _
          _ ≤ 1 * (ε / 3) := mul_le_mul io_norm_le hTarget (norm_nonneg _) zero_le_one
          _ = ε / 3 := one_mul _
    _ = ε := by ring

end

end SparseHamiltonian.GateCircuit.Sim
