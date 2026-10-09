import GateEfficientBinarySelect.Identity
import GateEfficientQuadrature.Solver

/-!
# Branch samples, branch geometry and the clock promises

For the power-of-two source mesh with the `2^m` left-endpoint nodes `v_u = u T / 2^m`
(`GateQuad.vQ p (2^m)`, every source label a node):

* `startB_vQ`, `durB_vQ`, `addrB_vQ`: the start `u' T / 2^m`, the duration `(2^m - u') T / 2^m`
  and the sample addresses `addrN T / 2^(2m)` of the branch-dependent meshes of
  `GateSelect.ODE` are points of the grid of `2^(2m)` points, at the integer addresses `addrN`
  computed by the address program;
* `HbB`, `LbB`: the lifted Hamiltonian and dissipative parts of the sample at the branch address
  (zero beyond the last slot); `gensB_eq`: the represented slot generator `L + i H` of a branch is
  the lifted sample `M̂` at its address;
* `clockB`: **the clock promises** of the released simulator for the private family `privFamB`
  and the normalised branch Hamiltonian `GateSelect.ODE.branchHB` at every label and slot, with
  the label-independent constants `Q = width(4s, γ)` and `q̄ = moment γ`: the branch scale enters
  through the Cayley parameter `γ (2^m - u') / 2^m ≤ γ` computed by the arithmetic.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinarySelect

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open CayleyClockInterface
open SparseHamiltonian.GateBinaryODETime (clock_at)
open SparseHamiltonian.GateODE (Label ClockPromise)
open SparseHamiltonian.GateODE.Time (TParams)
open SparseHamiltonian.GateSelect.ODE (startB durB addrB branchHB)
open SparseHamiltonian.GateQuad (vQ)
open SparseHamiltonian.GatePointerEncoding (wordEquivFin wordValue)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### Samples at the branch addresses -/

section Samples

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s k : ℕ}

/-- The lifted Hamiltonian part of the sample at the address of slot `r` of the branch of the
source label `z` (zero beyond the last slot). -/
def HbB (p : TParams) (D : Data (X × Fin (2 ^ (2 * p.m))) n Z s) (en : Cfg (Fin k) ≃ n) (x : X)
    (z : Bool × (Fin p.m → Bool)) (r : ℕ) : Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ :=
  if h : r < 2 ^ p.m then hLift D en (x, addrF z r h) else 0

/-- The lifted dissipative part of the sample at the branch address (zero beyond the last
slot). -/
def LbB (p : TParams) (D : Data (X × Fin (2 ^ (2 * p.m))) n Z s) (en : Cfg (Fin k) ≃ n) (x : X)
    (z : Bool × (Fin p.m → Bool)) (r : ℕ) : Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ :=
  if h : r < 2 ^ p.m then lLift D en (x, addrF z r h) else 0

theorem HbB_of_lt (p : TParams) (D : Data (X × Fin (2 ^ (2 * p.m))) n Z s)
    (en : Cfg (Fin k) ≃ n) (x : X) (z : Bool × (Fin p.m → Bool)) (r : ℕ) (hr : r < 2 ^ p.m) :
    HbB p D en x z r = hLift D en (x, addrF z r hr) := dif_pos hr

theorem LbB_of_lt (p : TParams) (D : Data (X × Fin (2 ^ (2 * p.m))) n Z s)
    (en : Cfg (Fin k) ≃ n) (x : X) (z : Bool × (Fin p.m → Bool)) (r : ℕ) (hr : r < 2 ^ p.m) :
    LbB p D en x z r = lLift D en (x, addrF z r hr) := dif_pos hr

/-- The represented slot generator `L + i H` of a branch is the lifted sample `M̂` at its
address. -/
theorem gensB_eq (p : TParams) (D : Data (X × Fin (2 ^ (2 * p.m))) n Z s)
    (en : Cfg (Fin k) ≃ n) (x : X) (z : Bool × (Fin p.m → Bool)) (r : ℕ) (hr : r < 2 ^ p.m) :
    GateODE.Time.gens (HbB p D en x z) (LbB p D en x z) r = mLift D en (x, addrF z r hr) := by
  rw [GateODE.Time.gens, HbB_of_lt p D en x z r hr, LbB_of_lt p D en x z r hr]
  have h := gen_lift D en (x, addrF z r hr)
  unfold GateODE.gen at h
  rw [← neg_neg (mLift D en (x, addrF z r hr)), ← h, neg_neg]

theorem HbB_self (p : TParams) (D : Data (X × Fin (2 ^ (2 * p.m))) n Z s)
    (en : Cfg (Fin k) ≃ n) (x : X) (z : Bool × (Fin p.m → Bool)) (r : ℕ) :
    star (HbB p D en x z r) = HbB p D en x z r := by
  unfold HbB
  split_ifs
  · unfold hLift
    rw [← qlift_star, SparseValuePrecision.matrixOperator_star_eq _
      (ODEMatrixEnergy.hamiltonianPart_isHermitian _)]
  · rw [ContinuousLinearMap.star_eq_adjoint]
    exact map_zero _

theorem LbB_self (p : TParams) (D : Data (X × Fin (2 ^ (2 * p.m))) n Z s)
    (en : Cfg (Fin k) ≃ n) (x : X) (z : Bool × (Fin p.m → Bool)) (r : ℕ) :
    star (LbB p D en x z r) = LbB p D en x z r := by
  unfold LbB
  split_ifs
  · unfold lLift
    rw [← qlift_star, SparseValuePrecision.matrixOperator_star_eq _
      (ODEMatrixEnergy.dissipativePart_isHermitian _)]
  · rw [ContinuousLinearMap.star_eq_adjoint]
    exact map_zero _

/-- The lifted Hamiltonian part of every branch sample has norm at most `√(2s) η_H`. -/
theorem HbB_norm_le (p : TParams) (D : Data (X × Fin (2 ^ (2 * p.m))) n Z s)
    (en : Cfg (Fin k) ≃ n) (x : X) (η : ℝ) (hη : 0 ≤ η)
    (hr : ∀ g i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ η ^ 2)
    (hc : ∀ g j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ η ^ 2)
    (z : Bool × (Fin p.m → Bool)) (r : ℕ) :
    ‖HbB p D en x z r‖ ≤ Real.sqrt (2 * (s : ℝ)) * η := by
  unfold HbB
  split_ifs with h
  · exact (norm_qlift_le _ _).trans (norm_matrixOperator_le D (x, addrF z r h) _
      (ODEMatrixEnergy.hamiltonianPart_isHermitian _)
      (fun i j hij hji => by simp [ODEMatrixEnergy.hamiltonianPart_apply, hij, hji]) η hη
      (hr _) (hc _))
  · rw [norm_zero]
    positivity

/-- The lifted dissipative part of every branch sample has norm at most `√(2s) η_D`. -/
theorem LbB_norm_le (p : TParams) (D : Data (X × Fin (2 ^ (2 * p.m))) n Z s)
    (en : Cfg (Fin k) ≃ n) (x : X) (η : ℝ) (hη : 0 ≤ η)
    (hr : ∀ g i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ η ^ 2)
    (hc : ∀ g j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ η ^ 2)
    (z : Bool × (Fin p.m → Bool)) (r : ℕ) :
    ‖LbB p D en x z r‖ ≤ Real.sqrt (2 * (s : ℝ)) * η := by
  unfold LbB
  split_ifs with h
  · exact (norm_qlift_le _ _).trans (norm_matrixOperator_le D (x, addrF z r h) _
      (ODEMatrixEnergy.dissipativePart_isHermitian _)
      (fun i j hij hji => by simp [ODEMatrixEnergy.dissipativePart_apply, hij, hji]) η hη
      (hr _) (hc _))
  · rw [norm_zero]
    positivity

/-- The lifted dissipative part of every branch sample is accretive. -/
theorem LbB_psd (p : TParams) (D : Data (X × Fin (2 ^ (2 * p.m))) n Z s)
    (en : Cfg (Fin k) ≃ n) (x : X)
    (hPSD : ∀ g, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.dissipativePart (D.matrix (x, g))) w)).re)
    (z : Bool × (Fin p.m → Bool)) (r : ℕ) (w : Reg (Fin k) ℂ) :
    0 ≤ (inner ℂ w (LbB p D en x z r w)).re := by
  unfold LbB
  split_ifs with h
  · exact re_inner_qlift_nonneg en _ (hPSD _) w
  · simp

end Samples

/-! ### The branch geometry of the left-endpoint mesh -/

section Geometry

variable (p : TParams)

theorem M_cast : ((p.M : ℕ) : ℝ) = 2 ^ p.m := by push_cast; rfl

/-- The start of the branch of a source label is `u' T / 2^m`. -/
theorem startB_vQ (z : Bool × (Fin p.m → Bool)) :
    startB p (vQ p p.M) z = (startW z : ℝ) * p.T / p.M := by
  unfold startB vQ startW
  by_cases h1 : z.1 = true
  · have h2 : wordValue z.2 < p.M := GatePointerEncoding.wordValue_lt_pow z.2
    simp only [h1, if_true, h2]
  · simp [h1]

/-- The duration of the branch of a source label is `(2^m - u') T / 2^m`. -/
theorem durB_vQ (z : Bool × (Fin p.m → Bool)) :
    durB p (vQ p p.M) z = ((2 ^ p.m - startW z : ℕ) : ℝ) * p.T / p.M := by
  unfold durB
  rw [startB_vQ]
  have hu := startW_lt z
  have hM : ((p.M : ℕ) : ℝ) ≠ 0 := by exact_mod_cast p.M_pos.ne'
  push_cast [Nat.cast_sub hu.le] at hM ⊢
  field_simp

/-- **The sample addresses of the branch-dependent meshes are points of the grid**: slot `r` of
the branch of `z` samples at `addrN z r · T / 2^(2m)`. -/
theorem addrB_vQ (z : Bool × (Fin p.m → Bool)) (r : ℕ) :
    addrB p (vQ p p.M) z r = (addrN z r : ℝ) * p.T / 2 ^ (2 * p.m) := by
  unfold addrB
  rw [startB_vQ, durB_vQ]
  have hu := startW_lt z
  unfold addrN
  push_cast [Nat.cast_sub hu.le]
  rw [pow_mul']
  have h2 : (2 : ℝ) ^ p.m ≠ 0 := by positivity
  field_simp

end Geometry

/-! ### The clock promises -/

section Clock

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}

/-- **The clock promises at every label and slot** of the private family `privFamB` for the
normalised branch Hamiltonian `branchHB` of the lifted samples at the branch addresses, with the
constants `width(4s, γ)` and `moment γ` that do not depend on the label. -/
theorem clockB (p : TParams) (D : Data (X × Fin (2 ^ (2 * p.m))) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (σ : ℕ) (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (x : X) (ηH ηD ρ γ : ℝ) (hηH : 0 ≤ ηH) (hηD : 0 ≤ ηD) (hρ : ρ = ηH + p.R * ηD)
    (hρpos : 0 < ρ) (hγ : 0 < γ) (hT : 0 < p.T) (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hε1 : p.ε ≤ 1)
    (hTD : 0 ≤ p.T * p.lamD) (hτ : p.tau = p.T * (Real.sqrt (4 * (s : ℝ)) * ρ) / γ)
    (hrH : ∀ g i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ ηH ^ 2)
    (hcH : ∀ g j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ ηH ^ 2)
    (hrD : ∀ g i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ ηD ^ 2)
    (hcD : ∀ g j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ ηD ^ 2)
    (z : Label p.m p.l) (r : ℕ) (hr : r < 2 ^ p.m) :
    ClockPromise (P := Reg (Fin k) ℂ) (a := k + 3) (UJop (R := ℂ) (hadUJ4 k σ hσ))
      (privFamB p D en x ρ γ z r)
      (branchHB p (vQ p p.M) (HbB p D en x) (LbB p D en x) z r)
      (width (4 * (s : ℝ)) γ) (moment γ) := by
  have hu := startW_lt z.1
  set γ' := γ * (((2 ^ p.m - startW z.1 : ℕ) : ℝ) / 2 ^ p.m) with hγ'
  have hfr0 : 0 ≤ ((2 ^ p.m - startW z.1 : ℕ) : ℝ) / 2 ^ p.m := by positivity
  have hfr1 : ((2 ^ p.m - startW z.1 : ℕ) : ℝ) / 2 ^ p.m ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (2 ^ p.m - startW z.1 : ℕ) ≤ 2 ^ p.m := Nat.sub_le _ _
    exact_mod_cast this
  have h0 : 0 ≤ γ' := mul_nonneg hγ.le hfr0
  have h1 : γ' ≤ γ := mul_le_of_le_one_right hγ.le hfr1
  have hsq : 0 < Real.sqrt (4 * (s : ℝ)) := by
    rw [hs]
    exact Real.sqrt_pos.mpr (by positivity)
  have hsc : durB p (vQ p p.M) z.1 / p.tau = γ' / (ρ * Real.sqrt (4 * (s : ℝ))) := by
    rw [durB_vQ, hτ, hγ', M_cast]
    have h2 : (2 : ℝ) ^ p.m ≠ 0 := by positivity
    field_simp
  have h := clock_at D en σ hσ hs hrange (x, addrF z.1 r hr) (p.nodeW z.2) ηH ηD ρ p.R γ γ'
    hηH hηD hρ hρpos (p.nodeW_abs_le hg hε hε1 hTD z.2) h0 h1 (hrH _) (hcH _) (hrD _) (hcD _)
  rw [privFamB, dif_pos hr, branchHB, hsc, HbB_of_lt p D en x z.1 r hr,
    LbB_of_lt p D en x z.1 r hr]
  exact h

end Clock

end

end SparseHamiltonian.GateBinarySelect
