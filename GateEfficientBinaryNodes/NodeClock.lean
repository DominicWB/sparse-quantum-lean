import GateEfficientBinaryNodes.NodeIdentity
import GateEfficientBinaryNodes.SelectIntegrated

/-!
# Branch samples, branch geometry and the clock promises for computed nodes

For the computed nodes `v_u = word u · T / 2^μ` of a node program (`vN`, every source label a
node):

* `startB_vN`, `durB_vN`, `addrB_vN`: the start `ν' T / 2^μ`, the duration `(2^μ - ν') T / 2^μ`
  and the sample addresses `addrNN T / 2^(μ+m)` of the branch-dependent meshes of
  `GateSelect.ODE` are points of the grid of `2^(μ+m)` points, at the integer addresses `addrNN`
  computed by the address program;
* `HbN`, `LbN`: the lifted Hamiltonian and dissipative parts of the sample at the data grid
  point `addrFN` of the branch address, the top `nd` bits of `addrNN` (zero beyond the last
  slot); `gensN_eq`: the represented slot generator `L + i H` of a branch is the lifted sample
  `M̂` at that grid point. The represented samples are read at the rounded time
  `addrFN · T / 2^nd ≤ addrNN · T / 2^(μ+m)`; the rounding is part of the represented-sample
  error of the integrated certificate (`NodePub.sampleErrNQ`);
* `clockN`: **the clock promises** of the released simulator for the private family `privFamN`
  and the normalised branch Hamiltonian `GateSelect.ODE.branchHB` at every label and slot, with
  the label-independent constants `Q = width(4s, γ)` and `q̄ = moment γ`, from the energy bounds
  of the sample the slot reads (`SampleOK` at `addrFN`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryNodes

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open CayleyClockInterface
open SparseHamiltonian.GateBinaryODETime (clock_at)
open SparseHamiltonian.GateODE (Label ClockPromise)
open SparseHamiltonian.GateODE.Time (TParams)
open SparseHamiltonian.GateSelect.ODE (startB durB addrB branchHB)
open SparseHamiltonian.GatePointerEncoding (wordEquivFin wordValue)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### The computed nodes -/

section Geometry

variable (p : TParams) {Zn : Type}

/-- **The computed nodes**: `v_q = word w_q · T / 2^μ` for the node index `q < 2^m` with word
`w_q`, and `T` beyond. -/
def vN (mu : ℕ) (N : NodeProg p.m mu Zn) (q : ℕ) : ℝ :=
  if h : q < 2 ^ p.m then (wordValue (N.word ((wordEquivFin p.m).symm ⟨q, h⟩)) : ℝ) * p.T / 2 ^ mu
  else p.T

theorem wordEquivFin_symm_word (w : Fin p.m → Bool) :
    (wordEquivFin p.m).symm ⟨wordValue w, GatePointerEncoding.wordValue_lt_pow w⟩ = w := by
  apply (wordEquivFin p.m).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  rw [GatePointerEncoding.wordEquivFin_apply, GatePointerEncoding.wordFin_val]

theorem vN_word (mu : ℕ) (N : NodeProg p.m mu Zn) (w : Fin p.m → Bool) :
    vN p mu N (wordValue w) = (wordValue (N.word w) : ℝ) * p.T / 2 ^ mu := by
  unfold vN
  rw [dif_pos (GatePointerEncoding.wordValue_lt_pow w), wordEquivFin_symm_word]

/-- The computed nodes lie in `[0, T]`. -/
theorem vN_mem (hT : 0 ≤ p.T) (mu : ℕ) (N : NodeProg p.m mu Zn) :
    ∀ q < p.M, 0 ≤ vN p mu N q ∧ vN p mu N q ≤ p.T := by
  intro q hq
  have hq' : q < 2 ^ p.m := hq
  unfold vN
  rw [dif_pos hq']
  have hw := GatePointerEncoding.wordValue_lt_pow (N.word ((wordEquivFin p.m).symm ⟨q, hq'⟩))
  have hwR : (wordValue (N.word ((wordEquivFin p.m).symm ⟨q, hq'⟩)) : ℝ) ≤ 2 ^ mu := by
    exact_mod_cast hw.le
  have h2 : (0 : ℝ) < 2 ^ mu := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ h2]
  nlinarith

/-- The start of the branch of a source label is `ν' T / 2^μ`. -/
theorem startB_vN (mu : ℕ) (N : NodeProg p.m mu Zn) (z : Bool × (Fin p.m → Bool)) :
    startB p (vN p mu N) z = (startWN N z : ℝ) * p.T / 2 ^ mu := by
  unfold startB startWN
  by_cases h1 : z.1 = true
  · simp only [h1, if_true]
    exact vN_word p mu N z.2
  · simp [h1]

/-- The duration of the branch of a source label is `(2^μ - ν') T / 2^μ`. -/
theorem durB_vN (mu : ℕ) (N : NodeProg p.m mu Zn) (z : Bool × (Fin p.m → Bool)) :
    durB p (vN p mu N) z = ((2 ^ mu - startWN N z : ℕ) : ℝ) * p.T / 2 ^ mu := by
  unfold durB
  rw [startB_vN]
  have hu := startWN_lt N z
  push_cast [Nat.cast_sub hu.le]
  have h2 : (2 : ℝ) ^ mu ≠ 0 := by positivity
  field_simp

/-- **The sample addresses of the branch-dependent meshes are points of the grid**: slot `r` of
the branch of `z` samples at `addrNN z r · T / 2^(μ+m)`. -/
theorem addrB_vN (mu : ℕ) (N : NodeProg p.m mu Zn) (z : Bool × (Fin p.m → Bool)) (r : ℕ) :
    addrB p (vN p mu N) z r = (addrNN N z r : ℝ) * p.T / 2 ^ (mu + p.m) := by
  unfold addrB
  rw [startB_vN, durB_vN]
  have hu := startWN_lt N z
  unfold addrNN
  push_cast [Nat.cast_sub hu.le]
  rw [pow_add]
  have h2 : (2 : ℝ) ^ mu ≠ 0 := by positivity
  have h3 : (2 : ℝ) ^ p.m ≠ 0 := by positivity
  field_simp

end Geometry

/-! ### Samples at the data grid points -/

section Samples

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s k : ℕ} {Zn : Type}

/-- The lifted Hamiltonian part of the sample at the data grid point of slot `r` of the branch of
the source label `z` (zero beyond the last slot). -/
def HbN (p : TParams) (mu nd : ℕ) (hnd : nd ≤ mu + p.m) (N : NodeProg p.m mu Zn)
    (D : Data (X × Fin (2 ^ nd)) n Z s) (en : Cfg (Fin k) ≃ n) (x : X)
    (z : Bool × (Fin p.m → Bool)) (r : ℕ) : Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ :=
  if h : r < 2 ^ p.m then hLift D en (x, addrFN nd hnd N z r h) else 0

/-- The lifted dissipative part of the sample at the data grid point (zero beyond the last
slot). -/
def LbN (p : TParams) (mu nd : ℕ) (hnd : nd ≤ mu + p.m) (N : NodeProg p.m mu Zn)
    (D : Data (X × Fin (2 ^ nd)) n Z s) (en : Cfg (Fin k) ≃ n) (x : X)
    (z : Bool × (Fin p.m → Bool)) (r : ℕ) : Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ :=
  if h : r < 2 ^ p.m then lLift D en (x, addrFN nd hnd N z r h) else 0

variable (p : TParams) (mu nd : ℕ) (hnd : nd ≤ mu + p.m) (N : NodeProg p.m mu Zn)

theorem HbN_of_lt (D : Data (X × Fin (2 ^ nd)) n Z s) (en : Cfg (Fin k) ≃ n) (x : X)
    (z : Bool × (Fin p.m → Bool)) (r : ℕ) (hr : r < 2 ^ p.m) :
    HbN p mu nd hnd N D en x z r = hLift D en (x, addrFN nd hnd N z r hr) := dif_pos hr

theorem LbN_of_lt (D : Data (X × Fin (2 ^ nd)) n Z s) (en : Cfg (Fin k) ≃ n) (x : X)
    (z : Bool × (Fin p.m → Bool)) (r : ℕ) (hr : r < 2 ^ p.m) :
    LbN p mu nd hnd N D en x z r = lLift D en (x, addrFN nd hnd N z r hr) := dif_pos hr

/-- The represented slot generator `L + i H` of a branch is the lifted sample `M̂` at its data
grid point. -/
theorem gensN_eq (D : Data (X × Fin (2 ^ nd)) n Z s) (en : Cfg (Fin k) ≃ n) (x : X)
    (z : Bool × (Fin p.m → Bool)) (r : ℕ) (hr : r < 2 ^ p.m) :
    GateODE.Time.gens (HbN p mu nd hnd N D en x z) (LbN p mu nd hnd N D en x z) r =
      mLift D en (x, addrFN nd hnd N z r hr) := by
  rw [GateODE.Time.gens, HbN_of_lt p mu nd hnd N D en x z r hr,
    LbN_of_lt p mu nd hnd N D en x z r hr]
  have h := gen_lift D en (x, addrFN nd hnd N z r hr)
  unfold GateODE.gen at h
  rw [← neg_neg (mLift D en (x, addrFN nd hnd N z r hr)), ← h, neg_neg]

theorem HbN_self (D : Data (X × Fin (2 ^ nd)) n Z s) (en : Cfg (Fin k) ≃ n) (x : X)
    (z : Bool × (Fin p.m → Bool)) (r : ℕ) :
    star (HbN p mu nd hnd N D en x z r) = HbN p mu nd hnd N D en x z r := by
  unfold HbN
  split_ifs
  · unfold hLift
    rw [← qlift_star, SparseValuePrecision.matrixOperator_star_eq _
      (ODEMatrixEnergy.hamiltonianPart_isHermitian _)]
  · rw [ContinuousLinearMap.star_eq_adjoint]
    exact map_zero _

theorem LbN_self (D : Data (X × Fin (2 ^ nd)) n Z s) (en : Cfg (Fin k) ≃ n) (x : X)
    (z : Bool × (Fin p.m → Bool)) (r : ℕ) :
    star (LbN p mu nd hnd N D en x z r) = LbN p mu nd hnd N D en x z r := by
  unfold LbN
  split_ifs
  · unfold lLift
    rw [← qlift_star, SparseValuePrecision.matrixOperator_star_eq _
      (ODEMatrixEnergy.dissipativePart_isHermitian _)]
  · rw [ContinuousLinearMap.star_eq_adjoint]
    exact map_zero _

end Samples

/-! ### The clock promises -/

section Clock

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ} {Zn : Type}

/-- **The clock promise at one label and slot** for computed nodes, from the energy bounds of the
sample at its data grid point only. -/
theorem clockN (p : TParams) (mu nd : ℕ) (hnd : nd ≤ mu + p.m) (N : NodeProg p.m mu Zn)
    (D : Data (X × Fin (2 ^ nd)) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (σ : ℕ) (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (x : X) (ηH ηD ρ γ : ℝ) (hηH : 0 ≤ ηH) (hηD : 0 ≤ ηD) (hρ : ρ = ηH + p.R * ηD)
    (hρpos : 0 < ρ) (hγ : 0 < γ) (hT : 0 < p.T) (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hε1 : p.ε ≤ 1)
    (hTD : 0 ≤ p.T * p.lamD) (hτ : p.tau = p.T * (Real.sqrt (4 * (s : ℝ)) * ρ) / γ)
    (z : Label p.m p.l) (r : ℕ) (hr : r < 2 ^ p.m)
    (hS : SampleOK D x ηH ηD (addrFN nd hnd N z.1 r hr)) :
    ClockPromise (P := Reg (Fin k) ℂ) (a := k + 3) (UJop (R := ℂ) (hadUJ4 k σ hσ))
      (privFamN p mu nd hnd N D en x ρ γ z r)
      (branchHB p (vN p mu N) (HbN p mu nd hnd N D en x) (LbN p mu nd hnd N D en x) z r)
      (width (4 * (s : ℝ)) γ) (moment γ) := by
  have hu := startWN_lt N z.1
  set γ' := γ * (((2 ^ mu - startWN N z.1 : ℕ) : ℝ) / 2 ^ mu) with hγ'
  have hfr0 : 0 ≤ ((2 ^ mu - startWN N z.1 : ℕ) : ℝ) / 2 ^ mu := by positivity
  have hfr1 : ((2 ^ mu - startWN N z.1 : ℕ) : ℝ) / 2 ^ mu ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (2 ^ mu - startWN N z.1 : ℕ) ≤ 2 ^ mu := Nat.sub_le _ _
    exact_mod_cast this
  have h0 : 0 ≤ γ' := mul_nonneg hγ.le hfr0
  have h1 : γ' ≤ γ := mul_le_of_le_one_right hγ.le hfr1
  have hsq : 0 < Real.sqrt (4 * (s : ℝ)) := by
    rw [hs]
    exact Real.sqrt_pos.mpr (by positivity)
  have hsc : durB p (vN p mu N) z.1 / p.tau = γ' / (ρ * Real.sqrt (4 * (s : ℝ))) := by
    rw [durB_vN, hτ, hγ']
    have h2 : (2 : ℝ) ^ mu ≠ 0 := by positivity
    field_simp
  have h := clock_at D en σ hσ hs hrange (x, addrFN nd hnd N z.1 r hr) (p.nodeW z.2) ηH ηD ρ
    p.R γ γ' hηH hηD hρ hρpos (p.nodeW_abs_le hg hε hε1 hTD z.2) h0 h1 hS.rowH hS.colH hS.rowD
    hS.colD
  rw [privFamN, dif_pos hr, branchHB, hsc, HbN_of_lt p mu nd hnd N D en x z.1 r hr,
    LbN_of_lt p mu nd hnd N D en x z.1 r hr]
  exact h

end Clock

end

end SparseHamiltonian.GateBinaryNodes
