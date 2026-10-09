import GateEfficientBinaryODETime.Native

/-!
# The clock promises of the time-dependent private operation

The clock promises of Lemma `ode:lem:gate-select` for the time-dependent selection of
Theorem `ode:thm:time`, at every label and every time slot, for the private operations from
time-indexed binary data.

* `clock_at`: the clock promises of the lifted four-sector Cayley action at one data input `y`,
  an LCHS node `k_w` with `|k_w| ≤ R` and a Cayley parameter `0 ≤ γ' ≤ γ`, with the lifted
  resolvent at one: it inverts `1 - D`, has norm at most `width(4s, γ)`, compresses on the
  boundary prepared by `hadUJ4` to `(1 + i H)/2` for `H = (γ'/(ρ √(4s))) (Ĥ + k_w L̂)`, and its
  endpoint is at most `endpoint γ'`, with square at most `moment γ / 2`. This is the argument of
  `GateBinaryODE.clock4` for an arbitrary Cayley parameter.
* `HsT`, `LsT`: the lifted Hamiltonian and dissipative parts of the sample of every slot (zero
  beyond the last slot); `gensT_eq`: the represented slot generator `L_r + i H_r` is the lifted
  sample `M̂_r`.
* `clockT`: the clock promises of the released time-dependent solver for every label `z` and slot
  `r < 2^m`: the private operation `privFamT` with the branch Hamiltonian
  `branchH z r = (T [start ≤ r] / τ)(H_r + k_w L_r)`, for the common time `τ = T √(4s) ρ / γ`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryODETime

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open CayleyClockInterface
open SparseHamiltonian.GateCircuit.Sim (iota0)
open SparseHamiltonian.GateODE (Label ClockPromise)
open SparseHamiltonian.GateODE.Time (TParams)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### The clock promises at one data input -/

section At

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s k : ℕ}

/-- **The clock promises** of the lifted four-sector Cayley action at the data input `y`, the
LCHS node `k_w` and the Cayley parameter `γ' ∈ [0, γ]`. -/
theorem clock_at (D : Data X n Z s) (en : Cfg (Fin k) ≃ n) (σ : ℕ) (hσ : σ ≤ k)
    (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (y : X) (kn ηH ηD ρ R γ γ' : ℝ) (hηH : 0 ≤ ηH) (hηD : 0 ≤ ηD) (hρ : ρ = ηH + R * ηD)
    (hρpos : 0 < ρ) (hk : |kn| ≤ R) (hγ0 : 0 ≤ γ') (hγ1 : γ' ≤ γ)
    (hrH : ∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ ηH ^ 2)
    (hcH : ∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ ηH ^ 2)
    (hrD : ∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ ηD ^ 2)
    (hcD : ∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ ηD ^ 2) :
    ClockPromise (P := Reg (Fin k) ℂ) (a := k + 3) (UJop (R := ℂ) (hadUJ4 k σ hσ))
      (elift4 en (act4 D y kn ρ γ'))
      (((γ' / (ρ * Real.sqrt (4 * (s : ℝ))) : ℝ) : ℂ) •
        (hLift D en y + ((kn : ℝ) : ℂ) • lLift D en y))
      (width (4 * (s : ℝ)) γ) (moment γ) := by
  have hr : ∀ pp i, ∑ j, ‖partK (D.matrix y) kn pp i j‖ ^ 2 ≤ rhoP kn ηH ηD pp ^ 2 :=
    fun pp i => partK_row_energy _ _ ηH ηD hrH hrD pp i
  have hc : ∀ pp j, ∑ i, ‖partK (D.matrix y) kn pp i j‖ ^ 2 ≤ rhoP kn ηH ηD pp ^ 2 :=
    fun pp j => partK_col_energy _ _ ηH ηD hcH hcD pp j
  have hsum : rhoP kn ηH ηD false ^ 2 + rhoP kn ηH ηD true ^ 2 ≤ ρ ^ 2 := by
    rw [hρ]
    exact rhoP_sq_sum_le _ ηH ηD R hηH hηD hk
  have hent : ∀ pp i j, ‖partK (D.matrix y) kn pp i j‖ ≤ ρ := by
    intro pp i j
    have h1 := norm_le_of_energy_le (rhoP kn ηH ηD pp) (partK (D.matrix y) kn pp i)
      (rhoP_nonneg _ ηH ηD hηH hηD pp) (hr pp i) j
    rw [hρ]
    exact h1.trans (rhoP_le _ ηH ηD R hηH hηD hk pp)
  refine ⟨⟨elift4 en (res4 D y kn ρ γ'), endpoint γ', ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have h := one_sub_act4_res4 D y kn ρ γ'
    rw [mul_def] at h
    rw [← elift4_one (R := ℂ) en, ← elift4_sub, ← elift4_comp, h, elift4_one]
  · have h := res4_one_sub_act4 D y kn ρ γ'
    rw [mul_def] at h
    rw [← elift4_one (R := ℂ) en, ← elift4_sub, ← elift4_comp, h, elift4_one]
  · exact (norm_elift4_le en _).trans ((norm_res4_le D y _ ρ _ hρpos hγ0 hent).trans
      (width_mono _ hγ1))
  · have hsc : ((γ' : ℝ) : ℂ) * ((ρ : ℂ) * (Real.sqrt (4 * (s : ℝ)) : ℂ))⁻¹ =
        ((γ' / (ρ * Real.sqrt (4 * (s : ℝ))) : ℝ) : ℂ) := by
      push_cast
      ring
    have hq : qlift (R := ℂ) en (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.lchsHamiltonian (D.matrix y) kn)) =
        hLift D en y + ((kn : ℝ) : ℂ) • lLift D en y := by
      rw [ODEMatrixEnergy.lchsHamiltonian, ODEMatrixEnergy.matrixOperator_add,
        ODEMatrixEnergy.matrixOperator_smul, qlift_add, qlift_smul]
      rfl
    rw [boundary_lift4 D σ hσ en hs hrange, res4_compression, qlift_smul, qlift_add, qlift_one,
      qlift_smul, qlift_smul, hsc, hq]
  · have hq := norm_res4_bdry4 D y kn ρ γ' (rhoP kn ηH ηD) hρpos hγ0 hr hc hsum
    have hgram : (elift4 (R := ℂ) en (res4 D y kn ρ γ') ∘L
        (UJop (R := ℂ) (hadUJ4 k σ hσ) ∘L iota0 (a := k + 3) (P := Reg (Fin k) ℂ)))† ∘L
        (elift4 (R := ℂ) en (res4 D y kn ρ γ') ∘L
          (UJop (R := ℂ) (hadUJ4 k σ hσ) ∘L iota0 (a := k + 3) (P := Reg (Fin k) ℂ))) =
        qlift en ((res4 D y kn ρ γ' ∘L bdry4 D)† ∘L (res4 D y kn ρ γ' ∘L bdry4 D)) := by
      rw [adjoint_comp_comp, adjoint_comp_comp, ← elift4_adjoint, ← elift4_comp,
        boundary_lift4 D σ hσ en hs hrange]
    have h1 := norm_adjoint_comp_self
      (elift4 (R := ℂ) en (res4 D y kn ρ γ') ∘L
        (UJop (R := ℂ) (hadUJ4 k σ hσ) ∘L iota0 (a := k + 3) (P := Reg (Fin k) ℂ)))
    rw [hgram] at h1
    have h2 := norm_qlift_le (R := ℂ) en
      ((res4 D y kn ρ γ' ∘L bdry4 D)† ∘L (res4 D y kn ρ γ' ∘L bdry4 D))
    rw [norm_adjoint_comp_self, h1] at h2
    have he : 0 ≤ endpoint γ' := Real.sqrt_nonneg _
    exact (mul_self_le_mul_self_iff (norm_nonneg _) he).2
      (h2.trans (mul_le_mul hq hq (norm_nonneg _) he))
  · rw [endpoint_sq]
    exact div_le_div_of_nonneg_right (moment_mono hγ0 hγ1) (by norm_num)

end At

/-! ### The time-dependent families -/

section Time

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s k m : ℕ}

/-- The lifted Hamiltonian part of the sample of slot `r` (zero beyond the last slot). -/
def HsT (D : Data (X × Fin (2 ^ m)) n Z s) (en : Cfg (Fin k) ≃ n) (x : X) (r : ℕ) :
    Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ :=
  if h : r < 2 ^ m then hLift D en (x, ⟨r, h⟩) else 0

/-- The lifted dissipative part of the sample of slot `r` (zero beyond the last slot). -/
def LsT (D : Data (X × Fin (2 ^ m)) n Z s) (en : Cfg (Fin k) ≃ n) (x : X) (r : ℕ) :
    Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ :=
  if h : r < 2 ^ m then lLift D en (x, ⟨r, h⟩) else 0

theorem HsT_of_lt (D : Data (X × Fin (2 ^ m)) n Z s) (en : Cfg (Fin k) ≃ n) (x : X) (r : ℕ)
    (hr : r < 2 ^ m) : HsT D en x r = hLift D en (x, ⟨r, hr⟩) := dif_pos hr

theorem LsT_of_lt (D : Data (X × Fin (2 ^ m)) n Z s) (en : Cfg (Fin k) ≃ n) (x : X) (r : ℕ)
    (hr : r < 2 ^ m) : LsT D en x r = lLift D en (x, ⟨r, hr⟩) := dif_pos hr

/-- The represented slot generator `L_r + i H_r` is the lifted sample `M̂_r`. -/
theorem gensT_eq (D : Data (X × Fin (2 ^ m)) n Z s) (en : Cfg (Fin k) ≃ n) (x : X) (r : ℕ)
    (hr : r < 2 ^ m) :
    GateODE.Time.gens (HsT D en x) (LsT D en x) r = mLift D en (x, ⟨r, hr⟩) := by
  rw [GateODE.Time.gens, HsT_of_lt D en x r hr, LsT_of_lt D en x r hr]
  have h := gen_lift D en (x, ⟨r, hr⟩)
  unfold GateODE.gen at h
  rw [← neg_neg (mLift D en (x, ⟨r, hr⟩)), ← h, neg_neg]

end Time

section Clock

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}

theorem mask_mem (q r : ℕ) :
    0 ≤ TimeDependentODE.mask q r ∧ TimeDependentODE.mask q r ≤ 1 := by
  unfold TimeDependentODE.mask
  split_ifs <;> norm_num

/-- **The clock promises at every label and slot** of the released time-dependent solver, for
the private operation `privFamT` and the branch Hamiltonian of the lifted samples. -/
theorem clockT (p : TParams) (D : Data (X × Fin (2 ^ p.m)) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (σ : ℕ) (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (x : X) (ηH ηD ρ γ : ℝ) (hηH : 0 ≤ ηH) (hηD : 0 ≤ ηD) (hρ : ρ = ηH + p.R * ηD)
    (hρpos : 0 < ρ) (hγ : 0 < γ) (hT : 0 < p.T) (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hε1 : p.ε ≤ 1)
    (hTD : 0 ≤ p.T * p.lamD) (hτ : p.tau = p.T * (Real.sqrt (4 * (s : ℝ)) * ρ) / γ)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ ηH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ ηH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ ηD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ ηD ^ 2)
    (z : Label p.m p.l) (r : ℕ) (hr : r < 2 ^ p.m) :
    ClockPromise (P := Reg (Fin k) ℂ) (a := k + 3) (UJop (R := ℂ) (hadUJ4 k σ hσ))
      (privFamT p D en x ρ γ z r) (p.branchH (HsT D en x) (LsT D en x) z r)
      (width (4 * (s : ℝ)) γ) (moment γ) := by
  obtain ⟨hm0, hm1⟩ := mask_mem (p.start z.1) r
  have hsq : 0 < Real.sqrt (4 * (s : ℝ)) := by
    rw [hs]
    exact Real.sqrt_pos.mpr (by positivity)
  have hsc : p.T * TimeDependentODE.mask (p.start z.1) r / p.tau =
      γ * TimeDependentODE.mask (p.start z.1) r / (ρ * Real.sqrt (4 * (s : ℝ))) := by
    rw [hτ]
    field_simp
  have h := clock_at D en σ hσ hs hrange (x, ⟨r, hr⟩) (p.nodeW z.2) ηH ηD ρ p.R γ
    (γ * TimeDependentODE.mask (p.start z.1) r) hηH hηD hρ hρpos
    (p.nodeW_abs_le hg hε hε1 hTD z.2) (mul_nonneg hγ.le hm0)
    (mul_le_of_le_one_right hγ.le hm1) (hrH _) (hcH _) (hrD _) (hcD _)
  rw [privFamT, dif_pos hr, GateODE.Time.TParams.branchH, hsc, HsT_of_lt D en x r hr,
    LsT_of_lt D en x r hr]
  exact h

end Clock

end

end SparseHamiltonian.GateBinaryODETime
