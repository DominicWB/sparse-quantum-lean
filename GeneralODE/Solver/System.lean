import GeneralODE.Solver.Source
import GeneralODE.Analysis.Decode
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The history linear system on one instance

`histData` fixes the history encoding of the paper: Taylor coefficients
`c_k = τ^k/k!` and source coefficients `d_k = τ^k/(k+1)!` with `τ = α h ≤ 1`,
normalisation `N = 7`, and a slot unitary sending the forcing slot to the
uniform superposition of the slots `1, …, m`.

`system` collects, for one instance `x' = A x + b` and any unitary `q` whose
two selected blocks approximate `A/α` and `I`, everything the solver and the
decoder need: a positive multiple `y` of the history solution solves
`M y = r⁻¹ β₀` for the block `M` of the history unitary, the right-hand side
`β₀ = (μ b, x₀, 0, …)` and any `r > 0`; every vector
satisfies `‖v‖ ≤ N κ_H ‖M v‖` (`N = 7` for `histData`); and the final-time
decoder sees a fixed
fraction `(1-ζ)/(8g)` of `y`, whose direction is within `2ζ` of that of
`x(T)`, where `ζ = 210 C̄ g ϑ`.
-/

namespace SparseHamiltonian.GeneralODE.Solver

noncomputable section
open ContinuousLinearMap OracleCircuit Registers History Implemented ODEStateNormalization
open scoped InnerProduct BigOperators ComplexConjugate Nat
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

variable {n PB : Type} [Fintype n] [DecidableEq n] [Fintype PB] [DecidableEq PB]

theorem uniformSlots_norm (m : ℕ) (hm : 1 ≤ m) : ‖uniformSlots m‖ = 1 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hsq : ‖uniformSlots m‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_option]
    have hterm : ∀ j : Fin (2 * m + 1), ‖uniformSlots m (some j)‖ ^ 2 =
        (if 1 ≤ j.val ∧ j.val ≤ m then (1 / m : ℝ) else 0) := by
      intro j
      change ‖(if 1 ≤ j.val ∧ j.val ≤ m then ((Real.sqrt m)⁻¹ : ℂ) else 0)‖ ^ 2 = _
      split_ifs
      · rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
          inv_pow, Real.sq_sqrt hm0.le, one_div]
      · simp
    simp only [hterm]
    rw [Fin.sum_univ_eq_sum_range (fun j => if 1 ≤ j ∧ j ≤ m then (1 / m : ℝ) else 0)
      (2 * m + 1)]
    have hsplit : ∑ j ∈ Finset.range (2 * m + 1), (if 1 ≤ j ∧ j ≤ m then (1 / m : ℝ) else 0) =
        ∑ j ∈ Finset.Icc 1 m, (1 / m : ℝ) := by
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    rw [hsplit, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    change ‖(0 : ℂ)‖ ^ 2 + _ = 1
    rw [norm_zero]
    simp only [Nat.add_sub_cancel]
    field_simp
    ring
  have h0 : 0 ≤ ‖uniformSlots m‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖uniformSlots m‖ - 1)]

/-- The slot unitary of the source term. -/
def slotSource (m : ℕ) (hm : 1 ≤ m) : EuclideanSpace ℂ (Slot m) →L[ℂ] EuclideanSpace ℂ (Slot m) :=
  Classical.choose (exists_unitary_single (none : Slot m) (uniformSlots m) (uniformSlots_norm m hm))

theorem slotSource_spec (m : ℕ) (hm : 1 ≤ m) :
    IsUnitary (slotSource m hm) ∧
      slotSource m hm (EuclideanSpace.single (none : Slot m) 1) = uniformSlots m :=
  Classical.choose_spec (exists_unitary_single (none : Slot m) (uniformSlots m)
    (uniformSlots_norm m hm))

theorem restIn_seven (m K : ℕ) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (s : Slot m) :
    restIn m K 7 (taylorCoef τ) (phiCoef τ) s ≤ 1 := by
  have hc := sum_taylorCoef_le τ hτ0 hτ1 K
  have hd := sum_phiCoef_le τ hτ0 hτ1 K
  have he := Real.exp_one_lt_d9
  rcases s with _ | ⟨j, hj⟩
  · simp only [restIn]
    linarith
  · simp only [restIn]
    split_ifs <;> linarith

theorem restOut_seven (m K : ℕ) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (s : Slot m) :
    restOut m K 7 (taylorCoef τ) (phiCoef τ) s ≤ 1 := by
  have hc := sum_taylorCoef_le τ hτ0 hτ1 K
  have hd := sum_phiCoef_le τ hτ0 hτ1 K
  have he := Real.exp_one_lt_d9
  rcases s with _ | ⟨j, hj⟩
  · simp only [restOut]
    norm_num
  · simp only [restOut]
    split_ifs <;> linarith

/-- The history encoding of the paper. -/
def histData (m K : ℕ) (hm : 1 ≤ m) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (i0 : n) (pb0 : PB)
    (Ein Eout : Bool → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ PB))
    (hin : ∀ b, (Ein b)† ∘L Ein b = 1) (hout : ∀ b, (Eout b)† ∘L Eout b = 1) : HistData n PB where
  m := m
  K := K
  N := 7
  c := taylorCoef τ
  d := phiCoef τ
  i0 := i0
  pb0 := pb0
  Ein := Ein
  Eout := Eout
  hin := hin
  hout := hout
  Rc := slotSource m hm
  N_pos := by norm_num
  c_nonneg := taylorCoef_nonneg τ hτ0
  d_nonneg := phiCoef_nonneg τ hτ0
  restIn_le := restIn_seven m K τ hτ0 hτ1
  restOut_le := restOut_seven m K τ hτ0 hτ1
  Rc_unitary := (slotSource_spec m hm).1
  Rc_none := by
    intro s'
    unfold entry
    rw [(slotSource_spec m hm).2]

/-- The block of the history unitary as a vector identity. -/
theorem block_eq (H : HistData n PB) (q : EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB)
    (y : EuclideanSpace ℂ H.Sys) :
    block (s := H.Sys) H.clean (H.unitary q) y =
      ((1 / H.N : ℝ) : ℂ) • RegisterEquivalences.productFlatten (Slot H.m) n
        (residual H.m (H.Pk q 0) (stepPoly H.c (H.Pk q)) (stepPoly H.d (H.Pk q))
          ((RegisterEquivalences.productFlatten (Slot H.m) n).symm y)) := by
  ext ⟨s', i⟩
  rw [PiLp.smul_apply, smul_eq_mul, RegisterEquivalences.productFlatten_apply]
  exact H.block_unitary q y s' i

set_option maxHeartbeats 4000000 in
/-- **The history system on one instance.** -/
theorem system (H : HistData n PB) (q : EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB)
    (hq : IsUnitary q) (A : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (x0 b : EuclideanSpace ℂ n) (Λ T Cbar g α δU ε0 ϑ : ℝ)
    (hc : H.c = taylorCoef (α * (T / H.m))) (hd : H.d = phiCoef (α * (T / H.m)))
    (hm : 1 ≤ H.m) (hT : 0 < T) (hα : 0 < α) (hαT : α * T ≤ H.m) (hΛT : 8 * Λ * T ≤ H.m)
    (hA : ‖A‖ ≤ Λ)
    (hUerr : ‖selBlock H.Ein H.Eout q true - ((α⁻¹ : ℝ) : ℂ) • A‖ ≤ δU)
    (h0err : ‖selBlock H.Ein H.Eout q false - 1‖ ≤ ε0)
    (hC1 : 1 ≤ Cbar) (hC : ∀ t, 0 ≤ t → t ≤ T → ‖NormedSpace.exp (t • A)‖ ≤ Cbar)
    (hg1 : 1 ≤ g)
    (hg : ∀ t, 0 ≤ t → t ≤ T →
      ‖ODEConstantForcing.solution A x0 b t‖ ≤ g * ‖ODEConstantForcing.solution A x0 b T‖)
    (hϑ0 : 0 ≤ ϑ) (hϑ : 210 * Cbar * g * ϑ < 1)
    (hR1 : H.m * (H.K * ε0) ≤ ϑ) (hR2 : H.m * δU ≤ ϑ)
    (hR3 : H.m * ((Λ * (T / H.m)) ^ (H.K + 1) / ((H.K + 1) ! : ℝ)) ≤ ϑ)
    (hx : ODEConstantForcing.solution A x0 b T ≠ 0)
    (r : ℝ) (hr0 : 0 < r) :
    ∃ y : EuclideanSpace ℂ H.Sys,
      block (s := H.Sys) H.clean (H.unitary q) y =
        (r⁻¹ : ℝ) • rhsVector H.m (T / Real.sqrt H.m) x0 b ∧
      (∀ v, ‖v‖ ≤ H.N * kappaH H.m 2 (Real.exp 1) (2 * Cbar) *
        ‖block (s := H.Sys) H.clean (H.unitary q) v‖) ∧
      y ≠ 0 ∧
      (1 - 210 * Cbar * g * ϑ) / (8 * g) * ‖y‖ ≤ ‖((Decode.decoder (n := n) H.m)†) y‖ ∧
      ‖unitDirection (((Decode.decoder (n := n) H.m)†) y) -
          unitDirection (ODEConstantForcing.solution A x0 b T)‖ ≤
        2 * (210 * Cbar * g * ϑ) := by
  haveI : Nontrivial (EuclideanSpace ℂ n) := ⟨⟨_, 0, hx⟩⟩
  have hnorm : ∀ bb, ‖selBlock H.Ein H.Eout q bb‖ ≤ 1 := by
    intro bb
    unfold selBlock
    have h1 := Decode.norm_adjoint_le_one (H.Eout bb) (H.hout bb)
    have h2 := norm_unitary_le q hq
    have h3 := norm_le_one_of_isometry (H.Ein bb) (H.hin bb)
    calc ‖(H.Eout bb)† ∘L q ∘L H.Ein bb‖ ≤ ‖(H.Eout bb)†‖ * (‖q‖ * ‖H.Ein bb‖) :=
          (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (1 * 1) := by gcongr
      _ = 1 := by norm_num
  obtain ⟨Q0, hQP, hPQ, hQ2, hΦn, hpow, hacc, hsol⟩ := history_accuracy A
    (selBlock H.Ein H.Eout q true) (selBlock H.Ein H.Eout q false) x0 b Λ T Cbar g α δU ε0 ϑ
    H.m H.K hm hT hα hαT hΛT hA (hnorm true) (hnorm false) hUerr h0err hC1 hC hg1 hg hϑ0 hϑ.le
    hR1 hR2 hR3
  set m := H.m with hmdef
  set τ := α * (T / m) with hτ
  set P := powers (selBlock H.Ein H.Eout q true) (selBlock H.Ein H.Eout q false) H.K with hP
  have hPk : H.Pk q = P := rfl
  set V := poly (taylorCoef τ) P with hV
  set Φ := poly (phiCoef τ) P with hΦ
  have hVs : stepPoly H.c (H.Pk q) = V := by rw [hc, hPk]; rfl
  have hΦs : stepPoly H.d (H.Pk q) = Φ := by rw [hd, hPk]; rfl
  set μ := T / Real.sqrt m with hμ
  set e := RegisterEquivalences.productFlatten (Slot m) n with he
  set sol := History.solution m V Φ Q0 μ x0 b with hsoldef
  set M := block (s := H.Sys) H.clean (H.unitary q) with hM
  have hMv : ∀ v, M v = ((1 / H.N : ℝ) : ℂ) • e (residual m (P 0) V Φ (e.symm v)) := by
    intro v
    rw [hM, block_eq, hVs, hΦs, hPk]
  have hN : (0 : ℝ) < H.N := H.N_pos
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by linarith)
  -- the system
  have hMsol : M (e sol) = ((1 / H.N : ℝ) : ℂ) • rhsVector m μ x0 b := by
    rw [hMv, LinearIsometryEquiv.symm_apply_apply, hsoldef, residual_solution m (P 0) V Φ Q0 hPQ]
    rfl
  set y : EuclideanSpace ℂ H.Sys := ((H.N / r : ℝ) : ℂ) • e sol with hy
  have hMy : M y = (r⁻¹ : ℝ) • rhsVector m μ x0 b := by
    rw [hy, map_smul, hMsol, smul_smul, ← Complex.ofReal_mul, ← Complex.coe_smul]
    congr 1
    field_simp
  -- the condition number
  have hkappa : ∀ v, ‖v‖ ≤ H.N * kappaH m 2 (Real.exp 1) (2 * Cbar) * ‖M v‖ := by
    intro v
    have hk := norm_le_kappaH (P 0) V Φ Q0 hm hQP 2 (Real.exp 1) (2 * Cbar) hQ2 hΦn
      (by linarith) hpow (e.symm v)
    rw [LinearIsometryEquiv.norm_map] at hk
    have hMn : ‖M v‖ = (1 / H.N) * ‖residual m (P 0) V Φ (e.symm v)‖ := by
      rw [hMv, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
        LinearIsometryEquiv.norm_map]
    rw [hMn]
    have : H.N * kappaH m 2 (Real.exp 1) (2 * Cbar) *
        ((1 / H.N) * ‖residual m (P 0) V Φ (e.symm v)‖) =
        kappaH m 2 (Real.exp 1) (2 * Cbar) * ‖residual m (P 0) V Φ (e.symm v)‖ := by
      field_simp
    rw [this]
    exact hk
  -- decoding
  set ζ := 210 * Cbar * g * ϑ with hζ
  set xT := ODEConstantForcing.solution A x0 b T with hxT
  set yhat := solSeq m V Φ Q0 μ x0 b m with hyhat
  have hxT0 : 0 < ‖xT‖ := norm_pos_iff.mpr hx
  have hrel : ‖yhat - xT‖ ≤ ζ * ‖xT‖ := hacc
  obtain ⟨hyhat0, hdir⟩ := relative_error xT yhat ζ hx hϑ hrel
  have hylow : (1 - ζ) * ‖xT‖ ≤ ‖yhat‖ := approximate_norm_lower xT yhat ζ hrel
  have hDy : ((Decode.decoder (n := n) m)†) y = ((H.N / r * Real.sqrt m : ℝ) : ℂ) • yhat := by
    rw [hy, map_smul, Decode.decoder_adjoint_solution m hm V Φ Q0 μ x0 b, smul_smul,
      ← Complex.ofReal_mul]
  have hc0 : 0 < H.N / r * Real.sqrt m := by positivity
  have hDyn : ‖((Decode.decoder (n := n) m)†) y‖ = H.N / r * Real.sqrt m * ‖yhat‖ := by
    rw [hDy, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
  have hyn : ‖y‖ = H.N / r * ‖sol‖ := by
    rw [hy, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
      LinearIsometryEquiv.norm_map]
  have hg0 : 0 < g := by linarith
  refine ⟨y, hMy, hkappa, ?_, ?_, ?_⟩
  · intro h0
    have : ‖((Decode.decoder (n := n) m)†) y‖ = 0 := by rw [h0, map_zero, norm_zero]
    rw [hDyn] at this
    have hyp : 0 < ‖yhat‖ := norm_pos_iff.mpr hyhat0
    have : 0 < H.N / r * Real.sqrt m * ‖yhat‖ := mul_pos hc0 hyp
    linarith
  · rw [hDyn, hyn]
    have hsol' : ‖sol‖ ≤ 8 * Real.sqrt m * (g * ‖xT‖) := hsol
    have hζ1 : 0 ≤ 1 - ζ := by linarith
    have hNr : 0 < H.N / r := by positivity
    calc (1 - ζ) / (8 * g) * (H.N / r * ‖sol‖)
        ≤ (1 - ζ) / (8 * g) * (H.N / r * (8 * Real.sqrt m * (g * ‖xT‖))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hsol' hNr.le
      _ = H.N / r * Real.sqrt m * ((1 - ζ) * ‖xT‖) := by
          field_simp
      _ ≤ H.N / r * Real.sqrt m * ‖yhat‖ := mul_le_mul_of_nonneg_left hylow hc0.le
  · rw [hDy, Complex.coe_smul, Decode.unitDirection_real_smul _ hc0]
    exact hdir

end

end SparseHamiltonian.GeneralODE.Solver
