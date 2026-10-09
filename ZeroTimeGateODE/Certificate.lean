import ZeroTimeGateODE.Grover
import GateEfficientNative.ODE.Protocol

/-!
# The certificate of a direct source assembly

A direct source assembly (the zero-case preparation of the remark of Theorem `ode:thm:gates`)
prepares, on clean work wires, the decoded vector `x / B` of the target `x` with the public
source mass `B` (no coefficient register, so no factor `1/3`).  If
the native preparation `UN` has decoded vector `dN` with `‖B dN - x‖ ≤ 2νB`,
`ν = ε / (10000 g)`, and `B ≤ g ‖x‖`, then

* the direction of `dN` is within `ε / 500` of `x / ‖x‖` and its amplitude `‖dN‖` is at least
  `1 / (4g)` (`output_certificate_direct`);
* the released native trials `GateNative.trialN` (exact zero tests, the literal inverse of the
  preparation) have mean success at least `1/4` over the released cutoff and every nonzero
  decoded trial is within `ε / 500` of `x / ‖x‖` up to a global phase
  (`trial_bounds_of_vec_direct`, through `randomized_certificate_full`, which covers every
  amplitude up to one);
* the released native protocol `GateNative.nprotocol prepN g` has the guarantees
  `GateNative.NOutcome` (`noutcome_direct`).

`vector_error_direct` and `noutcome_of_released` give the hypothesis `‖B dN - x‖ ≤ 2νB` from a
native preparation within `δ ≤ 2ν` of a lifted released preparation whose decoded vector is
exactly `x / B`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.ZeroTimeGateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open GateODE (OWire AW goodF)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-! ### The output certificate -/

section Output

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The output certificate of a direct source assembly**: a vector `y` with
`‖y - x‖ ≤ 2νB`, `ν = ε / (10000 g)`, `0 < B ≤ g ‖x‖`, is nonzero, its direction is within
`ε / 500` of that of `x`, and `‖y‖ / B ≥ 1 / (4g)`. -/
theorem output_certificate_direct (x y : E) (B g ε : ℝ) (hx : x ≠ 0) (hg : 1 ≤ g) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2) (hB : 0 < B) (hBudget : B ≤ g * ‖x‖)
    (hError : ‖y - x‖ ≤ 2 * ImprovedODEQueryBudget.precision g ε * B) :
    y ≠ 0 ∧ ‖unitDirection y - unitDirection x‖ ≤ ε / 500 ∧ 1 / (4 * g) ≤ ‖y‖ / B := by
  have hg0 : 0 < g := by linarith
  have hν : ImprovedODEQueryBudget.precision g ε = ε / (10000 * g) := rfl
  have hRel : ‖y - x‖ ≤ (ε / 5000) * ‖x‖ := by
    refine hError.trans ?_
    calc 2 * ImprovedODEQueryBudget.precision g ε * B
        ≤ 2 * ImprovedODEQueryBudget.precision g ε * (g * ‖x‖) :=
          mul_le_mul_of_nonneg_left hBudget (by rw [hν]; positivity)
      _ = (ε / 5000) * ‖x‖ := by
          rw [hν]
          field_simp
          ring
  have hSmall : ε / 5000 < 1 := by linarith
  have hDirection := ODEStateNormalization.relative_error x y (ε / 5000) hx hSmall hRel
  have hLower := ODEStateNormalization.extraction_amplitude_lower_of_budget_le x y B g 1
    (ε / 5000) hB hg0 one_pos hSmall.le hBudget hRel
  refine ⟨hDirection.1, by linarith [hDirection.2], ?_⟩
  rw [one_mul, one_mul] at hLower
  calc 1 / (4 * g) = (1 / 4) / g := by field_simp
    _ ≤ (1 - ε / 5000) / g := by
        apply div_le_div_of_nonneg_right _ hg0.le
        linarith
    _ ≤ ‖y‖ / B := hLower

/-- **Randomized amplification of a direct source assembly**: for an isometric decoding `G`,
a unitary preparation `U` and a unit seed `s` whose decoded vector `d = G† (U s)` satisfies
`‖B d - x‖ ≤ 2νB` with `0 < B ≤ g ‖x‖`, the actual Grover trials have mean success at least
`1/4` over the released cutoff, and every nonzero decoded trial is within `ε / 500` of
`x / ‖x‖` up to a global phase. -/
theorem trial_bounds_of_vec_direct {K P : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    (G : P →L[ℂ] K) (hG : G† ∘L G = 1) (U : K →L[ℂ] K) (hU : IsUnitary U) (s : K)
    (hs : ‖s‖ = 1) (x : P) (B g ε : ℝ) (hx : x ≠ 0) (hg : 1 ≤ g) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2) (hB : 0 < B) (hBudget : B ≤ g * ‖x‖)
    (hvec : ‖B • (G†) (U s) - x‖ ≤ 2 * ImprovedODEQueryBudget.precision g ε * B) :
    0 < ODEGroverAverage.chosenIterations g ∧
    (ODEGroverAverage.chosenIterations g : ℝ) ≤ 5 * g ∧
    (1 : ℝ) / 4 ≤ (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations g),
      ‖ODEHeraldedSuccess.successProjector G (ODEGroverActual.trial G U s j)‖ ^ 2) /
        (ODEGroverAverage.chosenIterations g : ℝ) ∧
    ∀ j : ℕ, (G†) (ODEGroverActual.trial G U s j) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection ((G†) (ODEGroverActual.trial G U s j)) - unitDirection x‖ ≤
          ε / 500 := by
  obtain ⟨-, hdir, hlow⟩ := output_certificate_direct x _ B g ε hx hg hε hεHalf hB hBudget hvec
  have hscale : ‖B • (G†) (U s)‖ / B = ‖(G†) (U s)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hB]
    exact mul_div_cancel_left₀ _ hB.ne'
  rw [hscale] at hlow
  rw [ODEHeraldedSuccess.unitDirection_pos_smul B hB] at hdir
  have hamp : ODEGroverActual.amplitude G U s = ‖(G†) (U s)‖ := by
    rw [ODEGroverActual.amplitude, ← ODEHeraldedSuccess.successfulComponent,
      ODEHeraldedSuccess.successfulComponent_norm _ hG]
    rfl
  exact randomized_certificate_full G hG U hU s hs g hg (by rw [hamp]; exact hlow) x (ε / 500)
    hdir

end Output

/-! ### Native registers -/

section Native

variable {a m r K k l f : ℕ} {S Zs Z Y J : Type*} {nP bT bP A : ℕ}
variable [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y]

/-- **Mean success and per-trial direction error of the native trials of a direct source
assembly**: for every native ODE register with a large enough pool and every unitary native
preparation that never touches the native flag and pool of the zero tests and whose clean
decoded vector `dN` satisfies `‖B dN - x‖ ≤ 2νB`, `0 < B ≤ g ‖x‖`, the released native trials
`trialN prepN j` have mean success at least `1/4` over the released cutoff, and every nonzero
decoded trial is within `ε / 500` of `x / ‖x‖` up to a global phase. -/
theorem native_trial_bounds_direct (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
      Fintype.card S ≤ nP + 1)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hU : IsUnitary (nrun prim prepN)) (hP : Pres2 (ZeroOn reflWire) (nrun prim prepN))
    (x : Reg S ℂ) (B g ε : ℝ) (hx : x ≠ 0) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hB : 0 < B) (hBudget : B ≤ g * ‖x‖)
    (hvec : ‖B • (goodN†) (nrun prim prepN sN) - x‖ ≤
      2 * ImprovedODEQueryBudget.precision g ε * B) :
    0 < ODEGroverAverage.chosenIterations g ∧
    (ODEGroverAverage.chosenIterations g : ℝ) ≤ 5 * g ∧
    (1 : ℝ) / 4 ≤ (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations g),
      ‖ODEHeraldedSuccess.successProjector goodN (nrun prim (trialN prepN j) sN)‖ ^ 2) /
        (ODEGroverAverage.chosenIterations g : ℝ) ∧
    ∀ j : ℕ, (goodN†) (nrun prim (trialN prepN j) sN) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection ((goodN†) (nrun prim (trialN prepN j) sN)) - unitDirection x‖ ≤
          ε / 500 := by
  have htrial : ∀ j, nrun prim (trialN prepN j) sN =
      ODEGroverActual.trial goodN (nrun prim prepN) sN j :=
    fun j => trialN_seed prim hnP prepN hU hP j
  have hGi := goodN_isometry (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)
  have hs := norm_sN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
    (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)
  simp only [htrial]
  generalize goodN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
    (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A) = G at hGi hvec ⊢
  generalize nrun prim prepN = U at hU hvec ⊢
  generalize (sN : Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ) = s at hs hvec ⊢
  exact trial_bounds_of_vec_direct G hGi U hU s hs x B g ε hx hg hε hεHalf hB hBudget hvec

/-- **The released native protocol is correct for a direct source assembly.**  For every native
ODE register with a large enough pool and every valid native preparation that never touches the
native flag and pool of the zero tests and whose clean decoded vector `dN` satisfies
`‖B dN - x‖ ≤ 2νB`, `0 < B ≤ g ‖x‖`, the protocol `nprotocol prepN g` has the guarantees
`NOutcome`: unitary trials, mean success at least `1/4`, every successful trial within
`ε / 500` of `x / ‖x‖` up to a global phase, success probability at least `175/256 > 2/3` and a
conditional output density within trace distance `ε` of `x / ‖x‖`. -/
theorem noutcome_direct
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
      Fintype.card S ≤ nP + 1)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j))
    (hvalid : ∀ i ∈ prepN, i.Valid) (hP : Pres2 (ZeroOn reflWire) (nrun prim prepN))
    (x : Reg S ℂ) (B g ε : ℝ) (hx : x ≠ 0) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hB : 0 < B) (hBudget : B ≤ g * ‖x‖)
    (hvec : ‖B • (goodN†) (nrun prim prepN sN) - x‖ ≤
      2 * ImprovedODEQueryBudget.precision g ε * B) :
    NOutcome prepN g ε hg prim x := by
  obtain ⟨-, -, hmean, hdir⟩ := native_trial_bounds_direct prim hnP prepN
    (nrun_isUnitary prim hprim _ hvalid) hP x B g ε hx hg hε hεHalf hB hBudget hvec
  exact noutcome_of_bounds prepN prim hprim hvalid x hx g ε hg hε hmean hdir

/-- **The released native protocol is correct for a direct source assembly of an intermediate
target**: if the clean decoded vector `dN` of the preparation satisfies `‖B dN - y‖ ≤ 2νB` for
the precision `ν = ε' / (10000 g)` of an internal accuracy `ε'`, `0 < B ≤ g ‖y‖`, and the
direction of `y` is within `η` of that of `x` with `ε'/500 + η ≤ ε/500`, then
`nprotocol prepN g` has the guarantees `NOutcome` against `x` (as the released time-dependent
solver, with `y` its discretised target). -/
theorem noutcome_direct_retarget
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
      Fintype.card S ≤ nP + 1)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j))
    (hvalid : ∀ i ∈ prepN, i.Valid) (hP : Pres2 (ZeroOn reflWire) (nrun prim prepN))
    (y x : Reg S ℂ) (B g ε ε' η : ℝ) (hy : y ≠ 0) (hx : x ≠ 0) (hg : 1 ≤ g) (hε : 0 < ε)
    (hε' : 0 < ε') (hε'Half : ε' ≤ 1 / 2) (hB : 0 < B) (hBudget : B ≤ g * ‖y‖)
    (hvec : ‖B • (goodN†) (nrun prim prepN sN) - y‖ ≤
      2 * ImprovedODEQueryBudget.precision g ε' * B)
    (hdirY : ‖unitDirection y - unitDirection x‖ ≤ η) (hsum : ε' / 500 + η ≤ ε / 500) :
    NOutcome prepN g ε hg prim x := by
  obtain ⟨-, -, hmean, hdir⟩ := native_trial_bounds_direct prim hnP prepN
    (nrun_isUnitary prim hprim _ hvalid) hP y B g ε' hy hg hε' hε'Half hB hBudget hvec
  refine noutcome_of_bounds prepN prim hprim hvalid x hx g ε hg hε hmean ?_
  intro j hj
  obtain ⟨ω, hω, hd⟩ := hdir j hj
  refine ⟨ω, hω, ?_⟩
  refine (norm_sub_le_norm_sub_add_norm_sub _ (unitDirection y) _).trans ?_
  linarith only [hd, hdirY, hsum]

/-- **The vector error of a native preparation** within `δ` of a lifted released preparation
`Urel` whose clean decoded vector is exactly `x / B`: `‖B dN - x‖ ≤ B δ`. -/
theorem vector_error_direct
    (UN : Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ →L[ℂ]
      Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ)
    (Urel : Reg (AW a m r K k l f) (Reg S ℂ) →L[ℂ] Reg (AW a m r K k l f) (Reg S ℂ))
    {δ : ℝ} (hA : ApproxOn CleanX UN (liftB (conj Urel)) δ) (x : Reg S ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hrel : B • (goodF†) (Urel (GateODE.seedState seedV)) = x) :
    ‖B • (goodN†) (UN sN) - x‖ ≤ B * δ := by
  have hc := native_decoded_close UN Urel hA
  rw [← hrel, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hB]
  exact mul_le_mul_of_nonneg_left hc hB

/-- **The released native protocol is correct** for a native preparation within `δ ≤ 2ν` of a
lifted released preparation whose clean decoded vector is exactly `x / B`, `0 < B ≤ g ‖x‖`. -/
theorem noutcome_of_released
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
      Fintype.card S ≤ nP + 1)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j))
    (hvalid : ∀ i ∈ prepN, i.Valid) (hP : Pres2 (ZeroOn reflWire) (nrun prim prepN))
    (Urel : Reg (AW a m r K k l f) (Reg S ℂ) →L[ℂ] Reg (AW a m r K k l f) (Reg S ℂ))
    {δ : ℝ} (hA : ApproxOn CleanX (nrun prim prepN) (liftB (conj Urel)) δ)
    (x : Reg S ℂ) (B g ε : ℝ) (hx : x ≠ 0) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hB : 0 < B) (hBudget : B ≤ g * ‖x‖)
    (hrel : B • (goodF†) (Urel (GateODE.seedState seedV)) = x)
    (hδ : δ ≤ 2 * ImprovedODEQueryBudget.precision g ε) :
    NOutcome prepN g ε hg prim x := by
  refine noutcome_direct hnP prepN prim hprim hvalid hP x B g ε hx hg hε hεHalf hB hBudget ?_
  refine (vector_error_direct (nrun prim prepN) Urel hA x B hB.le hrel).trans ?_
  calc B * δ ≤ B * (2 * ImprovedODEQueryBudget.precision g ε) :=
        mul_le_mul_of_nonneg_left hδ hB.le
    _ = 2 * ImprovedODEQueryBudget.precision g ε * B := by ring

end Native

end

end SparseHamiltonian.ZeroTimeGateODE
