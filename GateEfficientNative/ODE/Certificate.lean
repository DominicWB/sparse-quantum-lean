import GateEfficientNative.ODE.Grover
import SparseODE.ImprovedODEQueryBudget
import SparseODE.ODEGroverActual

/-!
# The certificate of the native preparation

The released analysis certifies the decoded vector `d` of the released
preparation `U_rel` (with exact private Cayley operations and exact source
interfaces): `‖3B d - x‖ ≤ 6νB` for the solution `x`, the source mass `B` and
`ν = ε / (10000 g)`.  If the native preparation is within `δ ≤ ν` of the
lifted released preparation on clean work wires, its decoded vector `dN`
satisfies `‖3B dN - x‖ ≤ 9νB` (`native_vector_error`).  This still gives the
amplitude interval `[1/(4g), 1/2)` and the direction error `ε / 500`
(`output_certificate9`), so the released randomized amplification theorem
applies to the native trials (`native_trial_bounds`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateODE (OInstr OWire AW goodF)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-! ### The output certificate with the enlarged vector error -/

section Output

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The released output certificate with vector error `9νB` instead of `6νB`. -/
theorem output_certificate9 (x y : E) (B g ε : ℝ)
    (hx : x ≠ 0) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hNorm : ‖x‖ ≤ B) (hBudget : B ≤ g * ‖x‖)
    (hError : ‖y - x‖ ≤ 9 * ImprovedODEQueryBudget.precision g ε * B) :
    y ≠ 0 ∧ ‖unitDirection y‖ = 1 ∧
      ‖unitDirection y - unitDirection x‖ ≤ ε / 500 ∧
      1 / (4 * g) ≤ ‖y‖ / (3 * B) ∧ ‖y‖ / (3 * B) < 1 / 2 := by
  have hg0 : 0 < g := by linarith
  have hB : 0 < B := (norm_pos_iff.mpr hx).trans_le hNorm
  have hν : ImprovedODEQueryBudget.precision g ε = ε / (10000 * g) := rfl
  have hRel : ‖y - x‖ ≤ (ε / 1000) * ‖x‖ := by
    refine hError.trans ?_
    calc 9 * ImprovedODEQueryBudget.precision g ε * B
        ≤ 9 * ImprovedODEQueryBudget.precision g ε * (g * ‖x‖) :=
          mul_le_mul_of_nonneg_left hBudget (by rw [hν]; positivity)
      _ = (9 * ε / 10000) * ‖x‖ := by
          rw [hν]
          field_simp
      _ ≤ (ε / 1000) * ‖x‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
          linarith
  have hSmall : ε / 1000 < 1 := by linarith
  have hDirection := ODEStateNormalization.relative_error x y (ε / 1000) hx hSmall hRel
  have hLower := ODEStateNormalization.extraction_amplitude_lower_of_budget_le x y B g 3
    (ε / 1000) hB hg0 (by norm_num) hSmall.le hBudget hRel
  have hνBound : ImprovedODEQueryBudget.precision g ε ≤ 1 / 10000 := by
    rw [hν]
    apply (div_le_iff₀ (by positivity : 0 < 10000 * g)).2
    nlinarith
  have hUpper : ‖y‖ ≤ (1 + 9 * ImprovedODEQueryBudget.precision g ε) * B := by
    calc
      _ ≤ ‖y - x‖ + ‖x‖ := by
        simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub y x 0
      _ ≤ 9 * ImprovedODEQueryBudget.precision g ε * B + B := add_le_add hError hNorm
      _ = _ := by ring
  refine ⟨hDirection.1, ODEStateNormalization.unitDirection_norm y hDirection.1, ?_, ?_, ?_⟩
  · convert hDirection.2 using 1; ring
  · calc
      1 / (4 * g) = (3 / 4 : ℝ) / (3 * g) := by
        field_simp
      _ ≤ (1 - ε / 1000) / (3 * g) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      _ ≤ ‖y‖ / (3 * B) := hLower
  · apply (div_lt_iff₀ (by positivity : 0 < 3 * B)).2
    have hScale := mul_le_mul_of_nonneg_right hνBound hB.le
    nlinarith

/-- The randomized amplification bounds for a decoded vector with the enlarged
error `9νB`, for any isometric decoding `G`, unitary preparation `U` and unit
seed `s`. -/
theorem trial_bounds_of_vec {K P : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    (G : P →L[ℂ] K) (hG : G† ∘L G = 1) (U : K →L[ℂ] K) (hU : IsUnitary U) (s : K)
    (hs : ‖s‖ = 1) (x : P) (B g ε : ℝ) (hx : x ≠ 0) (hg : 1 ≤ g) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2) (hNorm : ‖x‖ ≤ B) (hBudget : B ≤ g * ‖x‖)
    (hvec : ‖(3 * B) • (G†) (U s) - x‖ ≤ 9 * ImprovedODEQueryBudget.precision g ε * B) :
    0 < ODEGroverAverage.chosenIterations g ∧
    (ODEGroverAverage.chosenIterations g : ℝ) ≤ 5 * g ∧
    (1 : ℝ) / 4 ≤ (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations g),
      ‖ODEHeraldedSuccess.successProjector G (ODEGroverActual.trial G U s j)‖ ^ 2) /
        (ODEGroverAverage.chosenIterations g : ℝ) ∧
    ∀ j : ℕ, (G†) (ODEGroverActual.trial G U s j) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection ((G†) (ODEGroverActual.trial G U s j)) - unitDirection x‖ ≤
          ε / 500 := by
  have hB : 0 < B := (norm_pos_iff.mpr hx).trans_le hNorm
  have h3B : 0 < 3 * B := by positivity
  obtain ⟨_, _, hdir, hlow, hup⟩ := output_certificate9 x _ B g ε hx hg hε hεHalf hNorm hBudget hvec
  have hscale : ‖(3 * B) • (G†) (U s)‖ / (3 * B) = ‖(G†) (U s)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos h3B]
    exact mul_div_cancel_left₀ _ h3B.ne'
  rw [hscale] at hlow hup
  rw [ODEHeraldedSuccess.unitDirection_pos_smul (3 * B) h3B] at hdir
  have hamp : ODEGroverActual.amplitude G U s = ‖(G†) (U s)‖ := by
    rw [ODEGroverActual.amplitude, ← ODEHeraldedSuccess.successfulComponent,
      ODEHeraldedSuccess.successfulComponent_norm _ hG]
    rfl
  exact ODEGroverActual.randomized_certificate G hG U hU s hs g hg (by rw [hamp]; exact hlow)
    (by rw [hamp]; exact hup.le) x (ε / 500) hdir

end Output

/-! ### The decoded vector of the native preparation -/

section Native

variable {a m r K k l f : ℕ} {S Zs Z Y J : Type*} {nP bT bP A : ℕ}
variable [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y]

theorem cleanEmb_isometry {B X : Type*} [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X] :
    (cleanEmb (B := B) (X := X) (R := ℂ))† ∘L cleanEmb = 1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp norm_cleanEmb

/-- The clean decoding of a lifted embedded vector is the released decoding. -/
theorem goodN_adjoint_cleanEmb (ψ : Reg (AW a m r K k l f) (Reg S ℂ)) :
    ((goodN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S) (Zs := Zs)
      (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A))†) (cleanEmb (fl ψ)) = (goodF†) ψ := by
  have h1 : ((cleanEmb (B := AW a m r K k l f ⊕ S) (X := XW Z bT bP A ⊕ OX Zs nP) (R := ℂ))†)
      (cleanEmb (fl ψ)) = fl ψ := by
    rw [← comp_apply ((cleanEmb (B := AW a m r K k l f ⊕ S) (X := XW Z bT bP A ⊕ OX Zs nP)
      (R := ℂ))†), cleanEmb_isometry, one_apply_eq_self]
  rw [goodN, sysEmb, adjoint_comp, adjoint_comp, fl_adjoint, comp_apply, comp_apply, h1]
  simp

theorem norm_goodN_adjoint_le (φ : Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ) :
    ‖((goodN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S) (Zs := Zs)
      (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A))†) φ‖ ≤ ‖φ‖ := by
  have hn : ‖(goodN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
      (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A))‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun ψ => by rw [norm_goodN, one_mul])
  have hadj : ‖(goodN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
      (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A))†‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact hn
  calc _ ≤ ‖(goodN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
        (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A))†‖ * ‖φ‖ := le_opNorm _ _
    _ ≤ 1 * ‖φ‖ := mul_le_mul_of_nonneg_right hadj (norm_nonneg _)
    _ = ‖φ‖ := one_mul _

/-- **The decoded vector of the native preparation** is within `δ` of the
released decoded vector. -/
theorem native_decoded_close
    (UN : Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ →L[ℂ]
      Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ)
    (Urel : Reg (AW a m r K k l f) (Reg S ℂ) →L[ℂ] Reg (AW a m r K k l f) (Reg S ℂ))
    {δ : ℝ} (hA : ApproxOn CleanX UN (liftB (conj Urel)) δ) :
    ‖(goodN†) (UN sN) - (goodF†) (Urel (GateODE.seedState seedV))‖ ≤ δ := by
  have hsupp : Supp CleanX (sN : Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ) := by
    rw [sN_eq_cleanEmb]; exact supp_cleanEmb _
  have h1 := hA sN hsupp
  rw [norm_sN, mul_one] at h1
  have e : liftB (X := XW Z bT bP A ⊕ OX Zs nP) (conj Urel) sN =
      cleanEmb (fl (Urel (GateODE.seedState seedV))) := by
    rw [sN_eq_cleanEmb, ← comp_apply, liftB_cleanEmb, comp_apply, conj_fl]
  have e2 : (goodF†) (Urel (GateODE.seedState seedV)) =
      ((goodN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S) (Zs := Zs)
        (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A))†)
        (liftB (X := XW Z bT bP A ⊕ OX Zs nP) (conj Urel) sN) := by
    rw [e, goodN_adjoint_cleanEmb]
  rw [e2, ← map_sub]
  exact (norm_goodN_adjoint_le _).trans h1

/-- **The vector error of the native preparation.** -/
theorem native_vector_error
    (UN : Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ →L[ℂ]
      Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ)
    (Urel : Reg (AW a m r K k l f) (Reg S ℂ) →L[ℂ] Reg (AW a m r K k l f) (Reg S ℂ))
    {δ : ℝ} (hA : ApproxOn CleanX UN (liftB (conj Urel)) δ) (x : Reg S ℂ) (B ν : ℝ) (hB : 0 ≤ B)
    (hrel : ‖(3 * B) • (goodF†) (Urel (GateODE.seedState seedV)) - x‖ ≤ 6 * ν * B)
    (hδ : δ ≤ ν) :
    ‖(3 * B) • (goodN†) (UN sN) - x‖ ≤ 9 * ν * B := by
  have hc := native_decoded_close UN Urel hA
  have e : (3 * B) • ((goodN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
      (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A))†) (UN sN) - x =
      (3 * B) • ((goodN†) (UN sN) - (goodF†) (Urel (GateODE.seedState seedV))) +
        ((3 * B) • (goodF†) (Urel (GateODE.seedState seedV)) - x) := by
    rw [smul_sub]
    abel
  rw [e]
  calc _ ≤ ‖(3 * B) • (((goodN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
        (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A))†) (UN sN) -
        (goodF†) (Urel (GateODE.seedState seedV)))‖ +
        ‖(3 * B) • (goodF†) (Urel (GateODE.seedState seedV)) - x‖ := norm_add_le _ _
    _ ≤ 3 * B * δ + 6 * ν * B := by
        gcongr
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left hc (by positivity)
    _ ≤ 3 * B * ν + 6 * ν * B := by gcongr
    _ = 9 * ν * B := by ring

variable (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)

/-- **Mean success and direction error of the native trials.** -/
theorem native_trial_bounds
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
      Fintype.card S ≤ nP + 1)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hU : IsUnitary (nrun prim prepN)) (hP : Pres2 (ZeroOn reflWire) (nrun prim prepN))
    (Urel : Reg (AW a m r K k l f) (Reg S ℂ) →L[ℂ] Reg (AW a m r K k l f) (Reg S ℂ))
    {δ : ℝ} (hA : ApproxOn CleanX (nrun prim prepN) (liftB (conj Urel)) δ)
    (x : Reg S ℂ) (B g ε : ℝ) (hx : x ≠ 0) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hNorm : ‖x‖ ≤ B) (hBudget : B ≤ g * ‖x‖)
    (hrel : ‖(3 * B) • (goodF†) (Urel (GateODE.seedState seedV)) - x‖ ≤
      6 * ImprovedODEQueryBudget.precision g ε * B)
    (hδ : δ ≤ ImprovedODEQueryBudget.precision g ε) :
    0 < ODEGroverAverage.chosenIterations g ∧
    (ODEGroverAverage.chosenIterations g : ℝ) ≤ 5 * g ∧
    (1 : ℝ) / 4 ≤ (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations g),
      ‖ODEHeraldedSuccess.successProjector goodN (nrun prim (trialN prepN j) sN)‖ ^ 2) /
        (ODEGroverAverage.chosenIterations g : ℝ) ∧
    ∀ j : ℕ, (goodN†) (nrun prim (trialN prepN j) sN) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection ((goodN†) (nrun prim (trialN prepN j) sN)) - unitDirection x‖ ≤
          ε / 500 := by
  have hvec := native_vector_error (nrun prim prepN) Urel hA x B _
    ((norm_pos_iff.mpr hx).trans_le hNorm).le hrel hδ
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
  exact trial_bounds_of_vec G hGi U hU s hs x B g ε hx hg hε hεHalf hNorm hBudget hvec

end Native

end

end SparseHamiltonian.GateNative
