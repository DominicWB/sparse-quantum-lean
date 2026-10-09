import ODELowerBoundExtensions.Homogeneous.Solution
import ODELowerBoundExtensions.Homogeneous.Readout
import ODELowerBoundExtensions.Homogeneous.Compile
import ODELowerBoundExtensions.Homogeneous.General

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
-- The nested time-addressed workspaces exceed the default instance size.
set_option synthInstance.maxSize 1024

/-!
# Remark `odel:rem:homogeneous`: the homogeneous variant of Theorem `odel:thm:joint`

Manuscript lines 3907-3952. For `s ≥ 4`, `ḡ ≥ 2`, `τ ≥ 20(1 + log ḡ)` and `0 < ε ≤ 1/64`
(`HomRange`), the source-free family `homFamilyAt` (no source, `b = 0`: `homFamilyAt_src`;
time dependent, with one dissipative stage `D = P_reject`) is in the class with `η = 1`,
`T = τ` and `g ≤ ḡ`, and forces `ḡ √s τ / 500` matrix queries (`hom_witness`, explicit
constant `c_H = 1/500`, `homConst`): eq. `odel:eq:joint` for this homogeneous family. Moreover
`g = Θ(ḡ)`: `(4/√17)√M ≤ g ≤ √M` (`homFamily_g`, line 3933), hence
`(4/√34) ḡ ≤ g ≤ ḡ` (`hom_g_theta`), and the dimension is `2(2Mm + s) ≤ 6 ḡ² s`
(`hom_instance_props`).

Route (lines 3935-3937, 3946-3949). Run the solver; on success measure the half indicator
(`homHalfObs`) of the candidate register, on failure output a fair bit. The normalised solution
has probability at least `16/17` on `a_*`, so the ideal signed correlation is at least `15/17`
(`homEnd_ideal_corr`), and `Readout.heralded_correlation` gives the unconditional correlation
`β = (2/3)(15/17 - 2ε)` (`homCorr`). The access compiles to `hardCost` membership queries
(`implementsOn_hom`), and `outer_general` (Lemma `odel:lem:outer` via `outer_count_ge`) gives
`β² n √(Mm) / 16` value queries (`hom_forces`). With `n ≥ τ/5` (`fifth_le_homN`) and
`√(Mm) ≥ ḡ√s/2`, this is at least `ḡ √s τ / 500` (`hom_numeric`).
-/

namespace ODELowerBoundExtensions.Homogeneous

noncomputable section
open SparseLowerBounds SparseLowerBounds.ODE SparseHamiltonian NativeSparseBlockEncoding
open OracleCircuit
open scoped InnerProduct InnerProductSpace

section Family

variable {M n μ s : ℕ} {hμ : 1 ≤ μ} {hμs : 2 ^ μ ≤ s} {T : ℝ} {hT : homBusy M n ≤ T}

/-- **The promises of the class** (lines 3925-3933): accretive generators, row and column
norms at most `η = 1`, and the nonzero solution `homSol` with `B = 1 ≤ ḡ ‖x(T)‖` whenever
`√M ≤ ḡ` (`‖x(T)‖ ≥ 1/√M`). -/
theorem homFamily_inClass (hM : 1 ≤ M) {gbar : ℝ} (hg : Real.sqrt M ≤ gbar) :
    (homFamily M n μ s hμ hμs T hT).InClass 1 gbar := by
  exact
    { accretive := fun x k => accretive_homGen x.1 k
      row_norm := fun x k i => by rw [one_pow]; exact sum_norm_sq_homGen_row x.1 k i
      col_norm := fun x k j => by rw [one_pow]; exact sum_norm_sq_homGen_col x.1 k j
      solution := fun x => by
        refine ⟨homSol M n μ s x, homSol_solves hμ hμs hT x, ?_, ?_⟩
        · rw [homFamily_T, homSol_of_busy_le hM x hT]
          exact homEnd_ne_zero hM _
        · rw [homFamily_mass, norm_homInit hM, homFamily_T, homSol_of_busy_le hM x hT]
          have hpos : 0 < ‖homEnd M μ s (oddCand x)‖ :=
            norm_pos_iff.mpr (homEnd_ne_zero hM _)
          have h := (homEnd_g_bounds (μ := μ) (s := s) hM (oddCand x)).2
          rw [div_le_iff₀ hpos] at h
          nlinarith [mul_le_mul_of_nonneg_right hg hpos.le] }

/-- **The normalisation parameter of the family** (line 3933):
`(4/√17)√M ≤ g = B/‖x(T)‖ ≤ √M` on every input. -/
theorem homFamily_g (hM : 1 ≤ M) (x : Promised M n (2 ^ μ)) :
    4 / Real.sqrt 17 * Real.sqrt M ≤
        (homFamily M n μ s hμ hμs T hT).mass / ‖homSol M n μ s x T‖ ∧
      (homFamily M n μ s hμ hμs T hT).mass / ‖homSol M n μ s x T‖ ≤ Real.sqrt M := by
  rw [homFamily_mass, norm_homInit hM, homSol_of_busy_le hM x hT]
  exact homEnd_g_bounds hM (oddCand x)

/-- **Remark `odel:rem:homogeneous`, native form**: the homogeneous family forces
`β² n √(M 2^μ) / 16` value queries (and as many matrix queries), `β = (2/3)(15/17 - 2ε)`. -/
theorem hom_forces (hM : 2 ≤ M) (hMe : Even M) (hn : 1 ≤ n) {ε : ℝ} (hε : 2 * ε ≤ 15 / 17) :
    (homFamily M n μ s hμ hμs T hT).Forces ε
      (homCorr ε ^ 2 * n * Real.sqrt ((M : ℝ) * 2 ^ μ) / 16) := by
  intro ι _ G _ _ _ A
  have hacc : ∀ x, Readout.HeraldedAccurate A.out A.herald (A.prog.eval x A.seed)
      (ODEStateNormalization.unitDirection (homEnd M μ s (oddCand x))) ε := fun x => by
    have hx := A.accurate x _ (homSol_solves hμ hμs hT x)
    rwa [homFamily_T, homSol_of_busy_le (by omega) x hT] at hx
  have h := outer_general (S := HomIndex M μ s) hM hMe hn hμ hε (homBoolean ι M n μ s)
    (ancillaEmbed _) ancillaEmbed_isometry ((homFamily M n μ s hμ hμs T hT).access ι)
    (Family.access_unitary ι _) hardCost (implementsOn_hom ι hμ hμs T hT) A.prog A.seed
    A.seed_norm_le A.out A.out_isometry A.herald A.herald_proj A.success
    (fun x => ODEStateNormalization.unitDirection (homEnd M μ s (oddCand x)))
    (homHalfObs M μ s) homHalfObs_isSelfAdjoint norm_homHalfObs_le
    (fun x => homEnd_ideal_corr (by omega) (oddCand x)) hacc
  exact Hamiltonian.native_bound_of_cost A.prog (by unfold homCorr; linarith)

end Family

/-- **The hard family at the parameters** `(s, τ, ḡ)` (lines 3909-3910, 3946):
`M = jointM ḡ`, `m = 2^{jointMu s}`, `n = homN τ = ⌊τ/π⌋`, on `[0, τ]`. -/
def homFamilyAt (s : ℕ) (τ gbar : ℝ) (hs : 4 ≤ s) (hg : 2 ≤ gbar)
    (hτ : 20 * (1 + Real.log gbar) ≤ τ) :
    Family (Promised (jointM gbar) (homN τ) (2 ^ jointMu s))
      (HomIndex (jointM gbar) (jointMu s) s) (Hamiltonian.Word (jointMu s)) (homN τ + 4) s :=
  homFamily (jointM gbar) (homN τ) (jointMu s) s (one_le_jointMu (by omega))
    (two_pow_jointMu_le (by omega)) τ (homN_time hg hτ)

/-- **The hard family is homogeneous** (line 3929, `b = 0`). -/
theorem homFamilyAt_src {s : ℕ} {τ gbar : ℝ} (hs : 4 ≤ s) (hg : 2 ≤ gbar)
    (hτ : 20 * (1 + Real.log gbar) ≤ τ) (k : Fin (homN τ + 4)) :
    (homFamilyAt s τ gbar hs hg hτ).src k = 0 := rfl

/-- The dimension of the homogeneous index is `2(2Mm + s)`. -/
theorem card_homIndex {M μ s : ℕ} :
    Fintype.card (HomIndex M μ s) = 2 * (M * (2 * 2 ^ μ) + s) := by
  simp only [HomIndex, Fintype.card_prod, Fintype.card_bool, card_jointIndex]

/-- **The instance size** (lines 3866-3867, 3909): for `s ≥ 4` and `ḡ ≥ 2`,
`ḡ/√2 ≤ √M ≤ ḡ` and the dimension is `|HomIndex| = 2(2Mm + s) ≤ 6 ḡ² s`. -/
theorem hom_instance_props {s : ℕ} {gbar : ℝ} (hs : 4 ≤ s) (hg : 2 ≤ gbar) :
    gbar / Real.sqrt 2 ≤ Real.sqrt (jointM gbar) ∧ Real.sqrt (jointM gbar) ≤ gbar ∧
      (Fintype.card (HomIndex (jointM gbar) (jointMu s) s) : ℝ) ≤ 6 * gbar ^ 2 * s := by
  refine ⟨div_sqrt_two_le_sqrt_jointM hg, sqrt_jointM_le (by linarith), ?_⟩
  rw [card_homIndex]
  have hM := jointM_le gbar
  have hm : ((2 ^ jointMu s : ℕ) : ℝ) ≤ s := by exact_mod_cast two_pow_jointMu_le (by omega)
  push_cast at hm ⊢
  have hg2 : 1 ≤ gbar ^ 2 := by nlinarith
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have h1 := mul_le_mul hM hm (by positivity) (by positivity)
  have h2 := mul_le_mul_of_nonneg_right hg2 hs0
  linarith

/-- **`g = Θ(ḡ)`** (lines 3933, 3949): on the range, `(4/√34) ḡ ≤ g ≤ ḡ` on every input. -/
theorem hom_g_theta {s : ℕ} {τ gbar ε : ℝ} (h : HomRange s τ gbar ε)
    (x : Promised (jointM gbar) (homN τ) (2 ^ jointMu s)) :
    4 / Real.sqrt 34 * gbar ≤ (homFamilyAt s τ gbar h.s_ge h.gbar_ge h.tau_ge).mass /
        ‖homSol (jointM gbar) (homN τ) (jointMu s) s x τ‖ ∧
      (homFamilyAt s τ gbar h.s_ge h.gbar_ge h.tau_ge).mass /
        ‖homSol (jointM gbar) (homN τ) (jointMu s) s x τ‖ ≤ gbar := by
  have hs := h.s_ge
  have hg := h.gbar_ge
  have hM := four_le_jointM hg
  obtain ⟨h1, h2⟩ := homFamily_g (M := jointM gbar) (n := homN τ) (μ := jointMu s) (s := s)
    (hμ := one_le_jointMu (by omega)) (hμs := two_pow_jointMu_le (by omega)) (T := τ)
    (hT := homN_time hg h.tau_ge) (by omega) x
  refine ⟨le_trans ?_ h1, h2.trans (sqrt_jointM_le (by linarith))⟩
  have h17 : 0 < Real.sqrt 17 := Real.sqrt_pos.mpr (by norm_num)
  have h2' : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h34 : Real.sqrt 34 = Real.sqrt 17 * Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have e : 4 / Real.sqrt 34 * gbar = 4 / Real.sqrt 17 * (gbar / Real.sqrt 2) := by
    rw [h34]; field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left (div_sqrt_two_le_sqrt_jointM hg) (by positivity)

/-- **The constant `c_H = 1/500`**: on `HomRange`,
`ḡ √s τ / 500 ≤ β² n √(M m) / 16` (`hom_numeric`). -/
theorem hom_bound_le {s : ℕ} {τ gbar ε : ℝ} (h : HomRange s τ gbar ε) :
    homConst * gbar * Real.sqrt s * τ ≤
      homCorr ε ^ 2 * homN τ * Real.sqrt ((jointM gbar : ℝ) * 2 ^ jointMu s) / 16 :=
  hom_numeric (by linarith [twenty_le_tau h]) h.gbar_ge (homCorr_ge h.eps_le)

/-- **Remark `odel:rem:homogeneous`** (lines 3907-3952): for `s ≥ 4`, `ḡ ≥ 2`,
`τ ≥ 20(1 + log ḡ)` and `0 < ε ≤ 1/64`, the homogeneous (`b = 0`) time-dependent family is in
the class (`η = 1`, `T = τ`, `g ≤ ḡ`; `g = Θ(ḡ)` is `hom_g_theta`) and forces `ḡ √s τ / 500`
matrix queries (explicit constant `c_H = 1/500`, `homConst`), both value queries and total
count: eq. `odel:eq:joint` without a source. The remark's other claims are separate lemmas, as
for `joint_witness`: `b = 0` is `homFamilyAt_src`, `g = Θ(ḡ)` is `homFamily_g` / `hom_g_theta`,
and the dimension `2(2Mm + s) ≤ 6ḡ²s` is `hom_instance_props`. -/
theorem hom_witness {s : ℕ} {τ gbar ε : ℝ} (h : HomRange s τ gbar ε) :
    (homFamilyAt s τ gbar h.s_ge h.gbar_ge h.tau_ge).Witnesses τ gbar ε
      (homConst * gbar * Real.sqrt s * τ) := by
  have hb := hom_bound_le h
  have hs := h.s_ge
  have hM := four_le_jointM h.gbar_ge
  have hτ := twenty_le_tau h
  refine ⟨homFamily_inClass (by omega) (sqrt_jointM_le (by linarith [h.gbar_ge])),
    homFamily_T, ?_⟩
  intro ι _ G _ _ _ A
  have hf := hom_forces (s := s) (by omega) (even_jointM gbar) (one_le_homN (by linarith))
    (two_eps_le h.eps_le) ι G A
  exact ⟨hb.trans hf.1, hb.trans hf.2⟩

end

end ODELowerBoundExtensions.Homogeneous
