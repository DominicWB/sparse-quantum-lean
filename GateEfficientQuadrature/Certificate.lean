import GateEfficientQuadrature.Energy

/-!
# The source certificate of the left-endpoint quadrature

The proof of Theorem `ode:thm:gates` specifies "a sufficient positive quadrature for time-dependent
forcing": if `‖b(v)‖ ≤ b_*` and `Lip(b) ≤ L_b`, "contractivity and `‖A(v)‖ ≤ √s (η_D + η_H)` give
Lipschitz bound `√s (η_D + η_H) b_* + L_b` for `v ↦ U(T, v) b(v)`" (below `Λ_A = √s (η_D + η_H)` and
`C_b = Λ_A b_* + L_b`), and "a power-of-two left-endpoint mesh with
`m ≥ max{1, T² [√s (η_D + η_H) b_* + L_b] / (2 ν B)}` has vector quadrature error at most `ν B`"
(that is, `m ≥ max{1, T² C_b / (2 ν B)}`), which follows from the bound `T² C_b / (2m)` for `m`
nodes. With the propagator `U` of the dissipative equation (not a Lean object here) the vector
quadrature error is the first source certificate of `ode:eq:gate-source-certificates`,
`‖x(T) - U(T, 0) x₀ - ∑_i (T/m) U(T, v_i) b(v_i)‖`, by the Duhamel formula. This module proves both
statements with the propagator written through solutions of the homogeneous equation, and proves the
certificate directly, by a telescoping energy estimate, without the Duhamel formula:

* `flow_lipschitz`: for solutions `Y`, `Y'` of `y' = -G(u) y` from `v ≤ v'` with `Y(v) = b(v)`,
  `Y'(v') = b(v')`, `‖Y(T) - Y'(T)‖ ≤ (Λ b_* + L) (v' - v)` (the Lipschitz bound of
  `v ↦ U(T, v) b(v)`), for an accretive generator with `‖G(u)‖ ≤ Λ` and an `L`-Lipschitz forcing
  bounded by `b_*`;
* `step_left`: one interval `[a, a + h]`;
* `cert_left`: for `n` nodes `q T / n` (`q < n`, the paper's `m`), homogeneous solutions `Y_q`
  from `q T / n` with `Y_q(q T / n) = (T / n) f_q` and `y_0` from `0` with `y_0(0) = x(0)`, every
  solution `x` of `x' = -G(u) x + b(u)` satisfies
  `‖x(T) - y_0(T) - ∑_q Y_q(T)‖ ≤ (Λ b_s + L) T² / (2n) + T δ`
  for samples `f_q` with `‖f_q‖ ≤ b_s` and `‖b(q T / n) - f_q‖ ≤ δ`; with `f_q = b(q T / n)`
  this is `T² C_b / (2n)`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateQuad

noncomputable section
open Set
open TimeDependentODE (SolvesODE Accretive)
open scoped InnerProduct BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **The flow of the forcing is Lipschitz** (the paper's "contractivity and
`‖A(v)‖ ≤ √s (η_D + η_H)` give Lipschitz bound `√s (η_D + η_H) b_* + L_b` for `v ↦ U(T, v) b(v)`",
with any bound `Λ` of the generator in place of `√s (η_D + η_H)`). For an accretive generator with
`‖G(u)‖ ≤ Λ`, an `L`-Lipschitz forcing bounded by `b_*` on `[0, T]` and solutions `Y`, `Y'` of
`y' = -G(u) y` on `[v, T]` and `[v', T]` with `Y(v) = b(v)` and `Y'(v') = b(v')`,
`‖Y(T) - Y'(T)‖ ≤ (Λ b_* + L)(v' - v)`. -/
theorem flow_lipschitz {G : ℝ → V →L[ℂ] V} {b Y Y' : ℝ → V} {T Λ L bs v v' : ℝ}
    (hv : 0 ≤ v) (hvv : v ≤ v') (hv'T : v' ≤ T)
    (hG : ∀ u ∈ Icc 0 T, Accretive (G u)) (hGn : ∀ u ∈ Icc 0 T, ‖G u‖ ≤ Λ)
    (hb : ∀ u ∈ Icc 0 T, ‖b u‖ ≤ bs)
    (hbL : ∀ u ∈ Icc 0 T, ∀ u' ∈ Icc 0 T, ‖b u - b u'‖ ≤ L * |u - u'|)
    (hY : SolvesODE G (fun _ => 0) Y v T) (hY0 : Y v = b v)
    (hY' : SolvesODE G (fun _ => 0) Y' v' T) (hY'0 : Y' v' = b v') :
    ‖Y T - Y' T‖ ≤ (Λ * bs + L) * (v' - v) := by
  have hT : 0 ≤ T := hv.trans (hvv.trans hv'T)
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (hGn 0 ⟨le_rfl, hT⟩)
  have hbs : 0 ≤ bs := (norm_nonneg _).trans (hb 0 ⟨le_rfl, hT⟩)
  have hvI : v ∈ Icc 0 T := ⟨hv, hvv.trans hv'T⟩
  have hv'I : v' ∈ Icc 0 T := ⟨hv.trans hvv, hv'T⟩
  -- `Y - b(v)` on `[v, v']` has the forcing `-G(u) b(v)`
  have hc : ∀ u ∈ Icc v v', HasDerivWithinAt (fun _ : ℝ => -b v) 0 (Icc v v') u :=
    fun u _ => hasDerivWithinAt_const _ _ _
  have hU := solves_add_path (hY.mono le_rfl hv'T) hc
  have h1 : ‖Y v' + -b v‖ ≤ ‖Y v + -b v‖ + (0 + 0) * (v' - v) ^ 2 / 2 + Λ * bs * (v' - v) :=
    energy_affine hvv hU (fun u hu => hG u ⟨hv.trans hu.1, hu.2.trans hv'T⟩) le_rfl le_rfl
      (mul_nonneg hΛ hbs) (by
        intro u hu
        have huI : u ∈ Icc 0 T := ⟨hv.trans hu.1, hu.2.trans hv'T⟩
        simp only [zero_add, map_neg, norm_neg, zero_mul]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hGn u huI) (hb v hvI) (norm_nonneg _) hΛ))
  rw [hY0, add_neg_cancel, norm_zero] at h1
  -- the difference `Y - Y'` on `[v', T]` is a homogeneous solution
  have hD := solves_sub_homog (hY.mono hvv le_rfl) hY'
  have h2 : ‖Y T - Y' T‖ ≤ ‖Y v' - Y' v'‖ :=
    homog_norm_le hv'T hD (fun u hu => hG u ⟨(hv.trans hvv).trans hu.1, hu.2⟩)
  rw [hY'0] at h2
  have h3 : ‖b v - b v'‖ ≤ L * (v' - v) := by
    have := hbL v hvI v' hv'I
    rwa [abs_sub_comm, abs_of_nonneg (by linarith)] at this
  calc ‖Y T - Y' T‖ ≤ ‖Y v' - b v'‖ := h2
    _ = ‖(Y v' + -b v) + (b v - b v')‖ := by congr 1; abel
    _ ≤ ‖Y v' + -b v‖ + ‖b v - b v'‖ := norm_add_le _ _
    _ ≤ Λ * bs * (v' - v) + L * (v' - v) := add_le_add (by linarith) h3
    _ = (Λ * bs + L) * (v' - v) := by ring

/-- **One left-endpoint interval.** For a solution `E` of `E' = -G(u) E + b(u)` on `[a, a + h]`
with an accretive generator, `‖G(u)‖ ≤ Λ`, `‖b(u) - b(a)‖ ≤ L (u - a)` and a sample `f` with
`‖f‖ ≤ b_s` and `‖b(a) - f‖ ≤ δ`,
`‖E(a + h)‖ ≤ ‖E(a) + h f‖ + (Λ b_s + L) h² / 2 + δ h`. -/
theorem step_left {G : ℝ → V →L[ℂ] V} {b E : ℝ → V} {a h Λ L δ bs : ℝ} (hh : 0 ≤ h)
    (hE : SolvesODE G b E a (a + h)) (hG : ∀ u ∈ Icc a (a + h), Accretive (G u))
    (hGn : ∀ u ∈ Icc a (a + h), ‖G u‖ ≤ Λ) (hΛ : 0 ≤ Λ) (hL : 0 ≤ L) (f : V) (hf : ‖f‖ ≤ bs)
    (hbL : ∀ u ∈ Icc a (a + h), ‖b u - b a‖ ≤ L * (u - a)) (hbf : ‖b a - f‖ ≤ δ) :
    ‖E (a + h)‖ ≤ ‖E a + ((h : ℝ) : ℂ) • f‖ + (Λ * bs + L) * h ^ 2 / 2 + δ * h := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hbf
  have hbs : 0 ≤ bs := (norm_nonneg _).trans hf
  have hφ : ∀ u ∈ Icc a (a + h), HasDerivWithinAt (fun t : ℝ => ((a + h - t : ℝ) : ℂ) • f) (-f)
      (Icc a (a + h)) u := by
    intro u _
    have h1 : HasDerivAt (fun t : ℝ => ((a + h - t : ℝ) : ℂ)) ((-1 : ℝ) : ℂ) u :=
      ((hasDerivAt_id u).const_sub (a + h)).ofReal_comp
    exact (h1.smul_const f).hasDerivWithinAt.congr_deriv (by simp)
  have hU := solves_add_path hE hφ
  have hen : ‖E (a + h) + ((a + h - (a + h) : ℝ) : ℂ) • f‖ ≤
      ‖E a + ((a + h - a : ℝ) : ℂ) • f‖ + (Λ * bs + L) * (a + h - a) ^ 2 / 2 +
        δ * (a + h - a) :=
    energy_affine (le_add_of_nonneg_right hh) hU hG (mul_nonneg hΛ hbs) hL hδ (by
      intro u hu
      have hcu : 0 ≤ a + h - u := by linarith [hu.2]
      have h1 : ‖G u (((a + h - u : ℝ) : ℂ) • f)‖ ≤ Λ * bs * (a + h - u) := by
        rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcu]
        calc (a + h - u) * ‖G u f‖ ≤ (a + h - u) * (Λ * bs) :=
              mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans
                (mul_le_mul (hGn u hu) hf (norm_nonneg _) hΛ)) hcu
          _ = Λ * bs * (a + h - u) := by ring
      have h2 : ‖b u + -f‖ ≤ L * (u - a) + δ := by
        calc ‖b u + -f‖ = ‖(b u - b a) + (b a - f)‖ := by congr 1; abel
          _ ≤ ‖b u - b a‖ + ‖b a - f‖ := norm_add_le _ _
          _ ≤ L * (u - a) + δ := add_le_add (hbL u hu) hbf
      calc ‖b u + -f + G u (((a + h - u : ℝ) : ℂ) • f)‖ ≤
            ‖b u + -f‖ + ‖G u (((a + h - u : ℝ) : ℂ) • f)‖ := norm_add_le _ _
        _ ≤ (L * (u - a) + δ) + Λ * bs * (a + h - u) := add_le_add h2 h1
        _ = Λ * bs * (a + h - u) + L * (u - a) + δ := by ring)
  have e1 : (a + h - (a + h) : ℝ) = 0 := by ring
  have e2 : (a + h - a : ℝ) = h := by ring
  rw [e1, e2, Complex.ofReal_zero, zero_smul, add_zero] at hen
  exact hen

/-- **The source certificate of the left-endpoint quadrature.** For a solution `x` of
`x' = -G(u) x + b(u)` on `[0, T]` with an accretive generator, `‖G(u)‖ ≤ Λ` and an `L`-Lipschitz
forcing, samples `f_q` (`q < n`) with `‖f_q‖ ≤ b_s` and `‖b(q T / n) - f_q‖ ≤ δ`, a homogeneous
solution `y_0` on `[0, T]` with `y_0(0) = x(0)` and homogeneous solutions `Y_q` on
`[q T / n, T]` with `Y_q(q T / n) = (T / n) f_q`,
`‖x(T) - y_0(T) - ∑_{q < n} Y_q(T)‖ ≤ (Λ b_s + L) T² / (2n) + T δ`. -/
theorem cert_left {G : ℝ → V →L[ℂ] V} {b x y0 : ℝ → V} {Y : ℕ → ℝ → V} {f : ℕ → V}
    {T Λ L δ bs : ℝ} {n : ℕ} (hT : 0 ≤ T) (hn : 0 < n)
    (hx : SolvesODE G b x 0 T) (hG : ∀ u ∈ Icc 0 T, Accretive (G u))
    (hGn : ∀ u ∈ Icc 0 T, ‖G u‖ ≤ Λ)
    (hbL : ∀ u ∈ Icc 0 T, ∀ u' ∈ Icc 0 T, ‖b u - b u'‖ ≤ L * |u - u'|) (hL : 0 ≤ L)
    (hf : ∀ q < n, ‖f q‖ ≤ bs) (hbf : ∀ q < n, ‖b (q * T / n) - f q‖ ≤ δ)
    (hy0 : SolvesODE G (fun _ => 0) y0 0 T) (hy00 : y0 0 = x 0)
    (hY : ∀ q < n, SolvesODE G (fun _ => 0) (Y q) (q * T / n) T)
    (hY0 : ∀ q < n, Y q (q * T / n) = ((T / n : ℝ) : ℂ) • f q) :
    ‖x T - y0 T - ∑ q ∈ Finset.range n, Y q T‖ ≤ (Λ * bs + L) * T ^ 2 / (2 * n) + T * δ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (hGn 0 ⟨le_rfl, hT⟩)
  have hbs : 0 ≤ bs := (norm_nonneg _).trans (hf 0 hn)
  set h : ℝ := T / n with hh_def
  have hh : 0 ≤ h := div_nonneg hT hnR.le
  have hnode : ∀ k : ℕ, (k : ℝ) * T / n = k * h := by
    intro k
    rw [hh_def]
    ring
  have hnh : (n : ℝ) * h = T := by
    rw [hh_def]
    field_simp
  have hkT : ∀ k ≤ n, (k : ℝ) * h ≤ T := by
    intro k hk
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
    rw [← hnh]
    exact mul_le_mul_of_nonneg_right hkn hh
  have key : ∀ k ≤ n, ‖x (k * h) - y0 (k * h) - ∑ q ∈ Finset.range k, Y q (k * h)‖ ≤
      k * ((Λ * bs + L) * h ^ 2 / 2 + δ * h) := by
    intro k
    induction k with
    | zero =>
        intro _
        simp [hy00]
    | succ k ih =>
        intro hk
        have hk' : k < n := hk
        have ha0 : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg k) hh
        have hahT : (k : ℝ) * h + h ≤ T := by
          have h1 := hkT (k + 1) hk
          push_cast at h1
          linarith
        have haI : (k : ℝ) * h ∈ Icc 0 T := ⟨ha0, le_trans (le_add_of_nonneg_right hh) hahT⟩
        have hsub : ∀ u ∈ Icc ((k : ℝ) * h) ((k : ℝ) * h + h), u ∈ Icc 0 T :=
          fun u hu => ⟨ha0.trans hu.1, hu.2.trans hahT⟩
        have hS : SolvesODE G (fun _ => 0) (fun u => y0 u + ∑ q ∈ Finset.range (k + 1), Y q u)
            ((k : ℝ) * h) ((k : ℝ) * h + h) := by
          apply homog_add (hy0.mono ha0 hahT)
          apply homog_sum
          intro q hq
          have hqk : q ≤ k := Finset.mem_range_succ_iff.mp hq
          have hq' : q < n := lt_of_le_of_lt hqk hk'
          have hqa : (q : ℝ) * T / n ≤ (k : ℝ) * h := by
            rw [hnode q]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hqk) hh
          exact (hY q hq').mono hqa hahT
        have hE := solves_sub_homog (hx.mono ha0 hahT) hS
        have hYk : Y k ((k : ℝ) * h) = ((h : ℝ) : ℂ) • f k := by
          rw [← hnode k]
          exact hY0 k hk'
        have hstep := step_left (δ := δ) hh hE (fun u hu => hG u (hsub u hu))
          (fun u hu => hGn u (hsub u hu)) hΛ hL (f k) (hf k hk')
          (fun u hu => by
            have h1 := hbL u (hsub u hu) ((k : ℝ) * h) haI
            rwa [abs_of_nonneg (by linarith [hu.1])] at h1)
          (by rw [← hnode k]; exact hbf k hk')
        have hEa : x ((k : ℝ) * h) - (y0 ((k : ℝ) * h) +
              ∑ q ∈ Finset.range (k + 1), Y q ((k : ℝ) * h)) + ((h : ℝ) : ℂ) • f k =
            x ((k : ℝ) * h) - y0 ((k : ℝ) * h) -
              ∑ q ∈ Finset.range k, Y q ((k : ℝ) * h) := by
          rw [Finset.sum_range_succ, hYk]
          abel
        have hcast : ((k + 1 : ℕ) : ℝ) * h = (k : ℝ) * h + h := by
          push_cast
          ring
        rw [hcast]
        calc ‖x ((k : ℝ) * h + h) - y0 ((k : ℝ) * h + h) -
              ∑ q ∈ Finset.range (k + 1), Y q ((k : ℝ) * h + h)‖
            = ‖x ((k : ℝ) * h + h) - (y0 ((k : ℝ) * h + h) +
                ∑ q ∈ Finset.range (k + 1), Y q ((k : ℝ) * h + h))‖ := by rw [sub_sub]
          _ ≤ ‖x ((k : ℝ) * h) - (y0 ((k : ℝ) * h) +
                ∑ q ∈ Finset.range (k + 1), Y q ((k : ℝ) * h)) + ((h : ℝ) : ℂ) • f k‖ +
                (Λ * bs + L) * h ^ 2 / 2 + δ * h := hstep
          _ = ‖x ((k : ℝ) * h) - y0 ((k : ℝ) * h) -
                ∑ q ∈ Finset.range k, Y q ((k : ℝ) * h)‖ +
                ((Λ * bs + L) * h ^ 2 / 2 + δ * h) := by rw [hEa]; ring
          _ ≤ k * ((Λ * bs + L) * h ^ 2 / 2 + δ * h) +
                ((Λ * bs + L) * h ^ 2 / 2 + δ * h) := add_le_add (ih hk'.le) le_rfl
          _ = ((k + 1 : ℕ) : ℝ) * ((Λ * bs + L) * h ^ 2 / 2 + δ * h) := by
                push_cast
                ring
  have hfin := key n le_rfl
  rw [hnh] at hfin
  calc ‖x T - y0 T - ∑ q ∈ Finset.range n, Y q T‖ ≤
      n * ((Λ * bs + L) * h ^ 2 / 2 + δ * h) := hfin
    _ = (Λ * bs + L) * T ^ 2 / (2 * n) + T * δ := by
        rw [hh_def]
        field_simp

end

end SparseHamiltonian.GateQuad
