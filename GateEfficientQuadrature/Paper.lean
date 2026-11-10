import GateEfficientQuadrature.Mass

/-!
# The sufficient positive quadrature of the proof of Theorem `ode:thm:gates`

The proof of Theorem `ode:thm:gates` specifies a sufficient positive quadrature for time-dependent
forcing: if `‖b(v)‖ ≤ b_*` and `Lip(b) ≤ L_b` (below, `Λ_A = √s (η_D + η_H)` bounds the generator
and `C_b = Λ_A b_* + L_b`; the paper writes both out), "a power-of-two left-endpoint mesh with
`m ≥ max{1, T² [√s (η_D + η_H) b_* + L_b] / (2 ν B)}` has vector quadrature error at most `ν B`"
(that is, `m ≥ max{1, T² C_b / (2 ν B)}`), and `|B_m - B| ≤ T² L_b / (2m) ≤ ν B`,
`(1 - ν) B ≤ B_m ≤ (1 + ν) B`, `0 < B_m` and `B_m ≤ 2B`, including when `x₀ = 0`.

`paper_quadrature` states all of this, with the paper's number `m` of nodes written `n`, for a
solution `x` of `x' = -G(u) x + b(u)` on `[0, T]` with an accretive generator, `‖G(u)‖ ≤ Λ` (in the
paper `Λ = √s (η_D + η_H)`), the left-endpoint nodes `q T / n` with the weights `T / n` and the
exact samples `b(q T / n)`, every number `n ≥ 1` of nodes with `n ≥ T² (Λ b_* + L_b) / (2 ν B)` (a
power of two in the paper, `exists_pow_two_nodes`), and the source certificate written with
homogeneous solutions: `y_0` from `0` with `y_0(0) = x(0)` and `Y_q` from `q T / n` with `Y_q(q T /
n) = (T / n) b(q T / n)` (informally `U(T, 0) x₀` and `(T / n) U(T, v_q) b(v_q)`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateQuad

noncomputable section
open Set
open TimeDependentODE (SolvesODE Accretive)
open scoped InnerProduct BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **The sufficient positive quadrature of the proof of Theorem `ode:thm:gates`.** For a
solution `x` of `x' = -G(u) x + b(u)` on `[0, T]`, an accretive generator with `‖G(u)‖ ≤ Λ`, a
forcing with `‖b(u)‖ ≤ b_*` and `Lip(b) ≤ L`, `C_b = Λ b_* + L`, `B = ‖x(0)‖ + ∫_0^T ‖b‖ > 0`,
`0 < ν < 1` and `n ≥ 1` left-endpoint nodes with `n ≥ T² C_b / (2 ν B)` (the paper's `m`):

* the source certificate: `‖x(T) - y_0(T) - ∑_{q < n} Y_q(T)‖ ≤ ν B`;
* `|B_n - B| ≤ T² L / (2n) ≤ ν B` for `B_n = ‖x(0)‖ + ∑_{q < n} (T/n) ‖b(q T / n)‖`;
* `(1 - ν) B ≤ B_n ≤ (1 + ν) B`, `0 < B_n` and `B_n ≤ 2B`. -/
theorem paper_quadrature {G : ℝ → V →L[ℂ] V} {b x y0 : ℝ → V} {Y : ℕ → ℝ → V}
    {T Λ L bstar ν : ℝ} {n : ℕ} (hT : 0 ≤ T) (hn : 0 < n)
    (hx : SolvesODE G b x 0 T) (hG : ∀ u ∈ Icc 0 T, Accretive (G u))
    (hGn : ∀ u ∈ Icc 0 T, ‖G u‖ ≤ Λ) (hb : ∀ u ∈ Icc 0 T, ‖b u‖ ≤ bstar)
    (hbL : ∀ u ∈ Icc 0 T, ∀ u' ∈ Icc 0 T, ‖b u - b u'‖ ≤ L * |u - u'|) (hL : 0 ≤ L)
    (hy0 : SolvesODE G (fun _ => 0) y0 0 T) (hy00 : y0 0 = x 0)
    (hY : ∀ q < n, SolvesODE G (fun _ => 0) (Y q) (q * T / n) T)
    (hY0 : ∀ q < n, Y q (q * T / n) = ((T / n : ℝ) : ℂ) • b (q * T / n))
    (hB : 0 < contMass (x 0) b T) (hν0 : 0 < ν) (hν1 : ν < 1)
    (hnodes : T ^ 2 * (Λ * bstar + L) / (2 * ν * contMass (x 0) b T) ≤ n) :
    ‖x T - y0 T - ∑ q ∈ Finset.range n, Y q T‖ ≤ ν * contMass (x 0) b T ∧
      |quadMass (x 0) (fun q => b (q * T / n)) T n - contMass (x 0) b T| ≤
        T ^ 2 * L / (2 * n) ∧
      T ^ 2 * L / (2 * n) ≤ ν * contMass (x 0) b T ∧
      (1 - ν) * contMass (x 0) b T ≤ quadMass (x 0) (fun q => b (q * T / n)) T n ∧
      quadMass (x 0) (fun q => b (q * T / n)) T n ≤ (1 + ν) * contMass (x 0) b T ∧
      0 < quadMass (x 0) (fun q => b (q * T / n)) T n ∧
      quadMass (x 0) (fun q => b (q * T / n)) T n ≤ 2 * contMass (x 0) b T := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (hGn 0 ⟨le_rfl, hT⟩)
  have hbs : 0 ≤ bstar := (norm_nonneg _).trans (hb 0 ⟨le_rfl, hT⟩)
  have hνB : 0 < ν * contMass (x 0) b T := mul_pos hν0 hB
  have hnode : ∀ q < n, (q : ℝ) * T / n ∈ Icc 0 T := by
    intro q hq
    have hqn : (q : ℝ) ≤ n := by exact_mod_cast hq.le
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hnR]
    nlinarith
  have hsuff := nodes_sufficient hn hνB hnodes
  -- the source certificate
  have hcert := cert_left (f := fun q => b (q * T / n)) (δ := 0) (bs := bstar) hT hn hx hG hGn
    hbL hL (fun q hq => hb _ (hnode q hq)) (fun q _ => by simp) hy0 hy00 hY hY0
  rw [mul_zero, add_zero, mul_comm (Λ * bstar + L) (T ^ 2), mul_div_assoc] at hcert
  -- the mass comparison
  have hmass := mass_left (f := fun q => b (q * T / n)) (δ := 0) hT hn hbL
    (fun q _ => by simp) (x 0)
  rw [mul_zero, add_zero, mul_comm L (T ^ 2), mul_div_assoc] at hmass
  have hLC : T ^ 2 * L / (2 * n) ≤ T ^ 2 * (Λ * bstar + L) / (2 * n) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg T)
  have hmL : T ^ 2 * L / (2 * n) ≤ ν * contMass (x 0) b T := hLC.trans hsuff
  rw [← mul_div_assoc] at hcert hmass
  obtain ⟨h1, h2, h3, h4⟩ := mass_bounds hB hν1 (hmass.trans hmL)
  exact ⟨hcert.trans hsuff, hmass, hmL, h1, h2, h3, h4⟩

end

end SparseHamiltonian.GateQuad
