import OptimalPrecision.Weights.Theorem
import OptimalPrecision.Tail.Lemma

set_option autoImplicit false

/-!
# Theorem `opt:thm:weights` and Lemma `opt:lem:tail`: paper-to-Lean entry point

Appendix A of the manuscript (`opt:sec:proof`, "Optimal precision for time-independent Hamiltonian
simulation") proves Theorem `hs:thm:optimal` through a finite signed average of chronological reuse
circuits (Theorem `opt:thm:signed`). Its analytic core is an explicit finite moment construction
(Theorem `opt:thm:weights`) and an operator tail estimate (Lemma `opt:lem:tail`). This library
proves both. Theorem `opt:thm:signed` (the finite implementation of Sections `opt:sec:factor` and
`opt:sec:tail`), the native and large-sparsity factors (`opt:sec:native`, `opt:sec:core`) and
Theorem `hs:thm:optimal` itself are not part of this library.

No result from another paper is used. The released libraries are unchanged; the contraction
`SparseHamiltonian.ODEDissipative.exp_norm_le_one` is reused from them. References to the manuscript
use its labels. Every theorem of the library is axiom-audited in
`OptimalPrecision/Audit.lean`.

**Naming convention.** All declarations are in the namespace `OptimalPrecision`, with the
sub-namespaces `ExpPoly` (exponential polynomials and Laguerre functions), `Gamma` (the gamma
mixtures), `Resolvent` and `Dual` (the extraction rule) and `Tail` (Lemma `opt:lem:tail`);
names below are relative to `OptimalPrecision`.

**Conventions.** `coeff f k = f^{(k)}(0)/k!` is the `k`-th Taylor coefficient at the origin
of `f : ℂ → E`, and `ces f j = ∑_{k<j} (1 - k/j) coeff f k` is the uniform clock functional
`Ces_j` of `opt:eq:cesaro` (module `Taylor.Basic`). `xi w = (1 - w)/(1 + w)` and
`Rfun q w = (1 - ξ(w)²)/(1 + q² ξ(w)²)` are `ξ` and `R` of `opt:eq:xi-R`, and
`vt t w = e^{-t ξ(w)}` is the scalar transfer (`V = vt a` with `a = qM`).

**Theorem `opt:thm:weights`** (module `Weights.Theorem`).

* `exists_clock_weights`: for every real `q ≥ 1` and integer `M ≥ 1` there are `n` and real
  weights `λ` with `n ≤ 27 qM`, `∑_{j=1}^n |λ_j| ≤ 3000` and, for `0 ≤ m ≤ k < M`,
  `∑_{j=1}^n λ_j Ces_j(e^{-qMξ} R^k ξ^m) = δ_{m0}` (`opt:eq:clock-size`,
  `opt:eq:clock-moments`).
* The weights are explicit: `clockLength q M = D_* + 1` and
  `clockWeight q M = lamOf (D_* + 1) (beta q M)`, `λ_{k+1} = ((k+1)/2)(-1)^k β_k`
  (`opt:eq:weights`), with `beta q M` the real Laguerre coordinates of `ψ` (`beta_spec`);
  `clockLength_le`, `sum_abs_clockWeight_le` and `clock_moments` are the three conclusions.

The construction is the paper's. `Gamma.alpha`, `Gamma.theta`, `Gamma.m0`, `Gamma.d0`,
`Gamma.ell`, `Gamma.Apoly`, `Gamma.Bpoly`, `Gamma.C1`, `Gamma.C2` and `Gamma.Dstar` are `α`,
`θ`, `m₀`, `d₀`, `ℓ`, `A`, `B_ℓ`, `C₁`, `C₂` and `D_*`. `Dual.diffR q M` is
`(C₂ - C₁)/ℓ`, and the polynomial part `PR q M` of the extraction function `φ = e^{-t} P(t)`
(`opt:eq:phi`) is recorded through its Taylor data at the delay `a = qM`
(`ExpPoly.shifted`). `QR q M = 4 (1 + x)^{-1} P` is the polynomial part of `ψ`
(`opt:eq:psi`), where `x = 1 - D` is `-∂` on exponential polynomials and power series in the
derivative act on polynomials through `ExpPoly.op` (module `Weights.Operator`).

*Exact moments* (modules `Weights.Laguerre` to `Weights.Exact`). The proof replaces the
distributional pairing of the paper by an algebraic one; no inverse Laplace transform is used.

* `ExpPoly.lag k = L_k(2X)` with the recurrence, the derivative identities and the Laguerre
  equation (`ExpPoly.lag_recurrence`, `ExpPoly.derivative_lag`, `ExpPoly.lag_ode`);
  `lagGenCoeff_eq` is the generating function `opt:eq:laguerre-gf`
  (`[w^l] e^{-tξ}/(1+w) = (-1)^l ℓ_l(t)`), from the first-order equation
  `(1+w)² f' = (2t - 1 - w) f`; `coeff_vt` gives the coefficients of `e^{-tξ}`;
  `ExpPoly.exists_lag_expansion` is the finite Laguerre expansion.
* `lamSum_vt_mul`: the signed clock of `e^{-tξ} g` is `e^{-t} prof(g)(t)`; `prof_xi_mul`,
  `prof_aeval_mul`: multiplication by `ξ` acts as `x = -∂`; `ExpPoly.cesPoly_signed`,
  `ExpPoly.op_ramp_lag` and `prof_one_eq`: the profile of `1` is `x^{-2} P`.
* `Dual.pair` is the extraction rule `L(s) = ∑_i s_i d_i` on power series in `x`;
  `Dual.hyp_mixture` verifies `L(x^{-2}) = 1`, `L(x^{-1}) = 0` (`opt:eq:gamma-means`),
  `L(x^j) = 0` below `d₀`, and `L((x ∓ i/q)^{-b}) = 0` for `1 ≤ b ≤ M` (`opt:eq:oscillators`,
  from the zeros of `C₁`, `C₂` at `α`, `ᾱ`); `Resolvent.value_neg_two`,
  `Resolvent.vanish_neg_one` and `Resolvent.vanish_nonneg` are the partial-fraction
  identities behind `opt:eq:dual-pairing`.
* `lamSum_moment`: `∑_j λ_j Ces_j(V R^k ξ^m) = δ_{m0}` for `m ≤ k < M`.

*Variation bound* (modules `Weights.LaguerreL2` to `Weights.Theorem`).

* `ExpPoly.J` is `∫_0^∞ e^{-2t} π(t) dt` on polynomial parts
  (`ExpPoly.integral_eval_mul_exp_neg_two` identifies it with the Lebesgue integral);
  `ExpPoly.J_lag_mul_lag` is the orthogonality `∫ ℓ_j ℓ_k = δ_{jk}/2` and `ExpPoly.Lop_lag`
  the eigenrelation `𝔏 ℓ_k = (2k+1) ℓ_k` of `opt:eq:laguerre-identities`, with the symmetry
  of `𝔏` (`ExpPoly.J_Lop_mul`, `ExpPoly.J_Lop_mul_comm`) proved by integration by parts in
  `J` (`ExpPoly.J_derivative`).
* `ExpPoly.sum_abs_le`: if `ψ = ∑_k β_k ℓ_k` and `(𝔏 + 1) ψ = 4χ`, then
  `∑_k ((k+1)/2)|β_k| ≤ √(N+1) √(2 ∫ χ²)` (Parseval and Cauchy–Schwarz); `Lop_add_self_op`:
  `(𝔏 + 1) ψ = 4(tφ + tφ' + φ)`.
* `ExpPoly.J_chi_le`, `J_chi_mixture_le`: `∫_0^∞ (tφ + tφ' + φ)² ≤ 6512/a`, from the Poisson
  probabilities on `t > a` (`ExpPoly.Phi_sq_le`, `ExpPoly.integral_sq_mul_pk`) and the Poisson
  tail bound `e^a ∑_{k₀ ≤ j ≤ D} a^j/j! ≤ 1` for `a ≥ 1` and `k₀ ≥ 11a`, used below the delay
  (`ExpPoly.tail_le_one`). The proof of `sum_abs_clockWeight_le` obtains a total variation of
  at most `√(27 · 13024) < 600`; the statement keeps the paper's `3000`.
* `Gamma.Dstar_add_one_le`: `n = D_* + 1 ≤ 27a` (`opt:eq:degree27`).

**Lemma `opt:lem:tail`** (module `Tail.Lemma`).

* `Tail.tail_estimate`: let `λ_1, …, λ_n` satisfy the three conclusions of Theorem
  `opt:thm:weights` (`n ≤ 27 qM`, `∑ |λ_j| ≤ 3000`, exact moments below degree `M`). Let `C`,
  `D` be bounded operators on a complex Hilbert space with `0 ⪯ D ⪯ δI` and `-D ⪯ C ⪯ D`
  (Loewner order), `δ ≥ 0`, and `M ≥ 2 · 27² b` with `b = q²Mδ`. Then
  `‖∑_j λ_j Ces_j(F) - e^{-iq²M C}‖ ≤ 2 · 3001 · (e² · 27² b / M)^M`
  (`opt:eq:factorial-tail`, with `A_* = 3000`, `K_* = 27`, `T = aq = q²M`).
* `Tail.Fop a q C D w = e^{-aΩ(w)}` is the transfer `F` of `opt:eq:continuum`, with
  `Tail.Omega q C D w = ξ(w) I + R(w)(iqC + q²ξ(w)D)` (`opt:eq:omega`).

The steps of the proof: `Tail.Omega_eq` writes `Ω` as `ξ (I - D) + (μ₊/2)(D + C) +
(μ₋/2)(D - C)` with `Re ξ, Re μ_± ≥ 0`, so `Ω` is accretive (`Tail.re_inner_Omega_nonneg`) and
`‖F(w)‖ ≤ 1` on the disk (`Tail.norm_Fop_le_one`); `norm_ces_le` is the Fejér contraction
`‖Ces_j(F)‖ ≤ sup ‖F‖` (`opt:eq:fejer-radius`, `opt:eq:interval-bound`), proved with the Fejér
kernel sampled at roots of unity; `Tail.ces_Fop` expands the clocks of `F` in ordered words
`Tail.word` without commuting `C` and `D` (`Tail.Xop_pow`); `Tail.clock_smul` writes the clock
along the scaling `x ↦ (xC/δ, xD/δ)` as a polynomial and `Tail.clockCoeff_eq` gives its
matching jets `(-iTC₀)^m/m!` for `m < M` (`opt:eq:matching-jets`); `norm_polyEval_le` is the
Joukowski bound `‖P(z)‖ ≤ A exp(2(n-1)√|z|)` (`opt:eq:joukowski`), by the maximum principle for
`v^{n-1} P((2 + v + 1/v)/4)`; `norm_tail_le` is the Cauchy estimate on `|z| = (M/n)²`; and
`norm_exp_sub_sum_le'` is the exponential tail.

**Scope.** Lemma `opt:lem:tail` is stated for every family of weights with the three
conclusions of Theorem `opt:thm:weights`, in particular for `clockWeight q M`. It is proved
for every `δ ≥ 0`: `Tail.tail_estimate_of_pos` is the case `δ > 0`, by the paper's proof with
`C = δC₀` and `D = δD₀`; for `δ = 0` the hypotheses force `C = D = 0`, and the moment
`k = m = 0` makes the clock exact. The finite implementation of the transfer, the mesh, the
signed linear combination of circuits and the amplification of Theorem `opt:thm:signed` are
not formalised here.
-/
