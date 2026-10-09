import GateEfficientQuadrature.Native
import GateEfficientQuadrature.Sharp
import GateEfficientQuadrature.NonVacuity

/-!
# The sufficient source quadrature of Theorem `ode:thm:gates`: paper-to-Lean entry point

Theorem `ode:thm:gates` of the accompanying paper (gate-efficient dissipative equations,
manuscript line 4726) assumes, for time-dependent forcing, a positive source quadrature with
nodes `v_i`, weights `w_i ≥ 0` and the normalisation `B_m = ‖x₀‖ + ∑_i w_i ‖b(v_i)‖`, and the
certificates `ode:eq:gate-source-certificates` (line 4707)

`‖x(T) - U(T, 0) x₀ - ∑_i w_i U(T, v_i) b(v_i)‖ ≤ ν B`, `0 < B_m ≤ 2B`,

for `B = ‖x₀‖ + ∫_0^T ‖b(v)‖ dv` and the propagator `U` of the dissipative equation. Its proof
then specifies a sufficient positive quadrature (lines 4857-4874): if `‖b(v)‖ ≤ b_*` and
`Lip(b) ≤ L_b`, put `Λ_A = √s (η_D + η_H)` and `C_b = Λ_A b_* + L_b`; "contractivity gives
Lipschitz constant at most `C_b` for `v ↦ U(T, v) b(v)`"; "a power-of-two left-endpoint mesh with
`m ≥ max{1, T² C_b / (2 ν B)}` has vector quadrature error at most `ν B`"; and
`|B_m - B| ≤ T² L_b / (2m) ≤ ν B`, `(1 - ν) B ≤ B_m ≤ (1 + ν) B`, hence `B_m > 0` and
`B_m ≤ 2B`, "including when `x₀ = 0`". This library formalises these statements, without the
propagator as a Lean object (see *Formalisation choices*). It supplies the source certificate of
the solver on the branch-dependent meshes of Lemma `ode:lem:gate-select` (`GateEfficientSelect`),
where the certificate is a hypothesis, and derives the budget fields of that solver from the
paper's choice of parameters.

No result from another paper is used. The released libraries are unchanged. Manuscript lines
refer to `sparse_quantum_algorithms.tex` (v20); the labels are the stable references. Every
theorem of the library is axiom-audited in `GateEfficientQuadrature/Audit.lean`.

**Naming convention.** All declarations of this library are in the namespace
`SparseHamiltonian.GateQuad` and are named relative to it below. Released declarations are named
relative to `SparseHamiltonian` (for example `TimeDependentODE.SolvesODE`,
`GateSelect.ODE.BInstanceOK`, `GateODE.Time.TParams`).

**Notation.** The paper's number `m` of quadrature nodes is `n` here; `m` is the slot exponent
of the released protocol, with `M = 2^m` slots, `m` source bits and `2^m` forcing labels
`(true, q)` (`GateODE.Time.TParams`). The equation is `x' = -G(u) x + b(u)`
(`TimeDependentODE.SolvesODE`, `G = -A` accretive). `Λ` bounds `‖G(u)‖` on `[0, T]` (the paper's
`Λ_A`); `L` is the Lipschitz constant of the forcing (the paper's `L_b`; the operators `Lb` of
`LInstanceOK` are the represented dissipative branch samples, as `Hb` are the Hamiltonian ones);
the real number `bs` (`b_s` below) bounds the forcing samples `f_q` (`b_*` for exact samples; it
is unrelated to the released sample family `bs : ℕ → P` and to `GateSelect.ODE.bsW`); `δb`
(`δ` below) bounds their errors. `contMass x₀ b T` is the paper's `B`, and
`quadMass x₀ f T n = ‖x₀‖ + ∑_{q < n} (T / n) ‖f_q‖` is written `B_n` (the paper's `B_m`). A
solution `y` of the homogeneous equation `y' = -G(u) y` on `[v, T]` with `y(v) = z` stands for
`U(·, v) z`: for an accretive generator it is unique (`homog_eq_zero`) and, for a Lipschitz
generator, it exists
(`GateSelect.ODE.exists_branch_solution`), so the certificates below, stated for every such
family, are the certificates for `U`.

**What was already released (cited, not redone).**

* `GateSelect.ODE.solverB`, `GateSelect.ODE.native_ode_time_solverB`: the time-dependent part
  of Theorem `ode:thm:gates` on branch-dependent meshes, with the source certificate as a
  hypothesis (the field `quad` of `GateSelect.ODE.BInstanceOK`), and
  `GateSelect.ODE.quad_leftEndpoint`, a cruder certificate for the left-endpoint quadrature with
  one node per slot, which pays the generator discretisation twice.
* The released time-dependent solvers `GateODE.Time.solver` and its variants use the
  left-endpoint quadrature on the common mesh inside their own certified error
  (`GateODE.Time.TParams.discretisation`); the constant-coefficient solver uses `2^k`
  left-endpoint nodes with `T (λH + λD) ≤ p.nu 2^k < 2 p.nu (⌈T (λH + λD) / p.nu⌉ + 1)`, for its
  precision unit `p.nu` (`GateEfficientODE`).
* `TimeDependentODE.SolvesODE.norm_le`: the energy bound on `[0, T]` for a constant bound of the
  forcing.

**The certificate** (modules `Energy`, `Certificate`).

* `energy_affine`: for `a ≤ c`, a solution of `x' = -G(u) x + F(u)` on `[a, c]` with accretive
  `G(u)` and `‖F(u)‖ ≤ A (c - u) + L (u - a) + δ` with `A, L, δ ≥ 0`,
  `‖x(c)‖ ≤ ‖x(a)‖ + (A + L)(c - a)² / 2 + δ (c - a)`; with `F = 0`, contractivity
  (`homog_norm_le`, `homog_eq_zero`).
* `flow_lipschitz` (the Lipschitz bound of `v ↦ U(T, v) b(v)`): for an accretive generator with
  `‖G(u)‖ ≤ Λ`, a forcing with `‖b(u)‖ ≤ b_*` and `Lip(b) ≤ L` on `[0, T]`, `0 ≤ v ≤ v' ≤ T` and
  homogeneous solutions `Y` from `v`, `Y'` from `v'` with `Y(v) = b(v)`, `Y'(v') = b(v')`,
  `‖Y(T) - Y'(T)‖ ≤ (Λ b_* + L)(v' - v)`.
* `step_left`: one interval; `cert_left`: for `T ≥ 0`, `n ≥ 1`, a solution `x` of
  `x' = -G(u) x + b(u)` on `[0, T]`, an accretive generator with `‖G(u)‖ ≤ Λ`, `Lip(b) ≤ L` with
  `L ≥ 0`, samples `f_q` (`q < n`) with `‖f_q‖ ≤ b_s` and `‖b(q T / n) - f_q‖ ≤ δ`, a homogeneous
  `y_0` from `0` with `y_0(0) = x(0)` and homogeneous `Y_q` from `q T / n` with
  `Y_q(q T / n) = (T / n) f_q`:
  `‖x(T) - y_0(T) - ∑_{q < n} Y_q(T)‖ ≤ (Λ b_s + L) T² / (2n) + T δ`.

**The normalisation** (module `Mass`).

* `mass_left`: for `Lip(b) ≤ L` and samples with `‖b(q T / n) - f_q‖ ≤ δ`,
  `|B_n - B| ≤ L T² / (2n) + T δ`, where `B_n = quadMass x₀ f T n` and `B = contMass x₀ b T`.
* `mass_bounds`: `|B_n - B| ≤ ν B` with `B > 0`, `ν < 1` gives `(1 - ν) B ≤ B_n ≤ (1 + ν) B`,
  `0 < B_n` and `B_n ≤ 2B`.
* `nodes_sufficient`: `n ≥ T² C / (2 ν B)` with `ν B > 0` gives `T² C / (2n) ≤ ν B`;
  `exists_pow_two_nodes`: for every real `X` a power of two `2^k` with
  `max 1 X ≤ 2^k < 2 (⌈X⌉₊ + 1)` exists (`⌈X⌉₊` the natural ceiling; the paper's power-of-two
  mesh, with a logarithmic label register).

**The paper's statement** (`paper_quadrature`, module `Paper`). For a solution `x` on `[0, T]`, an
accretive generator with `‖G(u)‖ ≤ Λ`, a forcing with `‖b(u)‖ ≤ b_*` and `Lip(b) ≤ L` (`L ≥ 0`),
`B = contMass x(0) b T > 0`, `0 < ν < 1`, `n ≥ 1` nodes with `n ≥ T² (Λ b_* + L) / (2 ν B)`, the
exact samples `b(q T / n)` and homogeneous solutions as in `cert_left`: the certificate is at most
`ν B`; `|B_n - B| ≤ T² L / (2n) ≤ ν B`; `(1 - ν) B ≤ B_n ≤ (1 + ν) B`; `0 < B_n`; `B_n ≤ 2B`.

**The solver** (modules `Solver`, `Native`).

* `vQ n`, `wQ n`: the nodes `q T / n` and weights `T / n` for `q < n`; the remaining forcing
  labels (of the `2^m`) are padding with the node `T` and the weight `0` (`1 ≤ n ≤ 2^m`);
  `mass_wQ`: the released source mass is `B_n = quadMass x(0) f T n`.
* `quad_left`: every family of homogeneous branch solutions of `GateSelect.ODE.BInstanceOK`
  satisfies the source certificate `(Λ b_s + L) T² / (2n) + T δ` (`cert_left` after
  `sum_labels`, `sum_words`; the labels with source vector `0` contribute `0`).
* `LInstanceOK`: the conditions of `GateSelect.ODE.BInstanceOK` for `vQ n`, `wQ n` with the
  certificate replaced by `‖G(u)‖ ≤ Λ`, `Lip(b) ≤ L`, `‖f_q‖ ≤ b_s`, `‖b(q T / n) - f_q‖ ≤ δ`,
  the budget `B_n ≤ g ‖x(T)‖` and
  `(Λ b_s + L) T² / (2n) + T δ + T (βG T / 2^m + δG) B_n ≤ ε B_n / (2000 g)`;
  `LInstanceOK.toB` gives `BInstanceOK` with that certificate.
* `solverL` (exact gates): the protocol, validity, worst-case counts, register and degree bounds
  of `GateSelect.ODE.solverB` (the released `GateODE.Time.solver`), and the released `Outcome`
  for every instance satisfying `LInstanceOK` (`outcomeL`): success probability at least
  `175/256 > 2/3`, every successful trial within `ε / 500` of `x(T)/‖x(T)‖` up to a global phase
  and a conditional output within trace distance `ε`. Natively, `native_time_outcomeL`: the
  released `GateNative.NOutcome` under the hypotheses of `GateSelect.ODE.native_time_outcomeB`
  (the released error budget `24 d ζ + 3 ζs ≤ p.nu`) with `LInstanceOK` for the ideal oracles;
  the native counts are those of `GateSelect.ODE.native_ode_time_solverB`.
* The budget fields from the paper's parameters: `budget_of_paper` (`B_n ≤ 2B` and
  `B ≤ ḡ ‖x(T)‖` give `B_n ≤ g ‖x(T)‖` for `g = 2ḡ`), `disc_of_paper` (a certificate bound
  `κ ≤ ν B` with `|B_n - B| ≤ ν B`, `0 ≤ ν ≤ 1/2`, and `T (βG T / 2^m + δG) ≤ ν'` give the budget
  field if `2ν + ν' ≤ ε / (2000 g)`), `nu_paper` (the paper's `ν = ε / (10⁴ ḡ)` with `g = 2ḡ`
  and `ν' = ε / (10⁴ g)` give `2ν + ν' = ε / (2000 g)`), and their combination
  `budget_disc_paper`: for the exact samples, `‖b(u)‖ ≤ b_*`, `Lip(b) ≤ L`, `Λ ≥ 0`, the public
  `g = 2ḡ`, `0 < B ≤ ḡ ‖x(T)‖`, the paper's `ν = ε / (10⁴ ḡ)`, `n ≥ 1` nodes with
  `n ≥ T² (Λ b_* + L) / (2 ν B)` and `T (βG T / 2^m + δG) ≤ ε / (10⁴ g)`, the fields `budget`
  and `disc` of `LInstanceOK` hold.

**Sharpness** (module `Sharp`). For the zero generator, the ramp `b(t) = t w`
(`ramp_lipschitz`: Lipschitz constant `‖w‖`), its solution `rampSol` (`rampSol_solves`), the
exact samples and the constant homogeneous solutions (`const_homog`), the hypotheses of
`cert_left` and `mass_left` hold with `Λ = 0`, `L = ‖w‖`, `δ = 0`, and both bounds are attained:
`sharp_cert` (the certificate error is `‖w‖ T² / (2n)`) and `sharp_mass`
(`|B_n - B| = ‖w‖ T² / (2n)`). So `T² L_b / (2m)` cannot be improved, nor `T² C_b / (2m)` for a
zero generator; the sharpness of the coefficient of `Λ b_*` is not addressed.

**Non-vacuity** (module `NonVacuity`). `nvL_instance`: every condition of `LInstanceOK` holds at
once for `x' = 1 + t / 4000` on `[0, 1]` with `x(0) = 0`, the left-endpoint quadrature with
`n = 2` nodes `0` and `1/2` (the forcing branch of `1/2` has the address `3/4`, which is not a
point of the common mesh), the samples `f_0 = f_1 = 1 + 1/16000` with `δ = 1/16000`,
`L = 1/4000`, the public data `GateSelect.ODE.nvP` (`m = 1`) and the supplied unitaries `nvσ2`
(`U_J = 1`, the private operation `-1`, the loading `1` and the weight preparation `X ⊗ H`,
`nvWp2_mul_self`, `nvWp2_conjTranspose`); the certificate bound is `κ = 1/8000` (`nvL_kappa`),
the certificate error is `1/16000` (`nvL_error`), and `nvL_outcome`: `outcomeL` applies to them.
The generator of the witness is zero, so `Λ = βG = δG = 0` there and its branch samples and clock
promises hold trivially, and `x(0) = 0` makes the initial loading condition vacuous; with
`n = 2^m = 2` it has no padding label. `nvL1_instance`, `nvL1_outcome` and `nvL1_error` give a
second witness with one node `0`, the exact sample `b(0) = 1` and the second forcing label as
padding of weight `0` at the node `1` (weight preparation `GateSelect.ODE.nvWp`), whose
certificate error equals its bound `κ = 1/8000`.

**Proof map** (module paths relative to `GateEfficientQuadrature/`).

* `Energy`: `affInt_hasDerivAt`, `affInt_left`, `affInt_right`, `affInt_nonneg`, `energy_affine`
  (comparison of `‖x‖²` with the square of `‖x(a)‖ + ∫ (bound) + ε (u - a) + ε` by Mathlib's
  `image_le_of_deriv_right_lt_deriv_boundary'`, as the released
  `TimeDependentODE.SolvesODE.norm_le`), `homog_norm_le`, `homog_eq_zero`, `solves_add_path`,
  `solves_sub_homog`, `homog_add`, `homog_sum`.
* `Certificate`: `flow_lipschitz` (`energy_affine` for `Y - b(v)` on `[v, v']`, contractivity
  of `Y - Y'` on `[v', T]`), `step_left` (`energy_affine` for `E + (a + h - t) f`, whose forcing
  is `b(t) - f + (a + h - t) G(t) f`), `cert_left` (induction over the nodes: the difference of
  `x` and the homogeneous solutions started so far solves the forced equation).
* `Mass`: `integral_affine`, `mass_left` (`intervalIntegral.sum_integral_adjacent_intervals`
  and `intervalIntegral.norm_integral_le_of_norm_le` on every node interval), `mass_bounds`,
  `nodes_sufficient`, `exists_pow_two_nodes` (`Nat.clog`).
* `Paper`: `paper_quadrature` (`cert_left`, `mass_left`, `nodes_sufficient`, `mass_bounds`).
* `Solver`: `vQ_mem`, `wQ_nonneg`, `mass_wQ` (`GateSelect.ODE.mass_bsW`), `wordValue_wordOf`,
  `sum_labels`, `sum_words`, `quad_left`, `LInstanceOK.toB`, `outcomeL`
  (`GateSelect.ODE.outcomeB`), `solverL` (`GateSelect.ODE.solverB`), `budget_of_paper`,
  `disc_of_paper`, `nu_paper`, `budget_disc_paper` (`nodes_sufficient`, `mass_left`,
  `mass_bounds`).
* `Native`: `native_time_outcomeL` (`GateSelect.ODE.native_time_outcomeB`).
* `Sharp`: `sum_range_cast`, `rampSol_solves`, `ramp_lipschitz`, `const_homog`, `sharp_cert`,
  `sharp_mass`.
* `NonVacuity`: `cfg2_eq`, `inv_sqrt_two_sq`, `nvWp2_mul_self`, `nvWp2_conjTranspose`,
  `nvL_quadMass`, `nvL_mass`, `nvL_zsrc`, `nvL_instance`, `nvL_outcome`, `nvL_error`,
  `nvL_kappa`, `nvL1_quadMass`, `nvL1_mass`, `nvL1_zsrc`, `nvL1_instance`, `nvL1_outcome`,
  `nvL1_error`.

**Formalisation choices.**

* The propagator `U(T, v)` of the dissipative equation is not a Lean object here; `U(T, v) z` is
  written as the value at `T` of the solution of `y' = -G(u) y` on `[v, T]` with `y(v) = z`, as in
  `GateSelect.ODE.BInstanceOK`. The paper derives the certificate from the Lipschitz bound of
  `v ↦ U(T, v) b(v)` and the Duhamel formula; here the certificate is proved directly by a
  telescoping energy estimate with the same constant `C_b = Λ b_* + L` (`cert_left`), and the
  Lipschitz bound is stated separately in solution form (`flow_lipschitz`).
* Every number `n ≥ 1` of nodes is allowed (the paper takes a power of two, which
  `exists_pow_two_nodes` provides); in the solver `n ≤ 2^m` because the source register of the
  released protocol has `m` bits, and the remaining forcing labels are padding of weight `0` at
  the node `T`. A quadrature with more nodes needs a larger `m`, which keeps the mesh conditions.
* The certificate also allows represented forcing samples with errors `δ` (`cert_left`,
  `mass_left`, `LInstanceOK`); the paper's statement is the case `δ = 0`
  (`paper_quadrature`, `budget_disc_paper`). `Λ` is a hypothesis, any bound of `‖G(u)‖` on
  `[0, T]` (it is not derived from the branch samples); the paper's `Λ_A = √s (η_D + η_H)` is one
  for its sparse inputs.
* The budget fields keep the released form with the quadrature mass `B_n` (as in
  `GateSelect.ODE.BInstanceOK`); `budget_disc_paper` derives them from the paper's
  `B ≤ ḡ ‖x(T)‖`, `ν = ε / (10⁴ ḡ)` and number of nodes, for a branch discretisation
  `T (βG T / 2^m + δG) ≤ ε / (10⁴ g)`.

**Not formalised.**

* The propagator `U(T, v)` and the Duhamel formula `x(T) = U(T, 0) x₀ + ∫_0^T U(T, v) b(v) dv`,
  hence the vector quadrature error in its integral form (its consequence, the certificate, is
  proved).
* Source certificates for quadratures other than the left-endpoint one, which stay a hypothesis
  of the theorem as in the paper ("the theorem also allows other efficiently addressable
  positive quadratures satisfying the certificates").
* The binary-data and finite-gate-set solvers on branch-dependent meshes and the arithmetic of
  Lemma `ode:lem:gate-select` (see the guide of `GateEfficientSelect`).

**Provenance.** New library, written against the released package: it imports
`GateEfficientSelect` and `TimeDependentODE` (with their dependencies) and changes none of them.
The statement guide of `GateEfficientSelect` lists the source certificate for quadratures other
than the left-endpoint one and the comparison `B_m ≤ 2B` as not formalised, and its
`ODE.quad_leftEndpoint` is cruder than the paper's bound; the paper's sufficient left-endpoint
quadrature with its constants `T² C_b / (2m)` and `T² L_b / (2m)`, and `0 < B_m ≤ 2B`, are
formalised here.
-/
