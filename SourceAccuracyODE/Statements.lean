import SourceAccuracyODE.Outcome
import SourceAccuracyODE.Constant
import SourceAccuracyODE.Time

/-!
# Source circuits within `ν`: statement guide

Theorem `ode:thm:gates` charges the source circuits by `G_src(ν)`, where `G_src(ζ)` counts the gates
of `P_w`, the loading and `P_w†` "with their combined implementation error at most `ζ`" (the
paragraph before the theorem), `ν = ε/(10⁴ ḡ)`; for constant forcing
`G_src(ν) = G_{x₀}(cν) + G_b(cν) + …` (eq. `ode:eq:gate-constant-source`). Its proof absorbs the
source error into the vector error `9 ν B_m + ν B ≤ 19 ν B` and concludes that every successful
trial is within `ε` of the normalised solution (eq. `ode:eq:gate-vector-error`). The released native
gate solvers fix the per-trial bound at `ε / 500` (`GateNative.NOutcome`) and therefore ask each
source circuit to be within `ν/4` (constant coefficients) or `ν/24` (time-dependent, at the internal
precision `ν' = ν/4`). This library certifies the same protocols for source circuits within `ν`
each, which the manuscript's combined error `ν` implies.

## The method (`Outcome`)

* `WOutcome prepN g β`: the released guarantees of the native four-attempt protocol with the
  per-trial direction bound and the conditional trace distance at most `β`;
* `woutcome_of_bounds`: the released mean-success and per-trial bounds give `WOutcome … β`;
* `trial_bounds_of_rel`, `native_trial_bounds_rel`, `woutcome_of_vec`: a scaled decoded vector
  `c d` within `ρ ‖y‖` of an intermediate target `y`, `ρ ≤ 1/4`, `0 < c ≤ 3 g ‖y‖`, whose direction
  is within `η` of that of `x`, gives `WOutcome … (2ρ + η)` against `x` (the released amplification
  theorem for every amplitude at least `1/(4g)`);
* `native_vector_error_le`: a native preparation within `δ` of the lifted released preparation has
  vector error `3 B δ + 6 ν B`.

## Endpoints

* constant coefficients (`Constant`): `native_ode_outcome` (`24 d ζ + 2 ζ_s ≤ 4 ν`),
  `native_zero_outcome` (direct source assembly, `2 ζ_s ≤ 4 ν`), `binary_ode_outcome` (binary
  data, `T > 0`, `24 d ζ + 2 ζ_s ≤ 4 ν`), `binary_ode_outcome_nonneg` (binary data, every `T ≥ 0`,
  `98304 q* ζ + 2 ζ_s ≤ 4 ν`, `q* = qOf s T η_H η_D ḡ ε`): the released protocols with
  `WOutcome … (ε / 250)`;
* time-dependent coefficients (`Time`), represented samples of any sign:
  `native_time_outcome` (`24 d ζ + 3 ζ_s ≤ 13 ν'`), `native_time_zero_outcome`
  (`3 ζ_s ≤ 13 ν'`), `binary_time_outcome` (binary data, `T > 0`, `24 d ζ + 3 ζ_s ≤ 13 ν'`),
  `binary_time_outcome_nonneg` (binary data, every `T ≥ 0`, `98304 q* ζ + 3 ζ_s ≤ 13 ν'`, the
  internal `q* = qOf s T η_H η_D (2ḡ) (ε/2)`): the protocols of `RepresentedSampleODE.GateTime`
  with `WOutcome … (ε / 100)`.

With the released arithmetic accuracy (`98304 q* ζ ≤ ν/2`, resp. `ν'/2`) these budgets hold for
source circuits within `ν` (resp. `ν = 4 ν'`) each. The protocols, the gate, qubit and call counts
and the instance conditions are the released ones (`ManuscriptConformance.ode_thm_gates`,
`ManuscriptConformance.ode_thm_gates_time`).
-/
