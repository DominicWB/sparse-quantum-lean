import CleanWorkODE.Work
import CleanWorkODE.Registers
import CleanWorkODE.Oracles
import CleanWorkODE.Theorem

/-!
# Preparations on temporary work registers: statement guide

Theorem `ode:thm:time` with the general source interface lets the supplied preparations be finite
implementations: "the sum of their clean-input operator errors is chosen within the allocated
tolerance" (Section `ode:sec:time`, the paragraph after eq. `ode:eq:source-interface-preparation`).
Clean-input errors are those of the manuscript's temporary-work convention (eq.
`access:eq:full-output`): an implementation `A` with temporary work registers implements `U` within
`δ` if `‖A (ψ ⊗ |0⟩) - (U ψ) ⊗ |0⟩‖ ≤ δ ‖ψ‖` for every input `ψ`. The approximate-preparation
endpoints of `RepresentedSampleODE` and `GeneralSourceExtensions` ask the supplied `P_w` and
`U_load` to have no work registers and to be within `δ` of exact preparations in the full operator
norm. This library proves the endpoint for supplied preparations on a temporary work register, under
clean-input errors only.

## The method (`Work`)

* `CleanErr c A U δ`: the clean-input error for the embedding `c ψ = ψ ⊗ |0⟩`;
  `CleanErr.adjoint` (the adjoint of a unitary implementation has the same error) and
  `CleanErr.mul` (errors add along products of contractions);
* `WorkEmbedding`, `workRecast`, `eval_workRecast_clean`: a program over exact oracles, run with
  every fixed gate acting as the identity on the work register and every oracle call replaced by an
  implementation with the work register, has clean-input error at most the sum of the clean-input
  errors of its calls, inverse calls included;
* `perturbed_four_work`, `work_certificate`: four fresh trials of such a program, seeded and
  heralded on a clean work register, keep the guarantees of the released four-attempt protocol
  (`GeneralSourceExtensions.perturbed_four`, `GeneralSourceExtensions.approx_certificate`).

## The registers and oracles (`Registers`, `Oracles`)

* `cleanPi`, `liftPi`, `piWork`: the work register adjoined to the source register of the
  primitive workspace;
* `sourcePhysical_clean`: a supplied call enabled on the inactive matrix sector keeps the
  clean-input error of the operation on the source register;
* `liftAct_clean`: an operation on its registers and the work register keeps its clean-input error
  when the remaining registers are spectators (the manuscript's "tensoring that difference with an
  identity preserves its norm", the paragraph after eq. `access:eq:full-output`);
* `actualOracleW`, `actualOracleW_clean`: the actual oracles with a supplied `P_w` on the label and
  work registers (`LabelW`), a supplied `U_load` on the label, data and work registers (`LoadW`) and
  `P_w†` the adjoint of `P_w`; within `δ` of the exact oracles of
  `GeneralSourceExtensions.MeshOracles` on a clean work register when `P_w` and `U_load` are within
  `δ` of `P` and `∑_a |a⟩⟨a| ⊗ L(a)` (`ctrlL`);
* `CleanErr.liftPi_of_norm`, `norm_ctrlL_sub_le`: supplied operations without a work register
  within `δ` in operator norm (the hypotheses of the released endpoints), run with the work
  register as a spectator, are within `δ` on a clean work register of any size.

## Endpoints (`Theorem`)

* `work_approx_solver_nonneg` (`WorkApproxBudgetOutcome`):
  `RepresentedSampleODE.robust_approx_solver_nonneg` for preparations on a temporary work register;
* `work_approx_solver_nonneg_regular` (`WorkRegularOutcome`): the same for integrable generator
  pieces, mild solutions and the budgets of the true path, as
  `RepresentedSampleODE.robust_approx_solver_nonneg_regular`; it gives
  `ManuscriptConformance.ode_thm_time_approx`.

The public trial family is fixed before the instance; its circuits do not depend on the clean
state `w₀`, which enters only the seed and the herald. The matrix and source-call counts and the
budgets `30 g' δ ≤ 1/400`, `30 g' δ ≤ ε/20` (`g' = 2 c_q ḡ`) are those of the released endpoints.
By `CleanErr.liftPi_of_norm` and `norm_ctrlL_sub_le` the hypotheses of the released endpoints
give those here for every work register, and with `δ = 0` exact preparations meet them. The exact
loader is label-controlled (`ctrlL`), a hypothesis of this package; a
supplied loader close only to a label-mixing unitary completion of eq.
`ode:eq:source-interface-preparation` is not covered.
-/
