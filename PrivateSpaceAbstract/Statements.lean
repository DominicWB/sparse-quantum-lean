import PrivateSpaceAbstract.Pad
import PrivateSpaceAbstract.Flag

/-!
# Lemma `hs:lem:abstract` for any private space: statement guide

Manuscript: Lemma `hs:lem:abstract`. `D₀` is a unitary on a finite-dimensional private space, `J`
a known isometry from the system into it, `R₀ = (I - D₀)⁻¹` with the interface
`hs:eq:interface` (`J† R₀ J = (I + i h)/2`, `J† R₀† R₀ J ⪯ (ν/2) I`, `‖R₀‖ ≤ Q`, `h = h†`,
`‖h‖ ≤ 1`, an integer `Q ≥ 1` (any real `Q ≥ 1` in Lean), `0 < ν ≤ Q`); `D₀`, `D₀†` and their
controls are available. Simulating `e^{-itαh}` to full-output error `0 < ε ≤ 1/2` uses
`O(W + Q log(1/ε))` calls, `W = α|t|ν`, and the time slots do not multiply the count.

All declarations are in the namespace `SparseHamiltonian.PrivateSpaceAbstract`.

* `abstract_simulation_finite`: the lemma for every finite-dimensional private space `K` and every
  finite-dimensional nonzero system `P`: there are `a` and an isometry `V : K → Anc a P`, fixed
  before the data, such that for all data the conclusions of `abstract_simulation_private` hold.
  `U_J` is chosen after the data in this statement; the proof takes it from `V J₀` alone
  (`exists_unitary_extension`). The statement does not bound `a`, and the gate and wire counts grow
  with it; for a register with `dim K ≤ 2^a dim P` combine `exists_isometry_of_finrank_le` with
  `abstract_simulation_private`.
* `abstract_simulation_private`: the lemma for a private space `K` with a given isometry
  `V : K → Anc a P` into `a` ancilla qubits and a finite-dimensional system `P`: for the padded
  unitary `padUnitary V D₀ = V D₀ V† - (1 - V V†)` and the isometry `V J₀`, every conclusion of
  `GateRemarks.abstract_simulation_isometry` (and so of `GateRemarks.abstract_simulation`), with
  `6 d ≤ 3840 (W + Q log(1/ε))` calls of the padded unitary or its adjoint, each with at most one
  control.
* `exists_isometry_anc`: for finite-dimensional `K` and a finite-dimensional nonzero `P` there are
  `a` and an isometry `V : K → Anc a P`. The system must be nonzero: no isometry maps a nonzero `K`
  into a zero system.
* `exists_isometry_of_finrank_le`: the isometry exists for every `a` with `dim K ≤ 2^a dim P`;
  `finrank_anc`: `dim (Anc a P) = 2^a dim P`.
* `padUnitary_eq`, `padUnitary_comp_isometry`, `padUnitary_apply_of_orth`, `padUnitary_adjoint`: the
  padded unitary acts as `D₀` on the range of `V` and as the phase `-1` on its orthogonal complement.
  The theorems count calls of the padded unitary and its adjoint; `Flag` reduces each of them to one
  call of `D₀` or `D₀†` under the range flag (below). The gate and wire counts do not include the
  known reflection or the flag.
* `padUnitary_unitary`, `padResolvent_right`, `padResolvent_left`, `norm_padResolvent_le`
  (`‖R‖ ≤ max Q (1/2)`), `pad_boundary`, `pad_moment`, `pad_isometry`: the interface of the padded
  data from that of `(J₀, D₀, R₀)`.

**The padded call from the supplied unitary** (`Flag`).

* `flagCall V D₀ = V D₀ V† + (1 - V V†)` is `D₀` under the range flag of `V` (`D₀` on the range,
  the identity on the complement: `flagCall_comp_isometry`, `flagCall_apply_of_orth`), unitary for
  unitary `D₀` (`flagCall_unitary`), with `(flagCall V D₀)† = flagCall V D₀†` (`flagCall_adjoint`);
  `rangeRefl V = V V† - (1 - V V†)` is the known reflection about the range of `V`, a self-adjoint
  unitary involution independent of the data (`rangeRefl_adjoint`, `rangeRefl_mul_self`,
  `rangeRefl_unitary`), commuting with the flagged call (`flagCall_comm_rangeRefl`).
* `padUnitary_eq_flagCall`, `padUnitary_adjoint_eq_flagCall`: `padUnitary V D₀ = flagCall V D₀ ∘
  rangeRefl V` and `(padUnitary V D₀)† = flagCall V D₀† ∘ rangeRefl V`.
* `oracleOp_padUnitary`, `oracleOp_padUnitary_adjoint` (with `oracleOp_comp`): under any list of
  literal controls on the wires of a circuit, a call of the padded unitary or of its adjoint is the
  call of `flagCall V D₀` or `flagCall V D₀†` under the same controls after the controlled known
  reflection. So every padded call counted above is one call of `D₀` or `D₀†` under its control
  and the range flag, plus the known reflection, which makes no call. This is an operator identity
  for the abstract query theorem: no cheap elementary implementation of an arbitrary `V` (or of
  `rangeRefl V`) is claimed.

**The zero system** (`Flag`). No isometry maps a nonzero private space into the register of a zero
system. For a zero system every circuit is exact for every semantics, input embedding and target
(`run_subsingleton_exact`, `eq_of_subsingleton`); `abstract_simulation_zero`: the empty circuit, with
no private or `U_J` call and no gate, has full-output error zero against `exp(-it (α h))`.
-/
