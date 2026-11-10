import GateEfficientRemarks.AbstractIsometry

/-!
# Lemma `hs:lem:abstract` for any private space

`GateRemarks.abstract_simulation` and `abstract_simulation_isometry` take the private unitary on
`a` ancilla qubits and the system, `Anc a P`. Lemma `hs:lem:abstract` allows any finite-dimensional
private space `K`. Embed `K` into `Anc a P` by an isometry `V` (`V† V = 1`) and pad:

* `padUnitary V D₀ = V D₀ V† - (1 - V V†)`, for an isometry `V`, is unitary (`padUnitary_unitary`),
  acts as `D₀` on the range of `V` and as the phase `-1` on its orthogonal complement
  (`padUnitary_comp_isometry`, `padUnitary_apply_of_orth`), and has adjoint `padUnitary V D₀†`
  (`padUnitary_adjoint`). The theorems below count calls of the padded unitary and its adjoint.
  With a flag for that range, a call under a control `c` is counted, outside these statements, as
  one call of `D₀` or `D₀†` under `c` and the flag, plus known gates; no declaration states this
  reduction, and the gate and wire counts below do not include those gates or the flag;
* `padResolvent V R₀ = V R₀ V† + (1 - V V†)/2` is the two-sided inverse of `1 - padUnitary V D₀`
  when `R₀` is that of `1 - D₀` (`padResolvent_right`, `padResolvent_left`), and
  `‖padResolvent V R₀‖ ≤ max Q (1/2)` when `‖R₀‖ ≤ Q` (`norm_padResolvent_le`);
* for the isometry `J = V J₀` the interface `hs:eq:interface` of `(J₀, D₀, R₀)` in `K` gives that
  of `(J, padUnitary V D₀, padResolvent V R₀)` (`pad_boundary`, `pad_moment`).

`abstract_simulation_private` is Lemma `hs:lem:abstract` for the private space `K` and a given
isometry `V`: the conclusions of `abstract_simulation_isometry` for the padded data, with `Q ≥ 1`.

The isometry exists: `exists_isometry_of_finrank_le` gives it for every `a` with
`dim K ≤ 2^a dim P` (`finrank_anc`), `exists_isometry_anc` gives some `a` for finite-dimensional
`K` and a finite-dimensional nonzero system `P` (no isometry maps a nonzero `K` into a zero
system). `abstract_simulation_finite` is the resulting form of Lemma `hs:lem:abstract` for every
finite-dimensional private space: the same `a` and `V` serve all data.
-/

set_option autoImplicit false

namespace SparseHamiltonian.PrivateSpaceAbstract

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim GateRemarks
open scoped InnerProduct

/-- An isometry is undone by its adjoint. -/
theorem isometry_adjoint_apply {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {T : E →L[ℂ] F} (hT : T† ∘L T = 1) (y : E) : (T†) (T y) = y := by
  simpa using congrArg (fun A : E →L[ℂ] E => A y) hT

variable {a : ℕ} {P K : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The padded private unitary `V D₀ V† - (1 - V V†)`. -/
def padUnitary (V : K →L[ℂ] Anc a P) (D₀ : K →L[ℂ] K) : Anc a P →L[ℂ] Anc a P :=
  V ∘L D₀ ∘L V† - (1 - V ∘L V†)

/-- The padded resolvent `V R₀ V† + (1 - V V†)/2`. -/
def padResolvent (V : K →L[ℂ] Anc a P) (R₀ : K →L[ℂ] K) : Anc a P →L[ℂ] Anc a P :=
  V ∘L R₀ ∘L V† + (2 : ℂ)⁻¹ • (1 - V ∘L V†)

/-- The padded unitary is `V D₀ V†` plus the phase `-1` times `1 - V V†`, for any `V`. For an isometry
`V` these two terms act on the range of `V` and on its orthogonal complement: see
`padUnitary_comp_isometry` and `padUnitary_apply_of_orth`. -/
theorem padUnitary_eq (V : K →L[ℂ] Anc a P) (D₀ : K →L[ℂ] K) :
    padUnitary V D₀ = V ∘L D₀ ∘L V† + (-1 : ℂ) • (1 - V ∘L V†) := by
  rw [padUnitary]
  module

theorem padUnitary_apply (V : K →L[ℂ] Anc a P) (D₀ : K →L[ℂ] K) (x : Anc a P) :
    padUnitary V D₀ x = V (D₀ ((V†) x)) - (x - V ((V†) x)) := rfl

theorem padResolvent_apply (V : K →L[ℂ] Anc a P) (R₀ : K →L[ℂ] K) (x : Anc a P) :
    padResolvent V R₀ x = V (R₀ ((V†) x)) + (2 : ℂ)⁻¹ • (x - V ((V†) x)) := rfl

theorem adjoint_padUnitary_apply {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) (D₀ : K →L[ℂ] K)
    (x : Anc a P) : (V†) (padUnitary V D₀ x) = D₀ ((V†) x) := by
  rw [padUnitary_apply, map_sub, map_sub, isometry_adjoint_apply hV,
    isometry_adjoint_apply hV, sub_self, sub_zero]

theorem adjoint_padResolvent_apply {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) (R₀ : K →L[ℂ] K)
    (x : Anc a P) : (V†) (padResolvent V R₀ x) = R₀ ((V†) x) := by
  rw [padResolvent_apply, map_add, map_smul, map_sub, isometry_adjoint_apply hV,
    isometry_adjoint_apply hV, sub_self, smul_zero, add_zero]

/-- **On the range of `V`** the padded unitary acts as `D₀`. -/
theorem padUnitary_comp_isometry {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) (D₀ : K →L[ℂ] K) :
    padUnitary V D₀ ∘L V = V ∘L D₀ := by
  refine ContinuousLinearMap.ext fun y => ?_
  rw [comp_apply, comp_apply, padUnitary_apply, isometry_adjoint_apply hV, sub_self, sub_zero]

/-- **On the orthogonal complement of the range of `V`** the padded unitary is the phase `-1`. -/
theorem padUnitary_apply_of_orth (V : K →L[ℂ] Anc a P) (D₀ : K →L[ℂ] K) {w : Anc a P}
    (hw : (V†) w = 0) : padUnitary V D₀ w = -w := by
  rw [padUnitary_apply, hw, map_zero, map_zero, sub_zero, zero_sub]

theorem padUnitary_comp_apply {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) (A B : K →L[ℂ] K)
    (x : Anc a P) :
    padUnitary V A (padUnitary V B x) = V (A (B ((V†) x))) + (x - V ((V†) x)) := by
  rw [padUnitary_apply V A, adjoint_padUnitary_apply hV, padUnitary_apply V B]
  abel

theorem padUnitary_adjoint (V : K →L[ℂ] Anc a P) (D₀ : K →L[ℂ] K) :
    (padUnitary V D₀)† = padUnitary V (D₀†) := by
  have h1 : ((1 : Anc a P →L[ℂ] Anc a P)†) = 1 := by rw [← star_eq_adjoint, star_one]
  rw [padUnitary, padUnitary, map_sub, map_sub, h1, adjoint_comp, adjoint_comp, adjoint_comp,
    adjoint_adjoint, comp_assoc]

/-- **The padded unitary is unitary.** -/
theorem padUnitary_unitary {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) {D₀ : K →L[ℂ] K}
    (hD₀ : IsUnitary D₀) : IsUnitary (padUnitary V D₀) := by
  have h1 : ∀ y, (D₀†) (D₀ y) = y := fun y => by
    simpa [star_eq_adjoint] using congrArg (fun A : K →L[ℂ] K => A y) hD₀.1
  have h2 : ∀ y, D₀ ((D₀†) y) = y := fun y => by
    simpa [star_eq_adjoint] using congrArg (fun A : K →L[ℂ] K => A y) hD₀.2
  refine ⟨ContinuousLinearMap.ext fun x => ?_, ContinuousLinearMap.ext fun x => ?_⟩
  · rw [star_eq_adjoint, padUnitary_adjoint, mul_apply_eq_comp,
      padUnitary_comp_apply hV, h1, one_apply_eq_self]
    abel
  · rw [star_eq_adjoint, padUnitary_adjoint, mul_apply_eq_comp,
      padUnitary_comp_apply hV, h2, one_apply_eq_self]
    abel

/-- **The padded resolvent, right inverse.** -/
theorem padResolvent_right {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) {D₀ R₀ : K →L[ℂ] K}
    (hRight : (1 - D₀) ∘L R₀ = 1) : (1 - padUnitary V D₀) ∘L padResolvent V R₀ = 1 := by
  have h : ∀ y, R₀ y - D₀ (R₀ y) = y := fun y => by
    simpa using congrArg (fun A : K →L[ℂ] K => A y) hRight
  have hD : ∀ y, D₀ (R₀ y) = R₀ y - y := fun y => by
    calc D₀ (R₀ y) = R₀ y - (R₀ y - D₀ (R₀ y)) := by abel
      _ = R₀ y - y := by rw [h y]
  refine ContinuousLinearMap.ext fun x => ?_
  rw [comp_apply, sub_apply, one_apply_eq_self, one_apply_eq_self, padUnitary_apply,
    adjoint_padResolvent_apply hV, hD, map_sub, padResolvent_apply]
  module

/-- **The padded resolvent, left inverse.** -/
theorem padResolvent_left {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) {D₀ R₀ : K →L[ℂ] K}
    (hLeft : R₀ ∘L (1 - D₀) = 1) : padResolvent V R₀ ∘L (1 - padUnitary V D₀) = 1 := by
  have h : ∀ y, R₀ (y - D₀ y) = y := fun y => by
    simpa using congrArg (fun A : K →L[ℂ] K => A y) hLeft
  refine ContinuousLinearMap.ext fun x => ?_
  rw [comp_apply, sub_apply, one_apply_eq_self, padResolvent_apply, map_sub,
    adjoint_padUnitary_apply hV, h, padUnitary_apply, map_sub]
  module

/-- **The norm of the padded resolvent**: `‖V R₀ V† + (1 - V V†)/2‖ ≤ max Q (1/2)` when
`‖R₀‖ ≤ Q` (the two terms act on orthogonal ranges). -/
theorem norm_padResolvent_le {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) {R₀ : K →L[ℂ] K}
    {Q : ℝ} (hR₀ : ‖R₀‖ ≤ Q) : ‖padResolvent V R₀‖ ≤ max Q (1 / 2) := by
  have hQ0 : 0 ≤ Q := (norm_nonneg R₀).trans hR₀
  have hM0 : 0 ≤ max Q (1 / 2) := hQ0.trans (le_max_left _ _)
  have hVn : ∀ z, ‖V z‖ = ‖z‖ := (norm_map_iff_adjoint_comp_self V).mpr hV
  refine opNorm_le_bound _ hM0 fun x => ?_
  set u := (V†) x with hu
  set w := x - V u with hw
  have hVw : (V†) w = 0 := by
    rw [hw, map_sub, isometry_adjoint_apply hV, hu, sub_self]
  have horth : ∀ z (c : ℂ), inner ℂ (V z) (c • w) = 0 := fun z c => by
    rw [← adjoint_inner_right, map_smul, hVw, smul_zero, inner_zero_right]
  have hx : x = V u + w := by rw [hw]; abel
  have hxn : ‖x‖ ^ 2 = ‖u‖ ^ 2 + ‖w‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (V u) w
      (by simpa using horth u 1)
    rw [← hx, hVn] at h
    simpa only [sq] using h
  have hR : ‖padResolvent V R₀ x‖ ^ 2 = ‖R₀ u‖ ^ 2 + (‖w‖ / 2) ^ 2 := by
    have h2 : ‖(2 : ℂ)⁻¹‖ = 1 / 2 := by norm_num
    rw [padResolvent_apply, ← hu, ← hw, sq,
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (horth _ _), hVn, norm_smul, h2]
    ring
  have hRu : ‖R₀ u‖ ≤ Q * ‖u‖ :=
    (le_opNorm R₀ u).trans (mul_le_mul_of_nonneg_right hR₀ (norm_nonneg u))
  have h1 : ‖R₀ u‖ ^ 2 ≤ (Q * ‖u‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hRu 2
  have hQM : Q ≤ max Q (1 / 2) := le_max_left _ _
  have hHM : (1 / 2 : ℝ) ≤ max Q (1 / 2) := le_max_right _ _
  have hQ2 : Q ^ 2 ≤ max Q (1 / 2) ^ 2 := pow_le_pow_left₀ hQ0 hQM 2
  have hH2 : (1 / 2 : ℝ) ^ 2 ≤ max Q (1 / 2) ^ 2 := pow_le_pow_left₀ (by norm_num) hHM 2
  apply le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hM0 (norm_nonneg x))
  rw [mul_pow, hxn, hR]
  nlinarith [sq_nonneg ‖u‖, sq_nonneg ‖w‖, mul_le_mul_of_nonneg_right hQ2 (sq_nonneg ‖u‖),
    mul_le_mul_of_nonneg_right hH2 (sq_nonneg ‖w‖)]

/-- **The boundary condition transfers**: `(V J₀)† R (V J₀) = J₀† R₀ J₀` for the padded
resolvent `R`. -/
theorem pad_boundary {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) (J₀ : P →L[ℂ] K)
    (R₀ : K →L[ℂ] K) :
    (V ∘L J₀)† ∘L padResolvent V R₀ ∘L (V ∘L J₀) = J₀† ∘L R₀ ∘L J₀ := by
  ext p
  rw [adjoint_comp, comp_apply, comp_apply, comp_apply, comp_apply, comp_apply, comp_apply,
    adjoint_padResolvent_apply hV, isometry_adjoint_apply hV]

/-- **The second moment transfers**: `(V J₀)† R† R (V J₀) ⪯ (ν/2) 1` for the padded resolvent
`R` when `J₀† R₀† R₀ J₀ ⪯ (ν/2) 1`. -/
theorem pad_moment {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) (J₀ : P →L[ℂ] K)
    (R₀ : K →L[ℂ] K) {ν : ℝ} (hν : 0 ≤ ν)
    (hMoment : J₀† ∘L R₀† ∘L R₀ ∘L J₀ ≤ ((ν / 2 : ℝ) : ℂ) • (1 : P →L[ℂ] P)) :
    (V ∘L J₀)† ∘L (padResolvent V R₀)† ∘L padResolvent V R₀ ∘L (V ∘L J₀) ≤
      ((ν / 2 : ℝ) : ℂ) • (1 : P →L[ℂ] P) := by
  rw [second_moment_iff R₀ J₀ hν] at hMoment
  rw [second_moment_iff (padResolvent V R₀) (V ∘L J₀) hν]
  have h : padResolvent V R₀ ∘L (V ∘L J₀) = V ∘L (R₀ ∘L J₀) := by
    ext p
    rw [comp_apply, comp_apply, padResolvent_apply, isometry_adjoint_apply hV, sub_self,
      smul_zero, add_zero, comp_apply, comp_apply]
  rw [h]
  have hle : ‖V ∘L (R₀ ∘L J₀)‖ ≤ ‖R₀ ∘L J₀‖ := opNorm_le_bound _ (norm_nonneg _) fun p => by
    rw [comp_apply, (norm_map_iff_adjoint_comp_self V).mpr hV]
    exact le_opNorm _ p
  exact (pow_le_pow_left₀ (norm_nonneg _) hle 2).trans hMoment

/-- `V J₀` is an isometry. -/
theorem pad_isometry {V : K →L[ℂ] Anc a P} (hV : V† ∘L V = 1) {J₀ : P →L[ℂ] K}
    (hJ₀ : J₀† ∘L J₀ = 1) : (V ∘L J₀)† ∘L (V ∘L J₀) = 1 := by
  ext p
  rw [adjoint_comp, comp_apply, comp_apply, comp_apply, isometry_adjoint_apply hV,
    isometry_adjoint_apply hJ₀, one_apply_eq_self]

/-- **Lemma `hs:lem:abstract`, in calls of the padded unitary, for any private space `K`.** Let `V : K → Anc a P` be an isometry
into `a` ancilla qubits and a finite-dimensional system `P`, `J₀ : P → K` a known isometry, `D₀`
a unitary on `K`, `R₀` the two-sided inverse of `1 - D₀`, `h` self-adjoint with `‖h‖ ≤ 1`, and
assume the interface `hs:eq:interface` in `K`: `J₀† R₀ J₀ = (1 + i h)/2`,
`J₀† R₀† R₀ J₀ ≤ (ν/2) 1` in the Loewner order, `‖R₀‖ ≤ Q`, `1 ≤ Q` and `0 < ν ≤ Q`. The padded
private unitary `padUnitary V D₀ = V D₀ V† - (1 - V V†)` acts as `D₀` on the range of `V` and as
the phase `-1` on its orthogonal complement (`padUnitary_comp_isometry`,
`padUnitary_apply_of_orth`). The counts below are of calls of the padded unitary and its adjoint; with a flag for that range, a
call under a control `c` is counted, outside this statement, as one call of `D₀` or `D₀†` under `c`
and the flag, plus known gates, which the gate and wire counts below do not include. For every real `t`, `α > 0`
and `0 < ε ≤ 1/2` there is a unitary `U_J` with `U_J ι₀ = V J₀` for which the conclusions of
`abstract_simulation` hold for this unitary and the isometry `V J₀`: the circuit
`absCircuit a α t Q ν ε` has valid instructions, exactly `6 d ≤ 3840 (α|t|ν + Q log(1/ε))` calls
of the padded unitary or its adjoint (each with at most one control), `12 d` calls of `U_J` or
`U_J†`, the released gate count and number of qubit wires besides the system, full-output error
at most `ε` against `exp(-it (α h))`, and the released degree and register bounds. -/
theorem abstract_simulation_private [FiniteDimensional ℂ P] (V : K →L[ℂ] Anc a P)
    (hV : V† ∘L V = 1) (J₀ : P →L[ℂ] K) (hJ₀ : J₀† ∘L J₀ = 1) (D₀ R₀ : K →L[ℂ] K)
    (h : P →L[ℂ] P) (hD₀ : IsUnitary D₀) (hRight : (1 - D₀) ∘L R₀ = 1)
    (hLeft : R₀ ∘L (1 - D₀) = 1) (hSelf : star h = h) (hh : ‖h‖ ≤ 1)
    (hBoundary : J₀† ∘L R₀ ∘L J₀ = (2 : ℂ)⁻¹ • (1 + Complex.I • h))
    (Q ν : ℝ) (hQ : 1 ≤ Q) (hν : 0 < ν) (hνQ : ν ≤ Q)
    (hMoment : J₀† ∘L R₀† ∘L R₀ ∘L J₀ ≤ ((ν / 2 : ℝ) : ℂ) • (1 : P →L[ℂ] P))
    (hR₀ : ‖R₀‖ ≤ Q) (α t ε : ℝ) (hα : 0 < α) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ UJ : Anc a P →L[ℂ] Anc a P, IsUnitary UJ ∧ UJ ∘L iota0 = V ∘L J₀ ∧
    (∀ g ∈ absCircuit a α t Q ν ε, g.Valid Wire.anc) ∧
    nPriv (absCircuit a α t Q ν ε) = 6 * fDeg Q (α * |t|) ν ε ∧
    (nPriv (absCircuit a α t Q ν ε) : ℝ) ≤ 3840 * (α * |t| * ν + Q * Real.log (1 / ε)) ∧
    nUJ (absCircuit a α t Q ν ε) = 12 * fDeg Q (α * |t|) ν ε ∧
    (nUJ (absCircuit a α t Q ν ε) : ℝ) ≤ 7680 * (α * |t| * ν + Q * Real.log (1 / ε)) ∧
    nGates (absCircuit a α t Q ν ε) ≤
      200 * (fDeg Q (α * |t|) ν ε + 1) * (a + simM (α * |t|) ε + simR Q (α * |t|) ν ε + 1) ∧
    Fintype.card (SimWire a Q (α * |t|) ν ε) =
      2 * a + 3 * simM (α * |t|) ε + 6 * simR Q (α * |t|) ν ε + 3 ∧
    ‖run (simSem UJ (padUnitary V D₀)) (absCircuit a α t Q ν ε) ∘L io -
        io ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) • ((α : ℂ) • h))‖ ≤ ε ∧
    (fDeg Q (α * |t|) ν ε : ℝ) ≤ 128 * (α * |t| * ν + Q * (1 + Real.log (1 / (ε / 3)))) ∧
    TimeSchedule.steps (α * |t|) (ε / 3) ≤ 2 ^ simM (α * |t|) ε ∧
    2 ^ simM (α * |t|) ε < 2 * TimeSchedule.steps (α * |t|) (ε / 3) ∧
    2 * fDeg Q (α * |t|) ν ε + 2 ≤ 2 ^ simR Q (α * |t|) ν ε ∧
    2 ^ simR Q (α * |t|) ν ε ≤ 4 * (fDeg Q (α * |t|) ν ε + 1) :=
  abstract_simulation_isometry (V ∘L J₀) (pad_isometry hV hJ₀) (padUnitary V D₀)
    (padResolvent V R₀) h (padUnitary_unitary hV hD₀) (padResolvent_right hV hRight)
    (padResolvent_left hV hLeft) hSelf hh (by rw [pad_boundary hV J₀ R₀, hBoundary]) Q ν hQ hν
    hνQ (pad_moment hV J₀ R₀ hν.le hMoment)
    ((norm_padResolvent_le hV hR₀).trans_eq (max_eq_left (by linarith))) α t ε hα hε hε2

omit [CompleteSpace P] in
/-- The dimension of `a` ancilla qubits and the system is `2^a dim P`. -/
theorem finrank_anc [FiniteDimensional ℂ P] (a : ℕ) :
    Module.finrank ℂ (Anc a P) = 2 ^ a * Module.finrank ℂ P := by
  show Module.finrank ℂ (PiLp 2 fun _ : Cfg (Fin a) => P) = _
  rw [(WithLp.linearEquiv 2 ℂ _).finrank_eq, Module.finrank_pi_fintype]
  simp

/-- **The embedding exists for every large enough register**: for finite-dimensional `K` and `P`
with `dim K ≤ 2^a dim P` there is an isometry `V : K → Anc a P`. -/
theorem exists_isometry_of_finrank_le [FiniteDimensional ℂ K] [FiniteDimensional ℂ P] (a : ℕ)
    (hdim : Module.finrank ℂ K ≤ 2 ^ a * Module.finrank ℂ P) :
    ∃ V : K →L[ℂ] Anc a P, V† ∘L V = 1 := by
  have hle : Module.finrank ℂ K ≤ Module.finrank ℂ (Anc a P) := by rwa [finrank_anc]
  let bK := stdOrthonormalBasis ℂ K
  let bA := stdOrthonormalBasis ℂ (Anc a P)
  let w : Fin (Module.finrank ℂ K) → Anc a P := fun i => bA (Fin.castLE hle i)
  have hw : Orthonormal ℂ w := bA.orthonormal.comp _ (Fin.castLE_injective hle)
  let f : K →ₗ[ℂ] Anc a P := bK.toBasis.constr ℂ w
  have hf : Orthonormal ℂ (f ∘ bK.toBasis) := by
    have hfw : f ∘ bK.toBasis = w := funext fun i => bK.toBasis.constr_basis ℂ w i
    rw [hfw]
    exact hw
  have hb : Orthonormal ℂ bK.toBasis := by
    rw [bK.coe_toBasis]
    exact bK.orthonormal
  let L : K →ₗᵢ[ℂ] Anc a P := f.isometryOfOrthonormal hb hf
  exact ⟨L.toContinuousLinearMap, (norm_map_iff_adjoint_comp_self _).mp L.norm_map⟩

/-- **The embedding exists**: for finite-dimensional `K` and a finite-dimensional nonzero system
`P` there is an isometry `V` of `K` into `a` ancilla qubits and the system, for some `a`. -/
theorem exists_isometry_anc [FiniteDimensional ℂ K] [FiniteDimensional ℂ P] [Nontrivial P] :
    ∃ (a : ℕ) (V : K →L[ℂ] Anc a P), V† ∘L V = 1 :=
  ⟨Module.finrank ℂ K, exists_isometry_of_finrank_le _ <|
    Nat.lt_two_pow_self.le.trans (Nat.le_mul_of_pos_right _ Module.finrank_pos)⟩

/-- **Lemma `hs:lem:abstract`, in calls of the padded unitary, for every finite-dimensional private
space `K`.** Let `P` be a
finite-dimensional nonzero system. There are `a` and an isometry `V : K → Anc a P`, fixed before
the data, such that for every known isometry `J₀ : P → K`, unitary `D₀` on `K`, two-sided inverse
`R₀` of `1 - D₀` and self-adjoint `h` with `‖h‖ ≤ 1`, the interface `hs:eq:interface` with `1 ≤ Q`
and `0 < ν ≤ Q` gives the conclusions of `abstract_simulation_private` for the padded private
unitary `padUnitary V D₀` and the isometry `V J₀`. `U_J` is chosen after the data in this statement;
the proof takes it from `V J₀` alone (`exists_unitary_extension`). The statement does not bound `a`,
and the gate and wire counts grow with it; for a register with `dim K ≤ 2^a dim P` combine
`exists_isometry_of_finrank_le` with `abstract_simulation_private`. -/
theorem abstract_simulation_finite [FiniteDimensional ℂ K] [FiniteDimensional ℂ P] [Nontrivial P] :
    ∃ (a : ℕ) (V : K →L[ℂ] Anc a P), V† ∘L V = 1 ∧
    ∀ J₀ : P →L[ℂ] K, J₀† ∘L J₀ = 1 → ∀ (D₀ R₀ : K →L[ℂ] K) (h : P →L[ℂ] P), IsUnitary D₀ →
    (1 - D₀) ∘L R₀ = 1 → R₀ ∘L (1 - D₀) = 1 → star h = h → ‖h‖ ≤ 1 →
    J₀† ∘L R₀ ∘L J₀ = (2 : ℂ)⁻¹ • (1 + Complex.I • h) →
    ∀ Q ν : ℝ, 1 ≤ Q → 0 < ν → ν ≤ Q →
    J₀† ∘L R₀† ∘L R₀ ∘L J₀ ≤ ((ν / 2 : ℝ) : ℂ) • (1 : P →L[ℂ] P) → ‖R₀‖ ≤ Q →
    ∀ α t ε : ℝ, 0 < α → 0 < ε → ε ≤ 1 / 2 →
    ∃ UJ : Anc a P →L[ℂ] Anc a P, IsUnitary UJ ∧ UJ ∘L iota0 = V ∘L J₀ ∧
    (∀ g ∈ absCircuit a α t Q ν ε, g.Valid Wire.anc) ∧
    nPriv (absCircuit a α t Q ν ε) = 6 * fDeg Q (α * |t|) ν ε ∧
    (nPriv (absCircuit a α t Q ν ε) : ℝ) ≤ 3840 * (α * |t| * ν + Q * Real.log (1 / ε)) ∧
    nUJ (absCircuit a α t Q ν ε) = 12 * fDeg Q (α * |t|) ν ε ∧
    (nUJ (absCircuit a α t Q ν ε) : ℝ) ≤ 7680 * (α * |t| * ν + Q * Real.log (1 / ε)) ∧
    nGates (absCircuit a α t Q ν ε) ≤
      200 * (fDeg Q (α * |t|) ν ε + 1) * (a + simM (α * |t|) ε + simR Q (α * |t|) ν ε + 1) ∧
    Fintype.card (SimWire a Q (α * |t|) ν ε) =
      2 * a + 3 * simM (α * |t|) ε + 6 * simR Q (α * |t|) ν ε + 3 ∧
    ‖run (simSem UJ (padUnitary V D₀)) (absCircuit a α t Q ν ε) ∘L io -
        io ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) • ((α : ℂ) • h))‖ ≤ ε ∧
    (fDeg Q (α * |t|) ν ε : ℝ) ≤ 128 * (α * |t| * ν + Q * (1 + Real.log (1 / (ε / 3)))) ∧
    TimeSchedule.steps (α * |t|) (ε / 3) ≤ 2 ^ simM (α * |t|) ε ∧
    2 ^ simM (α * |t|) ε < 2 * TimeSchedule.steps (α * |t|) (ε / 3) ∧
    2 * fDeg Q (α * |t|) ν ε + 2 ≤ 2 ^ simR Q (α * |t|) ν ε ∧
    2 ^ simR Q (α * |t|) ν ε ≤ 4 * (fDeg Q (α * |t|) ν ε + 1) := by
  obtain ⟨a, V, hV⟩ := exists_isometry_anc (K := K) (P := P)
  exact ⟨a, V, hV, fun J₀ hJ₀ D₀ R₀ h hD₀ hRight hLeft hSelf hh hBoundary Q ν hQ hν hνQ hMoment hR₀
    α t ε hα hε hε2 => abstract_simulation_private V hV J₀ hJ₀ D₀ R₀ h hD₀ hRight hLeft hSelf hh
      hBoundary Q ν hQ hν hνQ hMoment hR₀ α t ε hα hε hε2⟩

end

end SparseHamiltonian.PrivateSpaceAbstract
