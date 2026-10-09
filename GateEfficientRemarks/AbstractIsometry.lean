import GateEfficientRemarks.Abstract
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Lemma `hs:lem:abstract` for an arbitrary known isometry

Lemma `hs:lem:abstract` of the accompanying paper takes an arbitrary known isometry `J` from
the system into the private space. The released gate model supplies `J` as `U_J ι₀`, where
`U_J` is a unitary on `a` ancilla qubits and the system and `ι₀` places the system on the
all-zero ancilla word. For a finite-dimensional system the two forms agree:

* `exists_unitary_extension`: every isometry `J : P → Anc a P` (`J† J = 1`) is `U_J ι₀` for a
  unitary `U_J` (Mathlib's `LinearIsometry.extend`, applied to the isometry `ι₀ p ↦ J p` on the
  range of `ι₀`, and upgraded to a linear isometry equivalence in finite dimension);
* `abstract_simulation_isometry`: Lemma `hs:lem:abstract` with the interface stated for `J`
  itself; the circuit `absCircuit` calls such a `U_J`. By `abstract_simulation` the conclusions
  hold for every unitary `U_J` with `U_J ι₀ = J`, since the interface involves `U_J` only
  through `J`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateRemarks

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim
open scoped InnerProduct

variable {a : ℕ} {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **Every isometry is `U_J ι₀`** (`hs:lem:abstract`): for a finite-dimensional system `P`,
every isometry `J : P → Anc a P`, `J† J = 1`, is `U_J ∘ ι₀` for a unitary `U_J` on the
ancillas and the system. -/
theorem exists_unitary_extension [FiniteDimensional ℂ P] (J : P →L[ℂ] Anc a P)
    (hJ : J† ∘L J = 1) : ∃ UJ : Anc a P →L[ℂ] Anc a P, IsUnitary UJ ∧ UJ ∘L iota0 = J := by
  have hJn : ∀ p, ‖J p‖ = ‖p‖ := (norm_map_iff_adjoint_comp_self J).mpr hJ
  have hιn : ∀ p, ‖(iota0 (a := a) (P := P)) p‖ = ‖p‖ :=
    (norm_map_iff_adjoint_comp_self _).mpr iota0_isometry
  have hιι : ∀ p, ((iota0 (a := a) (P := P))†) (iota0 p) = p := by
    intro p
    rw [← comp_apply, iota0_isometry, one_apply_eq_self]
  let S : Submodule ℂ (Anc a P) :=
    LinearMap.range ((iota0 (a := a) (P := P)) : P →ₗ[ℂ] Anc a P)
  let L0 : S →ₗ[ℂ] Anc a P :=
    ((J ∘L (iota0 (a := a) (P := P))†) : Anc a P →ₗ[ℂ] Anc a P).comp S.subtype
  have hL0 : ∀ s : S, ‖L0 s‖ = ‖s‖ := by
    rintro ⟨_, p, rfl⟩
    change ‖J (((iota0 (a := a) (P := P))†) (iota0 p))‖ = ‖iota0 (a := a) p‖
    rw [hιι, hJn, hιn]
  let L : S →ₗᵢ[ℂ] Anc a P := ⟨L0, hL0⟩
  let e : Anc a P ≃ₗᵢ[ℂ] Anc a P := L.extend.toLinearIsometryEquiv rfl
  refine ⟨(e : Anc a P →L[ℂ] Anc a P), ⟨?_, ?_⟩, ?_⟩
  · rw [star_eq_adjoint, LinearIsometryEquiv.adjoint_eq_symm]
    refine ContinuousLinearMap.ext (fun x => ?_)
    simp
  · rw [star_eq_adjoint, LinearIsometryEquiv.adjoint_eq_symm]
    refine ContinuousLinearMap.ext (fun x => ?_)
    simp
  · refine ContinuousLinearMap.ext (fun p => ?_)
    have h1 : L.extend (iota0 p) = L ⟨iota0 p, p, rfl⟩ :=
      LinearIsometry.extend_apply L ⟨iota0 p, p, rfl⟩
    change L.extend (iota0 p) = J p
    rw [h1]
    change J (((iota0 (a := a) (P := P))†) (iota0 p)) = J p
    rw [hιι]

/-- **Lemma `hs:lem:abstract` for an arbitrary known isometry `J`** (finite-dimensional system
`P`). Assume the interface `hs:eq:interface` for `J` itself: `J† J = 1`, `D` unitary, `R₁` the
two-sided inverse of `1 - D`, `J† R₁ J = (1 + i h)/2` with `h` self-adjoint and `‖h‖ ≤ 1`,
`J† R₁† R₁ J ≤ (ν/2) 1`, `‖R₁‖ ≤ Q`, `1 ≤ Q`, `0 < ν ≤ Q`. Then there is a unitary `U_J` with
`U_J ι₀ = J` for which the conclusions of `abstract_simulation` hold: for every real `t`,
`α > 0` and `0 < ε ≤ 1/2`, the circuit `absCircuit a α t Q ν ε` run with `U_J` and `D` has valid
instructions, exactly `6 d ≤ 3840 (α|t|ν + Q log(1/ε))` calls of `D` or `D†` (each with at most
one control), `12 d` calls of `U_J` or `U_J†`, the released gate count and number of qubit
wires besides the system, full-output error at most `ε` against `exp(-it (α h))`, and the
released degree and register bounds. -/
theorem abstract_simulation_isometry [FiniteDimensional ℂ P] (J : P →L[ℂ] Anc a P)
    (hJ : J† ∘L J = 1) (D R1 : Anc a P →L[ℂ] Anc a P) (h : P →L[ℂ] P) (hD : IsUnitary D)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hSelf : star h = h) (hh : ‖h‖ ≤ 1)
    (hBoundary : J† ∘L R1 ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • h))
    (Q ν : ℝ) (hQ : 1 ≤ Q) (hν : 0 < ν) (hνQ : ν ≤ Q)
    (hMoment : J† ∘L R1† ∘L R1 ∘L J ≤ ((ν / 2 : ℝ) : ℂ) • (1 : P →L[ℂ] P))
    (hR1 : ‖R1‖ ≤ Q) (α t ε : ℝ) (hα : 0 < α) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ UJ : Anc a P →L[ℂ] Anc a P, IsUnitary UJ ∧ UJ ∘L iota0 = J ∧
    (∀ g ∈ absCircuit a α t Q ν ε, g.Valid Wire.anc) ∧
    nPriv (absCircuit a α t Q ν ε) = 6 * fDeg Q (α * |t|) ν ε ∧
    (nPriv (absCircuit a α t Q ν ε) : ℝ) ≤ 3840 * (α * |t| * ν + Q * Real.log (1 / ε)) ∧
    nUJ (absCircuit a α t Q ν ε) = 12 * fDeg Q (α * |t|) ν ε ∧
    (nUJ (absCircuit a α t Q ν ε) : ℝ) ≤ 7680 * (α * |t| * ν + Q * Real.log (1 / ε)) ∧
    nGates (absCircuit a α t Q ν ε) ≤
      200 * (fDeg Q (α * |t|) ν ε + 1) * (a + simM (α * |t|) ε + simR Q (α * |t|) ν ε + 1) ∧
    Fintype.card (SimWire a Q (α * |t|) ν ε) =
      2 * a + 3 * simM (α * |t|) ε + 6 * simR Q (α * |t|) ν ε + 3 ∧
    ‖run (simSem UJ D) (absCircuit a α t Q ν ε) ∘L io -
        io ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) • ((α : ℂ) • h))‖ ≤ ε ∧
    (fDeg Q (α * |t|) ν ε : ℝ) ≤ 128 * (α * |t| * ν + Q * (1 + Real.log (1 / (ε / 3)))) ∧
    TimeSchedule.steps (α * |t|) (ε / 3) ≤ 2 ^ simM (α * |t|) ε ∧
    2 ^ simM (α * |t|) ε < 2 * TimeSchedule.steps (α * |t|) (ε / 3) ∧
    2 * fDeg Q (α * |t|) ν ε + 2 ≤ 2 ^ simR Q (α * |t|) ν ε ∧
    2 ^ simR Q (α * |t|) ν ε ≤ 4 * (fDeg Q (α * |t|) ν ε + 1) := by
  obtain ⟨UJ, hUJ, hJU⟩ := exists_unitary_extension J hJ
  rw [← hJU] at hBoundary hMoment
  exact ⟨UJ, hUJ, hJU, abstract_simulation a UJ D R1 h hUJ hD hRight hLeft hSelf hh hBoundary Q ν
    hQ hν hνQ hMoment hR1 α t ε hα hε hε2⟩

end

end SparseHamiltonian.GateRemarks
