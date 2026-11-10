import GateEfficientMesh.Exact
import GateEfficientNative.Hamiltonian.Theorem

/-!
# Native gates: integrated certificates and nonuniform meshes

The native time-dependent circuit `GateNative.nativeSimT` (the released slot circuit for accuracy
`ε/2`, filter parameter `ε/4`, with every supplied unitary replaced by its native implementation)
of the package extension Theorem `hs:thm:time` with the circuit of `hs:thm:gates` (single-label
case of Lemma `ode:lem:gate-select`) is released for Lipschitz paths
(`GateNative.native_time_simulation`). Its error splits into the exact-gate error, which the
released `GateCircuit.SlotSim.simulationT` bounds against the ordered product of the slot
exponentials, and the native private calls, which the released `GateNative.hcirc_error` adds.

* `native_slot_bounds`: validity, counts and qubits of the native circuit (assembled from the
  public lemmas `hcirc_valid`, `hcirc_nCalls`, `hcirc_nGates`, `card_HW` and the released
  `simulationT`), and, for every operator `U`, the full-output error
  `3ε/4 + ‖∏_k exp(-i (t/2^m) H̃_k) - U‖` on the system embedding.
* `native_time_simulation_certified`: uniform slots, full-output error `ε` against every
  propagator (integral-sense and classical piecewise) whenever the certificate is at most
  `ε/4`; only the subdivision condition `steps (α t) (ε/12) ≤ 2^m` and `48 d ζ ≤ ε`.
* `native_time_simulation_mesh`: a nonuniform mesh with one sample per interval; the native
  slot-selected operation implements, at slot `k`, the private operation of the interval
  `slotPiece k` (the data are presented on the uniform clock); error `ε` under the mesh
  certificate `≤ ε/8` and `8 M α T ≤ ε 2^m`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateMesh

noncomputable section

open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim GateNative
open MeasureTheory Set
open GatePointerEncoding (wordEquivFin)
open TimeDependentExtensions (IsMesh slotPiece slotPiece_lt IsPiecewisePropagator)
open IntegrablePathSimulation.Propagator (IsPropagator)
open scoped InnerProduct BigOperators

section Instances

variable {S : Type*} [Fintype S] [DecidableEq S]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R]

/-- The operators on a qubit register with a payload, with their operator topology, form an
`ENormedAddMonoid` (used to state interval integrability of operator paths on registers);
Mathlib's instance search does not reach it through the `PiLp` norm. It is a scoped instance of
`SparseHamiltonian.GateMesh`, like the released `GateNative.regIsTopologicalRing`. -/
scoped instance regENormedAddMonoid : ENormedAddMonoid (Reg S R →L[ℂ] Reg S R) :=
  @NormedAddGroup.toENormedAddMonoid (Reg S R →L[ℂ] Reg S R) inferInstance

end Instances

section Native

variable {S Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The native slot circuit: counts and the error against any operator.** With the
slot-selected private operations `D k` given natively by one compute circuit on the slot wires
(`NativeOK` for the slot-selected family), the clock promises at every slot for the normalised
samples `H̃_k / α`, the subdivision condition `steps (α t) (ε/12) ≤ 2^m` and the arithmetic
budget `48 d ζ ≤ ε`, the native circuit consists of valid instructions, makes exactly
`12 d` times the calls of `V`, uses at most `200 (d+1)(a+m+r+1) + 84 d C_J + 6 d G_C` elementary
gates on the stated qubits, and, for every operator `U`, its full output on the system
embedding is within `3ε/4 + ‖∏_k exp(-i (t/2^m) H̃_k) - U‖` of `U`. -/
theorem native_slot_bounds (a m : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R)
    (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (Fin m) (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (Fin m) (Fin a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (D R1 : ℕ → Anc a (Reg S R) →L[ℂ] Anc a (Reg S R))
    (hN : NativeOK prim nd (selOp (fun w : Cfg (Fin m) => D (wordEquivFin m w))))
    (Hs : ℕ → Reg S R →L[ℂ] Reg S R)
    (t α Q b qbar ε : ℝ) (ht : 0 ≤ t) (hα : 0 < α) (hQ : 1 ≤ Q)
    (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hCayley : TimeSchedule.steps (α * t) (ε / 12) ≤ 2 ^ m)
    (hD : ∀ k < 2 ^ m, IsUnitary (D k))
    (hRight : ∀ k < 2 ^ m, (1 - D k) ∘L R1 k = 1)
    (hLeft : ∀ k < 2 ^ m, R1 k ∘L (1 - D k) = 1) (hR1 : ∀ k < 2 ^ m, ‖R1 k‖ ≤ Q)
    (hBoundary : ∀ k < 2 ^ m, (UJop (R := R) UJg ∘L iota0 (P := Reg S R))† ∘L R1 k ∘L
      (UJop (R := R) UJg ∘L iota0 (P := Reg S R)) =
        (2 : ℂ)⁻¹ • (1 + Complex.I • ((α : ℂ)⁻¹ • Hs k)))
    (hEndpoint : ∀ k < 2 ^ m, ‖R1 k ∘L (UJop (R := R) UJg ∘L iota0 (P := Reg S R))‖ ≤ b)
    (hbq : b ^ 2 ≤ qbar / 2)
    (hSelf : ∀ k < 2 ^ m, star (Hs k) = Hs k) (hHs : ∀ k < 2 ^ m, ‖Hs k‖ ≤ α)
    (hζε : 48 * (fDeg Q (α * t) qbar (ε / 4) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ nativeSimT a m (α * t) Q qbar ε UJg nd ar, i.Valid) ∧
    (∀ p : J → Bool, nCallsN p (nativeSimT a m (α * t) Q qbar ε UJg nd ar) =
      12 * fDeg Q (α * t) qbar (ε / 4) * nCallsN p nd.V) ∧
    nGatesN (nativeSimT a m (α * t) Q qbar ε UJg nd ar) ≤
      200 * (fDeg Q (α * t) qbar (ε / 4) + 1) * (a + m + simR Q (α * t) qbar (ε / 4) + 1) +
        84 * fDeg Q (α * t) qbar (ε / 4) * UJg.length +
        6 * fDeg Q (α * t) qbar (ε / 4) *
          (2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)) ∧
    Fintype.card (HW (Wire a m (simR Q (α * t) qbar (ε / 4))
        (a + m + 2 * simR Q (α * t) qbar (ε / 4))) S Empty Z ar.bT ar.bP ar.A) =
      Fintype.card S + (2 * a + 3 * m + 6 * simR Q (α * t) qbar (ε / 4) + 3) +
        (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) ∧
    (fDeg Q (α * t) qbar (ε / 4) : ℝ) ≤ 128 * (α * t * qbar + Q * (1 + Real.log (12 / ε))) ∧
    2 * fDeg Q (α * t) qbar (ε / 4) + 2 ≤ 2 ^ simR Q (α * t) qbar (ε / 4) ∧
    2 ^ simR Q (α * t) qbar (ε / 4) ≤ 4 * (fDeg Q (α * t) qbar (ε / 4) + 1) ∧
    ∀ U : Reg S R →L[ℂ] Reg S R,
      ‖nrun prim (nativeSimT a m (α * t) Q qbar ε UJg nd ar) ∘L sysEmb (io (P := Reg S R)) -
          sysEmb (io (P := Reg S R)) ∘L U‖ ≤ 3 * ε / 4 + ‖slotEvolution Hs t m - U‖ := by
  have hε4 : 0 < ε / 4 := by linarith
  have hε41 : ε / 4 ≤ 1 := by linarith
  have hε2 : 0 < ε / 2 := by linarith
  have hε21 : ε / 2 ≤ 1 := by linarith
  have hUJu : IsUnitary (UJop (R := R) UJg) := UJop_isUnitary UJg hUJg
  have hm : TimeSchedule.steps (α * t) (ε / 4 / 3) ≤ 2 ^ m := by
    rw [show ε / 4 / 3 = ε / 12 by ring]
    exact hCayley
  have hC' : TimeSchedule.steps (α * t) (ε / 2 / 6) ≤ 2 ^ m := by
    rw [show ε / 2 / 6 = ε / 12 by ring]
    exact hCayley
  obtain ⟨hvalid, hP, hJ, hG, hW, hdeg, hr1, hr2, -, -⟩ := time_simulation_certified
    (P := Reg S R) a m (UJop (R := R) UJg) D R1 Hs t α Q b qbar (ε / 2) ht hα hQ hqQ hε2 hε21 hC'
    hUJu hD hRight hLeft hR1 hBoundary hEndpoint hbq hSelf hHs
  have e4 : ε / 2 / 2 = ε / 4 := by ring
  have hlog : (6 : ℝ) / (ε / 2) = 12 / ε := by
    field_simp
    ring
  rw [e4] at hvalid hP hJ hG hW hdeg hr1 hr2
  rw [hlog] at hdeg
  have hsec : ∀ i ∈ SlotSim.simCircuitT a (α * t) Q qbar (ε / 4) m,
      SecOK (wireRel _ _ _ _) i := by
    unfold SlotSim.simCircuitT
    exact secOK_ampI _ _ _ _ _ _
  have hfam : slotFam (m := m) (S := S) (R := R) D false = fun w => D (wordEquivFin m w) := rfl
  have hDu : ∀ w, IsUnitary (slotFam (m := m) (S := S) (R := R) D false w) := by
    intro w
    rw [hfam]
    exact hD _ (wordEquivFin m w).isLt
  have hDadj : ∀ w, slotFam (m := m) (S := S) (R := R) D true w = (slotFam D false w)† :=
    fun _ => rfl
  have hN' : NativeOK prim nd (selOp (slotFam D false)) := by rw [hfam]; exact hN
  refine ⟨hcirc_valid (wireRel _ _ _ _) (slotSel _ _ _ _) UJg hUJg nd hnd ar har.elem
    har.classical _ hvalid, fun p => ?_, ?_, ?_, hdeg, hr1, hr2, fun U => ?_⟩
  · rw [nativeSimT, hcirc_nCalls, hP]
    ring
  · refine (hcirc_nGates (wireRel _ _ _ _) (slotSel _ _ _ _) UJg hUJg nd ar _).trans ?_
    rw [hP, hJ, mul_one]
    have h84 : 12 * fDeg Q (α * t) qbar (ε / 4) * (7 * UJg.length) =
        84 * fDeg Q (α * t) qbar (ε / 4) * UJg.length := by ring
    rw [h84]
    exact Nat.add_le_add_right (Nat.add_le_add_right hG _) _
  · rw [card_HW, hW]
    simp only [Fintype.card_empty, add_zero]
    ring
  · have hio : ∀ ψ : Reg S R, ‖(io (P := Reg S R) (a := a) (m := m)
        (r := simR Q (α * t) qbar (ε / 4)) (K := a + m + 2 * simR Q (α * t) qbar (ε / 4))) ψ‖ =
        ‖ψ‖ :=
      fun ψ => by rw [io_apply, norm_bas]
    have herr := slot_product_error (P := Reg S R) a m (UJop (R := R) UJg) D R1 Hs t α Q b qbar
      (ε / 4) ht hα hQ hqQ hε4 hε41 hm hUJu hD hRight hLeft hR1 hBoundary hEndpoint hbq hSelf hHs U
    rw [nativeSimT]
    generalize SlotSim.simCircuitT a (α * t) Q qbar (ε / 4) m = l at herr hvalid hsec hP ⊢
    have h := hcirc_error (X' := Empty) prim hprim (wireRel _ _ _ _) (slotSel _ _ _ _) UJg hUJg nd
      hnd ar hζ har (slotFam D) hDu hDadj hN' l hvalid io hio U _
      (prodOps_evalSel_slot UJg D l hsec) herr
    refine h.trans ?_
    rw [hP, Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hζε]

/-- **Native gate-efficient time-dependent simulation under the integrated certificate** (Theorem
`hs:thm:time` with the circuit of `hs:thm:gates`, before finite-set synthesis, with the certificate
of the paragraphs after the proof of Theorem `hs:thm:time`).

The native circuit `nativeSimT a m (α t) Q qbar ε UJg nd ar` depends only on the public data.
With the slot-selected private operations `D k` given natively by the compute circuit `V`
(`NativeOK`), the clock promises at every slot for `H̃_k / α` (`H̃_k` self-adjoint,
`‖H̃_k‖ ≤ α`), the subdivision condition `steps (α t) (ε/12) ≤ 2^m` and the arithmetic budget
`48 d ζ ≤ ε`, it has the counts of `native_slot_bounds`, and its full output on the system
embedding is within `ε` of `U(t)` for every integral-sense propagator `U` of a path that is
self-adjoint almost everywhere and interval integrable, and for every classical piecewise
propagator of a path with one piece per slot, whenever
`∑_k ∫_{kt/2^m}^{(k+1)t/2^m} ‖H(u) - H̃_k‖ du ≤ ε / 4`. -/
theorem native_time_simulation_certified (a m : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R)
    (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (Fin m) (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (Fin m) (Fin a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (D R1 : ℕ → Anc a (Reg S R) →L[ℂ] Anc a (Reg S R))
    (hN : NativeOK prim nd (selOp (fun w : Cfg (Fin m) => D (wordEquivFin m w))))
    (Hs : ℕ → Reg S R →L[ℂ] Reg S R)
    (t α Q b qbar ε : ℝ) (ht : 0 ≤ t) (hα : 0 < α) (hQ : 1 ≤ Q)
    (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hCayley : TimeSchedule.steps (α * t) (ε / 12) ≤ 2 ^ m)
    (hD : ∀ k < 2 ^ m, IsUnitary (D k))
    (hRight : ∀ k < 2 ^ m, (1 - D k) ∘L R1 k = 1)
    (hLeft : ∀ k < 2 ^ m, R1 k ∘L (1 - D k) = 1) (hR1 : ∀ k < 2 ^ m, ‖R1 k‖ ≤ Q)
    (hBoundary : ∀ k < 2 ^ m, (UJop (R := R) UJg ∘L iota0 (P := Reg S R))† ∘L R1 k ∘L
      (UJop (R := R) UJg ∘L iota0 (P := Reg S R)) =
        (2 : ℂ)⁻¹ • (1 + Complex.I • ((α : ℂ)⁻¹ • Hs k)))
    (hEndpoint : ∀ k < 2 ^ m, ‖R1 k ∘L (UJop (R := R) UJg ∘L iota0 (P := Reg S R))‖ ≤ b)
    (hbq : b ^ 2 ≤ qbar / 2)
    (hSelf : ∀ k < 2 ^ m, star (Hs k) = Hs k) (hHs : ∀ k < 2 ^ m, ‖Hs k‖ ≤ α)
    (hζε : 48 * (fDeg Q (α * t) qbar (ε / 4) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ nativeSimT a m (α * t) Q qbar ε UJg nd ar, i.Valid) ∧
    (∀ p : J → Bool, nCallsN p (nativeSimT a m (α * t) Q qbar ε UJg nd ar) =
      12 * fDeg Q (α * t) qbar (ε / 4) * nCallsN p nd.V) ∧
    nGatesN (nativeSimT a m (α * t) Q qbar ε UJg nd ar) ≤
      200 * (fDeg Q (α * t) qbar (ε / 4) + 1) * (a + m + simR Q (α * t) qbar (ε / 4) + 1) +
        84 * fDeg Q (α * t) qbar (ε / 4) * UJg.length +
        6 * fDeg Q (α * t) qbar (ε / 4) *
          (2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)) ∧
    Fintype.card (HW (Wire a m (simR Q (α * t) qbar (ε / 4))
        (a + m + 2 * simR Q (α * t) qbar (ε / 4))) S Empty Z ar.bT ar.bP ar.A) =
      Fintype.card S + (2 * a + 3 * m + 6 * simR Q (α * t) qbar (ε / 4) + 3) +
        (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) ∧
    (fDeg Q (α * t) qbar (ε / 4) : ℝ) ≤ 128 * (α * t * qbar + Q * (1 + Real.log (12 / ε))) ∧
    2 * fDeg Q (α * t) qbar (ε / 4) + 2 ≤ 2 ^ simR Q (α * t) qbar (ε / 4) ∧
    2 ^ simR Q (α * t) qbar (ε / 4) ≤ 4 * (fDeg Q (α * t) qbar (ε / 4) + 1) ∧
    (∀ H U : ℝ → Reg S R →L[ℂ] Reg S R, (∀ᵐ u, u ∈ Icc 0 t → star (H u) = H u) →
      IntervalIntegrable H volume 0 t →
      ∑ k ∈ Finset.range (2 ^ m), ∫ u in slotMesh t m k..slotMesh t m (k + 1), ‖H u - Hs k‖ ≤
        ε / 4 →
      IsPropagator H U t →
      ‖nrun prim (nativeSimT a m (α * t) Q qbar ε UJg nd ar) ∘L sysEmb (io (P := Reg S R)) -
          sysEmb (io (P := Reg S R)) ∘L U t‖ ≤ ε) ∧
    (∀ (Hp : ℕ → ℝ → Reg S R →L[ℂ] Reg S R) (U : ℝ → Reg S R →L[ℂ] Reg S R),
      (∀ k < 2 ^ m, ∀ u ∈ Icc (slotMesh t m k) (slotMesh t m (k + 1)),
        star (Hp k u) = Hp k u) →
      (∀ k < 2 ^ m, IntervalIntegrable (Hp k) volume (slotMesh t m k) (slotMesh t m (k + 1))) →
      ∑ k ∈ Finset.range (2 ^ m),
          ∫ u in slotMesh t m k..slotMesh t m (k + 1), ‖Hp k u - Hs k‖ ≤ ε / 4 →
      IsPiecewisePropagator Hp (slotMesh t m) (2 ^ m) U →
      ‖nrun prim (nativeSimT a m (α * t) Q qbar ε UJg nd ar) ∘L sysEmb (io (P := Reg S R)) -
          sysEmb (io (P := Reg S R)) ∘L U t‖ ≤ ε) := by
  obtain ⟨hvalid, hcalls, hgates, hcard, hdeg, hr1, hr2, herr⟩ := native_slot_bounds a m prim
    hprim UJg hUJg nd hnd ar ζ hζ har D R1 hN Hs t α Q b qbar ε ht hα hQ hqQ hε hε1 hCayley hD
    hRight hLeft hR1 hBoundary hEndpoint hbq hSelf hHs hζε
  refine ⟨hvalid, hcalls, hgates, hcard, hdeg, hr1, hr2, fun H U hH hint hcert hU => ?_,
    fun Hp U hH hint hcert hU => ?_⟩
  · have h1 := herr (U t)
    have h2 := slot_error_integral Hs ht m hU hH hSelf hint
    rw [norm_sub_rev] at h2
    linarith
  · have h1 := herr (U t)
    have h2 := slot_error_piecewise Hs ht m hU hH hSelf hint
    rw [norm_sub_rev] at h2
    linarith

/-- **Native gate-efficient time-dependent simulation on a nonuniform mesh** (Theorem `hs:thm:time`
with the circuit of `hs:thm:gates`, before finite-set synthesis, extended by uniform refinement to
nonuniform meshes with breakpoints, with the integrated certificate).

Let `0 = t_0 ≤ ⋯ ≤ t_M = T` be a mesh (`M ≥ 1`, `T > 0`) with private operations `D_r` and
samples `H̃_r` (`r < M`) satisfying the clock promises for `H̃_r / α`. The data are presented on
the uniform clock of `2^m` slots: the native compute circuit implements, at slot word `k`, the
private operation `D_{σ k}` of the interval `σ k = slotPiece` containing `k T / 2^m`
(`NativeOK` for this slot-selected family). Under the subdivision condition
`steps (α T) (ε/12) ≤ 2^m`, the rounding condition `8 M α T ≤ ε 2^m` and `48 d ζ ≤ ε`, the
native circuit has the counts of `native_slot_bounds` (the mesh enters only through `m`) and its
full output is within `ε` of `U(T)` for every integral-sense propagator and every classical
piecewise propagator with one piece per mesh interval, whenever the mesh certificate
`∑_r ∫_{t_r}^{t_{r+1}} ‖H(u) - H̃_r‖ du` is at most `ε / 8`. -/
theorem native_time_simulation_mesh (a m M : ℕ) (hM : 0 < M) (prim : J → Reg Y R →L[ℂ] Reg Y R)
    (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (Fin m) (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (Fin m) (Fin a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (D R1 : ℕ → Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (Hs : ℕ → Reg S R →L[ℂ] Reg S R)
    (tm : ℕ → ℝ) (T α Q b qbar ε : ℝ) (hmesh : IsMesh tm M T) (hT : 0 < T)
    (hN : NativeOK prim nd
      (selOp (fun w : Cfg (Fin m) => D (slotPiece tm T (2 ^ m) M (wordEquivFin m w)))))
    (hα : 0 < α) (hQ : 1 ≤ Q) (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hCayley : TimeSchedule.steps (α * T) (ε / 12) ≤ 2 ^ m)
    (hRound : 8 * M * α * T ≤ ε * 2 ^ m)
    (hD : ∀ r < M, IsUnitary (D r))
    (hRight : ∀ r < M, (1 - D r) ∘L R1 r = 1)
    (hLeft : ∀ r < M, R1 r ∘L (1 - D r) = 1) (hR1 : ∀ r < M, ‖R1 r‖ ≤ Q)
    (hBoundary : ∀ r < M, (UJop (R := R) UJg ∘L iota0 (P := Reg S R))† ∘L R1 r ∘L
      (UJop (R := R) UJg ∘L iota0 (P := Reg S R)) =
        (2 : ℂ)⁻¹ • (1 + Complex.I • ((α : ℂ)⁻¹ • Hs r)))
    (hEndpoint : ∀ r < M, ‖R1 r ∘L (UJop (R := R) UJg ∘L iota0 (P := Reg S R))‖ ≤ b)
    (hbq : b ^ 2 ≤ qbar / 2)
    (hSelf : ∀ r < M, star (Hs r) = Hs r) (hHs : ∀ r < M, ‖Hs r‖ ≤ α)
    (hζε : 48 * (fDeg Q (α * T) qbar (ε / 4) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ nativeSimT a m (α * T) Q qbar ε UJg nd ar, i.Valid) ∧
    (∀ p : J → Bool, nCallsN p (nativeSimT a m (α * T) Q qbar ε UJg nd ar) =
      12 * fDeg Q (α * T) qbar (ε / 4) * nCallsN p nd.V) ∧
    nGatesN (nativeSimT a m (α * T) Q qbar ε UJg nd ar) ≤
      200 * (fDeg Q (α * T) qbar (ε / 4) + 1) * (a + m + simR Q (α * T) qbar (ε / 4) + 1) +
        84 * fDeg Q (α * T) qbar (ε / 4) * UJg.length +
        6 * fDeg Q (α * T) qbar (ε / 4) *
          (2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)) ∧
    Fintype.card (HW (Wire a m (simR Q (α * T) qbar (ε / 4))
        (a + m + 2 * simR Q (α * T) qbar (ε / 4))) S Empty Z ar.bT ar.bP ar.A) =
      Fintype.card S + (2 * a + 3 * m + 6 * simR Q (α * T) qbar (ε / 4) + 3) +
        (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) ∧
    (fDeg Q (α * T) qbar (ε / 4) : ℝ) ≤ 128 * (α * T * qbar + Q * (1 + Real.log (12 / ε))) ∧
    2 * fDeg Q (α * T) qbar (ε / 4) + 2 ≤ 2 ^ simR Q (α * T) qbar (ε / 4) ∧
    2 ^ simR Q (α * T) qbar (ε / 4) ≤ 4 * (fDeg Q (α * T) qbar (ε / 4) + 1) ∧
    (∀ H U : ℝ → Reg S R →L[ℂ] Reg S R, (∀ᵐ u, u ∈ Icc 0 T → star (H u) = H u) →
      IntervalIntegrable H volume 0 T →
      ∑ r ∈ Finset.range M, ∫ u in tm r..tm (r + 1), ‖H u - Hs r‖ ≤ ε / 8 →
      IsPropagator H U T →
      ‖nrun prim (nativeSimT a m (α * T) Q qbar ε UJg nd ar) ∘L sysEmb (io (P := Reg S R)) -
          sysEmb (io (P := Reg S R)) ∘L U T‖ ≤ ε) ∧
    (∀ (Hp : ℕ → ℝ → Reg S R →L[ℂ] Reg S R) (U : ℝ → Reg S R →L[ℂ] Reg S R),
      (∀ r < M, ∀ u ∈ Icc (tm r) (tm (r + 1)), star (Hp r u) = Hp r u) →
      (∀ r < M, IntervalIntegrable (Hp r) volume (tm r) (tm (r + 1))) →
      ∑ r ∈ Finset.range M, ∫ u in tm r..tm (r + 1), ‖Hp r u - Hs r‖ ≤ ε / 8 →
      IsPiecewisePropagator Hp tm M U →
      ‖nrun prim (nativeSimT a m (α * T) Q qbar ε UJg nd ar) ∘L sysEmb (io (P := Reg S R)) -
          sysEmb (io (P := Reg S R)) ∘L U T‖ ≤ ε) := by
  have hσ : ∀ k, slotPiece tm T (2 ^ m) M k < M := fun k => slotPiece_lt hM k
  obtain ⟨hvalid, hcalls, hgates, hcard, hdeg, hr1, hr2, herr⟩ := native_slot_bounds a m prim
    hprim UJg hUJg nd hnd ar ζ hζ har (fun k => D (slotPiece tm T (2 ^ m) M k))
    (fun k => R1 (slotPiece tm T (2 ^ m) M k)) hN (fun k => Hs (slotPiece tm T (2 ^ m) M k)) T α
    Q b qbar ε hT.le hα hQ hqQ hε hε1 hCayley (fun k _ => hD _ (hσ k))
    (fun k _ => hRight _ (hσ k)) (fun k _ => hLeft _ (hσ k)) (fun k _ => hR1 _ (hσ k))
    (fun k _ => hBoundary _ (hσ k)) (fun k _ => hEndpoint _ (hσ k)) hbq
    (fun k _ => hSelf _ (hσ k)) (fun k _ => hHs _ (hσ k)) hζε
  have hround : (M : ℝ) * (T / 2 ^ m) * α ≤ ε / 8 := by
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    rw [show (M : ℝ) * (T / 2 ^ m) * α = M * α * T / 2 ^ m by ring, div_le_iff₀ h2]
    linarith
  refine ⟨hvalid, hcalls, hgates, hcard, hdeg, hr1, hr2, fun H U hH hint hcert hU => ?_,
    fun Hp U hH hint hcert hU => ?_⟩
  · have h1 := herr (U T)
    have h2 := mesh_slot_error Hs hM hmesh hT m hU hH hSelf hHs hint
    rw [norm_sub_rev] at h2
    linarith
  · have h1 := herr (U T)
    have h2 := mesh_slot_error_piecewise Hs hM hmesh hT m hU hH hSelf hHs hint
    rw [norm_sub_rev] at h2
    linarith

end Native

end

end SparseHamiltonian.GateMesh
