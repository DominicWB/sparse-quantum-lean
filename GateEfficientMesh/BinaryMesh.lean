import GateEfficientMesh.BinaryTheorem
import ODELowerBoundExtensions.Release.Refine

/-!
# Binary sparse data on a nonuniform mesh

Theorem `hs:thm:gates`, time-dependent part, from time-indexed binary sparse oracles, extended by
uniform refinement to nonuniform meshes with breakpoints (the paper states the gate theorem on
uniform meshes). A mesh `0 = t_0 ≤ ⋯ ≤ t_M = T` carries one represented sample per interval,
given by native sparse data `D_m : Data (X × Fin M)` in the released binary format. The uniform
clock of the binary circuit has `2^m` slots; its time-indexed data are the re-indexed data
`(x, k) ↦ D_m (x, σ k)` (`clockData`, the released `ODELowerBoundExtensions.Release.stageData`
along the slot-to-sample map `σ = TimeDependentExtensions.pieceOf`), so slot `k` reads the
sample of the interval containing `k T / 2^m`.

* `clockData_matrix`, `prims_reindexData`, `primsT_clockData`: the clock data have the mesh
  samples, the same slots and decoder, and their time-indexed primitive oracles are the
  coherent sampled-time oracles `∑_w |w⟩⟨w| ⊗ O(x, σ w)` of the mesh data.
* `binary_time_simulation_mesh`: the released circuit `binaryTimeSim` with the counts of the
  uniform theorem (the mesh enters only through `m`), and full-output error at most `ε`
  against every propagator of the lifted path, integral-sense or classical piecewise with one
  piece per mesh interval, under the mesh certificate `≤ ε/8`, the rounding condition
  `8 M τ' ≤ ε 2^m` (`τ' = √s T/γ`) and the subdivision condition.
* `binary_time_simulation_budget_mesh`: the budget form on a mesh, with the rescaling `γ` of
  `binary_time_simulation_budget_certified` chosen before the mesh and the data.

The slot-to-sample map is part of the presentation of the data on the uniform clock, not a
counted circuit: computing it from an arbitrary table of `M` breakpoints would cost a factor `M`
(or a comparator against every breakpoint) in every private call.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateMesh

noncomputable section

open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary
open SparseHamiltonian.GateCircuit.Sim (iota0 fDeg simR io Wire)
open SparseHamiltonian.OracleCircuit CayleyClockInterface
open SparseHamiltonian.GatePointerEncoding (wordEquivFin)
open NativeSparseBlockEncoding (Data Query)
open MeasureTheory Set
open TimeDependentExtensions (IsMesh IsPiecewisePropagator slotPiece slotPiece_lt pieceOf)
open IntegrablePathSimulation.Propagator (IsPropagator)
open scoped InnerProduct BigOperators

section Clock

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s M : ℕ}

/-- **The mesh data on the uniform clock**: slot `k < 2^m` reads the sample of the interval
`pieceOf k` containing `k T / 2^m` (the released `stageData` along the slot-to-sample map). -/
def clockData (D : Data (X × Fin M) n Z s) (hM : 0 < M) (tm : ℕ → ℝ) (T : ℝ) (m : ℕ) :
    Data (X × Fin (2 ^ m)) n Z s :=
  ODELowerBoundExtensions.Release.stageData D (fun k : Fin (2 ^ m) => pieceOf tm T (2 ^ m) hM k)

/-- The clock data at slot `k` have the mesh sample of the interval `pieceOf k`. -/
theorem clockData_matrix (D : Data (X × Fin M) n Z s) (hM : 0 < M) (tm : ℕ → ℝ) (T : ℝ)
    (m : ℕ) (x : X) (k : Fin (2 ^ m)) :
    (clockData D hM tm T m).matrix (x, k) = D.matrix (x, pieceOf tm T (2 ^ m) hM k) := rfl

/-- The clock data have the slots (location lists) of the mesh data. -/
theorem clockData_slot (D : Data (X × Fin M) n Z s) (hM : 0 < M) (tm : ℕ → ℝ) (T : ℝ)
    (m : ℕ) : (clockData D hM tm T m).slot = D.slot := rfl

/-- The clock data have the value decoder of the mesh data. -/
theorem clockData_decode (D : Data (X × Fin M) n Z s) (hM : 0 < M) (tm : ℕ → ℝ) (T : ℝ)
    (m : ℕ) : (clockData D hM tm T m).decode = D.decode := rfl

end Clock

section Oracles

variable {X Y n : Type*} [Fintype n] [DecidableEq n] {s k b m M : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The binary primitive oracles of reindexed data are those of the data at the image input. -/
theorem prims_reindexData (D : Data Y n (Cfg (VW b)) s) (f : X → Y) (en : Cfg (Fin k) ≃ n)
    (x : X) :
    prims (R := R) (ODELowerBoundExtensions.Release.reindexData D f) en x =
      prims (R := R) D en (f x) := by
  funext q
  cases q <;> rfl

/-- **The oracle identity**: the time-indexed primitive oracles of the clock data are the
coherent sampled-time oracles that read, at slot word `w`, the binary primitive oracles of the
mesh sample of the interval containing the slot. -/
theorem primsT_clockData (D : Data (X × Fin M) n (Cfg (VW b)) s) (hM : 0 < M) (tm : ℕ → ℝ)
    (T : ℝ) (en : Cfg (Fin k) ≃ n) (x : X) :
    primsT (R := R) (clockData D hM tm T m) en x =
      slotPrim (fun w => prims (R := R) D en (x, pieceOf tm T (2 ^ m) hM (wordEquivFin m w))) := by
  unfold primsT clockData ODELowerBoundExtensions.Release.stageData
  congr 1

end Oracles

/-! ### The mesh theorem -/

section Main

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b m M : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The lifted samples of the mesh intervals (zero beyond the last interval). -/
def meshSample (D : Data (X × Fin M) n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (r : ℕ) : Reg (Fin k) R →L[ℂ] Reg (Fin k) R :=
  if h : r < M then qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix (x, ⟨r, h⟩)))
  else 0

/-- **Gate-efficient time-dependent sparse simulation from binary data on a nonuniform mesh**
(Theorem `hs:thm:gates`, time-dependent part, for binary sparse oracles, extended by uniform
refinement to nonuniform meshes with breakpoints, with the integrated certificate, before
finite-set synthesis). Let `0 = t_0 ≤ ⋯ ≤ t_M = T` be a mesh (`M ≥ 1`, `T > 0`) whose samples
`H̃_r = D_m.matrix (x, r)` are given by native sparse data in the released binary format,
Hermitian with row and column norms at most one. The circuit
`binaryTimeSim` runs on the clock data `clockData D_m` (slot `k` reads the sample of the
interval containing `k T / 2^m`, through the oracles of `primsT_clockData`). Under the
subdivision condition `steps τ' (ε/12) ≤ 2^m` (`τ' = √s T/γ`), the rounding condition
`8 M τ' ≤ ε 2^m` and `48 d ζ ≤ ε`, the circuit has the counts and qubits of the uniform theorem
`binary_time_simulation_certified` and its full output is within `ε` of `U(T)` for every
integral-sense propagator `U` of the lift of a matrix path that is Hermitian almost everywhere
and interval integrable, and for every classical piecewise propagator of the lift of a
piecewise matrix path with one piece per mesh interval, whenever the mesh certificate
`∑_r ∫_{t_r}^{t_{r+1}} ‖H(u) - H̃_r‖ du` is at most `ε / 8`. -/
theorem binary_time_simulation_mesh (D : Data (X × Fin M) n (Cfg (VW b)) s) (hM : 0 < M)
    (en : Cfg (Fin k) ≃ n) (σ : ℕ) (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ q, D.slot q = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (hb : 0 < b) (c0 : ℝ) (hc0 : 0 < c0) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z)
    (x : X) (hHerm : ∀ r, (D.matrix (x, r)).IsHermitian)
    (hrow : ∀ r i, ∑ j, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1)
    (hcol : ∀ r j, ∑ i, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1)
    (tm : ℕ → ℝ) (T γ ε ζ : ℝ) (hmesh : IsMesh tm M T) (hT : 0 < T) (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hCayley : TimeSchedule.steps (time (s : ℝ) T γ) (ε / 12) ≤ 2 ^ m)
    (hRound : 8 * M * time (s : ℝ) T γ ≤ ε * 2 ^ m)
    (hζε : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ binaryTimeSim k b m σ hσ s γ c0 T ε ζ, i.Valid) ∧
    (∀ p : Query → Bool, nCallsN p (binaryTimeSim k b m σ hσ s γ c0 T ε ζ) =
      12 * fDeg (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) *
        (2 * (if p Query.rowLocation then 1 else 0) +
          2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0))) ∧
    nGatesN (binaryTimeSim k b m σ hσ s γ c0 T ε ζ) ≤
      200 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) + 1) *
          (k + 1 + m + simR (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) + 1) +
        84 * fDeg (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) * (σ + 1) +
        6 * fDeg (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) *
          (2 * (28 * k) + 2 * (binArithT k b m (γ * Real.sqrt s * c0) ζ).circ.length +
            (2 * (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
              (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT + 1)) ∧
    Fintype.card (HW (Wire (k + 1) m
        (simR (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4))
        (k + 1 + m + 2 * simR (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4)))
        (Fin k) Empty (SZ k b) (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT
        (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP
        (binArithT k b m (γ * Real.sqrt s * c0) ζ).A) =
      k + (2 * (k + 1) + 3 * m +
          6 * simR (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) + 3) +
        (6 * k + 2 * b + (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT +
          (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
          (binArithT k b m (γ * Real.sqrt s * c0) ζ).A + 3) ∧
    (fDeg (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) : ℝ) ≤
      128 * (time (s : ℝ) T γ * moment γ + width (s : ℝ) γ * (1 + Real.log (12 / ε))) ∧
    2 * fDeg (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) + 2 ≤
      2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) ∧
    2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) ≤
      4 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) + 1) ∧
    (∀ (H : ℝ → Matrix n n ℂ) (U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R),
      (∀ᵐ u, u ∈ Icc 0 T → (H u).IsHermitian) →
      IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (H u)) volume 0 T →
      ∑ r : Fin M, ∫ u in tm r..tm ((r : ℕ) + 1),
          ‖SparseStateOverlap.matrixOperator (H u) -
            SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 8 →
      IsPropagator (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U T →
      ‖nrun (primsT (R := R) (clockData D hM tm T m) en x)
          (binaryTimeSim k b m σ hσ s γ c0 T ε ζ) ∘L sysEmb (io (P := Reg (Fin k) R)) -
        sysEmb (io (P := Reg (Fin k) R)) ∘L U T‖ ≤ ε) ∧
    (∀ (Hp : ℕ → ℝ → Matrix n n ℂ) (U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R),
      (∀ r < M, ∀ u ∈ Icc (tm r) (tm (r + 1)), (Hp r u).IsHermitian) →
      (∀ r < M, IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (Hp r u))
        volume (tm r) (tm (r + 1))) →
      ∑ r : Fin M, ∫ u in tm r..tm ((r : ℕ) + 1),
          ‖SparseStateOverlap.matrixOperator (Hp r u) -
            SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 8 →
      IsPiecewisePropagator
        (fun r u => qlift (R := R) en (SparseStateOverlap.matrixOperator (Hp r u))) tm M U →
      ‖nrun (primsT (R := R) (clockData D hM tm T m) en x)
          (binaryTimeSim k b m σ hσ s γ c0 T ε ζ) ∘L sysEmb (io (P := Reg (Fin k) R)) -
        sysEmb (io (P := Reg (Fin k) R)) ∘L U T‖ ≤ ε) := by
  have hs0 : 0 < s := D.slots_pos
  obtain ⟨hvalid, hcalls, hgates, hcard, hdeg, hr1, hr2, herr⟩ := binary_slot_bounds (R := R)
    (clockData D hM tm T m) en σ hσ hs hrange hb c0 hc0 hdec x (fun r => hHerm _)
    (fun r => hrow _) (fun r => hcol _) T γ ε ζ hT.le hγ hγ1 hε hε1 hζ hζ1 hCayley hζε
  -- the clock samples are the mesh samples of the slot pieces
  have hσ' : ∀ j, slotPiece tm T (2 ^ m) M j < M := fun j => slotPiece_lt hM j
  have hslot : slotEvolution (HsT (R := R) (clockData D hM tm T m) en x) T m =
      slotEvolution (fun j => meshSample (R := R) D en x (slotPiece tm T (2 ^ m) M j)) T m := by
    apply slotEvolution_congr
    intro j hj
    rw [HsT, dif_pos hj, meshSample, dif_pos (hσ' j)]
    rfl
  rw [hslot] at herr
  -- the mesh samples
  have hlift : ∀ r (hr : r < M), meshSample (R := R) D en x r =
      qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix (x, ⟨r, hr⟩))) := by
    intro r hr
    rw [meshSample, dif_pos hr]
  have hSelf : ∀ r < M, star (meshSample (R := R) D en x r) = meshSample (R := R) D en x r := by
    intro r hr
    rw [hlift r hr]
    exact (lifted_sample D en _ (hHerm _) (hrow _) (hcol _) γ hγ hγ1).2.1
  have hNorm : ∀ r < M, ‖meshSample (R := R) D en x r‖ ≤ Real.sqrt (s : ℝ) / γ := by
    intro r hr
    rw [hlift r hr]
    exact (lifted_sample D en _ (hHerm _) (hrow _) (hcol _) γ hγ hγ1).2.2
  have hround : (M : ℝ) * (T / 2 ^ m) * (Real.sqrt (s : ℝ) / γ) ≤ ε / 8 := by
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    have e : (M : ℝ) * (T / 2 ^ m) * (Real.sqrt (s : ℝ) / γ) = M * time (s : ℝ) T γ / 2 ^ m := by
      unfold time
      ring
    rw [e, div_le_iff₀ h2]
    linarith
  -- the certificate of the lifted path
  have hcertLift : ∀ (F : ℕ → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
      (∀ r < M, IntervalIntegrable (F r) volume (tm r) (tm (r + 1))) →
      ∑ r ∈ Finset.range M, ∫ u in tm r..tm (r + 1),
          ‖qlift (R := R) en (F r u) - meshSample (R := R) D en x r‖ ≤
        ∑ r : Fin M, ∫ u in tm r..tm ((r : ℕ) + 1),
          ‖F r u - SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ := by
    intro F hF
    rw [← Fin.sum_univ_eq_sum_range (fun r => ∫ u in tm r..tm (r + 1),
      ‖qlift (R := R) en (F r u) - meshSample (R := R) D en x r‖)]
    refine Finset.sum_le_sum fun r _ => ?_
    rw [hlift r r.isLt]
    exact lifted_integral_le (R := R) en _ (hmesh.mono (Nat.le_succ r)) (hF r r.isLt)
  refine ⟨hvalid, hcalls, hgates, hcard, hdeg, hr1, hr2, fun H U hH hint hcert hU => ?_,
    fun Hp U hH hint hcert hU => ?_⟩
  · have h1 := herr (U T)
    have hH' : ∀ᵐ u, u ∈ Icc 0 T →
        star (qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) =
          qlift (R := R) en (SparseStateOverlap.matrixOperator (H u)) := by
      filter_upwards [hH] with u hu hmem
      rw [← qlift_star, SparseValuePrecision.matrixOperator_star_eq _ (hu hmem)]
    have h2 := mesh_slot_error (meshSample (R := R) D en x) hM hmesh hT m hU hH' hSelf hNorm
      (intervalIntegrable_qlift (R := R) en hint)
    have h3 := hcertLift (fun _ u => SparseStateOverlap.matrixOperator (H u)) (fun r hr =>
      hint.mono_set (by
        rw [uIcc_of_le (hmesh.mono (Nat.le_succ r)), uIcc_of_le hT.le]
        exact Icc_subset_Icc (hmesh.nonneg r) (hmesh.le_last (by omega))))
    have h4 := (norm_sub_rev (slotEvolution (fun j => meshSample (R := R) D en x
      (slotPiece tm T (2 ^ m) M j)) T m) (U T)).trans_le h2
    linarith
  · have h1 := herr (U T)
    have h2 := mesh_slot_error_piecewise (meshSample (R := R) D en x) hM hmesh hT m hU
      (fun r hr u hu => by
        rw [← qlift_star, SparseValuePrecision.matrixOperator_star_eq _ (hH r hr u hu)])
      hSelf hNorm (fun r hr => intervalIntegrable_qlift (R := R) en (hint r hr))
    have h3 := hcertLift (fun r u => SparseStateOverlap.matrixOperator (Hp r u)) hint
    have h4 := (norm_sub_rev (slotEvolution (fun j => meshSample (R := R) D en x
      (slotPiece tm T (2 ^ m) M j)) T m) (U T)).trans_le h2
    linarith

end Main

universe u v w

/-- **The budget of the time-dependent binary construction on a nonuniform mesh** (Theorem
`hs:thm:gates`, time-dependent part, before finite-set synthesis, extended by uniform refinement
to nonuniform meshes with breakpoints, with the rescaled sparse parameters). The rescaling
`γ` of `binary_time_simulation_budget_certified` is chosen from `s`, `T` and `ε` before the mesh,
the data, the path and the slot exponent; for every mesh of `M ≥ 1` intervals with mesh data in
the released binary format, the subdivision condition, the rounding condition
`8 M τ' ≤ ε 2^m` (`τ' = √s T/γ`) and `221184 q ζ ≤ ε`, the circuit run on the clock data has at
most `55296 q` times `2 + 2 + 1` calls, at most `200 (4608 q + 1)(G_C + (σ+1) + (k+1) + m + r + 1)`
gates, `2^r ≤ 4 (4608 q + 1)`, and error `ε` against every integral-sense propagator of the lifted
path with mesh certificate at most `ε/8`. -/
theorem binary_time_simulation_budget_mesh (s : ℕ) (hs1 : 1 ≤ s) (T ε : ℝ) (hT : 0 < T)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt s ∧
      (fDeg (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) : ℝ) ≤
        4608 * ImprovedPrecisionBudget.shape s T (Real.log (2 / ε)) ∧
      ∀ {X : Type u} {n : Type v} [Fintype n] [DecidableEq n] {k b m M : ℕ} {R : Type w}
        [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
        (D : Data (X × Fin M) n (Cfg (VW b)) s) (hM : 0 < M) (en : Cfg (Fin k) ≃ n) (σ : ℕ)
        (hσ : σ ≤ k), s = 2 ^ σ →
        (∀ j : n, (∃ q, D.slot q = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u)) →
        0 < b → ∀ c0 : ℝ, 0 < c0 → (∀ e z, D.decode e z = (c0 : ℂ) * gauss z) →
        ∀ x : X, (∀ r, (D.matrix (x, r)).IsHermitian) →
        (∀ r i, ∑ j, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1) →
        (∀ r j, ∑ i, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1) →
        ∀ tm : ℕ → ℝ, IsMesh tm M T →
        TimeSchedule.steps (time (s : ℝ) T γ) (ε / 12) ≤ 2 ^ m →
        8 * M * time (s : ℝ) T γ ≤ ε * 2 ^ m →
        ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
        221184 * ImprovedPrecisionBudget.shape s T (Real.log (2 / ε)) * ζ ≤ ε →
        (∀ p : Query → Bool, (nCallsN p (binaryTimeSim k b m σ hσ s γ c0 T ε ζ) : ℝ) ≤
          55296 * ImprovedPrecisionBudget.shape s T (Real.log (2 / ε)) *
            (2 * (if p Query.rowLocation then 1 else 0) +
              2 * (if p Query.columnLocation then 1 else 0) +
              (if p Query.value then 1 else 0))) ∧
        (nGatesN (binaryTimeSim k b m σ hσ s γ c0 T ε ζ) : ℝ) ≤
          200 * (4608 * ImprovedPrecisionBudget.shape s T (Real.log (2 / ε)) + 1) *
            ((privGates (sparseOpT k b m (γ * Real.sqrt s * c0))
                (binArithT k b m (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) + m +
              simR (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) + 1) ∧
        ((2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) : ℕ) : ℝ) ≤
          4 * (4608 * ImprovedPrecisionBudget.shape s T (Real.log (2 / ε)) + 1) ∧
        ∀ (H : ℝ → Matrix n n ℂ) (U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R),
          (∀ᵐ u, u ∈ Icc 0 T → (H u).IsHermitian) →
          IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (H u)) volume 0 T →
          ∑ r : Fin M, ∫ u in tm r..tm ((r : ℕ) + 1),
              ‖SparseStateOverlap.matrixOperator (H u) -
                SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 8 →
          IsPropagator (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u)))
            U T →
          ‖nrun (primsT (R := R) (clockData D hM tm T m) en x)
              (binaryTimeSim k b m σ hσ s γ c0 T ε ζ) ∘L sysEmb (io (P := Reg (Fin k) R)) -
            sysEmb (io (P := Reg (Fin k) R)) ∘L U T‖ ≤ ε := by
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hall⟩ :=
    binary_time_simulation_budget_certified.{u, v, w} s hs1 T ε hT.le hε hε1
  refine ⟨γ, hγ, hγ1, hγs, hdeg, ?_⟩
  intro X n _ _ k b m M R _ _ _ D hM en σ hσ hs hrange hb c0 hc0 hdec x hHerm hrow hcol tm hmesh
    hCayley hRound ζ hζ hζ1 hζε
  have hζε' : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) T γ) (moment γ) (ε / 4) : ℝ) * ζ ≤
      ε := by
    nlinarith [hdeg, hζ]
  -- the counts do not depend on the data: those of the budget form for the clock data
  obtain ⟨hcalls, hgates, hr2, -⟩ := hall (R := R) (clockData D hM tm T m) en σ hσ hs hrange hb
    c0 hc0 hdec x (fun r => hHerm _) (fun r => hrow _) (fun r => hcol _) hCayley ζ hζ hζ1 hζε
  obtain ⟨-, -, -, -, -, -, -, herr, -⟩ := binary_time_simulation_mesh (R := R) D hM en σ hσ
    hs hrange hb c0 hc0 hdec x hHerm hrow hcol tm T γ ε ζ hmesh hT hγ hγ1 hε hε1 hζ hζ1 hCayley
    hRound hζε'
  exact ⟨hcalls, hgates, hr2, herr⟩

end

end SparseHamiltonian.GateMesh
