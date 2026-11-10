import GateEfficientTimeDependent.SlotError
import TimeDependentExtensions.Mesh.Duhamel
import IntegrablePathSimulation.Propagator.Released

/-!
# Uniform slots, slot products and integrated sample-error certificates

The gate-level circuits of the package extension combining Theorem `hs:thm:time` with the circuit
of Theorem `hs:thm:gates` run on a uniform clock of `2^m` slots of length `t / 2^m` (`slotMesh`).
Their ideal output is the ordered product of the slot exponentials (`slotEvolution`):

  `∏_k exp(-i (t / 2^m) H̃_k)`.

The paragraphs after the proof of Theorem `hs:thm:time` state that for an integrable Hermitian path
a certified bound on the sum of the integrated sample errors
`∑_r ∫_{t_r}^{t_{r+1}} ‖H(u) - H̃_r‖ du` suffices. This module bounds the distance of the slot
product from every propagator by that certificate:

* uniform slots (`slot_error_integral` for integral-sense propagators of interval-integrable
  paths, `slot_error_piecewise` for classical piecewise propagators with one piece per slot,
  one-sided derivatives at the slot boundaries);
* a nonuniform mesh `0 = t_0 ≤ ⋯ ≤ t_M = T` with breakpoints, refined into the `2^m` slots
  with the slot-to-sample map `slotPiece` (`mesh_slot_error`, `mesh_slot_error_piecewise`):
  the certificate plus the refinement rounding `M (T / 2^m) Λ` for samples of norm at most
  `Λ`.

The hypotheses are satisfiable: piecewise constant paths `H(u) = H̃_k` on slot `k` have a
piecewise propagator and certificate `0` (`exists_slot_propagator`), and a `β`-Lipschitz path
with sample errors `δ` at the slot points has certificate at most `β t² / (2 · 2^m) + t δ`
(`slot_certificate_le_of_lipschitz`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateMesh

noncomputable section

open ContinuousLinearMap MeasureTheory Set
open TimeDependentExtensions (IsMesh meshEvolution refinedEvolution slotPiece slotPiece_lt
  IsPiecewisePropagator)
open IntegrablePathSimulation.Propagator (IsPropagator)
open scoped BigOperators

/-! ### The uniform clock -/

/-- The uniform mesh of `2^m` slots of `[0, t]`: slot `k` is `[k t / 2^m, (k + 1) t / 2^m]`. -/
def slotMesh (t : ℝ) (m : ℕ) (k : ℕ) : ℝ := (k : ℝ) * t / 2 ^ m

/-- Every slot has length `t / 2^m`. -/
theorem slotMesh_succ_sub (t : ℝ) (m k : ℕ) :
    slotMesh t m (k + 1) - slotMesh t m k = t / ((2 ^ m : ℕ) : ℝ) := by
  unfold slotMesh
  push_cast
  ring

/-- The uniform slots form a mesh of `[0, t]`. -/
theorem isMesh_slotMesh {t : ℝ} (ht : 0 ≤ t) (m : ℕ) : IsMesh (slotMesh t m) (2 ^ m) t where
  zero := by simp [slotMesh]
  last := by
    unfold slotMesh
    push_cast
    field_simp
  mono := by
    intro k k' hkk'
    unfold slotMesh
    have hk : (k : ℝ) ≤ k' := by exact_mod_cast hkk'
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hk ht) h2.le

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The ordered product `exp(-i (t/2^m) H̃_{2^m - 1}) ⋯ exp(-i (t/2^m) H̃_0)` of the slot
exponentials of the samples `H̃_k`. -/
def slotEvolution (Hs : ℕ → P →L[ℂ] P) (t : ℝ) (m : ℕ) : P →L[ℂ] P :=
  TimeDependent.evolution (fun k => NormedSpace.exp
    ((-Complex.I * ((t / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) • Hs k)) (2 ^ m)

omit [CompleteSpace P] in
/-- The slot product depends only on the samples of the `2^m` slots. -/
theorem slotEvolution_congr (Hs Hs' : ℕ → P →L[ℂ] P) (t : ℝ) (m : ℕ)
    (h : ∀ k < 2 ^ m, Hs k = Hs' k) : slotEvolution Hs t m = slotEvolution Hs' t m :=
  GateCircuit.SlotSim.evolution_eq_of_lt _ _ _ (fun k hk => by rw [h k hk])

omit [CompleteSpace P] in
/-- On the uniform slots the mesh product of the samples is the slot product. -/
theorem meshEvolution_slotMesh (Hs : ℕ → P →L[ℂ] P) (t : ℝ) (m : ℕ) :
    meshEvolution Hs (slotMesh t m) (2 ^ m) = slotEvolution Hs t m := by
  unfold meshEvolution slotEvolution
  congr 1
  funext k
  rw [slotMesh_succ_sub]

omit [CompleteSpace P] in
/-- The refined product of a mesh on `2^m` slots is the slot product of the samples read
through the slot-to-sample map. -/
theorem refinedEvolution_eq_slotEvolution (A : ℕ → P →L[ℂ] P) (tm : ℕ → ℝ) (T : ℝ)
    (m M : ℕ) :
    refinedEvolution A tm T (2 ^ m) M =
      slotEvolution (fun k => A (slotPiece tm T (2 ^ m) M k)) T m := rfl

/-! ### Certificates on the uniform slots -/

/-- **The integrated certificate on the uniform slots, integral-sense propagators.** For a
path that is self-adjoint at almost every time of `[0, t]` and interval integrable, every
propagator (`IsPropagator`) is within `∑_k ∫_{slot k} ‖H(u) - H̃_k‖ du` of the slot product. -/
theorem slot_error_integral {H U : ℝ → P →L[ℂ] P} (Hs : ℕ → P →L[ℂ] P) {t : ℝ} (ht : 0 ≤ t)
    (m : ℕ) (hU : IsPropagator H U t) (hH : ∀ᵐ u, u ∈ Icc 0 t → star (H u) = H u)
    (hHs : ∀ k < 2 ^ m, star (Hs k) = Hs k) (hint : IntervalIntegrable H volume 0 t) :
    ‖U t - slotEvolution Hs t m‖ ≤
      ∑ k ∈ Finset.range (2 ^ m), ∫ u in slotMesh t m k..slotMesh t m (k + 1), ‖H u - Hs k‖ := by
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  have h := hU.mesh_error_integral (GateCircuit.SlotSim.clampAt (2 ^ m) Hs)
    (isMesh_slotMesh ht m) hH (fun k => hHs _ (GateCircuit.SlotSim.min_pred_lt hpos k)) hint
  rw [meshEvolution_slotMesh, slotEvolution_congr _ Hs t m
    (fun k hk => GateCircuit.SlotSim.clampAt_of_lt _ _ hk)] at h
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_))
  rw [GateCircuit.SlotSim.clampAt_of_lt _ _ (Finset.mem_range.mp hk)]

/-- **The integrated certificate on the uniform slots, classical piecewise propagators** with
one piece per slot (one-sided derivatives at the slot boundaries). -/
theorem slot_error_piecewise {Hp : ℕ → ℝ → P →L[ℂ] P} {U : ℝ → P →L[ℂ] P}
    (Hs : ℕ → P →L[ℂ] P) {t : ℝ} (ht : 0 ≤ t) (m : ℕ)
    (hU : IsPiecewisePropagator Hp (slotMesh t m) (2 ^ m) U)
    (hH : ∀ k < 2 ^ m, ∀ u ∈ Icc (slotMesh t m k) (slotMesh t m (k + 1)),
      star (Hp k u) = Hp k u)
    (hHs : ∀ k < 2 ^ m, star (Hs k) = Hs k)
    (hint : ∀ k < 2 ^ m, IntervalIntegrable (Hp k) volume (slotMesh t m k)
      (slotMesh t m (k + 1))) :
    ‖U t - slotEvolution Hs t m‖ ≤
      ∑ k ∈ Finset.range (2 ^ m),
        ∫ u in slotMesh t m k..slotMesh t m (k + 1), ‖Hp k u - Hs k‖ := by
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  have h := TimeDependentExtensions.mesh_error_integral (GateCircuit.SlotSim.clampAt (2 ^ m) Hs)
    (isMesh_slotMesh ht m) hU hH (fun k => hHs _ (GateCircuit.SlotSim.min_pred_lt hpos k)) hint
  rw [meshEvolution_slotMesh, slotEvolution_congr _ Hs t m
    (fun k hk => GateCircuit.SlotSim.clampAt_of_lt _ _ hk)] at h
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_))
  rw [GateCircuit.SlotSim.clampAt_of_lt _ _ (Finset.mem_range.mp hk)]

/-! ### Certificates on a nonuniform mesh -/

/-- The rounding cost `M (T/2^m) Λ` with the natural-number power cast to the reals. -/
theorem mul_div_two_pow (M : ℕ) (T Λ : ℝ) (m : ℕ) :
    (M : ℝ) * (T / ((2 ^ m : ℕ) : ℝ)) * Λ = M * (T / 2 ^ m) * Λ := by
  push_cast
  ring

/-- **The mesh certificate and the refinement, integral-sense propagators.** For a mesh
`0 = t_0 ≤ ⋯ ≤ t_M = T` with breakpoints, samples `H̃_r` of norm at most `Λ` and slot `k` of
the `2^m` slots reading the sample of the interval containing `k T / 2^m`, every propagator of
an interval-integrable path that is self-adjoint almost everywhere is within
`∑_r ∫_{t_r}^{t_{r+1}} ‖H(u) - H̃_r‖ du + M (T / 2^m) Λ` of the slot product. -/
theorem mesh_slot_error {H U : ℝ → P →L[ℂ] P} (Hs : ℕ → P →L[ℂ] P) {tm : ℕ → ℝ} {M : ℕ}
    {T : ℝ} (hM : 0 < M) (hmesh : IsMesh tm M T) (hT : 0 < T) (m : ℕ)
    (hU : IsPropagator H U T) (hH : ∀ᵐ u, u ∈ Icc 0 T → star (H u) = H u)
    (hHs : ∀ r < M, star (Hs r) = Hs r) {Λ : ℝ} (hΛ : ∀ r < M, ‖Hs r‖ ≤ Λ)
    (hint : IntervalIntegrable H volume 0 T) :
    ‖U T - slotEvolution (fun k => Hs (slotPiece tm T (2 ^ m) M k)) T m‖ ≤
      (∑ r ∈ Finset.range M, ∫ u in tm r..tm (r + 1), ‖H u - Hs r‖) + M * (T / 2 ^ m) * Λ := by
  have h := hU.refined_error (N := 2 ^ m) (GateCircuit.SlotSim.clampAt M Hs) hmesh hT
    (Nat.two_pow_pos m) hH (fun r => hHs _ (GateCircuit.SlotSim.min_pred_lt hM r))
    (fun r => hΛ _ (GateCircuit.SlotSim.min_pred_lt hM r)) hint
  rw [refinedEvolution_eq_slotEvolution, mul_div_two_pow] at h
  have e1 : slotEvolution (fun k => GateCircuit.SlotSim.clampAt M Hs (slotPiece tm T (2 ^ m) M k))
      T m = slotEvolution (fun k => Hs (slotPiece tm T (2 ^ m) M k)) T m := by
    congr 1
    funext k
    exact GateCircuit.SlotSim.clampAt_of_lt _ _ (slotPiece_lt hM k)
  have e2 : ∑ r ∈ Finset.range M, ∫ u in tm r..tm (r + 1),
      ‖H u - GateCircuit.SlotSim.clampAt M Hs r‖ =
      ∑ r ∈ Finset.range M, ∫ u in tm r..tm (r + 1), ‖H u - Hs r‖ :=
    Finset.sum_congr rfl fun r hr => by
      rw [GateCircuit.SlotSim.clampAt_of_lt _ _ (Finset.mem_range.mp hr)]
  rw [e1, e2] at h
  exact h

/-- **The mesh certificate and the refinement, classical piecewise propagators** with one
piece per mesh interval (one-sided derivatives at the breakpoints). -/
theorem mesh_slot_error_piecewise {Hp : ℕ → ℝ → P →L[ℂ] P} {U : ℝ → P →L[ℂ] P}
    (Hs : ℕ → P →L[ℂ] P) {tm : ℕ → ℝ} {M : ℕ} {T : ℝ} (hM : 0 < M) (hmesh : IsMesh tm M T)
    (hT : 0 < T) (m : ℕ) (hU : IsPiecewisePropagator Hp tm M U)
    (hH : ∀ r < M, ∀ u ∈ Icc (tm r) (tm (r + 1)), star (Hp r u) = Hp r u)
    (hHs : ∀ r < M, star (Hs r) = Hs r) {Λ : ℝ} (hΛ : ∀ r < M, ‖Hs r‖ ≤ Λ)
    (hint : ∀ r < M, IntervalIntegrable (Hp r) volume (tm r) (tm (r + 1))) :
    ‖U T - slotEvolution (fun k => Hs (slotPiece tm T (2 ^ m) M k)) T m‖ ≤
      (∑ r ∈ Finset.range M, ∫ u in tm r..tm (r + 1), ‖Hp r u - Hs r‖) +
        M * (T / 2 ^ m) * Λ := by
  have h := TimeDependentExtensions.refined_error (N := 2 ^ m)
    (GateCircuit.SlotSim.clampAt M Hs) hmesh hT (Nat.two_pow_pos m) hU hH
    (fun r => hHs _ (GateCircuit.SlotSim.min_pred_lt hM r))
    (fun r => hΛ _ (GateCircuit.SlotSim.min_pred_lt hM r)) hint
  rw [refinedEvolution_eq_slotEvolution, mul_div_two_pow] at h
  have e1 : slotEvolution (fun k => GateCircuit.SlotSim.clampAt M Hs (slotPiece tm T (2 ^ m) M k))
      T m = slotEvolution (fun k => Hs (slotPiece tm T (2 ^ m) M k)) T m := by
    congr 1
    funext k
    exact GateCircuit.SlotSim.clampAt_of_lt _ _ (slotPiece_lt hM k)
  have e2 : ∑ r ∈ Finset.range M, ∫ u in tm r..tm (r + 1),
      ‖Hp r u - GateCircuit.SlotSim.clampAt M Hs r‖ =
      ∑ r ∈ Finset.range M, ∫ u in tm r..tm (r + 1), ‖Hp r u - Hs r‖ :=
    Finset.sum_congr rfl fun r hr => by
      rw [GateCircuit.SlotSim.clampAt_of_lt _ _ (Finset.mem_range.mp hr)]
  rw [e1, e2] at h
  exact h

/-! ### Satisfiability -/

/-- **Piecewise constant paths.** The path equal to `H̃_k` on slot `k` has a piecewise
propagator (for any samples), and its certificate on the uniform slots is `0`. -/
theorem exists_slot_propagator (Hs : ℕ → P →L[ℂ] P) {t : ℝ} (ht : 0 ≤ t) (m : ℕ)
    (Hp : ℕ → ℝ → P →L[ℂ] P) (hHp : ∀ k u, Hp k u = Hs k) :
    (∃ U : ℝ → P →L[ℂ] P, IsPiecewisePropagator Hp (slotMesh t m) (2 ^ m) U) ∧
      ∑ k ∈ Finset.range (2 ^ m),
        ∫ u in slotMesh t m k..slotMesh t m (k + 1), ‖Hp k u - Hs k‖ = 0 := by
  obtain rfl : Hp = fun k _ => Hs k := funext fun k => funext fun u => hHp k u
  refine ⟨TimeDependentExtensions.exists_piecewise_propagator _ (isMesh_slotMesh ht m).zero
    (isMesh_slotMesh ht m).mono _ (fun k _ => continuousOn_const), ?_⟩
  simp

omit [InnerProductSpace ℂ P] [CompleteSpace P] in
/-- **Lipschitz paths.** A `β`-Lipschitz path on `[0, t]` whose values at the slot points
`k t / 2^m` are within `δ` of the samples has certificate at most `β t² / (2 · 2^m) + t δ` on
the uniform slots. -/
theorem slot_certificate_le_of_lipschitz (H : ℝ → P) (Hs : ℕ → P) {t β δ : ℝ} (ht : 0 ≤ t)
    (m : ℕ) (hLip : ∀ u ∈ Icc 0 t, ∀ v ∈ Icc 0 t, ‖H u - H v‖ ≤ β * |u - v|)
    (hVal : ∀ k < 2 ^ m, ‖H (slotMesh t m k) - Hs k‖ ≤ δ) :
    ∑ k ∈ Finset.range (2 ^ m), ∫ u in slotMesh t m k..slotMesh t m (k + 1), ‖H u - Hs k‖ ≤
      β * t ^ 2 / (2 * 2 ^ m) + t * δ := by
  have hmesh := isMesh_slotMesh ht m
  have hstep : ∀ k ∈ Finset.range (2 ^ m),
      ∫ u in slotMesh t m k..slotMesh t m (k + 1), ‖H u - Hs k‖ ≤
        β * (t / 2 ^ m) ^ 2 / 2 + δ * (t / 2 ^ m) := by
    intro k hk
    have hkM := Finset.mem_range.mp hk
    have h0 : 0 ≤ slotMesh t m k := hmesh.nonneg k
    have h1 : slotMesh t m k ≤ slotMesh t m (k + 1) := hmesh.mono (Nat.le_succ k)
    have h2 : slotMesh t m (k + 1) ≤ t := hmesh.le_last (by omega)
    have hsub : Icc (slotMesh t m k) (slotMesh t m (k + 1)) ⊆ Icc 0 t :=
      Icc_subset_Icc h0 h2
    have h := TimeDependentExtensions.integral_le_of_lipschitz' H (Hs k) h1
      (fun u hu v hv => hLip u (hsub hu) v (hsub hv)) (hVal k hkM)
    have e : slotMesh t m (k + 1) - slotMesh t m k = t / 2 ^ m := by
      rw [slotMesh_succ_sub]
      push_cast
      ring
    rw [e] at h
    exact h
  refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  field_simp

end

end SparseHamiltonian.GateMesh
