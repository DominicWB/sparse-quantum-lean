import GateEfficientMesh.ODE.Core
import GateEfficientMesh.Slots
import TimeDependentExtensions.ODE.Discretisation

/-!
# The discretised target under integrated certificates on the uniform slots

Theorem `ode:thm:gates`, time-dependent part ("a certificate for the same uniform meshes
suffices"). The exact target of the time-dependent gate-level ODE solver is the exponential
left-endpoint
recurrence `y_{r+1} = exp(-(T/2^m) G̃_r)(y_r + (T/2^m) b̃_r)` of the represented slot generators
`G̃_r = L_r + i H_r` and forcing samples `b̃_r` (`GateODE.Time.TParams.target`). The released
solver bounds its distance from the solution by the Lipschitz budget `discretisation`. Here the
generator and the forcing are classical piecewise paths with one piece `G_k`, `b_k` per slot
(accretive and interval integrable on the closed slot; one-sided derivatives at the slot
boundaries, as in `TimeDependentExtensions.ODE`), and the released mesh estimate
`TimeDependentExtensions.ODEMesh.mesh_error` with the energy bound
`TimeDependentExtensions.ODEMesh.piecewise_norm_le` gives (`slot_target_error`)

  `‖x(T) - y‖ ≤ (‖x(0)‖ + b_max T) ∑_k ∫_{slot k} ‖G_k - G̃_k‖
      + ∑_k ∫_{slot k} ‖b_k - b̃_k‖ + (λ_H + λ_D) (T/2^m)² / 2 · ∑_k ‖b̃_k‖`

(the integrated certificates of the generator and of the forcing, and the left-endpoint
quadrature). `slotCertificate` names the right-hand side.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateMesh.ODE

noncomputable section
open ContinuousLinearMap MeasureTheory Set
open GateODE.Time (TParams gens)
open TimeDependentODE (SolvesODE Accretive recurrence)
open TimeDependentExtensions.ODEMesh (meshRecurrence)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

omit [CompleteSpace P] in
/-- The scheme with constant steps is the released recurrence. -/
theorem meshRecurrence_const (Gs : ℕ → P →L[ℂ] P) (bs : ℕ → P) (h : ℝ) (y0 : P) (n : ℕ) :
    meshRecurrence Gs bs (fun _ => h) y0 n = recurrence Gs bs h y0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [TimeDependentExtensions.ODEMesh.meshRecurrence_succ, TimeDependentODE.recurrence_succ, ih]

/-- **The certified error on the uniform slots**: the integrated certificates of the generator
pieces `G_k` against the represented generators `L_k + i H_k` (weighted by the energy bound
`‖x(0)‖ + b_max T`) and of the forcing pieces `b_k` against the samples `b̃_k`, and the
left-endpoint quadrature `(λ_H + λ_D) (T/2^m)² / 2 · ∑_k ‖b̃_k‖`. -/
def slotCertificate (p : TParams) (Hs Ls : ℕ → P →L[ℂ] P) (bs : ℕ → P)
    (G : ℕ → ℝ → P →L[ℂ] P) (b : ℕ → ℝ → P) (r₀ bmax : ℝ) : ℝ :=
  (r₀ + bmax * p.T) * (∑ k ∈ Finset.range p.M,
      ∫ u in slotMesh p.T p.m k..slotMesh p.T p.m (k + 1), ‖G k u - gens Hs Ls k‖) +
    (∑ k ∈ Finset.range p.M,
      ∫ u in slotMesh p.T p.m k..slotMesh p.T p.m (k + 1), ‖b k u - bs k‖) +
    (p.lamH + p.lamD) * (p.T / p.M) ^ 2 / 2 * ∑ k ∈ Finset.range p.M, ‖bs k‖

/-- **The discretised target against a classical piecewise solution on the uniform slots.**
For accretive, interval-integrable generator pieces `G_k` and interval-integrable forcing pieces
`b_k` with `‖b_k‖ ≤ b_max` on the slots, and a solution of `x' = -G_k x + b_k` on every closed
slot, the discretised target of the represented samples is within the slot certificate of
`x(T)`. -/
theorem slot_target_error (p : TParams) (hT : 0 < p.T) (Hs Ls : ℕ → P →L[ℂ] P) (bs : ℕ → P)
    (G : ℕ → ℝ → P →L[ℂ] P) (b : ℕ → ℝ → P) (x : ℝ → P) (bmax : ℝ) (hbmax : 0 ≤ bmax)
    (hx : ∀ k < p.M, SolvesODE (G k) (b k) x (slotMesh p.T p.m k) (slotMesh p.T p.m (k + 1)))
    (hG : ∀ k < p.M, ∀ u ∈ Icc (slotMesh p.T p.m k) (slotMesh p.T p.m (k + 1)),
      Accretive (G k u))
    (hGint : ∀ k < p.M, IntervalIntegrable (G k) volume (slotMesh p.T p.m k)
      (slotMesh p.T p.m (k + 1)))
    (hbint : ∀ k < p.M, IntervalIntegrable (b k) volume (slotMesh p.T p.m k)
      (slotMesh p.T p.m (k + 1)))
    (hb : ∀ k < p.M, ∀ u ∈ Icc (slotMesh p.T p.m k) (slotMesh p.T p.m (k + 1)), ‖b k u‖ ≤ bmax)
    (hH : ∀ r < p.M, star (Hs r) = Hs r)
    (hPSD : ∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (Ls r w)).re)
    (hHn : ∀ r < p.M, ‖Hs r‖ ≤ p.lamH) (hLn : ∀ r < p.M, ‖Ls r‖ ≤ p.lamD) :
    ‖x p.T - p.target Hs Ls (x 0) bs‖ ≤ slotCertificate p Hs Ls bs G b ‖x 0‖ bmax := by
  have hmesh := isMesh_slotMesh hT.le p.m
  have hcl := GateCircuit.SlotSim.min_pred_lt p.M_pos
  have hGs : ∀ r, Accretive (GateCircuit.SlotSim.clampAt p.M (gens Hs Ls) r) := fun r =>
    GateODE.Time.slot_accretive _ _ (hH _ (hcl r)) (hPSD _ (hcl r))
  have hX := TimeDependentExtensions.ODEMesh.piecewise_norm_le hmesh hx hG bmax hbmax hb
  have hErr := TimeDependentExtensions.ODEMesh.mesh_error hmesh hx hGint hbint
    (GateCircuit.SlotSim.clampAt p.M (gens Hs Ls)) hGs (GateCircuit.SlotSim.clampAt p.M bs)
    (‖x 0‖ + bmax * p.T) hX
  have hstep : (fun r => slotMesh p.T p.m (r + 1) - slotMesh p.T p.m r) =
      fun _ => p.T / p.M := by
    funext r
    rw [slotMesh_succ_sub]
  have htarget : meshRecurrence (GateCircuit.SlotSim.clampAt p.M (gens Hs Ls))
      (GateCircuit.SlotSim.clampAt p.M bs)
      (fun r => slotMesh p.T p.m (r + 1) - slotMesh p.T p.m r) (x 0) p.M =
      p.target Hs Ls (x 0) bs := by
    rw [hstep, meshRecurrence_const]
    unfold TParams.target
    exact GateODE.Time.recurrence_congr _ _ _ _ _ _ _
      (fun r hr => GateCircuit.SlotSim.clampAt_of_lt _ _ hr)
      (fun r hr => GateCircuit.SlotSim.clampAt_of_lt _ _ hr)
  rw [htarget] at hErr
  refine hErr.trans ?_
  have hterm : ∀ r ∈ Finset.range p.M,
      (‖x 0‖ + bmax * p.T) * (∫ u in slotMesh p.T p.m r..slotMesh p.T p.m (r + 1),
          ‖G r u - GateCircuit.SlotSim.clampAt p.M (gens Hs Ls) r‖) +
        (∫ u in slotMesh p.T p.m r..slotMesh p.T p.m (r + 1),
          ‖b r u - GateCircuit.SlotSim.clampAt p.M bs r‖) +
        (slotMesh p.T p.m (r + 1) - slotMesh p.T p.m r) ^ 2 / 2 *
          (‖GateCircuit.SlotSim.clampAt p.M (gens Hs Ls) r‖ *
            ‖GateCircuit.SlotSim.clampAt p.M bs r‖) ≤
      (‖x 0‖ + bmax * p.T) * (∫ u in slotMesh p.T p.m r..slotMesh p.T p.m (r + 1),
          ‖G r u - gens Hs Ls r‖) +
        (∫ u in slotMesh p.T p.m r..slotMesh p.T p.m (r + 1), ‖b r u - bs r‖) +
        (p.lamH + p.lamD) * (p.T / p.M) ^ 2 / 2 * ‖bs r‖ := by
    intro r hr
    have hrM := Finset.mem_range.mp hr
    rw [GateCircuit.SlotSim.clampAt_of_lt _ _ hrM, GateCircuit.SlotSim.clampAt_of_lt _ _ hrM,
      slotMesh_succ_sub]
    have hgn : ‖gens Hs Ls r‖ ≤ p.lamH + p.lamD := by
      unfold gens
      calc ‖Ls r + Complex.I • Hs r‖ ≤ ‖Ls r‖ + ‖Complex.I • Hs r‖ := norm_add_le _ _
        _ ≤ p.lamD + p.lamH := by
            rw [norm_smul, Complex.norm_I, one_mul]
            exact add_le_add (hLn r hrM) (hHn r hrM)
        _ = p.lamH + p.lamD := add_comm _ _
    have hsq : 0 ≤ (p.T / ((2 ^ p.m : ℕ) : ℝ)) ^ 2 / 2 := by positivity
    have h3 : (p.T / ((2 ^ p.m : ℕ) : ℝ)) ^ 2 / 2 * (‖gens Hs Ls r‖ * ‖bs r‖) ≤
        (p.lamH + p.lamD) * (p.T / p.M) ^ 2 / 2 * ‖bs r‖ := by
      have e : (p.lamH + p.lamD) * (p.T / p.M) ^ 2 / 2 * ‖bs r‖ =
          (p.T / ((2 ^ p.m : ℕ) : ℝ)) ^ 2 / 2 * ((p.lamH + p.lamD) * ‖bs r‖) := by
        push_cast
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hgn (norm_nonneg _)) hsq
    linarith
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  unfold slotCertificate
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

end

end SparseHamiltonian.GateMesh.ODE
