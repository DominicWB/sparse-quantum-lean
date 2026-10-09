import GateEfficientMesh.ODE.MeshScheme

/-!
# The discretised target on a nonuniform mesh

Theorem `ode:thm:gates`, time-dependent part, extended by uniform refinement to nonuniform
meshes with breakpoints. A mesh `0 = t_0 ≤ ⋯ ≤ t_M = T` (`M` intervals, breakpoints at the mesh
points) carries one represented generator `G̃_q = L_q + i H_q` and one forcing sample `b̃_q` per
interval. The gate-level solver runs on its uniform clock of `2^m` slots of length `h = T/2^m`;
slot `k` uses the samples of the interval `σ k = slotPiece k` containing `k T/2^m` (generator
and forcing samples per slot from the containing interval). The generator and the forcing are
classical piecewise paths with one piece per mesh interval (accretive, interval integrable,
bounded forcing), and the solution solves each piece on its closed interval (one-sided
derivatives at the breakpoints).

`mesh_target_error` bounds the distance of the discretised target of the slot data from `x(T)`
by `meshCertificate`:

  `(‖x(0)‖ + b_max T) ∑_q ∫_{t_q}^{t_{q+1}} ‖G_q - G̃_q‖ + ∑_q ∫_{t_q}^{t_{q+1}} ‖b_q - b̃_q‖
    + ∑_q (Λ (Δ_q + h)² + h) ‖b̃_q‖ + M h Λ (‖x(0)‖ + ∑_q Δ_q ‖b̃_q‖)`,

`Λ = λ_H + λ_D`: the integrated certificates of the generator and of the forcing on the mesh
(the released `TimeDependentExtensions.ODEMesh.mesh_error`), the left-endpoint quadrature on the
mesh, and the cost of the refinement into slots (`slot_mesh_recurrence`: the rounding of the
interval lengths to multiples of `h`, the per-slot forcing and the refined propagators).
`meshCertificate_le` separates the refinement cost, which is `O(h) = O(2^{-m})`.

The comparison goes through the mesh scheme, so the left-endpoint quadrature of the mesh is kept
and does not decrease with `m`: for one interval and data equal to the samples the certificate
contains `Λ (T + h)² ‖b̃‖`, against `Λ T h ‖b̃‖ / 2` in `slotCertificate` on the uniform slots
(`meshCertificate_one_interval`, `slotCertificate_samples`, module `NonVacuity`). Inserting
breakpoints decreases it; a direct comparison of the slot scheme with the solution is not
formalised.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateMesh.ODE

noncomputable section
open ContinuousLinearMap MeasureTheory Set
open GateODE.Time (TParams gens)
open TimeDependentODE (SolvesODE Accretive recurrence)
open TimeDependentExtensions (IsMesh slotPiece slotPiece_lt blockLength)
open TimeDependentExtensions.ODEMesh (meshRecurrence)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **The certified error on a mesh** of `Mm` intervals refined into the `2^m` slots of `p`:
the integrated certificates of the generator pieces `G_q` against `L_q + i H_q` (weighted by the
energy bound `r₀ + b_max T`) and of the forcing pieces `b_q` against `b̃_q`, the left-endpoint
quadrature on the mesh and the refinement into slots of length `h = T/2^m`,
`∑_q (Λ (Δ_q + h)² + h) ‖b̃_q‖ + Mm h Λ (r₀ + ∑_q Δ_q ‖b̃_q‖)`, `Λ = λ_H + λ_D`. The quadrature
term of the mesh, at most `2 Λ ∑_q Δ_q² ‖b̃_q‖` up to `O(h)` (`meshCertificate_le`), does not
decrease with `m`. -/
def meshCertificate (p : TParams) (tm : ℕ → ℝ) (Mm : ℕ) (Hm Lm : ℕ → P →L[ℂ] P) (bm : ℕ → P)
    (G : ℕ → ℝ → P →L[ℂ] P) (b : ℕ → ℝ → P) (r₀ bmax : ℝ) : ℝ :=
  (r₀ + bmax * p.T) * (∑ q ∈ Finset.range Mm, ∫ u in tm q..tm (q + 1), ‖G q u - gens Hm Lm q‖) +
    (∑ q ∈ Finset.range Mm, ∫ u in tm q..tm (q + 1), ‖b q u - bm q‖) +
    ∑ q ∈ Finset.range Mm,
      ((p.lamH + p.lamD) * (tm (q + 1) - tm q + p.T / p.M) ^ 2 + p.T / p.M) * ‖bm q‖ +
    Mm * (p.T / p.M) * (p.lamH + p.lamD) *
      (r₀ + ∑ q ∈ Finset.range Mm, (tm (q + 1) - tm q) * ‖bm q‖)

omit [CompleteSpace P] in
/-- **The refinement cost is `O(2^{-m})`.** The mesh certificate is at most the integrated
certificates, the left-endpoint quadrature `2 Λ ∑_q Δ_q² ‖b̃_q‖` on the mesh, and
`h ((2 Λ T + 1) ∑_q ‖b̃_q‖ + Mm Λ (r₀ + ∑_q Δ_q ‖b̃_q‖))` with `h = T/2^m`: every slot exponent
`m` for which the last term fits in the remaining budget is admissible. -/
theorem meshCertificate_le (p : TParams) (hT : 0 < p.T) (hlam : 0 ≤ p.lamH + p.lamD)
    (tm : ℕ → ℝ) (Mm : ℕ) (Hm Lm : ℕ → P →L[ℂ] P) (bm : ℕ → P) (G : ℕ → ℝ → P →L[ℂ] P)
    (b : ℕ → ℝ → P) (r₀ bmax : ℝ) :
    meshCertificate p tm Mm Hm Lm bm G b r₀ bmax ≤
      (r₀ + bmax * p.T) *
          (∑ q ∈ Finset.range Mm, ∫ u in tm q..tm (q + 1), ‖G q u - gens Hm Lm q‖) +
        (∑ q ∈ Finset.range Mm, ∫ u in tm q..tm (q + 1), ‖b q u - bm q‖) +
        2 * (p.lamH + p.lamD) * ∑ q ∈ Finset.range Mm, (tm (q + 1) - tm q) ^ 2 * ‖bm q‖ +
        p.T / p.M * ((2 * (p.lamH + p.lamD) * p.T + 1) * ∑ q ∈ Finset.range Mm, ‖bm q‖ +
          Mm * (p.lamH + p.lamD) *
            (r₀ + ∑ q ∈ Finset.range Mm, (tm (q + 1) - tm q) * ‖bm q‖)) := by
  have hNR : (1 : ℝ) ≤ p.M := by exact_mod_cast p.M_pos
  set Λ := p.lamH + p.lamD with hΛdef
  set h := p.T / (p.M : ℝ) with hhdef
  have hh0 : 0 ≤ h := div_nonneg hT.le (by linarith)
  have hhT : h ≤ p.T := div_le_self hT.le hNR
  have hterm : ∀ q ∈ Finset.range Mm,
      (Λ * (tm (q + 1) - tm q + h) ^ 2 + h) * ‖bm q‖ ≤
        2 * Λ * ((tm (q + 1) - tm q) ^ 2 * ‖bm q‖) + h * ((2 * Λ * p.T + 1) * ‖bm q‖) := by
    intro q _
    have hb0 := norm_nonneg (bm q)
    have h1 : (tm (q + 1) - tm q + h) ^ 2 ≤ 2 * (tm (q + 1) - tm q) ^ 2 + 2 * h ^ 2 := by
      nlinarith [sq_nonneg (tm (q + 1) - tm q - h)]
    have h2 : h ^ 2 ≤ h * p.T := by nlinarith
    have h3 : Λ * (tm (q + 1) - tm q + h) ^ 2 ≤
        2 * Λ * (tm (q + 1) - tm q) ^ 2 + 2 * Λ * (h * p.T) := by
      have := mul_le_mul_of_nonneg_left h1 hlam
      have := mul_le_mul_of_nonneg_left h2 hlam
      nlinarith
    have h4 := mul_le_mul_of_nonneg_right (add_le_add_right h3 h) hb0
    nlinarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  unfold meshCertificate
  rw [← hΛdef, ← hhdef]
  nlinarith [hsum]

/-- **The discretised target of the slot data against a classical piecewise solution on a
nonuniform mesh.** -/
theorem mesh_target_error (p : TParams) (hT : 0 < p.T) (hlam : 0 ≤ p.lamH + p.lamD)
    (tm : ℕ → ℝ) (Mm : ℕ) (hMm : 0 < Mm) (hmesh : IsMesh tm Mm p.T)
    (Hm Lm : ℕ → P →L[ℂ] P) (bm : ℕ → P) (hH : ∀ q < Mm, star (Hm q) = Hm q)
    (hPSD : ∀ q < Mm, ∀ w : P, 0 ≤ (inner ℂ w (Lm q w)).re)
    (hHn : ∀ q < Mm, ‖Hm q‖ ≤ p.lamH) (hLn : ∀ q < Mm, ‖Lm q‖ ≤ p.lamD)
    (G : ℕ → ℝ → P →L[ℂ] P) (b : ℕ → ℝ → P) (x : ℝ → P) (bmax : ℝ) (hbmax : 0 ≤ bmax)
    (hx : ∀ q < Mm, SolvesODE (G q) (b q) x (tm q) (tm (q + 1)))
    (hG : ∀ q < Mm, ∀ u ∈ Icc (tm q) (tm (q + 1)), Accretive (G q u))
    (hGint : ∀ q < Mm, IntervalIntegrable (G q) volume (tm q) (tm (q + 1)))
    (hbint : ∀ q < Mm, IntervalIntegrable (b q) volume (tm q) (tm (q + 1)))
    (hb : ∀ q < Mm, ∀ u ∈ Icc (tm q) (tm (q + 1)), ‖b q u‖ ≤ bmax) :
    ‖x p.T - p.target (fun k => Hm (slotPiece tm p.T p.M Mm k))
        (fun k => Lm (slotPiece tm p.T p.M Mm k)) (x 0)
        (fun k => bm (slotPiece tm p.T p.M Mm k))‖ ≤
      meshCertificate p tm Mm Hm Lm bm G b ‖x 0‖ bmax := by
  have hcl := GateCircuit.SlotSim.min_pred_lt hMm
  have hN : 0 < p.M := p.M_pos
  have hNR : (0 : ℝ) < p.M := by exact_mod_cast hN
  have hh : 0 ≤ p.T / p.M := (div_pos hT hNR).le
  set Gm : ℕ → P →L[ℂ] P := GateCircuit.SlotSim.clampAt Mm (gens Hm Lm) with hGmdef
  set bm' : ℕ → P := GateCircuit.SlotSim.clampAt Mm bm with hbmdef
  have hgn : ∀ q < Mm, ‖gens Hm Lm q‖ ≤ p.lamH + p.lamD := by
    intro q hq
    unfold gens
    calc ‖Lm q + Complex.I • Hm q‖ ≤ ‖Lm q‖ + ‖Complex.I • Hm q‖ := norm_add_le _ _
      _ ≤ p.lamD + p.lamH := by
          rw [norm_smul, Complex.norm_I, one_mul]
          exact add_le_add (hLn q hq) (hHn q hq)
      _ = p.lamH + p.lamD := add_comm _ _
  have hGm : ∀ r, Accretive (Gm r) := fun r =>
    GateODE.Time.slot_accretive _ _ (hH _ (hcl r)) (hPSD _ (hcl r))
  have hGmn : ∀ r, ‖Gm r‖ ≤ p.lamH + p.lamD := fun r => hgn _ (hcl r)
  have hX := TimeDependentExtensions.ODEMesh.piecewise_norm_le hmesh hx hG bmax hbmax hb
  have hErr1 := TimeDependentExtensions.ODEMesh.mesh_error hmesh hx hGint hbint Gm hGm bm'
    (‖x 0‖ + bmax * p.T) hX
  have hErr2 := slot_mesh_recurrence Gm bm' hGm hGmn hmesh hT hN hMm (x 0)
  have hσ : ∀ k, slotPiece tm p.T p.M Mm k < Mm := fun k => slotPiece_lt hMm k
  have htarget : p.target (fun k => Hm (slotPiece tm p.T p.M Mm k))
      (fun k => Lm (slotPiece tm p.T p.M Mm k)) (x 0)
      (fun k => bm (slotPiece tm p.T p.M Mm k)) =
      recurrence (fun k => Gm (slotPiece tm p.T p.M Mm k))
        (fun k => bm' (slotPiece tm p.T p.M Mm k)) (p.T / p.M) (x 0) p.M := by
    unfold TParams.target
    congr 1
    · funext k
      simp only [hGmdef, GateCircuit.SlotSim.clampAt_of_lt _ _ (hσ k)]
      rfl
    · funext k
      simp only [hbmdef, GateCircuit.SlotSim.clampAt_of_lt _ _ (hσ k)]
  rw [htarget]
  set Λ := p.lamH + p.lamD with hΛdef
  set h := p.T / (p.M : ℝ) with hhdef
  -- the per-interval bound
  have hterm : ∀ q ∈ Finset.range Mm,
      ((‖x 0‖ + bmax * p.T) * (∫ u in tm q..tm (q + 1), ‖G q u - Gm q‖) +
          (∫ u in tm q..tm (q + 1), ‖b q u - bm' q‖) +
          (tm (q + 1) - tm q) ^ 2 / 2 * (‖Gm q‖ * ‖bm' q‖)) +
        (Λ * ((blockLength tm p.T p.M q : ℝ) * h) ^ 2 / 2 +
          |(blockLength tm p.T p.M q : ℝ) * h - (tm (q + 1) - tm q)| +
          (tm (q + 1) - tm q) * (Mm * h * Λ)) * ‖bm' q‖ ≤
      (‖x 0‖ + bmax * p.T) * (∫ u in tm q..tm (q + 1), ‖G q u - gens Hm Lm q‖) +
        (∫ u in tm q..tm (q + 1), ‖b q u - bm q‖) +
        (Λ * (tm (q + 1) - tm q + h) ^ 2 + h) * ‖bm q‖ +
        (tm (q + 1) - tm q) * (Mm * h * Λ) * ‖bm q‖ := by
    intro q hq
    have hqM := Finset.mem_range.mp hq
    have e1 : Gm q = gens Hm Lm q := GateCircuit.SlotSim.clampAt_of_lt _ _ hqM
    have e2 : bm' q = bm q := GateCircuit.SlotSim.clampAt_of_lt _ _ hqM
    rw [e1, e2]
    have hΔ := hmesh.length_nonneg q
    have habs := TimeDependentExtensions.blockLength_sub_lt hmesh hT hN q
    rw [abs_lt] at habs
    have hn0 : 0 ≤ (blockLength tm p.T p.M q : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh
    have hb0 := norm_nonneg (bm q)
    have hgq := hgn q hqM
    have hsq1 : ((blockLength tm p.T p.M q : ℝ) * h) ^ 2 ≤ (tm (q + 1) - tm q + h) ^ 2 := by
      apply pow_le_pow_left₀ hn0
      linarith
    have hsq2 : (tm (q + 1) - tm q) ^ 2 ≤ (tm (q + 1) - tm q + h) ^ 2 :=
      pow_le_pow_left₀ hΔ (by linarith) 2
    have habs' : |(blockLength tm p.T p.M q : ℝ) * h - (tm (q + 1) - tm q)| ≤ h := by
      rw [abs_le]
      constructor <;> linarith
    have hq1 : (tm (q + 1) - tm q) ^ 2 / 2 * (‖gens Hm Lm q‖ * ‖bm q‖) ≤
        Λ * (tm (q + 1) - tm q + h) ^ 2 / 2 * ‖bm q‖ := by
      have h1 : (tm (q + 1) - tm q) ^ 2 / 2 * (‖gens Hm Lm q‖ * ‖bm q‖) ≤
          (tm (q + 1) - tm q) ^ 2 / 2 * (Λ * ‖bm q‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hgq hb0) (by positivity)
      have h2 : (tm (q + 1) - tm q) ^ 2 * (Λ * ‖bm q‖) ≤
          (tm (q + 1) - tm q + h) ^ 2 * (Λ * ‖bm q‖) :=
        mul_le_mul_of_nonneg_right hsq2 (mul_nonneg hlam hb0)
      linarith
    have hq2 : Λ * ((blockLength tm p.T p.M q : ℝ) * h) ^ 2 / 2 * ‖bm q‖ ≤
        Λ * (tm (q + 1) - tm q + h) ^ 2 / 2 * ‖bm q‖ := by
      have := mul_le_mul_of_nonneg_left hsq1 hlam
      nlinarith
    have hq3 : |(blockLength tm p.T p.M q : ℝ) * h - (tm (q + 1) - tm q)| * ‖bm q‖ ≤ h * ‖bm q‖ :=
      mul_le_mul_of_nonneg_right habs' hb0
    nlinarith [hq1, hq2, hq3]
  have hsum := Finset.sum_le_sum hterm
  simp only [Finset.sum_add_distrib] at hsum hErr1
  have s1 : (‖x 0‖ + bmax * p.T) *
      (∑ q ∈ Finset.range Mm, ∫ u in tm q..tm (q + 1), ‖G q u - gens Hm Lm q‖) =
      ∑ q ∈ Finset.range Mm, (‖x 0‖ + bmax * p.T) *
        ∫ u in tm q..tm (q + 1), ‖G q u - gens Hm Lm q‖ := Finset.mul_sum _ _ _
  have s4 : (Mm : ℝ) * h * Λ * ∑ q ∈ Finset.range Mm, (tm (q + 1) - tm q) * ‖bm q‖ =
      ∑ q ∈ Finset.range Mm, (tm (q + 1) - tm q) * (Mm * h * Λ) * ‖bm q‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  calc _ ≤ ‖x p.T - meshRecurrence Gm bm' (fun r => tm (r + 1) - tm r) (x 0) Mm‖ +
        ‖meshRecurrence Gm bm' (fun r => tm (r + 1) - tm r) (x 0) Mm -
          recurrence (fun k => Gm (slotPiece tm p.T p.M Mm k))
            (fun k => bm' (slotPiece tm p.T p.M Mm k)) (p.T / p.M) (x 0) p.M‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
        rw [norm_sub_rev (meshRecurrence _ _ _ _ _)]
        unfold meshCertificate
        rw [← hΛdef, ← hhdef]
        linarith [hErr1, hErr2, hsum, s1, s4]

end

end SparseHamiltonian.GateMesh.ODE
