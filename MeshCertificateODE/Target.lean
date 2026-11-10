import MeshCertificateODE.Errors
import RepresentedSampleODE.Gate.Certificate

/-!
# The discretised target of the time-dependent gate solver against the certificates

The time-dependent gate solver (`GateODE.Time`) runs on the uniform mesh `t_r = r T / M` of its
`M = 2^m` slots, with the source labels the initial state and the forcing samples `b_r` at the slot
times, weighted by the slot width `T / M` (`TParams.zsrc`). Its discretised target is the
exponential left-endpoint recurrence of the slot generators `G̃_r = L_r + i H_r`
(`TParams.target`). The manuscript's certificates (Theorem `ode:thm:gates`;
eq. `ode:eq:gate-source-certificates`) compare it with the exact propagator `U`
of the generator: the source certificate bounds `‖x(T) - U(T,0) x₀ - ∑_r w_r U(T, v_r) b(v_r)‖`, and
the sample certificate bounds the integrated sample error of the uniform mesh. Here:

* `umesh T M`: the uniform mesh; `maskedPropagator_eq_meshNodeProduct`: the masked propagator of a
  slot is the mesh product of its start time (`GeneralSourceExtensions.Mesh.meshNodeProduct`);
* `quadSum T M U x₀ b`: the propagated quadrature sum `U(T, 0) x₀ + ∑_r (T/M) U(T, t_r) b_r`;
* `quad_target_error`: for accretive slot generators, the discretised target is within
  `ΔG · B_m` of the quadrature sum, `ΔG = sampleErr` the integrated sample error of the slot
  generators against the generator pieces and `B_m` the source mass;
* `repLs`, `repLs_facts`, `sampleErr_repLs_le`: the positive repairs `repair L_r κ_r` of the
  dissipative samples with slot-dependent negativity bounds (`RepresentedSampleODE.repair`); the
  integrated sample error of the repaired generators is at most `ΔG + 2 Λ_κ`;
* `pathκ`: the path negativity bounds `κ_r = pathNeg` of the slots, with negativity mass the
  dissipative sample error `ΔD` (`negativity_pathκ`);
* `cert_target_facts`: from the source certificate `ζ B`, the target error `K B_m`, the mass
  condition `B_m ≤ c_q B`, the amplification bound `B ≤ ḡ ‖x(T)‖`, `c_q ḡ ≤ g` and the budget
  `ζ + c_q K ≤ ε / (2000 ḡ)`, the target is nonzero, `B_m ≤ 2 g ‖y‖` and its direction is within
  `ε / 1000` of that of `x(T)`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.MeshCertificateODE

noncomputable section
open ContinuousLinearMap Set MeasureTheory
open TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE recurrence maskedPropagator mask)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (meshWidth meshNodeProduct IsMeshPropagator
  node_error_nat meshScale)
open SparseHamiltonian.GateODE.Time (TParams gens)
open scoped BigOperators InnerProduct

/-! ### The uniform mesh -/

/-- **The uniform mesh** of `M` slots of `[0, T]`: `t_r = r T / M`. -/
def umesh (T : ℝ) (M : ℕ) : ℕ → ℝ := fun r => (r : ℝ) * T / M

theorem umesh_apply (T : ℝ) (M r : ℕ) : umesh T M r = (r : ℝ) * T / M := rfl

theorem umesh_succ_sub (T : ℝ) (M r : ℕ) : umesh T M (r + 1) - umesh T M r = T / M := by
  unfold umesh
  push_cast
  ring

theorem umesh_mono {T : ℝ} (hT : 0 ≤ T) (M : ℕ) : Monotone (umesh T M) := by
  intro a b hab
  unfold umesh
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hab' hT) (Nat.cast_nonneg M)

theorem isMesh_umesh {T : ℝ} {M : ℕ} (hT : 0 ≤ T) (hM : 0 < M) : IsMesh (umesh T M) M T where
  zero := by simp [umesh]
  last := by
    unfold umesh
    have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    field_simp
  mono := umesh_mono hT M

theorem umesh_mem {T : ℝ} {M : ℕ} (hT : 0 ≤ T) (hM : 0 < M) {q : ℕ} (hq : q ≤ M) :
    umesh T M q ∈ Icc 0 T := by
  have hmesh := isMesh_umesh hT hM
  exact ⟨hmesh.nonneg q, hmesh.le_last hq⟩

/-- On the uniform mesh the width of slot `r` after the slot time of `q` is `(T/M) mask q r`. -/
theorem meshWidth_umesh {T : ℝ} (hT : 0 ≤ T) (M q r : ℕ) :
    meshWidth (umesh T M q) (umesh T M) r = T / M * mask q r := by
  unfold meshWidth
  have hmono := umesh_mono hT M
  by_cases hqr : q ≤ r
  · rw [mask, if_pos hqr, mul_one, max_eq_right (hmono (hqr.trans (Nat.le_succ r))),
      max_eq_right (hmono hqr), umesh_succ_sub]
  · push Not at hqr
    rw [mask, if_neg (not_le.mpr hqr), mul_zero, max_eq_left (hmono (Nat.succ_le_of_lt hqr)),
      max_eq_left (hmono hqr.le), sub_self]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- **The masked propagator of a slot is the mesh product of its start time** on the uniform
mesh. -/
theorem maskedPropagator_eq_meshNodeProduct (Gs : ℕ → V →L[ℂ] V) {T : ℝ} (hT : 0 ≤ T)
    (M q : ℕ) :
    maskedPropagator Gs (T / M) q M = meshNodeProduct Gs (umesh T M) M (umesh T M q) := by
  unfold maskedPropagator meshNodeProduct
  congr 1
  funext r
  rw [meshWidth_umesh hT]

/-! ### The propagated quadrature sum and the discretised target -/

/-- **The propagated quadrature sum** of the slot nodes: `U(T, 0) x₀ + ∑_r (T/M) U(T, t_r) b_r`. -/
def quadSum (T : ℝ) (M : ℕ) (U : ℝ → V → ℝ → V) (x0 : V) (bs : ℕ → V) : V :=
  U 0 x0 T + ∑ r ∈ Finset.range M, (T / M) • U (umesh T M r) (bs r) T

set_option maxHeartbeats 1000000 in
/-- **One node**: the propagation of `w` from the slot time of `q ≤ M` against the masked
propagator of accretive slot generators, at most `ΔG ‖w‖`. -/
theorem quad_node_error {T : ℝ} (hT : 0 ≤ T) {M : ℕ} (hM : 0 < M) (Gs : ℕ → V →L[ℂ] V)
    (hacc : ∀ r < M, Accretive (Gs r)) (G : Fin M → ℝ → V →L[ℂ] V)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (umesh T M r) (umesh T M ((r : ℕ) + 1)), Accretive (G r u))
    (hGi : RepresentedSampleODE.RegularPieces (umesh T M) G) (U : ℝ → V → ℝ → V)
    (hU : IsMeshPropagator G (umesh T M) T U) {q : ℕ} (hq : q ≤ M) (w : V) :
    ‖U (umesh T M q) w T - maskedPropagator Gs (T / M) q M w‖ ≤
      sampleErr (umesh T M) G (fun r => Gs r) * ‖w‖ := by
  classical
  set t := umesh T M with ht
  have hmesh := isMesh_umesh hT hM
  let Gq : ℕ → ℝ → V →L[ℂ] V := fun r => if h : r < M then G ⟨r, h⟩ else 0
  have hGq : ∀ (r : ℕ) (h : r < M), Gq r = G ⟨r, h⟩ := fun r h => dif_pos h
  let Gc : ℕ → V →L[ℂ] V := GateCircuit.SlotSim.clampAt M Gs
  have hcl := GateCircuit.SlotSim.min_pred_lt hM
  have hGc : ∀ r, Accretive (Gc r) := fun r => hacc _ (hcl r)
  have hGcs : ∀ r < M, Gc r = Gs r := fun r hr => GateCircuit.SlotSim.clampAt_of_lt M Gs hr
  have ht₀ : t q ∈ Icc 0 T := umesh_mem hT hM hq
  obtain ⟨h0, hsol⟩ := hU (t q) ht₀ w
  have hNode := node_error_nat hmesh Gq
    (fun r hr u hu => by rw [hGq r hr]; exact hG ⟨r, hr⟩ u hu)
    (fun r hr => by rw [hGq r hr]; exact hGi ⟨r, hr⟩) Gc hGc ht₀ (U (t q) w)
    (fun r hr hst => by rw [hGq r hr]; exact hsol ⟨r, hr⟩ hst)
  rw [h0] at hNode
  have hprod : maskedPropagator Gs (T / M) q M = meshNodeProduct Gc t M (t q) := by
    rw [ht, ← maskedPropagator_eq_meshNodeProduct Gc hT M q]
    unfold maskedPropagator
    exact GateCircuit.SlotSim.evolution_eq_of_lt _ _ M (fun r hr => by rw [hGcs r hr])
  have hsum : ∑ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖Gq r u - Gc r‖ =
      sampleErr t G (fun r => Gs r) := by
    rw [← Fin.sum_univ_eq_sum_range (fun r => ∫ u in t r..t (r + 1), ‖Gq r u - Gc r‖) M]
    unfold sampleErr
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hGq r r.isLt, hGcs r r.isLt]
  rw [hprod, mul_comm]
  rw [hsum] at hNode
  exact hNode

/-- **The discretised target against the propagated quadrature sum**: for accretive slot
generators, `‖U(T, 0) x₀ + ∑_r (T/M) U(T, t_r) b_r - y‖ ≤ ΔG B_m`. -/
theorem quad_target_error (p : TParams) (hT : 0 ≤ p.T) (Hs Ls : ℕ → V →L[ℂ] V)
    (hacc : ∀ r < p.M, Accretive (gens Hs Ls r)) (G : Fin p.M → ℝ → V →L[ℂ] V)
    (hG : ∀ r : Fin p.M, ∀ u ∈ Icc (umesh p.T p.M r) (umesh p.T p.M ((r : ℕ) + 1)),
      Accretive (G r u))
    (hGi : RepresentedSampleODE.RegularPieces (umesh p.T p.M) G) (U : ℝ → V → ℝ → V)
    (hU : IsMeshPropagator G (umesh p.T p.M) p.T U) (x0 : V) (bs : ℕ → V) :
    ‖quadSum p.T p.M U x0 bs - p.target Hs Ls x0 bs‖ ≤
      sampleErr (umesh p.T p.M) G (fun r => gens Hs Ls r) * p.mass x0 bs := by
  set K := sampleErr (umesh p.T p.M) G (fun r => gens Hs Ls r) with hK
  have hnode := fun {q : ℕ} (hq : q ≤ p.M) (w : V) =>
    quad_node_error hT p.M_pos (gens Hs Ls) hacc G hG hGi U hU hq w
  have hK0 : 0 ≤ K := sampleErr_nonneg (isMesh_umesh hT p.M_pos) G _
  have htarget : p.target Hs Ls x0 bs = maskedPropagator (gens Hs Ls) (p.T / p.M) 0 p.M x0 +
      ∑ q ∈ Finset.range p.M,
        maskedPropagator (gens Hs Ls) (p.T / p.M) q p.M ((p.T / p.M) • bs q) := by
    unfold TParams.target
    exact TimeDependentODE.recurrence_eq_sum _ _ _ _ _
  have hsplit : quadSum p.T p.M U x0 bs - p.target Hs Ls x0 bs =
      (U (umesh p.T p.M 0) x0 p.T - maskedPropagator (gens Hs Ls) (p.T / p.M) 0 p.M x0) +
        ∑ q ∈ Finset.range p.M, (p.T / p.M) •
          (U (umesh p.T p.M q) (bs q) p.T -
            maskedPropagator (gens Hs Ls) (p.T / p.M) q p.M (bs q)) := by
    rw [htarget, quadSum]
    have e0 : umesh p.T p.M 0 = 0 := by simp [umesh]
    rw [e0]
    have e1 : ∀ q ∈ Finset.range p.M, (p.T / p.M) • (U (umesh p.T p.M q) (bs q) p.T -
        maskedPropagator (gens Hs Ls) (p.T / p.M) q p.M (bs q)) =
        (p.T / p.M) • U (umesh p.T p.M q) (bs q) p.T -
          maskedPropagator (gens Hs Ls) (p.T / p.M) q p.M ((p.T / p.M) • bs q) := by
      intro q _
      rw [smul_sub, map_smul_of_tower]
    rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib]
    abel
  have hh : 0 ≤ p.T / p.M := div_nonneg hT (Nat.cast_nonneg _)
  rw [hsplit, p.mass_eq hT]
  calc _ ≤ ‖U (umesh p.T p.M 0) x0 p.T - maskedPropagator (gens Hs Ls) (p.T / p.M) 0 p.M x0‖ +
        ∑ q ∈ Finset.range p.M, ‖(p.T / p.M) • (U (umesh p.T p.M q) (bs q) p.T -
          maskedPropagator (gens Hs Ls) (p.T / p.M) q p.M (bs q))‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ K * ‖x0‖ + ∑ q ∈ Finset.range p.M, p.T / p.M * (K * ‖bs q‖) := by
        refine add_le_add (hnode (Nat.zero_le _) x0) (Finset.sum_le_sum fun q hq => ?_)
        rw [norm_smul, Real.norm_of_nonneg hh]
        exact mul_le_mul_of_nonneg_left
          (hnode (Finset.mem_range.mp hq).le (bs q)) hh
    _ = K * (‖x0‖ + p.T / p.M * ∑ q ∈ Finset.range p.M, ‖bs q‖) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun q _ => ?_
        ring

/-! ### The repaired samples -/

/-- **The repaired dissipative samples** `repair L_r κ_r`, slot-dependent negativity bounds. -/
def repLs (Ls : ℕ → V →L[ℂ] V) (κ : ℕ → ℝ) (r : ℕ) : V →L[ℂ] V :=
  RepresentedSampleODE.repair (Ls r) (κ r)

/-- **The facts on the repaired samples**: on every slot they are self-adjoint, positive
semidefinite, no larger than `λ_D` and within `2 κ_r` of the samples. -/
theorem repLs_facts (p : TParams) (Ls : ℕ → V →L[ℂ] V) (κ : ℕ → ℝ) (hκ : ∀ r, 0 ≤ κ r)
    (hL : ∀ r < p.M, star (Ls r) = Ls r) (hLn : ∀ r < p.M, ‖Ls r‖ ≤ p.lamD)
    (hneg : ∀ r < p.M, ∀ w : V, -κ r * ‖w‖ ^ 2 ≤ (inner ℂ w (Ls r w)).re) :
    (∀ r < p.M, star (repLs Ls κ r) = repLs Ls κ r) ∧
    (∀ r < p.M, ∀ w : V, 0 ≤ (inner ℂ w (repLs Ls κ r w)).re) ∧
    (∀ r < p.M, ‖repLs Ls κ r‖ ≤ p.lamD) ∧
    (∀ r < p.M, ‖Ls r - repLs Ls κ r‖ ≤ 2 * κ r) :=
  ⟨fun r hr => RepresentedSampleODE.repair_selfAdjoint (Ls r) (hL r hr) (κ r),
    fun r hr w => RepresentedSampleODE.repair_nonneg (Ls r) (hκ r) (hneg r hr) w,
    fun r hr => (RepresentedSampleODE.norm_repair_le (Ls r) (hκ r)).trans (hLn r hr),
    fun r _ => by
      rw [norm_sub_rev]
      exact RepresentedSampleODE.norm_repair_sub_le (Ls r) (hκ r)⟩

omit [CompleteSpace V] in
/-- **The integrated sample error of the repaired generators** is at most `ΔG + 2 Λ_κ`. -/
theorem sampleErr_repLs_le {T : ℝ} (hT : 0 ≤ T) {M : ℕ} (hM : 0 < M) (Hs Ls : ℕ → V →L[ℂ] V)
    (κ : ℕ → ℝ) (hdiff : ∀ r < M, ‖Ls r - repLs Ls κ r‖ ≤ 2 * κ r)
    (G : Fin M → ℝ → V →L[ℂ] V) (hGi : RepresentedSampleODE.RegularPieces (umesh T M) G) :
    sampleErr (umesh T M) G (fun r => gens Hs (repLs Ls κ) r) ≤
      sampleErr (umesh T M) G (fun r => gens Hs Ls r) +
        2 * RepresentedSampleODE.negativity (umesh T M) (fun r : Fin M => κ r) := by
  have hmesh := isMesh_umesh hT hM
  unfold sampleErr RepresentedSampleODE.negativity
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun r _ => ?_
  have hgen : ‖gens Hs Ls r - gens Hs (repLs Ls κ) r‖ ≤ 2 * κ r := by
    have e : gens Hs Ls r - gens Hs (repLs Ls κ) r = Ls r - repLs Ls κ r := by
      simp only [gens]
      abel
    rw [e]
    exact hdiff r r.isLt
  refine (RepresentedSampleODE.integral_norm_sub_le (hmesh.mono (Nat.le_succ r)) (hGi r)
    (gens Hs Ls r) (gens Hs (repLs Ls κ) r)).trans ?_
  have := mul_le_mul_of_nonneg_left hgen (hmesh.length_nonneg r)
  linarith

/-- **The path negativity bounds of the slots**: `κ_r = pathNeg` of the slot generators against
the generator pieces (zero beyond the mesh). -/
def pathκ {M : ℕ} (T : ℝ) (G : Fin M → ℝ → V →L[ℂ] V) (Hs Ls : ℕ → V →L[ℂ] V) (r : ℕ) : ℝ :=
  if h : r < M then pathNeg (umesh T M) G (fun r => gens Hs Ls r) ⟨r, h⟩ else 0

theorem pathκ_nonneg {M : ℕ} {T : ℝ} (hT : 0 ≤ T) (hM : 0 < M) (G : Fin M → ℝ → V →L[ℂ] V)
    (Hs Ls : ℕ → V →L[ℂ] V) (r : ℕ) : 0 ≤ pathκ T G Hs Ls r := by
  unfold pathκ
  split_ifs with h
  · exact pathNeg_nonneg (isMesh_umesh hT hM) G _ _
  · exact le_rfl

/-- **The path negativity bounds are negativity bounds of the dissipative samples**, for accretive
integrable pieces and self-adjoint Hamiltonian samples. -/
theorem pathκ_bound {M : ℕ} {T : ℝ} (G : Fin M → ℝ → V →L[ℂ] V) (Hs Ls : ℕ → V →L[ℂ] V)
    (hH : ∀ r < M, star (Hs r) = Hs r)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (umesh T M r) (umesh T M ((r : ℕ) + 1)), Accretive (G r u))
    (hGi : RepresentedSampleODE.RegularPieces (umesh T M) G) {r : ℕ} (hr : r < M) (w : V) :
    -pathκ T G Hs Ls r * ‖w‖ ^ 2 ≤ (inner ℂ w (Ls r w)).re := by
  have h := pathNeg_bound G (fun r => gens Hs Ls r) hG hGi ⟨r, hr⟩ w
  unfold pathκ
  rw [dif_pos hr]
  rw [RepresentedSampleODE.GateTime.re_inner_gens Hs Ls r (hH r hr) w] at h
  exact h

/-- The negativity mass of the path bounds is the dissipative sample error. -/
theorem negativity_pathκ {M : ℕ} {T : ℝ} (hT : 0 ≤ T) (hM : 0 < M) (G : Fin M → ℝ → V →L[ℂ] V)
    (Hs Ls : ℕ → V →L[ℂ] V) :
    RepresentedSampleODE.negativity (umesh T M) (fun r : Fin M => pathκ T G Hs Ls r) =
      dissErr (umesh T M) G (fun r => gens Hs Ls r) := by
  rw [← negativity_pathNeg (isMesh_umesh hT hM) G (fun r => gens Hs Ls r)]
  unfold RepresentedSampleODE.negativity
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [pathκ, r.isLt]

/-! ### The target facts -/

/-- **The target facts from the certificates.** For the source certificate
`‖x(T) - S‖ ≤ ζ B`, a target `y` within `K B_m` of the quadrature sum `S`, the mass condition
`B_m ≤ c_q B`, the amplification bound `B ≤ ḡ ‖x(T)‖`, `c_q ḡ ≤ g` and the budget
`ζ + c_q K ≤ ε / (2000 ḡ)`: the target is nonzero, `B_m ≤ 2 g ‖y‖` and its direction is within
`ε / 1000` of that of `x(T)`. -/
theorem cert_target_facts {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (xT S y : E)
    {B Bm K ζ cq gb g ε : ℝ} (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) (hx : xT ≠ 0)
    (hB0 : 0 ≤ B) (hgb : 0 < gb) (hcq : 0 ≤ cq) (hK : 0 ≤ K) (hsrc : ‖xT - S‖ ≤ ζ * B)
    (herr : ‖S - y‖ ≤ K * Bm) (hmass : Bm ≤ cq * B) (hscale : B ≤ gb * ‖xT‖)
    (hratio : cq * gb ≤ g) (hbudget : ζ + cq * K ≤ ε / (2000 * gb)) :
    y ≠ 0 ∧ Bm ≤ 2 * g * ‖y‖ ∧
      ‖ODEStateNormalization.unitDirection y - ODEStateNormalization.unitDirection xT‖ ≤
        ε / 1000 := by
  have hg0 : 0 < g := by linarith
  have hxN : 0 ≤ ‖xT‖ := norm_nonneg _
  have hErr : ‖xT - y‖ ≤ ε * ‖xT‖ / 2000 := by
    have h1 : ‖xT - y‖ ≤ ζ * B + K * Bm :=
      (norm_sub_le_norm_sub_add_norm_sub xT S y).trans (add_le_add hsrc herr)
    have h2 : K * Bm ≤ K * (cq * B) := mul_le_mul_of_nonneg_left hmass hK
    have h3 : (ζ + cq * K) * B ≤ ε / (2000 * gb) * B := mul_le_mul_of_nonneg_right hbudget hB0
    have h4 : ε / (2000 * gb) * B ≤ ε / (2000 * gb) * (gb * ‖xT‖) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    have h5 : ε / (2000 * gb) * (gb * ‖xT‖) = ε * ‖xT‖ / 2000 := by
      rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by norm_num)]
      ring
    linarith
  obtain ⟨hy, hhalf, hdir⟩ := TimeDependentODE.Sampling.target_budget xT y (g * ‖xT‖) g ε
    (ε * ‖xT‖ / 2000) hg hε hεOne hx le_rfl hErr (le_of_eq (by
      rw [div_eq_div_iff (by norm_num) (by positivity)]
      ring))
  refine ⟨hy, ?_, hdir⟩
  have h6 : Bm ≤ cq * (gb * ‖xT‖) := hmass.trans (mul_le_mul_of_nonneg_left hscale hcq)
  have h7 : cq * (gb * ‖xT‖) ≤ g * ‖xT‖ := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hratio hxN
  linarith

end

end SparseHamiltonian.MeshCertificateODE
