import GeneralSourceExtensions.Mesh.Durations
import GeneralSourceODE.Duhamel

/-!
# Duhamel's formula on a mesh

For accretive pieces `G_r` on the mesh intervals, the homogeneous piecewise solutions from a start
time are unique (`SolvesFrom.unique`), contractive (`SolvesFrom.norm_le`) and linear in the
initial value; hence a propagator on the mesh (`IsMeshPropagator`) satisfies the cocycle law
across the mesh points (`IsMeshPropagator.cocycle`) and `w ↦ U(T, c) w` is a contraction
(`endMap`). On each interval, the single-path Duhamel formula of `GeneralSourceODE.duhamel`
applies to the piece, and the cocycle law carries it to the final time. Summing over the
intervals, for continuous pieces and forcing pieces and every piecewise solution,

  `∑_r ∫_{t_r}^{t_{r+1}} U(T, v) b_r(v) dv = x(T) - U(T, 0) x(0)`   (`mesh_duhamel`).

This identifies the manuscript's certificate on the propagated vector integral with the
certificate on the propagated source sum used by the mesh endpoints.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralSourceExtensions.Mesh

noncomputable section
open ContinuousLinearMap Set MeasureTheory
open TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE)
open scoped BigOperators InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {t : ℕ → ℝ} {M : ℕ} {T : ℝ}

/-- **Induction along the mesh** from a start time `t₀`: a property at `t₀` that propagates over
the part of every interval after `t₀` holds on `[t₀, T]`. -/
theorem mesh_induction (hmesh : IsMesh t M T) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T) (P : ℝ → Prop)
    (h0 : P t₀)
    (hstep : ∀ r : Fin M, t₀ ≤ t ((r : ℕ) + 1) → P (max t₀ (t r)) →
      ∀ u ∈ Icc (max t₀ (t r)) (t ((r : ℕ) + 1)), P u) :
    ∀ u ∈ Icc t₀ T, P u := by
  have key : ∀ m ≤ M, ∀ u ∈ Icc t₀ (max t₀ (t m)), P u := by
    intro m
    induction m with
    | zero =>
        intro _ u hu
        rw [hmesh.zero, max_eq_left ht₀.1] at hu
        rw [le_antisymm hu.2 hu.1]
        exact h0
    | succ m ih =>
        intro hm u hu
        have hmM : m < M := by omega
        by_cases hum : u ≤ max t₀ (t m)
        · exact ih hmM.le u ⟨hu.1, hum⟩
        · push Not at hum
          have hst : t₀ ≤ t (m + 1) := by
            by_contra hlt
            push Not at hlt
            have h1 : max t₀ (t (m + 1)) = t₀ := max_eq_left hlt.le
            have h2 := hu.2
            rw [h1] at h2
            linarith [le_max_left t₀ (t m)]
          have hc : max t₀ (t (m + 1)) = t (m + 1) := max_eq_right hst
          have hP : P (max t₀ (t m)) := ih hmM.le _ ⟨le_max_left _ _, le_rfl⟩
          have hu2 : u ≤ t (m + 1) := hc ▸ hu.2
          exact hstep ⟨m, hmM⟩ hst hP u ⟨hum.le, hu2⟩
  intro u hu
  have h := key M le_rfl u
  rw [hmesh.last, max_eq_right ht₀.2] at h
  exact h hu

/-- Homogeneous piecewise solutions from the start time `t₀`. -/
def SolvesFrom (G : Fin M → ℝ → V →L[ℂ] V) (t : ℕ → ℝ) (t₀ : ℝ) (y : ℝ → V) : Prop :=
  ∀ r : Fin M, t₀ ≤ t ((r : ℕ) + 1) → SolvesODE (G r) 0 y (max t₀ (t r)) (t ((r : ℕ) + 1))

variable {G : Fin M → ℝ → V →L[ℂ] V}

theorem accretive_after (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (t₀ : ℝ) (r : Fin M) :
    ∀ u ∈ Icc (max t₀ (t r)) (t ((r : ℕ) + 1)), Accretive (G r u) :=
  fun u hu => hG r u ⟨(le_max_right _ _).trans hu.1, hu.2⟩

/-- Uniqueness of homogeneous piecewise solutions. -/
theorem SolvesFrom.unique (hmesh : IsMesh t M T)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T) {y₁ y₂ : ℝ → V} (h₁ : SolvesFrom G t t₀ y₁)
    (h₂ : SolvesFrom G t t₀ y₂) (h : y₁ t₀ = y₂ t₀) : ∀ u ∈ Icc t₀ T, y₁ u = y₂ u :=
  mesh_induction hmesh ht₀ (fun u => y₁ u = y₂ u) h fun r hst hP u hu =>
    GeneralSourceODE.homogeneous_unique (h₁ r hst) (h₂ r hst) (accretive_after hG t₀ r) hP u hu

/-- Homogeneous piecewise solutions do not grow. -/
theorem SolvesFrom.norm_le (hmesh : IsMesh t M T)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T) {y : ℝ → V} (h : SolvesFrom G t t₀ y) :
    ∀ u ∈ Icc t₀ T, ‖y u‖ ≤ ‖y t₀‖ :=
  mesh_induction hmesh ht₀ (fun u => ‖y u‖ ≤ ‖y t₀‖) le_rfl fun r hst hP u hu =>
    (GeneralSourceODE.homogeneous_norm_le (h r hst) (accretive_after hG t₀ r) u hu).trans hP

/-- A solution from `t₀` is a solution from every later start time. -/
theorem SolvesFrom.mono {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁) {y : ℝ → V} (h : SolvesFrom G t t₀ y) :
    SolvesFrom G t t₁ y :=
  fun r hst => (h r (h01.trans hst)).mono (max_le_max h01 le_rfl) le_rfl

/-- Linear combinations of homogeneous piecewise solutions. -/
theorem SolvesFrom.lincomb {t₀ : ℝ} {y₁ y₂ : ℝ → V} (h₁ : SolvesFrom G t t₀ y₁)
    (h₂ : SolvesFrom G t t₀ y₂) (k : ℂ) : SolvesFrom G t t₀ (fun u => y₁ u - k • y₂ u) := by
  intro r hst
  have hs := GeneralSourceODE.solvesODE_smul (h₂ r hst) k
  have hd := GeneralSourceODE.solvesODE_sub (h₁ r hst) hs
  have h0 : (fun u => (0 : ℝ → V) u - (fun u => k • (0 : ℝ → V) u) u) = 0 := by
    funext u
    simp
  rwa [h0] at hd

variable {U : ℝ → V → ℝ → V}

/-- Linear combinations of propagated vectors on a mesh. -/
theorem IsMeshPropagator.lincomb (hmesh : IsMesh t M T) (hU : IsMeshPropagator G t T U)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T) (w₁ w₂ : V) (k : ℂ) :
    ∀ u ∈ Icc t₀ T, U t₀ w₁ u - k • U t₀ w₂ u = U t₀ (w₁ - k • w₂) u := by
  apply SolvesFrom.unique hmesh hG ht₀ (SolvesFrom.lincomb (hU t₀ ht₀ w₁).2 (hU t₀ ht₀ w₂).2 k)
    (hU t₀ ht₀ (w₁ - k • w₂)).2
  rw [(hU t₀ ht₀ w₁).1, (hU t₀ ht₀ w₂).1, (hU t₀ ht₀ (w₁ - k • w₂)).1]

/-- Propagated vectors on a mesh do not grow. -/
theorem IsMeshPropagator.norm_le (hmesh : IsMesh t M T) (hU : IsMeshPropagator G t T U)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T) (w : V) : ∀ u ∈ Icc t₀ T, ‖U t₀ w u‖ ≤ ‖w‖ := by
  intro u hu
  have h := SolvesFrom.norm_le hmesh hG ht₀ (hU t₀ ht₀ w).2 u hu
  rwa [(hU t₀ ht₀ w).1] at h

/-- **The cocycle law across the mesh points**: `U(u, t₀) = U(u, t₁) U(t₁, t₀)`. -/
theorem IsMeshPropagator.cocycle (hmesh : IsMesh t M T) (hU : IsMeshPropagator G t T U)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    {t₀ t₁ : ℝ} (ht₀ : t₀ ∈ Icc 0 T) (h01 : t₀ ≤ t₁) (ht₁ : t₁ ≤ T) (w : V) :
    ∀ u ∈ Icc t₁ T, U t₀ w u = U t₁ (U t₀ w t₁) u := by
  have ht₁' : t₁ ∈ Icc 0 T := ⟨ht₀.1.trans h01, ht₁⟩
  exact SolvesFrom.unique hmesh hG ht₁' (SolvesFrom.mono h01 (hU t₀ ht₀ w).2) (hU t₁ ht₁' _).2
    (hU t₁ ht₁' _).1.symm

theorem IsMeshPropagator.map_zero (hmesh : IsMesh t M T) (hU : IsMeshPropagator G t T U)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T) : ∀ u ∈ Icc t₀ T, U t₀ 0 u = 0 := by
  intro u hu
  have h := hU.lincomb hmesh hG ht₀ 0 0 1 u hu
  rw [one_smul, sub_self, one_smul, sub_self] at h
  exact h.symm

variable [CompleteSpace V]

/-- The propagation from `c` to the final time as a contraction. -/
def endMap (hmesh : IsMesh t M T) (hU : IsMeshPropagator G t T U)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    {c : ℝ} (hc : c ∈ Icc 0 T) : V →L[ℂ] V :=
  LinearMap.mkContinuous
    { toFun := fun w => U c w T
      map_add' := fun w₁ w₂ => by
        have h := hU.lincomb hmesh hG hc w₁ w₂ (-1) T ⟨hc.2, le_rfl⟩
        simp only [neg_one_smul, sub_neg_eq_add] at h
        exact h.symm
      map_smul' := fun k w => by
        have h := hU.lincomb hmesh hG hc 0 w (-k) T ⟨hc.2, le_rfl⟩
        rw [hU.map_zero hmesh hG hc T ⟨hc.2, le_rfl⟩, zero_sub, zero_sub, neg_smul, neg_neg,
          neg_smul, neg_neg] at h
        exact h.symm }
    1 (fun w => by
      rw [one_mul]
      exact hU.norm_le hmesh hG hc w T ⟨hc.2, le_rfl⟩)

omit [CompleteSpace V] in
theorem endMap_apply (hmesh : IsMesh t M T) (hU : IsMeshPropagator G t T U)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    {c : ℝ} (hc : c ∈ Icc 0 T) (w : V) : endMap hmesh hU hG hc w = U c w T := rfl

omit [CompleteSpace V] in
/-- Shifting a solution in time. -/
theorem solvesODE_shift_forward {G' : ℝ → V →L[ℂ] V} {b x : ℝ → V} {a c : ℝ}
    (hx : SolvesODE G' b x a c) (d : ℝ) :
    SolvesODE (fun u => G' (u + d)) (fun u => b (u + d)) (fun u => x (u + d)) (a - d)
      (c - d) := by
  intro v hv
  have hmaps : MapsTo (fun v : ℝ => v + d) (Icc (a - d) (c - d)) (Icc a c) := fun w hw =>
    ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hg : HasDerivWithinAt (fun v : ℝ => v + d) 1 (Icc (a - d) (c - d)) v :=
    ((hasDerivAt_id' v).add_const d).hasDerivWithinAt
  have h := (hx (v + d) (hmaps hv)).scomp v hg hmaps
  simpa only [one_smul, Function.comp_def] using h

set_option maxHeartbeats 1000000 in
/-- **Duhamel's formula on one interval**, carried to the final time. -/
theorem piece_duhamel (hmesh : IsMesh t M T) (hU : IsMeshPropagator G t T U)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGc : ∀ r : Fin M, ContinuousOn (G r) (Icc (t r) (t ((r : ℕ) + 1))))
    (b : Fin M → ℝ → V) (hbc : ∀ r : Fin M, ContinuousOn (b r) (Icc (t r) (t ((r : ℕ) + 1))))
    (sol : ℝ → V) (hsol : ∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1)))
    (r : Fin M) :
    ∫ v in t r..t ((r : ℕ) + 1), U v (b r v) T =
      U (t ((r : ℕ) + 1)) (sol (t ((r : ℕ) + 1))) T - U (t r) (sol (t r)) T := by
  set a := t r with ha
  set c := t ((r : ℕ) + 1) with hc
  have hac : a ≤ c := hmesh.mono (Nat.le_succ r)
  have ha0 : 0 ≤ a := hmesh.nonneg r
  have hcT : c ≤ T := hmesh.le_last (Nat.succ_le_of_lt r.isLt)
  have haI : a ∈ Icc 0 T := ⟨ha0, hac.trans hcT⟩
  have hcI : c ∈ Icc 0 T := ⟨ha0.trans hac, hcT⟩
  set Δ := c - a with hΔ
  have hΔ0 : 0 ≤ Δ := sub_nonneg.mpr hac
  have hΔa : Δ + a = c := by rw [hΔ, sub_add_cancel]
  -- The shifted single-path problem.
  let G' : ℝ → V →L[ℂ] V := fun u => G r (u + a)
  let b' : ℝ → V := fun u => b r (u + a)
  let sol' : ℝ → V := fun u => sol (u + a)
  let U' : ℝ → V → ℝ → V := fun s w u => U (s + a) w (u + a)
  have hmapsI : MapsTo (fun u : ℝ => u + a) (Icc 0 Δ) (Icc a c) := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hU' : GeneralSourceODE.IsPropagator G' U' Δ := by
    intro s hs w
    have hst : s + a ∈ Icc a c := hmapsI hs
    have hstI : s + a ∈ Icc 0 T := ⟨ha0.trans hst.1, hst.2.trans hcT⟩
    obtain ⟨h0, hsolU⟩ := hU (s + a) hstI w
    have h1 := hsolU r hst.2
    rw [← ha, ← hc, max_eq_left hst.1] at h1
    have h2 := solvesODE_shift_forward h1 a
    rw [add_sub_cancel_right, ← hΔ] at h2
    refine ⟨h2, ?_⟩
    exact h0
  have hG' : ∀ u ∈ Icc 0 Δ, Accretive (G' u) := fun u hu => hG r (u + a) (hmapsI hu)
  obtain ⟨Λ, hΛ⟩ := isCompact_Icc.exists_bound_of_continuousOn (hGc r)
  have hΛ' : ∀ u ∈ Icc 0 Δ, ‖G' u‖ ≤ Λ := fun u hu => hΛ (u + a) (hmapsI hu)
  have hbc' : ContinuousOn b' (Icc 0 Δ) :=
    (hbc r).comp (continuous_add_const a).continuousOn hmapsI
  have hsol' : SolvesODE G' b' sol' 0 Δ := by
    have h := solvesODE_shift_forward (hsol r) a
    rw [← ha, ← hc, sub_self, ← hΔ] at h
    exact h
  have hD := GeneralSourceODE.duhamel hΔ0 hU' hG' Λ hΛ' hbc' hsol'
  -- Back to the interval `[a, c]`.
  have hD' : ∫ v in a..c, U v (b r v) c = sol c - U a (sol a) c := by
    have hcomp := intervalIntegral.integral_comp_add_right (fun v => U v (b r v) c) a
      (a := 0) (b := Δ)
    rw [zero_add, hΔa] at hcomp
    rw [← hcomp]
    have hrw : (∫ x in (0 : ℝ)..Δ, U (x + a) (b r (x + a)) c) =
        ∫ s in (0 : ℝ)..Δ, U' s (b' s) Δ := by
      simp only [U', b', hΔa]
    rw [hrw, hD]
    simp only [sol', U', zero_add, hΔa]
  -- Carry the identity to the final time.
  obtain ⟨bmax, hbmax⟩ := isCompact_Icc.exists_bound_of_continuousOn hbc'
  have hcont' := GeneralSourceODE.forcing_continuousOn hU' hG' Λ hΛ' hbc' bmax hbmax
  have hcont : ContinuousOn (fun v => U v (b r v) c) (Icc a c) := by
    have hmaps : MapsTo (fun v : ℝ => v - a) (Icc a c) (Icc 0 Δ) := fun v hv =>
      ⟨by linarith [hv.1], by linarith [hv.2]⟩
    refine (hcont'.comp (continuous_sub_right a).continuousOn hmaps).congr fun v _ => ?_
    simp only [Function.comp_apply, U', b', sub_add_cancel, hΔa]
  have hint : IntervalIntegrable (fun v => U v (b r v) c) volume a c :=
    hcont.intervalIntegrable_of_Icc hac
  have hcoc : ∀ v ∈ uIcc a c, U v (b r v) T = endMap hmesh hU hG hcI (U v (b r v) c) := by
    intro v hv
    rw [uIcc_of_le hac] at hv
    rw [endMap_apply]
    exact hU.cocycle hmesh hG ⟨ha0.trans hv.1, hv.2.trans hcT⟩ hv.2 hcT _ T ⟨hcT, le_rfl⟩
  rw [intervalIntegral.integral_congr hcoc,
    ContinuousLinearMap.intervalIntegral_comp_comm _ hint, hD', map_sub, endMap_apply,
    endMap_apply]
  congr 1
  exact (hU.cocycle hmesh hG haI hac hcT _ T ⟨hcT, le_rfl⟩).symm

set_option maxHeartbeats 1000000 in
/-- **Duhamel's formula on a mesh.** For accretive continuous pieces, continuous forcing pieces,
a propagator `U` on the mesh and every piecewise solution,
`∑_r ∫_{t_r}^{t_{r+1}} U(T, v) b_r(v) dv = x(T) - U(T, 0) x(0)`. -/
theorem mesh_duhamel (hmesh : IsMesh t M T) (hU : IsMeshPropagator G t T U)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGc : ∀ r : Fin M, ContinuousOn (G r) (Icc (t r) (t ((r : ℕ) + 1))))
    (b : Fin M → ℝ → V) (hbc : ∀ r : Fin M, ContinuousOn (b r) (Icc (t r) (t ((r : ℕ) + 1))))
    (sol : ℝ → V) (hsol : ∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) :
    ∑ r : Fin M, ∫ v in t r..t ((r : ℕ) + 1), U v (b r v) T = sol T - U 0 (sol 0) T := by
  have hT : 0 ≤ T := hmesh.last ▸ hmesh.nonneg M
  simp only [piece_duhamel hmesh hU hG hGc b hbc sol hsol]
  rw [Fin.sum_univ_eq_sum_range (fun r => U (t (r + 1)) (sol (t (r + 1))) T -
    U (t r) (sol (t r)) T) M, Finset.sum_range_sub (fun r => U (t r) (sol (t r)) T),
    hmesh.last, hmesh.zero, (hU T ⟨hT, le_rfl⟩ (sol T)).1]

end

end SparseHamiltonian.GeneralSourceExtensions.Mesh
