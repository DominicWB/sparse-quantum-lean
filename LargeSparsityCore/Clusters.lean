import LargeSparsityCore.Riesz
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Minpoly.Field

set_option autoImplicit false

/-!
# Spectral clusters in finite dimensions

For an element `T` of a finite-dimensional complex algebra, the minimal polynomial splits into
linear factors over `ℂ`, and each of its roots `μ` has `μ - T` noninvertible
(`not_isUnit_of_mem_roots`). Grouping the roots into the sets `S₁`, `S₂` and the remainder gives
coprime factors of the minimal polynomial; Bézout identities for these factors give commuting
idempotent polynomials `P₁`, `P₂` in `T` (`exists_clusters`). If every `z` outside `S₁ ∪ S₂ ∪ B` has
`z - T` invertible, then

* `(z - T) P₁ + (1 - P₁)` is invertible for `z ∉ S₁`, and `(z - T)(1 - P₁) + P₁` for
  `z ∉ S₂ ∪ B`; likewise for `P₂`;
* `(z - T) P_b + (1 - P_b)` is invertible for `z ∉ B`, where `P_b = 1 - P₁ - P₂`.

These are exactly the invertibility hypotheses of the Riesz lemmas (`LargeSparsityCore.Riesz`)
for circles around two isolated clusters, and of the bulk Cauchy estimate. No eigenvector, Jordan
form or spectral theorem is used.
-/

namespace LargeSparsityCore.Clusters

noncomputable section

open Polynomial

/-- The monic product `∏_{a ∈ s} (X - a)`. -/
def linProd (s : Multiset ℂ) : ℂ[X] := (s.map fun a => X - C a).prod

theorem linProd_add (s t : Multiset ℂ) : linProd (s + t) = linProd s * linProd t := by
  simp only [linProd, Multiset.map_add, Multiset.prod_add]

theorem eval_linProd_ne_zero (s : Multiset ℂ) (z : ℂ) (h : z ∉ s) : (linProd s).eval z ≠ 0 := by
  rw [linProd, eval_multiset_prod, Ne, Multiset.prod_eq_zero_iff, Multiset.map_map]
  intro h0
  obtain ⟨a, ha, hza⟩ := Multiset.mem_map.mp h0
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C, sub_eq_zero] at hza
  exact h (hza ▸ ha)

theorem isCoprime_X_sub_C_linProd (a : ℂ) (t : Multiset ℂ) (h : ∀ b ∈ t, a ≠ b) :
    IsCoprime (X - C a) (linProd t) := by
  induction t using Multiset.induction_on with
  | empty => simp [linProd, isCoprime_one_right]
  | cons b t ih =>
      rw [linProd, Multiset.map_cons, Multiset.prod_cons]
      exact IsCoprime.mul_right
        (isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr
          (sub_ne_zero.mpr (h b (Multiset.mem_cons_self b t)))))
        (ih fun c hc => h c (Multiset.mem_cons_of_mem hc))

theorem isCoprime_linProd (s t : Multiset ℂ) (h : ∀ a ∈ s, ∀ b ∈ t, a ≠ b) :
    IsCoprime (linProd s) (linProd t) := by
  induction s using Multiset.induction_on with
  | empty => simp [linProd, isCoprime_one_left]
  | cons a s ih =>
      rw [linProd, Multiset.map_cons, Multiset.prod_cons]
      exact IsCoprime.mul_left (isCoprime_X_sub_C_linProd a t (h a (Multiset.mem_cons_self a s)))
        (ih fun c hc => h c (Multiset.mem_cons_of_mem hc))

section Algebra

variable {𝒜 : Type*} [Ring 𝒜] [Algebra ℂ 𝒜]

theorem outer_eq_aeval (T : 𝒜) (p : ℂ[X]) (z : ℂ) :
    Riesz.outer T (aeval T p) z = aeval T ((C z - X) * p + (1 - p)) := by
  simp only [Riesz.outer, map_add, map_mul, map_sub, aeval_C, aeval_X, map_one,
    Algebra.algebraMap_eq_smul_one]

theorem inner_eq_outer (T P : 𝒜) (z : ℂ) : Riesz.inner T P z = Riesz.outer T (1 - P) z := by
  simp only [Riesz.inner, Riesz.outer, sub_sub_cancel]

/-- If `q(T) P = 0` for an idempotent polynomial `P = p(T)` and `q(z) ≠ 0`, then
`(z - T) P + (1 - P)` is invertible. -/
theorem isUnit_outer (T : 𝒜) (p q : ℂ[X]) (hp : aeval T p * aeval T p = aeval T p)
    (hq : aeval T q * aeval T p = 0) (z : ℂ) (hz : q.eval z ≠ 0) :
    IsUnit (Riesz.outer T (aeval T p) z) := by
  set e := q.eval z
  set s := q /ₘ (X - C z)
  have hqs : q = C e + (X - C z) * s := by
    have h := modByMonic_add_div q (X - C z)
    rw [modByMonic_X_sub_C_eq_C_eval] at h
    exact h.symm
  set F := (C z - X) * p + (1 - p)
  set G := s * p + C e * (1 - p)
  set A := (C z - X) * s - C e * (C z - X) - s + C e
  have hid : F * G - C e = A * (p * p - p) - q * p := by
    simp only [F, G, A]
    linear_combination p * hqs
  have hFG : aeval T F * aeval T G = e • (1 : 𝒜) := by
    have h := congrArg (aeval T) hid
    simp only [map_sub, map_mul, aeval_C, hp, sub_self, mul_zero, hq] at h
    rw [Algebra.algebraMap_eq_smul_one] at h
    exact sub_eq_zero.mp h
  have hGF : aeval T G * aeval T F = e • (1 : 𝒜) := by
    rw [← map_mul, mul_comm, map_mul, hFG]
  rw [outer_eq_aeval]
  refine ⟨⟨aeval T F, e⁻¹ • aeval T G, ?_, ?_⟩, rfl⟩
  · rw [mul_smul_comm, hFG, smul_smul, inv_mul_cancel₀ hz, one_smul]
  · rw [smul_mul_assoc, hGF, smul_smul, inv_mul_cancel₀ hz, one_smul]

/-- The interior version: if `q(T)(1 - P) = 0` and `q(z) ≠ 0`, then `(z - T)(1 - P) + P` is
invertible. -/
theorem isUnit_inner (T : 𝒜) (p q : ℂ[X]) (hp : aeval T p * aeval T p = aeval T p)
    (hq : aeval T q * (1 - aeval T p) = 0) (z : ℂ) (hz : q.eval z ≠ 0) :
    IsUnit (Riesz.inner T (aeval T p) z) := by
  rw [inner_eq_outer, show (1 : 𝒜) - aeval T p = aeval T (1 - p) by simp]
  apply isUnit_outer T (1 - p) q _ _ z hz
  · simp only [map_sub, map_one, sub_mul, mul_sub, one_mul, mul_one, hp, sub_self, sub_zero]
  · simpa using hq

/-- Every root `μ` of the minimal polynomial has `μ - T` noninvertible. -/
theorem not_isUnit_of_mem_roots [FiniteDimensional ℂ 𝒜] (T : 𝒜) {μ : ℂ}
    (hμ : μ ∈ (minpoly ℂ T).roots) : ¬ IsUnit (μ • (1 : 𝒜) - T) := by
  intro hu
  have hint : IsIntegral ℂ T := Algebra.IsIntegral.isIntegral T
  have hne : minpoly ℂ T ≠ 0 := minpoly.ne_zero hint
  have hroot : (minpoly ℂ T).IsRoot μ := (mem_roots hne).mp hμ
  set s := minpoly ℂ T /ₘ (X - C μ)
  have hfac : (X - C μ) * s = minpoly ℂ T := mul_divByMonic_eq_iff_isRoot.mpr hroot
  have h0 : (T - μ • (1 : 𝒜)) * aeval T s = 0 := by
    have h := minpoly.aeval ℂ T
    rw [← hfac, map_mul] at h
    simpa only [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] using h
  have hs : aeval T s = 0 := by
    have hu' : IsUnit (T - μ • (1 : 𝒜)) := by
      rw [← neg_sub]
      exact hu.neg
    exact hu'.mul_right_eq_zero.mp h0
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, mul_zero] at hfac
    exact hne hfac.symm
  have hdeg := natDegree_le_of_dvd (minpoly.dvd ℂ T hs) hs0
  have hdeg2 : (minpoly ℂ T).natDegree = 1 + s.natDegree := by
    rw [← hfac, natDegree_mul (X_sub_C_ne_zero μ) hs0, natDegree_X_sub_C]
  omega

/-- **Cluster decomposition.** If `z - T` is invertible outside `S₁ ∪ S₂ ∪ B`, there are commuting
idempotents `P₁`, `P₂` (polynomials in `T`) with the invertibility properties used by the Riesz
lemmas on two isolated circles and by the bulk estimate for `P_b = 1 - P₁ - P₂`. -/
theorem exists_clusters [FiniteDimensional ℂ 𝒜] (T : 𝒜) (S₁ S₂ B : Set ℂ)
    (hspec : ∀ z : ℂ, z ∉ S₁ → z ∉ S₂ → z ∉ B → IsUnit (z • (1 : 𝒜) - T)) :
    ∃ P₁ P₂ : 𝒜, P₁ * P₁ = P₁ ∧ P₂ * P₂ = P₂ ∧ P₁ * P₂ = 0 ∧ P₂ * P₁ = 0 ∧
      T * P₁ = P₁ * T ∧ T * P₂ = P₂ * T ∧
      (∀ z : ℂ, z ∉ S₁ → IsUnit (Riesz.outer T P₁ z)) ∧
      (∀ z : ℂ, z ∉ S₂ → z ∉ B → IsUnit (Riesz.inner T P₁ z)) ∧
      (∀ z : ℂ, z ∉ S₂ → IsUnit (Riesz.outer T P₂ z)) ∧
      (∀ z : ℂ, z ∉ S₁ → z ∉ B → IsUnit (Riesz.inner T P₂ z)) ∧
      (∀ z : ℂ, z ∉ B → IsUnit (Riesz.outer T (1 - P₁ - P₂) z)) := by
  classical
  set m := minpoly ℂ T
  have hint : IsIntegral ℂ T := Algebra.IsIntegral.isIntegral T
  have hmon : m.Monic := minpoly.monic hint
  have hm : m = linProd m.roots := (IsAlgClosed.splits m).eq_prod_roots_of_monic hmon
  -- Split the roots.
  set R₁ := m.roots.filter (· ∈ S₁)
  set R' := m.roots.filter (· ∉ S₁)
  set R₂ := R'.filter (· ∈ S₂)
  set Rb := R'.filter (· ∉ S₂)
  have hsplit : m.roots = R₁ + (R₂ + Rb) := by
    rw [Multiset.filter_add_not, Multiset.filter_add_not]
  set p₁ := linProd R₁
  set p₂ := linProd R₂
  set pb := linProd Rb
  have hfac : m = p₁ * (p₂ * pb) := by
    rw [hm, hsplit, linProd_add, linProd_add]
  have hzero : aeval T (p₁ * (p₂ * pb)) = 0 := by rw [← hfac]; exact minpoly.aeval ℂ T
  -- Location of the roots of each factor.
  have hR₁ : ∀ a ∈ R₁, a ∈ S₁ := fun a ha => (Multiset.mem_filter.mp ha).2
  have hR'₁ : ∀ a ∈ R', a ∉ S₁ := fun a ha => (Multiset.mem_filter.mp ha).2
  have hR₂ : ∀ a ∈ R₂, a ∈ S₂ ∧ a ∉ S₁ := fun a ha =>
    ⟨(Multiset.mem_filter.mp ha).2, hR'₁ a (Multiset.mem_filter.mp ha).1⟩
  have hRb : ∀ a ∈ Rb, a ∈ B ∧ a ∉ S₂ ∧ a ∉ S₁ := by
    intro a ha
    have ha' := Multiset.mem_filter.mp ha
    have ha1 : a ∉ S₁ := hR'₁ a ha'.1
    refine ⟨?_, ha'.2, ha1⟩
    by_contra haB
    exact not_isUnit_of_mem_roots T (Multiset.mem_of_mem_filter ha'.1)
      (hspec a ha1 ha'.2 haB)
  -- Coprimality.
  have hc₁ : IsCoprime p₁ (p₂ * pb) := by
    rw [← linProd_add]
    apply isCoprime_linProd
    intro a ha b hb hab
    subst hab
    rcases Multiset.mem_add.mp hb with hb | hb
    · exact (hR₂ a hb).2 (hR₁ a ha)
    · exact (hRb a hb).2.2 (hR₁ a ha)
  have hc₂ : IsCoprime p₂ (p₁ * pb) := by
    rw [← linProd_add]
    apply isCoprime_linProd
    intro a ha b hb hab
    subst hab
    rcases Multiset.mem_add.mp hb with hb | hb
    · exact (hR₂ a ha).2 (hR₁ a hb)
    · exact (hRb a hb).2.1 (hR₂ a ha).1
  obtain ⟨a₁, b₁, hab₁⟩ := hc₁
  obtain ⟨a₂, b₂, hab₂⟩ := hc₂
  obtain ⟨π₁, hπ₁⟩ : ∃ π₁ : ℂ[X], π₁ = b₁ * (p₂ * pb) := ⟨_, rfl⟩
  obtain ⟨π₂, hπ₂⟩ : ∃ π₂ : ℂ[X], π₂ = b₂ * (p₁ * pb) := ⟨_, rfl⟩
  have h1 : aeval T π₁ + aeval T (a₁ * p₁) = 1 := by
    rw [← map_add, add_comm, hπ₁, hab₁, map_one]
  have h2 : aeval T π₂ + aeval T (a₂ * p₂) = 1 := by
    rw [← map_add, add_comm, hπ₂, hab₂, map_one]
  have hm₁ : aeval T (a₁ * p₁) * aeval T π₁ = 0 := by
    rw [← map_mul, hπ₁, show a₁ * p₁ * (b₁ * (p₂ * pb)) = (a₁ * b₁) * (p₁ * (p₂ * pb)) by ring,
      map_mul, hzero, mul_zero]
  have hm₂ : aeval T (a₂ * p₂) * aeval T π₂ = 0 := by
    rw [← map_mul, hπ₂, show a₂ * p₂ * (b₂ * (p₁ * pb)) = (a₂ * b₂) * (p₁ * (p₂ * pb)) by ring,
      map_mul, hzero, mul_zero]
  have hidem₁ : aeval T π₁ * aeval T π₁ = aeval T π₁ := by
    have h := congrArg (fun x => x * aeval T π₁) h1
    simp only [add_mul, hm₁, add_zero, one_mul] at h
    exact h
  have hidem₂ : aeval T π₂ * aeval T π₂ = aeval T π₂ := by
    have h := congrArg (fun x => x * aeval T π₂) h2
    simp only [add_mul, hm₂, add_zero, one_mul] at h
    exact h
  have h12 : aeval T π₁ * aeval T π₂ = 0 := by
    rw [← map_mul, hπ₁, hπ₂,
      show b₁ * (p₂ * pb) * (b₂ * (p₁ * pb)) = (b₁ * b₂ * pb) * (p₁ * (p₂ * pb)) by ring,
      map_mul, hzero, mul_zero]
  have h21 : aeval T π₂ * aeval T π₁ = 0 := by
    rw [← map_mul, mul_comm, map_mul, h12]
  have hcomm : ∀ f : ℂ[X], T * aeval T f = aeval T f * T := fun f =>
    (Riesz.commute_aeval T T (Commute.refl T) f).eq
  have hcompl₁ : (1 : 𝒜) - aeval T π₁ = aeval T (a₁ * p₁) := by rw [← h1]; abel
  have hcompl₂ : (1 : 𝒜) - aeval T π₂ = aeval T (a₂ * p₂) := by rw [← h2]; abel
  refine ⟨aeval T π₁, aeval T π₂, hidem₁, hidem₂, h12, h21, hcomm _, hcomm _, ?_, ?_, ?_, ?_, ?_⟩
  · -- `p₁(T) P₁ = 0`
    intro z hz
    apply isUnit_outer T π₁ p₁ hidem₁ _ z
    · exact eval_linProd_ne_zero R₁ z fun hzR => hz (hR₁ z hzR)
    · rw [← map_mul, hπ₁, show p₁ * (b₁ * (p₂ * pb)) = b₁ * (p₁ * (p₂ * pb)) by ring, map_mul,
        hzero, mul_zero]
  · intro z hz2 hzB
    apply isUnit_inner T π₁ (p₂ * pb) hidem₁ _ z
    · rw [← linProd_add]
      refine eval_linProd_ne_zero _ z fun hzR => ?_
      rcases Multiset.mem_add.mp hzR with h | h
      · exact hz2 (hR₂ z h).1
      · exact hzB (hRb z h).1
    · rw [hcompl₁, ← map_mul, show p₂ * pb * (a₁ * p₁) = a₁ * (p₁ * (p₂ * pb)) by ring, map_mul,
        hzero, mul_zero]
  · intro z hz
    apply isUnit_outer T π₂ p₂ hidem₂ _ z
    · exact eval_linProd_ne_zero R₂ z fun hzR => hz (hR₂ z hzR).1
    · rw [← map_mul, hπ₂, show p₂ * (b₂ * (p₁ * pb)) = b₂ * (p₁ * (p₂ * pb)) by ring, map_mul,
        hzero, mul_zero]
  · intro z hz1 hzB
    apply isUnit_inner T π₂ (p₁ * pb) hidem₂ _ z
    · rw [← linProd_add]
      refine eval_linProd_ne_zero _ z fun hzR => ?_
      rcases Multiset.mem_add.mp hzR with h | h
      · exact hz1 (hR₁ z h)
      · exact hzB (hRb z h).1
    · rw [hcompl₂, ← map_mul, show p₁ * pb * (a₂ * p₂) = a₂ * (p₁ * (p₂ * pb)) by ring, map_mul,
        hzero, mul_zero]
  · intro z hz
    have hPb : (1 : 𝒜) - aeval T π₁ - aeval T π₂ = aeval T ((a₁ * p₁) * (a₂ * p₂)) := by
      rw [map_mul (aeval T) (a₁ * p₁) (a₂ * p₂), ← hcompl₁, ← hcompl₂, sub_mul, one_mul, mul_sub,
        mul_one, h12, sub_zero, sub_right_comm]
    have hidemb : aeval T ((a₁ * p₁) * (a₂ * p₂)) * aeval T ((a₁ * p₁) * (a₂ * p₂)) =
        aeval T ((a₁ * p₁) * (a₂ * p₂)) := by
      rw [← hPb, ← sub_eq_zero]
      have h : ((1 : 𝒜) - aeval T π₁ - aeval T π₂) * (1 - aeval T π₁ - aeval T π₂) -
          (1 - aeval T π₁ - aeval T π₂) =
          (aeval T π₁ * aeval T π₁ - aeval T π₁) + (aeval T π₂ * aeval T π₂ - aeval T π₂) +
            aeval T π₁ * aeval T π₂ + aeval T π₂ * aeval T π₁ := by noncomm_ring
      rw [h, hidem₁, hidem₂, h12, h21, sub_self, sub_self, add_zero, add_zero, add_zero]
    rw [hPb]
    apply isUnit_outer T _ pb hidemb _ z
    · exact eval_linProd_ne_zero Rb z fun hzR => hz (hRb z hzR).1
    · rw [← map_mul, show pb * ((a₁ * p₁) * (a₂ * p₂)) = (a₁ * a₂) * (p₁ * (p₂ * pb)) by ring,
        map_mul, hzero, mul_zero]

end Algebra

end

end LargeSparsityCore.Clusters
