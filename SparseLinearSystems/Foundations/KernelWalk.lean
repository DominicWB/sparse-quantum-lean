import SparseLinearSystems.Foundations.Augmentation

/-!
# Exact algebra of the kernel walk

The algebraic part of Lemma `qls:lem:walk` for linear maps.  Let `E` be an
embedding with retraction `F`, `W = (1 - 2EF) D` and `R₀ = (1 + iK)/2`.  If
`α F K E = H` and `R₀` inverts `1 - D`, then `u ↦ R₀ E u` maps the kernel of `H`
bijectively onto the fixed vectors of `W` (`fixed_lift_of_kernel`,
`kernel_of_fixed`, `kernelEquiv`, `cayleyKernelEquiv`).  The resolvent
identities are hypotheses here.  The endpoint uses the operator version with
the phase gap in `SparseLinearSystems.WalkGap`.
-/

namespace SparseLinearSystems.KernelWalk

noncomputable section

variable {P V : Type*}
variable [AddCommGroup P] [Module ℂ P] [AddCommGroup V] [Module ℂ V]

/-- Reflection in the complement of the embedded public subspace. -/
def reflection (E : P →ₗ[ℂ] V) (F : V →ₗ[ℂ] P) : V →ₗ[ℂ] V :=
  LinearMap.id - (2 : ℂ) • E.comp F

/-- The kernel walk associated with a Cayley map `D`. -/
def walk (E : P →ₗ[ℂ] V) (F : V →ₗ[ℂ] P) (D : V →ₗ[ℂ] V) :
    V →ₗ[ℂ] V :=
  (reflection E F).comp D

/-- The exact resolvent formula, before connecting it to the Cayley map. -/
def resolvent (K : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  (1 / 2 : ℂ) • (LinearMap.id + Complex.I • K)

/-- A retraction makes the public reflection involutive. -/
theorem reflection_involutive (E : P →ₗ[ℂ] V) (F : V →ₗ[ℂ] P)
    (hFE : ∀ u, F (E u) = u) (v : V) :
    reflection E F (reflection E F v) = v := by
  change (v - (2 : ℂ) • E (F v)) -
    (2 : ℂ) • E (F (v - (2 : ℂ) • E (F v))) = v
  rw [map_sub, map_smul, hFE, map_sub, map_smul]
  module

/-- The fixed-vector equation is a resolvent equation on the public part. -/
theorem fixed_iff (E : P →ₗ[ℂ] V) (F : V →ₗ[ℂ] P)
    (D : V →ₗ[ℂ] V) (hFE : ∀ u, F (E u) = u) (v : V) :
    walk E F D v = v ↔ v - D v = (2 : ℂ) • E (F v) := by
  constructor
  · intro hv
    have h := congrArg (reflection E F) hv
    change reflection E F (reflection E F (D v)) = reflection E F v at h
    rw [reflection_involutive E F hFE] at h
    change D v = v - (2 : ℂ) • E (F v) at h
    rw [h]
    abel
  · intro hv
    have hD : D v = reflection E F v := by
      change D v = v - (2 : ℂ) • E (F v)
      rw [← hv]
      abel
    change reflection E F (D v) = v
    rw [hD]
    exact reflection_involutive E F hFE v

/-- Compression of the explicit resolvent gives the kernel consistency
equation without any inverse or spectral assumptions. -/
theorem two_compression_resolvent (E : P →ₗ[ℂ] V) (F : V →ₗ[ℂ] P)
    (K : V →ₗ[ℂ] V) (hFE : ∀ u, F (E u) = u) (u : P) :
    (2 : ℂ) • F (resolvent K (E u)) =
      u + Complex.I • F (K (E u)) := by
  change (2 : ℂ) • F ((1 / 2 : ℂ) • (E u + Complex.I • K (E u))) = _
  rw [map_smul, map_add, map_smul, hFE]
  norm_num [smul_smul]
  have hscalar : (2 : ℂ) * ((1 / 2 : ℂ) * Complex.I) = Complex.I := by
    ring
  rw [hscalar]

/-- On the kernel, the public component of the lifted vector is exactly
one half of the original vector.  The equation `α • F K E = H` encodes the
normalization convention `F K E = H / α`. -/
theorem projection_lift_of_kernel
    (E : P →ₗ[ℂ] V) (F : V →ₗ[ℂ] P) (K : V →ₗ[ℂ] V)
    (H : P →ₗ[ℂ] P) (α : ℂ) (hα : α ≠ 0)
    (hFE : ∀ u, F (E u) = u)
    (hCompression : ∀ u, α • F (K (E u)) = H u)
    (u : P) (hu : H u = 0) :
    F (resolvent K (E u)) = (1 / 2 : ℂ) • u := by
  have hzero : α • F (K (E u)) = 0 := (hCompression u).trans hu
  have hkernel : F (K (E u)) = 0 := (smul_eq_zero.mp hzero).resolve_left hα
  change F ((1 / 2 : ℂ) • (E u + Complex.I • K (E u))) = _
  rw [map_smul, map_add, map_smul, hFE, hkernel]
  simp

/-- The resolvent lift of every kernel vector is fixed by the walk. -/
theorem fixed_lift_of_kernel
    (E : P →ₗ[ℂ] V) (F : V →ₗ[ℂ] P) (K D : V →ₗ[ℂ] V)
    (H : P →ₗ[ℂ] P) (α : ℂ) (hα : α ≠ 0)
    (hFE : ∀ u, F (E u) = u)
    (hCompression : ∀ u, α • F (K (E u)) = H u)
    (hRight : ∀ v, resolvent K v - D (resolvent K v) = v)
    (u : P) (hu : H u = 0) :
    walk E F D (resolvent K (E u)) = resolvent K (E u) := by
  apply (fixed_iff E F D hFE _).mpr
  rw [hRight, projection_lift_of_kernel E F K H α hα hFE hCompression u hu,
    map_smul]
  norm_num [smul_smul]

/-- Every fixed vector is reconstructed from twice its public component. -/
theorem lift_reconstruct_fixed
    (E : P →ₗ[ℂ] V) (F : V →ₗ[ℂ] P) (K D : V →ₗ[ℂ] V)
    (hFE : ∀ u, F (E u) = u)
    (hLeft : ∀ v, resolvent K (v - D v) = v)
    (v : V) (hv : walk E F D v = v) :
    resolvent K (E ((2 : ℂ) • F v)) = v := by
  rw [map_smul, ← (fixed_iff E F D hFE v).mp hv]
  exact hLeft v

/-- Twice the public component of a fixed vector lies in the physical kernel. -/
theorem kernel_of_fixed
    (E : P →ₗ[ℂ] V) (F : V →ₗ[ℂ] P) (K D : V →ₗ[ℂ] V)
    (H : P →ₗ[ℂ] P) (α : ℂ)
    (hFE : ∀ u, F (E u) = u)
    (hCompression : ∀ u, α • F (K (E u)) = H u)
    (hLeft : ∀ v, resolvent K (v - D v) = v)
    (v : V) (hv : walk E F D v = v) :
    H ((2 : ℂ) • F v) = 0 := by
  let u := (2 : ℂ) • F v
  have hReconstruct : resolvent K (E u) = v :=
    lift_reconstruct_fixed E F K D hFE hLeft v hv
  have hConsistency := two_compression_resolvent E F K hFE u
  rw [hReconstruct] at hConsistency
  have hConsistency' : u = u + Complex.I • F (K (E u)) := hConsistency
  have hzero : Complex.I • F (K (E u)) = 0 := by
    calc
      Complex.I • F (K (E u)) = (u + Complex.I • F (K (E u))) - u := by abel
      _ = u - u := by rw [← hConsistency']
      _ = 0 := sub_self u
  have hkernel : F (K (E u)) = 0 :=
    (smul_eq_zero.mp hzero).resolve_left Complex.I_ne_zero
  change H u = 0
  rw [← hCompression u, hkernel, smul_zero]

/-- Exact bijection between the physical kernel and the walk's fixed space.
No Hermiticity, norm, implementation, or gap claim is bundled into this
purely algebraic equivalence. -/
def kernelEquiv
    (E : P →ₗ[ℂ] V) (F : V →ₗ[ℂ] P) (K D : V →ₗ[ℂ] V)
    (H : P →ₗ[ℂ] P) (α : ℂ) (hα : α ≠ 0)
    (hFE : ∀ u, F (E u) = u)
    (hCompression : ∀ u, α • F (K (E u)) = H u)
    (hLeft : ∀ v, resolvent K (v - D v) = v)
    (hRight : ∀ v, resolvent K v - D (resolvent K v) = v) :
    LinearMap.ker H ≃ LinearMap.ker (walk E F D - LinearMap.id) where
  toFun u := ⟨resolvent K (E u), by
    change walk E F D (resolvent K (E u)) - resolvent K (E u) = 0
    exact sub_eq_zero.mpr
      (fixed_lift_of_kernel E F K D H α hα hFE hCompression hRight u u.property)⟩
  invFun v := ⟨(2 : ℂ) • F v, by
    apply kernel_of_fixed E F K D H α hFE hCompression hLeft v
    exact sub_eq_zero.mp
      (show walk E F D v - v = 0 from v.property)⟩
  left_inv u := by
    apply Subtype.ext
    change (2 : ℂ) • F (resolvent K (E u)) = u
    rw [projection_lift_of_kernel E F K H α hα hFE hCompression u u.property]
    norm_num [smul_smul]
  right_inv v := by
    apply Subtype.ext
    change resolvent K (E ((2 : ℂ) • F v)) = v
    exact lift_reconstruct_fixed E F K D hFE hLeft v
      (sub_eq_zero.mp (show walk E F D v - v = 0 from v.property))

omit [AddCommGroup P] [Module ℂ P] in
/-- The map formula above is the generic algebraic Cayley resolvent. -/
theorem resolvent_eq (K : V →ₗ[ℂ] V) :
    resolvent K = Cayley.resolventAtOne K := by
  change (1 / 2 : ℂ) • ((1 : V →ₗ[ℂ] V) + Complex.I • K) =
    (2 : ℂ)⁻¹ • ((1 : V →ₗ[ℂ] V) + Complex.I • K)
  rw [one_div]

/-- The actual Cayley formula gives the exact kernel bijection from the
denominator-inverse equations.  Resolvent inverse identities are now derived,
rather than taken as additional hypotheses. -/
def cayleyKernelEquiv
    (E : P →ₗ[ℂ] V) (F : V →ₗ[ℂ] P) (K S : V →ₗ[ℂ] V)
    (H : P →ₗ[ℂ] P) (α : ℂ) (hα : α ≠ 0)
    (hFE : ∀ u, F (E u) = u)
    (hCompression : ∀ u, α • F (K (E u)) = H u)
    (hRight : (K - Complex.I • (1 : V →ₗ[ℂ] V)) * S = 1)
    (hLeft : S * (K - Complex.I • (1 : V →ₗ[ℂ] V)) = 1) :
    LinearMap.ker H ≃
      LinearMap.ker (walk E F (Cayley.cayleyAction K S) - LinearMap.id) := by
  apply kernelEquiv E F K (Cayley.cayleyAction K S) H α hα hFE hCompression
  · intro v
    have h := congrArg (fun A : V →ₗ[ℂ] V => A v)
      (Cayley.resolventAtOne_mul_one_sub_cayleyAction K S hRight)
    rw [← resolvent_eq K] at h
    change resolvent K (v - Cayley.cayleyAction K S v) = v at h
    exact h
  · intro v
    have h := congrArg (fun A : V →ₗ[ℂ] V => A v)
      (Cayley.one_sub_cayleyAction_mul_resolventAtOne K S hRight hLeft)
    rw [← resolvent_eq K] at h
    change resolvent K v - Cayley.cayleyAction K S (resolvent K v) = v at h
    exact h

end
end SparseLinearSystems.KernelWalk
