import GeneralSourceODE.Branch
import GeneralSourceODE.Counted

/-!
# Source vectors, public phases and the propagated target

The general source interface supplies public nodes `v_i ∈ [0, T]` and
complex coefficients `ω_i`. The actual source vectors are the initial state on
label `none` and `ω_i b(v_i)` on label `some i` (`sources`); their mass is
`B_q = ‖x₀‖ + ∑ |ω_i| ‖b(v_i)‖` (`mass_sources`). The loading oracle prepares
the directions of `x₀` and `b(v_i)`; the public phase `ω_i / |ω_i|`
(`phases`) is applied separately, and the phased preparation then prepares
the direction of every nonzero source vector (`phased_prepares`).

The circuit propagates every source branch with the node propagator of its
start time. Against the propagated source sum
`U(T,0) x₀ + ∑ ω_i U(T, v_i) b(v_i)`, the propagated target `nodeTarget`
has error at most `T (β_G T/M + δ_G) B_q` (`target_error`).
-/

namespace SparseHamiltonian.GeneralSourceODE

noncomputable section
open ContinuousLinearMap Set TimeDependentODE ODEStateNormalization OracleCircuit
open scoped BigOperators InnerProduct

section Sources

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {m : ℕ}

/-- The actual source vectors: the initial state and the weighted loaded
forcing values at the nodes. -/
def sources (x₀ : V) (bv : Fin m → V) (ω : Fin m → ℂ) : Option (Fin m) → V
  | none => x₀
  | some i => ω i • bv i

/-- The public coefficient phases: `ω_i / |ω_i|` on source label `i`, phase one
on the initial branch and on zero coefficients. -/
def phases (ω : Fin m → ℂ) : Option (Fin m) → ℂ
  | none => 1
  | some i => if ω i = 0 then 1 else ω i / (‖ω i‖ : ℂ)

theorem phases_norm (ω : Fin m → ℂ) (a : Option (Fin m)) : ‖phases ω a‖ = 1 := by
  cases a with
  | none => simp [phases]
  | some i =>
      by_cases h : ω i = 0
      · simp [phases, h]
      · have hn : 0 < ‖ω i‖ := norm_pos_iff.mpr h
        simp only [phases, if_neg h, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hn]
        exact div_self hn.ne'

/-- The mass of the actual source vectors is the absolute coefficient mass
`B_q = ‖x₀‖ + ∑ |ω_i| ‖b(v_i)‖`. -/
theorem mass_sources (x₀ : V) (bv : Fin m → V) (ω : Fin m → ℂ) :
    ODESourceBranches.mass (sources x₀ bv ω) = ‖x₀‖ + ∑ i, ‖ω i‖ * ‖bv i‖ := by
  unfold ODESourceBranches.mass
  rw [Fintype.sum_option]
  simp only [sources, norm_smul]

/-- Directions of complex multiples. -/
theorem unitDirection_complex_smul (c : ℂ) (hc : c ≠ 0) (w : V) :
    unitDirection (c • w) = (c / (‖c‖ : ℂ)) • unitDirection w := by
  unfold unitDirection
  have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
  rw [norm_smul, ← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul]
  have : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast hc'.ne'
  congr 1
  push_cast
  field_simp

/-- The phased preparations are isometries. -/
theorem phased_isometry [CompleteSpace V] (Jx : Option (Fin m) → V →L[ℂ] V)
    (hJ : ∀ a, IsUnitary (Jx a)) (ω : Fin m → ℂ) (a : Option (Fin m)) :
    (Compiled.phased Jx (phases ω) a)† ∘L Compiled.phased Jx (phases ω) a = 1 := by
  have hφ := phases_norm ω a
  have hconj : star (phases ω a) * phases ω a = 1 := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hφ]
    norm_num
  have h1 : star (Jx a) ∘L Jx a = 1 := (hJ a).1
  unfold Compiled.phased
  rw [← star_eq_adjoint, star_smul, smul_comp, comp_smul, smul_smul, h1, hconj, one_smul]

/-- The loading oracle and the public phases prepare the direction of every
nonzero actual source vector. -/
theorem phased_prepares (Jx : Option (Fin m) → V →L[ℂ] V) (x₀ : V) (bv : Fin m → V)
    (ω : Fin m → ℂ) (seed : V)
    (h₀ : x₀ ≠ 0 → Jx none seed = unitDirection x₀)
    (hb : ∀ i, ω i ≠ 0 → bv i ≠ 0 → Jx (some i) seed = unitDirection (bv i)) :
    ∀ a, sources x₀ bv ω a ≠ 0 →
      Compiled.phased Jx (phases ω) a seed = unitDirection (sources x₀ bv ω a) := by
  intro a ha
  cases a with
  | none =>
      change (1 : ℂ) • Jx none seed = unitDirection x₀
      rw [one_smul]
      exact h₀ ha
  | some i =>
      have ha' : ω i • bv i ≠ 0 := ha
      have hω : ω i ≠ 0 := fun h => ha' (by rw [h, zero_smul])
      have hbv : bv i ≠ 0 := fun h => ha' (by rw [h, smul_zero])
      change (if ω i = 0 then 1 else ω i / (‖ω i‖ : ℂ)) • Jx (some i) seed =
        unitDirection (ω i • bv i)
      rw [if_neg hω, hb i hω hbv, unitDirection_complex_smul (ω i) hω]

end Sources

section Target

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {m M : ℕ}

/-- The propagated target: every source branch propagated by the node
propagator of its start time. -/
def nodeTarget (Gs : ℕ → V →L[ℂ] V) (T : ℝ) (M : ℕ) (v : Fin m → ℝ) (x₀ : V)
    (bv : Fin m → V) (ω : Fin m → ℂ) : V :=
  ∑ a, nodePropagator Gs T M (startTime v a) (sources x₀ bv ω a)

/-- With accretive samples the target norm is at most the source mass. -/
theorem nodeTarget_norm_le (Gs : ℕ → V →L[ℂ] V) (hGs : ∀ r, Accretive (Gs r))
    {T : ℝ} (hT : 0 ≤ T) (M : ℕ) (v : Fin m → ℝ) (x₀ : V) (bv : Fin m → V)
    (ω : Fin m → ℂ) :
    ‖nodeTarget Gs T M v x₀ bv ω‖ ≤ ODESourceBranches.mass (sources x₀ bv ω) := by
  unfold nodeTarget ODESourceBranches.mass
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  calc
    ‖nodePropagator Gs T M (startTime v a) (sources x₀ bv ω a)‖ ≤
        ‖nodePropagator Gs T M (startTime v a)‖ * ‖sources x₀ bv ω a‖ := le_opNorm _ _
    _ ≤ 1 * ‖sources x₀ bv ω a‖ := mul_le_mul_of_nonneg_right
        (nodePropagator_norm_le_one Gs hGs hT M _) (norm_nonneg _)
    _ = ‖sources x₀ bv ω a‖ := one_mul _

/-- **Propagated target error.** Against the propagated source sum
`U(T,0) x₀ + ∑ ω_i U(T, v_i) b(v_i)` the target errs by at most
`T (β_G T/M + δ_G) B_q`. Here `U t w` is the homogeneous solution on
`[t, T]` with value `w` at `t`. -/
theorem target_error {T : ℝ} (hT : 0 ≤ T) (hM : 0 < M) (v : Fin m → ℝ)
    (hv : ∀ i, v i ∈ Icc 0 T) (ω : Fin m → ℂ)
    (G : ℝ → V →L[ℂ] V) (hG : ∀ u ∈ Icc 0 T, Accretive (G u))
    (Gs : ℕ → V →L[ℂ] V) (hGs : ∀ r, Accretive (Gs r))
    (βG δG : ℝ) (hβG : 0 ≤ βG) (hδG : 0 ≤ δG)
    (hGLip : ∀ u ∈ Icc 0 T, ∀ w ∈ Icc 0 T, ‖G u - G w‖ ≤ βG * |u - w|)
    (hGs_err : ∀ r < M, ‖G (r * T / M) - Gs r‖ ≤ δG)
    (U : ℝ → V → ℝ → V) (hU : ∀ t ∈ Icc 0 T, ∀ w, SolvesODE G 0 (U t w) t T ∧ U t w t = w)
    (x₀ : V) (bv : Fin m → V) :
    ‖(U 0 x₀ T + ∑ i, ω i • U (v i) (bv i) T) - nodeTarget Gs T M v x₀ bv ω‖ ≤
      T * (βG * (T / M) + δG) * ODESourceBranches.mass (sources x₀ bv ω) := by
  set K : ℝ := βG * (T / M) + δG with hK
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hK0 : 0 ≤ K := add_nonneg (mul_nonneg hβG (div_nonneg hT hMR.le)) hδG
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  -- the initial branch
  have hInit : ‖U 0 x₀ T - nodePropagator Gs T M 0 x₀‖ ≤ T * K * ‖x₀‖ := by
    obtain ⟨hsol, hval⟩ := hU 0 h0 x₀
    have h := branch_error hT hM le_rfl hT hsol hG Gs hGs βG δG hβG hδG hGLip hGs_err
    rw [hval] at h
    calc
      _ ≤ (T - 0) * (K * ‖x₀‖) := h
      _ = T * K * ‖x₀‖ := by ring
  -- the node branches
  have hNode : ∀ i, ‖ω i • U (v i) (bv i) T -
      nodePropagator Gs T M (v i) (ω i • bv i)‖ ≤ T * K * (‖ω i‖ * ‖bv i‖) := by
    intro i
    obtain ⟨hsol, hval⟩ := hU (v i) (hv i) (bv i)
    have h := branch_error hT hM (hv i).1 (hv i).2 hsol hG Gs hGs βG δG hβG hδG hGLip hGs_err
    rw [hval] at h
    have hsplit : ω i • U (v i) (bv i) T - nodePropagator Gs T M (v i) (ω i • bv i) =
        ω i • (U (v i) (bv i) T - nodePropagator Gs T M (v i) (bv i)) := by
      rw [map_smul, smul_sub]
    rw [hsplit, norm_smul]
    have hle : (T - v i) * (K * ‖bv i‖) ≤ T * (K * ‖bv i‖) :=
      mul_le_mul_of_nonneg_right (by linarith [(hv i).1]) (mul_nonneg hK0 (norm_nonneg _))
    calc
      ‖ω i‖ * ‖U (v i) (bv i) T - nodePropagator Gs T M (v i) (bv i)‖ ≤
          ‖ω i‖ * (T * (K * ‖bv i‖)) :=
        mul_le_mul_of_nonneg_left (h.trans hle) (norm_nonneg _)
      _ = T * K * (‖ω i‖ * ‖bv i‖) := by ring
  have hTarget : nodeTarget Gs T M v x₀ bv ω =
      nodePropagator Gs T M 0 x₀ + ∑ i, nodePropagator Gs T M (v i) (ω i • bv i) := by
    unfold nodeTarget
    rw [Fintype.sum_option]
    rfl
  have hsplit : (U 0 x₀ T + ∑ i, ω i • U (v i) (bv i) T) - nodeTarget Gs T M v x₀ bv ω =
      (U 0 x₀ T - nodePropagator Gs T M 0 x₀) +
        ∑ i, (ω i • U (v i) (bv i) T - nodePropagator Gs T M (v i) (ω i • bv i)) := by
    rw [hTarget, Finset.sum_sub_distrib]
    abel
  rw [hsplit, mass_sources]
  calc
    _ ≤ ‖U 0 x₀ T - nodePropagator Gs T M 0 x₀‖ +
        ∑ i, ‖ω i • U (v i) (bv i) T - nodePropagator Gs T M (v i) (ω i • bv i)‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ T * K * ‖x₀‖ + ∑ i, T * K * (‖ω i‖ * ‖bv i‖) :=
      add_le_add hInit (Finset.sum_le_sum fun i _ => hNode i)
    _ = T * K * (‖x₀‖ + ∑ i, ‖ω i‖ * ‖bv i‖) := by
      rw [← Finset.mul_sum]
      ring

end Target

end

end SparseHamiltonian.GeneralSourceODE
