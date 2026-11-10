import TimeDependentODE.Solver.Families

/-!
# Node start times, slot durations and the product family of each source label

The general source interface of `ode:thm:time` (Eqs.
`ode:eq:source-interface-mass`, `ode:eq:source-interface-preparation`)
injects the forcing at arbitrary public nodes `v i ∈ [0, T]`, not only at the
mesh points. On the uniform mesh `t_r = r T / M` of the coherent sampled-time
oracle, the source label of node `i` is propagated from `v i` on: its duration
on slot `r` is the part of `[t_r, t_{r+1}]` after `v i`,

  `width T M (v i) r = max (v i) t_{r+1} - max (v i) t_r ∈ [0, T / M]`,

so that a node inside a slot starts with a partial first step. The initial
state starts at `0` and uses every slot fully. These durations form one public
SELECT table (`durationTable`), with entries `M · width ∈ [0, T]`, as required
by the coherent sampled-time SELECT `TimeDependentODE.Select.select`.

The product family of a label (`family`) is the released Gaussian-LCHS product
family of the sampled generators with these slot times. It is entire,
contractive on the closed lower half-plane and `T s Λ`-Lipschitz on the real
axis; at `-i` it is the node propagator, the ordered product of
`exp (-width · G̃_r)` (`family_neg_I`), and at real frequencies it is exactly
the coherent SELECT branch with the public table (`branchEvolution_eq_family`).
-/

namespace SparseHamiltonian.GeneralSourceODE

noncomputable section
open ContinuousLinearMap NativeSparseBlockEncoding
open scoped BigOperators InnerProduct

/-! ### The clock of a start time -/

section Clock

/-- The boundary `r T / M` of slot `r`, clipped below at the start time `t₀`. -/
def clip (T : ℝ) (M : ℕ) (t₀ : ℝ) (r : ℕ) : ℝ := max t₀ (r * T / M)

/-- The duration of slot `r` after the start time `t₀`. -/
def width (T : ℝ) (M : ℕ) (t₀ : ℝ) (r : ℕ) : ℝ := clip T M t₀ (r + 1) - clip T M t₀ r

variable {T t₀ : ℝ} {M : ℕ}

theorem clip_zero (ht₀ : 0 ≤ t₀) : clip T M t₀ 0 = t₀ := by
  simp only [clip, Nat.cast_zero, zero_mul, zero_div]
  exact max_eq_left ht₀

theorem le_clip (r : ℕ) : t₀ ≤ clip T M t₀ r := le_max_left _ _

theorem slot_le_clip (r : ℕ) : r * T / M ≤ clip T M t₀ r := le_max_right _ _

theorem slot_mono (hT : 0 ≤ T) {r r' : ℕ} (h : r ≤ r') : r * T / M ≤ r' * T / M := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) hT

theorem clip_mono (hT : 0 ≤ T) {r r' : ℕ} (h : r ≤ r') : clip T M t₀ r ≤ clip T M t₀ r' :=
  max_le_max le_rfl (slot_mono hT h)

theorem width_nonneg (hT : 0 ≤ T) (r : ℕ) : 0 ≤ width T M t₀ r :=
  sub_nonneg.mpr (clip_mono hT (Nat.le_succ r))

/-- The slot length `T / M` between consecutive boundaries. -/
theorem slot_succ_sub (r : ℕ) : (r + 1 : ℕ) * T / M - r * T / M = T / M := by
  push_cast
  ring

theorem width_le (hT : 0 ≤ T) (r : ℕ) : width T M t₀ r ≤ T / M := by
  unfold width clip
  have h1 := slot_succ_sub (T := T) (M := M) r
  have h2 : (r : ℝ) * T / M ≤ (r + 1 : ℕ) * T / M := slot_mono hT (Nat.le_succ r)
  rcases le_total t₀ ((r : ℝ) * T / M) with h | h
  · rw [max_eq_right h, max_eq_right (h.trans h2)]
    linarith
  · rcases le_total t₀ ((r + 1 : ℕ) * T / M) with h' | h'
    · rw [max_eq_left h, max_eq_right h']
      linarith
    · rw [max_eq_left h, max_eq_left h', sub_self]
      exact div_nonneg hT (Nat.cast_nonneg M)

/-- A positive duration lies within its slot. -/
theorem slot_le_of_width_pos {r : ℕ} (h : 0 < width T M t₀ r) :
    clip T M t₀ r = max t₀ (r * T / M) ∧ clip T M t₀ (r + 1) = (r + 1 : ℕ) * T / M := by
  refine ⟨rfl, ?_⟩
  unfold width clip at h
  unfold clip
  rcases le_total t₀ ((r + 1 : ℕ) * T / M) with h' | h'
  · exact max_eq_right h'
  · exfalso
    have hle : max t₀ ((r : ℝ) * T / M) ≥ t₀ := le_max_left _ _
    rw [max_eq_left h'] at h
    linarith

/-- Every point of a slot with positive duration is within `T / M` of the slot start. -/
theorem mem_slot_of_width_pos {r : ℕ} (h : 0 < width T M t₀ r) {u : ℝ}
    (hu : u ∈ Set.Icc (clip T M t₀ r) (clip T M t₀ (r + 1))) :
    r * T / M ≤ u ∧ u - r * T / M ≤ T / M := by
  obtain ⟨-, hc⟩ := slot_le_of_width_pos h
  have h1 := slot_le_clip (T := T) (M := M) (t₀ := t₀) r
  refine ⟨h1.trans hu.1, ?_⟩
  have h2 := hu.2
  rw [hc] at h2
  have h3 := slot_succ_sub (T := T) (M := M) r
  linarith

theorem clip_le (hT : 0 ≤ T) (hM : 0 < M) (ht₀ : t₀ ≤ T) {r : ℕ} (hr : r ≤ M) :
    clip T M t₀ r ≤ T := by
  unfold clip
  apply max_le ht₀
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  rw [div_le_iff₀ hMR]
  have : (r : ℝ) ≤ M := by exact_mod_cast hr
  nlinarith

theorem clip_last (hM : 0 < M) (ht₀ : t₀ ≤ T) : clip T M t₀ M = T := by
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold clip
  rw [mul_div_assoc, mul_div_cancel₀ T hMR]
  exact max_eq_right ht₀

end Clock

/-! ### Source labels and the public duration table -/

section Labels

variable {m M : ℕ}

/-- Start time of a source label: the initial state at `0`, node `i` at `v i`. -/
def startTime (v : Fin m → ℝ) : Option (Fin m) → ℝ
  | none => 0
  | some i => v i

theorem startTime_nonneg (v : Fin m → ℝ) (hv : ∀ i, 0 ≤ v i) (a : Option (Fin m)) :
    0 ≤ startTime v a := by
  cases a with
  | none => exact le_rfl
  | some i => exact hv i

theorem startTime_le (v : Fin m → ℝ) {T : ℝ} (hT : 0 ≤ T) (hv : ∀ i, v i ≤ T)
    (a : Option (Fin m)) : startTime v a ≤ T := by
  cases a with
  | none => exact hT
  | some i => exact hv i

/-- Public durations of a source label at a time address, in the units of the
SELECT table: the slot time is the entry divided by `M`. -/
def durations (T : ℝ) (v : Fin m → ℝ) (a : Option (Fin m)) (r : Fin M) : ℝ :=
  M * width T M (startTime v a) r

/-- Public SELECT duration table: every LCHS branch of a source label uses
that label's durations. -/
def durationTable {ι : Type*} (T : ℝ) (v : Fin m → ℝ) (b : Option (Fin m) × ι)
    (r : Fin M) : ℝ :=
  durations T v b.1 r

theorem durations_nonneg {T : ℝ} (hT : 0 ≤ T) (v : Fin m → ℝ) (a : Option (Fin m))
    (r : Fin M) : 0 ≤ durations T v a r :=
  mul_nonneg (Nat.cast_nonneg M) (width_nonneg hT r)

theorem durations_le {T : ℝ} (hT : 0 ≤ T) (hM : 0 < M) (v : Fin m → ℝ)
    (a : Option (Fin m)) (r : Fin M) : durations T v a r ≤ T := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have h := width_le (T := T) (M := M) (t₀ := startTime v a) hT r
  unfold durations
  calc (M : ℝ) * width T M (startTime v a) r ≤ M * (T / M) :=
        mul_le_mul_of_nonneg_left h hMR.le
    _ = T := by field_simp

end Labels

/-! ### The node propagator -/

section Propagator

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The ordered product of the slot exponentials after the start time `t₀`. -/
def nodePropagator (Gs : ℕ → V →L[ℂ] V) (T : ℝ) (M : ℕ) (t₀ : ℝ) : V →L[ℂ] V :=
  TimeDependent.evolution (fun r => NormedSpace.exp (width T M t₀ r • (-Gs r))) M

/-- With accretive slot generators the node propagator is a contraction. -/
theorem nodePropagator_norm_le_one (Gs : ℕ → V →L[ℂ] V)
    (hGs : ∀ r, TimeDependentODE.Accretive (Gs r)) {T : ℝ} (hT : 0 ≤ T) (M : ℕ) (t₀ : ℝ) :
    ‖nodePropagator Gs T M t₀‖ ≤ 1 :=
  TimeDependent.evolution_norm_le_one _
    (fun r => TimeDependentODE.accretive_exp_norm_le_one (Gs r) (hGs r) _
      (width_nonneg hT r)) M

end Propagator

/-! ### The product family of a source label -/

section Families

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s M m : ℕ}

/-- Slot times of a source label in chronological order. -/
def slotTimes (hM : 0 < M) (T : ℝ) (v : Fin m → ℝ) (a : Option (Fin m)) (r : ℕ) : ℝ :=
  durations T v a (TimeDependent.Sampled.sampleIndex hM r) / M

/-- The ordered product family of a source label. -/
def family (D : Data (X × Fin M) n Z s) (hM : 0 < M) (T : ℝ) (v : Fin m → ℝ) (x : X)
    (a : Option (Fin m)) : ℂ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  TimeDependentODE.GaussianLCHS.productFamily (TimeDependentODE.Sampling.hamiltonian D hM x)
    (TimeDependentODE.Sampling.dissipative D hM x) (slotTimes hM T v a) M

theorem slotTimes_nonneg (hM : 0 < M) {T : ℝ} (hT : 0 ≤ T) (v : Fin m → ℝ)
    (a : Option (Fin m)) (r : ℕ) : 0 ≤ slotTimes hM T v a r :=
  div_nonneg (durations_nonneg hT v a _) (Nat.cast_nonneg M)

theorem slotTimes_eq (hM : 0 < M) (T : ℝ) (v : Fin m → ℝ) (a : Option (Fin m))
    {r : ℕ} (hr : r < M) : slotTimes hM T v a r = width T M (startTime v a) r := by
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hidx : ((TimeDependent.Sampled.sampleIndex hM r : Fin M) : ℕ) = r :=
    Nat.mod_eq_of_lt hr
  unfold slotTimes durations
  rw [hidx]
  field_simp

theorem slotTimes_le (hM : 0 < M) {T : ℝ} (hT : 0 ≤ T) (v : Fin m → ℝ)
    (a : Option (Fin m)) (r : ℕ) : slotTimes hM T v a r ≤ T / M := by
  unfold slotTimes
  exact div_le_div_of_nonneg_right (durations_le hT hM v a _) (Nat.cast_nonneg M)

theorem family_analyticAt (D : Data (X × Fin M) n Z s) (hM : 0 < M) (T : ℝ)
    (v : Fin m → ℝ) (x : X) (a : Option (Fin m)) (z : ℂ) :
    AnalyticAt ℂ (family D hM T v x a) z :=
  TimeDependentODE.GaussianLCHS.productFamily_analyticAt _ _ _ M z

theorem family_norm_le_one (D : Data (X × Fin M) n Z s) (hM : 0 < M) (T : ℝ) (hT : 0 ≤ T)
    (v : Fin m → ℝ)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (x : X) (a : Option (Fin m)) (z : ℂ) (hz : z.im ≤ 0) :
    ‖family D hM T v x a z‖ ≤ 1 :=
  TimeDependentODE.GaussianLCHS.productFamily_norm_le_one _ _ _ M
    (fun r => by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ODEHermitianReduction.hamiltonianPart_selfAdjoint _)
    (fun r => by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ODEHermitianReduction.dissipativePart_selfAdjoint _)
    (fun r w => by
      have h := hPSD (x, TimeDependent.Sampled.sampleIndex hM r) w
      rwa [ODEMatrixEnergy.matrixOperator_dissipativePart] at h)
    (slotTimes_nonneg hM hT v a) z hz

/-- One public real-axis Lipschitz constant `T s D.scale` serves every
instance and every source label. -/
theorem family_lipschitz (D : Data (X × Fin M) n Z s) (hM : 0 < M) (T : ℝ) (hT : 0 ≤ T)
    (v : Fin m → ℝ) (x : X) (a : Option (Fin m)) (k l : ℝ) :
    ‖family D hM T v x a (k : ℂ) - family D hM T v x a (l : ℂ)‖ ≤
      T * ((s : ℝ) * D.scale) * |k - l| := by
  have h := TimeDependentODE.GaussianLCHS.productFamily_lipschitz
    (TimeDependentODE.Sampling.hamiltonian D hM x)
    (TimeDependentODE.Sampling.dissipative D hM x) (slotTimes hM T v a) M
    (fun r => by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ODEHermitianReduction.hamiltonianPart_selfAdjoint _)
    (fun r => by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ODEHermitianReduction.dissipativePart_selfAdjoint _)
    (slotTimes_nonneg hM hT v a) k l
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  calc
    ∑ r ∈ Finset.range M, slotTimes hM T v a r *
        ‖TimeDependentODE.Sampling.dissipative D hM x r‖ ≤
        ∑ r ∈ Finset.range M, T / M * ((s : ℝ) * D.scale) :=
      Finset.sum_le_sum (fun r _ => mul_le_mul (slotTimes_le hM hT v a r)
        (TimeDependentODE.Sampling.dissipative_norm_le D hM x r) (norm_nonneg _)
        (div_nonneg hT (Nat.cast_nonneg M)))
    _ = T * ((s : ℝ) * D.scale) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      field_simp

/-- At the pole `-i` the family of a label is its node propagator. -/
theorem family_neg_I (D : Data (X × Fin M) n Z s) (hM : 0 < M) (T : ℝ) (v : Fin m → ℝ)
    (x : X) (a : Option (Fin m)) :
    family D hM T v x a (-Complex.I) =
      nodePropagator (TimeDependentODE.Sampling.generator D hM x) T M (startTime v a) := by
  unfold family nodePropagator
  rw [TimeDependentODE.GaussianLCHS.productFamily_neg_I]
  apply TimeDependentODE.Select.evolution_congr
  intro r hr
  rw [TimeDependentODE.Sampling.decomposition, slotTimes_eq hM T v a hr]

/-- At a real frequency the family is the coherent SELECT branch with the
public duration table of the source label. -/
theorem branchEvolution_eq_family {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Data (X × Fin M) n Z s) (hM : 0 < M) (T : ℝ) (v : Fin m → ℝ) (x : X)
    (k : Option (Fin m) × ι → ℝ) (a : Option (Fin m)) (i : ι) :
    TimeDependentODE.Select.branchEvolution D hM k (durationTable T v) x (a, i) =
      family D hM T v x a (k (a, i) : ℂ) := by
  unfold family
  rw [TimeDependentODE.GaussianLCHS.productFamily_ofReal]
  unfold TimeDependentODE.Select.branchEvolution
  congr 1
  funext t
  exact ODEWeightedLCHS.nativeEvolution_eq_evolution D
    (x, TimeDependent.Sampled.sampleIndex hM t) _ _

end Families

end

end SparseHamiltonian.GeneralSourceODE
