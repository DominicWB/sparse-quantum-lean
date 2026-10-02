import SparseODE.ODEActualPrimitiveEndpoint

/-!
# Public uniform quadrature for the LCHS integral

The mesh below is fixed by public interval, Lipschitz and precision bounds.
Its error is proved in the norm of an arbitrary complete real normed space,
so the same result controls the operator norm of the LCHS propagator. A
second application to the norm of its scalar density bounds the coefficient
mass. The cardinality of this finite mesh is not a matrix-query multiplier.

-/

namespace SparseHamiltonian.ODEUniformQuadrature

noncomputable section
open scoped BigOperators Interval

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The left endpoint of one interval in a uniform finite partition. -/
def node (a b : ℝ) (N : ℕ) (i : Fin N) : ℝ :=
  a + (i.val : ℝ) * ((b - a) / (N : ℝ))

/-- A uniform left-endpoint sum, interpreted in its target normed space. -/
def uniformSum (f : ℝ → V) (a b : ℝ) (N : ℕ) : V :=
  ∑ i : Fin N, ((b - a) / (N : ℝ)) • f (node a b N i)

/-- A partial sum used only for the telescoping proof. -/
def partialSum (f : ℝ → V) (a h : ℝ) (N : ℕ) : V :=
  ∑ i ∈ Finset.range N, h • f (a + (i : ℝ) * h)

/-- A Lipschitz bound gives a quadratic local integration error. -/
theorem interval_error (f : ℝ → V) (hf : Continuous f)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y : ℝ, ‖f x - f y‖ ≤ L * |x - y|)
    (a b : ℝ) (hab : a ≤ b) :
    ‖(∫ k in a..b, f k) - (b - a) • f a‖ ≤ (b - a) ^ 2 * L := by
  have hi := hf.intervalIntegrable (μ := MeasureTheory.volume) a b
  have heq : (∫ k in a..b, f k) - (b - a) • f a =
      ∫ k in a..b, f k - f a := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_const]
  rw [heq]
  have hbound (k : ℝ) (hk : k ∈ Set.uIoc a b) :
      ‖f k - f a‖ ≤ L * (b - a) := by
    have hk' : k ∈ Set.Ioc a b := by
      simpa only [Set.uIoc_of_le hab] using hk
    calc
      _ ≤ L * |k - a| := hLip k a
      _ ≤ L * (b - a) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hk'.1.le)]
        exact mul_le_mul_of_nonneg_left (sub_le_sub_right hk'.2 a) hL
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  calc
    _ ≤ (L * (b - a)) * |b - a| := h
    _ = (b - a) ^ 2 * L := by
      rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      ring

/-- The local errors telescope over a fixed mesh. -/
theorem partialSum_error (f : ℝ → V) (hf : Continuous f)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y : ℝ, ‖f x - f y‖ ≤ L * |x - y|)
    (a h : ℝ) (hh : 0 ≤ h) (N : ℕ) :
    ‖(∫ k in a..(a + (N : ℝ) * h), f k) - partialSum f a h N‖ ≤
      (N : ℝ) * h ^ 2 * L := by
  induction N with
  | zero => simp [partialSum]
  | succ N ih =>
      have hwidth : (a + ((N + 1 : ℕ) : ℝ) * h) -
          (a + (N : ℝ) * h) = h := by
        push_cast
        ring
      have horder : a + (N : ℝ) * h ≤ a + ((N + 1 : ℕ) : ℝ) * h := by
        linarith
      have hsplit : (∫ k in a..(a + ((N + 1 : ℕ) : ℝ) * h), f k) =
          (∫ k in a..(a + (N : ℝ) * h), f k) +
            ∫ k in (a + (N : ℝ) * h)..(a + ((N + 1 : ℕ) : ℝ) * h), f k := by
        exact (intervalIntegral.integral_add_adjacent_intervals
          (hf.intervalIntegrable (μ := MeasureTheory.volume) a (a + (N : ℝ) * h))
          (hf.intervalIntegrable (μ := MeasureTheory.volume)
            (a + (N : ℝ) * h) (a + ((N + 1 : ℕ) : ℝ) * h))).symm
      have hlocal :
          ‖(∫ k in (a + (N : ℝ) * h)..(a + ((N + 1 : ℕ) : ℝ) * h), f k) -
              h • f (a + (N : ℝ) * h)‖ ≤ h ^ 2 * L := by
        simpa only [hwidth] using interval_error f hf L hL hLip
          (a + (N : ℝ) * h) (a + ((N + 1 : ℕ) : ℝ) * h) horder
      have hsum : partialSum f a h (N + 1) = partialSum f a h N +
          h • f (a + (N : ℝ) * h) := by
        simp only [partialSum, Finset.sum_range_succ]
      have herror :
          (∫ k in a..(a + ((N + 1 : ℕ) : ℝ) * h), f k) -
              partialSum f a h (N + 1) =
            ((∫ k in a..(a + (N : ℝ) * h), f k) - partialSum f a h N) +
              ((∫ k in (a + (N : ℝ) * h)..(a + ((N + 1 : ℕ) : ℝ) * h), f k) -
                h • f (a + (N : ℝ) * h)) := by
        rw [hsplit, hsum]
        abel
      rw [herror]
      calc
        _ ≤ ‖(∫ k in a..(a + (N : ℝ) * h), f k) - partialSum f a h N‖ +
            ‖(∫ k in (a + (N : ℝ) * h)..(a + ((N + 1 : ℕ) : ℝ) * h), f k) -
              h • f (a + (N : ℝ) * h)‖ := norm_add_le _ _
        _ ≤ (N : ℝ) * h ^ 2 * L + h ^ 2 * L := add_le_add ih hlocal
        _ = ((N + 1 : ℕ) : ℝ) * h ^ 2 * L := by
          push_cast
          ring

/-- Every node lies in the chosen interval, including when its width is zero. -/
theorem node_mem (a b : ℝ) (hab : a ≤ b) (N : ℕ) (hN : 0 < N)
    (i : Fin N) : node a b N i ∈ Set.Icc a b := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hh : 0 ≤ (b - a) / (N : ℝ) :=
    div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg _)
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hh)
  · calc
      _ ≤ a + (N : ℝ) * ((b - a) / (N : ℝ)) := by
        change a + (i.val : ℝ) * ((b - a) / (N : ℝ)) ≤
          a + (N : ℝ) * ((b - a) / (N : ℝ))
        exact add_le_add (le_refl a) (mul_le_mul_of_nonneg_right
          (by exact_mod_cast i.isLt.le) hh)
      _ = b := by field_simp [hNr] ; ring

/-- In particular, the coherent LCHS node lies inside the public cutoff. -/
theorem node_abs_le (R : ℝ) (hR : 0 ≤ R) (N : ℕ) (hN : 0 < N)
    (i : Fin N) : |node (-R) R N i| ≤ R := by
  exact abs_le.mpr (node_mem (-R) R (by linarith) N hN i)

omit [CompleteSpace V] in
theorem uniformSum_eq_partialSum (f : ℝ → V) (a b : ℝ) (N : ℕ) :
    uniformSum f a b N = partialSum f a ((b - a) / (N : ℝ)) N := by
  unfold uniformSum node partialSum
  exact Fin.sum_univ_eq_sum_range
    (fun i : ℕ => ((b - a) / (N : ℝ)) •
      f (a + (i : ℝ) * ((b - a) / (N : ℝ)))) N

/-- Explicit `1/N` operator-norm quadrature error for the finite grid. -/
theorem uniformSum_error (f : ℝ → V) (hf : Continuous f)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y : ℝ, ‖f x - f y‖ ≤ L * |x - y|)
    (a b : ℝ) (hab : a ≤ b) (N : ℕ) (hN : 0 < N) :
    ‖uniformSum f a b N - ∫ k in a..b, f k‖ ≤ (b - a) ^ 2 * L / (N : ℝ) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hend : a + (N : ℝ) * ((b - a) / (N : ℝ)) = b := by
    field_simp [hNr] ; ring
  have hfactor : (N : ℝ) * ((b - a) / (N : ℝ)) ^ 2 * L =
      (b - a) ^ 2 * L / (N : ℝ) := by
    field_simp [hNr]
  rw [uniformSum_eq_partialSum, norm_sub_rev]
  simpa only [hend, hfactor] using partialSum_error f hf L hL hLip a
    ((b - a) / (N : ℝ)) (div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg _)) N

/-- The complex coefficient sampled at the left endpoint. -/
def coefficient (f : ℝ → ℂ) (a b : ℝ) (N : ℕ) (i : Fin N) : ℂ :=
  ((b - a) / (N : ℝ)) • f (node a b N i)

omit [NormedSpace ℝ V] [CompleteSpace V] in
/-- Reverse triangle inequality in a form compatible with the quadrature
interface. -/
theorem norm_function_lipschitz (f : ℝ → V) (L : ℝ)
    (hLip : ∀ x y : ℝ, ‖f x - f y‖ ≤ L * |x - y|) :
    ∀ x y : ℝ, ‖‖f x‖ - ‖f y‖‖ ≤ L * |x - y| := by
  intro x y
  have hxy : ‖f x‖ ≤ ‖f x - f y‖ + ‖f y‖ := by
    calc
      _ = ‖(f x - f y) + f y‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hyx : ‖f y‖ ≤ ‖f y - f x‖ + ‖f x‖ := by
    calc
      _ = ‖(f y - f x) + f x‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hlxy := hLip x y
  have hlyx := hLip y x
  rw [abs_sub_comm y x] at hlyx
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The total absolute coefficient weight is exactly the same quadrature
applied to the norm of the scalar density. -/
theorem coefficient_mass_eq (f : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b) (N : ℕ) :
    ODECoherentLCU.coefficientMass (coefficient f a b N) =
      uniformSum (fun k => ‖f k‖) a b N := by
  have hh : 0 ≤ (b - a) / (N : ℝ) :=
    div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg _)
  unfold ODECoherentLCU.coefficientMass uniformSum coefficient
  apply Finset.sum_congr rfl
  intro i _
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh, smul_eq_mul]

/-- Refining the grid increases the continuous coefficient-mass bound by at
most the same explicit quadrature error; there is no factor from the number
of coherent branches. -/
theorem coefficient_mass_le (f : ℝ → ℂ) (hf : Continuous f)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y : ℝ, ‖f x - f y‖ ≤ L * |x - y|)
    (a b : ℝ) (hab : a ≤ b) (N : ℕ) (hN : 0 < N) :
    ODECoherentLCU.coefficientMass (coefficient f a b N) ≤
      (∫ k in a..b, ‖f k‖) + (b - a) ^ 2 * L / (N : ℝ) := by
  rw [coefficient_mass_eq f a b hab N]
  have h := uniformSum_error (fun k => ‖f k‖) hf.norm L hL
    (norm_function_lipschitz f L hLip) a b hab N hN
  rw [Real.norm_eq_abs] at h
  have hupper := (abs_le.mp h).2
  linarith

/-- One public mesh size for both the operator error and coefficient mass. -/
def meshSize (a b L ν : ℝ) : ℕ := Nat.ceil ((b - a) ^ 2 * L / ν) + 1

theorem meshSize_pos (a b L ν : ℝ) : 0 < meshSize a b L ν :=
  Nat.zero_lt_succ _

/-- Any Lipschitz constant below the public envelope attains precision ν. -/
theorem mesh_budget (a b L C ν : ℝ) (hLC : L ≤ C) (hν : 0 < ν) :
    (b - a) ^ 2 * L / (meshSize a b C ν : ℝ) ≤ ν := by
  have hN := meshSize_pos a b C ν
  have hNr : 0 < (meshSize a b C ν : ℝ) := by exact_mod_cast hN
  have hceil : (b - a) ^ 2 * C / ν < (meshSize a b C ν : ℝ) := by
    calc
      _ ≤ (Nat.ceil ((b - a) ^ 2 * C / ν) : ℝ) := Nat.le_ceil _
      _ < (meshSize a b C ν : ℝ) := by
        simp only [meshSize, Nat.cast_add, Nat.cast_one]
        linarith
  have hprod := (div_lt_iff₀ hν).mp hceil
  apply (div_le_iff₀ hNr).mpr
  calc
    _ ≤ (b - a) ^ 2 * C := mul_le_mul_of_nonneg_left hLC (sq_nonneg _)
    _ ≤ ν * (meshSize a b C ν : ℝ) := by linarith

/-- A single explicit finite grid works for an entire operator family whose
Lipschitz constant is public. In the LCHS application the family label holds
both the unknown matrix input and the propagation duration, so neither can
change the grid or the coefficient preparation. -/
theorem family_certificate {Y : Type*} (F : Y → ℝ → V)
    (hF : ∀ y, Continuous (F y)) (L : ℝ) (hL : 0 ≤ L)
    (hFLip : ∀ y k l, ‖F y k - F y l‖ ≤ L * |k - l|)
    (f : ℝ → ℂ) (hf : Continuous f) (Lf : ℝ) (hLf : 0 ≤ Lf)
    (hfLip : ∀ k l, ‖f k - f l‖ ≤ Lf * |k - l|)
    (R ν : ℝ) (hR : 0 ≤ R) (hν : 0 < ν) :
    let N := meshSize (-R) R (max L Lf) ν
    0 < N ∧
      (∀ i : Fin N, |node (-R) R N i| ≤ R) ∧
      (∀ y, ‖uniformSum (F y) (-R) R N - ∫ k in (-R)..R, F y k‖ ≤ ν) ∧
      ODECoherentLCU.coefficientMass (coefficient f (-R) R N) ≤
        (∫ k in (-R)..R, ‖f k‖) + ν := by
  let N := meshSize (-R) R (max L Lf) ν
  have hN : 0 < N := meshSize_pos (-R) R (max L Lf) ν
  have hab : -R ≤ R := by linarith
  refine ⟨hN, node_abs_le R hR N hN, ?_, ?_⟩
  · intro y
    exact (uniformSum_error (F y) (hF y) L hL (hFLip y) (-R) R hab N hN).trans
      (mesh_budget (-R) R L (max L Lf) ν (le_max_left _ _) hν)
  · exact (coefficient_mass_le f hf Lf hLf hfLip (-R) R hab N hN).trans
      (add_le_add (le_refl _)
        (mesh_budget (-R) R Lf (max L Lf) ν (le_max_right _ _) hν))

section ComplexTarget

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedSpace ℂ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W]

omit [CompleteSpace W] in
/-- The sampled operator quadrature is exactly the linear combination using
its public scalar coefficients. -/
theorem weightedSum_eq_uniformSum (f : ℝ → ℂ) (U : ℝ → W)
    (a b : ℝ) (N : ℕ) :
    (∑ i : Fin N, coefficient f a b N i • U (node a b N i)) =
      uniformSum (fun k => f k • U k) a b N := by
  unfold coefficient uniformSum
  apply Finset.sum_congr rfl
  intro i _
  exact smul_assoc _ _ _

end ComplexTarget
end
end SparseHamiltonian.ODEUniformQuadrature
