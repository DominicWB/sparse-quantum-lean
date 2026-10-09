import ODELowerBoundExtensions.Psd.Data.SearchData
import ODELowerBoundExtensions.Psd.Data.ScalarData
import ODELowerBoundExtensions.Psd.Numerics

/-!
# The PSD families as one-stage families of the ODE model

Manuscript lines 4016-4030 (the homogeneous equation
`ẋ = -D_X x` with `D_X ⪰ 0`, `‖D_X‖ = η_D = 1`, `T = τ`, `1 ≤ g ≤ √2`, public supports, dyadic
entries, the heralded output) and 4086-4088 (start vector, `P ∈ [1/2, 1]`).

The Hamiltonian lower bound's `g = 1` families enter the ODE model through
`ODE.hamFamily` (generator `iH`). The PSD families have generator `D` itself, so this module
builds the analogous one-stage family `heatFamily D T x₀` of `ODE.Family` (`ODE/Model`):
one stage of length `T`, no source, generator `G_0(x) = D_x` (`oneStageData`: the same words,
decode and locators, indexed by `X × Fin 1`), start `x₀`.

* `access_heatFamily`: the sampled-time access is the spectated native access
  `specOracles (ι × Fin 1) D` (as `ODE.access_hamFamily`);
* `heatFamily_solves`: `t ↦ e^{-tD_x} x₀` solves instance `x` (`solves_heat`);
* `heatFamily_inClass`: accretive data with row/column norms at most one and
  `B = ‖x₀‖ ≤ ḡ ‖x(T)‖` is in the class with `η = 1`;
* `forces_of_spec_heat`: solver transfer (as `ODE.forces_of_spec`): a bound proved for
  programs over `specOracles (ι × Fin 1) D` with heralded accuracy for the normalised endpoint
  `x(T)/‖x(T)‖` is forced by the family;
* `psdSearchFamilyAt`, `psdScalarFamilyAt`: the two hard families of Theorem `odel:thm:psd` at
  the main parameters `n = ⌊r/4⌋`, `u = τ/2`, `m = 2^{psdMu s}`, `T = τ`, with their class
  membership for `ḡ ≥ √2` and their properties (`*_props`: no source, generator
  `D_X = psdSearchMat …`/`psdScalarMat …`, `B = 1`, `T = τ`, `1 ≤ g ≤ √2`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Psd

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit SparseLowerBounds
  SparseLowerBounds.Hamiltonian SparseLowerBounds.ODE Readout
open scoped InnerProduct InnerProductSpace ComplexOrder

-- The nested spectator spaces over the search index exceed the default instance size.
set_option synthInstance.maxSize 1024

section Generic

variable {X N Z : Type*} [Fintype N] [DecidableEq N] {s : ℕ}

/-- **One-stage data**: the data `D` read with the time address `Fin 1` (generator
`G_0(x) = D_x`; the same words, decode, locators and locator oracles). The same construction
as `ODELowerBoundExtensions.Release.reindexData D Prod.fst`. -/
def oneStageData (D : Data X N Z s) : Data (X × Fin 1) N Z s where
  slot := D.slot
  slots_pos := D.slots_pos
  scale := D.scale
  scale_pos := D.scale_pos
  matrix p := D.matrix p.1
  table p := D.table p.1
  decode := D.decode
  decode_bound := D.decode_bound
  decoded p i j := D.decoded p.1 i j
  rowloc p := D.rowloc p.1
  colloc p := D.colloc p.1
  row_injective p := D.row_injective p.1
  column_injective p := D.column_injective p.1
  row_covers p i j h := D.row_covers p.1 i j h
  column_covers p i j h := D.column_covers p.1 i j h
  rowOracle p := D.rowOracle p.1
  columnOracle p := D.columnOracle p.1
  row_unitary p := D.row_unitary p.1
  column_unitary p := D.column_unitary p.1
  row_valid p := D.row_valid p.1
  column_valid p := D.column_valid p.1

/-- The matrix of the one-stage data is that of `D`. -/
@[simp] theorem oneStageData_matrix (D : Data X N Z s) (x : X) (r : Fin 1) :
    (oneStageData D).matrix (x, r) = D.matrix x := rfl

/-- **The homogeneous constant-coefficient family** `ẋ = -D_x x`, `x(0) = x₀`, on `[0, T]`
(one stage, no source). -/
def heatFamily (D : Data X N Z s) (T : ℝ) (hT : 0 ≤ T) (x₀ : EuclideanSpace ℂ N) :
    Family X N Z 1 s where
  data := oneStageData D
  len _ := T
  len_nonneg _ := hT
  src _ := 0
  init := x₀

variable (D : Data X N Z s) (T : ℝ) (hT : 0 ≤ T) (x₀ : EuclideanSpace ℂ N)

/-- The final time of `heatFamily D T hT x₀` is `T` (one stage of length `T`). -/
@[simp] theorem heatFamily_T : (heatFamily D T hT x₀).T = T := by
  rw [Family.T_eq_sum]
  simp [heatFamily]

/-- `B = ‖x₀‖` (no source). -/
theorem heatFamily_mass : (heatFamily D T hT x₀).mass = ‖x₀‖ := by
  simp [Family.mass, heatFamily]

/-- **Oracle transfer**: the sampled-time access of `heatFamily D` is the native access of `D`
with the untouched spectator `ι × Fin 1`. -/
theorem access_heatFamily [Fintype Z] [AddCommGroup Z] (ι : Type*) [Fintype ι] (l : Query)
    (x : X) : (heatFamily D T hT x₀).access ι l x = specOracles (ι × Fin 1) D l x := by
  ext Ψ b : 2
  cases l <;> rfl

/-- **The solution**: `t ↦ e^{-tD_x} x₀` solves instance `x`. -/
theorem heatFamily_solves (x : X) :
    (heatFamily D T hT x₀).Solves x (fun t => heat (D.matrix x) t x₀) := by
  refine ⟨?_, fun k => ?_⟩
  · simp [heatFamily, heat_zero]
  · exact solves_heat (D.matrix x) x₀ _ _

/-- **The class promises** with `η = 1`: accretive generators, row and column Euclidean norms
at most one, and `B = ‖x₀‖ ≤ ḡ ‖x(T)‖` with `x(T) ≠ 0`. -/
theorem heatFamily_inClass
    (hacc : ∀ x, TimeDependentODE.Accretive (SparseStateOverlap.matrixOperator (D.matrix x)))
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1) (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    {gbar : ℝ} (hne : ∀ x, heat (D.matrix x) T x₀ ≠ 0)
    (hg : ∀ x, ‖x₀‖ ≤ gbar * ‖heat (D.matrix x) T x₀‖) :
    (heatFamily D T hT x₀).InClass 1 gbar where
  accretive x _ := hacc x
  row_norm x _ i := by rw [one_pow]; exact hrow x i
  col_norm x _ j := by rw [one_pow]; exact hcol x j
  solution x := by
    refine ⟨_, heatFamily_solves D T hT x₀ x, ?_, ?_⟩
    · rw [heatFamily_T]; exact hne x
    · rw [heatFamily_T, heatFamily_mass]; exact hg x

/-- **Solver transfer** (as `ODE.forces_of_spec`): if every program over the spectated native
primitives `specOracles (ι × Fin 1) D` that succeeds with probability `≥ 2/3` and is
heralded-accurate for the normalised endpoint `e^{-TD_x} x₀/‖e^{-TD_x} x₀‖` makes at least `b`
value queries and `b` queries in total, then every solver of `heatFamily D T x₀` does. -/
theorem forces_of_spec_heat [Fintype Z] [AddCommGroup Z] {ι G : Type*} [Fintype ι]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] {ε b : ℝ}
    (A : Solver ι (heatFamily D T hT x₀) G ε)
    (hb : ∀ p : MultiOracleCircuit.Program (specOracles (ι × Fin 1) D),
      (∀ x, 2 / 3 ≤ ‖A.herald (p.eval x A.seed)‖ ^ 2) →
      (∀ x, HeraldedAccurate A.out A.herald (p.eval x A.seed)
        (ODEStateNormalization.unitDirection (heat (D.matrix x) T x₀)) ε) →
      b ≤ p.labelCount .value ∧ b ≤ p.count) :
    b ≤ A.prog.labelCount .value ∧ b ≤ A.prog.count := by
  have hacc : ∀ x, HeraldedAccurate A.out A.herald (A.prog.eval x A.seed)
      (ODEStateNormalization.unitDirection (heat (D.matrix x) T x₀)) ε := by
    intro x
    have h := A.accurate x _ (heatFamily_solves D T hT x₀ x)
    rw [heatFamily_T] at h
    exact h
  have key : ∀ (O : Query → X → Workspace ι N Z 1 →L[ℂ] Workspace ι N Z 1),
      O = specOracles (ι × Fin 1) D → ∀ p : MultiOracleCircuit.Program O,
      (∀ x, 2 / 3 ≤ ‖A.herald (p.eval x A.seed)‖ ^ 2) →
      (∀ x, HeraldedAccurate A.out A.herald (p.eval x A.seed)
        (ODEStateNormalization.unitDirection (heat (D.matrix x) T x₀)) ε) →
      b ≤ p.labelCount .value ∧ b ≤ p.count := by
    rintro O rfl p
    exact hb p
  exact key _ (funext fun l => funext fun x => access_heatFamily D T hT x₀ ι l x) A.prog
    A.success hacc

end Generic

/-- **The instance properties pass to the one-stage data**: every field of
`Hamiltonian.HardInstance` (real symmetric, norm one, row/column norms, sparsity exactly `s`,
scale one, dyadic words, input-independent locators) holds for `oneStageData D` when it holds for
`D`. -/
theorem hardInstance_oneStageData {X N : Type*} [Fintype N] [DecidableEq N] {B s : ℕ}
    {D : Data X N (Word B) s} (hD : HardInstance D) : HardInstance (oneStageData D) where
  transpose_eq p := hD.transpose_eq p.1
  real p := hD.real p.1
  isHermitian p := hD.isHermitian p.1
  norm_eq_one p := hD.norm_eq_one p.1
  row_norm_le p := hD.row_norm_le p.1
  col_norm_le p := hD.col_norm_le p.1
  row_norm_attained p := hD.row_norm_attained p.1
  col_norm_attained p := hD.col_norm_attained p.1
  row_sparsity_le p := hD.row_sparsity_le p.1
  col_sparsity_le p := hD.col_sparsity_le p.1
  row_sparsity_attained p := hD.row_sparsity_attained p.1
  col_sparsity_attained p := hD.col_sparsity_attained p.1
  scale_eq := hD.scale_eq
  decode_eq := hD.decode_eq
  dyadic p := hD.dyadic p.1
  locators_const p p' := hD.locators_const p.1 p'.1

/-- `1/2 ≤ r²` and `0 ≤ r` give `1 ≤ √2 · r` (i.e. `r ≥ 1/√2`). -/
theorem one_le_sqrt_two_mul_of_half_le_sq {r : ℝ} (hr : 0 ≤ r) (h : 1 / 2 ≤ r ^ 2) :
    1 ≤ Real.sqrt 2 * r := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h0 := Real.sqrt_nonneg 2
  have ha : 0 ≤ Real.sqrt 2 * r := mul_nonneg h0 hr
  have hsq : 1 ≤ (Real.sqrt 2 * r) ^ 2 := by rw [mul_pow, h2]; linarith
  nlinarith

/-- `1/2 ≤ r² ≤ 1` and `0 ≤ r` give `1 ≤ 1/r ≤ √2`. -/
theorem one_div_mem_of_half_le_sq {r : ℝ} (hr : 0 ≤ r) (h : 1 / 2 ≤ r ^ 2) (h1 : r ≤ 1) :
    1 ≤ 1 / r ∧ 1 / r ≤ Real.sqrt 2 := by
  have hpos : 0 < r := by
    rcases hr.lt_or_eq with hr | hr
    · exact hr
    · subst hr; norm_num at h
  refine ⟨(one_le_div hpos).2 h1, (div_le_iff₀ hpos).2 ?_⟩
  exact one_le_sqrt_two_mul_of_half_le_sq hr h

/-! ### The two hard families at the main parameters -/

variable {τ ε : ℝ} {s : ℕ}

/-- `n = ⌊r/4⌋ ≥ 1` in the range. -/
theorem PsdRange.one_le_precN (h : PsdRange τ s ε) : 1 ≤ precN τ ε := by
  have := (precN_range h.toHSRange h.hL).1
  omega

/-- **The gadget-family data at the main parameters** `n = ⌊r/4⌋`, `m = 2^{psdMu s}`,
`u = τ/2`. -/
def psdSearchDataAt (h : PsdRange τ s ε) :
    Data (Fin (precN τ ε) → Fin (2 ^ psdMu s)) (SearchIndex (precN τ ε) (psdMu s) s)
      (Word (psdSearchBits (precN τ ε) (psdMu s) s (τ / 2))) s :=
  psdSearchData (precN τ ε) (psdMu s) s (τ / 2) h.one_le_precN (two_mul_psdM_add_one_le h.s_ge)

/-- **The scalar-family data at the main parameters** `n = ⌊r/4⌋`, `u = τ/2`. -/
def psdScalarDataAt (h : PsdRange τ s ε) :
    Data (Fin (precN τ ε) → Bool) (ScalarIndex (precN τ ε) s)
      (Word (psdScalarBits (precN τ ε) s (τ / 2))) s :=
  psdScalarData (precN τ ε) s (τ / 2) h.one_le_precN (by have := h.s_ge; omega)

/-- The matrix of the gadget data at the main parameters is `psdSearchMat`. -/
@[simp] theorem psdSearchDataAt_matrix (h : PsdRange τ s ε) :
    (psdSearchDataAt h).matrix = psdSearchMat (precN τ ε) (psdMu s) s (τ / 2) := rfl

/-- The matrix of the scalar data at the main parameters is `psdScalarMat`. -/
@[simp] theorem psdScalarDataAt_matrix (h : PsdRange τ s ε) :
    (psdScalarDataAt h).matrix = psdScalarMat (precN τ ε) s (τ / 2) := rfl

/-- **The gadget family of Theorem `odel:thm:psd`** (lines 4032-4117): `ẋ = -D_X x` on
`[0, τ]`, `D_X = psdSearchMat n μ s (τ/2) X` (`n = ⌊r/4⌋`, `m = 2^{psdMu s}`), start
`(|r₀⟩ + |0, v⟩)/√2`. -/
def psdSearchFamilyAt (h : PsdRange τ s ε) :
    Family (Fin (precN τ ε) → Fin (2 ^ psdMu s)) (SearchIndex (precN τ ε) (psdMu s) s)
      (Word (psdSearchBits (precN τ ε) (psdMu s) s (τ / 2))) 1 s :=
  heatFamily (psdSearchDataAt h) τ (by linarith [h.one_le_tau])
    (searchInput (precN τ ε) (psdMu s) s)

/-- **The scalar family of Theorem `odel:thm:psd`** (lines 4119-4127): the gadgets replaced by
scalar signs, start `(|r₀⟩ + |0⟩)/√2`. -/
def psdScalarFamilyAt (h : PsdRange τ s ε) :
    Family (Fin (precN τ ε) → Bool) (ScalarIndex (precN τ ε) s)
      (Word (psdScalarBits (precN τ ε) s (τ / 2))) 1 s :=
  heatFamily (psdScalarDataAt h) τ (by linarith [h.one_le_tau]) (scalarInput (precN τ ε) s)

/-- The data of the gadget family are the one-stage gadget data. -/
@[simp] theorem psdSearchFamilyAt_data (h : PsdRange τ s ε) :
    (psdSearchFamilyAt h).data = oneStageData (psdSearchDataAt h) := rfl

/-- The data of the scalar family are the one-stage scalar data. -/
@[simp] theorem psdScalarFamilyAt_data (h : PsdRange τ s ε) :
    (psdScalarFamilyAt h).data = oneStageData (psdScalarDataAt h) := rfl

/-- `T = τ` for the gadget family. -/
theorem psdSearchFamilyAt_T (h : PsdRange τ s ε) : (psdSearchFamilyAt h).T = τ :=
  heatFamily_T _ _ _ _

/-- `T = τ` for the scalar family. -/
theorem psdScalarFamilyAt_T (h : PsdRange τ s ε) : (psdScalarFamilyAt h).T = τ :=
  heatFamily_T _ _ _ _

/-- The gadget family is in the class with `η = 1` and any `ḡ ≥ √2` (`g ≤ √2`). -/
theorem psdSearchFamilyAt_inClass (h : PsdRange τ s ε) {gbar : ℝ} (hg : Real.sqrt 2 ≤ gbar) :
    (psdSearchFamilyAt h).InClass 1 gbar := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  have hP := fun j => psdSearchMat_props (n := precN τ ε) (μ := psdMu s) (s := s)
    (two_mul_psdM_add_one_le h.s_ge) (τ / 2) j
  have hacc : ∀ j, TimeDependentODE.Accretive
      (SparseStateOverlap.matrixOperator ((psdSearchDataAt h).matrix j)) := fun j => by
    rw [psdSearchDataAt_matrix]
    exact accretive_of_posSemidef (psdSearchMat_posSemidef (τ / 2) j)
  have hrow : ∀ j i, ∑ i', ‖(psdSearchDataAt h).matrix j i i'‖ ^ 2 ≤ 1 := fun j => by
    rw [psdSearchDataAt_matrix]
    exact (hP j).2.1
  have hcol : ∀ j i', ∑ i, ‖(psdSearchDataAt h).matrix j i i'‖ ^ 2 ≤ 1 := fun j => by
    rw [psdSearchDataAt_matrix]
    exact (hP j).2.2.1
  have hne : ∀ j, heat ((psdSearchDataAt h).matrix j) τ
      (searchInput (precN τ ε) (psdMu s) s) ≠ 0 := fun j => by
    rw [psdSearchDataAt_matrix]
    intro h0
    have he := (psdSearch_endpoint_norm (s := s) hτ j).1
    rw [h0, norm_zero] at he
    norm_num at he
  have hgg : ∀ j, ‖searchInput (precN τ ε) (psdMu s) s‖ ≤
      gbar * ‖heat ((psdSearchDataAt h).matrix j) τ (searchInput (precN τ ε) (psdMu s) s)‖ :=
    fun j => by
      rw [psdSearchDataAt_matrix, norm_searchInput]
      exact (one_le_sqrt_two_mul_of_half_le_sq (norm_nonneg _)
        (psdSearch_endpoint_norm (s := s) hτ j).1).trans
        (mul_le_mul_of_nonneg_right hg (norm_nonneg _))
  exact heatFamily_inClass _ _ _ _ hacc hrow hcol hne hgg

/-- The scalar family is in the class with `η = 1` and any `ḡ ≥ √2` (`g ≤ √2`). -/
theorem psdScalarFamilyAt_inClass (h : PsdRange τ s ε) {gbar : ℝ} (hg : Real.sqrt 2 ≤ gbar) :
    (psdScalarFamilyAt h).InClass 1 gbar := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  have hP := fun x => psdScalarMat_props (n := precN τ ε) (s := s)
    (by have := h.s_ge; omega) (τ / 2) x
  have hacc : ∀ x, TimeDependentODE.Accretive
      (SparseStateOverlap.matrixOperator ((psdScalarDataAt h).matrix x)) := fun x => by
    rw [psdScalarDataAt_matrix]
    exact accretive_of_posSemidef (psdScalarMat_posSemidef (τ / 2) x)
  have hrow : ∀ x i, ∑ i', ‖(psdScalarDataAt h).matrix x i i'‖ ^ 2 ≤ 1 := fun x => by
    rw [psdScalarDataAt_matrix]
    exact (hP x).2.1
  have hcol : ∀ x i', ∑ i, ‖(psdScalarDataAt h).matrix x i i'‖ ^ 2 ≤ 1 := fun x => by
    rw [psdScalarDataAt_matrix]
    exact (hP x).2.2.1
  have hne : ∀ x, heat ((psdScalarDataAt h).matrix x) τ (scalarInput (precN τ ε) s) ≠ 0 :=
    fun x => by
      rw [psdScalarDataAt_matrix]
      intro h0
      have he := (psdScalar_endpoint_norm (s := s) hτ x).1
      rw [h0, norm_zero] at he
      norm_num at he
  have hgg : ∀ x, ‖scalarInput (precN τ ε) s‖ ≤
      gbar * ‖heat ((psdScalarDataAt h).matrix x) τ (scalarInput (precN τ ε) s)‖ :=
    fun x => by
      rw [psdScalarDataAt_matrix, norm_scalarInput]
      exact (one_le_sqrt_two_mul_of_half_le_sq (norm_nonneg _)
        (psdScalar_endpoint_norm (s := s) hτ x).1).trans
        (mul_le_mul_of_nonneg_right hg (norm_nonneg _))
  exact heatFamily_inClass _ _ _ _ hacc hrow hcol hne hgg

/-- **The gadget family is homogeneous and constant-coefficient with `D_X ⪰ 0`, `B = 1`,
`T = τ` and `1 ≤ g ≤ √2`** (lines 4019-4025, 4087-4088): no source, generator
`psdSearchMat n μ s (τ/2) X` (positive semidefinite, `psdSearchMat_posSemidef`), and
`g = B/‖x(T)‖ ∈ [1, √2]` for the solution `x(t) = e^{-tD_X} x₀` (`heatFamily_solves`). -/
theorem psdSearchFamilyAt_props (h : PsdRange τ s ε)
    (j : Fin (precN τ ε) → Fin (2 ^ psdMu s)) :
    (∀ k, (psdSearchFamilyAt h).src k = 0) ∧
      (∀ k, (psdSearchFamilyAt h).data.matrix (j, k) =
        psdSearchMat (precN τ ε) (psdMu s) s (τ / 2) j) ∧
      (psdSearchFamilyAt h).mass = 1 ∧ (psdSearchFamilyAt h).T = τ ∧
      1 ≤ (psdSearchFamilyAt h).mass /
        ‖heat (psdSearchMat (precN τ ε) (psdMu s) s (τ / 2) j) τ
          (searchInput (precN τ ε) (psdMu s) s)‖ ∧
      (psdSearchFamilyAt h).mass /
        ‖heat (psdSearchMat (precN τ ε) (psdMu s) s (τ / 2) j) τ
          (searchInput (precN τ ε) (psdMu s) s)‖ ≤ Real.sqrt 2 := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  have hm : (psdSearchFamilyAt h).mass = 1 := by
    rw [psdSearchFamilyAt, heatFamily_mass, norm_searchInput]
  have he := psdSearch_endpoint_norm (s := s) hτ j
  rw [hm]
  exact ⟨fun _ => rfl, fun _ => rfl, rfl, psdSearchFamilyAt_T h,
    one_div_mem_of_half_le_sq (norm_nonneg _) he.1 he.2⟩

/-- **The scalar family is homogeneous and constant-coefficient with `D_x ⪰ 0`, `B = 1`,
`T = τ` and `1 ≤ g ≤ √2`** (lines 4019-4025, 4087-4088, 4120-4121). -/
theorem psdScalarFamilyAt_props (h : PsdRange τ s ε) (x : Fin (precN τ ε) → Bool) :
    (∀ k, (psdScalarFamilyAt h).src k = 0) ∧
      (∀ k, (psdScalarFamilyAt h).data.matrix (x, k) = psdScalarMat (precN τ ε) s (τ / 2) x) ∧
      (psdScalarFamilyAt h).mass = 1 ∧ (psdScalarFamilyAt h).T = τ ∧
      1 ≤ (psdScalarFamilyAt h).mass /
        ‖heat (psdScalarMat (precN τ ε) s (τ / 2) x) τ (scalarInput (precN τ ε) s)‖ ∧
      (psdScalarFamilyAt h).mass /
        ‖heat (psdScalarMat (precN τ ε) s (τ / 2) x) τ (scalarInput (precN τ ε) s)‖ ≤
          Real.sqrt 2 := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  have hm : (psdScalarFamilyAt h).mass = 1 := by
    rw [psdScalarFamilyAt, heatFamily_mass, norm_scalarInput]
  have he := psdScalar_endpoint_norm (s := s) hτ x
  rw [hm]
  exact ⟨fun _ => rfl, fun _ => rfl, rfl, psdScalarFamilyAt_T h,
    one_div_mem_of_half_le_sq (norm_nonneg _) he.1 he.2⟩

end

end ODELowerBoundExtensions.Psd
