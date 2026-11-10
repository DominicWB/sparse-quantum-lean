import SparseHamiltonian.MaskedProgram
import SparseHamiltonian.OracleTransport

/-!
# Cells, sectors, the signal qubit and the combination `(I - U)/2`

Register bookkeeping for Corollary `qls:cor:separate`.

* `cellIn i` puts a vector into cell `i` of a finite Hilbert sum; its adjoint reads that cell
  (`cellIn_adjoint`). `sector f` puts a whole sum into the flag sector `f` of `⨁_{Bool × α}`.
  Vectors with disjoint supports are orthogonal (`inner_eq_zero_of_disjoint`).
* `Pair K = K ⊕ K` carries a signal qubit. `had` is the Hadamard gate on it, a self-adjoint
  involution (`had_unitary`).
* `lcu U = had · (I ⊕ -U) · had` maps `|0⟩ v` to `|0⟩ (I - U) v/2 + |1⟩ (I + U) v/2`
  (`lcu_cellIn_false`, `lcu_cellIn_true`). Its selected block is `(I - U)/2` with normalisation
  one (`lcu_block`), on every vector.
* `prodCurry` regroups `⨁_{α × β} K` as `⨁_α ⨁_β K`; a mask that factors through the two
  coordinates becomes a nested mask (`prodCurry_masked`).
-/

set_option autoImplicit false

namespace SparseLinearSystems.Separate

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit
open scoped InnerProduct ComplexConjugate

section Unitary

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem neg_unitary {U : K →L[ℂ] K} (hU : IsUnitary U) : IsUnitary (-U) := by
  constructor
  · rw [star_neg, neg_mul_neg]; exact hU.1
  · rw [star_neg, neg_mul_neg]; exact hU.2

/-- A unitary preserves norms. -/
theorem IsUnitary.norm_apply {U : K →L[ℂ] K} (hU : IsUnitary U) (v : K) : ‖U v‖ = ‖v‖ :=
  (U.norm_map_iff_adjoint_comp_self).mpr (by rw [← star_eq_adjoint]; exact hU.1) v

end Unitary

section Cells

variable {α K : Type*} [Fintype α] [DecidableEq α]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The injection of `K` into the cell `i` of the finite Hilbert sum `⨁_α K`. -/
def cellIn (i : α) : K →L[ℂ] PiLp 2 (fun _ : α => K) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : α => K)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : α => K) i

/-- The coordinate of the cell `i`. -/
def cellOut (i : α) : PiLp 2 (fun _ : α => K) →L[ℂ] K :=
  PiLp.proj (𝕜 := ℂ) (p := 2) (β := fun _ : α => K) i

omit [Fintype α] in
@[simp] theorem cellIn_apply (i : α) (v : K) (j : α) :
    cellIn i v j = if j = i then v else 0 := by
  simp [cellIn]

omit [Fintype α] [DecidableEq α] in
@[simp] theorem cellOut_apply (i : α) (u : PiLp 2 (fun _ : α => K)) : cellOut i u = u i := rfl

theorem norm_cellIn (i : α) (v : K) : ‖(cellIn i v : PiLp 2 (fun _ : α => K))‖ = ‖v‖ := by
  change ‖PiLp.single (β := fun _ : α => K) 2 i v‖ = ‖v‖
  exact PiLp.norm_single 2 (fun _ : α => K) i v

theorem cellIn_adjoint [CompleteSpace K] (i : α) : (cellIn (K := K) i)† = cellOut i := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem cellIn_isometry [CompleteSpace K] (i : α) : (cellIn (K := K) i)† ∘L cellIn i = 1 := by
  rw [cellIn_adjoint]
  ext v
  simp

omit [DecidableEq α] in
/-- Vectors with disjoint supports are orthogonal. -/
theorem inner_eq_zero_of_disjoint (u v : PiLp 2 (fun _ : α => K))
    (h : ∀ j, u j = 0 ∨ v j = 0) : inner ℂ u v = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro j _
  rcases h j with h | h <;> simp [h]

/-- The flag sector `f` of `⨁_{Bool × α} K`, as an isometry. -/
def sectorIso (f : Bool) : PiLp 2 (fun _ : α => K) →ₗᵢ[ℂ] PiLp 2 (fun _ : Bool × α => K) where
  toFun v := WithLp.toLp 2 (fun p => if p.1 = f then v p.2 else 0)
  map_add' u v := by
    apply PiLp.ext
    intro p
    by_cases h : p.1 = f <;> simp [h]
  map_smul' c v := by
    apply PiLp.ext
    intro p
    by_cases h : p.1 = f <;> simp [h]
  norm_map' v := by
    rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2, Fintype.sum_prod_type, Fintype.sum_bool]
    cases f <;> simp

/-- The flag sector `f` of `⨁_{Bool × α} K`. -/
def sector (f : Bool) : PiLp 2 (fun _ : α => K) →L[ℂ] PiLp 2 (fun _ : Bool × α => K) :=
  (sectorIso f).toContinuousLinearMap

omit [DecidableEq α] in
@[simp] theorem sector_apply (f : Bool) (v : PiLp 2 (fun _ : α => K)) (p : Bool × α) :
    sector f v p = if p.1 = f then v p.2 else 0 := by
  simp only [sector, LinearIsometry.coe_toContinuousLinearMap]
  rfl

omit [DecidableEq α] in
theorem sector_isometry [CompleteSpace K] (f : Bool) :
    (sector (α := α) (K := K) f)† ∘L sector f = 1 := by
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp
  intro v
  exact (sectorIso f).norm_map v

end Cells

section Pair

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Two copies of `K`, indexed by a signal qubit. -/
abbrev Pair (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  PiLp 2 (fun _ : Bool => K)

/-- The amplitude `1/√2`. -/
def invSqrtTwo : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem invSqrtTwo_mul_self : invSqrtTwo * invSqrtTwo = (2 : ℂ)⁻¹ := by
  rw [invSqrtTwo, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  push_cast
  rfl

theorem conj_invSqrtTwo : (starRingEnd ℂ) invSqrtTwo = invSqrtTwo := Complex.conj_ofReal _

/-- The Hadamard gate on the signal qubit. -/
def had : Pair K →L[ℂ] Pair K :=
  invSqrtTwo • (cellIn false ∘L (cellOut false + cellOut true) +
    cellIn true ∘L (cellOut false - cellOut true))

@[simp] theorem had_false (g : Pair K) : had g false = invSqrtTwo • (g false + g true) := by
  simp [had]

@[simp] theorem had_true (g : Pair K) : had g true = invSqrtTwo • (g false - g true) := by
  simp [had]

theorem had_mul_had : (had : Pair K →L[ℂ] Pair K) * had = 1 := by
  apply ContinuousLinearMap.ext
  intro g
  apply PiLp.ext
  intro c
  have h := invSqrtTwo_mul_self
  cases c <;>
  · simp only [mul_apply_eq_comp, one_apply_eq_self, had_false, had_true, smul_add, smul_sub,
      smul_smul, h]
    module

theorem had_adjoint [CompleteSpace K] : (had : Pair K →L[ℂ] Pair K)† = had := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_bool, Fintype.sum_bool]
  simp only [had_false, had_true, inner_smul_left, inner_smul_right, inner_add_left,
    inner_add_right, inner_sub_left, inner_sub_right, conj_invSqrtTwo]
  ring

theorem had_unitary [CompleteSpace K] : IsUnitary (had : Pair K →L[ℂ] Pair K) := by
  constructor
  · rw [star_eq_adjoint, had_adjoint, had_mul_had]
  · rw [star_eq_adjoint, had_adjoint, had_mul_had]

/-- **The combination `(I - U)/2`**: Hadamard, `I` or `-U` on the signal qubit, Hadamard. -/
def lcu (U : K →L[ℂ] K) : Pair K →L[ℂ] Pair K :=
  had * MaskedProgram.masked (fun c : Bool => c) (-U) * had

theorem lcu_unitary [CompleteSpace K] {U : K →L[ℂ] K} (hU : IsUnitary U) : IsUnitary (lcu U) :=
  (had_unitary.mul (MaskedProgram.masked_unitary _ _ (neg_unitary hU))).mul had_unitary

theorem lcu_false (U : K →L[ℂ] K) (g : Pair K) :
    lcu U g false = (2 : ℂ)⁻¹ • ((g false + g true) - U (g false - g true)) := by
  have h := invSqrtTwo_mul_self
  simp only [lcu, mul_apply_eq_comp, had_false, had_true, MaskedProgram.masked_apply,
    if_true, if_false, Bool.false_eq_true, neg_apply, map_smul, smul_add, smul_neg, smul_smul, h]
  module

theorem lcu_true (U : K →L[ℂ] K) (g : Pair K) :
    lcu U g true = (2 : ℂ)⁻¹ • ((g false + g true) + U (g false - g true)) := by
  have h := invSqrtTwo_mul_self
  simp only [lcu, mul_apply_eq_comp, had_false, had_true, MaskedProgram.masked_apply,
    if_true, if_false, Bool.false_eq_true, neg_apply, map_smul, map_sub, smul_add, smul_sub,
    smul_neg, smul_smul, h]
  module

theorem lcu_cellIn_false (U : K →L[ℂ] K) (v : K) :
    lcu U (cellIn false v) false = (2 : ℂ)⁻¹ • (v - U v) := by
  rw [lcu_false]
  simp

theorem lcu_cellIn_true (U : K →L[ℂ] K) (v : K) :
    lcu U (cellIn false v) true = (2 : ℂ)⁻¹ • (v + U v) := by
  rw [lcu_true]
  simp

/-- **The selected block of `lcu U`** is `(I - U)/2`, with normalisation one. -/
theorem lcu_block [CompleteSpace K] (U : K →L[ℂ] K) (v : K) :
    ((cellIn false)†) (lcu U (cellIn false v)) = (2 : ℂ)⁻¹ • (v - U v) := by
  rw [cellIn_adjoint, cellOut_apply, lcu_cellIn_false]

end Pair

section Curry

variable {α β K : Type*} [Fintype α] [Fintype β]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Regroup the cells of `⨁_{α × β} K` as `⨁_α ⨁_β K`. -/
def prodCurry :
    PiLp 2 (fun _ : α × β => K) ≃ₗᵢ[ℂ] PiLp 2 (fun _ : α => PiLp 2 (fun _ : β => K)) where
  toFun u := WithLp.toLp 2 (fun a => WithLp.toLp 2 (fun b => u (a, b)))
  invFun g := WithLp.toLp 2 (fun p => g p.1 p.2)
  map_add' u v := rfl
  map_smul' c u := rfl
  left_inv u := rfl
  right_inv g := rfl
  norm_map' u := by
    change ‖(WithLp.toLp 2 (fun a => WithLp.toLp 2 (fun b => u (a, b))) :
      PiLp 2 (fun _ : α => PiLp 2 (fun _ : β => K)))‖ = ‖u‖
    rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2, Fintype.sum_prod_type]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [PiLp.toLp_apply, PiLp.norm_sq_eq_of_L2]

@[simp] theorem prodCurry_apply (u : PiLp 2 (fun _ : α × β => K)) (a : α) (b : β) :
    prodCurry u a b = u (a, b) := rfl

@[simp] theorem prodCurry_symm_apply (g : PiLp 2 (fun _ : α => PiLp 2 (fun _ : β => K)))
    (p : α × β) : prodCurry.symm g p = g p.1 p.2 := rfl

/-- **Masks through the regrouping.** A mask `mh a ∧ sel b` on `⨁_{α × β}` is the nested mask
`mh` of the mask `sel`. -/
theorem prodCurry_masked [CompleteSpace K] (mh : α → Bool) (sel : β → Bool) (U : K →L[ℂ] K)
    (g : PiLp 2 (fun _ : α => PiLp 2 (fun _ : β => K))) :
    MaskedProgram.masked (fun p : α × β => mh p.1 && sel p.2) U (prodCurry.symm g) =
      prodCurry.symm (MaskedProgram.masked mh (MaskedProgram.masked sel U) g) := by
  apply PiLp.ext
  intro p
  simp only [MaskedProgram.masked_apply, prodCurry_symm_apply]
  by_cases h1 : mh p.1 <;> by_cases h2 : sel p.2 <;> simp [h1, h2]

end Curry

end

end SparseLinearSystems.Separate
