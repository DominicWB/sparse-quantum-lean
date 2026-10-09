import SparseLowerBounds.Helpers.Joint.Amplify

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Tensor products of single-register matrices

Helper for `SparseLowerBounds.Query.Joint`. For matrices `f k` on `ℂ^m`,
`prodMat f` is the matrix `⊗_k f k` on `ℂ^{Fin n → Fin m}`, with entries
`Π_k f k (j k) (j' k)`. It is multiplicative, unital and compatible with `ᴴ`
and diagonals; a single factor `A` on register `k` (all other factors `1`)
acts by `Σ_b A (j k) b • Ψ (update j k b)`.
-/

namespace SparseLowerBounds.Helpers.Joint

noncomputable section
open scoped Matrix

variable {n m : ℕ}

/-- `⊗_k f k` as a matrix on `ℂ^{Fin n → Fin m}`. -/
def prodMat (f : Fin n → Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin n → Fin m) (Fin n → Fin m) ℂ :=
  Matrix.of fun j j' => ∏ k, f k (j k) (j' k)

theorem prodMat_apply (f : Fin n → Matrix (Fin m) (Fin m) ℂ) (j j' : Fin n → Fin m) :
    prodMat f j j' = ∏ k, f k (j k) (j' k) := rfl

theorem prodMat_mul (f g : Fin n → Matrix (Fin m) (Fin m) ℂ) :
    prodMat f * prodMat g = prodMat (f * g) := by
  ext j j''
  simp only [Matrix.mul_apply, prodMat_apply, Pi.mul_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

theorem exists_ne_of_ne {j j' : Fin n → Fin m} (h : j ≠ j') : ∃ k, j k ≠ j' k := by
  by_contra hc
  push Not at hc
  exact h (funext hc)

theorem prodMat_one : prodMat (1 : Fin n → Matrix (Fin m) (Fin m) ℂ) = 1 := by
  ext j j'
  simp only [prodMat_apply, Pi.one_apply, Matrix.one_apply]
  by_cases h : j = j'
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨k, hk⟩ := exists_ne_of_ne h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

theorem prodMat_conjTranspose (f : Fin n → Matrix (Fin m) (Fin m) ℂ) :
    (prodMat f)ᴴ = prodMat fun k => (f k)ᴴ := by
  ext j j'
  simp [prodMat_apply, Matrix.conjTranspose_apply, star_prod]

theorem prodMat_diagonal (d : Fin n → Fin m → ℂ) :
    prodMat (fun k => Matrix.diagonal (d k)) = Matrix.diagonal fun j => ∏ k, d k (j k) := by
  ext j j'
  simp only [prodMat_apply, Matrix.diagonal_apply]
  by_cases h : j = j'
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨k, hk⟩ := exists_ne_of_ne h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

/-- `prodMat` as a monoid homomorphism. -/
def prodMatHom : (Fin n → Matrix (Fin m) (Fin m) ℂ) →* Matrix (Fin n → Fin m) (Fin n → Fin m) ℂ where
  toFun := prodMat
  map_one' := prodMat_one
  map_mul' f g := (prodMat_mul f g).symm

theorem prodMatHom_apply (f : Fin n → Matrix (Fin m) (Fin m) ℂ) : prodMatHom f = prodMat f := rfl

/-- A single factor `A` on register `k` acts by `Σ_b A (j k) b • Ψ (update j k b)`. -/
theorem sum_prodMat_update_smul {K : Type*} [AddCommMonoid K] [Module ℂ K] (k : Fin n)
    (A : Matrix (Fin m) (Fin m) ℂ) (Ψ : (Fin n → Fin m) → K) (j : Fin n → Fin m) :
    ∑ j', prodMat (Function.update 1 k A) j j' • Ψ j' =
      ∑ b, A (j k) b • Ψ (Function.update j k b) := by
  classical
  have hzero : ∀ j' ∈ (Finset.univ : Finset (Fin n → Fin m)),
      j' ∉ Finset.univ.image (fun b => Function.update j k b) →
        prodMat (Function.update 1 k A) j j' • Ψ j' = 0 := by
    intro j' _ hj'
    have hex : ∃ l, l ≠ k ∧ j l ≠ j' l := by
      by_contra hc
      push Not at hc
      apply hj'
      refine Finset.mem_image.2 ⟨j' k, Finset.mem_univ _, ?_⟩
      funext l
      by_cases hl : l = k
      · subst hl
        simp
      · rw [Function.update_of_ne hl]
        exact hc l hl
    obtain ⟨l, hlk, hl⟩ := hex
    rw [prodMat_apply, Finset.prod_eq_zero (Finset.mem_univ l), zero_smul]
    simp [Function.update_of_ne hlk, hl]
  rw [← Finset.sum_subset (Finset.subset_univ _) hzero,
    Finset.sum_image (fun b _ b' _ h => Function.update_injective j k h)]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  rw [prodMat_apply, Fintype.prod_eq_single k]
  · simp
  · intro l hl
    simp [Function.update_of_ne hl]

/-- A list product with at most one factor different from `1`. -/
theorem ofFn_prod_eq_of_eq_one {M : Type*} [Monoid M] :
    ∀ {r : ℕ} (f : Fin r → M) (l : Fin r), (∀ k, k ≠ l → f k = 1) → (List.ofFn f).prod = f l
  | 0, _, l, _ => l.elim0
  | r + 1, f, l, h => by
    rw [List.ofFn_succ, List.prod_cons]
    by_cases hl : l = 0
    · subst hl
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact h _ (Fin.succ_ne_zero i)
    · obtain ⟨l', rfl⟩ := Fin.exists_succ_eq.2 hl
      rw [h 0 (Ne.symm hl), one_mul]
      exact ofFn_prod_eq_of_eq_one (fun i => f i.succ) l'
        (fun k hk => h _ fun e => hk (Fin.succ_injective _ e))

/-- The product of the single-register factors `update 1 k A` is `fun _ => A`. -/
theorem ofFn_update_one_prod {M : Type*} [Monoid M] (A : M) :
    (List.ofFn fun k : Fin n => Function.update (1 : Fin n → M) k A).prod = fun _ => A := by
  funext l
  rw [Pi.list_prod_apply, List.map_ofFn]
  refine (ofFn_prod_eq_of_eq_one _ l fun k hk => ?_).trans ?_
  · simp [Function.update_of_ne (Ne.symm hk)]
  · simp

end

end SparseLowerBounds.Helpers.Joint
end
