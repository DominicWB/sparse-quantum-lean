import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Families over hidden inputs and Kronecker weights

The weight-growth argument works with families `ψ = (ψ_j)` of vectors indexed by the hidden
inputs `j`, with the `ℓ²` norm (`Fam X V`).  A complex matrix `A` on the index set acts by
`(act A ψ)_j = ∑_{j'} A j j' ψ_{j'}`; this is the matrix tensored with the identity of `V`.

The hidden inputs are functions `j : ι → Fin m` (one marked position per coordinate).  The
Kronecker power `kron a` of a one-coordinate matrix has entries `∏_b a (j b) (j' b)`.
Splitting at one coordinate `c` (`splitEquiv`) separates `j c` from the other coordinates;
`slice_act_splitMat` reduces the action of a split matrix to a one-coordinate action on
slices, and `norm_sq_act_kron_le` bounds a Kronecker power by the one-coordinate bound.
-/

namespace LinearSystemLowerBound

noncomputable section
open scoped BigOperators InnerProductSpace Matrix

universe u

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Families of vectors indexed by a finite set, with the `ℓ²` norm. -/
abbrev Fam (X V : Type*) := PiLp 2 (fun _ : X => V)

omit [InnerProductSpace ℂ V] in
theorem norm_sq_fam {X : Type*} [Fintype X] (ψ : Fam X V) : ‖ψ‖ ^ 2 = ∑ j, ‖ψ j‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ ψ

/-- `⟪u, u⟫ = ‖u‖²` with the concrete complex coercion. -/
theorem inner_self_cpx (u : V) : ⟪u, u⟫_ℂ = ((‖u‖ : ℝ) : ℂ) ^ 2 :=
  inner_self_eq_norm_sq_to_K u

theorem inner_fam {X : Type*} [Fintype X] (ψ φ : Fam X V) :
    ⟪ψ, φ⟫_ℂ = ∑ j, ⟪ψ j, φ j⟫_ℂ :=
  PiLp.inner_apply ψ φ

/-! ### Matrices acting on the index -/

section Act

variable {X : Type*} [Fintype X]

/-- A complex matrix acting on the index of a family. -/
def act (A : Matrix X X ℂ) (ψ : Fam X V) : Fam X V :=
  WithLp.toLp 2 (fun j => ∑ j', A j j' • ψ j')

@[simp] theorem act_apply (A : Matrix X X ℂ) (ψ : Fam X V) (j : X) :
    act A ψ j = ∑ j', A j j' • ψ j' := rfl

theorem act_add (A : Matrix X X ℂ) (ψ φ : Fam X V) : act A (ψ + φ) = act A ψ + act A φ := by
  ext j
  simp only [act_apply, PiLp.add_apply, smul_add, Finset.sum_add_distrib]

theorem act_sub (A : Matrix X X ℂ) (ψ φ : Fam X V) : act A (ψ - φ) = act A ψ - act A φ := by
  ext j
  simp only [act_apply, PiLp.sub_apply, smul_sub, Finset.sum_sub_distrib]

theorem act_smul (A : Matrix X X ℂ) (z : ℂ) (ψ : Fam X V) : act A (z • ψ) = z • act A ψ := by
  ext j
  simp only [act_apply, PiLp.smul_apply, Finset.smul_sum, smul_comm z]

theorem act_mul (A B : Matrix X X ℂ) (ψ : Fam X V) : act (A * B) ψ = act A (act B ψ) := by
  ext j
  simp only [act_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem act_one [DecidableEq X] (ψ : Fam X V) : act 1 ψ = ψ := by
  ext j
  simp [Matrix.one_apply]

theorem act_add_matrix (A B : Matrix X X ℂ) (ψ : Fam X V) :
    act (A + B) ψ = act A ψ + act B ψ := by
  ext j
  simp only [act_apply, Matrix.add_apply, add_smul, Finset.sum_add_distrib, PiLp.add_apply]

theorem act_sub_matrix (A B : Matrix X X ℂ) (ψ : Fam X V) :
    act (A - B) ψ = act A ψ - act B ψ := by
  ext j
  simp only [act_apply, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, PiLp.sub_apply]

theorem act_smul_matrix (z : ℂ) (A : Matrix X X ℂ) (ψ : Fam X V) :
    act (z • A) ψ = z • act A ψ := by
  ext j
  simp only [act_apply, Matrix.smul_apply, smul_eq_mul, PiLp.smul_apply, Finset.smul_sum,
    mul_smul]

/-- The action is the matrix tensored with the identity: its adjoint is `Aᴴ`. -/
theorem inner_act (A : Matrix X X ℂ) (ψ φ : Fam X V) :
    ⟪act A ψ, φ⟫_ℂ = ⟪ψ, act Aᴴ φ⟫_ℂ := by
  simp only [inner_fam, act_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro j' _
  simp [RCLike.star_def]

/-- `‖A φ‖² = Re ⟪φ, AᴴA φ⟫`. -/
theorem norm_sq_act_eq_inner (A : Matrix X X ℂ) (φ : Fam X V) :
    ‖act A φ‖ ^ 2 = (⟪φ, act (Aᴴ * A) φ⟫_ℂ).re := by
  have h : ‖act A φ‖ ^ 2 = (⟪act A φ, act A φ⟫_ℂ).re := by
    rw [inner_self_cpx]
    norm_cast
  rw [h, inner_act, ← act_mul]

/-- A matrix with `Aᴴ A = 1` preserves family norms. -/
theorem norm_act_of_unitary [DecidableEq X] (A : Matrix X X ℂ) (hA : Aᴴ * A = 1)
    (φ : Fam X V) : ‖act A φ‖ = ‖φ‖ := by
  have h : ‖act A φ‖ ^ 2 = ‖φ‖ ^ 2 := by
    rw [norm_sq_act_eq_inner, hA, act_one, inner_self_cpx]
    norm_cast
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- The joint operator of an input-dependent family of operators. -/
def joint (O : X → V →L[ℂ] V) (ψ : Fam X V) : Fam X V :=
  WithLp.toLp 2 (fun j => O j (ψ j))

omit [Fintype X] in
@[simp] theorem joint_apply (O : X → V →L[ℂ] V) (ψ : Fam X V) (j : X) :
    joint O ψ j = O j (ψ j) := rfl

omit [Fintype X] in
theorem joint_comp (O O' : X → V →L[ℂ] V) (ψ : Fam X V) :
    joint (fun j => O j * O' j) ψ = joint O (joint O' ψ) := rfl

/-- An input-independent operator commutes with every index action. -/
theorem act_joint_const (A : Matrix X X ℂ) (U : V →L[ℂ] V) (ψ : Fam X V) :
    act A (joint (fun _ => U) ψ) = joint (fun _ => U) (act A ψ) := by
  ext j
  simp only [act_apply, joint_apply, map_sum, map_smul]

/-- A family of norm-preserving operators preserves the family norm. -/
theorem norm_joint (O : X → V →L[ℂ] V) (hO : ∀ j v, ‖O j v‖ = ‖v‖) (ψ : Fam X V) :
    ‖joint O ψ‖ = ‖ψ‖ := by
  have h : ‖joint O ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [norm_sq_fam, norm_sq_fam]
    simp only [joint_apply, hO]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- Scalar weights per index. -/
def scale (g : X → ℂ) (ψ : Fam X V) : Fam X V :=
  WithLp.toLp 2 (fun j => g j • ψ j)

omit [Fintype X] in
@[simp] theorem scale_apply (g : X → ℂ) (ψ : Fam X V) (j : X) :
    scale g ψ j = g j • ψ j := rfl

omit [Fintype X] in
theorem joint_scale (O : X → V →L[ℂ] V) (g : X → ℂ) (ψ : Fam X V) :
    joint O (scale g ψ) = scale g (joint O ψ) := by
  ext j
  simp only [joint_apply, scale_apply, map_smul]

/-- Cauchy--Schwarz for families. -/
theorem norm_inner_fam_le (ψ φ : Fam X V) : ‖⟪ψ, φ⟫_ℂ‖ ≤ ‖ψ‖ * ‖φ‖ :=
  norm_inner_le_norm ψ φ

end Act

/-! ### Kronecker powers -/

section Kron

variable {ι : Type*} [Fintype ι] {m : ℕ}

/-- The Kronecker power of a one-coordinate matrix: entries `∏_b a (j b) (j' b)`. -/
def kron (a : Matrix (Fin m) (Fin m) ℂ) : Matrix (ι → Fin m) (ι → Fin m) ℂ :=
  Matrix.of fun j j' => ∏ b, a (j b) (j' b)

@[simp] theorem kron_apply (a : Matrix (Fin m) (Fin m) ℂ) (j j' : ι → Fin m) :
    kron a j j' = ∏ b, a (j b) (j' b) := rfl

theorem kron_mul [DecidableEq ι] (a a' : Matrix (Fin m) (Fin m) ℂ) :
    kron (ι := ι) a * kron a' = kron (a * a') := by
  ext j j'
  simp only [Matrix.mul_apply, kron_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib]

theorem kron_one [DecidableEq ι] : kron (ι := ι) (1 : Matrix (Fin m) (Fin m) ℂ) = 1 := by
  ext j j'
  simp only [kron_apply, Matrix.one_apply]
  by_cases h : j = j'
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨b, hb⟩ : ∃ b, j b ≠ j' b := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ b) (if_neg hb)

theorem kron_conjTranspose (a : Matrix (Fin m) (Fin m) ℂ) :
    (kron (ι := ι) a)ᴴ = kron aᴴ := by
  ext j j'
  simp only [Matrix.conjTranspose_apply, kron_apply]
  rw [star_prod]

theorem kron_diagonal [DecidableEq ι] (d : Fin m → ℂ) :
    kron (ι := ι) (Matrix.diagonal d) = Matrix.diagonal (fun j => ∏ b, d (j b)) := by
  ext j j'
  simp only [kron_apply, Matrix.diagonal_apply]
  by_cases h : j = j'
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨b, hb⟩ : ∃ b, j b ≠ j' b := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ b) (if_neg hb)

end Kron

/-! ### Splitting at one coordinate -/

section Split

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {m : ℕ} (c : ι)

/-- The coordinates other than `c`. -/
abbrev Rest (c : ι) := {b : ι // b ≠ c}

/-- Hidden inputs as the value at `c` and the values at the other coordinates. -/
def splitEquiv : Fin m × (Rest c → Fin m) ≃ (ι → Fin m) :=
  (Equiv.funSplitAt c (Fin m)).symm

omit [Fintype ι] in
@[simp] theorem splitEquiv_self (q : Fin m) (r : Rest c → Fin m) :
    splitEquiv c (q, r) c = q := by
  simp [splitEquiv, Equiv.funSplitAt_symm_apply]

omit [Fintype ι] in
@[simp] theorem splitEquiv_rest (q : Fin m) (r : Rest c → Fin m) (b : Rest c) :
    splitEquiv c (q, r) b = r b := by
  simp [splitEquiv, Equiv.funSplitAt_symm_apply, b.2]

/-- The restriction to the other coordinates. -/
def rest (j : ι → Fin m) : Rest c → Fin m := fun b => j b

omit [Fintype ι] in
@[simp] theorem rest_splitEquiv (q : Fin m) (r : Rest c → Fin m) :
    rest c (splitEquiv c (q, r)) = r := by
  funext b
  simp [rest]

omit [Fintype ι] in
theorem splitEquiv_symm (j : ι → Fin m) : (splitEquiv c).symm j = (j c, rest c j) := rfl

theorem kron_split (a : Matrix (Fin m) (Fin m) ℂ) (j j' : ι → Fin m) :
    kron a j j' = a (j c) (j' c) * kron a (rest c j) (rest c j') := by
  simp only [kron_apply]
  rw [Fintype.prod_eq_mul_prod_compl c]
  congr 1
  exact Finset.prod_subtype ({c}ᶜ : Finset ι) (fun b => by simp) (fun b => a (j b) (j' b))

/-- A matrix acting as `a` on coordinate `c` and as `B` on the other coordinates. -/
def splitMat (a : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Rest c → Fin m) (Rest c → Fin m) ℂ) :
    Matrix (ι → Fin m) (ι → Fin m) ℂ :=
  Matrix.of fun j j' => a (j c) (j' c) * B (rest c j) (rest c j')

theorem kron_eq_splitMat (a : Matrix (Fin m) (Fin m) ℂ) :
    kron (ι := ι) a = splitMat c a (kron a) := by
  ext j j'
  rw [kron_split c]
  rfl

/-- Fix the other coordinates: a family over the values at `c`. -/
def slice (ψ : Fam (ι → Fin m) V) (r : Rest c → Fin m) : Fam (Fin m) V :=
  WithLp.toLp 2 (fun q => ψ (splitEquiv c (q, r)))

/-- Fix the value at `c`: a family over the other coordinates. -/
def fiber (ψ : Fam (ι → Fin m) V) (q : Fin m) : Fam (Rest c → Fin m) V :=
  WithLp.toLp 2 (fun r => ψ (splitEquiv c (q, r)))

omit [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι] in
@[simp] theorem slice_apply (ψ : Fam (ι → Fin m) V) (r : Rest c → Fin m) (q : Fin m) :
    slice c ψ r q = ψ (splitEquiv c (q, r)) := rfl

omit [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι] in
@[simp] theorem fiber_apply (ψ : Fam (ι → Fin m) V) (q : Fin m) (r : Rest c → Fin m) :
    fiber c ψ q r = ψ (splitEquiv c (q, r)) := rfl

theorem sum_split {M : Type*} [AddCommMonoid M] (f : (ι → Fin m) → M) :
    ∑ j, f j = ∑ q, ∑ r, f (splitEquiv c (q, r)) := by
  rw [← Fintype.sum_prod_type', ← (splitEquiv c).sum_comp]

omit [InnerProductSpace ℂ V] in
theorem norm_sq_eq_sum_slice (ψ : Fam (ι → Fin m) V) :
    ‖ψ‖ ^ 2 = ∑ r, ‖slice c ψ r‖ ^ 2 := by
  rw [norm_sq_fam, sum_split c, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [norm_sq_fam]
  rfl

omit [InnerProductSpace ℂ V] in
theorem norm_sq_eq_sum_fiber (ψ : Fam (ι → Fin m) V) :
    ‖ψ‖ ^ 2 = ∑ q, ‖fiber c ψ q‖ ^ 2 := by
  rw [norm_sq_fam, sum_split c]
  apply Finset.sum_congr rfl
  intro q _
  rw [norm_sq_fam]
  rfl

/-- **Splitting of an action.**  On a slice, a split matrix acts as `a` on the values at
`c`, applied to the slice of the `B`-transformed fibers. -/
theorem slice_act_splitMat (a : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Rest c → Fin m) (Rest c → Fin m) ℂ) (ψ : Fam (ι → Fin m) V)
    (r : Rest c → Fin m) :
    slice c (act (splitMat c a B) ψ) r =
      act a (WithLp.toLp 2 (fun q' => act B (fiber c ψ q') r)) := by
  ext q
  simp only [slice_apply, act_apply, fiber_apply]
  rw [sum_split c]
  apply Finset.sum_congr rfl
  intro q' _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r' _
  simp only [splitMat, Matrix.of_apply, splitEquiv_self, rest_splitEquiv, mul_smul]

theorem norm_sq_act_splitMat (a : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Rest c → Fin m) (Rest c → Fin m) ℂ) (ψ : Fam (ι → Fin m) V) :
    ‖act (splitMat c a B) ψ‖ ^ 2 =
      ∑ r, ‖act a (WithLp.toLp 2 (fun q' => act B (fiber c ψ q') r))‖ ^ 2 := by
  rw [norm_sq_eq_sum_slice c]
  apply Finset.sum_congr rfl
  intro r _
  rw [slice_act_splitMat]

/-- The slices of the transformed fibers carry the total norm of the transformed fibers. -/
theorem sum_norm_sq_inner (B : Matrix (Rest c → Fin m) (Rest c → Fin m) ℂ)
    (ψ : Fam (ι → Fin m) V) :
    ∑ r, ‖(WithLp.toLp 2 (fun q' => act B (fiber c ψ q') r) : Fam (Fin m) V)‖ ^ 2 =
      ∑ q, ‖act B (fiber c ψ q)‖ ^ 2 := by
  simp only [norm_sq_fam]
  rw [Finset.sum_comm]

end Split

/-! ### Kronecker powers of a bounded one-coordinate matrix -/

theorem card_rest {ι : Type u} [Fintype ι] [DecidableEq ι] (c : ι) :
    Fintype.card (Rest c) = Fintype.card ι - 1 := by
  simp [Rest, Fintype.card_subtype_compl]

/-- **Kronecker bound.**  If a one-coordinate matrix satisfies `‖a φ‖² ≤ C ‖φ‖²` on every
family over `Fin m` with values in `V`, its Kronecker power over `k` coordinates satisfies
the same bound with `C ^ k`. -/
theorem norm_sq_act_kron_le {m : ℕ} (a : Matrix (Fin m) (Fin m) ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ φ : Fam (Fin m) V, ‖act a φ‖ ^ 2 ≤ C * ‖φ‖ ^ 2) :
    ∀ (k : ℕ) (ι : Type u) [Fintype ι] [DecidableEq ι], Fintype.card ι = k →
      ∀ ψ : Fam (ι → Fin m) V, ‖act (kron a) ψ‖ ^ 2 ≤ C ^ k * ‖ψ‖ ^ 2 := by
  intro k
  induction k with
  | zero =>
      intro ι _ _ hk ψ
      haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hk
      have hK : kron (ι := ι) a = 1 := by
        ext j j'
        have hj : j = j' := Subsingleton.elim _ _
        subst hj
        simp
      rw [hK, act_one, pow_zero, one_mul]
  | succ k ih =>
      intro ι _ _ hk ψ
      have hne : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
      obtain ⟨c⟩ := hne
      have hrest : Fintype.card (Rest c) = k := by rw [card_rest, hk]; rfl
      rw [kron_eq_splitMat c, norm_sq_act_splitMat]
      calc
        _ ≤ ∑ r, C * ‖(WithLp.toLp 2 (fun q' => act (kron a) (fiber c ψ q') r) :
              Fam (Fin m) V)‖ ^ 2 :=
          Finset.sum_le_sum fun r _ => ha _
        _ = C * ∑ q, ‖act (kron a) (fiber c ψ q)‖ ^ 2 := by
          rw [← Finset.mul_sum, sum_norm_sq_inner]
        _ ≤ C * ∑ q, C ^ k * ‖fiber c ψ q‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hC
          exact Finset.sum_le_sum fun q _ => ih (Rest c) hrest _
        _ = C ^ (k + 1) * ‖ψ‖ ^ 2 := by
          rw [norm_sq_eq_sum_fiber c ψ, ← Finset.mul_sum, ← mul_assoc, pow_succ']

end

end LinearSystemLowerBound
