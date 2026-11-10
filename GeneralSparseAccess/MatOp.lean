import GateEfficientBinary.Sparse.Oracles

/-!
# Register operators as payload-free matrices

The register operators used by the padded oracles act on the configurations of their wires and
leave the payload `R` untouched: each is `matOp M` for a matrix `M` on configurations that does not
depend on `R`. This file records

* the matrices of permutations of configurations (`permOp_eq_matOp`) and of operators on exposed
  wires selected by the other wires (`localOp_matOp`);
* that `matOp` is injective on scalar payloads (`matOp_injective`);
* the operator `ofMat φ M` on `ℓ²(ι)` whose configuration matrix along `φ : Cfg V ≃ ι` is `M`
  (`toMat_ofMat`): its qubit lift is `matOp M` for every payload (`qlift_ofMat`), it is unitary when
  `matOp M` is unitary on scalar payloads (`ofMat_isUnitary`), and it maps a basis vector to a basis
  vector when the corresponding column of `M` is a standard basis column (`ofMat_single`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralSparseAccess

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateBinary
open SparseHamiltonian.OracleCircuit
open scoped InnerProduct

section Mat

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The permutation matrix of a permutation of configurations. -/
def permMat (e : Cfg V ≃ Cfg V) : Matrix (Cfg V) (Cfg V) ℂ :=
  fun b c => if b = e c then 1 else 0

omit [CompleteSpace R] in
/-- A permutation of configurations is the matrix of the permutation. -/
theorem permOp_eq_matOp (e : Cfg V ≃ Cfg V) : permOp (Q := R) e = matOp (permMat e) := by
  ext ψ b
  rw [permOp_apply, matOp_apply, Finset.sum_eq_single (e.symm b)]
  · simp [permMat]
  · intro c _ hc
    have h : b ≠ e c := fun h => hc (by rw [h, Equiv.symm_apply_apply])
    simp [permMat, h]
  · intro h
    exact absurd (Finset.mem_univ _) h

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The matrix of an operator on the wires `ι` selected by the configuration of the other
wires. -/
def locMat (ι : A → V) (M : Cfg V → Matrix (Cfg A) (Cfg A) ℂ) : Matrix (Cfg V) (Cfg V) ℂ :=
  fun x y => if outPart ι y = outPart ι x then
    M (clearCfg ι x) (fun a => x (ι a)) (fun a => y (ι a)) else 0

/-- An operator on exposed wires, selected by the other wires, is the matrix `locMat`. -/
theorem localOp_matOp {ι : A → V} (hι : Function.Injective ι)
    (M : Cfg V → Matrix (Cfg A) (Cfg A) ℂ) :
    localOp ι hι (fun x => matOp (Q := R) (M x)) = matOp (locMat ι M) := by
  ext ψ x
  rw [localOp_apply, matOp_apply, matOp_apply]
  symm
  rw [← (splitCfg ι hι).symm.sum_comp, Fintype.sum_prod_type,
    Finset.sum_eq_single (outPart ι x)]
  · apply Finset.sum_congr rfl
    intro c _
    change (if outPart ι (joinCfg ι (outPart ι x) c) = outPart ι x then
        M (clearCfg ι x) (fun a => x (ι a)) (fun a => joinCfg ι (outPart ι x) c (ι a))
      else 0) • ψ (joinCfg ι (outPart ι x) c) = _
    rw [outPart_joinCfg, if_pos rfl]
    have hc : (fun a => joinCfg ι (outPart ι x) c (ι a)) = c :=
      funext (joinCfg_apply_ι hι _ c)
    rw [hc, slice_apply]
  · intro o _ ho
    apply Finset.sum_eq_zero
    intro c _
    change (if outPart ι (joinCfg ι o c) = outPart ι x then _ else 0) • _ = 0
    rw [outPart_joinCfg, if_neg ho, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [CompleteSpace R] in
/-- The coordinates of `matOp M` on a basis vector. -/
theorem matOp_bas_apply (M : Matrix (Cfg V) (Cfg V) ℂ) (c : Cfg V) (q : R) (b : Cfg V) :
    matOp M (bas c q) b = M b c • q := by
  rw [matOp_apply, Finset.sum_eq_single c]
  · rw [bas_apply, if_pos rfl]
  · intro c' _ hc'
    rw [bas_apply, if_neg hc', smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [CompleteSpace R] in
/-- `matOp M` on a basis vector. -/
theorem matOp_bas (M : Matrix (Cfg V) (Cfg V) ℂ) (c : Cfg V) (q : R) :
    matOp M (bas c q) = ∑ c', M c' c • bas c' q := by
  apply PiLp.ext
  intro b
  rw [matOp_bas_apply, WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single b]
  · rw [WithLp.ofLp_smul, Pi.smul_apply, bas_apply, if_pos rfl]
  · intro c' _ hc'
    rw [WithLp.ofLp_smul, Pi.smul_apply, bas_apply, if_neg (Ne.symm hc'), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- On scalar payloads `matOp` is injective. -/
theorem matOp_injective {M N : Matrix (Cfg V) (Cfg V) ℂ}
    (h : matOp (Q := ℂ) M = matOp N) : M = N := by
  funext b c
  have := congrArg (fun F => F (bas c (1 : ℂ)) b) h
  simp only [matOp_bas_apply, smul_eq_mul, mul_one] at this
  exact this

/-! ### Operators on `ℓ²(ι)` with a given configuration matrix -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The operator on `ℓ²(ι)` whose configuration matrix along `φ` is `M`. -/
def ofMat (φ : Cfg V ≃ ι) (M : Matrix (Cfg V) (Cfg V) ℂ) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun i => ∑ j, M (φ.symm i) (φ.symm j) * v j)
      map_add' := by
        intro v w
        apply PiLp.ext
        intro i
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro z v
        apply PiLp.ext
        intro i
        simp [Finset.mul_sum, mul_left_comm] }

omit [Fintype V] [DecidableEq V] [DecidableEq ι] in
theorem ofMat_apply (φ : Cfg V ≃ ι) (M : Matrix (Cfg V) (Cfg V) ℂ)
    (v : EuclideanSpace ℂ ι) (i : ι) :
    ofMat φ M v i = ∑ j, M (φ.symm i) (φ.symm j) * v j := rfl

omit [Fintype V] [DecidableEq V] in
theorem ofMat_single_apply (φ : Cfg V ≃ ι) (M : Matrix (Cfg V) (Cfg V) ℂ) (c : Cfg V)
    (i : ι) : ofMat φ M (EuclideanSpace.single (φ c) 1) i = M (φ.symm i) c := by
  rw [ofMat_apply, Finset.sum_eq_single (φ c)]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [Fintype V] [DecidableEq V] in
/-- The configuration matrix of `ofMat φ M` is `M`. -/
theorem toMat_ofMat (φ : Cfg V ≃ ι) (M : Matrix (Cfg V) (Cfg V) ℂ) :
    toMat φ (ofMat φ M) = M := by
  funext c c'
  rw [toMat, ofMat_single_apply, Equiv.symm_apply_apply]

/-- The qubit lift of `ofMat φ M` is `matOp M`, for every payload. -/
theorem qlift_ofMat (φ : Cfg V ≃ ι) (M : Matrix (Cfg V) (Cfg V) ℂ) :
    qlift (R := R) φ (ofMat φ M) = matOp M := by
  rw [qlift_eq, toMat_ofMat]

omit [Fintype V] [DecidableEq V] in
/-- An operator on `ℓ²(ι)` is determined by its configuration matrix. -/
theorem toMat_injective (φ : Cfg V ≃ ι) {A B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (h : toMat φ A = toMat φ B) : A = B := by
  have hs : ∀ d : ι, A (EuclideanSpace.single d 1) = B (EuclideanSpace.single d 1) := by
    intro d
    apply PiLp.ext
    intro i
    have := congrFun (congrFun h (φ.symm i)) (φ.symm d)
    simpa [toMat] using this
  apply ContinuousLinearMap.ext
  intro v
  rw [euclid_eq_sum v, map_sum, map_sum]
  simp only [map_smul, hs]

/-- On scalar payloads the qubit lift is injective. -/
theorem qlift_injective (φ : Cfg V ≃ ι) {A B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (h : qlift (R := ℂ) φ A = qlift φ B) : A = B :=
  toMat_injective φ (matOp_injective (by rwa [qlift_eq, qlift_eq] at h))

/-- `ofMat φ M` is unitary when `matOp M` is unitary on scalar payloads. -/
theorem ofMat_isUnitary (φ : Cfg V ≃ ι) {M : Matrix (Cfg V) (Cfg V) ℂ}
    (h : IsUnitary (matOp (Q := ℂ) M)) : IsUnitary (ofMat φ M) := by
  have hq : qlift (R := ℂ) φ (ofMat φ M) = matOp M := qlift_ofMat φ M
  constructor
  · apply qlift_injective φ
    change qliftHom (R := ℂ) φ (star (ofMat φ M) * ofMat φ M) = qliftHom (R := ℂ) φ 1
    rw [map_mul, map_star, map_one]
    change star (qlift (R := ℂ) φ (ofMat φ M)) * qlift (R := ℂ) φ (ofMat φ M) = 1
    rw [hq]
    exact h.1
  · apply qlift_injective φ
    change qliftHom (R := ℂ) φ (ofMat φ M * star (ofMat φ M)) = qliftHom (R := ℂ) φ 1
    rw [map_mul, map_star, map_one]
    change qlift (R := ℂ) φ (ofMat φ M) * star (qlift (R := ℂ) φ (ofMat φ M)) = 1
    rw [hq]
    exact h.2

omit [DecidableEq V] in
/-- `ofMat φ M` maps the basis vector of `c` to the basis vector of `c'` when the column `c` of `M`
is the standard basis column of `c'`. -/
theorem ofMat_single (φ : Cfg V ≃ ι) (M : Matrix (Cfg V) (Cfg V) ℂ) (c c' : Cfg V)
    (h : ∀ b, M b c = if b = c' then 1 else 0) :
    ofMat φ M (EuclideanSpace.single (φ c) 1) = EuclideanSpace.single (φ c') 1 := by
  apply PiLp.ext
  intro i
  rw [ofMat_single_apply, h]
  by_cases hi : i = φ c'
  · subst hi
    simp
  · have : φ.symm i ≠ c' := fun h' => hi (by rw [← h', Equiv.apply_symm_apply])
    rw [if_neg this]
    simp [hi]

end Mat

end

end SparseHamiltonian.GeneralSparseAccess
