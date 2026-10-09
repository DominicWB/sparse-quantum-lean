import ODELowerBoundExtensions.Padding.Readout

/-!
# Known zero padding of an ODE family

Manuscript Section `part:odel`: "Known zero padding permits
any sufficiently large qubit register" (proof of Theorem `odel:thm:joint`, line 3904) and "Pad
dimensions to a common known size if desired" (proof of Theorem `odel:thm:combined`,
lines 4005-4006). The class and the output model are those of `SparseLowerBounds/ODE/Model`
(lines 3655-3695).

**The relation `ZeroPad F' F`.** A family `F'` on the index `N ⊕ P` is the known zero padding of
a family `F` on `N` when every sampled matrix is `F.data.matrix y ⊕ 0_P`
(`LowerBoundRemarks.HamiltonianPadding.padMat`), the stage durations agree, and the stage sources
and the initial state are extended by zero (`HsInstance.inlOp N P`). The relation says nothing
about the word tables or the locators: each padded hard family below is built explicitly (its
Boolean implementation is what carries the hardness, as in `HamiltonianPadding`), and `ZeroPad`
only records how its equation relates to the original one.

**What zero padding preserves** (the class facts, proved once here):

* `ZeroPad.start_eq`, `ZeroPad.T_eq`, `ZeroPad.mass_eq`: same breakpoints, `T` and `B`;
* `ZeroPad.solves`: a solution `x(t)` of `F` gives the solution `x(t) ⊕ 0` of `F'`
  (the generator `G ⊕ 0` maps `v ⊕ 0` to `G v ⊕ 0`, `gen_inlOp`);
* `ZeroPad.inClass`: `F'` is in the class with the same `η` and `ḡ` (same `D ⪰ 0`, same row and
  column norms on the original block and zero on the padding block, same `‖x(T)‖` and `B`);
* `ZeroPad.sparsityAttained`: maximum row and column sparsity exactly `s` survives, since it is
  attained on the original block (`SparsityAttained`);
* `ZeroPad.heraldedAccurate`: a solver of `F'`, read through `padReadout P G i₀ ∘ out`, is
  heralded-accurate for the normalised solution of `F`, with the same herald and `ε`.

The last item is the readout half of the hardness transfer. The query half is not generic: a
padded value call on a padding address, or a padded locator call on a padding row, cannot be
simulated by one call of the original access without controlled calls. The hardness of each padded
hard family is therefore re-derived from its Boolean implementation (`Padding/JointTheorem`,
`Padding/Precision`), exactly as `HamiltonianPadding` does for Theorem `hsl:thm:main`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Padding

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit SparseLowerBounds
  SparseLowerBounds.Hamiltonian SparseLowerBounds.Readout SparseLowerBounds.ODE
  LowerBoundRemarks.HamiltonianPadding
open scoped InnerProduct InnerProductSpace

/-- **Maximum row and column sparsity exactly `s`** (line 3899, "maximum sparsity exactly
`s`"): on every input and every stage, some row and some column of the sampled matrix have
exactly `s` nonzero entries. The bound `≤ s` holds for every family (`Family.row_sparsity_le`,
`Family.col_sparsity_le`). The ODE analogue of the fields `HardInstance.row_sparsity_attained`
and `HardInstance.col_sparsity_attained` of the Hamiltonian lower bound. -/
def SparsityAttained {X N Z : Type*} [Fintype N] [DecidableEq N] {K s : ℕ}
    (F : Family X N Z K s) : Prop :=
  ∀ x k, (∃ i, (Finset.univ.filter fun j => F.data.matrix (x, k) i j ≠ 0).card = s) ∧
    ∃ j, (Finset.univ.filter fun i => F.data.matrix (x, k) i j ≠ 0).card = s

/-- **`F'` is the known zero padding of `F` by `P`**: matrices `H ⊕ 0_P`, the same stage
durations, stage sources and initial state extended by zero. The word types `Z'`, `Z` may differ
(the relation concerns the equations, not their encodings). `ZeroPad` transfers the class facts
and the heralded readout, not hardness: there is no generic `ZeroPad F' F → F.Forces ε b →
F'.Forces ε b`, since simulating a padded value or locator call needs a controlled call of the
original access; each padded hard family is re-proved from its Boolean implementation instead. -/
structure ZeroPad {X N Z Z' : Type*} [Fintype N] [DecidableEq N] {P : Type*} [Fintype P]
    [DecidableEq P] {K s : ℕ} (F' : Family X (N ⊕ P) Z' K s) (F : Family X N Z K s) : Prop where
  matrix_eq : ∀ y, F'.data.matrix y = padMat P (F.data.matrix y)
  len_eq : ∀ k, F'.len k = F.len k
  src_eq : ∀ k, F'.src k = HsInstance.inlOp N P (F.src k)
  init_eq : F'.init = HsInstance.inlOp N P F.init

section Matrices

variable {N : Type*} [Fintype N] [DecidableEq N] {P : Type*} [Fintype P] [DecidableEq P]

omit [Fintype N] [DecidableEq N] [Fintype P] [DecidableEq P] in
/-- Scalars pass through the padding: `(c H) ⊕ 0 = c (H ⊕ 0)`. -/
theorem padMat_smul (c : ℂ) (H : Matrix N N ℂ) : padMat P (c • H) = c • padMat P H := by
  unfold padMat
  simp only [Matrix.fromBlocks_smul, smul_zero]

/-- **The padded generator on padded vectors**: `(G ⊕ 0)(v ⊕ 0) = (G v) ⊕ 0`. -/
theorem matrixOperator_padMat_inlOp (H : Matrix N N ℂ) (v : EuclideanSpace ℂ N) :
    SparseStateOverlap.matrixOperator (padMat P H) (HsInstance.inlOp N P v) =
      HsInstance.inlOp N P (SparseStateOverlap.matrixOperator H v) := by
  ext k
  cases k with
  | inl i => simp [SparseStateOverlap.matrixOperator_apply, Fintype.sum_sum_type, padMat]
  | inr p => simp [SparseStateOverlap.matrixOperator_apply, Fintype.sum_sum_type, padMat]

omit [DecidableEq N] [DecidableEq P] in
/-- Row sparsity of a padded original row equals that of the original row: the case `K = 0` of
`SparseLowerBounds.Hamiltonian.HsInstance.card_fromBlocks_row_inl`, since `padMat P H` is
`Matrix.fromBlocks H 0 0 0`. -/
theorem card_padMat_row (H : Matrix N N ℂ) (i : N) :
    (Finset.univ.filter fun j => padMat P H (Sum.inl i) j ≠ 0).card =
      (Finset.univ.filter fun j => H i j ≠ 0).card := by
  rw [padMat]
  exact HsInstance.card_fromBlocks_row_inl H 0 i

omit [DecidableEq N] [DecidableEq P] in
/-- Column sparsity of a padded original column equals that of the original column: the case
`K = 0` of `SparseLowerBounds.Hamiltonian.HsInstance.card_fromBlocks_col_inl`. -/
theorem card_padMat_col (H : Matrix N N ℂ) (j : N) :
    (Finset.univ.filter fun i => padMat P H i (Sum.inl j) ≠ 0).card =
      (Finset.univ.filter fun i => H i j ≠ 0).card := by
  rw [padMat]
  exact HsInstance.card_fromBlocks_col_inl H 0 j

/-- The padded generator in terms of the restriction `v ↦ (v_i)_{i ∈ N}` to the original block:
`(G ⊕ 0) v = (G (v|_N)) ⊕ 0`. -/
theorem matrixOperator_padMat_restrict (H : Matrix N N ℂ) (v : EuclideanSpace ℂ (N ⊕ P)) :
    SparseStateOverlap.matrixOperator (padMat P H) v =
      HsInstance.inlOp N P
        (SparseStateOverlap.matrixOperator H (WithLp.toLp 2 fun i => v (Sum.inl i))) := by
  ext k
  cases k with
  | inl i => simp [SparseStateOverlap.matrixOperator_apply, Fintype.sum_sum_type, padMat]
  | inr p => simp [SparseStateOverlap.matrixOperator_apply, Fintype.sum_sum_type, padMat]

/-- Pairing with a padded vector only sees the original block:
`⟪v, w ⊕ 0⟫ = ⟪v|_N, w⟫`. -/
theorem inner_inlOp_restrict (v : EuclideanSpace ℂ (N ⊕ P)) (w : EuclideanSpace ℂ N) :
    ⟪v, HsInstance.inlOp N P w⟫_ℂ = ⟪(WithLp.toLp 2 fun i => v (Sum.inl i) :
      EuclideanSpace ℂ N), w⟫_ℂ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_sum_type]
  simp

end Matrices

section Solutions

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

omit [CompleteSpace V] in
/-- **A solution survives a change of generator that agrees along it**: if `G' u (x u) =
G u (x u)` on `[a, c]`, a solution of `ẋ = -G x + b` solves `ẋ = -G' x + b`. -/
theorem solvesODE_congr_apply {G G' : ℝ → V →L[ℂ] V} {b x : ℝ → V} {a c : ℝ}
    (hG : ∀ u ∈ Set.Icc a c, G' u (x u) = G u (x u))
    (h : TimeDependentODE.SolvesODE G b x a c) : TimeDependentODE.SolvesODE G' b x a c := by
  intro u hu
  rw [hG u hu]
  exact h u hu

omit [CompleteSpace V] [CompleteSpace W] in
/-- **A solution survives an intertwining linear map**: if `L G = G' L` and `b' = L b` (constant
generator and source), then `L x(t)` solves `ẋ = -G' x + b'` whenever `x(t)` solves
`ẋ = -G x + b`. -/
theorem solvesODE_map (L : V →L[ℂ] W) {G : V →L[ℂ] V} {G' : W →L[ℂ] W} {b : V} {x : ℝ → V}
    {a c : ℝ} (hG : ∀ v, G' (L v) = L (G v))
    (h : TimeDependentODE.SolvesODE (fun _ => G) (fun _ => b) x a c) :
    TimeDependentODE.SolvesODE (fun _ => G') (fun _ => L b) (fun t => L (x t)) a c := by
  intro u hu
  have hu' : HasDerivWithinAt x (-(G (x u)) + b) (Set.Icc a c) u := h u hu
  have h1 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt u hu'
  have h2 : L (-(G (x u)) + b) = -(G' (L (x u))) + L b := by rw [map_add, map_neg, hG]
  show HasDerivWithinAt (fun t => L (x t)) (-(G' (L (x u))) + L b) (Set.Icc a c) u
  rw [← h2]
  exact h1

end Solutions

namespace ZeroPad

variable {X N Z Z' : Type*} [Fintype N] [DecidableEq N] {P : Type*} [Fintype P] [DecidableEq P]
  {K s : ℕ} {F' : Family X (N ⊕ P) Z' K s} {F : Family X N Z K s}

/-- Zero padding keeps the breakpoints. -/
theorem start_eq (hF : ZeroPad F' F) (k : ℕ) : F'.start k = F.start k := by
  unfold Family.start
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold Family.lenNat
  split_ifs with hi
  · exact hF.len_eq _
  · rfl

/-- Zero padding keeps the final time `T`. -/
theorem T_eq (hF : ZeroPad F' F) : F'.T = F.T := by
  unfold Family.T
  exact hF.start_eq K

/-- Zero padding keeps the source mass `B = ‖x₀‖ + ∫‖b‖`. -/
theorem mass_eq (hF : ZeroPad F' F) : F'.mass = F.mass := by
  simp only [Family.mass, hF.init_eq, hF.src_eq, hF.len_eq, norm_inlOp]

/-- The padded stage generator maps `v ⊕ 0` to `G_k(x) v ⊕ 0`. -/
theorem gen_inlOp (hF : ZeroPad F' F) (x : X) (k : Fin K) (v : EuclideanSpace ℂ N) :
    F'.gen x k (HsInstance.inlOp N P v) = HsInstance.inlOp N P (F.gen x k v) := by
  unfold Family.gen
  rw [hF.matrix_eq, matrixOperator_padMat_inlOp]

/-- **Solutions pad by zero**: if `x(t)` solves instance `x` of `F`, then `x(t) ⊕ 0` solves
instance `x` of `F'`. -/
theorem solves (hF : ZeroPad F' F) {x : X} {sol : ℝ → EuclideanSpace ℂ N} (h : F.Solves x sol) :
    F'.Solves x (fun t => HsInstance.inlOp N P (sol t)) := by
  refine ⟨?_, fun k => ?_⟩
  · show HsInstance.inlOp N P (sol 0) = F'.init
    rw [h.1, hF.init_eq]
  · have h1 := solvesODE_map (HsInstance.inlOp N P) (G := F.gen x k) (G' := F'.gen x k)
      (fun v => hF.gen_inlOp x k v) (h.2 k)
    rw [hF.start_eq, hF.start_eq, hF.src_eq]
    exact h1

/-- **Zero padding stays in the class** with the same `η` and `ḡ` (lines 3657-3669): accretive
generators `G ⊕ 0`, row and column norms of the original block and zero on the padding block,
and the padded solution `x(t) ⊕ 0` with the same `‖x(T)‖` and the same `B`. -/
theorem inClass (hF : ZeroPad F' F) {η gbar : ℝ} (h : F.InClass η gbar) :
    F'.InClass η gbar := by
  refine ⟨fun x k v => ?_, fun x k i => ?_, fun x k j => ?_, fun x => ?_⟩
  · have e1 : F'.gen x k v =
        HsInstance.inlOp N P (F.gen x k (WithLp.toLp 2 fun i => v (Sum.inl i))) := by
      unfold Family.gen
      rw [hF.matrix_eq]
      exact matrixOperator_padMat_restrict _ v
    rw [e1, inner_inlOp_restrict]
    exact h.accretive x k _
  · rw [hF.matrix_eq, padMat]
    exact HsInstance.sum_sq_fromBlocks_row_le (h.row_norm x k)
      (fun _ => by rw [Finset.sum_eq_zero (fun _ _ => by simp)]; exact sq_nonneg η) i
  · rw [hF.matrix_eq, padMat]
    exact HsInstance.sum_sq_fromBlocks_col_le (h.col_norm x k)
      (fun _ => by rw [Finset.sum_eq_zero (fun _ _ => by simp)]; exact sq_nonneg η) j
  · obtain ⟨sol, hs, hne, hm⟩ := h.solution x
    refine ⟨fun t => HsInstance.inlOp N P (sol t), hF.solves hs, ?_, ?_⟩
    · show HsInstance.inlOp N P (sol F'.T) ≠ 0
      rw [hF.T_eq]
      intro h0
      apply hne
      rw [← norm_eq_zero, ← norm_inlOp (P := P), h0, norm_zero]
    · show F'.mass ≤ gbar * ‖HsInstance.inlOp N P (sol F'.T)‖
      rw [hF.mass_eq, hF.T_eq, norm_inlOp]
      exact hm

/-- **Zero padding keeps maximum sparsity exactly `s`**, attained on the original block. -/
theorem sparsityAttained (hF : ZeroPad F' F) (h : SparsityAttained F) :
    SparsityAttained F' := by
  intro x k
  obtain ⟨⟨i, hi⟩, j, hj⟩ := h x k
  refine ⟨⟨Sum.inl i, ?_⟩, Sum.inl j, ?_⟩
  · rw [hF.matrix_eq, card_padMat_row, hi]
  · rw [hF.matrix_eq, card_padMat_col, hj]

/-- **Readout of a padded solver** (heralded readout transfer, lines 3675-3678): for every
solver of `F'`, every `i₀ : N` and every solution `x(t)` of instance `x` of `F`, the output read
through `padReadout P G i₀ ∘ out` and conditioned on the same herald is `ε`-accurate for
`x(T)/‖x(T)‖`. -/
theorem heraldedAccurate [Fintype Z'] [AddCommGroup Z'] (hF : ZeroPad F' F) {ι : Type*}
    [Fintype ι] {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {ε : ℝ} (A : Solver ι F' G ε) (i₀ : N) (x : X) {sol : ℝ → EuclideanSpace ℂ N}
    (h : F.Solves x sol) :
    HeraldedAccurate (padReadout P G i₀ ∘L A.out) A.herald (A.prog.eval x A.seed)
      (ODEStateNormalization.unitDirection (sol F.T)) ε := by
  have h' := A.accurate x _ (hF.solves h)
  beta_reduce at h'
  rw [hF.T_eq, unitDirection_inlOp] at h'
  exact heraldedAccurate_padReadout i₀ A.out A.herald _ _ ε h'

end ZeroPad

end

end ODELowerBoundExtensions.Padding
