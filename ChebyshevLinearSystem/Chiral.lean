import SparseLinearSystems.Circuit.Opaque
import SparseLinearSystems.Augmented.Analysis

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

/-!
# The chiral symmetry of the augmented walk

Every branch of the four-branch generator `K_{σ,r}(x)` of the released walk
(`LogicalWalk.Kw`) is off-diagonal with respect to a fixed involution:

* the sparse branch: the edge generator exchanges the two edge orientations
  (`SparseEdgeMoments.entryGenerator`), and the locator conjugation acts separately on the
  two orientations (`FixedLocatorConjugation.block`), so the orientation parity
  `Z_or = 1 ⊕ (-1)` anticommutes with the native generator (`parOr_generator`);
* the public branches: `T₁` and `T₂(β)` exchange the upper sector with the sector
  `(lower, e)`, so `Z_pub = 1 ⊕ (-1)` anticommutes with them (`par_offDiag`, `parPub_T1`,
  `parPub_T2`);
* the padding branch is `0`: the released walk has no padding term (equation
  `qls:eq:composition` has `P_pad/(8√s)` there, and no involution anticommutes with a
  nonzero positive semidefinite term).

Hence `Z K Z = -K` for the fixed involution `Z = Z_0 ⊕ Z_pub ⊕ Z_pub ⊕ 1` (`parPriv`,
`parPriv_Kw`), which is independent of the unknown input, of `σ` and of `r`. Since the Cayley
transform of `-K` is the adjoint of the Cayley transform of `K` (`cayley_neg`), `Z C Z = C†`
for `C = Cayley(K)` (`cayley_chiral`), and the fixed unitary `Y = Z R` (`flipO`, with
`R = I - 2 J J†` the walk reflection) reverses the walk `W = R C` (`walk_reverse`):

`Y W Y = Z R R C Z R = Z C Z R = C† R = W†` (`flip_WwO`).

The reversal is stated in the opaque copy `PrivO` of the released circuit layer, where the
walk of `Step.logOracle` is `WwO = (I - 2 J J†) Cayley(K)` for the transported generator
(`WwO_walk`; `parO` is the transported parity). No promise on the input is needed.

This replaces the common-conjugator form `D = V† C V` of equation `qls:eq:commonconjugator`
in the proof of Lemma `qls:lem:signedwalk` (`SignedStep.lean`).
-/

namespace ChebyshevLinearSystem

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseLinearSystems HilbertBlocks
  FourBranchCompression Augmented SparseBranch LogicalWalk HilbertAugmentation
open scoped InnerProduct

/-! ### Cayley transforms of negated and anticommuting generators -/

section Cayley

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V]

/-- `Cayley(-K) = Cayley(K)†`. -/
theorem cayley_neg (K : V →L[ℂ] V) (h : (K†) = K) (h' : ((-K)†) = -K) :
    HilbertCayley.cayley (-K) h' = star (HilbertCayley.cayley K h) := by
  have e1 := HilbertCayley.inverse_mul_denominator (-K) h'
  have e2 := HilbertCayley.denominator_mul_inverse K h
  simp only [HilbertCayley.denominator] at e1 e2
  have e3 : HilbertCayley.denominatorInverse (-K) h' * (K + Complex.I • (1 : V →L[ℂ] V)) =
      -1 := by
    have e : K + Complex.I • (1 : V →L[ℂ] V) = -(-K - Complex.I • 1) := by abel
    rw [e, mul_neg, e1]
  have hL : HilbertCayley.cayley (-K) h' * HilbertCayley.cayley K h = 1 := by
    rw [HilbertCayley.cayley, HilbertCayley.cayley, Cayley.cayleyAction, Cayley.cayleyAction]
    calc (-K + Complex.I • (1 : V →L[ℂ] V)) * HilbertCayley.denominatorInverse (-K) h' *
          ((K + Complex.I • 1) * HilbertCayley.denominatorInverse K h)
        = (-K + Complex.I • (1 : V →L[ℂ] V)) *
            (HilbertCayley.denominatorInverse (-K) h' * (K + Complex.I • 1)) *
            HilbertCayley.denominatorInverse K h := by simp only [mul_assoc]
      _ = (K - Complex.I • (1 : V →L[ℂ] V)) * HilbertCayley.denominatorInverse K h := by
          rw [e3, mul_neg_one, neg_add, neg_neg, ← sub_eq_add_neg]
      _ = 1 := e2
  have hR := HilbertCayley.cayley_mul_star_self K h
  calc HilbertCayley.cayley (-K) h'
      = HilbertCayley.cayley (-K) h' *
          (HilbertCayley.cayley K h * star (HilbertCayley.cayley K h)) := by rw [hR, mul_one]
    _ = star (HilbertCayley.cayley K h) := by rw [← mul_assoc, hL, one_mul]

/-- A self-adjoint involution anticommuting with `K` conjugates `Cayley(K)` to its adjoint. -/
theorem cayley_chiral (K P : V →L[ℂ] V) (h : (K†) = K) (hP : (P†) = P) (hPP : P * P = 1)
    (hanti : P * K * P = -K) :
    P * HilbertCayley.cayley K h * P = star (HilbertCayley.cayley K h) := by
  have hU : (P†) * P = 1 ∧ P * (P†) = 1 := by rw [hP]; exact ⟨hPP, hPP⟩
  have hneg : ((-K)†) = -K := by rw [map_neg, h]
  have e : P * K * (P†) = -K := by rw [hP, hanti]
  have h'' : ((P * K * (P†))†) = P * K * (P†) := by rw [e]; exact hneg
  have hc := CayleyAlgebra.cayley_conj K h P hU h''
  rw [cayley_congr _ _ e h'' hneg, cayley_neg K h hneg, hP] at hc
  exact hc.symm

end Cayley

/-! ### The walk reversed by a fixed unitary -/

section Walk

variable {P V : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- If `Z C Z = C†`, then `Y = Z R` reverses the walk `W = R C`: `Y W Y = W†`. -/
theorem walk_reverse (J : P →L[ℂ] V) (hJ : (J†) ∘L J = 1) (C Q : V →L[ℂ] V)
    (hQC : Q * C * Q = star C) :
    (Q * WalkGap.reflection J) * WalkGap.walk J C * (Q * WalkGap.reflection J) =
      star (WalkGap.walk J C) := by
  have hRR := WalkGap.reflection_mul_self J hJ
  have hR : star (WalkGap.reflection J) = WalkGap.reflection J := by
    rw [star_eq_adjoint, WalkGap.reflection_adjoint]
  rw [WalkGap.walk, star_mul, hR]
  calc Q * WalkGap.reflection J * (WalkGap.reflection J * C) * (Q * WalkGap.reflection J)
      = Q * (WalkGap.reflection J * WalkGap.reflection J) * C * Q * WalkGap.reflection J := by
        simp only [mul_assoc]
    _ = star C * WalkGap.reflection J := by rw [hRR, mul_one, hQC]

end Walk

/-! ### The orientation parity of the sparse branch -/

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- The orientation parity `Z_or = 1 ⊕ (-1)` on the oriented edge space. -/
def parOr : SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n :=
  FixedLocatorConjugation.block 1 (-1)

omit [DecidableEq n] in
@[simp] theorem parOr_inl (v : SparseEdgeMoments.OrientedSpace n) (e : n × n) :
    parOr v (.inl e) = v (.inl e) := rfl

omit [DecidableEq n] in
@[simp] theorem parOr_inr (v : SparseEdgeMoments.OrientedSpace n) (e : n × n) :
    parOr v (.inr e) = -v (.inr e) := rfl

omit [DecidableEq n] in
theorem parOr_adjoint : ((parOr (n := n))†) = parOr := by
  rw [parOr, FixedLocatorConjugation.block_adjoint, WalkGap.adjoint_one', map_neg,
    WalkGap.adjoint_one']

omit [DecidableEq n] in
theorem parOr_mul_self : parOr (n := n) * parOr = 1 := by
  ext v e
  cases e <;> simp [mul_def]

omit [DecidableEq n] in
/-- The orientation parity commutes with every orientation-diagonal operator. -/
theorem parOr_block (A B : SparseEdgeMoments.EdgeSpace n →L[ℂ] SparseEdgeMoments.EdgeSpace n) :
    parOr * FixedLocatorConjugation.block A B = FixedLocatorConjugation.block A B * parOr := by
  ext v e
  cases e <;> simp [parOr, mul_def]

omit [DecidableEq n] in
/-- The edge generator exchanges the two orientations: `Z_or G Z_or = -G`. -/
theorem parOr_entryGenerator (H : Matrix n n ℂ) :
    parOr * SparseEdgeMoments.entryGenerator H * parOr = -SparseEdgeMoments.entryGenerator H := by
  ext v e
  cases e <;> simp [mul_def]

/-- `P (c • K) P = -(c • K)` from `P K P = -K`. -/
theorem smul_anti {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P K : E →L[ℂ] E) (c : ℂ) (h : P * K * P = -K) : P * (c • K) * P = -(c • K) := by
  rw [mul_smul_comm, smul_mul_assoc, h, smul_neg]

/-- **The native sparse generator anticommutes with the orientation parity**, for every
input: the locator conjugation is orientation diagonal. -/
theorem parOr_generator (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    parOr * FixedNativeCayleySimulation.generator D x * parOr =
      -FixedNativeCayleySimulation.generator D x := by
  set L := FixedLocatorConjugation.locator D x with hL
  have hstar : star L = FixedLocatorConjugation.block ((D.rowOracle x)†) ((D.columnOracle x)†) := by
    rw [star_eq_adjoint, hL, FixedLocatorConjugation.locator, FixedLocatorConjugation.block_adjoint]
  have h1 : parOr * star L = star L * parOr := by rw [hstar, parOr_block]
  have h2 : L * parOr = parOr * L := by
    rw [hL, FixedLocatorConjugation.locator, parOr_block]
  have h3 : parOr * SparseEdgeMoments.generator (D.matrix x) s * parOr =
      -SparseEdgeMoments.generator (D.matrix x) s :=
    smul_anti _ _ _ (parOr_entryGenerator (D.matrix x))
  change parOr * (star L * SparseEdgeMoments.generator (D.matrix x) s * L) * parOr =
    -(star L * SparseEdgeMoments.generator (D.matrix x) s * L)
  calc parOr * (star L * SparseEdgeMoments.generator (D.matrix x) s * L) * parOr
      = (parOr * star L) * SparseEdgeMoments.generator (D.matrix x) s * (L * parOr) := by
        simp only [mul_assoc]
    _ = star L * (parOr * SparseEdgeMoments.generator (D.matrix x) s * parOr) * L := by
        rw [h1, h2]
        simp only [mul_assoc]
    _ = -(star L * SparseEdgeMoments.generator (D.matrix x) s * L) := by
        rw [h3]
        simp only [mul_def, neg_comp, comp_neg]

/-! ### Block parities -/

/-- Negation of a block-diagonal operator. -/
theorem neg_blockMap_diag {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup Q] [NormedSpace ℂ Q] (A : P →L[ℂ] P) (B : Q →L[ℂ] Q) :
    -blockMap A 0 0 B = blockMap (-A) 0 0 (-B) := by
  ext x : 1
  apply prodExt <;> simp [blockMap_apply]

/-- The parity `1 ⊕ (-1)` anticommutes with every off-diagonal block operator. -/
theorem par_offDiag {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup Q] [NormedSpace ℂ Q] (B : Q →L[ℂ] P) (C : P →L[ℂ] Q) :
    blockMap 1 0 0 (-1) * blockMap 0 B C 0 * blockMap 1 0 0 (-1) = -blockMap 0 B C 0 := by
  ext x : 1
  apply prodExt <;> simp [mul_def, blockMap_apply]

/-- Negation of a register-diagonal operator. -/
theorem neg_wdiagonal {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (A : ι → E →L[ℂ] E) :
    -WeightedClock.diagonal A = WeightedClock.diagonal (fun i => -A i) := by
  ext x i
  simp

/-- A block parity `A ⊕ 1` anticommutes with `G ⊕ 0` when `A` anticommutes with `G`. -/
theorem blockMap_anti {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup Q] [NormedSpace ℂ Q] (A G : P →L[ℂ] P) (h : A * G * A = -G) :
    blockMap A 0 0 (1 : Q →L[ℂ] Q) * blockMap G 0 0 0 * blockMap A 0 0 1 =
      -blockMap G 0 0 0 := by
  rw [neg_blockMap_diag, neg_zero, ← h]
  ext x : 1
  apply prodExt <;> simp [mul_def, blockMap_apply]

/-- A register-constant parity anticommutes with a register-constant operator. -/
theorem wdiag_anti {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (P K : E →L[ℂ] E) (h : P * K * P = -K) :
    WeightedClock.diagonal (fun _ : ι => P) * WeightedClock.diagonal (fun _ : ι => K) *
      WeightedClock.diagonal (fun _ : ι => P) = -WeightedClock.diagonal (fun _ : ι => K) := by
  rw [neg_wdiagonal, ← h]
  ext x i
  simp [mul_def]

/-- Branchwise anticommutation of four-branch operators (padding branch `0`). -/
theorem four_anti {P₀ P₁ P₂ P₃ : Type*} [NormedAddCommGroup P₀] [InnerProductSpace ℂ P₀]
    [NormedAddCommGroup P₁] [InnerProductSpace ℂ P₁] [NormedAddCommGroup P₂]
    [InnerProductSpace ℂ P₂] [NormedAddCommGroup P₃] [InnerProductSpace ℂ P₃]
    (Z₀ K₀ : P₀ →L[ℂ] P₀) (Z₁ K₁ : P₁ →L[ℂ] P₁) (Z₂ K₂ : P₂ →L[ℂ] P₂)
    (h₀ : Z₀ * K₀ * Z₀ = -K₀) (h₁ : Z₁ * K₁ * Z₁ = -K₁) (h₂ : Z₂ * K₂ * Z₂ = -K₂) :
    diagonal Z₀ Z₁ Z₂ (1 : P₃ →L[ℂ] P₃) * diagonal K₀ K₁ K₂ 0 * diagonal Z₀ Z₁ Z₂ 1 =
      -diagonal K₀ K₁ K₂ 0 := by
  rw [diagonal_mul, diagonal_mul, h₀, h₁, h₂, mul_zero, zero_mul]
  simp only [diagonal, neg_blockMap_diag, neg_zero]

/-- The parity `Z_0 = (1 ⊗ Z_or) ⊕ 1` of the sparse branch. -/
def parP0 : P0 n →L[ℂ] P0 n :=
  blockMap (WeightedClock.diagonal (fun _ : Bool × Bool => parOr)) 0 0 1

/-- The parity `Z_pub = 1 ⊕ (-1)` of a public branch: `+1` on the upper sector, `-1` on the
sector `(lower, e)`. -/
def parPub : Pub V0 →L[ℂ] Pub V0 := blockMap 1 0 0 (-1)

/-- The four-branch parity `Z = Z_0 ⊕ Z_pub ⊕ Z_pub ⊕ 1`. -/
def parPriv : Priv n →L[ℂ] Priv n := diagonal parP0 parPub parPub 1

/-- **The sparse branch anticommutes with its parity**, for every input. -/
theorem parP0_K0 (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    parP0 * K0 D x * parP0 = -K0 D x :=
  blockMap_anti _ _ (wdiag_anti _ _ (parOr_generator D x))

omit [DecidableEq n] in
/-- `T₁` exchanges the upper sector with `(lower, e)`. -/
theorem parPub_T1 : parPub * (T1 : Pub V0 →L[ℂ] Pub V0) * parPub = -T1 :=
  par_offDiag _ _

omit [DecidableEq n] in
/-- `T₂(β)` exchanges the upper sector with `(lower, e)`. -/
theorem parPub_T2 (β : Sys V0) : parPub * T2 β * parPub = -T2 β :=
  par_offDiag _ _

/-- **The chiral symmetry of the four-branch generator**: `Z K_{σ,r}(x) Z = -K_{σ,r}(x)` for
every input, every `σ` and every `r`. -/
theorem parPriv_Kw (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (σ r : ℝ) (x : X) :
    parPriv * Kw D Ub sv σ r x * parPriv = -Kw D Ub sv σ r x :=
  four_anti _ _ _ _ _ _ (smul_anti _ _ _ (parP0_K0 D x)) (smul_anti _ _ _ parPub_T1)
    (smul_anti _ _ _ (parPub_T2 _))

omit [DecidableEq n] in
theorem parOr_diag_adjoint :
    ((WeightedClock.diagonal (fun _ : Bool × Bool => (parOr (n := n))))†) =
      WeightedClock.diagonal (fun _ : Bool × Bool => parOr) := by
  rw [WeightedClock.diagonal_adjoint]
  simp only [parOr_adjoint]

omit [DecidableEq n] in
theorem parP0_adjoint : ((parP0 (n := n))†) = parP0 := by
  rw [parP0, block_adjoint, parOr_diag_adjoint, WalkGap.adjoint_one']
  simp only [map_zero]

omit [DecidableEq n] in
theorem parPub_adjoint : ((parPub (n := n))†) = parPub := by
  rw [parPub, block_adjoint, WalkGap.adjoint_one', map_neg, WalkGap.adjoint_one']
  simp only [map_zero]

omit [DecidableEq n] in
theorem parPriv_adjoint : ((parPriv (n := n))†) = parPriv := by
  rw [parPriv, diagonal_adjoint, parP0_adjoint, parPub_adjoint, WalkGap.adjoint_one']

omit [DecidableEq n] in
theorem parP0_mul_self : parP0 (n := n) * parP0 = 1 := by
  rw [parP0, CayleyAlgebra.blockMap_mul_diag, diagonal_mul', parOr_mul_self, mul_one,
    WeightedClock.diagonal_one, CayleyAlgebra.blockMap_one']

omit [DecidableEq n] in
theorem parPub_mul_self : parPub (n := n) * parPub = 1 := by
  rw [parPub, CayleyAlgebra.blockMap_mul_diag, mul_one, mul_neg_one, neg_neg,
    CayleyAlgebra.blockMap_one']

omit [DecidableEq n] in
theorem parPriv_mul_self : parPriv (n := n) * parPriv = 1 := by
  rw [parPriv, diagonal_mul, parP0_mul_self, parPub_mul_self, mul_one]
  simp only [diagonal, CayleyAlgebra.blockMap_one']

/-! ### The parity and the walk in the opaque copy -/

/-- The four-branch parity in the opaque copy. -/
def parO : PrivO n →L[ℂ] PrivO n := opO parPriv

omit [DecidableEq n] in
theorem parO_adjoint : ((parO (n := n))†) = parO := by
  rw [parO, ← opO_adjoint, parPriv_adjoint]

omit [DecidableEq n] in
theorem parO_mul_self : parO (n := n) * parO = 1 := by
  rw [parO, ← opO_mul, parPriv_mul_self, opO_one]

theorem parO_Kw (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (σ r : ℝ) (x : X) :
    parO * opO (Kw D Ub sv σ r x) * parO = -opO (Kw D Ub sv σ r x) := by
  rw [parO, ← opO_mul, ← opO_mul, parPriv_Kw, opO, opO, map_neg]

theorem KwO_selfAdjoint (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (σ r : ℝ) (x : X) :
    ((opO (Kw D Ub sv σ r x))†) = opO (Kw D Ub sv σ r x) := by
  rw [← opO_adjoint, Kw_selfAdjoint]

variable [Fintype Z] [AddCommGroup Z] [DecidableEq Z]

/-- The opaque walk is the walk of the transported generator. No promise is needed. -/
theorem WwO_walk (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (σ r : ℝ) (x : X) :
    WwO D Ub sv σ r x = WalkGap.walk (JwO D).toContinuousLinearMap
      (HilbertCayley.cayley (opO (Kw D Ub sv σ r x)) (KwO_selfAdjoint D Ub sv σ r x)) :=
  conj_walk toO (Jw D).toContinuousLinearMap (JwO D).toContinuousLinearMap (fun _ => rfl)
    (Kw D Ub sv σ r x) (Kw_selfAdjoint D Ub sv σ r x) (KwO_selfAdjoint D Ub sv σ r x)

/-- **The fixed reversal gate** `Y = Z R` in the opaque copy: the four-branch parity after the
walk reflection `R = I - 2 J J†`. It depends only on the public data of `D`. -/
def flipO (D : NativeSparseBlockEncoding.Data X n Z s) : PrivO n →L[ℂ] PrivO n :=
  parO * WalkGap.reflection (JwO D).toContinuousLinearMap

/-- **The walk reversed by a fixed gate**: `Y W_{σ,r}(x) Y = W_{σ,r}(x)†` for every input,
every `σ` and every `r`. -/
theorem flip_WwO (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (σ r : ℝ) (x : X) :
    flipO D * WwO D Ub sv σ r x * flipO D = (WwO D Ub sv σ r x)† := by
  rw [WwO_walk, flipO, walk_reverse _ (LinearIsometry.adjoint_comp_self _) _ _
    (cayley_chiral _ _ _ parO_adjoint parO_mul_self (parO_Kw D Ub sv σ r x)), star_eq_adjoint]

end

end ChebyshevLinearSystem
