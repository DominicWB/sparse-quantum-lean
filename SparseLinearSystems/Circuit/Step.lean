import SparseLinearSystems.Circuit.Cells

/-!
# Primitive-query implementation of counter-controlled walk steps

The physical workspace has one native register per cell `(counter, cell)`.
Its oracle family consists of the three original sparse primitives (with the
cell, control, dummy and reference registers as spectators) and the controlled
source preparation.  The clean encoding is `E = input ∘ Enc`.

For a public label `(σ, r, m)` the logical operation is the walk `W_{σ,r}`
on the counter values selected by `m` (`logOracle`).  `stepProg` implements it
with

* fixed public gates (the reflection and the two fixed factors, lifted from the
  clean subspace),
* one masked native Cayley circuit (54 sparse primitive calls),
* two masked controlled-source calls (one forward, one inverse),

exactly on the full clean subspace (`stepProg_intertwines`).

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/

namespace SparseLinearSystems.Step

noncomputable section
open SparseHamiltonian
open ContinuousLinearMap OracleCircuit HilbertBlocks HilbertRegularization HilbertAugmentation
  FourBranchCompression Augmented SparseBranch LogicalWalk Source CounterFilter Cells
open scoped InnerProduct
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- The physical cell index. -/
abbrev Idx (T : ℕ) := Fin (T + 1) × Cell

/-- The physical workspace. -/
abbrev Phys (n Z : Type*) [Fintype n] [Fintype Z] (T : ℕ) :=
  NativeMaskedOracle.Physical (Idx T) (Bas n Z)

/-- Physical oracle labels: the three sparse primitives and the controlled source. -/
abbrev Lbl := NativeSparseBlockEncoding.Query ⊕ Unit

/-- The physical oracle family. -/
def physOracle (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (T : ℕ) :
    Lbl → X → Phys n Z T →L[ℂ] Phys n Z T :=
  Sum.elim (NativeMaskedProgram.oracle (ι := Idx T) (NativeCayleyProgram.oracle D))
    (fun _ => sourceOracle (ι := Idx T) (Z := Z) Ub)

omit [DecidableEq Z] in
theorem physOracle_unitary (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (T : ℕ) : ∀ l x, IsUnitary (physOracle D Ub T l x) := by
  intro l x
  cases l with
  | inl l => exact NativeMaskedOracle.oracle_unitary _ (NativeCayleyProgram.oracle_unitary D l) x
  | inr _ => exact sourceOracle_unitary Ub hUb x

/-- The clean encoding `E = input ∘ Enc`. -/
def E (D : NativeSparseBlockEncoding.Data X n Z s) (T : ℕ) : Ctr T (PrivO n) →L[ℂ] Phys n Z T :=
  (NativeMaskedOracle.input (ι := Idx T) (NativeCayleyProgram.cleanBasis D)).toContinuousLinearMap ∘L
    (Enc D T).toContinuousLinearMap

theorem E_isometry (D : NativeSparseBlockEncoding.Data X n Z s) (T : ℕ) :
    ((E D T)†) ∘L E D T = 1 :=
  ((NativeMaskedOracle.input (ι := Idx T) (NativeCayleyProgram.cleanBasis D)).comp
    (Enc D T)).adjoint_comp_self

/-! ### Logical labels -/

/-- Logical labels: regularization angle, norm guess and counter mask. -/
abbrev LLbl (T : ℕ) := ℝ × ℝ × (Fin (T + 1) → Bool)

/-- The walk on the selected counter values. -/
def logOracle (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (T : ℕ) : LLbl T → X → Ctr T (PrivO n) →L[ℂ] Ctr T (PrivO n) :=
  fun l x => MaskedProgram.masked l.2.2 (WwO D Ub sv l.1 l.2.1 x)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem logOracle_unitary (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (T : ℕ) : ∀ l x, IsUnitary (logOracle D Ub sv T l x) :=
  fun l x => MaskedProgram.masked_unitary _ _ (WwO_unitary D Ub sv l.1 l.2.1 x)

/-! ### Unitarity of the fixed factors -/

theorem neg_one_unitary {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] : IsUnitary (-1 : K →L[ℂ] K) := by
  constructor <;> simp

theorem diagonal_unitary {P₀ P₁ P₂ P₃ : Type*}
    [NormedAddCommGroup P₀] [InnerProductSpace ℂ P₀] [CompleteSpace P₀]
    [NormedAddCommGroup P₁] [InnerProductSpace ℂ P₁] [CompleteSpace P₁]
    [NormedAddCommGroup P₂] [InnerProductSpace ℂ P₂] [CompleteSpace P₂]
    [NormedAddCommGroup P₃] [InnerProductSpace ℂ P₃] [CompleteSpace P₃]
    (K₀ : P₀ →L[ℂ] P₀) (K₁ : P₁ →L[ℂ] P₁) (K₂ : P₂ →L[ℂ] P₂) (K₃ : P₃ →L[ℂ] P₃)
    (h₀ : IsUnitary K₀) (h₁ : IsUnitary K₁) (h₂ : IsUnitary K₂) (h₃ : IsUnitary K₃) :
    IsUnitary (diagonal K₀ K₁ K₂ K₃) :=
  blockMap_isUnitary _ _ h₀ (blockMap_isUnitary _ _ h₁ (blockMap_isUnitary _ _ h₂ h₃))

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem reflection_unitary (D : NativeSparseBlockEncoding.Data X n Z s) :
    IsUnitary (WalkGap.reflection (Jw D).toContinuousLinearMap) := by
  have hs : star (WalkGap.reflection (Jw D).toContinuousLinearMap) =
      WalkGap.reflection (Jw D).toContinuousLinearMap := by
    rw [star_eq_adjoint, WalkGap.reflection_adjoint]
  have hm := WalkGap.reflection_mul_self _ (LinearIsometry.adjoint_comp_self (Jw D))
  exact ⟨by rw [hs, hm], by rw [hs, hm]⟩

theorem cayley_isUnitary {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [FiniteDimensional ℂ K] (T : K →L[ℂ] K) (h : (T†) = T) :
    IsUnitary (HilbertCayley.cayley T h) :=
  HilbertCayley.cayley_unitary T h

omit [DecidableEq n] in
theorem Fa_unitary (s σ : ℝ) : IsUnitary (Fa (n := n) s σ) :=
  diagonal_unitary _ _ _ _ (blockMap_isUnitary _ _ isUnitary_one neg_one_unitary)
    (cayley_isUnitary _ _) isUnitary_one neg_one_unitary

omit [DecidableEq n] in
theorem Fb_unitary (s r : ℝ) (sv : V0) : IsUnitary (Fb (n := n) s r sv) :=
  diagonal_unitary _ _ _ _ isUnitary_one isUnitary_one (cayley_isUnitary _ _) isUnitary_one

omit [DecidableEq n] in
theorem Vd_unitary (U : V0 →L[ℂ] V0) (hU : IsUnitary U) : IsUnitary (Vd (n := n) U) :=
  diagonal_unitary _ _ _ _ isUnitary_one isUnitary_one (slotOp_unitary U hU) isUnitary_one

/-! ### The step program -/

/-- Native programs are physical programs with the native label vocabulary. -/
def inlProg (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (T : ℕ) :
    MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := Idx T) (NativeCayleyProgram.oracle D)) →
      MultiOracleCircuit.Program (physOracle D Ub T)
  | .fixed U hU => .fixed U hU
  | .query l => .query (.inl l)
  | .queryAdjoint l => .queryAdjoint (.inl l)
  | .seq p q => .seq (inlProg D Ub T p) (inlProg D Ub T q)

omit [DecidableEq Z] in
theorem inlProg_eval (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (T : ℕ)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := Idx T) (NativeCayleyProgram.oracle D)))
    (x : X) : (inlProg D Ub T p).eval x = p.eval x := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
    simp only [inlProg, MultiOracleCircuit.Program.eval_seq, hp, hq]

omit [DecidableEq Z] in
theorem inlProg_cost (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (T : ℕ)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := Idx T) (NativeCayleyProgram.oracle D)))
    (w : Lbl → ℕ) : (inlProg D Ub T p).cost w = p.cost (fun l => w (.inl l)) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
    simp only [inlProg, MultiOracleCircuit.Program.cost_seq, hp, hq]

/-- Source programs are physical programs with the source label. -/
def inrProg (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (T : ℕ) :
    OracleCircuit.Program (sourceOracle (ι := Idx T) (Z := Z) Ub) →
      MultiOracleCircuit.Program (physOracle D Ub T)
  | .fixed U hU => .fixed U hU
  | .query => .query (.inr ())
  | .queryAdjoint => .queryAdjoint (.inr ())
  | .seq p q => .seq (inrProg D Ub T p) (inrProg D Ub T q)

omit [DecidableEq Z] in
theorem inrProg_eval (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (T : ℕ)
    (p : OracleCircuit.Program (sourceOracle (ι := Idx T) (Z := Z) Ub)) (x : X) :
    (inrProg D Ub T p).eval x = p.eval x := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => rfl
  | seq p q hp hq =>
    simp only [inrProg, MultiOracleCircuit.Program.eval_seq, OracleCircuit.Program.eval_seq, hp, hq]

omit [DecidableEq Z] in
theorem inrProg_cost (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (T : ℕ)
    (p : OracleCircuit.Program (sourceOracle (ι := Idx T) (Z := Z) Ub)) (w : Lbl → ℕ) :
    (inrProg D Ub T p).cost w = p.count * w (.inr ()) := by
  induction p with
  | fixed U hU => simp [inrProg]
  | query => simp [inrProg]
  | queryAdjoint => simp [inrProg]
  | seq p q hp hq =>
    simp only [inrProg, MultiOracleCircuit.Program.cost_seq, OracleCircuit.Program.count_seq, hp,
      hq, Nat.add_mul]

/-- The masked native Cayley circuit on the active sparse cells. -/
def nativeStep (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (T : ℕ)
    (σ : ℝ) (m : Fin (T + 1) → Bool) : MultiOracleCircuit.Program (physOracle D Ub T) :=
  inlProg D Ub T
    (NativeWholeProgramMask.program (ι := Idx T) (NativeCayleyProgram.oracle D)
      (NativeCayleyProgram.cleanBasis D) (activeSparse m) (NativeCayleyProgram.program D (w0 σ)))

/-- The masked controlled-source call on the active source cells. -/
def sourceStep (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (T : ℕ)
    (m : Fin (T + 1) → Bool) : MultiOracleCircuit.Program (physOracle D Ub T) :=
  inrProg D Ub T (sourceProgram (ι := Idx T) (Z := Z) Ub (activeSrc m))

/-- A lifted public gate. -/
def fixedStep (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (T : ℕ)
    (U : Ctr T (PrivO n) →L[ℂ] Ctr T (PrivO n)) (hU : IsUnitary U) :
    MultiOracleCircuit.Program (physOracle D Ub T) :=
  .fixed (SubspaceOracle.lift (E D T) U) (SubspaceOracle.lift_unitary _ (E_isometry D T) U hU)

/-- **The implementation of one logical label.** -/
def stepProg (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (T : ℕ) (l : LLbl T) : MultiOracleCircuit.Program (physOracle D Ub T) :=
  .seq (fixedStep D Ub T
      (MaskedProgram.masked l.2.2 (opO (WalkGap.reflection (Jw D).toContinuousLinearMap)))
      (MaskedProgram.masked_unitary _ _ (opO_unitary _ (reflection_unitary D))))
    (.seq (nativeStep D Ub T l.1 l.2.2)
      (.seq (fixedStep D Ub T (MaskedProgram.masked l.2.2 (opO (Fa (s : ℝ) l.1)))
          (MaskedProgram.masked_unitary _ _ (opO_unitary _ (Fa_unitary _ _))))
        (.seq (sourceStep D Ub T l.2.2)
          (.seq (fixedStep D Ub T (MaskedProgram.masked l.2.2 (opO (Fb (s : ℝ) l.2.1 sv)))
              (MaskedProgram.masked_unitary _ _ (opO_unitary _ (Fb_unitary _ _ _))))
            (sourceStep D Ub T l.2.2).adjoint))))

/-! ### Correctness -/

theorem intertwine_mul {P K : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] {Em : P →L[ℂ] K} {A B : K →L[ℂ] K}
    {F G : P →L[ℂ] P} (hA : A ∘L Em = Em ∘L F) (hB : B ∘L Em = Em ∘L G) :
    (A * B) ∘L Em = Em ∘L (F * G) := by
  rw [mul_def, mul_def, comp_assoc, hB, ← comp_assoc, hA, comp_assoc]

theorem fixedStep_intertwines (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (T : ℕ) (U : Ctr T (PrivO n) →L[ℂ] Ctr T (PrivO n)) (hU : IsUnitary U) (x : X) :
    (fixedStep D Ub T U hU).eval x ∘L E D T = E D T ∘L U :=
  EncodedOracle.lift_comp _ (E_isometry D T) U

theorem nativeStep_eval (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (T : ℕ) (σ : ℝ) (m : Fin (T + 1) → Bool) (x : X) :
    (nativeStep D Ub T σ m).eval x =
      (NativeWholeProgramMask.program (ι := Idx T) (NativeCayleyProgram.oracle D)
        (NativeCayleyProgram.cleanBasis D) (activeSparse m)
        (NativeCayleyProgram.program D (w0 σ))).eval x :=
  inlProg_eval D Ub T _ x

omit [DecidableEq Z] in
theorem sourceStep_eval (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (T : ℕ) (m : Fin (T + 1) → Bool) (x : X) :
    (sourceStep D Ub T m).eval x = (sourceProgram (ι := Idx T) (Z := Z) Ub (activeSrc m)).eval x :=
  inrProg_eval D Ub T _ x

theorem nativeStep_intertwines (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (T : ℕ) (σ : ℝ) (m : Fin (T + 1) → Bool) (x : X) :
    (nativeStep D Ub T σ m).eval x ∘L E D T =
      E D T ∘L MaskedProgram.masked m (opO (Asp D σ x)) := by
  have h1 := NativeWholeProgramMask.program_intertwines (ι := Idx T) (NativeCayleyProgram.oracle D)
    (NativeCayleyProgram.oracle_unitary D) (NativeCayleyProgram.cleanBasis D)
    (NativeCayleyProgram.image D) (NativeCayleyProgram.valid D) (activeSparse m)
    (NativeCayleyProgram.program D (w0 σ)) x
  have h2 := sparse_intertwines D T σ x m
  rw [nativeStep_eval, E, ← comp_assoc, h1, comp_assoc, h2, ← comp_assoc]

theorem sourceStep_intertwines (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (T : ℕ) (m : Fin (T + 1) → Bool) (x : X) :
    (sourceStep D Ub T m).eval x ∘L E D T =
      E D T ∘L MaskedProgram.masked m (opO (Vd (Ub x))) := by
  have h1 := sourceProgram_intertwines (ι := Idx T) (Z := Z) Ub (NativeCayleyProgram.cleanBasis D)
    (activeSrc m) x
  have h2 := source_intertwines D T (Ub x) m
  rw [sourceStep_eval, E, ← comp_assoc, h1, comp_assoc, h2, ← comp_assoc]

/-- **Exact implementation of every logical label on the clean subspace.** -/
theorem stepProg_intertwines (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (T : ℕ) (l : LLbl T) (x : X) :
    (stepProg D Ub sv T l).eval x ∘L E D T = E D T ∘L logOracle D Ub sv T l x := by
  obtain ⟨σ, r, m⟩ := l
  have hsrc := sourceStep_intertwines D Ub T m x
  have hsrcAdj : star ((sourceStep D Ub T m).eval x) ∘L E D T =
      E D T ∘L star (MaskedProgram.masked m (opO (Vd (Ub x)))) :=
    EncodedOracle.adjoint_intertwines _ _ _
      ((sourceStep D Ub T m).eval_unitary (physOracle_unitary D Ub hUb T) x)
      (MaskedProgram.masked_unitary _ _ (opO_unitary _ (Vd_unitary _ (hUb x)))) hsrc
  have hstar : star (MaskedProgram.masked m (opO (Vd (n := n) (Ub x)))) =
      MaskedProgram.masked m (opO (Vd ((Ub x)†))) := by
    rw [star_eq_adjoint, MaskedProgram.masked_adjoint, ← star_eq_adjoint, ← opO_star,
      star_eq_adjoint, Vd_adjoint]
  rw [hstar] at hsrcAdj
  have hW : logOracle D Ub sv T (σ, r, m) x =
      MaskedProgram.masked m (opO (WalkGap.reflection (Jw D).toContinuousLinearMap)) *
        (MaskedProgram.masked m (opO (Asp D σ x)) * (MaskedProgram.masked m (opO (Fa (s : ℝ) σ)) *
          (MaskedProgram.masked m (opO (Vd (Ub x))) * (MaskedProgram.masked m (opO (Fb (s : ℝ) r sv)) *
            MaskedProgram.masked m (opO (Vd ((Ub x)†))))))) := by
    simp only [logOracle, WwO_factor D Ub sv σ r x (hUb x), MaskedProgram.masked_mul]
  rw [hW]
  simp only [stepProg, MultiOracleCircuit.Program.eval_seq, MultiOracleCircuit.Program.eval_adjoint]
  apply intertwine_mul (fixedStep_intertwines D Ub T _ _ x)
  apply intertwine_mul (nativeStep_intertwines D Ub T σ m x)
  apply intertwine_mul (fixedStep_intertwines D Ub T _ _ x)
  apply intertwine_mul hsrc
  exact intertwine_mul (fixedStep_intertwines D Ub T _ _ x) hsrcAdj

/-! ### Query counts -/

/-- Matrix-primitive weight. -/
def wMat : Lbl → ℕ := Sum.elim (fun _ => 1) (fun _ => 0)

/-- Source-call weight (forward and inverse calls are both counted). -/
def wSrc : Lbl → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

theorem nativeStep_cost (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (T : ℕ) (σ : ℝ) (m : Fin (T + 1) → Bool) (w : Lbl → ℕ) :
    (nativeStep D Ub T σ m).cost w =
      3 * (6 * w (.inl .rowLocation) + 6 * w (.inl .columnLocation) + 6 * w (.inl .value)) := by
  rw [nativeStep, inlProg_cost, NativeWholeProgramMask.program_cost,
    NativeCayleyProgram.program_cost]

omit [DecidableEq Z] in
theorem sourceStep_cost (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (T : ℕ) (m : Fin (T + 1) → Bool) (w : Lbl → ℕ) :
    (sourceStep D Ub T m).cost w = w (.inr ()) := by
  rw [sourceStep, inrProg_cost, sourceProgram_count, one_mul]

theorem stepProg_cost (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (T : ℕ) (l : LLbl T) (w : Lbl → ℕ) :
    (stepProg D Ub sv T l).cost w =
      3 * (6 * w (.inl .rowLocation) + 6 * w (.inl .columnLocation) + 6 * w (.inl .value)) +
        2 * w (.inr ()) := by
  simp only [stepProg, MultiOracleCircuit.Program.cost_seq, MultiOracleCircuit.Program.cost_adjoint,
    fixedStep, MultiOracleCircuit.Program.cost_fixed, nativeStep_cost, sourceStep_cost]
  ring

theorem stepProg_cost_mat (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (T : ℕ) (l : LLbl T) : (stepProg D Ub sv T l).cost wMat = 54 := by
  rw [stepProg_cost]; rfl

theorem stepProg_cost_src (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (T : ℕ) (l : LLbl T) : (stepProg D Ub sv T l).cost wSrc = 2 := by
  rw [stepProg_cost]; rfl

end

end SparseLinearSystems.Step
