import ManuscriptConformance.WriterProtocolEndpoints
import ManuscriptConformance.ODETime

/-!
# Theorem `ode:thm:time` with a time-indexed writer value oracle (handover item B4)

`ode_thm_time_writer` restates Theorem `ode:thm:time` for value access by a reversible writer
specified only on a clean target (`WriterAccess`), for time-indexed sparse data: the supplied
access takes the time address of the sample as an input register, so the primitive calls are the
time-indexed locators and the time-indexed writer `W_t |r, a, 0⟩ = c_{r,a} |r, a, w_{r,a}⟩`
(`timeWriterOracles`), with any phases. The released protocol of `ode_thm_time` is run with every
circuit compiled (every coherent sampled-time value call replaced by writer, adder and inverse
writer on one more clean scratch register; every locator and source call by the same call with the
scratch register a spectator) and every seed and output isometry encoded. Every Born probability,
the success mass and the conditional output are those of the released protocol; the worst-case
matrix calls (locator and writer calls) are at most twice those of the released protocol, the
source calls the same.

The coherent sampled-time oracle reads a different instance in each branch of its label register
(`TimeDependentODE.labelOracle`). The layer for it:

* `ampHom`: a unital star-algebra homomorphism `Φ` of the bounded operators, applied blockwise on a
  finite Hilbert sum (`blk`, `ext_blk`, `blk_comp`, `blk_adjoint`, `ampHom_diagonal`);
* `labelProg`, `Impl.flabel`, `FImplH.label`: a converted implementation of a family of calls gives
  one of the label-dependent family, every branch running the converted circuit of its own instance,
  with the primitive calls read in every branch at the instance of the branch;
* `labelOracle_sample_eq`, `homOf_time`: the branch-dependent primitive calls of the sampled-time
  query are the time-indexed primitive calls under one fixed unital star-algebra homomorphism.
-/

namespace SparseHamiltonian.WriterAccess

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct InnerProductSpace
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

/-! ### Operators on a finite Hilbert sum by their blocks -/

section Blocks

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The inclusion of the branch `b`. -/
def injB (b : κ) : V →L[ℂ] PiLp 2 (fun _ : κ => V) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => V)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : κ => V) b

omit [Fintype κ] [CompleteSpace V] in
@[simp] theorem injB_apply (b : κ) (v : V) (c : κ) :
    injB (κ := κ) b v c = if c = b then v else 0 := by
  simp [injB]

/-- The block `(b, b')` of an operator on the finite Hilbert sum. -/
def blk (A : PiLp 2 (fun _ : κ => V) →L[ℂ] PiLp 2 (fun _ : κ => V)) (b b' : κ) : V →L[ℂ] V :=
  PiLp.proj 2 (fun _ : κ => V) b ∘L A ∘L injB b'

omit [Fintype κ] [CompleteSpace V] in
theorem blk_apply (A : PiLp 2 (fun _ : κ => V) →L[ℂ] PiLp 2 (fun _ : κ => V)) (b b' : κ)
    (v : V) : blk A b b' v = A (injB b' v) b := rfl

omit [CompleteSpace V] in
theorem eq_sum_injB (v : PiLp 2 (fun _ : κ => V)) : v = ∑ b', injB b' (v b') := by
  apply PiLp.ext
  intro c
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp [injB_apply]

omit [CompleteSpace V] in
/-- An operator acts through its blocks. -/
theorem apply_eq_sum_blk (A : PiLp 2 (fun _ : κ => V) →L[ℂ] PiLp 2 (fun _ : κ => V))
    (v : PiLp 2 (fun _ : κ => V)) (b : κ) : A v b = ∑ b', blk A b b' (v b') := by
  conv_lhs => rw [eq_sum_injB v]
  rw [map_sum, WithLp.ofLp_sum, Finset.sum_apply]
  rfl

omit [CompleteSpace V] in
/-- Operators with the same blocks are equal. -/
theorem ext_blk {A B : PiLp 2 (fun _ : κ => V) →L[ℂ] PiLp 2 (fun _ : κ => V)}
    (h : ∀ b b', blk A b b' = blk B b b') : A = B := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro b
  rw [apply_eq_sum_blk A, apply_eq_sum_blk B]
  simp only [h]

omit [CompleteSpace V] in
theorem blk_comp (A B : PiLp 2 (fun _ : κ => V) →L[ℂ] PiLp 2 (fun _ : κ => V)) (b b' : κ) :
    blk (A ∘L B) b b' = ∑ c, blk A b c ∘L blk B c b' := by
  apply ContinuousLinearMap.ext
  intro v
  rw [_root_.sum_apply]
  change A (B (injB b' v)) b = _
  rw [apply_eq_sum_blk A]
  rfl

omit [Fintype κ] [CompleteSpace V] in
theorem blk_one (b b' : κ) :
    blk (1 : PiLp 2 (fun _ : κ => V) →L[ℂ] PiLp 2 (fun _ : κ => V)) b b' =
      if b = b' then 1 else 0 := by
  apply ContinuousLinearMap.ext
  intro v
  rw [blk_apply, one_apply_eq_self, injB_apply]
  split_ifs <;> simp

omit [Fintype κ] [CompleteSpace V] in
theorem blk_zero (b b' : κ) :
    blk (0 : PiLp 2 (fun _ : κ => V) →L[ℂ] PiLp 2 (fun _ : κ => V)) b b' = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

omit [CompleteSpace V] in
theorem blk_add (A B : PiLp 2 (fun _ : κ => V) →L[ℂ] PiLp 2 (fun _ : κ => V)) (b b' : κ) :
    blk (A + B) b b' = blk A b b' + blk B b b' := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

omit [CompleteSpace V] in
theorem blk_smul (r : ℂ) (A : PiLp 2 (fun _ : κ => V) →L[ℂ] PiLp 2 (fun _ : κ => V)) (b b' : κ) :
    blk (r • A) b b' = r • blk A b b' := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

omit [CompleteSpace V] in
theorem blk_sum_inj (F : κ → κ → V →L[ℂ] V) (b b' : κ) :
    blk (∑ c, ∑ c', injB c ∘L F c c' ∘L PiLp.proj 2 (fun _ : κ => V) c') b b' = F b b' := by
  apply ContinuousLinearMap.ext
  intro v
  rw [blk_apply, _root_.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  simp only [_root_.sum_apply, WithLp.ofLp_sum, Finset.sum_apply, comp_apply, injB_apply,
    PiLp.proj_apply]
  simp
  rw [Finset.sum_eq_single b']
  · simp
  · intro c _ hc
    simp [hc]
  · simp

theorem blk_adjoint (A : PiLp 2 (fun _ : κ => V) →L[ℂ] PiLp 2 (fun _ : κ => V)) (b b' : κ) :
    blk (A†) b b' = (blk A b' b)† := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro v w
  rw [blk_apply, blk_apply]
  have h1 : ⟪(A†) (injB b' v) b, w⟫_ℂ = ⟪(A†) (injB b' v), injB b w⟫_ℂ := by
    rw [PiLp.inner_apply, Finset.sum_eq_single b]
    · simp [injB_apply]
    · intro c _ hc
      simp [injB_apply, hc]
    · simp
  have h2 : ⟪v, A (injB b w) b'⟫_ℂ = ⟪injB b' v, A (injB b w)⟫_ℂ := by
    rw [PiLp.inner_apply, Finset.sum_eq_single b']
    · simp [injB_apply]
    · intro c _ hc
      simp [injB_apply, hc]
    · simp
  rw [h1, h2, ContinuousLinearMap.adjoint_inner_left]

omit [Fintype κ] [CompleteSpace V] in
theorem blk_diagonal (F : κ → V →L[ℂ] V) (b b' : κ) :
    blk (WeightedClock.diagonal (V := fun _ : κ => V) F) b b' = if b = b' then F b else 0 := by
  apply ContinuousLinearMap.ext
  intro v
  rw [blk_apply, WeightedClock.diagonal_apply, injB_apply]
  split_ifs with h
  · subst h; rfl
  · simp

end Blocks

/-! ### A star-algebra homomorphism applied blockwise -/

section Amp

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The blockwise image of an operator on the finite Hilbert sum. -/
def ampFun (Φ : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K))
    (A : PiLp 2 (fun _ : κ => H) →L[ℂ] PiLp 2 (fun _ : κ => H)) :
    PiLp 2 (fun _ : κ => K) →L[ℂ] PiLp 2 (fun _ : κ => K) :=
  ∑ c, ∑ c', injB c ∘L Φ (blk A c c') ∘L PiLp.proj 2 (fun _ : κ => K) c'

theorem blk_ampFun (Φ : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K))
    (A : PiLp 2 (fun _ : κ => H) →L[ℂ] PiLp 2 (fun _ : κ => H)) (b b' : κ) :
    blk (ampFun Φ A) b b' = Φ (blk A b b') :=
  blk_sum_inj _ b b'

/-- **A unital star-algebra homomorphism applied blockwise** on a finite Hilbert sum. -/
def ampHom (κ : Type*) [Fintype κ] [DecidableEq κ] (Φ : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    (PiLp 2 (fun _ : κ => H) →L[ℂ] PiLp 2 (fun _ : κ => H)) →⋆ₐ[ℂ]
      (PiLp 2 (fun _ : κ => K) →L[ℂ] PiLp 2 (fun _ : κ => K)) where
  toFun := ampFun Φ
  map_one' := ext_blk fun b b' => by
    rw [blk_ampFun, blk_one, blk_one]
    split_ifs <;> simp
  map_mul' A B := ext_blk fun b b' => by
    rw [mul_def, mul_def, blk_ampFun, blk_comp, blk_comp, map_sum]
    simp only [blk_ampFun, ← mul_def, map_mul]
  map_zero' := ext_blk fun b b' => by rw [blk_ampFun, blk_zero, blk_zero, map_zero]
  map_add' A B := ext_blk fun b b' => by
    rw [blk_ampFun, blk_add, blk_add, map_add, blk_ampFun, blk_ampFun]
  commutes' r := ext_blk fun b b' => by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, blk_ampFun, blk_smul,
      blk_smul, blk_one, blk_one, map_smul]
    split_ifs <;> simp
  map_star' A := ext_blk fun b b' => by
    rw [star_eq_adjoint, star_eq_adjoint, blk_ampFun, blk_adjoint, blk_adjoint, blk_ampFun,
      ← star_eq_adjoint, ← star_eq_adjoint, map_star]

theorem ampHom_apply (Φ : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K))
    (A : PiLp 2 (fun _ : κ => H) →L[ℂ] PiLp 2 (fun _ : κ => H)) :
    ampHom κ Φ A = ampFun Φ A := rfl

/-- The blockwise homomorphism on a diagonal operator. -/
theorem ampHom_diagonal (Φ : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)) (F : κ → H →L[ℂ] H) :
    ampHom κ Φ (WeightedClock.diagonal (V := fun _ : κ => H) F) =
      WeightedClock.diagonal (V := fun _ : κ => K) (fun b => Φ (F b)) := by
  refine ext_blk fun b b' => ?_
  rw [ampHom_apply, blk_ampFun, blk_diagonal, blk_diagonal]
  split_ifs <;> simp

end Amp

/-! ### Label-dependent instances -/

section Label

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {Z : Type*} [Fintype Z] [DecidableEq Z] [AddCommGroup Z]
  {X Y L Q : Type*} {κ : Type*} [Fintype κ]

/-- The same program in every branch of the label register, the branch `b` reading the instance
`σ x b`. -/
def labelProg {K' : Type*} [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
    (σ : X → κ → Y) {Ow : Q → Y → K' →L[ℂ] K'} :
    MultiOracleCircuit.Program Ow →
      MultiOracleCircuit.Program (TimeDependentODE.labelOracle Ow σ)
  | .fixed U hU => .fixed _
      (CoherentQuerySchedule.diagonal_unitary (fun _ : κ => U) (fun _ => hU))
  | .query l => .query l
  | .queryAdjoint l => .queryAdjoint l
  | .seq p q => .seq (labelProg σ p) (labelProg σ q)

@[simp] theorem labelProg_cost {K' : Type*} [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
    [CompleteSpace K'] (σ : X → κ → Y) {Ow : Q → Y → K' →L[ℂ] K'}
    (p : MultiOracleCircuit.Program Ow) (w : Q → ℕ) :
    (labelProg σ p).cost w = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [labelProg, MultiOracleCircuit.Program.cost_seq, hp, hq]

theorem labelProg_eval {K' : Type*} [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
    [CompleteSpace K'] (σ : X → κ → Y) {Ow : Q → Y → K' →L[ℂ] K'}
    (p : MultiOracleCircuit.Program Ow) (x : X) :
    (labelProg σ p).eval x = WeightedClock.diagonal (fun b : κ => p.eval (σ x b)) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => exact WeightedClock.diagonal_adjoint _
  | seq p q hp hq =>
    simp only [labelProg, MultiOracleCircuit.Program.eval_seq, hp, hq]
    exact WeightedClock.diagonal_comp _ _

/-- **A converted implementation, read at label-dependent instances**: every branch of the label
register runs the converted circuit of its own instance; the scratch register stays outermost. -/
theorem Impl.flabel {O : L → Y → K →L[ℂ] K}
    {Ow : Q → Y → PiLp 2 (fun _ : Z => K) →L[ℂ] PiLp 2 (fun _ : Z => K)}
    {circ : L → MultiOracleCircuit.Program Ow} {c : L → (Q → ℕ) → ℕ}
    (h : Impl O Ow (single0 Z K) circ c) (σ : X → κ → Y) :
    Impl (TimeDependentODE.labelOracle O σ)
      (fun q x => (swapPi (K := K) κ Z).conjStarAlgEquiv (TimeDependentODE.labelOracle Ow σ q x))
      (single0 Z (PiLp 2 (fun _ : κ => K)))
      (fun l => (labelProg σ (circ l)).transport (swapPi (K := K) κ Z)) c where
  iso := single0_isometry
  unitary l x := TimeDependentODE.labelOracle_unitary O h.unitary σ l x
  unitaryW q x := (TimeDependentODE.labelOracle_unitary Ow h.unitaryW σ q x).transport _
  intertwines l x := by
    apply ContinuousLinearMap.ext
    intro v
    rw [MultiOracleCircuit.Program.eval_transport, labelProg_eval]
    have h1 : (swapPi (K := K) κ Z).symm (single0 Z (PiLp 2 (fun _ : κ => K)) v) =
        WithLp.toLp 2 (fun i => single0 Z K (v i)) := by
      apply PiLp.ext
      intro i
      apply PiLp.ext
      intro t
      rw [swapPi_symm_apply, single0_apply]
      change _ = single0 Z K (v i) t
      rw [single0_apply]
      split_ifs <;> rfl
    have hv : ∀ i, (circ l).eval (σ x i) (single0 Z K (v i)) =
        single0 Z K (O l (σ x i) (v i)) := fun i => by
      have := congrArg (fun T => T (v i)) (h.intertwines l (σ x i))
      simpa only [comp_apply] using this
    simp only [comp_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, h1]
    apply PiLp.ext
    intro t
    apply PiLp.ext
    intro i
    rw [swapPi_apply, WeightedClock.diagonal_apply]
    change (circ l).eval (σ x i) (single0 Z K (v i)) t = _
    rw [hv, single0_apply, single0_apply]
    split_ifs <;> rfl
  cost l w := by rw [MultiOracleCircuit.Program.cost_transport, labelProg_cost, h.cost]

/-- **The label layer for a converted implementation**: the primitive calls are read in every
branch at the instance of the branch, under the blockwise homomorphism. -/
theorem FImplH.label [DecidableEq κ] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {Ow₀ : Q → Y → H →L[ℂ] H} {O : L → Y → K →L[ℂ] K} {c : L → (Q → ℕ) → ℕ}
    (h : FImplH Z O Ow₀ c) (σ : X → κ → Y) :
    FImplH Z (TimeDependentODE.labelOracle O σ) (TimeDependentODE.labelOracle Ow₀ σ) c := by
  obtain ⟨Ow, circ, hI, Φ, hΦ⟩ := h
  refine ⟨_, _, hI.flabel σ, ((swapPi (K := K) κ Z).conjStarAlgEquiv :
    (PiLp 2 (fun _ : κ => PiLp 2 (fun _ : Z => K)) →L[ℂ]
      PiLp 2 (fun _ : κ => PiLp 2 (fun _ : Z => K))) →⋆ₐ[ℂ]
      (PiLp 2 (fun _ : Z => PiLp 2 (fun _ : κ => K)) →L[ℂ]
        PiLp 2 (fun _ : Z => PiLp 2 (fun _ : κ => K)))).comp (ampHom κ Φ),
    fun q x => ?_⟩
  show (swapPi (K := K) κ Z).conjStarAlgEquiv (TimeDependentODE.labelOracle Ow σ q x) =
    (swapPi (K := K) κ Z).conjStarAlgEquiv (ampHom κ Φ (TimeDependentODE.labelOracle Ow₀ σ q x))
  congr 1
  unfold TimeDependentODE.labelOracle
  rw [ampHom_diagonal]
  simp only [hΦ]

/-- A converted implementation over primitive calls that are themselves the images of further
primitive calls under a fixed unital star-algebra homomorphism. -/
theorem FImplH.homOf {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    {Ow₀ : Q → X → H →L[ℂ] H} {Ow₁ : Q → X → H' →L[ℂ] H'} {O : L → X → K →L[ℂ] K}
    {c : L → (Q → ℕ) → ℕ} (h : FImplH Z O Ow₀ c) (h' : HomOf Ow₀ Ow₁) : FImplH Z O Ow₁ c := by
  obtain ⟨Ow, circ, hI, Φ, hΦ⟩ := h
  obtain ⟨Ψ, hΨ⟩ := h'
  exact ⟨Ow, circ, hI, Φ.comp Ψ, fun q x => by rw [hΦ, hΨ]; rfl⟩

end Label

/-! ### The time-indexed primitive calls -/

section Time

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s M : ℕ}

/-- **The time-indexed primitive calls**: the supplied locators and writer of the sample at the
time address `r`, the time address an input register (`Fin M`). -/
def timeWriterOracles (D : Data (X × Fin M) n Z s) (W : X × Fin M → WReg n Z →L[ℂ] WReg n Z)
    (q : WQuery) (x : X) :
    PiLp 2 (fun _ : Fin M => Space n Z) →L[ℂ] PiLp 2 (fun _ : Fin M => Space n Z) :=
  WeightedClock.diagonal (V := fun _ : Fin M => Space n Z) (fun r => writerOracles D W q (x, r))

/-- The label register `ι × Fin M` of the sampled-time query, as `ι` copies of the time register. -/
def timeFlat (ι : Type*) [Fintype ι] (M : ℕ) (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] :
    PiLp 2 (fun _ : ι => PiLp 2 (fun _ : Fin M => V)) ≃ₗᵢ[ℂ] PiLp 2 (fun _ : ι × Fin M => V) :=
  (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : ι) (_ : Fin M) => V)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ V (Equiv.sigmaEquivProd ι (Fin M)))

omit [DecidableEq Z] in
/-- **The primitive calls of the sampled-time query are the time-indexed primitive calls** under one
fixed unital star-algebra homomorphism (the other labels spectators). -/
theorem homOf_time (ι : Type*) [Fintype ι] (D : Data (X × Fin M) n Z s)
    (W : X × Fin M → WReg n Z →L[ℂ] WReg n Z) :
    HomOf (TimeDependentODE.labelOracle (writerOracles D W)
      (TimeDependentODE.sample (ι := ι) (M := M))) (timeWriterOracles D W) := by
  refine ⟨((timeFlat ι M (Space n Z)).conjStarAlgEquiv :
    (PiLp 2 (fun _ : ι => PiLp 2 (fun _ : Fin M => Space n Z)) →L[ℂ]
      PiLp 2 (fun _ : ι => PiLp 2 (fun _ : Fin M => Space n Z))) →⋆ₐ[ℂ]
      (PiLp 2 (fun _ : ι × Fin M => Space n Z) →L[ℂ]
        PiLp 2 (fun _ : ι × Fin M => Space n Z))).comp (diagHom ι),
    fun q x => ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro b
  rfl

end Time

/-! ### Cost weights with the three source calls -/

section Weights

/-- Matrix calls of the writer family with the three source calls. -/
def wMatS : WQuery ⊕ GeneralSourceODE.SourceCall → ℕ := Sum.elim (fun _ => 1) (fun _ => 0)

/-- Source calls of the writer family with the three source calls. -/
def wSrcS : WQuery ⊕ GeneralSourceODE.SourceCall → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

/-- The converted weights of the three source calls. -/
abbrev wcostS : Query ⊕ GeneralSourceODE.SourceCall →
    (WQuery ⊕ GeneralSourceODE.SourceCall → ℕ) → ℕ :=
  Sum.elim (fun l w => wcost l (fun m => w (.inl m))) (fun l w => w (.inr l))

theorem wcostS_wMat_le (l : Query ⊕ GeneralSourceODE.SourceCall) :
    wcostS l wMatS ≤ 2 * GeneralSourceODE.Oracles.matrixCalls l := by
  rcases l with l | l
  · cases l <;> simp [wcostS, wcost, wMatS, GeneralSourceODE.Oracles.matrixCalls]
  · simp [wcostS, wMatS, GeneralSourceODE.Oracles.matrixCalls]

theorem wcostS_wSrc (l : Query ⊕ GeneralSourceODE.SourceCall) :
    wcostS l wSrcS = GeneralSourceODE.Oracles.sourceCalls l := by
  rcases l with l | l
  · cases l <;> simp [wcostS, wcost, wSrcS, GeneralSourceODE.Oracles.sourceCalls]
  · simp [wcostS, wSrcS, GeneralSourceODE.Oracles.sourceCalls]

end Weights

/-! ### The actual oracles of the time-dependent solver -/

section Mesh

open SparseHamiltonian.GeneralSourceExtensions
open GeneralSourceODE.Native (Label SourceBasis)

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s M m : ℕ}

/-- **The actual oracles of the time-dependent solver from a time-indexed writer**: the coherent
sampled-time matrix calls of the `N`-slot SELECT and the three source calls of
`MeshOracles.actualOracle` are implemented on the physical workspace with one more value-word
register (`single0`), at the converted weights `wcostS` (two writer calls per value call); every
converted matrix call is a time-indexed primitive call (`timeWriterOracles`) under one fixed unital
star-algebra homomorphism, every converted source call the source call with the scratch register a
spectator. -/
theorem fimplH_meshActual (D : Data (X × Fin M) n Z s)
    (W : X × Fin M → WReg n Z →L[ℂ] WReg n Z) (hWu : ∀ y, IsUnitary (W y))
    (c : X × Fin M → n × n → ℂ)
    (hW : ∀ y a, W y (EuclideanSpace.single (a, (0 : Z)) 1) =
      c y a • EuclideanSpace.single (a, D.table y a) 1)
    (N d : ℕ) {Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))}
    (hPw : ∀ x, IsUnitary (Pw x))
    {J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n}
    (hJ : ∀ x a, IsUnitary (J x a)) :
    ∃ (Ow : WQuery ⊕ GeneralSourceODE.SourceCall → X →
        PiLp 2 (fun _ : Z => MeshNative.PhysicalSpace ι n Z m M N d) →L[ℂ]
          PiLp 2 (fun _ : Z => MeshNative.PhysicalSpace ι n Z m M N d))
      (circ : Query ⊕ GeneralSourceODE.SourceCall → MultiOracleCircuit.Program Ow)
      (Φ : (PiLp 2 (fun _ : Fin M => Space n Z) →L[ℂ] PiLp 2 (fun _ : Fin M => Space n Z)) →⋆ₐ[ℂ]
        (PiLp 2 (fun _ : Z => MeshNative.PhysicalSpace ι n Z m M N d) →L[ℂ]
          PiLp 2 (fun _ : Z => MeshNative.PhysicalSpace ι n Z m M N d))),
      Impl (MeshOracles.actualOracle (ι := ι) D m N d Pw J) Ow
        (single0 Z (MeshNative.PhysicalSpace ι n Z m M N d)) circ wcostS ∧
      (∀ q x, Ow (.inl q) x = Φ (timeWriterOracles D W q x)) ∧
      (∀ k x, Ow (.inr k) x = diagHom (K' := MeshNative.PhysicalSpace ι n Z m M N d) Z
        (MeshOracles.actualOracle (ι := ι) D m N d Pw J (.inr k) x)) := by
  have h1 := (fimplH_flat D W hWu c hW).masked (B := NativeSparseMaskedAccess.Basis n Z)
    (ODENativeLayout.Branch Z)
  have h2 : FImplH Z (ODENativeCayley.oracle D) _ wcost :=
    h1.conj (FlatBranchNativeAccess.layout (ι := ODENativeLayout.Branch Z)
      (B := NativeSparseMaskedAccess.Basis n Z))
  have h3 : FImplH Z (TimeDependentODE.coherentOracle (ι := Label ι m) D)
      (timeWriterOracles D W) wcost :=
    (h2.label (TimeDependentODE.sample (ι := Label ι m) (M := M))).homOf
      (homOf_time (Label ι m) D W)
  have h4 : FImplH Z (TimeDependentODE.cayleyOracle (ι := Label ι m) D) _ wcost :=
    h3.conj (TimeDependentODE.layout (ι := Label ι m) (M := M) (n := n) (Z := Z))
  have h5 := h4.masked (B := TimeDependentODE.Basis (Label ι m) n Z M)
    (ActiveRegisterLayout.Label PUnit.{1} N d)
  have h6 : FImplH Z (MeshNative.matrixOracle (ι := ι) D m N d) _ wcost := h5.diag Bool
  have h7 := h6.conj (MeshNative.matrixLayout (ι := ι) (n := n) (Z := Z) m M N d)
  have h8 := h7.masked (B := MeshNative.MatrixBasis ι n Z m M N d) (SourceBasis ι n m)
  obtain ⟨Ow, circ, Φ, hI0, hΦ, hU⟩ := h8.extra
    (fun k x => MeshOracles.actualOracle (ι := ι) D m N d Pw J (.inr k) x)
    (fun k x => MeshOracles.actualOracle_unitary (ι := ι) D m N d hPw hJ (.inr k) x)
  exact ⟨Ow, circ, Φ, hI0, hΦ, hU⟩

end Mesh

end

end SparseHamiltonian.WriterAccess

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Set
open SparseHamiltonian.GeneralSourceExtensions SparseHamiltonian.WriterAccess
open scoped InnerProduct InnerProductSpace
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 4000000

universe u v w

/-- **Theorem `ode:thm:time` with a time-indexed writer value oracle.** The hypotheses of
`ode_thm_time`, and a supplied unitary writer `W (x, r)` for every sample `r` with
`W (x, r) |a, 0⟩ = c (x, r) a |a, w_{r,a}⟩` for the stored words `w_{r,a} = D.table (x, r) a` and
any phases: the time-indexed primitive calls (`timeWriterOracles`: the locators and the writer of
the sample at the time address, the time address an input register). On the released workspace
with one more value-word register, the converted protocol `A'` (every coherent sampled-time value
call replaced by writer, adder and inverse writer on the scratch register; every locator and source
call by the same call with the scratch register a spectator; every seed and output isometry
encoded) has the success mass and conditional output of the released protocol `A` of
`ode_thm_time` on every instance, at most twice its worst-case matrix calls (locator and writer
calls) and the same worst-case source calls; every converted matrix call is a time-indexed primitive
call under one fixed unital star-algebra homomorphism `Φ`. Under the instance conditions of
`ode_thm_time`: `HeraldedOutput` for `A'` and the doubled matrix-call budget. -/
theorem ode_thm_time_writer :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s M : ℕ} (D : Data (X × Fin M) n Z s), 0 < M →
        ∀ (W : X × Fin M → WReg n Z →L[ℂ] WReg n Z) (c : X × Fin M → n × n → ℂ),
        (∀ y, IsUnitary (W y)) →
        (∀ y a, W y (EuclideanSpace.single (a, (0 : Z)) 1) =
          c y a • EuclideanSpace.single (a, D.table y a) 1) →
        ∀ (t : ℕ → ℝ) (N : ℕ), 0 < N →
        ∀ (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ),
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 1 ≤ gbar → 1 ≤ cq → 0 < ε → ε ≤ 1 →
        TimeDependentExtensions.IsMesh t M T →
        8 * s * ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T) ≤ N →
        3 * (Real.sqrt (2 * (s : ℝ)) *
          ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
          TimeDependentODE.precision (cq * gbar) ε * (N : ℝ) ^ 2 →
        (∀ i, v i ∈ Icc 0 T) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        ∀ (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))), (∀ x, IsUnitary (Pw x)) →
        ∀ (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
        (∀ x a, IsUnitary (J x a)) →
        ∀ seed : EuclideanSpace ℂ n, ‖seed‖ = 1 →
        ∃ (d : ℕ) (A : ODERepeatProtocol.Protocol
            (MeshOracles.actualOracle (ι := TimeDependentODE.Index D T (cq * gbar) ε) D m N d Pw J)
            (EuclideanSpace ℂ n))
          (Ow : WQuery ⊕ GeneralSourceODE.SourceCall → X →
            PiLp 2 (fun _ : Z => MeshNative.PhysicalSpace (TimeDependentODE.Index D T (cq * gbar) ε)
              n Z m M N d) →L[ℂ]
            PiLp 2 (fun _ : Z => MeshNative.PhysicalSpace (TimeDependentODE.Index D T (cq * gbar) ε)
              n Z m M N d))
          (Φ : (PiLp 2 (fun _ : Fin M => WriterAccess.Space n Z) →L[ℂ]
              PiLp 2 (fun _ : Fin M => WriterAccess.Space n Z)) →⋆ₐ[ℂ]
            (PiLp 2 (fun _ : Z => MeshNative.PhysicalSpace (TimeDependentODE.Index D T (cq * gbar) ε)
              n Z m M N d) →L[ℂ]
            PiLp 2 (fun _ : Z => MeshNative.PhysicalSpace (TimeDependentODE.Index D T (cq * gbar) ε)
              n Z m M N d)))
          (_ : ∀ q x, Ow (.inl q) x = Φ (timeWriterOracles D W q x))
          (_ : ∀ k x, Ow (.inr k) x = diagHom (K' := MeshNative.PhysicalSpace
              (TimeDependentODE.Index D T (cq * gbar) ε) n Z m M N d) Z
            (MeshOracles.actualOracle (ι := TimeDependentODE.Index D T (cq * gbar) ε) D m N d Pw J
              (.inr k) x))
          (A' : ODERepeatProtocol.Protocol Ow (EuclideanSpace ℂ n)),
          (∀ x, A'.successMass x = A.successMass x ∧
            A'.conditionalDensity x = A.conditionalDensity x) ∧
          A'.worstCost wMatS ≤ 2 * A.worstCost GeneralSourceODE.Oracles.matrixCalls ∧
          A'.worstCost wSrcS = A.worstCost GeneralSourceODE.Oracles.sourceCalls ∧
          ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
            (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
            (bv : Fin m → EuclideanSpace ℂ n)
            (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces t G →
            RepresentedSampleODE.MildSolution t T b sol U →
            formal_classicalPropagator G t T U →
            GeneralSourceODE.Compiled.WeightPrep (Pw x) (GeneralSourceODE.sources (sol 0) bv ω) →
            (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
            (∀ i, ω i ≠ 0 → bv i ≠ 0 →
              J x (some i) seed = ODEStateNormalization.unitDirection (bv i)) →
            ODESourceBranches.mass (GeneralSourceODE.sources (sol 0) bv ω) ≤
              cq * Mesh.meshScale sol b t →
            ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
                ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * Mesh.meshScale sol b t →
            sol T ≠ 0 →
            Mesh.meshScale sol b t ≤ gbar * ‖sol T‖ →
            ζ + cq * (Mesh.sampleError D x t G + 2 * RepresentedSampleODE.dissipativeError D x t G +
                2 * Mesh.refinementError D t T N) ≤ ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (cq * gbar) ε *
                (RepresentedSampleODE.dissipativeError D x t G + Mesh.refinementError D t T N) ≤
              TimeDependentODE.precision (cq * gbar) ε →
            HeraldedOutput A' x (ODEStateNormalization.unitDirection (sol T)) ε ∧
            (A'.worstCost wMatS : ℝ) ≤
              2 * (C * (cq * gbar) * (Real.sqrt s * (T * etaH + T * etaD *
                  Real.log (40000 * cq * gbar / ε)) +
                Real.sqrt (s * (T * etaH + T * etaD * Real.log (40000 * cq * gbar / ε)) *
                  Real.log (40000 * cq * gbar / ε)) + Real.log (40000 * cq * gbar / ε))) ∧
            (A'.worstCost wSrcS : ℝ) ≤ C * (cq * gbar) := by
  obtain ⟨C, hC, hode⟩ := ode_thm_time.{u, v, w}
  refine ⟨C, hC, ?_⟩
  intro X n Z _ _ _ _ _ s M D hM W c hWu hW t N hN etaH etaD T gbar cq ε m v ω hH hDiss hT hg hcq
    hε hεOne hmesh hClock hCayley hv hrH hcH hrD hcD Pw hPw J hJ seed hSeed
  obtain ⟨d, A, hA⟩ := hode D hM t N hN etaH etaD T gbar cq ε v ω hH hDiss hT hg hcq hε hεOne
    hmesh hClock hCayley hv hrH hcH hrD hcD Pw hPw J hJ seed hSeed
  obtain ⟨Ow, circ, Φ, hI, hΦ, hU⟩ := fimplH_meshActual
    (ι := TimeDependentODE.Index D T (cq * gbar) ε) D W hWu c hW N d hPw hJ
  have hsrc : (fun l => wcostS l wSrcS) = GeneralSourceODE.Oracles.sourceCalls :=
    funext wcostS_wSrc
  have hmat : A.worstCost (fun l => wcostS l wMatS) ≤
      2 * A.worstCost GeneralSourceODE.Oracles.matrixCalls :=
    protocol_worstCost_le_mul A (w₁ := fun l => wcostS l wMatS)
      (w₂ := GeneralSourceODE.Oracles.matrixCalls) (k := 2) wcostS_wMat_le
  refine ⟨d, A, Ow, Φ, hΦ, hU, encodeProtocol hI A,
    fun x => ⟨encodeProtocol_successMass hI A x, encodeProtocol_conditionalDensity hI A x⟩, ?_, ?_,
    ?_⟩
  · rw [encodeProtocol_worstCost]
    exact hmat
  · rw [encodeProtocol_worstCost, hsrc]
  · intro x G b sol bv U ζ hG hreg hsol hUm hWp hL0 hL hMass hInt hTarget hB hB1 hB2
    obtain ⟨⟨h₁, h₂, h₃⟩, hMat, hSrc⟩ := hA x G b sol bv U ζ hG hreg hsol hUm hWp hL0 hL hMass
      hInt hTarget hB hB1 hB2
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [encodeProtocol_successMass]; exact h₁
    · rw [encodeProtocol_conditionalDensity]; exact h₂
    · rw [encodeProtocol_conditionalDensity]; exact h₃
    · rw [encodeProtocol_worstCost]
      have hle : (A.worstCost (fun l => wcostS l wMatS) : ℝ) ≤
          2 * (A.worstCost GeneralSourceODE.Oracles.matrixCalls : ℝ) := by
        exact_mod_cast hmat
      linarith
    · rw [encodeProtocol_worstCost, hsrc]
      exact hSrc

end

end ManuscriptConformance
