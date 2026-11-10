import ManuscriptConformance.WriterTimeEndpoints
import ManuscriptConformance.ODEGeneral

/-!
# Theorem `ode:thm:general` with a writer value oracle (handover item B4)

`ode_thm_general_writer` restates Theorem `ode:thm:general` for value access by a reversible writer
specified only on a clean target (`WriterAccess`). The released protocol of `ode_thm_general` is run
with every circuit compiled (every value call replaced by writer, adder and inverse writer on one
more clean scratch register; every locator and source call by the same call with the scratch
register a spectator) and every seed and output isometry encoded: the same Born probabilities,
success mass and conditional output (so the same reduced output), at most twice the worst-case
matrix calls (locator and writer calls) and the same worst-case calls of each source interface.

The block-encoded Taylor history calls the native block encoding on `K` fresh copies of its
register (`GeneralODE.Registers.powOracle`: label `(i, l)`, the call `l` on the `i`-th copy), so
the converted calls are primitive calls under a homomorphism determined by the copy they act on:

* `ampHom_single0`, `Impl.fhom`: every unital star-algebra homomorphism of the physical workspace
  (spectators, reindexing, masking, the damping qubit) is a layer of a converted implementation,
  through its blockwise image `ampHom`;
* `Impl.fhomL`, `powHom`, `powOracle_eq`: the layer of a family of homomorphisms indexed by the
  label, for the `K` copies (`powHom k i` places a factor on the `i`-th of `k` fresh copies);
* `maskHom`, `masked_eq`: the masked native call as a homomorphism;
* `fimplH_generalFlat`, `impl_generalPhysical`: the actual oracles of `ode:thm:general`.
-/

namespace SparseHamiltonian.WriterAccess

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct InnerProductSpace
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 100000
set_option maxRecDepth 4096

/-! ### Homomorphism layers -/

section HomLayer

variable {K K₂ : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]
  {Z : Type*} [Fintype Z] [DecidableEq Z] [AddCommGroup Z]
  {X L Q : Type*}

omit [CompleteSpace K] in
theorem single0_eq_injB (v : K) : single0 Z K v = injB (0 : Z) v := by
  apply PiLp.ext
  intro t
  rw [single0_apply, injB_apply]

/-- **The blockwise image of an operator preserving the clean scratch word preserves it**, acting
there as the image of the clean block. -/
theorem ampHom_single0 (Ψ : (K →L[ℂ] K) →⋆ₐ[ℂ] (K₂ →L[ℂ] K₂))
    {A : PiLp 2 (fun _ : Z => K) →L[ℂ] PiLp 2 (fun _ : Z => K)} {A₀ : K →L[ℂ] K}
    (h : A ∘L single0 Z K = single0 Z K ∘L A₀) :
    ampHom Z Ψ A ∘L single0 Z K₂ = single0 Z K₂ ∘L Ψ A₀ := by
  have hb : ∀ z, blk A z 0 = if z = 0 then A₀ else 0 := by
    intro z
    apply ContinuousLinearMap.ext
    intro v
    rw [blk_apply, ← single0_eq_injB]
    have hv := congrArg (fun T => T v) h
    simp only [comp_apply] at hv
    rw [hv, single0_apply]
    split_ifs <;> rfl
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro z
  rw [comp_apply, comp_apply, single0_eq_injB (Z := Z) u, apply_eq_sum_blk,
    single0_eq_injB (Z := Z) (Ψ A₀ u), injB_apply, Finset.sum_eq_single 0]
  · rw [ampHom_apply, blk_ampFun, hb, injB_apply, if_pos rfl]
    split_ifs with hz <;> simp
  · intro b' _ hb'
    rw [injB_apply, if_neg hb', map_zero]
  · simp

/-- **A homomorphism layer**: a converted implementation of `O` gives one of `Ψ ∘ O` for every
unital star-algebra homomorphism `Ψ` of the physical workspace, with the blockwise image of `Ψ` on
the converted calls and the same weighted costs. -/
theorem Impl.fhom {O : L → X → K →L[ℂ] K}
    {Ow : Q → X → PiLp 2 (fun _ : Z => K) →L[ℂ] PiLp 2 (fun _ : Z => K)}
    {circ : L → MultiOracleCircuit.Program Ow} {c : L → (Q → ℕ) → ℕ}
    (h : Impl O Ow (single0 Z K) circ c) (Ψ : (K →L[ℂ] K) →⋆ₐ[ℂ] (K₂ →L[ℂ] K₂)) :
    Impl (fun l x => Ψ (O l x)) (fun q x => ampHom Z Ψ (Ow q x)) (single0 Z K₂)
      (fun l => MultiOracleCircuit.Program.mapHom
        (O' := fun q x => ampHom Z Ψ (Ow q x)) (ampHom Z Ψ) id (circ l)) c where
  iso := single0_isometry
  unitary l x := GeneralODE.Registers.isUnitary_map Ψ (h.unitary l x)
  unitaryW q x := GeneralODE.Registers.isUnitary_map _ (h.unitaryW q x)
  intertwines l x := by
    rw [MultiOracleCircuit.Program.eval_mapHom (ampHom Z Ψ) id (fun _ _ => rfl)]
    exact ampHom_single0 Ψ (h.intertwines l x)
  cost l w := by
    rw [MultiOracleCircuit.Program.cost_mapHom, h.cost]
    rfl

/-- **A layer of label-dependent homomorphisms**: the call `(i, l)` is `Ψ i (O l)`; the converted
call `(i, q)` is the blockwise image of `Ψ i` of the converted call `q`. -/
theorem Impl.fhomL {I : Type*} {O : L → X → K →L[ℂ] K}
    {Ow : Q → X → PiLp 2 (fun _ : Z => K) →L[ℂ] PiLp 2 (fun _ : Z => K)}
    {circ : L → MultiOracleCircuit.Program Ow} {c : L → (Q → ℕ) → ℕ}
    (h : Impl O Ow (single0 Z K) circ c) (Ψ : I → (K →L[ℂ] K) →⋆ₐ[ℂ] (K₂ →L[ℂ] K₂)) :
    Impl (fun (il : I × L) x => Ψ il.1 (O il.2 x))
      (fun (iq : I × Q) x => ampHom Z (Ψ iq.1) (Ow iq.2 x)) (single0 Z K₂)
      (fun il => MultiOracleCircuit.Program.mapHom
        (O' := fun (iq : I × Q) x => ampHom Z (Ψ iq.1) (Ow iq.2 x)) (ampHom Z (Ψ il.1))
        (fun q => (il.1, q)) (circ il.2))
      (fun il w => c il.2 (fun q => w (il.1, q))) where
  iso := single0_isometry
  unitary il x := GeneralODE.Registers.isUnitary_map (Ψ il.1) (h.unitary il.2 x)
  unitaryW iq x := GeneralODE.Registers.isUnitary_map _ (h.unitaryW iq.2 x)
  intertwines il x := by
    rw [MultiOracleCircuit.Program.eval_mapHom (ampHom Z (Ψ il.1)) (fun q => (il.1, q))
      (fun _ _ => rfl)]
    exact ampHom_single0 (Ψ il.1) (h.intertwines il.2 x)
  cost il w := by
    rw [MultiOracleCircuit.Program.cost_mapHom, h.cost]

end HomLayer

/-! ### The `k` fresh copies of the Taylor history -/

section Pow

open GeneralODE.Registers (Anc onFactor firstFrame secondFrame powOracle)

variable {σ ν : Type} [Fintype σ] [Fintype ν] [DecidableEq σ] [DecidableEq ν]

/-- **The homomorphism placing a factor on the `i`-th of `k` fresh copies.** -/
def powHom : ∀ k, Fin k → ((EuclideanSpace ℂ (σ × ν) →L[ℂ] EuclideanSpace ℂ (σ × ν)) →⋆ₐ[ℂ]
    (EuclideanSpace ℂ (σ × Anc ν k) →L[ℂ] EuclideanSpace ℂ (σ × Anc ν k)))
  | 0, i => i.elim0
  | k + 1, i => if h : i = Fin.last k then onFactor (secondFrame σ (Anc ν k) ν)
      else (onFactor (firstFrame σ (Anc ν k) ν)).comp (powHom k (i.castPred h))

omit [DecidableEq σ] [DecidableEq ν] in
/-- The power oracle is the factor oracle on the copy of its label. -/
theorem powOracle_eq {X L : Type*}
    (F : L → X → EuclideanSpace ℂ (σ × ν) →L[ℂ] EuclideanSpace ℂ (σ × ν)) :
    ∀ k (il : Fin k × L) (x : X), powOracle F k il x = powHom k il.1 (F il.2 x)
  | 0, il, _ => il.1.elim0
  | k + 1, il, x => by
      simp only [powOracle, powHom]
      split_ifs with h
      · rfl
      · exact congrArg (fun U => onFactor (firstFrame σ (Anc ν k) ν) U)
          (powOracle_eq F k (il.1.castPred h, il.2) x)

end Pow

/-! ### The masked native call as a homomorphism -/

section Mask

variable (ι B : Type*) [Fintype ι] [Fintype B] [DecidableEq B]

/-- The masked native call: the same call in every branch, with the control, dummy and reference
registers spectators. -/
def maskHom : (EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) →⋆ₐ[ℂ]
    (NativeMaskedOracle.Physical ι B →L[ℂ] NativeMaskedOracle.Physical ι B) :=
  (diagHom (K' := EuclideanSpace ℂ (NativeControlledOracle.Workspace B)) ι).comp
    (GeneralODE.Registers.specHom ((Bool × B) × B) B)

variable {ι B}

omit [DecidableEq B] in
theorem masked_eq {X L : Type*} (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (l : L) (x : X) : NativeMaskedProgram.oracle (ι := ι) F l x = maskHom ι B (F l x) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  rfl

end Mask

/-! ### Cost weights with copy labels -/

section Weights

variable {I : Type*}

/-- Matrix calls of the writer family on labelled copies, with the two source interfaces. -/
def wMatG : (I × WQuery) ⊕ Bool → ℕ := Sum.elim (fun _ => 1) (fun _ => 0)

/-- Calls of one source interface. -/
def wSrcG (b : Bool) : (I × WQuery) ⊕ Bool → ℕ :=
  Sum.elim (fun _ => 0) (fun c => if c = b then 1 else 0)

/-- The converted weights on labelled copies. -/
abbrev wcostG : (I × Query) ⊕ Bool → ((I × WQuery) ⊕ Bool → ℕ) → ℕ :=
  Sum.elim (fun il w => wcost il.2 (fun q => w (.inl (il.1, q)))) (fun b w => w (.inr b))

theorem wcostG_wMat_le (l : (I × Query) ⊕ Bool) :
    wcostG l wMatG ≤ 2 * ODESourceQueryBudget.matrixWeight (fun _ => 1) l := by
  rcases l with ⟨i, l⟩ | l
  · cases l <;> simp [wcostG, wcost, wMatG, ODESourceQueryBudget.matrixWeight]
  · simp [wcostG, wMatG, ODESourceQueryBudget.matrixWeight]

theorem wcostG_wSrc (b : Bool) (l : (I × Query) ⊕ Bool) :
    wcostG l (wSrcG b) = ODESourceQueryBudget.sourceWeight b l := by
  rcases l with ⟨i, l⟩ | l
  · cases l <;> simp [wcostG, wcost, wSrcG, ODESourceQueryBudget.sourceWeight]
  · simp [wcostG, wSrcG, ODESourceQueryBudget.sourceWeight]

end Weights

/-! ### The actual oracles of `ode:thm:general` -/

section General

open GeneralODE.Registers (Ctl PowAnc HistAnc Term)
open GeneralODE.History (Slot)

variable {X n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

/-- **The native block-encoding oracles of `ode:thm:general` from a writer.** -/
theorem fimplH_generalFlat (D : Data X n Z s) (W : X → WReg n Z →L[ℂ] WReg n Z)
    (hWu : ∀ x, IsUnitary (W x)) (c : X → n × n → ℂ)
    (hW : ∀ x a, W x (EuclideanSpace.single (a, (0 : Z)) 1) =
      c x a • EuclideanSpace.single (a, D.table x a) 1) (N T d : ℕ) :
    FImplH Z (GeneralODE.NativeBlock.flatOracle D N T d) (writerOracles D W) wcost := by
  have h1 := (fimplH_flat D W hWu c hW).masked (B := NativeSparseMaskedAccess.Basis n Z)
    (ODENativeLayout.Branch Z)
  have h2 : FImplH Z (ODENativeCayley.oracle D) _ wcost :=
    h1.conj (FlatBranchNativeAccess.layout (ι := ODENativeLayout.Branch Z)
      (B := NativeSparseMaskedAccess.Basis n Z))
  have h3 : FImplH Z (ODECoherentCayley.oracle (ι := GeneralODE.NativeBlock.Branch N) D) _
      wcost := h2.diag (GeneralODE.NativeBlock.Branch N)
  have h4 : FImplH Z (ODEJointNative.cayleyOracle (ι := GeneralODE.NativeBlock.Branch N) D) _
      wcost := h3.conj (ODEJointNative.layout (ι := GeneralODE.NativeBlock.Branch N) (n := n)
        (Z := Z))
  have h5 := h4.masked (B := ODEJointNative.Basis (GeneralODE.NativeBlock.Branch N) n Z)
    (ActiveRegisterLayout.Label PUnit.{1} T d)
  exact h5.conj (FlatBranchNativeAccess.layout (ι := ActiveRegisterLayout.Label PUnit.{1} T d)
    (B := ODEJointNative.Basis (GeneralODE.NativeBlock.Branch N) n Z))

/-- **The actual oracles of `ode:thm:general` from a writer**: the native block-encoding calls on
the `K` copies of the Taylor history and the two source interfaces of
`GeneralODE.physicalOracle` are implemented on its workspace with one more value-word register
(`single0`), at the converted weights `wcostG` (two writer calls per value call); the converted
call `(i, q)` is the primitive call `q` (a locator or the writer) under a fixed unital
star-algebra homomorphism `Φ i` determined by the copy `i` it acts on, and every converted source
call is the source call with the scratch register a spectator. -/
theorem impl_generalPhysical (D : Data X n Z s) (W : X → WReg n Z →L[ℂ] WReg n Z)
    (hWu : ∀ x, IsUnitary (W x)) (c : X → n × n → ℂ)
    (hW : ∀ x a, W x (EuclideanSpace.single (a, (0 : Z)) 1) =
      c x a • EuclideanSpace.single (a, D.table x a) 1)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y)) (N Tn d m K w : ℕ) :
    ∃ (Ow : (Fin K × WQuery) ⊕ Bool → X →
        PiLp 2 (fun _ : Z => GeneralODE.Register n Z N Tn d m K w) →L[ℂ]
          PiLp 2 (fun _ : Z => GeneralODE.Register n Z N Tn d m K w))
      (circ : (Fin K × Query) ⊕ Bool → MultiOracleCircuit.Program Ow)
      (Φ : Fin K → (Space n Z →L[ℂ] Space n Z) →⋆ₐ[ℂ]
        (PiLp 2 (fun _ : Z => GeneralODE.Register n Z N Tn d m K w) →L[ℂ]
          PiLp 2 (fun _ : Z => GeneralODE.Register n Z N Tn d m K w))),
      Impl (GeneralODE.physicalOracle D J₀ Jb N Tn d m K w) Ow
        (single0 Z (GeneralODE.Register n Z N Tn d m K w)) circ wcostG ∧
      (∀ i q x, Ow (.inl (i, q)) x = Φ i (writerOracles D W q x)) ∧
      (∀ b x, Ow (.inr b) x = diagHom (K' := GeneralODE.Register n Z N Tn d m K w) Z
        (GeneralODE.physicalOracle D J₀ Jb N Tn d m K w (.inr b) x)) := by
  have hF := fimplH_generalFlat D W hWu c hW N Tn d
  have hFac : FImplH Z (GeneralODE.Registers.facOracle (n := n) m K
      (GeneralODE.NativeBlock.flatOracle D N Tn d)) (writerOracles D W) wcost :=
    (hF.spectator (Ctl m K)).spectator (Ctl m K × n)
  obtain ⟨Ow1, circ1, hI1, Φ1, hΦ1⟩ := hFac
  have hI2 := (hI1.fhomL (powHom K)).congr
    (fun il x => (powOracle_eq _ K il x).symm)
  have hI3 := hI2.fhom ((GeneralODE.Registers.specHom (Slot m × n)
    (HistAnc n (GeneralODE.NativeBlock.FlatBasis N n Z Tn d) m K)).comp
      (GeneralODE.Registers.specHom Term
        ((Ctl m K × n) × PowAnc (GeneralODE.NativeBlock.FlatBasis N n Z Tn d) m K)))
  have hI4 := hI3.fextra (GeneralODE.Solver.sourceOracle (m := m)
      (a := HistAnc n (GeneralODE.NativeBlock.FlatBasis N n Z Tn d) m K) J₀ Jb)
    (GeneralODE.Solver.sourceOracle_unitary J₀ Jb hJ₀ hJb)
  have hI5 := (hI4.fhom (maskHom (Fin w)
    ((Slot m × n) × HistAnc n (GeneralODE.NativeBlock.FlatBasis N n Z Tn d) m K))).congr
      (fun l x => (masked_eq _ l x).symm)
  have hI6 := hI5.fhom (GeneralODE.Registers.diagHom Bool (NativeMaskedOracle.Physical (Fin w)
    ((Slot m × n) × HistAnc n (GeneralODE.NativeBlock.FlatBasis N n Z Tn d) m K)))
  refine ⟨_, _, fun i => (((ampHom Z (GeneralODE.Registers.diagHom Bool
      (NativeMaskedOracle.Physical (Fin w)
        ((Slot m × n) × HistAnc n (GeneralODE.NativeBlock.FlatBasis N n Z Tn d) m K)))).comp
    (ampHom Z (maskHom (Fin w)
      ((Slot m × n) × HistAnc n (GeneralODE.NativeBlock.FlatBasis N n Z Tn d) m K)))).comp
    ((ampHom Z ((GeneralODE.Registers.specHom (Slot m × n)
      (HistAnc n (GeneralODE.NativeBlock.FlatBasis N n Z Tn d) m K)).comp
        (GeneralODE.Registers.specHom Term
          ((Ctl m K × n) × PowAnc (GeneralODE.NativeBlock.FlatBasis N n Z Tn d) m K)))).comp
      (ampHom Z (powHom K i)))).comp Φ1, hI6.congr (fun l x => rfl), ?_, ?_⟩
  · intro i q x
    simp only [StarAlgHom.comp_apply]
    rw [← hΦ1]
    rfl
  · intro b x
    simp only [Sum.elim_inr]
    rw [ampHom_diagonal, ampHom_diagonal]
    simp only [GeneralODE.physicalOracle, GeneralODE.Amplify.liftOracle, masked_eq, Sum.elim_inr]
    rfl

end General

end

end SparseHamiltonian.WriterAccess

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseHamiltonian.WriterAccess
open scoped InnerProduct InnerProductSpace

set_option maxRecDepth 4096
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:general` with a writer value oracle.** The hypotheses of
`ode_thm_general`, and a supplied unitary writer `Wr x` with `Wr x |a, 0⟩ = cw x a |a, w_a⟩` for
the stored words `w_a = D.table x a` and any phases. On the released workspace with one more
value-word register, the converted protocol `A'` (every value call replaced by writer, adder and
inverse writer on the scratch register; every locator and source call by the same call with the
scratch register a spectator; every seed and output isometry encoded) has the success mass and
conditional output of the released protocol `A` of `ode_thm_general` on every instance (so the
same reduced output), at most twice its worst-case matrix calls (locator and writer calls) and the
same worst-case calls of each source interface; the converted call on the `i`-th copy of the
Taylor history is a primitive call under a fixed unital star-algebra homomorphism `Φ i`. Under the
instance conditions of `ode_thm_general`: success at least `2/3` and reduced conditional output
within trace distance `ε` for `A'`, with the doubled matrix-call budget. -/
theorem ode_thm_general_writer (c q₀ : ℝ) (hc : 0 ≤ c) (hq₀ : 0 < q₀) (hq₀1 : q₀ ≤ 1)
    (ext_blockSolver :
      MixedOutputODE.MixedBlockSolver (fun κ δ => c * κ * Real.log (2 / δ)) q₀)
    {X n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
    {s : ℕ} (D : Data X n Z s) (Wr : X → WReg n Z →L[ℂ] WReg n Z) (cw : X → n × n → ℂ)
    (hWu : ∀ x, IsUnitary (Wr x))
    (hWr : ∀ x a, Wr x (EuclideanSpace.single (a, (0 : Z)) 1) =
      cw x a • EuclideanSpace.single (a, D.table x a) 1)
    (Λ T Cbar gpath ε r₀ rb : ℝ)
    (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ gpath) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hA : ∀ x, ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ Λ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hseed : ‖seed‖ = 1) :
    ∃ (Tn d w : ℕ) (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ODERepeatProtocol.Protocol
        (GeneralODE.physicalOracle D J₀ Jb (GeneralODE.Plan.arcDegree Λ T Cbar gpath ε) Tn d
          (GeneralODE.Plan.steps Λ T) (GeneralODE.Plan.degree Λ T Cbar gpath ε) w)
        (EuclideanSpace ℂ (n × W)))
      (Ow : (Fin (GeneralODE.Plan.degree Λ T Cbar gpath ε) × WQuery) ⊕ Bool → X →
        PiLp 2 (fun _ : Z => GeneralODE.Register n Z (GeneralODE.Plan.arcDegree Λ T Cbar gpath ε)
          Tn d (GeneralODE.Plan.steps Λ T) (GeneralODE.Plan.degree Λ T Cbar gpath ε) w) →L[ℂ]
        PiLp 2 (fun _ : Z => GeneralODE.Register n Z (GeneralODE.Plan.arcDegree Λ T Cbar gpath ε)
          Tn d (GeneralODE.Plan.steps Λ T) (GeneralODE.Plan.degree Λ T Cbar gpath ε) w))
      (Φ : Fin (GeneralODE.Plan.degree Λ T Cbar gpath ε) →
        (WriterAccess.Space n Z →L[ℂ] WriterAccess.Space n Z) →⋆ₐ[ℂ]
        (PiLp 2 (fun _ : Z => GeneralODE.Register n Z (GeneralODE.Plan.arcDegree Λ T Cbar gpath ε)
          Tn d (GeneralODE.Plan.steps Λ T) (GeneralODE.Plan.degree Λ T Cbar gpath ε) w) →L[ℂ]
        PiLp 2 (fun _ : Z => GeneralODE.Register n Z (GeneralODE.Plan.arcDegree Λ T Cbar gpath ε)
          Tn d (GeneralODE.Plan.steps Λ T) (GeneralODE.Plan.degree Λ T Cbar gpath ε) w)))
      (_ : ∀ i q x, Ow (.inl (i, q)) x = Φ i (writerOracles D Wr q x))
      (_ : ∀ b x, Ow (.inr b) x = diagHom (K' := GeneralODE.Register n Z
          (GeneralODE.Plan.arcDegree Λ T Cbar gpath ε) Tn d (GeneralODE.Plan.steps Λ T)
          (GeneralODE.Plan.degree Λ T Cbar gpath ε) w) Z
        (GeneralODE.physicalOracle D J₀ Jb (GeneralODE.Plan.arcDegree Λ T Cbar gpath ε) Tn d
          (GeneralODE.Plan.steps Λ T) (GeneralODE.Plan.degree Λ T Cbar gpath ε) w (.inr b) x))
      (A' : ODERepeatProtocol.Protocol Ow (EuclideanSpace ℂ (n × W))),
      (∀ x, A'.successMass x = A.successMass x ∧
        A'.conditionalDensity x = A.conditionalDensity x) ∧
      A'.worstCost wMatG ≤ 2 * A.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) ∧
      (∀ b : Bool, A'.worstCost (wSrcG b) = A.worstCost (ODESourceQueryBudget.sourceWeight b)) ∧
      (A'.worstCost wMatG : ℝ) ≤
          2 * (227776401506304000 * (c * (gpath / Real.sqrt q₀) * (Cbar * (1 + Λ * T)) *
            Real.sqrt s * (1 + Real.log ((1 + Λ * T) * Cbar * gpath / ε)) ^ 3)) ∧
      (∀ b : Bool, (A'.worstCost (wSrcG b) : ℝ) ≤
          26292000 * (c * (gpath / Real.sqrt q₀) * (Cbar * (1 + Λ * T)) *
            (1 + Real.log ((1 + Λ * T) * Cbar * gpath / ε)))) ∧
      ∀ (x : X) (v b : EuclideanSpace ℂ n), ‖v‖ = r₀ → ‖b‖ = rb →
        (v ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection v) →
        (b ≠ 0 → Jb x seed = ODEStateNormalization.unitDirection b) →
        (∀ t, 0 ≤ t → t ≤ T →
          ‖NormedSpace.exp (t • ODEPublicSourceMesh.generator D x)‖ ≤ Cbar) →
        (∀ t, 0 ≤ t → t ≤ T →
          ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b t‖ ≤
            gpath * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖) →
        ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 →
        2 / 3 ≤ A'.successMass x ∧
          ODEMixedOutput.IsDensity (MixedOutputODE.ptrace (A'.conditionalDensity x)) ∧
          TraceDistanceLE (MixedOutputODE.ptrace (A'.conditionalDensity x))
            (ODEStateNormalization.unitDirection
              (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T)) ε := by
  obtain ⟨Tn, d, w, W, hW, hWd, A, h1, h2, h3⟩ := ode_thm_general c q₀ hc hq₀ hq₀1
    ext_blockSolver D Λ T Cbar gpath ε r₀ rb hΛ hT hC hg hε hε1 hA J₀ Jb hJ₀ hJb seed hseed
  obtain ⟨Ow, circ, Φ, hI, hΦ, hU⟩ := impl_generalPhysical D Wr hWu cw hWr J₀ Jb hJ₀ hJb
    (GeneralODE.Plan.arcDegree Λ T Cbar gpath ε) Tn d (GeneralODE.Plan.steps Λ T)
    (GeneralODE.Plan.degree Λ T Cbar gpath ε) w
  have hmat : A.worstCost (fun l => wcostG l wMatG) ≤
      2 * A.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) :=
    protocol_worstCost_le_mul A (w₁ := fun l => wcostG l wMatG)
      (w₂ := ODESourceQueryBudget.matrixWeight (fun _ => 1)) (k := 2) wcostG_wMat_le
  have hsrc : ∀ b : Bool,
      (fun l => wcostG (I := Fin (GeneralODE.Plan.degree Λ T Cbar gpath ε)) l (wSrcG b)) =
        ODESourceQueryBudget.sourceWeight b :=
    fun b => funext (wcostG_wSrc b)
  refine ⟨Tn, d, w, W, hW, hWd, A, Ow, Φ, hΦ, hU, encodeProtocol hI A,
    fun x => ⟨encodeProtocol_successMass hI A x, encodeProtocol_conditionalDensity hI A x⟩, ?_,
    fun b => ?_, ?_, fun b => ?_, ?_⟩
  · rw [encodeProtocol_worstCost]
    exact hmat
  · rw [encodeProtocol_worstCost, hsrc b]
  · rw [encodeProtocol_worstCost]
    have hle : (A.worstCost (fun l => wcostG l wMatG) : ℝ) ≤
        2 * (A.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) := by
      exact_mod_cast hmat
    linarith
  · rw [encodeProtocol_worstCost, hsrc b]
    exact h2 b
  · intro x v b hv hb hJv hJbv hCA hpath hsol
    have h := h3 x v b hv hb hJv hJbv hCA hpath hsol
    rw [encodeProtocol_successMass, encodeProtocol_conditionalDensity]
    exact h

end

end ManuscriptConformance
