import SparseLinearSystems.Separate.Bounds
import SparseLinearSystems.Separate.Registers
import SparseLinearSystems.Circuit.Step
import GeneralODE.Block.Standard

/-!
# Native circuits for the enlarged system, with separate matrix and preparation costs

Corollary `qls:cor:separate`, implementation. The physical workspace has one native register per
cell `((flag, branch), signal)` (`Cell w`). Its oracle family `sepOracle` consists of the three
original sparse primitives and the controlled preparation, with the labels and weights
`Step.wMat`, `Step.wSrc` of Theorem `qls:thm:main`. The paired logical workspace
`Paired n Z w` groups the two signal values of each `(flag, branch)`; it is encoded by `enc`.

* `D̃₀ = Cay D x` is the eighteen-call native Cayley circuit `NativeCayleyProgram.program D 1`;
  on the clean encoding it is the Cayley transform `D₀` of the edge generator (`cay_clean`).
* `UB D x = lcu (R̃ D̃₀)` is an exact block encoding of the enlarged matrix `B = (I - W)/2` with
  normalisation one, for the public encoding `sysEnc D = |0⟩ ⊗ clean` (`UB_block`).
* `PB D Ub x = Φ U_b` maps the public seed `|0⟩ ⊗ nEmb sv` to `sysEnc D (J (b, 0))` (`PB_seed`);
  `Φ` is a fixed unitary extension of `nEmb u ↦ clean (J (u, 0))`, independent of the instance.
* `circLcu D Ub w G hG mh` implements `lcu (G D̃₀)` on the pairs selected by `mh`, with 54 matrix
  calls and no preparation call (`circLcu_apply`, `circLcu_cost_mat`, `circLcu_cost_src`);
  `circP` implements `PB` with one preparation call and no matrix call (`circP_apply`,
  `circP_cost_mat`, `circP_cost_src`). Inverse and controlled forms come from the program model
  and the masks; public gates make no query.
-/

set_option autoImplicit false

namespace SparseLinearSystems.Separate

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit
open scoped InnerProduct
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8192

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n
local notation "Vsys" => SparseEdgeMoments.OrientedSpace n

/-! ### Registers and the physical oracle family -/

/-- The native register. -/
abbrev Reg (n Z : Type*) [Fintype n] [Fintype Z] := EuclideanSpace ℂ (Source.Bas n Z)

/-- Cells of the physical workspace: flag, solver branch and signal qubit. -/
abbrev Cell (w : ℕ) := (Bool × Fin w) × Bool

/-- The physical workspace. -/
abbrev Phys (n Z : Type*) [Fintype n] [Fintype Z] (w : ℕ) :=
  NativeMaskedOracle.Physical (Cell w) (Source.Bas n Z)

/-- The logical workspace: one native register per cell. -/
abbrev Logi (n Z : Type*) [Fintype n] [Fintype Z] (w : ℕ) :=
  NativeMaskedOracle.Logical (Cell w) (Source.Bas n Z)

/-- The paired logical workspace: one signal pair of native registers per `(flag, branch)`. -/
abbrev Paired (n Z : Type*) [Fintype n] [Fintype Z] (w : ℕ) :=
  PiLp 2 (fun _ : Bool × Fin w => Pair (Reg n Z))

/-- **The physical oracle family**: the three original sparse primitives and the controlled
preparation, in every cell. -/
def sepOracle (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (w : ℕ) :
    Step.Lbl → X → Phys n Z w →L[ℂ] Phys n Z w :=
  Sum.elim (NativeMaskedProgram.oracle (ι := Cell w) (NativeCayleyProgram.oracle D))
    (fun _ => Source.sourceOracle (ι := Cell w) (Z := Z) Ub)

omit [DecidableEq Z] in
theorem sepOracle_unitary (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (w : ℕ) : ∀ l x, IsUnitary (sepOracle D Ub w l x) := by
  intro l x
  cases l with
  | inl l => exact NativeMaskedOracle.oracle_unitary _ (NativeCayleyProgram.oracle_unitary D l) x
  | inr _ => exact Source.sourceOracle_unitary Ub hUb x

/-- The clean encoding of the paired workspace: regroup the cells, then append the clean control,
dummy and reference registers. It depends only on public data. -/
def enc (D : NativeSparseBlockEncoding.Data X n Z s) (w : ℕ) : Paired n Z w →L[ℂ] Phys n Z w :=
  (NativeMaskedOracle.input (ι := Cell w)
    (NativeCayleyProgram.cleanBasis D)).toContinuousLinearMap ∘L
    (prodCurry.symm : Paired n Z w ≃ₗᵢ[ℂ] Logi n Z w).toLinearIsometry.toContinuousLinearMap

theorem enc_apply (D : NativeSparseBlockEncoding.Data X n Z s) (w : ℕ) (g : Paired n Z w) :
    enc D w g = NativeMaskedOracle.input (ι := Cell w) (NativeCayleyProgram.cleanBasis D)
      (prodCurry.symm g : Logi n Z w) := rfl

theorem norm_enc (D : NativeSparseBlockEncoding.Data X n Z s) (w : ℕ) (g : Paired n Z w) :
    ‖enc D w g‖ = ‖g‖ := by
  rw [enc_apply, LinearIsometry.norm_map, LinearIsometryEquiv.norm_map]

theorem enc_isometry (D : NativeSparseBlockEncoding.Data X n Z s) (w : ℕ) :
    (enc D w)† ∘L enc D w = 1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp (norm_enc D w)

/-! ### Letters: public gates, masked Cayley circuits and masked preparation calls -/

/-- The native Cayley circuit `D̃₀`: six row, six column and six value calls. -/
abbrev cayProg (D : NativeSparseBlockEncoding.Data X n Z s) :
    MultiOracleCircuit.Program (NativeCayleyProgram.oracle D) :=
  NativeCayleyProgram.program D 1

/-- `D̃₀` on the native register. -/
abbrev Cay (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) : Reg n Z →L[ℂ] Reg n Z :=
  (cayProg D).eval x

/-- A public gate of the paired workspace, lifted to the physical workspace. -/
def fixL (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (w : ℕ)
    (Q : Paired n Z w →L[ℂ] Paired n Z w) (hQ : IsUnitary Q) :
    MultiOracleCircuit.Program (sepOracle D Ub w) :=
  .fixed (SubspaceOracle.lift (enc D w) Q) (SubspaceOracle.lift_unitary _ (enc_isometry D w) Q hQ)

theorem fixL_apply (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (w : ℕ)
    (Q : Paired n Z w →L[ℂ] Paired n Z w) (hQ : IsUnitary Q) (x : X) (g : Paired n Z w) :
    (fixL D Ub w Q hQ).eval x (enc D w g) = enc D w (Q g) := by
  have h := EncodedOracle.lift_comp (enc D w) (enc_isometry D w) Q
  exact congrArg (fun A : Paired n Z w →L[ℂ] Phys n Z w => A g) h

/-- Native programs in the physical vocabulary. -/
def inlP (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (w : ℕ) :
    MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := Cell w)
      (NativeCayleyProgram.oracle D)) → MultiOracleCircuit.Program (sepOracle D Ub w)
  | .fixed U hU => .fixed U hU
  | .query l => .query (.inl l)
  | .queryAdjoint l => .queryAdjoint (.inl l)
  | .seq p q => .seq (inlP D Ub w p) (inlP D Ub w q)

omit [DecidableEq Z] in
theorem inlP_eval (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (w : ℕ)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := Cell w)
      (NativeCayleyProgram.oracle D))) (x : X) : (inlP D Ub w p).eval x = p.eval x := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [inlP, MultiOracleCircuit.Program.eval_seq, hp, hq]

omit [DecidableEq Z] in
theorem inlP_cost (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (w : ℕ)
    (p : MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := Cell w)
      (NativeCayleyProgram.oracle D))) (wt : Step.Lbl → ℕ) :
    (inlP D Ub w p).cost wt = p.cost (fun l => wt (.inl l)) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [inlP, MultiOracleCircuit.Program.cost_seq, hp, hq]

/-- Preparation programs in the physical vocabulary. -/
def inrP (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (w : ℕ) :
    OracleCircuit.Program (Source.sourceOracle (ι := Cell w) (Z := Z) Ub) →
      MultiOracleCircuit.Program (sepOracle D Ub w)
  | .fixed U hU => .fixed U hU
  | .query => .query (.inr ())
  | .queryAdjoint => .queryAdjoint (.inr ())
  | .seq p q => .seq (inrP D Ub w p) (inrP D Ub w q)

omit [DecidableEq Z] in
theorem inrP_eval (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (w : ℕ)
    (p : OracleCircuit.Program (Source.sourceOracle (ι := Cell w) (Z := Z) Ub)) (x : X) :
    (inrP D Ub w p).eval x = p.eval x := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => rfl
  | seq p q hp hq =>
    simp only [inrP, MultiOracleCircuit.Program.eval_seq, OracleCircuit.Program.eval_seq, hp, hq]

omit [DecidableEq Z] in
theorem inrP_cost (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (w : ℕ)
    (p : OracleCircuit.Program (Source.sourceOracle (ι := Cell w) (Z := Z) Ub))
    (wt : Step.Lbl → ℕ) : (inrP D Ub w p).cost wt = p.count * wt (.inr ()) := by
  induction p with
  | fixed U hU => simp [inrP]
  | query => simp [inrP]
  | queryAdjoint => simp [inrP]
  | seq p q hp hq =>
    simp only [inrP, MultiOracleCircuit.Program.cost_seq, OracleCircuit.Program.count_seq, hp,
      hq, Nat.add_mul]

/-- The masked native Cayley circuit on the cells selected by `m`. -/
abbrev natProg (D : NativeSparseBlockEncoding.Data X n Z s) (w : ℕ) (m : Cell w → Bool) :
    MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := Cell w)
      (NativeCayleyProgram.oracle D)) :=
  NativeWholeProgramMask.program (NativeCayleyProgram.oracle D) (NativeCayleyProgram.cleanBasis D) m
    (cayProg D)

/-- `D̃₀` on the signal-`|1⟩` half of the pairs selected by `mh`. -/
def natL (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (w : ℕ)
    (mh : Bool × Fin w → Bool) : MultiOracleCircuit.Program (sepOracle D Ub w) :=
  inlP D Ub w (natProg D w (fun p : Cell w => mh p.1 && p.2))

theorem natProg_apply (D : NativeSparseBlockEncoding.Data X n Z s) (w : ℕ) (m : Cell w → Bool)
    (x : X) (y : Logi n Z w) :
    (natProg D w m).eval x
        ((NativeMaskedOracle.input (ι := Cell w) (NativeCayleyProgram.cleanBasis D)) y) =
      (NativeMaskedOracle.input (ι := Cell w) (NativeCayleyProgram.cleanBasis D))
        (MaskedProgram.masked m ((cayProg D).eval x) y) := by
  have h := NativeWholeProgramMask.program_intertwines (ι := Cell w) (NativeCayleyProgram.oracle D)
    (NativeCayleyProgram.oracle_unitary D) (NativeCayleyProgram.cleanBasis D)
    (NativeCayleyProgram.image D) (NativeCayleyProgram.valid D) m (cayProg D) x
  rw [← LinearIsometry.coe_toContinuousLinearMap, ← comp_apply, h, comp_apply]

theorem natL_apply (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (w : ℕ)
    (mh : Bool × Fin w → Bool) (x : X) (g : Paired n Z w) :
    (natL D Ub w mh).eval x (enc D w g) =
      enc D w (MaskedProgram.masked mh (MaskedProgram.masked (fun c : Bool => c) (Cay D x)) g) := by
  rw [natL, inlP_eval, enc_apply, enc_apply, natProg_apply,
    prodCurry_masked mh (fun c : Bool => c) (Cay D x) g]

theorem natL_cost (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (w : ℕ)
    (mh : Bool × Fin w → Bool) (wt : Step.Lbl → ℕ) :
    (natL D Ub w mh).cost wt =
      3 * (6 * wt (.inl .rowLocation) + 6 * wt (.inl .columnLocation) + 6 * wt (.inl .value)) := by
  rw [natL, inlP_cost, natProg, NativeWholeProgramMask.program_cost,
    NativeCayleyProgram.program_cost]

/-- One masked preparation call on both signal halves of the pairs selected by `mh`. -/
def srcL (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (w : ℕ)
    (mh : Bool × Fin w → Bool) : MultiOracleCircuit.Program (sepOracle D Ub w) :=
  inrP D Ub w (Source.sourceProgram (ι := Cell w) (Z := Z) Ub (fun p : Cell w => mh p.1 && true))

theorem srcProg_apply (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (w : ℕ) (m : Cell w → Bool) (x : X) (y : Logi n Z w) :
    (Source.sourceProgram (ι := Cell w) (Z := Z) Ub m).eval x
        ((NativeMaskedOracle.input (ι := Cell w) (NativeCayleyProgram.cleanBasis D)) y) =
      (NativeMaskedOracle.input (ι := Cell w) (NativeCayleyProgram.cleanBasis D))
        (MaskedProgram.masked m (Source.srcU (Z := Z) (Ub x)) y) := by
  have h := Source.sourceProgram_intertwines (ι := Cell w) (Z := Z) Ub
    (NativeCayleyProgram.cleanBasis D) m x
  rw [← LinearIsometry.coe_toContinuousLinearMap, ← comp_apply, h, comp_apply]

theorem srcL_apply (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (w : ℕ)
    (mh : Bool × Fin w → Bool) (x : X) (g : Paired n Z w) :
    (srcL D Ub w mh).eval x (enc D w g) =
      enc D w (MaskedProgram.masked mh
        (MaskedProgram.masked (fun _ : Bool => true) (Source.srcU (Z := Z) (Ub x))) g) := by
  rw [srcL, inrP_eval, enc_apply, enc_apply, srcProg_apply,
    prodCurry_masked mh (fun _ : Bool => true) (Source.srcU (Z := Z) (Ub x)) g]

omit [DecidableEq Z] in
theorem srcL_cost (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (w : ℕ)
    (mh : Bool × Fin w → Bool) (wt : Step.Lbl → ℕ) : (srcL D Ub w mh).cost wt = wt (.inr ()) := by
  rw [srcL, inrP_cost, Source.sourceProgram_count, one_mul]

/-! ### The native Cayley circuit, the reflection and the walk -/

/-- The fixed clean embedding of the edge space. -/
abbrev cl (D : NativeSparseBlockEncoding.Data X n Z s) : Vsys →L[ℂ] Reg n Z :=
  (NativeCayleyProgram.clean D).toContinuousLinearMap

theorem cl_isometry (D : NativeSparseBlockEncoding.Data X n Z s) : (cl D)† ∘L cl D = 1 :=
  NativeCayleyProgram.clean_isometry D

theorem cl_adjoint_cl (D : NativeSparseBlockEncoding.Data X n Z s) (v : Vsys) :
    ((cl D)†) (cl D v) = v :=
  congrArg (fun A : Vsys →L[ℂ] Vsys => A v) (cl_isometry D)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem bdry_isometry (D : NativeSparseBlockEncoding.Data X n Z s) :
    ((bdry D)†) ∘L bdry D = 1 :=
  SplitBoundary.fixedSplit_isometry D.slot D.slots_pos

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem reflection_unitary (D : NativeSparseBlockEncoding.Data X n Z s) :
    IsUnitary (WalkGap.reflection (bdry D)) := by
  have hs : star (WalkGap.reflection (bdry D)) = WalkGap.reflection (bdry D) := by
    rw [star_eq_adjoint, WalkGap.reflection_adjoint]
  have hm := WalkGap.reflection_mul_self _ (bdry_isometry D)
  exact ⟨by rw [hs, hm], by rw [hs, hm]⟩

/-- The public boundary reflection `R = I - 2 J J†` on the native register. -/
def reflNat (D : NativeSparseBlockEncoding.Data X n Z s) : Reg n Z →L[ℂ] Reg n Z :=
  SubspaceOracle.lift (cl D) (WalkGap.reflection (bdry D))

theorem reflNat_unitary (D : NativeSparseBlockEncoding.Data X n Z s) : IsUnitary (reflNat D) :=
  SubspaceOracle.lift_unitary _ (cl_isometry D) _ (reflection_unitary D)

theorem reflNat_clean (D : NativeSparseBlockEncoding.Data X n Z s) (v : Vsys) :
    reflNat D (cl D v) = cl D (WalkGap.reflection (bdry D) v) :=
  congrArg (fun A : Vsys →L[ℂ] Reg n Z => A v)
    (EncodedOracle.lift_comp _ (cl_isometry D) (WalkGap.reflection (bdry D)))

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem generator_adjoint (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    (FixedNativeCayleySimulation.generator D x)† = FixedNativeCayleySimulation.generator D x := by
  rw [← star_eq_adjoint]
  exact FixedNativeCayleySimulation.generator_self_adjoint D x

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The concrete Cayley action at scale one is the Hilbert-space Cayley transform: the concrete
and the constructed inverses of `K - i` agree. -/
theorem action_one (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    FixedNativeCayleySimulation.action D x 1 =
      HilbertCayley.cayley (FixedNativeCayleySimulation.generator D x) (generator_adjoint D x) := by
  set K := FixedNativeCayleySimulation.generator D x
  have hs : CayleyClockInterface.scaled K 1 = K := by
    rw [CayleyClockInterface.scaled, Complex.ofReal_one, one_smul]
  have h1 := FixedNativeCayleySimulation.inverse_left D x 1
  rw [hs] at h1
  have h2 := HilbertCayley.denominator_mul_inverse K (generator_adjoint D x)
  have hinv : FixedNativeCayleySimulation.inverse D x 1 =
      HilbertCayley.denominatorInverse K (generator_adjoint D x) := by
    calc FixedNativeCayleySimulation.inverse D x 1
        = FixedNativeCayleySimulation.inverse D x 1 *
            (HilbertCayley.denominator K * HilbertCayley.denominatorInverse K
              (generator_adjoint D x)) := by rw [h2, mul_one]
      _ = (FixedNativeCayleySimulation.inverse D x 1 * HilbertCayley.denominator K) *
            HilbertCayley.denominatorInverse K (generator_adjoint D x) := (mul_assoc _ _ _).symm
      _ = _ := by rw [HilbertCayley.denominator, h1, one_mul]
  rw [FixedNativeCayleySimulation.action_eq_cayley, hs, hinv, HilbertCayley.cayley,
    ImprovedCayleyMoments.cayleyAction, Cayley.cayleyAction]

/-- The native Cayley circuit implements the Cayley transform on the clean encoding. -/
theorem cay_clean (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (v : Vsys) :
    Cay D x (cl D v) =
      cl D (HilbertCayley.cayley (FixedNativeCayleySimulation.generator D x)
        (generator_adjoint D x) v) := by
  have h := NativeCayleyProgram.program_intertwines D 1 x
  rw [action_one] at h
  rw [← comp_apply, h, comp_apply]

theorem cay_unitary (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) : IsUnitary (Cay D x) :=
  NativeCayleyProgram.program_unitary D 1 x

/-- The native walk `W̃ = R̃ D̃₀`. -/
def walkNat (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) : Reg n Z →L[ℂ] Reg n Z :=
  reflNat D * Cay D x

theorem walkNat_clean (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (v : Vsys) :
    walkNat D x (cl D v) =
      cl D (WalkGap.walk (bdry D) (HilbertCayley.cayley (FixedNativeCayleySimulation.generator D x)
        (generator_adjoint D x)) v) := by
  rw [walkNat, mul_apply_eq_comp, cay_clean, reflNat_clean, WalkGap.walk, mul_apply_eq_comp]

/-! ### The block encoding of `B` and the preparation of `J (b, 0)` -/

/-- **The exact block encoding of the enlarged matrix**: `U_B = lcu W̃`. -/
def UB (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    Pair (Reg n Z) →L[ℂ] Pair (Reg n Z) :=
  lcu (walkNat D x)

theorem UB_unitary (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) : IsUnitary (UB D x) :=
  lcu_unitary ((reflNat_unitary D).mul (cay_unitary D x))

/-- The public system encoding `v ↦ |0⟩ ⊗ clean v`. -/
def sysEnc (D : NativeSparseBlockEncoding.Data X n Z s) : Vsys →L[ℂ] Pair (Reg n Z) :=
  cellIn false ∘L cl D

theorem sysEnc_adjoint_apply (D : NativeSparseBlockEncoding.Data X n Z s) (g : Pair (Reg n Z)) :
    ((sysEnc D)†) g = ((cl D)†) (g false) := by
  rw [sysEnc, adjoint_comp, comp_apply, cellIn_adjoint, cellOut_apply]

theorem norm_sysEnc (D : NativeSparseBlockEncoding.Data X n Z s) (v : Vsys) :
    ‖sysEnc D v‖ = ‖v‖ := by
  rw [sysEnc, comp_apply, norm_cellIn, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map]

theorem sysEnc_isometry (D : NativeSparseBlockEncoding.Data X n Z s) :
    (sysEnc D)† ∘L sysEnc D = 1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp (norm_sysEnc D)

/-- **The selected block of `U_B` is `B`**, on the whole logical edge space. -/
theorem UB_block (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1) :
    (sysEnc D)† ∘L UB D x ∘L sysEnc D = enlarged (hyp D x hA1) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [comp_apply, comp_apply, enlarged_apply, sysEnc_adjoint_apply, sysEnc, comp_apply, UB,
    lcu_cellIn_false, walkNat_clean, map_smul, map_sub, cl_adjoint_cl, cl_adjoint_cl]

/-- The dilated right-hand side `u ↦ (u, 0)` as a continuous linear map. -/
def rhsL : V0 →L[ℂ] HilbertRegularization.Double V0 :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ V0 V0).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inl ℂ V0 V0

omit [Fintype n] [DecidableEq n] in
theorem rhsL_apply (u : V0) : rhsL u = rhs u := rfl

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem norm_bdry (D : NativeSparseBlockEncoding.Data X n Z s)
    (v : HilbertRegularization.Double V0) :
    ‖bdry D v‖ = ‖v‖ :=
  WalkGap.isometry_norm (bdry_isometry D) v

/-- A fixed unitary `Φ` with `Φ (nEmb a u) = clean (J (u, 0))`, `a` the clean basis state. It is
an extension of an isometry built from public data only. -/
theorem exists_prepGate (D : NativeSparseBlockEncoding.Data X n Z s) :
    ∃ Φ : Reg n Z →L[ℂ] Reg n Z, IsUnitary Φ ∧
      Φ ∘L (Source.nEmb (Z := Z) (NativeCayleyProgram.cleanBasis D)).toContinuousLinearMap =
        cl D ∘L bdry D ∘L rhsL := by
  apply GeneralODE.Registers.exists_unitary_comp
  · exact (Source.nEmb (Z := Z) (NativeCayleyProgram.cleanBasis D)).adjoint_comp_self
  · apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp
    intro u
    rw [comp_apply, comp_apply, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map,
      norm_bdry, rhsL_apply, norm_rhs]

/-- The public preparation gate `Φ`. -/
def prepGate (D : NativeSparseBlockEncoding.Data X n Z s) : Reg n Z →L[ℂ] Reg n Z :=
  Classical.choose (exists_prepGate D)

theorem prepGate_unitary (D : NativeSparseBlockEncoding.Data X n Z s) :
    IsUnitary (prepGate D) :=
  (Classical.choose_spec (exists_prepGate D)).1

theorem prepGate_nEmb (D : NativeSparseBlockEncoding.Data X n Z s) (u : V0) :
    prepGate D (Source.nEmb (Z := Z) (NativeCayleyProgram.cleanBasis D) u) =
      cl D (bdry D (rhs u)) :=
  congrArg (fun A : V0 →L[ℂ] Reg n Z => A u) (Classical.choose_spec (exists_prepGate D)).2

/-- **The preparation** `P_b = Φ U_b` on both signal halves. -/
def PB (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (x : X) :
    Pair (Reg n Z) →L[ℂ] Pair (Reg n Z) :=
  MaskedProgram.masked (fun _ : Bool => true) (prepGate D * Source.srcU (Z := Z) (Ub x))

theorem PB_unitary (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (x : X)
    (hU : IsUnitary (Ub x)) : IsUnitary (PB D Ub x) :=
  MaskedProgram.masked_unitary _ _ ((prepGate_unitary D).mul (Source.srcU_unitary _ hU))

/-- The public seed `|0⟩ ⊗ nEmb sv`. -/
def seedVec (D : NativeSparseBlockEncoding.Data X n Z s) (sv : V0) : Pair (Reg n Z) :=
  cellIn false (Source.nEmb (Z := Z) (NativeCayleyProgram.cleanBasis D) sv)

theorem norm_seedVec (D : NativeSparseBlockEncoding.Data X n Z s) (sv : V0) :
    ‖seedVec D sv‖ = ‖sv‖ := by
  rw [seedVec, norm_cellIn, LinearIsometry.norm_map]

/-- **The preparation of the enlarged right-hand side**: `P_b r₀ = sysEnc (J (b, 0))`. -/
theorem PB_seed (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (x : X)
    (sv : V0) : PB D Ub x (seedVec D sv) = sysEnc D (bdry D (rhs (Ub x sv))) := by
  apply PiLp.ext
  intro c
  cases c
  · simp only [PB, seedVec, sysEnc, MaskedProgram.masked_apply, cellIn_apply, if_true,
      mul_apply_eq_comp, comp_apply, Source.srcU_nEmb, prepGate_nEmb]
  · simp [PB, seedVec, sysEnc]

/-! ### The physical letters -/

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
/-- `lcu (G D̃₀)` on the pairs selected by `mh`, as a product of masks. -/
theorem masked_lcu_mul {w : ℕ} (mh : Bool × Fin w → Bool) (G C : Reg n Z →L[ℂ] Reg n Z) :
    MaskedProgram.masked mh (lcu (G * C)) =
      (MaskedProgram.masked mh had * MaskedProgram.masked mh
        (MaskedProgram.masked (fun c : Bool => c) (-G))) *
        MaskedProgram.masked mh (MaskedProgram.masked (fun c : Bool => c) C) *
          MaskedProgram.masked mh had := by
  rw [lcu, ← neg_mul, MaskedProgram.masked_mul (fun c : Bool => c) (-G) C]
  simp only [MaskedProgram.masked_mul, mul_assoc]

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem hadMask_unitary {w : ℕ} (mh : Bool × Fin w → Bool) :
    IsUnitary (MaskedProgram.masked mh (had : Pair (Reg n Z) →L[ℂ] Pair (Reg n Z))) :=
  MaskedProgram.masked_unitary _ _ had_unitary

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem lcuGate_unitary {w : ℕ} (mh : Bool × Fin w → Bool) {G : Reg n Z →L[ℂ] Reg n Z}
    (hG : IsUnitary G) :
    IsUnitary (MaskedProgram.masked mh (had : Pair (Reg n Z) →L[ℂ] Pair (Reg n Z)) *
      MaskedProgram.masked mh (MaskedProgram.masked (fun c : Bool => c) (-G))) :=
  (hadMask_unitary mh).mul
    (MaskedProgram.masked_unitary _ _ (MaskedProgram.masked_unitary _ _ (neg_unitary hG)))

/-- **`lcu (G D̃₀)` on the pairs selected by `mh`**: two public gates and one masked native
Cayley circuit. -/
def circLcu (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (w : ℕ)
    (G : Reg n Z →L[ℂ] Reg n Z) (hG : IsUnitary G) (mh : Bool × Fin w → Bool) :
    MultiOracleCircuit.Program (sepOracle D Ub w) :=
  .seq (fixL D Ub w _ (lcuGate_unitary mh hG))
    (.seq (natL D Ub w mh) (fixL D Ub w _ (hadMask_unitary mh)))

theorem circLcu_apply (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (w : ℕ) (G : Reg n Z →L[ℂ] Reg n Z) (hG : IsUnitary G) (mh : Bool × Fin w → Bool) (x : X)
    (g : Paired n Z w) :
    (circLcu D Ub w G hG mh).eval x (enc D w g) =
      enc D w (MaskedProgram.masked mh (lcu (G * Cay D x)) g) := by
  rw [masked_lcu_mul]
  simp only [circLcu, MultiOracleCircuit.Program.eval_seq, mul_apply_eq_comp, fixL_apply,
    natL_apply]

theorem circLcu_cost (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (w : ℕ) (G : Reg n Z →L[ℂ] Reg n Z) (hG : IsUnitary G) (mh : Bool × Fin w → Bool)
    (wt : Step.Lbl → ℕ) :
    (circLcu D Ub w G hG mh).cost wt =
      3 * (6 * wt (.inl .rowLocation) + 6 * wt (.inl .columnLocation) + 6 * wt (.inl .value)) := by
  simp only [circLcu, fixL, MultiOracleCircuit.Program.cost_seq,
    MultiOracleCircuit.Program.cost_fixed, natL_cost]
  omega

/-- **Matrix cost of an `lcu` letter**: 54 sparse primitive calls. -/
theorem circLcu_cost_mat (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (w : ℕ) (G : Reg n Z →L[ℂ] Reg n Z) (hG : IsUnitary G) (mh : Bool × Fin w → Bool) :
    (circLcu D Ub w G hG mh).cost Step.wMat = 54 := by
  rw [circLcu_cost]; rfl

/-- **Preparation cost of an `lcu` letter**: none. -/
theorem circLcu_cost_src (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (w : ℕ) (G : Reg n Z →L[ℂ] Reg n Z) (hG : IsUnitary G) (mh : Bool × Fin w → Bool) :
    (circLcu D Ub w G hG mh).cost Step.wSrc = 0 := by
  rw [circLcu_cost]; rfl

/-- **`P_b` on the pairs selected by `mh`**: one masked preparation call and a public gate. -/
def circP (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (w : ℕ)
    (mh : Bool × Fin w → Bool) : MultiOracleCircuit.Program (sepOracle D Ub w) :=
  .seq (fixL D Ub w (MaskedProgram.masked mh (MaskedProgram.masked (fun _ : Bool => true)
      (prepGate D)))
      (MaskedProgram.masked_unitary _ _ (MaskedProgram.masked_unitary _ _ (prepGate_unitary D))))
    (srcL D Ub w mh)

theorem circP_apply (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (w : ℕ) (mh : Bool × Fin w → Bool) (x : X) (g : Paired n Z w) :
    (circP D Ub w mh).eval x (enc D w g) = enc D w (MaskedProgram.masked mh (PB D Ub x) g) := by
  rw [PB, MaskedProgram.masked_mul, MaskedProgram.masked_mul]
  simp only [circP, MultiOracleCircuit.Program.eval_seq, mul_apply_eq_comp, fixL_apply,
    srcL_apply]

theorem circP_cost (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (w : ℕ)
    (mh : Bool × Fin w → Bool) (wt : Step.Lbl → ℕ) : (circP D Ub w mh).cost wt = wt (.inr ()) := by
  simp only [circP, fixL, MultiOracleCircuit.Program.cost_seq,
    MultiOracleCircuit.Program.cost_fixed, srcL_cost, zero_add]

/-- **Matrix cost of a preparation letter**: none. -/
theorem circP_cost_mat (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (w : ℕ) (mh : Bool × Fin w → Bool) : (circP D Ub w mh).cost Step.wMat = 0 := by
  rw [circP_cost]; rfl

/-- **Preparation cost of a preparation letter**: one call. -/
theorem circP_cost_src (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (w : ℕ) (mh : Bool × Fin w → Bool) : (circP D Ub w mh).cost Step.wSrc = 1 := by
  rw [circP_cost]; rfl

end

end SparseLinearSystems.Separate
