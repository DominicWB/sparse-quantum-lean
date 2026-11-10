import DysonFullClass.Single
import CleanWorkODE.Oracles
import GeneralSourceExtensions.Approx.Pullback

set_option autoImplicit false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 8192

/-!
# Lemma `odel:lem:dyson` on the full class with approximate source preparations

Theorem `ode:thm:time` allows the supplied `P_w` and `U_load` to use temporary work registers and
to be accurate only on clean inputs (`ManuscriptConformance.ode_thm_time_approx`,
`CleanWorkODE`). Here the Dyson comparison algorithm of `Theorem.full_dyson_shape` is run with
these supplied operations:

* `FSpaceW`, `fullActualOracleW`: the full-class workspace with a temporary work register `W`
  adjoined to the source register; the masked native calls with the work register as a spectator,
  and the supplied `P_w ⊗ 1`, `U_load ⊗ 1`, `P_w† ⊗ 1` with their supported enable control;
* `fullActualOracleW_clean`: if the supplied `P_w(x)` and `U_load(x)` are within `δ` of exact
  preparations `P` and `∑_a |a⟩⟨a| ⊗ L(a)` on a clean work register (`CleanWorkODE.CleanErr`,
  the clean-input operator norm, coherently over the source labels), every primitive implements
  the exact primitive of `Single.fullActualOracle` within `δ` (exactly on matrix labels) on a
  clean work register;
* `full_approx`: one public trial family over `fullActualOracleW D₀`, fixed before the instance,
  such that for every input `x`, all exact unitary preparations `P`, `L` within `δ` of the
  supplied ones with `30 g' δ ≤ 1/400` and `30 g' δ ≤ ε/20` (`g' = c_q ḡ e^z`, so
  `δ = O(ε/(c_q ḡ e^z))`, the order of the manuscript's `ξ ≤ e^{-z} δ` with its propagator budget
  `δ = ε/[16(1 + c_q) ḡ]` in the proof of Lemma `odel:lem:dyson`; the `δ` here is the clean-input
  error of each supplied preparation, while `ξ` bounds the error of the selected vector), and every
  valid instance `FullValidAt` for `P`, `L`, four fresh trials heralded on a clean work register
  satisfy `ApproxCertificate`: success at least `2/3`, conditional trace distance at most `ε`,
  worst-case `2160 g' K` matrix queries and at most `40 g'` calls of each supplied operation.

The perturbation is tracked through the whole amplified protocol: the actual preparation and its
actual inverse are amplified about the public seed and herald (no reflection about an unknown
ideal state), and each of the at most `30 g'` source calls of a trial moves the clean-input state
by at most `δ` (`CleanWorkODE.work_certificate`).
-/

namespace DysonFullClass

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set
open MeasureTheory TimeDependentExtensions
open SparseHamiltonian.GeneralSourceODE (sources phases phases_norm SourceCall)
open SparseHamiltonian.CleanWorkODE (LabelW LoadW CleanErr cleanPi ctrlL liftPi liftAct sourceOpW
  labelSplit loadSplit piWork workRecast)
open SparseHamiltonian.GeneralSourceExtensions (pullback Inst ApproxCertificate)
open ODELowerBoundExtensions.Dyson
open scoped InnerProduct BigOperators

variable {X Y n Z W : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] [Fintype W] [DecidableEq W] {s Ks M m : ℕ}

/-- The full-class workspace with a temporary work register `W` adjoined to the source
register. -/
abbrev FSpaceW (Ks : ℕ) (n Z W : Type) [Fintype n] [Fintype Z] [Fintype W] (K M m : ℕ) : Type :=
  ODESectorTensor.Physical (GeneralSourceODE.Native.SourceBasis (FIota K M) n m × W)
    (OmegaG (FLab K M m) K × NativeControlledOracle.Workspace (PBasis Ks n Z))

/-- **The actual primitives with a temporary work register**: the masked native calls of `D` with
the work register as a spectator, and the supplied `P_w ⊗ 1` (label and work registers),
`U_load ⊗ 1` (label, data and work registers) and `P_w† ⊗ 1`, with their supported enable
control. -/
def fullActualOracleW (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → LabelW m W →L[ℂ] LabelW m W) (J : X → LoadW m n W →L[ℂ] LoadW m n W) :
    Query ⊕ SourceCall → X → FSpaceW Ks n Z W K M m →L[ℂ] FSpaceW Ks n Z W K M m :=
  Sum.elim
    (fun l x => liftPi (fullActualOracle D K M m (fun _ => 1) (fun _ _ => 1) (Sum.inl l) x))
    (fun k x => ODESectorTensor.sourcePhysical
      (A := GeneralSourceODE.Native.SourceBasis (FIota K M) n m × W)
      (B := OmegaG (FLab K M m) K × NativeControlledOracle.Workspace (PBasis Ks n Z))
      (sourceOpW (ι := FIota K M) Pw J k x))

omit [DecidableEq Z] [DecidableEq W] in
theorem fullActualOracleW_unitary (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    {Pw : X → LabelW m W →L[ℂ] LabelW m W} (hPw : ∀ x, IsUnitary (Pw x))
    {J : X → LoadW m n W →L[ℂ] LoadW m n W} (hJ : ∀ x, IsUnitary (J x)) :
    ∀ l x, IsUnitary (fullActualOracleW D K M m Pw J l x) := by
  intro l x
  cases l with
  | inl l =>
      exact CleanWorkODE.liftPi_unitary (fullActualOracle_unitary D K M m
        (fun _ => isUnitary_one) (fun _ _ => isUnitary_one) (Sum.inl l) x)
  | inr k =>
      exact ODESectorTensor.sourcePhysical_unitary _
        (CleanWorkODE.sourceOpW_unitary hPw hJ k x)

omit [DecidableEq Z] in
/-- On the matrix labels the primitives of the data read through `f` at `y` are those of the
original data at `f y`. -/
theorem fullActualOracle_pullback_matrix (D : Data (X × Fin Ks) n Z s) (f : Y → X) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Pw' : Y → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J' : Y → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (l : Query) (y : Y) :
    fullActualOracle D K M m Pw J (Sum.inl l) (f y) =
      fullActualOracle (pullback D f) K M m Pw' J' (Sum.inl l) y := by
  cases l <;> rfl

omit [DecidableEq Z] in
set_option maxHeartbeats 4000000 in
/-- **The primitives keep the clean-input errors of the supplied operations.** If the matrix
primitives agree and the supplied `P_w` and `U_load` are within `δ` of `P` and
`∑_a |a⟩⟨a| ⊗ L(a)` on a clean work register, every primitive with the work register implements
the exact primitive of `fullActualOracle` for `P`, `L` within `δ` on the three source labels, and
exactly on the matrix labels, on a clean work register. -/
theorem fullActualOracleW_clean (D : Data (X × Fin Ks) n Z s) (D' : Data (Y × Fin Ks) n Z s)
    (K M m : ℕ) (w₀ : W) (Pw : X → LabelW m W →L[ℂ] LabelW m W)
    (J : X → LoadW m n W →L[ℂ] LoadW m n W) (Pw' : Y → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J' : Y → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (x : X) (y : Y)
    (hmat : ∀ l, fullActualOracle D K M m (fun _ => 1) (fun _ _ => 1) (Sum.inl l) x =
      fullActualOracle D' K M m Pw' J' (Sum.inl l) y)
    (hPw : IsUnitary (Pw x)) (hP : IsUnitary (Pw' y)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hPc : CleanErr (cleanPi (V := ℂ) w₀) (Pw x) (Pw' y) δ)
    (hJc : CleanErr (cleanPi (V := ℂ) w₀) (J x) (ctrlL (J' y)) δ) :
    ∀ l, CleanErr (cleanPi w₀) (fullActualOracleW D K M m Pw J l x)
      (fullActualOracle D' K M m Pw' J' l y)
      (δ * GeneralSourceODE.Oracles.sourceCalls l) := by
  rintro (l | k)
  · have h0 := CleanErr.of_comp (CleanWorkODE.liftPi_clean w₀
      (fullActualOracle D K M m (fun _ => 1) (fun _ _ => 1) (Sum.inl l) x))
    have e : δ * (GeneralSourceODE.Oracles.sourceCalls
        (Sum.inl l : Query ⊕ SourceCall) : ℝ) = 0 := by
      simp [GeneralSourceODE.Oracles.sourceCalls]
    rw [e]
    change CleanErr (cleanPi w₀)
      (liftPi (fullActualOracle D K M m (fun _ => 1) (fun _ _ => 1) (Sum.inl l) x))
      (fullActualOracle D' K M m Pw' J' (Sum.inl l) y) 0
    rw [← hmat l]
    exact h0
  · have e : δ * (GeneralSourceODE.Oracles.sourceCalls
        (Sum.inr k : Query ⊕ SourceCall) : ℝ) = δ := by
      simp [GeneralSourceODE.Oracles.sourceCalls]
    rw [e]
    change CleanErr (cleanPi w₀)
      (ODESectorTensor.sourcePhysical
        (A := GeneralSourceODE.Native.SourceBasis (FIota K M) n m × W)
        (B := OmegaG (FLab K M m) K × NativeControlledOracle.Workspace (PBasis Ks n Z))
        (sourceOpW (ι := FIota K M) Pw J k x))
      (ODESectorTensor.sourcePhysical
        (B := OmegaG (FLab K M m) K × NativeControlledOracle.Workspace (PBasis Ks n Z))
        ((GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m).conjStarAlgEquiv
          (GeneralSourceODE.Oracles.sourceOperation (ι := FIota K M) Pw' J' k y))) δ
    cases k with
    | weight =>
        exact CleanWorkODE.sourcePhysical_clean w₀ _ _ hδ
          (CleanWorkODE.liftAct_clean w₀ labelSplit (Pw x) (Pw' y)
            ((GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m).conjStarAlgEquiv
              (GeneralSourceODE.Weights.act (Pw' y)))
            (CleanWorkODE.slice_act (Pw' y)) hδ hPc)
    | load =>
        exact CleanWorkODE.sourcePhysical_clean w₀ _ _ hδ
          (CleanWorkODE.liftAct_clean w₀ loadSplit (J x) (ctrlL (J' y))
            ((GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m).conjStarAlgEquiv
              (GeneralSourceODE.Weights.loader (J' y)))
            (CleanWorkODE.slice_loader (J' y)) hδ hJc)
    | unweight =>
        exact CleanWorkODE.sourcePhysical_clean w₀ _ _ hδ
          (CleanWorkODE.liftAct_clean w₀ labelSplit (star (Pw x)) (star (Pw' y))
            ((GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m).conjStarAlgEquiv
              (GeneralSourceODE.Weights.act (star (Pw' y))))
            (CleanWorkODE.slice_act (star (Pw' y))) hδ (hPc.adjoint hPw hP))

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- A valid instance has a nonzero target. -/
theorem FullValidAt.target_ne_zero {D₀ : Data (X × Fin Ks) n Z s} {σ : Fin M → Fin Ks}
    {t : ℕ → ℝ} {T η g cq ε : ℝ} {hη : 0 < η} {v : Fin m → ℝ} {ω : Fin m → ℂ}
    {P : GeneralSourceODE.Weights.LabelOp (Option (Fin m))}
    {L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n}
    {seed : EuclideanSpace ℂ n} {x : X} {y : EuclideanSpace ℂ n}
    (h : FullValidAt D₀ σ t T η g cq ε hη v ω P L seed x y) : y ≠ 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsol, _, _, rfl⟩ := h
  exact hsol

set_option maxHeartbeats 8000000 in
/-- **Lemma `odel:lem:dyson` on the full time-dependent class with approximate source
preparations on temporary work registers.** For every public specification (as in
`Theorem.full_dyson`, with a work register `W`, clean work state `w₀` and supplied unitaries
`P_w(x)` on the label and work registers and `U_load(x)` on the label, data and work registers)
there is one public trial family over `fullActualOracleW D₀` with `chosenIterations g'` choices,
`g' = c_q ḡ e^z`, such that for every input `x`, all exact unitary preparations `P`, `L` within
`δ` of the supplied ones on a clean work register, `30 g' δ ≤ 1/400`, `30 g' δ ≤ ε/20`, and every
valid instance `FullValidAt D₀ … P L seed x y`, four fresh trials, heralded on the output flag
and a clean work register, satisfy `ApproxCertificate` (success at least `2/3`, conditional trace
distance at most `ε` after discarding the work registers, at most
`1274019840 g' queryShape s 0 (K/589824) = 2160 g' K` matrix queries and `40 g'` calls of each
supplied operation in every history). -/
theorem full_approx (D₀ : Data (X × Fin Ks) n Z s) (hM : 0 < M) (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T η g cq ε : ℝ) (hmesh : IsMesh t M T) (hT : 0 < T) (hη : 0 < η)
    (hg : 1 ≤ g) (hcq : 1 ≤ cq) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (v : Fin m → ℝ) (hv : ∀ i, v i ∈ Icc 0 T) (ω : Fin m → ℂ) (w₀ : W)
    (Pw : X → LabelW m W →L[ℂ] LabelW m W) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → LoadW m n W →L[ℂ] LoadW m n W) (hJ : ∀ x, IsUnitary (J x))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    ∃ tf : ODERepeatProtocol.TrialFamily
        (fullActualOracleW D₀ (fullDegree s η T g cq ε) M m Pw J) (EuclideanSpace ℂ n),
      tf.choices = ODEGroverAverage.chosenIterations (fullAmp s η T g cq) ∧
      (∀ j x, IsUnitary ((tf.circuit j).eval x)) ∧
      ∀ (x : X) (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
        (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (δ : ℝ)
        (y : EuclideanSpace ℂ n),
        IsUnitary P → (∀ a, IsUnitary (L a)) → 0 ≤ δ →
        CleanErr (cleanPi (V := ℂ) w₀) (Pw x) P δ →
        CleanErr (cleanPi (V := ℂ) w₀) (J x) (ctrlL L) δ →
        30 * fullAmp s η T g cq * δ ≤ 1 / 400 → 30 * fullAmp s η T g cq * δ ≤ ε / 20 →
        FullValidAt D₀ σ t T η g cq ε hη v ω P L seed x y →
        ApproxCertificate (ODERepeatProtocol.Protocol.repeatTrials tf 4) x y (s : ℝ) 0
          (fullShape (fullDegree s η T g cq ε)) (fullAmp s η T g cq) ε := by
  -- The exact family for the instances with exact preparations.
  obtain ⟨q, ψ, F, -, -, -, -, -, -, hψ, hF, -, hC⟩ := full_dyson_shape (X := Inst X n m)
    (pullback D₀ (Inst.input (X := X) (n := n) (m := m))) hM σ t T η g cq ε hmesh hT hη hg hcq
    hε hε1 v hv ω Inst.weight (Inst.weight_unitary (X := X) (n := n) (m := m)) Inst.loader
    (Inst.loader_unitary (X := X) (n := n) (m := m)) seed hSeed
  have hg1 := one_le_fullAmp (s := s) hη.le hT.le hg hcq
  obtain ⟨hMpos, -, -⟩ := ODEGroverAverage.chosenIterations_bounds (fullAmp s η T g cq) hg1
  -- The same family over the exact separate primitives of the instances.
  let q₁ := fullActualTrials (pullback D₀ (Inst.input (X := X) (n := n) (m := m)))
    (fullDegree s η T g cq ε) M m Inst.weight Inst.loader ω q
  have hO₁ := fullActualOracle_unitary (pullback D₀ (Inst.input (X := X) (n := n) (m := m)))
    (fullDegree s η T g cq ε) M m (Inst.weight_unitary (X := X) (n := n) (m := m))
    (Inst.loader_unitary (X := X) (n := n) (m := m))
  have hO₂ := fullActualOracleW_unitary D₀ (fullDegree s η T g cq ε) M m hPw hJ
  have hEval : ∀ j p, (q₁ j).eval p = (q j).eval p := fun j p =>
    MultiOracleCircuit.Program.eval_substitute (q j) _
      (fullImplementation_eval (pullback D₀ (Inst.input (X := X) (n := n) (m := m)))
        (fullDegree s η T g cq ε) M m Inst.weight Inst.loader ω) p
  have hCost : ∀ (w : Query ⊕ SourceCall → ℕ) (j : ℕ), (q₁ j).cost w = (q j).cost (fun l =>
      (fullImplementation (pullback D₀ (Inst.input (X := X) (n := n) (m := m)))
        (fullDegree s η T g cq ε) M m Inst.weight Inst.loader ω l).cost w) :=
    fun w j => MultiOracleCircuit.Program.cost_substitute (q j) _ w
  -- The same syntax, every fixed gate lifted to the work register, over the supplied primitives.
  let q₂ : ℕ → MultiOracleCircuit.Program (fullActualOracleW D₀ (fullDegree s η T g cq ε) M m Pw J) :=
    fun j => workRecast (piWork w₀) (q₁ j)
  refine ⟨ODERepeatProtocol.ofCircuits q₂
    (ODEGroverAverage.chosenIterations (fullAmp s η T g cq)) hMpos _
    ((piWork w₀).clean_unit hψ) _ ((piWork w₀).output_isometry hF), rfl,
    fun j y => (q₂ j.val).eval_unitary hO₂ y, ?_⟩
  intro x P L δ y hP hL hδ hPc hJc hδ1 hδε hvalid
  let p : Inst X n m := Inst.mk x P L hP hL
  have hC' := hC p y hvalid
  have hclean := fullActualOracleW_clean D₀ (pullback D₀ (Inst.input (X := X) (n := n) (m := m)))
    (fullDegree s η T g cq ε) M m w₀ Pw J Inst.weight Inst.loader x p
    (fun l => fullActualOracle_pullback_matrix D₀ (Inst.input (X := X) (n := n) (m := m))
      (fullDegree s η T g cq ε) M m (fun _ => 1) (fun _ _ => 1) Inst.weight Inst.loader l p)
    (hPw x) hP hδ hPc hJc
  exact CleanWorkODE.work_certificate (piWork w₀) hC' q₁ hMpos hψ hF (fun j => hEval j p)
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (fullImplementation_matrix _ _ M m _ _ ω)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (fullImplementation_weight _ _ M m _ _ ω)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (fullImplementation_load _ _ M m _ _ ω)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (fullImplementation_unweight _ _ M m _ _ ω)))
    (fun j => by
      rw [hCost, funext (fullImplementation_source _ _ M m _ _ ω),
        GeneralSourceODE.Oracles.cost_add, NativeHermitianDilation.cost_scale])
    hO₁ hO₂ x hδ hclean hδ1 hδε (FullValidAt.target_ne_zero hvalid)

end

end DysonFullClass
