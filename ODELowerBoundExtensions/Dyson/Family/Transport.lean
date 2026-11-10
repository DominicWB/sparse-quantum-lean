import ODELowerBoundExtensions.Dyson.Theorem
import SparseLowerBounds.ODE.Model
import SparseHamiltonian.MultiOracleTransport

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The Dyson access is the ODE lower-bound access (`odel:lem:dyson`)

The consequence of Lemma `odel:lem:dyson` refutes a uniform lower bound for the class of the ODE
lower bounds, whose access is `SparseLowerBounds.ODE.Family.access ι`: the release's coherent
sampled-time query `∑_{(i,r)} |i,r⟩⟨i,r| ⊗ O_l(x, r)` (`TimeDependentODE.labelOracle` of the
native primitives with `TimeDependentODE.sample`) with an arbitrary spectator register `ι`.

Every matrix call of the Dyson access (`Theorem.oracle`) is the same native call with spectator
registers: the source branch and system index, the control/dummy/reference registers of the two
masked-access layers and the LCU branch and flags. A fixed reordering of the computational basis
(`basisEquiv`) and the release's flattenings give one fixed isometry `familyLayout` from the
Dyson workspace onto `SparseLowerBounds.ODE.Workspace (Spectator …) n Z Kₛ` which conjugates every
matrix call to the lower-bound access (`familyLayout_matrix`). When the source interfaces do not
depend on the input (public sources, as in the lower-bound class) their calls are known gates
(`knownSource`, `oracle_inr`), and the generic map `sourceFreeProgram` (with `familyLayout` and
`knownSource`; the release's `Program.transport` followed by `Program.substitute`) sends every
Dyson program to a program over the lower-bound access with the same matrix calls
(`sourceFreeProgram_eval`, `sourceFreeProgram_matrix_cost`) and no source calls.
`certificate_transport` carries the released complete certificate along such a map.
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct BigOperators

/-- The matrix-sector basis of the Dyson workspace (LCU branch, flags, masked-access registers
and payload). -/
abbrev DysonB (Ks : ℕ) (n Z : Type*) (K M : ℕ) : Type _ :=
  Omega K M × NativeControlledOracle.Workspace (PBasis Ks n Z)

/-- **The spectator register** of the transported access: every register of the Dyson
workspace except the time address and the native register. -/
abbrev Spectator (Ks : ℕ) (n Z : Type*) (K M : ℕ) : Type _ :=
  ((Lab K M × n) × ((Bool × DysonB Ks n Z K M) × DysonB Ks n Z K M)) ×
    (Omega K M × ((Bool × PBasis Ks n Z) × PBasis Ks n Z))

/-- The fixed reordering of the computational basis. -/
def basisEquiv (Ks : ℕ) (n Z : Type*) (K M : ℕ) :
    (Lab K M × n) × NativeControlledOracle.Workspace (DysonB Ks n Z K M) ≃
      (Spectator Ks n Z K M × Fin Ks) × NBasis n Z where
  toFun v := ((((v.1, v.2.1), (v.2.2.1, v.2.2.2.1)), v.2.2.2.2.1), v.2.2.2.2.2)
  invFun w := (w.1.1.1.1, (w.1.1.1.2, (w.1.1.2.1, (w.1.1.2.2, (w.1.2, w.2)))))
  left_inv _ := rfl
  right_inv _ := rfl

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s Ks : ℕ}

/-- **The fixed layout** from the Dyson workspace onto the lower-bound workspace. -/
def familyLayout (K M : ℕ) :
    DysonSpace Ks n Z K M ≃ₗᵢ[ℂ] SparseLowerBounds.ODE.Workspace (Spectator Ks n Z K M) n Z Ks :=
  (RegisterEquivalences.productFlatten (Lab K M × n)
      (NativeControlledOracle.Workspace (DysonB Ks n Z K M))).trans
    ((LookupOracle.permutationUnitary (basisEquiv Ks n Z K M)).trans
      ((RegisterEquivalences.productFlatten (Spectator Ks n Z K M × Fin Ks) (NBasis n Z)).symm.trans
        (LinearIsometryEquiv.piLpCongrRight 2
          (fun _ : Spectator Ks n Z K M × Fin Ks =>
            (NativeSparseMaskedAccess.layout (n := n) (Z := Z)).symm))))

set_option maxRecDepth 20000 in
omit [DecidableEq Z] in
/-- **Every Dyson matrix call is the lower-bound access** with spectator `Spectator …`. -/
theorem familyLayout_matrix (D : Data (X × Fin Ks) n Z s) (K M : ℕ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (l : Query) (x : X) :
    (familyLayout (Ks := Ks) (n := n) (Z := Z) K M).conjStarAlgEquiv
        (oracle D K M J₀ Jb (Sum.inl l) x) =
      TimeDependentODE.labelOracle (oracles D)
        (TimeDependentODE.sample (ι := Spectator Ks n Z K M) (M := Ks)) l x := by
  have hcomm : ∀ u : DysonSpace Ks n Z K M,
      familyLayout (Ks := Ks) (n := n) (Z := Z) K M (oracle D K M J₀ Jb (Sum.inl l) x u) =
        TimeDependentODE.labelOracle (oracles D)
          (TimeDependentODE.sample (ι := Spectator Ks n Z K M) (M := Ks)) l x
          (familyLayout (Ks := Ks) (n := n) (Z := Z) K M u) := by
    intro u
    apply PiLp.ext
    rintro ⟨sp, t⟩
    apply (NativeSparseMaskedAccess.layout (n := n) (Z := Z)).injective
    apply PiLp.ext
    intro nb
    rfl
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply]
  apply ContinuousLinearMap.ext
  intro w
  have h := hcomm ((familyLayout (Ks := Ks) (n := n) (Z := Z) K M).symm w)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h

/-- A source call with input-independent interfaces `J₀'`, `Jb'`: a known gate. -/
def knownSource (K M : ℕ) (J₀' : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb' : Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (b : Bool) :
    DysonSpace Ks n Z K M →L[ℂ] DysonSpace Ks n Z K M :=
  ODESectorTensor.sourcePhysical (B := DysonB Ks n Z K M)
    ((sourceLayout K M n).conjStarAlgEquiv
      (if b then TimeDependentODE.SourceTD.forcing (ι := LabelI K M) Jb'
        else ODESourceControls.initial (ι := LabelI K M) J₀' M))

omit [AddCommGroup Z] [DecidableEq Z] in
/-- The known source gates are unitary. -/
theorem knownSource_unitary (K M : ℕ) (J₀' : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb' : Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (hJ₀ : IsUnitary J₀')
    (hJb : ∀ q, IsUnitary (Jb' q)) (b : Bool) :
    IsUnitary (knownSource (Ks := Ks) (Z := Z) K M J₀' Jb' b) := by
  unfold knownSource
  apply ODESectorTensor.sourcePhysical_unitary
  apply IsUnitary.transport
  cases b with
  | false => exact ODESourceControls.initial_unitary J₀' M hJ₀
  | true => exact TimeDependentODE.SourceTD.forcing_unitary Jb' hJb

omit [DecidableEq Z] in
/-- Input-independent source interfaces give the known source gates. -/
theorem oracle_inr (D : Data (X × Fin Ks) n Z s) (K M : ℕ)
    (J₀' : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb' : Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (b : Bool) (x : X) :
    oracle D K M (fun _ => J₀') (fun _ => Jb') (Sum.inr b) x = knownSource K M J₀' Jb' b := by
  cases b <;> rfl

/-- The lower-bound access with an idle source vocabulary (never called after the map). -/
abbrev familyOracle (D : Data (X × Fin Ks) n Z s) (K M : ℕ) :
    Query ⊕ Bool → X → SparseLowerBounds.ODE.Workspace (Spectator Ks n Z K M) n Z Ks →L[ℂ]
      SparseLowerBounds.ODE.Workspace (Spectator Ks n Z K M) n Z Ks :=
  ODESourceQueryBudget.oracle
    (TimeDependentODE.labelOracle (oracles D)
      (TimeDependentODE.sample (ι := Spectator Ks n Z K M) (M := Ks)))
    (fun _ _ => 1)

/-- **Source-free program map** (generic): the release's coordinate change
`MultiOracleCircuit.Program.transport Φ` followed by syntactic substitution
(`MultiOracleCircuit.Program.substitute`): matrix calls are kept, and the calls of the
input-independent source interfaces `S b` become the known gates `Φ (S b) Φ⁻¹`. -/
def sourceFreeProgram {R R' Y L : Type*}
    [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
    [NormedAddCommGroup R'] [InnerProductSpace ℂ R'] [CompleteSpace R']
    {O : (L ⊕ Bool) → Y → R →L[ℂ] R} {O' : L → Y → R' →L[ℂ] R'}
    (Φ : R ≃ₗᵢ[ℂ] R') (S : Bool → R →L[ℂ] R) (hS : ∀ b, IsUnitary (S b))
    (p : MultiOracleCircuit.Program O) :
    MultiOracleCircuit.Program (ODESourceQueryBudget.oracle O' (fun _ _ => 1)) :=
  (p.transport Φ).substitute
    (Sum.elim
      (fun l => (.query (.inl l) :
        MultiOracleCircuit.Program (ODESourceQueryBudget.oracle O' (fun _ _ => 1))))
      (fun b => .fixed (Φ.conjStarAlgEquiv (S b)) ((hS b).transport Φ)))

/-- The source-free program evaluates to the `Φ`-conjugate of the original program. -/
theorem sourceFreeProgram_eval {R R' Y L : Type*}
    [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
    [NormedAddCommGroup R'] [InnerProductSpace ℂ R'] [CompleteSpace R']
    {O : (L ⊕ Bool) → Y → R →L[ℂ] R} {O' : L → Y → R' →L[ℂ] R'}
    (Φ : R ≃ₗᵢ[ℂ] R') (S : Bool → R →L[ℂ] R) (hS : ∀ b, IsUnitary (S b))
    (hO' : ∀ l x, O' l x = Φ.conjStarAlgEquiv (O (Sum.inl l) x))
    (hOS : ∀ b x, O (Sum.inr b) x = S b) (p : MultiOracleCircuit.Program O) (x : Y) :
    (sourceFreeProgram (O' := O') Φ S hS p).eval x = Φ.conjStarAlgEquiv (p.eval x) := by
  unfold sourceFreeProgram
  rw [MultiOracleCircuit.Program.eval_substitute _ _ ?_ x,
    MultiOracleCircuit.Program.eval_transport]
  intro k y
  cases k with
  | inl l => exact hO' l y
  | inr b => exact congrArg Φ.conjStarAlgEquiv (hOS b y).symm

/-- The source-free program has the matrix cost of the original program. -/
theorem sourceFreeProgram_matrix_cost {R R' Y L : Type*}
    [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
    [NormedAddCommGroup R'] [InnerProductSpace ℂ R'] [CompleteSpace R']
    {O : (L ⊕ Bool) → Y → R →L[ℂ] R} {O' : L → Y → R' →L[ℂ] R'}
    (Φ : R ≃ₗᵢ[ℂ] R') (S : Bool → R →L[ℂ] R) (hS : ∀ b, IsUnitary (S b))
    (p : MultiOracleCircuit.Program O) (w : L → ℕ) :
    (sourceFreeProgram (O' := O') Φ S hS p).cost (ODESourceQueryBudget.matrixWeight w) =
      p.cost (ODESourceQueryBudget.matrixWeight w) := by
  unfold sourceFreeProgram
  rw [MultiOracleCircuit.Program.cost_substitute, MultiOracleCircuit.Program.cost_transport]
  congr 1
  funext k
  cases k <;> rfl

/-- The source-free program calls no source interface. -/
theorem sourceFreeProgram_source_cost {R R' Y L : Type*}
    [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
    [NormedAddCommGroup R'] [InnerProductSpace ℂ R'] [CompleteSpace R']
    {O : (L ⊕ Bool) → Y → R →L[ℂ] R} {O' : L → Y → R' →L[ℂ] R'}
    (Φ : R ≃ₗᵢ[ℂ] R') (S : Bool → R →L[ℂ] R) (hS : ∀ b, IsUnitary (S b))
    (p : MultiOracleCircuit.Program O) :
    (sourceFreeProgram (O' := O') Φ S hS p).cost ODESourceQueryBudget.sourceTotalWeight = 0 := by
  unfold sourceFreeProgram
  rw [MultiOracleCircuit.Program.cost_substitute, MultiOracleCircuit.Program.cost_transport]
  have hw : (fun k => (Sum.elim
      (fun l => (.query (.inl l) :
        MultiOracleCircuit.Program (ODESourceQueryBudget.oracle O' (fun _ _ => 1))))
      (fun b => .fixed (Φ.conjStarAlgEquiv (S b)) ((hS b).transport Φ)) k).cost
        ODESourceQueryBudget.sourceTotalWeight) = fun _ => 0 := by
    funext k
    cases k <;> rfl
  rw [hw, MultiOracleCircuit.Program.cost_const, mul_zero]

/-- **Transport of the released complete certificate** along a cost-preserving program map that
conjugates every program by a fixed isometry: matrix costs equal, source costs not larger. -/
theorem certificate_transport {P R R' X L : Type*}
    [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P] [FiniteDimensional ℂ P]
    [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
    [NormedAddCommGroup R'] [InnerProductSpace ℂ R'] [CompleteSpace R']
    {O : (L ⊕ Bool) → X → R →L[ℂ] R} {O' : (L ⊕ Bool) → X → R' →L[ℂ] R'}
    (Φ : R ≃ₗᵢ[ℂ] R') (f : MultiOracleCircuit.Program O → MultiOracleCircuit.Program O')
    (hEval : ∀ p x, (f p).eval x = Φ.conjStarAlgEquiv (p.eval x))
    (hMatrix : ∀ p, (f p).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) =
      p.cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)))
    (hSource : ∀ p b, (f p).cost (ODESourceQueryBudget.sourceWeight b) ≤
      p.cost (ODESourceQueryBudget.sourceWeight b))
    (hTotal : ∀ p, (f p).cost ODESourceQueryBudget.sourceTotalWeight ≤
      p.cost ODESourceQueryBudget.sourceTotalWeight)
    (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ) (ψ : R) (F : P →L[ℂ] R) (x : X)
    (target : P) (htarget : target ≠ 0) (s Θ ell g ε : ℝ) (hε : 0 ≤ ε)
    (h : ODECompleteTrial.Certificate q M ψ F x target s Θ ell g ε) :
    ODECompleteTrial.Certificate (fun j => f (q j)) M (Φ ψ)
      (Φ.toLinearIsometry.toContinuousLinearMap ∘L F) x target s Θ ell g ε := by
  set E : R →L[ℂ] R' := Φ.toLinearIsometry.toContinuousLinearMap with hE
  have hEE : E† ∘L E = 1 := Φ.toLinearIsometry.adjoint_comp_self
  have hEw : ∀ w : R, (E†) (Φ w) = w := fun w => by
    exact congrArg (fun T : R →L[ℂ] R => T w) hEE
  have hev : ∀ j, (f (q j)).eval x (Φ ψ) = Φ ((q j).eval x ψ) := by
    intro j
    rw [hEval, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.symm_apply_apply]
  have hadj : ∀ w : R, ((E ∘L F)†) (Φ w) = (F†) w := by
    intro w
    rw [adjoint_comp, comp_apply, hEw]
  have hproj : ∀ w : R, ODEHeraldedSuccess.successProjector (E ∘L F) (Φ w) =
      Φ (ODEHeraldedSuccess.successProjector F w) := by
    intro w
    simp only [ODEHeraldedSuccess.successProjector, comp_apply, hadj]
    rfl
  have ht := h.trial
  refine ODECompleteTrial.of_trialCertificate (fun j => ?_) hε htarget ?_
  · rw [hEval]
    exact (h.unitary_trials j).transport Φ
  · refine
      { cutoff_pos := ht.cutoff_pos
        cutoff_le := ht.cutoff_le
        seed_unit := by rw [LinearIsometryEquiv.norm_map]; exact ht.seed_unit
        output_isometry := by
          rw [adjoint_comp, comp_assoc, ← comp_assoc (adjoint E) E F, hEE, one_def, id_comp]
          exact ht.output_isometry
        matrix_queries := fun j hj => by rw [hMatrix]; exact ht.matrix_queries j hj
        source_queries := fun j hj b =>
          le_trans (by exact_mod_cast hSource (q j) b) (ht.source_queries j hj b)
        total_source_queries := fun j hj =>
          le_trans (by exact_mod_cast hTotal (q j)) (ht.total_source_queries j hj)
        mean_success := by
          simp only [hev, hproj, LinearIsometryEquiv.norm_map]
          exact ht.mean_success
        direction_error := fun j hj hne => by
          rw [hev, hadj] at hne ⊢
          exact ht.direction_error j hj hne }

end

end ODELowerBoundExtensions.Dyson
