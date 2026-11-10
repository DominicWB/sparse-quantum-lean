import AdaptiveUnitaryLowerBound.Accuracy
import AdaptiveUnitaryLowerBound.Oracles
import AdaptiveHamiltonianLowerBound.Model.Single
import AdaptiveODELowerBound.Access.Control

set_option autoImplicit false

/-!
# The lower half of `Θ(√N)` for adaptive algorithms and controlled calls

Corollary `hs:cor:unitary` of the manuscript ends: "the constant-error worst-case complexity is
`Θ(√N)`." The lower half is stated with the reduction to unstructured search, and the corollary
counts inverse calls. Controlled and controlled-inverse calls and adaptive algorithms follow the
convention of the lower-bound sections of the manuscript (access with inverses and the controls of
Lemma `access:lem:control`, Section `hsl:sec:main`; "Purification and deferred measurement include
adaptive and randomised algorithms", proof of Lemma `hsl:lem:precision`). The non-adaptive lower
half is `UnitaryImplementationExtensions.LowerBound`; this module proves it for the adaptive
protocols `SparseLinearSystems.Protocol.Tree` over the released entry oracle of the search family,
`UnitaryEntryOracle.oracle (searchData N) γ η t ε` (for all parameters), and for the controlled and
controlled-inverse forms of its calls.

**Algorithms.** A labelled unitary family `O` on a workspace `W`, every label
`l` implemented on an isometric encoding `Enc` by at most `w l` calls of the
entry oracle (inverse calls included; fixed unitaries and input-independent
labels are free), and any adaptive protocol `T` over `O`; its cost is the
worst-case weighted count `T.worstCost w` over all transcripts. With the call
family `AdaptiveODELowerBound.Access.callFamily O` every label is also available
in its inverse, controlled and controlled-inverse forms, each counted with the
weight of the label. The protocol bounds need finite-dimensional workspace and
output spaces (lossless purification).

**Accuracy.** As in the package's adaptive lower bounds: on every instance `m`
success has probability at least `s₀ > 0`, and the conditional output, read
through an isometry `e` into system ⊗ garbage, is `ε₀`-accurate
(`AdaptiveHamiltonianLowerBound.DensityAccurate`, trace-distance accuracy) for
`U_m |0⟩`, the action of the target unitary on the input `|0⟩` of the
reduction. These bounds are positive for `ε₀ < 1/2` and empty at `ε₀ = 1/2`,
where the pair-observable gap vanishes. The manuscript's error notion is the
operator norm `‖A_U - U‖ ≤ ε` (eq. `hs:eq:unitaryerror`). For a unitary program,
operator-norm error `ε` gives `ε`-accuracy of the output on `|0⟩` by composing
the endpoint readout `SparseLowerBounds.Hamiltonian.accurate_of_endpoint` with
`AdaptiveHamiltonianLowerBound.densityAccurate_pure_iff` (a composition not
stated as a separate theorem), so through it the protocol bounds reach
operator-norm error only for `ε < 1/2`. For programs the operator norm is taken
directly by
`implementation_count_ge_program_of_error` (labels of `O`) and
`implementation_count_ge_calls_program_of_error` (the call family), whose factor
is positive on the corollary's whole range `0 < ε ≤ 1/2`; the endpoint
`ε = 1/2` is covered only by these program forms.

**Conventions.** The success threshold `s₀` is a parameter; `s₀ = 2/3` (the
heralded convention of the package's adaptive lower bounds) gives the constant
`9`, and `s₀ = 1` (unheralded) the constant `4`. The instance `[NeZero N]`,
implied by `2 ≤ N`, is kept for the input `0 : Fin N` of the reduction, as in
`UnitaryImplementationExtensions.LowerBound.implementation_count_ge`.

**Guarantees.** For `N ≥ 2`:

* `implementation_count_ge_tree`: `(s₀ (1 - 2ε₀))² sqrt (N - 1) ≤ 4 T.worstCost w`
  for `ε₀ ≤ 1/2`, positive for `ε₀ < 1/2`;
* `implementation_count_ge_calls_tree`: the same bound for protocols over the
  call family;
* `implementation_count_ge_program`: the same bound with `s₀ = 1` for a single
  program over `O` run on a unit seed, with accurate output (`Readout.Accurate`);
* `implementation_count_ge_program_of_error`: a single program over `O` that
  implements every `U_m` on an isometric encoding `J` with operator-norm error
  `ε₀ ≤ 1` has `(1 - 2 ε₀ sqrt (1 - ε₀²/4)) sqrt (N - 1) ≤ 2 p.cost w`, the
  constant of `UnitaryImplementationExtensions.LowerBound.implementation_count_ge`,
  for weighted labelled families;
* `implementation_count_ge_calls_program_of_error`: the same bound for a single
  program over the call family, on an isometric encoding into `Joint Bool W`.

The generic form `program_search_count_ge_of_error` holds for any family of
labels implemented by Boolean phase queries of the marked strings of a position
map, and serves the entry lookup forms in `Lookup`.
-/

namespace AdaptiveUnitaryLowerBound.Theorem

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Readout
open SparseLinearSystems.Protocol ContinuousLinearMap
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open UnitaryImplementationExtensions UnitaryImplementationExtensions.SearchFamily
open scoped InnerProduct InnerProductSpace
set_option synthInstance.maxSize 8192

variable {E W Fl L G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **Lower half of `Θ(√N)` for adaptive algorithms** (Corollary
`hs:cor:unitary`, last sentence). Every adaptive protocol over labels
implemented by at most `w l` calls of the released entry oracle of the search
family on an isometric encoding, on a finite-dimensional workspace, that on
every instance `m` succeeds with probability at least `s₀ > 0` and outputs,
conditionally on success, an `ε₀`-accurate copy of `U_m |0⟩` (`ε₀ ≤ 1/2`), has
worst-case weighted cost at least `(s₀ (1 - 2ε₀))² sqrt (N - 1) / 4`, positive
for `ε₀ < 1/2`. -/
theorem implementation_count_ge_tree [FiniteDimensional ℂ W] [FiniteDimensional ℂ E]
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) (γ η t ε : ℝ)
    (Enc : W →L[ℂ] UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε)
    (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn
      (UnitaryEntryOracle.oracle (searchData N) γ η t ε) (O l) Enc (w l))
    (T : Tree O Fl E) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1)
    {s₀ ε₀ : ℝ} (hs₀ : 0 < s₀) (hε₀ : ε₀ ≤ 1 / 2)
    (hsucc : ∀ m, s₀ ≤ T.successMass m)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1)) ε₀) :
    (s₀ * (1 - 2 * ε₀)) ^ 2 * Real.sqrt ((N : ℝ) - 1) ≤ 4 * T.worstCost w := by
  have hacc' : ∀ m, DensityAccurate e (T.conditionalDensity m) (Observable.ket m) ε₀ :=
    fun m => by simpa only [searchMatrix_single_zero] using hacc m
  exact Accuracy.tree_search_count_ge_of_accurate hN
    (LiftPhase.entryFamily (n := Fin N) γ η t ε) (Oracles.entryPosition N) Enc hEnc hO w
    (fun l => Oracles.implementsOn_phase_of_entry N γ η t ε (hw l)) T e he hs₀ hε₀ hsucc hacc'

/-- **Lower half of `Θ(√N)` with controlled and controlled-inverse calls**
(Corollary `hs:cor:unitary`, last sentence). The bound of
`implementation_count_ge_tree` for adaptive protocols over the call family of
`O`: every label in its plain, inverse, controlled and controlled-inverse forms,
each counted with the weight of the label. -/
theorem implementation_count_ge_calls_tree [FiniteDimensional ℂ W] [FiniteDimensional ℂ E]
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) (γ η t ε : ℝ)
    (Enc : W →L[ℂ] UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε)
    (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn
      (UnitaryEntryOracle.oracle (searchData N) γ η t ε) (O l) Enc (w l))
    (T : Tree (AdaptiveODELowerBound.Access.callFamily O) Fl E)
    (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1)
    {s₀ ε₀ : ℝ} (hs₀ : 0 < s₀) (hε₀ : ε₀ ≤ 1 / 2)
    (hsucc : ∀ m, s₀ ≤ T.successMass m)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1)) ε₀) :
    (s₀ * (1 - 2 * ε₀)) ^ 2 * Real.sqrt ((N : ℝ) - 1) ≤
      4 * T.worstCost (fun c => w c.1) := by
  have hacc' : ∀ m, DensityAccurate e (T.conditionalDensity m) (Observable.ket m) ε₀ :=
    fun m => by simpa only [searchMatrix_single_zero] using hacc m
  have hw' := fun l => Oracles.implementsOn_phase_of_entry N γ η t ε (hw l)
  exact Accuracy.tree_search_count_ge_of_accurate hN
    (AdaptiveODELowerBound.Access.callBoolean (LiftPhase.entryFamily (n := Fin N) γ η t ε))
    (Oracles.entryPosition N) (AdaptiveODELowerBound.Access.callEncoding Enc)
    (AdaptiveODELowerBound.Access.callEncoding_isometry Enc hEnc)
    (AdaptiveODELowerBound.Access.callFamily_unitary hO) (fun c => w c.1)
    (fun c => AdaptiveODELowerBound.Access.implementsOn_callFamily
      (LiftPhase.entryFamily (n := Fin N) γ η t ε)
      (Search.markedString (Oracles.entryPosition N)) Enc O hO w hw' c)
    T e he hs₀ hε₀ hsucc hacc'

/-- **The program form in the readout of the adaptive class** (Corollary
`hs:cor:unitary`, last sentence). A single program over `O` (labels as in
`implementation_count_ge_tree`) run on a unit seed `φ₀`, whose output on every
instance `m`, read through the isometry `e`, is `ε₀`-accurate for `U_m |0⟩`
(`ε₀ ≤ 1/2`), has weighted cost at least `(1 - 2ε₀)² sqrt (N - 1) / 4`, positive
for `ε₀ < 1/2`. -/
theorem implementation_count_ge_program [FiniteDimensional ℂ W] {N : ℕ} [NeZero N]
    (hN : 2 ≤ N)
    (γ η t ε : ℝ) (Enc : W →L[ℂ] UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε)
    (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn
      (UnitaryEntryOracle.oracle (searchData N) γ η t ε) (O l) Enc (w l))
    (p : MultiOracleCircuit.Program O) (φ₀ : W) (hφ₀ : ‖φ₀‖ = 1)
    (e : W →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) {ε₀ : ℝ} (hε₀ : ε₀ ≤ 1 / 2)
    (hacc : ∀ m, Accurate e (p.eval m φ₀)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1)) ε₀) :
    (1 - 2 * ε₀) ^ 2 * Real.sqrt ((N : ℝ) - 1) ≤ 4 * p.cost w := by
  have hU := fun m => MultiOracleCircuit.Program.eval_unitary p hO m
  have h := implementation_count_ge_tree (E := W) (Fl := ℂ) hN γ η t ε Enc hEnc hO w hw
    (AdaptiveHamiltonianLowerBound.Single.tree ℂ p φ₀ hφ₀) e he (s₀ := 1) one_pos hε₀
    (fun m => (AdaptiveHamiltonianLowerBound.Single.successMass_tree p φ₀ hφ₀ m (hU m)).ge)
    (fun m => by
      rw [AdaptiveHamiltonianLowerBound.Single.conditionalDensity_tree p φ₀ hφ₀ m (hU m),
        AdaptiveHamiltonianLowerBound.densityAccurate_pure_iff]
      exact hacc m)
  rw [AdaptiveHamiltonianLowerBound.Single.worstCost_tree, one_mul] at h
  exact h

/-- **Search programs with operator-norm error** (the reduction to unstructured
search in the proof of Corollary `hs:cor:unitary`). If every label of a unitary
family over the instances `Fin N` is implemented on the isometric encoding `Enc`
by at most `w l` queries of the phase oracle of the marked strings of `c`, a
single program over the family that implements every search unitary `U_m` on an
isometric encoding `J` with operator-norm error at most `ε₀ ≤ 1` has weighted
cost at least `(1 - 2 ε₀ sqrt (1 - ε₀²/4)) sqrt (N - 1) / 2`. The output on
`J |0⟩` is `ε₀`-close to `J |m⟩` (`searchMatrix_single_zero`), so
`Search.norm_inner_le_of_near` bounds the Gram kernel of the one-trial protocol
`AdaptiveHamiltonianLowerBound.Single.tree`, and `Kernel.tree_search_count_ge`
applies. -/
theorem program_search_count_ge_of_error {B I : Type*} [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] [Fintype I] {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (P : ProjFamily B I) (c : I → Fin N) (Enc : W →L[ℂ] B) (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun m => P.phase (Search.markedString c m))
      (O l) Enc (w l))
    (p : MultiOracleCircuit.Program O)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] W) (hJ : J† ∘L J = 1) {ε₀ : ℝ} (hε₀ : ε₀ ≤ 1)
    (hErr : ∀ m, ‖p.eval m ∘L J - J ∘L
      SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤ ε₀) :
    (1 - 2 * ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4)) * Real.sqrt ((N : ℝ) - 1) ≤
      2 * p.cost w := by
  classical
  have hIso : ∀ x, ‖J x‖ = ‖x‖ :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self J).mpr hJ
  have hInner : ∀ x y, ⟪J x, J y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro x y
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply, hJ,
      one_apply_eq_self]
  have hu : ∀ m : Fin N, ‖J (EuclideanSpace.single m 1)‖ = 1 := by
    intro m
    rw [hIso]
    simp
  have horth : ∀ m m' : Fin N, m ≠ m' →
      ⟪J (EuclideanSpace.single m 1), J (EuclideanSpace.single m' 1)⟫_ℂ = 0 := by
    intro m m' h
    rw [hInner, EuclideanSpace.inner_single_left]
    simp [h]
  set φ₀ : W := J (EuclideanSpace.single 0 1)
  have hφ₀ : ‖φ₀‖ = 1 := hu 0
  have hEval : ∀ m, ‖p.eval m φ₀‖ = 1 := by
    intro m
    rw [(ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr
      (MultiOracleCircuit.Program.eval_unitary p hO m).1]
    exact hφ₀
  have hOut : ∀ m, ‖p.eval m φ₀ - J (EuclideanSpace.single m 1)‖ ≤ ε₀ := by
    intro m
    have h := (p.eval m ∘L J - J ∘L
      SparseStateOverlap.matrixOperator (searchMatrix N m)).le_opNorm (EuclideanSpace.single 0 1)
    have h1 : ‖(EuclideanSpace.single (0 : Fin N) (1 : ℂ) : EuclideanSpace ℂ (Fin N))‖ = 1 := by
      simp
    rw [h1, mul_one] at h
    simp only [sub_apply, ContinuousLinearMap.comp_apply, searchMatrix_single_zero] at h
    exact h.trans (hErr m)
  let T := AdaptiveHamiltonianLowerBound.Single.tree ℂ p φ₀ hφ₀
  have hkern : ∀ m m', AdaptiveODELowerBound.Adversary.treeKernel T m m' =
      ⟪p.eval m φ₀, p.eval m' φ₀⟫_ℂ := by
    intro m m'
    simp [T, AdaptiveODELowerBound.Adversary.treeKernel, AdaptiveHamiltonianLowerBound.Single.tree,
      ODELowerBoundExtensions.Release.kernel, ODELowerBoundExtensions.Release.trialKernel,
      AdaptiveHamiltonianLowerBound.Single.trial]
  have h := Kernel.tree_search_count_ge hN P c Enc hEnc hO w hw T
    (κ := 1 - 2 * ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4)) (fun m m' hmm => by
      rw [hkern]
      have hn := Search.norm_inner_le_of_near hε₀ (hEval m) (hEval m') (hu m) (hu m')
        (horth m m' hmm) (hOut m) (hOut m')
      exact (Complex.re_le_norm _).trans (by linarith))
  rw [AdaptiveHamiltonianLowerBound.Single.worstCost_tree] at h
  exact h

/-- **The program form with the manuscript's operator-norm error** (Corollary
`hs:cor:unitary`, last sentence). A single program over `O` (labels as in
`implementation_count_ge_tree`, on any workspace) that implements every search
unitary `U_m` on an isometric encoding `J` with operator-norm error at most
`ε₀ ≤ 1` has weighted cost at least
`(1 - 2 ε₀ sqrt (1 - ε₀²/4)) sqrt (N - 1) / 2`. The factor is positive on the
corollary's whole range `0 < ε₀ ≤ 1/2` (`Search.near_factor_pos`); the constant
is that of `UnitaryImplementationExtensions.LowerBound.implementation_count_ge`.
-/
theorem implementation_count_ge_program_of_error {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (γ η t ε : ℝ) (Enc : W →L[ℂ] UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε)
    (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn
      (UnitaryEntryOracle.oracle (searchData N) γ η t ε) (O l) Enc (w l))
    (p : MultiOracleCircuit.Program O)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] W) (hJ : J† ∘L J = 1) {ε₀ : ℝ} (hε₀ : ε₀ ≤ 1)
    (hErr : ∀ m, ‖p.eval m ∘L J - J ∘L
      SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤ ε₀) :
    (1 - 2 * ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4)) * Real.sqrt ((N : ℝ) - 1) ≤
      2 * p.cost w :=
  program_search_count_ge_of_error hN (LiftPhase.entryFamily (n := Fin N) γ η t ε)
    (Oracles.entryPosition N) Enc hEnc hO w
    (fun l => Oracles.implementsOn_phase_of_entry N γ η t ε (hw l)) p J hJ hε₀ hErr

/-- **The program form with operator-norm error and controlled calls**
(Corollary `hs:cor:unitary`, last sentence). The bound of
`implementation_count_ge_program_of_error` for a single program over the call
family of `O` (every label in its plain, inverse, controlled and
controlled-inverse forms, each counted with the weight of the label) that
implements every search unitary `U_m` on an isometric encoding `J` into the
controlled workspace `Joint Bool W` with operator-norm error at most `ε₀ ≤ 1`.
The factor is positive on the corollary's whole range `0 < ε₀ ≤ 1/2`. -/
theorem implementation_count_ge_calls_program_of_error {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (γ η t ε : ℝ) (Enc : W →L[ℂ] UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε)
    (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn
      (UnitaryEntryOracle.oracle (searchData N) γ η t ε) (O l) Enc (w l))
    (p : MultiOracleCircuit.Program (AdaptiveODELowerBound.Access.callFamily O))
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] Joint Bool W)
    (hJ : J† ∘L J = 1) {ε₀ : ℝ} (hε₀ : ε₀ ≤ 1)
    (hErr : ∀ m, ‖p.eval m ∘L J - J ∘L
      SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤ ε₀) :
    (1 - 2 * ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4)) * Real.sqrt ((N : ℝ) - 1) ≤
      2 * p.cost (fun c => w c.1) := by
  have hw' := fun l => Oracles.implementsOn_phase_of_entry N γ η t ε (hw l)
  exact program_search_count_ge_of_error hN
    (AdaptiveODELowerBound.Access.callBoolean (LiftPhase.entryFamily (n := Fin N) γ η t ε))
    (Oracles.entryPosition N) (AdaptiveODELowerBound.Access.callEncoding Enc)
    (AdaptiveODELowerBound.Access.callEncoding_isometry Enc hEnc)
    (AdaptiveODELowerBound.Access.callFamily_unitary hO) (fun c => w c.1)
    (fun c => AdaptiveODELowerBound.Access.implementsOn_callFamily
      (LiftPhase.entryFamily (n := Fin N) γ η t ε)
      (Search.markedString (Oracles.entryPosition N)) Enc O hO w hw' c)
    p J hJ hε₀ hErr

end
end AdaptiveUnitaryLowerBound.Theorem
