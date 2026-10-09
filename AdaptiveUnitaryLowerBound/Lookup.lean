import AdaptiveUnitaryLowerBound.Theorem

set_option autoImplicit false

/-!
# Adaptive algorithms over the ordinary entry lookup

The lower half of the last sentence of corollary `hs:cor:unitary` of the
manuscript (lines 1664-1665, reduction at lines 1711-1718) for adaptive
algorithms over the ordinary reversible entry lookup of the search family,
`LookupControlledGate.oracle (K := V) (searchTable N)`, with an arbitrary
untouched payload `V` (for the protocol forms the workspace `W` and the output
space are finite-dimensional; the adaptive analogue of
`UnitaryImplementationExtensions.LowerBound.entry_count_ge`). Labels are
implemented on an isometric encoding by at most `w l` lookups;
`entry_count_ge_tree` covers protocols over the labels, and
`entry_count_ge_calls_tree` protocols over their four call forms
(`AdaptiveODELowerBound.Access.callFamily`). Accuracy is
`AdaptiveHamiltonianLowerBound.DensityAccurate` of the conditional output for
`U_m |0⟩`, with success probability at least `s₀ > 0` and `ε₀ ≤ 1/2`; the bound
is `(s₀ (1 - 2ε₀))² sqrt (N - 1) ≤ 4 Q`, positive for `ε₀ < 1/2` and empty at
`ε₀ = 1/2` (`ε₀` is trace-distance accuracy). For unitary programs with the
manuscript's operator-norm error the whole range `0 < ε ≤ 1/2` is covered:
over the lookup itself by the non-adaptive
`UnitaryImplementationExtensions.LowerBound.entry_count_ge`, over weighted labels
by `entry_count_ge_program_of_error`, and over their four call forms by
`entry_count_ge_calls_program_of_error`, all with
`(1 - 2ε₀ sqrt (1 - ε₀²/4)) sqrt (N - 1) ≤ 2 Q` for `ε₀ ≤ 1` (any workspace).
-/

namespace AdaptiveUnitaryLowerBound.Lookup

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Readout
open SparseLinearSystems.Protocol ContinuousLinearMap
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open UnitaryImplementationExtensions UnitaryImplementationExtensions.SearchFamily
open scoped InnerProduct InnerProductSpace

variable {E W Fl L G V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- **Adaptive algorithms over the ordinary entry lookup** (Corollary
`hs:cor:unitary`, last sentence). Every adaptive protocol over labels
implemented by at most `w l` lookups of the search table (payload `V`) on an
isometric encoding, on a finite-dimensional workspace, that on every instance
`m` succeeds with probability at least `s₀ > 0` and outputs, conditionally on
success, an `ε₀`-accurate copy of `U_m |0⟩` (`ε₀ ≤ 1/2`), has worst-case
weighted cost at least `(s₀ (1 - 2ε₀))² sqrt (N - 1) / 4`, positive for
`ε₀ < 1/2`. -/
theorem entry_count_ge_tree [FiniteDimensional ℂ W] [FiniteDimensional ℂ E] {N : ℕ}
    [NeZero N] (hN : 2 ≤ N)
    (Enc : W →L[ℂ] PiLp 2 (fun _ : (Fin N × Fin N) × ZMod 2 => V)) (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn
      (fun m => LookupControlledGate.oracle (K := V) (searchTable N) m) (O l) Enc (w l))
    (T : Tree O Fl E) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1)
    {s₀ ε₀ : ℝ} (hs₀ : 0 < s₀) (hε₀ : ε₀ ≤ 1 / 2)
    (hsucc : ∀ m, s₀ ≤ T.successMass m)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1)) ε₀) :
    (s₀ * (1 - 2 * ε₀)) ^ 2 * Real.sqrt ((N : ℝ) - 1) ≤ 4 * T.worstCost w := by
  have hw' : ∀ l, EncodedOracle.ImplementsOn
      (fun m => (PhaseBridge.xorFamily (Fin N × Fin N) V).phase
        (Search.markedString (Oracles.lookupPosition N) m)) (O l) Enc (w l) := fun l =>
    Oracles.implementsOn_phase_of_lookup V N (hw l)
  have hacc' : ∀ m, DensityAccurate e (T.conditionalDensity m) (Observable.ket m) ε₀ := by
    intro m
    simpa only [SearchFamily.searchMatrix_single_zero] using hacc m
  exact Accuracy.tree_search_count_ge_of_accurate hN (PhaseBridge.xorFamily (Fin N × Fin N) V)
    (Oracles.lookupPosition N) Enc hEnc hO w hw' T e he hs₀ hε₀ hsucc hacc'

/-- **Adaptive algorithms over the call forms of the ordinary entry lookup**
(Corollary `hs:cor:unitary`, last sentence). The bound of `entry_count_ge_tree`
for adaptive protocols over the call family of the labels: plain, inverse,
controlled and controlled-inverse forms, each counted with the weight of the
label. -/
theorem entry_count_ge_calls_tree [FiniteDimensional ℂ W] [FiniteDimensional ℂ E] {N : ℕ}
    [NeZero N] (hN : 2 ≤ N)
    (Enc : W →L[ℂ] PiLp 2 (fun _ : (Fin N × Fin N) × ZMod 2 => V)) (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn
      (fun m => LookupControlledGate.oracle (K := V) (searchTable N) m) (O l) Enc (w l))
    (T : Tree (AdaptiveODELowerBound.Access.callFamily O) Fl E)
    (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1)
    {s₀ ε₀ : ℝ} (hs₀ : 0 < s₀) (hε₀ : ε₀ ≤ 1 / 2)
    (hsucc : ∀ m, s₀ ≤ T.successMass m)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1)) ε₀) :
    (s₀ * (1 - 2 * ε₀)) ^ 2 * Real.sqrt ((N : ℝ) - 1) ≤
      4 * T.worstCost (fun c => w c.1) := by
  have hw' : ∀ l, EncodedOracle.ImplementsOn
      (fun m => (PhaseBridge.xorFamily (Fin N × Fin N) V).phase
        (Search.markedString (Oracles.lookupPosition N) m)) (O l) Enc (w l) := fun l =>
    Oracles.implementsOn_phase_of_lookup V N (hw l)
  have hacc' : ∀ m, DensityAccurate e (T.conditionalDensity m) (Observable.ket m) ε₀ := by
    intro m
    simpa only [SearchFamily.searchMatrix_single_zero] using hacc m
  exact Accuracy.tree_search_count_ge_of_accurate hN
    (AdaptiveODELowerBound.Access.callBoolean (PhaseBridge.xorFamily (Fin N × Fin N) V))
    (Oracles.lookupPosition N) (AdaptiveODELowerBound.Access.callEncoding Enc)
    (AdaptiveODELowerBound.Access.callEncoding_isometry Enc hEnc)
    (AdaptiveODELowerBound.Access.callFamily_unitary hO) (fun c => w c.1)
    (AdaptiveODELowerBound.Access.implementsOn_callFamily
      (PhaseBridge.xorFamily (Fin N × Fin N) V) (Search.markedString (Oracles.lookupPosition N))
      Enc O hO w hw') T e he hs₀ hε₀ hsucc hacc'

/-- **Unitary programs over the ordinary entry lookup with operator-norm error**
(Corollary `hs:cor:unitary`, last sentence). A single program over labels
implemented by at most `w l` lookups of the search table (payload `V`) on an
isometric encoding, on any workspace, that implements every search unitary `U_m`
on an isometric encoding `J` with operator-norm error at most `ε₀ ≤ 1` has
weighted cost at least `(1 - 2ε₀ sqrt (1 - ε₀²/4)) sqrt (N - 1) / 2`, positive
on the corollary's whole range `0 < ε₀ ≤ 1/2`. -/
theorem entry_count_ge_program_of_error {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (Enc : W →L[ℂ] PiLp 2 (fun _ : (Fin N × Fin N) × ZMod 2 => V)) (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn
      (fun m => LookupControlledGate.oracle (K := V) (searchTable N) m) (O l) Enc (w l))
    (p : MultiOracleCircuit.Program O)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] W) (hJ : J† ∘L J = 1) {ε₀ : ℝ} (hε₀ : ε₀ ≤ 1)
    (hErr : ∀ m, ‖p.eval m ∘L J - J ∘L
      SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤ ε₀) :
    (1 - 2 * ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4)) * Real.sqrt ((N : ℝ) - 1) ≤
      2 * p.cost w :=
  Theorem.program_search_count_ge_of_error hN (PhaseBridge.xorFamily (Fin N × Fin N) V)
    (Oracles.lookupPosition N) Enc hEnc hO w
    (fun l => Oracles.implementsOn_phase_of_lookup V N (hw l)) p J hJ hε₀ hErr

/-- **Unitary programs over the call forms of the ordinary entry lookup with
operator-norm error** (Corollary `hs:cor:unitary`, last sentence). The bound of
`entry_count_ge_program_of_error` for a single program over the call family of
the labels (plain, inverse, controlled and controlled-inverse forms, each
counted with the weight of the label) that implements every search unitary `U_m`
on an isometric encoding `J` into the controlled workspace `Joint Bool W` with
operator-norm error at most `ε₀ ≤ 1`. -/
theorem entry_count_ge_calls_program_of_error {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (Enc : W →L[ℂ] PiLp 2 (fun _ : (Fin N × Fin N) × ZMod 2 => V)) (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn
      (fun m => LookupControlledGate.oracle (K := V) (searchTable N) m) (O l) Enc (w l))
    (p : MultiOracleCircuit.Program (AdaptiveODELowerBound.Access.callFamily O))
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] Joint Bool W) (hJ : J† ∘L J = 1) {ε₀ : ℝ}
    (hε₀ : ε₀ ≤ 1)
    (hErr : ∀ m, ‖p.eval m ∘L J - J ∘L
      SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤ ε₀) :
    (1 - 2 * ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4)) * Real.sqrt ((N : ℝ) - 1) ≤
      2 * p.cost (fun c => w c.1) :=
  Theorem.program_search_count_ge_of_error hN
    (AdaptiveODELowerBound.Access.callBoolean (PhaseBridge.xorFamily (Fin N × Fin N) V))
    (Oracles.lookupPosition N) (AdaptiveODELowerBound.Access.callEncoding Enc)
    (AdaptiveODELowerBound.Access.callEncoding_isometry Enc hEnc)
    (AdaptiveODELowerBound.Access.callFamily_unitary hO) (fun c => w c.1)
    (AdaptiveODELowerBound.Access.implementsOn_callFamily
      (PhaseBridge.xorFamily (Fin N × Fin N) V) (Search.markedString (Oracles.lookupPosition N))
      Enc O hO w (fun l => Oracles.implementsOn_phase_of_lookup V N (hw l))) p J hJ hε₀ hErr

end
end AdaptiveUnitaryLowerBound.Lookup
