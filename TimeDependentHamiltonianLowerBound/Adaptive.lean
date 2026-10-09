import TimeDependentHamiltonianLowerBound.Access
import AdaptiveHamiltonianLowerBound.Theorem
import AdaptiveODELowerBound.Access.Admissible
import TimeDependentODE.Native.Layer

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Admissible time-dependent oracles and the adaptive lower bound

The adaptive form of Theorem `hsl:thm:main` (`AdaptiveHamiltonianLowerBound.main_max_tree`)
admits every oracle label that is `AdaptiveHamiltonianLowerBound.Access.Admissible` for the
hard data: a native call (in a fixed isometric layout of the workspace as a direct sum of
copies of the native query space, every copy applies the identity, one native query or its
inverse; weight at least one) or an input-independent unitary. This module shows that the
time-dependent access of Theorem `hs:thm:time` on constant data consists of admissible labels,
with the value-query weight `AdaptiveHamiltonianLowerBound.Access.valueWeight`.

* Transport (any input type, as `LinearSystemLowerBound.Native.NativeCall.conj` for one-hot
  inputs, outside this library's imports): admissible labels stay admissible, with the same
  weight, under a fixed isometric relabelling (`nativeCall_conj`, `admissible_conj`).
* **The coherent sampled-time native access** `∑_{(i,r)} |i,r⟩⟨i,r| ⊗ O_l(x, r)`
  (`coherentAccess ι D`, the released `TimeDependentODE.labelOracle` of the native primitives
  with `TimeDependentODE.sample`, the access of `SparseLowerBounds.ODE.Family.access`, outside
  this library's imports) of constant data is the native access of the instance with the
  untouched spectator `ι × Fin M` (`coherentAccess_constData`): a direct sum of copies of the
  native query space, one per branch and time slot. Hence its labels and all their call forms
  (plain, inverse, controlled, controlled inverse; `AdaptiveODELowerBound.Access.callFamily`)
  are admissible (`admissible_coherentAccess`, `admissible_callFamily_coherentAccess`).
* **The released physical families** of the time-dependent simulators on constant data, the
  coherent sampled-time oracle `TimeDependent.sampledOracle (constData D M)` and the aligned
  families `AlignedMultiOracleProgram.oracle (Sampled.oracle (constData D M) T d)` (in
  particular `TimeDependent.oracle` and `TimeDependentExtensions.Hamiltonian.oracle`), are in
  the normal form `U⁻¹ (1_Ω ⊗ oracles D l x) U` (`sampled_normal_form`, `aligned_normal_form`),
  hence admissible (`admissible_of_normal_form`, `admissible_sampledOracle`,
  `admissible_aligned`, `admissible_uniform`, `admissible_mesh`).

The tree forms of Theorem `hsl:thm:main` for these label families are in
`TimeDependentHamiltonianLowerBound/Trees.lean`.
-/

namespace TimeDependentHamiltonianLowerBound

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseLowerBounds
open AdaptiveHamiltonianLowerBound.Access (Admissible NativeCall valueWeight)

/-! ### Transports of admissible labels -/

section Transport

variable {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s : ℕ}
variable {K K' : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']

/-- Native calls are closed under fixed isometric layouts (any input type). -/
theorem nativeCall_conj {D : Data X N Z s} {O : X → K →L[ℂ] K} (h : NativeCall D O)
    (Φ : K ≃ₗᵢ[ℂ] K') : NativeCall D (fun x => Φ.conjStarAlgEquiv (O x)) := by
  obtain ⟨S, hS, ℓ, call, hO⟩ := h
  refine ⟨S, hS, Φ.symm.trans ℓ, call, fun x => ?_⟩
  ext v
  simp [hO, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

/-- **Admissible labels are closed under fixed isometric layouts**, with the same weight. -/
theorem admissible_conj {D : Data X N Z s} {O : X → K →L[ℂ] K} {w : ℕ} (h : Admissible D O w)
    (Φ : K ≃ₗᵢ[ℂ] K') : Admissible D (fun x => Φ.conjStarAlgEquiv (O x)) w := by
  rcases h with ⟨hN, hw⟩ | ⟨hc, hu⟩
  · exact Or.inl ⟨nativeCall_conj hN Φ, hw⟩
  · exact Or.inr ⟨fun x x' => congrArg (fun A => Φ.conjStarAlgEquiv A) (hc x x'),
      fun x => (hu x).transport Φ⟩

end Transport

/-! ### The coherent sampled-time native access -/

section Coherent

variable {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s : ℕ}

/-- **The coherent sampled-time native access** (equation `hs:eq:timeaccess`): label `l` on
input `x` is `∑_{(i,r)} |i,r⟩⟨i,r| ⊗ O_l(x, r)` on `ℂ^{ι × Fin M} ⊗ NSpace`, with the native
primitive `O_l(x, r) = oracles D l (x, r)` of the sample `r` and an untouched branch register
`ι` (the released `TimeDependentODE.labelOracle` with `TimeDependentODE.sample`, as
`SparseLowerBounds.ODE.Family.access`, outside this library's imports). -/
abbrev coherentAccess (ι : Type*) {M : ℕ} (D : Data (X × Fin M) N Z s) :
    Query → X → Joint (ι × Fin M) (SparseFlagEmbedding.Space (N × N) Z) →L[ℂ]
      Joint (ι × Fin M) (SparseFlagEmbedding.Space (N × N) Z) :=
  TimeDependentODE.labelOracle (oracles D) (TimeDependentODE.sample (ι := ι) (M := M))

/-- **The coherent sampled-time access of constant data is the native access with a spectator
time register**: `∑_{(i,r)} |i,r⟩⟨i,r| ⊗ O_l(x, r) = 1_{ι × Fin M} ⊗ O_l(x)`. -/
theorem coherentAccess_constData (ι : Type*) [Fintype ι] (D : Data X N Z s) (M : ℕ)
    (l : Query) (x : X) :
    coherentAccess ι (constData D M) l x = specOracles (ι × Fin M) D l x := by
  ext Ψ b : 2
  cases l <;> rfl

/-- **The coherent sampled-time access of constant data is admissible** with the value-query
weight, for data with input-independent locators. -/
theorem admissible_coherentAccess (ι : Type) [Fintype ι] (D : Data X N Z s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x') (M : ℕ) (q : Query) :
    Admissible D (coherentAccess ι (constData D M) q) (valueWeight q) := by
  have e : coherentAccess ι (constData D M) q = specOracles (ι × Fin M) D q :=
    funext fun x => coherentAccess_constData ι D M q x
  rw [e]
  exact AdaptiveHamiltonianLowerBound.Access.admissible_specOracles (ι × Fin M) D hrow hcol q

/-- **Every call form of the coherent sampled-time access of constant data is admissible**
(plain, inverse, controlled and controlled inverse; `AdaptiveODELowerBound.Access.callFamily`),
with the value-query weight of its label. -/
theorem admissible_callFamily_coherentAccess (ι : Type) [Fintype ι] (D : Data X N Z s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x') (M : ℕ)
    (c : Query × AdaptiveODELowerBound.Access.CallForm) :
    Admissible D (AdaptiveODELowerBound.Access.callFamily (coherentAccess ι (constData D M)) c)
      (valueWeight c.1) := by
  have e : coherentAccess ι (constData D M) = specOracles (ι × Fin M) D :=
    funext fun q => funext fun x => coherentAccess_constData ι D M q x
  rw [e]
  exact AdaptiveODELowerBound.Access.admissible_callFamily_spec (ι × Fin M) D hrow hcol c

end Coherent

/-! ### The released physical families -/

section Released

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s : ℕ}

/-- A family in the normal form `U⁻¹ (1_Ω ⊗ oracles D l x) U` is admissible with the
value-query weight, for data with input-independent locators. -/
theorem admissible_of_normal_form {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (D : Data X N Z s) (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x') {O : Query → X → K →L[ℂ] K}
    (hO : ∃ (Ω : Type) (_ : Fintype Ω) (U : K ≃ₗᵢ[ℂ] Joint Ω (SparseFlagEmbedding.Space (N × N) Z)),
      ∀ l x, O l x = U.symm.conjStarAlgEquiv (specOracles Ω D l x)) (q : Query) :
    Admissible D (O q) (valueWeight q) := by
  obtain ⟨Ω, _, U, hU⟩ := hO
  have e : O q = fun x => U.symm.conjStarAlgEquiv (specOracles Ω D q x) :=
    funext fun x => hU q x
  rw [e]
  exact admissible_conj
    (AdaptiveHamiltonianLowerBound.Access.admissible_specOracles Ω D hrow hcol q) U.symm

/-- **The coherent sampled-time oracle of the released simulators on constant data is
admissible** (`TimeDependent.sampledOracle`; normal form `sampled_normal_form`). -/
theorem admissible_sampledOracle (D : Data X N Z s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x') (M : ℕ) (q : Query) :
    Admissible D (TimeDependent.sampledOracle (constData D M) q) (valueWeight q) :=
  admissible_of_normal_form D hrow hcol (sampled_normal_form D M) q

/-- **The aligned physical family of the released time-dependent simulators on constant data
is admissible** (any number of samples `M`, slot count `T` and degree `d`; normal form
`aligned_normal_form`). -/
theorem admissible_aligned (D : Data X N Z s) (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x') (M T d : ℕ) (q : Query) :
    Admissible D
      (AlignedMultiOracleProgram.oracle (TimeDependent.Sampled.oracle (constData D M) T d) q)
      (valueWeight q) :=
  admissible_of_normal_form D hrow hcol (aligned_normal_form D M T d) q

/-- **The uniform-mesh released family on constant data is admissible**
(`TimeDependent.oracle`, any schedule). -/
theorem admissible_uniform (D : Data X N Z s) (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x') (M : ℕ) (γ η t ε : ℝ) (q : Query) :
    Admissible D (TimeDependent.oracle (constData D M) γ η t ε q) (valueWeight q) :=
  admissible_aligned D hrow hcol M M _ q

/-- **The general-mesh released family on constant data is admissible**
(`TimeDependentExtensions.Hamiltonian.oracle`, any slot count and schedule). -/
theorem admissible_mesh (D : Data X N Z s) (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x') (M Nsl : ℕ) (γ η T ε : ℝ)
    (q : Query) :
    Admissible D (TimeDependentExtensions.Hamiltonian.oracle (constData D M) Nsl γ η T ε q)
      (valueWeight q) :=
  admissible_aligned D hrow hcol M Nsl _ q

end Released

end

end TimeDependentHamiltonianLowerBound
