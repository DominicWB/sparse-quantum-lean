import TimeDependentHamiltonianLowerBound.Constant
import TimeDependentExtensions.Hamiltonian.Theorem
import SparseLowerBounds.Hamiltonian.ReleaseAccess
import ODELowerBoundExtensions.Release.Registers

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The released time-dependent oracles on constant data are Boolean-implementable

The time-dependent access model of Theorem `hs:thm:time` (equation `hs:eq:timeaccess`): one
query applies the coherent sampled-time oracle `∑_r |r⟩⟨r| ⊗ O_r`. The released simulators
call it through the physical oracle families

* `SparseHamiltonian.TimeDependent.oracle D γ η t ε` (uniform mesh, `M` slots) and
* `TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε` (general meshes and integrable
  paths, `N` slots),

both abbreviations of `AlignedMultiOracleProgram.oracle (TimeDependent.Sampled.oracle D T d)`
for a slot count `T` and a degree `d`. Unfolded, for every label `l` and input `x`:

* `AlignedMultiOracleProgram.oracle F l x = WeightedClock.diagonal (fun _ : Bool => F l x)`
  (clean-output alignment spectator);
* `Sampled.oracle D T d = NativeWholeProgramActive.oracle (C := PUnit) (sampledOracle D) T d`,
  the native-masked layer on `ActiveRegisterLayout.Label PUnit T d` (control, dummy and
  reference registers as spectators);
* `sampledOracle D = timeOracle (NativeCayleyProgram.oracle D)`, the time register.

On constant data the time register is an untouched spectator (`sampledOracle_constData`), so
every label is again exactly one call of the native primitive `oracles D l` of the same
label, with spectators and fixed relabellings.

**Normal form.** In terms of the released spectator wrappers
`ODELowerBoundExtensions.Release.IsWrap` (`W A = U⁻¹ (1_Ω ⊗ A) U` for one fixed isometric
identification `U`): the coherent sampled-time oracle of constant data is `timeWrap` of the
native primitive and the aligned family is `alignedWrap` of it (`sampled_eq_wrap`,
`aligned_eq_wrap`, by `rfl`), both wrappers (`isWrap_timeWrap`, `isWrap_alignedWrap`). Hence
there are a finite spectator register `Ω` and a fixed isometric identification `U` of the
physical workspace with `ℂ^Ω ⊗ NSpace` such that every label is
`U⁻¹ (1_Ω ⊗ oracles D l x) U = U⁻¹ (specOracles Ω D l x) U` (`sampled_normal_form`,
`aligned_normal_form`, and for the released families `uniform_normal_form`,
`mesh_normal_form`): on constant data the released time-dependent oracles are exactly the
time-independent native primitives acting with untouched spectator registers.

**Boolean certificates.** The released Boolean certificates of the time-independent release
bridge (`SparseLowerBounds.Hamiltonian.HsRelease`) therefore pass to the time-dependent families
with the **same** per-label costs:

* `timeCayleyAccess`: the coherent sampled-time oracle (`spectatorAccess` with the spectator
  `Fin M` after `cayleyAccess`);
* `sampledAccess`: the active layer `Sampled.oracle (constData D M) T d`
  (`nativeMaskedAccess`);
* `alignedAccess`: the aligned family, for every slot count `T` and degree `d`; its instances
  `uniformAccess` (`TimeDependent.oracle`) and `meshAccess`
  (`TimeDependentExtensions.Hamiltonian.oracle`) hold by definition.

For the three hard families of Theorem `hsl:thm:main` (`timeData`, `mixedMainData`,
`precisionMainData`) with the native certificates `searchAccess`, `scalarAccess`
(`hardCost`: `2` per value call, `0` per location call): `timeSampledAccess`,
`mixedSampledAccess`, `precisionSampledAccess`, and in the form of the hypotheses of the
general family lemmas `time_sampled_implementsOn`, `mixed_sampled_implementsOn`,
`precision_sampled_implementsOn`.
-/

namespace TimeDependentHamiltonianLowerBound

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseLowerBounds SparseLowerBounds.Hamiltonian HsRelease
open scoped InnerProduct InnerProductSpace

/-! ### Normal form -/

section Normal

open ODELowerBoundExtensions.Release (IsWrap isWrap_spectator)

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s : ℕ}

/-- The fixed wrapper of the released coherent sampled-time oracle on constant data around one
native primitive: the native Cayley-layout layers (fixed flattening
`NativeSparseMaskedAccess.layout`, control, dummy and reference spectators, dilation branch,
`NativeDilationLayout.layout`) and the spectator time register `Fin M`. -/
def timeWrap (N Z : Type) [Fintype N] [DecidableEq N] [Fintype Z] (M : ℕ)
    (A : SparseFlagEmbedding.Space (N × N) Z →L[ℂ] SparseFlagEmbedding.Space (N × N) Z) :
    EuclideanSpace ℂ (Fin M × NativeCayleyProgram.Basis N Z) →L[ℂ]
      EuclideanSpace ℂ (Fin M × NativeCayleyProgram.Basis N Z) :=
  LookupFromBasisOracle.spectator (S := Fin M)
    ((NativeDilationLayout.layout (B := NativeSparseMaskedAccess.Basis N Z)).conjStarAlgEquiv
      (MaskedProgram.masked (fun _ : Bool => true)
        (LookupFromBasisOracle.spectator
          (S := (Bool × NativeSparseMaskedAccess.Basis N Z) × NativeSparseMaskedAccess.Basis N Z)
          ((NativeSparseMaskedAccess.layout (n := N) (Z := Z)).conjStarAlgEquiv A))))

/-- The fixed wrapper of the released aligned physical family on constant data: `timeWrap`,
then the control, dummy and reference spectators of the active layer, the chronological cells
`ActiveRegisterLayout.Label PUnit T d` and the clean-output alignment spectator `Bool`. -/
def alignedWrap (N Z : Type) [Fintype N] [DecidableEq N] [Fintype Z] (M T d : ℕ)
    (A : SparseFlagEmbedding.Space (N × N) Z →L[ℂ] SparseFlagEmbedding.Space (N × N) Z) :
    CleanOutputAlignment.Double (TimeDependent.Sampled.Physical N Z M T d) →L[ℂ]
      CleanOutputAlignment.Double (TimeDependent.Sampled.Physical N Z M T d) :=
  WeightedClock.diagonal (fun _ : Bool =>
    MaskedProgram.masked (fun _ : ActiveRegisterLayout.Label PUnit.{1} T d => true)
      (LookupFromBasisOracle.spectator
        (S := (Bool × (Fin M × NativeCayleyProgram.Basis N Z)) ×
          (Fin M × NativeCayleyProgram.Basis N Z))
        (timeWrap N Z M A)))

/-- `timeWrap` consists of spectators and fixed relabellings only. -/
theorem isWrap_timeWrap (N Z : Type) [Fintype N] [DecidableEq N] [Fintype Z] (M : ℕ) :
    IsWrap (timeWrap N Z M) :=
  ((((isWrap_spectator _ _).precomp (NativeSparseMaskedAccess.layout (n := N) (Z := Z))).masked
    Bool).conj (NativeDilationLayout.layout (B := NativeSparseMaskedAccess.Basis N Z))).spectator
      (S := Fin M)

/-- `alignedWrap` consists of spectators and fixed relabellings only. -/
theorem isWrap_alignedWrap (N Z : Type) [Fintype N] [DecidableEq N] [Fintype Z] (M T d : ℕ) :
    IsWrap (alignedWrap N Z M T d) :=
  (((isWrap_timeWrap N Z M).spectator
    (S := (Bool × (Fin M × NativeCayleyProgram.Basis N Z)) ×
      (Fin M × NativeCayleyProgram.Basis N Z))).masked
    (ActiveRegisterLayout.Label PUnit.{1} T d)).diagonalConst Bool

/-- The coherent sampled-time oracle of constant data is `timeWrap` of the native
primitive. -/
theorem sampled_eq_wrap (D : Data X N Z s) (M : ℕ) (l : Query) (x : X) :
    TimeDependent.sampledOracle (constData D M) l x = timeWrap N Z M (oracles D l x) := by
  cases l <;> rfl

/-- The aligned physical family of constant data is `alignedWrap` of the native primitive. -/
theorem aligned_eq_wrap (D : Data X N Z s) (M T d : ℕ) (l : Query) (x : X) :
    AlignedMultiOracleProgram.oracle (TimeDependent.Sampled.oracle (constData D M) T d) l x =
      alignedWrap N Z M T d (oracles D l x) := by
  cases l <;> rfl

/-- **Normal form of the coherent sampled-time oracle of constant data** (eq.
`hs:eq:timeaccess`): there are a finite spectator register `Ω` and a fixed isometric
identification `U` with `∑_r |r⟩⟨r| ⊗ O_r = U⁻¹ (1_Ω ⊗ oracles D l x) U` for every label and
input. -/
theorem sampled_normal_form (D : Data X N Z s) (M : ℕ) :
    ∃ (Ω : Type) (_ : Fintype Ω)
      (U : EuclideanSpace ℂ (Fin M × NativeCayleyProgram.Basis N Z) ≃ₗᵢ[ℂ]
        Joint Ω (SparseFlagEmbedding.Space (N × N) Z)),
      ∀ l x, TimeDependent.sampledOracle (constData D M) l x =
        U.symm.conjStarAlgEquiv (specOracles Ω D l x) := by
  obtain ⟨Ω, _, U, hU⟩ := isWrap_timeWrap N Z M
  exact ⟨Ω, inferInstance, U, fun l x => (sampled_eq_wrap D M l x).trans (hU _)⟩

/-- **Normal form of the released time-dependent physical family on constant data**: for every
number `M` of samples, slot count `T` and degree `d` there are a finite spectator register `Ω`
and a fixed isometric identification `U` of the physical workspace with `ℂ^Ω ⊗ NSpace` such
that every label is `U⁻¹ (1_Ω ⊗ oracles D l x) U`, one call of the time-independent native
primitive of the same label with untouched spectators. -/
theorem aligned_normal_form (D : Data X N Z s) (M T d : ℕ) :
    ∃ (Ω : Type) (_ : Fintype Ω)
      (U : CleanOutputAlignment.Double (TimeDependent.Sampled.Physical N Z M T d) ≃ₗᵢ[ℂ]
        Joint Ω (SparseFlagEmbedding.Space (N × N) Z)),
      ∀ l x, AlignedMultiOracleProgram.oracle (TimeDependent.Sampled.oracle (constData D M) T d)
          l x = U.symm.conjStarAlgEquiv (specOracles Ω D l x) := by
  obtain ⟨Ω, _, U, hU⟩ := isWrap_alignedWrap N Z M T d
  exact ⟨Ω, inferInstance, U, fun l x => (aligned_eq_wrap D M T d l x).trans (hU _)⟩

/-- **Normal form of the uniform-mesh released family** `TimeDependent.oracle` on constant
data (any schedule). -/
theorem uniform_normal_form (D : Data X N Z s) (M : ℕ) (γ η t ε : ℝ) :
    ∃ (Ω : Type) (_ : Fintype Ω)
      (U : TimeDependent.Workspace N Z s M γ η t ε ≃ₗᵢ[ℂ]
        Joint Ω (SparseFlagEmbedding.Space (N × N) Z)),
      ∀ l x, TimeDependent.oracle (constData D M) γ η t ε l x =
        U.symm.conjStarAlgEquiv (specOracles Ω D l x) :=
  aligned_normal_form D M M _

/-- **Normal form of the general-mesh released family**
`TimeDependentExtensions.Hamiltonian.oracle` on constant data (any slot count and
schedule). -/
theorem mesh_normal_form (D : Data X N Z s) (M Nsl : ℕ) (γ η T ε : ℝ) :
    ∃ (Ω : Type) (_ : Fintype Ω)
      (U : TimeDependentExtensions.Hamiltonian.Workspace N Z s M Nsl γ η T ε ≃ₗᵢ[ℂ]
        Joint Ω (SparseFlagEmbedding.Space (N × N) Z)),
      ∀ l x, TimeDependentExtensions.Hamiltonian.oracle (constData D M) Nsl γ η T ε l x =
        U.symm.conjStarAlgEquiv (specOracles Ω D l x) :=
  aligned_normal_form D M Nsl _

end Normal

/-! ### Certificates for constant data -/

section Certificates

variable {I : Type*} [Fintype I] {X : Type*} {y : X → I → Bool}
variable {N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

/-- **The coherent sampled-time oracle of constant data**: the native Cayley-layout
certificate with the untouched spectator time register `Fin M` (`sampledOracle_constData`),
same Boolean costs. -/
def timeCayleyAccess (D : Data X N Z s) {w : Query → ℕ} (A : PhaseAccess I y (oracles D) w)
    (M : ℕ) : PhaseAccess I y (TimeDependent.sampledOracle (constData D M)) w :=
  (spectatorAccess (cayleyAccess D A) (Fin M)).congr fun l x =>
    (sampledOracle_constData D M l x).symm

/-- **The active layer of constant data** (`TimeDependent.Sampled.oracle`, any slot count `T`
and degree `d`): the sampled-time certificate in every branch of the native-masked layer, same
Boolean costs. -/
def sampledAccess (D : Data X N Z s) {w : Query → ℕ} (A : PhaseAccess I y (oracles D) w)
    (M T d : ℕ) : PhaseAccess I y (TimeDependent.Sampled.oracle (constData D M) T d) w :=
  nativeMaskedAccess (ActiveRegisterLayout.Label PUnit.{1} T d) (timeCayleyAccess D A M)

/-- **The aligned physical family of constant data** (both sectors of the clean-output
alignment spectator `Bool`), same Boolean costs. -/
def alignedAccess (D : Data X N Z s) {w : Query → ℕ} (A : PhaseAccess I y (oracles D) w)
    (M T d : ℕ) :
    PhaseAccess I y
      (AlignedMultiOracleProgram.oracle (TimeDependent.Sampled.oracle (constData D M) T d)) w :=
  ((sampledAccess D A M T d).spectate Bool).congr
    fun _ _ => (SparseLowerBounds.Helpers.Adaptive.Access.diagonal_const_eq_fiber _).symm

/-- **The uniform-mesh released family** `TimeDependent.oracle (constData D M) γ η t ε` (any
schedule), same Boolean costs. -/
def uniformAccess (D : Data X N Z s) {w : Query → ℕ} (A : PhaseAccess I y (oracles D) w)
    (M : ℕ) (γ η t ε : ℝ) :
    PhaseAccess I y (TimeDependent.oracle (constData D M) γ η t ε) w :=
  alignedAccess D A M M _

/-- **The general-mesh released family**
`TimeDependentExtensions.Hamiltonian.oracle (constData D M) N γ η T ε` (any slot count and
schedule), same Boolean costs. -/
def meshAccess (D : Data X N Z s) {w : Query → ℕ} (A : PhaseAccess I y (oracles D) w)
    (M Nsl : ℕ) (γ η T ε : ℝ) :
    PhaseAccess I y (TimeDependentExtensions.Hamiltonian.oracle (constData D M) Nsl γ η T ε) w :=
  alignedAccess D A M Nsl _

end Certificates

/-- The aligned physical family is unitary on every label and input. -/
theorem aligned_oracle_unitary {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] [DecidableEq Z] {s M : ℕ} (D : Data (X × Fin M) N Z s) (T d : ℕ)
    (l : Query) (x : X) :
    IsUnitary (AlignedMultiOracleProgram.oracle (TimeDependent.Sampled.oracle D T d) l x) :=
  CoherentQuerySchedule.oracle_unitary _ (TimeDependent.Sampled.oracle_unitary D T d) l x

/-! ### The three hard families -/

section Hard

variable {τ ε : ℝ} {s : ℕ}

/-- The workspace of the aligned family on the time family (`T` slots, degree `d`). -/
abbrev TimeWork (τ : ℝ) (s M T d : ℕ) : Type :=
  CleanOutputAlignment.Double (TimeDependent.Sampled.Physical (SearchIndex (timeN τ) (hsMu s) s)
    (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) M T d)

/-- The workspace of the aligned family on the mixed family. -/
abbrev MixedWork (τ ε : ℝ) (s M T d : ℕ) : Type :=
  CleanOutputAlignment.Double (TimeDependent.Sampled.Physical (SearchIndex (precN τ ε) (hsMu s) s)
    (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) M T d)

/-- The workspace of the aligned family on the precision family. -/
abbrev PrecisionWork (τ ε : ℝ) (s M T d : ℕ) : Type :=
  CleanOutputAlignment.Double (TimeDependent.Sampled.Physical (ScalarIndex (precN τ ε) s)
    (Word (scalarBits (precN τ ε) s τ)) M T d)

/-- Time family (`timeData`): the certificate of the aligned family on the constant data. -/
def timeSampledAccess (hs : 32 ≤ s) (M T d : ℕ) :
    PhaseAccess (Fin (timeN τ) × Fin (2 ^ hsMu s)) oneHotPattern
      (AlignedMultiOracleProgram.oracle
        (TimeDependent.Sampled.oracle (constData (timeData τ s hs) M) T d)) hardCost :=
  alignedAccess _ (searchAccess (one_le_hsMu hs) (two_mul_hsM_le hs)) M T d

/-- Mixed family (`mixedMainData`): the certificate of the aligned family on the constant
data. -/
def mixedSampledAccess (hs : 32 ≤ s) (M T d : ℕ) :
    PhaseAccess (Fin (precN τ ε) × Fin (2 ^ hsMu s)) oneHotPattern
      (AlignedMultiOracleProgram.oracle
        (TimeDependent.Sampled.oracle (constData (mixedMainData τ ε s hs) M) T d)) hardCost :=
  alignedAccess _ (searchAccess (one_le_hsMu hs) (two_mul_hsM_le hs)) M T d

/-- Precision family (`precisionMainData`): the certificate of the aligned family on the
constant data. -/
def precisionSampledAccess (hs : 32 ≤ s) (M T d : ℕ) :
    PhaseAccess (Fin (precN τ ε)) bitPattern
      (AlignedMultiOracleProgram.oracle
        (TimeDependent.Sampled.oracle (constData (precisionMainData τ ε s hs) M) T d)) hardCost :=
  alignedAccess _ (scalarAccess (by omega)) M T d

/-- **The released time-dependent family on the constant time family is Boolean-implementable**
(manuscript: two Boolean queries per value call, location calls free): for every mesh size
`M`, slot count `T` and degree `d`, every label `l` of
`AlignedMultiOracleProgram.oracle (Sampled.oracle (constData (timeData τ s hs) M) T d)` (in
particular of `TimeDependent.oracle` and `TimeDependentExtensions.Hamiltonian.oracle` on the
constant data) is implemented on one isometric encoding by at most `hardCost l` queries of the
one-hot Boolean oracle. -/
theorem time_sampled_implementsOn (hs : 32 ≤ s) (M T d : ℕ) :
    (timeSampledAccess (τ := τ) hs M T d).enc† ∘L (timeSampledAccess (τ := τ) hs M T d).enc = 1 ∧
      ∀ l, EncodedOracle.ImplementsOn (oneHotOracle (timeSampledAccess (τ := τ) hs M T d).fam)
        (AlignedMultiOracleProgram.oracle
          (TimeDependent.Sampled.oracle (constData (timeData τ s hs) M) T d) l)
        (timeSampledAccess (τ := τ) hs M T d).enc (hardCost l) :=
  ⟨(timeSampledAccess hs M T d).enc_isometry, (timeSampledAccess hs M T d).implementsOn_oneHot⟩

/-- **The released time-dependent family on the constant mixed family is
Boolean-implementable**: as `time_sampled_implementsOn`, for `mixedMainData`. -/
theorem mixed_sampled_implementsOn (hs : 32 ≤ s) (M T d : ℕ) :
    (mixedSampledAccess (τ := τ) (ε := ε) hs M T d).enc† ∘L
        (mixedSampledAccess (τ := τ) (ε := ε) hs M T d).enc = 1 ∧
      ∀ l, EncodedOracle.ImplementsOn
        (oneHotOracle (mixedSampledAccess (τ := τ) (ε := ε) hs M T d).fam)
        (AlignedMultiOracleProgram.oracle
          (TimeDependent.Sampled.oracle (constData (mixedMainData τ ε s hs) M) T d) l)
        (mixedSampledAccess (τ := τ) (ε := ε) hs M T d).enc (hardCost l) :=
  ⟨(mixedSampledAccess hs M T d).enc_isometry, (mixedSampledAccess hs M T d).implementsOn_oneHot⟩

/-- **The released time-dependent family on the constant precision family is
Boolean-implementable**: as `time_sampled_implementsOn`, for `precisionMainData`, with the bit
oracle of the `precN τ ε` sign bits. -/
theorem precision_sampled_implementsOn (hs : 32 ≤ s) (M T d : ℕ) :
    (precisionSampledAccess (τ := τ) (ε := ε) hs M T d).enc† ∘L
        (precisionSampledAccess (τ := τ) (ε := ε) hs M T d).enc = 1 ∧
      ∀ l, EncodedOracle.ImplementsOn
        (bitOracle (precisionSampledAccess (τ := τ) (ε := ε) hs M T d).fam)
        (AlignedMultiOracleProgram.oracle
          (TimeDependent.Sampled.oracle (constData (precisionMainData τ ε s hs) M) T d) l)
        (precisionSampledAccess (τ := τ) (ε := ε) hs M T d).enc (hardCost l) :=
  ⟨(precisionSampledAccess hs M T d).enc_isometry,
    (precisionSampledAccess hs M T d).implementsOn_bit⟩

end Hard

end

end TimeDependentHamiltonianLowerBound
