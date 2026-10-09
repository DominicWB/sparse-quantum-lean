import SparseLowerBounds.Adaptive.Access
import SparseLowerBounds.Hamiltonian.Statements

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Helper: Boolean phase-oracle access certificates for any hidden input

For `Hamiltonian/ReleaseAccess`.
`Adaptive.Access.BooleanAccess` packages a Boolean implementation of a whole
labelled family for one-hot hidden inputs `Fin n → Fin m` only. The
Hamiltonian-simulation lower bounds use two Boolean oracles (manuscript lines
2143-2146 and 2283-2289), both phase oracles `Q.phase (y x)` of a fixed
projection family `Q` (`Query/PhaseOracle`) at a pattern `y x : I → Bool` of
the hidden input `x`:

* search (time and mixed) families: `x = j : Fin n → Fin m`,
  `y = oneHotPattern` (`(k, a) ↦ [j k = a]`, definitionally
  `oneHotBits`), so `Q.phase (y j) = oneHotOracle Q j` by definition;
* precision family: `x : Fin n → Bool`, `y = bitPattern` (`y x = x`), so
  `Q.phase (y x) = bitOracle Q x` by definition.

`PhaseAccess I y O w` is the common generalisation: a Boolean workspace, a
projection family over `I`, one isometric encoding of `O`'s workspace and an
implementation of every label `l` by at most `w l` Boolean queries
`x ↦ fam.phase (y x)` (`EncodedOracle.ImplementsOn`). It survives the release's
wrappers at the **same** cost, exactly as `BooleanAccess`:

* `PhaseAccess.conj`: a fixed unitary relabelling of the logical workspace
  (`Adaptive.Access.implementsOn_conj`);
* `PhaseAccess.spectate`: an untouched spectator register `ℂ^Ω`
  (`Adaptive.Access.implementsOn_spectate` and `phase_spectate`:
  the phase oracle of `Q.spectate Ω` is `1_Ω ⊗ Q.phase y`);
* `PhaseAccess.congr`, `PhaseAccess.mono`.

`implementsOn_oneHot` and `implementsOn_bit` read a certificate back in the
form the general family lemmas (`time_general`, `mixed_general`,
`precision_general`, `*_herald_general`) take; `toBooleanAccess` turns a
one-hot certificate into a `BooleanAccess`.

Proof notes: `phase_spectate` from `PhaseCircuit.phase_eq_hitProj` and
`PhaseCircuit.hitProj_spectate_apply` (as `Adaptive.Access.oneHotOracle_spectate`);
`implementsOn_oneHot` and `implementsOn_bit` are `A.impl l` up to unfolding
`oneHotOracle` / `bitOracle`.
-/

namespace SparseLowerBounds.Hamiltonian.HsRelease

noncomputable section
set_option autoImplicit false
open SparseHamiltonian OracleCircuit Adaptive.Access
open scoped InnerProduct InnerProductSpace

variable {K K₂ : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]

/-- The one-hot pattern `(k, a) ↦ [j k = a]` of `n` one-hot strings of length
`m` (definitionally `oneHotBits`): `Q.phase (oneHotPattern j)` is
`oneHotOracle Q j` by definition. -/
abbrev oneHotPattern {n m : ℕ} : (Fin n → Fin m) → Fin n × Fin m → Bool :=
  fun j ka => decide (j ka.1 = ka.2)

/-- The bit pattern `y x = x` of an `n`-bit string: `Q.phase (bitPattern x)` is
`bitOracle Q x` by definition. -/
abbrev bitPattern {n : ℕ} : (Fin n → Bool) → Fin n → Bool := fun x => x

/-- The phase oracle of the spectated family is the spectated phase oracle:
`(1_Ω ⊗ Q).phase y = 1_Ω ⊗ Q.phase y` (any pattern `y`). -/
theorem phase_spectate {I : Type*} [Fintype I] (Ω : Type*) [Fintype Ω] (Q : ProjFamily K I)
    (y : I → Bool) : (Q.spectate Ω).phase y = Joint.fiber (fun _ : Ω => Q.phase y) := by
  ext Ψ ω
  rw [Joint.fiber_apply, PhaseCircuit.phase_eq_hitProj, PhaseCircuit.phase_eq_hitProj]
  change Ψ ω - ((2 : ℂ) • PhaseCircuit.hitProj (Q.spectate Ω) y Ψ) ω =
    Ψ ω - (2 : ℂ) • PhaseCircuit.hitProj Q y (Ψ ω)
  rw [PiLp.smul_apply, PhaseCircuit.hitProj_spectate_apply]

/-- **A Boolean phase-oracle access certificate** for a labelled family `O`
over hidden inputs `X`, with Boolean pattern `y : X → I → Bool`: a Boolean
workspace with a projection family over `I` (phase form, `ProjFamily`),
one isometric encoding of `O`'s workspace, and an implementation of every
label `l` by at most `w l` queries to `x ↦ fam.phase (y x)`. For
`y = oneHotPattern` this is `Adaptive.Access.BooleanAccess` (`toBooleanAccess`). -/
structure PhaseAccess (I : Type*) [Fintype I] {X : Type*} (y : X → I → Bool) {L : Type*}
    (O : L → X → K →L[ℂ] K) (w : L → ℕ) where
  /-- The Boolean workspace. -/
  Space : Type
  [instNormed : NormedAddCommGroup Space]
  [instInner : InnerProductSpace ℂ Space]
  [instComplete : CompleteSpace Space]
  /-- The Boolean oracle's projection family, in phase form. -/
  fam : ProjFamily Space I
  /-- The fixed isometric encoding of `O`'s workspace. -/
  enc : K →L[ℂ] Space
  enc_isometry : enc† ∘L enc = 1
  /-- Every label costs at most `w l` Boolean queries. -/
  impl : ∀ l, EncodedOracle.ImplementsOn (fun x => fam.phase (y x)) (O l) enc (w l)

attribute [instance] PhaseAccess.instNormed PhaseAccess.instInner PhaseAccess.instComplete

namespace PhaseAccess

variable {I : Type*} [Fintype I] {X : Type*} {y : X → I → Bool} {L : Type*}

/-- A certificate from explicit data on a workspace in `Type`. -/
def ofImplementsOn {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    (P : ProjFamily B I) (E : K →L[ℂ] B) (hE : E† ∘L E = 1) {O : L → X → K →L[ℂ] K}
    {w : L → ℕ} (h : ∀ l, EncodedOracle.ImplementsOn (fun x => P.phase (y x)) (O l) E (w l)) :
    PhaseAccess I y O w where
  Space := B
  fam := P
  enc := E
  enc_isometry := hE
  impl := h

/-- Transport along a fixed unitary relabelling `V` of the logical workspace
(`Adaptive.Access.implementsOn_conj`): encoding `E ∘ V⁻¹`, same Boolean oracle
and costs. -/
def conj {O : L → X → K →L[ℂ] K} {w : L → ℕ} (A : PhaseAccess I y O w) (V : K ≃ₗᵢ[ℂ] K₂) :
    PhaseAccess I y (fun l x => V.conjStarAlgEquiv (O l x)) w where
  Space := A.Space
  fam := A.fam
  enc := A.enc ∘L V.symm.toLinearIsometry.toContinuousLinearMap
  enc_isometry := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc _ A.enc, A.enc_isometry, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp]
    exact LinearIsometry.adjoint_comp_self _
  impl l := implementsOn_conj V (A.impl l)

/-- Transport to an untouched spectator register `ℂ^Ω`
(`Adaptive.Access.implementsOn_spectate`, `phase_spectate`): Boolean family
`1_Ω ⊗ fam`, encoding `1_Ω ⊗ enc`, same costs. -/
def spectate {O : L → X → K →L[ℂ] K} {w : L → ℕ} (A : PhaseAccess I y O w)
    (Ω : Type) [Fintype Ω] :
    PhaseAccess I y (fun l x => Joint.fiber (fun _ : Ω => O l x)) w where
  Space := Joint Ω A.Space
  fam := A.fam.spectate Ω
  enc := jointMap Ω A.enc
  enc_isometry := jointMap_isometry Ω A.enc A.enc_isometry
  impl l := by
    have hQ : (fun x => (A.fam.spectate Ω).phase (y x)) =
        fun x => Joint.fiber (fun _ : Ω => A.fam.phase (y x)) :=
      funext fun x => phase_spectate Ω A.fam (y x)
    rw [hQ]
    exact implementsOn_spectate Ω (A.impl l)

/-- Pointwise equal families have the same certificate. -/
def congr {O O' : L → X → K →L[ℂ] K} {w : L → ℕ} (A : PhaseAccess I y O w)
    (h : ∀ l x, O l x = O' l x) : PhaseAccess I y O' w where
  Space := A.Space
  fam := A.fam
  enc := A.enc
  enc_isometry := A.enc_isometry
  impl l := (A.impl l).congr (h l)

/-- A certificate for larger costs. -/
def mono {O : L → X → K →L[ℂ] K} {w v : L → ℕ} (A : PhaseAccess I y O w)
    (h : ∀ l, w l ≤ v l) : PhaseAccess I y O v where
  Space := A.Space
  fam := A.fam
  enc := A.enc
  enc_isometry := A.enc_isometry
  impl l := (A.impl l).mono (h l)

/-! ### Reading a certificate back -/

/-- A one-hot certificate (`y = oneHotPattern`) in the form of the search-family
lemmas: every label is `ImplementsOn (oneHotOracle fam)`. -/
theorem implementsOn_oneHot {n m : ℕ} {O : L → (Fin n → Fin m) → K →L[ℂ] K} {w : L → ℕ}
    (A : PhaseAccess (Fin n × Fin m) oneHotPattern O w) (l : L) :
    EncodedOracle.ImplementsOn (oneHotOracle A.fam) (O l) A.enc (w l) :=
  A.impl l

/-- A bit certificate (`y = bitPattern`) in the form of the precision-family lemmas:
every label is `ImplementsOn (bitOracle fam)`. -/
theorem implementsOn_bit {n : ℕ} {O : L → (Fin n → Bool) → K →L[ℂ] K} {w : L → ℕ}
    (A : PhaseAccess (Fin n) bitPattern O w) (l : L) :
    EncodedOracle.ImplementsOn (bitOracle A.fam) (O l) A.enc (w l) :=
  A.impl l

/-- A one-hot certificate is an `Adaptive.Access.BooleanAccess`. -/
def toBooleanAccess {n m : ℕ} {O : L → (Fin n → Fin m) → K →L[ℂ] K} {w : L → ℕ}
    (A : PhaseAccess (Fin n × Fin m) oneHotPattern O w) : BooleanAccess n m O w :=
  BooleanAccess.ofImplementsOn A.fam A.enc A.enc_isometry A.implementsOn_oneHot

end PhaseAccess

end

end SparseLowerBounds.Hamiltonian.HsRelease
end
