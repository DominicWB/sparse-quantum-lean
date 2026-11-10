import ODELowerBoundExtensions.Release.Model
import AdaptiveHamiltonianLowerBound.Theorem

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Lemma `odel:lem:herald` for retry protocols: the `g = 1` families

Manuscript: eq. `odel:eq:hsbound` and Lemma `odel:lem:herald`. The `g = 1` families of
`SparseLowerBounds/ODE/Precision` (`timeFamilyAt`, `mixedFamilyAt`, `precisionFamilyAt`: the hard
Hamiltonian data read as homogeneous constant-coefficient ODEs with generator `iH`, `D = 0`,
`‖x(T)‖ = 1`) force the per-family bounds of eqs. `hsl:eq:timelower`, `hsl:eq:mixrbound`,
`hsl:eq:rbound` and `hsl:eq:failedmix` on retry protocols, with the constants of the Hamiltonian
lower bound. The combined form `c₀ (√s τ + √(sτr) + r)` of eq. `odel:eq:hsbound` and the fourth
sentence of `odel:thm:combined` are `herald_max_retry`, `herald_witness_retry` and
`precision_terms_witness_retry` in `Release/Theorem` (they use `forces_or_of_max_retry`).

Route. A retry protocol `p` is the adaptive protocol `Tree.final p` of
`SparseLinearSystems.Protocol.Tree` (no test runs), whose success mass, conditional density and
worst-case cost are those of `p` by definition. The sampled-time access of `hamFamily D` is the
spectated native access `specOracles (ι × Fin 1) D` (`access_hamFamily`), whose labels are
admissible for `D` with the value-query weight
(`AdaptiveHamiltonianLowerBound.Access.admissible_specOracles`, the hard data have
input-independent locators). The adaptive Hamiltonian lower bound
(`AdaptiveHamiltonianLowerBound.time_tree`, `mixed_tree`, `precision_tree`, heralded accuracy in
the form `DensityAccurate`) then gives the bounds, since accuracy for `x(T)/‖x(T)‖` is accuracy for
the unit vector `x(T) = e^{-iτH_x} x₀` (`hamFamily_solves`). The total count is at least the value
count (`worstCost_mono`).
-/

namespace ODELowerBoundExtensions.Release

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open scoped InnerProduct InnerProductSpace

variable {τ ε : ℝ} {s : ℕ}

section Transfer

variable {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s' : ℕ}
  (D : Data X N Z s') (T : ℝ) (hT : 0 ≤ T) (x₀ : EuclideanSpace ℂ N)

/-- **Retry-protocol transfer** (the retry analogue of `SparseLowerBounds.ODE.forces_of_spec`, Lemma
`odel:lem:herald`): if every adaptive protocol over an oracle family whose labels are admissible for
`D` with the value-query weight, heralding success with probability `≥ 2/3` and `ε`-accurate for
`e^{-iTH_x} x₀`, makes at least `b` value queries in the worst case, then `hamFamily D T x₀`
retry-forces `b`. The sampled-time access is the spectated access `specOracles (ι × Fin 1) D`
(`access_hamFamily`), admissible when the locators of `D` are input-independent
(`Access.admissible_specOracles`); a retry protocol is the adaptive protocol `Tree.final` with the
same success mass, conditional density and worst-case cost; accuracy for `x(T)/‖x(T)‖` is accuracy
for the unit vector `x(T) = e^{-iTH_x} x₀`; and the total count is at least the value count
(`worstCost_mono`). -/
theorem retryForces_of_tree {b : ℝ} (hH : ∀ x, (D.matrix x).IsHermitian) (hx₀ : ‖x₀‖ = 1)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x')
    (hb : ∀ (ι : Type) [Fintype ι] (E G : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
      [CompleteSpace G] (O : Query → X → Workspace ι N Z 1 →L[ℂ] Workspace ι N Z 1),
      (∀ q, AdaptiveHamiltonianLowerBound.Access.Admissible D (O q) (valueWeight q)) →
      ∀ (P : SparseLinearSystems.Protocol.Tree O E E) (e : E →L[ℂ] SysGarb N G), e† ∘L e = 1 →
      (∀ x, 2 / 3 ≤ P.successMass x) →
      (∀ x, DensityAccurate e (P.conditionalDensity x)
        (Hamiltonian.evolve (D.matrix x) T x₀) ε) →
      b ≤ P.worstCost valueWeight) :
    RetryForces (hamFamily D T hT x₀) ε b := by
  intro ι _ E G _ _ _ _ _ _ _ A
  have hO : ∀ q, AdaptiveHamiltonianLowerBound.Access.Admissible D
      ((hamFamily D T hT x₀).access ι q) (valueWeight q) := by
    intro q
    have hq : (hamFamily D T hT x₀).access ι q = specOracles (ι × Fin 1) D q :=
      funext fun x => access_hamFamily D T hT x₀ ι q x
    rw [hq]
    exact AdaptiveHamiltonianLowerBound.Access.admissible_specOracles (ι × Fin 1) D hrow hcol q
  have hacc : ∀ x, DensityAccurate A.readout (A.prot.conditionalDensity x)
      (Hamiltonian.evolve (D.matrix x) T x₀) ε := by
    intro x
    have h := A.accurate x _ (hamFamily_solves D T hT x₀ x)
    have hu : ODEStateNormalization.unitDirection (Hamiltonian.evolve (D.matrix x) T x₀) =
        Hamiltonian.evolve (D.matrix x) T x₀ := by
      rw [ODEStateNormalization.unitDirection, Hamiltonian.norm_evolve_apply (hH x), hx₀,
        inv_one, one_smul]
    rw [hamFamily_T, hu] at h
    exact h
  have h1 : b ≤ A.prot.worstCost valueWeight :=
    hb ι E G _ hO (.final A.prot) A.readout A.readout_isometry A.success hacc
  refine ⟨h1, h1.trans ?_⟩
  exact_mod_cast worstCost_mono A.prot fun q => by cases q <;> simp [valueWeight]

end Transfer

/-- **Lemma `odel:lem:herald` for retry protocols, time family** (eq. `hsl:eq:timelower`):
`Q ≥ c_T √s τ`, `c_T = log 2/(192π)`. -/
theorem time_forces_retry (h : HSRange τ s ε) :
    RetryForces (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) ε
      (cT * Real.sqrt s * τ) := by
  have hI := (hard_instances h).1
  have hA := AdaptiveHamiltonianLowerBound.Access.hardAccess_timeData τ s h.s_ge
  refine retryForces_of_tree _ _ _ _ hI.isHermitian (norm_searchInput _ _ _) hA.row_const
    hA.column_const ?_
  intro ι _ E G _ _ _ _ _ _ _ O hO P e he hsucc hacc
  exact AdaptiveHamiltonianLowerBound.time_tree h O valueWeight hO P e he hsucc hacc

/-- **Lemma `odel:lem:herald` for retry protocols, mixed family** (eq. `hsl:eq:mixrbound`): for
`L ≥ 64τ` and `s ≥ 64n/τ`, `Q ≥ (log 2/(384√2)) √(sτr)`. -/
theorem mixed_forces_retry (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) :
    RetryForces (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε
      (Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε)) := by
  have hI := (hard_instances h).2.1
  have hA := AdaptiveHamiltonianLowerBound.Access.hardAccess_mixedMainData τ ε s h.s_ge
  refine retryForces_of_tree _ _ _ _ hI.isHermitian (norm_searchInput _ _ _) hA.row_const
    hA.column_const ?_
  intro ι _ E G _ _ _ _ _ _ _ O hO P e he hsucc hacc
  exact AdaptiveHamiltonianLowerBound.mixed_tree h hL hs O valueWeight hO P e he hsucc hacc

/-- **Lemma `odel:lem:herald` for retry protocols, precision family** (eq. `hsl:eq:rbound`): for
`L ≥ 64τ`, `Q ≥ r/32`. -/
theorem precision_forces_retry (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) :
    RetryForces (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε
      (hsR τ ε / 32) := by
  have hI := (hard_instances h).2.2.1
  have hA := AdaptiveHamiltonianLowerBound.Access.hardAccess_precisionMainData τ ε s h.s_ge
  refine retryForces_of_tree _ _ _ _ hI.isHermitian (norm_scalarInput _ _) hA.row_const
    hA.column_const ?_
  intro ι _ E G _ _ _ _ _ _ _ O hO P e he hsucc hacc
  exact (AdaptiveHamiltonianLowerBound.precision_tree h hL O valueWeight hO P e he hsucc hacc).1

/-- **Lemma `odel:lem:herald` for retry protocols, precision family, small sparsity**
(eq. `hsl:eq:failedmix`): for `L ≥ 64τ` and `s < 64n/τ`, `Q ≥ √(sτr)/(64√2)`. -/
theorem precision_forces_sqrt_retry (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs' : (s : ℝ) < 64 * precN τ ε / τ) :
    RetryForces (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε
      (Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2)) := by
  have hI := (hard_instances h).2.2.1
  have hA := AdaptiveHamiltonianLowerBound.Access.hardAccess_precisionMainData τ ε s h.s_ge
  refine retryForces_of_tree _ _ _ _ hI.isHermitian (norm_scalarInput _ _) hA.row_const
    hA.column_const ?_
  intro ι _ E G _ _ _ _ _ _ _ O hO P e he hsucc hacc
  exact (AdaptiveHamiltonianLowerBound.precision_tree h hL O valueWeight hO P e he hsucc hacc).2
    hs'

end

end ODELowerBoundExtensions.Release
