import ManuscriptConformance.Defs
import ManuscriptConformance.Readout
import SparseLowerBounds.ODE.Theorem
import SparseLowerBounds.ODE.Uniqueness
import ODELowerBoundExtensions.Homogeneous.Theorem
import ODELowerBoundExtensions.Psd.Theorem

/-!
# Conformance: differential-equation lower bounds

Theorems `odel:thm:combined`, `odel:thm:joint` and `odel:thm:psd` and Proposition
`odel:rem:homogeneous`, in the manuscript's ODE lower-bound model (Section
`odel:sec:main`, before Theorem `odel:thm:combined`):

* **Input class** (`SparseLowerBounds.ODE.Family`, `Family.InClass η ḡ`). The dissipative
  equation `ẋ = A(t)x + b(t)`, `x(0) = x₀`, `0 ≤ t ≤ T`, `-A = D + iH`, `D ⪰ 0`, written with the
  negative generator `G = -A` (`ẋ = -G(t) x + b(t)`); piecewise constant with public breakpoints,
  as the
  manuscript's examples are; every row and column of every sample has at most `s` nonzeros and
  Euclidean norm at most `η`; `x(T) ≠ 0` and `g = B/‖x(T)‖ ≤ ḡ` with `B = ‖x₀‖ + ∫‖b‖`.
  `τ = Tη`; the lower bounds use `η = 1` and `T = τ`.
* **Access.** The coherent sampled-time native sparse access (value oracle and in-place
  locators, inverses included, time address coherent), with an untouched branch register `ι`;
  the initial state and the sources are public, and known state preparations are free.
* **Solvers** (`ForcesODE`, single programs without controlled calls or adaptivity; the
  adaptive forms are in `ManuscriptConformance.ODELowerAdaptive`). A program run on an input-independent initial vector of norm at
  most one, read through an isometry into system ⊗ garbage, with an input-independent herald
  projection `P`: success probability `‖PΦ‖² ≥ 2/3` on every input, and the conditional system
  state (`heraldedState`) within trace distance `ε` of the normalised solution
  `x(T)/‖x(T)‖`. Queries are counted in the worst case; both value queries and all matrix
  queries are bounded below.

The theorems are proved from `SparseLowerBounds.ODE.combined`, `joint_witness`,
`precision_terms_witness`, `ODELowerBoundExtensions.Homogeneous.hom_witness` and
`ODELowerBoundExtensions.Psd.psd`, whose solvers (`SparseLowerBounds.ODE.Solver`) state the
accuracy in the observable form `Readout.HeraldedAccurate` (`forcesODE_of_forces`).
-/

set_option autoImplicit false

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding SparseLowerBounds
open SparseLowerBounds.Hamiltonian SparseLowerBounds.ODE
open scoped InnerProduct InnerProductSpace ComplexOrder

set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

/-- **`F` forces `b` matrix queries at accuracy `ε`** (the single-program, uncontrolled,
non-adaptive part of the solver class of Section `odel:sec:main`; the adaptive class with
controlled calls is `AdaptiveODELowerBound.Model.TreeForces`): every program over the coherent sampled-time access of `F` with any branch
register `ι`, run on an input-independent initial vector of norm at most one, read through an
isometry into system ⊗ any garbage `G`, with an input-independent herald projection `P` that
succeeds with probability at least `2/3` on every input and whose conditional system state is
within trace distance `ε` of `x(T)/‖x(T)‖` for the solution `x` of every instance, makes at least
`b` value queries and at least `b` matrix queries. -/
def ForcesODE {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {K s : ℕ}
    (F : Family X N Z K s) (ε b : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : Type) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (p : MultiOracleCircuit.Program (F.access ι)) (φ₀ : Workspace ι N Z K)
    (e : Workspace ι N Z K →L[ℂ] SysGarb N G) (P : Workspace ι N Z K →L[ℂ] Workspace ι N Z K),
    ‖φ₀‖ ≤ 1 → e† ∘L e = 1 → IsStarProjection P →
    (∀ x, 2 / 3 ≤ ‖P (p.eval x φ₀)‖ ^ 2) →
    (∀ x sol, F.Solves x sol →
      TraceDistanceLE (heraldedState e P (p.eval x φ₀)) ((‖sol F.T‖⁻¹ : ℝ) • sol F.T) ε) →
    b ≤ p.labelCount .value ∧ b ≤ p.count

/-- **The package's solver class is contained in the manuscript's**: a family that forces `b`
for the package's solvers (observable-form heralded accuracy) forces `b` for every single-program,
uncontrolled, non-adaptive solver of the manuscript's class (`ForcesODE`). The class with
controlled calls and adaptivity is treated in `ManuscriptConformance.ODELowerAdaptive`. -/
theorem forcesODE_of_forces {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] {K s : ℕ} {F : Family X N Z K s} {ε b : ℝ} (h : F.Forces ε b) :
    ForcesODE F ε b := by
  intro ι _ G _ _ _ p φ₀ e P hφ he hP hsucc hacc
  have hpos : ∀ x, 0 < ‖P (p.eval x φ₀)‖ := by
    intro x
    rcases (norm_nonneg (P (p.eval x φ₀))).lt_or_eq with hlt | heq
    · exact hlt
    · have := hsucc x
      rw [← heq] at this
      norm_num at this
  exact h ι G
    { prog := p
      seed := φ₀
      seed_norm_le := hφ
      out := e
      out_isometry := he
      herald := P
      herald_proj := hP
      success := hsucc
      accurate := fun x sol hs => heraldedAccurate_of_traceDistanceLE hP (hpos x) (hacc x sol hs) }

/-- `ForcesODE` is monotone in the bound. -/
theorem ForcesODE.mono {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
    {K s : ℕ} {F : Family X N Z K s} {ε b b' : ℝ} (h : ForcesODE F ε b) (hb : b' ≤ b) :
    ForcesODE F ε b' := by
  intro ι _ G _ _ _ p φ₀ e P hφ he hP hsucc hacc
  have := h ι G p φ₀ e P hφ he hP hsucc hacc
  exact ⟨hb.trans this.1, hb.trans this.2⟩

/-- **The Hamiltonian families read as ODEs** (Lemma `odel:lem:herald`): homogeneous, one stage
(constant coefficients), generator `iH_x` (`D = 0`), and `g = B/‖x(T)‖ = 1` for every solution,
for Hermitian data and a unit initial state. -/
theorem hamFamily_conformance {X N Z : Type} [Fintype N] [DecidableEq N] {s : ℕ}
    (D : Data X N Z s) (T : ℝ) (hT : 0 ≤ T) (x₀ : EuclideanSpace ℂ N)
    (hH : ∀ x, (D.matrix x).IsHermitian) (hx₀ : ‖x₀‖ = 1) :
    (∀ k, (hamFamily D T hT x₀).src k = 0) ∧
      (∀ x k, ∃ H : Matrix N N ℂ, H.IsHermitian ∧
        (hamFamily D T hT x₀).data.matrix (x, k) = Complex.I • H) ∧
      (∀ x sol, (hamFamily D T hT x₀).Solves x sol →
        (hamFamily D T hT x₀).mass / ‖sol (hamFamily D T hT x₀).T‖ = 1) := by
  refine ⟨fun _ => rfl, fun x _ => ⟨D.matrix x, hH x, rfl⟩, fun x sol hs => ?_⟩
  have hu : sol (hamFamily D T hT x₀).T =
      Hamiltonian.evolve (D.matrix x) (hamFamily D T hT x₀).T x₀ :=
    (hamFamily D T hT x₀).solves_endpoint_unique hs (hamFamily_solves D T hT x₀ x)
  rw [hu, hamFamily_mass, Hamiltonian.norm_evolve_apply (hH x), hx₀, div_one]

/-- **The joint family** (proof of Theorem `odel:thm:joint`): inhomogeneous (the source stage),
`D = 0` (every stage generator is `iH`), `ḡ/√2 ≤ g ≤ ḡ` for every solution, dimension at most
`3ḡ²s`. -/
theorem joint_conformance {s : ℕ} {τ gbar ε : ℝ} (h : JointRange s τ gbar ε) :
    (∃ k, (jointFamilyAt s τ gbar h.s_ge h.tau_ge).src k ≠ 0) ∧
      (∀ x k, ∃ H : Matrix (JointIndex (jointM gbar) (jointMu s) s)
          (JointIndex (jointM gbar) (jointMu s) s) ℂ,
        H.IsHermitian ∧ (jointFamilyAt s τ gbar h.s_ge h.tau_ge).data.matrix (x, k) =
          Complex.I • H) ∧
      (∀ x sol, (jointFamilyAt s τ gbar h.s_ge h.tau_ge).Solves x sol →
        gbar / Real.sqrt 2 ≤ (jointFamilyAt s τ gbar h.s_ge h.tau_ge).mass /
            ‖sol (jointFamilyAt s τ gbar h.s_ge h.tau_ge).T‖ ∧
          (jointFamilyAt s τ gbar h.s_ge h.tau_ge).mass /
            ‖sol (jointFamilyAt s τ gbar h.s_ge h.tau_ge).T‖ ≤ gbar) ∧
      (Fintype.card (JointIndex (jointM gbar) (jointMu s) s) : ℝ) ≤ 3 * gbar ^ 2 * s := by
  have hM := four_le_jointM h.gbar_ge
  obtain ⟨hg1, hg2, hcard⟩ := joint_instance_props h.s_ge h.gbar_ge
  have hT : (jointFamilyAt s τ gbar h.s_ge h.tau_ge).T = τ := jointFamily_T
  refine ⟨⟨Fin.last _, ?_⟩, fun x k => jointFamily_skew x k, fun x sol hs => ?_, hcard⟩
  · show (if ((Fin.last (jointN τ + 1) : Fin (jointN τ + 2)) : ℕ) = jointN τ + 1 then
      jointSrc (jointM gbar) (jointN τ) (jointMu s) s else 0) ≠ 0
    rw [Fin.val_last, if_pos rfl]
    intro h0
    have h1 := norm_jointSrc (M := jointM gbar) (n := jointN τ) (μ := jointMu s) (s := s)
      (by omega)
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  · have hu : sol (jointFamilyAt s τ gbar h.s_ge h.tau_ge).T =
        jointSol (jointM gbar) (jointN τ) (jointMu s) s τ x
          (jointFamilyAt s τ gbar h.s_ge h.tau_ge).T :=
      (jointFamilyAt s τ gbar h.s_ge h.tau_ge).solves_endpoint_unique hs (jointSol_solves x)
    have hn := norm_jointSol_T (M := jointM gbar) (μ := jointMu s) (s := s)
      (jointN_time (by linarith [h.tau_ge])) x
    have hsM : 0 < Real.sqrt (jointM gbar) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega))
    have hne : ‖jointSol (jointM gbar) (jointN τ) (jointMu s) s τ x τ‖ ≠ 0 := by
      rw [hn]; positivity
    rw [hu, hT, jointFamilyAt_g h x, mul_div_assoc, div_self hne, mul_one]
    exact ⟨hg1, hg2⟩

set_option maxHeartbeats 4000000 in
/-- **Theorem `odel:thm:combined`** (eq. `odel:eq:combined`). For `s ≥ 32`,
`τ ≥ 4`, `ḡ ≥ 2` and `0 < ε ≤ 1/64`, every solver for the time-dependent class (`η = 1`, `T = τ`,
`g ≤ ḡ`) has worst-case matrix-query complexity `Q_A ≥ c (ḡ√s τ + √(sτr) + r)`,
`r = L/log(e + L/τ)`, with the absolute constant `c = log 2/(8192π)`: some family in the class
forces this bound. The first term is witnessed by an inhomogeneous time-dependent family with
`D = 0` and `ḡ/√2 ≤ g ≤ ḡ`; the last two terms by a homogeneous constant-coefficient family
(one stage) with `D = 0` and `g = 1`. Formal restrictions: the solvers are single circuit
programs over the coherent sampled-time access with forward and inverse calls, without
controlled calls and without adaptivity; the adaptive form with controlled and
controlled-inverse calls is `odel_thm_combined_adaptive`. -/
theorem odel_thm_combined :
    ∃ c : ℝ, 0 < c ∧ ∀ (s : ℕ) (τ gbar ε : ℝ), 32 ≤ s → 4 ≤ τ → 2 ≤ gbar → 0 < ε →
      ε ≤ 1 / 64 →
      (∃ (X N Z : Type) (_ : Fintype N) (_ : DecidableEq N) (_ : Fintype Z) (_ : AddCommGroup Z)
          (K : ℕ) (F : Family X N Z K s),
        F.InClass 1 gbar ∧ F.T = τ ∧
          ForcesODE F ε
            (c * (gbar * Real.sqrt s * τ + Real.sqrt (s * τ * hslR τ ε) + hslR τ ε))) ∧
      (∃ (X N Z : Type) (_ : Fintype N) (_ : DecidableEq N) (_ : Fintype Z) (_ : AddCommGroup Z)
          (K : ℕ) (F : Family X N Z K s),
        F.InClass 1 gbar ∧ F.T = τ ∧ (∃ k, F.src k ≠ 0) ∧
          (∀ x k, ∃ H : Matrix N N ℂ, H.IsHermitian ∧ F.data.matrix (x, k) = Complex.I • H) ∧
          (∀ x sol, F.Solves x sol →
            gbar / Real.sqrt 2 ≤ F.mass / ‖sol F.T‖ ∧ F.mass / ‖sol F.T‖ ≤ gbar) ∧
          ForcesODE F ε (c * (gbar * Real.sqrt s * τ))) ∧
      (∃ (X N Z : Type) (_ : Fintype N) (_ : DecidableEq N) (_ : Fintype Z) (_ : AddCommGroup Z)
          (F : Family X N Z 1 s),
        F.InClass 1 1 ∧ F.T = τ ∧ (∀ k, F.src k = 0) ∧
          (∀ x k, ∃ H : Matrix N N ℂ, H.IsHermitian ∧ F.data.matrix (x, k) = Complex.I • H) ∧
          (∀ x sol, F.Solves x sol → F.mass / ‖sol F.T‖ = 1) ∧
          ForcesODE F ε (c * (Real.sqrt (s * τ * hslR τ ε) + hslR τ ε))) := by
  refine ⟨combinedConst, combinedConst_pos, ?_⟩
  intro s τ gbar ε hs hτ hg hε hε1
  have h : CombinedRange s τ gbar ε := ⟨hs, hτ, hg, hε, hε1⟩
  have hH := h.toHSRange
  have hJ := h.toJointRange
  obtain ⟨hIT, hIM, hIP, -, -, -⟩ := hard_instances hH
  have hc0 : combinedConst ≤ c0 := by rw [combinedConst_eq]; linarith [c0_pos]
  have hr := hH.hsR_pos
  have hsr : 0 ≤ Real.sqrt (s * τ * hsR τ ε) + hsR τ ε := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rcases combined h with hw | hw | hw
    · exact ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _, _,
        hw.inClass, hw.time_eq, forcesODE_of_forces hw.forces⟩
    · exact ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _, _,
        hw.inClass, hw.time_eq, forcesODE_of_forces hw.forces⟩
    · exact ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _, _,
        hw.inClass, hw.time_eq, forcesODE_of_forces hw.forces⟩
  · have hw := joint_witness hJ
    obtain ⟨hsrc, hskew, hgr, -⟩ := joint_conformance hJ
    refine ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _, _,
      hw.inClass, hw.time_eq, hsrc, hskew, hgr, (forcesODE_of_forces hw.forces).mono ?_⟩
    have h1 : combinedConst ≤ jointConst := hc0.trans c0_le_jointConst
    have h2 : 0 ≤ gbar * Real.sqrt s * τ := by
      have := Real.sqrt_nonneg (s : ℝ)
      have : 0 ≤ gbar := by linarith
      have : 0 ≤ τ := by linarith
      positivity
    calc combinedConst * (gbar * Real.sqrt s * τ) ≤ jointConst * (gbar * Real.sqrt s * τ) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = jointConst * gbar * Real.sqrt s * τ := by ring
  · have hb : combinedConst * (Real.sqrt (s * τ * hslR τ ε) + hslR τ ε) ≤
        c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) := mul_le_mul_of_nonneg_right hc0 hsr
    rcases precision_terms_witness hH (le_refl (1 : ℝ)) with hw | hw | hw
    · obtain ⟨hsrc, hskew, hg1⟩ := hamFamily_conformance (timeData τ s hH.s_ge) τ
        (by linarith [hH.one_le_tau]) (searchInput (timeN τ) (hsMu s) s) hIT.isHermitian
        (norm_searchInput _ _ _)
      exact ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _,
        hw.inClass, hw.time_eq, hsrc, hskew, hg1, (forcesODE_of_forces hw.forces).mono hb⟩
    · obtain ⟨hsrc, hskew, hg1⟩ := hamFamily_conformance (mixedMainData τ ε s hH.s_ge) τ
        (by linarith [hH.one_le_tau]) (searchInput (precN τ ε) (hsMu s) s) hIM.isHermitian
        (norm_searchInput _ _ _)
      exact ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _,
        hw.inClass, hw.time_eq, hsrc, hskew, hg1, (forcesODE_of_forces hw.forces).mono hb⟩
    · obtain ⟨hsrc, hskew, hg1⟩ := hamFamily_conformance (precisionMainData τ ε s hH.s_ge) τ
        (by linarith [hH.one_le_tau]) (scalarInput (precN τ ε) s) hIP.isHermitian
        (norm_scalarInput _ _)
      exact ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _,
        hw.inClass, hw.time_eq, hsrc, hskew, hg1, (forcesODE_of_forces hw.forces).mono hb⟩

set_option maxHeartbeats 4000000 in
/-- **Theorem `odel:thm:joint`** (eq. `odel:eq:joint`). For `s ≥ 4`,
`τ ≥ 4`, `ḡ ≥ 2` and `0 < ε ≤ 1/64`, the ODE promise `g ≤ ḡ` requires `Q_A ≥ c ḡ√s τ`, with the
absolute constant `c = 1/400`. The hard family is in the class with `D = 0`, `η = 1`, `T = τ` and
`g ≥ ḡ/√2`, and has dimension at most `3ḡ²s` (`O(ḡ²s)`).
Formal restrictions: the solvers are single circuit programs over the coherent sampled-time
access with forward and inverse calls, without controlled calls and without adaptivity; the
adaptive form with controlled and controlled-inverse calls is `odel_thm_joint_adaptive`. -/
theorem odel_thm_joint :
    ∃ c : ℝ, 0 < c ∧ ∀ (s : ℕ) (τ gbar ε : ℝ), 4 ≤ s → 4 ≤ τ → 2 ≤ gbar → 0 < ε →
      ε ≤ 1 / 64 →
      ∃ (X N Z : Type) (_ : Fintype N) (_ : DecidableEq N) (_ : Fintype Z) (_ : AddCommGroup Z)
          (K : ℕ) (F : Family X N Z K s),
        F.InClass 1 gbar ∧ F.T = τ ∧
          (∀ x k, ∃ H : Matrix N N ℂ, H.IsHermitian ∧ F.data.matrix (x, k) = Complex.I • H) ∧
          (∀ x sol, F.Solves x sol → gbar / Real.sqrt 2 ≤ F.mass / ‖sol F.T‖) ∧
          (Fintype.card N : ℝ) ≤ 3 * gbar ^ 2 * s ∧
          ForcesODE F ε (c * gbar * Real.sqrt s * τ) := by
  refine ⟨jointConst, by norm_num [jointConst], ?_⟩
  intro s τ gbar ε hs hτ hg hε hε1
  have hJ : JointRange s τ gbar ε := ⟨hs, hτ, hg, hε, hε1⟩
  have hw := joint_witness hJ
  obtain ⟨-, hskew, hgr, hcard⟩ := joint_conformance hJ
  exact ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _, _, hw.inClass,
    hw.time_eq, hskew, fun x sol hs' => (hgr x sol hs').1, hcard, forcesODE_of_forces hw.forces⟩

set_option maxHeartbeats 4000000 in
/-- **Proposition `odel:rem:homogeneous`**. When `τ ≥ 20(1 + log ḡ)` (with
`s ≥ 4`, `ḡ ≥ 2`, `0 < ε ≤ 1/64`), the joint lower bound `Q_A ≥ c ḡ√s τ` (`c = 1/500`) also has a
homogeneous (`b = 0`) time-dependent witness in the class, with `g = Θ(ḡ)`:
`(4/√34) ḡ ≤ g ≤ ḡ`; its dimension is at most `6ḡ²s`.
Formal restrictions: the solvers are single circuit programs over the coherent sampled-time
access with forward and inverse calls, without controlled calls and without adaptivity; the
adaptive form with controlled and controlled-inverse calls is `odel_rem_homogeneous_adaptive`.
-/
theorem odel_rem_homogeneous :
    ∃ c : ℝ, 0 < c ∧ ∀ (s : ℕ) (τ gbar ε : ℝ), 4 ≤ s → 2 ≤ gbar →
      20 * (1 + Real.log gbar) ≤ τ → 0 < ε → ε ≤ 1 / 64 →
      ∃ (X N Z : Type) (_ : Fintype N) (_ : DecidableEq N) (_ : Fintype Z) (_ : AddCommGroup Z)
          (K : ℕ) (F : Family X N Z K s),
        F.InClass 1 gbar ∧ F.T = τ ∧ (∀ k, F.src k = 0) ∧
          (∀ x sol, F.Solves x sol →
            4 / Real.sqrt 34 * gbar ≤ F.mass / ‖sol F.T‖ ∧ F.mass / ‖sol F.T‖ ≤ gbar) ∧
          (Fintype.card N : ℝ) ≤ 6 * gbar ^ 2 * s ∧
          ForcesODE F ε (c * gbar * Real.sqrt s * τ) := by
  refine ⟨ODELowerBoundExtensions.Homogeneous.homConst,
    by norm_num [ODELowerBoundExtensions.Homogeneous.homConst], ?_⟩
  intro s τ gbar ε hs hg hτ hε hε1
  have h : ODELowerBoundExtensions.Homogeneous.HomRange s τ gbar ε := ⟨hs, hg, hτ, hε, hε1⟩
  have hw := ODELowerBoundExtensions.Homogeneous.hom_witness h
  have hT : (ODELowerBoundExtensions.Homogeneous.homFamilyAt s τ gbar h.s_ge h.gbar_ge
      h.tau_ge).T = τ := ODELowerBoundExtensions.Homogeneous.homFamily_T
  refine ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _, _, hw.inClass,
    hw.time_eq, ODELowerBoundExtensions.Homogeneous.homFamilyAt_src hs hg hτ, fun x sol hs' => ?_,
    (ODELowerBoundExtensions.Homogeneous.hom_instance_props hs hg).2.2,
    forcesODE_of_forces hw.forces⟩
  have hu : sol (ODELowerBoundExtensions.Homogeneous.homFamilyAt s τ gbar h.s_ge h.gbar_ge
      h.tau_ge).T = ODELowerBoundExtensions.Homogeneous.homSol (jointM gbar)
        (ODELowerBoundExtensions.Homogeneous.homN τ) (jointMu s) s x
        (ODELowerBoundExtensions.Homogeneous.homFamilyAt s τ gbar h.s_ge h.gbar_ge h.tau_ge).T :=
    (ODELowerBoundExtensions.Homogeneous.homFamilyAt s τ gbar h.s_ge h.gbar_ge
      h.tau_ge).solves_endpoint_unique hs'
      (ODELowerBoundExtensions.Homogeneous.homSol_solves _ _ _ x)
  rw [hu, hT]
  exact ODELowerBoundExtensions.Homogeneous.hom_g_theta h x

set_option maxHeartbeats 4000000 in
/-- **Theorem `odel:thm:psd`** (eq. `odel:eq:psd`). Let `s ≥ 32`, `τ ≥ 2`
and `L = log(1/ε) ≥ 64τ`. For the homogeneous equation `ẋ = -D_X x` there are hard families with
`D_X ⪰ 0`, `‖D_X‖ = η_D = 1`, `T = τ`, `1 ≤ g ≤ √2`, public supports and dyadic entries
(`HardInstance` of the data: real symmetric, exact dyadic words, operator norm exactly one,
row and column norms at most one, input-independent location lists and extensions), in the
class with `η = 1` and `ḡ = √2`, for which `Q_A ≥ c (√(sτr) + r)`, `c = log 2/(3072√2)`, for the
same heralded output as before.
Formal restrictions: the solvers are single circuit programs over the coherent sampled-time
access with forward and inverse calls, without controlled calls and without adaptivity; the
adaptive form with controlled and controlled-inverse calls is `odel_thm_psd_adaptive` (the
package's range is `τ ≥ 1`). -/
theorem odel_thm_psd :
    ∃ c : ℝ, 0 < c ∧ ∀ (s : ℕ) (τ ε : ℝ), 32 ≤ s → 2 ≤ τ → 0 < ε → 64 * τ ≤ logInv ε →
      ∃ (X N : Type) (_ : Fintype N) (_ : DecidableEq N) (B : ℕ) (F : Family X N (Word B) 1 s),
        HardInstance F.data ∧ (∀ y, (F.data.matrix y).PosSemidef) ∧ (∀ k, F.src k = 0) ∧
          F.T = τ ∧ F.InClass 1 (Real.sqrt 2) ∧
          (∀ x sol, F.Solves x sol →
            1 ≤ F.mass / ‖sol F.T‖ ∧ F.mass / ‖sol F.T‖ ≤ Real.sqrt 2) ∧
          ForcesODE F ε (c * (Real.sqrt (s * τ * hslR τ ε) + hslR τ ε)) := by
  refine ⟨ODELowerBoundExtensions.Psd.psdConst, ODELowerBoundExtensions.Psd.psdConst_pos, ?_⟩
  intro s τ ε hs hτ hε hL
  have h := ODELowerBoundExtensions.Psd.PsdRange.of_paper hs hτ hε hL
  rcases ODELowerBoundExtensions.Psd.psd h le_rfl with hw | hw
  · refine ⟨_, _, inferInstance, inferInstance, _, _,
      ODELowerBoundExtensions.Psd.hardInstance_oneStageData
        (ODELowerBoundExtensions.Psd.psdSearchData_hardInstance h.one_le_precN
          (ODELowerBoundExtensions.Psd.two_mul_psdM_add_one_le h.s_ge)),
      fun y => ODELowerBoundExtensions.Psd.psdSearchMat_posSemidef (τ / 2) y.1,
      fun _ => rfl, hw.time_eq, hw.inClass, fun x sol hs' => ?_, forcesODE_of_forces hw.forces⟩
    have hu : sol (ODELowerBoundExtensions.Psd.psdSearchFamilyAt h).T =
        ODELowerBoundExtensions.Psd.heat ((ODELowerBoundExtensions.Psd.psdSearchDataAt h).matrix x)
          (ODELowerBoundExtensions.Psd.psdSearchFamilyAt h).T
          (searchInput (precN τ ε) (ODELowerBoundExtensions.Psd.psdMu s) s) :=
      (ODELowerBoundExtensions.Psd.psdSearchFamilyAt h).solves_endpoint_unique hs'
        (ODELowerBoundExtensions.Psd.heatFamily_solves _ _ _ _ x)
    rw [hu, ODELowerBoundExtensions.Psd.psdSearchFamilyAt_T h]
    exact (ODELowerBoundExtensions.Psd.psdSearchFamilyAt_props h x).2.2.2.2
  · refine ⟨_, _, inferInstance, inferInstance, _, _,
      ODELowerBoundExtensions.Psd.hardInstance_oneStageData
        (ODELowerBoundExtensions.Psd.psdScalarData_hardInstance h.one_le_precN
          (by have := h.s_ge; omega)),
      fun y => ODELowerBoundExtensions.Psd.psdScalarMat_posSemidef (τ / 2) y.1,
      fun _ => rfl, hw.time_eq, hw.inClass, fun x sol hs' => ?_, forcesODE_of_forces hw.forces⟩
    have hu : sol (ODELowerBoundExtensions.Psd.psdScalarFamilyAt h).T =
        ODELowerBoundExtensions.Psd.heat ((ODELowerBoundExtensions.Psd.psdScalarDataAt h).matrix x)
          (ODELowerBoundExtensions.Psd.psdScalarFamilyAt h).T (scalarInput (precN τ ε) s) :=
      (ODELowerBoundExtensions.Psd.psdScalarFamilyAt h).solves_endpoint_unique hs'
        (ODELowerBoundExtensions.Psd.heatFamily_solves _ _ _ _ x)
    rw [hu, ODELowerBoundExtensions.Psd.psdScalarFamilyAt_T h]
    exact (ODELowerBoundExtensions.Psd.psdScalarFamilyAt_props h x).2.2.2.2

end

end ManuscriptConformance
