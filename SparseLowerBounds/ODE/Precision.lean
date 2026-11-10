import SparseLowerBounds.Helpers.Ode.Precision.Transfer

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Lemma `odel:lem:herald` in the ODE model: the `g = 1` families

Manuscript: eq. `odel:eq:hsbound` and Lemma `odel:lem:herald`. Theorem `hsl:thm:main` bounds the
cost of producing `e^{-iτH_X}|ψ_in⟩` on a known input by eq. `odel:eq:hsbound`,
`Q = Ω(√s τ + √(sτr) + r)`; with `A = -iH_X` and `b = 0` this is a homogeneous constant-coefficient
ODE with `D = 0` and `g = 1` (Lemma `odel:lem:herald`). Lemma `odel:lem:herald` (heralded transfer)
says the bound survives a success flag (probability `≥ 2/3` on each input, conditional error `ε`);
the Hamiltonian lower bound proves it as `Hamiltonian.time_herald`, `Hamiltonian.mixed_herald` and
`Hamiltonian.precision_herald` (spectator form).

This module reads the three hard data of the Hamiltonian lower bound (`Hamiltonian.timeData`,
`Hamiltonian.mixedMainData`, `Hamiltonian.precisionMainData`) as one-stage
families of `ODE/Model` through the transfer helper
`Helpers/Ode/Precision/Transfer` (`hamFamily`):

* `timeFamilyAt`, `mixedFamilyAt`, `precisionFamilyAt`: the families on
  `[0, τ]` with the unit inputs `searchInput`, `scalarInput`; they are in the
  class with `η = 1`, `T = τ` and any `ḡ ≥ 1` (`*_inClass`), and are
  homogeneous, constant-coefficient with generator `iH`, mass `1` and
  `‖x(T)‖ = 1`, so `D = 0` and `g = 1` (`hamFamily_props`);
* `forces_of_spec`: a bound proved by the Hamiltonian lower bound for programs
  over the spectated
  native primitives `specOracles (ι × Fin 1) D` with target
  `Hamiltonian.evolve (D.matrix x) T x₀` is forced by `hamFamily D`, because
  the sampled-time access is that spectated access (`access_hamFamily`) and
  every solver's accuracy for `x(T)/‖x(T)‖` is accuracy for the unit vector
  `x(T) = e^{-iTH_x} x₀`;
* `time_forces`, `mixed_forces`, `precision_forces`, `precision_forces_sqrt`:
  Lemma `odel:lem:herald` for the three families, with the constants of the
  Hamiltonian lower bound, for
  both value queries and all matrix queries;
* `herald_max`, `herald_witness`: eq. `odel:eq:hsbound` in the ODE model with
  the constant `c₀ = log 2/(4096π)` of `Hamiltonian.assembly`, in max
  form and in family form (one of the three `g = 1` families witnesses
  `c₀ (√s τ + √(sτr) + r)`), on the whole range `HSRange`, including
  `L < 64τ`, where the proof takes the bound from the time family alone
  (proof of Lemma `odel:lem:herald`);
* `precision_terms_witness`: hence the last two terms `√(sτr) + r` of
  Theorem `odel:thm:combined` are witnessed by homogeneous constant-coefficient
  families with `D = 0` and `g = 1`;
* `forces_or_of_max`: the classical step from a max form over three families
  to the family form, shared with `ODE/Theorem`.
-/

namespace SparseLowerBounds.ODE

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Readout
open scoped InnerProduct InnerProductSpace

-- The nested spectator spaces over the search index exceed the default instance size.
set_option synthInstance.maxSize 1024

section Transfer

variable {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s : ℕ}
  (D : Data X N Z s) (T : ℝ) (hT : 0 ≤ T) (x₀ : EuclideanSpace ℂ N)

omit [Fintype Z] [AddCommGroup Z] in
/-- **The precision families are homogeneous constant-coefficient ODEs with
`D = 0` and `g = 1`** (Lemma `odel:lem:herald`): one stage (`K = 1`, by type), no
source, generator `iH_x` (`A = -iH_x`), mass `B = ‖x₀‖ = 1`, `T = τ`, and the
solution has `‖x(T)‖ = 1`, so `g = B/‖x(T)‖ = 1`. -/
theorem hamFamily_props (hH : ∀ x, (D.matrix x).IsHermitian) (hx₀ : ‖x₀‖ = 1) (x : X) :
    (∀ k, (hamFamily D T hT x₀).src k = 0) ∧
      (∀ k, (hamFamily D T hT x₀).data.matrix (x, k) = Complex.I • D.matrix x) ∧
      (hamFamily D T hT x₀).mass = 1 ∧ (hamFamily D T hT x₀).T = T ∧
      ‖Hamiltonian.evolve (D.matrix x) (hamFamily D T hT x₀).T x₀‖ = 1 := by
  refine ⟨fun _ => rfl, fun _ => rfl, by rw [hamFamily_mass, hx₀], hamFamily_T D T hT x₀, ?_⟩
  rw [Hamiltonian.norm_evolve_apply (hH x), hx₀]

/-- **Solver transfer** (Lemma `odel:lem:herald` in the ODE model): if every program over the
spectated native primitives `specOracles (ι × Fin 1) D` that succeeds with probability `≥ 2/3` and
is `ε`-accurate for `e^{-iTH_x} x₀` makes at least `b` value queries and `b` queries in total, then
every solver of the family `hamFamily D T x₀` does. The solver's accuracy for `x(T)/‖x(T)‖` is
accuracy for `x(T) = e^{-iTH_x} x₀` since `‖x(T)‖ = 1`. -/
theorem forces_of_spec {ι G : Type*} [Fintype ι] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] {ε b : ℝ} (hH : ∀ x, (D.matrix x).IsHermitian) (hx₀ : ‖x₀‖ = 1)
    (A : Solver ι (hamFamily D T hT x₀) G ε)
    (hb : ∀ p : MultiOracleCircuit.Program (specOracles (ι × Fin 1) D),
      (∀ x, 2 / 3 ≤ ‖A.herald (p.eval x A.seed)‖ ^ 2) →
      (∀ x, HeraldedAccurate A.out A.herald (p.eval x A.seed)
        (Hamiltonian.evolve (D.matrix x) T x₀) ε) →
      b ≤ p.labelCount .value ∧ b ≤ p.count) :
    b ≤ A.prog.labelCount .value ∧ b ≤ A.prog.count := by
  have hacc : ∀ x, HeraldedAccurate A.out A.herald (A.prog.eval x A.seed)
      (Hamiltonian.evolve (D.matrix x) T x₀) ε := by
    intro x
    have h := A.accurate x _ (hamFamily_solves D T hT x₀ x)
    have hu : ODEStateNormalization.unitDirection (Hamiltonian.evolve (D.matrix x) T x₀) =
        Hamiltonian.evolve (D.matrix x) T x₀ := by
      rw [ODEStateNormalization.unitDirection, Hamiltonian.norm_evolve_apply (hH x), hx₀,
        inv_one, one_smul]
    rw [hamFamily_T, hu] at h
    exact h
  have key : ∀ (O : Query → X → Workspace ι N Z 1 →L[ℂ] Workspace ι N Z 1),
      O = specOracles (ι × Fin 1) D → ∀ p : MultiOracleCircuit.Program O,
      (∀ x, 2 / 3 ≤ ‖A.herald (p.eval x A.seed)‖ ^ 2) →
      (∀ x, HeraldedAccurate A.out A.herald (p.eval x A.seed)
        (Hamiltonian.evolve (D.matrix x) T x₀) ε) →
      b ≤ p.labelCount .value ∧ b ≤ p.count := by
    rintro O rfl p
    exact hb p
  exact key _ (funext fun l => funext fun x => access_hamFamily D T hT x₀ ι l x) A.prog
    A.success hacc

end Transfer

/-- **From a max form to a family form**: if, for one solver of each of three
families, the largest value-query count is at least `b`, then one of the three
families forces `b` (value queries and all matrix queries). Classical: if none
did, one cheap solver per family would contradict the max form. -/
theorem forces_or_of_max {X₁ N₁ Z₁ X₂ N₂ Z₂ X₃ N₃ Z₃ : Type*}
    [Fintype N₁] [DecidableEq N₁] [Fintype Z₁] [AddCommGroup Z₁]
    [Fintype N₂] [DecidableEq N₂] [Fintype Z₂] [AddCommGroup Z₂]
    [Fintype N₃] [DecidableEq N₃] [Fintype Z₃] [AddCommGroup Z₃] {K₁ K₂ K₃ s₁ s₂ s₃ : ℕ}
    (F₁ : Family X₁ N₁ Z₁ K₁ s₁) (F₂ : Family X₂ N₂ Z₂ K₂ s₂) (F₃ : Family X₃ N₃ Z₃ K₃ s₃)
    {ε b : ℝ}
    (h : ∀ (ι₁ ι₂ ι₃ G₁ G₂ G₃ : Type) [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
      [NormedAddCommGroup G₁] [InnerProductSpace ℂ G₁] [CompleteSpace G₁]
      [NormedAddCommGroup G₂] [InnerProductSpace ℂ G₂] [CompleteSpace G₂]
      [NormedAddCommGroup G₃] [InnerProductSpace ℂ G₃] [CompleteSpace G₃]
      (A₁ : Solver ι₁ F₁ G₁ ε) (A₂ : Solver ι₂ F₂ G₂ ε) (A₃ : Solver ι₃ F₃ G₃ ε),
      b ≤ max (A₁.prog.labelCount .value : ℝ)
        (max (A₂.prog.labelCount .value : ℝ) (A₃.prog.labelCount .value))) :
    F₁.Forces ε b ∨ F₂.Forces ε b ∨ F₃.Forces ε b := by
  by_contra hne
  push Not at hne
  obtain ⟨h₁, h₂, h₃⟩ := hne
  unfold Family.Forces at h₁ h₂ h₃
  simp only [not_forall] at h₁ h₂ h₃
  obtain ⟨ι₁, _, G₁, _, _, _, A₁, hA₁⟩ := h₁
  obtain ⟨ι₂, _, G₂, _, _, _, A₂, hA₂⟩ := h₂
  obtain ⟨ι₃, _, G₃, _, _, _, A₃, hA₃⟩ := h₃
  have cheap : ∀ {L C : ℕ}, L ≤ C → ¬ (b ≤ (L : ℝ) ∧ b ≤ (C : ℝ)) → (L : ℝ) < b := by
    intro L C hLC hn
    by_contra hc
    push Not at hc
    exact hn ⟨hc, hc.trans (by exact_mod_cast hLC)⟩
  have hmax := h ι₁ ι₂ ι₃ G₁ G₂ G₃ A₁ A₂ A₃
  have hlt := max_lt (cheap (labelCount_le_count A₁.prog _) hA₁)
    (max_lt (cheap (labelCount_le_count A₂.prog _) hA₂) (cheap (labelCount_le_count A₃.prog _) hA₃))
  linarith

open Hamiltonian in
/-- **The time family as an ODE family** (Lemma `hsl:lem:time` and Lemma `odel:lem:herald`):
`ẋ = -iH_j x` on `[0, τ]`, `x(0) = searchInput`, with the time data
(`n = timeN τ`, amplitude `timeC τ`, `m = 2^{hsMu s}`); it does not depend on `ε`. -/
def timeFamilyAt (τ : ℝ) (s : ℕ) (hs : 32 ≤ s) (hτ : 0 ≤ τ) :
    Family (Fin (timeN τ) → Fin (2 ^ hsMu s)) (SearchIndex (timeN τ) (hsMu s) s)
      (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) 1 s :=
  hamFamily (timeData τ s hs) τ hτ (searchInput (timeN τ) (hsMu s) s)

open Hamiltonian in
/-- **The mixed family as an ODE family** (proof of Theorem `hsl:thm:main` and Lemma
`odel:lem:herald`): `ẋ = -iH_j x` on `[0, τ]`, `x(0) = searchInput`, with the main-parameter mixed
data (`n = precN τ ε`, `a = 1`, `m = 2^{hsMu s}`). -/
def mixedFamilyAt (τ ε : ℝ) (s : ℕ) (hs : 32 ≤ s) (hτ : 0 ≤ τ) :
    Family (Fin (precN τ ε) → Fin (2 ^ hsMu s)) (SearchIndex (precN τ ε) (hsMu s) s)
      (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) 1 s :=
  hamFamily (mixedMainData τ ε s hs) τ hτ (searchInput (precN τ ε) (hsMu s) s)

open Hamiltonian in
/-- **The precision family as an ODE family** (proof of Theorem `hsl:thm:main` and Lemma
`odel:lem:herald`): `ẋ = -iH_x x` on `[0, τ]`, `x(0) = scalarInput`, with the main-parameter
precision data (`n = precN τ ε`). -/
def precisionFamilyAt (τ ε : ℝ) (s : ℕ) (hs : 32 ≤ s) (hτ : 0 ≤ τ) :
    Family (Fin (precN τ ε) → Bool) (ScalarIndex (precN τ ε) s)
      (Word (scalarBits (precN τ ε) s τ)) 1 s :=
  hamFamily (precisionMainData τ ε s hs) τ hτ (scalarInput (precN τ ε) s)

open Hamiltonian

variable {τ ε : ℝ} {s : ℕ}

/-- The time family is in the class with `η = 1` and any `ḡ ≥ 1` (`g = 1`). -/
theorem timeFamilyAt_inClass (h : HSRange τ s ε) {gbar : ℝ} (hg : 1 ≤ gbar) :
    (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])).InClass 1 gbar := by
  have hI := (hard_instances h).1
  exact hamFamily_inClass _ _ _ _ hI.isHermitian hI.row_norm_le hI.col_norm_le
    (norm_searchInput _ _ _) hg

/-- `T = τ` for the time family. -/
theorem timeFamilyAt_T (h : HSRange τ s ε) :
    (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])).T = τ :=
  hamFamily_T _ _ _ _

/-- The mixed family is in the class with `η = 1` and any `ḡ ≥ 1` (`g = 1`). -/
theorem mixedFamilyAt_inClass (h : HSRange τ s ε) {gbar : ℝ} (hg : 1 ≤ gbar) :
    (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])).InClass 1 gbar := by
  have hI := (hard_instances h).2.1
  exact hamFamily_inClass _ _ _ _ hI.isHermitian hI.row_norm_le hI.col_norm_le
    (norm_searchInput _ _ _) hg

/-- The precision family is in the class with `η = 1` and any `ḡ ≥ 1` (`g = 1`). -/
theorem precisionFamilyAt_inClass (h : HSRange τ s ε) {gbar : ℝ} (hg : 1 ≤ gbar) :
    (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])).InClass 1 gbar := by
  have hI := (hard_instances h).2.2.1
  exact hamFamily_inClass _ _ _ _ hI.isHermitian hI.row_norm_le hI.col_norm_le
    (norm_scalarInput _ _) hg

/-- `T = τ` for the mixed family. -/
theorem mixedFamilyAt_T (h : HSRange τ s ε) :
    (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])).T = τ :=
  hamFamily_T _ _ _ _

/-- `T = τ` for the precision family. -/
theorem precisionFamilyAt_T (h : HSRange τ s ε) :
    (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])).T = τ :=
  hamFamily_T _ _ _ _

/-- **Lemma `odel:lem:herald`, time family** (proof of Lemma `odel:lem:herald`;
`Hamiltonian.time_herald`): on the whole range `HSRange`, every heralded solver of the time
family makes at least `c_T √s τ` value queries (and as many matrix queries),
`c_T = log 2/(192π)`. -/
theorem time_forces (h : HSRange τ s ε) :
    (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])).Forces ε (cT * Real.sqrt s * τ) := by
  intro ι _ G _ _ _ A
  have hI := (hard_instances h).1
  exact forces_of_spec _ _ _ _ hI.isHermitian (norm_searchInput _ _ _) A fun p hsucc hacc =>
    time_herald h (ι × Fin 1) p A.seed A.seed_norm_le A.out A.out_isometry A.herald
      A.herald_proj hsucc hacc

/-- **Lemma `odel:lem:herald`, mixed family** (Lemma `odel:lem:herald`;
`Hamiltonian.mixed_herald`): for `L ≥ 64τ` and `s ≥ 64n/τ`, every heralded solver of the
mixed family makes at least `(log 2/(384√2)) √(sτr)` value queries (and as
many matrix queries). -/
theorem mixed_forces (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) :
    (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])).Forces ε
      (Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε)) := by
  intro ι _ G _ _ _ A
  have hI := (hard_instances h).2.1
  exact forces_of_spec _ _ _ _ hI.isHermitian (norm_searchInput _ _ _) A fun p hsucc hacc =>
    mixed_herald h hL hs (ι × Fin 1) p A.seed A.seed_norm_le A.out A.out_isometry A.herald
      A.herald_proj hsucc hacc

/-- **Lemma `odel:lem:herald`, precision family** (Lemma `odel:lem:herald`;
`Hamiltonian.precision_herald`): for `L ≥ 64τ`, every heralded solver of the precision
family makes at least `r/32` value queries (and as many matrix queries). -/
theorem precision_forces (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) :
    (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])).Forces ε (hsR τ ε / 32) := by
  intro ι _ G _ _ _ A
  have hI := (hard_instances h).2.2.1
  exact forces_of_spec _ _ _ _ hI.isHermitian (norm_scalarInput _ _) A fun p hsucc hacc =>
    let hp := precision_herald h hL (ι × Fin 1) p A.seed A.out A.out_isometry A.herald
      A.herald_proj hsucc hacc
    ⟨hp.1, hp.2.1⟩

/-- **Lemma `odel:lem:herald`, precision family, small sparsity** (Lemma `odel:lem:herald`;
`Hamiltonian.precision_herald`): for `L ≥ 64τ` and `s < 64n/τ`, every heralded solver of the
precision family makes at least `√(sτr)/(64√2)` value queries (and as many matrix queries). -/
theorem precision_forces_sqrt (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs' : (s : ℝ) < 64 * precN τ ε / τ) :
    (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])).Forces ε
      (Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2)) := by
  intro ι _ G _ _ _ A
  have hI := (hard_instances h).2.2.1
  refine forces_of_spec _ _ _ _ hI.isHermitian (norm_scalarInput _ _) A fun p hsucc hacc => ?_
  have hp := (precision_herald h hL (ι × Fin 1) p A.seed A.out A.out_isometry A.herald
    A.herald_proj hsucc hacc).2.2 hs'
  have hc : (p.labelCount .value : ℝ) ≤ p.count := by
    exact_mod_cast SparseLowerBounds.labelCount_le_count p _
  exact ⟨hp, hp.trans hc⟩


/-- **Eq. `odel:eq:hsbound` in the ODE model, max form** (Lemma `odel:lem:herald`;
`Hamiltonian.assembly`): for one solver of each of the three `g = 1` families
(time, mixed, precision) at `(s, τ, ε)`, the largest value-query count is at
least `c₀ (√s τ + √(sτr) + r)`, `c₀ = log 2/(4096π)`. For `L < 64τ` the time
bound alone carries it (proof of Lemma `odel:lem:herald`). -/
theorem herald_max (h : HSRange τ s ε) {ιT ιM ιP GT GM GP : Type}
    [Fintype ιT] [Fintype ιM] [Fintype ιP]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AT : Solver ιT (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) GT ε)
    (AM : Solver ιM (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) GM ε)
    (AP : Solver ιP (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) GP ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (AT.prog.labelCount .value : ℝ)
        (max (AM.prog.labelCount .value : ℝ) (AP.prog.labelCount .value)) :=
  assembly h (time_forces h ιT GT AT).1
    (fun hL => ⟨(precision_forces h hL ιP GP AP).1,
      fun hs' => (precision_forces_sqrt h hL hs' ιP GP AP).1⟩)
    (fun hL hs => (mixed_forces h hL hs ιM GM AM).1)

/-- **Eq. `odel:eq:hsbound` in the ODE model, family form** (Lemma
`odel:lem:herald`): for `τ ≥ 1`, `s ≥ 32`, `0 < ε ≤ 1/64`
(`HSRange`) and any `ḡ ≥ 1`, one of the time, mixed and precision families
(homogeneous, constant-coefficient, `D = 0`, `g = 1`; `hamFamily_props`) is in
the class (`η = 1`, `T = τ`, `g ≤ ḡ`) and forces `c₀ (√s τ + √(sτr) + r)` value
queries (and as many matrix queries), `c₀ = log 2/(4096π)`. Derived from
`herald_max` by `forces_or_of_max`. -/
theorem herald_witness (h : HSRange τ s ε) {gbar : ℝ} (hg : 1 ≤ gbar) :
    (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])).Witnesses τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])).Witnesses τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])).Witnesses τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  have hf := forces_or_of_max (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]))
    (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
    (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
    (ε := ε) (b := c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) (by
      intro ιT ιM ιP GT GM GP _ _ _ _ _ _ _ _ _ _ _ _ AT AM AP
      exact herald_max h AT AM AP)
  rcases hf with hf | hf | hf
  · exact Or.inl ⟨timeFamilyAt_inClass h hg, timeFamilyAt_T h, hf⟩
  · exact Or.inr (Or.inl ⟨mixedFamilyAt_inClass h hg, mixedFamilyAt_T h, hf⟩)
  · exact Or.inr (Or.inr ⟨precisionFamilyAt_inClass h hg, precisionFamilyAt_T h, hf⟩)

/-- **The precision terms of Theorem `odel:thm:combined` are witnessed by `g = 1`
families** (fourth sentence of the theorem, Theorem `odel:thm:combined`): on the whole range
`HSRange` and for any `ḡ ≥ 1`, one of the homogeneous constant-coefficient
families with `D = 0` and `g = 1` (time, mixed, precision; `hamFamily_props`)
witnesses `c₀ (√(sτr) + r)`. The statement is a disjunction and does not name
the family; the proof (`Hamiltonian.assembly`) obtains these terms from the mixed and
precision bounds when `L ≥ 64τ` (`mixed_forces`, `precision_forces`) and from
the time bound alone when `L < 64τ` (proof of Lemma `odel:lem:herald`). -/
theorem precision_terms_witness (h : HSRange τ s ε) {gbar : ℝ} (hg : 1 ≤ gbar) :
    (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])).Witnesses τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])).Witnesses τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])).Witnesses τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  have hS : 0 ≤ Real.sqrt s * τ := mul_nonneg (Real.sqrt_nonneg _) h.tau_pos.le
  have hb : c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) :=
    mul_le_mul_of_nonneg_left (by linarith) c0_pos.le
  rcases herald_witness h hg with hw | hw | hw
  · exact Or.inl (hw.mono hb)
  · exact Or.inr (Or.inl (hw.mono hb))
  · exact Or.inr (Or.inr (hw.mono hb))

end

end SparseLowerBounds.ODE
end
