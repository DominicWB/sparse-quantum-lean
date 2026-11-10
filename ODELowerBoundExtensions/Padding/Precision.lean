import ODELowerBoundExtensions.Padding.ZeroPad

/-!
# Lemma `odel:lem:herald` for the zero-padded `g = 1` families

Manuscript: Lemma `odel:lem:herald` and the proof of Theorem `odel:thm:combined` ("Pad dimensions to
a common known size if desired"). The `g = 1` families of `SparseLowerBounds/ODE/Precision`
(`timeFamilyAt`, `mixedFamilyAt`, `precisionFamilyAt`: the hard data of the Hamiltonian lower bound
read as homogeneous constant-coefficient ODEs `ẋ = -iH x`) are padded by known registers through the
padded Hamiltonian data of `LowerBoundRemarks.HamiltonianPadding` (`timePadData`, `mixedPadData`,
`precisionPadData`, matrices `H ⊕ 0_P`), with the initial state `ψ_in ⊕ 0`: `timePadFamilyAt`,
`mixedPadFamilyAt`, `precisionPadFamilyAt`.

* `*PadFamilyAt_zeroPad`: each is the zero padding (`ZeroPad`) of the unpadded family, so it is in
  the class with `η = 1`, `T = τ`, `g = 1 ≤ ḡ` and keeps maximum sparsity exactly `s`
  (`herald_instances_pad`; sparsity from `HardInstance`, `sparsityAttained_hamFamily`).
* `time_forces_pad`, `mixed_forces_pad`, `precision_forces_pad`, `precision_forces_sqrt_pad`:
  Lemma `odel:lem:herald` for the padded families, with the constants and side conditions of
  `time_forces`, `mixed_forces`, `precision_forces`, `precision_forces_sqrt`. Route: the released
  `SparseLowerBounds.ODE.forces_of_spec`, applied directly to `hamFamily (timePadData …) τ hτ
  (inlOp ψ_in)` (it is generic over the data and the initial state; the sampled-time access of
  `hamFamily D` is the spectated native access of `D`, `access_hamFamily`); the padded
  primitives are `hardCost` programs over the padded Boolean family
  (`implementsOn_padSearchData_spec`, `implementsOn_padScalarData_spec`); the readout `padReadout P G i₀ ∘ out` is heralded-accurate
  for `e^{-iτH} ψ_in` (`evolve_padMat`, `heraldedAccurate_padReadout`); then
  `Hamiltonian.time_herald_general` (resp. `mixed_herald_general`, `precision_herald_general`)
  and `Hamiltonian.native_bound_of_cost` with the numerics of `Hamiltonian.time_herald` etc.
* `herald_max_pad`: eq. `odel:eq:hsbound` for the padded families in max form, constant
  `c₀ = log 2/(4096π)` (`Hamiltonian.assembly`); `herald_witness_pad` and
  `precision_terms_witness_pad`: the family forms (as `herald_witness`, `precision_terms_witness`),
  the second being the fourth sentence of Theorem `odel:thm:combined` for the
  padded families. That the padded families are homogeneous, constant-coefficient, with `D = 0`
  and `g = 1` is `herald_pad_props`: the released `hamFamily_props` applied to the Hermitian
  matrices `H ⊕ 0_P` (`hard_instances_pad`) and `‖ψ_in ⊕ 0‖ = 1` (`norm_inlOp`).

**Forms covered.** The full heralded `SparseLowerBounds.ODE.Solver` of `ODE/Model` (any branch
register `ι`, any garbage space `G`), i.e. `Family.Forces`; controlled calls by the reduction of
the **Controlled calls** paragraph of `ODE/Model`, which has no Lean lemma (the locators of
`hamFamily` are those of the padded Hamiltonian data, input independent).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Padding

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit SparseLowerBounds
  SparseLowerBounds.ODE SparseLowerBounds.Readout SparseLowerBounds.Hamiltonian
  LowerBoundRemarks.HamiltonianPadding

-- The nested spectator spaces over the search index exceed the default instance size.
set_option synthInstance.maxSize 1024

/-- **Maximum sparsity exactly `s` for a `g = 1` family**: the sampled matrices of `hamFamily D`
are `i · D.matrix x`, so the sparsity attained by a `HardInstance` is attained at the one stage. -/
theorem sparsityAttained_hamFamily {X N : Type*} [Fintype N] [DecidableEq N] {B s : ℕ}
    {D : Data X N (Word B) s} (hD : HardInstance D) (T : ℝ) (hT : 0 ≤ T)
    (x₀ : EuclideanSpace ℂ N) : SparsityAttained (hamFamily D T hT x₀) := by
  intro x k
  have hne : ∀ i j, (Complex.I • D.matrix x) i j ≠ 0 ↔ D.matrix x i j ≠ 0 := fun i j => by
    simp [Complex.I_ne_zero]
  change (∃ i, (Finset.univ.filter fun j => (Complex.I • D.matrix x) i j ≠ 0).card = s) ∧
    ∃ j, (Finset.univ.filter fun i => (Complex.I • D.matrix x) i j ≠ 0).card = s
  obtain ⟨i, hi⟩ := hD.row_sparsity_attained x
  obtain ⟨j, hj⟩ := hD.col_sparsity_attained x
  exact ⟨⟨i, (congrArg Finset.card (Finset.filter_congr fun j _ => hne i j)).trans hi⟩,
    ⟨j, (congrArg Finset.card (Finset.filter_congr fun i _ => hne i j)).trans hj⟩⟩

/-- **The padded time family** `ẋ = -i(H_j ⊕ 0) x`, `x(0) = ψ_in ⊕ 0`, on `[0, τ]`. -/
def timePadFamilyAt (τ : ℝ) (s : ℕ) (hs : 32 ≤ s) (hτ : 0 ≤ τ) (P : Type*) [Fintype P]
    [DecidableEq P] :
    Family (Fin (timeN τ) → Fin (2 ^ hsMu s)) (SearchIndex (timeN τ) (hsMu s) s ⊕ P)
      (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) 1 s :=
  hamFamily (timePadData τ s hs P) τ hτ (HsInstance.inlOp _ P (searchInput (timeN τ) (hsMu s) s))

/-- **The padded mixed family** `ẋ = -i(H_j ⊕ 0) x`, `x(0) = ψ_in ⊕ 0`, on `[0, τ]`. -/
def mixedPadFamilyAt (τ ε : ℝ) (s : ℕ) (hs : 32 ≤ s) (hτ : 0 ≤ τ) (P : Type*) [Fintype P]
    [DecidableEq P] :
    Family (Fin (precN τ ε) → Fin (2 ^ hsMu s)) (SearchIndex (precN τ ε) (hsMu s) s ⊕ P)
      (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) 1 s :=
  hamFamily (mixedPadData τ ε s hs P) τ hτ
    (HsInstance.inlOp _ P (searchInput (precN τ ε) (hsMu s) s))

/-- **The padded precision family** `ẋ = -i(H_x ⊕ 0) x`, `x(0) = ψ_in ⊕ 0`, on `[0, τ]`. -/
def precisionPadFamilyAt (τ ε : ℝ) (s : ℕ) (hs : 32 ≤ s) (hτ : 0 ≤ τ) (P : Type*) [Fintype P]
    [DecidableEq P] :
    Family (Fin (precN τ ε) → Bool) (ScalarIndex (precN τ ε) s ⊕ P)
      (Word (scalarBits (precN τ ε) s τ)) 1 s :=
  hamFamily (precisionPadData τ ε s hs P) τ hτ (HsInstance.inlOp _ P (scalarInput (precN τ ε) s))

variable {τ ε : ℝ} {s : ℕ}

/-- The padded time family is the zero padding of `timeFamilyAt`. -/
theorem timePadFamilyAt_zeroPad (hs : 32 ≤ s) (hτ : 0 ≤ τ) (P : Type*) [Fintype P]
    [DecidableEq P] : ZeroPad (timePadFamilyAt τ s hs hτ P) (timeFamilyAt τ s hs hτ) := by
  exact ⟨fun _ => (padMat_smul Complex.I _).symm, fun _ => rfl, fun _ => (map_zero _).symm, rfl⟩

/-- The padded mixed family is the zero padding of `mixedFamilyAt`. -/
theorem mixedPadFamilyAt_zeroPad (hs : 32 ≤ s) (hτ : 0 ≤ τ) (P : Type*) [Fintype P]
    [DecidableEq P] : ZeroPad (mixedPadFamilyAt τ ε s hs hτ P) (mixedFamilyAt τ ε s hs hτ) := by
  exact ⟨fun _ => (padMat_smul Complex.I _).symm, fun _ => rfl, fun _ => (map_zero _).symm, rfl⟩

/-- The padded precision family is the zero padding of `precisionFamilyAt`. -/
theorem precisionPadFamilyAt_zeroPad (hs : 32 ≤ s) (hτ : 0 ≤ τ) (P : Type*) [Fintype P]
    [DecidableEq P] :
    ZeroPad (precisionPadFamilyAt τ ε s hs hτ P) (precisionFamilyAt τ ε s hs hτ) := by
  exact ⟨fun _ => (padMat_smul Complex.I _).symm, fun _ => rfl, fun _ => (map_zero _).symm, rfl⟩

/-- **The padded `g = 1` families are in the class** (`η = 1`, `T = τ`, `g = 1 ≤ ḡ`) and have
maximum row and column sparsity exactly `s`, for any known paddings `PT`, `PM`, `PP`. -/
theorem herald_instances_pad (h : HSRange τ s ε) {gbar : ℝ} (hg : 1 ≤ gbar)
    (PT PM PP : Type*) [Fintype PT] [DecidableEq PT] [Fintype PM] [DecidableEq PM]
    [Fintype PP] [DecidableEq PP] :
    ((timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT).InClass 1 gbar ∧
        (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT).T = τ ∧
        SparsityAttained (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT)) ∧
      ((mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM).InClass 1 gbar ∧
        (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM).T = τ ∧
        SparsityAttained (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM)) ∧
      ((precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP).InClass 1 gbar ∧
        (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP).T = τ ∧
        SparsityAttained (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP)) := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  have hT := hard_instances h
  exact ⟨⟨(timePadFamilyAt_zeroPad h.s_ge hτ PT).inClass (timeFamilyAt_inClass h hg),
      ((timePadFamilyAt_zeroPad h.s_ge hτ PT).T_eq).trans (timeFamilyAt_T h),
      (timePadFamilyAt_zeroPad h.s_ge hτ PT).sparsityAttained
        (sparsityAttained_hamFamily hT.1 _ _ _)⟩,
    ⟨(mixedPadFamilyAt_zeroPad h.s_ge hτ PM).inClass (mixedFamilyAt_inClass h hg),
      ((mixedPadFamilyAt_zeroPad h.s_ge hτ PM).T_eq).trans (mixedFamilyAt_T h),
      (mixedPadFamilyAt_zeroPad h.s_ge hτ PM).sparsityAttained
        (sparsityAttained_hamFamily hT.2.1 _ _ _)⟩,
    ⟨(precisionPadFamilyAt_zeroPad h.s_ge hτ PP).inClass (precisionFamilyAt_inClass h hg),
      ((precisionPadFamilyAt_zeroPad h.s_ge hτ PP).T_eq).trans (precisionFamilyAt_T h),
      (precisionPadFamilyAt_zeroPad h.s_ge hτ PP).sparsityAttained
        (sparsityAttained_hamFamily hT.2.2.1 _ _ _)⟩⟩

/-- **The padded `g = 1` families have `D = 0` and `g = 1`** (as the released `hamFamily_props`,
Lemma `odel:lem:herald`): at every input the source vanishes, every stage generator is `i (H ⊕ 0_P)`
with `H` the hard Hamiltonian of `hard_instances` (`D = 0`), the mass is `1`, `T = τ`, and the
solution `x(τ) = e^{-iτ(H ⊕ 0)} (ψ_in ⊕ 0)` has norm `1`, so `g = 1`. -/
theorem herald_pad_props (h : HSRange τ s ε) (PT PM PP : Type*) [Fintype PT] [DecidableEq PT]
    [Fintype PM] [DecidableEq PM] [Fintype PP] [DecidableEq PP] :
    (∀ j, (∀ k, (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT).src k = 0) ∧
      (∀ k, (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT).data.matrix (j, k) =
        Complex.I • padMat PT (searchHam (timeN τ) (hsMu s) s (timeC τ) τ j)) ∧
      (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT).mass = 1 ∧
      (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT).T = τ ∧
      ‖evolve (padMat PT (searchHam (timeN τ) (hsMu s) s (timeC τ) τ j)) τ
        (HsInstance.inlOp _ PT (searchInput (timeN τ) (hsMu s) s))‖ = 1) ∧
    (∀ j, (∀ k, (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM).src k = 0) ∧
      (∀ k, (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM).data.matrix (j, k) =
        Complex.I • padMat PM (searchHam (precN τ ε) (hsMu s) s 1 τ j)) ∧
      (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM).mass = 1 ∧
      (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM).T = τ ∧
      ‖evolve (padMat PM (searchHam (precN τ ε) (hsMu s) s 1 τ j)) τ
        (HsInstance.inlOp _ PM (searchInput (precN τ ε) (hsMu s) s))‖ = 1) ∧
    (∀ x, (∀ k, (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP).src k = 0) ∧
      (∀ k, (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP).data.matrix
        (x, k) = Complex.I • padMat PP (scalarHam (precN τ ε) s τ x)) ∧
      (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP).mass = 1 ∧
      (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP).T = τ ∧
      ‖evolve (padMat PP (scalarHam (precN τ ε) s τ x)) τ
        (HsInstance.inlOp _ PP (scalarInput (precN τ ε) s))‖ = 1) := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  have hI := hard_instances_pad h PT PM PP
  refine ⟨fun j => ?_, fun j => ?_, fun x => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hamFamily_props (timePadData τ s h.s_ge PT) τ hτ _
      hI.1.isHermitian (by rw [norm_inlOp]; exact norm_searchInput _ _ _) j
    rw [h4] at h5
    exact ⟨h1, h2, h3, h4, h5⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hamFamily_props (mixedPadData τ ε s h.s_ge PM) τ hτ _
      hI.2.1.isHermitian (by rw [norm_inlOp]; exact norm_searchInput _ _ _) j
    rw [h4] at h5
    exact ⟨h1, h2, h3, h4, h5⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hamFamily_props (precisionPadData τ ε s h.s_ge PP) τ hτ _
      hI.2.2.1.isHermitian (by rw [norm_inlOp]; exact norm_scalarInput _ _) x
    rw [h4] at h5
    exact ⟨h1, h2, h3, h4, h5⟩

/-- **Lemma `odel:lem:herald`, padded time family** (as `time_forces`): on `HSRange`, for every
known padding `P`, every heralded solver makes at least `c_T √s τ` value queries (and as many
matrix queries), `c_T = log 2/(192π)`. -/
theorem time_forces_pad (h : HSRange τ s ε) (P : Type*) [Fintype P] [DecidableEq P] :
    (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) P).Forces ε
      (cT * Real.sqrt s * τ) := by
  intro ι _ G _ _ _ A
  have hI := (hard_instances_pad h P P P).1
  refine forces_of_spec _ _ _ _ hI.isHermitian
    (by rw [norm_inlOp]; exact norm_searchInput _ _ _) A fun p hsucc hacc => ?_
  have hacc' : ∀ j, HeraldedAccurate (padReadout P G refZero ∘L A.out) A.herald
      (p.eval j A.seed)
      (evolve (searchHam (timeN τ) (hsMu s) s (timeC τ) τ j) τ
        (searchInput (timeN τ) (hsMu s) s)) ε := by
    intro j
    have hj := hacc j
    rw [show (timePadData τ s h.s_ge P).matrix j =
      padMat P (searchHam (timeN τ) (hsMu s) s (timeC τ) τ j) from rfl, evolve_padMat] at hj
    exact heraldedAccurate_padReadout refZero A.out A.herald _ _ ε hj
  have hb := time_herald_general h
    (bitSpecFamily (ι × Fin 1) (padTable (searchTable (timeN τ) (hsMu s) s (timeC τ) τ) P)
      (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)))
    (ancillaEmbed _) ancillaEmbed_isometry (specOracles (ι × Fin 1) (timePadData τ s h.s_ge P))
    (specOracles_unitary _ _) hardCost
    (implementsOn_padSearchData_spec P (ι × Fin 1) (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge))
    p A.seed A.seed_norm_le (padReadout P G refZero ∘L A.out)
    (padReadout_comp_isometry refZero A.out A.out_isometry) A.herald A.herald_proj hsucc hacc'
  exact native_bound_of_cost p (by linarith [hb, time_final h.one_le_tau h.s_ge])

/-- **Lemma `odel:lem:herald`, padded mixed family** (as `mixed_forces`): for `L ≥ 64τ` and
`s ≥ 64n/τ`, every heralded solver makes at least `(log 2/(384√2)) √(sτr)` value queries (and as
many matrix queries). -/
theorem mixed_forces_pad (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) (P : Type*) [Fintype P] [DecidableEq P] :
    (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) P).Forces ε
      (Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε)) := by
  intro ι _ G _ _ _ A
  have hI := (hard_instances_pad h P P P).2.1
  refine forces_of_spec _ _ _ _ hI.isHermitian
    (by rw [norm_inlOp]; exact norm_searchInput _ _ _) A fun p hsucc hacc => ?_
  have hacc' : ∀ j, HeraldedAccurate (padReadout P G refZero ∘L A.out) A.herald
      (p.eval j A.seed)
      (evolve (searchHam (precN τ ε) (hsMu s) s 1 τ j) τ
        (searchInput (precN τ ε) (hsMu s) s)) ε := by
    intro j
    have hj := hacc j
    rw [show (mixedPadData τ ε s h.s_ge P).matrix j =
      padMat P (searchHam (precN τ ε) (hsMu s) s 1 τ j) from rfl, evolve_padMat] at hj
    exact heraldedAccurate_padReadout refZero A.out A.herald _ _ ε hj
  have hb := mixed_herald_general h hL hs
    (bitSpecFamily (ι × Fin 1) (padTable (searchTable (precN τ ε) (hsMu s) s 1 τ) P)
      (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)))
    (ancillaEmbed _) ancillaEmbed_isometry
    (specOracles (ι × Fin 1) (mixedPadData τ ε s h.s_ge P))
    (specOracles_unitary _ _) hardCost
    (implementsOn_padSearchData_spec P (ι × Fin 1) (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge))
    p A.seed A.seed_norm_le (padReadout P G refZero ∘L A.out)
    (padReadout_comp_isometry refZero A.out A.out_isometry) A.herald A.herald_proj hsucc hacc'
  exact native_bound_of_cost p (by linarith [hb, mixrbound h hL])

/-- **Lemma `odel:lem:herald`, padded precision family** (as `precision_forces`): for `L ≥ 64τ`,
every heralded solver makes at least `r/32` value queries (and as many matrix queries). -/
theorem precision_forces_pad (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) (P : Type*) [Fintype P]
    [DecidableEq P] :
    (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) P).Forces ε
      (hsR τ ε / 32) := by
  intro ι _ G _ _ _ A
  have hI := (hard_instances_pad h P P P).2.2.1
  refine forces_of_spec _ _ _ _ hI.isHermitian
    (by rw [norm_inlOp]; exact norm_scalarInput _ _) A fun p hsucc hacc => ?_
  have hacc' : ∀ x, HeraldedAccurate (padReadout P G refZero ∘L A.out) A.herald
      (p.eval x A.seed)
      (evolve (scalarHam (precN τ ε) s τ x) τ (scalarInput (precN τ ε) s)) ε := by
    intro x
    have hx := hacc x
    rw [show (precisionPadData τ ε s h.s_ge P).matrix x =
      padMat P (scalarHam (precN τ ε) s τ x) from rfl, evolve_padMat] at hx
    exact heraldedAccurate_padReadout refZero A.out A.herald _ _ ε hx
  have hb := precision_herald_general h hL
    (bitSpecFamily (ι × Fin 1) (padTable (scalarTable (precN τ ε) s τ) P)
      (Word (scalarBits (precN τ ε) s τ)))
    (ancillaEmbed _) ancillaEmbed_isometry
    (specOracles (ι × Fin 1) (precisionPadData τ ε s h.s_ge P))
    (specOracles_unitary _ _) hardCost
    (implementsOn_padScalarData_spec P (ι × Fin 1) (le_trans (by norm_num) h.s_ge))
    p A.seed (padReadout P G refZero ∘L A.out)
    (padReadout_comp_isometry refZero A.out A.out_isometry) A.herald A.herald_proj hsucc hacc'
  have hq := native_bound_of_cost (b := (precN τ ε : ℝ) / 4) p (by linarith [hb])
  have hrb := rbound h hL
  exact ⟨by linarith [hq.1], by linarith [hq.2]⟩

/-- **Lemma `odel:lem:herald`, padded precision family, small sparsity** (as
`precision_forces_sqrt`): for `L ≥ 64τ` and `s < 64n/τ`, every heralded solver makes at least
`√(sτr)/(64√2)` value queries (and as many matrix queries). -/
theorem precision_forces_sqrt_pad (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs' : (s : ℝ) < 64 * precN τ ε / τ) (P : Type*) [Fintype P] [DecidableEq P] :
    (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) P).Forces ε
      (Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2)) := by
  intro ι _ G _ _ _ A
  have hI := (hard_instances_pad h P P P).2.2.1
  refine forces_of_spec _ _ _ _ hI.isHermitian
    (by rw [norm_inlOp]; exact norm_scalarInput _ _) A fun p hsucc hacc => ?_
  have hacc' : ∀ x, HeraldedAccurate (padReadout P G refZero ∘L A.out) A.herald
      (p.eval x A.seed)
      (evolve (scalarHam (precN τ ε) s τ x) τ (scalarInput (precN τ ε) s)) ε := by
    intro x
    have hx := hacc x
    rw [show (precisionPadData τ ε s h.s_ge P).matrix x =
      padMat P (scalarHam (precN τ ε) s τ x) from rfl, evolve_padMat] at hx
    exact heraldedAccurate_padReadout refZero A.out A.herald _ _ ε hx
  have hb := precision_herald_general h hL
    (bitSpecFamily (ι × Fin 1) (padTable (scalarTable (precN τ ε) s τ) P)
      (Word (scalarBits (precN τ ε) s τ)))
    (ancillaEmbed _) ancillaEmbed_isometry
    (specOracles (ι × Fin 1) (precisionPadData τ ε s h.s_ge P))
    (specOracles_unitary _ _) hardCost
    (implementsOn_padScalarData_spec P (ι × Fin 1) (le_trans (by norm_num) h.s_ge))
    p A.seed (padReadout P G refZero ∘L A.out)
    (padReadout_comp_isometry refZero A.out A.out_isometry) A.herald A.herald_proj hsucc hacc'
  have hq := native_bound_of_cost (b := (precN τ ε : ℝ) / 4) p (by linarith [hb])
  have hp := failedmix h hL hs'
  exact ⟨by linarith [hq.1], by linarith [hq.2]⟩

/-- **Eq. `odel:eq:hsbound` for the padded `g = 1` families, max form** (as `herald_max`): for
any known paddings and one solver of each padded family, the largest value-query count is at
least `c₀ (√s τ + √(sτr) + r)`, `c₀ = log 2/(4096π)`. -/
theorem herald_max_pad (h : HSRange τ s ε) (PT PM PP : Type*) [Fintype PT] [DecidableEq PT]
    [Fintype PM] [DecidableEq PM] [Fintype PP] [DecidableEq PP] {ιT ιM ιP GT GM GP : Type}
    [Fintype ιT] [Fintype ιM] [Fintype ιP]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AT : Solver ιT (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT) GT ε)
    (AM : Solver ιM (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM) GM ε)
    (AP : Solver ιP (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP) GP ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (AT.prog.labelCount .value : ℝ)
        (max (AM.prog.labelCount .value : ℝ) (AP.prog.labelCount .value)) := by
  exact assembly h (time_forces_pad h PT ιT GT AT).1
    (fun hL => ⟨(precision_forces_pad h hL PP ιP GP AP).1,
      fun hs' => (precision_forces_sqrt_pad h hL hs' PP ιP GP AP).1⟩)
    (fun hL hs => (mixed_forces_pad h hL hs PM ιM GM AM).1)

/-- **Eq. `odel:eq:hsbound` for the padded `g = 1` families, family form** (Lemma `odel:lem:herald`;
as `herald_witness`): on `HSRange`, for any `ḡ ≥ 1` and any known paddings, one of the padded time,
mixed and precision families (homogeneous, constant-coefficient, `D = 0` and `g = 1` by
`herald_pad_props`) is in the class (`η = 1`, `T = τ`, `g ≤ ḡ`) and forces `c₀ (√s τ + √(sτr) + r)`
value queries (and as many matrix queries), `c₀ = log 2/(4096π)`. -/
theorem herald_witness_pad (h : HSRange τ s ε) {gbar : ℝ} (hg : 1 ≤ gbar) (PT PM PP : Type*)
    [Fintype PT] [DecidableEq PT] [Fintype PM] [DecidableEq PM] [Fintype PP] [DecidableEq PP] :
    (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT).Witnesses τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM).Witnesses τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP).Witnesses τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  have hf := forces_or_of_max (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT)
    (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM)
    (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP)
    (ε := ε) (b := c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) (by
      intro ιT ιM ιP GT GM GP _ _ _ _ _ _ _ _ _ _ _ _ AT AM AP
      exact herald_max_pad h PT PM PP AT AM AP)
  have hI := herald_instances_pad (ε := ε) h hg PT PM PP
  rcases hf with hf | hf | hf
  · exact Or.inl ⟨hI.1.1, hI.1.2.1, hf⟩
  · exact Or.inr (Or.inl ⟨hI.2.1.1, hI.2.1.2.1, hf⟩)
  · exact Or.inr (Or.inr ⟨hI.2.2.1, hI.2.2.2.1, hf⟩)

/-- **The precision terms of Theorem `odel:thm:combined` are witnessed by padded `g = 1` families**
(fourth sentence of the theorem, Theorem `odel:thm:combined`; as `precision_terms_witness`): on
`HSRange`, for any `ḡ ≥ 1` and any known paddings, one of the padded homogeneous
constant-coefficient families (`D = 0` and `g = 1` by `herald_pad_props`) witnesses
`c₀ (√(sτr) + r)`. -/
theorem precision_terms_witness_pad (h : HSRange τ s ε) {gbar : ℝ} (hg : 1 ≤ gbar)
    (PT PM PP : Type*) [Fintype PT] [DecidableEq PT] [Fintype PM] [DecidableEq PM] [Fintype PP]
    [DecidableEq PP] :
    (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT).Witnesses τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM).Witnesses τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP).Witnesses τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  have hS : 0 ≤ Real.sqrt s * τ := mul_nonneg (Real.sqrt_nonneg _) h.tau_pos.le
  have hb : c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) :=
    mul_le_mul_of_nonneg_left (by linarith) c0_pos.le
  rcases herald_witness_pad h hg PT PM PP with hw | hw | hw
  · exact Or.inl (hw.mono hb)
  · exact Or.inr (Or.inl (hw.mono hb))
  · exact Or.inr (Or.inr (hw.mono hb))

end

end ODELowerBoundExtensions.Padding
