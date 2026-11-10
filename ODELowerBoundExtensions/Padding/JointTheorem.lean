import ODELowerBoundExtensions.Padding.JointPad

/-!
# Theorem `odel:thm:joint` for the padded joint families

Manuscript: Theorem `odel:thm:joint` and
the end of its proof: the dense padding to maximum sparsity exactly `s` and
the known zero padding to any sufficiently large (qubit) register keep the bound
`Q ≥ c_J ḡ √s τ`, `c_J = 1/400` (`SparseLowerBounds.ODE.jointConst`).

**Hardness.** As in `SparseLowerBounds.ODE.joint_forces`, the solver is fed to the general form
`SparseLowerBounds.ODE.joint_general` (heralded half measurement, Lemma `odel:lem:outer`). The
Boolean implementation of the padded access is `implementsOn_stageData` (two membership queries
per value call, none for the locators, the dense block or the padding); the readout is the
solver's own isometry for the dense family and `padReadout P G i₀ ∘ out` for the zero-padded
family (`ZeroPad.heraldedAccurate`), whose targets are `jointTarget` in both cases. Hence
`joint_forces_dense` and `joint_forces_pad` give the constant `β² n √(M m)/16` of `joint_forces`,
and at the parameters `joint_witness_dense` and `joint_witness_pad` give exactly
`joint_witness`'s `ḡ √s τ / 400`.

**Word length at the parameters.** The dense family uses `B = ⌈log₂ s⌉ =
Hamiltonian.padExp s` (the released padding exponent, so its block is `Hamiltonian.padBlock s`). The
padded family `jointPadFamilyAt … dense … P` uses `jointPadBits s dense`: `padExp s` with the
dense block, and `jointMu s`, the word length of `jointFamilyAt`, without it. So
`jointPadFamilyAt … false … P` is the zero padding of `jointFamilyAt` both as an equation
(`jointZeroPad_zeroPad`) and as an encoding: its value table is that of `jointFamilyAt` on the
original block and `0` elsewhere (`jointZeroPad_table`, `jointPadFamily_table_off`).

**Instance facts** (`jointDenseFamilyAt_props`, proof of Theorem `odel:thm:joint`): maximum sparsity
exactly `s`, block norm at most one, dyadic entries, the unchanged solution `jointSol`, `D = 0`,
dimension `2Mm + s`; and `g = √M ∈ [ḡ/√2, ḡ]` (`jointDenseFamilyAt_g`, `jointPadFamilyAt_g` with
`joint_instance_props`, Theorem `odel:thm:joint`). **Common dimension and qubit registers**
(`joint_common_dimension`, `joint_qubit_register`, proof of Theorem `odel:thm:joint`): for every
`Nd` at least the dimension of `jointFamilyAt` (e.g. `Nd = 2^q ≥ 3 ḡ² s`) the zero padding
`PadTo JointIndex Nd` has dimension exactly `Nd` and keeps the bound and the sparsity.

**Forms covered.** The full heralded `SparseLowerBounds.ODE.Solver` of `ODE/Model` (any branch
register `ι`, any garbage space `G`), i.e. `Family.Forces`; controlled calls by the reduction of
the **Controlled calls** paragraph of `ODE/Model`, which has no Lean lemma (the locators of the
padded families are public, `stageData_locators_const`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Padding

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit SparseLowerBounds
  SparseLowerBounds.ODE SparseLowerBounds.Readout LowerBoundRemarks.HamiltonianPadding
open SparseLowerBounds.Hamiltonian (Word)

-- The nested time-addressed workspaces exceed the default instance size.
set_option synthInstance.maxSize 1024

/-- `μ = ⌊log₂ s⌋ ≤ ⌈log₂ s⌉ = Hamiltonian.padExp s` (`s ≤ 2^{padExp s}` is the released
`Hamiltonian.le_two_pow_padExp`). -/
theorem jointMu_le_padExp (s : ℕ) : jointMu s ≤ Hamiltonian.padExp s := by
  exact Nat.log_le_clog 2 s

/-- **The word length of the padded joint family at the parameters**:
`⌈log₂ s⌉ = Hamiltonian.padExp s` with the dense block (proof of Theorem `odel:thm:joint`),
`jointMu s = ⌊log₂ s⌋`, the word length of `jointFamilyAt`, without it. -/
def jointPadBits (s : ℕ) : Bool → ℕ
  | true => Hamiltonian.padExp s
  | false => jointMu s

/-- `μ = ⌊log₂ s⌋ ≤ jointPadBits s dense`. -/
theorem jointMu_le_jointPadBits (s : ℕ) (dense : Bool) : jointMu s ≤ jointPadBits s dense := by
  cases dense with
  | false => exact le_rfl
  | true => exact jointMu_le_padExp s

/-- With the dense block, `s ≤ 2^{jointPadBits s dense}`. -/
theorem le_two_pow_jointPadBits (s : ℕ) {dense : Bool} (hd : dense = true) :
    s ≤ 2 ^ jointPadBits s dense := by
  subst hd
  exact Hamiltonian.le_two_pow_padExp s

section General

variable {M n μ s B : ℕ} {dense : Bool}

/-- **Theorem `odel:thm:joint` for the dense family**, native form: every solver makes at least
`β² n √(M 2^μ) / 16` value queries (and as many matrix queries), as `joint_forces`. -/
theorem joint_forces_dense (hM : 2 ≤ M) (hMe : Even M) (hn : 1 ≤ n) (hμ : 1 ≤ μ)
    (hμs : 2 ^ μ ≤ s) (hμB : μ ≤ B) {T : ℝ} (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T) {ε : ℝ}
    (hε : 2 * ε ≤ 1) :
    (jointDenseFamily M n μ s B dense hμ hμs hμB T hT).Forces ε
      (jointCorr ε ^ 2 * n * Real.sqrt ((M : ℝ) * 2 ^ μ) / 16) := by
  intro ι _ G _ _ _ A
  have h := joint_general (s := s) hM hMe hn hμ hε
    (stageBoolean ι M n μ B (jointDenseTable M μ s B dense)) (ancillaEmbed _)
    ancillaEmbed_isometry ((jointDenseFamily M n μ s B dense hμ hμs hμB T hT).access ι)
    (Family.access_unitary ι _) hardCost (implementsOn_jointDense ι) A.prog A.seed
    A.seed_norm_le A.out A.out_isometry A.herald A.herald_proj A.success fun x => by
      have hx := A.accurate x _ (jointDenseSol_solves x)
      rwa [jointDenseFamily_T, unitDirection_jointSol_T hT] at hx
  exact Hamiltonian.native_bound_of_cost A.prog (by linarith)

/-- **Theorem `odel:thm:joint` for the zero-padded dense family**, native form: for every known
padding `P`, every solver makes at least `β² n √(M 2^μ) / 16` value queries (and as many matrix
queries). -/
theorem joint_forces_pad (hM : 2 ≤ M) (hMe : Even M) (hn : 1 ≤ n) (hμ : 1 ≤ μ)
    (hμs : 2 ^ μ ≤ s) (hμB : μ ≤ B) {T : ℝ} (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T) {ε : ℝ}
    (hε : 2 * ε ≤ 1) (P : Type*) [Fintype P] [DecidableEq P] :
    (jointPadFamily M n μ s B dense P hμ hμs hμB T hT).Forces ε
      (jointCorr ε ^ 2 * n * Real.sqrt ((M : ℝ) * 2 ^ μ) / 16) := by
  intro ι _ G _ _ _ A
  let i₀ : JointIndex M μ s := Sum.inr ⟨0, lt_of_lt_of_le (Nat.two_pow_pos μ) hμs⟩
  have h := joint_general (s := s) (G := Joint (Option P) G) hM hMe hn hμ hε
    (stageBoolean ι M n μ B (padTable (jointDenseTable M μ s B dense) P)) (ancillaEmbed _)
    ancillaEmbed_isometry ((jointPadFamily M n μ s B dense P hμ hμs hμB T hT).access ι)
    (Family.access_unitary ι _) hardCost (implementsOn_jointPad ι) A.prog A.seed
    A.seed_norm_le (padReadout P G i₀ ∘L A.out) (padReadout_comp_isometry i₀ A.out A.out_isometry)
    A.herald A.herald_proj A.success fun x => by
      have hx := jointPadFamily_zeroPad.heraldedAccurate A i₀ x (jointDenseSol_solves x)
      rwa [jointDenseFamily_T, unitDirection_jointSol_T hT] at hx
  exact Hamiltonian.native_bound_of_cost A.prog (by linarith)

end General

/-- **The densely padded hard family at the parameters** `(s, τ, ḡ)` of the proof of Theorem
`odel:thm:joint`: `jointFamilyAt` with the block `2^{-⌈log₂ s⌉} 1 1ᵀ = Hamiltonian.padBlock s` on
the `Fin s` block, words `Word ⌈log₂ s⌉` (`Hamiltonian.padExp s`). -/
def jointDenseFamilyAt (s : ℕ) (τ gbar : ℝ) (hs : 4 ≤ s) (hτ : 4 ≤ τ) :
    Family (Promised (jointM gbar) (jointN τ) (2 ^ jointMu s))
      (JointIndex (jointM gbar) (jointMu s) s) (Word (Hamiltonian.padExp s)) (jointN τ + 2) s :=
  jointDenseFamily (jointM gbar) (jointN τ) (jointMu s) s (Hamiltonian.padExp s) true
    (one_le_jointMu (by omega)) (two_pow_jointMu_le (by omega)) (jointMu_le_padExp s) τ
    (jointN_time (by linarith))

/-- **The hard family padded by a known register `P`** (proof of Theorem `odel:thm:joint` and proof
of Theorem `odel:thm:combined`), words `Word (jointPadBits s dense)`. With `dense = true` it carries
the dense block (maximum sparsity exactly `s`, words `Word ⌈log₂ s⌉`). With `dense = false` it is
the zero padding of `jointFamilyAt`: matrices `jointGen ⊕ 0_P`, sources and initial state `⊕ 0`
(`jointZeroPad_zeroPad`), and the words `Word ⌊log₂ s⌋` of `jointFamilyAt` on the original block,
`0` elsewhere (`jointZeroPad_table`). -/
def jointPadFamilyAt (s : ℕ) (τ gbar : ℝ) (dense : Bool) (hs : 4 ≤ s) (hτ : 4 ≤ τ) (P : Type*)
    [Fintype P] [DecidableEq P] :
    Family (Promised (jointM gbar) (jointN τ) (2 ^ jointMu s))
      (JointIndex (jointM gbar) (jointMu s) s ⊕ P) (Word (jointPadBits s dense)) (jointN τ + 2) s :=
  jointPadFamily (jointM gbar) (jointN τ) (jointMu s) s (jointPadBits s dense) dense P
    (one_le_jointMu (by omega)) (two_pow_jointMu_le (by omega)) (jointMu_le_jointPadBits s dense) τ
    (jointN_time (by linarith))

variable {s : ℕ} {τ gbar ε : ℝ}

/-- **Plain zero padding of the joint family** (proof of Theorem `odel:thm:joint`, proof of Theorem
`odel:thm:combined`): without the dense block, `jointPadFamilyAt … false … P` is the zero padding of
`jointFamilyAt` by `P` (matrices `jointGen ⊕ 0_P`, sources and initial state `⊕ 0`). -/
theorem jointZeroPad_zeroPad (hs : 4 ≤ s) (hτ : 4 ≤ τ) (P : Type*) [Fintype P] [DecidableEq P] :
    ZeroPad (jointPadFamilyAt s τ gbar false hs hτ P) (jointFamilyAt s τ gbar hs hτ) := by
  exact jointPadFamily_zeroPad_joint

/-- **The plain zero padding keeps the released encoding**: on the original block the value table of
`jointPadFamilyAt … false … P` (words `Word ⌊log₂ s⌋`) is that of `jointFamilyAt`; off it the
words are `0` (`jointPadFamily_table_off`). The analogue of
`HamiltonianPadding.padTable_value_inl_inl` for `timePadData`. -/
theorem jointZeroPad_table (hs : 4 ≤ s) (hτ : 4 ≤ τ) (P : Type*) [Fintype P] [DecidableEq P]
    (p : Promised (jointM gbar) (jointN τ) (2 ^ jointMu s) × Fin (jointN τ + 2))
    (i j : JointIndex (jointM gbar) (jointMu s) s) :
    (jointPadFamilyAt s τ gbar false hs hτ P).data.table p (Sum.inl i, Sum.inl j) =
      (jointFamilyAt s τ gbar hs hτ).data.table p (i, j) := by
  exact jointPadFamily_table_inl p i j

/-- **The dense padding** (proof of Theorem `odel:thm:joint`), at the parameters with `s ≥ 4`,
`τ ≥ 4`: maximum row and column sparsity exactly `s` at every input and stage; the block
`2^{-⌈log₂ s⌉} 1 1ᵀ` (`Hamiltonian.padBlock s`, `denseHam_padExp`) has operator norm at most one;
every entry is `i · v/2^{⌈log₂ s⌉}` with `-2^{⌈log₂ s⌉} < v ≤ 2^{⌈log₂ s⌉}`; the solution is
unchanged (`jointSol`, the solution of `jointFamilyAt`); `D = 0`; and the dimension is `2Mm + s`,
that of `jointFamilyAt`. The dense analogue of the released instance bundle
`joint_instance_props`. -/
theorem jointDenseFamilyAt_props (hs : 4 ≤ s) (hτ : 4 ≤ τ) :
    SparsityAttained (jointDenseFamilyAt s τ gbar hs hτ) ∧
      ‖SparseStateOverlap.matrixOperator
          (denseHam (jointM gbar) (jointMu s) s (Hamiltonian.padExp s) true)‖ ≤ 1 ∧
      (∀ p i j, ∃ v : ℤ, -(2 : ℤ) ^ Hamiltonian.padExp s < v ∧ v ≤ 2 ^ Hamiltonian.padExp s ∧
        (jointDenseFamilyAt s τ gbar hs hτ).data.matrix p i j =
          Complex.I * ((v : ℂ) / 2 ^ Hamiltonian.padExp s)) ∧
      (∀ x, (jointDenseFamilyAt s τ gbar hs hτ).Solves x
        (jointSol (jointM gbar) (jointN τ) (jointMu s) s τ x)) ∧
      (∀ x k, ∃ H : Matrix (JointIndex (jointM gbar) (jointMu s) s)
          (JointIndex (jointM gbar) (jointMu s) s) ℂ, H.IsHermitian ∧
        (jointDenseFamilyAt s τ gbar hs hτ).data.matrix (x, k) = Complex.I • H) ∧
      Fintype.card (JointIndex (jointM gbar) (jointMu s) s) =
        jointM gbar * (2 * 2 ^ jointMu s) + s := by
  exact ⟨jointDenseFamily_sparsityAttained rfl,
    norm_denseHam_le fun _ => Hamiltonian.le_two_pow_padExp s,
    fun p i j => jointDenseFamily_dyadic p i j, fun x => jointDenseSol_solves x,
    fun x k => jointDenseFamily_skew x k, card_jointIndex⟩

/-- **`g = √M` for the dense family** (eq. `odel:eq:cancel` and Theorem `odel:thm:joint`; as
`jointFamilyAt_g`): the mass `B = 2` equals `√M ‖x(T)‖` with the unchanged solution `jointSol`. With
`joint_instance_props`, `ḡ/√2 ≤ √M ≤ ḡ`, i.e. `g = Θ(ḡ)`. -/
theorem jointDenseFamilyAt_g (h : JointRange s τ gbar ε)
    (x : Promised (jointM gbar) (jointN τ) (2 ^ jointMu s)) :
    (jointDenseFamilyAt s τ gbar h.s_ge h.tau_ge).mass =
      Real.sqrt (jointM gbar) * ‖jointSol (jointM gbar) (jointN τ) (jointMu s) s τ x τ‖ := by
  have hM : 1 ≤ jointM gbar := by have := four_le_jointM h.gbar_ge; omega
  have hpos : 0 < Real.sqrt (jointM gbar) := Real.sqrt_pos.mpr (by exact_mod_cast hM)
  rw [norm_jointSol_T (jointN_time (by linarith [h.tau_ge])) x,
    show (jointDenseFamilyAt s τ gbar h.s_ge h.tau_ge).mass = 2 from jointDenseFamily_mass hM]
  field_simp

/-- **`g = √M` for the padded family** (Theorem `odel:thm:joint`; as `jointFamilyAt_g`): the mass
`B = 2` equals `√M ‖x(T) ⊕ 0‖` for the padded solution `jointSol ⊕ 0` (`jointPadSol_solves`).
With `joint_instance_props`, `ḡ/√2 ≤ √M ≤ ḡ`, i.e. `g = Θ(ḡ)`. -/
theorem jointPadFamilyAt_g (h : JointRange s τ gbar ε) (dense : Bool) (P : Type*) [Fintype P]
    [DecidableEq P] (x : Promised (jointM gbar) (jointN τ) (2 ^ jointMu s)) :
    (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge P).mass =
      Real.sqrt (jointM gbar) * ‖Hamiltonian.HsInstance.inlOp
        (JointIndex (jointM gbar) (jointMu s) s) P
        (jointSol (jointM gbar) (jointN τ) (jointMu s) s τ x τ)‖ := by
  have hM : 1 ≤ jointM gbar := by have := four_le_jointM h.gbar_ge; omega
  have hpos : 0 < Real.sqrt (jointM gbar) := Real.sqrt_pos.mpr (by exact_mod_cast hM)
  rw [norm_inlOp, norm_jointSol_T (jointN_time (by linarith [h.tau_ge])) x,
    show (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge P).mass = 2 from
      jointPadFamily_zeroPad.mass_eq.trans (jointDenseFamily_mass hM)]
  field_simp

/-- **Theorem `odel:thm:joint` with maximum sparsity exactly `s`** (Theorem `odel:thm:joint`): for
`s ≥ 4`, `τ ≥ 4`, `ḡ ≥ 2`, `0 < ε ≤ 1/64`, the densely padded joint family is in the class (`η = 1`,
`T = τ`, `g ≤ ḡ`) and forces `ḡ √s τ / 400` matrix queries, the bound and constant of
`joint_witness`. -/
theorem joint_witness_dense (h : JointRange s τ gbar ε) :
    (jointDenseFamilyAt s τ gbar h.s_ge h.tau_ge).Witnesses τ gbar ε
      (jointConst * gbar * Real.sqrt s * τ) := by
  have hb := joint_bound_le h
  have hs := h.s_ge
  have hM := four_le_jointM h.gbar_ge
  refine ⟨jointDenseFamily_inClass (fun _ => (Hamiltonian.le_two_pow_padExp s).trans
      (Nat.pow_le_pow_left (by norm_num) _)) (sqrt_jointM_le (by linarith [h.gbar_ge])),
    jointDenseFamily_T, ?_⟩
  intro ι _ G _ _ _ A
  have hf := joint_forces_dense (s := s) (by omega) (even_jointM gbar) (one_le_jointN h.tau_ge)
    (one_le_jointMu (by omega)) (two_pow_jointMu_le (by omega)) (jointMu_le_padExp s)
    (jointN_time (by linarith [h.tau_ge])) (by linarith [h.eps_le]) ι G A
  exact ⟨hb.trans hf.1, hb.trans hf.2⟩

/-- **Theorem `odel:thm:joint` after known zero padding** (proof of Theorem `odel:thm:joint`): for
every finite known register `P`, with or without the dense block, the padded joint family is in the
class (`η = 1`, `T = τ`, `g ≤ ḡ`) and forces `ḡ √s τ / 400` matrix queries; with the dense block it
has maximum sparsity exactly `s`. -/
theorem joint_witness_pad (h : JointRange s τ gbar ε) (dense : Bool) (P : Type*) [Fintype P]
    [DecidableEq P] :
    (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge P).Witnesses τ gbar ε
        (jointConst * gbar * Real.sqrt s * τ) ∧
      (dense = true → SparsityAttained (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge P)) := by
  have hb := joint_bound_le h
  have hs := h.s_ge
  have hM := four_le_jointM h.gbar_ge
  refine ⟨⟨jointPadFamily_inClass (fun hd => (le_two_pow_jointPadBits s hd).trans
      (Nat.pow_le_pow_left (by norm_num) _)) (sqrt_jointM_le (by linarith [h.gbar_ge])),
    jointPadFamily_T, ?_⟩, fun hd => by subst hd; exact jointPadFamily_sparsityAttained rfl⟩
  intro ι _ G _ _ _ A
  have hf := joint_forces_pad (s := s) (dense := dense) (by omega) (even_jointM gbar)
    (one_le_jointN h.tau_ge) (one_le_jointMu (by omega)) (two_pow_jointMu_le (by omega))
    (jointMu_le_jointPadBits s dense) (jointN_time (by linarith [h.tau_ge]))
    (by linarith [h.eps_le]) P ι G A
  exact ⟨hb.trans hf.1, hb.trans hf.2⟩

/-- **Theorem `odel:thm:joint` in any sufficiently large common dimension** (proof of Theorem
`odel:thm:joint` and proof of Theorem `odel:thm:combined`): for every `Nd` at least the dimension
`2Mm + s` of `jointFamilyAt`, the joint family padded by `PadTo JointIndex Nd`, with or without the
dense block, has dimension exactly `Nd`, is in the class and forces `ḡ √s τ / 400` matrix queries;
with the dense block it has maximum sparsity exactly `s`. -/
theorem joint_common_dimension (h : JointRange s τ gbar ε) (dense : Bool) (Nd : ℕ)
    (hJ : Fintype.card (JointIndex (jointM gbar) (jointMu s) s) ≤ Nd) :
    Fintype.card (JointIndex (jointM gbar) (jointMu s) s ⊕
        PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd) = Nd ∧
      (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd)).Witnesses τ gbar ε
        (jointConst * gbar * Real.sqrt s * τ) ∧
      (dense = true → SparsityAttained (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd))) := by
  exact ⟨card_padTo hJ, joint_witness_pad h dense _⟩

/-- **Any sufficiently large qubit register** (proof of Theorem `odel:thm:joint`): for every `q`
with `3 ḡ² s ≤ 2^q` (the dimension of `jointFamilyAt` is at most `3 ḡ² s`, `joint_instance_props`),
the joint family padded by `PadTo JointIndex (2^q)`, with or without the dense block, has dimension
exactly `2^q`, is in the class and forces `ḡ √s τ / 400` matrix queries; with the dense block it has
maximum sparsity exactly `s`. The case `Nd = 2^q` of `joint_common_dimension`. -/
theorem joint_qubit_register (h : JointRange s τ gbar ε) (dense : Bool) (q : ℕ)
    (hq : 3 * gbar ^ 2 * s ≤ (2 : ℝ) ^ q) :
    Fintype.card (JointIndex (jointM gbar) (jointMu s) s ⊕
        PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q)) = 2 ^ q ∧
      (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q))).Witnesses τ gbar ε
        (jointConst * gbar * Real.sqrt s * τ) ∧
      (dense = true → SparsityAttained (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q)))) := by
  have hc := (joint_instance_props (s := s) h.s_ge h.gbar_ge).2.2
  have hJ : Fintype.card (JointIndex (jointM gbar) (jointMu s) s) ≤ 2 ^ q := by
    have : (Fintype.card (JointIndex (jointM gbar) (jointMu s) s) : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  exact joint_common_dimension h dense (2 ^ q) hJ

end

end ODELowerBoundExtensions.Padding
