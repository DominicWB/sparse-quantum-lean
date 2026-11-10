import ODELowerBoundExtensions.Release.Model
import TimeDependentExtensions.ODE.Sampling

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Mesh refinement of a piecewise-constant family

Manuscript: Section `odel:sec:main` ("The time-dependent examples are piecewise constant with
known breakpoints, as permitted by Theorem `ode:thm:time`") and the general-mesh released solver
`TimeDependentExtensions.ODE.solver` (Theorem `ode:thm:time` on general meshes).

The released solver certifies the error
`publicError = s Λ (Σ_q Δ_q² rb_q / 2 + M (T/N) B)` (`TimeDependentExtensions.ODE.publicError`),
whose left-endpoint source quadrature `Σ_q Δ_q² rb_q / 2` does not shrink with the number `N` of
slots. On a family with a source stage of fixed length (the joint family, stage `n + 1` of length
`1`) it is a constant, so the released solver runs on the **refined** data: every stage `k` of the
family is cut into `R` equal pieces (`stageOf`: piece `r` lies in stage `r / R`). The refinement
`refineFamily F R` is again a family of `SparseLowerBounds.ODE.Model` with `KR` stages: its
sampled-time input reads the stage's generator (`refineData`, a reindexing `reindexData` of the
family's native data, same words, locators and decoder), its breakpoints `t_r` are the release's
mesh and its stage sources the release's forcing samples:

* `refine_isMesh`, `refineFamily_T`: a mesh `0 = t_0 ≤ ⋯ ≤ t_{KR} = T`;
* `refine_meshMass`, `refineFamily_mass`: the release's source mass
  `MeshSampling.mass ‖x₀‖ t rb` is the family's `B = ‖x₀‖ + Σ_k len_k ‖b_k‖`;
* `refine_quadrature`: `Σ_q Δ_q² rb_q = (Σ_k len_k² ‖b_k‖) / R`;
* `refine_interval`, `refine_solves`: each refined interval lies in its stage, so a solution of
  the family solves the release's piecewise problem on the refined mesh;
* `stageData`, `stageAccess`, `stageEmbed`, `access_stageEmbed`: more generally, for **any** public
  placement `σ : Fin M → Fin K` of `M` mesh pieces into the stages (the uniform refinement is
  `σ = stageOf K R`, `refineFamily_access`), the sampled-time access of the data
  `stageData F.data σ` (piece `r` reads stage `σ r`) is the family's access with branch
  register `ι × Fin M`, restricted along a fixed isometry that places branch `(i, r)` at stage
  `σ r` (`implementsOn_stage` transports Boolean certificates). The lower bounds on the release's
  oracle (`Release/Bridge`) hold for every such placement; uniformity is used only for the
  upper-bound arithmetic (`refine_quadrature`).
-/

namespace ODELowerBoundExtensions.Release

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open scoped InnerProduct InnerProductSpace

variable {N Z : Type*} [Fintype N] [DecidableEq N] {s : ℕ}

/-- **Reindexing native sparse data** along a map of inputs `f : Y' → Y`: the same words,
locators and decoder, read at `f y'`. -/
def reindexData {Y Y' : Type*} (D : Data Y N Z s) (f : Y' → Y) : Data Y' N Z s where
  slot := D.slot
  slots_pos := D.slots_pos
  scale := D.scale
  scale_pos := D.scale_pos
  matrix y := D.matrix (f y)
  table y := D.table (f y)
  decode := D.decode
  decode_bound := D.decode_bound
  decoded y := D.decoded (f y)
  rowloc y := D.rowloc (f y)
  colloc y := D.colloc (f y)
  row_injective y := D.row_injective (f y)
  column_injective y := D.column_injective (f y)
  row_covers y := D.row_covers (f y)
  column_covers y := D.column_covers (f y)
  rowOracle y := D.rowOracle (f y)
  columnOracle y := D.columnOracle (f y)
  row_unitary y := D.row_unitary (f y)
  column_unitary y := D.column_unitary (f y)
  row_valid y := D.row_valid (f y)
  column_valid y := D.column_valid (f y)

/-- Reindexed data read the matrix of the image input. -/
@[simp] theorem reindexData_matrix {Y Y' : Type*} (D : Data Y N Z s) (f : Y' → Y) (y : Y') :
    (reindexData D f).matrix y = D.matrix (f y) := rfl

/-- The native primitives of reindexed data are those of the data at the image input. -/
theorem oracles_reindexData [Fintype Z] [AddCommGroup Z] {Y Y' : Type*} (D : Data Y N Z s)
    (f : Y' → Y) (l : Query) (y : Y') : oracles (reindexData D f) l y = oracles D l (f y) := by
  cases l <;> rfl

/-- The stage of piece `r` of the `R`-fold refinement of `K` stages: `r / R`. -/
def stageOf (K R : ℕ) (r : Fin (K * R)) : Fin K :=
  ⟨r / R, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq r.2 (mul_comm K R))⟩

/-- **Sampled-time data along a placement** `σ : Fin M → Fin K` of mesh pieces into stages:
piece `r` reads the generator of stage `σ r` (same words, locators and decoder). -/
def stageData {X : Type*} {K M : ℕ} (D : Data (X × Fin K) N Z s) (σ : Fin M → Fin K) :
    Data (X × Fin M) N Z s :=
  reindexData D (fun p => (p.1, σ p.2))

/-- **The refined sampled-time input**: piece `r` reads the generator of stage `r / R`. -/
def refineData {X : Type*} {K : ℕ} (D : Data (X × Fin K) N Z s) (R : ℕ) :
    Data (X × Fin (K * R)) N Z s :=
  stageData D (stageOf K R)

variable {X : Type*} {K : ℕ}

/-- **The `R`-fold refinement of a family**: piece `r` is a copy of stage `r / R` of length
`len_{r/R} / R`, with that stage's generator (`refineData`) and source; same initial state. -/
def refineFamily (F : Family X N Z K s) (R : ℕ) : Family X N Z (K * R) s where
  data := refineData F.data R
  len r := F.len (stageOf K R r) / R
  len_nonneg _ := div_nonneg (F.len_nonneg _) (Nat.cast_nonneg R)
  src r := F.src (stageOf K R r)
  init := F.init

/-- The refined generator of piece `r` is the family's generator of stage `r / R`. -/
@[simp] theorem refineFamily_gen (F : Family X N Z K s) (R : ℕ) (x : X)
    (r : Fin (K * R)) : (refineFamily F R).gen x r = F.gen x (stageOf K R r) := rfl

/-- The refined durations, extended by `0` beyond the last piece: `len_{i/R} / R`. -/
theorem refineFamily_lenNat (F : Family X N Z K s) (R : ℕ) (i : ℕ) :
    (refineFamily F R).lenNat i = F.lenNat (i / R) / R := by
  rcases Nat.eq_zero_or_pos R with hR | hR
  · subst hR; simp [Family.lenNat]
  by_cases hi : i < K * R
  · have hq : i / R < K := Nat.div_lt_of_lt_mul (lt_of_lt_of_eq hi (mul_comm K R))
    rw [Family.lenNat, dif_pos hi, Family.lenNat, dif_pos hq]
    rfl
  · have hq : ¬ i / R < K := fun h => hi (by
      have := (Nat.div_lt_iff_lt_mul hR).mp h; linarith)
    rw [Family.lenNat, dif_neg hi, Family.lenNat, dif_neg hq, zero_div]

/-- The refined breakpoints: `t'_{qR + m} = t_q + m len_q / R` for `m ≤ R`. -/
theorem refineFamily_start (F : Family X N Z K s) {R : ℕ} (hR : 0 < R) (q m : ℕ) (hm : m ≤ R) :
    (refineFamily F R).start (q * R + m) = F.start q + m * (F.lenNat q / R) := by
  induction q generalizing m with
  | zero =>
    induction m with
    | zero => simp
    | succ m ih =>
      rw [zero_mul, zero_add] at ih ⊢
      rw [Family.start_succ, ih (by omega), refineFamily_lenNat,
        Nat.div_eq_of_lt (by omega : m < R)]
      push_cast; ring
  | succ q ihq =>
    induction m with
    | zero =>
      simp only [add_zero, Nat.cast_zero, zero_mul]
      rw [Nat.succ_mul, ihq R le_rfl, F.start_succ]
      have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
      field_simp
    | succ m ih =>
      rw [← add_assoc, Family.start_succ, ih (by omega), refineFamily_lenNat]
      have : ((q + 1) * R + m) / R = q + 1 := by
        rw [add_comm, Nat.add_mul_div_right _ _ hR, Nat.div_eq_of_lt (by omega), zero_add]
      rw [this]; push_cast; ring

/-- Sums over the pieces of the refinement: `Σ_r g(r / R) = R Σ_k g k`. -/
theorem sum_stageOf (R : ℕ) (g : Fin K → ℝ) :
    ∑ r : Fin (K * R), g (stageOf K R r) = R * ∑ k, g k := by
  rw [← (finProdFinEquiv : Fin K × Fin R ≃ Fin (K * R)).sum_comp, Fintype.sum_prod_type,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hst : ∀ j : Fin R, stageOf K R (finProdFinEquiv (k, j)) = k := fun j => by
    have hR : 0 < R := j.pos
    apply Fin.ext
    simp only [stageOf, finProdFinEquiv, Equiv.coe_fn_mk]
    rw [Nat.add_mul_div_left _ _ hR, Nat.div_eq_of_lt j.2, zero_add]
  simp [hst]

/-- The refinement has the same final time. -/
theorem refineFamily_T (F : Family X N Z K s) (R : ℕ) (hR : 0 < R) :
    (refineFamily F R).T = F.T := by
  have h := refineFamily_start F hR K 0 (Nat.zero_le _)
  rw [add_zero, Nat.cast_zero, zero_mul, add_zero] at h
  exact h

/-- The refinement has the same source mass `B`. -/
theorem refineFamily_mass (F : Family X N Z K s) (R : ℕ) (hR : 0 < R) :
    (refineFamily F R).mass = F.mass := by
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  simp only [Family.mass]
  rw [show (∑ r : Fin (K * R), (refineFamily F R).len r * ‖(refineFamily F R).src r‖) =
      R * ∑ k, F.len k / R * ‖F.src k‖ from sum_stageOf R fun k => F.len k / R * ‖F.src k‖,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp

/-- **The refined mesh**: the breakpoints `t_r` of the refinement form a mesh of `[0, T]` with
`KR` pieces. -/
theorem refine_isMesh (F : Family X N Z K s) (R : ℕ) (hR : 0 < R) :
    TimeDependentExtensions.IsMesh (refineFamily F R).start (K * R) F.T where
  zero := Family.start_zero _
  last := refineFamily_T F R hR
  mono := monotone_nat_of_le_succ (refineFamily F R).start_le_start_succ

/-- Every refined interval lies in its stage interval. -/
theorem refine_interval (F : Family X N Z K s) (R : ℕ) (r : Fin (K * R)) :
    F.start (stageOf K R r) ≤ (refineFamily F R).start r ∧
      (refineFamily F R).start ((r : ℕ) + 1) ≤ F.start ((stageOf K R r : ℕ) + 1) := by
  have hR : 0 < R := Nat.pos_of_ne_zero fun h => by
    subst h; exact absurd r.2 (by simp)
  have hl := F.lenNat_nonneg ((r : ℕ) / R)
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hdec : (r : ℕ) = (r : ℕ) / R * R + (r : ℕ) % R := (Nat.div_add_mod' _ _).symm
  have hmod : (r : ℕ) % R < R := Nat.mod_lt _ hR
  have hst : ((stageOf K R r : Fin K) : ℕ) = (r : ℕ) / R := rfl
  rw [hst]
  constructor
  · rw [hdec, refineFamily_start F hR _ _ hmod.le, ← hdec]
    have := div_nonneg hl hR'.le
    nlinarith [(Nat.cast_nonneg ((r : ℕ) % R) : (0 : ℝ) ≤ _)]
  · rw [hdec, add_assoc, refineFamily_start F hR _ _ hmod, ← hdec, F.start_succ]
    have h1 : (((r : ℕ) % R + 1 : ℕ) : ℝ) ≤ R := by exact_mod_cast hmod
    have h2 : (R : ℝ) * (F.lenNat ((r : ℕ) / R) / R) = F.lenNat ((r : ℕ) / R) := by
      field_simp
    nlinarith [div_nonneg hl hR'.le]

/-- **The release's source mass is `B`**: `‖x₀‖ + Σ_q Δ_q ‖b_q‖ = B` on the refined mesh
(`MeshSampling.mass`). -/
theorem refine_meshMass (F : Family X N Z K s) (R : ℕ) (hR : 0 < R) :
    TimeDependentExtensions.MeshSampling.mass ‖F.init‖ (refineFamily F R).start
      (fun r => ‖(refineFamily F R).src r‖) = F.mass := by
  rw [← refineFamily_mass F R hR]
  simp only [TimeDependentExtensions.MeshSampling.mass, Family.mass]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [(refineFamily F R).start_succ_fin q, add_sub_cancel_left]

/-- **The source quadrature shrinks like `1/R`**: `Σ_q Δ_q² ‖b_q‖ = (Σ_k len_k² ‖b_k‖) / R`. -/
theorem refine_quadrature (F : Family X N Z K s) (R : ℕ) :
    ∑ q : Fin (K * R), ((refineFamily F R).start ((q : ℕ) + 1) -
        (refineFamily F R).start q) ^ 2 * ‖(refineFamily F R).src q‖ =
      (∑ k, F.len k ^ 2 * ‖F.src k‖) / R := by
  have h : ∀ q : Fin (K * R), ((refineFamily F R).start ((q : ℕ) + 1) -
      (refineFamily F R).start q) ^ 2 * ‖(refineFamily F R).src q‖ =
      (fun k => (F.len k / R) ^ 2 * ‖F.src k‖) (stageOf K R q) := fun q => by
    rw [(refineFamily F R).start_succ_fin q, add_sub_cancel_left]; rfl
  rw [Finset.sum_congr rfl fun q _ => h q, sum_stageOf R fun k => (F.len k / R) ^ 2 * ‖F.src k‖]
  rcases Nat.eq_zero_or_pos R with hR | hR
  · subst hR; simp
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp

/-- **A solution solves the refined piecewise problem**: on every refined interval, the
release's `SolvesODE` with the constant generator and source of its stage. -/
theorem refine_solves (F : Family X N Z K s) (R : ℕ) {x : X}
    {sol : ℝ → EuclideanSpace ℂ N} (hs : F.Solves x sol) (r : Fin (K * R)) :
    TimeDependentODE.SolvesODE (fun _ => (refineFamily F R).gen x r)
      (fun _ => (refineFamily F R).src r) sol ((refineFamily F R).start r)
      ((refineFamily F R).start ((r : ℕ) + 1)) :=
  (hs.2 (stageOf K R r)).mono (refine_interval F R r).1 (refine_interval F R r).2

variable [Fintype Z] [AddCommGroup Z]

/-- **The sampled-time access along a placement** `σ`: the access of `SparseLowerBounds.ODE.Model`
(`Family.access`) of the data `stageData F.data σ`, branch register `ι`. -/
abbrev stageAccess {M : ℕ} (F : Family X N Z K s) (σ : Fin M → Fin K) (ι : Type*) [Fintype ι] :
    Query → X → Workspace ι N Z M →L[ℂ] Workspace ι N Z M :=
  TimeDependentODE.labelOracle (oracles (stageData F.data σ))
    (TimeDependentODE.sample (ι := ι) (M := M))

/-- The refined family's access is the access along the placement `stageOf K R`. -/
theorem refineFamily_access (F : Family X N Z K s) (R : ℕ) (ι : Type*) [Fintype ι] :
    (refineFamily F R).access ι = stageAccess F (stageOf K R) ι := rfl

/-- **The stage placement isometry** along `σ : Fin M → Fin K`: branch `(i, r)` of the piece
workspace goes to branch `((i, r), σ r)` of the family's workspace with branch register
`ι × Fin M`; the other stages receive `0`. -/
def stageEmbed (ι : Type*) [Fintype ι] {M : ℕ} (σ : Fin M → Fin K) :
    Workspace ι N Z M →L[ℂ] Workspace (ι × Fin M) N Z K :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : (ι × Fin M) × Fin K =>
      SparseFlagEmbedding.Space (N × N) Z)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun b : (ι × Fin M) × Fin K =>
      if b.2 = σ b.1.2 then Joint.proj b.1 else 0)

omit [DecidableEq N] [AddCommGroup Z] in
/-- The placement on components: `(i, r)` at stage `σ r`, zero elsewhere. -/
theorem stageEmbed_apply (ι : Type*) [Fintype ι] {M : ℕ} (σ : Fin M → Fin K)
    (v : Workspace ι N Z M) (b : (ι × Fin M) × Fin K) :
    stageEmbed ι σ v b = if b.2 = σ b.1.2 then v b.1 else 0 := by
  change (if b.2 = σ b.1.2 then Joint.proj b.1 else 0) v = _
  split_ifs <;> rfl

omit [DecidableEq N] [AddCommGroup Z] in
/-- The placement is an isometry. -/
theorem stageEmbed_isometry (ι : Type*) [Fintype ι] {M : ℕ} (σ : Fin M → Fin K) :
    (stageEmbed (N := N) (Z := Z) ι σ)† ∘L stageEmbed ι σ = 1 := by
  refine ContinuousLinearMap.ext fun v => ?_
  refine ext_inner_left ℂ fun w => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply, PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single (σ b.2)]
  · simp [stageEmbed_apply]
  · intro k _ hk
    simp [stageEmbed_apply, hk]
  · simp

/-- **The access along a placement is the family's access along the placement isometry**: the
sampled-time access of `stageData F.data σ` with branch register `ι` intertwines, through
`stageEmbed`, with the family's access with branch register `ι × Fin M`. -/
theorem access_stageEmbed (F : Family X N Z K s) {M : ℕ} (σ : Fin M → Fin K) (ι : Type*)
    [Fintype ι] (l : Query) (x : X) :
    F.access (ι × Fin M) l x ∘L stageEmbed ι σ = stageEmbed ι σ ∘L stageAccess F σ ι l x := by
  ext v : 1
  refine PiLp.ext fun b => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, stageEmbed_apply]
  change oracles F.data l (x, b.2) (stageEmbed ι σ v b) = _
  rw [stageEmbed_apply]
  split_ifs with h
  · change _ = oracles (stageData F.data σ) l (x, b.1.2) (v b.1)
    rw [stageData, oracles_reindexData, h]
  · exact map_zero _

/-- **Boolean certificates transfer along a placement**: an implementation of the family's
access (branch register `ι × Fin M`) on an encoding `Enc` implements the access along `σ` on
`Enc ∘ stageEmbed`, with the same cost. -/
theorem implementsOn_stage (F : Family X N Z K s) {M : ℕ} (σ : Fin M → Fin K) (ι : Type*)
    [Fintype ι] {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    {Q : X → B →L[ℂ] B} (Enc : Workspace (ι × Fin M) N Z K →L[ℂ] B) (l : Query) (c : ℕ)
    (h : EncodedOracle.ImplementsOn Q (F.access (ι × Fin M) l) Enc c) :
    EncodedOracle.ImplementsOn Q (stageAccess F σ ι l) (Enc ∘L stageEmbed ι σ) c := by
  obtain ⟨p, hp, hc⟩ := h
  refine ⟨p, fun x => ?_, hc⟩
  rw [← ContinuousLinearMap.comp_assoc, hp x, ContinuousLinearMap.comp_assoc,
    access_stageEmbed, ContinuousLinearMap.comp_assoc]

end

end ODELowerBoundExtensions.Release
