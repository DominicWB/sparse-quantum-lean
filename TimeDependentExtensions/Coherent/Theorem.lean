import TimeDependentExtensions.ODE.Select
import TimeDependentExtensions.Hamiltonian.Theorem

set_option autoImplicit false

/-!
# Coherent selection of durations and start times

The paragraphs after the proof of Theorem `hs:thm:time`: the proof permits coherent selection of
known durations and start times, provided the corresponding coherent sampled-time oracle is supplied
and a common schedule is fixed for the largest total time. Here the selection register is a branch
label `i`; on slot `k` branch `i` evolves for `u_i(σ k) / N`, hence for `n_r u_i(r) / N` on the
`n_r` slots that read sample `r`, with public `0 ≤ u_i(r) ≤ T`; the values `u_i(r) ∈ {0, T}` switch
the intervals of a window on and off (`windows`).

The SELECT on `N` slots of `MeshSelect` simulates, coherently in a branch label, the ordered
products of the tagged LCHS Hamiltonians with branch-dependent durations. For Hamiltonian
samples it is applied to the generator samples `i H̃_r` (`rotate`): the rotation changes only
the public decoder, not the supplied locators or value table, so the queries are those of the
sampled-time sparse oracle with a branch spectator, and the LCHS Hamiltonian of `i H̃` is
`H̃` at every frequency (`lchsHamiltonian_rotate`).

* `coherent_select`: one rescaling `γ`, hence one oracle family and one clean encoding, fixed
  by the largest duration `T`, serves every public table of durations `0 ≤ u_i(r) ≤ T`: for
  each table there is a program (its query-free gates depend on the table) with at most
  `663552 · shape (2s) (η T) (log (2/ε))` queries whose full output is within `ε` of
  `∑_i |i⟩⟨i| ⊗ ∏_k exp(-i (u_i(σ k) / N) H̃_{σ k})`.
* `coherent_windows`: start times and stop times at mesh points, `[t_{a_i}, t_{b_i}]`: with
  the same oracle family and clean encoding for every table of windows, the output is within
  `ε` of `∑_i |i⟩⟨i| ⊗ V_i(t_{b_i})` for every family of propagators `V_i` of the piecewise
  path from the identity at `t_{a_i}`, under the integrated certificate
  `∑_r ∫ ‖H_r - H̃_r‖ ≤ ε / 3`.
-/

namespace TimeDependentExtensions

namespace Coherent

noncomputable section

open SparseHamiltonian SparseHamiltonian.TimeDependent ContinuousLinearMap OracleCircuit
open NativeSparseBlockEncoding MeasureTheory Set
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

/-! ### Rotated samples -/

section Rotate

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- The generator samples `i H̃`, with the same supplied locators and value table. -/
def rotate (D : Data X n Z s) : Data X n Z s where
  slot := D.slot
  slots_pos := D.slots_pos
  scale := D.scale
  scale_pos := D.scale_pos
  matrix := fun x i j => Complex.I * D.matrix x i j
  table := D.table
  decode := fun a z => Complex.I * D.decode a z
  decode_bound := by
    intro a z
    rw [norm_mul, Complex.norm_I, one_mul]
    exact D.decode_bound a z
  decoded := by
    intro x i j
    rw [D.decoded]
  rowloc := D.rowloc
  colloc := D.colloc
  row_injective := D.row_injective
  column_injective := D.column_injective
  row_covers := by
    intro x i j h
    apply D.row_covers x i j
    intro hz
    exact h (by rw [hz, mul_zero])
  column_covers := by
    intro x i j h
    apply D.column_covers x i j
    intro hz
    exact h (by rw [hz, mul_zero])
  rowOracle := D.rowOracle
  columnOracle := D.columnOracle
  row_unitary := D.row_unitary
  column_unitary := D.column_unitary
  row_valid := D.row_valid
  column_valid := D.column_valid

theorem hamiltonianPart_rotate (D : Data X n Z s) (y : X) (hH : (D.matrix y).IsHermitian) :
    ODEMatrixEnergy.hamiltonianPart ((rotate D).matrix y) = D.matrix y := by
  ext i j
  rw [ODEMatrixEnergy.hamiltonianPart_apply]
  change (-Complex.I / 2) * (Complex.I * D.matrix y i j - star (Complex.I * D.matrix y j i)) =
    D.matrix y i j
  rw [star_mul', hH.apply i j, Complex.star_def, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem dissipativePart_rotate (D : Data X n Z s) (y : X) (hH : (D.matrix y).IsHermitian) :
    ODEMatrixEnergy.dissipativePart ((rotate D).matrix y) = 0 := by
  ext i j
  rw [ODEMatrixEnergy.dissipativePart_apply]
  change (2 : ℂ)⁻¹ * (Complex.I * D.matrix y i j + star (Complex.I * D.matrix y j i)) = 0
  rw [star_mul', hH.apply i j, Complex.star_def, Complex.conj_I]
  ring

/-- The LCHS Hamiltonian of the rotated samples is the Hamiltonian at every frequency. -/
theorem lchsHamiltonian_rotate (D : Data X n Z s) (y : X) (hH : (D.matrix y).IsHermitian)
    (k : ℝ) : ODEMatrixEnergy.lchsHamiltonian ((rotate D).matrix y) k = D.matrix y := by
  rw [ODEMatrixEnergy.lchsHamiltonian, hamiltonianPart_rotate D y hH,
    dissipativePart_rotate D y hH, smul_zero, add_zero]

end Rotate

/-! ### Coherent durations -/

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s M : ℕ}

/-- The ordered products with branch-dependent durations, on the branch register. -/
def selected (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (N : ℕ) (u : ι → Fin M → ℝ)
    (x : X) : ODEJointNative.Public ι n →L[ℂ] ODEJointNative.Public ι n :=
  WeightedClock.diagonal (fun i => evolution (fun k => NormedSpace.exp
    ((-Complex.I * ((u i (σ k) / N : ℝ) : ℂ)) •
      SparseStateOverlap.matrixOperator (D.matrix (x, σ k)))) N)

set_option maxRecDepth 8192 in
/-- **Coherent selection of durations.** One rescaling `γ`, hence one oracle family and one
clean encoding, fixed by the filter schedule of the largest duration `T`, serves every public
duration table `0 ≤ u_i(r) ≤ T`: for each table there is a program, with the same query bound,
whose output is within `ε` of the coherently selected products. -/
theorem coherent_select (D : Data (X × Fin M) n Z s) (hM : 0 < M) (σ : ℕ → Fin M) {N : ℕ}
    (hN : 0 < N) (b0 : ι × Fin M) (η T ε : ℝ) (hη : 0 < η) (hT : 0 < T) (hε : 0 < ε)
    (hεOne : ε ≤ 1)
    (hH : ∀ y, (D.matrix y).IsHermitian)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hClock : 8 * s * (η * T) ≤ N)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) * (η * T)) ^ 3 ≤ ε * (N : ℝ) ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (2 * (s : ℝ)) ∧
      ∀ u : ι → Fin M → ℝ, (∀ i r, 0 ≤ u i r) → (∀ i r, u i r ≤ T) →
        ∃ p : MultiOracleCircuit.Program (MeshSelect.alignedOracle (ι := ι) D N γ η T ε),
          (p.count : ℝ) ≤ 663552 * ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (η * T)
            (ImprovedPrecisionBudget.targetLog ε) ∧
          (MeshSelect.alignedInput D hM σ b0 N γ η T ε)† ∘L
            MeshSelect.alignedInput D hM σ b0 N γ η T ε = 1 ∧
          ∀ x, IsUnitary (p.eval x) ∧
            ‖p.eval x ∘L MeshSelect.alignedInput D hM σ b0 N γ η T ε -
              MeshSelect.alignedInput D hM σ b0 N γ η T ε ∘L selected D σ N u x‖ ≤ ε := by
  have hρ : η + 0 * 0 = η := by ring
  have h := MeshSelect.select (ι := ι) (rotate D) hM σ hN b0 η 0 0 T ε hη.le le_rfl
    (by rw [hρ]; exact hη) hT hε hεOne
    (fun y i => by simpa only [hamiltonianPart_rotate D y (hH y)] using hrow y i)
    (fun y j => by simpa only [hamiltonianPart_rotate D y (hH y)] using hcol y j)
    (fun y i => by rw [dissipativePart_rotate D y (hH y)]; simp)
    (fun y j => by rw [dissipativePart_rotate D y (hH y)]; simp)
    (by rw [hρ]; exact hClock) (by rw [hρ]; exact hCayley)
  rw [hρ] at h
  obtain ⟨γ, hγ, hγOne, hWidth, hAll⟩ := h
  refine ⟨γ, hγ, hγOne, hWidth, fun u hu huT => ?_⟩
  obtain ⟨p, hCount, hIn, hAct⟩ := hAll (fun _ => 0) u (fun _ => by simp) hu huT
  refine ⟨p, hCount, hIn, fun x => ⟨(hAct x).1, ?_⟩⟩
  have hsel : MeshSelect.selectEvolution (rotate D) σ N (fun _ => 0) u x = selected D σ N u x := by
    unfold MeshSelect.selectEvolution selected MeshSelect.branchEvolution
    congr 1
    funext i
    congr 1
    funext k
    rw [lchsHamiltonian_rotate D _ (hH _)]
  rw [← hsel]
  exact (hAct x).2

/-! ### Windows of the mesh -/

section Windows

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

omit [CompleteSpace P] in
theorem orderedProduct_eq_evolution (F : ℕ → P →L[ℂ] P) (a m : ℕ) :
    TimeDependent.orderedProduct F a m = evolution (fun j => F (a + j)) m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [TimeDependent.orderedProduct_succ, evolution_succ, ih]

omit [CompleteSpace P] in
theorem orderedProduct_congr (F F' : ℕ → P →L[ℂ] P) (k m : ℕ)
    (h : ∀ j < m, F (k + j) = F' (k + j)) :
    TimeDependent.orderedProduct F k m = TimeDependent.orderedProduct F' k m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [TimeDependent.orderedProduct_succ, TimeDependent.orderedProduct_succ,
      h m (Nat.lt_succ_self m), ih (fun j hj => h j (Nat.lt_succ_of_lt hj))]

omit [CompleteSpace P] in
/-- An ordered product whose factors are the identity outside `[a, b)` is the product over
`[a, b)`. -/
theorem evolution_window (F : ℕ → P →L[ℂ] P) {a b M : ℕ} (hab : a ≤ b) (hbM : b ≤ M)
    (h1 : ∀ r, (r < a ∨ b ≤ r) → F r = 1) :
    evolution F M = TimeDependent.orderedProduct F a (b - a) := by
  have hM : M = a + ((b - a) + (M - b)) := by omega
  change TimeDependent.orderedProduct F 0 M = _
  rw [hM, orderedProduct_add, orderedProduct_add, zero_add,
    orderedProduct_congr_const F 1 0 a (fun j hj => h1 _ (Or.inl (by omega))),
    orderedProduct_congr_const F 1 (a + (b - a)) (M - b)
      (fun j _ => h1 _ (Or.inr (by omega)))]
  simp

/-- **Duhamel on a window of the mesh**: a propagator from the identity at `t_a` is within the
integrated sample errors of the intervals `a, …, a + m - 1` of the product of the step
exponentials over those intervals. -/
theorem window_error {Hp : ℕ → ℝ → P →L[ℂ] P} (Hs : ℕ → P →L[ℂ] P) {V : ℝ → P →L[ℂ] P}
    {t : ℕ → ℝ} (hmono : Monotone t) (a m : ℕ) (hV0 : V (t a) = 1)
    (hV : ∀ j < m, SolvesOn (Hp (a + j)) V (t (a + j)) (t (a + j + 1)))
    (hH : ∀ j < m, ∀ u ∈ Icc (t (a + j)) (t (a + j + 1)), star (Hp (a + j) u) = Hp (a + j) u)
    (hHs : ∀ r, star (Hs r) = Hs r)
    (hint : ∀ j < m, IntervalIntegrable (Hp (a + j)) volume (t (a + j)) (t (a + j + 1))) :
    ‖V (t (a + m)) - TimeDependent.orderedProduct (fun r => NormedSpace.exp
        ((-Complex.I * ((t (r + 1) - t r : ℝ) : ℂ)) • Hs r)) a m‖ ≤
      ∑ j ∈ Finset.range m, ∫ u in t (a + j)..t (a + j + 1), ‖Hp (a + j) u - Hs (a + j)‖ := by
  have hnode : ∀ j ≤ m, ∀ v : P, ‖V (t (a + j)) v‖ = ‖v‖ := by
    intro j
    induction j with
    | zero => intro _ v; rw [add_zero, hV0, one_apply_eq_self]
    | succ j ih =>
      intro hj v
      have hmem : t (a + j + 1) ∈ Icc (t (a + j)) (t (a + j + 1)) :=
        ⟨hmono (Nat.le_succ _), le_rfl⟩
      rw [← add_assoc, (hV j (by omega)).norm_apply_eq (hH j (by omega)) v _ hmem,
        ih (by omega)]
  have hnorm : ∀ j < m, ∀ u ∈ Icc (t (a + j)) (t (a + j + 1)), ‖V u‖ ≤ 1 := by
    intro j hj u hu
    apply opNorm_le_bound _ zero_le_one
    intro v
    rw [(hV j hj).norm_apply_eq (hH j hj) v u hu, hnode j hj.le v, one_mul]
  rw [orderedProduct_eq_evolution]
  have htel := propagator_telescope V (fun j => NormedSpace.exp
    ((-Complex.I * ((t (a + j + 1) - t (a + j) : ℝ) : ℂ)) • Hs (a + j)))
    (fun j => exp_skew_norm_le (Hs (a + j)) (hHs _) _) (fun j => t (a + j)) hV0 m
  refine htel.trans (Finset.sum_le_sum fun j hj => ?_)
  have hjm := Finset.mem_range.mp hj
  have h := duhamel_integral (Hs (a + j)) (hmono (Nat.le_succ (a + j))) (hV j hjm)
    (hnorm j hjm) (hHs _) (hint j hjm)
  simpa only [← add_assoc] using h

end Windows

/-- The public duration table of the windows `[t_{a_i}, t_{b_i}]`. -/
def windows (T : ℝ) (a b : ι → ℕ) (i : ι) (r : Fin M) : ℝ :=
  if a i ≤ (r : ℕ) ∧ (r : ℕ) < b i then T else 0

set_option maxRecDepth 8192 in
/-- **Coherent start times and durations at mesh points.** One rescaling `γ`, hence one oracle
family and one clean encoding, serves every public table of windows `a_i ≤ b_i ≤ M`: for each
table there is a program such that, for every instance, every piecewise path whose integrated
sample errors are at most `ε / 3`, and every family of propagators `V_i` of that path from the
identity at `t_{a_i}`, the full output is within `ε` of `∑_i |i⟩⟨i| ⊗ V_i(t_{b_i})`. The slot
conditions are `8 s η T ≤ N`, `9 (√(2s) η T)³ ≤ ε N²` and `3 M √s η T ≤ ε N`. -/
theorem coherent_windows (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) (b0 : ι × Fin M) (η T ε : ℝ) (hη : 0 < η) (hT : 0 < T) (hε : 0 < ε)
    (hεOne : ε ≤ 1) (hmesh : IsMesh t M T)
    (hH : ∀ y, (D.matrix y).IsHermitian)
    (hrow : ∀ y i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ y j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ η ^ 2)
    (hClock : 8 * s * (η * T) ≤ N)
    (hCayley : 9 * (Real.sqrt (2 * (s : ℝ)) * (η * T)) ^ 3 ≤ ε * (N : ℝ) ^ 2)
    (hRefine : 3 * M * (Real.sqrt s * (η * T)) ≤ ε * N) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (2 * (s : ℝ)) ∧
      ∀ a b : ι → ℕ, (∀ i, a i ≤ b i) → (∀ i, b i ≤ M) →
      ∃ p : MultiOracleCircuit.Program
          (MeshSelect.alignedOracle (ι := ι) D N γ η T (ε / 3)),
        (p.count : ℝ) ≤ 663552 * ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (η * T)
          (ImprovedPrecisionBudget.targetLog (ε / 3)) ∧
        (MeshSelect.alignedInput D hM (pieceOf t T N hM) b0 N γ η T (ε / 3))† ∘L
          MeshSelect.alignedInput D hM (pieceOf t T N hM) b0 N γ η T (ε / 3) = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ (Hp : Fin M → ℝ → Matrix n n ℂ) (V : ι → ℝ → EuclideanSpace ℂ n →L[ℂ]
              EuclideanSpace ℂ n),
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), (Hp r u).IsHermitian) →
            (∀ r : Fin M, IntervalIntegrable
              (fun u => SparseStateOverlap.matrixOperator (Hp r u)) volume
                (t r) (t ((r : ℕ) + 1))) →
            ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
              ‖SparseStateOverlap.matrixOperator (Hp r u) -
                SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 3 →
            (∀ i, V i (t (a i)) = 1) →
            (∀ i (r : Fin M), a i ≤ (r : ℕ) → (r : ℕ) < b i →
              SolvesOn (fun u => SparseStateOverlap.matrixOperator (Hp r u)) (V i)
                (t r) (t ((r : ℕ) + 1))) →
            ‖p.eval x ∘L MeshSelect.alignedInput D hM (pieceOf t T N hM) b0 N γ η T (ε / 3) -
              MeshSelect.alignedInput D hM (pieceOf t T N hM) b0 N γ η T (ε / 3) ∘L
                WeightedClock.diagonal (fun i => V i (t (b i)))‖ ≤ ε := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨γ, hγ, hγOne, hWidth, hAll⟩ := coherent_select D hM (pieceOf t T N hM) hN b0 η T
    (ε / 3) hη hT hε3 (by linarith) hH hrow hcol hClock (by nlinarith)
  refine ⟨γ, hγ, hγOne, hWidth, fun a b hab hbM => ?_⟩
  have hu : ∀ i r, 0 ≤ windows (M := M) T a b i r := fun i r => by
    unfold windows; split_ifs <;> linarith
  have huT : ∀ i r, windows (M := M) T a b i r ≤ T := fun i r => by
    unfold windows; split_ifs <;> linarith
  obtain ⟨p, hCount, hIn, hAct⟩ := hAll (windows T a b) hu huT
  refine ⟨p, hCount, hIn, fun x => ⟨(hAct x).1, ?_⟩⟩
  intro Hp V hPath hInt hCert hV0 hV
  set ι' := MeshSelect.alignedInput D hM (pieceOf t T N hM) b0 N γ η T (ε / 3)
  have hιn : ‖ι'‖ ≤ 1 := SparseMatrixNorm.norm_le_one_of_adjoint_comp _ hIn
  -- The per-branch distance of the selected product from the window propagator.
  let A : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
    SparseStateOverlap.matrixOperator (D.matrix (x, Sampled.sampleIndex hM r))
  have hA : ∀ r, star (A r) = A r := fun r =>
    SparseValuePrecision.matrixOperator_star_eq _ (hH _)
  have hΛ : ∀ r, ‖A r‖ ≤ Real.sqrt s * η := fun r =>
    Hamiltonian.sample_norm_le D η hη _ (hH _) (hrow _) (hcol _)
  have hbranch : ∀ i, ‖(evolution (fun k => NormedSpace.exp
      ((-Complex.I * ((windows T a b i (pieceOf t T N hM k) / N : ℝ) : ℂ)) •
        SparseStateOverlap.matrixOperator (D.matrix (x, pieceOf t T N hM k)))) N) -
      V i (t (b i))‖ ≤ ε / 3 + ε / 3 := by
    intro i
    -- Group the slots by mesh interval.
    let w' : ℕ → ℝ := fun r => if a i ≤ r ∧ r < b i then T else 0
    let f : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
      NormedSpace.exp ((-Complex.I * ((w' r / N : ℝ) : ℂ)) • A r)
    have hslot : evolution (fun k => NormedSpace.exp
        ((-Complex.I * ((windows T a b i (pieceOf t T N hM k) / N : ℝ) : ℂ)) •
          SparseStateOverlap.matrixOperator (D.matrix (x, pieceOf t T N hM k)))) N =
        evolution (fun k => f (slotPiece t T N M k)) N := by
      congr 1
      funext k
      have hk : Sampled.sampleIndex hM (slotPiece t T N M k) = pieceOf t T N hM k :=
        Hamiltonian.sampleIndex_of_lt hM (slotPiece_lt hM k)
      simp only [f, A, hk]
      rfl
    let ℓ : ℕ → ℝ := fun r => (blockLength t T N r : ℝ) * (T / N)
    let G : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
      NormedSpace.exp ((-Complex.I * ((ℓ r : ℝ) : ℂ)) • A r)
    have hgroup : evolution (fun k => f (slotPiece t T N M k)) N =
        TimeDependent.orderedProduct G (a i) (b i - a i) := by
      rw [evolution_slotPiece f hmesh hT]
      have hf : ∀ r, f r ^ blockLength t T N r =
          if a i ≤ r ∧ r < b i then G r else 1 := by
        intro r
        show NormedSpace.exp ((-Complex.I * ((w' r / N : ℝ) : ℂ)) • A r) ^
          blockLength t T N r = _
        rw [exp_pow]
        by_cases hr : a i ≤ r ∧ r < b i
        · rw [if_pos hr]
          show NormedSpace.exp _ = NormedSpace.exp ((-Complex.I * ((ℓ r : ℝ) : ℂ)) • A r)
          congr 4
          simp only [w', if_pos hr, ℓ]
        · rw [if_neg hr]
          simp only [w', if_neg hr, zero_div, mul_zero, Complex.ofReal_zero, zero_smul,
            NormedSpace.exp_zero]
      rw [evolution_congr' _ _ M (fun r _ => hf r),
        evolution_window (fun r => if a i ≤ r ∧ r < b i then G r else 1) (hab i) (hbM i)
          (fun r hr => if_neg (by omega))]
      exact orderedProduct_congr _ _ _ _ (fun j hj => if_pos (by omega))
    -- The mesh product over the window.
    let E : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
      NormedSpace.exp ((-Complex.I * ((t (r + 1) - t r : ℝ) : ℂ)) • A r)
    have hmis : ‖TimeDependent.orderedProduct G (a i) (b i - a i) -
        TimeDependent.orderedProduct E (a i) (b i - a i)‖ ≤ ε / 3 := by
      rw [orderedProduct_eq_evolution, orderedProduct_eq_evolution]
      have hstep : ∀ j, ‖G (a i + j) - E (a i + j)‖ ≤ T / N * (Real.sqrt s * η) := by
        intro j
        refine (exp_sub_exp_norm_le (A _) (hA _) _ _).trans ?_
        exact mul_le_mul (blockLength_sub_lt hmesh hT hN _).le (hΛ _) (norm_nonneg _)
          (div_pos hT hNR).le
      have h1 := evolution_sub_norm_le_mul _ _ (fun j => exp_skew_norm_le (A _) (hA _) _)
        (fun j => exp_skew_norm_le (A _) (hA _) _) hstep (b i - a i)
      have hlen : ((b i - a i : ℕ) : ℝ) ≤ M := by
        exact_mod_cast (show b i - a i ≤ M by have := hbM i; omega)
      have hbound : (M : ℝ) * (T / N * (Real.sqrt s * η)) ≤ ε / 3 := by
        have heq : (M : ℝ) * (T / N * (Real.sqrt s * η)) =
            M * (Real.sqrt s * (η * T)) / N := by
          field_simp
        rw [heq, div_le_iff₀ hNR]
        linarith
      calc _ ≤ ((b i - a i : ℕ) : ℝ) * (T / N * (Real.sqrt s * η)) := h1
        _ ≤ (M : ℝ) * (T / N * (Real.sqrt s * η)) :=
          mul_le_mul_of_nonneg_right hlen (by positivity)
        _ ≤ ε / 3 := hbound
    -- Duhamel on the window.
    let Hq : ℕ → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r u =>
      SparseStateOverlap.matrixOperator (Hp (Sampled.sampleIndex hM r) u)
    have hwin := window_error (Hp := Hq) A hmesh.mono (a i) (b i - a i) (hV0 i)
      (fun j hj => by
        have hr : a i + j < M := by have := hbM i; omega
        have h := hV i ⟨a i + j, hr⟩ (by simp) (by simp; omega)
        simp only [Hq, Hamiltonian.sampleIndex_of_lt hM hr]
        exact h)
      (fun j hj u hu => by
        have hr : a i + j < M := by have := hbM i; omega
        simp only [Hq, Hamiltonian.sampleIndex_of_lt hM hr]
        exact SparseValuePrecision.matrixOperator_star_eq _ (hPath ⟨a i + j, hr⟩ u hu))
      hA
      (fun j hj => by
        have hr : a i + j < M := by have := hbM i; omega
        simp only [Hq, Hamiltonian.sampleIndex_of_lt hM hr]
        exact hInt ⟨a i + j, hr⟩)
    have hab' : a i + (b i - a i) = b i := by have := hab i; omega
    rw [hab'] at hwin
    have hnonneg : ∀ r, 0 ≤ ∫ u in t r..t (r + 1), ‖Hq r u - A r‖ := fun r =>
      intervalIntegral.integral_nonneg (hmesh.mono (Nat.le_succ r)) (fun u _ => norm_nonneg _)
    have hsum : ∑ j ∈ Finset.range (b i - a i), ∫ u in t (a i + j)..t (a i + j + 1),
        ‖Hq (a i + j) u - A (a i + j)‖ ≤ ε / 3 := by
      rw [← Finset.sum_Ico_eq_sum_range (fun r => ∫ u in t r..t (r + 1), ‖Hq r u - A r‖)]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.range M) ?_
        (fun r _ _ => hnonneg r)) ?_
      · intro r hr
        rw [Finset.mem_Ico] at hr
        rw [Finset.mem_range]
        have := hbM i
        omega
      · rw [← Fin.sum_univ_eq_sum_range (fun r => ∫ u in t r..t (r + 1), ‖Hq r u - A r‖) M]
        have hidx : ∀ r : Fin M, Sampled.sampleIndex hM r = r := fun r =>
          Hamiltonian.sampleIndex_val hM r
        simpa only [Hq, A, hidx] using hCert
    rw [hslot, hgroup]
    calc ‖TimeDependent.orderedProduct G (a i) (b i - a i) - V i (t (b i))‖ ≤
          ‖TimeDependent.orderedProduct G (a i) (b i - a i) -
            TimeDependent.orderedProduct E (a i) (b i - a i)‖ +
          ‖TimeDependent.orderedProduct E (a i) (b i - a i) - V i (t (b i))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε / 3 + ε / 3 := by
        apply add_le_add hmis
        rw [norm_sub_rev]
        exact hwin.trans hsum
  have hsel := (hAct x).2
  have hdiag : selected D (pieceOf t T N hM) N (windows T a b) x -
      WeightedClock.diagonal (fun i => V i (t (b i))) =
        WeightedClock.diagonal (fun i => evolution (fun k => NormedSpace.exp
          ((-Complex.I * ((windows T a b i (pieceOf t T N hM k) / N : ℝ) : ℂ)) •
            SparseStateOverlap.matrixOperator (D.matrix (x, pieceOf t T N hM k)))) N -
          V i (t (b i))) := by
    ext v i
    rfl
  have hdn : ‖selected D (pieceOf t T N hM) N (windows T a b) x -
      WeightedClock.diagonal (fun i => V i (t (b i)))‖ ≤ ε / 3 + ε / 3 := by
    rw [hdiag]
    exact WeightedClock.norm_diagonal_le _ _ (by positivity) hbranch
  calc ‖p.eval x ∘L ι' - ι' ∘L WeightedClock.diagonal (fun i => V i (t (b i)))‖ ≤
        ‖p.eval x ∘L ι' - ι' ∘L selected D (pieceOf t T N hM) N (windows T a b) x‖ +
        ‖ι' ∘L selected D (pieceOf t T N hM) N (windows T a b) x -
          ι' ∘L WeightedClock.diagonal (fun i => V i (t (b i)))‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε / 3 + 1 * (ε / 3 + ε / 3) := by
      apply add_le_add hsel
      rw [← comp_sub]
      exact (opNorm_comp_le _ _).trans (mul_le_mul hιn hdn (norm_nonneg _) zero_le_one)
    _ = ε := by ring
end

end Coherent

end TimeDependentExtensions
