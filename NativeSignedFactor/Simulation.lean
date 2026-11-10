import NativeSignedFactor.Physical

set_option autoImplicit false

/-!
# Simulation with the native factor

Theorem `opt:thm:signed` applied to the native factor gives a sparse Hamiltonian simulation whose
only oracle calls are the original native primitives with spectator registers (`opt:sec:native`,
last paragraph: "Theorem `opt:thm:signed` is therefore available with `T = sτ` and `b = √s τ`").
Every factor query `I_ι ⊗ U_B` of the signed-factor program, and its adjoint, is replaced by the
physical factor program applied on every block of `ℂ^ι ⊗ W` (`diagProgram`, `subst`), which costs
`12` native calls.

* `native_signed_simulation`: entries of modulus at most `κ`, row and column Euclidean norms at
  most `η ≤ √s κ`; `T = sκ|t|` and `b = √s η|t|`.
* `native_signed_simulation_eta`: the case `κ = η` of the paper, `T = sτ` and `b = √s τ` with
  `τ = η|t|`.
-/

namespace NativeSignedFactor

noncomputable section

open ContinuousLinearMap SparseHamiltonian OracleCircuit NativeSparseBlockEncoding
open OrientedNativeLayout SparseEdgeMoments SignedFactorSimulation
open scoped InnerProduct

/-! ### Program constructions -/

section Programs

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {X L : Type*}

/-- Apply a program on every block of `ℂ^ι ⊗ K`; every oracle call becomes the same call with
the block register a spectator. -/
def diagProgram (ι : Type*) [Fintype ι] {O : L → X → K →L[ℂ] K} :
    MultiOracleCircuit.Program O →
      MultiOracleCircuit.Program (CoherentQuerySchedule.oracle (ι := ι) O)
  | .fixed U hU => .fixed _ (CoherentQuerySchedule.diagonal_unitary (fun _ : ι => U) (fun _ => hU))
  | .query l => .query l
  | .queryAdjoint l => .queryAdjoint l
  | .seq p q => .seq (diagProgram ι p) (diagProgram ι q)

@[simp] theorem diagProgram_count (ι : Type*) [Fintype ι] {O : L → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program O) : (diagProgram ι p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [diagProgram, MultiOracleCircuit.Program.count_seq, hp, hq]

@[simp] theorem diagProgram_cost (ι : Type*) [Fintype ι] {O : L → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program O) (w : L → ℕ) : (diagProgram ι p).cost w = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [diagProgram, MultiOracleCircuit.Program.cost_seq, hp, hq]

theorem diagProgram_eval (ι : Type*) [Fintype ι] {O : L → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program O) (x : X) :
    (diagProgram ι p).eval x = WeightedClock.diagonal (fun _ : ι => p.eval x) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => exact WeightedClock.diagonal_adjoint _
  | seq p q hp hq =>
      simp only [diagProgram, MultiOracleCircuit.Program.eval_seq, hp, hq]
      exact WeightedClock.diagonal_comp _ _

/-- Replace every call of a single oracle by a program over another oracle family, and every
adjoint call by the adjoint program. -/
def subst {F : L → X → K →L[ℂ] K} {O : X → K →L[ℂ] K} (c : MultiOracleCircuit.Program F) :
    OracleCircuit.Program O → MultiOracleCircuit.Program F
  | .fixed U hU => .fixed U hU
  | .query => c
  | .queryAdjoint => c.adjoint
  | .seq p q => .seq (subst c p) (subst c q)

theorem subst_count {F : L → X → K →L[ℂ] K} {O : X → K →L[ℂ] K}
    (c : MultiOracleCircuit.Program F) (p : OracleCircuit.Program O) :
    (subst c p).count = p.count * c.count := by
  induction p with
  | fixed U hU => simp [subst]
  | query => simp [subst]
  | queryAdjoint => simp [subst, MultiOracleCircuit.Program.count_adjoint]
  | seq p q hp hq =>
      simp only [subst, MultiOracleCircuit.Program.count_seq, OracleCircuit.Program.count_seq,
        hp, hq, add_mul]

theorem subst_cost {F : L → X → K →L[ℂ] K} {O : X → K →L[ℂ] K}
    (c : MultiOracleCircuit.Program F) (p : OracleCircuit.Program O) (w : L → ℕ) :
    (subst c p).cost w = p.count * c.cost w := by
  induction p with
  | fixed U hU => simp [subst]
  | query => simp [subst]
  | queryAdjoint => simp [subst, MultiOracleCircuit.Program.cost_adjoint]
  | seq p q hp hq =>
      simp only [subst, MultiOracleCircuit.Program.cost_seq, OracleCircuit.Program.count_seq,
        hp, hq, add_mul]

theorem subst_eval {F : L → X → K →L[ℂ] K} {O : X → K →L[ℂ] K}
    (c : MultiOracleCircuit.Program F) (hc : ∀ x, c.eval x = O x)
    (p : OracleCircuit.Program O) (x : X) : (subst c p).eval x = p.eval x := by
  induction p with
  | fixed U hU => rfl
  | query => exact hc x
  | queryAdjoint =>
      change c.adjoint.eval x = star (O x)
      rw [MultiOracleCircuit.Program.eval_adjoint, hc]
  | seq p q hp hq =>
      simp only [subst, MultiOracleCircuit.Program.eval_seq, OracleCircuit.Program.eval_seq,
        hp, hq]

end Programs

/-! ### The simulation predicate -/

section Predicate

variable {P W : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  {X L : Type*}

/-- `Simulates O H t ε q`: there are a finite label type `ι`, a known isometry
`inp : P → ℂ^ι ⊗ W` (the space `PiLp 2 (fun _ : ι => W)`) and a program whose only oracle calls
are calls of the family `O` on every block of `ℂ^ι ⊗ W` (`CoherentQuerySchedule.oracle`), with
at most `q` calls counting adjoints, unitary for every instance, and with full-output error at
most `ε` for `e^{-itH(x)}` with the same known embedding on input and output. -/
def Simulates (O : L → X → W →L[ℂ] W) (H : X → P →L[ℂ] P) (t ε q : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (inp : P →L[ℂ] PiLp 2 (fun _ : ι => W))
    (p : MultiOracleCircuit.Program (CoherentQuerySchedule.oracle (ι := ι) O)),
    inp† ∘L inp = 1 ∧ (p.count : ℝ) ≤ q ∧
    ∀ x, IsUnitary (p.eval x) ∧
      ‖p.eval x ∘L inp - inp ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) • H x)‖ ≤ ε

theorem Simulates.mono {O : L → X → W →L[ℂ] W} {H : X → P →L[ℂ] P} {t ε q q' : ℝ}
    (h : Simulates O H t ε q) (hq : q ≤ q') : Simulates O H t ε q' := by
  obtain ⟨ι, hι, inp, p, hinp, hcount, hrest⟩ := h
  exact ⟨ι, hι, inp, p, hinp, hcount.trans hq, hrest⟩

/-- **Theorem `opt:thm:signed` with a programmed factor.** If the factor unitary of a known
factor structure is the evaluation of a program `c` over an oracle family `F`, then the
signed-factor simulation, with every factor query replaced by `c` on every block (and every
adjoint query by the adjoint of `c`), simulates `H` with `c.count` times the query bound of
`signed_factor_simulation`. -/
theorem simulates_of_factor [FiniteDimensional ℂ P] [FiniteDimensional ℂ W] (K : Known P W)
    (F : L → X → W →L[ℂ] W) (hF : ∀ l x, IsUnitary (F l x)) (c : MultiOracleCircuit.Program F)
    (H : X → P →L[ℂ] P) {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hD : ∀ x, K.Dop (c.eval x) ≤ (δ : ℂ) • (1 : P →L[ℂ] P))
    (hH : ∀ x, K.ham lam (c.eval x) = H x) (t : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    Simulates F H t ε ((c.count : ℝ) * (if lam * |t| * δ ≤ ε then 0 else
      4 * 10 ^ 10 * (Real.sqrt (lam * |t| * (lam * |t| * δ)) +
        Real.sqrt (lam * |t| * rb (lam * |t| * δ) ε) + rb (lam * |t| * δ) ε))) := by
  obtain ⟨ι, hι, inp, p, hinp, hcount, herr⟩ :=
    signed_factor_simulation K (fun x => c.eval x) (fun x => c.eval_unitary hF x) hlam hδ hδ1
      hD t hε hε1
  have hc : ∀ x, (diagProgram ι c).eval x = WeightedClock.diagonal (fun _ : ι => c.eval x) :=
    fun x => diagProgram_eval ι c x
  refine ⟨ι, hι, inp, subst (diagProgram ι c) p, hinp, ?_, fun x => ⟨?_, ?_⟩⟩
  · rw [subst_count, diagProgram_count, Nat.cast_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left hcount (Nat.cast_nonneg _)
  · exact MultiOracleCircuit.Program.eval_unitary _
      (fun l y => CoherentQuerySchedule.oracle_unitary _ hF l y) x
  · rw [subst_eval _ hc p x, ← hH x]
    exact herr x

end Predicate

/-! ### The simulation theorems -/

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

/-- **Native signed-factor simulation**, general entry scale. Let `H = D.matrix x` be Hermitian
with entries of modulus at most `κ` and row and column Euclidean norms at most `η`, where
`η ≤ √s κ`. For every time `t` and `0 < ε ≤ 1/64`, `e^{-itH}` is simulated (`Simulates`) by a
program whose oracle calls are the original row-locator, column-locator and value oracles with
spectator registers (`physOracle`), using `0` calls if `b ≤ ε` and at most
`12·4·10¹⁰ (√(Tb) + √(T r_b) + r_b)` calls otherwise, with `T = sκ|t|` and `b = √s η|t|`. -/
theorem native_signed_simulation (D : Data X n Z s) {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η)
    (hηκ : η ≤ Real.sqrt (s : ℝ) * κ)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hentry : ∀ x i j, ‖D.matrix x i j‖ ≤ κ)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    Simulates (physOracle D) (fun x => SparseStateOverlap.matrixOperator (D.matrix x)) t ε
      (if Real.sqrt (s : ℝ) * η * |t| ≤ ε then 0 else
        12 * (4 * 10 ^ 10) *
          (Real.sqrt ((s : ℝ) * κ * |t| * (Real.sqrt (s : ℝ) * η * |t|)) +
            Real.sqrt ((s : ℝ) * κ * |t| * rb (Real.sqrt (s : ℝ) * η * |t|) ε) +
              rb (Real.sqrt (s : ℝ) * η * |t|) ε)) := by
  have hs : (0 : ℝ) < s := by exact_mod_cast D.slots_pos
  have hsq : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr hs
  have hlam : 0 < (s : ℝ) * κ := mul_pos hs hκ
  have hδ : 0 < η / (Real.sqrt (s : ℝ) * κ) := div_pos hη (mul_pos hsq hκ)
  have hδ1 : η / (Real.sqrt (s : ℝ) * κ) ≤ 1 := (div_le_one (mul_pos hsq hκ)).mpr hηκ
  have hsim := simulates_of_factor (physKnown D) (physOracle D) (physOracle_unitary D)
    (physProgram D κ) (fun x => SparseStateOverlap.matrixOperator (D.matrix x)) hlam hδ hδ1
    (fun x => Dop_le_of_bound (physKnown D) _ (phys_bound D hκ hη.le x (hrow x) (hcol x)))
    (fun x => phys_ham D hκ x (hH x) (hentry x))
    t hε hε1
  refine hsim.mono (le_of_eq ?_)
  have hb : (s : ℝ) * κ * |t| * (η / (Real.sqrt (s : ℝ) * κ)) =
      Real.sqrt (s : ℝ) * η * |t| := by
    rw [show (s : ℝ) * κ * |t| * (η / (Real.sqrt (s : ℝ) * κ)) =
      ((s : ℝ) / Real.sqrt (s : ℝ)) * η * |t| by field_simp, Real.div_sqrt]
  rw [physProgram_count, hb]
  split_ifs <;> push_cast <;> ring

/-- **Native signed-factor simulation** (`opt:sec:native`, `opt:eq:whole-factor`), the case
`κ = η`: for a Hermitian `H` with row and column Euclidean norms at most `η`, put `τ = η|t|`,
`T = sτ` and `b = √s τ`. The program uses `0` native calls if `b ≤ ε` and at most
`48·10¹⁰ (√(Tb) + √(T r_b) + r_b)` native calls otherwise, with full-output error at most `ε`. -/
theorem native_signed_simulation_eta (D : Data X n Z s) {η : ℝ} (hη : 0 < η)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    Simulates (physOracle D) (fun x => SparseStateOverlap.matrixOperator (D.matrix x)) t ε
      (if Real.sqrt (s : ℝ) * (η * |t|) ≤ ε then 0 else
        48 * 10 ^ 10 *
          (Real.sqrt ((s : ℝ) * (η * |t|) * (Real.sqrt (s : ℝ) * (η * |t|))) +
            Real.sqrt ((s : ℝ) * (η * |t|) * rb (Real.sqrt (s : ℝ) * (η * |t|)) ε) +
              rb (Real.sqrt (s : ℝ) * (η * |t|)) ε)) := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast D.slots_pos
  have hsq1 : 1 ≤ Real.sqrt (s : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hs1
  have hentry : ∀ x i j, ‖D.matrix x i j‖ ≤ η := fun x i j =>
    norm_le_of_energy_le η (D.matrix x i) hη.le (hrow x i) j
  have hηκ : η ≤ Real.sqrt (s : ℝ) * η := le_mul_of_one_le_left hη.le hsq1
  refine (native_signed_simulation D hη hη hηκ hH hentry hrow hcol t hε hε1).mono
    (le_of_eq ?_)
  have e1 : Real.sqrt (s : ℝ) * η * |t| = Real.sqrt (s : ℝ) * (η * |t|) := by ring
  have e2 : (s : ℝ) * η * |t| = (s : ℝ) * (η * |t|) := by ring
  rw [e1, e2]
  split_ifs <;> norm_num

end

end NativeSignedFactor
