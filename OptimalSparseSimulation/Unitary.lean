import OptimalSparseSimulation.Optimal
import UnitaryImplementationPrecision.Inexact

set_option autoImplicit false

/-!
# Corollary `hs:cor:unitary-optimal`: refined precision for unitary implementation

Under the assumptions of Corollary `hs:cor:unitary` (a unitary `U ∈ ℂ^{N×N}` supplied by a
reversible entry-value oracle, exactly or with entrywise error at most `ε/(πN)`,
`0 < ε ≤ 1/2`), the full-output guarantee `‖𝒜_U - U‖ ≤ ε` is achieved with
`O(√(N ρ_ε) + ρ_ε)` entry-oracle queries, `ρ_ε = ℓ/log(e + ℓ)` and `ℓ = log(1/ε)`. As in the proof
of the corollary, Theorem `hs:thm:optimal` (`optimal_simulation`) is applied to the dilation
`H̃_U = [[0, Ũ], [Ũ†, 0]]` of the represented matrix (`Table.toNative`, sparsity `N`, norm bound
`η = 2`) for `t = π/2` and precision `δ = min(ε/2, 1/64)`; Duhamel's bound
(`UnitaryPrecision.duhamel_step`) gives error `ε` for the true dilation `H_U`; the released
transfer (`UnitaryDilationTransfer.exists_clean_unitary_program`) adds the flag flip and the
phase correction; and the known locators are compiled into fixed gates, each value query into one
entry query between fixed routing gates (`compile`).

* `entryOracle T ι`: one ordinary call of the entry table, with the spectator registers of the
  common form (`Table.flatEntry_eq_original` identifies `Table.flatEntry` with the original
  table call).
* `unitary_budget`: the query bound `bound` of `optimal_simulation` at `s = N`, `τ = π` and
  precision `δ` is at most `5·10¹³ (√(N ρ_ε) + ρ_ε)`.
* `unitary_optimal_inexact`, `unitary_optimal`: the corollary with inexact and exact entries;
  `unitary_optimal_inexact_with_reference`, `unitary_optimal_with_reference`: inputs entangled
  with an untouched finite reference.

The constant-error lower bound `Θ(√N)` of the corollary is not part of this module.
-/

namespace OptimalSparseSimulation

noncomputable section

open ContinuousLinearMap SparseHamiltonian OracleCircuit UnitaryPrecision UnitaryEntryOracle
open NativeSparseBlockEncoding (Query)
open UnitaryEntryData (Index)
open LargeSparsityCore.Parameters SignedFactorSimulation
open scoped InnerProduct
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192

/-! ### The budget -/

/-- `ρ_ε = ℓ/log(e + ℓ)` with `ℓ = log(1/ε)`, the precision quotient in the proof of Corollary
`hs:cor:unitary-optimal`. -/
def rho (ε : ℝ) : ℝ := Real.log (1 / ε) / Real.log (Real.exp 1 + Real.log (1 / ε))

/-- The simulation precision `δ = min(ε/2, 1/64)` of the proof. -/
def delta (ε : ℝ) : ℝ := min (ε / 2) (1 / 64)

theorem delta_pos {ε : ℝ} (hε : 0 < ε) : 0 < delta ε :=
  lt_min (half_pos hε) (by norm_num)

theorem delta_le {ε : ℝ} : delta ε ≤ 1 / 64 := min_le_right _ _

theorem delta_le_half {ε : ℝ} : delta ε ≤ ε / 2 := min_le_left _ _

section Budget

variable {ε : ℝ}

/-- `ρ_ε ≥ 1/2` for `ε ≤ 1/2`. -/
theorem half_le_rho (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) : 1 / 2 ≤ rho ε := by
  have hℓ := log_two_le_log_one ε hε hε1
  have hlog2 := Real.log_two_gt_d9
  have he := Real.exp_one_gt_d9
  set ℓ := Real.log (1 / ε) with hℓdef
  have hℓ0 : 0 < ℓ := by linarith
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have ha : Real.log (Real.exp 1 + ℓ) ≤ 1 + ℓ / Real.exp 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (Real.exp 1 + ℓ) / Real.exp 1) (by positivity)
    rw [Real.log_div (by positivity) he0.ne', Real.log_exp] at h
    have : (Real.exp 1 + ℓ) / Real.exp 1 - 1 = ℓ / Real.exp 1 := by
      field_simp
      ring
    linarith
  have ha0 : 0 < Real.log (Real.exp 1 + ℓ) :=
    Real.log_pos (by linarith)
  unfold rho
  rw [← hℓdef, le_div_iff₀ ha0]
  have : ℓ / Real.exp 1 ≤ ℓ / 2.7 :=
    div_le_div_of_nonneg_left hℓ0.le (by norm_num) (by linarith)
  have : ℓ / 2.7 = ℓ * (10 / 27) := by ring
  nlinarith

/-- `ℓ ≤ L ≤ 7ℓ` for `L = log(1/δ)`. -/
theorem L_delta_le (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    Real.log (1 / ε) ≤ Real.log (1 / delta ε) ∧
      Real.log (1 / delta ε) ≤ 7 * Real.log (1 / ε) := by
  have hδ := delta_pos hε
  have hℓ := log_two_le_log_one ε hε hε1
  constructor
  · apply Real.log_le_log (by positivity)
    rw [one_div_le_one_div (by positivity) hδ]
    linarith [delta_le_half (ε := ε)]
  · have hδge : ε / 64 ≤ delta ε := le_min (by linarith) (by linarith)
    have h1 : Real.log (1 / delta ε) ≤ Real.log (64 / ε) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ hδ hε]
      linarith
    have h64 : Real.log (64 / ε) = 6 * Real.log 2 + Real.log (1 / ε) := by
      rw [show (64 : ℝ) / ε = 2 ^ 6 * (1 / ε) by ring, Real.log_mul (by norm_num) (by positivity),
        Real.log_pow]
      norm_num
    linarith

/-- `log(e + L/π) ≥ log(e + ℓ)/3`. -/
theorem log_delta_ge (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    Real.log (Real.exp 1 + Real.log (1 / ε)) / 3 ≤
      Real.log (Real.exp 1 + Real.log (1 / delta ε) / Real.pi) := by
  obtain ⟨hL1, -⟩ := L_delta_le hε hε1
  have hℓ0 := log_one_nonneg ε hε hε1
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  set ℓ := Real.log (1 / ε)
  set L := Real.log (1 / delta ε)
  have hx1 : Real.log (Real.exp 1 + ℓ / Real.pi) ≤ Real.log (Real.exp 1 + L / Real.pi) :=
    Real.log_le_log (by positivity) (by gcongr)
  have hx0 : 1 ≤ Real.log (Real.exp 1 + ℓ / Real.pi) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have : 0 ≤ ℓ / Real.pi := by positivity
    linarith
  have hx2 : Real.log (Real.exp 1 + ℓ) - Real.log Real.pi ≤
      Real.log (Real.exp 1 + ℓ / Real.pi) := by
    rw [← Real.log_div (by positivity) hpi.ne']
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hpi, add_mul, div_mul_cancel₀ _ hpi.ne']
    nlinarith
  have hlogpi : Real.log Real.pi ≤ 2 := by
    rw [Real.log_le_iff_le_exp hpi]
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have he := Real.exp_one_gt_d9
    nlinarith
  linarith

/-- `r = L/log(e + L/π) ≤ 21 ρ_ε`. -/
theorem rb_delta_le (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) : rb Real.pi (delta ε) ≤ 21 * rho ε := by
  obtain ⟨hL1, hL7⟩ := L_delta_le hε hε1
  have hg := log_delta_ge hε hε1
  have hℓ := log_two_le_log_one ε hε hε1
  have hlog2 := Real.log_two_gt_d9
  have ha0 : 0 < Real.log (Real.exp 1 + Real.log (1 / ε)) :=
    Real.log_pos (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have hg0 : 0 < Real.log (Real.exp 1 + Real.log (1 / delta ε) / Real.pi) := by linarith
  have hL0 : 0 ≤ Real.log (1 / delta ε) := by linarith
  unfold rb rho
  rw [div_le_iff₀ hg0]
  calc Real.log (1 / delta ε) ≤ 7 * Real.log (1 / ε) := hL7
    _ = 21 * (Real.log (1 / ε) / Real.log (Real.exp 1 + Real.log (1 / ε))) *
          (Real.log (Real.exp 1 + Real.log (1 / ε)) / 3) := by
        field_simp
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hg (by
        have : 0 ≤ Real.log (1 / ε) := by linarith
        positivity)

/-- **The budget of Corollary `hs:cor:unitary-optimal`.** The query bound of
`optimal_simulation` at sparsity `N`, `τ = 2|π/2| = π` and precision `δ = min(ε/2, 1/64)` is at
most `5·10¹³ (√(N ρ_ε) + ρ_ε)` (`hs:eq:unitary-optimal-bound`). -/
theorem unitary_budget (N : ℕ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    bound N (2 * |Real.pi / 2|) (delta ε) ≤
      5 * 10 ^ 13 * (Real.sqrt (N * rho ε) + rho ε) := by
  have hτ : 2 * |Real.pi / 2| = Real.pi := by
    rw [abs_of_pos (by linarith [Real.pi_pos])]
    ring
  have hρ := half_le_rho hε hε1
  have hr := rb_delta_le hε hε1
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_d2
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hρ0 : 0 ≤ rho ε := by linarith
  have hr0 : 0 ≤ rb Real.pi (delta ε) := by
    unfold rb
    have hδ := delta_pos hε
    have h1 : 0 ≤ Real.log (1 / delta ε) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hδ]
      linarith [delta_le (ε := ε)]
    have h2 : 0 ≤ Real.log (Real.exp 1 + Real.log (1 / delta ε) / Real.pi) := by
      apply Real.log_nonneg
      have : 0 ≤ Real.log (1 / delta ε) / Real.pi := by positivity
      linarith [Real.add_one_le_exp (1 : ℝ)]
    positivity
  unfold bound
  rw [hτ]
  -- `√N ≤ √2 √(Nρ)` and `√2 π ≤ 5`
  have h1 : Real.sqrt N * Real.pi ≤ 5 * Real.sqrt (N * rho ε) := by
    have hs : Real.sqrt N ≤ Real.sqrt 2 * Real.sqrt (N * rho ε) := by
      rw [← Real.sqrt_mul (by norm_num)]
      apply Real.sqrt_le_sqrt
      nlinarith
    have h2 : Real.sqrt 2 < 1.415 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have h3 := Real.sqrt_nonneg (N * rho ε)
    have h4 : Real.sqrt N * Real.pi ≤ Real.sqrt 2 * Real.sqrt (N * rho ε) * Real.pi :=
      mul_le_mul_of_nonneg_right hs hpi.le
    have h5 : Real.sqrt 2 * Real.pi ≤ 5 := by nlinarith [Real.sqrt_nonneg 2]
    nlinarith
  -- `√(N π r) ≤ √(21 π) √(Nρ) ≤ 9 √(Nρ)`
  have h2 : Real.sqrt (N * Real.pi * rb Real.pi (delta ε)) ≤ 9 * Real.sqrt (N * rho ε) := by
    have h81 : (9 : ℝ) = Real.sqrt 81 := by
      rw [show (81 : ℝ) = 9 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h81, ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    have : N * Real.pi * rb Real.pi (delta ε) ≤ N * 3.15 * (21 * rho ε) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hpi4.le hN) hr hr0 (by positivity)
    nlinarith
  have h3 := Real.sqrt_nonneg (N * rho ε)
  nlinarith

end Budget

/-! ### Entry queries in the common form -/

variable {X : Type*} {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z]

/-- The fixed spectator extension of the common form: every block of `ℂ^ι`, both Boolean
branches and the registers of the native-control construction. -/
def lift (ι : Type) [Fintype ι]
    (F : EuclideanSpace ℂ (Base n Z) →L[ℂ] EuclideanSpace ℂ (Base n Z)) :
    PiLp 2 (fun _ : ι => NativeSignedFactor.Phys (Index n) Z) →L[ℂ]
      PiLp 2 (fun _ : ι => NativeSignedFactor.Phys (Index n) Z) :=
  WeightedClock.diagonal (fun _ : ι => MaskedProgram.masked (fun _ : Bool => true)
    (LookupFromBasisOracle.spectator (S := (Bool × Base n Z) × Base n Z) F))

omit [DecidableEq n] [DecidableEq Z] [AddCommGroup Z] in
theorem lift_mul (ι : Type) [Fintype ι]
    (U V : EuclideanSpace ℂ (Base n Z) →L[ℂ] EuclideanSpace ℂ (Base n Z)) :
    lift ι (U * V) = lift ι U * lift ι V := by
  simp only [lift, spectator_mul, MaskedProgram.masked_mul, UnitaryEntryOracle.diagonal_mul]

omit [DecidableEq n] [DecidableEq Z] [AddCommGroup Z] in
theorem lift_unitary (ι : Type) [Fintype ι]
    (U : EuclideanSpace ℂ (Base n Z) →L[ℂ] EuclideanSpace ℂ (Base n Z)) (hU : IsUnitary U) :
    IsUnitary (lift ι U) :=
  CoherentQuerySchedule.diagonal_unitary _ (fun _ =>
    MaskedProgram.masked_unitary _ _ (LookupFromBasisOracle.spectator_unitary _ hU))

/-- **The entry oracle.** One ordinary call of the entry table (`Table.flatEntry`, the original
table call with spectators by `Table.flatEntry_eq_original`), with the spectator registers of the
common form. -/
def entryOracle (T : Table X n Z) (ι : Type) [Fintype ι] (x : X) :
    PiLp 2 (fun _ : ι => NativeSignedFactor.Phys (Index n) Z) →L[ℂ]
      PiLp 2 (fun _ : ι => NativeSignedFactor.Phys (Index n) Z) :=
  lift ι (Table.flatEntry T x)

omit [DecidableEq n] [DecidableEq Z] in
theorem entryOracle_unitary (T : Table X n Z) (ι : Type) [Fintype ι] (x : X) :
    IsUnitary (entryOracle T ι x) :=
  lift_unitary ι _ (Table.flatEntry_unitary T x)

section Compile

variable [Nonempty n]

omit [DecidableEq Z] in
/-- The native calls of the dilation in the common form are the flat native calls with the same
spectators. -/
theorem physOracle_eq (T : Table X n Z) (ι : Type) [Fintype ι] (l : Query) (x : X) :
    CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle (Table.toNative T)) l x =
      lift ι (NativeSparseMaskedAccess.flatOracle (Table.toNative T) l x) := rfl

/-- Known locators become fixed gates; a value query is one entry query between fixed routing
gates. -/
def letter (T : Table X n Z) (ι : Type) [Fintype ι] :
    Query → OracleCircuit.Program (entryOracle T ι)
  | .rowLocation => .fixed (lift ι rowBase) (lift_unitary ι _ rowBase_unitary)
  | .columnLocation => .fixed (lift ι columnBase) (lift_unitary ι _ columnBase_unitary)
  | .value => .seq (.fixed (lift ι route) (lift_unitary ι _ route_unitary))
      (.seq .query (.fixed (lift ι route) (lift_unitary ι _ route_unitary)))

omit [DecidableEq Z] in
theorem letter_eval (T : Table X n Z) (ι : Type) [Fintype ι] (l : Query) (x : X) :
    (letter T ι l).eval x =
      CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle (Table.toNative T))
        l x := by
  rw [physOracle_eq]
  cases l
  · rfl
  · rfl
  · change lift ι route * (lift ι (Table.flatEntry T x) * lift ι route) = _
    rw [← lift_mul, ← lift_mul, ← Table.value_routing]

/-- Exact compilation of a program over the native calls of the dilation to entry queries. -/
def compile (T : Table X n Z) (ι : Type) [Fintype ι]
    (p : MultiOracleCircuit.Program
      (CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle (Table.toNative T)))) :
    OracleCircuit.Program (entryOracle T ι) :=
  p.compile (letter T ι)

omit [DecidableEq Z] in
theorem compile_eval (T : Table X n Z) (ι : Type) [Fintype ι]
    (p : MultiOracleCircuit.Program
      (CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle (Table.toNative T))))
    (x : X) : (compile T ι p).eval x = p.eval x :=
  p.eval_compile (letter T ι) (letter_eval T ι) x

omit [DecidableEq Z] in
theorem compile_count_le (T : Table X n Z) (ι : Type) [Fintype ι]
    (p : MultiOracleCircuit.Program
      (CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle (Table.toNative T)))) :
    (compile T ι p).count ≤ p.count := by
  change (p.compile (letter T ι)).count ≤ p.count
  rw [MultiOracleCircuit.Program.count_compile]
  calc
    _ ≤ p.cost (fun _ => 1) := p.cost_mono (by intro l; cases l <;> simp [letter])
    _ = p.count := by simp

end Compile

/-! ### The corollary -/

section Corollary

variable [Nonempty n]

/-- **Corollary `hs:cor:unitary-optimal`, inexact entries.** Let the entry table `T` represent,
within `ε/(πN)` in every entry, an intended unitary family `U`, `N = card n`, `0 < ε ≤ 1/2`. There
are a known isometric input and one program whose only oracle calls are ordinary calls of the
entry table with spectator registers (`entryOracle`; no location oracle), unitary for every
instance, with full-output error at most `ε` against `U` and at most
`5·10¹³ (√(N ρ_ε) + ρ_ε)` calls, inverse calls counted, `ρ_ε = ℓ/log(e + ℓ)`, `ℓ = log(1/ε)`. -/
theorem unitary_optimal_inexact (T : Table X n Z) (U : X → Matrix n n ℂ)
    (hU : ∀ x, IsUnitary (SparseStateOverlap.matrixOperator (U x))) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2)
    (hEntry : ∀ x i j, ‖T.matrix x i j - U x i j‖ ≤ ε / (Real.pi * Fintype.card n)) :
    ∃ (ι : Type) (_ : Fintype ι)
      (inp : EuclideanSpace ℂ n →L[ℂ] PiLp 2 (fun _ : ι => NativeSignedFactor.Phys (Index n) Z))
      (p : OracleCircuit.Program (entryOracle T ι)),
      inp† ∘L inp = 1 ∧
      (p.count : ℝ) ≤ 5 * 10 ^ 13 * (Real.sqrt (Fintype.card n * rho ε) + rho ε) ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L inp - inp ∘L SparseStateOverlap.matrixOperator (U x)‖ ≤ ε := by
  have hN : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hξ := card_mul_sq_le_one (Fintype.card n : ℝ) ε hN hε hε1
  have hτ : (1 : ℝ) ≤ 2 * |Real.pi / 2| := by
    rw [abs_of_pos (by linarith [Real.pi_pos])]
    linarith [Real.pi_gt_three]
  -- Theorem `hs:thm:optimal` for the represented dilation, `η = 2`, `t = π/2`, precision `δ`
  obtain ⟨ι, hι, inp, p, hinp, hcount, hp⟩ :=
    optimal_simulation (Table.toNative T) (η := 2) (t := Real.pi / 2) hτ
      (delta_pos hε) delta_le (Table.dilation_hermitian T)
      (Table.dilation_row_energy_two T U hU _ hEntry hξ)
      (Table.dilation_column_energy_two T U hU _ hEntry hξ)
  -- Duhamel's bound, the flag flip and the phase correction
  obtain ⟨q, hqcount, -, hclean, hq⟩ :=
    UnitaryDilationTransfer.exists_clean_unitary_program
      (CoherentQuerySchedule.oracle (ι := ι)
        (NativeSignedFactor.physOracle (Table.toNative T)))
      (fun l x => CoherentQuerySchedule.oracle_unitary _
        (NativeSignedFactor.physOracle_unitary _) l x)
      inp UnitaryEntryData.includeOne UnitaryEntryData.includeZero
      hinp UnitaryEntryData.includeOne_isometry UnitaryEntryData.includeZero_isometry
      (fun x => SparseStateOverlap.matrixOperator
        (UnitaryEntryData.dilationMatrix (exactData U hU) x))
      (fun x => SparseStateOverlap.matrixOperator (U x))
      (UnitaryEntryData.dilation_sq (exactData U hU))
      (UnitaryEntryData.dilation_includeOne (exactData U hU))
      p ε
      (duhamel_step T U hU ε hε hEntry (fun x => p.eval x ∘L inp) inp hinp
        (fun x => (hp x).2.trans delta_le_half))
  -- back to the common form, then entry queries only
  obtain ⟨ι', hι', inp', p', hinp', hcount', hp'⟩ :=
    implements_of_spectatorForm
      ((SpectatorForm.oracle (NativeSignedFactor.physOracle (Table.toNative T)) ι).diagonal Bool)
      (fun x => SparseStateOverlap.matrixOperator (U x)) ε
      (bound (Fintype.card n) (2 * |Real.pi / 2|) (delta ε)) _ hclean q
      (by rw [hqcount]; exact hcount) hq
  refine ⟨ι', hι', inp', compile T ι' p', hinp', ?_, fun x => ?_⟩
  · calc ((compile T ι' p').count : ℝ) ≤ p'.count := by
          exact_mod_cast compile_count_le T ι' p'
      _ ≤ _ := hcount'
      _ ≤ _ := unitary_budget _ hε hε1
  · rw [compile_eval]
    exact hp' x

/-- **Corollary `hs:cor:unitary-optimal`, exact entries.** For released exact entry data `D`
(`N = card n`, `0 < ε ≤ 1/2`), one program over ordinary entry queries with spectators
(`entryOracle (Table.ofData D)`, the released entry call `UnitaryEntryOracle.flatEntry D` by
`Table.flatEntry_ofData`), unitary for every instance, with full-output error at most `ε` against
the unitary `D.matrix x` and at most `5·10¹³ (√(N ρ_ε) + ρ_ε)` calls, inverse calls counted. -/
theorem unitary_optimal (D : UnitaryEntryData.Data X n Z) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2) :
    ∃ (ι : Type) (_ : Fintype ι)
      (inp : EuclideanSpace ℂ n →L[ℂ] PiLp 2 (fun _ : ι => NativeSignedFactor.Phys (Index n) Z))
      (p : OracleCircuit.Program (entryOracle (Table.ofData D) ι)),
      inp† ∘L inp = 1 ∧
      (p.count : ℝ) ≤ 5 * 10 ^ 13 * (Real.sqrt (Fintype.card n * rho ε) + rho ε) ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L inp - inp ∘L SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ ε :=
  unitary_optimal_inexact (Table.ofData D) D.matrix D.unitary ε hε hε1 (fun x i j => by
    change ‖D.matrix x i j - D.matrix x i j‖ ≤ _
    rw [sub_self, norm_zero]
    have := Real.pi_pos
    positivity)

/-- **Corollary `hs:cor:unitary-optimal`, inexact entries, with an untouched reference.** The
circuit of `unitary_optimal_inexact` keeps its error on normalised inputs entangled with an
arbitrary finite reference `R`. -/
theorem unitary_optimal_inexact_with_reference {R : Type*} [Fintype R] (T : Table X n Z)
    (U : X → Matrix n n ℂ) (hU : ∀ x, IsUnitary (SparseStateOverlap.matrixOperator (U x)))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hEntry : ∀ x i j, ‖T.matrix x i j - U x i j‖ ≤ ε / (Real.pi * Fintype.card n)) :
    ∃ (ι : Type) (_ : Fintype ι)
      (inp : EuclideanSpace ℂ n →L[ℂ] PiLp 2 (fun _ : ι => NativeSignedFactor.Phys (Index n) Z))
      (p : OracleCircuit.Program (entryOracle T ι)),
      inp† ∘L inp = 1 ∧
      (p.count : ℝ) ≤ 5 * 10 ^ 13 * (Real.sqrt (Fintype.card n * rho ε) + rho ε) ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ∀ ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n), ‖ψ‖ = 1 →
          ‖FiniteReferenceLift.lift (p.eval x) (FiniteReferenceLift.lift inp ψ) -
            FiniteReferenceLift.lift inp
              (FiniteReferenceLift.lift (SparseStateOverlap.matrixOperator (U x)) ψ)‖ ≤ ε := by
  obtain ⟨ι, hι, inp, p, hinp, hcount, hp⟩ :=
    unitary_optimal_inexact T U hU ε hε hε1 hEntry
  refine ⟨ι, hι, inp, p, hinp, hcount, fun x => ⟨(hp x).1, fun ψ hψ => ?_⟩⟩
  simpa only [hψ, mul_one] using
    FiniteReferenceLift.same_embedding_error_le (p.eval x) inp _ ε (hp x).2 ψ

/-- **Corollary `hs:cor:unitary-optimal`, exact entries, with an untouched reference.** -/
theorem unitary_optimal_with_reference {R : Type*} [Fintype R]
    (D : UnitaryEntryData.Data X n Z) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∃ (ι : Type) (_ : Fintype ι)
      (inp : EuclideanSpace ℂ n →L[ℂ] PiLp 2 (fun _ : ι => NativeSignedFactor.Phys (Index n) Z))
      (p : OracleCircuit.Program (entryOracle (Table.ofData D) ι)),
      inp† ∘L inp = 1 ∧
      (p.count : ℝ) ≤ 5 * 10 ^ 13 * (Real.sqrt (Fintype.card n * rho ε) + rho ε) ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ∀ ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n), ‖ψ‖ = 1 →
          ‖FiniteReferenceLift.lift (p.eval x) (FiniteReferenceLift.lift inp ψ) -
            FiniteReferenceLift.lift inp
              (FiniteReferenceLift.lift (SparseStateOverlap.matrixOperator (D.matrix x)) ψ)‖ ≤
            ε := by
  obtain ⟨ι, hι, inp, p, hinp, hcount, hp⟩ := unitary_optimal D ε hε hε1
  refine ⟨ι, hι, inp, p, hinp, hcount, fun x => ⟨(hp x).1, fun ψ hψ => ?_⟩⟩
  simpa only [hψ, mul_one] using
    FiniteReferenceLift.same_embedding_error_le (p.eval x) inp _ ε (hp x).2 ψ

end Corollary

end

end OptimalSparseSimulation
