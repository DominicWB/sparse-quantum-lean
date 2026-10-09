import SparseLowerBounds.ODE.JointTheorem

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Hamiltonian data as single-stage constant-coefficient ODE families

Helper of `ODE/Precision` (manuscript lines 3955-3964): the precision terms of
`odel:thm:combined` are witnessed by the Hamiltonian-simulation families of
`part:hsl`, read as constant-coefficient ODEs `A = -iH`, `b = 0`, `g = 1`.
For native sparse Hamiltonian data `D` (`NativeSparseBlockEncoding.Data X N Z s`)
this module builds the one-stage family `hamFamily D T x₀` of `ODE/Model`
(generator `G = iH`, decode `i · decode`, the same words and locators) and
proves the transfer:

* **oracles** — the sampled-time oracle of `hamFamily D` is the spectated native
  oracle of `D`: `oracles (hamData D) l (x, r) = oracles D l x` by `rfl`
  (the native primitives read only the words and locators, not the decode), so
  `access ι (hamFamily D …) l x = specOracles (ι × Fin 1) D l x`
  (`access_hamFamily`) and every Boolean certificate of `D` with spectator
  `ι × Fin 1` is one of the family (`implementsOn_hamFamily`);
* **solution** — `t ↦ exp(-itH) x₀ = Hamiltonian.evolve H t x₀` solves the
  release's `SolvesODE` with `G = iH`, `b = 0` (`solves_flow`, `solves_evolve`),
  so its endpoint is `Hamiltonian.evolve H T x₀` (`hamFamily_solves`);
* **class** — for Hermitian data with row/column norms at most one, a unit
  `x₀` and `ḡ ≥ 1`, the family is in the class with `η = 1`, `T = τ`, `g = 1`
  (`hamFamily_inClass`, `hamFamily_T`).
-/

namespace SparseLowerBounds.ODE

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open scoped InnerProductSpace

section Flow

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- `ℚ`-algebra structure on operators, needed by Mathlib's exponential lemmas. -/
local instance instNormedAlgebraRatCLMOde : NormedAlgebra ℚ (V →L[ℂ] V) :=
  .restrictScalars ℚ ℂ _

/-- **The Schrödinger flow solves the ODE**: `t ↦ exp(-itX) x₀` satisfies the
release's `SolvesODE` with generator `iX` and no source, on every interval. -/
theorem solves_flow (X : V →L[ℂ] V) (x0 : V) (a c : ℝ) :
    TimeDependentODE.SolvesODE (fun _ => Complex.I • X) (fun _ => 0)
      (fun u => NormedSpace.exp ((-Complex.I * (u : ℂ)) • X) x0) a c := by
  intro u _
  have h := Helpers.SpinChain.hasDerivAt_clm_apply_real (Helpers.SpinChain.hasDerivAt_flow X u)
    (hasDerivAt_const u x0)
  have hc : Commute (NormedSpace.exp ((-Complex.I * (u : ℂ)) • X)) ((-Complex.I) • X) :=
    (((Commute.refl X).smul_left _).smul_right _).exp_left
  refine (h.congr_deriv ?_).hasDerivWithinAt
  rw [hc.eq]
  simp [neg_smul]

end Flow

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- `t ↦ Hamiltonian.evolve H t x₀` solves `ẋ = -(iH) x` on every interval. -/
theorem solves_evolve (H : Matrix N N ℂ) (x0 : EuclideanSpace ℂ N) (a c : ℝ) :
    TimeDependentODE.SolvesODE (fun _ => SparseStateOverlap.matrixOperator (Complex.I • H))
      (fun _ => 0) (fun u => Hamiltonian.evolve H u x0) a c := by
  rw [matrixOperator_I_smul]
  exact solves_flow _ x0 a c

variable {X Z : Type*} {s : ℕ}

/-- **The single-stage ODE data `G = iH`** of Hamiltonian data `D`: matrix
`i H_x`, decode `i · decode`, the same words, locators and locator oracles. -/
def hamData (D : Data X N Z s) : Data (X × Fin 1) N Z s where
  slot := D.slot
  slots_pos := D.slots_pos
  scale := D.scale
  scale_pos := D.scale_pos
  matrix p := Complex.I • D.matrix p.1
  table p := D.table p.1
  decode a z := Complex.I * D.decode a z
  decode_bound a z := by rw [norm_mul, Complex.norm_I, one_mul]; exact D.decode_bound a z
  decoded p i j := by simp [D.decoded]
  rowloc p := D.rowloc p.1
  colloc p := D.colloc p.1
  row_injective p := D.row_injective p.1
  column_injective p := D.column_injective p.1
  row_covers p i j h := D.row_covers p.1 i j (fun h0 => h (by simp [h0]))
  column_covers p i j h := D.column_covers p.1 i j (fun h0 => h (by simp [h0]))
  rowOracle p := D.rowOracle p.1
  columnOracle p := D.columnOracle p.1
  row_unitary p := D.row_unitary p.1
  column_unitary p := D.column_unitary p.1
  row_valid p := D.row_valid p.1
  column_valid p := D.column_valid p.1

@[simp] theorem hamData_matrix (D : Data X N Z s) (x : X) (r : Fin 1) :
    (hamData D).matrix (x, r) = Complex.I • D.matrix x := rfl

/-- The native primitives of `hamData D` are those of `D` (they read only words
and locators). -/
theorem oracles_hamData [Fintype Z] [AddCommGroup Z] (D : Data X N Z s) (l : Query) (x : X)
    (r : Fin 1) :
    oracles (hamData D) l (x, r) = oracles D l x := by
  cases l <;> rfl

/-- **The constant-coefficient ODE family** `ẋ = -iH_x x`, `x(0) = x₀`, on
`[0, T]` (one stage, no source; lines 3962-3964). -/
def hamFamily (D : Data X N Z s) (T : ℝ) (hT : 0 ≤ T) (x₀ : EuclideanSpace ℂ N) :
    Family X N Z 1 s where
  data := hamData D
  len _ := T
  len_nonneg _ := hT
  src _ := 0
  init := x₀

variable (D : Data X N Z s) (T : ℝ) (hT : 0 ≤ T) (x₀ : EuclideanSpace ℂ N)

@[simp] theorem hamFamily_T : (hamFamily D T hT x₀).T = T := by
  rw [Family.T_eq_sum]
  simp [hamFamily]

theorem hamFamily_mass : (hamFamily D T hT x₀).mass = ‖x₀‖ := by
  simp [Family.mass, hamFamily]

variable [Fintype Z] [AddCommGroup Z]

/-- **Oracle transfer**: the sampled-time access of `hamFamily D` is the native
access of `D` with the untouched spectator `ι × Fin 1`. -/
theorem access_hamFamily (ι : Type*) [Fintype ι] (l : Query) (x : X) :
    (hamFamily D T hT x₀).access ι l x = specOracles (ι × Fin 1) D l x := by
  ext Ψ b : 2
  cases l <;> rfl

/-- **Certificate transfer**: a Boolean implementation of `D`'s spectated
primitives (e.g. `implementsOn_searchData_spec`, `implementsOn_scalarData_spec`
with `Ω = ι × Fin 1`) implements the sampled-time access of `hamFamily D`. -/
theorem implementsOn_hamFamily {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    [CompleteSpace B] (ι : Type*) [Fintype ι] {Q : X → B →L[ℂ] B}
    {E : Joint (ι × Fin 1) (SparseFlagEmbedding.Space (N × N) Z) →L[ℂ] B} {c : ℕ} (l : Query)
    (h : EncodedOracle.ImplementsOn Q (specOracles (ι × Fin 1) D l) E c) :
    EncodedOracle.ImplementsOn Q ((hamFamily D T hT x₀).access ι l) E c := by
  have e : (hamFamily D T hT x₀).access ι l = specOracles (ι × Fin 1) D l :=
    funext fun x => access_hamFamily D T hT x₀ ι l x
  rw [e]
  exact h

omit [Fintype Z] [AddCommGroup Z] in
/-- **The solution**: `t ↦ exp(-itH_x) x₀` solves instance `x`. -/
theorem hamFamily_solves (x : X) :
    (hamFamily D T hT x₀).Solves x (fun u => Hamiltonian.evolve (D.matrix x) u x₀) := by
  refine ⟨?_, fun k => ?_⟩
  · simp [hamFamily, Hamiltonian.evolve_zero]
  · exact solves_evolve (D.matrix x) x₀ _ _

omit [Fintype Z] [AddCommGroup Z] in
/-- **The class promises** with `η = 1` and `g = 1 ≤ ḡ`: for Hermitian data with
row and column Euclidean norms at most one and a unit initial state. -/
theorem hamFamily_inClass (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1) (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hx₀ : ‖x₀‖ = 1) {gbar : ℝ} (hg : 1 ≤ gbar) :
    (hamFamily D T hT x₀).InClass 1 gbar where
  accretive x k := accretive_I_smul (hH x)
  row_norm x k i := by
    simpa [hamFamily, norm_mul, Complex.norm_I] using hrow x i
  col_norm x k j := by
    simpa [hamFamily, norm_mul, Complex.norm_I] using hcol x j
  solution x := by
    refine ⟨_, hamFamily_solves D T hT x₀ x, ?_, ?_⟩
    · rw [hamFamily_T, ne_eq, ← norm_eq_zero, Hamiltonian.norm_evolve_apply (hH x), hx₀]
      exact one_ne_zero
    · rw [hamFamily_T, hamFamily_mass, Hamiltonian.norm_evolve_apply (hH x), hx₀]
      linarith

end

end SparseLowerBounds.ODE
end
