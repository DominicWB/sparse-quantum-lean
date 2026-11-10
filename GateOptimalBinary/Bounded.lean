import GateOptimalPrecision.NativeMain
import GateEfficientBinary.Sparse.Simulation
import TwoNormSimulation.Bounded

/-!
# The bounded-logarithm regime from binary sparse oracles

The bounded regime of Theorem `gate:thm:main` ("If `h_a = log(e + L_a/Θ)` is bounded by the fixed
threshold, use the baseline gate-efficient Cayley construction. With `E_H` the orientation entry
operator normalised by `μ`, it uses `K₀ = √σ E_H`, `J₀†K₀J₀ = H/(√s η)`, `J₀†K₀²J₀ ⪯ I`,
`‖K₀‖ ≤ √σ`", Section `gate:sec:combine`) needs the interface `GateOptimalPrecision.BoundedIface`
and the native data `GateOptimalPrecision.CayleyNative` of its private Cayley operation. Both are
constructed here from the binary sparse oracles of `GateEfficientBinary`:

* the data are normalised by the row-norm bound `η` (`NativeSparseRescaling.normalize`; the
  oracles and the stored words are unchanged), and `K₀` is the qubit lift of the baseline
  generator `L†(√s E_{H/η})L` of the normalised data (`bdK`); the boundary is `U_J = hadUJ`
  (Hadamard gates on the orientation wire and the lowest slot wires);
* `boundedIface`: `‖K₀‖ ≤ √s μ/η = √σ` from the entry bound `μ`, `‖K₀J₀‖ ≤ 1` from the row and
  column norms, and `J₀†K₀J₀ = H/(√s η)` for the qubit lift `H` of the represented matrix;
* `bdPriv_elift`: the private operation `(γK₀ + i)(γK₀ - i)⁻¹` of the bounded circuit, for the
  public rescaling `γ = bdGamma σ θ ε`, is the qubit lift of the baseline private Cayley
  operation of the normalised data, so the native identity of `GateBinary.sparse_nativeOK`
  applies;
* `boundedNative`: the native data, with the compute circuit `GateBinary.computeV` (two row, two
  column and one value call, `28 k` gates) and the CORDIC arithmetic `GateBinary.binArith` at the
  decoder scale `γ √s c₀/η`, whose accuracy is proved (`GateBinary.cordicArith_ok`).

References to the manuscript use its labels.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace GateOptimalBinary

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary GateOptimalPrecision
open NativeSparseBlockEncoding (Data Query)
open CayleyClockInterface
open scoped InnerProduct

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-! ### The lift of edge operators -/

theorem elift_smul (en : Cfg (Fin k) ≃ n) (c : ℂ)
    (A : SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n) :
    elift (R := R) en (c • A) = c • elift (R := R) en A := by
  rw [elift, elift, qlift_smul]
  unfold unconj
  rw [smul_comp, comp_smul]

theorem elift_add (en : Cfg (Fin k) ≃ n)
    (A B : SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n) :
    elift (R := R) en (A + B) = elift (R := R) en A + elift (R := R) en B := by
  rw [elift, elift, elift, qlift_add]
  unfold unconj
  rw [add_comp, comp_add]

theorem elift_mul (en : Cfg (Fin k) ≃ n)
    (A B : SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n) :
    elift (R := R) en (A * B) = elift (R := R) en A * elift (R := R) en B := by
  rw [mul_def, mul_def, elift_comp]

theorem elift_star (en : Cfg (Fin k) ≃ n)
    (A : SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n) :
    star (elift (R := R) en A) = elift (R := R) en (star A) := by
  rw [star_eq_adjoint, star_eq_adjoint, elift_adjoint]

/-! ### The Cayley operation of the bounded regime -/

/-- **The private operation of the bounded regime is the lifted baseline Cayley operation**: for
the qubit lift `K₀` of the baseline generator, `(γK₀ + i)(γK₀ - i)⁻¹` with the public rescaling
`γ = bdGamma σ θ ε` is the lift of `FixedNativeCayleySimulation.action` at `γ`. -/
theorem bdPriv_elift {Z : Type*} (en : Cfg (Fin k) ≃ n) (D' : Data X n Z s) (x : X)
    (σ θ ε : ℝ) :
    bdPriv (elift (R := R) en (FixedNativeCayleySimulation.generator D' x)) σ θ ε =
      elift (R := R) en (FixedNativeCayleySimulation.action D' x (bdGamma σ θ ε)) := by
  set γ := bdGamma σ θ ε
  set G := FixedNativeCayleySimulation.generator D' x
  set Inv := FixedNativeCayleySimulation.inverse D' x γ
  have hE : scaled (elift (R := R) en G) γ - Complex.I •
      (1 : Reg (Fin (k + 1)) (Reg (Fin k) R) →L[ℂ] Reg (Fin (k + 1)) (Reg (Fin k) R)) =
      elift (R := R) en (scaled G γ - Complex.I • 1) := by
    unfold scaled
    rw [elift_sub, elift_smul, elift_smul, elift_one]
  have h1 : (scaled (elift (R := R) en G) γ - Complex.I • 1) * elift (R := R) en Inv = 1 := by
    rw [hE, ← elift_mul, FixedNativeCayleySimulation.inverse_right D' x γ, elift_one]
  have h2 : elift (R := R) en Inv * (scaled (elift (R := R) en G) γ - Complex.I • 1) = 1 := by
    rw [hE, ← elift_mul, FixedNativeCayleySimulation.inverse_left D' x γ, elift_one]
  have hInv : cayleyInv (scaled (elift (R := R) en G) γ) = elift (R := R) en Inv := by
    unfold cayleyInv
    have h := Ring.inverse_unit
      (⟨scaled (elift (R := R) en G) γ - Complex.I • 1, elift (R := R) en Inv, h1, h2⟩ :
        (Reg (Fin (k + 1)) (Reg (Fin k) R) →L[ℂ] Reg (Fin (k + 1)) (Reg (Fin k) R))ˣ)
    simpa using h
  have hS : scaled (elift (R := R) en G) γ + Complex.I •
      (1 : Reg (Fin (k + 1)) (Reg (Fin k) R) →L[ℂ] Reg (Fin (k + 1)) (Reg (Fin k) R)) =
      elift (R := R) en (scaled G γ + Complex.I • 1) := by
    unfold scaled
    rw [elift_add, elift_smul, elift_smul, elift_one]
  unfold bdPriv cayleyGate
  rw [FixedNativeCayleySimulation.action_eq_cayley, hInv]
  unfold ImprovedCayleyMoments.cayleyAction
  rw [hS, elift_mul]

/-! ### The interface -/

/-- The represented matrix as an operator on the `k` system qubits. -/
abbrev sysH (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    Reg (Fin k) R →L[ℂ] Reg (Fin k) R :=
  qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x))

/-- The data normalised by the row-norm bound `η`; the oracles and the stored words are those of
`D`. -/
abbrev normD (D : Data X n (Cfg (VW b)) s) (η : ℝ) (hη : 0 < η) : Data X n (Cfg (VW b)) s :=
  NativeSparseRescaling.normalize D η hη

/-- The generator `K₀ = L†(√s E_{H/η})L` of the bounded regime on the ancilla register with the
system payload. -/
abbrev bdK (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (η : ℝ) (hη : 0 < η) (x : X) :
    Reg (Fin (k + 1)) (Reg (Fin k) R) →L[ℂ] Reg (Fin (k + 1)) (Reg (Fin k) R) :=
  elift (R := R) en (FixedNativeCayleySimulation.generator (normD D η hη) x)

theorem matrixOperator_real_smul {I : Type*} [Fintype I] [DecidableEq I] (c : ℝ)
    (M : Matrix I I ℂ) :
    SparseStateOverlap.matrixOperator (fun i j => (c : ℂ) * M i j) =
      (c : ℂ) • SparseStateOverlap.matrixOperator M := by
  ext v i
  simp [SparseStateOverlap.matrixOperator_apply, Finset.mul_sum, mul_assoc]

theorem bdK_self (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (η : ℝ) (hη : 0 < η)
    (x : X) : star (bdK (R := R) D en η hη x) = bdK (R := R) D en η hη x := by
  rw [bdK, elift_star, FixedNativeCayleySimulation.generator_self_adjoint]

/-- The baseline generator has norm at most `√s m` when every entry has modulus at most `m`
(`TwoNormSimulation.generator_norm_le_entry`, for index types in any universe). -/
theorem generator_norm_le_entry' {Z : Type*} (D : Data X n Z s) (x : X) {m : ℝ} (hm : 0 ≤ m)
    (hent : ∀ i j, ‖D.matrix x i j‖ ≤ m) :
    ‖FixedNativeCayleySimulation.generator D x‖ ≤ Real.sqrt s * m := by
  refine (UnitaryCayleyTransport.conjugate_norm_le _
    (FixedLocatorConjugation.locator_unitary D x) _).trans ?_
  rw [SparseEdgeMoments.generator, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (SparseEdgeMoments.entryGenerator_norm_le _ m hm hent)
    (Real.sqrt_nonneg _)

theorem bdK_norm_le (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) {η μ : ℝ}
    (hη : 0 < η) (hμ : 0 ≤ μ) (x : X) (hent : ∀ i j, ‖D.matrix x i j‖ ≤ μ) :
    ‖bdK (R := R) D en η hη x‖ ≤ Real.sqrt s * (μ / η) := by
  refine (norm_elift_le en _).trans ?_
  refine generator_norm_le_entry' (normD D η hη) x (div_nonneg hμ hη.le) (fun i j => ?_)
  rw [NativeSparseRescaling.normalize_matrix, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hη), inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (hent i j) hη.le

theorem sqrt_sigma_eq {σ η μ : ℝ} (hη : 0 < η) (hμ : 0 ≤ μ) (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2) :
    Real.sqrt σ = Real.sqrt s * (μ / η) := by
  have hσ' : σ = (s : ℝ) * (μ / η) ^ 2 := by
    field_simp
    linarith
  rw [hσ', Real.sqrt_mul (Nat.cast_nonneg s), Real.sqrt_sq (div_nonneg hμ hη.le)]

/-- The lifted boundary compression of the bounded regime. -/
theorem bd_boundary_lift (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ)
    (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    (η : ℝ) (hη : 0 < η)
    (A : SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n) :
    (UJop (R := R) (hadUJ k sb hsb) ∘L iota0)† ∘L elift (R := R) en A ∘L
        (UJop (hadUJ k sb hsb) ∘L iota0) =
      qlift (R := R) en ((FixedNativeCayleySimulation.boundary (normD D η hη))† ∘L A ∘L
        FixedNativeCayleySimulation.boundary (normD D η hη)) := by
  have hB : FixedNativeCayleySimulation.boundary (normD D η hη) =
      FixedLocatorConjugation.fixedBoundary D.slot := rfl
  rw [hB]
  exact boundary_lift sb hsb en D.slot hs hrange A

/-- `(K J)† (K J) = J† K² J` for a self-adjoint `K`. -/
theorem adjoint_comp_self_of_sa {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (K : W →L[ℂ] W) (J : V →L[ℂ] W) (hK : K† = K) :
    (K ∘L J)† ∘L (K ∘L J) = J† ∘L (K ∘L K) ∘L J := by
  rw [adjoint_comp, hK]
  simp only [comp_assoc]

theorem bdK_boundary_le (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ)
    (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {η : ℝ} (hη : 0 < η) (x : X) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ‖bdK (R := R) D en η hη x ∘L (UJop (hadUJ k sb hsb) ∘L iota0)‖ ≤ 1 := by
  have hGs : (FixedNativeCayleySimulation.generator (normD D η hη) x)† =
      FixedNativeCayleySimulation.generator (normD D η hη) x := by
    rw [← star_eq_adjoint]
    exact FixedNativeCayleySimulation.generator_self_adjoint _ x
  have hGB : ‖FixedNativeCayleySimulation.generator (normD D η hη) x ∘L
      FixedNativeCayleySimulation.boundary (normD D η hη)‖ ≤ 1 :=
    FixedNativeCayleySimulation.generator_boundary_norm_le (normD D η hη) x
      (fun i => NativeSparseRescaling.normalized_row_energy D η hη x i (hrow i))
      (fun j => NativeSparseRescaling.normalized_column_energy D η hη x j (hcol j))
  have hK : (bdK (R := R) D en η hη x)† = bdK (R := R) D en η hη x := by
    rw [← star_eq_adjoint]
    exact bdK_self D en η hη x
  have e1 := adjoint_comp_self_of_sa (bdK (R := R) D en η hη x)
    (UJop (R := R) (hadUJ k sb hsb) ∘L iota0) hK
  have e1' : bdK (R := R) D en η hη x ∘L bdK (R := R) D en η hη x =
      elift (R := R) en (FixedNativeCayleySimulation.generator (normD D η hη) x ∘L
        FixedNativeCayleySimulation.generator (normD D η hη) x) :=
    (elift_comp en _ _).symm
  have hL := bd_boundary_lift (R := R) D en sb hsb hs hrange η hη
    (FixedNativeCayleySimulation.generator (normD D η hη) x ∘L
      FixedNativeCayleySimulation.generator (normD D η hη) x)
  have e2 := adjoint_comp_self_of_sa (FixedNativeCayleySimulation.generator (normD D η hη) x)
    (FixedNativeCayleySimulation.boundary (normD D η hη)) hGs
  have hq : ‖(bdK (R := R) D en η hη x ∘L (UJop (hadUJ k sb hsb) ∘L iota0))† ∘L
      (bdK (R := R) D en η hη x ∘L (UJop (hadUJ k sb hsb) ∘L iota0))‖ ≤ 1 := by
    rw [e1, e1', hL]
    refine (norm_qlift_le _ _).trans ?_
    rw [← e2, norm_adjoint_comp_self]
    nlinarith [norm_nonneg (FixedNativeCayleySimulation.generator (normD D η hη) x ∘L
      FixedNativeCayleySimulation.boundary (normD D η hη))]
  rw [norm_adjoint_comp_self] at hq
  nlinarith [norm_nonneg (bdK (R := R) D en η hη x ∘L (UJop (hadUJ k sb hsb) ∘L iota0))]

theorem bdK_compress (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ)
    (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {η : ℝ} (hη : 0 < η) (x : X) (hH : (D.matrix x).IsHermitian) :
    (UJop (R := R) (hadUJ k sb hsb) ∘L iota0)† ∘L bdK (R := R) D en η hη x ∘L
        (UJop (hadUJ k sb hsb) ∘L iota0) =
      ((Real.sqrt s * η : ℝ) : ℂ)⁻¹ • sysH (R := R) D en x := by
  rw [bdK, bd_boundary_lift D en sb hsb hs hrange η hη,
    FixedNativeCayleySimulation.compression (normD D η hη) x
      (NativeSparseRescaling.normalize_hermitian D η hη x hH), qlift_smul]
  have hM : (normD D η hη).matrix x = fun i j => ((η⁻¹ : ℝ) : ℂ) * D.matrix x i j := rfl
  rw [hM, matrixOperator_real_smul, qlift_smul, smul_smul]
  congr 1
  push_cast
  rw [mul_inv]

/-- **The bounded-regime interface from binary sparse oracles.** For an input whose matrix is
Hermitian with row and column Euclidean norms at most `η` and entries of modulus at most `μ`, and
`σ` with `s μ² = σ η²`: the generator `K₀` of the normalised data with the boundary `U_J =
hadUJ`. -/
def boundedIface (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ) (hsb : sb ≤ k)
    (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {η μ σ : ℝ} (hη : 0 < η) (hμ : 0 ≤ μ) (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2) (x : X)
    (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (hent : ∀ i j, ‖D.matrix x i j‖ ≤ μ) :
    BoundedIface (Reg (Fin k) R) σ (Real.sqrt s * η) (sysH (R := R) D en x) where
  a := k + 1
  UJ := UJop (hadUJ k sb hsb)
  K := bdK D en η hη x
  unitary := UJop_isUnitary _ (hadUJ_ok sb hsb)
  self := bdK_self D en η hη x
  norm_le := by
    rw [sqrt_sigma_eq hη hμ hσ]
    exact bdK_norm_le D en hη hμ x hent
  boundary_le := bdK_boundary_le D en sb hsb hs hrange hη x hrow hcol
  compress := by
    rw [bdK_compress D en sb hsb hs hrange hη x hH]

/-! ### The native data -/

/-- The decoder scale of the bounded regime: `γ √s c₀/η` for the public rescaling
`γ = bdGamma σ θ ε`. -/
abbrev bdScale (s : ℕ) (c0 η σ θ ε : ℝ) : ℝ := bdGamma σ θ ε * Real.sqrt s * (c0 / η)

theorem bdScale_pos {c0 η σ θ ε : ℝ} (hs : 1 ≤ (s : ℝ)) (hc0 : 0 < c0) (hη : 0 < η)
    (hσ : 1 ≤ σ) (hθ : 0 ≤ θ) (hε : 0 < ε) (hε1 : ε ≤ 1) : 0 < bdScale s c0 η σ θ ε := by
  have hγ := (bdGamma_spec (σ := σ) (θ := θ) (ε := ε) ⟨hσ, hθ, hε, hε1⟩).1
  have : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 (by linarith)
  unfold bdScale
  positivity

/-- **The native data of the bounded regime from binary sparse oracles**: `U_J = hadUJ`, the
compute circuit `computeV`, the CORDIC arithmetic at the scale `bdScale` and accuracy `ζ`, and the
native identity of `sparse_nativeOK` for the normalised data. -/
def boundedNative (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ) (hsb : sb ≤ k)
    (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    (hb : 0 < b) {c0 : ℝ} (hc0 : 0 < c0) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z)
    {η μ σ θ ε ζ : ℝ} (hη : 0 < η) (hμ : 0 ≤ μ) (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2)
    (hσ1 : 1 ≤ σ) (hθ : 0 ≤ θ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (x : X)
    (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (hent : ∀ i j, ‖D.matrix x i j‖ ≤ μ) :
    CayleyNative (prims (R := R) D en x)
      (boundedIface (R := R) D en sb hsb hs hrange hη hμ hσ x hH hrow hcol hent).UJ
      (bdPriv (boundedIface (R := R) D en sb hsb hs hrange hη hμ hσ x hH hrow hcol hent).K
        σ θ ε) (SZ k b) ζ where
  UJg := hadUJ k sb hsb
  ok := hadUJ_ok sb hsb
  boundary := rfl
  nd := sparseOp k b (bdScale s c0 η σ θ ε)
  pub := sparseOp_public k b _
  ar := binArith k b (bdScale s c0 η σ θ ε) ζ
  arith := by
    have hs1 : (1 : ℝ) ≤ (s : ℝ) := by
      rw [hs]
      exact_mod_cast Nat.one_le_two_pow
    have hxy : Function.Injective (Sum.elim (valX k b) (valY k b)) := by
      intro i j h
      rcases i with i | i <;> rcases j with j | j <;> simp_all [valX, valY, vB]
    have ho : ∀ i, Sum.elim (valX k b) (valY k b) i ≠
        Sum.inl (Sum.inr (sparseOp k b (bdScale s c0 η σ θ ε)).o) := by
      intro i
      rcases i with i | i
      · exact vB_ne_oB _
      · exact vB_ne_oB _
    exact cordicArith_ok b hb (valX k b) (valY k b) hxy _ ho _ ζ
      (bdScale_pos hs1 hc0 hη hσ1 hθ hε hε1) hζ hζ1
  native := by
    obtain ⟨k0, hk0⟩ : ∃ m, D.slot m = zIdx en := by
      refine (hrange _).2 ⟨fun _ => false, ?_⟩
      unfold zIdx
      congr 1
      funext i
      simp [lowWord]
    have hdec' : ∀ e z, (normD D η hη).decode e z = ((c0 / η : ℝ) : ℂ) * gauss z := by
      intro e z
      change ((η⁻¹ : ℝ) : ℂ) * D.decode e z = _
      rw [hdec]
      push_cast
      ring
    have h := sparse_nativeOK (R := R) (normD D η hη) en k0 hk0 (c0 / η) hdec' x
      (bdGamma σ θ ε)
    change NativeOK (prims (R := R) D en x) (sparseOp k b (bdScale s c0 η σ θ ε))
      (selOp (fun _ : Cfg Empty => bdPriv (bdK (R := R) D en η hη x) σ θ ε))
    rw [bdK, bdPriv_elift]
    exact h

end

end GateOptimalBinary
