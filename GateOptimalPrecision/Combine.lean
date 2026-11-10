import GateOptimalPrecision.Bounded
import TwoNormSimulation.Regimes

/-!
# The three regimes at the gate level

Section `gate:sec:combine` ("Completing the gate bound"). With `0 < μ ≤ η ≤ √s μ`, the moment
parameter `σ` and the time parameter `θ` of `gate:eq:effective` are fixed by `sμ² = ση²` and
`θ = η²|t|/μ`; then `σ ≥ 1`, `√σ θ = √s η|t|` (the paper's `A`) and `σθ = sμ|t|` (the paper's `B`)
(`two_norm_params`). The query count of Theorem `gate:thm:main` is
`Q_μ = √s η|t| + √(sμ|t| r_μ) + r_μ` with `r_μ = L/log(e + L/θ)` (`Qmu`, `Qmu_eq`).

The private operation of each regime enters through its interface on a gate register of `a` ancilla
qubits and the system (the paper builds these identities natively in Section `gate:sec:native`; here
they enter as hypotheses):

* `BoundedIface` (`h_a` bounded): a self-adjoint generator `K₀` with `‖K₀‖ ≤ √σ`, a boundary
  `J₀ = U_J ι₀` with `‖K₀ J₀‖ ≤ 1` (`J₀†K₀²J₀ ⪯ I`) and `J₀†K₀J₀ = H/(√s η)`;
* `SignedIface` (`gate:eq:whole-factor`): the factor `B = Π U_B U_J ι₀` with sign `Z`, `H = sμ B†ZB`
  and `B†B ⪯ σ^{-1/2} I`;
* `ClippedIface` (`gate:eq:joint-moments`): the clipped joint representation `(J_b, K_b)` with the
  core hypotheses `LargeSparsityCore.Core.CoreData` and `J_b†K_bJ_b = H/α`, `α = sμ/q`.

`GateClaims` collects the conclusions of Theorem `gate:thm:main` for one circuit with its two
oracles: the circuit is valid and unitary, it makes at most `2·10¹¹ Q_μ` private calls and at most
`2·10¹¹ Q_μ` boundary calls, at most `10¹³ (Q_μ + 1)(a + m + r + 1)` elementary gates on at most
`2a + 3m + 6r + 5` qubit wires, with `2^m ≤ 10³⁶ (Q_μ + 1)⁴/ε` slots and `2^r ≤ 10⁸ (Q_μ + 1)`
labels, and its full output is within `ε` of `e^{-itH}`.

* `bounded_branch`, `signed_branch`, `clipped_branch`: the three regimes;
* `clip_steps_le`: the slot count of the clipped regime is at most `d²/(5ε)`.
-/

set_option autoImplicit false

namespace GateOptimalPrecision

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim
open LargeSparsityCore LargeSparsityCore.Parameters
open CayleyClockInterface
open Complex (I)
open scoped InnerProduct InnerProductSpace BigOperators ComplexOrder

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### The two-norm parameters -/

/-- The query count `Q_μ = √s η|t| + √(sμ|t| r_μ) + r_μ` of Theorem `gate:thm:main`, with
`r_μ = L/log(e + L/θ)` and `θ = η²|t|/μ`. -/
def Qmu (s : ℕ) (η μ t ε : ℝ) : ℝ :=
  Real.sqrt s * η * |t| + Real.sqrt (s * μ * |t| * rval (η ^ 2 * |t| / μ) ε) +
    rval (η ^ 2 * |t| / μ) ε

/-- The parameter identities of `gate:eq:effective`: `σ ≥ 1`, `σθ = sμ|t|` and `√σ θ = √s η|t|`. -/
theorem two_norm_params {s : ℕ} {η μ t σ θ : ℝ} (hμη : μ ≤ η) (hηs : η ≤ Real.sqrt s * μ)
    (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2) (hθd : θ = η ^ 2 * |t| / μ) (hθ : 1 ≤ θ) :
    0 < μ ∧ 0 < η ∧ 0 < s ∧ 1 ≤ σ ∧ σ * θ = s * μ * |t| ∧
      Real.sqrt σ * θ = Real.sqrt s * η * |t| := by
  have hμ : 0 < μ := by
    by_contra h
    have h' : μ ≤ 0 := not_lt.mp h
    have : η ^ 2 * |t| / μ ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg η) (abs_nonneg t)) h'
    linarith
  have hη : 0 < η := lt_of_lt_of_le hμ hμη
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hsq : 0 < Real.sqrt s := by
    by_contra h
    have h' : Real.sqrt s ≤ 0 := not_lt.mp h
    have : Real.sqrt s * μ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h' hμ.le
    linarith
  have hs : 0 < s := by
    have := Real.sqrt_pos.mp hsq
    exact_mod_cast this
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs0
  have hσ1 : 1 ≤ σ := by
    have h1 : η * η ≤ (Real.sqrt s * μ) * (Real.sqrt s * μ) := mul_self_le_mul_self hη.le hηs
    have h2 : (Real.sqrt s * μ) * (Real.sqrt s * μ) = s * μ ^ 2 := by
      rw [show (Real.sqrt s * μ) * (Real.sqrt s * μ) = (Real.sqrt s * Real.sqrt s) * μ ^ 2 by ring,
        hss]
    have h3 : η ^ 2 ≤ σ * η ^ 2 := by nlinarith
    have h4 : 0 < η ^ 2 := by positivity
    nlinarith
  have hST : σ * θ = s * μ * |t| := by
    rw [hθd, mul_div_assoc', div_eq_iff hμ.ne']
    linear_combination (-|t|) * hσ
  have hsqσ : Real.sqrt σ = Real.sqrt s * μ / η := by
    have e : σ = (Real.sqrt s * μ / η) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hs0, eq_div_iff (by positivity)]
      linarith
    rw [e, Real.sqrt_sq (by positivity)]
  refine ⟨hμ, hη, hs, hσ1, hST, ?_⟩
  rw [hsqσ, hθd]
  field_simp

/-- `Q_μ = √σ θ + √(σθ r_μ) + r_μ`. -/
theorem Qmu_eq {s : ℕ} {η μ t ε σ θ : ℝ} (hθd : θ = η ^ 2 * |t| / μ)
    (hST : σ * θ = s * μ * |t|) (hSq : Real.sqrt σ * θ = Real.sqrt s * η * |t|) :
    Qmu s η μ t ε = Real.sqrt σ * θ + Real.sqrt (σ * θ * rval θ ε) + rval θ ε := by
  unfold Qmu
  rw [← hθd, hST, hSq]

theorem Qmu_nonneg {s : ℕ} {η μ t ε σ θ : ℝ} (hθd : θ = η ^ 2 * |t| / μ)
    (hST : σ * θ = s * μ * |t|) (hSq : Real.sqrt σ * θ = Real.sqrt s * η * |t|) (hθ : 1 ≤ θ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) : 0 ≤ Qmu s η μ t ε := by
  rw [Qmu_eq hθd hST hSq]
  have := OptimalSparseSimulation.r_pos hθ hε hε1
  have : 0 ≤ Real.sqrt σ * θ := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have := Real.sqrt_nonneg (σ * θ * rval θ ε)
  linarith

omit [CompleteSpace P] in
/-- The exponent of a rescaled compression: `e^{-i x (H/c)} = e^{-i y H}` for `x/c = y`. -/
theorem exp_rescale (H : P →L[ℂ] P) {x c y : ℝ} (hy : x / c = y) :
    NormedSpace.exp ((-I * (x : ℂ)) • ((c : ℂ)⁻¹ • H)) = NormedSpace.exp ((-I * (y : ℂ)) • H) := by
  have h : (-I * (x : ℂ)) * (c : ℂ)⁻¹ = -I * (y : ℂ) := by
    rw [← hy, Complex.ofReal_div]
    ring
  rw [smul_smul, h]

omit [CompleteSpace P] in
/-- The full-output error transported through a rescaled compression. -/
theorem err_rescale {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {C : V →L[ℂ] V}
    {ι : P →L[ℂ] V} (H : P →L[ℂ] P) {G : P →L[ℂ] P} {x c y ε : ℝ} (hG : G = (c : ℂ)⁻¹ • H)
    (hy : x / c = y) (h : ‖C ∘L ι - ι ∘L NormedSpace.exp ((-I * (x : ℂ)) • G)‖ ≤ ε) :
    ‖C ∘L ι - ι ∘L NormedSpace.exp ((-I * (y : ℂ)) • H)‖ ≤ ε := by
  rw [hG, exp_rescale H hy] at h
  exact h

/-! ### Slot counts -/

theorem sqrt_le_one_add {y : ℝ} (hy : 0 ≤ y) : Real.sqrt y ≤ 1 + y := by
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

/-- The baseline slot count: `N ≤ 2 + 4τ + √(τ³/ε)`. -/
theorem tsteps_le {τ ε : ℝ} (hτ : 0 ≤ τ) :
    (TimeSchedule.steps τ ε : ℝ) ≤ 2 + 4 * τ + Real.sqrt (τ ^ 3 / ε) := by
  unfold TimeSchedule.steps TimeSchedule.threshold
  push_cast
  have h0 : 0 ≤ max (4 * τ) (Real.sqrt (τ ^ 3 / ε)) := le_max_of_le_left (by linarith)
  have hc := Nat.ceil_lt_add_one h0
  have hm : max (4 * τ) (Real.sqrt (τ ^ 3 / ε)) ≤ 4 * τ + Real.sqrt (τ ^ 3 / ε) :=
    max_le (by linarith [Real.sqrt_nonneg (τ ^ 3 / ε)]) (by linarith)
  linarith

/-- The arithmetic of the clipped slot count. -/
theorem steps_arith {A ε x y : ℝ} (hA : 1 ≤ A) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hx : x ≤ A + A ^ 2 / ε) (hy : y ≤ A / 2 + A ^ 2 / 25) (hx0 : 0 ≤ x) :
    1 + (⌈max x y⌉₊ : ℝ) ≤ 5 * A ^ 2 / ε := by
  have hc := Nat.ceil_lt_add_one (le_max_of_le_left hx0 : 0 ≤ max x y)
  have hp1 : 0 ≤ A / 2 + A ^ 2 / 25 := by positivity
  have hp2 : 0 ≤ A + A ^ 2 / ε := by positivity
  have hm : max x y ≤ (A + A ^ 2 / ε) + (A / 2 + A ^ 2 / 25) :=
    max_le (le_add_of_le_of_nonneg hx hp1) (le_add_of_nonneg_of_le hp2 hy)
  have hA2 : A ≤ A ^ 2 := by nlinarith
  have hAε : A ^ 2 ≤ A ^ 2 / ε := by
    rw [le_div_iff₀ hε]
    nlinarith [sq_nonneg A]
  have h1 : (1 : ℝ) ≤ A ^ 2 := by nlinarith
  have e : 5 * A ^ 2 / ε = 5 * (A ^ 2 / ε) := by ring
  rw [e]
  linarith

/-- **The slot count of the clipped regime** is polynomial: `N_s ≤ d²/(5ε)` for the filter degree
`d`. (With `A = qk`: `a ≤ A/4`, `a/ζ = 100 sk/h ≤ A²/50`, `a Q₀ = 2sτ/h`, and `d ≥ 5A`.) -/
theorem clip_steps_le {s τ ε : ℝ} (R : Regime s τ ε) :
    (steps s τ ε : ℝ) ≤ (degree s τ ε : ℝ) ^ 2 / (5 * ε) := by
  have hq := R.q_pos
  have hq4 := R.q_large
  have hk1 := R.one_le_k_real
  have hk := kval_ge τ ε
  have hr := R.r_pos
  have hh := R.h_pos
  have hh4 := R.h_large
  have hτ := R.one_le_τ
  have hτ0 := R.τ_pos
  have hε := R.ε_pos
  have hε1 := R.ε_le
  have hs1 := R.one_le_s
  have ha := R.a_pos
  set q := qval s τ ε with hqdef
  set k : ℝ := (kval τ ε : ℝ) with hkdef
  set A : ℝ := q * k with hAdef
  have hA1 : 1 ≤ A := by nlinarith
  -- `d ≥ 5A`
  have hd : 5 * A ≤ (degree s τ ε : ℝ) := by
    rw [R.degree_eq]
    have hB : (0 : ℝ) ≤ (B0 s τ ε : ℝ) - 1 := by
      have := R.one_le_B0
      have : (1 : ℝ) ≤ (B0 s τ ε : ℝ) := by exact_mod_cast this
      linarith
    have hm0 : (0 : ℝ) ≤ (mval τ ε : ℝ) := Nat.cast_nonneg _
    have hp := R.five_q_le_p_sub_one
    have : k * (5 * q) ≤ k * ((pval s τ ε : ℝ) - 1) := mul_le_mul_of_nonneg_left hp (by linarith)
    nlinarith [mul_nonneg hm0 hB]
  -- `a ≤ A/4`
  have haA : aval s τ ε ≤ A / 4 := by
    have h1 := R.a_le_qr
    have h2 : q * rval τ ε ≤ q * (k / 4) := mul_le_mul_of_nonneg_left (by linarith) hq.le
    rw [hAdef]
    linarith
  -- `sτ ≤ q² k/4`
  have hsτ : s * τ ≤ q ^ 2 * k / 4 := by
    rw [R.s_tau_eq]
    have hq' := R.q_ge_qstar
    have hq0 := R.qstar_pos
    have h1 : qstar s τ ε ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hq0.le hq' 2
    have h2 : qstar s τ ε ^ 2 * rval τ ε ≤ q ^ 2 * rval τ ε :=
      mul_le_mul_of_nonneg_right h1 hr.le
    have h3 : q ^ 2 * rval τ ε ≤ q ^ 2 * (k / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hs : s ≤ q ^ 2 * k / 4 := by nlinarith
  -- the three terms of the mesh requirement
  have hz : aval s τ ε * (8 / zeta s τ ε) = 800 * s * k / hval τ ε := by
    unfold aval zeta
    rw [← hqdef, ← hkdef]
    field_simp
    ring
  have hz' : 800 * s * k / hval τ ε ≤ A ^ 2 / 50 := by
    rw [div_le_iff₀ hh]
    have : 800 * s * k ≤ 800 * (q ^ 2 * k / 4) * k :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have hA2 : A ^ 2 = q ^ 2 * k ^ 2 := by rw [hAdef]; ring
    rw [hA2]
    nlinarith [sq_nonneg (q * k)]
  have hQ : aval s τ ε * (6 * Q0 s τ ε) = 12 * (s * τ) / hval τ ε := by
    unfold aval Q0
    rw [← hqdef]
    field_simp
    ring
  have hQ' : 12 * (s * τ) / hval τ ε ≤ A ^ 2 / 50 := by
    rw [div_le_iff₀ hh]
    have hA2 : A ^ 2 = q ^ 2 * k ^ 2 := by rw [hAdef]; ring
    have hkk : k ≤ k ^ 2 := by nlinarith
    have : q ^ 2 * k ≤ q ^ 2 * k ^ 2 := mul_le_mul_of_nonneg_left hkk (by positivity)
    rw [hA2]
    nlinarith
  have hmesh : meshMin s τ ε ≤ A / 2 + A ^ 2 / 25 := by
    unfold meshMin
    rw [mul_add, mul_add, hz, hQ]
    nlinarith
  -- the Cayley threshold
  have hthr : SparseHamiltonian.TimeSchedule.threshold (aval s τ ε) (ε / 3) ≤ A + A ^ 2 / ε := by
    unfold SparseHamiltonian.TimeSchedule.threshold
    refine max_le (by nlinarith [sq_nonneg A, div_nonneg (sq_nonneg A) hε.le]) ?_
    have hsq : Real.sqrt (aval s τ ε ^ 3 / (ε / 3)) ≤ A ^ 2 / ε := by
      rw [Real.sqrt_le_left (by positivity)]
      have h1 : aval s τ ε ^ 3 ≤ (A / 4) ^ 3 := pow_le_pow_left₀ ha.le haA 3
      have h2 : aval s τ ε ^ 3 / (ε / 3) = 3 * aval s τ ε ^ 3 / ε := by field_simp
      rw [h2, div_pow, div_le_div_iff₀ hε (by positivity)]
      have h3 : 3 * aval s τ ε ^ 3 ≤ A ^ 4 := by nlinarith [pow_le_pow_right₀ hA1 (show 3 ≤ 4 by norm_num)]
      have h4 : ε ^ 2 ≤ ε := by nlinarith
      calc 3 * aval s τ ε ^ 3 * ε ^ 2 ≤ A ^ 4 * ε := by
            have : 0 ≤ 3 * aval s τ ε ^ 3 := by positivity
            calc 3 * aval s τ ε ^ 3 * ε ^ 2 ≤ 3 * aval s τ ε ^ 3 * ε :=
                  mul_le_mul_of_nonneg_left h4 this
              _ ≤ A ^ 4 * ε := mul_le_mul_of_nonneg_right h3 hε.le
        _ = (A ^ 2) ^ 2 * ε := by ring
    linarith [Real.sqrt_nonneg (aval s τ ε ^ 3 / (ε / 3))]
  -- assemble
  have hdA : 25 * A ^ 2 ≤ (degree s τ ε : ℝ) ^ 2 := by
    have h0 : 0 ≤ 5 * A := by linarith only [hA1]
    have h2 := mul_le_mul hd hd h0 (by linarith only [hA1, hd])
    linarith only [h2]
  have hfin : 5 * A ^ 2 / ε ≤ (degree s τ ε : ℝ) ^ 2 / (5 * ε) := by
    rw [div_le_div_iff₀ hε (by positivity)]
    have h2 := mul_le_mul_of_nonneg_right hdA hε.le
    linarith only [h2]
  have hx0 : 0 ≤ SparseHamiltonian.TimeSchedule.threshold (aval s τ ε) (ε / 3) := by
    unfold SparseHamiltonian.TimeSchedule.threshold
    exact le_max_of_le_left (by linarith only [ha])
  have h5 := steps_arith hA1 hε (by linarith only [hε1]) hthr hmesh hx0
  refine le_trans ?_ hfin
  unfold steps
  push_cast
  exact h5

/-! ### The regime interfaces -/

/-- **The bounded-regime interface** (`h_a` bounded): "`K₀ = √σ E_H`, `J₀†K₀J₀ = H/(√s η)`,
`J₀†K₀²J₀ ⪯ I`, `‖K₀‖ ≤ √σ`", with `J₀ = U_J ι₀` on `a` ancilla qubits and `c = √s η`. -/
structure BoundedIface (P : Type*) [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [CompleteSpace P] (σ c : ℝ) (H : P →L[ℂ] P) where
  /-- The number of ancilla qubits. -/
  a : ℕ
  /-- The boundary preparation: `J₀ = U_J ι₀`. -/
  UJ : Anc a P →L[ℂ] Anc a P
  /-- The generator `K₀`. -/
  K : Anc a P →L[ℂ] Anc a P
  unitary : IsUnitary UJ
  self : star K = K
  norm_le : ‖K‖ ≤ Real.sqrt σ
  boundary_le : ‖K ∘L (UJ ∘L iota0)‖ ≤ 1
  compress : (UJ ∘L iota0)† ∘L K ∘L (UJ ∘L iota0) = (c : ℂ)⁻¹ • H

/-- **The signed-factor interface** (`gate:eq:whole-factor`): the factor `B = Π U_B U_J ι₀` of the
wire-defined interface `wKnown U_J f z` with `B†B ⪯ δ I` and `H = λ B†ZB`; in Theorem
`gate:thm:main`, `λ = sμ` and `δ = σ^{-1/2}`. -/
structure SignedIface (P : Type*) [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [CompleteSpace P] (lam δ : ℝ) (H : P →L[ℂ] P) where
  /-- The number of ancilla qubits of the factor. -/
  a : ℕ
  /-- The preparation `U_J`. -/
  UJ : Anc a P →L[ℂ] Anc a P
  /-- The factor unitary `U_B`. -/
  U : Anc a P →L[ℂ] Anc a P
  unitaryJ : IsUnitary UJ
  unitaryU : IsUnitary U
  /-- The success wire. -/
  f : Fin a
  /-- The sign wire. -/
  z : Fin a
  ne : f ≠ z
  factor_le : (wKnown UJ (unitary_adj_comp unitaryJ) f z).Dop U ≤ (δ : ℂ) • (1 : P →L[ℂ] P)
  ham : sgHam UJ unitaryJ f z lam U = H

/-- **The clipped-transducer interface** (`gate:eq:joint-moments`): the joint boundary
`J_b = U_J ι₀`, the private Hermitian operator `K_b` with its Cayley unitary `D` and the isolated
projections `P_±`, satisfying the hypotheses `Core.CoreData σ θ ε` of the large-sparsity core, with
`J_b†K_bJ_b = H/α`; in Theorem `gate:thm:main`, `α = sμ/q`. -/
structure ClippedIface (P : Type*) [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [CompleteSpace P] (σ θ ε α : ℝ) (H : P →L[ℂ] P) where
  /-- The number of ancilla qubits. -/
  a : ℕ
  /-- The joint boundary preparation. -/
  UJ : Anc a P →L[ℂ] Anc a P
  /-- The private Cayley unitary. -/
  D : Anc a P →L[ℂ] Anc a P
  /-- The private Hermitian operator. -/
  K : Anc a P →L[ℂ] Anc a P
  /-- The isolated projection at `e^{2πi/p}`. -/
  Pp : Anc a P →L[ℂ] Anc a P
  /-- The isolated projection at `e^{-2πi/p}`. -/
  Pm : Anc a P →L[ℂ] Anc a P
  unitaryJ : IsUnitary UJ
  unitaryD : IsUnitary D
  core : Core.CoreData σ θ ε K D Pp Pm (UJ ∘L iota0)
  compress : (UJ ∘L iota0)† ∘L K ∘L (UJ ∘L iota0) = (α : ℂ)⁻¹ • H

/-! ### The claims of Theorem `gate:thm:main` -/

/-- **The conclusions of Theorem `gate:thm:main`** for a circuit `l` on `a` ancilla qubits, `2^m`
slots and `2^r` labels, run with the boundary `U_J` and the private operation `D`. -/
structure GateClaims {a m r K : ℕ} (UJ D : Anc a P →L[ℂ] Anc a P)
    (l : List (Instr (Wire a m r K))) (H : P →L[ℂ] P) (t ε Q : ℝ) : Prop where
  valid : ∀ i ∈ l, i.Valid Wire.anc
  unitary : IsUnitary (run (simSem UJ D) l)
  priv : (nPriv l : ℝ) ≤ 2 * 10 ^ 11 * Q
  uj : (nUJ l : ℝ) ≤ 2 * 10 ^ 11 * Q
  gates : (nGates l : ℝ) ≤ 10 ^ 13 * (Q + 1) * (a + m + r + 1)
  wires : Fintype.card (Wire a m r K) ≤ 2 * a + 3 * m + 6 * r + 5
  mesh : ((2 ^ m : ℕ) : ℝ) ≤ 10 ^ 36 * (Q + 1) ^ 4 / ε
  labels : ((2 ^ r : ℕ) : ℝ) ≤ 10 ^ 8 * (Q + 1)
  error : ‖run (simSem UJ D) l ∘L io - io ∘L NormedSpace.exp ((-I * (t : ℂ)) • H)‖ ≤ ε

/-! ### The circuits for a real time -/

/-- The bounded-regime circuit for a real time `t`: the circuit of `bounded_gate_simulation`, or
its literal inverse for `t < 0`. -/
def bdSigned (a : ℕ) (σ θ ε t : ℝ) :
    List (Instr (SimWire a (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε)) :=
  if 0 ≤ t then bdCircuit a σ θ ε else invList (bdCircuit a σ θ ε)

/-- The clipped-regime circuit for a real time `t`. -/
def clipSigned (a : ℕ) (σ θ ε t : ℝ) : List (Instr (ClipWire a σ θ ε)) :=
  if 0 ≤ t then clipCircuit a σ θ ε else invList (clipCircuit a σ θ ε)

theorem ite_counts {W : Type*} (c : Prop) [Decidable c] (l : List (Instr W)) :
    nPriv (if c then l else invList l) = nPriv l ∧ nUJ (if c then l else invList l) = nUJ l ∧
      nGates (if c then l else invList l) = nGates l := by
  split_ifs
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨nPriv_invList l, nUJ_invList l, nGates_invList l⟩

theorem ite_valid {a m r K : ℕ} (c : Prop) [Decidable c] (l : List (Instr (Wire a m r K)))
    (h : ∀ i ∈ l, i.Valid Wire.anc) : ∀ i ∈ (if c then l else invList l), i.Valid Wire.anc := by
  split_ifs
  · exact h
  · exact invList_valid l h

/-! ### Scalar bounds for the claims -/

theorem le_mul_X4 {X ε c : ℝ} (hX : 1 ≤ X) (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 0 ≤ c) :
    c ≤ c * (X ^ 4 / ε) := by
  have h1 : 1 ≤ X ^ 4 := one_le_pow₀ hX
  have h2 : 1 ≤ X ^ 4 / ε := by rw [le_div_iff₀ hε]; linarith
  nlinarith

/-- The slot count of the bounded regime. -/
theorem bd_mesh_le {τ ε X : ℝ} (hτ : 0 ≤ τ) (hτX : τ ≤ 288000 * X) (hX : 1 ≤ X) (hε : 0 < ε)
    (hε1 : ε ≤ 1) : 2 * (TimeSchedule.steps τ (ε / 3) : ℝ) ≤ 10 ^ 36 * X ^ 4 / ε := by
  have h1 := tsteps_le (ε := ε / 3) hτ
  have hy : 0 ≤ τ ^ 3 / (ε / 3) := by positivity
  have h2 := sqrt_le_one_add hy
  have hX0 : 0 ≤ X := by linarith
  have hτ3 : τ ^ 3 ≤ (288000 * X) ^ 3 := pow_le_pow_left₀ hτ hτX 3
  have hX34 : X ^ 3 ≤ X ^ 4 := pow_le_pow_right₀ hX (by norm_num)
  have hX14 : X ≤ X ^ 4 := by
    have := pow_le_pow_right₀ hX (show 1 ≤ 4 by norm_num)
    simpa using this
  have hdiv : τ ^ 3 / (ε / 3) = 3 * τ ^ 3 / ε := by field_simp
  have hcube : 3 * τ ^ 3 / ε ≤ 3 * 288000 ^ 3 * (X ^ 4 / ε) := by
    rw [show 3 * 288000 ^ 3 * (X ^ 4 / ε) = 3 * 288000 ^ 3 * X ^ 4 / ε by ring]
    apply div_le_div_of_nonneg_right _ hε.le
    have : (288000 * X) ^ 3 = 288000 ^ 3 * X ^ 3 := by ring
    nlinarith
  have hlin : 4 * τ ≤ 1152000 * (X ^ 4 / ε) := by
    have := le_mul_X4 hX hε hε1 (show (0 : ℝ) ≤ 1152000 * X ^ 4 by positivity)
    have h4 : 1152000 * X ^ 4 * (X ^ 4 / ε) = 1152000 * X ^ 4 * (X ^ 4 / ε) := rfl
    have hXε : X ^ 4 ≤ X ^ 4 / ε := by
      have := le_mul_X4 hX hε hε1 (show (0 : ℝ) ≤ 1 by norm_num)
      rw [le_div_iff₀ hε]
      nlinarith [one_le_pow₀ hX (n := 4)]
    nlinarith
  have h3 : (3 : ℝ) ≤ 3 * (X ^ 4 / ε) := by
    have := le_mul_X4 hX hε hε1 (show (0 : ℝ) ≤ 3 by norm_num)
    linarith
  rw [hdiv] at h1 h2
  have e : 10 ^ 36 * X ^ 4 / ε = 10 ^ 36 * (X ^ 4 / ε) := by ring
  rw [e]
  have hY : 0 ≤ X ^ 4 / ε := by positivity
  linarith

/-! ### The bounded regime -/

/-- **The bounded regime** (`h_a < 10⁴`): the baseline Cayley circuit with the public rescaling. -/
theorem bounded_branch [FiniteDimensional ℂ P] {s : ℕ} {η μ t ε σ θ : ℝ}
    (hμη : μ ≤ η) (hηs : η ≤ Real.sqrt s * μ) (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2)
    (hθd : θ = η ^ 2 * |t| / μ) (hθ : 1 ≤ θ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    {H : P →L[ℂ] P} (hH : star H = H) (IB : BoundedIface P σ (Real.sqrt s * η) H)
    (hh : hval θ ε < 10 ^ 4) :
    GateClaims IB.UJ (bdPriv IB.K σ θ ε) (bdSigned IB.a σ θ ε t) H t ε (Qmu s η μ t ε) := by
  obtain ⟨hμ, hη, hs, hσ1, hST, hSq⟩ := two_norm_params hμη hηs hσ hθd hθ
  have hQ := Qmu_eq (ε := ε) hθd hST hSq
  have hQ0 := Qmu_nonneg (ε := ε) hθd hST hSq hθ hε hε1
  have hε1' : ε ≤ 1 := by linarith
  have hX : 1 ≤ Qmu s η μ t ε + 1 := by linarith
  obtain ⟨hv, h1, h2, h3, h4, herr, hdeg, -, hm2, -, hr2⟩ :=
    bounded_gate_simulation (θ := θ) IB.a IB.UJ IB.K IB.unitary IB.self hσ1 IB.norm_le
      IB.boundary_le (by linarith) hε hε1'
  have hsh := TwoNormSimulation.bounded_shape_le (by linarith : (0 : ℝ) ≤ σ) hθ hε hε1 hh
  rw [← hQ] at hsh
  have hdQ : (fDeg (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε : ℝ) ≤
      18432000 * Qmu s η μ t ε := by linarith only [hdeg, hsh]
  have hok : bdOK σ θ ε := ⟨hσ1, by linarith, hε, hε1'⟩
  obtain ⟨hγ, -, -, hBudget⟩ := bdGamma_spec hok
  have hSs : star (scaled IB.K (bdGamma σ θ ε)) = scaled IB.K (bdGamma σ θ ε) :=
    scaled_self_adjoint IB.K _ IB.self
  have hDu : IsUnitary (bdPriv IB.K σ θ ε) := cayleyGate_isUnitary hSs
  have hval : ∀ i ∈ bdSigned IB.a σ θ ε t, i.Valid Wire.anc := ite_valid (0 ≤ t) _ hv
  obtain ⟨c1, c2, c3⟩ := ite_counts (0 ≤ t) (bdCircuit IB.a σ θ ε)
  have hc0 : Real.sqrt s * η ≠ 0 := by
    have : 0 < Real.sqrt s := Real.sqrt_pos.mpr (by exact_mod_cast hs)
    positivity
  refine ⟨hval, run_isUnitary (simSem IB.UJ (bdPriv IB.K σ θ ε)) IB.unitary hDu _ hval,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- private calls
    change (nPriv (if 0 ≤ t then _ else _) : ℝ) ≤ _
    rw [c1, h1, Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hdQ, hQ0]
  · -- boundary calls
    change (nUJ (if 0 ≤ t then _ else _) : ℝ) ≤ _
    rw [c2, h2, Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hdQ, hQ0]
  · -- gates
    change (nGates (if 0 ≤ t then _ else _) : ℝ) ≤ _
    rw [c3]
    have h3' : (nGates (bdCircuit IB.a σ θ ε) : ℝ) ≤
        200 * ((fDeg (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε : ℝ) + 1) *
          ((IB.a : ℝ) + simM (bdTau σ θ ε) ε + simR (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε +
            1) := by exact_mod_cast h3
    have hw : (0 : ℝ) ≤ (IB.a : ℝ) + simM (bdTau σ θ ε) ε +
        simR (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε + 1 :=
      add_nonneg (add_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)) zero_le_one
    have hk : 200 * ((fDeg (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε : ℝ) + 1) ≤
        10 ^ 13 * (Qmu s η μ t ε + 1) := by linarith only [hdQ, hQ0]
    refine h3'.trans ?_
    exact mul_le_mul_of_nonneg_right hk hw
  · -- wires
    have := h4
    change Fintype.card (SimWire IB.a (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε) ≤ _
    omega
  · -- slots
    have hτ0 : 0 ≤ bdTau σ θ ε := div_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) hγ.le
    have hmom : 1 / 2 ≤ moment (bdGamma σ θ ε) := by
      have := sq_nonneg (bdGamma σ θ ε)
      unfold moment
      linarith only [this]
    have hwl : 0 ≤ width σ (bdGamma σ θ ε) * ImprovedPrecisionBudget.circuitLog ε :=
      mul_nonneg (by linarith [width_ge_one σ (bdGamma σ θ ε)])
        (ImprovedPrecisionBudget.circuitLog_pos ε hε hε1').le
    have hτm : time σ θ (bdGamma σ θ ε) * (1 / 2) ≤
        time σ θ (bdGamma σ θ ε) * moment (bdGamma σ θ ε) := mul_le_mul_of_nonneg_left hmom hτ0
    have hτX : bdTau σ θ ε ≤ 288000 * (Qmu s η μ t ε + 1) := by
      change time σ θ (bdGamma σ θ ε) ≤ _
      linarith only [hτm, hBudget, hwl, hsh, hQ0]
    have hm := bd_mesh_le hτ0 hτX hX hε hε1'
    have hm2' : ((2 ^ simM (bdTau σ θ ε) ε : ℕ) : ℝ) <
        2 * (TimeSchedule.steps (bdTau σ θ ε) (ε / 3) : ℝ) := by exact_mod_cast hm2
    exact hm2'.le.trans hm
  · -- labels
    have hr2' : ((2 ^ simR (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε : ℕ) : ℝ) ≤
        4 * ((fDeg (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε : ℝ) + 1) := by exact_mod_cast hr2
    linarith only [hr2', hdQ, hQ0]
  · -- the error
    have hy : (θ * Real.sqrt σ) / (Real.sqrt s * η) = |t| := by
      rw [show θ * Real.sqrt σ = Real.sqrt σ * θ by ring, hSq]
      field_simp
    rw [IB.compress, exp_rescale H hy] at herr
    by_cases ht : 0 ≤ t
    · have hb : bdSigned IB.a σ θ ε t = bdCircuit IB.a σ θ ε := by
        unfold bdSigned; rw [if_pos ht]
      rw [hb]
      rwa [abs_of_nonneg ht] at herr
    · have hb : bdSigned IB.a σ θ ε t = invList (bdCircuit IB.a σ θ ε) := by
        unfold bdSigned; rw [if_neg ht]
      rw [hb, run_invList]
      have hCu := run_isUnitary (simSem IB.UJ (bdPriv IB.K σ θ ε)) IB.unitary hDu _ hv
      generalize run (simSem IB.UJ (bdPriv IB.K σ θ ε)) (bdCircuit IB.a σ θ ε) = C at hCu herr ⊢
      exact err_inverse C hCu _ H hH t ε (not_le.mp ht) herr

/-! ### The signed-factor regime -/

/-- `b = sμ|t| σ^{-1/2} = √σ θ` and `T = sμ|t| = σθ`. -/
theorem signed_params {s : ℕ} {μ t σ θ : ℝ} (hσ1 : 1 ≤ σ) (hST : σ * θ = s * μ * |t|) :
    sgT ((s : ℝ) * μ) t = σ * θ ∧ sgB ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t = Real.sqrt σ * θ := by
  refine ⟨by unfold sgT; rw [hST], ?_⟩
  unfold sgB
  rw [← hST]
  have h0 : Real.sqrt σ ≠ 0 := by
    have : 0 < Real.sqrt σ := Real.sqrt_pos.mpr (by linarith)
    exact this.ne'
  have hss : Real.sqrt σ * Real.sqrt σ = σ := Real.mul_self_sqrt (by linarith)
  calc σ * θ * (Real.sqrt σ)⁻¹ = (Real.sqrt σ * Real.sqrt σ) * θ * (Real.sqrt σ)⁻¹ := by rw [hss]
    _ = Real.sqrt σ * θ * (Real.sqrt σ * (Real.sqrt σ)⁻¹) := by ring
    _ = Real.sqrt σ * θ := by rw [mul_inv_cancel₀ h0, mul_one]

/-- **The signed-factor regime** (`h_a ≥ 10⁴`, `B < L_a h_a`): Proposition `gate:prop:signed` with
`T_f = B`, `b_f = A`. -/
theorem signed_branch [FiniteDimensional ℂ P] {s : ℕ} {η μ t ε σ θ : ℝ}
    (hμη : μ ≤ η) (hηs : η ≤ Real.sqrt s * μ) (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2)
    (hθd : θ = η ^ 2 * |t| / μ) (hθ : 1 ≤ θ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    {H : P →L[ℂ] P} (IS : SignedIface P (s * μ) (Real.sqrt σ)⁻¹ H)
    (hh : 10 ^ 4 ≤ hval θ ε) (hc : σ * θ < Lval ε * hval θ ε) :
    GateClaims (liftA IS.UJ) (liftA IS.U)
      (sgCircuit IS.a IS.f IS.z (s * μ) (Real.sqrt σ)⁻¹ t ε) H t ε (Qmu s η μ t ε) := by
  obtain ⟨hμ, -, hs, hσ1, hST, hSq⟩ := two_norm_params hμη hηs hσ hθd hθ
  have hQ := Qmu_eq (ε := ε) hθd hST hSq
  have hQ0 := Qmu_nonneg (ε := ε) hθd hST hSq hθ hε hε1
  have hX : 1 ≤ Qmu s η μ t ε + 1 := by linarith
  have hlam : 0 < (s : ℝ) * μ := mul_pos (by exact_mod_cast hs) hμ
  have hsq1 : 1 ≤ Real.sqrt σ := Real.one_le_sqrt.mpr hσ1
  have hδ : 0 < (Real.sqrt σ)⁻¹ := inv_pos.mpr (by linarith)
  have hδ1 : (Real.sqrt σ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsq1
  obtain ⟨hT, hB⟩ := signed_params (s := s) (μ := μ) (t := t) hσ1 hST
  obtain ⟨hv, hpriv, huj, hgates, hcard, herr, hmesh, hlab⟩ :=
    signed_gate_simulation IS.UJ IS.U IS.unitaryJ IS.unitaryU IS.ne hlam hδ hδ1 IS.factor_le t hε
      hε1
  have hb : ε < sgB ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t := by
    rw [hB]
    have : 1 ≤ Real.sqrt σ * θ := one_le_mul_of_one_le_of_one_le hsq1 hθ
    linarith
  rw [if_neg (not_le.mpr hb), hT, hB] at hpriv
  have hsb := OptimalSparseSimulation.signed_bound hσ1 hθ hε hε1 hh hc
  have hcount := sg_count_le hlam hδ1 hε hε1 hb
  rw [hT, hB] at hcount
  have hA0 : 0 ≤ Real.sqrt σ * θ := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have hsum : Real.sqrt (σ * θ * (Real.sqrt σ * θ)) + Real.sqrt (σ * θ * SignedFactorSimulation.rb
      (Real.sqrt σ * θ) ε) + SignedFactorSimulation.rb (Real.sqrt σ * θ) ε ≤
      4 * Qmu s η μ t ε := by
    rw [hQ]
    linarith only [hsb, hA0]
  have hsum0 : 0 ≤ Real.sqrt (σ * θ * (Real.sqrt σ * θ)) + Real.sqrt (σ * θ *
      SignedFactorSimulation.rb (Real.sqrt σ * θ) ε) + SignedFactorSimulation.rb (Real.sqrt σ * θ) ε :=
    by
      have := SignedFactorSimulation.rb_pos hε hε1 (by linarith : 0 < Real.sqrt σ * θ)
      have := Real.sqrt_nonneg (σ * θ * (Real.sqrt σ * θ))
      have := Real.sqrt_nonneg (σ * θ * SignedFactorSimulation.rb (Real.sqrt σ * θ) ε)
      linarith
  have hpQ : (nPriv (sgCircuit IS.a IS.f IS.z ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) : ℝ) ≤
      2 * 10 ^ 11 * Qmu s η μ t ε := by
    have := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 4 * 10 ^ 10)
    linarith only [hpriv, this, hQ0]
  -- the clock length `n`
  set n := sigN (sgQ ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) (sgOrd ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε)
    with hn
  have hnQ : (n : ℝ) ≤ 13000000 * (Qmu s η μ t ε + 1) := by
    have := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 4 * 10 ^ 10)
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith only [hcount, this, hQ0, h0]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  refine ⟨hv, run_isUnitary (simSem (liftA IS.UJ) (liftA IS.U)) (liftA_isUnitary IS.unitaryJ)
    (liftA_isUnitary IS.unitaryU) _ hv, hpQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [huj]; exact hpQ
  · -- gates
    have hg : (nGates (sgCircuit IS.a IS.f IS.z ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) : ℝ) ≤
        64 * 3 ^ 8 * (((n : ℝ) + 1) * ((IS.a : ℝ) +
          sigM (sgQ ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) (sgOrd ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) ε +
          sigR (sgQ ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) (sgOrd ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) +
          1)) := by exact_mod_cast hgates
    have hw0 : (0 : ℝ) ≤ (IS.a : ℝ) +
        sigM (sgQ ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) (sgOrd ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) ε +
        sigR (sgQ ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) (sgOrd ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) + 1 :=
      add_nonneg (add_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)) zero_le_one
    have hk : 64 * 3 ^ 8 * ((n : ℝ) + 1) ≤ 10 ^ 13 * (Qmu s η μ t ε + 1) := by
      have := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 4 * 10 ^ 10)
      linarith only [hcount, this, hQ0]
    have hw : (IS.a : ℝ) +
        sigM (sgQ ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) (sgOrd ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) ε +
        sigR (sgQ ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) (sgOrd ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) + 1 ≤
        ((IS.a + 1 : ℕ) : ℝ) +
        sigM (sgQ ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) (sgOrd ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) ε +
        sigR (sgQ ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) (sgOrd ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) + 1 := by
      have : ((IS.a + 1 : ℕ) : ℝ) = (IS.a : ℝ) + 1 := by push_cast; ring
      rw [this]
      linarith only
    have hQ1 : (0 : ℝ) ≤ 10 ^ 13 * (Qmu s η μ t ε + 1) := by linarith only [hQ0]
    calc (nGates (sgCircuit IS.a IS.f IS.z ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) : ℝ) ≤ _ := hg
      _ = (64 * 3 ^ 8 * ((n : ℝ) + 1)) * ((IS.a : ℝ) +
          sigM (sgQ ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) (sgOrd ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) ε +
          sigR (sgQ ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) (sgOrd ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) +
          1) := by ring
      _ ≤ _ := mul_le_mul hk hw hw0 hQ1
  · -- wires
    have := hcard
    change Fintype.card (SgWire IS.a ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) ≤ _
    omega
  · -- slots
    have hm := hmesh hb
    have hn4 : (n : ℝ) ^ 4 ≤ (13000000 * (Qmu s η μ t ε + 1)) ^ 4 :=
      pow_le_pow_left₀ hn0 hnQ 4
    have hY : (10 : ℝ) ^ 7 * (n : ℝ) ^ 4 ≤ 10 ^ 36 * (Qmu s η μ t ε + 1) ^ 4 := by
      have e : (13000000 * (Qmu s η μ t ε + 1)) ^ 4 = 13000000 ^ 4 * (Qmu s η μ t ε + 1) ^ 4 := by
        ring
      rw [e] at hn4
      have : (0 : ℝ) ≤ (Qmu s η μ t ε + 1) ^ 4 := by positivity
      linarith only [hn4, this]
    calc (((2 ^ sigM (sgQ ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε)
          (sgOrd ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) ε : ℕ)) : ℝ) ≤ 10 ^ 7 * (n : ℝ) ^ 4 / ε := hm
      _ ≤ 10 ^ 36 * (Qmu s η μ t ε + 1) ^ 4 / ε := div_le_div_of_nonneg_right hY hε.le
  · -- labels
    have hl : ((2 ^ sigR (sgQ ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε)
        (sgOrd ((s : ℝ) * μ) (Real.sqrt σ)⁻¹ t ε) : ℕ) : ℝ) < 2 * ((n : ℝ) + 2) := by
      exact_mod_cast hlab
    linarith only [hl, hnQ, hQ0]
  · -- the error
    rw [IS.ham] at herr
    exact herr

/-! ### The clipped-transducer regime -/

/-- **The clipped-transducer regime** (`h_a ≥ 10⁴`, `B ≥ L_a h_a`): Proposition `gate:prop:core`. -/
theorem clipped_branch [FiniteDimensional ℂ P] {s : ℕ} {η μ t ε σ θ : ℝ}
    (hμη : μ ≤ η) (hηs : η ≤ Real.sqrt s * μ) (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2)
    (hθd : θ = η ^ 2 * |t| / μ) (R : Regime σ θ ε) {H : P →L[ℂ] P} (hH : star H = H)
    (IC : ClippedIface P σ θ ε (s * μ / qval σ θ ε) H) :
    GateClaims IC.UJ IC.D (clipSigned IC.a σ θ ε t) H t ε (Qmu s η μ t ε) := by
  have hθ := R.one_le_τ
  have hε := R.ε_pos
  have hε1 := R.ε_le
  obtain ⟨hμ, -, hs, -, hST, hSq⟩ := two_norm_params hμη hηs hσ hθd hθ
  have hQ := Qmu_eq (ε := ε) hθd hST hSq
  have hQ0 := Qmu_nonneg (ε := ε) hθd hST hSq hθ hε hε1
  have hX : 1 ≤ Qmu s η μ t ε + 1 := by linarith
  have hε1' : ε ≤ 1 := by linarith
  obtain ⟨hv, h1, h2, h3, h4, herr, -, hm2, -, hr2⟩ :=
    clipped_gate_simulation IC.a R IC.UJ IC.D IC.unitaryJ IC.unitaryD IC.core
  have hdeg := R.degree_le_sqrt
  have hdQ : (degree σ θ ε : ℝ) ≤ 21520 * Qmu s η μ t ε := by
    rw [hQ]
    have h0 : 0 ≤ Real.sqrt σ * θ := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
    have hr := R.r_pos
    linarith only [hdeg, h0, hr]
  have hd0 : (0 : ℝ) ≤ (degree σ θ ε : ℝ) := Nat.cast_nonneg _
  have hval : ∀ i ∈ clipSigned IC.a σ θ ε t, i.Valid Wire.anc := ite_valid (0 ≤ t) _ hv
  obtain ⟨c1, c2, c3⟩ := ite_counts (0 ≤ t) (clipCircuit IC.a σ θ ε)
  refine ⟨hval, run_isUnitary (simSem IC.UJ IC.D) IC.unitaryJ IC.unitaryD _ hval,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (nPriv (if 0 ≤ t then _ else _) : ℝ) ≤ _
    rw [c1, h1, Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hdQ, hQ0]
  · change (nUJ (if 0 ≤ t then _ else _) : ℝ) ≤ _
    rw [c2, h2, Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hdQ, hQ0]
  · change (nGates (if 0 ≤ t then _ else _) : ℝ) ≤ _
    rw [c3]
    have h3' : (nGates (clipCircuit IC.a σ θ ε) : ℝ) ≤
        200 * ((degree σ θ ε : ℝ) + 1) * ((IC.a : ℝ) + clipM σ θ ε + clipR σ θ ε + 1) := by
      exact_mod_cast h3
    have hw : (0 : ℝ) ≤ (IC.a : ℝ) + clipM σ θ ε + clipR σ θ ε + 1 :=
      add_nonneg (add_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)) zero_le_one
    have hk : 200 * ((degree σ θ ε : ℝ) + 1) ≤ 10 ^ 13 * (Qmu s η μ t ε + 1) := by
      linarith only [hdQ, hQ0]
    exact h3'.trans (mul_le_mul_of_nonneg_right hk hw)
  · have := h4
    change Fintype.card (ClipWire IC.a σ θ ε) ≤ _
    omega
  · -- slots
    have hm2' : ((2 ^ clipM σ θ ε : ℕ) : ℝ) < 2 * (steps σ θ ε : ℝ) := by exact_mod_cast hm2
    have hst := clip_steps_le R
    have hd2 : (degree σ θ ε : ℝ) ^ 2 ≤ (21520 * (Qmu s η μ t ε + 1)) ^ 2 :=
      pow_le_pow_left₀ hd0 (by linarith only [hdQ, hQ0]) 2
    have hX24 : (Qmu s η μ t ε + 1) ^ 2 ≤ (Qmu s η μ t ε + 1) ^ 4 :=
      pow_le_pow_right₀ hX (by norm_num)
    have hnum : 2 * (degree σ θ ε : ℝ) ^ 2 / 5 ≤ 10 ^ 36 * (Qmu s η μ t ε + 1) ^ 4 := by
      have e : (21520 * (Qmu s η μ t ε + 1)) ^ 2 = 21520 ^ 2 * (Qmu s η μ t ε + 1) ^ 2 := by ring
      rw [e] at hd2
      have : (0 : ℝ) ≤ (Qmu s η μ t ε + 1) ^ 2 := by positivity
      linarith only [hd2, hX24, this]
    have e2 : 2 * ((degree σ θ ε : ℝ) ^ 2 / (5 * ε)) = (2 * (degree σ θ ε : ℝ) ^ 2 / 5) / ε := by
      field_simp
    calc ((2 ^ clipM σ θ ε : ℕ) : ℝ) ≤ 2 * ((degree σ θ ε : ℝ) ^ 2 / (5 * ε)) := by
          linarith only [hm2', hst]
      _ = (2 * (degree σ θ ε : ℝ) ^ 2 / 5) / ε := e2
      _ ≤ 10 ^ 36 * (Qmu s η μ t ε + 1) ^ 4 / ε := div_le_div_of_nonneg_right hnum hε.le
  · have hr2' : ((2 ^ clipR σ θ ε : ℕ) : ℝ) ≤ 4 * ((degree σ θ ε : ℝ) + 1) := by
      exact_mod_cast hr2
    linarith only [hr2', hdQ, hQ0]
  · -- the error
    have hq := R.q_pos
    have hy : aval σ θ ε / ((s : ℝ) * μ / qval σ θ ε) = |t| := by
      unfold aval
      rw [hST]
      have : (s : ℝ) * μ ≠ 0 := (mul_pos (by exact_mod_cast hs) hμ).ne'
      field_simp
    rw [IC.compress, exp_rescale H hy] at herr
    by_cases ht : 0 ≤ t
    · have hb : clipSigned IC.a σ θ ε t = clipCircuit IC.a σ θ ε := by
        unfold clipSigned; rw [if_pos ht]
      rw [hb]
      rwa [abs_of_nonneg ht] at herr
    · have hb : clipSigned IC.a σ θ ε t = invList (clipCircuit IC.a σ θ ε) := by
        unfold clipSigned; rw [if_neg ht]
      rw [hb, run_invList]
      have hCu := run_isUnitary (simSem (m := clipM σ θ ε) (r := clipR σ θ ε)
        (K := clipK IC.a σ θ ε) IC.UJ IC.D) IC.unitaryJ IC.unitaryD _ hv
      generalize run (simSem (m := clipM σ θ ε) (r := clipR σ θ ε) (K := clipK IC.a σ θ ε) IC.UJ
        IC.D) (clipCircuit IC.a σ θ ε) = C at hCu herr ⊢
      exact err_inverse C hCu _ H hH t ε (not_le.mp ht) herr

end

end GateOptimalPrecision
