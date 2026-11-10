import GateOptimalPrecision.SignedCore

/-!
# Proposition `gate:prop:signed`: the signed-factor gate bound

The signed-factor simulator of Appendix `gate:sec:proof` at the gate level, for every real time and
with the explicit constants of the query proof (`SignedFactorSimulation.signed_factor_simulation`).

Public parameters (`sgT`, `sgB`, `sgOrd`, `sgQ`, `sgKap`): `T = λ|t|`, `b = Tδ`, the order
`M = ⌈40000 b + 100000 r_b⌉` (`SignedFactorSimulation.order`), and either `q = √(T/M)`, `κ = 1`
(if `M ≤ T`) or `q = 1` with the attenuation `κ = T/M` (if `T < M`): "If `T_f < M`, attenuate `B`
by `√(T_f/M)` and increase `λ` so that `T_f' = M`; this preserves `H` and `b_f`. Use `q = 1`,
`a = M` in that case. The attenuation is a known flag rotation, with no extra factor queries."
The circuit `sgCircuit` is empty if `b ≤ ε` ("If `b_f ≤ ε/2`, use the identity"; here `b ≤ ε`
with `‖e^{-itH} - I‖ ≤ b`), the signed-factor circuit `sigCircuit` for `t ≥ 0`, and its literal
inverse for `t < 0` ("negative time uses the inverse circuit").

**Proposition `gate:prop:signed`** (`signed_gate_simulation`). Let `U_J`, `U_B` be unitaries on `a`
ancilla qubits and the system (finite-dimensional), let `f ≠ z` be the success and sign wires of the
factor interface `wKnown U_J f z` (`B = Π U_B U_J ι₀`, `C = B†ZB`, `D = B†B`) with `D ⪯ δ I`,
`0 < δ ≤ 1`, `λ > 0`, `H = λ C`, and `0 < ε ≤ 1/64`. Then the circuit is valid, it makes `nPriv`
calls of `U_B` or `U_B†` (on the last `a` of `a + 1` ancillas) with `nPriv = 0` if `b ≤ ε` and
`nPriv ≤ 4·10¹⁰ (√(Tb) + √(T r_b) + r_b)` otherwise, the same number of calls of `U_J` or `U_J†`, at
most `64·3⁸ (n+1)(a+m+r+1)` elementary gates, on `2a + 3m + 6r + 5` qubit wires, with `n` the number
of clock weights, `2^m ≤ 10⁷ n⁴/ε` slot bits and `2^r < 2(n+2)`, and its full output is within `ε`
of `e^{-itH}`.
-/

set_option autoImplicit false

namespace GateOptimalPrecision

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim
open Complex (I)
open SignedFactorSimulation (Known rb order)
open scoped InnerProduct InnerProductSpace BigOperators ComplexOrder

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Public parameters -/

/-- `T = λ|t|`. -/
def sgT (lam t : ℝ) : ℝ := lam * |t|

/-- `b = Tδ`. -/
def sgB (lam δ t : ℝ) : ℝ := lam * |t| * δ

/-- The order `M = ⌈40000 b + 100000 r_b⌉`. -/
def sgOrd (lam δ t ε : ℝ) : ℕ := order (sgB lam δ t) ε

/-- `q = √(T/M)` if `M ≤ T`, else `1`. -/
def sgQ (lam δ t ε : ℝ) : ℝ :=
  if (sgOrd lam δ t ε : ℝ) ≤ sgT lam t then Real.sqrt (sgT lam t / sgOrd lam δ t ε) else 1

/-- The attenuation `κ = 1` if `M ≤ T`, else `T/M`. -/
def sgKap (lam δ t ε : ℝ) : ℝ :=
  if (sgOrd lam δ t ε : ℝ) ≤ sgT lam t then 1 else sgT lam t / sgOrd lam δ t ε

/-- The wires of the signed-factor simulator. -/
abbrev SgWire (a : ℕ) (lam δ t ε : ℝ) := SigWire a (sgQ lam δ t ε) (sgOrd lam δ t ε) ε

/-- **The signed-factor simulation circuit** for a real time `t`, fixed by the public data
`a, f, z, λ, δ, t, ε`. -/
def sgCircuit (a : ℕ) (f z : Fin a) (lam δ t ε : ℝ) : List (Instr (SgWire a lam δ t ε)) :=
  if sgB lam δ t ≤ ε then [] else
    if 0 ≤ t then sigCircuit a f z (sgQ lam δ t ε) (sgOrd lam δ t ε) ε (sgKap lam δ t ε)
    else invList (sigCircuit a f z (sgQ lam δ t ε) (sgOrd lam δ t ε) ε (sgKap lam δ t ε))

/-! ### The parameter identities -/

theorem sg_params {lam δ t ε : ℝ} (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    (hb : ε < sgB lam δ t) :
    1 ≤ sgQ lam δ t ε ∧ 0 ≤ sgKap lam δ t ε ∧ sgKap lam δ t ε ≤ 1 ∧
      sgQ lam δ t ε ^ 2 * sgOrd lam δ t ε * sgKap lam δ t ε = sgT lam t ∧
      1 ≤ sgOrd lam δ t ε := by
  have hb0 : 0 < sgB lam δ t := hε.trans hb
  have hM1 : 1 ≤ sgOrd lam δ t ε := SignedFactorSimulation.one_le_order hε hε1 hb0
  have hM0 : (0 : ℝ) < sgOrd lam δ t ε := by exact_mod_cast hM1
  have hT : 0 ≤ sgT lam t := mul_nonneg hlam.le (abs_nonneg t)
  refine ⟨?_, ?_, ?_, ?_, hM1⟩
  · unfold sgQ
    split_ifs with h
    · rw [Real.le_sqrt (by norm_num) (by positivity), one_pow, le_div_iff₀ hM0, one_mul]
      exact h
    · exact le_rfl
  · unfold sgKap; split_ifs <;> positivity
  · unfold sgKap
    split_ifs with h
    · exact le_rfl
    · push Not at h
      rw [div_le_one hM0]; exact h.le
  · unfold sgQ sgKap
    split_ifs with h
    · rw [Real.sq_sqrt (by positivity), mul_one]; field_simp
    · rw [one_pow, one_mul]; field_simp

theorem sg_b_eq {lam δ t ε : ℝ} (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    (hb : ε < sgB lam δ t) :
    sgQ lam δ t ε ^ 2 * sgOrd lam δ t ε * (sgKap lam δ t ε * δ) = sgB lam δ t := by
  obtain ⟨-, -, -, h, -⟩ := sg_params hlam hε hε1 hb
  rw [show sgQ lam δ t ε ^ 2 * sgOrd lam δ t ε * (sgKap lam δ t ε * δ) =
    (sgQ lam δ t ε ^ 2 * sgOrd lam δ t ε * sgKap lam δ t ε) * δ by ring, h]
  rfl

/-! ### The counts -/

/-- The factor-call count of the query theorem. -/
theorem sg_count_le {lam δ t ε : ℝ} (hlam : 0 < lam) (hδ1 : δ ≤ 1) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64) (hb : ε < sgB lam δ t) :
    (2 * 3 ^ 8 * sigN (sgQ lam δ t ε) (sgOrd lam δ t ε) : ℝ) ≤
      4 * 10 ^ 10 * (Real.sqrt (sgT lam t * sgB lam δ t) +
        Real.sqrt (sgT lam t * rb (sgB lam δ t) ε) + rb (sgB lam δ t) ε) := by
  obtain ⟨hq1, -, -, -, hM1⟩ := sg_params hlam hε hε1 hb
  have hb0 : 0 < sgB lam δ t := hε.trans hb
  have hr := SignedFactorSimulation.rb_pos hε hε1 hb0
  have hMle := SignedFactorSimulation.order_le hε hε1 hb
  have hn := OptimalPrecision.clockLength_le hq1 hM1
  have hT : 0 ≤ sgT lam t := mul_nonneg hlam.le (abs_nonneg t)
  have hbT : sgB lam δ t ≤ sgT lam t := by
    unfold sgB sgT
    have := mul_le_mul_of_nonneg_left hδ1 hT
    unfold sgT at this
    linarith
  have hM0 : (0 : ℝ) < sgOrd lam δ t ε := by exact_mod_cast hM1
  by_cases hTM : (sgOrd lam δ t ε : ℝ) ≤ sgT lam t
  · have hq : sgQ lam δ t ε = Real.sqrt (sgT lam t / sgOrd lam δ t ε) := by
      unfold sgQ; rw [if_pos hTM]
    have hqM : sgQ lam δ t ε * sgOrd lam δ t ε = Real.sqrt (sgT lam t * sgOrd lam δ t ε) := by
      rw [hq, show sgT lam t * sgOrd lam δ t ε =
          (sgT lam t / sgOrd lam δ t ε) * (sgOrd lam δ t ε : ℝ) ^ 2 by field_simp,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hM0.le]
    have h := SignedFactorSimulation.count_le_of_large hT hb0.le hr.le hMle
    rw [hqM] at hn
    have : (2 * 3 ^ 8 * sigN (sgQ lam δ t ε) (sgOrd lam δ t ε) : ℝ) ≤
        2 * 3 ^ 8 * 27 * Real.sqrt (sgT lam t * sgOrd lam δ t ε) := by
      nlinarith
    exact this.trans h
  · have hq : sgQ lam δ t ε = 1 := by unfold sgQ; rw [if_neg hTM]
    rw [hq, one_mul] at hn
    have h := SignedFactorSimulation.count_le_of_small hb0.le hbT hr.le hMle
    have : (2 * 3 ^ 8 * sigN (sgQ lam δ t ε) (sgOrd lam δ t ε) : ℝ) ≤
        2 * 3 ^ 8 * 27 * (sgOrd lam δ t ε) := by
      rw [hq]; nlinarith
    exact this.trans h

/-- The gate bound in product form. -/
theorem sig_gate_bound (a n m r : ℕ) (hr : 2 ^ r < 2 * (n + 2)) :
    3 ^ 8 * (2 * (2 ^ r * (2 * r + 1)) + 2 * ((n + 2) * (8 * r + 2)) +
      n * (4 * (a + 1) + 8 * m + 7 * r + 5) + 2 * ((a + 1) + m + 2 * r) + 3 + 5 * n) ≤
      64 * 3 ^ 8 * ((n + 1) * (a + m + r + 1)) := by
  have h1 : 2 ^ r * (2 * r + 1) ≤ 2 * (n + 2) * (2 * r + 1) :=
    Nat.mul_le_mul_right _ hr.le
  nlinarith [Nat.zero_le (n * a), Nat.zero_le (n * m), Nat.zero_le (n * r), Nat.zero_le a,
    Nat.zero_le m, Nat.zero_le r, Nat.zero_le n]

/-- The slot count is polynomial: `2^m ≤ 10⁷ n⁴/ε`. -/
theorem sigM_le {q : ℝ} (hq : 1 ≤ q) {M : ℕ} (hM : 1 ≤ M) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((2 ^ sigM q M ε : ℕ) : ℝ) ≤ 10 ^ 7 * (sigN q M : ℝ) ^ 4 / ε := by
  have hspec := (sigM_spec q M ε).2
  have hn1 : (1 : ℝ) ≤ sigN q M := by exact_mod_cast one_le_sigN q M
  have haN := qM_le_sigN hq hM
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have ha : 1 ≤ q * M := by nlinarith
  set n : ℝ := (sigN q M : ℝ) with hn
  set A : ℝ := q * M with hA
  have hLB0 : 0 ≤ sigMeshLB q M ε := (by positivity : (0 : ℝ) ≤ 8 * A * n).trans (le_max_left _ _)
  have hceil : (⌈sigMeshLB q M ε⌉₊ : ℝ) ≤ sigMeshLB q M ε + 1 :=
    (Nat.ceil_lt_add_one hLB0).le
  have h2 : ((2 ^ sigM q M ε : ℕ) : ℝ) ≤ 2 * sigMeshLB q M ε + 3 := by
    have : ((2 ^ sigM q M ε : ℕ) : ℝ) ≤ 2 * (⌈sigMeshLB q M ε⌉₊ : ℝ) + 1 := by exact_mod_cast hspec
    linarith
  -- the two branches of the maximum
  have hη : sigEta ε = ε ^ 2 / (2 * 7 ^ 8) := rfl
  have hn2 : n ^ 2 ≤ n ^ 4 := pow_le_pow_right₀ hn1 (by norm_num)
  have hn4 : n ^ 4 ≤ n ^ 4 / ε := by
    rw [le_div_iff₀ hε]
    nlinarith [pow_pos (show (0 : ℝ) < n by linarith) 4]
  have hb1 : 8 * A * n ≤ 8 * n ^ 4 / ε := by
    have : A * n ≤ n ^ 2 := by nlinarith
    have : 8 * n ^ 4 / ε = 8 * (n ^ 4 / ε) := by ring
    nlinarith
  have hb2 : Real.sqrt (768000 * A ^ 3 * n ^ 4 / sigEta ε) ≤ 4 * 10 ^ 6 * n ^ 4 / ε := by
    rw [Real.sqrt_le_left (by positivity)]
    have e1 : 768000 * A ^ 3 * n ^ 4 / sigEta ε =
        (768000 * (2 * 7 ^ 8)) * (A ^ 3 * n ^ 4) / ε ^ 2 := by
      rw [hη]; field_simp
    have e2 : (4 * 10 ^ 6 * n ^ 4 / ε) ^ 2 = (16 * 10 ^ 12) * (n ^ 4 * n ^ 4) / ε ^ 2 := by
      field_simp; ring
    rw [e1, e2]
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr
    have hA3 : A ^ 3 ≤ n ^ 4 :=
      (pow_le_pow_left₀ (by linarith) haN 3).trans (pow_le_pow_right₀ hn1 (by norm_num))
    have hX : A ^ 3 * n ^ 4 ≤ n ^ 4 * n ^ 4 := mul_le_mul_of_nonneg_right hA3 (by positivity)
    have hX0 : 0 ≤ A ^ 3 * n ^ 4 := by positivity
    nlinarith
  have hmax : sigMeshLB q M ε ≤ 4 * 10 ^ 6 * n ^ 4 / ε := by
    unfold sigMeshLB
    refine max_le (hb1.trans ?_) hb2
    apply (div_le_div_iff_of_pos_right hε).mpr
    nlinarith [pow_pos (show (0 : ℝ) < n by linarith) 4]
  have h3 : (3 : ℝ) ≤ 3 * n ^ 4 / ε := by
    rw [le_div_iff₀ hε]
    have : (1 : ℝ) ≤ n ^ 4 := one_le_pow₀ hn1
    nlinarith
  calc ((2 ^ sigM q M ε : ℕ) : ℝ) ≤ 2 * sigMeshLB q M ε + 3 := h2
    _ ≤ 2 * (4 * 10 ^ 6 * n ^ 4 / ε) + 3 * n ^ 4 / ε := by linarith
    _ = (8 * 10 ^ 6 + 3) * n ^ 4 / ε := by ring
    _ ≤ 10 ^ 7 * n ^ 4 / ε := by
        apply (div_le_div_iff_of_pos_right hε).mpr
        nlinarith [pow_pos (show (0 : ℝ) < n by linarith) 4]

/-! ### Negative time -/

theorem err_inverse {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (C : K →L[ℂ] K) (hC : IsUnitary C) (ι : P →L[ℂ] K) (H : P →L[ℂ] P) (hH : star H = H)
    (t ε : ℝ) (ht : t < 0)
    (h : ‖C ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * ((|t| : ℝ) : ℂ)) • H)‖ ≤ ε) :
    ‖C† ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)‖ ≤ ε := by
  have hV := LabeledAdjointSimulation.evolution_unitary H hH |t|
  have hadj := LabeledAdjointSimulation.evolution_adjoint H hH |t|
  have ht' : ((-|t| : ℝ) : ℂ) = (t : ℂ) := by rw [abs_of_neg ht, neg_neg]
  rw [ht'] at hadj
  rw [← hadj, LabeledAdjointSimulation.adjoint_error_eq _ _ hC hV]
  exact h

/-! ### Proposition `gate:prop:signed` -/

/-- The represented Hamiltonian `H = λ C` of the wire-defined factor interface. -/
abbrev sgHam {a : ℕ} (UJ : Anc a P →L[ℂ] Anc a P) (hUJ : IsUnitary UJ) (f z : Fin a) (lam : ℝ)
    (U : Anc a P →L[ℂ] Anc a P) : P →L[ℂ] P :=
  (wKnown UJ (unitary_adj_comp hUJ) f z).ham lam U

/-- **Proposition `gate:prop:signed` (signed-factor gate bound), exact gates.** See the module
docstring. -/
theorem signed_gate_simulation [FiniteDimensional ℂ P] {a : ℕ} (UJ U : Anc a P →L[ℂ] Anc a P)
    (hUJ : IsUnitary UJ) (hU : IsUnitary U) {f z : Fin a} (hfz : f ≠ z) {lam δ : ℝ}
    (hlam : 0 < lam) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hD : (wKnown UJ (unitary_adj_comp hUJ) f z).Dop U ≤ (δ : ℂ) • (1 : P →L[ℂ] P))
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    (∀ i ∈ sgCircuit a f z lam δ t ε, i.Valid Wire.anc) ∧
    ((nPriv (sgCircuit a f z lam δ t ε) : ℝ) ≤ (if sgB lam δ t ≤ ε then 0 else
      4 * 10 ^ 10 * (Real.sqrt (sgT lam t * sgB lam δ t) +
        Real.sqrt (sgT lam t * rb (sgB lam δ t) ε) + rb (sgB lam δ t) ε))) ∧
    nUJ (sgCircuit a f z lam δ t ε) = nPriv (sgCircuit a f z lam δ t ε) ∧
    nGates (sgCircuit a f z lam δ t ε) ≤
      64 * 3 ^ 8 * ((sigN (sgQ lam δ t ε) (sgOrd lam δ t ε) + 1) *
        (a + sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε + sigR (sgQ lam δ t ε) (sgOrd lam δ t ε) +
          1)) ∧
    Fintype.card (SgWire a lam δ t ε) =
      2 * a + 3 * sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε +
        6 * sigR (sgQ lam δ t ε) (sgOrd lam δ t ε) + 5 ∧
    ‖run (simSem (liftA UJ) (liftA U)) (sgCircuit a f z lam δ t ε) ∘L io -
        io ∘L NormedSpace.exp ((-I * (t : ℂ)) • sgHam UJ hUJ f z lam U)‖ ≤ ε ∧
    (ε < sgB lam δ t →
      ((2 ^ sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε : ℕ) : ℝ) ≤
        10 ^ 7 * (sigN (sgQ lam δ t ε) (sgOrd lam δ t ε) : ℝ) ^ 4 / ε) ∧
    2 ^ sigR (sgQ lam δ t ε) (sgOrd lam δ t ε) <
      2 * (sigN (sgQ lam δ t ε) (sgOrd lam δ t ε) + 2) := by
  have hcard : Fintype.card (SgWire a lam δ t ε) =
      2 * a + 3 * sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε +
        6 * sigR (sgQ lam δ t ε) (sgOrd lam δ t ε) + 5 := by
    rw [card_wire, sigK]; ring
  have hr2 := (sigR_spec (sgQ lam δ t ε) (sgOrd lam δ t ε)).2.2
  by_cases hsmall : sgB lam δ t ≤ ε
  · -- the identity
    have hc : sgCircuit a f z lam δ t ε = [] := by unfold sgCircuit; rw [if_pos hsmall]
    rw [hc, if_pos hsmall]
    refine ⟨fun i hi => by simp at hi, by simp [nPriv], rfl, by simp [nGates], hcard, ?_,
      fun h => absurd hsmall (not_le.mpr h), hr2⟩
    rw [run_nil, SignedFactorSimulation.one_comp']
    have hsub : ∀ V : P →L[ℂ] P, (io (a := a + 1) (m := sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε)
        (r := sigR (sgQ lam δ t ε) (sgOrd lam δ t ε))
        (K := sigK a (sgQ lam δ t ε) (sgOrd lam δ t ε) ε) (P := P)) - io ∘L V = io ∘L (1 - V) := by
      intro V
      rw [comp_sub, SignedFactorSimulation.comp_one']
    rw [hsub]
    calc _ ≤ ‖(io (a := a + 1) (m := sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε)
          (r := sigR (sgQ lam δ t ε) (sgOrd lam δ t ε))
          (K := sigK a (sgQ lam δ t ε) (sgOrd lam δ t ε) ε) (P := P))‖ *
          ‖1 - NormedSpace.exp ((-I * (t : ℂ)) • sgHam UJ hUJ f z lam U)‖ := opNorm_comp_le _ _
      _ ≤ 1 * ‖1 - NormedSpace.exp ((-I * (t : ℂ)) • sgHam UJ hUJ f z lam U)‖ :=
          mul_le_mul_of_nonneg_right io_norm_le (norm_nonneg _)
      _ = ‖NormedSpace.exp ((-I * (t : ℂ)) • sgHam UJ hUJ f z lam U) - 1‖ := by
          rw [one_mul, norm_sub_rev]
      _ ≤ |t| * ‖sgHam UJ hUJ f z lam U‖ :=
          SignedFactorSimulation.norm_evolution_sub_one_le _
            ((wKnown UJ (unitary_adj_comp hUJ) f z).ham_star lam U) t
      _ ≤ |t| * (lam * δ) :=
          mul_le_mul_of_nonneg_left
            ((wKnown UJ (unitary_adj_comp hUJ) f z).norm_ham_le hlam.le hδ.le U hD) (abs_nonneg t)
      _ = sgB lam δ t := by unfold sgB; ring
      _ ≤ ε := hsmall
  · push Not at hsmall
    obtain ⟨hq1, hκ0, hκ1, hqMκ, hM1⟩ := sg_params hlam hε hε1 hsmall
    have hb0 : 0 < sgB lam δ t := hε.trans hsmall
    have hMge := SignedFactorSimulation.order_ge (sgB lam δ t) ε
    have htail := SignedFactorSimulation.tail_bound hε hε1 hb0 hMge
    have hbeq := sg_b_eq hlam hε hε1 hsmall
    have htail' : 2 * (3000 + 1) * (Real.exp 2 * 27 ^ 2 *
        (sgQ lam δ t ε ^ 2 * sgOrd lam δ t ε * (sgKap lam δ t ε * δ)) / sgOrd lam δ t ε) ^
          sgOrd lam δ t ε ≤ ε ^ 2 / (4 * 7 ^ 8) := by
      rw [hbeq]; exact htail
    have hMb : 2 * 27 ^ 2 * (sgQ lam δ t ε ^ 2 * sgOrd lam δ t ε * (sgKap lam δ t ε * δ)) ≤
        sgOrd lam δ t ε := by
      rw [hbeq]
      have hr := SignedFactorSimulation.rb_pos hε hε1 hb0
      have : (sgOrd lam δ t ε : ℝ) ≥ 40000 * sgB lam δ t + 100000 * rb (sgB lam δ t) ε := hMge
      nlinarith
    have hD' : (attKnown UJ hUJ f z hκ0 hκ1).Dop (liftA U) ≤
        ((sgKap lam δ t ε * δ : ℝ) : ℂ) • (1 : P →L[ℂ] P) := by
      rw [attKnown_Dop]
      exact SignedFactorSimulation.smul_le_smul_one hκ0 hD
    have hcore := sig_core UJ U hUJ hU hfz hκ0 hκ1 hq1 hM1 (by positivity) hD' hMb hε
      (by linarith) htail'
    -- the exponent
    have hexp : (-(I * ((sgQ lam δ t ε ^ 2 * sgOrd lam δ t ε : ℝ) : ℂ))) •
        (attKnown UJ hUJ f z hκ0 hκ1).Cop (liftA U) =
        (-I * ((|t| : ℝ) : ℂ)) • sgHam UJ hUJ f z lam U := by
      rw [attKnown_Cop, sgHam, Known.ham, smul_smul, smul_smul]
      congr 1
      have h2c : ((sgQ lam δ t ε ^ 2 * sgOrd lam δ t ε : ℝ) : ℂ) * (sgKap lam δ t ε : ℂ) =
          (lam : ℂ) * ((|t| : ℝ) : ℂ) := by
        have h2 : (sgQ lam δ t ε ^ 2 * sgOrd lam δ t ε * sgKap lam δ t ε : ℝ) = lam * |t| :=
          hqMκ
        exact_mod_cast h2
      linear_combination (-I) * h2c
    rw [hexp] at hcore
    have hvalid := sig_valid a hfz hq1 (sgOrd lam δ t ε) ε hκ0 hκ1
    obtain ⟨hc1, hc2, hc3⟩ := sig_counts a f z (sgQ lam δ t ε) (sgOrd lam δ t ε) ε (sgKap lam δ t ε)
    have hcnt := sg_count_le hlam hδ1 hε hε1 hsmall
    have hgb := sig_gate_bound a (sigN (sgQ lam δ t ε) (sgOrd lam δ t ε))
      (sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε) (sigR (sgQ lam δ t ε) (sgOrd lam δ t ε)) hr2
    have hG := hc3.trans hgb
    have hm := sigM_le hq1 hM1 hε (by linarith)
    rw [if_neg (not_le.mpr hsmall)]
    by_cases ht : 0 ≤ t
    · have hc : sgCircuit a f z lam δ t ε =
          sigCircuit a f z (sgQ lam δ t ε) (sgOrd lam δ t ε) ε (sgKap lam δ t ε) := by
        unfold sgCircuit; rw [if_neg (not_le.mpr hsmall), if_pos ht]
      rw [hc]
      rw [abs_of_nonneg ht] at hcore
      refine ⟨hvalid, ?_, by rw [hc1, hc2], hG, hcard, hcore, fun _ => hm, hr2⟩
      rw [hc1]; exact_mod_cast hcnt
    · push Not at ht
      have hc : sgCircuit a f z lam δ t ε =
          invList (sigCircuit a f z (sgQ lam δ t ε) (sgOrd lam δ t ε) ε (sgKap lam δ t ε)) := by
        unfold sgCircuit; rw [if_neg (not_le.mpr hsmall), if_neg (not_le.mpr ht)]
      rw [hc]
      refine ⟨invList_valid _ hvalid, ?_, by rw [nUJ_invList, nPriv_invList, hc1, hc2],
        by rw [nGates_invList]; exact hG, hcard, ?_, fun _ => hm, hr2⟩
      swap
      · have hCu : IsUnitary (run (simSem (m := sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε)
            (r := sigR (sgQ lam δ t ε) (sgOrd lam δ t ε))
            (K := sigK a (sgQ lam δ t ε) (sgOrd lam δ t ε) ε) (liftA UJ) (liftA U))
            (sigCircuit a f z (sgQ lam δ t ε) (sgOrd lam δ t ε) ε (sgKap lam δ t ε))) :=
          run_isUnitary (simSem (m := sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε)
            (r := sigR (sgQ lam δ t ε) (sgOrd lam δ t ε))
            (K := sigK a (sgQ lam δ t ε) (sgOrd lam δ t ε) ε) (liftA UJ) (liftA U))
            (liftA_isUnitary hUJ) (liftA_isUnitary hU) _ hvalid
        rw [run_invList]
        generalize run (simSem (m := sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε)
            (r := sigR (sgQ lam δ t ε) (sgOrd lam δ t ε))
            (K := sigK a (sgQ lam δ t ε) (sgOrd lam δ t ε) ε) (liftA UJ) (liftA U))
            (sigCircuit a f z (sgQ lam δ t ε) (sgOrd lam δ t ε) ε (sgKap lam δ t ε)) = C
          at hCu hcore ⊢
        exact err_inverse C hCu _ _ ((wKnown UJ (unitary_adj_comp hUJ) f z).ham_star lam U) t ε ht
          hcore
      rw [nPriv_invList, hc1]; exact_mod_cast hcnt

end

end GateOptimalPrecision
