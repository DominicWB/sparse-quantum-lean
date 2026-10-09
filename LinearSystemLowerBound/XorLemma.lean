import LinearSystemLowerBound.Hard.Native
import LinearSystemLowerBound.Weight.Bias

/-!
# Lemma `qlsl:lem:xor`: the XOR lower bound for Boolean queries

The hidden input consists of `n` one-hot strings of length `m`, described by their marked
positions `x : Fin n → Fin m`; the target is the parity `F(x) = ⊕_a (x_a mod 2)`, whose sign
is `parSign x = (-1)^{F(x)}`.  The Boolean oracle `|a, q, z⟩ ↦ |a, q, z ⊕ x^{(a)}_q⟩`
(`boolOracle`, with `x^{(a)}_q = [x_a = q]` and an arbitrary payload register) is an
additive lookup whose entries depend on one bit, so each Boolean query (forward or inverse)
has weight growth `(1 + 2/√m)²`.

An algorithm is an adaptive protocol over the Boolean oracle (`SparseLinearSystems.Protocol.
Tree`), followed by a two-outcome measurement of the heralded output; failure is reported as
a uniformly random bit.  For a decoder observable `M = Π₀ - Π₁` its probability of reporting
`F(x)` is `(1 + (-1)^{F(x)} Re tr(M σ_x))/2`, where `σ_x` is the unnormalised heralded output,
so success probability at least `(1 + β)/2` means `β ≤ (-1)^{F(x)} Re tr(M σ_x)`.

* `xor_lemma`: then `β ≤ 2^{-n} e^{4t/√m}`, `t` the worst-case number of Boolean queries;
* `xor_lemma_count`: equivalently `t ≥ (√m/4)(n ln 2 + ln β)` for `β > 0`.

The argument is the paper's weight-growth argument; adaptivity (fresh measured runs with
classical branching) is handled by the kernel potential of `tree_xor`.
-/

namespace LinearSystemLowerBound.Boolean

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct
open SparseHamiltonian SparseLinearSystems.Protocol LinearSystemLowerBound.Hard
  LinearSystemLowerBound.Native

variable {n m : ℕ} {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- The Boolean string bits `x^{(a)}_q = [x_a = q]`. -/
def bit (x : Fin n → Fin m) (aq : Fin n × Fin m) : ZMod 2 := if x aq.1 = aq.2 then 1 else 0

/-- **The Boolean oracle** `|a, q, z⟩ ↦ |a, q, z ⊕ x^{(a)}_q⟩` with a payload register `Q`. -/
def boolOracle (x : Fin n → Fin m) :
    PiLp 2 (fun _ : (Fin n × Fin m) × ZMod 2 => Q) →L[ℂ]
      PiLp 2 (fun _ : (Fin n × Fin m) × ZMod 2 => Q) :=
  LookupControlledGate.oracle (K := Q) bit x

omit [CompleteSpace Q] in
theorem boolOracle_apply (x : Fin n → Fin m)
    (v : PiLp 2 (fun _ : (Fin n × Fin m) × ZMod 2 => Q)) (a : Fin n) (q : Fin m) (z : ZMod 2) :
    boolOracle x v ((a, q), z) = v ((a, q), z + bit x (a, q)) := by
  rw [boolOracle, LookupControlledGate.oracle_apply]
  have h : ∀ b : ZMod 2, -b = b := by decide
  rw [sub_eq_add_neg, h]

theorem bitDetermined_bit (aq : Fin n × Fin m) : BitDetermined (fun x : Fin n → Fin m => bit x aq) :=
  Or.inr ⟨aq.1, aq.2, 0, 1, fun _ => rfl⟩

/-- **Lemma `qlsl:lem:xor`.**  If an adaptive protocol over the Boolean oracle satisfies
`β ≤ (-1)^{F(x)} Re tr(M σ_x)` on every input, for an observable `‖M‖ ≤ 1` and even `m`, then
`β ≤ 2^{-n} e^{4t/√m}` with `t` its worst-case number of Boolean queries. -/
theorem xor_lemma (hm : Even m) (hm0 : m ≠ 0) {F E : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (T : Tree (fun (_ : Unit) => boolOracle (n := n) (m := m) (Q := Q)) F E)
    (M : E →L[ℂ] E) (hM : ∀ v, ‖M v‖ ≤ ‖v‖) (β : ℝ)
    (hβ : ∀ x, β ≤ parSign x * corr M (T.successDensity x)) :
    β ≤ (1 / 2) ^ n * Real.exp (4 * T.worstCost (fun _ => 1) / Real.sqrt m) := by
  set C := (1 + 2 / Real.sqrt m) ^ 2
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hm0)
  have hC : 1 ≤ C := by
    have : (0 : ℝ) ≤ 2 / Real.sqrt m := by positivity
    nlinarith
  have hO : ∀ l : Unit, Growth (fun x => boolOracle (n := n) (m := m) (Q := Q) x)
      (C ^ (fun _ : Unit => 1) l) := by
    intro l
    simp only [pow_one]
    exact growth_lookup (Q := Q) hm0 bit bitDetermined_bit
  have hO' : ∀ l : Unit, Growth (fun x => star (boolOracle (n := n) (m := m) (Q := Q) x))
      (C ^ (fun _ : Unit => 1) l) := by
    intro l
    simp only [pow_one]
    exact growth_lookup_star (Q := Q) hm0 bit bitDetermined_bit
  have hU : ∀ (l : Unit) (x : Fin n → Fin m), OracleCircuit.IsUnitary (boolOracle (Q := Q) x) :=
    fun _ x => LookupControlledGate.oracle_unitary bit x
  have hxor := tree_xor hm hm0 hU (fun _ => 1) C hC hO hO' M hM T
  rw [Fintype.card_fin] at hxor
  have hsum : (m : ℝ) ^ n * β ≤ ∑ x, parSign x * corr M (T.successDensity x) := by
    have := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hβ x)
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_pi, Fintype.card_fin]
      using this
  have hmpos : 0 < (m : ℝ) ^ n := by
    have : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
    positivity
  have h1 : β ≤ (1 / 2) ^ n * C ^ T.worstCost (fun _ => 1) := by
    have h2 := hsum.trans ((le_abs_self _).trans hxor)
    have h3 : (m : ℝ) ^ n * β ≤ (m : ℝ) ^ n * ((1 / 2) ^ n * C ^ T.worstCost (fun _ => 1)) := by
      linarith
    exact le_of_mul_le_mul_left h3 hmpos
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hγ : 1 + 2 / Real.sqrt m ≤ Real.exp (2 / Real.sqrt m) := by
    have := Real.add_one_le_exp (2 / Real.sqrt m)
    linarith
  calc C ^ T.worstCost (fun _ => 1) = (1 + 2 / Real.sqrt m) ^ (2 * T.worstCost (fun _ => 1)) := by
        rw [pow_mul]
    _ ≤ Real.exp (2 / Real.sqrt m) ^ (2 * T.worstCost (fun _ => 1)) :=
        pow_le_pow_left₀ (by positivity) hγ _
    _ = Real.exp (4 * T.worstCost (fun _ => 1) / Real.sqrt m) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

/-- **Lemma `qlsl:lem:xor`, query form**: `t ≥ (√m/4)(n ln 2 + ln β)` for `β > 0`. -/
theorem xor_lemma_count (hm : Even m) (hm0 : m ≠ 0) {F E : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (T : Tree (fun (_ : Unit) => boolOracle (n := n) (m := m) (Q := Q)) F E)
    (M : E →L[ℂ] E) (hM : ∀ v, ‖M v‖ ≤ ‖v‖) (β : ℝ) (hβ0 : 0 < β)
    (hβ : ∀ x, β ≤ parSign x * corr M (T.successDensity x)) :
    Real.sqrt m / 4 * (n * Real.log 2 + Real.log β) ≤ T.worstCost (fun _ => 1) := by
  have h := xor_lemma hm hm0 T M hM β hβ
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hm0)
  have hlog := Real.log_le_log hβ0 h
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_pow, one_div,
    Real.log_inv] at hlog
  have : n * Real.log 2 + Real.log β ≤ 4 * T.worstCost (fun _ => 1) / Real.sqrt m := by linarith
  rw [le_div_iff₀ hsm] at this
  nlinarith

end

end LinearSystemLowerBound.Boolean
