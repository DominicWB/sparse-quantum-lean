import GateOptimalPrecision.Combine

/-!
# Theorem `gate:thm:main` and its single-norm case at the gate level

**Theorem `gate:thm:main`** (`gate_optimal_simulation`, gate-efficient optimal-precision
simulation). Let `0 < μ ≤ η ≤ √s μ`, `θ = η²|t|/μ ≥ 1`, `0 < ε ≤ 1/64`, `sμ² = ση²`
(`gate:eq:effective`), and let `H` be self-adjoint on a finite-dimensional system space. Suppose the
private operations of the three regimes are given on gate registers by their interfaces
(`BoundedIface`, `SignedIface`, `ClippedIface`; in the paper they are the native constructions of
Section `gate:sec:native`, whose identities enter here as hypotheses), each required only in its own
regime. With `L = log(1/ε)` and `h = log(e + L/θ)` (`Lval`, `hval`; the manuscript's Section
`gate:sec:combine` uses `ε_a = ε/2` in these, which only moves the thresholds by absolute factors),
the regimes and circuits are

* `h < 10⁴`: the baseline Cayley circuit `bdSigned` with the generator `K₀`;
* `h ≥ 10⁴` and `σθ < Lh`: the signed-factor circuit `sgCircuit` with the factor `U_B`;
* `h ≥ 10⁴` and `σθ ≥ Lh` (`Regime`): the clipped-transducer circuit `clipSigned` with the joint
  representation;

satisfies `GateClaims` with `Q_μ = √s η|t| + √(sμ|t| r_μ) + r_μ` (`Qmu`): it is a valid, unitary
circuit of elementary gates and oracle calls with at most `2·10¹¹ Q_μ` private calls and at most
`2·10¹¹ Q_μ` boundary calls, at most `10¹³ (Q_μ + 1)(a + m + r + 1)` elementary gates on at most
`2a + 3m + 6r + 5` qubits, `2^m ≤ 10³⁶ (Q_μ + 1)⁴/ε` and `2^r ≤ 10⁸ (Q_μ + 1)`, so that
`m = O(log((Q_μ + 1)/ε))` and `r = O(log(Q_μ + 1))`, and full-output error at most `ε` for
`e^{-itH}` (`gate:eq:full`), for both signs of `t` (the actual inverse circuit for `t < 0`).

The circuits are fixed by public data: the ancilla count of the interface and its wires, and
`s, η, μ, t, ε`. In the paper each private or boundary call has constant sparse-query cost by the
native constructions of Section `gate:sec:native`; that is not formalised here (the calls are oracle
calls of the gate model). Finite-set synthesis is not included (arbitrary one-qubit gates are
elementary). An untouched reference is part of the system space: for `H ⊗ I` on a system with a
finite reference the same circuit and bounds apply.

**The single-norm case** (`gate_optimal_simulation_single`, single supplied norm): `μ = η`, so
`σ = s`, `θ = τ = η|t| ≥ 1`, and `Q_μ = Q = √s τ + √(sτr) + r` with
`r = log(1/ε)/log(e + log(1/ε)/τ)` (`Qone`, `Qmu_self`).
-/

set_option autoImplicit false

namespace GateOptimalPrecision

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim
open LargeSparsityCore LargeSparsityCore.Parameters
open scoped InnerProduct InnerProductSpace BigOperators ComplexOrder

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **Theorem `gate:thm:main` (gate-efficient optimal-precision simulation), exact gates.** See the
module docstring. -/
theorem gate_optimal_simulation [FiniteDimensional ℂ P] {s : ℕ} {η μ t ε σ θ : ℝ}
    (hμη : μ ≤ η) (hηs : η ≤ Real.sqrt s * μ) (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2)
    (hθd : θ = η ^ 2 * |t| / μ) (hθ : 1 ≤ θ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    {H : P →L[ℂ] P} (hH : star H = H)
    (IB : hval θ ε < 10 ^ 4 → BoundedIface P σ (Real.sqrt s * η) H)
    (IS : 10 ^ 4 ≤ hval θ ε → σ * θ < Lval ε * hval θ ε →
      SignedIface P (s * μ) (Real.sqrt σ)⁻¹ H)
    (IC : Regime σ θ ε → ClippedIface P σ θ ε (s * μ / qval σ θ ε) H) :
    (∃ hb : hval θ ε < 10 ^ 4,
      GateClaims (IB hb).UJ (bdPriv (IB hb).K σ θ ε) (bdSigned (IB hb).a σ θ ε t) H t ε
        (Qmu s η μ t ε)) ∨
    (∃ (h1 : 10 ^ 4 ≤ hval θ ε) (h2 : σ * θ < Lval ε * hval θ ε),
      GateClaims (liftA (IS h1 h2).UJ) (liftA (IS h1 h2).U)
        (sgCircuit (IS h1 h2).a (IS h1 h2).f (IS h1 h2).z (s * μ) (Real.sqrt σ)⁻¹ t ε) H t ε
        (Qmu s η μ t ε)) ∨
    (∃ R : Regime σ θ ε,
      GateClaims (IC R).UJ (IC R).D (clipSigned (IC R).a σ θ ε t) H t ε (Qmu s η μ t ε)) := by
  by_cases h1 : hval θ ε < 10 ^ 4
  · exact Or.inl ⟨h1, bounded_branch hμη hηs hσ hθd hθ hε hε1 hH (IB h1) h1⟩
  · replace h1 : 10 ^ 4 ≤ hval θ ε := not_lt.mp h1
    by_cases h2 : Lval ε * hval θ ε ≤ σ * θ
    · obtain ⟨-, -, -, hσ1, -, -⟩ := two_norm_params hμη hηs hσ hθd hθ
      have R : Regime σ θ ε := ⟨hσ1, hθ, hε, hε1, h1, h2⟩
      exact Or.inr (Or.inr ⟨R, clipped_branch hμη hηs hσ hθd R hH (IC R)⟩)
    · have h2' : σ * θ < Lval ε * hval θ ε := not_le.mp h2
      exact Or.inr (Or.inl ⟨h1, h2', signed_branch hμη hηs hσ hθd hθ hε hε1 (IS h1 h2') h1 h2'⟩)

/-- The query count of the single-norm case: `Q = √s τ + √(sτr) + r` with `τ = η|t|` and
`r = L/log(e + L/τ)`. -/
def Qone (s : ℕ) (η t ε : ℝ) : ℝ :=
  Real.sqrt s * (η * |t|) + Real.sqrt (s * (η * |t|) * rval (η * |t|) ε) + rval (η * |t|) ε

/-- `Q_η = Q`. -/
theorem Qmu_self {s : ℕ} {η t ε : ℝ} (hη : 0 < η) : Qmu s η η t ε = Qone s η t ε := by
  unfold Qmu Qone
  have e : η ^ 2 * |t| / η = η * |t| := by field_simp
  rw [e]
  simp only [mul_assoc]

/-- **The single-norm case of Theorem `gate:thm:main` (single supplied norm), exact gates**: the
theorem at `μ = η`. -/
theorem gate_optimal_simulation_single [FiniteDimensional ℂ P] {s : ℕ} (hs : 1 ≤ s) {η t ε : ℝ}
    (hη : 0 < η) (hτ : 1 ≤ η * |t|) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) {H : P →L[ℂ] P}
    (hH : star H = H) (IB : hval (η * |t|) ε < 10 ^ 4 → BoundedIface P s (Real.sqrt s * η) H)
    (IS : 10 ^ 4 ≤ hval (η * |t|) ε → (s : ℝ) * (η * |t|) < Lval ε * hval (η * |t|) ε →
      SignedIface P (s * η) (Real.sqrt s)⁻¹ H)
    (IC : Regime s (η * |t|) ε → ClippedIface P s (η * |t|) ε (s * η / qval s (η * |t|) ε) H) :
    (∃ hb : hval (η * |t|) ε < 10 ^ 4,
      GateClaims (IB hb).UJ (bdPriv (IB hb).K s (η * |t|) ε) (bdSigned (IB hb).a s (η * |t|) ε t)
        H t ε (Qone s η t ε)) ∨
    (∃ (h1 : 10 ^ 4 ≤ hval (η * |t|) ε) (h2 : (s : ℝ) * (η * |t|) < Lval ε * hval (η * |t|) ε),
      GateClaims (liftA (IS h1 h2).UJ) (liftA (IS h1 h2).U)
        (sgCircuit (IS h1 h2).a (IS h1 h2).f (IS h1 h2).z (s * η) (Real.sqrt s)⁻¹ t ε) H t ε
        (Qone s η t ε)) ∨
    (∃ R : Regime s (η * |t|) ε,
      GateClaims (IC R).UJ (IC R).D (clipSigned (IC R).a s (η * |t|) ε t) H t ε
        (Qone s η t ε)) := by
  have hs1 : (1 : ℝ) ≤ Real.sqrt s := Real.one_le_sqrt.mpr (by exact_mod_cast hs)
  have hηs : η ≤ Real.sqrt s * η := le_mul_of_one_le_left hη.le hs1
  have hθd : η * |t| = η ^ 2 * |t| / η := by field_simp
  have h := gate_optimal_simulation (σ := (s : ℝ)) (θ := η * |t|) (μ := η) le_rfl hηs rfl hθd hτ
    hε hε1 hH IB IS IC
  rw [Qmu_self hη] at h
  exact h

end

end GateOptimalPrecision
