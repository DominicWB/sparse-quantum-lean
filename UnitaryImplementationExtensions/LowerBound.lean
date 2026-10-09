import UnitaryImplementationExtensions.SearchFamily
import UnitaryImplementationExtensions.LiftPhase
import UnitaryImplementationExtensions.General
import UnitaryImplementationExtensions.Inexact

set_option autoImplicit false

/-!
# The `Θ(√N)` query complexity of black-box unitary implementation

The last sentence of corollary `hs:cor:unitary` of the manuscript (lines
1786-1787): at fixed constant error the worst-case query complexity is
`Θ(√N)`. The manuscript states the lower half without a detailed argument
(lines 1833-1840, a reduction from unstructured search); it is proved here.

The hard instances are the search unitaries `SearchFamily.searchMatrix N m`.
Their one-bit reversible entry lookup is the Boolean phase oracle of the marked
strings `(j, k) ↦ (j + k = m)` (`PhaseBridge.lookup_eq_phase`), so each entry
query is one search query, and a constant-error implementation, applied to
`|0⟩`, prepares `|m⟩`. The bound holds

* for every program over the ordinary entry lookup with an arbitrary untouched
  payload Hilbert space and an arbitrary isometric input encoding
  (`entry_count_ge`), and
* for every program over the released entry oracle of the upper bound,
  `UnitaryEntryOracle.oracle (searchData N) γ η t ε`, for all parameters
  (`implementation_count_ge`, via `LiftPhase.oracle_eq_phase`).

Both lower bounds are `(1 - 2 ε₀ sqrt (1 - ε₀²/4)) sqrt (N - 1) / 2` queries
for error `ε₀ ≤ 1`, with a positive factor on the corollary's whole range
`0 < ε₀ ≤ 1/2`. Inverse queries are counted and fixed gates are free; the
algorithms are unitary query circuits (`OracleCircuit.Program`), the class of
the upper bound. `theta` combines the lower bound with the released upper bound
`SparseHamiltonian.UnitaryImplementation.implementation` at error `1/4`, and
`theta_of_error` with the general-precision upper bound
`General.implementation` at every fixed error `0 < ε ≤ 1/2`. Since exact data
is inexact data with zero entry error (`ApproxOracle.oracle_ofExact`),
`implementation_count_ge` at `η = 2`, time `π/2` and precision `ε/2` is the
lower bound in the oracle model of `Inexact.implementation`; `theta_inexact`
pairs it with `Inexact.implementation_ofExact`.
-/

namespace UnitaryImplementationExtensions.LowerBound

noncomputable section
open SparseHamiltonian SparseLowerBounds SearchFamily
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192

/-- **Lower bound for the ordinary entry lookup.** Every program over the
reversible entry lookup of the search family, with an arbitrary untouched
payload `W`, that implements every `U_m` on an isometric encoding with
operator-norm error at most `ε₀ ≤ 1`, makes at least
`(1 - 2 ε₀ sqrt (1 - ε₀²/4)) sqrt (N - 1) / 2` entry queries, inverse queries
included. -/
theorem entry_count_ge {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (q : OracleCircuit.Program (fun m : Fin N =>
      LookupControlledGate.oracle (K := W) (searchTable N) m))
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] PiLp 2 (fun _ : (Fin N × Fin N) × ZMod 2 => W))
    (hJ : J† ∘L J = 1) {ε₀ : ℝ} (hε₀ : ε₀ ≤ 1)
    (hErr : ∀ m, ‖q.eval m ∘L J - J ∘L
      SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤ ε₀) :
    (1 - 2 * ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4)) * Real.sqrt ((N : ℝ) - 1) ≤
      2 * q.count := by
  refine SearchFamily.count_ge_of_phase hN (PhaseBridge.xorFamily (Fin N × Fin N) W)
    (fun a => a.1 + a.2) (fun m => ?_) q J hJ hε₀ hErr
  refine (PhaseBridge.lookup_eq_phase (searchTable N) m).trans (congrArg _ (funext fun a => ?_))
  simp [Search.markedString, searchTable_eq_one_iff]

/-- **Lower bound in the oracle model of the upper bound.** Every program over
the released entry oracle `UnitaryEntryOracle.oracle (searchData N) γ η t ε`,
for any parameters, that implements every `U_m` on an isometric encoding with
operator-norm error at most `ε₀ ≤ 1`, makes at least
`(1 - 2 ε₀ sqrt (1 - ε₀²/4)) sqrt (N - 1) / 2` entry queries, inverse queries
included. -/
theorem implementation_count_ge {N : ℕ} [NeZero N] (hN : 2 ≤ N) (γ η t ε : ℝ)
    (q : OracleCircuit.Program (UnitaryEntryOracle.oracle (searchData N) γ η t ε))
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε)
    (hJ : J† ∘L J = 1) {ε₀ : ℝ} (hε₀ : ε₀ ≤ 1)
    (hErr : ∀ m, ‖q.eval m ∘L J - J ∘L
      SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤ ε₀) :
    (1 - 2 * ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4)) * Real.sqrt ((N : ℝ) - 1) ≤
      2 * q.count := by
  refine SearchFamily.count_ge_of_phase hN (LiftPhase.entryFamily (n := Fin N) γ η t ε)
    (fun a => a.1.2 + a.2.2) (fun m => ?_) q J hJ hε₀ hErr
  refine (LiftPhase.oracle_eq_phase (searchData N) γ η t ε m).trans
    (congrArg _ (funext fun a => ?_))
  change decide (searchTable N m (a.1.2, a.2.2) = 1) = decide (a.1.2 + a.2.2 = m)
  simp [searchTable_eq_one_iff]

/-- `sqrt N ≤ sqrt 2 * sqrt (N - 1)` for `N ≥ 2`. -/
theorem sqrt_le_sqrt_two_mul {N : ℕ} (hN : 2 ≤ N) :
    Real.sqrt (N : ℝ) ≤ Real.sqrt 2 * Real.sqrt ((N : ℝ) - 1) := by
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply Real.sqrt_le_sqrt
  have h : (2 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

/-- **`Θ(√N)` at error `1/4`.** For the search family on `N ≥ 2` points, the
released corollary implements every `U_m` by a unitary circuit with error at
most `1/4` using at most
`UnitaryImplementation.queryConstant * sqrt N` entry queries, and every program
over the same oracle that achieves error `1/4` on an isometric encoding uses at
least `sqrt N / (4 sqrt 2)` entry queries. -/
theorem theta {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    (∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ p : OracleCircuit.Program (UnitaryImplementation.oracle (searchData N) γ),
        (p.count : ℝ) ≤ UnitaryImplementation.queryConstant * Real.sqrt (N : ℝ) ∧
        (UnitaryImplementation.input (searchData N) γ)† ∘L
          UnitaryImplementation.input (searchData N) γ = 1 ∧
        ∀ m, IsUnitary (p.eval m) ∧
          ‖p.eval m ∘L UnitaryImplementation.input (searchData N) γ -
            UnitaryImplementation.input (searchData N) γ ∘L
              SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤ (1 / 4 : ℝ)) ∧
    ∀ (γ : ℝ) (q : OracleCircuit.Program (UnitaryImplementation.oracle (searchData N) γ))
      (J : EuclideanSpace ℂ (Fin N) →L[ℂ] UnitaryImplementation.Physical (Fin N) (ZMod 2) γ),
      J† ∘L J = 1 →
      (∀ m, ‖q.eval m ∘L J - J ∘L
        SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤ (1 / 4 : ℝ)) →
      Real.sqrt (N : ℝ) ≤ 4 * Real.sqrt 2 * q.count := by
  refine ⟨?_, ?_⟩
  · obtain ⟨γ, hγ, hγOne, p, hCount, hInput, hAction⟩ :=
      UnitaryImplementation.implementation (searchData N)
    have hcard : ((Fintype.card (Fin N) : ℕ) : ℝ) = N := by simp
    exact ⟨γ, hγ, hγOne, p, hCount.trans_eq (by rw [hcard]), hInput, hAction⟩
  · intro γ q J hJ hErr
    have h := implementation_count_ge hN γ 1 (Real.pi / 2) (1 / 4) q J hJ (by norm_num) hErr
    have hs : Real.sqrt (1 - (1 / 4 : ℝ) ^ 2 / 4) ≤ 1 := Real.sqrt_le_one.mpr (by norm_num)
    have hr : 0 ≤ Real.sqrt ((N : ℝ) - 1) := Real.sqrt_nonneg _
    have hle : Real.sqrt ((N : ℝ) - 1) ≤ 4 * q.count := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hs) hr]
    calc Real.sqrt (N : ℝ) ≤ Real.sqrt 2 * Real.sqrt ((N : ℝ) - 1) := sqrt_le_sqrt_two_mul hN
      _ ≤ Real.sqrt 2 * (4 * q.count) :=
          mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg 2)
      _ = 4 * Real.sqrt 2 * q.count := by ring

/-- **`Θ(√N)` at every fixed error `0 < ε ≤ 1/2`.** For the search family on
`N ≥ 2` points, the general-precision circuit implements every `U_m` with error
at most `ε` using at most `exactConstant (sqrt ℓ + ℓ) sqrt N` entry queries,
`ℓ = log (1/ε)`, and every program over the same oracle that achieves error `ε`
on an isometric encoding uses at least
`(1 - 2 ε sqrt (1 - ε²/4)) sqrt (N - 1) / 2` entry queries, with a positive
factor. -/
theorem theta_of_error {N : ℕ} [NeZero N] (hN : 2 ≤ N) (ε : ℝ) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2) :
    (∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ p : OracleCircuit.Program (General.oracle (searchData N) γ ε),
        (p.count : ℝ) ≤ General.exactConstant *
          (Real.sqrt (Real.log (1 / ε)) + Real.log (1 / ε)) * Real.sqrt (N : ℝ) ∧
        (General.input (searchData N) γ ε)† ∘L General.input (searchData N) γ ε = 1 ∧
        ∀ m, IsUnitary (p.eval m) ∧
          ‖p.eval m ∘L General.input (searchData N) γ ε -
            General.input (searchData N) γ ε ∘L
              SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤ ε) ∧
    0 < 1 - 2 * ε * Real.sqrt (1 - ε ^ 2 / 4) ∧
    ∀ (γ : ℝ) (q : OracleCircuit.Program (General.oracle (searchData N) γ ε))
      (J : EuclideanSpace ℂ (Fin N) →L[ℂ]
        UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ 1 (Real.pi / 2) ε),
      J† ∘L J = 1 →
      (∀ m, ‖q.eval m ∘L J - J ∘L
        SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤ ε) →
      (1 - 2 * ε * Real.sqrt (1 - ε ^ 2 / 4)) * Real.sqrt ((N : ℝ) - 1) ≤
        2 * q.count := by
  refine ⟨?_, Search.near_factor_pos hε.le hεHalf, ?_⟩
  · obtain ⟨γ, hγ, hγOne, p, hCount, hInput, hAction⟩ :=
      General.implementation (searchData N) ε hε hεHalf
    refine ⟨γ, hγ, hγOne, p, ?_, hInput, hAction⟩
    have hcard : ((Fintype.card (Fin N) : ℕ) : ℝ) = N := by simp
    have hCount' : (p.count : ℝ) ≤ General.exactConstant *
        (Real.sqrt (N : ℝ) * Real.sqrt (Real.log (1 / ε)) + Real.log (1 / ε)) := by
      refine hCount.trans_eq ?_
      rw [hcard, Real.sqrt_mul (Nat.cast_nonneg _)]
    refine hCount'.trans ?_
    have hℓ : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (one_le_one_div hε (by linarith))
    have hN1 : 1 ≤ Real.sqrt (N : ℝ) := by
      have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ N by exact_mod_cast (by omega : 1 ≤ N))
      rwa [Real.sqrt_one] at h
    have hsℓ : 0 ≤ Real.sqrt (Real.log (1 / ε)) := Real.sqrt_nonneg _
    have hbody : Real.sqrt (N : ℝ) * Real.sqrt (Real.log (1 / ε)) + Real.log (1 / ε) ≤
        (Real.sqrt (Real.log (1 / ε)) + Real.log (1 / ε)) * Real.sqrt (N : ℝ) := by
      nlinarith
    calc General.exactConstant *
          (Real.sqrt (N : ℝ) * Real.sqrt (Real.log (1 / ε)) + Real.log (1 / ε)) ≤
        General.exactConstant *
          ((Real.sqrt (Real.log (1 / ε)) + Real.log (1 / ε)) * Real.sqrt (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hbody General.exactConstant_pos.le
      _ = _ := by ring
  · intro γ q J hJ hErr
    exact implementation_count_ge hN γ 1 (Real.pi / 2) ε q J hJ (by linarith) hErr

/-- **`Θ(√N)` in the oracle model of the inexact circuit.** For the search
family on `N ≥ 2` points and every fixed error `0 < ε ≤ 1/2`, the inexact-entry
circuit (here with zero entry error) implements every `U_m` with error at most
`ε` using at most `inexactConstant (sqrt (N ℓ) + ℓ)` entry queries,
`ℓ = log (1/ε)`, over the oracle at `η = 2`, time `π/2` and precision `ε/2`, and
every program over the same oracle that achieves error `ε` on an isometric
encoding uses at least `(1 - 2 ε sqrt (1 - ε²/4)) sqrt (N - 1) / 2` entry
queries, with a positive factor. -/
theorem theta_inexact {N : ℕ} [NeZero N] (hN : 2 ≤ N) (ε : ℝ) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2) :
    (∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ p : OracleCircuit.Program
          (UnitaryEntryOracle.oracle (searchData N) γ 2 (Real.pi / 2) (ε / 2)),
        (p.count : ℝ) ≤ Inexact.inexactConstant *
          (Real.sqrt ((N : ℝ) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (Inexact.input (ApproxData.ofExact (searchData N)) γ ε)† ∘L
          Inexact.input (ApproxData.ofExact (searchData N)) γ ε = 1 ∧
        ∀ m, IsUnitary (p.eval m) ∧
          ‖p.eval m ∘L Inexact.input (ApproxData.ofExact (searchData N)) γ ε -
            Inexact.input (ApproxData.ofExact (searchData N)) γ ε ∘L
              SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤ ε) ∧
    0 < 1 - 2 * ε * Real.sqrt (1 - ε ^ 2 / 4) ∧
    ∀ (γ : ℝ) (q : OracleCircuit.Program
        (UnitaryEntryOracle.oracle (searchData N) γ 2 (Real.pi / 2) (ε / 2)))
      (J : EuclideanSpace ℂ (Fin N) →L[ℂ]
        UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ 2 (Real.pi / 2) (ε / 2)),
      J† ∘L J = 1 →
      (∀ m, ‖q.eval m ∘L J - J ∘L
        SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤ ε) →
      (1 - 2 * ε * Real.sqrt (1 - ε ^ 2 / 4)) * Real.sqrt ((N : ℝ) - 1) ≤
        2 * q.count := by
  refine ⟨?_, Search.near_factor_pos hε.le hεHalf, ?_⟩
  · obtain ⟨γ, hγ, hγOne, p, hCount, hInput, hAction⟩ :=
      Inexact.implementation_ofExact (searchData N) ε hε hεHalf
    have hcard : ((Fintype.card (Fin N) : ℕ) : ℝ) = N := by simp
    exact ⟨γ, hγ, hγOne, p, hCount.trans_eq (by rw [hcard]), hInput, hAction⟩
  · intro γ q J hJ hErr
    exact implementation_count_ge hN γ 2 (Real.pi / 2) (ε / 2) q J hJ (by linarith) hErr

end
end UnitaryImplementationExtensions.LowerBound
