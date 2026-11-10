import ManuscriptConformance.Defs
import SignedFactorSimulation.Theorem
import OptimalPrecision.Weights.Theorem
import LargeSparsityCore.NativeCore

/-!
# Conformance: the query-level results of Appendix `opt:sec:proof`

Theorem `opt:thm:signed`, Theorem `opt:thm:weights` and Proposition `opt:prop:core`.

**The factor model of `opt:thm:signed`** (Section `opt:sec:factor`, eq. `opt:eq:factor`). A known
isometry `E : H_sys → K` initialises the work registers, a known orthogonal projection `Π` selects
the success space `ran Π`, and a known Hermitian unitary `Z` of the success space assigns the signs.
Here `Z` is any operator on `K` whose compression `Π Z Π` is a Hermitian unitary of the success
space (`(Π Z Π)† = Π Z Π`, `(Π Z Π)² = Π`): only that compression enters `B† Z B`, and every
Hermitian unitary `Z₀` of `ran Π` arises so (take `Z = Z₀ Π`). The supplied unitary `U_B` and its
adjoint are the only oracle operations, each charged as one factor query; `B = Π U_B E`,
`C = B† Z B`, `D = B† B ⪯ δ I`, `H = λ C`, `λ > 0`, `0 < δ ≤ 1`. The registers are
finite-dimensional, as in the manuscript's circuit model. The package's factor data
(`SignedFactorSimulation.Known`) take a reflection of all of `K` commuting with `Π`; `knownOf`
builds it as `Π Z Π + (1 - Π)`, which has the same `C` (`knownOf_Cop`).

**The query model.** As in the package: a program over the factor query `I_ι ⊗ U_B` (a finite
label register `ι` on which the factor acts diagonally) and its adjoint, all other gates known
unitaries, on a known isometric encoding `J` of the system fixed before the factor unitary; the
controls of the manuscript's circuit are built inside the program, so no controlled factor query is
needed. For `opt:prop:core` the oracles are the original native sparse primitives with spectators
(`SparseHamiltonian.NativeCayleyActive.oracle`), as in `hs_thm_optimal`.
-/

set_option autoImplicit false

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open scoped InnerProduct InnerProductSpace ComplexOrder
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096

universe u v w

/-! ### Theorem `opt:thm:signed` -/

section Signed

variable {P : Type u} {W : Type v}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- `r_b = log(1/ε)/log(e + log(1/ε)/b)` for `b ≠ 0`, and `r_0 = 0` "by continuity"
(theorem `opt:thm:signed`). -/
def signedR (b ε : ℝ) : ℝ := if b = 0 then 0 else logInv ε / Real.log (Real.exp 1 + logInv ε / b)

/-- Eq. `opt:eq:signed-bound`: `√(Tb) + √(T r_b) + r_b`. -/
def signedBound (T b ε : ℝ) : ℝ :=
  Real.sqrt (T * b) + Real.sqrt (T * signedR b ε) + signedR b ε

theorem signedR_nonneg {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε) (hε1 : ε ≤ 1) : 0 ≤ signedR b ε := by
  unfold signedR
  split_ifs with h
  · exact le_rfl
  · have hL : 0 ≤ logInv ε := by
      unfold logInv; exact Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
    have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm h)
    have h1 : 1 < Real.exp 1 + logInv ε / b := by
      have := Real.add_one_lt_exp (one_ne_zero)
      have : 0 ≤ logInv ε / b := div_nonneg hL hb'.le
      linarith
    exact div_nonneg hL (Real.log_pos h1).le

theorem signedBound_nonneg {T b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ signedBound T b ε := by
  unfold signedBound
  have := signedR_nonneg hb hε hε1
  positivity

/-- The package's ratio `r_b` is the manuscript's for `b ≠ 0`. -/
theorem rb_eq_signedR {b ε : ℝ} (hb : b ≠ 0) : SignedFactorSimulation.rb b ε = signedR b ε := by
  unfold signedR
  rw [if_neg hb]
  rfl

/-- The package's factor data from the manuscript's: the reflection `Π Z Π + (1 - Π)` of the whole
preparation space. -/
def knownOf (E : P →L[ℂ] W) (Pi Z : W →L[ℂ] W) (hE : E† ∘L E = 1) (hPi : Pi† = Pi)
    (hPi2 : Pi ∘L Pi = Pi) (hZh : (Pi ∘L Z ∘L Pi)† = Pi ∘L Z ∘L Pi)
    (hZu : (Pi ∘L Z ∘L Pi) ∘L (Pi ∘L Z ∘L Pi) = Pi) : SignedFactorSimulation.Known P W where
  E := E
  proj := Pi
  Z := Pi ∘L Z ∘L Pi + (1 - Pi)
  E_isometry := hE
  proj_adjoint := hPi
  proj_idem := by rw [mul_def]; exact hPi2
  Z_adjoint := by
    rw [map_add, map_sub, adjoint_one, hZh, hPi]
  Z_sq := by
    set A := Pi ∘L Z ∘L Pi with hA
    have hP2 : Pi * Pi = Pi := by rw [mul_def]; exact hPi2
    have hAA : A * A = Pi := by rw [mul_def]; exact hZu
    have hAP : A * Pi = A := by
      rw [mul_def, hA, comp_assoc, comp_assoc, hPi2]
    have hPA : Pi * A = A := by
      rw [mul_def, hA, ← comp_assoc, hPi2]
    have e : (A + (1 - Pi)) * (A + (1 - Pi)) =
        A * A + (A - A * Pi) + (A - Pi * A) + (1 - Pi - Pi + Pi * Pi) := by noncomm_ring
    rw [e, hAA, hAP, hPA, hP2]
    abel
  Z_comm := by
    set A := Pi ∘L Z ∘L Pi with hA
    have hP2 : Pi * Pi = Pi := by rw [mul_def]; exact hPi2
    have hAP : A * Pi = A := by
      rw [mul_def, hA, comp_assoc, comp_assoc, hPi2]
    have hPA : Pi * A = A := by
      rw [mul_def, hA, ← comp_assoc, hPi2]
    have e1 : (A + (1 - Pi)) * Pi = A * Pi + (Pi - Pi * Pi) := by noncomm_ring
    have e2 : Pi * (A + (1 - Pi)) = Pi * A + (Pi - Pi * Pi) := by noncomm_ring
    rw [e1, e2, hAP, hPA]

/-- The signed compression of `knownOf` is the manuscript's `C = B† Z B`, `B = Π U_B E`. -/
theorem knownOf_Cop (E : P →L[ℂ] W) (Pi Z : W →L[ℂ] W) (hE : E† ∘L E = 1) (hPi : Pi† = Pi)
    (hPi2 : Pi ∘L Pi = Pi) (hZh : (Pi ∘L Z ∘L Pi)† = Pi ∘L Z ∘L Pi)
    (hZu : (Pi ∘L Z ∘L Pi) ∘L (Pi ∘L Z ∘L Pi) = Pi) (U : W →L[ℂ] W) :
    (knownOf E Pi Z hE hPi hPi2 hZh hZu).Cop U =
      (Pi ∘L U ∘L E)† ∘L Z ∘L (Pi ∘L U ∘L E) := by
  set B := Pi ∘L U ∘L E with hB
  have hPB : Pi ∘L B = B := by rw [hB, ← comp_assoc, hPi2]
  have hBP : B† ∘L Pi = B† := by
    conv_lhs => rw [← hPi, ← adjoint_comp, hPB]
  have hZB : (Pi ∘L Z ∘L Pi + (1 - Pi)) ∘L B = Pi ∘L Z ∘L B := by
    rw [add_comp, sub_comp, comp_assoc, comp_assoc, hPB]
    rw [show (1 : W →L[ℂ] W) ∘L B = B from ContinuousLinearMap.id_comp B]
    abel
  change B† ∘L (Pi ∘L Z ∘L Pi + (1 - Pi)) ∘L B = _
  rw [hZB, ← comp_assoc, hBP]

/-- The weight of `knownOf` is the manuscript's `D = B† B`. -/
theorem knownOf_Dop (E : P →L[ℂ] W) (Pi Z : W →L[ℂ] W) (hE : E† ∘L E = 1) (hPi : Pi† = Pi)
    (hPi2 : Pi ∘L Pi = Pi) (hZh : (Pi ∘L Z ∘L Pi)† = Pi ∘L Z ∘L Pi)
    (hZu : (Pi ∘L Z ∘L Pi) ∘L (Pi ∘L Z ∘L Pi) = Pi) (U : W →L[ℂ] W) :
    (knownOf E Pi Z hE hPi hPi2 hZh hZu).Dop U = (Pi ∘L U ∘L E)† ∘L (Pi ∘L U ∘L E) := rfl

set_option maxHeartbeats 1000000 in
/-- **Theorem `opt:thm:signed`: simulation from a signed factor.** Under
the factor-access assumptions (eq. `opt:eq:factor`: `E` a known isometry, `Π` a known orthogonal
projection, `Z` Hermitian unitary on the success space, `U_B` a supplied unitary with
`D = B† B ⪯ δ I`, `B = Π U_B E`, `H = λ B† Z B`, `λ > 0`, `0 < δ ≤ 1`), put `T = λ|t|`,
`b = Tδ`, `r_b = log(1/ε)/log(e + log(1/ε)/b)` (`r_0 = 0`) and let `0 < ε ≤ 1/64`. One unitary
program over the factor query and its adjoint, on a known isometric encoding, fixed before `U_B`,
has full-output error at most `ε` (also with an untouched reference) and uses
`O(√(Tb) + √(T r_b) + r_b)` factor queries (eq. `opt:eq:signed-bound`), with no query if `b ≤ ε`;
the absolute constant is `4·10¹⁰`. Formal restrictions: none. -/
theorem opt_thm_signed :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P : Type u} {W : Type v}
        [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P] [FiniteDimensional ℂ P]
        [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] [FiniteDimensional ℂ W]
        (E : P →L[ℂ] W) (Pi Z : W →L[ℂ] W),
        E† ∘L E = 1 → Pi† = Pi → Pi ∘L Pi = Pi →
        (Pi ∘L Z ∘L Pi)† = Pi ∘L Z ∘L Pi → (Pi ∘L Z ∘L Pi) ∘L (Pi ∘L Z ∘L Pi) = Pi →
        ∀ {X : Type w} (U : X → W →L[ℂ] W), (∀ x, IsUnitary (U x)) →
        ∀ lam δ t ε : ℝ, 0 < lam → 0 < δ → δ ≤ 1 → 0 < ε → ε ≤ 1 / 64 →
        (∀ x, (Pi ∘L U x ∘L E)† ∘L (Pi ∘L U x ∘L E) ≤ (δ : ℂ) • (1 : P →L[ℂ] P)) →
        ∃ (ι : Type) (_ : Fintype ι) (J : P →L[ℂ] PiLp 2 (fun _ : ι => W))
          (p : Program (fun x => WeightedClock.diagonal (fun _ : ι => U x))),
          J† ∘L J = 1 ∧
          (p.count : ℝ) ≤ C * signedBound (lam * |t|) (lam * |t| * δ) ε ∧
          (lam * |t| * δ ≤ ε → p.count = 0) ∧
          ∀ x, IsUnitary (p.eval x) ∧
            FullOutputError (p.eval x) J (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              ((lam : ℂ) • ((Pi ∘L U x ∘L E)† ∘L Z ∘L (Pi ∘L U x ∘L E))))) ε ∧
            ∀ (R : Type) [Fintype R], ReferenceOutputError R (p.eval x) J
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                ((lam : ℂ) • ((Pi ∘L U x ∘L E)† ∘L Z ∘L (Pi ∘L U x ∘L E))))) ε := by
  refine ⟨4 * 10 ^ 10, by norm_num, ?_⟩
  intro P W _ _ _ _ _ _ _ _ E Pi Z hE hPi hPi2 hZh hZu X U hU lam δ t ε hlam hδ hδ1 hε hε1 hD
  set K := knownOf E Pi Z hE hPi hPi2 hZh hZu with hK
  obtain ⟨ι, hι, J, p, hJ, hc, herr⟩ :=
    SignedFactorSimulation.signed_factor_simulation K U hU hlam hδ hδ1 hD t hε hε1
  have hb0 : 0 ≤ lam * |t| * δ := by positivity
  have hO : ∀ x, IsUnitary (WeightedClock.diagonal (fun _ : ι => U x)) :=
    fun x => SignedFactorSimulation.diagonal_unitary_const ι (hU x)
  have hH : ∀ x, K.ham lam (U x) =
      (lam : ℂ) • ((Pi ∘L U x ∘L E)† ∘L Z ∘L (Pi ∘L U x ∘L E)) := by
    intro x
    rw [SignedFactorSimulation.Known.ham, hK, knownOf_Cop]
  refine ⟨ι, hι, J, p, hJ, ?_, ?_, fun x => ⟨p.eval_unitary hO x, ?_, ?_⟩⟩
  · by_cases hs : lam * |t| * δ ≤ ε
    · rw [if_pos hs] at hc
      exact hc.trans (mul_nonneg (by norm_num) (signedBound_nonneg hb0 hε (by linarith)))
    · rw [if_neg hs] at hc
      have hb : lam * |t| * δ ≠ 0 := by
        intro h0; rw [h0] at hs; exact hs hε.le
      rw [rb_eq_signedR hb] at hc
      exact hc
  · intro hs
    rw [if_pos hs] at hc
    exact_mod_cast le_antisymm hc (Nat.cast_nonneg _)
  · rw [← hH x]; exact fullOutputError_of_norm (herr x)
  · intro R _
    rw [← hH x]; exact referenceOutputError_of_norm (herr x) R

/-- **Theorem `opt:thm:signed`, the identity case** ("If `t = 0` or `b ≤ ε`, the identity
suffices"): under the factor assumptions, if `b = λ|t|δ ≤ ε` (in particular if `t = 0`), the
identity circuit has full-output error at most `ε` on every isometric encoding. -/
theorem opt_thm_signed_identity {K' : Type*} [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
    [CompleteSpace K'] (E : P →L[ℂ] W) (Pi Z : W →L[ℂ] W) (hE : E† ∘L E = 1) (hPi : Pi† = Pi)
    (hPi2 : Pi ∘L Pi = Pi) (hZh : (Pi ∘L Z ∘L Pi)† = Pi ∘L Z ∘L Pi)
    (hZu : (Pi ∘L Z ∘L Pi) ∘L (Pi ∘L Z ∘L Pi) = Pi) (U : W →L[ℂ] W) {lam δ t ε : ℝ}
    (hlam : 0 < lam) (hδ : 0 < δ)
    (hD : (Pi ∘L U ∘L E)† ∘L (Pi ∘L U ∘L E) ≤ (δ : ℂ) • (1 : P →L[ℂ] P))
    (hsmall : lam * |t| * δ ≤ ε) (J : P →L[ℂ] K') (hJ : J† ∘L J = 1) :
    FullOutputError (1 : K' →L[ℂ] K') J (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
      ((lam : ℂ) • ((Pi ∘L U ∘L E)† ∘L Z ∘L (Pi ∘L U ∘L E))))) ε := by
  set K := knownOf E Pi Z hE hPi hPi2 hZh hZu with hK
  have hH : K.ham lam U = (lam : ℂ) • ((Pi ∘L U ∘L E)† ∘L Z ∘L (Pi ∘L U ∘L E)) := by
    rw [SignedFactorSimulation.Known.ham, hK, knownOf_Cop]
  rw [← hH]
  apply fullOutputError_of_norm
  set V := NormedSpace.exp ((-Complex.I * (t : ℂ)) • K.ham lam U)
  have h1 : (1 : K' →L[ℂ] K') ∘L J - J ∘L V = J ∘L (1 - V) := by
    rw [comp_sub, show (1 : K' →L[ℂ] K') ∘L J = J from ContinuousLinearMap.id_comp J,
      show J ∘L (1 : P →L[ℂ] P) = J from ContinuousLinearMap.comp_id J]
  rw [h1, EncodedOracle.norm_comp_eq J hJ, norm_sub_rev]
  calc ‖V - 1‖ ≤ |t| * ‖K.ham lam U‖ :=
        SignedFactorSimulation.norm_evolution_sub_one_le _ (K.ham_star lam U) t
    _ ≤ |t| * (lam * δ) :=
        mul_le_mul_of_nonneg_left (K.norm_ham_le hlam.le hδ.le U hD) (abs_nonneg t)
    _ = lam * |t| * δ := by ring
    _ ≤ ε := hsmall

end Signed

/-! ### Theorem `opt:thm:weights` -/

/-- `ξ(w) = (1 - w)/(1 + w)` (eq. `opt:eq:xi-R`). -/
theorem xi_eq (w : ℂ) : OptimalPrecision.xi w = (1 - w) / (1 + w) := rfl

/-- `R(w) = (1 - ξ(w)²)/(1 + q² ξ(w)²)` (eq. `opt:eq:xi-R`). -/
theorem Rfun_eq (q : ℝ) (w : ℂ) :
    OptimalPrecision.Rfun q w =
      (1 - OptimalPrecision.xi w ^ 2) / (1 + (q : ℂ) ^ 2 * OptimalPrecision.xi w ^ 2) := rfl

/-- `Ces_n(f) = ∑_{r<n} (1 - r/n) [w^r] f` (eq. `opt:eq:cesaro`), with the Taylor coefficient
`[w^r] f = f^{(r)}(0)/r!`. -/
theorem ces_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E) (n : ℕ) :
    OptimalPrecision.ces f n =
      ∑ r ∈ Finset.range n, ((1 : ℂ) - (r : ℂ) / (n : ℂ)) •
        (((Nat.factorial r : ℂ))⁻¹ • iteratedDeriv r f 0) := rfl

/-- **Theorem `opt:thm:weights`: bounded finite moment-cancelling weights.**
For every real `q ≥ 1` and integer `M ≥ 1`, with `a = qM` and `V(w) = e^{-a ξ(w)}`, there are real
numbers `λ_1, …, λ_n`, depending only on `q` and `M`, with `n ≤ 27a`, `∑ |λ_j| ≤ 3000`
(eq. `opt:eq:clock-size`) and `∑_j λ_j Ces_j(V R^k ξ^m) = δ_{m0}` for `0 ≤ m ≤ k < M`
(eq. `opt:eq:clock-moments`); `ξ`, `R` and `Ces_j` as in `xi_eq`, `Rfun_eq`, `ces_eq`. Formal
restrictions: none. -/
theorem opt_thm_weights (q : ℝ) (hq : 1 ≤ q) (M : ℕ) (hM : 1 ≤ M) :
    ∃ (n : ℕ) (lam : ℕ → ℝ), (n : ℝ) ≤ 27 * (q * M) ∧ ∑ j ∈ Finset.Icc 1 n, |lam j| ≤ 3000 ∧
      ∀ k m : ℕ, m ≤ k → k < M →
        ∑ j ∈ Finset.Icc 1 n, (lam j : ℂ) *
            OptimalPrecision.ces (fun w => Complex.exp (-(((q * M : ℝ) : ℂ) *
              OptimalPrecision.xi w)) * OptimalPrecision.Rfun q w ^ k *
                OptimalPrecision.xi w ^ m) j =
          if m = 0 then 1 else 0 :=
  OptimalPrecision.exists_clock_weights q hq M hM

/-! ### Proposition `opt:prop:core` -/

set_option maxHeartbeats 1000000 in
/-- **Proposition `opt:prop:core`: the large-sparsity construction.** In the
setting of Appendix `opt:sec:proof` (the sparse access and row and column norm promises of
`hs:thm:main`, `τ = η|t| ≥ 1` and `0 < ε ≤ 1/64`), with `L = log(1/ε)`, `h = log(e + L/τ)` and
`r = L/h`: for `h` at least an absolute constant `h₀` and `sτ ≥ Lh`
(eq. `opt:eq:core-regime`), one unitary program over the original native sparse primitives (with
spectators), on a known isometric encoding, fixed before the instance, has full-output error at most
`ε` (also with an untouched reference) and uses `O(√(sτr))` queries; `h₀ = 10⁴` and the absolute
constant is `6972480`. Formal restrictions: none. -/
theorem opt_prop_core :
    ∃ h₀ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n Z : Type v} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
        [DecidableEq Z] {s : ℕ} (D : Data X n Z s) (η t ε : ℝ),
        0 < η → 1 ≤ η * |t| → 0 < ε → ε ≤ 1 / 64 →
        h₀ ≤ hRatio (η * |t|) ε → logInv ε * hRatio (η * |t|) ε ≤ s * (η * |t|) →
        (∀ x, (D.matrix x).IsHermitian) →
        (∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
        (∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
        ∃ (T d : ℕ) (J : EuclideanSpace ℂ n →L[ℂ] NativeCayleyActive.Physical n Z T d)
          (p : MultiOracleCircuit.Program (NativeCayleyActive.oracle D T d)),
          J† ∘L J = 1 ∧ (p.count : ℝ) ≤ C * Real.sqrt (s * (η * |t|) * hslR (η * |t|) ε) ∧
          ∀ x, IsUnitary (p.eval x) ∧
            FullOutputError (p.eval x) J (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))) ε ∧
            ∀ (R : Type) [Fintype R], ReferenceOutputError R (p.eval x) J
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                SparseStateOverlap.matrixOperator (D.matrix x))) ε := by
  refine ⟨10 ^ 4, 6972480, by norm_num, ?_⟩
  intro X n Z _ _ _ _ _ s D η t ε hη hτ hε hε1 hh hcore hH hrow hcol
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast D.slots_pos
  have R : LargeSparsityCore.Parameters.Regime s (η * |t|) ε :=
    ⟨hs1, hτ, hε, hε1, hh, hcore⟩
  obtain ⟨hJ, p, hc, hp⟩ :=
    LargeSparsityCore.Native.core_simulation D hη R hH (fun x => ⟨hrow x, hcol x⟩)
  exact ⟨_, _, _, p, hJ, hc, fun x => ⟨(hp x).1, fullOutputError_of_norm (hp x).2,
    referenceOutputError_of_norm (hp x).2⟩⟩

end

end ManuscriptConformance
