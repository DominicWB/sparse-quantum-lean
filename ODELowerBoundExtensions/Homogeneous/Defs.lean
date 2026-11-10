import ODELowerBoundExtensions.Homogeneous.Parameters

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

/-!
# Proposition `odel:rem:homogeneous`: the source-free joint family

Manuscript: Proposition `odel:rem:homogeneous`. The joint family of Theorem `odel:thm:joint`
(`SparseLowerBounds.ODE.JointInstance`) with its source replaced by a flag
qubit, known pulses and a known dissipative stage.

**Index.** `HomIndex M μ s = Bool × JointIndex M μ s`: the flag qubit (first component,
`true` is flag one) times the joint index `(Fin M × Bool × Fin 2^μ) ⊕ Fin s` (candidate, dilation
sector, gadget position; zero padding).

**Stages** (`n + 4` stages, generator `G = -A`, `ẋ = -G x`, no source):

* `k < n` (length `π/2`): `G = i (|1⟩⟨1| ⊗ H_k)` with `H_k = ⊕_a S_{j_{ak}}` the joint stage
  Hamiltonian `stageHam` (eq. `odel:eq:stages` "only on flag one", Proposition
  `odel:rem:homogeneous`);
* `k = n` (length `pulseLen n = ((n+2) mod 4)π/2`): `G = i(-|1⟩⟨1| ⊗ 1)`, the phase pulse of
  the proof merged with the `Z` pulse (`e^{-iπZ/2} = -i e^{iπ|1⟩⟨1|}`);
* `k = n + 1` (length `π/4`): `G = i(Y ⊗ 1)`; with the merged pulse it implements the Hadamard
  `e^{-iπY/4} e^{iπ|1⟩⟨1|} = (1/√2)[[1,1],[1,-1]]` on the flag (Proposition `odel:rem:homogeneous`;
  the merge is a formalization choice, explained in
  `ODELowerBoundExtensions.Homogeneous.Parameters`);
* `k = n + 2` (length `d = log(4√M)`): the dissipative generator `G = P_reject = |0⟩⟨0| ⊗ 1`
  (`A = -P_reject`, Proposition `odel:rem:homogeneous`);
* `k = n + 3` (length `T - homBusy M n`): known idle stage `G = 0` (Proposition
  `odel:rem:homogeneous`).

All pulses act on the whole joint index (`P ⊗ 1`), padding included. Start
`x₀ = |+⟩ ⊗ u_M ⊗ ω` (`homInit`).

**Solution** (`homSol`), closed form with the clamped ramps of
`SparseLowerBounds.Helpers.Ode.JointFamily.Solution`: every candidate stays in the span of
`flagCand false a = |0, a, ω⟩` and `flagCand true a = |1, a, ω⟩`, with coefficients
`(2M)^{-1/2} (α_a(t), β_a(t))`:
`β` acquires the hidden phase `e^{-iΦ_a(t)}` (`candPhase`) and the pulse phase
`e^{i clamp}` (`phaseCoeff`), the `Y` pulse rotates `(α, β)` by the angle `θ(t) ∈ [0, π/4]`
(`yAngle`; `α' = -β`, `β' = α`), and the dissipation multiplies `α` by `e^{-clamp}`
(`dampTime`). At the end every even candidate has flag zero with weight `e^{-d} = 1/(4√M)` and
the odd candidate `a_*` has flag one (`homEnd`). `homHalfObs` reads the half of the candidate
register (Proposition `odel:rem:homogeneous`).
-/

namespace ODELowerBoundExtensions.Homogeneous

noncomputable section
open SparseLowerBounds SparseLowerBounds.ODE SparseHamiltonian
open scoped InnerProductSpace

/-- **The index** of the homogeneous variant: flag qubit ⊗ joint index (Proposition
`odel:rem:homogeneous`). -/
abbrev HomIndex (M μ s : ℕ) : Type := Bool × JointIndex M μ s

variable {M n μ s : ℕ}

/-! ### The stage Hamiltonians and generators -/

/-- **The flag-controlled stage Hamiltonian** `|1⟩⟨1| ⊗ H_k` (Proposition
`odel:rem:homogeneous`). -/
def flagHam (j : Positions M n (2 ^ μ)) (k : Fin n) :
    Matrix (HomIndex M μ s) (HomIndex M μ s) ℂ :=
  Matrix.of fun i i' => if i.1 = true ∧ i'.1 = true then stageHam (s := s) j k i.2 i'.2 else 0

variable (M μ s) in
/-- **The phase pulse Hamiltonian** `-|1⟩⟨1| ⊗ 1` (Proposition `odel:rem:homogeneous`). -/
def pulseHam : Matrix (HomIndex M μ s) (HomIndex M μ s) ℂ :=
  Matrix.diagonal fun i => if i.1 = true then -1 else 0

variable (M μ s) in
/-- **The Pauli `Y` pulse Hamiltonian** `Y ⊗ 1`, `Y = [[0, -i], [i, 0]]` (Proposition
`odel:rem:homogeneous`). -/
def yHam : Matrix (HomIndex M μ s) (HomIndex M μ s) ℂ :=
  Matrix.of fun i i' =>
    if i.2 = i'.2 ∧ i.1 ≠ i'.1 then (if i.1 = true then Complex.I else -Complex.I) else 0

variable (M μ s) in
/-- **The rejection projection** `P_reject = |0⟩⟨0| ⊗ 1` (Proposition `odel:rem:homogeneous`). -/
def rejectProj : Matrix (HomIndex M μ s) (HomIndex M μ s) ℂ :=
  Matrix.diagonal fun i => if i.1 = true then 0 else 1

/-- **The stage Hamiltonian** of stage `k` (Hermitian part `H` of `-A = D + iH`): `flagHam` on
the hidden stages `k < n`, `pulseHam` at `k = n`, `yHam` at `k = n + 1`, `0` on the dissipative
stage `n + 2` and the idle stage `n + 3`. -/
def homHam (j : Positions M n (2 ^ μ)) (k : Fin (n + 4)) :
    Matrix (HomIndex M μ s) (HomIndex M μ s) ℂ :=
  if hk : (k : ℕ) < n then flagHam j ⟨k, hk⟩
  else if (k : ℕ) = n then pulseHam M μ s
  else if (k : ℕ) = n + 1 then yHam M μ s
  else 0

/-- **The generator** `G_k = -A_k` of stage `k`: `P_reject` on the dissipative stage `n + 2`
(`D = P_reject`, `H = 0`), `i H_k` (`D = 0`) on every other stage. -/
def homGen (j : Positions M n (2 ^ μ)) (k : Fin (n + 4)) :
    Matrix (HomIndex M μ s) (HomIndex M μ s) ℂ :=
  if (k : ℕ) = n + 2 then rejectProj M μ s else Complex.I • homHam j k

/-- **The stage durations** (Proposition `odel:rem:homogeneous`): `π/2` (hidden), `pulseLen n`
(merged phase pulse), `π/4` (`Y`), `d` (dissipation), `T - homBusy M n` (idle). -/
def homLen (M n : ℕ) (T : ℝ) (k : Fin (n + 4)) : ℝ :=
  if (k : ℕ) < n then Real.pi / 2
  else if (k : ℕ) = n then pulseLen n
  else if (k : ℕ) = n + 1 then Real.pi / 4
  else if (k : ℕ) = n + 2 then homD M
  else T - homBusy M n

/-! ### States -/

/-- `|f, a, ω⟩ = |f⟩ ⊗ |a, ω⟩` (flag `f`, candidate `a`; `candState` of the joint family). -/
def flagCand (M μ s : ℕ) (f : Bool) (a : Fin M) : EuclideanSpace ℂ (HomIndex M μ s) :=
  WithLp.toLp 2 fun i => if i.1 = f then candState M μ s a i.2 else 0

/-- The entries of `|f, a, ω⟩`. -/
theorem flagCand_apply (f : Bool) (a : Fin M) (i : HomIndex M μ s) :
    flagCand M μ s f a i = if i.1 = f then candState M μ s a i.2 else 0 := rfl

/-- **The initial state** `x₀ = |+⟩ ⊗ u_M ⊗ ω = (2M)^{-1/2} Σ_a (|0,a,ω⟩ + |1,a,ω⟩)`
(Proposition `odel:rem:homogeneous`, with `x₀ = u_M ⊗ ω` of Section `odel:sec:main`). -/
def homInit (M μ s : ℕ) : EuclideanSpace ℂ (HomIndex M μ s) :=
  ((Real.sqrt (2 * (M : ℝ)) : ℂ))⁻¹ • ∑ a, (flagCand M μ s false a + flagCand M μ s true a)

/-- The flag-one coefficient after the hidden stages and the merged pulse:
`e^{-iΦ_a(t)} e^{i clamp(t - nπ/2, 0, pulseLen n)}`. -/
def phaseCoeff (j : Positions M n (2 ^ μ)) (a : Fin M) (t : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (candPhase j a t : ℂ)) *
    Complex.exp (Complex.I * ((min (max (t - n * (Real.pi / 2)) 0) (pulseLen n) : ℝ) : ℂ))

/-- The rotation angle of the `Y` pulse: `clamp(t - (nπ/2 + pulseLen n), 0, π/4)`. -/
def yAngle (n : ℕ) (t : ℝ) : ℝ :=
  min (max (t - (n * (Real.pi / 2) + pulseLen n)) 0) (Real.pi / 4)

/-- The elapsed dissipation time: `clamp(t - (nπ/2 + pulseLen n + π/4), 0, d)`. -/
def dampTime (M n : ℕ) (t : ℝ) : ℝ :=
  min (max (t - (n * (Real.pi / 2) + pulseLen n + Real.pi / 4)) 0) (homD M)

/-- The flag-zero coefficient `α_a(t) = e^{-clamp} (cos θ - sin θ · phaseCoeff)`. -/
def homAlpha (j : Positions M n (2 ^ μ)) (a : Fin M) (t : ℝ) : ℂ :=
  (Real.exp (-dampTime M n t) : ℂ) *
    ((Real.cos (yAngle n t) : ℂ) - (Real.sin (yAngle n t) : ℂ) * phaseCoeff j a t)

/-- The flag-one coefficient `β_a(t) = sin θ + cos θ · phaseCoeff`. -/
def homBeta (j : Positions M n (2 ^ μ)) (a : Fin M) (t : ℝ) : ℂ :=
  (Real.sin (yAngle n t) : ℂ) + (Real.cos (yAngle n t) : ℂ) * phaseCoeff j a t

/-- **The explicit solution**
`x(t) = (2M)^{-1/2} Σ_a (α_a(t) |0, a, ω⟩ + β_a(t) |1, a, ω⟩)`. -/
def homSol (M n μ s : ℕ) (x : Promised M n (2 ^ μ)) (t : ℝ) : EuclideanSpace ℂ (HomIndex M μ s) :=
  ((Real.sqrt (2 * (M : ℝ)) : ℂ))⁻¹ •
    ∑ a, (homAlpha x.1 a t • flagCand M μ s false a + homBeta x.1 a t • flagCand M μ s true a)

/-- **The final state** for odd candidate `b`:
`x(T) = M^{-1/2} (e^{-d} Σ_{a ≠ b} |0, a, ω⟩ + |1, b, ω⟩)` with `e^{-d} = 1/(4√M)`
(Proposition `odel:rem:homogeneous`). -/
def homEnd (M μ s : ℕ) (b : Fin M) : EuclideanSpace ℂ (HomIndex M μ s) :=
  ((Real.sqrt M : ℂ))⁻¹ •
    ((((4 * Real.sqrt M)⁻¹ : ℝ) : ℂ) • ∑ a ∈ Finset.univ.erase b, flagCand M μ s false a +
      flagCand M μ s true b)

/-- **The half indicator** `1 ⊗ Σ_a halfSign(a) |a⟩⟨a| ⊗ 1` (padding `0`): measure the candidate
register and answer its half, whatever the flag (Proposition `odel:rem:homogeneous` and proof of
Theorem `odel:thm:joint`). -/
def homHalfObs (M μ s : ℕ) :
    EuclideanSpace ℂ (HomIndex M μ s) →L[ℂ] EuclideanSpace ℂ (HomIndex M μ s) :=
  SparseStateOverlap.matrixOperator (Matrix.diagonal fun i : HomIndex M μ s => match i.2 with
    | Sum.inl (a, _, _) => (halfSign M a : ℂ)
    | Sum.inr _ => 0)

end

end ODELowerBoundExtensions.Homogeneous
