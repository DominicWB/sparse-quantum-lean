import GateOptimalBinary.Bounded
import GateOptimalBinary.SignedNative
import GateOptimalBinary.ClipNative
import GateEfficientSynthesis.Hamiltonian

/-!
# Theorem `gate:thm:main` from binary sparse oracles

The three regimes of Theorem `gate:thm:main` (gate-efficient improved-precision simulation) with
every interface and every native identity built from the binary sparse oracles of
`GateEfficientBinary` (`k`-bit indices, `s = 2^{s_b}` slots enumerated by the low words, entries
stored as `b`-bit two's complement components with decoder `c₀(X + iY)`):

* bounded regime: `boundedIface` and `boundedNative`, with the CORDIC angle arithmetic of
  `GateBinary.binArith` at accuracy `ζ` (constructed; its counts give `bdNativeCost_le`);
* signed-factor regime: `signedIface` and `signedNative`, with the factor arithmetic as the
  hypothesis `FactorWordArith` at accuracy `ξ`;
* clipped regime: `clippedIface` and `clipNative`, with the factor and angle arithmetic as the
  hypotheses `ClipFactorArith` at accuracy `ξ` and `ClipAngleArith` at accuracy `ζ`.

The arithmetic hypotheses of the signed and clipped regimes are required only in their own regime.
They are supplied circuits: their lengths and word sizes enter `sgNativeCost` and `clNativeCost` as
given, so the manuscript's assumption that the scalar arithmetic has polynomially many gates in
`b`, `k` and the logarithm of the inverse accuracy is part of the hypothesis there.

**The binary endpoint** (`gate_optimal_binary`): for a binary sparse input (`BinaryInput`) and
the parameters of the theorem (`MainParams`), the native circuit of the regime selected by
`(h, σθ)` satisfies `GateOptimalPrecision.NativeClaims` with the sparse oracles as primitives:

* per private call, `2` (bounded, signed) or `6` (clipped) copies of the compute circuit
  `computeV` (`2` row, `2` column and `1` value calls, `computeV_nCalls`; `5` in total,
  `computeV_calls_total`), that is `10` or `30` primitive calls, independent of `t` and `ε`;
* the per-call gate cost `G` (`bdNativeCost`, `sgNativeCost`, `clNativeCost`): the gates of one
  native boundary call (`7` for each gate of the boundary circuit) and of one native private call
  (`28 k` gates per compute circuit, the arithmetic circuits and `O(b_T + b_P)` rotation gates);
* the scratch register `SZ k b` of `6k + 2b` qubits (`card_SZ`) and the arithmetic wires;
* full-output error `ε + 2·10¹¹ Q_μ ζ'` with `ζ' = 4ζ`, `3ξ` or `6ξ + 4ζ`.

`gate_optimal_binary_total` has total error `ε` under `8·10¹¹ Q_μ (6ξ + 4ζ) ≤ ε`.

**Finite gate sets** (`synthClaims_of_native`, `gate_optimal_binary_synth`): under the synthesis
hypothesis `GateSynth.Synthesis 𝒢 X_a L` (every one-qubit unitary with at most three controls is
approximated within every `ζ > 0` by at most `L ζ` gates of the finite set `𝒢`; by
`GateSynth.Synthesis.of_parts` it follows from single-qubit synthesis, the external result, which is
not reproved, and an exact decomposition of the controlled gates), the synthesis budget `ε'` of
`GateSynth.synthBudget` gives a circuit of gates of `𝒢` and the same primitive calls, with at most
`N L(ε'/(N+1))` gates (`N` the gates of the native circuit), `|X_a|` more qubits, and full-output
error `δ + ε'` (`SynthClaims`). If `L ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]`, `SynthClaims.gates_log`
bounds the gates by `G_N (c₁ log((G_N + 1)/ε') + c₀)`, with `G_N` the native gate bound of
`NativeClaims`: the finite-gate-set form of `gate:eq:main-gates`.

References to the manuscript use its labels.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace GateOptimalBinary

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary SparseHamiltonian.GateSynth GateOptimalPrecision
open NativeSparseBlockEncoding (Data Query)
open LargeSparsityCore.Parameters (hval qval Lval Regime)
open Complex (I)
open scoped InnerProduct Matrix

/-! ### Synthesis over a finite gate set -/

section Synth

variable {S Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Y] [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The conclusions of Theorem `gate:thm:main` over a finite gate set** for a circuit `C` on the
wires of a released circuit with `a` ancilla qubits, `2^m` slots and `2^r` labels, and the
synthesis ancillas `X_a`: valid; every elementary gate a gate of `𝒢`; at most `2·10¹¹ Q` times
`calls p` primitive calls of kind `p`; at most `N L(ε'/(N+1))` gates for the gates `N` of a native
circuit with at most `10¹³ (Q + 1)(a + m + r + 1) + 2·10¹¹ Q G` gates; the native wires and `|X_a|`;
full-output error `δ` with every ancilla clean. -/
structure SynthClaims (prim : J → Reg Y R →L[ℂ] Reg Y R) {Z : Type*} [Fintype Z] [DecidableEq Z]
    {a m r K bT bP A : ℕ} (𝒢 : Set Kind) (Xa : Type*) [Fintype Xa] [DecidableEq Xa] (L : ℝ → ℕ)
    (ε' : ℝ) (C : List (NInstr (HW (Wire a m r K) S Empty Z bT bP A ⊕ Xa) Y J))
    (H : Reg S R →L[ℂ] Reg S R) (t ε Q : ℝ) (calls : (J → Bool) → ℕ) (N G : ℕ) (δ : ℝ) :
    Prop where
  valid : ∀ i ∈ C, i.Valid
  gateset : ∀ g, NInstr.gate g ∈ C → GateOf 𝒢 g
  calls_le : ∀ p : J → Bool, (nCallsN p C : ℝ) ≤ 2 * 10 ^ 11 * Q * calls p
  gates : nGatesN C ≤ N * L (ε' / (N + 1))
  native_gates : (N : ℝ) ≤ 10 ^ 13 * (Q + 1) * (a + m + r + 1) + 2 * 10 ^ 11 * Q * G
  wires : Fintype.card (HW (Wire a m r K) S Empty Z bT bP A ⊕ Xa) ≤
    2 * a + 3 * m + 6 * r + 5 + Fintype.card S + (Fintype.card Z + bT + bP + A + 3) +
      Fintype.card Xa
  mesh : ((2 ^ m : ℕ) : ℝ) ≤ 10 ^ 36 * (Q + 1) ^ 4 / ε
  labels : ((2 ^ r : ℕ) : ℝ) ≤ 10 ^ 8 * (Q + 1)
  error : ‖nrun prim C ∘L (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg S R))) -
    (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L NormedSpace.exp ((-I * (t : ℂ)) • H)‖ ≤ δ

/-- **Synthesis of a native circuit with the claims of Theorem `gate:thm:main`** over a finite gate
set, with the synthesis budget `ε'` (`GateSynth.synthBudget`). -/
theorem synthClaims_of_native {prim : J → Reg Y R →L[ℂ] Reg Y R} (hprim : ∀ j, IsUnitary (prim j))
    {Z : Type*} [Fintype Z] [DecidableEq Z] {a m r K bT bP A : ℕ}
    {C : List (NInstr (HW (Wire a m r K) S Empty Z bT bP A) Y J)} {H : Reg S R →L[ℂ] Reg S R}
    {t ε Q : ℝ} {calls : (J → Bool) → ℕ} {G : ℕ} {δ : ℝ}
    (h : NativeClaims prim C H t ε Q calls G δ) {𝒢 : Set Kind} {Xa : Type*} [Fintype Xa]
    [DecidableEq Xa] {L : ℝ → ℕ} (hS : Synthesis 𝒢 Xa L) {ε' : ℝ} (hε' : 0 < ε') :
    SynthClaims prim 𝒢 Xa L ε' (synthBudget hS ε' C) H t ε Q calls (nGatesN C) G (δ + ε') := by
  obtain ⟨hv, hk, hg, hc⟩ := synthBudget_spec hS hε' C h.valid
  refine ⟨hv, hk, fun p => ?_, hg, h.gates, ?_, h.mesh, h.labels, ?_⟩
  · rw [hc p]
    exact h.calls_le p
  · rw [Fintype.card_sum]
    have := h.wires
    omega
  · exact synthBudget_error hS hε' C h.valid prim hprim _
      (fun ψ => (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le) _ h.error

/-- **The gates over a finite gate set with a logarithmic synthesis length** (the finite-gate-set
form of `gate:eq:main-gates`): if `L ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]` and `ε' ≤ 1`, a circuit with
`SynthClaims` has at most `G_N (c₁ log((G_N + 1)/ε') + c₀)` gates, where
`G_N = 10¹³ (Q + 1)(a + m + r + 1) + 2·10¹¹ Q G` is the native gate bound
(`GateSynth.gates_log_le`). -/
theorem SynthClaims.gates_log {prim : J → Reg Y R →L[ℂ] Reg Y R} {Z : Type*} [Fintype Z]
    [DecidableEq Z] {a m r K bT bP A : ℕ} {𝒢 : Set Kind} {Xa : Type*} [Fintype Xa] [DecidableEq Xa]
    {L : ℝ → ℕ} {ε' : ℝ} {C : List (NInstr (HW (Wire a m r K) S Empty Z bT bP A ⊕ Xa) Y J)}
    {H : Reg S R →L[ℂ] Reg S R} {t ε Q : ℝ} {calls : (J → Bool) → ℕ} {N G : ℕ} {δ : ℝ}
    (h : SynthClaims prim 𝒢 Xa L ε' C H t ε Q calls N G δ) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (hε' : 0 < ε') (hε'1 : ε' ≤ 1) :
    (nGatesN C : ℝ) ≤ (10 ^ 13 * (Q + 1) * (a + m + r + 1) + 2 * 10 ^ 11 * Q * G) *
      (c₁ * Real.log ((10 ^ 13 * (Q + 1) * (a + m + r + 1) + 2 * 10 ^ 11 * Q * G + 1) / ε') +
        c₀) := by
  have h1 : (nGatesN C : ℝ) ≤ ((N * L (ε' / (N + 1)) : ℕ) : ℝ) := Nat.cast_le.mpr h.gates
  exact h1.trans (gates_log_le hc₀ hc₁ hL hε' hε'1 N _ h.native_gates)

end Synth

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-! ### The binary input and the parameters -/

/-- **A binary sparse input** of Theorem `gate:thm:main`: sparse access data `D` with `k`-bit
indices (`en`), `s = 2^{s_b}` slots enumerated by the low words (`hrange`), entries stored as
`b`-bit two's complement components with decoder `c₀(X + iY)` (`hdec`), and an input `x` whose
matrix is Hermitian with row and column Euclidean norms at most `η` and entries of modulus at most
`μ`. -/
structure BinaryInput (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ) (c0 : ℝ)
    (x : X) (η μ : ℝ) : Prop where
  hsb : sb ≤ k
  hs : s = 2 ^ sb
  hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u)
  hb : 0 < b
  hc0 : 0 < c0
  hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z
  herm : (D.matrix x).IsHermitian
  row : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2
  col : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2
  ent : ∀ i j, ‖D.matrix x i j‖ ≤ μ

/-- **The parameters of Theorem `gate:thm:main`**: `μ ≤ η ≤ √s μ`, `sμ² = ση²`, `θ = η²|t|/μ ≥ 1`
and `0 < ε ≤ 1/64`. -/
structure MainParams (s : ℕ) (η μ t ε σ θ : ℝ) : Prop where
  μη : μ ≤ η
  ηs : η ≤ Real.sqrt s * μ
  σdef : (s : ℝ) * μ ^ 2 = σ * η ^ 2
  θdef : θ = η ^ 2 * |t| / μ
  θ1 : 1 ≤ θ
  ε0 : 0 < ε
  ε1 : ε ≤ 1 / 64

namespace MainParams

variable {η μ t ε σ θ : ℝ}

theorem μ_pos (hP : MainParams s η μ t ε σ θ) : 0 < μ :=
  (two_norm_params hP.μη hP.ηs hP.σdef hP.θdef hP.θ1).1

theorem η_pos (hP : MainParams s η μ t ε σ θ) : 0 < η :=
  (two_norm_params hP.μη hP.ηs hP.σdef hP.θdef hP.θ1).2.1

theorem σ_one (hP : MainParams s η μ t ε σ θ) : 1 ≤ σ :=
  (two_norm_params hP.μη hP.ηs hP.σdef hP.θdef hP.θ1).2.2.2.1

end MainParams

theorem sysH_star (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (hH : (D.matrix x).IsHermitian) : star (sysH (R := R) D en x) = sysH (R := R) D en x := by
  rw [sysH, qlift, ← map_star, SparseValuePrecision.matrixOperator_star_eq _ hH]

/-- The slot of the all-zero index word. -/
def zeroSlot (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u)) :
    Fin s :=
  Classical.choose (exists_zero_slot D en sb hrange)

theorem zeroSlot_spec (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u)) :
    D.slot (zeroSlot D en sb hrange) = zIdx en :=
  Classical.choose_spec (exists_zero_slot D en sb hrange)

/-! ### The interfaces and the native data of the three regimes -/

section Families

variable {D : Data X n (Cfg (VW b)) s} {en : Cfg (Fin k) ≃ n} {sb : ℕ} {c0 : ℝ} {x : X}
  {η μ t ε σ θ : ℝ}

/-- The interface of the bounded regime. -/
def binIB (hI : BinaryInput D en sb c0 x η μ) (hP : MainParams s η μ t ε σ θ) :
    hval θ ε < 10 ^ 4 → BoundedIface (Reg (Fin k) R) σ (Real.sqrt s * η) (sysH (R := R) D en x) :=
  fun _ => boundedIface D en sb hI.hsb hI.hs hI.hrange hP.η_pos hP.μ_pos.le hP.σdef x hI.herm
    hI.row hI.col hI.ent

/-- The native data of the bounded regime, with the CORDIC arithmetic at accuracy `ζ`. -/
def binNB (hI : BinaryInput D en sb c0 x η μ) (hP : MainParams s η μ t ε σ θ) {ζ : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    ∀ hb : hval θ ε < 10 ^ 4, CayleyNative (prims (R := R) D en x) (binIB (R := R) hI hP hb).UJ
      (bdPriv (binIB (R := R) hI hP hb).K σ θ ε) (SZ k b) ζ :=
  fun _ => boundedNative D en sb hI.hsb hI.hs hI.hrange hI.hb hI.hc0 hI.hdec hP.η_pos
    hP.μ_pos.le hP.σdef hP.σ_one (by linarith [hP.θ1]) hP.ε0 (by linarith [hP.ε1]) hζ hζ1 x
    hI.herm hI.row hI.col hI.ent

/-- The interface of the signed-factor regime. -/
def binIS (hI : BinaryInput D en sb c0 x η μ) (hP : MainParams s η μ t ε σ θ) :
    10 ^ 4 ≤ hval θ ε → σ * θ < Lval ε * hval θ ε →
      SignedIface (Reg (Fin k) R) (s * μ) (Real.sqrt σ)⁻¹ (sysH (R := R) D en x) :=
  fun _ _ => signedIface D en sb hI.hsb hI.hs hI.hrange hP.η_pos hP.μ_pos hP.σdef x hI.herm
    hI.row hI.ent

/-- The native data of the signed-factor regime, with the factor arithmetic `ar`, supplied in this
regime only. -/
def binNS (hI : BinaryInput D en sb c0 x η μ) (hP : MainParams s η μ t ε σ θ) {ξ : ℝ}
    {bT bP A : ℕ}
    (ar : 10 ^ 4 ≤ hval θ ε → σ * θ < Lval ε * hval θ ε → FactorWordArith b (c0 / μ) ξ bT bP A) :
    ∀ (h1 : 10 ^ 4 ≤ hval θ ε) (h2 : σ * θ < Lval ε * hval θ ε),
      FactorNative (prims (R := R) D en x) (binIS (R := R) hI hP h1 h2).UJ
        (binIS (R := R) hI hP h1 h2).U (SZ k b) bT bP A ξ :=
  fun h1 h2 => signedNative D en sb hI.hsb hI.hs hI.hrange hP.η_pos hP.μ_pos hP.σdef x hI.herm
    hI.row hI.ent (zeroSlot D en sb hI.hrange) (zeroSlot_spec D en sb hI.hrange) c0 hI.hdec
    (ar h1 h2)

/-- The interface of the clipped regime. -/
def binIC (hI : BinaryInput D en sb c0 x η μ) (hP : MainParams s η μ t ε σ θ) :
    Regime σ θ ε → ClippedIface (Reg (Fin k) R) σ θ ε (s * μ / qval σ θ ε)
      (sysH (R := R) D en x) :=
  fun Rg => clippedIface D en sb hI.hsb hI.hs hI.hrange Rg hP.μ_pos hP.σdef x hI.herm hI.row
    hI.col hI.ent

/-- The native data of the clipped regime, with the factor arithmetic `af` and the angle
arithmetic `aa`, supplied in this regime only. -/
def binNC (hI : BinaryInput D en sb c0 x η μ) (hP : MainParams s η μ t ε σ θ) {ξ ζ : ℝ}
    {bT bP A : ℕ} (af : Regime σ θ ε → ClipFactorArith b μ (hval θ ε) c0 ξ bT bP A)
    (aa : Regime σ θ ε →
      ClipAngleArith b μ (hval θ ε) (qval σ θ ε) c0 ζ bT bP A) :
    ∀ Rg : Regime σ θ ε, ClipNative (prims (R := R) D en x) (binIC (R := R) hI hP Rg).UJ
      (binIC (R := R) hI hP Rg).D (SZ k b) bT bP A ξ ζ :=
  fun Rg => clipNative D en sb hI.hsb hI.hs hI.hrange Rg hP.μ_pos hP.σdef x hI.herm hI.row
    hI.col hI.ent hI.hdec (af Rg) (aa Rg)

end Families

/-! ### The native circuits -/

/-- **The native circuit of the bounded regime**: the boundary gates `hadUJ`, the compute circuit
`computeV` with the decoder `bdScale`, the CORDIC arithmetic and the released circuit
`bdSigned`. -/
def bdNativeCircuit (k b sb : ℕ) (hsb : sb ≤ k) (s : ℕ) (c0 η σ θ ε ζ t : ℝ) :=
  nativeOf (S := Fin k) (hadUJ k sb hsb) (sparseOp k b (bdScale s c0 η σ θ ε))
    (binArith k b (bdScale s c0 η σ θ ε) ζ) (bdSigned (k + 1) σ θ ε t)

/-- The gates of one native boundary call and one native private call of the bounded regime. -/
def bdNativeCost (k b sb s : ℕ) (c0 η σ θ ε ζ : ℝ) : ℕ :=
  7 * (sb + 1) + (2 * (28 * k) + 2 * (binArith k b (bdScale s c0 η σ θ ε) ζ).circ.length +
    (2 * (binArith k b (bdScale s c0 η σ θ ε) ζ).bP + (binArith k b (bdScale s c0 η σ θ ε) ζ).bT +
      1))

/-- **The native circuit of the signed-factor regime**: the boundary gates `sgUJg`, the native
factor `sgFO` and the released circuit `sgCircuit`. -/
def sgNativeCircuit (k b sb : ℕ) (hsb : sb ≤ k) (s : ℕ) (μ σ t ε c0 : ℝ) {ξ : ℝ} {bT bP A : ℕ}
    (ar : FactorWordArith b (c0 / μ) ξ bT bP A) :=
  factorNativeOf (S := Fin k) (sgUJg k sb hsb) (sgFO k b (c0 / μ) ar)
    (sgCircuit (k + 3) (fW k) (zW k) (s * μ) (Real.sqrt σ)⁻¹ t ε)

/-- The gates of one native boundary call and one native factor call of the signed regime. -/
def sgNativeCost (k sb : ℕ) {b : ℕ} {κ ξ : ℝ} {bT bP A : ℕ} (ar : FactorWordArith b κ ξ bT bP A) :
    ℕ :=
  7 * (sb + 1) + (2 * (28 * k) + 2 * ar.circ.length + (2 * bP + bT + 4))

/-- **The native private call of the clipped regime**: the native factor, the native rotation and
the literal inverse of the native factor. -/
def clipPC (k b : ℕ) {μ β q c0 ξ ζ : ℝ} {bT bP A : ℕ} (af : ClipFactorArith b μ β c0 ξ bT bP A)
    (aa : ClipAngleArith b μ β q c0 ζ bT bP A) :
    List (NInstr (PWr Empty (PRf k) (SZ k b) bT bP A) (PY k b) Query) :=
  factorMacro (clFO k b af) ++ privMacro (clND k b μ β q c0) (clAr k b aa) ++
    ninv (factorMacro (clFO k b af))

/-- **The native circuit of the clipped regime**: the boundary gates `clUJg`, the native private
call `clipPC` and the released circuit `clipSigned`. -/
def clNativeCircuit (k b sb : ℕ) (hsb : sb ≤ k) (σ θ ε t : ℝ) {μ β q c0 ξ ζ : ℝ} {bT bP A : ℕ}
    (af : ClipFactorArith b μ β c0 ξ bT bP A) (aa : ClipAngleArith b μ β q c0 ζ bT bP A) :=
  clipNativeOf (S := Fin k) (clUJg k sb hsb) (clipPC k b af aa) (clipSigned (k + 3 + 1) σ θ ε t)

/-- The gates of one native boundary call and one native private call of the clipped regime. -/
def clNativeCost (k sb : ℕ) {b : ℕ} {μ β q c0 ξ ζ : ℝ} {bT bP A : ℕ}
    (af : ClipFactorArith b μ β c0 ξ bT bP A) (aa : ClipAngleArith b μ β q c0 ζ bT bP A) : ℕ :=
  7 * (sb + 2) + (2 * (2 * (28 * k) + 2 * af.circ.length + (2 * bP + bT + 4)) +
    (2 * (28 * k) + 2 * aa.circ.length + (2 * bP + bT + 1)))

/-- **The primitive calls of one compute circuit**: `5` in total (`2` row, `2` column and `1`
value calls, `computeV_nCalls`). -/
theorem computeV_calls_total (k b : ℕ) : nCallsN (fun _ => true) (computeV k b) = 5 := by
  rw [computeV_nCalls]
  rfl

/-- The CORDIC parameters of the bounded regime, for the decoder scale `bdScale s c₀ η σ θ ε`. -/
abbrev bdParams (b s : ℕ) (c0 η σ θ ε ζ : ℝ) := Cordic.params b (bdScale s c0 η σ θ ε) ζ

/-- **The explicit gate cost of the bounded regime**: with the CORDIC parameters
`p = bdParams b s c₀ η σ θ ε ζ` (`p.w` the register width, `p.n` the steps per stage, `p.bT`,
`p.bP` the word lengths), one native boundary call and one native private call have at most
`7 (s_b + 1) + 56 k + 2 (156 p.w (p.n + 1) + p.bP + 2 p.bT) + (2 p.bP + p.bT + 1)` gates
(`GateBinary.cordicArith_counts`). -/
theorem bdNativeCost_le (k b sb s : ℕ) (c0 η σ θ ε ζ : ℝ) :
    bdNativeCost k b sb s c0 η σ θ ε ζ ≤ 7 * (sb + 1) + 56 * k +
      2 * (156 * (bdParams b s c0 η σ θ ε ζ).w * ((bdParams b s c0 η σ θ ε ζ).n + 1) +
        (bdParams b s c0 η σ θ ε ζ).bP + 2 * (bdParams b s c0 η σ θ ε ζ).bT) +
      (2 * (bdParams b s c0 η σ θ ε ζ).bP + (bdParams b s c0 η σ θ ε ζ).bT + 1) := by
  obtain ⟨hc, -, hT, hP⟩ := cordicArith_counts b (valX k b) (valY k b) (bdScale s c0 η σ θ ε) ζ
  unfold bdNativeCost binArith bdParams
  omega

/-! ### The binary endpoint -/

section Endpoint

variable {D : Data X n (Cfg (VW b)) s} {en : Cfg (Fin k) ≃ n} {sb : ℕ} {c0 : ℝ} {x : X}
  {η μ t ε σ θ : ℝ}

theorem binNB_calls (hI : BinaryInput D en sb c0 x η μ) (hP : MainParams s η μ t ε σ θ) {ζ : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hb : hval θ ε < 10 ^ 4) :
    (binNB (R := R) hI hP hζ hζ1 hb).calls = fun p => 2 * nCallsN p (computeV k b) := rfl

theorem binNB_cost (hI : BinaryInput D en sb c0 x η μ) (hP : MainParams s η μ t ε σ θ) {ζ : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hb : hval θ ε < 10 ^ 4) :
    (binNB (R := R) hI hP hζ hζ1 hb).cost = bdNativeCost k b sb s c0 η σ θ ε ζ := by
  change 7 * (hadUJ k sb hI.hsb).length + (2 * nGatesN (computeV k b) +
    2 * (binArith k b (bdScale s c0 η σ θ ε) ζ).circ.length +
    (2 * (binArith k b (bdScale s c0 η σ θ ε) ζ).bP +
      (binArith k b (bdScale s c0 η σ θ ε) ζ).bT + 1)) = _
  rw [hadUJ_length, computeV_nGates]
  rfl

theorem binNS_calls (hI : BinaryInput D en sb c0 x η μ) (hP : MainParams s η μ t ε σ θ) {ξ : ℝ}
    {bT bP A : ℕ}
    (ar : 10 ^ 4 ≤ hval θ ε → σ * θ < Lval ε * hval θ ε → FactorWordArith b (c0 / μ) ξ bT bP A)
    (h1 : 10 ^ 4 ≤ hval θ ε) (h2 : σ * θ < Lval ε * hval θ ε) :
    (binNS (R := R) hI hP ar h1 h2).calls = fun p => 2 * nCallsN p (computeV k b) := by
  funext p
  change 2 * nCallsN p ((computeV k b).map (NInstr.map (ιBe k b))) = _
  rw [nCallsN_map]

theorem binNS_cost (hI : BinaryInput D en sb c0 x η μ) (hP : MainParams s η μ t ε σ θ) {ξ : ℝ}
    {bT bP A : ℕ}
    (ar : 10 ^ 4 ≤ hval θ ε → σ * θ < Lval ε * hval θ ε → FactorWordArith b (c0 / μ) ξ bT bP A)
    (h1 : 10 ^ 4 ≤ hval θ ε) (h2 : σ * θ < Lval ε * hval θ ε) :
    (binNS (R := R) hI hP ar h1 h2).cost = sgNativeCost k sb (ar h1 h2) := by
  change 7 * (sgUJg k sb hI.hsb).length +
    (2 * nGatesN ((computeV k b).map (NInstr.map (ιBe k b))) +
      2 * ((ar h1 h2).circ.map (GateODE.Gate.map (Sum.map (vF k b) id))).length +
      (2 * bP + bT + 4)) = _
  rw [sgUJg_length, nGatesN_map, computeV_nGates, List.length_map]
  rfl

theorem binNC_calls (hI : BinaryInput D en sb c0 x η μ) (hP : MainParams s η μ t ε σ θ) {ξ ζ : ℝ}
    {bT bP A : ℕ} (af : Regime σ θ ε → ClipFactorArith b μ (hval θ ε) c0 ξ bT bP A)
    (aa : Regime σ θ ε →
      ClipAngleArith b μ (hval θ ε) (qval σ θ ε) c0 ζ bT bP A) (Rg : Regime σ θ ε) :
    (binNC (R := R) hI hP af aa Rg).calls = fun p => 6 * nCallsN p (computeV k b) := by
  funext p
  rw [ClipNative.calls_eq]
  change 4 * nCallsN p ((computeV k b).map (NInstr.map (ιBe k b))) +
    2 * nCallsN p ((computeV k b).map (NInstr.map (ιBe k b))) = _
  rw [nCallsN_map]
  ring

theorem binNC_cost (hI : BinaryInput D en sb c0 x η μ) (hP : MainParams s η μ t ε σ θ) {ξ ζ : ℝ}
    {bT bP A : ℕ} (af : Regime σ θ ε → ClipFactorArith b μ (hval θ ε) c0 ξ bT bP A)
    (aa : Regime σ θ ε →
      ClipAngleArith b μ (hval θ ε) (qval σ θ ε) c0 ζ bT bP A) (Rg : Regime σ θ ε) :
    (binNC (R := R) hI hP af aa Rg).cost = clNativeCost k sb (af Rg) (aa Rg) := by
  rw [ClipNative.cost, ClipNative.pc_nGates]
  change 7 * (clUJg k sb hI.hsb).length +
    (2 * (2 * nGatesN ((computeV k b).map (NInstr.map (ιBe k b))) +
      2 * ((af Rg).circ.map (GateODE.Gate.map (Sum.map (ιFin k b) id))).length +
      (2 * bP + bT + 4)) +
    (2 * nGatesN ((computeV k b).map (NInstr.map (ιBe k b))) +
      2 * ((aa Rg).circ.map (GateODE.Gate.map (Sum.map (ιCin k b) id))).length +
      (2 * bP + bT + 1))) = _
  rw [clUJg_length, nGatesN_map, computeV_nGates, List.length_map, List.length_map]
  rfl

/-- **Theorem `gate:thm:main` from binary sparse oracles, native form.** For a binary sparse
input, the parameters of the theorem and the CORDIC accuracy `0 < ζ ≤ 1`, and, as hypotheses each
required only in its own regime, the scalar arithmetic of the signed factor (`ar`) and of the
clipped factor and rotation (`af`, `aa`), the native circuit of the selected regime satisfies
`NativeClaims` with the sparse oracles as primitives: `2`, `2` or `6` compute circuits per private
call, the gate costs `bdNativeCost`, `sgNativeCost`, `clNativeCost`, and full-output error
`ε + 2·10¹¹ Q_μ ζ'` with `ζ' = 4ζ`, `3ξ`, `6ξ + 4ζ`. -/
theorem gate_optimal_binary [FiniteDimensional ℂ R] (hI : BinaryInput D en sb c0 x η μ)
    (hP : MainParams s η μ t ε σ θ) {ξ ζ : ℝ} (hξ : 0 ≤ ξ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    {bT bP A bT' bP' A' : ℕ}
    (ar : 10 ^ 4 ≤ hval θ ε → σ * θ < Lval ε * hval θ ε → FactorWordArith b (c0 / μ) ξ bT bP A)
    (af : Regime σ θ ε → ClipFactorArith b μ (hval θ ε) c0 ξ bT' bP' A')
    (aa : Regime σ θ ε → ClipAngleArith b μ (hval θ ε) (qval σ θ ε) c0 ζ bT' bP' A') :
    (hval θ ε < 10 ^ 4 ∧
      NativeClaims (prims (R := R) D en x) (bdNativeCircuit k b sb hI.hsb s c0 η σ θ ε ζ t)
        (sysH (R := R) D en x) t ε (Qmu s η μ t ε) (fun p => 2 * nCallsN p (computeV k b))
        (bdNativeCost k b sb s c0 η σ θ ε ζ) (ε + 2 * 10 ^ 11 * Qmu s η μ t ε * (4 * ζ))) ∨
    (∃ (h1 : 10 ^ 4 ≤ hval θ ε) (h2 : σ * θ < Lval ε * hval θ ε),
      NativeClaims (prims (R := R) D en x) (sgNativeCircuit k b sb hI.hsb s μ σ t ε c0 (ar h1 h2))
        (sysH (R := R) D en x) t ε (Qmu s η μ t ε) (fun p => 2 * nCallsN p (computeV k b))
        (sgNativeCost k sb (ar h1 h2)) (ε + 2 * 10 ^ 11 * Qmu s η μ t ε * (3 * ξ))) ∨
    (∃ Rg : Regime σ θ ε,
      NativeClaims (prims (R := R) D en x)
        (clNativeCircuit k b sb hI.hsb σ θ ε t (af Rg) (aa Rg)) (sysH (R := R) D en x) t ε
        (Qmu s η μ t ε) (fun p => 6 * nCallsN p (computeV k b))
        (clNativeCost k sb (af Rg) (aa Rg))
        (ε + 2 * 10 ^ 11 * Qmu s η μ t ε * (6 * ξ + 4 * ζ))) := by
  rcases gate_optimal_native_clip (prims (R := R) D en x) (prims_isUnitary D en x) hξ hζ.le
      hP.μη hP.ηs hP.σdef hP.θdef hP.θ1 hP.ε0 hP.ε1 (sysH_star D en x hI.herm)
      (binIB hI hP) (binNB hI hP hζ hζ1) (binIS hI hP) (binNS hI hP ar) (binIC hI hP)
      (binNC hI hP af aa) with ⟨hb, hN⟩ | ⟨h1, h2, hN⟩ | ⟨Rg, hN⟩
  · rw [binNB_calls, binNB_cost] at hN
    exact Or.inl ⟨hb, hN⟩
  · rw [binNS_calls, binNS_cost] at hN
    exact Or.inr (Or.inl ⟨h1, h2, hN⟩)
  · rw [binNC_calls, binNC_cost] at hN
    exact Or.inr (Or.inr ⟨Rg, hN⟩)

/-- **Theorem `gate:thm:main` from binary sparse oracles, native form, total error `ε`**: the
exact-gate construction at accuracy `ε/2` (the parameters `hP` at `ε/2`) and the arithmetic
accuracies `ξ`, `ζ` with `8·10¹¹ Q_μ (6ξ + 4ζ) ≤ ε` (`Q_μ` at `ε`); the native circuit of each
regime satisfies `NativeClaims` at `ε/2` with the count parameter `2 Q_μ` and full-output error
`ε`. The arithmetic hypotheses are required only in their own regimes. -/
theorem gate_optimal_binary_total [FiniteDimensional ℂ R] (hI : BinaryInput D en sb c0 x η μ)
    (hP : MainParams s η μ t (ε / 2) σ θ) {ξ ζ : ℝ} (hξ : 0 ≤ ξ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hδε : 8 * 10 ^ 11 * Qmu s η μ t ε * (6 * ξ + 4 * ζ) ≤ ε)
    {bT bP A bT' bP' A' : ℕ}
    (ar : 10 ^ 4 ≤ hval θ (ε / 2) → σ * θ < Lval (ε / 2) * hval θ (ε / 2) →
      FactorWordArith b (c0 / μ) ξ bT bP A)
    (af : Regime σ θ (ε / 2) → ClipFactorArith b μ (hval θ (ε / 2)) c0 ξ bT' bP' A')
    (aa : Regime σ θ (ε / 2) →
      ClipAngleArith b μ (hval θ (ε / 2)) (qval σ θ (ε / 2)) c0 ζ bT' bP' A') :
    (hval θ (ε / 2) < 10 ^ 4 ∧
      NativeClaims (prims (R := R) D en x)
        (bdNativeCircuit k b sb hI.hsb s c0 η σ θ (ε / 2) ζ t) (sysH (R := R) D en x) t (ε / 2)
        (2 * Qmu s η μ t ε) (fun p => 2 * nCallsN p (computeV k b))
        (bdNativeCost k b sb s c0 η σ θ (ε / 2) ζ) ε) ∨
    (∃ (h1 : 10 ^ 4 ≤ hval θ (ε / 2)) (h2 : σ * θ < Lval (ε / 2) * hval θ (ε / 2)),
      NativeClaims (prims (R := R) D en x)
        (sgNativeCircuit k b sb hI.hsb s μ σ t (ε / 2) c0 (ar h1 h2)) (sysH (R := R) D en x) t
        (ε / 2) (2 * Qmu s η μ t ε) (fun p => 2 * nCallsN p (computeV k b))
        (sgNativeCost k sb (ar h1 h2)) ε) ∨
    (∃ Rg : Regime σ θ (ε / 2),
      NativeClaims (prims (R := R) D en x)
        (clNativeCircuit k b sb hI.hsb σ θ (ε / 2) t (af Rg) (aa Rg)) (sysH (R := R) D en x) t
        (ε / 2) (2 * Qmu s η μ t ε) (fun p => 6 * nCallsN p (computeV k b))
        (clNativeCost k sb (af Rg) (aa Rg)) ε) := by
  have hε : 0 < ε := by linarith [hP.ε0]
  have hε1 : ε ≤ 1 / 32 := by linarith [hP.ε1]
  rcases gate_optimal_native_clip_total (prims (R := R) D en x) (prims_isUnitary D en x) hξ hζ.le
      hP.μη hP.ηs hP.σdef hP.θdef hP.θ1 hε hε1 hδε (sysH_star D en x hI.herm)
      (binIB hI hP) (binNB hI hP hζ hζ1) (binIS hI hP) (binNS hI hP ar) (binIC hI hP)
      (binNC hI hP af aa) with ⟨hb, hN⟩ | ⟨h1, h2, hN⟩ | ⟨Rg, hN⟩
  · rw [binNB_calls, binNB_cost] at hN
    exact Or.inl ⟨hb, hN⟩
  · rw [binNS_calls, binNS_cost] at hN
    exact Or.inr (Or.inl ⟨h1, h2, hN⟩)
  · rw [binNC_calls, binNC_cost] at hN
    exact Or.inr (Or.inr ⟨Rg, hN⟩)

/-- **Theorem `gate:thm:main` from binary sparse oracles over a finite gate set.** Under the
synthesis hypothesis `Synthesis 𝒢 X_a L` (one-qubit unitaries with at most three controls; by
`Synthesis.of_parts` it follows from single-qubit synthesis, the external result, and an exact
decomposition of the controlled gates) and the synthesis budget `ε' > 0`, the synthesised native
circuit `synthBudget hS ε' C` of the selected regime satisfies `SynthClaims`: gates of `𝒢` and the
same primitive calls (`2`, `2` or `6` compute circuits per private call), at most `N L(ε'/(N+1))`
gates for the `N` gates of the native circuit (with a logarithmic `L`, `SynthClaims.gates_log`),
`|X_a|` more qubits, and full-output error `ε + ε'`. -/
theorem gate_optimal_binary_synth [FiniteDimensional ℂ R] (hI : BinaryInput D en sb c0 x η μ)
    (hP : MainParams s η μ t (ε / 2) σ θ) {ξ ζ : ℝ} (hξ : 0 ≤ ξ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hδε : 8 * 10 ^ 11 * Qmu s η μ t ε * (6 * ξ + 4 * ζ) ≤ ε)
    {bT bP A bT' bP' A' : ℕ}
    (ar : 10 ^ 4 ≤ hval θ (ε / 2) → σ * θ < Lval (ε / 2) * hval θ (ε / 2) →
      FactorWordArith b (c0 / μ) ξ bT bP A)
    (af : Regime σ θ (ε / 2) → ClipFactorArith b μ (hval θ (ε / 2)) c0 ξ bT' bP' A')
    (aa : Regime σ θ (ε / 2) →
      ClipAngleArith b μ (hval θ (ε / 2)) (qval σ θ (ε / 2)) c0 ζ bT' bP' A')
    {𝒢 : Set Kind} {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {L : ℝ → ℕ}
    (hS : Synthesis 𝒢 Xa L) {ε' : ℝ} (hε' : 0 < ε') :
    (hval θ (ε / 2) < 10 ^ 4 ∧
      SynthClaims (prims (R := R) D en x) 𝒢 Xa L ε'
        (synthBudget hS ε' (bdNativeCircuit k b sb hI.hsb s c0 η σ θ (ε / 2) ζ t))
        (sysH (R := R) D en x) t (ε / 2) (2 * Qmu s η μ t ε)
        (fun p => 2 * nCallsN p (computeV k b))
        (nGatesN (bdNativeCircuit k b sb hI.hsb s c0 η σ θ (ε / 2) ζ t))
        (bdNativeCost k b sb s c0 η σ θ (ε / 2) ζ) (ε + ε')) ∨
    (∃ (h1 : 10 ^ 4 ≤ hval θ (ε / 2)) (h2 : σ * θ < Lval (ε / 2) * hval θ (ε / 2)),
      SynthClaims (prims (R := R) D en x) 𝒢 Xa L ε'
        (synthBudget hS ε' (sgNativeCircuit k b sb hI.hsb s μ σ t (ε / 2) c0 (ar h1 h2)))
        (sysH (R := R) D en x) t (ε / 2) (2 * Qmu s η μ t ε)
        (fun p => 2 * nCallsN p (computeV k b))
        (nGatesN (sgNativeCircuit k b sb hI.hsb s μ σ t (ε / 2) c0 (ar h1 h2)))
        (sgNativeCost k sb (ar h1 h2)) (ε + ε')) ∨
    (∃ Rg : Regime σ θ (ε / 2),
      SynthClaims (prims (R := R) D en x) 𝒢 Xa L ε'
        (synthBudget hS ε' (clNativeCircuit k b sb hI.hsb σ θ (ε / 2) t (af Rg) (aa Rg)))
        (sysH (R := R) D en x) t (ε / 2) (2 * Qmu s η μ t ε)
        (fun p => 6 * nCallsN p (computeV k b))
        (nGatesN (clNativeCircuit k b sb hI.hsb σ θ (ε / 2) t (af Rg) (aa Rg)))
        (clNativeCost k sb (af Rg) (aa Rg)) (ε + ε')) := by
  have hpu := prims_isUnitary (R := R) D en x
  rcases gate_optimal_binary_total (R := R) hI hP hξ hζ hζ1 hδε ar af aa with
    ⟨hb, hN⟩ | ⟨h1, h2, hN⟩ | ⟨Rg, hN⟩
  · exact Or.inl ⟨hb, synthClaims_of_native hpu hN hS hε'⟩
  · exact Or.inr (Or.inl ⟨h1, h2, synthClaims_of_native hpu hN hS hε'⟩)
  · exact Or.inr (Or.inr ⟨Rg, synthClaims_of_native hpu hN hS hε'⟩)

end Endpoint

end

end GateOptimalBinary
