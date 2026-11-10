import GeneralDecoder.MainNative

/-!
# Theorem `gate:thm:main` from binary sparse oracles with the decoder of the data

The binary endpoint of `GateOptimalBinary.Main` for a binary sparse input whose stored words are
decoded by the public decoder of the data (`BinaryInputD`: `k`-bit indices, `s = 2^{s_b}` slots
enumerated by the low words, no assumption on the decoder), with the scalar arithmetic of each
regime supplied on the base wires as the arithmetic hypothesis of the native theorem:

* bounded regime: an angle arithmetic of the decoded entry `(γ √s/η) decode(e, w)`
  (`γ = bdGamma σ θ ε`, `ArithOK`);
* signed-factor regime: a factor arithmetic of `clip(decode(e, w)/μ)` (`FactorArithOK` of `sgFOD`);
* clipped regime: a factor arithmetic of `[g] c₂` (`FactorArithOK` of `clFOD`) and an angle
  arithmetic of `y(g, f, c₁, c₂)` (`ArithOK` of `clNDD`) on common arithmetic wires.

`gate_optimal_binaryD_total`: the native circuit of the regime selected by `(h, σθ)` satisfies
`GateOptimalPrecision.NativeClaims` with total error `ε`; `gate_optimal_binaryD_synth`: over a
finite gate set, `GateOptimalBinary.SynthClaims`. The counts are those of `GateOptimalBinary`
(`2`, `2` or `6` compute circuits per private call), the per-call gates `bdNativeCostD`,
`sgNativeCostD`, `clNativeCostD` those of the supplied arithmetic.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralDecoder

noncomputable section

open ContinuousLinearMap SparseHamiltonian.OracleCircuit SparseHamiltonian.GateCircuit
  SparseHamiltonian.GateCircuit.Sim SparseHamiltonian.GateNative SparseHamiltonian.GateBinary
  SparseHamiltonian.GateSynth GateOptimalPrecision GateOptimalBinary
open NativeSparseBlockEncoding (Data Query)
open LargeSparsityCore.Parameters (hval qval Lval Regime)

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-! ### The input -/

/-- **A binary sparse input with the decoder of the data** of Theorem `gate:thm:main`: sparse
access data `D` with `k`-bit indices (`en`), `s = 2^{s_b}` slots enumerated by the low words
(`hrange`), and an input `x` whose matrix is Hermitian with row and column Euclidean norms at most
`η` and entries of modulus at most `μ`. The stored words are decoded by the decoder of the data,
which may depend on the edge. -/
structure BinaryInputD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ) (x : X)
    (η μ : ℝ) : Prop where
  hsb : sb ≤ k
  hs : s = 2 ^ sb
  hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u)
  herm : (D.matrix x).IsHermitian
  row : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2
  col : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2
  ent : ∀ i j, ‖D.matrix x i j‖ ≤ μ

/-! ### The native circuits -/

/-- **The native circuit of the bounded regime with the decoder of the data**: the boundary gates
`hadUJ`, the native private operation `sparseOpD` of the normalised data at the rescaling `γ √s`
(`γ = bdGamma σ θ ε`), the supplied angle arithmetic and the released circuit `bdSigned`. -/
def bdNativeCircuitD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ) (hsb : sb ≤ k)
    {η : ℝ} (hη : 0 < η) (σ θ ε t : ℝ) (ar : Arith (BW k b)) :=
  nativeOf (S := Fin k) (hadUJ k sb hsb)
    (sparseOpD (normD D η hη) en (bdGamma σ θ ε * Real.sqrt s)) ar (bdSigned (k + 1) σ θ ε t)

/-- The gates of one native boundary call and one native private call of the bounded regime. -/
def bdNativeCostD (k sb : ℕ) {b : ℕ} (ar : Arith (BW k b)) : ℕ :=
  7 * (sb + 1) + (2 * (28 * k) + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1))

/-- **The native circuit of the signed-factor regime with the decoder of the data**: the boundary
gates `sgUJg`, the native factor `sgFOD` and the released circuit `sgCircuit`. -/
def sgNativeCircuitD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ) (hsb : sb ≤ k)
    (μ σ t ε : ℝ) {bT bP A : ℕ} (circ : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (tw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (pw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool) :=
  factorNativeOf (S := Fin k) (sgUJg k sb hsb) (sgFOD D en μ circ tw pw)
    (sgCircuit (k + 3) (GateOptimalBinary.fW k) (GateOptimalBinary.zW k) (s * μ)
      (Real.sqrt σ)⁻¹ t ε)

/-- The gates of one native boundary call and one native factor call of the signed regime. -/
def sgNativeCostD (k sb : ℕ) {b bT bP A : ℕ}
    (circ : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A))) : ℕ :=
  7 * (sb + 1) + (2 * (28 * k) + 2 * circ.length + (2 * bP + bT + 4))

/-- **The native private call of the clipped regime with the decoder of the data**: the native
factor, the native rotation and the literal inverse of the native factor. -/
def clipPCD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) {bT bP A : ℕ}
    (fcirc : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (ftw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (fpw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool)
    (acirc : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (atw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (apw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool) :
    List (NInstr (PWr Empty (PRf k) (SZ k b) bT bP A) (PY k b) Query) :=
  factorMacro (clFOD D en μ β fcirc ftw fpw) ++
    privMacro (clNDD D en μ β q) (⟨bT, bP, A, acirc, atw, apw⟩ : Arith (NB Empty (PRf k) (SZ k b))) ++
    ninv (factorMacro (clFOD D en μ β fcirc ftw fpw))

/-- **The native circuit of the clipped regime with the decoder of the data**: the boundary gates
`clUJg`, the native private call `clipPCD` and the released circuit `clipSigned`. -/
def clNativeCircuitD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ) (hsb : sb ≤ k)
    (σ θ ε t μ : ℝ) {bT bP A : ℕ}
    (fcirc : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (ftw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (fpw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool)
    (acirc : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (atw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (apw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool) :=
  clipNativeOf (S := Fin k) (clUJg k sb hsb)
    (clipPCD D en μ (hval θ ε) (qval σ θ ε) fcirc ftw fpw acirc atw apw)
    (clipSigned (k + 3 + 1) σ θ ε t)

/-- The gates of one native boundary call and one native private call of the clipped regime. -/
def clNativeCostD (k sb : ℕ) {b bT bP A : ℕ}
    (fcirc acirc : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A))) : ℕ :=
  7 * (sb + 2) + (2 * (2 * (28 * k) + 2 * fcirc.length + (2 * bP + bT + 4)) +
    (2 * (28 * k) + 2 * acirc.length + (2 * bP + bT + 1)))

/-! ### The interfaces and the native data of the three regimes -/

section Families

variable {D : Data X n (Cfg (VW b)) s} {en : Cfg (Fin k) ≃ n} {sb : ℕ} {x : X}
  {η μ t ε σ θ : ℝ}

/-- The interface of the bounded regime. -/
def binIBD (hI : BinaryInputD D en sb x η μ) (hP : MainParams s η μ t ε σ θ) :
    hval θ ε < 10 ^ 4 → BoundedIface (Reg (Fin k) R) σ (Real.sqrt s * η) (sysH (R := R) D en x) :=
  fun _ => boundedIface D en sb hI.hsb hI.hs hI.hrange hP.η_pos hP.μ_pos.le hP.σdef x hI.herm
    hI.row hI.col hI.ent

/-- The native data of the bounded regime, with the supplied angle arithmetic `ar`. -/
def binNBD (hI : BinaryInputD D en sb x η μ) (hP : MainParams s η μ t ε σ θ) {ζ : ℝ}
    (ar : Arith (BW k b))
    (har : ArithOK ar (Sum.inl (Sum.inr (oPR k)))
      (fun y => ((bdGamma σ θ ε * Real.sqrt s / η : ℝ) : ℂ) *
        D.decode (phiE en (eword y)) (vword y)) ζ) :
    ∀ hb : hval θ ε < 10 ^ 4, CayleyNative (prims (R := R) D en x) (binIBD (R := R) hI hP hb).UJ
      (bdPriv (binIBD (R := R) hI hP hb).K σ θ ε) (SZ k b) ζ :=
  fun _ => boundedNativeD D en sb hI.hsb hI.hs hI.hrange hP.η_pos hP.μ_pos.le hP.σdef x hI.herm
    hI.row hI.col hI.ent ar har

/-- The interface of the signed-factor regime. -/
def binISD (hI : BinaryInputD D en sb x η μ) (hP : MainParams s η μ t ε σ θ) :
    10 ^ 4 ≤ hval θ ε → σ * θ < Lval ε * hval θ ε →
      SignedIface (Reg (Fin k) R) (s * μ) (Real.sqrt σ)⁻¹ (sysH (R := R) D en x) :=
  fun _ _ => signedIface D en sb hI.hsb hI.hs hI.hrange hP.η_pos hP.μ_pos hP.σdef x hI.herm
    hI.row hI.ent

/-- The native data of the signed-factor regime, with the supplied factor arithmetic. -/
def binNSD (hI : BinaryInputD D en sb x η μ) (hP : MainParams s η μ t ε σ θ) {ξ : ℝ}
    {bT bP A : ℕ} (circ : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (tw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (pw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool)
    (har : FactorArithOK (sgFOD D en μ circ tw pw) ξ) :
    ∀ (h1 : 10 ^ 4 ≤ hval θ ε) (h2 : σ * θ < Lval ε * hval θ ε),
      FactorNative (prims (R := R) D en x) (binISD (R := R) hI hP h1 h2).UJ
        (binISD (R := R) hI hP h1 h2).U (SZ k b) bT bP A ξ :=
  fun _ _ => signedNativeD D en sb hI.hsb hI.hs hI.hrange hP.η_pos hP.μ_pos hP.σdef x hI.herm
    hI.row hI.ent circ tw pw har

/-- The interface of the clipped regime. -/
def binICD (hI : BinaryInputD D en sb x η μ) (hP : MainParams s η μ t ε σ θ) :
    Regime σ θ ε → ClippedIface (Reg (Fin k) R) σ θ ε (s * μ / qval σ θ ε)
      (sysH (R := R) D en x) :=
  fun Rg => clippedIface D en sb hI.hsb hI.hs hI.hrange Rg hP.μ_pos hP.σdef x hI.herm hI.row
    hI.col hI.ent

/-- The native data of the clipped regime, with the supplied factor and angle arithmetic. -/
def binNCD (hI : BinaryInputD D en sb x η μ) (hP : MainParams s η μ t ε σ θ) {ξ ζ : ℝ}
    {bT bP A : ℕ} (fcirc : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (ftw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (fpw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool)
    (acirc : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (atw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (apw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool)
    (haf : FactorArithOK (clFOD D en μ (hval θ ε) fcirc ftw fpw) ξ)
    (haa : ArithOK (⟨bT, bP, A, acirc, atw, apw⟩ : Arith (NB Empty (PRf k) (SZ k b)))
      (Sum.inl (Sum.inr (locF k 1))) (ckdecD D en μ (hval θ ε) (qval σ θ ε)) ζ) :
    ∀ Rg : Regime σ θ ε, ClipNative (prims (R := R) D en x) (binICD (R := R) hI hP Rg).UJ
      (binICD (R := R) hI hP Rg).D (SZ k b) bT bP A ξ ζ :=
  fun Rg => clipNativeD D en sb hI.hsb hI.hs hI.hrange Rg hP.μ_pos hP.σdef x hI.herm hI.row
    hI.col hI.ent fcirc ftw fpw acirc atw apw haf haa

theorem binNBD_calls (hI : BinaryInputD D en sb x η μ) (hP : MainParams s η μ t ε σ θ) {ζ : ℝ}
    (ar : Arith (BW k b))
    (har : ArithOK ar (Sum.inl (Sum.inr (oPR k)))
      (fun y => ((bdGamma σ θ ε * Real.sqrt s / η : ℝ) : ℂ) *
        D.decode (phiE en (eword y)) (vword y)) ζ) (hb : hval θ ε < 10 ^ 4) :
    (binNBD (R := R) hI hP ar har hb).calls = fun p => 2 * nCallsN p (computeV k b) := rfl

theorem binNBD_cost (hI : BinaryInputD D en sb x η μ) (hP : MainParams s η μ t ε σ θ) {ζ : ℝ}
    (ar : Arith (BW k b))
    (har : ArithOK ar (Sum.inl (Sum.inr (oPR k)))
      (fun y => ((bdGamma σ θ ε * Real.sqrt s / η : ℝ) : ℂ) *
        D.decode (phiE en (eword y)) (vword y)) ζ) (hb : hval θ ε < 10 ^ 4) :
    (binNBD (R := R) hI hP ar har hb).cost = bdNativeCostD k sb ar := by
  change 7 * (hadUJ k sb hI.hsb).length + (2 * nGatesN (computeV k b) + 2 * ar.circ.length +
    (2 * ar.bP + ar.bT + 1)) = _
  rw [hadUJ_length, computeV_nGates]
  rfl

theorem binNSD_calls (hI : BinaryInputD D en sb x η μ) (hP : MainParams s η μ t ε σ θ) {ξ : ℝ}
    {bT bP A : ℕ} (circ : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (tw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (pw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool)
    (har : FactorArithOK (sgFOD D en μ circ tw pw) ξ)
    (h1 : 10 ^ 4 ≤ hval θ ε) (h2 : σ * θ < Lval ε * hval θ ε) :
    (binNSD (R := R) hI hP circ tw pw har h1 h2).calls =
      fun p => 2 * nCallsN p (computeV k b) := by
  funext p
  change 2 * nCallsN p ((computeV k b).map (NInstr.map (ιBe k b))) = _
  rw [nCallsN_map]

theorem binNSD_cost (hI : BinaryInputD D en sb x η μ) (hP : MainParams s η μ t ε σ θ) {ξ : ℝ}
    {bT bP A : ℕ} (circ : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (tw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (pw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool)
    (har : FactorArithOK (sgFOD D en μ circ tw pw) ξ)
    (h1 : 10 ^ 4 ≤ hval θ ε) (h2 : σ * θ < Lval ε * hval θ ε) :
    (binNSD (R := R) hI hP circ tw pw har h1 h2).cost = sgNativeCostD k sb circ := by
  change 7 * (sgUJg k sb hI.hsb).length +
    (2 * nGatesN ((computeV k b).map (NInstr.map (ιBe k b))) + 2 * circ.length +
      (2 * bP + bT + 4)) = _
  rw [sgUJg_length, nGatesN_map, computeV_nGates]
  rfl

theorem binNCD_calls (hI : BinaryInputD D en sb x η μ) (hP : MainParams s η μ t ε σ θ) {ξ ζ : ℝ}
    {bT bP A : ℕ} (fcirc : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (ftw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (fpw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool)
    (acirc : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (atw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (apw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool)
    (haf : FactorArithOK (clFOD D en μ (hval θ ε) fcirc ftw fpw) ξ)
    (haa : ArithOK (⟨bT, bP, A, acirc, atw, apw⟩ : Arith (NB Empty (PRf k) (SZ k b)))
      (Sum.inl (Sum.inr (locF k 1))) (ckdecD D en μ (hval θ ε) (qval σ θ ε)) ζ)
    (Rg : Regime σ θ ε) :
    (binNCD (R := R) hI hP fcirc ftw fpw acirc atw apw haf haa Rg).calls =
      fun p => 6 * nCallsN p (computeV k b) := by
  funext p
  rw [ClipNative.calls_eq]
  change 4 * nCallsN p ((computeV k b).map (NInstr.map (ιBe k b))) +
    2 * nCallsN p ((computeV k b).map (NInstr.map (ιBe k b))) = _
  rw [nCallsN_map]
  ring

theorem binNCD_cost (hI : BinaryInputD D en sb x η μ) (hP : MainParams s η μ t ε σ θ) {ξ ζ : ℝ}
    {bT bP A : ℕ} (fcirc : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (ftw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (fpw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool)
    (acirc : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (atw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (apw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool)
    (haf : FactorArithOK (clFOD D en μ (hval θ ε) fcirc ftw fpw) ξ)
    (haa : ArithOK (⟨bT, bP, A, acirc, atw, apw⟩ : Arith (NB Empty (PRf k) (SZ k b)))
      (Sum.inl (Sum.inr (locF k 1))) (ckdecD D en μ (hval θ ε) (qval σ θ ε)) ζ)
    (Rg : Regime σ θ ε) :
    (binNCD (R := R) hI hP fcirc ftw fpw acirc atw apw haf haa Rg).cost =
      clNativeCostD k sb fcirc acirc := by
  rw [ClipNative.cost, ClipNative.pc_nGates]
  change 7 * (clUJg k sb hI.hsb).length +
    (2 * (2 * nGatesN ((computeV k b).map (NInstr.map (ιBe k b))) + 2 * fcirc.length +
      (2 * bP + bT + 4)) +
    (2 * nGatesN ((computeV k b).map (NInstr.map (ιBe k b))) + 2 * acirc.length +
      (2 * bP + bT + 1))) = _
  rw [clUJg_length, nGatesN_map, computeV_nGates]
  rfl

end Families

/-! ### The binary endpoint -/

section Endpoint

variable {D : Data X n (Cfg (VW b)) s} {en : Cfg (Fin k) ≃ n} {sb : ℕ} {x : X}
  {η μ t ε σ θ : ℝ}

/-- **Theorem `gate:thm:main` from binary sparse oracles with the decoder of the data, native
form, total error `ε`**: the exact-gate construction at accuracy `ε/2` (the parameters `hP` at
`ε/2`) and the supplied arithmetic of accuracies `ξ` (factor) and `ζ` (angles) with
`8·10¹¹ Q_μ (6ξ + 4ζ) ≤ ε`; the native circuit of each regime satisfies `NativeClaims` at `ε/2`
with the count parameter `2 Q_μ` and full-output error `ε`. -/
theorem gate_optimal_binaryD_total [FiniteDimensional ℂ R] (hI : BinaryInputD D en sb x η μ)
    (hP : MainParams s η μ t (ε / 2) σ θ) {ξ ζ : ℝ} (hξ : 0 ≤ ξ) (hζ : 0 ≤ ζ)
    (hδε : 8 * 10 ^ 11 * Qmu s η μ t ε * (6 * ξ + 4 * ζ) ≤ ε)
    (arB : Arith (BW k b))
    (harB : ArithOK arB (Sum.inl (Sum.inr (oPR k)))
      (fun y => ((bdGamma σ θ (ε / 2) * Real.sqrt s / η : ℝ) : ℂ) *
        D.decode (phiE en (eword y)) (vword y)) ζ)
    {bT bP A : ℕ} (scirc : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (stw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (spw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool)
    (hsa : FactorArithOK (sgFOD D en μ scirc stw spw) ξ)
    {bT' bP' A' : ℕ} (fcirc : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT' bP' A')))
    (ftw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT' → Bool)
    (fpw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP' → Bool)
    (acirc : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT' bP' A')))
    (atw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT' → Bool)
    (apw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP' → Bool)
    (haf : FactorArithOK (clFOD D en μ (hval θ (ε / 2)) fcirc ftw fpw) ξ)
    (haa : ArithOK (⟨bT', bP', A', acirc, atw, apw⟩ : Arith (NB Empty (PRf k) (SZ k b)))
      (Sum.inl (Sum.inr (locF k 1))) (ckdecD D en μ (hval θ (ε / 2)) (qval σ θ (ε / 2))) ζ) :
    (hval θ (ε / 2) < 10 ^ 4 ∧
      NativeClaims (prims (R := R) D en x)
        (bdNativeCircuitD D en sb hI.hsb hP.η_pos σ θ (ε / 2) t arB) (sysH (R := R) D en x) t
        (ε / 2) (2 * Qmu s η μ t ε) (fun p => 2 * nCallsN p (computeV k b))
        (bdNativeCostD k sb arB) ε) ∨
    (∃ (_ : 10 ^ 4 ≤ hval θ (ε / 2)) (_ : σ * θ < Lval (ε / 2) * hval θ (ε / 2)),
      NativeClaims (prims (R := R) D en x)
        (sgNativeCircuitD D en sb hI.hsb μ σ t (ε / 2) scirc stw spw) (sysH (R := R) D en x) t
        (ε / 2) (2 * Qmu s η μ t ε) (fun p => 2 * nCallsN p (computeV k b))
        (sgNativeCostD k sb scirc) ε) ∨
    (∃ _ : Regime σ θ (ε / 2),
      NativeClaims (prims (R := R) D en x)
        (clNativeCircuitD D en sb hI.hsb σ θ (ε / 2) t μ fcirc ftw fpw acirc atw apw)
        (sysH (R := R) D en x) t (ε / 2) (2 * Qmu s η μ t ε)
        (fun p => 6 * nCallsN p (computeV k b)) (clNativeCostD k sb fcirc acirc) ε) := by
  have hε : 0 < ε := by linarith [hP.ε0]
  have hε1 : ε ≤ 1 / 32 := by linarith [hP.ε1]
  rcases gate_optimal_native_clip_total (prims (R := R) D en x) (prims_isUnitary D en x) hξ hζ
      hP.μη hP.ηs hP.σdef hP.θdef hP.θ1 hε hε1 hδε (sysH_star D en x hI.herm)
      (binIBD hI hP) (binNBD hI hP arB harB) (binISD hI hP) (binNSD hI hP scirc stw spw hsa)
      (binICD hI hP) (binNCD hI hP fcirc ftw fpw acirc atw apw haf haa) with
    ⟨hb, hN⟩ | ⟨h1, h2, hN⟩ | ⟨Rg, hN⟩
  · rw [binNBD_calls, binNBD_cost] at hN
    exact Or.inl ⟨hb, hN⟩
  · rw [binNSD_calls, binNSD_cost] at hN
    exact Or.inr (Or.inl ⟨h1, h2, hN⟩)
  · rw [binNCD_calls, binNCD_cost] at hN
    exact Or.inr (Or.inr ⟨Rg, hN⟩)

/-- **Theorem `gate:thm:main` from binary sparse oracles with the decoder of the data over a
finite gate set.** Under the synthesis hypothesis `Synthesis 𝒢 X_a L` and the synthesis budget
`ε' > 0`, the synthesised native circuit `synthBudget hS ε' C` of the selected regime satisfies
`SynthClaims`, with full-output error `ε + ε'`. -/
theorem gate_optimal_binaryD_synth [FiniteDimensional ℂ R] (hI : BinaryInputD D en sb x η μ)
    (hP : MainParams s η μ t (ε / 2) σ θ) {ξ ζ : ℝ} (hξ : 0 ≤ ξ) (hζ : 0 ≤ ζ)
    (hδε : 8 * 10 ^ 11 * Qmu s η μ t ε * (6 * ξ + 4 * ζ) ≤ ε)
    (arB : Arith (BW k b))
    (harB : ArithOK arB (Sum.inl (Sum.inr (oPR k)))
      (fun y => ((bdGamma σ θ (ε / 2) * Real.sqrt s / η : ℝ) : ℂ) *
        D.decode (phiE en (eword y)) (vword y)) ζ)
    {bT bP A : ℕ} (scirc : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (stw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (spw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool)
    (hsa : FactorArithOK (sgFOD D en μ scirc stw spw) ξ)
    {bT' bP' A' : ℕ} (fcirc : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT' bP' A')))
    (ftw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT' → Bool)
    (fpw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP' → Bool)
    (acirc : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT' bP' A')))
    (atw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT' → Bool)
    (apw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP' → Bool)
    (haf : FactorArithOK (clFOD D en μ (hval θ (ε / 2)) fcirc ftw fpw) ξ)
    (haa : ArithOK (⟨bT', bP', A', acirc, atw, apw⟩ : Arith (NB Empty (PRf k) (SZ k b)))
      (Sum.inl (Sum.inr (locF k 1))) (ckdecD D en μ (hval θ (ε / 2)) (qval σ θ (ε / 2))) ζ)
    {𝒢 : Set Kind} {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {L : ℝ → ℕ}
    (hS : Synthesis 𝒢 Xa L) {ε' : ℝ} (hε' : 0 < ε') :
    (hval θ (ε / 2) < 10 ^ 4 ∧
      SynthClaims (prims (R := R) D en x) 𝒢 Xa L ε'
        (synthBudget hS ε' (bdNativeCircuitD D en sb hI.hsb hP.η_pos σ θ (ε / 2) t arB))
        (sysH (R := R) D en x) t (ε / 2) (2 * Qmu s η μ t ε)
        (fun p => 2 * nCallsN p (computeV k b))
        (nGatesN (bdNativeCircuitD D en sb hI.hsb hP.η_pos σ θ (ε / 2) t arB))
        (bdNativeCostD k sb arB) (ε + ε')) ∨
    (∃ (_ : 10 ^ 4 ≤ hval θ (ε / 2)) (_ : σ * θ < Lval (ε / 2) * hval θ (ε / 2)),
      SynthClaims (prims (R := R) D en x) 𝒢 Xa L ε'
        (synthBudget hS ε' (sgNativeCircuitD D en sb hI.hsb μ σ t (ε / 2) scirc stw spw))
        (sysH (R := R) D en x) t (ε / 2) (2 * Qmu s η μ t ε)
        (fun p => 2 * nCallsN p (computeV k b))
        (nGatesN (sgNativeCircuitD D en sb hI.hsb μ σ t (ε / 2) scirc stw spw))
        (sgNativeCostD k sb scirc) (ε + ε')) ∨
    (∃ _ : Regime σ θ (ε / 2),
      SynthClaims (prims (R := R) D en x) 𝒢 Xa L ε'
        (synthBudget hS ε'
          (clNativeCircuitD D en sb hI.hsb σ θ (ε / 2) t μ fcirc ftw fpw acirc atw apw))
        (sysH (R := R) D en x) t (ε / 2) (2 * Qmu s η μ t ε)
        (fun p => 6 * nCallsN p (computeV k b))
        (nGatesN (clNativeCircuitD D en sb hI.hsb σ θ (ε / 2) t μ fcirc ftw fpw acirc atw apw))
        (clNativeCostD k sb fcirc acirc) (ε + ε')) := by
  have hpu := prims_isUnitary (R := R) D en x
  rcases gate_optimal_binaryD_total (R := R) hI hP hξ hζ hδε arB harB scirc stw spw hsa fcirc ftw
      fpw acirc atw apw haf haa with ⟨hb, hN⟩ | ⟨h1, h2, hN⟩ | ⟨Rg, hN⟩
  · exact Or.inl ⟨hb, synthClaims_of_native hpu hN hS hε'⟩
  · exact Or.inr (Or.inl ⟨h1, h2, synthClaims_of_native hpu hN hS hε'⟩)
  · exact Or.inr (Or.inr ⟨Rg, synthClaims_of_native hpu hN hS hε'⟩)

end Endpoint

end

end SparseHamiltonian.GeneralDecoder
