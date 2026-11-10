import ManuscriptConformance.GateODEGeneral
import ManuscriptConformance.GateODETimeGeneral
import GeneralDecoderODE.Decoder

/-!
# Conformance: Theorem `ode:thm:gates` with binary entry decoding

Theorem `ode:thm:gates` assumes "efficient binary entry decoding" (the introduction of Section
`ode:sec:gates`: "entry decoding, the exact zero tests in Eq. `ode:eq:tagvalue` and the required
arithmetic admit reversible circuits of fixed polynomial gate and work cost in these lengths and
the requested accuracy bits"), for sparse access
with a known decoder `val` of the stored words (Section `hs:sec:control`: `H_ij = val(w_ij)`).
`ode_thm_gates_general` and `ode_thm_gates_time_general` (`GateODEGeneral`, `GateODETimeGeneral`)
assume the decoder `c₀(X + iY)` (`formal_binaryDecoder`, review item B2). This module states the
theorem for any decoder `val` with an **exact binary entry decoding**, this package's own condition
and its formal reading of that assumption:

* **Binary entry decoding** (`BinaryEntryDecoding D dc c₀`): a reversible circuit
  `dc : GeneralDecoderODE.BinDecode b b' A` of controlled NOT gates with at most three controls on
  the stored word (`2b` bits), the decoded word (two `b'`-bit two's complement components, `b' > 0`)
  and `A` work wires, which writes the decoded word on clean wires and restores the work wires, and
  is exact for the decoder: `val w = c₀ (X + iY)` for the components of the decoded word of every
  stored word `w`, `c₀ > 0`. Its cost `cost dc = |dc| + 2b + 2b' + A` counts its gates and wires,
  `wires dc = 2b + 2b' + A` its wires.
* **Protocol.** The package's four-attempt protocol for the padded problem of the decoded data
  (`GeneralDecoderODE.prepD`, `prepTD`, public data `odePubG …`, `odePubTG …` with `b'` stored
  bits): as in `ode_thm_gates_general` and `ode_thm_gates_time_general`, with every call of the
  padded oracles replaced by the implementation `implP` of the decoded data and every decoded value
  call in it by two supplied value calls around the decoding circuit, the copy of the decoded word
  and the decoding backwards (`GeneralDecoderODE.implDP`, `implDec`: at most six supplied calls
  and `implG k b' + 3 (2 |dc| + 2b')` gates per padded call, on clean ancillas in the private
  scratch). It depends only on the public data, the decoding circuit and the source circuits.
* **Conclusions.** Those of `ode_thm_gates_general` and `ode_thm_gates_time_general` for the
  supplied oracles of `D`, with the decoding cost in the polynomial of the gate bound and its wires
  in the qubit bound: at most `C ḡ [q ((𝔟+1)³ + cost dc) + G_src + A_src]` gates and
  `C (𝔟+1)³ + C A_src + C wires dc` qubits; at most `C ḡ q` calls of each supplied matrix oracle
  besides `C ḡ` times the calls inside the source circuits; the same output guarantees.

**Scope of the decoding.** Exactness asks every decoded value to be a binary entry `c₀ (X + iY)`,
with two `b'`-bit two's complement components and one public scale `c₀` of at most `b_data` bits,
so the represented entries lie on the grid `c₀ (ℤ + iℤ)`. It is asked on every stored word, which
is harmless: the oracles do not depend on `val` and the matrix depends on it only through the
stored words of its entries, so a decoding exact on those words is a binary entry decoding of the
sparse access with the decoder changed on the other words to the decoded values (and the scale
`D.scale` enlarged if needed), which has the same oracles and the same matrix. A decoder with other
values, or a decoding to the requested accuracy only, is not covered; the theorems apply to the
rounded decoder, whose matrix is then the represented matrix. The bound `b_data` of `comp_bits`
bounds the bits `b'` of the decoded components and the public parameters; the stored words, of `2b`
bits, enter the bounds through `cost dc` and `wires dc`, both at least `2b`. For the manuscript's
`b_data`, which also bounds the stored words (the introduction of Section `ode:sec:gates`), apply
the theorems with `max(b_data, b')`; for an efficient decoding `b'`, `cost dc` and `wires dc` are
polynomial in `b_data` and the accuracy bits, so that `C ((𝔟+1)³ + cost dc)` and
`C (𝔟+1)³ + C wires dc` are polynomial in the manuscript's `𝔟` (Theorem `ode:thm:gates`, eqs.
`ode:eq:gate-word-budget`, `ode:eq:gate-main`, `ode:eq:gate-space`).

The decoder `c₀(X + iY)` has the copy of the stored word as its binary entry decoding
(`binaryEntryDecoding_copy`: `2b` gates, cost `6b + A`), so these theorems apply under the
hypotheses of `ode_thm_gates_general` and `ode_thm_gates_time_general`, with their own protocol
(the stored words read through the copy) and constants; every decoder whose values are binary
entries `c₀ (X + iY)` has an exact lookup-table decoding (`exists_binaryEntryDecoding`), whose cost
is exponential in `b`.

**Special case.** `ode_thm_gates_time_decoder` is the special case of Theorem `ode:thm:gates` under
the package's uniform-mesh conditions (`formal_uniformMeshG`); the conformance forms of the theorem
are `ode_thm_gates_time_cert` and `ode_thm_gates_time_decoder_cert` (`GateODETimeCert`).

**Formal restrictions.** `formal_nondegenerate` (constant coefficients), `formal_gbarOne` and
`formal_uniformMeshG` (time-dependent); the sizes `N`, `s` and the locator lists are general, and
the decoder is every decoder with an exact binary entry decoding (review items B, B2).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GeneralSparseODE (GPub GPubT markEmb padLift primsTG)
open SparseHamiltonian.GeneralDecoderODE (BinDecode DW prepD prepTD)
open SparseHamiltonian.ZeroTimeGateODE (BPublicOK0 BZeroCase BTPublicOK0 BTZeroCase)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

universe u

/-! ### Binary entry decoding -/

/-- **Binary entry decoding** (the introduction of Section `ode:sec:gates` and Theorem
`ode:thm:gates`): the reversible decoding circuit `dc` writes the decoded word of every stored
word, two `b'`-bit two's complement components, `b' > 0`, and is exact for the decoder of the
sparse access on every stored word: `val w = c₀ (X + iY)`, `c₀ > 0`. (Exactness on the stored
words of the entries of the matrix suffices: the oracles do not depend on `val`, so the decoder
may be changed on the other words; see the module docstring.) -/
structure BinaryEntryDecoding {X : Type*} {N s k b b' A : ℕ}
    (D : GeneralSparseAccess.QData X N s k b) (dc : BinDecode b b' A) (c0 : ℝ) : Prop where
  hb : 0 < b'
  hc0 : 0 < c0
  exact : dc.Exact D.val c0

/-- **The decoder `c₀(X + iY)` has a binary entry decoding**: the copy of the stored word. -/
theorem binaryEntryDecoding_copy {X : Type*} {N s k b : ℕ} {D : GeneralSparseAccess.QData X N s k b}
    {c0 : ℝ} (h : formal_binaryDecoder D c0) (A : ℕ) :
    BinaryEntryDecoding D (BinDecode.copy b A) c0 ∧ (BinDecode.copy b A).cost = 6 * b + A :=
  ⟨⟨h.hb, h.hc0, BinDecode.copy_exact b A D.val c0 h.dec⟩, BinDecode.copy_cost b A⟩

/-- **Every decoder with binary entries has a binary entry decoding**: if every value of the
decoder is `c₀ (X + iY)` for two `b'`-bit two's complement words, `b' > 0`, `c₀ > 0`, the
lookup-table decoding of these words, with at most `2^{2b} · 2b' (4b + 1)` gates on
`2b + 2b' + A` wires, `A ≥ 2b - 1`, is a binary entry decoding. -/
theorem exists_binaryEntryDecoding {X : Type*} {N s k b b' A : ℕ}
    (D : GeneralSparseAccess.QData X N s k b) (c0 : ℝ) (hb : 0 < b') (hc0 : 0 < c0)
    (hA : 2 * b ≤ A + 1) (h : ∀ w, ∃ z : Cfg (VW b'), D.val w = (c0 : ℂ) * gauss z) :
    ∃ dc : BinDecode b b' A, BinaryEntryDecoding D dc c0 ∧
      dc.cost ≤ 2 ^ (2 * b) * (2 * b') * (4 * b + 1) + (2 * b + 2 * b' + A) := by
  obtain ⟨dc, hdc, hcost⟩ := GeneralDecoderODE.exists_table_exact hA D.val c0 h
  exact ⟨dc, ⟨hb, hc0, hdc⟩, hcost⟩

/-- The qubits of the register of the constant-coefficient decoder solver. -/
abbrev odeQubitsD (q : GPub) {b A : ℕ} (_dc : BinDecode b q.b A) (Zs : Type) [Fintype Zs] : ℕ :=
  Fintype.card (GeneralDecoderODE.GPubI.regI q (GeneralSparseAccess.AW q.k q.b ⊕ DW b q.b A) Zs)

/-- The qubits of the register of the time-dependent decoder solver. -/
abbrev odeQubitsTD (q : GPubT) {b A : ℕ} (_dc : BinDecode b q.b A) (Zs : Type) [Fintype Zs] :
    ℕ :=
  Fintype.card (GeneralDecoderODE.GPubTI.regTI q (GeneralSparseAccess.AW q.k q.b ⊕ DW b q.b A) Zs)

/-! ### Theorem `ode:thm:gates` with binary entry decoding, constant coefficients -/

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:gates` for sparse access of general size with binary entry decoding,
constant coefficients**. See the module docstring. With `C = 10²³`: for
the general sparse access `D` (`2^{k-1} < N ≤ 2^k`) with a decoder that has an exact binary entry
decoding `dc` of its stored words into `b'`-bit components, `b' ≤ b_data`, public parameters of at
most `b_data` bits, every `T ≥ 0`, `ḡ`, `0 < ε ≤ 1/2` and valid source circuits calling the
supplied oracles, the protocol `nprotocol (prepD (odePubG …) N dc srcC) ḡ` (fixed before the instance) has
valid trials, at most `C ḡ [q ((𝔟+1)³ + cost dc) + G_src + A_src]` elementary gates in every
history, at most `C (𝔟+1)³ + C A_src + C wires dc` qubits, at most `C ḡ q` calls of each supplied
matrix oracle (none if `T = 0` or `η_H + η_D = 0`) besides `C ḡ` times the calls inside the source
circuits, and on every admissible instance with source circuits within `ν = ε/(10⁴ ḡ)` of the
controlled source preparations: success at least `2/3`, conditional output within trace distance
`ε` of the normalised solution of `x' = -A x + b` on the index register (marker clean), and every
successful trial within `ε` of it up to a global phase. Formal restriction:
`formal_nondegenerate`. The finite-gate-set bound with `G_src` entering linearly is a separate
result for the binary format (`N = 2^{k_x}`, `T > 0`, `η_H + η_D > 0`):
`GateSelective.binary_ode_budget_sel`. -/
theorem ode_thm_gates_decoder :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b b' A : ℕ} (D : GeneralSparseAccess.QData X N s k b)
        (dc : BinDecode b b' A) (bd : ℕ) (c0 etaH etaD T gbar ε r₀ rb : ℝ),
        2 ^ k < 2 * N → BinaryEntryDecoding D dc c0 → comp_bits b' bd [c0, T, etaH, etaD] →
        ∀ (hnd : formal_nondegenerate gbar (r₀ + T * rb))
        {Zs : Type} [Fintype Zs] [DecidableEq Zs]
        (srcC : Bool → List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)),
        (∀ c, ∀ i ∈ srcC c, i.Valid) →
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 → 0 ≤ r₀ → 0 ≤ rb →
        (∀ j, ∀ i ∈ trialN (prepD (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc
          srcC) j, i.Valid) ∧
        ((nprotocol (prepD (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc srcC)
            gbar hnd.1).worstCost wGateN : ℝ) ≤
          C * gbar * (odeShape s T etaH etaD gbar ε *
              ((bitB bd N 0 0 (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 + dc.cost) +
            ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ∧
        (odeQubitsD (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) dc Zs : ℝ) ≤
          C * (bitB bd N 0 0 (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
            C * Fintype.card Zs + C * dc.wires ∧
        (∀ c : Query → Bool,
          ((nprotocol (prepD (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc srcC)
            gbar hnd.1).worstCost (wCallN c) : ℝ) ≤
          (if T = 0 ∨ etaH + etaD = 0 then 0 else
            C * gbar * odeShape s T etaH etaD gbar ε *
              ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
                (if c Query.value then 1 else 0))) +
          C * gbar * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true))) ∧
        ∀ x : X,
          (∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2) →
          (∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2) →
          (∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) →
          (∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) →
          (∀ w : EuclideanSpace ℂ (Fin N), 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
            (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re) →
          ∀ (Jsrc : Bool → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) (x0 v : Reg (Fin k) ℂ) (ζs : ℝ),
          (∀ c, OracleCircuit.IsUnitary (Jsrc c)) → 0 ≤ ζs →
          (∀ c, ApproxOn CleanX (nrun (D.prims (R := ℂ) x) (srcC c))
            (liftB (srcIdeal c (Jsrc c))) ζs) →
          ζs ≤ ImprovedODEQueryBudget.precision gbar ε →
          ‖x0‖ = r₀ → ‖v‖ = rb →
          (x0 ≠ 0 → Jsrc false (seedV (S := Fin k)) = ODEStateNormalization.unitDirection x0) →
          (v ≠ 0 → Jsrc true (seedV (S := Fin k)) = ODEStateNormalization.unitDirection v) →
          ODEConstantForcing.solution (-padLift D x) x0 v T ≠ 0 →
          r₀ + T * rb ≤ gbar * ‖ODEConstantForcing.solution (-padLift D x) x0 v T‖ →
          HeraldedOutput (nprotocol (prepD (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb)
              N dc srcC) gbar hnd.1) (D.prims (R := ℂ) x)
            (ODEStateNormalization.unitDirection
              (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))
                (ODEConstantForcing.solution (-padLift D x) x0 v T))) ε ∧
          ∀ j : ℕ, ((goodN (S := Fin (k + 1)))†) (nrun (D.prims (R := ℂ) x)
              (trialN (prepD (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc srcC) j)
              sN) ≠ 0 →
            ∃ ω : ℂ, ‖ω‖ = 1 ∧
              ‖ω • ODEStateNormalization.unitDirection (((goodN (S := Fin (k + 1)))†)
                  (nrun (D.prims (R := ℂ) x) (trialN (prepD (odePubG k s D.s_le_pow b' c0 etaH
                    etaD T gbar ε r₀ rb) N dc srcC) j) sN)) -
                ODEStateNormalization.unitDirection
                  (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))
                    (ODEConstantForcing.solution (-padLift D x) x0 v T))‖ ≤ ε := by
  refine ⟨10 ^ 23, by norm_num, ?_⟩
  intro X N s k b b' A D dc bd c0 etaH etaD T gbar ε r₀ rb hk hF hbits hnd Zs _ _ srcC hsrcV hH hD
    hT hε hε2 hr0 hrb
  obtain ⟨hbd, hc0b, hTb, hHb, hDb⟩ := hbits
  have hg := hnd.1
  have hB := hnd.2
  have hε1 : ε ≤ 1 := by linarith
  have hg0 : 0 ≤ gbar := by linarith
  set q := odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb with hqdef
  have hqp : q.pub = odePub (k + 1) (sbP s) ((sbP_le D.s_le_pow).trans (Nat.le_succ k)) b' c0
      etaH etaD T gbar ε r₀ rb := rfl
  have hq : BPublicOK0 q.pub := by
    rw [hqp]
    exact odePub_ok _ hF.hb hF.hc0 hH hD hT hg hε hε2 hr0 hrb hB
  have hγ := odePub_gamma hqp hF.hb hbd
  obtain ⟨hζ, hζs⟩ := odePub_zeta hqp hH hD hT hg hε hε1
  obtain ⟨hV, hWg0, hWq0, hWc0⟩ := GeneralDecoderODE.decoder_ode_budget bd q hq hγ hζ hbd hc0b
    hTb hHb hDb N dc srcC hsrcV
  have hWg : ((nprotocol (prepD q N dc srcC) gbar hnd.1).worstCost wGateN : ℝ) ≤
      10 ^ 20 * gbar * (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε *
        ((bitB bd (2 ^ (k + 1)) 0 0 (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε) gbar
          ε + 1) ^ 3 + dc.cost) + ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
          Fintype.card Zs) := hWg0
  have hWq : (odeQubitsD q dc Zs : ℝ) ≤ 3 * 10 ^ 11 * (bitB bd (2 ^ (k + 1)) 0 0
      (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
      2 * Fintype.card Zs + 2 * dc.wires := hWq0
  have hWc : ∀ c : Query → Bool, ((nprotocol (prepD q N dc srcC) gbar
      hnd.1).worstCost (wCallN c) : ℝ) ≤ (if T = 0 ∨ etaH + etaD = 0 then 0 else
        23592960 * gbar * GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0))) +
        40 * gbar * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true)) := hWc0
  -- the query shapes and the word budgets
  have hsP : (((sP s : ℕ) : ℝ)) ≤ 2 * (s : ℝ) := by
    have h' : ((sP s : ℕ) : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast (sP_lt D.slots_pos).le
    push_cast at h'
    exact h'
  have hQQ : GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε ≤
      2 * GateODEBudget.qOf s T etaH etaD gbar ε :=
    qOf_le_of_le (Nat.cast_nonneg _) hsP hT hH hD hg hε hε1
  have hQ1 : 1 ≤ GateODEBudget.qOf s T etaH etaD gbar ε :=
    GateRemarks.ODE.one_le_qOf hT hH hD hg hε hε1
  have hQ1' : 1 ≤ GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε :=
    GateRemarks.ODE.one_le_qOf hT hH hD hg hε hε1
  have hB0 : 0 ≤ bitB bd N 0 0 (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hB0' : 0 ≤ bitB bd (2 ^ (k + 1)) 0 0 (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε)
      gbar ε := bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hBB := bitB_pad_le (bd := bd) hk (by linarith) hQQ (by linarith) hg0 hε
  have hcube := cube_pad_le hB0 hB0' hBB
  have hY : 0 ≤ (bitB bd N 0 0 (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε + 1) ^ 3 := by
    positivity
  have hY' : 0 ≤ (bitB bd (2 ^ (k + 1)) 0 0 (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε)
      gbar ε + 1) ^ 3 := by positivity
  have hZ0 : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ dc.cost := Nat.cast_nonneg _
  rw [odeShape_eq]
  refine ⟨hV, ?_, ?_, ?_, ?_⟩
  · -- gates
    refine hWg.trans ?_
    generalize GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε = Q' at hQQ hQ1' hcube hY' ⊢
    generalize GateODEBudget.qOf s T etaH etaD gbar ε = Q at hQQ hQ1 hcube hB0 hY ⊢
    generalize (bitB bd (2 ^ (k + 1)) 0 0 Q' gbar ε + 1) ^ 3 = Y' at hcube hY' ⊢
    generalize (bitB bd N 0 0 Q gbar ε + 1) ^ 3 = Y at hcube hY ⊢
    generalize (dc.cost : ℝ) = Cst at hC0 ⊢
    have hG0 : (0 : ℝ) ≤ (nGatesN (srcC false) : ℝ) + nGatesN (srcC true) := by positivity
    have h1 : Q' * (Y' + Cst) ≤ 128 * (Q * (Y + Cst)) := by
      have h2 : Q' * (Y' + Cst) ≤ (2 * Q) * (Y' + Cst) :=
        mul_le_mul_of_nonneg_right hQQ (by linarith)
      have h3 : (2 * Q) * (Y' + Cst) ≤ (2 * Q) * (64 * Y + 64 * Cst) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith
    have hQY : 0 ≤ Q * (Y + Cst) := mul_nonneg (by linarith) (by linarith)
    have h4 : (10 : ℝ) ^ 20 * gbar * (Q' * (Y' + Cst) +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ≤
        10 ^ 20 * gbar * (128 * (Q * (Y + Cst)) + ((nGatesN (srcC false) : ℝ) +
          nGatesN (srcC true)) + Fintype.card Zs) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h5 : (10 : ℝ) ^ 20 * gbar * (128 * (Q * (Y + Cst)) + ((nGatesN (srcC false) : ℝ) +
          nGatesN (srcC true)) + Fintype.card Zs) ≤ 10 ^ 23 * gbar * (Q * (Y + Cst) +
          ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) := by
      have h6 : (10 : ℝ) ^ 20 * (128 * (Q * (Y + Cst)) + ((nGatesN (srcC false) : ℝ) +
          nGatesN (srcC true)) + Fintype.card Zs) ≤ 10 ^ 23 * (Q * (Y + Cst) +
          ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) := by
        nlinarith
      have := mul_le_mul_of_nonneg_left h6 hg0
      linarith
    linarith
  · -- qubits
    have h1 := mul_le_mul_of_nonneg_left hcube (by norm_num : (0 : ℝ) ≤ 3 * 10 ^ 11)
    have h2 : (2 : ℝ) * Fintype.card Zs ≤ 10 ^ 23 * Fintype.card Zs :=
      mul_le_mul_of_nonneg_right (by norm_num) hZ0
    have h2' : (2 : ℝ) * dc.wires ≤ 10 ^ 23 * dc.wires :=
      mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg _)
    have h3 : (3 * 10 ^ 11 : ℝ) * (64 * (bitB bd N 0 0 (GateODEBudget.qOf s T etaH etaD gbar ε)
        gbar ε + 1) ^ 3) ≤ 10 ^ 23 * (bitB bd N 0 0 (GateODEBudget.qOf s T etaH etaD gbar ε)
        gbar ε + 1) ^ 3 := by nlinarith
    linarith
  · -- calls
    intro c
    have hW := hWc c
    have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
        (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    have hS0 : (0 : ℝ) ≤ (nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true) := by positivity
    have hS : 40 * gbar * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true)) ≤
        10 ^ 23 * gbar * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hg0) hS0
    by_cases hz : T = 0 ∨ etaH + etaD = 0
    · rw [if_pos hz] at hW
      rw [if_pos hz]
      linarith
    · rw [if_neg hz] at hW
      rw [if_neg hz]
      generalize hId : ((if c Query.rowLocation then 1 else 0) +
          (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) : ℝ) = I
        at hI0 hW ⊢
      generalize GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε = Q' at hQQ hW
      have h1 : 23592960 * gbar * Q' * I ≤ 10 ^ 23 * gbar * GateODEBudget.qOf s T etaH etaD gbar ε *
          I := by
        have h2 : Q' * I ≤ (2 * GateODEBudget.qOf s T etaH etaD gbar ε) * I :=
          mul_le_mul_of_nonneg_right hQQ hI0
        have h3 : 0 ≤ GateODEBudget.qOf s T etaH etaD gbar ε * I :=
          mul_nonneg (by linarith) hI0
        have h4 : 23592960 * (Q' * I) ≤ 10 ^ 23 * (GateODEBudget.qOf s T etaH etaD gbar ε * I) := by
          nlinarith
        have h5 := mul_le_mul_of_nonneg_left h4 hg0
        nlinarith
      linarith
  · -- the guarantees
    intro x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs0 hsrc hacc hx0 hv hpx hpv hne hBud
    have hγ' : ¬ BZeroCase q.pub → q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD q.g q.ε := by
      intro hz
      have h := hγ
      rw [if_neg hz] at h
      exact h
    -- the public data is passed literally (not as the local definition `q`), so that the
    -- outcome has the types of the statement and the final unification is syntactic
    have o := (GeneralDecoderODE.decoder_ode_outcome
      (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) hq hγ' D dc hF.exact srcC hsrcV x
      hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs0 hsrc (hζs ζs hacc) hx0 hv hpx hpv hne
      hBud).mono (β' := ε) (by
        show ε / 250 ≤ ε
        linarith)
    rw [markEmb_eq_cleanAlong] at o
    exact ⟨⟨o.success_two_thirds, o.output_density, o.conditional_error⟩, o.trial_direction⟩

/-! ### Theorem `ode:thm:gates` with binary entry decoding, time-dependent coefficients -/

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:gates` for sparse access of general size with binary entry decoding,
time-dependent coefficients, special case under the package's uniform-mesh conditions**. See the
module docstring. With `C = 10²⁴`: for the time-indexed general sparse access `D`
(`2^{k-1} < N ≤ 2^k`) with a decoder that has an exact binary entry decoding `dc` of its stored
words into `b'`-bit components, `b' ≤ b_data`, on a mesh `M = 2^m` at least the coarsest admissible
one of the padded problem of the decoded data, public parameters of at most `b_data` bits, every
`T ≥ 0`, `ḡ ≥ 1`, `0 < ε ≤ 1/2` and valid loading and
weight-preparation circuits calling the coherent sampled-time supplied oracles, the protocol
`nprotocol (prepTD (odePubTG …) N dc loadC wpC) (2ḡ)` (fixed before the instance) has valid
trials, at most `C ḡ [q ((𝔟+1)³ + cost dc) + G_src + A_src]` elementary gates in every history,
at most `C (𝔟+1)³ + C A_src + C wires dc` qubits, at most `C ḡ q` calls of each supplied matrix
oracle (none if `T = 0` or `η_H + η_D = 0`) besides `C ḡ` times the calls inside the source
circuits, and on every instance with the uniform-mesh conditions on the index register and source
circuits within `ν = ε/(10⁴ ḡ)`: success at least `2/3`, conditional output within trace distance
`ε` of `x(T)/‖x(T)‖` on the index register (marker clean), and every successful trial within `ε` of
it up to a global phase. Formal restrictions: `formal_gbarOne`, `formal_uniformMeshG`. The
finite-gate-set bound with `G_src` entering linearly is a separate result for the binary format
(`N = 2^{k_x}`, `T > 0`, `η_H + η_D > 0`): `GateSelective.binary_ode_time_budget_sel`. -/
theorem ode_thm_gates_time_decoder :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b b' A : ℕ} (bd : ℕ) (c0 etaH etaD T gbar ε : ℝ) (m : ℕ)
        (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b) (dc : BinDecode b b' A),
        odeMeshG k s D.s_le_pow b' c0 etaH etaD T gbar ε ≤ m →
        2 ^ k < 2 * N → BinaryEntryDecoding D dc c0 → comp_bits b' bd [c0, T, etaH, etaD] →
        ∀ (hg : formal_gbarOne gbar) {Zs : Type} [Fintype Zs] [DecidableEq Zs]
          (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
          (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)),
          (∀ i ∈ loadC, i.Valid) → (∀ i ∈ wpC, i.Valid) →
          0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 →
          (∀ j, ∀ i ∈ trialN (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc
            loadC wpC) j, i.Valid) ∧
          ((nprotocol (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc loadC wpC)
              (2 * gbar) (one_le_two_mul hg)).worstCost wGateN : ℝ) ≤
            C * gbar * (odeShape s T etaH etaD gbar ε *
                ((bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
                  dc.cost) +
              ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
          (odeQubitsTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) dc Zs : ℝ) ≤
            C * (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
              C * Fintype.card Zs + C * dc.wires ∧
          (∀ c : Query → Bool,
            ((nprotocol (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc loadC
              wpC) (2 * gbar) (one_le_two_mul hg)).worstCost (wCallN c) : ℝ) ≤
            (if T = 0 ∨ etaH + etaD = 0 then 0 else
              C * gbar * odeShape s T etaH etaD gbar ε *
                ((if c Query.rowLocation then 1 else 0) +
                  (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))) +
            C * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
          ∀ x : X,
            (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaH ^ 2) →
            (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaH ^ 2) →
            (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaD ^ 2) →
            (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaD ^ 2) →
            ∀ (Jl : Bool × (Fin m → Bool) → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
              (Wp : Matrix (Cfg (Fin (m + 1))) (Cfg (Fin (m + 1))) ℂ)
              (G : ℝ → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) (bf xs : ℝ → Reg (Fin k) ℂ)
              (bs : ℕ → Reg (Fin k) ℂ) (βG δG βb δb bmax ζs : ℝ),
            0 ≤ ζs →
            ApproxOn CleanX (nrun (primsTG D x) loadC) (liftB (loadIdeal Jl)) ζs →
            ApproxOn CleanX (nrun (primsTG D x) wpC) (liftB (matOp Wp)) ζs →
            ζs ≤ ImprovedODEQueryBudget.precision gbar ε →
            formal_uniformMeshG (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) D x Jl Wp G
              bf xs bs βG δG βb δb bmax →
            HeraldedOutput (nprotocol (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m)
                N dc loadC wpC) (2 * gbar) (one_le_two_mul hg))
              (primsTG D x) (ODEStateNormalization.unitDirection
                (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (xs T))) ε ∧
            ∀ j : ℕ, ((goodN)†) (nrun (primsTG D x)
                (trialN (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc loadC
                  wpC) j) sN) ≠ 0 →
              ∃ ω : ℂ, ‖ω‖ = 1 ∧
                ‖ω • ODEStateNormalization.unitDirection (((goodN)†)
                    (nrun (primsTG D x) (trialN (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T
                      gbar ε m) N dc loadC wpC) j) sN)) -
                  ODEStateNormalization.unitDirection
                    (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (xs T))‖ ≤ ε := by
  refine ⟨10 ^ 24, by norm_num, ?_⟩
  intro X N s k b b' A bd c0 etaH etaD T gbar ε m D dc hm hk hF hbits hg Zs _ _ loadC wpC hloadV
    hwpV hH hD hT hε hε2
  obtain ⟨hbd, hc0b, hTb, hHb, hDb⟩ := hbits
  have hg1 : 1 ≤ gbar := hg
  have hε1 : ε ≤ 1 := by linarith
  have hg0 : 0 ≤ gbar := by linarith
  set q := odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m with hqdef
  have hqp : q.pub = odePubT (k + 1) (sbP s) ((sbP_le D.s_le_pow).trans (Nat.le_succ k)) b' c0
      etaH etaD T gbar ε m := rfl
  have hq : BTPublicOK0 q.pub := by
    rw [hqp]
    exact odePubT_ok _ hF.hb hF.hc0 hH hD hT hg hε hε2 hm
  have hγ := odePubT_gamma hqp hF.hb hbd
  obtain ⟨hζ, hζs⟩ := odePubT_zeta hqp hH hD hT hg hε hε2
  obtain ⟨hV, hWg0, hWq0, hWc0⟩ := GeneralDecoderODE.decoder_time_budget bd q hq hγ hζ hbd hc0b
    hTb hHb hDb N dc loadC hloadV wpC hwpV
  have hWg : ((nprotocol (prepTD q N dc loadC wpC) (2 * gbar)
      (one_le_two_mul hg)).worstCost wGateN : ℝ) ≤
      2 * 10 ^ 20 * gbar * (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) *
        ((bitB bd (2 ^ (k + 1)) (2 ^ m) (2 ^ m)
          (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2)) gbar ε + 1) ^ 3 +
            dc.cost) +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) := hWg0
  have hWq : (odeQubitsTD q dc Zs : ℝ) ≤ 3 * 10 ^ 11 * (bitB bd (2 ^ (k + 1)) (2 ^ m) (2 ^ m)
      (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2)) gbar ε + 1) ^ 3 +
      2 * Fintype.card Zs + 2 * dc.wires := hWq0
  have hWc : ∀ c : Query → Bool, ((nprotocol (prepTD q N dc loadC wpC) (2 * gbar)
      (one_le_two_mul hg)).worstCost (wCallN c) : ℝ) ≤ (if T = 0 ∨ etaH + etaD = 0 then 0 else
        47185920 * gbar * GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0))) +
        80 * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) := hWc0
  -- the query shapes and the word budgets
  have hsP : (((sP s : ℕ) : ℝ)) ≤ 2 * (s : ℝ) := by
    have h' : ((sP s : ℕ) : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast (sP_lt D.slots_pos).le
    push_cast at h'
    exact h'
  have hQQ1 : GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε ≤
      2 * GateODEBudget.qOf s T etaH etaD gbar ε :=
    qOf_le_of_le (Nat.cast_nonneg _) hsP hT hH hD hg hε hε1
  have hQQ2 : GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) ≤
      3 * GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε :=
    qOf_two_le0 (Nat.cast_nonneg _) hT hH hD hg hε hε1
  have hQQ : GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) ≤
      6 * GateODEBudget.qOf s T etaH etaD gbar ε := by linarith
  have hQ1 : 1 ≤ GateODEBudget.qOf s T etaH etaD gbar ε :=
    GateRemarks.ODE.one_le_qOf hT hH hD hg hε hε1
  have hQ1' : 1 ≤ GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) :=
    GateRemarks.ODE.one_le_qOf hT hH hD (by linarith) (by linarith) (by linarith)
  have hB0 : 0 ≤ bitB bd N (2 ^ m) (2 ^ m) (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hB0' : 0 ≤ bitB bd (2 ^ (k + 1)) (2 ^ m) (2 ^ m)
      (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2)) gbar ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hBB := bitB_padT_le (bd := bd) (M := 2 ^ m) hk (by linarith) hQQ (by linarith) hg0 hε hε1
  have hcube := cube_padT_le hB0 hB0' hBB
  have hY : 0 ≤ (bitB bd N (2 ^ m) (2 ^ m) (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε + 1) ^ 3 :=
    by positivity
  have hY' : 0 ≤ (bitB bd (2 ^ (k + 1)) (2 ^ m) (2 ^ m)
      (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2)) gbar ε + 1) ^ 3 := by
    positivity
  have hZ0 : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ dc.cost := Nat.cast_nonneg _
  rw [odeShape_eq]
  refine ⟨hV, ?_, ?_, ?_, ?_⟩
  · -- gates
    refine hWg.trans ?_
    generalize GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) = Q'
      at hQQ hQ1' hcube hY' ⊢
    generalize GateODEBudget.qOf s T etaH etaD gbar ε = Q at hQQ hQ1 hcube hB0 hY ⊢
    generalize (bitB bd (2 ^ (k + 1)) (2 ^ m) (2 ^ m) Q' gbar ε + 1) ^ 3 = Y' at hcube hY' ⊢
    generalize (bitB bd N (2 ^ m) (2 ^ m) Q gbar ε + 1) ^ 3 = Y at hcube hY ⊢
    generalize (dc.cost : ℝ) = Cst at hC0 ⊢
    have hG0 : (0 : ℝ) ≤ (nGatesN loadC : ℝ) + 2 * nGatesN wpC := by positivity
    have h1 : Q' * (Y' + Cst) ≤ 1296 * (Q * (Y + Cst)) := by
      have h2 : Q' * (Y' + Cst) ≤ (6 * Q) * (Y' + Cst) :=
        mul_le_mul_of_nonneg_right hQQ (by linarith)
      have h3 : (6 * Q) * (Y' + Cst) ≤ (6 * Q) * (216 * Y + 216 * Cst) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith
    have hQY : 0 ≤ Q * (Y + Cst) := mul_nonneg (by linarith) (by linarith)
    have h4 : (2 * 10 ^ 20 : ℝ) * gbar * (Q' * (Y' + Cst) +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ≤
        2 * 10 ^ 20 * gbar * (1296 * (Q * (Y + Cst)) + ((nGatesN loadC : ℝ) +
          2 * nGatesN wpC) + Fintype.card Zs) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h5 : (2 * 10 ^ 20 : ℝ) * gbar * (1296 * (Q * (Y + Cst)) + ((nGatesN loadC : ℝ) +
          2 * nGatesN wpC) + Fintype.card Zs) ≤ 10 ^ 24 * gbar * (Q * (Y + Cst) +
          ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) := by
      have h6 : (2 * 10 ^ 20 : ℝ) * (1296 * (Q * (Y + Cst)) + ((nGatesN loadC : ℝ) +
          2 * nGatesN wpC) + Fintype.card Zs) ≤ 10 ^ 24 * (Q * (Y + Cst) +
          ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) := by
        nlinarith
      have := mul_le_mul_of_nonneg_left h6 hg0
      linarith
    exact h4.trans h5
  · -- qubits
    have h1 := mul_le_mul_of_nonneg_left hcube (by norm_num : (0 : ℝ) ≤ 3 * 10 ^ 11)
    have h2 : (2 : ℝ) * Fintype.card Zs ≤ 10 ^ 24 * Fintype.card Zs :=
      mul_le_mul_of_nonneg_right (by norm_num) hZ0
    have h2' : (2 : ℝ) * dc.wires ≤ 10 ^ 24 * dc.wires :=
      mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg _)
    have h3 : (3 * 10 ^ 11 : ℝ) * (216 * (bitB bd N (2 ^ m) (2 ^ m)
        (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε + 1) ^ 3) ≤ 10 ^ 24 * (bitB bd N (2 ^ m)
          (2 ^ m) (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε + 1) ^ 3 := by nlinarith
    linarith
  · -- calls
    intro c
    have hW := hWc c
    have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
        (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    have hS0 : (0 : ℝ) ≤ (nCallsN c loadC : ℝ) + 2 * nCallsN c wpC := by positivity
    have hS : 80 * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) ≤
        10 ^ 24 * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hg0) hS0
    by_cases hz : T = 0 ∨ etaH + etaD = 0
    · rw [if_pos hz] at hW
      rw [if_pos hz]
      exact hW.trans (add_le_add le_rfl hS)
    · rw [if_neg hz] at hW
      rw [if_neg hz]
      generalize hId : ((if c Query.rowLocation then 1 else 0) +
          (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) : ℝ) = I
        at hI0 hW ⊢
      generalize GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) = Q' at hQQ hW
      have h1 : 47185920 * gbar * Q' * I ≤ 10 ^ 24 * gbar * GateODEBudget.qOf s T etaH etaD gbar ε *
          I := by
        have h2 : Q' * I ≤ (6 * GateODEBudget.qOf s T etaH etaD gbar ε) * I :=
          mul_le_mul_of_nonneg_right hQQ hI0
        have h3 : 0 ≤ GateODEBudget.qOf s T etaH etaD gbar ε * I :=
          mul_nonneg (by linarith) hI0
        have h4 : 47185920 * (Q' * I) ≤ 10 ^ 24 * (GateODEBudget.qOf s T etaH etaD gbar ε * I) := by
          nlinarith
        have h5 := mul_le_mul_of_nonneg_left h4 hg0
        nlinarith
      exact hW.trans (add_le_add h1 hS)
  · -- the guarantees
    intro x hrH hcH hrD hcD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs0 hload hwp hacc hR
    have hγ' : ¬ BTZeroCase q.pub →
        q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := by
      intro hz
      have h := hγ
      rw [if_neg hz] at h
      exact h
    -- the public data is passed literally (not as the local definition `q`), so that the
    -- outcome has the types of the statement and the final unification is syntactic
    have o := (GeneralDecoderODE.decoder_time_outcome
      (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) hq hγ' D dc hF.exact loadC hloadV wpC
      hwpV x hrH hcH hrD hcD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs0 hload hwp
      (hζs ζs hacc) hR).mono (β' := ε) (by
        show ε / 100 ≤ ε
        linarith)
    rw [markEmb_eq_cleanAlong] at o
    exact ⟨⟨o.success_two_thirds, o.output_density, o.conditional_error⟩, o.trial_direction⟩

end

end ManuscriptConformance
