import ManuscriptConformance.GatePropsSelective

/-!
# Conformance: `gate:prop:signed` for a general known success projection and sign reflection

Section `gate:sec:signed` allows any known success projection `Π` and sign reflection `Z` of the
factor (`SignedFactorSimulation.Known`: the initialised-input isometry `E`, `Π`, `Z`); the package's
signed circuits use the designated-flag interface `wKnown` (`Π` and `Z` read off two flag qubits
`f ≠ z` of the ancillas). Item B3 asks that a designated-qubit encoding construct and charge its
basis conversion. Here the conversion is a known unitary `C` of the ancilla space with
`C E = U_J ι₀`, `C Π C† = [wire f = 1]` and `C Z C† = (-1)^{wire z}` (`Converts`); the signed circuit
runs with the converted boundary `U_J` (so `C` enters every boundary call) and the converted
factor `C U_B C†` (so `C` and `C†` enter every factor call), and the Hamiltonian is unchanged:

* `factor_conj`, `Cop_conj`, `Dop_conj`, `ham_conj`: conjugating the interface and the factor by a
  unitary leaves the signed compression `C = B† Z B`, the weight `D = B† B` and the Hamiltonian
  `λ C` unchanged;
* `Converts.ham`, `Converts.Dop`: the designated-flag interface of the converted boundary, with the
  converted factor, has the Hamiltonian and the weight of the general interface;
* `gate_prop_signed_known`: Proposition `gate:prop:signed` (exact gates) for a general known `Π`,
  `Z` with a conversion: the signed circuit of the converted boundary and factor simulates
  `exp(-i t λ C)` of the general interface, with the counts of `signed_gate_simulation`;
* `gate_prop_signed_known_sel`: the same over a finite gate set, from `gate_prop_signed_sel`, for a
  supplied factor circuit implementing the converted factor `C U_B C†` and the gates `UJg` of the
  converted boundary: the conversion is charged inside the factor budget (`|fc|`) and the boundary
  gates (`C_J = |UJg|`);
* `placeC`, `nrun_placeC`, `convFactor`, `convFactor_approx`, `nGatesN_convFactor`,
  `nCallsN_convFactor`, `convFactor_valid`, `convFactor_gates`: for conversion gates `Cg` on the
  `a` ancillas and the system (operator `U_C`), the converted factor circuit
  `U_C† · fc · U_C` with the conversion gates placed on the factor wires past the flag: within `ξ`
  of `U_C U U_C† ⊗ I_flag` on clean work wires when `fc` is within `ξ` of `U ⊗ I_flag`
  (`approxOn_sandwich`), with `|fc| + 2 |Cg|` gates and exactly the calls of `fc`;
* `UJop_append`, `converts_of_gates`: gates `Eg` preparing the initialised input on clean ancillas
  (`U_E ι₀ = E`) and conversion gates `Cg` with `U_C Π U_C† = [wire f = 1]`,
  `U_C Z U_C† = (-1)^{wire z}` give a conversion `U_C` with the boundary gates `Eg ++ Cg`;
* `gate_prop_signed_known_conv`: the finite-set proposition for a general known `Π`, `Z` with the
  conversion built from these gates and charged: the converted factor circuit retains
  `n_P (|fc| + 2 |Cg|)` gates, the boundary has `C_J = |Eg| + |Cg|` gates, the calls are those of
  `n_P` copies of `fc`, and the full output is within `ε + n_P ξ + δ` of `exp(-i t λ C_K)`.

Scope: the preparation gates `Eg` and the conversion gates `Cg` are supplied with their exact
promises; their synthesis from a description of `Π` and `Z` (for example, computing a predicate
into a designated flag qubit, which needs a further ancilla when the rank of `Π` is not half the
dimension) is not formalised. The conversion gates are retained inside the factor circuit, so they
are required to be gates of `𝒢`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8192

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim SparseHamiltonian.GateNative
  SparseHamiltonian.GateSynth SparseHamiltonian.GateSelective GateOptimalPrecision
open SparseHamiltonian.GateSynthTrials (AdjClosed)
open SignedFactorSimulation (Known)
open SignedFactorSimulation (rb)
open scoped InnerProduct InnerProductSpace

/-! ### Conjugating the factor interface -/

section Conj

variable {P W : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- The factor of the conjugated interface is the conjugated factor. -/
theorem factor_conj (K K' : Known P W) (C : W →L[ℂ] W) (hC : C† ∘L C = 1)
    (hE : K'.E = C ∘L K.E) (hP : K'.proj = C ∘L K.proj ∘L C†) (U : W →L[ℂ] W) :
    K'.factor (C ∘L U ∘L C†) = C ∘L K.factor U := by
  unfold Known.factor
  rw [hE, hP]
  calc (C ∘L K.proj ∘L C†) ∘L (C ∘L U ∘L C†) ∘L C ∘L K.E
      = C ∘L K.proj ∘L (C† ∘L C) ∘L U ∘L (C† ∘L C) ∘L K.E := by
        simp only [comp_assoc]
    _ = C ∘L K.proj ∘L U ∘L K.E := by
        rw [hC]
        simp only [one_def, id_comp]

/-- **The signed compression is invariant under conjugation.** -/
theorem Cop_conj (K K' : Known P W) (C : W →L[ℂ] W) (hC : C† ∘L C = 1)
    (hE : K'.E = C ∘L K.E) (hP : K'.proj = C ∘L K.proj ∘L C†) (hZ : K'.Z = C ∘L K.Z ∘L C†)
    (U : W →L[ℂ] W) : K'.Cop (C ∘L U ∘L C†) = K.Cop U := by
  unfold Known.Cop
  rw [factor_conj K K' C hC hE hP U, hZ, adjoint_comp]
  calc ((K.factor U)† ∘L C†) ∘L (C ∘L K.Z ∘L C†) ∘L C ∘L K.factor U
      = (K.factor U)† ∘L (C† ∘L C) ∘L K.Z ∘L (C† ∘L C) ∘L K.factor U := by
        simp only [comp_assoc]
    _ = (K.factor U)† ∘L K.Z ∘L K.factor U := by
        rw [hC]
        simp only [one_def, id_comp]

/-- **The successful weight is invariant under conjugation.** -/
theorem Dop_conj (K K' : Known P W) (C : W →L[ℂ] W) (hC : C† ∘L C = 1)
    (hE : K'.E = C ∘L K.E) (hP : K'.proj = C ∘L K.proj ∘L C†) (U : W →L[ℂ] W) :
    K'.Dop (C ∘L U ∘L C†) = K.Dop U := by
  unfold Known.Dop
  rw [factor_conj K K' C hC hE hP U, adjoint_comp]
  calc ((K.factor U)† ∘L C†) ∘L C ∘L K.factor U
      = (K.factor U)† ∘L (C† ∘L C) ∘L K.factor U := by
        simp only [comp_assoc]
    _ = (K.factor U)† ∘L K.factor U := by
        rw [hC]
        simp only [one_def, id_comp]

/-- **The Hamiltonian `λ C` is invariant under conjugation.** -/
theorem ham_conj (K K' : Known P W) (C : W →L[ℂ] W) (hC : C† ∘L C = 1)
    (hE : K'.E = C ∘L K.E) (hP : K'.proj = C ∘L K.proj ∘L C†) (hZ : K'.Z = C ∘L K.Z ∘L C†)
    (lam : ℝ) (U : W →L[ℂ] W) : K'.ham lam (C ∘L U ∘L C†) = K.ham lam U := by
  unfold Known.ham
  rw [Cop_conj K K' C hC hE hP hZ U]

end Conj

/-! ### The designated-flag interface of a conversion -/

section Converts

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
variable {a : ℕ}

/-- **A basis conversion to designated flag qubits**: a unitary `C` of the ancilla space taking the
initialised input to `U_J ι₀`, the success projection to `[wire f = 1]` and the sign reflection to
`(-1)^{wire z}`. -/
structure Converts (K : Known P (Anc a P)) (C UJ : Anc a P →L[ℂ] Anc a P) (f z : Fin a) :
    Prop where
  unitary : IsUnitary C
  boundary : C ∘L K.E = UJ ∘L iota0
  proj : C ∘L K.proj ∘L C† = dg (projD f)
  sign : C ∘L K.Z ∘L C† = dg (signD z)

theorem Converts.adj_comp {K : Known P (Anc a P)} {C UJ : Anc a P →L[ℂ] Anc a P} {f z : Fin a}
    (h : Converts K C UJ f z) : C† ∘L C = 1 := by
  have := h.unitary.1
  rwa [star_eq_adjoint, mul_def] at this

/-- **The designated-flag interface of the converted boundary has the Hamiltonian of the general
interface** for the converted factor `C U C†`. -/
theorem Converts.ham {K : Known P (Anc a P)} {C UJ : Anc a P →L[ℂ] Anc a P} {f z : Fin a}
    (h : Converts K C UJ f z) (hUJ : IsUnitary UJ) (lam : ℝ) (U : Anc a P →L[ℂ] Anc a P) :
    sgHam (P := P) UJ hUJ f z lam (C ∘L U ∘L C†) = K.ham lam U :=
  ham_conj K (wKnown UJ (unitary_adj_comp hUJ) f z) C h.adj_comp h.boundary.symm h.proj.symm
    h.sign.symm lam U

/-- The designated-flag interface of the converted boundary has the successful weight of the
general interface. -/
theorem Converts.Dop {K : Known P (Anc a P)} {C UJ : Anc a P →L[ℂ] Anc a P} {f z : Fin a}
    (h : Converts K C UJ f z) (hUJ : IsUnitary UJ) (U : Anc a P →L[ℂ] Anc a P) :
    (wKnown UJ (unitary_adj_comp hUJ) f z).Dop (C ∘L U ∘L C†) = K.Dop U :=
  Dop_conj K (wKnown UJ (unitary_adj_comp hUJ) f z) C h.adj_comp h.boundary.symm h.proj.symm U

/-- **Proposition `gate:prop:signed` (exact gates) for a general known success projection and
sign reflection.** For a general factor interface `K` with a conversion `C` to designated flag
qubits `f ≠ z` (`Converts`), the signed circuit of `signed_gate_simulation` run with the converted
boundary `U_J` and the converted factor `C U C†` is valid, makes `n_P` factor calls with the bound
of `signed_gate_simulation` and as many boundary calls, has the stated known gates and wires, and
its full output is within `ε` of `exp(-i t λ C_K)` for the signed compression `C_K` of the general
interface, when its successful weight is at most `δ`. -/
theorem gate_prop_signed_known [FiniteDimensional ℂ P] (K : Known P (Anc a P))
    (C UJ U : Anc a P →L[ℂ] Anc a P) (hUJ : IsUnitary UJ) (hU : IsUnitary U) {f z : Fin a}
    (hfz : f ≠ z) (hK : Converts K C UJ f z) {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hD : K.Dop U ≤ (δ : ℂ) • (1 : P →L[ℂ] P)) (t : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64) :
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
    ‖run (simSem (liftA UJ) (liftA (C ∘L U ∘L C†))) (sgCircuit a f z lam δ t ε) ∘L io -
        io ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) • K.ham lam U)‖ ≤ ε := by
  have hCu := hK.unitary
  have hU' : IsUnitary (C ∘L U ∘L C†) := by
    have h1 : IsUnitary (C ∘L U) := by
      rw [← mul_def]
      exact hCu.mul hU
    have h2 : IsUnitary (C†) := by
      simpa [star_eq_adjoint] using hCu.adjoint
    rw [← comp_assoc, ← mul_def]
    exact h1.mul h2
  have hD' : (wKnown UJ (unitary_adj_comp hUJ) f z).Dop (C ∘L U ∘L C†) ≤
      (δ : ℂ) • (1 : P →L[ℂ] P) := by
    rw [hK.Dop hUJ U]
    exact hD
  obtain ⟨hv, hpriv, hJn, hgates, hcard, herr, -, -⟩ :=
    signed_gate_simulation (P := P) UJ (C ∘L U ∘L C†) hUJ hU' hfz hlam hδ hδ1 hD' t hε hε1
  rw [hK.ham hUJ lam U] at herr
  exact ⟨hv, hpriv, hJn, hgates, hcard, herr⟩

end Converts

/-! ### Over a finite gate set -/

section KnownSel

variable {S Z Y J Xs : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y] [Fintype Xs] [DecidableEq Xs] {bT bP A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- **Proposition `gate:prop:signed` over a finite gate set for a general known success projection
and sign reflection.** For a general factor interface `K` with a conversion `C` to designated flag
qubits (`Converts`), the gates `UJg` of the converted boundary, and a supplied factor circuit over
`𝒢` within `ξ` of the converted factor `C U C† ⊗ I_flag` on clean work wires (so the conversion is
charged inside the factor circuit and the boundary gates): the conclusions of
`gate_prop_signed_sel`, with the full output within `ε + n_P ξ + δ` of `exp(-i t λ C_K)` for the
signed compression `C_K` of the general interface. -/
theorem gate_prop_signed_known_sel [FiniteDimensional ℂ R] (hS : Synthesis 𝒢 Xs L)
    (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀) {a : ℕ}
    (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (K : Known (Reg S R) (Anc a (Reg S R))) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJg : ∀ g ∈ UJg, GateOK 3 g) (C UJ U : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R))
    (hJ : UJop (R := R) UJg = UJ) (hUJ : IsUnitary UJ) (hU : IsUnitary U) {f z : Fin a}
    (hfz : f ≠ z) (hK : Converts K C UJ f z)
    (fc : List (NInstr (PWr Empty (Fin (a + 1) ⊕ S) Z bT bP A) Y J))
    (hfcV : ∀ i ∈ fc, i.Valid) (hfcG : ∀ g, NInstr.gate g ∈ fc → GateOf 𝒢 g) {ξ : ℝ}
    (hξ : 0 ≤ ξ)
    (hfc : ApproxOn CleanP (nrun prim fc)
      (uncIdeal (selOp (fun _ : Cfg Empty => liftA (C ∘L U ∘L C†)))) ξ)
    {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hD : K.Dop U ≤ (δ : ℂ) • (1 : Reg S R →L[ℂ] Reg S R))
    (t : ℝ) {ε δs : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) (hδs : 0 < δs) (hδs1 : δs ≤ 1) :
    (∀ i ∈ selSgOf hS δs UJg fc (sgCircuit a f z lam δ t ε), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ selSgOf hS δs UJg fc (sgCircuit a f z lam δ t ε) → GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (selSgOf hS δs UJg fc (sgCircuit a f z lam δ t ε)) =
      nPriv (sgCircuit a f z lam δ t ε) * nCallsN p fc) ∧
    ((nPriv (sgCircuit a f z lam δ t ε) : ℝ) ≤ (if sgB lam δ t ≤ ε then 0 else
      4 * 10 ^ 10 * (Real.sqrt (sgT lam t * sgB lam δ t) +
        Real.sqrt (sgT lam t * rb (sgB lam δ t) ε) + rb (sgB lam δ t) ε))) ∧
    knownG UJg.length (sgCircuit a f z lam δ t ε) ≤
      64 * 3 ^ 8 * ((sigN (sgQ lam δ t ε) (sgOrd lam δ t ε) + 1) *
        (a + sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε + sigR (sgQ lam δ t ε) (sgOrd lam δ t ε) +
          1)) + nPriv (sgCircuit a f z lam δ t ε) * (7 * UJg.length) ∧
    (nGatesN (selSgOf hS δs UJg fc (sgCircuit a f z lam δ t ε)) : ℝ) ≤
      (nPriv (sgCircuit a f z lam δ t ε) : ℝ) * nGatesN fc +
        (knownG UJg.length (sgCircuit a f z lam δ t ε) : ℝ) *
          (c₁ * Real.log (((knownG UJg.length (sgCircuit a f z lam δ t ε) : ℝ) + 1) / δs) +
            c₀ + 1) ∧
    Fintype.card (HW (SgWire a lam δ t ε) S Empty Z bT bP A ⊕ Xs) =
      2 * a + 3 * sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε +
        6 * sigR (sgQ lam δ t ε) (sgOrd lam δ t ε) + 5 + Fintype.card S +
          (Fintype.card Z + bT + bP + A + 3) + Fintype.card Xs ∧
    ‖nrun prim (selSgOf hS δs UJg fc (sgCircuit a f z lam δ t ε)) ∘L
        (cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • K.ham lam U)‖ ≤
      ε + (nPriv (sgCircuit a f z lam δ t ε) : ℝ) * ξ + δs := by
  have hCu := hK.unitary
  have hU' : IsUnitary (C ∘L U ∘L C†) := by
    have h1 : IsUnitary (C ∘L U) := by
      rw [← mul_def]
      exact hCu.mul hU
    have h2 : IsUnitary (C†) := by
      simpa [star_eq_adjoint] using hCu.adjoint
    rw [← comp_assoc, ← mul_def]
    exact h1.mul h2
  have hD' : (wKnown UJ (unitary_adj_comp hUJ) f z).Dop (C ∘L U ∘L C†) ≤
      (δ : ℂ) • (1 : Reg S R →L[ℂ] Reg S R) := by
    rw [hK.Dop hUJ U]
    exact hD
  have h := gate_prop_signed_sel hS hadj hc₀ hc₁ hL prim hprim UJg hUJg UJ (C ∘L U ∘L C†) hJ
    hUJ hU' fc hfcV hfcG hξ hfc hfz hlam hδ hδ1 hD' t hε hε1 hδs hδs1
  rw [hK.ham hUJ lam U] at h
  exact h

end KnownSel

/-! ### Conjugating an approximation -/

section Sandwich

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- Conjugating an approximation by unitaries (the inner one preserving the support) keeps its
error. -/
theorem approxOn_sandwich {S : Cfg W → Prop} {F O Uc Ui : Reg W Q →L[ℂ] Reg W Q} {ξ : ℝ}
    (hξ : 0 ≤ ξ) (hF : ApproxOn S F O ξ) (hUc : IsUnitary Uc) (hUi : IsUnitary Ui)
    (hpres : Preserves S Ui) : ApproxOn S (Uc ∘L (F ∘L Ui)) (Uc ∘L (O ∘L Ui)) ξ := by
  intro ψ hψ
  simp only [comp_apply]
  rw [← map_sub]
  calc ‖Uc (F (Ui ψ) - O (Ui ψ))‖ ≤ ‖F (Ui ψ) - O (Ui ψ)‖ := IsUnitary.norm_apply_le hUc _
    _ ≤ ξ * ‖Ui ψ‖ := hF _ (hpres ψ hψ)
    _ ≤ ξ * ‖ψ‖ := mul_le_mul_of_nonneg_left (IsUnitary.norm_apply_le hUi ψ) hξ

/-- `approxOn_sandwich` with the conjugated ideal named. -/
theorem approxOn_sandwich_eq {S : Cfg W → Prop} {F O Uc Ui T : Reg W Q →L[ℂ] Reg W Q} {ξ : ℝ}
    (hξ : 0 ≤ ξ) (hF : ApproxOn S F O ξ) (hUc : IsUnitary Uc) (hUi : IsUnitary Ui)
    (hpres : Preserves S Ui) (hT : Uc ∘L (O ∘L Ui) = T) : ApproxOn S (Uc ∘L (F ∘L Ui)) T ξ := by
  subst hT
  exact approxOn_sandwich hξ hF hUc hUi hpres

end Sandwich

/-! ### The converted factor circuit -/

section ConvCircuit

variable {S Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y] {bT bP A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {a : ℕ}

/-- The wires of the factor register inside the private register. -/
def ePR (a : ℕ) : (Fin (a + 1) ⊕ S) ↪ PWr Empty (Fin (a + 1) ⊕ S) Z bT bP A :=
  ⟨fun p => selPR (Sum.inr p), fun _ _ h => Sum.inr_injective (selPR.injective h)⟩

/-- **Known gates of the conversion placed on the factor wires**: the gates on the `a` ancillas and
the system, shifted past the flag wire (`shiftG`) and placed on the private register. -/
def placeC (Cg : List (Gate (Fin a ⊕ S))) :
    List (NInstr (PWr Empty (Fin (a + 1) ⊕ S) Z bT bP A) Y J) :=
  nGatesOf ((shiftG Cg).map (GateODE.Gate.map (ePR (S := S) (Z := Z) (bT := bT) (bP := bP)
    (A := A) a)))

/-- The placed conversion gates act as the unconditional ideal of the conversion. -/
theorem nrun_placeC (prim : J → Reg Y R →L[ℂ] Reg Y R) (Cg : List (Gate (Fin a ⊕ S))) :
    nrun prim (placeC (Z := Z) (bT := bT) (bP := bP) (A := A) Cg) =
      uncIdeal (selOp (Sel := Empty) (a := a + 1) (S := S) (R := R)
        (fun _ => liftA (a := a) (P := Reg S R) (UJop (R := R) Cg))) := by
  have h1 : selOp (Sel := Empty) (a := a + 1) (S := S) (R := R)
      (fun _ => liftA (a := a) (P := Reg S R) (UJop (R := R) Cg)) =
      localOp Sum.inr Sum.inr_injective (fun _ => gRun (Q := R) (shiftG Cg)) := by
    rw [← UJop_shiftG]
    unfold selOp
    congr 1
    funext _
    exact conj_unfl_fl _
  rw [h1, placeC, nrun_nGatesOf, gRun_map_gates]
  unfold uncIdeal
  exact (GateODE.localOp_localOp' (selPR (Sel := Empty) (PR := Fin (a + 1) ⊕ S) (Z := Z)
    (bT := bT) (bP := bP) (A := A)).injective Sum.inr_injective
    (ePR (S := S) (Z := Z) (bT := bT) (bP := bP) (A := A) a)
    (ePR (S := S) (Z := Z) (bT := bT) (bP := bP) (A := A) a).injective (fun _ => rfl)
    (fun _ _ => gRun (Q := R) (shiftG Cg))).symm

/-- **The converted factor circuit**: the inverse conversion, the supplied factor circuit, the
conversion. -/
def convFactor (Cg : List (Gate (Fin a ⊕ S)))
    (fc : List (NInstr (PWr Empty (Fin (a + 1) ⊕ S) Z bT bP A) Y J)) :
    List (NInstr (PWr Empty (Fin (a + 1) ⊕ S) Z bT bP A) Y J) :=
  placeC (gInv Cg) ++ fc ++ placeC Cg

omit [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] in
/-- The converted factor circuit has the gates of the supplied circuit and twice the conversion
gates. -/
theorem nGatesN_convFactor (Cg : List (Gate (Fin a ⊕ S)))
    (fc : List (NInstr (PWr Empty (Fin (a + 1) ⊕ S) Z bT bP A) Y J)) :
    nGatesN (convFactor Cg fc) = nGatesN fc + 2 * Cg.length := by
  simp only [convFactor, placeC, nGatesN_append, nGatesN_nGatesOf, List.length_map,
    shiftG_length, gInv_length]
  ring

omit [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] in
/-- The converted factor circuit makes the calls of the supplied circuit. -/
theorem nCallsN_convFactor (p : J → Bool) (Cg : List (Gate (Fin a ⊕ S)))
    (fc : List (NInstr (PWr Empty (Fin (a + 1) ⊕ S) Z bT bP A) Y J)) :
    nCallsN p (convFactor Cg fc) = nCallsN p fc := by
  simp only [convFactor, placeC, nCallsN_append, nCallsN_nGatesOf]
  ring

omit [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] in
theorem placeC_valid {Cg : List (Gate (Fin a ⊕ S))} (hCg : ∀ g ∈ Cg, GateOK 3 g) :
    ∀ i ∈ placeC (Z := Z) (bT := bT) (bP := bP) (A := A) (Y := Y) (J := J) Cg, i.Valid := by
  intro i hi
  simp only [placeC, nGatesOf, List.mem_map] at hi
  obtain ⟨g, ⟨g', hg', rfl⟩, rfl⟩ := hi
  exact gateOK_map _ (shiftG_ok hCg _ hg')

omit [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] in
/-- The converted factor circuit is valid. -/
theorem convFactor_valid {Cg : List (Gate (Fin a ⊕ S))} (hCg : ∀ g ∈ Cg, GateOK 3 g)
    {fc : List (NInstr (PWr Empty (Fin (a + 1) ⊕ S) Z bT bP A) Y J)}
    (hfc : ∀ i ∈ fc, i.Valid) : ∀ i ∈ convFactor Cg fc, i.Valid := by
  intro i hi
  simp only [convFactor, List.mem_append] at hi
  rcases hi with (h | h) | h
  · exact placeC_valid (gInv_ok Cg hCg) i h
  · exact hfc i h
  · exact placeC_valid hCg i h

omit [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] in
theorem placeC_gates {𝒢 : Set Kind} {Cg : List (Gate (Fin a ⊕ S))}
    (hCg : ∀ g ∈ Cg, GateOf 𝒢 g) :
    ∀ g, NInstr.gate g ∈ placeC (Z := Z) (bT := bT) (bP := bP) (A := A) (Y := Y) (J := J) Cg →
      GateOf 𝒢 g := by
  intro g hg
  simp only [placeC, nGatesOf, List.mem_map, NInstr.gate.injEq] at hg
  obtain ⟨g₁, ⟨g₂, hg₂, rfl⟩, rfl⟩ := hg
  simp only [shiftG, List.mem_map] at hg₂
  obtain ⟨g₃, hg₃, rfl⟩ := hg₂
  exact GateOf.map _ (GateOf.map _ (hCg g₃ hg₃))

omit [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] in
/-- The converted factor circuit is over `𝒢` (an adjoint-closed gate set). -/
theorem convFactor_gates {𝒢 : Set Kind} (hadj : AdjClosed 𝒢) {Cg : List (Gate (Fin a ⊕ S))}
    (hCg : ∀ g ∈ Cg, GateOf 𝒢 g)
    {fc : List (NInstr (PWr Empty (Fin (a + 1) ⊕ S) Z bT bP A) Y J)}
    (hfc : ∀ g, NInstr.gate g ∈ fc → GateOf 𝒢 g) :
    ∀ g, NInstr.gate g ∈ convFactor Cg fc → GateOf 𝒢 g := by
  intro g hg
  simp only [convFactor, List.mem_append] at hg
  rcases hg with (h | h) | h
  · refine placeC_gates (fun g' hg' => ?_) g h
    obtain ⟨g'', hg'', rfl⟩ := mem_gInv Cg g' hg'
    exact SparseHamiltonian.GateSynthTrials.GateOf.inv hadj (hCg g'' hg'')
  · exact hfc g h
  · exact placeC_gates hCg g h

omit [Fintype S] [DecidableEq S] in
/-- The unconditional ideal preserves clean work wires. -/
theorem uncIdeal_preserves {PR : Type*} [Fintype PR] [DecidableEq PR]
    (Usel : Reg (Empty ⊕ PR) R →L[ℂ] Reg (Empty ⊕ PR) R) :
    Preserves CleanP (uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) Usel) := by
  unfold uncIdeal
  apply preserves_localOp
  intro y b hy
  constructor
  · intro z
    rw [GateODE.overwrite_apply_out _ y b _ (fun p hp => by simp [selPR] at hp)]
    exact hy.1 z
  · intro w
    rw [GateODE.overwrite_apply_out _ y b _ (fun p hp => by simp [selPR] at hp)]
    exact hy.2 w

/-- **The converted factor circuit implements the converted factor**: if the supplied factor
circuit is within `ξ` of `U ⊗ I_flag` on clean work wires, the converted circuit is within `ξ` of
`C U C† ⊗ I_flag`, `C = U_C` the operator of the conversion gates. -/
theorem convFactor_approx (prim : J → Reg Y R →L[ℂ] Reg Y R) (Cg : List (Gate (Fin a ⊕ S)))
    (hCg : ∀ g ∈ Cg, GateOK 3 g)
    (fc : List (NInstr (PWr Empty (Fin (a + 1) ⊕ S) Z bT bP A) Y J))
    (U : Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)) {ξ : ℝ} (hξ : 0 ≤ ξ)
    (hfc : ApproxOn CleanP (nrun prim fc) (uncIdeal (selOp (Sel := Empty) (a := a + 1) (S := S)
      (R := R) (fun _ => liftA (a := a) (P := Reg S R) U))) ξ) :
    ApproxOn CleanP (nrun prim (convFactor Cg fc))
      (uncIdeal (selOp (Sel := Empty) (a := a + 1) (S := S) (R := R)
        (fun _ => liftA (a := a) (P := Reg S R)
          (UJop (R := R) Cg ∘L U ∘L (UJop (R := R) Cg)†)))) ξ := by
  have hCi : UJop (R := R) (gInv Cg) = (UJop (R := R) Cg)† := by
    rw [UJop_adjoint]
    rfl
  have hCu : IsUnitary (UJop (R := R) Cg) := UJop_isUnitary Cg hCg
  have hun : ∀ O : Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R), IsUnitary O →
      IsUnitary (uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A)
        (selOp (Sel := Empty) (a := a + 1) (S := S) (R := R)
          (fun _ => liftA (a := a) (P := Reg S R) O))) := fun O hO =>
    localOp_isUnitary _ _ (fun _ => selOp_isUnitary _ (fun _ => liftA_isUnitary hO))
  have hrun : nrun prim (convFactor Cg fc) =
      uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A)
        (selOp (Sel := Empty) (a := a + 1) (S := S) (R := R)
          (fun _ => liftA (a := a) (P := Reg S R) (UJop (R := R) Cg))) ∘L
      (nrun prim fc ∘L uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A)
        (selOp (Sel := Empty) (a := a + 1) (S := S) (R := R)
          (fun _ => liftA (a := a) (P := Reg S R) ((UJop (R := R) Cg)†)))) := by
    rw [convFactor, nrun_append, nrun_append, nrun_placeC, nrun_placeC, hCi]
  have hid : uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A)
        (selOp (Sel := Empty) (a := a + 1) (S := S) (R := R)
          (fun _ => liftA (a := a) (P := Reg S R) (UJop (R := R) Cg))) ∘L
      (uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A)
        (selOp (Sel := Empty) (a := a + 1) (S := S) (R := R)
          (fun _ => liftA (a := a) (P := Reg S R) U)) ∘L
      uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A)
        (selOp (Sel := Empty) (a := a + 1) (S := S) (R := R)
          (fun _ => liftA (a := a) (P := Reg S R) ((UJop (R := R) Cg)†)))) =
      uncIdeal (selOp (Sel := Empty) (a := a + 1) (S := S) (R := R)
        (fun _ => liftA (a := a) (P := Reg S R)
          (UJop (R := R) Cg ∘L U ∘L (UJop (R := R) Cg)†))) := by
    unfold uncIdeal
    simp only [localOp_comp, GateOptimalBinary.selOp_const_comp, liftA_comp]
  rw [hrun]
  exact approxOn_sandwich_eq hξ hfc (hun _ hCu) (hun _ (isUnitary_adj hCu))
    (uncIdeal_preserves _) hid

end ConvCircuit

/-! ### A conversion given by gates, charged in the circuit -/

section ConvGates

variable {S Z Y J Xs : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y] [Fintype Xs] [DecidableEq Xs] {bT bP A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

omit [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype Xs] [DecidableEq Xs] in
/-- The operator of concatenated gate lists. -/
theorem UJop_append {a : ℕ} (gs hs : List (Gate (Fin a ⊕ S))) :
    UJop (R := R) (gs ++ hs) = UJop (R := R) hs ∘L UJop (R := R) gs := by
  unfold UJop
  rw [gRun_append]
  ext ψ
  simp

omit [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype Xs] [DecidableEq Xs] in
/-- **A conversion given by gates**: for gates `Eg` preparing the initialised input on clean
ancillas (`U_E ι₀ = E`) and gates `Cg` whose operator `U_C` takes `Π` and `Z` to the designated flag
qubits, `U_C` is a conversion with boundary `U_J = U_C U_E`, the operator of `Eg ++ Cg`. -/
theorem converts_of_gates {a : ℕ} (K : Known (Reg S R) (Anc a (Reg S R)))
    (Eg Cg : List (Gate (Fin a ⊕ S))) (hCg : ∀ g ∈ Cg, GateOK 3 g) {f z : Fin a}
    (hE : UJop (R := R) Eg ∘L iota0 = K.E)
    (hP : UJop (R := R) Cg ∘L K.proj ∘L (UJop (R := R) Cg)† = dg (projD f))
    (hZ : UJop (R := R) Cg ∘L K.Z ∘L (UJop (R := R) Cg)† = dg (signD z)) :
    Converts K (UJop (R := R) Cg) (UJop (R := R) (Eg ++ Cg)) f z where
  unitary := UJop_isUnitary Cg hCg
  boundary := by rw [UJop_append, ← hE, comp_assoc]
  proj := hP
  sign := hZ

/-- **Proposition `gate:prop:signed` over a finite gate set for a general known success projection
and sign reflection, with the conversion built from gates and charged.** For a general factor
interface `K`, gates `Eg` preparing its initialised input, conversion gates `Cg` over `𝒢` taking
`Π` and `Z` to designated flag qubits `f ≠ z`, and a supplied factor circuit `fc` over `𝒢` within `ξ`
of the original factor `U ⊗ I_flag`: the signed circuit with the boundary gates `Eg ++ Cg` and the
converted factor circuit `convFactor Cg fc` (`U_C† · fc · U_C` on the factor wires) is valid, over
`𝒢`, makes `n_P` copies of the calls of `fc`, has at most `n_P (|fc| + 2 |Cg|)` retained gates plus
the synthesised known gates (`C_J = |Eg| + |Cg|`), and its full output is within `ε + n_P ξ + δ` of
`exp(-i t λ C_K)` for the signed compression `C_K` of the general interface. -/
theorem gate_prop_signed_known_conv [FiniteDimensional ℂ R] (hS : Synthesis 𝒢 Xs L)
    (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀) {a : ℕ}
    (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (K : Known (Reg S R) (Anc a (Reg S R))) (Eg Cg : List (Gate (Fin a ⊕ S)))
    (hEg : ∀ g ∈ Eg, GateOK 3 g) (hCg : ∀ g ∈ Cg, GateOK 3 g) (hCgG : ∀ g ∈ Cg, GateOf 𝒢 g)
    {f z : Fin a} (hfz : f ≠ z) (hE : UJop (R := R) Eg ∘L iota0 = K.E)
    (hP : UJop (R := R) Cg ∘L K.proj ∘L (UJop (R := R) Cg)† = dg (projD f))
    (hZ : UJop (R := R) Cg ∘L K.Z ∘L (UJop (R := R) Cg)† = dg (signD z))
    (U : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (hU : IsUnitary U)
    (fc : List (NInstr (PWr Empty (Fin (a + 1) ⊕ S) Z bT bP A) Y J))
    (hfcV : ∀ i ∈ fc, i.Valid) (hfcG : ∀ g, NInstr.gate g ∈ fc → GateOf 𝒢 g) {ξ : ℝ}
    (hξ : 0 ≤ ξ)
    (hfc : ApproxOn CleanP (nrun prim fc) (uncIdeal (selOp (Sel := Empty) (a := a + 1) (S := S)
      (R := R) (fun _ => liftA (a := a) (P := Reg S R) U))) ξ)
    {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hD : K.Dop U ≤ (δ : ℂ) • (1 : Reg S R →L[ℂ] Reg S R))
    (t : ℝ) {ε δs : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) (hδs : 0 < δs) (hδs1 : δs ≤ 1) :
    (∀ i ∈ selSgOf hS δs (Eg ++ Cg) (convFactor Cg fc) (sgCircuit a f z lam δ t ε), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ selSgOf hS δs (Eg ++ Cg) (convFactor Cg fc)
      (sgCircuit a f z lam δ t ε) → GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (selSgOf hS δs (Eg ++ Cg) (convFactor Cg fc)
      (sgCircuit a f z lam δ t ε)) = nPriv (sgCircuit a f z lam δ t ε) * nCallsN p fc) ∧
    ((nPriv (sgCircuit a f z lam δ t ε) : ℝ) ≤ (if sgB lam δ t ≤ ε then 0 else
      4 * 10 ^ 10 * (Real.sqrt (sgT lam t * sgB lam δ t) +
        Real.sqrt (sgT lam t * rb (sgB lam δ t) ε) + rb (sgB lam δ t) ε))) ∧
    knownG (Eg.length + Cg.length) (sgCircuit a f z lam δ t ε) ≤
      64 * 3 ^ 8 * ((sigN (sgQ lam δ t ε) (sgOrd lam δ t ε) + 1) *
        (a + sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε + sigR (sgQ lam δ t ε) (sgOrd lam δ t ε) +
          1)) + nPriv (sgCircuit a f z lam δ t ε) * (7 * (Eg.length + Cg.length)) ∧
    (nGatesN (selSgOf hS δs (Eg ++ Cg) (convFactor Cg fc) (sgCircuit a f z lam δ t ε)) : ℝ) ≤
      (nPriv (sgCircuit a f z lam δ t ε) : ℝ) * ((nGatesN fc : ℝ) + 2 * Cg.length) +
        (knownG (Eg.length + Cg.length) (sgCircuit a f z lam δ t ε) : ℝ) *
          (c₁ * Real.log (((knownG (Eg.length + Cg.length) (sgCircuit a f z lam δ t ε) : ℝ) +
            1) / δs) + c₀ + 1) ∧
    Fintype.card (HW (SgWire a lam δ t ε) S Empty Z bT bP A ⊕ Xs) =
      2 * a + 3 * sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε +
        6 * sigR (sgQ lam δ t ε) (sgOrd lam δ t ε) + 5 + Fintype.card S +
          (Fintype.card Z + bT + bP + A + 3) + Fintype.card Xs ∧
    ‖nrun prim (selSgOf hS δs (Eg ++ Cg) (convFactor Cg fc) (sgCircuit a f z lam δ t ε)) ∘L
        (cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • K.ham lam U)‖ ≤
      ε + (nPriv (sgCircuit a f z lam δ t ε) : ℝ) * ξ + δs := by
  have hJg : ∀ g ∈ Eg ++ Cg, GateOK 3 g := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hEg g h
    · exact hCg g h
  have hK := converts_of_gates K Eg Cg hCg hE hP hZ
  have hfc' := convFactor_approx prim Cg hCg fc U hξ hfc
  have h := gate_prop_signed_known_sel hS hadj hc₀ hc₁ hL prim hprim K (Eg ++ Cg) hJg
    (UJop (R := R) Cg) (UJop (R := R) (Eg ++ Cg)) U rfl (UJop_isUnitary _ hJg) hU hfz hK
    (convFactor Cg fc) (convFactor_valid hCg hfcV) (convFactor_gates hadj hCgG hfcG) hξ hfc'
    hlam hδ hδ1 hD t hε hε1 hδs hδs1
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  rw [List.length_append] at h5 h6
  rw [nGatesN_convFactor, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h6
  exact ⟨h1, h2, fun p => by rw [h3 p, nCallsN_convFactor], h4, h5, h6, h7, h8⟩

end ConvGates

end

end ManuscriptConformance
