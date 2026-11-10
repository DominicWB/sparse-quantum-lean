import GateOptimalBinary.FactorLayout
import GateOptimalBinary.FactorLocal
import NativeSignedFactor.Factor
import Mathlib.Algebra.Group.TransferInstance

/-!
# The signed-factor regime from binary sparse oracles

The signed-factor regime of Theorem `gate:thm:main` uses the interface
`GateOptimalPrecision.SignedIface` with `λ = sμ` and `δ = σ^{-1/2}`: a boundary preparation `U_J`
and a factor unitary `U_B` with `H = sμ B†ZB` and `B†B ⪯ σ^{-1/2} I` for `B = Π U_B U_J ι₀`
(`gate:eq:native`, `gate:eq:whole-factor`, Section `gate:sec:native`). It is constructed here from
the binary sparse oracles of `GateEfficientBinary`, on `k + 3` ancilla qubits (`GU k`):

* `sgUJg`: the Hadamard gates of the bounded regime (`GateBinary.hadUJ`) on the bounded wires,
  preparing `J₀ = (2s)^{-1/2} (L₀; R₀)` up to the locator, with clean flag and sign;
* `UF`: the factor `U_B = F† U(c) F` with the lifted locator `F` (`FuF`) and the stable signed
  factor `U(c)` of the paragraph "A stable constant-dimensional signed factor" on the flag, the
  orientation and the sign, selected by the located edge, at `c = clip(H_e/μ)` (`AuF`, `cvU`);
* `sg_Cop`, `sg_Dop`: the compressions `B†ZB` and `B†B` are the qubit lifts of those of the
  released query-level native factor (`NativeSignedFactor.known`), so `B†ZB = H/(sμ)` and
  `B†B ⪯ η/(√s μ) I = σ^{-1/2} I` (`NativeSignedFactor.Cop_eq`, `NativeSignedFactor.Dop_le`);
* `signedIface`: the interface.

The two-sided completion `U(c) = A_φ (R_u ⊗ I) A_φ†` enters only through its action on the
initial block (`uMat_sign_block`, `uMat_weight_block`); its stability on the whole private space is
used by the native transfer (`GateOptimalPrecision.signed_transfer`).

References to the manuscript use its labels.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace GateOptimalBinary

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary GateOptimalPrecision
open NativeSparseBlockEncoding (Data Query)
open SparseHamiltonian.GateODE (overwrite_apply_ι overwrite_apply_out)
open scoped InnerProduct Matrix

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-! ### Flat operators -/

omit [CompleteSpace R] in
theorem unconj_conj {W S : Type*} [Fintype W] [DecidableEq W] [Fintype S] [DecidableEq S]
    (O : Reg W (Reg S R) →L[ℂ] Reg W (Reg S R)) : unconj (conj O) = O := by
  unfold unconj GateNative.conj
  ext ψ
  simp

omit [CompleteSpace R] in
theorem unconj_eq {W S : Type*} [Fintype W] [DecidableEq W] [Fintype S] [DecidableEq S]
    (O : Reg (W ⊕ S) R →L[ℂ] Reg (W ⊕ S) R) : unconj O = unfl ∘L O ∘L fl := rfl

/-- Compressing a flat operator to clean ancillas reads it through the flat clean embedding. -/
theorem iota0_unconj {a : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    (T : Reg (Fin a ⊕ S) R →L[ℂ] Reg (Fin a ⊕ S) R) :
    (iota0 (a := a) (P := Reg S R))† ∘L unconj T ∘L iota0 =
      ((fl (W := Fin a) (S := S) (R := R)) ∘L iota0 (a := a) (P := Reg S R))† ∘L T ∘L
        ((fl (W := Fin a) (S := S) (R := R)) ∘L iota0 (a := a) (P := Reg S R)) := by
  rw [unconj_eq, adjoint_comp, fl_adjoint]
  simp only [comp_assoc]

/-- **From `k + 3` to `k + 1` ancillas**: compressing to clean ancillas passes through `ι2`. -/
theorem iota0_unconj_ι2 (T : Reg (GU k) R →L[ℂ] Reg (GU k) R) :
    (iota0 (a := k + 3) (P := Reg (Fin k) R))† ∘L unconj T ∘L iota0 =
      (iota0 (a := k + 1) (P := Reg (Fin k) R))† ∘L unconj ((ι2 k)† ∘L T ∘L ι2 k) ∘L
        iota0 := by
  rw [iota0_unconj, iota0_unconj, fl_iota0_ι2, adjoint_comp]
  simp only [comp_assoc]

/-! ### The boundary preparation -/

theorem gateOK_map {A W : Type*} {e : A → W} (he : Function.Injective e) {m : ℕ} {g : Gate A}
    (h : GateOK m g) : GateOK m (GateODE.Gate.map e g) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simpa [GateODE.Gate.map] using h1, ?_, h3⟩
  intro c hc
  simp only [GateODE.Gate.map, List.mem_map] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  intro hct
  exact h2 c' hc' (he hct)

/-- **The gates of `U_J`**: the Hadamard gates `GateBinary.hadUJ` on the bounded wires. -/
def sgUJg (k sb : ℕ) (hsb : sb ≤ k) : List (Gate (GU k)) :=
  (hadUJ k sb hsb).map (GateODE.Gate.map (ιUe k))

theorem sgUJg_ok (sb : ℕ) (hsb : sb ≤ k) : ∀ g ∈ sgUJg k sb hsb, GateOK 3 g := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
  exact gateOK_map (ιU_injective k) (hadUJ_ok sb hsb g' hg')

theorem sgUJg_length (sb : ℕ) (hsb : sb ≤ k) : (sgUJg k sb hsb).length = sb + 1 := by
  rw [sgUJg, List.length_map, hadUJ_length]

theorem gRun_sgUJg (sb : ℕ) (hsb : sb ≤ k) :
    gRun (Q := R) (sgUJg k sb hsb) =
      localOp (ιU k) (ιU_injective k) (fun _ => gRun (Q := R) (hadUJ k sb hsb)) :=
  gRun_map_gates (ιUe k) _

/-! ### The factor -/

/-- The edge held by a configuration of the factor register. -/
def edgeU (en : Cfg (Fin k) ≃ n) (y : Cfg (GU k)) : n × n :=
  phiE en (fun e => y (ιU k (ixPR k e)))

/-- The entry `clip(H_e/μ)` of the factor at the edge `e` of a configuration. -/
def cvU (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X) (y : Cfg (GU k)) :
    ℂ :=
  NativeSignedFactor.entry D μ (edgeU en y, D.table x (edgeU en y))

theorem norm_cvU_le (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X)
    (y : Cfg (GU k)) : ‖cvU D en μ x y‖ ≤ 1 :=
  NativeSignedFactor.norm_entry_le D μ _

/-- The lifted locator on the factor register. -/
def FuF (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    Reg (GU k) R →L[ℂ] Reg (GU k) R :=
  localOp (ιU k) (ιU_injective k)
    (fun _ => qlift (R := R) (phiPR en) (FixedLocatorConjugation.locator D x))

/-- The stable signed factor `U(c)` on the flag, orientation and sign qubits, at the entry of the
located edge. -/
def AuF (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X) :
    Reg (GU k) R →L[ℂ] Reg (GU k) R :=
  localOp (locU k) (locU_injective k) (fun y => matOp (blk (uMat (cvU D en μ x y))))

/-- **The signed factor** `U_B = F† U(c) F` on the flat factor register. -/
def UF (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X) :
    Reg (GU k) R →L[ℂ] Reg (GU k) R :=
  (FuF D en x)† ∘L AuF D en μ x ∘L FuF D en x

/-- The signed factor on the ancilla register with the system payload. -/
def sgU (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X) :
    Anc (k + 3) (Reg (Fin k) R) →L[ℂ] Anc (k + 3) (Reg (Fin k) R) :=
  unconj (UF (R := R) D en μ x)

theorem FuF_isUnitary (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    IsUnitary (FuF (R := R) D en x) :=
  localOp_isUnitary _ _ (fun _ => qlift_isUnitary _ (FixedLocatorConjugation.locator_unitary D x))

theorem blk_uMat_unitary {c : ℂ} (hc : ‖c‖ ≤ 1) :
    (blk (uMat c))ᴴ * blk (uMat c) = 1 ∧ blk (uMat c) * (blk (uMat c))ᴴ = 1 := by
  obtain ⟨h1, h2⟩ := uMat_unitary hc
  rw [blk_conjTranspose, ← blk_mul, ← blk_mul, h1, h2, blk_one]
  exact ⟨rfl, rfl⟩

theorem AuF_isUnitary (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X) :
    IsUnitary (AuF (R := R) D en μ x) :=
  localOp_isUnitary _ _ (fun y => matOp_isUnitary _
    (blk_uMat_unitary (norm_cvU_le D en μ x y)).1 (blk_uMat_unitary (norm_cvU_le D en μ x y)).2)

theorem UF_isUnitary (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X) :
    IsUnitary (UF (R := R) D en μ x) := by
  have hF := FuF_isUnitary (R := R) D en x
  have hA := AuF_isUnitary (R := R) D en μ x
  have hF' : IsUnitary ((FuF (R := R) D en x)†) := by
    rw [← star_eq_adjoint]
    exact hF.adjoint
  exact (hF'.mul (hA.mul hF))

theorem sgU_isUnitary (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X) :
    IsUnitary (sgU (R := R) D en μ x) :=
  unconj_isUnitary (UF_isUnitary D en μ x)

/-! ### The compressions -/

/-- The flat success projection `Π = [f = 1]`. -/
abbrev projF (k : ℕ) : Reg (GU k) R →L[ℂ] Reg (GU k) R :=
  conj (dg (P := Reg (Fin k) R) (projD (fW k)))

/-- The flat sign `Z = (-1)^z`. -/
abbrev signF (k : ℕ) : Reg (GU k) R →L[ℂ] Reg (GU k) R :=
  conj (dg (P := Reg (Fin k) R) (signD (zW k)))

theorem sgU_eq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X) :
    sgU (R := R) D en μ x = unconj (UF (R := R) D en μ x) := rfl

theorem UJop_eq_unconj {a : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    (g : List (Gate (Fin a ⊕ S))) : UJop (R := R) g = unconj (gRun (Q := R) g) := rfl

theorem sgUJ_adj (sb : ℕ) (hsb : sb ≤ k) :
    (UJop (R := R) (sgUJg k sb hsb))† ∘L UJop (R := R) (sgUJg k sb hsb) = 1 :=
  unitary_adj_comp (UJop_isUnitary _ (sgUJg_ok sb hsb))

/-- The known structure of the signed factor: `E = U_J ι₀`, `Π = [f = 1]`, `Z = (-1)^z`. -/
abbrev sgKnown (k sb : ℕ) (hsb : sb ≤ k) :
    SignedFactorSimulation.Known (Reg (Fin k) R) (Anc (k + 3) (Reg (Fin k) R)) :=
  wKnown (P := Reg (Fin k) R) (a := k + 3) (UJop (R := R) (sgUJg k sb hsb))
    (unitary_adj_comp (UJop_isUnitary _ (sgUJg_ok sb hsb))) (fW k) (zW k)

/-- The factor `B = Π U_B U_J ι₀` in flat form. -/
theorem sg_factor (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X)
    (sb : ℕ) (hsb : sb ≤ k) :
    (sgKnown (R := R) k sb hsb).factor (sgU (R := R) D en μ x) =
      unconj (projF (R := R) k ∘L UF (R := R) D en μ x ∘L gRun (Q := R) (sgUJg k sb hsb)) ∘L
        iota0 := by
  show dg (P := Reg (Fin k) R) (projD (fW k)) ∘L sgU (R := R) D en μ x ∘L
      (UJop (R := R) (sgUJg k sb hsb) ∘L iota0) = _
  rw [sgU_eq, UJop_eq_unconj, unconj_comp, unconj_comp, unconj_conj]
  simp only [comp_assoc]

theorem unconj_sandwich {W S : Type*} [Fintype W] [DecidableEq W] [Fintype S] [DecidableEq S]
    {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    (A T : Reg (W ⊕ S) R →L[ℂ] Reg (W ⊕ S) R) (J : P →L[ℂ] Reg W (Reg S R)) :
    (unconj A ∘L J)† ∘L unconj T ∘L (unconj A ∘L J) = J† ∘L unconj (A† ∘L T ∘L A) ∘L J := by
  rw [adjoint_comp, ← unconj_adjoint, unconj_comp, unconj_comp]
  simp only [comp_assoc]

/-- `B† M B` for a flat operator `M`. -/
theorem sg_sandwich (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X)
    (sb : ℕ) (hsb : sb ≤ k) (T : Reg (GU k) R →L[ℂ] Reg (GU k) R) :
    ((sgKnown (R := R) k sb hsb).factor (sgU (R := R) D en μ x))† ∘L unconj T ∘L
      (sgKnown (R := R) k sb hsb).factor (sgU (R := R) D en μ x) =
      (iota0 (a := k + 3) (P := Reg (Fin k) R))† ∘L
        unconj ((projF (R := R) k ∘L UF (R := R) D en μ x ∘L gRun (Q := R) (sgUJg k sb hsb))† ∘L
          T ∘L (projF (R := R) k ∘L UF (R := R) D en μ x ∘L gRun (Q := R) (sgUJg k sb hsb))) ∘L
        iota0 := by
  rw [sg_factor, unconj_sandwich]

/-- The success projection commutes with the lifted locator. -/
theorem projF_comm (T : Reg (PR k) R →L[ℂ] Reg (PR k) R) :
    projF (R := R) k ∘L localOp (ιU k) (ιU_injective k) (fun _ => T) =
      localOp (ιU k) (ιU_injective k) (fun _ => T) ∘L projF (R := R) k := by
  rw [projF, conj_dg]
  apply diag_comm_localOp
  intro y c
  simp only [projD, overwrite_apply_out _ _ _ _ (ιU_ne_f k)]

/-- The sign commutes with the lifted locator. -/
theorem signF_comm (T : Reg (PR k) R →L[ℂ] Reg (PR k) R) :
    signF (R := R) k ∘L localOp (ιU k) (ιU_injective k) (fun _ => T) =
      localOp (ιU k) (ιU_injective k) (fun _ => T) ∘L signF (R := R) k := by
  rw [signF, conj_dg]
  apply diag_comm_localOp
  intro y c
  simp only [signD, overwrite_apply_out _ _ _ _ (ιU_ne_z k)]

theorem projF_adjoint : (projF (R := R) k)† = projF k := by
  rw [projF, ← conj_adjoint, dg_adjoint]
  congr 2
  funext c
  exact star_projD _ c

/-- The factor applied to clean flag and sign: `X ι₂ = F† (Π U(c) ι₂) (L Had)`. -/
theorem sg_X_ι2 (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X)
    (sb : ℕ) (hsb : sb ≤ k) :
    (projF (R := R) k ∘L UF (R := R) D en μ x ∘L gRun (Q := R) (sgUJg k sb hsb)) ∘L ι2 k =
      (FuF (R := R) D en x)† ∘L (projF (R := R) k ∘L AuF (R := R) D en μ x ∘L ι2 k) ∘L
        (qlift (R := R) (phiPR en) (FixedLocatorConjugation.locator D x) ∘L
          gRun (Q := R) (hadUJ k sb hsb)) := by
  have h1 : gRun (Q := R) (sgUJg k sb hsb) ∘L ι2 k = ι2 k ∘L gRun (Q := R) (hadUJ k sb hsb) := by
    rw [gRun_sgUJg, localOp_ι2]
  have h2 : FuF (R := R) D en x ∘L ι2 k =
      ι2 k ∘L qlift (R := R) (phiPR en) (FixedLocatorConjugation.locator D x) :=
    localOp_ι2 _
  have h3 : projF (R := R) k ∘L (FuF (R := R) D en x)† = (FuF (R := R) D en x)† ∘L projF k := by
    rw [FuF, localOp_adjoint]
    exact projF_comm _
  calc (projF (R := R) k ∘L UF (R := R) D en μ x ∘L gRun (Q := R) (sgUJg k sb hsb)) ∘L ι2 k
      = projF (R := R) k ∘L (FuF (R := R) D en x)† ∘L AuF (R := R) D en μ x ∘L
          (FuF (R := R) D en x ∘L ι2 k) ∘L gRun (Q := R) (hadUJ k sb hsb) := by
        rw [UF]
        simp only [comp_assoc]
        rw [h1]
    _ = (projF (R := R) k ∘L (FuF (R := R) D en x)†) ∘L AuF (R := R) D en μ x ∘L ι2 k ∘L
          qlift (R := R) (phiPR en) (FixedLocatorConjugation.locator D x) ∘L
            gRun (Q := R) (hadUJ k sb hsb) := by
        rw [h2]
        simp only [comp_assoc]
    _ = _ := by
        rw [h3]
        simp only [comp_assoc]

/-- `Π Z Π` acts on the local qubits by the diagonal `[f = 1] (-1)^z`. -/
theorem projF_signF_projF :
    projF (R := R) k ∘L signF (R := R) k ∘L projF (R := R) k =
      localOp (locU k) (locU_injective k)
        (fun _ => matOp (Matrix.diagonal (fun c => sgnQ3 (eQ c)))) := by
  rw [projF, signF, ← conj_comp, ← conj_comp, dg_comp, dg_comp, conj_dg]
  apply diag_eq_localOp
  intro y
  simp only [projD, signD, sgnQ3, eQ, Equiv.coe_fn_mk, locU_zero, locU_two]
  by_cases hf : y (Sum.inl (fW k)) <;> by_cases hz : y (Sum.inl (zW k)) <;> simp [hf, hz]

/-- `Π Π` acts on the local qubits by the diagonal `[f = 1]`. -/
theorem projF_projF :
    projF (R := R) k ∘L projF (R := R) k =
      localOp (locU k) (locU_injective k)
        (fun _ => matOp (Matrix.diagonal (fun c => sucQ3 (eQ c)))) := by
  rw [projF, ← conj_comp, dg_comp, conj_dg]
  apply diag_eq_localOp
  intro y
  simp only [projD, sucQ3, eQ, Equiv.coe_fn_mk, locU_zero]
  by_cases hf : y (Sum.inl (fW k)) <;> simp [hf]

theorem blk_diagonal (e : Q3 → ℂ) : blk (Matrix.diagonal e) = Matrix.diagonal (fun c => e (eQ c)) :=
  Matrix.submatrix_diagonal_equiv e eQ

/-- `U(c)† D U(c)` for a diagonal `D` on the local qubits, at every edge. -/
theorem AuF_sandwich (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X)
    (e : Q3 → ℂ) {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T : V →L[ℂ] Reg (GU k) R) :
    (AuF (R := R) D en μ x)† ∘L localOp (locU k) (locU_injective k)
        (fun _ => matOp (Matrix.diagonal (fun c => e (eQ c)))) ∘L AuF (R := R) D en μ x ∘L T =
      localOp (locU k) (locU_injective k) (fun y => matOp (blk ((uMat (cvU D en μ x y))ᴴ *
        Matrix.diagonal e * uMat (cvU D en μ x y)))) ∘L T := by
  have h : (AuF (R := R) D en μ x)† ∘L localOp (locU k) (locU_injective k)
        (fun _ => matOp (Matrix.diagonal (fun c => e (eQ c)))) ∘L AuF (R := R) D en μ x =
      localOp (locU k) (locU_injective k) (fun y => matOp (blk ((uMat (cvU D en μ x y))ᴴ *
        Matrix.diagonal e * uMat (cvU D en μ x y)))) := by
    rw [AuF, localOp_adjoint, localOp_comp, localOp_comp]
    congr 1
    funext y
    rw [matOp_adjoint, matOp_mul, matOp_mul, blk_mul, blk_mul, blk_conjTranspose, blk_diagonal,
      Matrix.mul_assoc]
  rw [← h]
  simp only [comp_assoc]

/-- The entry of the edge held by an extended configuration. -/
theorem cvU_clr_extU (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X)
    (c : Cfg (PR k)) :
    cvU D en μ x (clearCfg (locU k) (extU c)) =
      NativeSignedFactor.entry D μ (phiE en (fun e => c (ixPR k e)),
        D.table x (phiE en (fun e => c (ixPR k e)))) := by
  have h : (fun e => clearCfg (locU k) (extU c) (ιU k (ixPR k e))) = fun e => c (ixPR k e) := by
    funext e
    rw [clearCfg_apply_out _ _ _ (fun a => locU_ne_ixPR k a e), extU_ιU]
  unfold cvU edgeU
  rw [h]

theorem qmat_generator (z : ℂ) : qmat (ExactEdgeCayley.generator z) = eMat z := by
  funext b c
  cases b <;> cases c <;> simp [qmat, eMat, ExactEdgeCayley.generator_false,
    ExactEdgeCayley.generator_true]

theorem qmat_smul_one (r : ℂ) :
    qmat (r • (1 : ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit)) =
      fun b c => r * (1 : Matrix Bool Bool ℂ) b c := by
  funext b c
  cases b <;> cases c <;> simp [qmat]

/-- **The signed edge compression**: `ι₂† U(c)† (Π Z Π) U(c) ι₂` is the lifted edge generator
`E_c` with `c_e = clip(H_e/μ)`. -/
theorem sg_sign_edge (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X) :
    (ι2 (R := R) k)† ∘L (AuF (R := R) D en μ x)† ∘L
        (projF (R := R) k ∘L signF (R := R) k ∘L projF (R := R) k) ∘L AuF (R := R) D en μ x ∘L
          ι2 k =
      qlift (R := R) (phiPR en) (OrientedEdgeCayley.lift (fun e =>
        ExactEdgeCayley.generator (NativeSignedFactor.entry D μ (e, D.table x e)))) := by
  rw [projF_signF_projF, AuF_sandwich, ι2_compress, qlift_lift]
  congr 1
  funext c b b'
  rw [qmat_generator, cvU_clr_extU]
  exact uMat_sign_block _ b b'

/-- **The edge weight**: `ι₂† U(c)† Π U(c) ι₂` multiplies both orientations of the edge `e` by
`|c_e|`. -/
theorem sg_weight_edge (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X) :
    (ι2 (R := R) k)† ∘L (AuF (R := R) D en μ x)† ∘L
        (projF (R := R) k ∘L projF (R := R) k) ∘L AuF (R := R) D en μ x ∘L ι2 k =
      qlift (R := R) (phiPR en) (OrientedEdgeCayley.lift (fun e =>
        ((‖NativeSignedFactor.entry D μ (e, D.table x e)‖ : ℝ) : ℂ) •
          (1 : ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit))) := by
  rw [projF_projF, AuF_sandwich, ι2_compress, qlift_lift]
  congr 1
  funext c b b'
  rw [qmat_smul_one, cvU_clr_extU]
  exact uMat_weight_block _ b b'

/-! ### Assembly -/

theorem conj_mid {V V' W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [CompleteSpace V']
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (F M : W →L[ℂ] W) (Y : V →L[ℂ] W) (L : V' →L[ℂ] V) (hM : M ∘L F = F ∘L M)
    (hF : F ∘L F† = 1) :
    (F† ∘L Y ∘L L)† ∘L M ∘L (F† ∘L Y ∘L L) = L† ∘L (Y† ∘L M ∘L Y) ∘L L := by
  have h : F ∘L M ∘L F† = M := by
    rw [← comp_assoc, ← hM, comp_assoc, hF, one_def, comp_id]
  rw [adjoint_comp, adjoint_comp, adjoint_adjoint]
  simp only [comp_assoc]
  rw [← comp_assoc M (F†), ← comp_assoc F (M ∘L F†), h]

theorem FuF_comp_adjoint (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    FuF (R := R) D en x ∘L (FuF (R := R) D en x)† = 1 := by
  have h := (FuF_isUnitary (R := R) D en x).2
  rwa [star_eq_adjoint, mul_def] at h

/-- `(X ι₂)† M (X ι₂) = (L Had)† (Y† M Y) (L Had)` with `Y = Π U(c) ι₂`, for a flat `M`
commuting with the locator. -/
theorem sg_mid (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X)
    (sb : ℕ) (hsb : sb ≤ k) (M : Reg (GU k) R →L[ℂ] Reg (GU k) R)
    (hM : M ∘L FuF (R := R) D en x = FuF (R := R) D en x ∘L M) :
    (ι2 (R := R) k)† ∘L
        ((projF (R := R) k ∘L UF (R := R) D en μ x ∘L gRun (Q := R) (sgUJg k sb hsb))† ∘L M ∘L
          (projF (R := R) k ∘L UF (R := R) D en μ x ∘L gRun (Q := R) (sgUJg k sb hsb))) ∘L
        ι2 k =
      (qlift (R := R) (phiPR en) (FixedLocatorConjugation.locator D x) ∘L
          gRun (Q := R) (hadUJ k sb hsb))† ∘L
        ((projF (R := R) k ∘L AuF (R := R) D en μ x ∘L ι2 k)† ∘L M ∘L
          (projF (R := R) k ∘L AuF (R := R) D en μ x ∘L ι2 k)) ∘L
        (qlift (R := R) (phiPR en) (FixedLocatorConjugation.locator D x) ∘L
          gRun (Q := R) (hadUJ k sb hsb)) := by
  have e : (ι2 (R := R) k)† ∘L
        ((projF (R := R) k ∘L UF (R := R) D en μ x ∘L gRun (Q := R) (sgUJg k sb hsb))† ∘L M ∘L
          (projF (R := R) k ∘L UF (R := R) D en μ x ∘L gRun (Q := R) (sgUJg k sb hsb))) ∘L
        ι2 k =
      ((projF (R := R) k ∘L UF (R := R) D en μ x ∘L gRun (Q := R) (sgUJg k sb hsb)) ∘L ι2 k)† ∘L
        M ∘L ((projF (R := R) k ∘L UF (R := R) D en μ x ∘L gRun (Q := R) (sgUJg k sb hsb)) ∘L
          ι2 k) := by
    conv_rhs => rw [adjoint_comp]
    simp only [comp_assoc]
  rw [e, sg_X_ι2]
  exact conj_mid _ _ _ _ hM (FuF_comp_adjoint D en x)

theorem Y_sandwich (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X)
    (M : Reg (GU k) R →L[ℂ] Reg (GU k) R) :
    (projF (R := R) k ∘L AuF (R := R) D en μ x ∘L ι2 k)† ∘L M ∘L
        (projF (R := R) k ∘L AuF (R := R) D en μ x ∘L ι2 k) =
      (ι2 (R := R) k)† ∘L (AuF (R := R) D en μ x)† ∘L
        (projF (R := R) k ∘L M ∘L projF (R := R) k) ∘L AuF (R := R) D en μ x ∘L ι2 k := by
  rw [adjoint_comp, adjoint_comp, projF_adjoint]
  simp only [comp_assoc]

/-- The tail: the locator and the boundary preparation of the bounded register. -/
theorem sg_tail (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) (sb : ℕ)
    (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    (G : SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n) :
    (iota0 (a := k + 1) (P := Reg (Fin k) R))† ∘L
        unconj ((qlift (R := R) (phiPR en) (FixedLocatorConjugation.locator D x) ∘L
            gRun (Q := R) (hadUJ k sb hsb))† ∘L qlift (R := R) (phiPR en) G ∘L
          (qlift (R := R) (phiPR en) (FixedLocatorConjugation.locator D x) ∘L
            gRun (Q := R) (hadUJ k sb hsb))) ∘L iota0 =
      qlift (R := R) en ((FixedLocatorConjugation.fixedBoundary D.slot)† ∘L
        ((FixedLocatorConjugation.locator D x)† ∘L G ∘L FixedLocatorConjugation.locator D x) ∘L
          FixedLocatorConjugation.fixedBoundary D.slot) := by
  have e1 : (qlift (R := R) (phiPR en) (FixedLocatorConjugation.locator D x) ∘L
        gRun (Q := R) (hadUJ k sb hsb))† ∘L qlift (R := R) (phiPR en) G ∘L
      (qlift (R := R) (phiPR en) (FixedLocatorConjugation.locator D x) ∘L
        gRun (Q := R) (hadUJ k sb hsb)) =
      (gRun (Q := R) (hadUJ k sb hsb))† ∘L qlift (R := R) (phiPR en)
        ((FixedLocatorConjugation.locator D x)† ∘L G ∘L FixedLocatorConjugation.locator D x) ∘L
        gRun (Q := R) (hadUJ k sb hsb) := by
    rw [qlift_comp, qlift_comp, qlift_adjoint, adjoint_comp]
    simp only [comp_assoc]
  rw [e1, ← unconj_sandwich, ← UJop_eq_unconj]
  exact boundary_lift sb hsb en D.slot hs hrange _

/-- **The signed compression** `B†ZB` of the factor, as the lift of an operator of the system. -/
theorem sg_Cop (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X) (sb : ℕ)
    (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u)) :
    (sgKnown (R := R) k sb hsb).Cop (sgU (R := R) D en μ x) =
      qlift (R := R) en ((FixedLocatorConjugation.fixedBoundary D.slot)† ∘L
        ((FixedLocatorConjugation.locator D x)† ∘L OrientedEdgeCayley.lift (fun e =>
          ExactEdgeCayley.generator (NativeSignedFactor.entry D μ (e, D.table x e))) ∘L
          FixedLocatorConjugation.locator D x) ∘L
        FixedLocatorConjugation.fixedBoundary D.slot) := by
  have hZ : (sgKnown (R := R) k sb hsb).Z = unconj (signF (R := R) k) := (unconj_conj _).symm
  have hM : signF (R := R) k ∘L FuF (R := R) D en x = FuF (R := R) D en x ∘L signF k := by
    rw [FuF]
    exact signF_comm _
  rw [SignedFactorSimulation.Known.Cop, hZ, sg_sandwich, iota0_unconj_ι2,
    sg_mid D en μ x sb hsb (signF k) hM, Y_sandwich, sg_sign_edge]
  exact sg_tail D en x sb hsb hs hrange _

/-- **The successful weight** `B†B` of the factor, as the lift of an operator of the system. -/
theorem sg_Dop (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X) (sb : ℕ)
    (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u)) :
    (sgKnown (R := R) k sb hsb).Dop (sgU (R := R) D en μ x) =
      qlift (R := R) en ((FixedLocatorConjugation.fixedBoundary D.slot)† ∘L
        ((FixedLocatorConjugation.locator D x)† ∘L OrientedEdgeCayley.lift (fun e =>
          ((‖NativeSignedFactor.entry D μ (e, D.table x e)‖ : ℝ) : ℂ) •
            (1 : ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit)) ∘L
          FixedLocatorConjugation.locator D x) ∘L
        FixedLocatorConjugation.fixedBoundary D.slot) := by
  have h1 : (sgKnown (R := R) k sb hsb).Dop (sgU (R := R) D en μ x) =
      ((sgKnown (R := R) k sb hsb).factor (sgU (R := R) D en μ x))† ∘L
        unconj (1 : Reg (GU k) R →L[ℂ] Reg (GU k) R) ∘L
          (sgKnown (R := R) k sb hsb).factor (sgU (R := R) D en μ x) := by
    rw [unconj_one, one_def, id_comp]
    rfl
  have hM : (1 : Reg (GU k) R →L[ℂ] Reg (GU k) R) ∘L FuF (R := R) D en x =
      FuF (R := R) D en x ∘L 1 := by
    rw [one_def, id_comp, comp_id]
  have h2 : projF (R := R) k ∘L (1 : Reg (GU k) R →L[ℂ] Reg (GU k) R) ∘L projF (R := R) k =
      projF (R := R) k ∘L projF (R := R) k := by
    rw [one_def, id_comp]
  rw [h1, sg_sandwich, iota0_unconj_ι2, sg_mid D en μ x sb hsb 1 hM, Y_sandwich, h2,
    sg_weight_edge]
  exact sg_tail D en x sb hsb hs hrange _

/-- An additive group structure on the value words (bitwise addition modulo two), used only to
instantiate the released query-level native factor. -/
abbrev cfgAddCommGroup (W : Type*) : AddCommGroup (Cfg W) :=
  @Pi.addCommGroup W (fun _ => Bool) (fun _ => finTwoEquiv.symm.addCommGroup)

/-- The query-level signed compression. -/
theorem qCop_eq [AddCommGroup (Cfg (VW b))] (D : Data X n (Cfg (VW b)) s) (μ : ℝ) (x : X) :
    (FixedLocatorConjugation.fixedBoundary D.slot)† ∘L
        ((FixedLocatorConjugation.locator D x)† ∘L OrientedEdgeCayley.lift (fun e =>
          ExactEdgeCayley.generator (NativeSignedFactor.entry D μ (e, D.table x e))) ∘L
          FixedLocatorConjugation.locator D x) ∘L
        FixedLocatorConjugation.fixedBoundary D.slot =
      (NativeSignedFactor.known D).Cop ((NativeSignedFactor.factorProgram D μ).eval x) := by
  have hG : OrientedEdgeCayley.lift (fun e : n × n =>
      ExactEdgeCayley.generator (NativeSignedFactor.entry D μ (e, D.table x e))) =
      SparseEdgeMoments.entryGenerator
        (fun i j => NativeSignedFactor.entry D μ ((i, j), D.table x (i, j))) :=
    OrientedEdgeCayley.lift_generator
      (fun i j => NativeSignedFactor.entry D μ ((i, j), D.table x (i, j)))
  have e1 : (FixedLocatorConjugation.fixedBoundary D.slot)† ∘L
        ((FixedLocatorConjugation.locator D x)† ∘L SparseEdgeMoments.entryGenerator
          (fun i j => NativeSignedFactor.entry D μ ((i, j), D.table x (i, j))) ∘L
          FixedLocatorConjugation.locator D x) ∘L
        FixedLocatorConjugation.fixedBoundary D.slot =
      (SparseEdgeMoments.boundary (D.rowloc x) (D.colloc x))† ∘L SparseEdgeMoments.entryGenerator
          (fun i j => NativeSignedFactor.entry D μ ((i, j), D.table x (i, j))) ∘L
        SparseEdgeMoments.boundary (D.rowloc x) (D.colloc x) := by
    rw [← FixedLocatorConjugation.locator_boundary D x, adjoint_comp]
    simp only [comp_assoc]
  have hZ : (NativeSignedFactor.known (Z := Cfg (VW b)) D).Z = NativeSignedFactor.sign := rfl
  rw [hG, e1, SignedFactorSimulation.Known.Cop, NativeSignedFactor.factor_eq, hZ,
    ← NativeSignedFactor.facOp_sign,
    ← NativeSignedFactor.clean_sign_clean (n := n) (Z := Cfg (VW b))]
  simp only [adjoint_comp, comp_assoc]

/-- The query-level successful weight. -/
theorem qDop_eq [AddCommGroup (Cfg (VW b))] (D : Data X n (Cfg (VW b)) s) (μ : ℝ) (x : X) :
    (FixedLocatorConjugation.fixedBoundary D.slot)† ∘L
        ((FixedLocatorConjugation.locator D x)† ∘L OrientedEdgeCayley.lift (fun e =>
          ((‖NativeSignedFactor.entry D μ (e, D.table x e)‖ : ℝ) : ℂ) •
            (1 : ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit)) ∘L
          FixedLocatorConjugation.locator D x) ∘L
        FixedLocatorConjugation.fixedBoundary D.slot =
      (NativeSignedFactor.known D).Dop ((NativeSignedFactor.factorProgram D μ).eval x) := by
  have e1 : (FixedLocatorConjugation.fixedBoundary D.slot)† ∘L
        ((FixedLocatorConjugation.locator D x)† ∘L OrientedEdgeCayley.lift (fun e =>
          ((‖NativeSignedFactor.entry D μ (e, D.table x e)‖ : ℝ) : ℂ) •
            (1 : ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit)) ∘L
          FixedLocatorConjugation.locator D x) ∘L
        FixedLocatorConjugation.fixedBoundary D.slot =
      (SparseEdgeMoments.boundary (D.rowloc x) (D.colloc x))† ∘L OrientedEdgeCayley.lift (fun e =>
          ((‖NativeSignedFactor.entry D μ (e, D.table x e)‖ : ℝ) : ℂ) •
            (1 : ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit)) ∘L
        SparseEdgeMoments.boundary (D.rowloc x) (D.colloc x) := by
    rw [← FixedLocatorConjugation.locator_boundary D x, adjoint_comp]
    simp only [comp_assoc]
  rw [e1, SignedFactorSimulation.Known.Dop, NativeSignedFactor.factor_eq,
    ← NativeSignedFactor.facOp_gram]
  simp only [adjoint_comp, comp_assoc]
  rw [← comp_assoc ((SparseHamiltonian.OrientedNativeLayout.clean (n := n)
      (Z := Cfg (VW b))).toContinuousLinearMap†)
    (SparseHamiltonian.OrientedNativeLayout.clean (n := n) (Z := Cfg (VW b))).toContinuousLinearMap,
    LinearIsometry.adjoint_comp_self, one_def, id_comp]

/-! ### The interface -/

/-- **The represented Hamiltonian** `H = sμ B†ZB` (`gate:eq:whole-factor`), for a Hermitian
matrix with entries of modulus at most `μ`. -/
theorem sg_ham (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ) (hsb : sb ≤ k)
    (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {μ : ℝ} (hμ : 0 < μ) (x : X) (hH : (D.matrix x).IsHermitian)
    (hent : ∀ i j, ‖D.matrix x i j‖ ≤ μ) :
    (sgKnown (R := R) k sb hsb).ham ((s : ℝ) * μ) (sgU (R := R) D en μ x) =
      sysH (R := R) D en x := by
  letI : AddCommGroup (Cfg (VW b)) := cfgAddCommGroup (VW b)
  have hs0 : (0 : ℝ) < s := by
    rw [hs]
    positivity
  rw [SignedFactorSimulation.Known.ham, sg_Cop D en μ x sb hsb hs hrange, qCop_eq,
    NativeSignedFactor.Cop_eq D hμ x hH hent, qlift_smul, smul_smul]
  have h1 : (((s : ℝ) * μ : ℝ) : ℂ) * ((((s : ℝ) * μ)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (mul_pos hs0 hμ).ne', Complex.ofReal_one]
  rw [h1, one_smul]

/-- A diagonal operator with real entries at most `δ` is at most `δ I`. -/
theorem matOp_diag_le {V : Type*} [Fintype V] [DecidableEq V] (t : Cfg V → ℝ) {δ : ℝ}
    (ht : ∀ c, t c ≤ δ) :
    matOp (Q := R) (Matrix.diagonal (fun c => (t c : ℂ))) ≤
      (δ : ℂ) • (1 : Reg V R →L[ℂ] Reg V R) := by
  rw [ContinuousLinearMap.le_def, isPositive_def']
  refine ⟨?_, fun ψ => ?_⟩
  · refine IsSelfAdjoint.sub ?_ ?_
    · rw [IsSelfAdjoint, star_smul, star_one, Complex.star_def, Complex.conj_ofReal]
    · rw [IsSelfAdjoint, star_eq_adjoint, matOp_adjoint, Matrix.diagonal_conjTranspose]
      congr 2
      funext c
      simp
  · have hM : RCLike.re (inner ℂ (matOp (Q := R) (Matrix.diagonal (fun c => (t c : ℂ))) ψ) ψ) =
        ∑ c, t c * ‖ψ c‖ ^ 2 := by
      rw [PiLp.inner_apply, map_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [matOp_diagonal_apply, inner_smul_left, Complex.conj_ofReal, RCLike.re_to_complex,
        Complex.re_ofReal_mul, ← RCLike.re_to_complex, inner_self_eq_norm_sq]
    have hψ : RCLike.re (inner ℂ ψ ψ) = ∑ c, ‖ψ c‖ ^ 2 := by
      rw [inner_self_eq_norm_sq, PiLp.norm_sq_eq_of_L2]
    rw [reApplyInnerSelf_apply, sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
      inner_smul_left, map_sub, Complex.conj_ofReal, RCLike.re_to_complex, Complex.re_ofReal_mul,
      ← RCLike.re_to_complex, hψ, hM, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun c _ => by nlinarith [ht c, sq_nonneg ‖ψ c‖]

/-- The qubit lift of a diagonal operator of the system. -/
theorem qlift_matrixOperator_diagonal (en : Cfg (Fin k) ≃ n) (w : n → ℂ) :
    qlift (R := R) en (SparseStateOverlap.matrixOperator (Matrix.diagonal w)) =
      matOp (Matrix.diagonal (fun c => w (en c))) := by
  rw [qlift_eq]
  congr 1
  funext c c'
  simp only [toMat, SparseStateOverlap.matrixOperator_apply, Matrix.diagonal_apply]
  by_cases h : c = c'
  · subst h
    simp
  · have h' : en c ≠ en c' := fun h'' => h (en.injective h'')
    simp [h, h']

/-- **The successful weight** `B†B ⪯ η/(√s μ) I` (`gate:eq:whole-factor`), for a Hermitian matrix
with row Euclidean norms at most `η` and entries of modulus at most `μ`. -/
theorem sg_factor_le (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ)
    (hsb : sb ≤ k) (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {μ η : ℝ} (hμ : 0 < μ) (hη : 0 ≤ η) (x : X) (hH : (D.matrix x).IsHermitian)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (hent : ∀ i j, ‖D.matrix x i j‖ ≤ μ) :
    (sgKnown (R := R) k sb hsb).Dop (sgU (R := R) D en μ x) ≤
      ((η / (Real.sqrt s * μ) : ℝ) : ℂ) • (1 : Reg (Fin k) R →L[ℂ] Reg (Fin k) R) := by
  letI : AddCommGroup (Cfg (VW b)) := cfgAddCommGroup (VW b)
  have hs0 : (0 : ℝ) < s := by
    rw [hs]
    positivity
  have hD : (sgKnown (R := R) k sb hsb).Dop (sgU (R := R) D en μ x) =
      matOp (Matrix.diagonal
        (fun c => ((((s : ℝ) * μ)⁻¹ * ∑ j, ‖D.matrix x (en c) j‖ : ℝ) : ℂ))) := by
    rw [sg_Dop D en μ x sb hsb hs hrange, qDop_eq, NativeSignedFactor.Dop_eq D hμ x hH hent,
      qlift_smul, qlift_matrixOperator_diagonal, ← matOp_smul]
    congr 1
    funext c c'
    simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs <;> push_cast <;> ring
  rw [hD]
  apply matOp_diag_le
  intro c
  have h := NativeSignedFactor.row_abs_sum_le D hη x hrow (en c)
  have hsq : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 hs0
  have hr : Real.sqrt (s : ℝ) * Real.sqrt (s : ℝ) = (s : ℝ) := Real.mul_self_sqrt hs0.le
  have hsμ : ((s : ℝ) * μ)⁻¹ = ((Real.sqrt s * Real.sqrt s) * μ)⁻¹ := by rw [hr]
  calc ((s : ℝ) * μ)⁻¹ * ∑ j, ‖D.matrix x (en c) j‖ ≤ ((s : ℝ) * μ)⁻¹ * (Real.sqrt s * η) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.2 (mul_pos hs0 hμ).le)
    _ = η / (Real.sqrt s * μ) := by
        rw [hsμ]
        field_simp

theorem inv_sqrt_sigma {σ η μ : ℝ} (hη : 0 < η) (hμ : 0 < μ) (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2)
    (hs : 0 < s) : (Real.sqrt σ)⁻¹ = η / (Real.sqrt s * μ) := by
  rw [sqrt_sigma_eq hη hμ.le hσ]
  have : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hs)
  field_simp

/-- **The signed-factor interface from binary sparse oracles.** For an input whose matrix is
Hermitian with row Euclidean norms at most `η` and entries of modulus at most `μ`, and
`σ` with `s μ² = σ η²`: `U_J` from Hadamard gates (`sgUJg`) and the factor `U_B` (`sgU`) on `k + 3`
ancillas, with `H = sμ B†ZB` and `B†B ⪯ σ^{-1/2} I` (the column norms follow from the row norms
by symmetry). -/
def signedIface (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ) (hsb : sb ≤ k)
    (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {η μ σ : ℝ} (hη : 0 < η) (hμ : 0 < μ) (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2) (x : X)
    (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hent : ∀ i j, ‖D.matrix x i j‖ ≤ μ) :
    SignedIface (Reg (Fin k) R) (s * μ) (Real.sqrt σ)⁻¹ (sysH (R := R) D en x) where
  a := k + 3
  UJ := UJop (sgUJg k sb hsb)
  U := sgU D en μ x
  unitaryJ := UJop_isUnitary _ (sgUJg_ok sb hsb)
  unitaryU := sgU_isUnitary D en μ x
  f := fW k
  z := zW k
  ne := fW_ne_zW k
  factor_le := by
    have hs0 : 0 < s := by
      rw [hs]
      positivity
    rw [inv_sqrt_sigma hη hμ hσ hs0]
    convert sg_factor_le (R := R) D en sb hsb hs hrange hμ hη.le x hH hrow hent using 1
  ham := sg_ham D en sb hsb hs hrange hμ x hH hent

end

end GateOptimalBinary
