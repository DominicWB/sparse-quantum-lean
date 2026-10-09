import GateEfficientBinary.Sparse.Oracles

/-!
# The native identity from binary sparse oracles

For the binary sparse oracles of `Sparse/Oracles` the compute circuit `computeV` and the decoder
`γ √s c₀ (X + i Y)` of the value wires satisfy the native identity `V† R_val V = D` of the
native gate model on clean scratch (`sparse_nativeOK`), for the qubit lift `D` of the private
Cayley operation `FixedNativeCayleySimulation.action D x γ`: the locator conjugation of the
exact edge action.

The proof combines `compute_cleanEmb` (`V` on clean scratch is the lifted locator `F` followed by
a permutation `P` of basis configurations), `rdec_sigma` (`R_val P = P A` on clean scratch for
the lifted edge action `A`) and the unitarity of `V` and `F` (`nativeOK_of`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinary

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.OracleCircuit
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The operator algebra of the native identity: if `V` acts on clean scratch as `F` followed
by `P` and the rotation `Rd` commutes past `P` into `A`, then `V† Rd V` acts on clean scratch as
`F† A F`. -/
theorem nativeOK_of {B Z : Type*} [Fintype B] [DecidableEq B] [Fintype Z] [DecidableEq Z]
    (V P Rd : Reg (B ⊕ Z) R →L[ℂ] Reg (B ⊕ Z) R) (F A : Reg B R →L[ℂ] Reg B R)
    (hK1 : V ∘L cleanEmb = P ∘L cleanEmb ∘L F)
    (hK2 : Rd ∘L P ∘L cleanEmb = P ∘L cleanEmb ∘L A)
    (hVV : V† ∘L V = 1) (hFF : F ∘L F† = 1) :
    V† ∘L Rd ∘L V ∘L cleanEmb = cleanEmb ∘L F† ∘L A ∘L F := by
  have hW : V† ∘L P ∘L cleanEmb (X := Z) = cleanEmb ∘L F† := by
    calc V† ∘L P ∘L cleanEmb (X := Z) = V† ∘L P ∘L cleanEmb ∘L (F ∘L F†) := by
          rw [hFF, one_def, comp_id]
      _ = V† ∘L (P ∘L cleanEmb ∘L F) ∘L F† := by simp only [comp_assoc]
      _ = V† ∘L (V ∘L cleanEmb) ∘L F† := by rw [hK1]
      _ = (V† ∘L V) ∘L cleanEmb ∘L F† := by simp only [comp_assoc]
      _ = cleanEmb ∘L F† := by rw [hVV, one_def, id_comp]
  calc V† ∘L Rd ∘L V ∘L cleanEmb = V† ∘L Rd ∘L P ∘L cleanEmb ∘L F := by rw [hK1]
    _ = V† ∘L (Rd ∘L P ∘L cleanEmb) ∘L F := by simp only [comp_assoc]
    _ = V† ∘L (P ∘L cleanEmb ∘L A) ∘L F := by rw [hK2]
    _ = (V† ∘L P ∘L cleanEmb) ∘L A ∘L F := by simp only [comp_assoc]
    _ = cleanEmb ∘L F† ∘L A ∘L F := by
        rw [hW]
        simp only [comp_assoc]

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}

/-- The lifted private operation is the lifted edge action conjugated by the lifted locator. -/
theorem liftE_action (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) (γ : ℝ) :
    liftE (qlift (R := R) (phiPR en) (FixedNativeCayleySimulation.action D x γ)) =
      (Fq D en x)† ∘L Aq D en x γ ∘L Fq D en x := by
  unfold FixedNativeCayleySimulation.action UnitaryCayleyTransport.conjugate Fq Aq
  rw [mul_def, mul_def, star_eq_adjoint, qlift_comp, qlift_comp, qlift_adjoint, liftE_comp,
    liftE_comp, liftE_adjoint, comp_assoc]

/-- **The native identity from binary sparse oracles.** For indices given by `k`-bit words
(`en`) with the all-zero word a slot (`hk0`) and entries stored as `b`-bit two's complement
components with decoder `c₀ (X + i Y)` (`hdec`), the compute circuit `computeV` with the
decoder `γ √s c₀ (X + i Y)` of the value wires satisfies the native identity `V† R_val V = D`
on clean scratch, for the qubit lift `D` of the private Cayley operation
`FixedNativeCayleySimulation.action D x γ`, at every input `x` and rescaling `γ`. -/
theorem sparse_nativeOK (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) (c0 : ℝ) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z)
    (x : X) (γ : ℝ) :
    NativeOK (prims (R := R) D en x) (sparseOp k b (γ * Real.sqrt s * c0))
      (selOp (fun _ : Cfg Empty =>
        unconj (qlift (R := R) (phiPR en) (FixedNativeCayleySimulation.action D x γ)))) := by
  have hK1 := compute_cleanEmb (R := R) (b := b) D en k0 hk0 x
  have hK2 := rdec_sigma (R := R) D en k0 x γ c0 hdec
  have hVu : IsUnitary (nrun (prims (R := R) D en x) (computeV k b)) :=
    nrun_isUnitary _ (prims_isUnitary D en x) _ (computeV_valid k b)
  have hFu : IsUnitary (Fq (R := R) D en x) :=
    liftE_isUnitary (qlift_isUnitary _ (FixedLocatorConjugation.locator_unitary D x))
  have hVV : (nrun (prims (R := R) D en x) (computeV k b))† ∘L
      nrun (prims (R := R) D en x) (computeV k b) = 1 := by
    have h := hVu.1
    rwa [star_eq_adjoint, mul_def] at h
  have hFF : Fq (R := R) D en x ∘L (Fq D en x)† = 1 := by
    have h := hFu.2
    rwa [star_eq_adjoint, mul_def] at h
  unfold NativeOK
  rw [selOp_unconj, liftE_action]
  exact nativeOK_of _ _ _ _ _ hK1 hK2 hVV hFF

end

end SparseHamiltonian.GateBinary
