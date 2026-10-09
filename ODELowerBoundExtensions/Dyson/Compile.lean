import ODELowerBoundExtensions.Dyson.Select
import SparseODE.ODEJointSourceLCU
import SparseODE.ODECompiledSource

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The physical Dyson SELECT and its LCU (`odel:lem:dyson`, lines 4200-4206, 4228)

The logical SELECT of `Select.lean` is compiled to the physical masked native access
`matrixOracle (Omega K M) D` by the release's masked-program compiler
(`NativeMaskedProgram.compile`, three native calls per logical letter, exact
`compile_eval` on the common clean encoding `NativeMaskedOracle.input`). The LCU branch space is
the release's source-branch space `ODECompiledSource.Branch (LabelI K M) ℂ^n M`
(`= PiLp 2 (Lab K M → ℂ^n)`), encoded at all flags zero (`encoding`).

* `select`: the physical program, `18 K` native calls (`select_count`; per label `select_cost`);
* `select_compression`: `encoding† select encoding = diag_l branchOperator l` (exact, no error);
* `decoded_select`: with any coefficients `d` and branch preparations `J`, the release's decoded
  LCU vector (`ODEJointSourceLCU.decoded`) is exactly `(∑_l |d l|)⁻¹ ∑_l d l • branchOperator l
  (J l v)` (from `ODECoherentLCU.successful_compression`).
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct BigOperators

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s Ks : ℕ}

/-- **The physical Dyson SELECT**: the logical SELECT compiled to masked native calls. -/
def select {M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (K : ℕ) :
    MultiOracleCircuit.Program (matrixOracle (Omega K M) D) :=
  NativeMaskedProgram.compile (timeOracle D) (cleanTime hK D) letterLabel letterActive
    (logicalSelect hM hK σ D K)

/-- **The LCU encoding**: branch `l` at all flags zero, payload encoded by `payloadEncoding`,
then the release's clean masked-access encoding. -/
def encoding {M : ℕ} (hK : 0 < Ks) (D : Data (X × Fin Ks) n Z s) (K : ℕ) :
    ODECompiledSource.Branch (LabelI K M) (EuclideanSpace ℂ n) M →L[ℂ]
      NativeMaskedOracle.Physical (Omega K M) (PBasis Ks n Z) :=
  (NativeMaskedOracle.input (ι := Omega K M) (cleanTime hK D)).toContinuousLinearMap ∘L
    zeroFlags (Λ := Lab K M) (K := K) (payloadEncoding hK D)

/-- The LCU input encoding (clean masked-access input after the all-zero-flag payload encoding)
is an isometry. -/
theorem encoding_isometry {M : ℕ} (hK : 0 < Ks) (D : Data (X × Fin Ks) n Z s) (K : ℕ) :
    (encoding (M := M) hK D K)† ∘L encoding hK D K = 1 :=
  NativeSparseAttenuation.isometry_comp _ _
    (zeroFlags_isometry _ (payloadEncoding_isometry hK D))
    (NativeMaskedOracle.input (ι := Omega K M) (cleanTime hK D)).adjoint_comp_self

/-- The physical SELECT is unitary on every input. -/
theorem select_unitary {M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (K : ℕ) (x : X) :
    IsUnitary ((select hM hK σ D K).eval x) :=
  NativeMaskedProgram.compile_unitary _ (timeOracle_unitary D) _ _ _ _ x

/-- **Exact compression of the physical SELECT** (lines 4200-4206). -/
theorem select_compression {M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (K : ℕ) (x : X) :
    (encoding (M := M) hK D K)† ∘L (select hM hK σ D K).eval x ∘L encoding hK D K =
      WeightedClock.diagonal (branchOperator (K := K) σ D x) := by
  have hc := NativeMaskedProgram.compile_eval (timeOracle D) (timeOracle_unitary D)
    (cleanTime hK D) (imageTime hK D) (timeOracle_valid hK D) letterLabel
    (letterActive (K := K) (M := M)) (logicalSelect hM hK σ D K) x
  have hi := (NativeMaskedOracle.input (ι := Omega K M) (cleanTime hK D)).adjoint_comp_self
  rw [← logicalSelect_compression hM hK σ D K x]
  refine ContinuousLinearMap.ext fun v => ?_
  have h1 := congrArg (fun f => f (zeroFlags (Λ := Lab K M) (K := K) (payloadEncoding hK D) v)) hc
  have h2 := congrArg (fun f => f ((logicalSelect hM hK σ D K).eval x
    (zeroFlags (Λ := Lab K M) (K := K) (payloadEncoding hK D) v))) hi
  simp only [comp_apply] at h1 h2
  simp only [encoding, select, adjoint_comp, comp_apply, h1, h2]
  rfl

/-- `18 K` native matrix calls (`O(K)`, line 4204; the count does not depend on the mesh). -/
theorem select_count {M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (K : ℕ) :
    (select hM hK σ D K).count = 18 * K := by
  rw [select, NativeMaskedProgram.compile_count, logicalSelect_count]
  ring

/-- Per native label: `3 K` row, `3 K` column and `12 K` value calls. -/
theorem select_cost {M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (K : ℕ) (w : Query → ℕ) :
    (select hM hK σ D K).cost w = 3 * K * (w .rowLocation + w .columnLocation + 4 * w .value) := by
  rw [select, NativeMaskedProgram.compile_cost]
  refine (logicalSelect_cost hM hK σ D K (fun l => 3 * w l)).trans ?_
  ring

/-- **The decoded LCU vector** of the actual circuit: for coefficients `d` of positive mass and
branch preparations `J`, `decoded = (∑ |d|)⁻¹ ∑_l d l • branchOperator l (J l v)`. -/
theorem decoded_select {M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (K : ℕ) (x : X) (d : Lab K M → ℂ)
    (hd : 0 < ODECoherentLCU.coefficientMass d)
    (J : Lab K M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (v : EuclideanSpace ℂ n) :
    ODEJointSourceLCU.decoded (encoding hK D K) d J ((select hM hK σ D K).eval x) v =
      ((ODECoherentLCU.coefficientMass d : ℂ))⁻¹ •
        ∑ l, d l • branchOperator (K := K) σ D x l (J l v) := by
  have _ := hd
  have hs := congrArg (fun f => f (ODECoherentLCU.inputEmbedding d J v))
    (select_compression hM hK σ D K x)
  have hl := congrArg (fun f => f v)
    (ODECoherentLCU.successful_compression d (branchOperator (K := K) σ D x) J
      (fun _ => (1 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)))
  simp only [comp_apply] at hs hl
  simp only [ODEJointSourceLCU.decoded, ODEHeraldedSuccess.decoded, ODEJointSourceLCU.input,
    ODEJointLCU.output, ODEJointLCU.coefficientOutput, adjoint_comp, comp_apply, hs]
  rw [hl]
  simp only [smul_apply, _root_.sum_apply, comp_apply, one_def, adjoint_id, id_apply]

end

end ODELowerBoundExtensions.Dyson
