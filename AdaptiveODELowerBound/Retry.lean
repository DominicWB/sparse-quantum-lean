import AdaptiveODELowerBound.Theorem
import AdaptiveODELowerBound.Psd.Theorem
import AdaptiveODELowerBound.Padding.Combined

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Retry-protocol forms of the positive semidefinite, homogeneous and padded bounds

Manuscript: Section `odel:sec:main` (the output model of the solvers; the released solvers are
bounded retry protocols) for Theorem `odel:thm:psd`, Proposition `odel:rem:homogeneous` and the
padded families (proof of Theorem `odel:thm:joint` and proof of Theorem `odel:thm:combined`).

A retry protocol (`ODERepeatProtocol.Protocol`) is the adaptive protocol `Tree.final` with the same
oracle family, labels, success mass, conditional output and worst-case cost (`Model.retryToTree`),
so every tree witness is a retry witness (`Model.treeWitnesses_retryWitnesses`) and a witness of
`SparseLowerBounds.ODE` (`Model.treeWitnesses_witnesses`). The retry-protocol forms below follow
from the tree forms: `psd_retry`, `hom_witness_retry`, `joint_witness_pad_retry`,
`herald_witness_pad_retry`, `combined_pad_retry`, and the common-dimension and qubit-register forms
`joint_common_dimension_retry`, `joint_qubit_register_retry`, `combined_common_dimension_retry` and
`combined_qubit_register_retry` (proof of Theorem `odel:thm:joint` and proof of Theorem
`odel:thm:combined`).
-/

namespace AdaptiveODELowerBound

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open LowerBoundRemarks.HamiltonianPadding
open ODELowerBoundExtensions.Release (RetryWitnesses)
open ODELowerBoundExtensions.Psd (PsdRange psdSearchFamilyAt psdScalarFamilyAt psdBound)
open ODELowerBoundExtensions.Homogeneous (HomRange homFamilyAt homConst)
open ODELowerBoundExtensions.Padding (jointPadFamilyAt timePadFamilyAt mixedPadFamilyAt
  precisionPadFamilyAt SparsityAttained)
open AdaptiveODELowerBound.Model

-- The nested time-addressed workspaces exceed the default instance size.
set_option synthInstance.maxSize 1024

variable {s : ℕ} {τ gbar ε : ℝ}

/-- **Theorem `odel:thm:psd` for retry protocols** (eq. `odel:eq:psd`): for `PsdRange` and any
`ḡ ≥ √2`, one of the two PSD families retry-witnesses `psdConst (√(sτr) + r)`. -/
theorem psd_retry (h : PsdRange τ s ε) (hg : Real.sqrt 2 ≤ gbar) :
    RetryWitnesses (psdSearchFamilyAt h) τ gbar ε (psdBound s τ ε) ∨
      RetryWitnesses (psdScalarFamilyAt h) τ gbar ε (psdBound s τ ε) :=
  (Psd.psd_tree h hg).imp treeWitnesses_retryWitnesses treeWitnesses_retryWitnesses

/-- **Proposition `odel:rem:homogeneous` for retry protocols**: on `HomRange`, the homogeneous
family retry-witnesses `ḡ √s τ / 500`. -/
theorem hom_witness_retry (h : HomRange s τ gbar ε) :
    RetryWitnesses (homFamilyAt s τ gbar h.s_ge h.gbar_ge h.tau_ge) τ gbar ε
      (homConst * gbar * Real.sqrt s * τ) :=
  treeWitnesses_retryWitnesses (Joint.hom_witness_tree h)

/-- **Theorem `odel:thm:joint` after known zero padding, retry protocols**: the padded joint
family retry-witnesses `ḡ √s τ / 400`. -/
theorem joint_witness_pad_retry (h : JointRange s τ gbar ε) (dense : Bool) (P : Type*)
    [Fintype P] [DecidableEq P] :
    RetryWitnesses (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge P) τ gbar ε
      (jointConst * gbar * Real.sqrt s * τ) :=
  treeWitnesses_retryWitnesses (Padding.joint_witness_pad_tree h dense P).1

/-- **Eq. `odel:eq:hsbound` for the padded `g = 1` families and retry protocols**: on `HSRange`,
for any `ḡ ≥ 1` and any known paddings, one of the padded time, mixed and precision families
retry-witnesses `c₀ (√s τ + √(sτr) + r)`. -/
theorem herald_witness_pad_retry (h : HSRange τ s ε) (hg : 1 ≤ gbar) (PT PM PP : Type*)
    [Fintype PT] [DecidableEq PT] [Fintype PM] [DecidableEq PM] [Fintype PP] [DecidableEq PP] :
    RetryWitnesses (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      RetryWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      RetryWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) :=
  (Padding.herald_witness_pad_tree h hg PT PM PP).imp treeWitnesses_retryWitnesses
    (Or.imp treeWitnesses_retryWitnesses treeWitnesses_retryWitnesses)

/-- **Theorem `odel:thm:combined` for padded families and retry protocols**: for any known
paddings, one of the three padded families retry-witnesses `c (ḡ √s τ + √(sτr) + r)`. -/
theorem combined_pad_retry (h : CombinedRange s τ gbar ε) (dense : Bool) (PJ PM PP : Type*)
    [Fintype PJ] [DecidableEq PJ] [Fintype PM] [DecidableEq PM] [Fintype PP] [DecidableEq PP] :
    RetryWitnesses (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge PJ) τ gbar ε
        (combinedBound s τ gbar ε) ∨
      RetryWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PM) τ gbar ε
        (combinedBound s τ gbar ε) ∨
      RetryWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PP) τ gbar ε
        (combinedBound s τ gbar ε) :=
  (Padding.combined_pad_tree h dense PJ PM PP).imp treeWitnesses_retryWitnesses
    (Or.imp treeWitnesses_retryWitnesses treeWitnesses_retryWitnesses)

/-- **Theorem `odel:thm:joint` in any sufficiently large common dimension, retry protocols**: for
every `Nd` at least the dimension of `jointFamilyAt`, the joint family padded by
`PadTo JointIndex Nd` has dimension exactly `Nd` and retry-witnesses `ḡ √s τ / 400`; with the
dense block it has maximum sparsity exactly `s`. -/
theorem joint_common_dimension_retry (h : JointRange s τ gbar ε) (dense : Bool) (Nd : ℕ)
    (hJ : Fintype.card (JointIndex (jointM gbar) (jointMu s) s) ≤ Nd) :
    Fintype.card (JointIndex (jointM gbar) (jointMu s) s ⊕
        PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd) = Nd ∧
      RetryWitnesses (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd)) τ gbar ε
        (jointConst * gbar * Real.sqrt s * τ) ∧
      (dense = true → SparsityAttained (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd))) :=
  have hw := Padding.joint_common_dimension_tree h dense Nd hJ
  ⟨hw.1, treeWitnesses_retryWitnesses hw.2.1, hw.2.2⟩

/-- **Theorem `odel:thm:joint` on any sufficiently large qubit register, retry protocols**: for
every `q` with `3 ḡ² s ≤ 2^q`, the joint family padded by `PadTo JointIndex (2^q)` has dimension
exactly `2^q` and retry-witnesses `ḡ √s τ / 400`; with the dense block it has maximum sparsity
exactly `s`. -/
theorem joint_qubit_register_retry (h : JointRange s τ gbar ε) (dense : Bool) (q : ℕ)
    (hq : 3 * gbar ^ 2 * s ≤ (2 : ℝ) ^ q) :
    Fintype.card (JointIndex (jointM gbar) (jointMu s) s ⊕
        PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q)) = 2 ^ q ∧
      RetryWitnesses (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q))) τ gbar ε
        (jointConst * gbar * Real.sqrt s * τ) ∧
      (dense = true → SparsityAttained (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q)))) :=
  have hw := Padding.joint_qubit_register_tree h dense q hq
  ⟨hw.1, treeWitnesses_retryWitnesses hw.2.1, hw.2.2⟩

/-- **Theorem `odel:thm:combined` in one common dimension, retry protocols**: for every `Nd` at
least the dimensions of the three hard families, the families padded by `PadTo S Nd` have
dimension exactly `Nd`, maximum sparsity exactly `s` (the joint family with the dense block), and
one of them retry-witnesses `c (ḡ √s τ + √(sτr) + r)`. -/
theorem combined_common_dimension_retry (h : CombinedRange s τ gbar ε) (dense : Bool) (Nd : ℕ)
    (hJ : Fintype.card (JointIndex (jointM gbar) (jointMu s) s) ≤ Nd)
    (hM : Fintype.card (SearchIndex (precN τ ε) (hsMu s) s) ≤ Nd)
    (hP : Fintype.card (ScalarIndex (precN τ ε) s) ≤ Nd) :
    Fintype.card (JointIndex (jointM gbar) (jointMu s) s ⊕
        PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd) = Nd ∧
      Fintype.card (SearchIndex (precN τ ε) (hsMu s) s ⊕
        PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd) = Nd ∧
      Fintype.card (ScalarIndex (precN τ ε) s ⊕ PadTo (ScalarIndex (precN τ ε) s) Nd) = Nd ∧
      ((dense = true → SparsityAttained (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge
          h.tau_ge (PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd))) ∧
        SparsityAttained (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd)) ∧
        SparsityAttained (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (ScalarIndex (precN τ ε) s) Nd))) ∧
      (RetryWitnesses (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd)) τ gbar ε
          (combinedBound s τ gbar ε) ∨
        RetryWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd)) τ gbar ε
          (combinedBound s τ gbar ε) ∨
        RetryWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (ScalarIndex (precN τ ε) s) Nd)) τ gbar ε (combinedBound s τ gbar ε)) :=
  have hw := Padding.combined_common_dimension_tree h dense Nd hJ hM hP
  ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.imp treeWitnesses_retryWitnesses
    (Or.imp treeWitnesses_retryWitnesses treeWitnesses_retryWitnesses)⟩

/-- **Theorem `odel:thm:combined` on a qubit register, retry protocols**: for every `q` with
`3 ḡ² s ≤ 2^q` and `4 s (τ + r + 1) ≤ 2^q`, the three families padded by `PadTo S (2^q)` have
dimension exactly `2^q` and maximum sparsity exactly `s` (the joint family when `dense = true`),
and one of them retry-witnesses `c (ḡ √s τ + √(sτr) + r)`. -/
theorem combined_qubit_register_retry (h : CombinedRange s τ gbar ε) (dense : Bool) (q : ℕ)
    (hqJ : 3 * gbar ^ 2 * s ≤ (2 : ℝ) ^ q) (hqH : 4 * s * (τ + hsR τ ε + 1) ≤ (2 : ℝ) ^ q) :
    Fintype.card (JointIndex (jointM gbar) (jointMu s) s ⊕
        PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q)) = 2 ^ q ∧
      Fintype.card (SearchIndex (precN τ ε) (hsMu s) s ⊕
        PadTo (SearchIndex (precN τ ε) (hsMu s) s) (2 ^ q)) = 2 ^ q ∧
      Fintype.card (ScalarIndex (precN τ ε) s ⊕
        PadTo (ScalarIndex (precN τ ε) s) (2 ^ q)) = 2 ^ q ∧
      ((dense = true → SparsityAttained (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge
          h.tau_ge (PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q)))) ∧
        SparsityAttained (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) (2 ^ q))) ∧
        SparsityAttained (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (ScalarIndex (precN τ ε) s) (2 ^ q)))) ∧
      (RetryWitnesses (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q))) τ gbar ε
          (combinedBound s τ gbar ε) ∨
        RetryWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) (2 ^ q))) τ gbar ε
          (combinedBound s τ gbar ε) ∨
        RetryWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (ScalarIndex (precN τ ε) s) (2 ^ q))) τ gbar ε (combinedBound s τ gbar ε)) :=
  have hw := Padding.combined_qubit_register_tree h dense q hqJ hqH
  ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.imp treeWitnesses_retryWitnesses
    (Or.imp treeWitnesses_retryWitnesses treeWitnesses_retryWitnesses)⟩

end

end AdaptiveODELowerBound
