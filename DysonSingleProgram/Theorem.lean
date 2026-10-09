import DysonSingleProgram.Solver
import DysonSingleProgram.Explicit.Family
import SparseLowerBounds.ODE.JointTheorem

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Lemma `odel:lem:dyson` for single heralded programs

Manuscript lines 4591-4690 (Lemma `odel:lem:dyson`, eq. `odel:eq:dyson`), on the class of the ODE
lower bounds (`SparseLowerBounds.ODE.Family`, `Family.InClass η ḡ`, access `Family.access ι`,
lines 4091-4132) and in its single-program solver class `SparseLowerBounds.ODE.Solver` (one
program, a seed, a herald projection with success at least `2/3`, heralded conditional accuracy
`ε`).

`solver_dyson`: every family of the class with `T > 0` has, for `0 < ε ≤ 1`, a single heralded
program over its own access whose number of calls (all labels, inverse calls included) is at most
`dysonBound (s η T) ḡ ε = 16000 ḡ e^z (1 + z + L_g/log(e + L_g/z))`, `z = s η T`,
`L_g = log(4000 ḡ/ε)` (eq. `odel:eq:dyson`), the bound of the released retry form
`ODELowerBoundExtensions.Dyson.retrySolver_dyson`.

Proof (`exists_solver_of_shape`, whose statement names the program `fourAttempts`): the four
public attempts of the released Dyson trial family (`Explicit.family_dyson_grover`), each on its
own register with its randomized cutoff held coherently in a label register (`Coherent.trial`),
then a fixed, query-free readout of the first heralded output; the herald is the OR of the four
attempt flags (`Parallel.Stage.four`). No oracle call is controlled. A family without inputs is
solved by the empty program (`exists_solver_of_isEmpty`).

`solver_dyson_joint` (non-vacuity): the joint hard family of the released lower bound
(`SparseLowerBounds.ODE.joint_witness`, Theorem `odel:thm:joint`) has an input and meets the
hypotheses of `solver_dyson` with `η = 1`; its single program makes at least `jointConst ḡ √s τ`
calls (the released lower bound) and at most `dysonBound (s τ) ḡ ε`.

Scope. The single heralded program is stated for the class of the ODE lower bounds, the class
that the lower bounds and eq. `odel:eq:fixed` quantify over. For the general certified-mesh class
of Lemma `odel:lem:dyson` (time-indexed native input, mesh, cell-to-sample map, source
interfaces), the package has the trial-family form `ODELowerBoundExtensions.Dyson.dyson` and its
amplification shape `Explicit.dyson_grover`. Only oracle calls of the access are counted (the
sources of the class are public); gate costs and time-register sizes may depend on the
discretisation and are not bounded (lines 4602-4603 and 4705-4707).
-/

namespace DysonSingleProgram

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE OracleCircuit
open ODELowerBoundExtensions.Dyson (dysonBound)
open scoped InnerProduct InnerProductSpace

/-- **A family without inputs has a zero-query solver**: the identity program, seed `0`, herald
`0`. -/
theorem exists_solver_of_isEmpty {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] {K s : ℕ} (F : Family X N Z K s) (ε : ℝ) [IsEmpty X] :
    ∃ (G : Type) (_ : NormedAddCommGroup G) (_ : InnerProductSpace ℂ G) (_ : CompleteSpace G)
      (A : Solver Unit F G ε), A.prog.count = 0 := by
  classical
  obtain ⟨out, hout⟩ : ∃ out : Workspace Unit N Z K →L[ℂ] SysGarb N (Workspace Unit N Z K),
      out† ∘L out = 1 := by
    by_cases hN : Nonempty N
    · obtain ⟨i₀⟩ := hN
      refine ⟨(PiLp.continuousLinearEquiv 2 ℂ
          (fun _ : N => Workspace Unit N Z K)).symm.toContinuousLinearMap ∘L
          ContinuousLinearMap.pi fun i => if i = i₀ then 1 else 0, ?_⟩
      ext1 v
      refine ext_inner_left ℂ fun w => ?_
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
        PiLp.inner_apply, Finset.sum_eq_single i₀ (fun b _ hb => by simp [hb]) (by simp)]
      simp
    · refine ⟨0, ContinuousLinearMap.ext fun v => ?_⟩
      have hv : v = 0 := by
        ext j k
        exact (hN ⟨k.1.1⟩).elim
      subst hv
      simp
  exact ⟨Workspace Unit N Z K, inferInstance, inferInstance, inferInstance,
    { prog := MultiOracleCircuit.Program.identity
      seed := 0
      seed_norm_le := by simp
      out := out
      out_isometry := hout
      herald := 0
      herald_proj := IsStarProjection.zero _
      success := fun x => isEmptyElim x
      accurate := fun x => isEmptyElim x }, rfl⟩

/-- **Lemma `odel:lem:dyson` for single heralded programs** (lines 4591-4690, eq.
`odel:eq:dyson`): every family of the class `InClass η ḡ` with `η > 0` and `T > 0` has, for
`ḡ ≥ 1` and `0 < ε ≤ 1`, a single-program solver (`SparseLowerBounds.ODE.Solver`) over its own
access `F.access ι` making at most `dysonBound (s η T) ḡ ε` calls. -/
theorem solver_dyson {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
    {K s : ℕ} (F : Family X N Z K s) (η gbar ε : ℝ) (hF : F.InClass η gbar) (hη : 0 < η)
    (hT : 0 < F.T) (hg : 1 ≤ gbar) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (ι : Type) (_ : Fintype ι) (G : Type) (_ : NormedAddCommGroup G)
      (_ : InnerProductSpace ℂ G) (_ : CompleteSpace G) (A : Solver ι F G ε),
      (A.prog.count : ℝ) ≤ dysonBound ((s : ℝ) * η * F.T) gbar ε := by
  classical
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · obtain ⟨G, i1, i2, i3, A, hA⟩ := exists_solver_of_isEmpty F ε
    refine ⟨Unit, inferInstance, G, i1, i2, i3, A, ?_⟩
    rw [hA, Nat.cast_zero]
    have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    exact ODELowerBoundExtensions.Dyson.dysonBound_nonneg (mul_nonneg (mul_nonneg hs hη.le) hT.le)
      hg hε hε1
  · obtain ⟨sol₀, -, hne₀, -⟩ := hF.solution x₀
    obtain ⟨i₀, -⟩ : ∃ i, sol₀ F.T i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne₀ (by ext i; simpa using hcon i)
    obtain ⟨ι, hι, q, M, ψ, out, g', ell, a, U₁, U₂, U₃, hbound, hshape, hcert⟩ :=
      Explicit.family_dyson_grover F η gbar ε hF hη hT hg hε hε1
    obtain ⟨A, -, hA⟩ := exists_solver_of_shape F ε ι q M ψ out (s : ℝ) 0 ell g' a U₁ U₂ U₃
      hshape (fun x => (hF.solution x).imp fun _ h => h.1) x₀ i₀ hcert
    exact ⟨_, inferInstance, _, inferInstance, inferInstance, inferInstance, A,
      hA.trans hbound⟩

open SparseLowerBounds.ODE ODELowerBoundExtensions.Dyson in
/-- **Non-vacuity of `solver_dyson`**: the joint hard family of the released lower bound
(`SparseLowerBounds.ODE.joint_witness`, `odel:thm:joint`) has an input and meets the hypotheses
of `solver_dyson` with `η = 1`; its single program makes between `c_J ḡ √s τ` and
`dysonBound (s τ) ḡ ε` calls. -/
theorem solver_dyson_joint {s : ℕ} {τ gbar ε : ℝ} (h : JointRange s τ gbar ε) :
    Nonempty (Promised (jointM gbar) (jointN τ) (2 ^ jointMu s)) ∧
    ∃ (ι : Type) (_ : Fintype ι) (G : Type) (_ : NormedAddCommGroup G)
      (_ : InnerProductSpace ℂ G) (_ : CompleteSpace G)
      (A : Solver ι (jointFamilyAt s τ gbar h.s_ge h.tau_ge) G ε),
      jointConst * gbar * Real.sqrt s * τ ≤ A.prog.count ∧
        (A.prog.count : ℝ) ≤ dysonBound ((s : ℝ) * τ) gbar ε := by
  have hW := joint_witness h
  have hs := h.s_ge
  refine ⟨nonempty_promised (by have := four_le_jointM h.gbar_ge; omega)
    (one_le_jointN h.tau_ge) ?_, ?_⟩
  · calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ jointMu s := Nat.pow_le_pow_right (by norm_num) (one_le_jointMu (by omega))
  obtain ⟨ι, hι, G, i1, i2, i3, A, hA⟩ := solver_dyson _ 1 gbar ε hW.inClass one_pos
    (by rw [hW.time_eq]; linarith [h.tau_ge]) (by linarith [h.gbar_ge]) h.eps_pos
    (by linarith [h.eps_le])
  rw [hW.time_eq, mul_one] at hA
  exact ⟨ι, hι, G, i1, i2, i3, A, (hW.forces ι G A).2, hA⟩

end

end DysonSingleProgram
