import GateEfficientSelect.ODE.Theorem
import GateEfficientSelect.NonVacuity

/-!
# The branch-dependent solver is not vacuous

Every condition of `BInstanceOK` holds at once for explicit data with a forcing node off the
common mesh, and `outcomeB` (the instance clause of `solverB`) then applies (`nvB_outcome`); the
generator of the witness is zero, so its branch samples and clock promises hold trivially:

* public data `nvP`: no ancilla qubits, `Q = qbar = 1`, `T = 1`, `λH = 1/100`, `λD = 0`,
  `g = 1`, `ε = 1/2` and `m = 1` (two slots per branch); they satisfy the released `PublicOK`
  (`nvP_ok`, with `steps (1/100) (ν/3) ≤ 2`);
* the problem `x' = 1` on `[0, 1]` with `x(0) = 0` (zero generator, forcing `b = 1`,
  solution `x(t) = t`, `x(1) = 1`);
* the quadrature with one node `v_0 = 1/3` of weight `1` and forcing vector `1` (and a second
  node of weight `0`): the forcing branch runs on `[1/3, 1]` with the addresses `1/3` and `2/3`,
  which are not points of the common mesh `{0, 1/2}`; the certificate holds with `κ = 0`
  (`x(1) = y(1) = 1` for the constant homogeneous solution `y = 1` from `1/3`);
* the supplied unitaries: `U_J = 1`, the scalar private operation `cayleyScalar 0 • 1 = -1`
  (the clock promise for the zero normalised Hamiltonian, `clock_scalar`), the loading `1` and
  the weight preparation `nvWp`, the permutation matrix exchanging the zero word with the word of
  the forcing label `(true, 0)` (unitary, `permMat_unitary`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSelect.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire Vsp)
open GateODE (Label ClockPromise)
open GateODE.Time (TParams TOracles gens)
open GatePointerEncoding (wordValue)
open TimeDependentODE (SolvesODE Accretive)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-- A permutation matrix is unitary. -/
theorem permMat_unitary {n : Type*} [Fintype n] [DecidableEq n] (e : Equiv.Perm n) :
    (Matrix.of fun i j => if e i = j then (1 : ℂ) else 0).conjTranspose *
        (Matrix.of fun i j => if e i = j then (1 : ℂ) else 0) = 1 ∧
      (Matrix.of fun i j => if e i = j then (1 : ℂ) else 0) *
        (Matrix.of fun i j => if e i = j then (1 : ℂ) else 0).conjTranspose = 1 := by
  constructor
  · ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (e.symm i)]
    · simp [Equiv.apply_symm_apply]
    · intro k _ hk
      have : e k ≠ i := fun h => hk (by rw [← h, Equiv.symm_apply_apply])
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (e i)]
    · by_cases h : i = j
      · subst h
        simp
      · have : e j ≠ e i := fun h' => h (e.injective h').symm
        simp [this, h]
    · intro k _ hk
      simp [Ne.symm hk]
    · intro h
      exact absurd (Finset.mem_univ _) h

/-! ### Public data -/

/-- Public data: `a = 0`, `Q = qbar = 1`, `T = 1`, `λH = 1/100`, `λD = 0`, `g = 1`,
`ε = 1/2`, `m = 1`. -/
abbrev nvP : TParams := ⟨0, 1, 1, 1, 1 / 100, 0, 1, 1 / 2, 1⟩

theorem nvP_tau : nvP.tau = 1 / 100 := by
  show (1 : ℝ) * (1 / 100 + nvP.R * 0) = 1 / 100
  ring

theorem nvP_nu : nvP.nu = 1 / 80000 := by
  show (1 / 2 / 2 : ℝ) / (10000 * (2 * 1)) = 1 / 80000
  norm_num

/-- The public data satisfy the released public conditions. -/
theorem nvP_ok : nvP.PublicOK := by
  have hmesh : TimeSchedule.steps nvP.tau (nvP.nu / 3) ≤ 2 ^ nvP.m := by
    rw [nvP_tau, nvP_nu]
    have hth : TimeSchedule.threshold (1 / 100) (1 / 80000 / 3) ≤ 1 := by
      unfold TimeSchedule.threshold
      refine max_le (by norm_num) ?_
      rw [Real.sqrt_le_one]
      norm_num
    have hc : ⌈TimeSchedule.threshold (1 / 100) (1 / 80000 / 3)⌉₊ ≤ 1 :=
      Nat.ceil_le.mpr (by exact_mod_cast hth)
    unfold TimeSchedule.steps
    show 1 + ⌈TimeSchedule.threshold (1 / 100) (1 / 80000 / 3)⌉₊ ≤ 2 ^ 1
    omega
  refine ⟨by norm_num [nvP], by norm_num [nvP], by norm_num [nvP], by norm_num [nvP],
    by norm_num [nvP], by norm_num [nvP], ?_, by norm_num [nvP], by norm_num [nvP],
    by norm_num [nvP], hmesh⟩
  show (0 : ℝ) < 1 / 100 + nvP.R * 0
  norm_num

/-! ### The instance -/

/-- The zero word of the weight-preparation register. -/
def nvC0 : Cfg (Fin 2) := fun _ => false

/-- The word of the forcing label `(true, 0)`: initial-or-forcing bit set, source bit clear. -/
def nvC1 : Cfg (Fin 2) := fun i => decide (i = 0)

/-- The weight preparation: the permutation matrix exchanging `nvC0` and `nvC1`. -/
def nvWp : Matrix (Cfg (Fin 2)) (Cfg (Fin 2)) ℂ :=
  Matrix.of fun i j => if Equiv.swap nvC0 nvC1 i = j then (1 : ℂ) else 0

/-- The supplied unitaries: `U_J = 1`, the private operation `-1` at every label and slot, the
loading `1` and the weight preparation `nvWp`. -/
def nvσ : TOracles nvP.a nvP.m nvP.l ℂ :=
  ⟨1, fun _ _ => cayleyScalar 0 • 1, fun _ => 1, nvWp⟩

/-- The nodes: `v 0 = 1/3`, `v 1 = 1`. -/
def nvV (q : ℕ) : ℝ := if q = 0 then 1 / 3 else 1

/-- The weights: `w 0 = 1`, `w 1 = 0`. -/
def nvW (q : ℕ) : ℝ := if q = 0 then 1 else 0

/-- The forcing vectors: `f 0 = 1`, `f 1 = 0`. -/
def nvF (q : ℕ) : ℂ := if q = 0 then 1 else 0

/-- The solution `x(t) = t`. -/
def nvX (t : ℝ) : ℂ := (t : ℂ)

/-- The homogeneous branch solutions: `1` on the forcing label `(true, 0)`, `0` elsewhere. -/
def nvY (s : Bool × (Fin 1 → Bool)) (_t : ℝ) : ℂ :=
  if s = (true, fun _ => false) then 1 else 0

theorem wordValue_fin_one (w : Fin 1 → Bool) : wordValue w = if w 0 then 1 else 0 := by
  unfold GatePointerEncoding.wordValue
  simp
  cases w 0 <;> simp

theorem fin_one_fun_eq (w : Fin 1 → Bool) : w = fun _ => w 0 := by
  funext i
  rw [Fin.fin_one_eq_zero i]

theorem nv_mass : nvP.mass (nvX 0) (bsW nvP nvW nvF) = 1 := by
  rw [mass_bsW nvP (by norm_num [nvP]) _ nvW (fun q _ => by unfold nvW; split_ifs <;> norm_num)]
  show ‖nvX 0‖ + ∑ q ∈ Finset.range (2 ^ 1), nvW q * ‖nvF q‖ = 1
  simp [nvX, nvW, nvF]

theorem nv_zsrc (s : Bool × (Fin 1 → Bool)) :
    nvP.zsrc (nvX 0) (bsW nvP nvW nvF) s = nvY s 0 := by
  obtain ⟨c, w⟩ := s
  cases c
  · unfold GateODE.Time.TParams.zsrc nvY
    simp [nvX]
  · rw [zsrc_bsW nvP (by norm_num [nvP])]
    unfold nvY nvW nvF
    rw [wordValue_fin_one]
    rcases (fin_one_fun_eq w) with hw
    cases h : w 0
    · have : w = fun _ => false := by rw [hw, h]
      simp [this]
    · have : w ≠ fun _ => false := by
        intro e
        rw [e] at h
        exact absurd h (by decide)
      simp [this]

/-- **Every condition of `BInstanceOK` holds** for the explicit data. -/
theorem nv_instance :
    BInstanceOK nvP (1 : ℂ) nvσ nvV nvW nvF (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0)
      (fun _ => 1) nvX nvY 0 0 0 := by
  have hmass := nv_mass
  constructor
  · exact isUnitary_one
  · intro z r _
    exact isUnitary_smul_one 0 _ (cayleyScalar_norm 0)
  · intro z r _
    have e : branchHB nvP nvV (fun _ _ => 0) (fun _ _ => 0) z r =
        ((0 : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
      ext
      simp [branchHB]
    rw [e]
    exact clock_scalar 0 0 (by norm_num)
  · intro s r _; exact star_zero _
  · intro s r _; exact star_zero _
  · intro s r _; simp
  · intro s r _; simp
  · intro s r _ w; simp
  · intro q _
    unfold nvV
    split_ifs <;> norm_num [nvP]
  · intro q _
    unfold nvW
    split_ifs <;> norm_num
  · intro s; exact isUnitary_one
  · exact (permMat_unitary (Equiv.swap nvC0 nvC1)).1
  · exact (permMat_unitary (Equiv.swap nvC0 nvC1)).2
  · intro w
    show nvWp w (fun _ => false) =
      ((Real.sqrt (‖nvP.zsrc (nvX 0) (bsW nvP nvW nvF) (w 0, Fin.tail w)‖ /
        nvP.mass (nvX 0) (bsW nvP nvW nvF)) : ℝ) : ℂ)
    rw [nv_mass, nv_zsrc]
    unfold nvWp nvY
    simp only [Matrix.of_apply]
    by_cases hw : w = nvC1
    · subst hw
      have h1 : ((nvC1 0, Fin.tail nvC1) : Bool × (Fin 1 → Bool)) = (true, fun _ => false) := by
        decide
      have h2 : Equiv.swap nvC0 nvC1 nvC1 = (fun _ => false) := Equiv.swap_apply_right _ _
      rw [h2, h1]
      simp
    · have h1 : ((w 0, Fin.tail w) : Bool × (Fin 1 → Bool)) ≠ (true, fun _ => false) := by
        intro h
        apply hw
        have h0 : w 0 = true := congrArg Prod.fst h
        have ht : Fin.tail w = fun _ => false := congrArg Prod.snd h
        funext i
        fin_cases i
        · simp [nvC1, h0]
        · have := congrFun ht 0
          simpa [nvC1, Fin.tail] using this
      have h2 : Equiv.swap nvC0 nvC1 w ≠ (fun _ => false) := by
        intro h
        apply hw
        rw [Equiv.swap_apply_eq_iff] at h
        rw [h]
        exact Equiv.swap_apply_left _ _
      rw [if_neg h2, if_neg h1]
      simp
  · intro h
    exact absurd (by simp [nvX]) h
  · intro w hw hf
    rw [wordValue_fin_one] at hw hf ⊢
    cases h : w 0
    · simp [h, nvF] at hf ⊢
      show (1 : ℂ →L[ℂ] ℂ) 1 = unitDirection 1
      simp [unitDirection]
    · simp [h, nvW] at hw
  · intro u _
    have h := ((hasDerivAt_id u).ofReal_comp).hasDerivWithinAt (s := Set.Icc 0 nvP.T)
    exact h.congr_deriv (by simp)
  · intro u _ w; simp
  · intro u _ u' _; simp
  · exact le_rfl
  · intro s r _; simp [gens]
  · intro s u _
    exact hasDerivWithinAt_const _ _ _ |>.congr_deriv (by simp)
  · intro s
    rw [nv_zsrc]
    rfl
  · have hsum : ∑ s, nvY s nvP.T = 1 := by
      unfold nvY
      rw [Finset.sum_ite_eq']
      simp
    rw [hsum]
    simp [nvX]
  · simp [nvX]
  · rw [hmass]
    simp [nvX]
  · rw [hmass]
    norm_num [nvP]

/-- **`outcomeB` applies to the explicit data**: the released protocol on the public data `nvP`
with the seed `1` satisfies the released `Outcome` for `x(1) = 1` (success probability at least
`175/256`, conditional output within trace distance `ε = 1/2` of `x(1)/‖x(1)‖`). -/
theorem nvB_outcome : nvP.Outcome (1 : ℂ) norm_one nvP_ok.g_ge nvσ (nvX nvP.T) :=
  outcomeB nvP nvP_ok (1 : ℂ) norm_one nvσ nvV nvW nvF (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0)
    (fun _ => 1) nvX nvY 0 0 0 nv_instance

end

end SparseHamiltonian.GateSelect.ODE
