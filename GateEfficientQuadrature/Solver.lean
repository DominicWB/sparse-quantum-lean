import GateEfficientQuadrature.Paper
import GateEfficientSelect.ODE.Theorem

/-!
# The left-endpoint quadrature in the solver on branch-dependent meshes

`GateSelect.ODE.solverB` (the time-dependent part of Theorem `ode:thm:gates` on the
branch-dependent meshes of Lemma `ode:lem:gate-select`) assumes the source certificate of
`ode:eq:gate-source-certificates` for its positive source quadrature. Here the quadrature is the
explicit left-endpoint quadrature of the proof of the theorem with `n` nodes, `1 ≤ n ≤ 2^m`
(the source register of the released protocol has `m` bits; a quadrature with more nodes needs
a larger `m`):

* nodes `vQ n q = q T / n` and weights `wQ n q = T / n` for `q < n`; the remaining forcing
  labels (of the `2^m` forcing labels `(true, q)`) are padding with the node `T` and the weight
  `0` (`vQ`, `wQ`), so that the quadrature mass is
  `quadMass x(0) f T n = ‖x(0)‖ + ∑_{q < n} (T / n) ‖f_q‖` (`mass_wQ`);
* `quad_left`: every family of homogeneous branch solutions of `BInstanceOK` satisfies the source
  certificate `‖x(T) - ∑_s y_s(T)‖ ≤ (Λ b_s + L) T² / (2n) + T δ` (`cert_left` on the labels);
* `LInstanceOK`: the conditions of `BInstanceOK` with this quadrature, the certificate replaced by
  the bounds `‖G(u)‖ ≤ Λ`, `Lip(b) ≤ L`, `‖f_q‖ ≤ b_s` and `‖b(q T / n) - f_q‖ ≤ δ`, and the
  budget with `κ = (Λ b_s + L) T² / (2n) + T δ`; `LInstanceOK.toB` gives `BInstanceOK`;
* `outcomeL`, `solverL`: the released protocol, counts and outcome (exact gates);
* `budget_of_paper`, `disc_of_paper`: the budget fields from the paper's parameters
  (`B ≤ ḡ ‖x(T)‖` with `g = 2ḡ`; the certificate bound `κ ≤ ν B` and `|B_n - B| ≤ ν B` with
  `ν ≤ 1/2`), and `nu_paper`: the paper's `ν = ε / (10⁴ ḡ)` with `g = 2ḡ` leaves `ε / (10⁴ g)`
  of the released budget for the branch discretisation `T (βG T / 2^m + δG)`;
* `budget_disc_paper`: with the exact samples, the paper's `ν` and the paper's number of nodes
  `n ≥ T² (Λ b_* + L) / (2 ν B)`, the fields `budget` and `disc` of `LInstanceOK` hold whenever
  `B ≤ ḡ ‖x(T)‖` for `g = 2ḡ` and `T (βG T / 2^m + δG) ≤ ε / (10⁴ g)`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateQuad

noncomputable section
open Set
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire)
open GateODE (Label ClockPromise)
open GateODE.Time (TParams TOracles gens)
open GatePointerEncoding (wordValue wordEquivFin)
open TimeDependentODE (SolvesODE Accretive)
open ODEStateNormalization (unitDirection)
open GateSelect.ODE (BInstanceOK startB addrB branchHB bsW)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]

variable (p : TParams)

/-- The left-endpoint nodes `q T / n` (`q < n`), padded with `T`. -/
def vQ (n q : ℕ) : ℝ := if q < n then q * p.T / n else p.T

/-- The left-endpoint weights `T / n` (`q < n`), padded with `0`. -/
def wQ (n q : ℕ) : ℝ := if q < n then p.T / n else 0

theorem vQ_mem (hT : 0 ≤ p.T) (n : ℕ) : ∀ q < p.M, 0 ≤ vQ p n q ∧ vQ p n q ≤ p.T := by
  intro q _
  unfold vQ
  split_ifs with h
  · have hnR : (0 : ℝ) < n := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le q) h
    have hqn : (q : ℝ) ≤ n := by exact_mod_cast h.le
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hnR]
    nlinarith
  · exact ⟨hT, le_rfl⟩

theorem wQ_nonneg (hT : 0 ≤ p.T) (n : ℕ) : ∀ q < p.M, 0 ≤ wQ p n q := by
  intro q _
  unfold wQ
  split_ifs
  · exact div_nonneg hT (Nat.cast_nonneg _)
  · exact le_rfl

/-- The source mass of the left-endpoint quadrature is `quadMass`. -/
theorem mass_wQ (hT : 0 < p.T) {n : ℕ} (hnM : n ≤ p.M) (x0 : P) (fv : ℕ → P) :
    p.mass x0 (bsW p (wQ p n) fv) = quadMass x0 fv p.T n := by
  rw [GateSelect.ODE.mass_bsW p hT x0 (wQ p n) (wQ_nonneg p hT.le n) fv]
  unfold quadMass
  congr 1
  rw [← Finset.sum_range_add_sum_Ico _ hnM]
  have h2 : ∑ q ∈ Finset.Ico n p.M, wQ p n q * ‖fv q‖ = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    have hq' : ¬ q < n := not_lt.mpr (Finset.mem_Ico.mp hq).1
    simp [wQ, hq']
  rw [h2, add_zero]
  apply Finset.sum_congr rfl
  intro q hq
  simp [wQ, Finset.mem_range.mp hq]

/-- The source word with the value `q < 2^m`. -/
def wordOf (q : ℕ) (hq : q < p.M) : Fin p.m → Bool := (wordEquivFin p.m).symm ⟨q, hq⟩

theorem wordValue_wordOf (q : ℕ) (hq : q < p.M) : wordValue (wordOf p q hq) = q := by
  have h : wordEquivFin p.m (wordOf p q hq) = ⟨q, hq⟩ := (wordEquivFin p.m).apply_symm_apply _
  have h2 := congrArg Fin.val h
  rw [GatePointerEncoding.wordEquivFin_apply, GatePointerEncoding.wordFin_val] at h2
  exact h2

/-- The sum over the source labels: the initial labels and the forcing labels. -/
theorem sum_labels {E : Type*} [AddCommMonoid E] (F : Bool × (Fin p.m → Bool) → E) :
    ∑ s, F s = ∑ w, F (false, w) + ∑ w, F (true, w) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  exact add_comm _ _

/-- The sum over the source words as a sum over their values. -/
theorem sum_words {E : Type*} [AddCommMonoid E] (F : (Fin p.m → Bool) → E) :
    ∑ w, F w = ∑ q ∈ Finset.range p.M, if h : q < p.M then F (wordOf p q h) else 0 := by
  rw [← Fin.sum_univ_eq_sum_range (fun q => if h : q < p.M then F (wordOf p q h) else 0) p.M,
    ← Equiv.sum_comp (wordEquivFin p.m).symm F]
  apply Finset.sum_congr rfl
  intro i _
  rw [dif_pos i.isLt]
  rfl

/-- **The source certificate of the left-endpoint quadrature on the labels of the released
protocol.** For a solution `x` of `x' = -G(u) x + b(u)` on `[0, T]` with an accretive generator,
`‖G(u)‖ ≤ Λ`, an `L`-Lipschitz forcing and samples `f_q` (`q < n`) with `‖f_q‖ ≤ b_s` and
`‖b(q T / n) - f_q‖ ≤ δ`, every family of homogeneous branch solutions of the left-endpoint
quadrature (the fields `branch_sol`, `branch_init` of `BInstanceOK`) satisfies
`‖x(T) - ∑_s y_s(T)‖ ≤ (Λ b_s + L) T² / (2n) + T δ`. -/
theorem quad_left (hT : 0 < p.T) {n : ℕ} (hn : 0 < n) (hnM : n ≤ p.M)
    (G : ℝ → P →L[ℂ] P) (b x : ℝ → P) (fv : ℕ → P) (ys : Bool × (Fin p.m → Bool) → ℝ → P)
    (Λ L δb bs : ℝ) (hL : 0 ≤ L)
    (hx : SolvesODE G b x 0 p.T) (hG : ∀ u ∈ Icc 0 p.T, Accretive (G u))
    (hGn : ∀ u ∈ Icc 0 p.T, ‖G u‖ ≤ Λ)
    (hbL : ∀ u ∈ Icc 0 p.T, ∀ u' ∈ Icc 0 p.T, ‖b u - b u'‖ ≤ L * |u - u'|)
    (hf : ∀ q < n, ‖fv q‖ ≤ bs) (hbf : ∀ q < n, ‖b (q * p.T / n) - fv q‖ ≤ δb)
    (hys : ∀ s, SolvesODE G (fun _ => 0) (ys s) (startB p (vQ p n) s) p.T)
    (hys0 : ∀ s, ys s (startB p (vQ p n) s) = p.zsrc (x 0) (bsW p (wQ p n) fv) s) :
    ‖x p.T - ∑ s, ys s p.T‖ ≤ (Λ * bs + L) * p.T ^ 2 / (2 * n) + p.T * δb := by
  set Y : ℕ → ℝ → P := fun q t => if h : q < p.M then ys (true, wordOf p q h) t else 0
    with hY_def
  -- labels with the source vector `0` contribute `0`
  have hzero : ∀ s, p.zsrc (x 0) (bsW p (wQ p n) fv) s = 0 → ys s p.T = 0 := by
    intro s hs
    have hst := GateSelect.ODE.startB_mem p (vQ p n) (vQ_mem p hT.le n) hT.le s
    exact homog_eq_zero hst.2 (hys s) (fun u hu => hG u ⟨hst.1.trans hu.1, hu.2⟩)
      ((hys0 s).trans hs)
  have hsum : ∑ s, ys s p.T = ys (false, fun _ => false) p.T + ∑ q ∈ Finset.range n, Y q p.T := by
    rw [sum_labels]
    congr 1
    · rw [Finset.sum_eq_single (fun _ => false)]
      · intro w _ hw
        apply hzero
        simp [GateODE.Time.TParams.zsrc, hw]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [sum_words p (fun w => ys (true, w) p.T), ← Finset.sum_range_add_sum_Ico _ hnM]
      have hIco : ∑ q ∈ Finset.Ico n p.M,
          (if h : q < p.M then ys (true, wordOf p q h) p.T else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro q hq
        obtain ⟨hnq, hqM⟩ := Finset.mem_Ico.mp hq
        rw [dif_pos hqM]
        apply hzero
        rw [GateSelect.ODE.zsrc_bsW p hT, wordValue_wordOf]
        simp [wQ, not_lt.mpr hnq]
      rw [hIco, add_zero]
  have hqM : ∀ q < n, q < p.M := fun q hq => lt_of_lt_of_le hq hnM
  have hstart : ∀ q (hq : q < n),
      startB p (vQ p n) (true, wordOf p q (hqM q hq)) = q * p.T / n := by
    intro q hq
    simp [startB, wordValue_wordOf, vQ, hq]
  have hYfun : ∀ q (hq : q < n), Y q = ys (true, wordOf p q (hqM q hq)) := by
    intro q hq
    funext t
    simp only [hY_def, dif_pos (hqM q hq)]
  have hcert := cert_left (Y := Y) (f := fv) (δ := δb) (bs := bs) hT.le hn hx hG hGn hbL hL hf
    hbf (y0 := ys (false, fun _ => false))
    (by
      have h := hys (false, fun _ => false)
      simpa [startB] using h)
    (by
      have h := hys0 (false, fun _ => false)
      simpa [startB, GateODE.Time.TParams.zsrc] using h)
    (fun q hq => by
      rw [hYfun q hq, ← hstart q hq]
      exact hys _)
    (fun q hq => by
      rw [hYfun q hq, ← hstart q hq, hys0, GateSelect.ODE.zsrc_bsW p hT, wordValue_wordOf]
      simp [wQ, hq])
  rw [hsum, ← sub_sub]
  exact hcert

variable [CompleteSpace P]

/-- The conditions on an instance of the solver on branch-dependent meshes with the left-endpoint
quadrature with `n` nodes: those of `GateSelect.ODE.BInstanceOK` for the nodes `vQ n` and the
weights `wQ n`, the source certificate replaced by the bounds of the generator and the forcing
and the sample errors, and the budget with
`κ = (Λ b_s + L) T² / (2n) + T δ`. -/
structure LInstanceOK (n : ℕ) (v₀ : P) (σ : TOracles p.a p.m p.l P) (fv : ℕ → P)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P) (b x : ℝ → P)
    (ys : Bool × (Fin p.m → Bool) → ℝ → P) (βG δG Λ L bs δb : ℝ) : Prop where
  n_pos : 0 < n
  n_le : n ≤ p.M
  uj : IsUnitary σ.UJ
  priv : ∀ z, ∀ r < p.M, IsUnitary (σ.D z r)
  clock : ∀ z, ∀ r < p.M,
    ClockPromise σ.UJ (σ.D z r) (branchHB p (vQ p n) Hb Lb z r) p.Q p.qbar
  selfH : ∀ s, ∀ r < p.M, star (Hb s r) = Hb s r
  selfL : ∀ s, ∀ r < p.M, star (Lb s r) = Lb s r
  normH : ∀ s, ∀ r < p.M, ‖Hb s r‖ ≤ p.lamH
  normL : ∀ s, ∀ r < p.M, ‖Lb s r‖ ≤ p.lamD
  psd : ∀ s, ∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (Lb s r w)).re
  load_unitary : ∀ s, IsUnitary (σ.J s)
  prep_left : σ.Wp.conjTranspose * σ.Wp = 1
  prep_right : σ.Wp * σ.Wp.conjTranspose = 1
  prep : p.WpPromise σ (x 0) (bsW p (wQ p n) fv)
  init_load : x 0 ≠ 0 → σ.J (false, fun _ => false) v₀ = unitDirection (x 0)
  forcing_load : ∀ w : Fin p.m → Bool, wordValue w < n → fv (wordValue w) ≠ 0 →
    σ.J (true, w) v₀ = unitDirection (fv (wordValue w))
  solves : SolvesODE G b x 0 p.T
  accretive : ∀ u ∈ Icc 0 p.T, Accretive (G u)
  lipG : ∀ u ∈ Icc 0 p.T, ∀ u' ∈ Icc 0 p.T, ‖G u - G u'‖ ≤ βG * |u - u'|
  βG_nonneg : 0 ≤ βG
  sampleG : ∀ s, ∀ r < p.M, ‖G (addrB p (vQ p n) s r) - gens (Hb s) (Lb s) r‖ ≤ δG
  normG : ∀ u ∈ Icc 0 p.T, ‖G u‖ ≤ Λ
  lipb : ∀ u ∈ Icc 0 p.T, ∀ u' ∈ Icc 0 p.T, ‖b u - b u'‖ ≤ L * |u - u'|
  L_nonneg : 0 ≤ L
  sample_norm : ∀ q < n, ‖fv q‖ ≤ bs
  sample_err : ∀ q < n, ‖b (q * p.T / n) - fv q‖ ≤ δb
  branch_sol : ∀ s, SolvesODE G (fun _ => 0) (ys s) (startB p (vQ p n) s) p.T
  branch_init : ∀ s, ys s (startB p (vQ p n) s) = p.zsrc (x 0) (bsW p (wQ p n) fv) s
  target_ne : x p.T ≠ 0
  budget : quadMass (x 0) fv p.T n ≤ p.g * ‖x p.T‖
  disc : (Λ * bs + L) * p.T ^ 2 / (2 * n) + p.T * δb +
      p.T * (βG * (p.T / p.M) + δG) * quadMass (x 0) fv p.T n ≤
    p.ε * quadMass (x 0) fv p.T n / (2000 * p.g)

variable {p}

/-- **An instance with the left-endpoint quadrature satisfies `BInstanceOK`** with the source
certificate `κ = (Λ b_s + L) T² / (2n) + T δ` (`quad_left`). -/
theorem LInstanceOK.toB (hp : p.PublicOK) {n : ℕ} {v₀ : P} {σ : TOracles p.a p.m p.l P}
    {fv : ℕ → P} {Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P} {G : ℝ → P →L[ℂ] P}
    {b x : ℝ → P} {ys : Bool × (Fin p.m → Bool) → ℝ → P} {βG δG Λ L bs δb : ℝ}
    (hI : LInstanceOK p n v₀ σ fv Hb Lb G b x ys βG δG Λ L bs δb) :
    BInstanceOK p v₀ σ (vQ p n) (wQ p n) fv Hb Lb G b x ys βG δG
      ((Λ * bs + L) * p.T ^ 2 / (2 * n) + p.T * δb) where
  uj := hI.uj
  priv := hI.priv
  clock := hI.clock
  selfH := hI.selfH
  selfL := hI.selfL
  normH := hI.normH
  normL := hI.normL
  psd := hI.psd
  nodes := vQ_mem p hp.T_pos.le n
  weights := wQ_nonneg p hp.T_pos.le n
  load_unitary := hI.load_unitary
  prep_left := hI.prep_left
  prep_right := hI.prep_right
  prep := hI.prep
  init_load := hI.init_load
  forcing_load := fun w hw hf => hI.forcing_load w (by
    by_contra h
    exact hw (by simp [wQ, h])) hf
  solves := hI.solves
  accretive := hI.accretive
  lipG := hI.lipG
  βG_nonneg := hI.βG_nonneg
  sampleG := hI.sampleG
  branch_sol := hI.branch_sol
  branch_init := hI.branch_init
  quad := quad_left p hp.T_pos hI.n_pos hI.n_le G b x fv ys Λ L δb bs hI.L_nonneg hI.solves
    hI.accretive hI.normG hI.lipb hI.sample_norm hI.sample_err hI.branch_sol hI.branch_init
  target_ne := hI.target_ne
  budget := by
    rw [mass_wQ p hp.T_pos hI.n_le]
    exact hI.budget
  disc := by
    rw [mass_wQ p hp.T_pos hI.n_le]
    exact hI.disc

variable (p)

variable [FiniteDimensional ℂ P]

/-- **The released time-dependent protocol is correct with the left-endpoint quadrature on
branch-dependent meshes** for every instance satisfying `LInstanceOK`. -/
theorem outcomeL (hp : p.PublicOK) (v₀ : P) (hv : ‖v₀‖ = 1) (σ : TOracles p.a p.m p.l P)
    (n : ℕ) (fv : ℕ → P) (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P)
    (G : ℝ → P →L[ℂ] P) (b x : ℝ → P) (ys : Bool × (Fin p.m → Bool) → ℝ → P)
    (βG δG Λ L bs δb : ℝ) (hI : LInstanceOK p n v₀ σ fv Hb Lb G b x ys βG δG Λ L bs δb) :
    p.Outcome v₀ hv hp.g_ge σ (x p.T) :=
  GateSelect.ODE.outcomeB p hp v₀ hv σ (vQ p n) (wQ p n) fv Hb Lb G b x ys βG δG _ (hI.toB hp)

/-- **Gate-efficient dissipative ODE solver with the left-endpoint quadrature, exact gates**
(Theorem `ode:thm:gates`, time-dependent part, on the branch-dependent meshes of Lemma
`ode:lem:gate-select`, with the sufficient positive quadrature of its proof). The protocol is that
of `GateSelect.ODE.solverB` (the released `GateODE.Time.solver`), with its validity, worst-case
counts, register and degree bounds, and every instance satisfying `LInstanceOK` satisfies the
released `Outcome` for `x(T)`. -/
theorem solverL (hp : p.PublicOK) (v₀ : P) (hv : ‖v₀‖ = 1) :
    (∀ j, ∀ g ∈ p.trialC j, g.Valid Wire.anc) ∧
    ((p.protocol v₀ hv hp.g_ge).worstCost p.wGate : ℝ) ≤
      80 * p.g * p.prepGates + 40 * p.g * p.reflGates ∧
    ((p.protocol v₀ hv hp.g_ge).worstCost p.wPriv : ℝ) ≤ 480 * p.g * p.d ∧
    ((p.protocol v₀ hv hp.g_ge).worstCost p.wUJ : ℝ) ≤ 960 * p.g * p.d ∧
    ((p.protocol v₀ hv hp.g_ge).worstCost p.wLoad : ℝ) ≤ 80 * p.g ∧
    ((p.protocol v₀ hv hp.g_ge).worstCost p.wPrep : ℝ) ≤ 160 * p.g ∧
    ((p.protocol v₀ hv hp.g_ge).worstCost p.wSeed : ℝ) ≤ 40 * p.g ∧
    p.prepGates = 200 * (p.d + 1) * (p.a + p.m + p.r + 1) + 3 * (2 ^ p.l * (2 * p.l + 1)) ∧
    p.reflGates = 6 * (2 * p.a + 4 * p.m + 6 * p.r + 4 + p.l) + 4 ∧
    Fintype.card p.W = 4 * p.a + 8 * p.m + 12 * p.r + 2 * p.l + 8 ∧
    (p.d : ℝ) ≤ 128 * (p.tau * p.qbar + p.Q * (1 + Real.log (3 / p.nu))) ∧
    2 * p.d + 2 ≤ 2 ^ p.r ∧ 2 ^ p.r ≤ 4 * (p.d + 1) ∧
    p.J + 2 ≤ 2 ^ p.l ∧ 2 ^ p.l < 2 * (p.J + 2) ∧
    (p.J : ℝ) ≤ p.R * (p.T * p.lamD + 2 * Real.log (512 / p.nu)) / Real.pi + 3 ∧
    ∀ (σ : TOracles p.a p.m p.l P) (n : ℕ) (fv : ℕ → P)
      (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P) (b x : ℝ → P)
      (ys : Bool × (Fin p.m → Bool) → ℝ → P) (βG δG Λ L bs δb : ℝ),
      LInstanceOK p n v₀ σ fv Hb Lb G b x ys βG δG Λ L bs δb →
        p.Outcome v₀ hv hp.g_ge σ (x p.T) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, -⟩ :=
    GateSelect.ODE.solverB p hp v₀ hv
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    fun σ n fv Hb Lb G b x ys βG δG Λ L bs δb hI =>
      outcomeL p hp v₀ hv σ n fv Hb Lb G b x ys βG δG Λ L bs δb hI⟩

/-! ### The budget fields from the paper's parameters -/

/-- **The budget field from the paper's normalisation.** `B_n ≤ 2B` and `B ≤ ḡ ‖x(T)‖` give
`B_n ≤ g ‖x(T)‖` for the public `g = 2ḡ`. -/
theorem budget_of_paper {Bm B gbar xT : ℝ} (hBm : Bm ≤ 2 * B) (hB : B ≤ gbar * xT) :
    Bm ≤ (2 * gbar) * xT := by
  linarith

/-- **The discretisation budget from the paper's parameters.** If the certificate bound `κ` is at
most `ν B`, `|B_n - B| ≤ ν B` with `0 ≤ ν ≤ 1/2`, the branch discretisation
`T (βG T / 2^m + δG)` is at most `ν'` and `2ν + ν' ≤ ε / (2000 g)`, then
`κ + T (βG T / 2^m + δG) B_n ≤ ε B_n / (2000 g)`. -/
theorem disc_of_paper {κ B Bm ν ν' D ε g : ℝ} (hB : 0 < B) (hν : 0 ≤ ν)
    (hν2 : ν ≤ 1 / 2) (hκ : κ ≤ ν * B) (hm : |Bm - B| ≤ ν * B) (hD : D ≤ ν')
    (hsum : 2 * ν + ν' ≤ ε / (2000 * g)) : κ + D * Bm ≤ ε * Bm / (2000 * g) := by
  obtain ⟨hm1, _⟩ := abs_le.mp hm
  have hBm : B ≤ 2 * Bm := by nlinarith
  have hBm0 : 0 < Bm := by nlinarith
  have h1 : κ ≤ 2 * ν * Bm := by nlinarith
  have h2 : D * Bm ≤ ν' * Bm := mul_le_mul_of_nonneg_right hD hBm0.le
  have h3 : (2 * ν + ν') * Bm ≤ ε / (2000 * g) * Bm := mul_le_mul_of_nonneg_right hsum hBm0.le
  calc κ + D * Bm ≤ 2 * ν * Bm + ν' * Bm := add_le_add h1 h2
    _ = (2 * ν + ν') * Bm := by ring
    _ ≤ ε / (2000 * g) * Bm := h3
    _ = ε * Bm / (2000 * g) := by ring

/-- **The paper's precision.** With `ν = ε / (10⁴ ḡ)` (Theorem `ode:thm:gates`), the public
`g = 2ḡ` and `ν' = ε / (10⁴ g)`, `2ν + ν' = ε / (2000 g)`. -/
theorem nu_paper (ε gbar : ℝ) (hg : 0 < gbar) :
    2 * (ε / (10 ^ 4 * gbar)) + ε / (10 ^ 4 * (2 * gbar)) = ε / (2000 * (2 * gbar)) := by
  field_simp
  ring

/-- **The budget fields of `LInstanceOK` from the paper's choice of parameters.** For the exact
samples `f_q = b(q T / n)` (`b_s = b_*`, `δ = 0`), `‖b(u)‖ ≤ b_*` and `Lip(b) ≤ L` on `[0, T]`,
`Λ ≥ 0`, the public `g = 2ḡ`, `0 < B ≤ ḡ ‖x(T)‖` for `B = contMass x(0) b T`, the paper's
precision `ν = ε / (10⁴ ḡ)`, `n ≥ 1` nodes with `n ≥ T² (Λ b_* + L) / (2 ν B)` and the branch
discretisation `T (βG T / 2^m + δG) ≤ ε / (10⁴ g)`, the fields `budget` and `disc` of
`LInstanceOK` hold. -/
theorem budget_disc_paper {E : Type*} [NormedAddCommGroup E] (hp : p.PublicOK) (b x : ℝ → E)
    {n : ℕ} {Λ L bstar gbar βG δG : ℝ} (hn : 0 < n) (hΛ : 0 ≤ Λ)
    (hb : ∀ u ∈ Icc 0 p.T, ‖b u‖ ≤ bstar)
    (hbL : ∀ u ∈ Icc 0 p.T, ∀ u' ∈ Icc 0 p.T, ‖b u - b u'‖ ≤ L * |u - u'|)
    (hg : p.g = 2 * gbar) (hB : 0 < contMass (x 0) b p.T)
    (hBg : contMass (x 0) b p.T ≤ gbar * ‖x p.T‖)
    (hnodes : p.T ^ 2 * (Λ * bstar + L) /
      (2 * (p.ε / (10 ^ 4 * gbar)) * contMass (x 0) b p.T) ≤ n)
    (hD : p.T * (βG * (p.T / p.M) + δG) ≤ p.ε / (10 ^ 4 * p.g)) :
    quadMass (x 0) (fun q => b (q * p.T / n)) p.T n ≤ p.g * ‖x p.T‖ ∧
      (Λ * bstar + L) * p.T ^ 2 / (2 * n) + p.T * 0 +
          p.T * (βG * (p.T / p.M) + δG) * quadMass (x 0) (fun q => b (q * p.T / n)) p.T n ≤
        p.ε * quadMass (x 0) (fun q => b (q * p.T / n)) p.T n / (2000 * p.g) := by
  have hT := hp.T_pos.le
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hgbar : 1 / 2 ≤ gbar := by
    have := hp.g_ge
    linarith
  have hgpos : 0 < gbar := by linarith
  have hε := hp.ε_pos
  have hε2 := hp.ε_half
  have hbs : 0 ≤ bstar := (norm_nonneg _).trans (hb 0 ⟨le_rfl, hT⟩)
  set ν : ℝ := p.ε / (10 ^ 4 * gbar) with hν_def
  have hν0 : 0 < ν := by positivity
  have hν2 : ν ≤ 1 / 2 := by
    rw [hν_def, div_le_iff₀ (by positivity)]
    nlinarith
  have hνB : 0 < ν * contMass (x 0) b p.T := mul_pos hν0 hB
  have hnodes' : p.T ^ 2 * (Λ * bstar + L) / (2 * ν * contMass (x 0) b p.T) ≤ n := by
    simpa only [mul_assoc] using hnodes
  have hκ := nodes_sufficient hn hνB hnodes'
  have hmass := mass_left (f := fun q => b (q * p.T / n)) (δ := 0) hT hn hbL
    (fun q _ => by simp) (x 0)
  have hLC : L * p.T ^ 2 / (2 * n) ≤ p.T ^ 2 * (Λ * bstar + L) / (2 * n) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [sq_nonneg p.T, mul_nonneg hΛ hbs]
  have hm : |quadMass (x 0) (fun q => b (q * p.T / n)) p.T n - contMass (x 0) b p.T| ≤
      ν * contMass (x 0) b p.T := by
    rw [mul_zero, add_zero] at hmass
    exact hmass.trans (hLC.trans hκ)
  obtain ⟨-, -, -, hB2⟩ := mass_bounds hB (by linarith) hm
  refine ⟨?_, ?_⟩
  · rw [hg]
    exact budget_of_paper hB2 hBg
  · have hsum : 2 * ν + p.ε / (10 ^ 4 * p.g) ≤ p.ε / (2000 * p.g) := by
      rw [hg, hν_def, nu_paper p.ε gbar hgpos]
    apply disc_of_paper hB hν0.le hν2 _ hm hD hsum
    rw [mul_zero, add_zero, mul_comm (Λ * bstar + L) (p.T ^ 2)]
    exact hκ

end

end SparseHamiltonian.GateQuad
