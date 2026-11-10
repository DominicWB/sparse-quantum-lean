import GateEfficientMesh.ODE.Target

/-!
# The gate-level time-dependent ODE solver under integrated certificates, exact gates

Theorem `ode:thm:gates`: "For time-dependent generators,
require the Lipschitz bounds and represented-sample certificates of Lemma
`ode:lem:gate-select`; more generally, a certificate for the same uniform meshes suffices." The
released `GateODE.Time.solver` proves the theorem under the Lipschitz budget
`GateODE.Time.TParams.discretisation`. Here the same protocol, with the same counts, is correct
under the integrated certificate on the uniform slots:

* `ode_time_solver_certified`: for every instance with the conditions on the supplied unitaries
  (`CoreOK`), a classical piecewise solution with one accretive, interval-integrable generator
  piece and one interval-integrable forcing piece per slot, `x(T) ≠ 0`, `B ≤ g ‖x(T)‖`, and
  `slotCertificate ≤ ε B/(2000 g)`, the released guarantee `Outcome` holds.
* `slotCertificate_le_discretisation`, `certified_of_instanceOK`: every instance of the released
  theorem (Lipschitz path, sample errors, released budget) satisfies these hypotheses with the
  restricted paths as pieces, so the hypotheses are satisfiable and the released theorem is a
  special case.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateMesh.ODE

noncomputable section
open ContinuousLinearMap MeasureTheory Set OracleCircuit GateCircuit
open GateCircuit.Sim (Wire)
open GateODE.Time (TParams TOracles gens)
open TimeDependentODE (SolvesODE Accretive)
open scoped InnerProduct BigOperators Real

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Satisfiability: the released Lipschitz instances -/

omit [CompleteSpace P] in
/-- **The released budget bounds the certificate.** For a `βG`-Lipschitz generator and a
`βb`-Lipschitz forcing with sample errors `δG`, `δb` at the slot points and `‖b‖ ≤ b_max`, the
slot certificate of the restricted paths is at most the released discretisation budget. -/
theorem slotCertificate_le_discretisation (p : TParams) (hp : p.PublicOK)
    (Hs Ls : ℕ → P →L[ℂ] P) (bs : ℕ → P) (G : ℝ → P →L[ℂ] P) (b : ℝ → P)
    (r₀ βG δG βb δb bmax : ℝ) (hr₀ : 0 ≤ r₀) (hbmax : 0 ≤ bmax)
    (hGLip : ∀ u ∈ Icc 0 p.T, ∀ u' ∈ Icc 0 p.T, ‖G u - G u'‖ ≤ βG * |u - u'|)
    (hGs : ∀ r < p.M, ‖G (r * p.T / p.M) - gens Hs Ls r‖ ≤ δG)
    (hbLip : ∀ u ∈ Icc 0 p.T, ∀ u' ∈ Icc 0 p.T, ‖b u - b u'‖ ≤ βb * |u - u'|)
    (hbs : ∀ r < p.M, ‖b (r * p.T / p.M) - bs r‖ ≤ δb)
    (hb : ∀ u ∈ Icc 0 p.T, ‖b u‖ ≤ bmax) :
    slotCertificate p Hs Ls bs (fun _ => G) (fun _ => b) r₀ bmax ≤
      p.discretisation βG δG βb δb bmax r₀ := by
  have hT := hp.T_pos
  have hmesh := isMesh_slotMesh hT.le p.m
  have hslot : ∀ r : ℕ, slotMesh p.T p.m r = r * p.T / p.M := by
    intro r
    unfold slotMesh
    push_cast
    ring
  have hcG := slot_certificate_le_of_lipschitz G (gens Hs Ls) hT.le p.m hGLip
    (fun k hk => by rw [hslot]; exact hGs k hk)
  have hcb := slot_certificate_le_of_lipschitz b bs hT.le p.m hbLip
    (fun k hk => by rw [hslot]; exact hbs k hk)
  have hM : (0 : ℝ) < p.M := by exact_mod_cast p.M_pos
  have hM2 : ((2 : ℝ) ^ p.m) = p.M := by push_cast; ring
  rw [hM2] at hcG hcb
  have hΛ : 0 ≤ p.lamH + p.lamD := add_nonneg hp.lamH_nonneg hp.lamD_nonneg
  have hδb : 0 ≤ δb := (norm_nonneg _).trans (hbs 0 p.M_pos)
  have hbsn : ∀ k ∈ Finset.range p.M, ‖bs k‖ ≤ bmax + δb := by
    intro k hk
    have hkM := Finset.mem_range.mp hk
    have hmem : (k : ℝ) * p.T / p.M ∈ Icc 0 p.T := by
      rw [← hslot]
      exact ⟨hmesh.nonneg k, hmesh.le_last hkM.le⟩
    calc ‖bs k‖ = ‖b (k * p.T / p.M) - (b (k * p.T / p.M) - bs k)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖b (k * p.T / p.M)‖ + ‖b (k * p.T / p.M) - bs k‖ := norm_sub_le _ _
      _ ≤ bmax + δb := add_le_add (hb _ hmem) (hbs k hkM)
  have hsum : ∑ k ∈ Finset.range p.M, ‖bs k‖ ≤ p.M * (bmax + δb) := by
    refine (Finset.sum_le_sum hbsn).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hX : 0 ≤ r₀ + bmax * p.T := by positivity
  have hq : (p.lamH + p.lamD) * (p.T / p.M) ^ 2 / 2 * ∑ k ∈ Finset.range p.M, ‖bs k‖ ≤
      p.T * ((p.T / p.M) * (p.lamH + p.lamD) * (bmax + δb)) := by
    have h1 : 0 ≤ (p.lamH + p.lamD) * (p.T / p.M) ^ 2 / 2 := by positivity
    calc _ ≤ (p.lamH + p.lamD) * (p.T / p.M) ^ 2 / 2 * (p.M * (bmax + δb)) :=
          mul_le_mul_of_nonneg_left hsum h1
      _ = p.T * ((p.T / p.M) * (p.lamH + p.lamD) * (bmax + δb)) / 2 := by
          field_simp
      _ ≤ p.T * ((p.T / p.M) * (p.lamH + p.lamD) * (bmax + δb)) := by
          have : 0 ≤ p.T * ((p.T / p.M) * (p.lamH + p.lamD) * (bmax + δb)) := by positivity
          linarith
  unfold slotCertificate TParams.discretisation
  have e1 : βG * p.T ^ 2 / (2 * p.M) + p.T * δG ≤ p.T * (βG * (p.T / p.M) + δG) := by
    have hβG : 0 ≤ βG := by
      have h := hGLip p.T ⟨hT.le, le_rfl⟩ 0 ⟨le_rfl, hT.le⟩
      rw [sub_zero, abs_of_pos hT] at h
      exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) hT
    have : βG * p.T ^ 2 / (2 * p.M) ≤ p.T * (βG * (p.T / p.M)) := by
      rw [div_le_iff₀ (by positivity)]
      have : 0 ≤ βG * p.T ^ 2 := by positivity
      field_simp
      nlinarith
    linarith
  have e2 : βb * p.T ^ 2 / (2 * p.M) + p.T * δb ≤ p.T * (βb * (p.T / p.M) + δb) := by
    have hβb : 0 ≤ βb := by
      have h := hbLip p.T ⟨hT.le, le_rfl⟩ 0 ⟨le_rfl, hT.le⟩
      rw [sub_zero, abs_of_pos hT] at h
      exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) hT
    have : βb * p.T ^ 2 / (2 * p.M) ≤ p.T * (βb * (p.T / p.M)) := by
      rw [div_le_iff₀ (by positivity)]
      have : 0 ≤ βb * p.T ^ 2 := by positivity
      field_simp
      nlinarith
    linarith
  have h1 := mul_le_mul_of_nonneg_left (hcG.trans e1) hX
  nlinarith [h1, hcb, e2, hq]

/-- **The released instances satisfy the certified hypotheses.** Every instance of the released
time-dependent solver (`InstanceOK`: a Lipschitz generator and forcing with sampled values and
the released discretisation budget) satisfies the conditions on the supplied unitaries, the
classical piecewise solution conditions on the uniform slots with the restricted paths as
pieces, and the certified budget `slotCertificate ≤ ε B/(2000 g)`. -/
theorem certified_of_instanceOK (p : TParams) (hp : p.PublicOK) {v : P}
    {σ : TOracles p.a p.m p.l P} {Hs Ls : ℕ → P →L[ℂ] P} {G : ℝ → P →L[ℂ] P} {b x : ℝ → P}
    {bs : ℕ → P} {βG δG βb δb bmax : ℝ}
    (hI : p.InstanceOK v σ Hs Ls G b x bs βG δG βb δb bmax) :
    CoreOK p v σ Hs Ls (x 0) bs ∧
    (∀ k < p.M, SolvesODE G b x (slotMesh p.T p.m k) (slotMesh p.T p.m (k + 1))) ∧
    (∀ k < p.M, ∀ u ∈ Icc (slotMesh p.T p.m k) (slotMesh p.T p.m (k + 1)), Accretive (G u)) ∧
    (∀ k < p.M, IntervalIntegrable G volume (slotMesh p.T p.m k) (slotMesh p.T p.m (k + 1))) ∧
    (∀ k < p.M, IntervalIntegrable b volume (slotMesh p.T p.m k) (slotMesh p.T p.m (k + 1))) ∧
    0 ≤ bmax ∧
    (∀ k < p.M, ∀ u ∈ Icc (slotMesh p.T p.m k) (slotMesh p.T p.m (k + 1)), ‖b u‖ ≤ bmax) ∧
    x p.T ≠ 0 ∧ p.mass (x 0) bs ≤ p.g * ‖x p.T‖ ∧
    slotCertificate p Hs Ls bs (fun _ => G) (fun _ => b) ‖x 0‖ bmax ≤
      p.ε * p.mass (x 0) bs / (2000 * p.g) := by
  have hT := hp.T_pos
  have hmesh := isMesh_slotMesh hT.le p.m
  have hsub : ∀ k < p.M, Icc (slotMesh p.T p.m k) (slotMesh p.T p.m (k + 1)) ⊆ Icc 0 p.T :=
    fun k hk => Icc_subset_Icc (hmesh.nonneg k) (hmesh.le_last (Nat.succ_le_of_lt hk))
  have hle : ∀ k, slotMesh p.T p.m k ≤ slotMesh p.T p.m (k + 1) :=
    fun k => hmesh.mono (Nat.le_succ k)
  have hbmax : 0 ≤ bmax := (norm_nonneg _).trans (hI.boundb 0 ⟨le_rfl, hT.le⟩)
  have hGc := TimeDependentExtensions.continuousOn_of_lipschitz G hI.lipG
  have hbc := TimeDependentExtensions.continuousOn_of_lipschitz b hI.lipb
  refine ⟨⟨hI.select, hI.psd, ⟨hI.load_unitary, hI.prep_left, hI.prep_right, hI.prep,
    hI.init_load, hI.forcing_load⟩⟩, fun k hk => ?_, fun k hk u hu => hI.accretive u (hsub k hk hu),
    fun k hk => ?_, fun k hk => ?_, hbmax, fun k hk u hu => hI.boundb u (hsub k hk hu),
    hI.target_ne, hI.budget, ?_⟩
  · exact hI.solves.mono (hmesh.nonneg k) (hmesh.le_last (Nat.succ_le_of_lt hk))
  · exact (hGc.mono (hsub k hk)).intervalIntegrable_of_Icc (hle k)
  · exact (hbc.mono (hsub k hk)).intervalIntegrable_of_Icc (hle k)
  · exact (slotCertificate_le_discretisation p hp Hs Ls bs G b ‖x 0‖ βG δG βb δb bmax
      (norm_nonneg _) hbmax hI.lipG hI.sampleG hI.lipb hI.sampleb hI.boundb).trans hI.disc

/-! ### The certified solver -/

/-- **Gate-efficient dissipative ODE solver under the integrated certificate on the uniform
slots, exact gates** (Theorem `ode:thm:gates`, time-dependent part: "more generally, a
certificate for the same uniform meshes suffices").

The released protocol `TParams.protocol p v` depends only on the public data (including the slot
exponent `m`) and the seed, and has the released validity, worst-case counts, qubits and sizes
of `GateODE.Time.solver`. For every instance with supplied unitaries, represented samples
`H_r, L_r`, forcing samples `b̃_r` and initial state `x(0)` satisfying `CoreOK`, every classical
piecewise solution `x` of `x' = -G_k(u) x + b_k(u)` on the closed slots
`[kT/2^m, (k+1)T/2^m]` (one-sided derivatives at the slot boundaries) with accretive,
interval-integrable generator pieces and interval-integrable forcing pieces bounded by
`b_max ≥ 0`, with `x(T) ≠ 0`, `B ≤ g ‖x(T)‖` for the source mass `B`, and the certified budget
`slotCertificate ≤ ε B/(2000 g)`, the protocol satisfies the released `Outcome`: success
probability at least `175/256 > 2/3`, every successful trial within `ε/500` of `x(T)/‖x(T)‖` up to
a phase, and conditional output within trace distance `ε` of `x(T)/‖x(T)‖`. No Lipschitz bound
and no regularity beyond integrability is used. -/
theorem ode_time_solver_certified [FiniteDimensional ℂ P] (p : TParams) (hp : p.PublicOK) (v : P)
    (hv : ‖v‖ = 1) :
    (∀ j, ∀ g ∈ p.trialC j, g.Valid Wire.anc) ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wGate : ℝ) ≤
      80 * p.g * p.prepGates + 40 * p.g * p.reflGates ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wPriv : ℝ) ≤ 480 * p.g * p.d ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wUJ : ℝ) ≤ 960 * p.g * p.d ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wLoad : ℝ) ≤ 80 * p.g ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wPrep : ℝ) ≤ 160 * p.g ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wSeed : ℝ) ≤ 40 * p.g ∧
    p.prepGates = 200 * (p.d + 1) * (p.a + p.m + p.r + 1) + 3 * (2 ^ p.l * (2 * p.l + 1)) ∧
    p.reflGates = 6 * (2 * p.a + 4 * p.m + 6 * p.r + 4 + p.l) + 4 ∧
    Fintype.card p.W = 4 * p.a + 8 * p.m + 12 * p.r + 2 * p.l + 8 ∧
    (p.d : ℝ) ≤ 128 * (p.tau * p.qbar + p.Q * (1 + Real.log (3 / p.nu))) ∧
    2 * p.d + 2 ≤ 2 ^ p.r ∧ 2 ^ p.r ≤ 4 * (p.d + 1) ∧
    p.J + 2 ≤ 2 ^ p.l ∧ 2 ^ p.l < 2 * (p.J + 2) ∧
    (p.J : ℝ) ≤ p.R * (p.T * p.lamD + 2 * Real.log (512 / p.nu)) / π + 3 ∧
    ∀ (σ : TOracles p.a p.m p.l P) (Hs Ls : ℕ → P →L[ℂ] P) (G : ℕ → ℝ → P →L[ℂ] P)
      (b : ℕ → ℝ → P) (x : ℝ → P) (bs : ℕ → P) (bmax : ℝ),
      CoreOK p v σ Hs Ls (x 0) bs →
      (∀ k < p.M, SolvesODE (G k) (b k) x (slotMesh p.T p.m k) (slotMesh p.T p.m (k + 1))) →
      (∀ k < p.M, ∀ u ∈ Icc (slotMesh p.T p.m k) (slotMesh p.T p.m (k + 1)),
        Accretive (G k u)) →
      (∀ k < p.M, IntervalIntegrable (G k) volume (slotMesh p.T p.m k)
        (slotMesh p.T p.m (k + 1))) →
      (∀ k < p.M, IntervalIntegrable (b k) volume (slotMesh p.T p.m k)
        (slotMesh p.T p.m (k + 1))) →
      0 ≤ bmax →
      (∀ k < p.M, ∀ u ∈ Icc (slotMesh p.T p.m k) (slotMesh p.T p.m (k + 1)), ‖b k u‖ ≤ bmax) →
      x p.T ≠ 0 → p.mass (x 0) bs ≤ p.g * ‖x p.T‖ →
      slotCertificate p Hs Ls bs G b ‖x 0‖ bmax ≤ p.ε * p.mass (x 0) bs / (2000 * p.g) →
      p.Outcome v hv hp.g_ge σ (x p.T) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, -⟩ :=
    GateODE.Time.solver p hp v hv
  refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, ?_⟩
  intro σ Hs Ls G b x bs bmax hC hx hG hGint hbint hbmax hb hne hbud hcert
  have herr := slot_target_error p hp.T_pos Hs Ls bs G b x bmax hbmax hx hG hGint hbint hb
    hC.select.selfH hC.psd hC.select.normH hC.select.normL
  exact outcome_of p hp v hv σ Hs Ls (x 0) bs (x p.T) hC ⟨hne, hbud, herr.trans hcert⟩

end

end SparseHamiltonian.GateMesh.ODE
