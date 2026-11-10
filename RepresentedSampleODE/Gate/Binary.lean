import GateEfficientRemarks.ODE.ZeroReleasedTime
import RepresentedSampleODE.Gate.Native

/-!
# The time-dependent gate solver from binary data, represented samples of any sign

The released time-dependent gate solver from time-indexed binary sparse data, for every `T ≥ 0`
(`GateRemarks.ODE.binary_ode_time_budget_bits_nonneg`), asks of the samples `D.matrix (x, r)`
positive semidefinite dissipative parts. Here the same protocol `btprepC q loadC wpC`, fixed
before the instance, has the guarantees `NOutcome` without that positivity, under the robust
remaining conditions `RobustRest`: the released `PubT.Rest` with the discretisation budget at the
sample error `3 δ_G` and the branch budget `6 R T δ_G ≤ ν` (`RobustRest.of_rest`,
`RobustRest.toRest`; for exact samples the released conditions themselves,
`RobustRest.of_rest_exact`).

* `robust_instanceOK`: the robust instance conditions of the released solver from the energy
  bounds of every sample and `RobustRest` (no accretivity of the samples);
* `robust_tzInstanceOK`: the zero-case instance conditions for the repaired samples;
* `robust_binary_time_outcome`: the guarantees of the released preparation `q.prep loadC wpC`;
* `robust_binary_time_outcome_nonneg`: the guarantees of `btprepC q loadC wpC` for every `T ≥ 0`
  (the direct source assembly in the zero case `T = 0 ∨ η_H + η_D = 0`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.RepresentedSampleODE.GateTime

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateBinary GateBinaryODE
open GateBinaryODETime (PubT HsT LsT HsT_of_lt LsT_of_lt gensT_eq privFamT)
open ZeroTimeGateODE (btprepC BTPublicOK0 BTZeroCase TZInstanceOK tzprepC)
open GateODE.Time (TParams TOracles gens)
open GatePointerEncoding (wordValue)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct BigOperators

variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- **The remaining instance conditions, represented samples of any sign**: those of the
released `PubT.Rest`, with the discretisation budget at the sample error `3 δ_G` and the branch
budget `6 R T δ_G ≤ ν` (`R`, `ν` the public LCHS radius and precision of the internal ratio `2g`
and accuracy `ε/2`). -/
structure RobustRest (q : PubT) (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n) (x : X)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf xs : ℝ → Reg (Fin q.kx) ℂ)
    (bs : ℕ → Reg (Fin q.kx) ℂ) (βG δG βb δb bmax : ℝ) : Prop where
  load_unitary : ∀ c, IsUnitary (Jl c)
  prep_left : Wp.conjTranspose * Wp = 1
  prep_right : Wp * Wp.conjTranspose = 1
  prep : ∀ w : Cfg (Fin (q.m + 1)),
    Wp w (fun _ => false) = ((q.params.srcAmp (xs 0) bs (w 0, Fin.tail w) : ℝ) : ℂ)
  init_load : xs 0 ≠ 0 →
    Jl (false, fun _ => false) (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection (xs 0)
  forcing_load : ∀ w : Fin q.m → Bool, bs (wordValue w) ≠ 0 →
    Jl (true, w) (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection (bs (wordValue w))
  solves : TimeDependentODE.SolvesODE G bf xs 0 q.T
  accretive : ∀ u ∈ Set.Icc 0 q.T, TimeDependentODE.Accretive (G u)
  lipG : ∀ u ∈ Set.Icc 0 q.T, ∀ u' ∈ Set.Icc 0 q.T, ‖G u - G u'‖ ≤ βG * |u - u'|
  sampleG : ∀ (r : ℕ) (hr : r < 2 ^ q.m),
    ‖G (r * q.T / ((2 ^ q.m : ℕ) : ℝ)) - mLift D en (x, ⟨r, hr⟩)‖ ≤ δG
  lipb : ∀ u ∈ Set.Icc 0 q.T, ∀ u' ∈ Set.Icc 0 q.T, ‖bf u - bf u'‖ ≤ βb * |u - u'|
  sampleb : ∀ r : ℕ, r < 2 ^ q.m → ‖bf (r * q.T / ((2 ^ q.m : ℕ) : ℝ)) - bs r‖ ≤ δb
  boundb : ∀ u ∈ Set.Icc 0 q.T, ‖bf u‖ ≤ bmax
  βG_nonneg : 0 ≤ βG
  βb_nonneg : 0 ≤ βb
  target_ne : xs q.T ≠ 0
  budget : q.params.mass (xs 0) bs ≤ q.g * ‖xs q.T‖
  disc : q.params.discretisation βG (3 * δG) βb δb bmax ‖xs 0‖ ≤
    q.ε * q.params.mass (xs 0) bs / (2000 * q.g)
  branch : 6 * q.params.R * q.T * δG ≤ q.params.nu

/-- The released remaining conditions with the two budgets give the robust ones. -/
theorem RobustRest.of_rest {q : PubT} {D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s}
    {en : Cfg (Fin q.kx) ≃ n} {x : X}
    {Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ}
    {Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ}
    {G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ} {bf xs : ℝ → Reg (Fin q.kx) ℂ}
    {bs : ℕ → Reg (Fin q.kx) ℂ} {βG δG βb δb bmax : ℝ}
    (hR : q.Rest D en x Jl Wp G bf xs bs βG δG βb δb bmax)
    (hdisc : q.params.discretisation βG (3 * δG) βb δb bmax ‖xs 0‖ ≤
      q.ε * q.params.mass (xs 0) bs / (2000 * q.g))
    (hbranch : 6 * q.params.R * q.T * δG ≤ q.params.nu) :
    RobustRest q D en x Jl Wp G bf xs bs βG δG βb δb bmax :=
  ⟨hR.load_unitary, hR.prep_left, hR.prep_right, hR.prep, hR.init_load, hR.forcing_load,
    hR.solves, hR.accretive, hR.lipG, hR.sampleG, hR.lipb, hR.sampleb, hR.boundb, hR.βG_nonneg,
    hR.βb_nonneg, hR.target_ne, hR.budget, hdisc, hbranch⟩

/-- The robust remaining conditions contain the released ones (the discretisation bound grows
with the sample error). -/
theorem RobustRest.toRest {q : PubT} {D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s}
    {en : Cfg (Fin q.kx) ≃ n} {x : X}
    {Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ}
    {Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ}
    {G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ} {bf xs : ℝ → Reg (Fin q.kx) ℂ}
    {bs : ℕ → Reg (Fin q.kx) ℂ} {βG δG βb δb bmax : ℝ} (hT : 0 ≤ q.T)
    (hR : RobustRest q D en x Jl Wp G bf xs bs βG δG βb δb bmax) :
    q.Rest D en x Jl Wp G bf xs bs βG δG βb δb bmax := by
  have hδ : 0 ≤ δG := (norm_nonneg _).trans (hR.sampleG 0 (Nat.two_pow_pos _))
  have hbmax : 0 ≤ bmax := (norm_nonneg _).trans (hR.boundb 0 ⟨le_rfl, hT⟩)
  have hmono : q.params.discretisation βG δG βb δb bmax ‖xs 0‖ ≤
      q.params.discretisation βG (3 * δG) βb δb bmax ‖xs 0‖ := by
    unfold GateODE.Time.TParams.discretisation
    have hT' : 0 ≤ q.params.T := hT
    have h1 : 0 ≤ ‖xs 0‖ + bmax * q.params.T := add_nonneg (norm_nonneg _) (mul_nonneg hbmax hT')
    have h2 : 0 ≤ q.params.T * (2 * δG * (‖xs 0‖ + bmax * q.params.T)) :=
      mul_nonneg hT' (mul_nonneg (by linarith) h1)
    nlinarith [h2]
  exact ⟨hR.load_unitary, hR.prep_left, hR.prep_right, hR.prep, hR.init_load, hR.forcing_load,
    hR.solves, hR.accretive, hR.lipG, hR.sampleG, hR.lipb, hR.sampleb, hR.boundb, hR.βG_nonneg,
    hR.βb_nonneg, hR.target_ne, hR.budget, hmono.trans hR.disc⟩

/-- **Exact samples** (`δ_G = 0`): the released remaining conditions are robust ones, so every
instance of the released solver with exact samples is an instance of the robust one. -/
theorem RobustRest.of_rest_exact {q : PubT} {D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s}
    {en : Cfg (Fin q.kx) ≃ n} {x : X}
    {Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ}
    {Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ}
    {G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ} {bf xs : ℝ → Reg (Fin q.kx) ℂ}
    {bs : ℕ → Reg (Fin q.kx) ℂ} {βG βb δb bmax : ℝ} (hν : 0 ≤ q.params.nu)
    (hR : q.Rest D en x Jl Wp G bf xs bs βG 0 βb δb bmax) :
    RobustRest q D en x Jl Wp G bf xs bs βG 0 βb δb bmax :=
  RobustRest.of_rest hR (by simpa using hR.disc) (by simpa using hν)

/-- **The robust instance conditions** of the released time-dependent solver from the energy
bounds of every sample and the robust remaining conditions (no accretivity of the samples). -/
theorem robust_instanceOK (q : PubT) (hq : q.OK) (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf xs : ℝ → Reg (Fin q.kx) ℂ)
    (bs : ℕ → Reg (Fin q.kx) ℂ) (βG δG βb δb bmax : ℝ)
    (hR : RobustRest q D en x Jl Wp G bf xs bs βG δG βb δb bmax) :
    RobustInstanceOK q.params (seedV (S := Fin q.kx))
      (⟨UJop (R := ℂ) q.UJg, privFamT q.params D en x q.rho q.γ, Jl, Wp⟩ :
        TOracles q.params.a q.params.m q.params.l (Reg (Fin q.kx) ℂ))
      (HsT D en x) (LsT D en x) G bf xs bs βG δG βb δb bmax where
  select := q.selectHyp hq D en hrange x hrH hcH hrD hcD Jl Wp
  load_unitary := hR.load_unitary
  prep_left := hR.prep_left
  prep_right := hR.prep_right
  prep := hR.prep
  init_load := hR.init_load
  forcing_load := hR.forcing_load
  solves := hR.solves
  accretive := hR.accretive
  lipG := hR.lipG
  sampleG r hr := by
    rw [gensT_eq D en x r hr]
    exact hR.sampleG r hr
  lipb := hR.lipb
  sampleb := hR.sampleb
  boundb := hR.boundb
  βG_nonneg := hR.βG_nonneg
  βb_nonneg := hR.βb_nonneg
  target_ne := hR.target_ne
  budget := hR.budget
  disc := hR.disc
  branch := hR.branch

/-- **The zero-case instance conditions for the repaired samples**: the lifted Hamiltonian parts
and the repairs `repair L̂_r δ_G` of the lifted dissipative parts satisfy the zero-case conditions
at the sample error `3 δ_G`. -/
theorem robust_tzInstanceOK (q : PubT) (hq : BTPublicOK0 q)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n) (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf xs : ℝ → Reg (Fin q.kx) ℂ)
    (bs : ℕ → Reg (Fin q.kx) ℂ) (βG δG βb δb bmax : ℝ)
    (hR : RobustRest q D en x Jl Wp G bf xs bs βG δG βb δb bmax) :
    TZInstanceOK q.params (seedV (S := Fin q.kx)) Jl Wp (HsT D en x)
      (repairedLs (LsT D en x) δG) G bf xs bs βG (3 * δG) βb δb bmax := by
  have hselfH : ∀ r < q.params.M, star (HsT D en x r) = HsT D en x r := by
    intro r hr
    rw [HsT_of_lt D en x r hr]
    unfold hLift
    rw [← qlift_star, SparseValuePrecision.matrixOperator_star_eq _
      (ODEMatrixEnergy.hamiltonianPart_isHermitian _)]
  have hselfL : ∀ r < q.params.M, star (LsT D en x r) = LsT D en x r := by
    intro r hr
    rw [LsT_of_lt D en x r hr]
    unfold lLift
    rw [← qlift_star, SparseValuePrecision.matrixOperator_star_eq _
      (ODEMatrixEnergy.dissipativePart_isHermitian _)]
  have hnormH : ∀ r < q.params.M, ‖HsT D en x r‖ ≤ q.params.lamH := by
    intro r hr
    rw [HsT_of_lt D en x r hr]
    exact (norm_qlift_le _ _).trans ((norm_matrixOperator_le D (x, ⟨r, hr⟩) _
      (ODEMatrixEnergy.hamiltonianPart_isHermitian _)
      (fun i j hij hji => by simp [ODEMatrixEnergy.hamiltonianPart_apply, hij, hji]) q.etaH
      hq.etaH_nonneg (hrH _) (hcH _)).trans
        (ZeroTimeGateODE.sqrt_le_lam0 q hq.γ_pos hq.γ_le q.etaH hq.etaH_nonneg))
  have hnormL : ∀ r < q.params.M, ‖LsT D en x r‖ ≤ q.params.lamD := by
    intro r hr
    rw [LsT_of_lt D en x r hr]
    exact (norm_qlift_le _ _).trans ((norm_matrixOperator_le D (x, ⟨r, hr⟩) _
      (ODEMatrixEnergy.dissipativePart_isHermitian _)
      (fun i j hij hji => by simp [ODEMatrixEnergy.dissipativePart_apply, hij, hji]) q.etaD
      hq.etaD_nonneg (hrD _) (hcD _)).trans
        (ZeroTimeGateODE.sqrt_le_lam0 q hq.γ_pos hq.γ_le q.etaD hq.etaD_nonneg))
  have hsample : ∀ r < q.params.M,
      ‖G (r * q.params.T / q.params.M) - gens (HsT D en x) (LsT D en x) r‖ ≤ δG := by
    intro r hr
    rw [gensT_eq D en x r hr]
    exact hR.sampleG r hr
  have hδ : 0 ≤ δG := (norm_nonneg _).trans (hsample 0 q.params.M_pos)
  obtain ⟨-, hpsd', hnorm', -, hsample'⟩ := repaired_facts (p := q.params) hq.T_nonneg
    (HsT D en x) (LsT D en x) G δG hδ hselfH hselfL hnormL hR.accretive hsample
  exact ⟨hselfH, hnormH, hnorm', hpsd', hR.load_unitary, hR.prep_left, hR.prep_right, hR.prep,
    hR.init_load, hR.forcing_load, hR.solves, hR.accretive, hR.lipG, hsample', hR.lipb,
    hR.sampleb, hR.boundb, hR.βG_nonneg, hR.βb_nonneg, hR.target_ne, hR.budget, hR.disc⟩

variable {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **The guarantees of the released preparation from binary data, represented samples of any
sign**: for public data with `PubT.OK`, every input whose samples have the released row and
column energy bounds, circuits within `ζs` with `24 d ζ + 3 ζs ≤ ν`, and the robust remaining
conditions, the protocol `nprotocol (q.prep loadC wpC) (2g)` has the guarantees `NOutcome`. -/
theorem robust_binary_time_outcome (q : PubT) (hq : q.OK)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf xs : ℝ → Reg (Fin q.kx) ℂ)
    (bs : ℕ → Reg (Fin q.kx) ℂ) (βG δG βb δb bmax ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) wpC) (liftB (matOp Wp)) ζs)
    (hbud : 24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu)
    (hR : RobustRest q D en x Jl Wp G bf xs bs βG δG βb δb bmax) :
    NOutcome (q.prep loadC wpC) q.params.ratio q.ε (q.params.ratio_ge hq.g_ge)
      (primsT (R := ℂ) D en x) (xs q.T) :=
  robust_native_time_outcome q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ) q.nd q.nd_public
    q.ar q.ζ hq.ζ_pos.le (q.ar_ok hq) loadC hloadV wpC hwpV (primsT (R := ℂ) D en x)
    (primsT_isUnitary D en x) ⟨UJop (R := ℂ) q.UJg, privFamT q.params D en x q.rho q.γ, Jl, Wp⟩
    rfl (q.nativeOK hq D en hrange hdec x) ζs hζs hload hwp hbud (HsT D en x) (LsT D en x) G bf xs
    bs βG δG βb δb bmax
    (robust_instanceOK q hq D en hrange x hrH hcH hrD hcD Jl Wp G bf xs bs βG δG βb δb bmax hR)

/-- **The guarantees for every `T ≥ 0`, represented samples of any sign**: for time-indexed
binary public data with `BTPublicOK0 q` and the public rescaling `γ = gammaOf T η_H η_D (2g) (ε/2)`
outside the zero case, every input whose samples have the released row and column energy
bounds, circuits within `ζs` with `98304 q* ζ + 3 ζs ≤ ν` and the robust remaining conditions,
the protocol `nprotocol (btprepC q loadC wpC) (2g)` of the released
`GateRemarks.ODE.binary_ode_time_budget_bits_nonneg` has the guarantees `NOutcome` against
`x(T)`. -/
theorem robust_binary_time_outcome_nonneg (q : PubT) (hq : BTPublicOK0 q)
    (hγ : ¬ BTZeroCase q →
      q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf xs : ℝ → Reg (Fin q.kx) ℂ)
    (bs : ℕ → Reg (Fin q.kx) ℂ) (βG δG βb δb bmax ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) wpC) (liftB (matOp Wp)) ζs)
    (hbud : 98304 * GateODEBudget.qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ + 3 * ζs ≤
      q.params.nu)
    (hR : RobustRest q D en x Jl Wp G bf xs bs βG δG βb δb bmax) :
    NOutcome (btprepC q loadC wpC) q.params.ratio q.ε (q.params.ratio_ge hq.g_ge)
      (primsT (R := ℂ) D en x) (xs q.T) := by
  have hε2 : (0 : ℝ) < q.ε / 2 := by linarith [hq.ε_pos]
  have hQ1 : 1 ≤ GateODEBudget.qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) :=
    GateRemarks.ODE.one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg (by linarith [hq.g_ge])
      hε2 (by linarith [hq.ε_half])
  by_cases hz : BTZeroCase q
  · have hp := ZeroTimeGateODE.btparams_ok0 hq
    obtain ⟨-, -, -, -, -, -, -, hout⟩ := ZeroTimeGateODE.native_ode_time_solver_zero
      (S := Fin q.kx) (Zs := Zs) (Z := SZ4 q.kx q.b) (Y := Fin q.m ⊕ PY q.kx q.b) (J := Query)
      q.params q.params.a q.params.m q.params.r q.params.K q.params.l q.params.f q.ar.bT q.ar.bP
      q.ar.A hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hp.lamH_nonneg hp.lamD_nonneg
      (ZeroTimeGateODE.btzeroCase_params hq hz) loadC hloadV wpC hwpV
    have hpr : btprepC q loadC wpC = tzprepC loadC wpC := by
      rw [btprepC, if_pos hz]
    have h0 : 0 ≤ 98304 * GateODEBudget.qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hq.ζ_pos.le
    have hI := robust_tzInstanceOK q hq D en x hrH hcH hrD hcD Jl Wp G bf xs bs βG δG βb δb bmax hR
    rw [hpr]
    exact hout (primsT (R := ℂ) D en x) Jl Wp (HsT D en x) (repairedLs (LsT D en x) δG) G bf xs bs
      βG (3 * δG) βb δb bmax ζs (primsT_isUnitary D en x) hζs hload hwp (by linarith) hI
  · have hP := ZeroTimeGateODE.btpublicOK_of hq hz
    obtain ⟨-, hd, -, -, -, -⟩ := GateODEBudget.binary_ode_time_sizes q hP (hγ hz)
    have hpr : btprepC q loadC wpC = q.prep loadC wpC := by
      rw [btprepC, if_neg hz]
    have hbud' : 24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu := by
      have := mul_le_mul_of_nonneg_right hd hP.ζ_pos.le
      linarith
    rw [hpr]
    exact robust_binary_time_outcome q hP D en hrange hdec loadC hloadV wpC hwpV x hrH hcH hrD hcD
      Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud' hR

end

end SparseHamiltonian.RepresentedSampleODE.GateTime
