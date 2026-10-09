import GateEfficientBinaryNodes.NodeBits
import GateEfficientBinarySelect.NonVacuity

/-!
# The new endpoints are not vacuous

* **Node programs** (`copyProg`, `midProg`): the copy program (`μ = m`, one CNOT per node bit,
  node words `u`, `m` gates) and the midpoint program (`μ = m + 1`, a NOT gate and one CNOT per
  node bit, node words `2u + 1`, `m + 1` gates) satisfy `NodeProg.OK` (`copyProg_length`,
  `midProg_length`); the copy program computes the released dyadic left-endpoint nodes
  (`vN_copy : vN = vQ`), the midpoint program the midpoints `(u + 1/2) T/2^m` (`vN_mid`).
* **The integrated certificate is implied by the uniform one** (`sampleErrNQ_le_of_uniform`):
  a uniform bound `δG` at the branch addresses gives `sampleErrNQ s ≤ T δG`. (No explicit data
  are given on which the solver certificate holds and no admissible uniform bound does; the
  released `GateBinarySelect.nvc_not_uniform` shows this for the certificate of Lemma
  `ode:lem:gate-select` on `H + k D`.)
* **Computed nodes** (`nvh_restN`, `nv_nodes_outcome`, `nv_copy_outcome`, `nv_mid_outcome`): for
  the public data `nvq` of `GateBinarySelect`, the one-point data on the grid of `2^(2m)` points
  and *every* node program with `μ ≥ m`, the homogeneous witness satisfies `RestN`, and every
  antecedent of `binary_nodes_solver` holds with empty loading and weight-preparation circuits;
  the native protocol has the guarantees `NOutcome`, in particular for the copy and midpoint
  programs. `nvMF_restN`, `nvMF_instanceN`: the forcing witness of `GateBinarySelect.nv_restB`
  with its forcing node at the midpoint `3T/2^(m+1)` (off the dyadic `2^m` mesh) satisfies
  `RestN`, and hence the integrated instance `BInstanceOKI` with the clock promises proved.
* **The budget in `𝔟`** (`nodes_all_hyps`): for the same public and binary data, the copy program
  and empty source circuits every hypothesis of `binary_nodes_budget_bits` holds for some
  `b_data`, and its gate bound holds.
* **Constant forcing** (`nv_const_outcome`): for the public data `nvq`, the one-point data, the
  problem `x' = seedV`, `x(0) = 0` (constant forcing `b = seedV`, `r₀ = 0`, `r_b = 1`), the zero
  generator path and empty supplied loading circuits, every antecedent of
  `binary_select_solverLI_const` holds and the protocol with the constructed weight preparation
  `wpConst` has the guarantees `NOutcome`; `nv_const_common_outcome`: the same for the
  common-mesh solver `binary_ode_time_solver_const` with `x(0) = seedV`, `b = 0`.
* **The integrated certificate from binary data** (`nvh_restBI`, `nv_selectI_outcome`): the
  homogeneous witness satisfies `RestBI`, and the released protocol `GateBinarySelect.prepQ` has
  the guarantees `NOutcome` by `binary_select_solverI` (`RestLI` is covered through
  `nvc_restLIConst` and `RestLIConst.toLI`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryNodes

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateBinaryODETime (PubT)
open SparseHamiltonian.GateODE.Time (TParams TOracles)
open SparseHamiltonian.GateSelect.ODE (startB bsW)
open SparseHamiltonian.GateQuad (vQ)
open SparseHamiltonian.GatePointerEncoding (wordValue wordEquivFin prepend)
open SparseHamiltonian.GateBitBudget (pointData pointData_range pointData_matrix withChoiceT
  withChoiceT_spec pointPubT pointPubT_ok withChoiceT_bits HasBits bitB)
open SparseHamiltonian.GateODEBudget (gammaOf qOf binary_ode_time_sizes)
open SparseHamiltonian.GateBinarySelect (nvq nvq_ok nvq_γ nvData nvData_dec nv_energies nv_psd
  nv_mLift_zero nvq_T nvq_g nvq_ε seedV_ne nvfv nvbf nvxs nvxs_zero nvxs_T nvhxs nvhys nvh_mass
  nvh_zsrc nvh_prep nvh_restB nvwq nvWp nv_mass1 nvys nv_restB)
open ODEStateNormalization (unitDirection)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### Node programs -/

section Programs

variable {m mu : ℕ} {Zn : Type} [DecidableEq Zn]

/-- The CNOT copying node-index bit `j` into node bit `t j`. -/
def cpG (t : Fin m → Fin mu) (j : Fin m) : CGate (Fin m ⊕ (Fin mu ⊕ Zn)) :=
  ⟨[(Sum.inl j, true)], Sum.inr (Sum.inl (t j))⟩

omit [DecidableEq Zn] in
theorem cpG_proper (t : Fin m → Fin mu) (j : Fin m) : (cpG (Zn := Zn) t j).Proper := by
  intro c hc
  simp only [cpG, List.mem_singleton] at hc
  subst hc
  exact Sum.inl_ne_inr

/-- The copies leave the node-index wires alone. -/
theorem cpG_run_inl (t : Fin m → Fin mu) (L : List (Fin m)) (z : Fin m ⊕ (Fin mu ⊕ Zn) → Bool)
    (j : Fin m) : crun (L.map (cpG t)) z (Sum.inl j) = z (Sum.inl j) :=
  crun_apply_of_not _ (fun w => ∃ k, w = Sum.inr (Sum.inl k)) (fun g hg => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hg
    exact ⟨t i, rfl⟩) z _ (fun ⟨_, hk⟩ => Sum.inl_ne_inr hk)

/-- The copies leave the node bits outside the image of `t` alone. -/
theorem cpG_run_other (t : Fin m → Fin mu) (L : List (Fin m)) (z : Fin m ⊕ (Fin mu ⊕ Zn) → Bool)
    (k : Fin mu) (hk : ∀ j, t j ≠ k) :
    crun (L.map (cpG t)) z (Sum.inr (Sum.inl k)) = z (Sum.inr (Sum.inl k)) :=
  crun_apply_of_not _ (fun w => ∃ j, w = Sum.inr (Sum.inl (t j))) (fun g hg => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hg
    exact ⟨i, rfl⟩) z _ (fun ⟨j, hj⟩ => hk j (Sum.inl_injective (Sum.inr_injective hj)).symm)

/-- **The copies XOR the node-index bits into their node bits.** -/
theorem cpG_run_tgt (t : Fin m → Fin mu) (ht : Function.Injective t) (L : List (Fin m))
    (hL : L.Nodup) (z : Fin m ⊕ (Fin mu ⊕ Zn) → Bool) (j : Fin m) :
    crun (L.map (cpG t)) z (Sum.inr (Sum.inl (t j))) =
      (z (Sum.inr (Sum.inl (t j))) ^^ (decide (j ∈ L) && z (Sum.inl j))) := by
  induction L generalizing z with
  | nil => simp
  | cons i L ih =>
      rw [List.nodup_cons] at hL
      rw [List.map_cons, crun_cons, ih hL.2]
      have h1 : (cpG (Zn := Zn) t i).run z (Sum.inl j) = z (Sum.inl j) :=
        CGate.run_apply_of_ne _ _ _ Sum.inl_ne_inr
      rw [h1]
      by_cases hji : j = i
      · subst hji
        have h2 : (cpG (Zn := Zn) t j).run z (Sum.inr (Sum.inl (t j))) =
            (z (Sum.inr (Sum.inl (t j))) ^^ z (Sum.inl j)) := by
          cases hz : z (Sum.inl j) <;> simp [CGate.run, cpG, lits, hz]
        rw [h2]
        simp [hL.1]
      · have h2 : (cpG (Zn := Zn) t i).run z (Sum.inr (Sum.inl (t j))) =
            z (Sum.inr (Sum.inl (t j))) :=
          CGate.run_apply_of_ne _ _ _ (fun h => hji (ht (Sum.inl_injective (Sum.inr_injective h))))
        rw [h2]
        simp [hji]

end Programs

/-- **The copy node program** (`μ = m`): one CNOT from every node-index bit to the node bit of the
same position; the node word of `u` is `u`, so that the nodes are the dyadic left endpoints
`u T / 2^m` (`vN_copy`). -/
def copyProg (m : ℕ) : NodeProg m m Empty where
  gates := (List.finRange m).map (cpG id)
  word := fun u => u

theorem copyProg_ok (m : ℕ) : (copyProg m).OK where
  proper := fun g hg => by
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hg
    exact cpG_proper _ _
  ctrl := fun g hg => by
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hg
    simp [cpG]
  run := fun u => by
    funext w
    rcases w with j | k | e
    · exact cpG_run_inl id _ _ j
    · have h := cpG_run_tgt (Zn := Empty) id Function.injective_id (List.finRange m)
        (List.nodup_finRange m) (Sum.elim u (fun _ => false)) k
      simp only [id] at h
      show crun ((List.finRange m).map (cpG id)) (Sum.elim u (fun _ => false))
        (Sum.inr (Sum.inl k)) = u k
      rw [h]
      simp
    · exact e.elim

/-- **The midpoint node program** (`μ = m + 1`): a NOT gate on the lowest node bit and one CNOT
from every node-index bit `j` to node bit `j + 1`; the node word of `u` is `2u + 1`, so that the
nodes are the midpoints `(u + 1/2) T / 2^m` (`vN_mid`). -/
def midProg (m : ℕ) : NodeProg m (m + 1) Empty where
  gates := ⟨[], Sum.inr (Sum.inl 0)⟩ :: (List.finRange m).map (cpG Fin.succ)
  word := fun u => prepend true u

theorem midProg_ok (m : ℕ) : (midProg m).OK where
  proper := fun g hg => by
    rcases List.mem_cons.1 hg with h | h
    · subst h
      intro c hc
      simp at hc
    · obtain ⟨j, _, rfl⟩ := List.mem_map.1 h
      exact cpG_proper _ _
  ctrl := fun g hg => by
    rcases List.mem_cons.1 hg with h | h
    · subst h
      simp
    · obtain ⟨j, _, rfl⟩ := List.mem_map.1 h
      simp [cpG]
  run := fun u => by
    have hstep : (⟨[], Sum.inr (Sum.inl 0)⟩ : CGate (Fin m ⊕ (Fin (m + 1) ⊕ Empty))).run
        (Sum.elim u (fun _ => false)) =
        Function.update (Sum.elim u (fun _ => false)) (Sum.inr (Sum.inl 0)) true := by
      unfold CGate.run
      split_ifs with h
      · rfl
      · exact absurd rfl h
    show crun ((List.finRange m).map (cpG Fin.succ))
      ((⟨[], Sum.inr (Sum.inl 0)⟩ : CGate (Fin m ⊕ (Fin (m + 1) ⊕ Empty))).run
        (Sum.elim u (fun _ => false))) = _
    rw [hstep]
    funext w
    rcases w with j | k | e
    · rw [cpG_run_inl Fin.succ _ _ j, Function.update_of_ne Sum.inl_ne_inr]
      rfl
    · refine Fin.cases ?_ (fun j => ?_) k
      · rw [cpG_run_other Fin.succ _ _ 0 (fun j => Fin.succ_ne_zero j), Function.update_self]
        rfl
      · rw [cpG_run_tgt Fin.succ (Fin.succ_injective m) _ (List.nodup_finRange m) _ j]
        have h1 : Function.update (Sum.elim u (fun _ => false)) (Sum.inr (Sum.inl 0)) true
            (Sum.inr (Sum.inl j.succ) : Fin m ⊕ (Fin (m + 1) ⊕ Empty)) = false := by
          rw [Function.update_of_ne (fun h => Fin.succ_ne_zero j
            (Sum.inl_injective (Sum.inr_injective h)))]
          rfl
        have h2 : Function.update (Sum.elim u (fun _ => false)) (Sum.inr (Sum.inl 0)) true
            (Sum.inl j : Fin m ⊕ (Fin (m + 1) ⊕ Empty)) = u j := by
          rw [Function.update_of_ne Sum.inl_ne_inr]
          rfl
        rw [h1, h2]
        simp only [List.mem_finRange, decide_true, Bool.true_and, Bool.false_xor]
        rfl
    · exact e.elim

/-- The copy program has `m` gates (and no scratch). -/
theorem copyProg_length (m : ℕ) : (copyProg m).gates.length = m := by
  simp [copyProg]

/-- The midpoint program has `m + 1` gates (and no scratch). -/
theorem midProg_length (m : ℕ) : (midProg m).gates.length = m + 1 := by
  simp [midProg]

/-- The word of a node index is its value. -/
theorem wordValue_symm (m q : ℕ) (h : q < 2 ^ m) :
    wordValue ((wordEquivFin m).symm ⟨q, h⟩) = q := by
  have := congrArg Fin.val ((wordEquivFin m).apply_symm_apply ⟨q, h⟩)
  rwa [GatePointerEncoding.wordEquivFin_apply, GatePointerEncoding.wordFin_val] at this

/-- **The copy program computes the released dyadic left-endpoint nodes** `u T / 2^m`. -/
theorem vN_copy (p : TParams) : vN p p.m (copyProg p.m) = vQ p p.M := by
  funext q
  unfold vN vQ
  by_cases h : q < 2 ^ p.m
  · have hM : q < p.M := h
    rw [dif_pos h, if_pos hM]
    show (wordValue ((wordEquivFin p.m).symm ⟨q, h⟩) : ℝ) * p.T / 2 ^ p.m = q * p.T / p.M
    rw [wordValue_symm p.m q h]
    have e : ((p.M : ℕ) : ℝ) = 2 ^ p.m := by
      show ((2 ^ p.m : ℕ) : ℝ) = 2 ^ p.m
      push_cast
      ring
    rw [e]
  · have hM : ¬ q < p.M := h
    rw [dif_neg h, if_neg hM]

/-- **The midpoint program computes the midpoints** `(u + 1/2) T / 2^m = (2u + 1) T / 2^(m+1)`. -/
theorem vN_mid (p : TParams) (q : ℕ) (hq : q < 2 ^ p.m) :
    vN p (p.m + 1) (midProg p.m) q = (2 * q + 1) * p.T / 2 ^ (p.m + 1) := by
  unfold vN
  rw [dif_pos hq]
  show (wordValue (prepend true ((wordEquivFin p.m).symm ⟨q, hq⟩)) : ℝ) * p.T / 2 ^ (p.m + 1) = _
  rw [GatePointerEncoding.wordValue_prepend, wordValue_symm p.m q hq,
    GatePointerEncoding.bitValue_true]
  push_cast
  ring

/-! ### The integrated certificate from the uniform bound -/

/-- **The integrated certificate for computed nodes from a uniform bound**: if every lifted sample
at a rounded branch address is within `δG` of the path at the exact address,
`sampleErrNQ s ≤ T δG`. -/
theorem sampleErrNQ_le_of_uniform (q : PubT) (hq : q.OK) (mu nd : ℕ) (hnd : nd ≤ mu + q.m)
    {Zn : Type} (N : NodeProg q.m mu Zn) {X n : Type*} [Fintype n] [DecidableEq n]
    (D : Data (X × Fin (2 ^ nd)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n) (x : X)
    (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (δG : ℝ)
    (h : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
      ‖G (addrNN N s r * q.T / 2 ^ (mu + q.m)) - mLift D en (x, addrFN nd hnd N s r hr)‖ ≤ δG)
    (s : Bool × (Fin q.m → Bool)) : sampleErrNQ q mu nd hnd N D en x G s ≤ q.T * δG := by
  rw [← sampleErrB_NQ]
  refine sampleErrB_le_of_uniform q.params (vN q.params mu N) (vN_mem q.params hq.T_pos.le mu N)
    hq.T_pos.le _ _ G s δG (fun r hr => ?_)
  rw [addrB_vN, gensN_eq q.params mu nd hnd N D en x s r hr]
  exact h s r hr

/-! ### Computed nodes on explicit data -/

section Nodes

/-- The data grid of `2^(2m)` points fits the copy program (`2m ≤ μ + m`, `μ = m`). -/
theorem nvq_copy_le : 2 * nvq.m ≤ nvq.m + nvq.m := by omega

/-- The data grid of `2^(2m)` points fits the midpoint program (`2m ≤ μ + m`, `μ = m + 1`). -/
theorem nvq_mid_le : 2 * nvq.m ≤ (nvq.m + 1) + nvq.m := by omega

/-- The samples of the one-point data satisfy `SampleOK` at every grid point. -/
theorem sampleOK_nv (g : Fin (2 ^ (2 * nvq.m))) : SampleOK nvData () nvq.etaH nvq.etaD g := by
  obtain ⟨hrH, hcH, hrD, hcD⟩ := nv_energies
  exact sampleOK_of_all nvData () nvq.etaH nvq.etaD hrH hcH hrD hcD nv_psd g

/-- With the zero path, the integrated sample error of the one-point data vanishes for every node
program. -/
theorem nv_sampleErrNQ (mu : ℕ) (hmu : 2 * nvq.m ≤ mu + nvq.m) {Zn : Type}
    (N : NodeProg nvq.m mu Zn) (s : Bool × (Fin nvq.m → Bool)) :
    sampleErrNQ nvq mu (2 * nvq.m) hmu N nvData (Equiv.refl _) ()
      (0 : ℝ → Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ) s ≤ 0 := by
  unfold sampleErrNQ
  apply le_of_eq
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro r _
  rw [Pi.zero_apply, zero_sub, norm_neg]
  exact norm_eq_zero.mpr (nv_mLift_zero _)

/-- **Every condition of `RestN` holds for the homogeneous witness and every node program** with
`μ ≥ m`: `x' = 0` on `[0, 1]` with `x(0) = seedV`, all quadrature weights `0`, the zero
generator path, the loading `1`, the identity weight preparation, the constant branch solutions
and `κ = βG = δI = 0`. -/
theorem nvh_restN (mu : ℕ) (hmu : 2 * nvq.m ≤ mu + nvq.m) {Zn : Type}
    (N : NodeProg nvq.m mu Zn) :
    RestN nvq mu (2 * nvq.m) hmu N nvData (Equiv.refl _) () (fun _ => 1) 1 (fun _ => 0) nvfv 0 0
      nvhxs nvhys 0 0 0 where
  weights := nvh_restB.weights
  load_unitary := nvh_restB.load_unitary
  prep_left := nvh_restB.prep_left
  prep_right := nvh_restB.prep_right
  prep := nvh_restB.prep
  init_load := nvh_restB.init_load
  forcing_load := nvh_restB.forcing_load
  solves := nvh_restB.solves
  accretive := nvh_restB.accretive
  lipG := nvh_restB.lipG
  βG_nonneg := nvh_restB.βG_nonneg
  sampleI := nv_sampleErrNQ mu hmu N
  branch_sol := fun s u _ => (hasDerivWithinAt_const _ _ _).congr_deriv (by simp)
  branch_init := fun s => rfl
  quad := nvh_restB.quad
  target_ne := nvh_restB.target_ne
  budget := nvh_restB.budget
  disc := by
    rw [nvh_mass, nvq_ε, nvq_g]
    norm_num

/-- **The guarantee of the solver with computed nodes holds for explicit data and every node
program** (`μ ≥ m`, `NodeProg.OK`): for the public data `nvq`, the one-point data on the grid of
`2^(2m)` points (`nd = 2m ≤ μ + m`), empty loading and weight-preparation circuits (the loading
`1` and the identity weight preparation, `ζs = 0`), the arithmetic budget `24 d ζ ≤ ν` of the
public choice of `ζ` and the homogeneous witness `nvh_restN`, every hypothesis of
`binary_nodes_solver` holds, and the native protocol has the guarantees `NOutcome` for
`x(T) = seedV`. -/
theorem nv_nodes_outcome (mu : ℕ) (hmu : 2 * nvq.m ≤ mu + nvq.m) {Zn : Type} [Fintype Zn]
    [DecidableEq Zn] (N : NodeProg nvq.m mu Zn) (hN : N.OK) :
    NOutcome (prepQN nvq mu (2 * nvq.m) hmu N
        ([] : List (NInstr ((Fin (nvq.params.m + 1) ⊕ Fin nvq.kx) ⊕ Empty)
          (Fin (2 * nvq.m) ⊕ PY nvq.kx nvq.b) Query)) [])
      nvq.params.ratio nvq.ε (nvq.params.ratio_ge nvq_ok.g_ge)
      (primsT (R := ℂ) (m := 2 * nvq.m) nvData (Equiv.refl _) ()) seedV := by
  obtain ⟨-, hd, -, -, -, -⟩ := binary_ode_time_sizes nvq nvq_ok nvq_γ
  have hd' : (nvq.params.d : ℝ) ≤
      4096 * qOf nvq.s nvq.T nvq.etaH nvq.etaD (2 * nvq.g) (nvq.ε / 2) := hd
  obtain ⟨-, -, -, hiff⟩ := withChoiceT_spec pointPubT pointPubT_ok
  have h0 := (hiff 0).mpr (by have := (nvq.params_ok nvq_ok).nu_pos; linarith)
  have hbud : 24 * (nvq.params.d : ℝ) * nvq.ζ + 3 * 0 ≤ nvq.params.nu := by
    have h1 := mul_le_mul_of_nonneg_right hd' nvq_ok.ζ_pos.le
    linarith
  have hL : ∀ k : ℕ, loadIdeal (k := k) (S := Fin nvq.kx)
      (fun _ => (1 : Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ)) = 1 := by
    intro k
    unfold loadIdeal
    exact localOp_one _
  refine binary_nodes_solver (X := Unit) (Zs := Empty) nvq nvq_ok mu (2 * nvq.m) hmu N hN nvData
    (Equiv.refl _) (pointData_range _ 1 1) nvData_dec [] (fun _ hi => by simp at hi) []
    (fun _ hi => by simp at hi) () (fun _ _ _ => sampleOK_nv _)
    (fun _ : Bool × (Fin nvq.params.m → Bool) =>
      (1 : Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ))
    (1 : Matrix (Cfg (Fin (nvq.params.m + 1))) (Cfg (Fin (nvq.params.m + 1))) ℂ) (fun _ => 0)
    nvfv 0 0 nvhxs
    nvhys 0 0 0 0 le_rfl ?_ ?_ hbud (nvh_restN mu hmu N)
  · rw [nrun_nil, hL, liftB_one]
    intro ψ _
    simp
  · rw [nrun_nil, matOp_one, liftB_one]
    intro ψ _
    simp

/-- **The guarantee with the copy program** (the dyadic left-endpoint nodes computed coherently by
`m` CNOT gates). -/
theorem nv_copy_outcome :
    NOutcome (prepQN nvq nvq.m (2 * nvq.m) nvq_copy_le (copyProg nvq.m)
        ([] : List (NInstr ((Fin (nvq.params.m + 1) ⊕ Fin nvq.kx) ⊕ Empty)
          (Fin (2 * nvq.m) ⊕ PY nvq.kx nvq.b) Query)) [])
      nvq.params.ratio nvq.ε (nvq.params.ratio_ge nvq_ok.g_ge)
      (primsT (R := ℂ) (m := 2 * nvq.m) nvData (Equiv.refl _) ()) seedV :=
  nv_nodes_outcome nvq.m nvq_copy_le (copyProg nvq.m) (copyProg_ok nvq.m)

/-- **The guarantee with the midpoint program** (the midpoints `(u + 1/2) T/2^m`, node words of
`m + 1` bits; the data grid of `2^(2m)` points is coarser than the address grid of `2^(2m+1)`
points, so that the time addresses are rounded). -/
theorem nv_mid_outcome :
    NOutcome (prepQN nvq (nvq.m + 1) (2 * nvq.m) nvq_mid_le (midProg nvq.m)
        ([] : List (NInstr ((Fin (nvq.params.m + 1) ⊕ Fin nvq.kx) ⊕ Empty)
          (Fin (2 * nvq.m) ⊕ PY nvq.kx nvq.b) Query)) [])
      nvq.params.ratio nvq.ε (nvq.params.ratio_ge nvq_ok.g_ge)
      (primsT (R := ℂ) (m := 2 * nvq.m) nvData (Equiv.refl _) ()) seedV :=
  nv_nodes_outcome (nvq.m + 1) nvq_mid_le (midProg nvq.m) (midProg_ok nvq.m)

/-- **Every condition of `RestN` holds for a forcing node at a midpoint**: the forcing witness of
`GateBinarySelect.nv_restB` (`x' = seedV` on `[0, 1]`, `x(0) = 0`, the single node of label `1`
with weight `1`, the permutation weight preparation `nvWp`) with the nodes of the midpoint
program, so that the branch of the forcing label starts at `3T/2^(m+1)`, off the dyadic mesh of
`2^m` points; `κ = βG = δI = 0`. -/
theorem nvMF_restN :
    RestN nvq (nvq.m + 1) (2 * nvq.m) nvq_mid_le (midProg nvq.m) nvData (Equiv.refl _) ()
      (fun _ => 1) nvWp nvwq nvfv 0 nvbf nvxs nvys 0 0 0 where
  weights := nv_restB.weights
  load_unitary := nv_restB.load_unitary
  prep_left := nv_restB.prep_left
  prep_right := nv_restB.prep_right
  prep := nv_restB.prep
  init_load := nv_restB.init_load
  forcing_load := nv_restB.forcing_load
  solves := nv_restB.solves
  accretive := nv_restB.accretive
  lipG := nv_restB.lipG
  βG_nonneg := nv_restB.βG_nonneg
  sampleI := nv_sampleErrNQ (nvq.m + 1) nvq_mid_le (midProg nvq.m)
  branch_sol := fun s u _ => (hasDerivWithinAt_const _ _ _).congr_deriv (by simp)
  branch_init := fun s => rfl
  quad := nv_restB.quad
  target_ne := nv_restB.target_ne
  budget := nv_restB.budget
  disc := by
    rw [nv_mass1, nvq_ε, nvq_g]
    norm_num

/-- The forcing node of the midpoint witness is `3T/2^(m+1)`. -/
theorem nvMF_node : vN nvq.params (nvq.params.m + 1) (midProg nvq.params.m) 1 =
    3 * nvq.params.T / 2 ^ (nvq.params.m + 1) := by
  have h1 : 1 < 2 ^ nvq.params.m :=
    Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp GateBinarySelect.nvq_m_pos)
  rw [vN_mid nvq.params 1 h1]
  norm_num

/-- **The integrated instance conditions hold for the midpoint forcing witness**: `instanceN`
turns `nvMF_restN` and the sample conditions of the one-point data into every condition of
`BInstanceOKI` for the private operations `privFamN` of the midpoint program, with the clock
promises proved. -/
theorem nvMF_instanceN :
    BInstanceOKI nvq.params (seedV (S := Fin nvq.kx))
      (⟨UJop (R := ℂ) nvq.UJg,
        privFamN nvq.params (nvq.m + 1) (2 * nvq.m) nvq_mid_le (midProg nvq.m) nvData
          (Equiv.refl _) () nvq.rho nvq.γ, fun _ => 1, nvWp⟩ :
        TOracles nvq.params.a nvq.params.m nvq.params.l (Reg (Fin nvq.kx) ℂ))
      (vN nvq.params (nvq.m + 1) (midProg nvq.m)) nvwq nvfv
      (HbN nvq.params (nvq.m + 1) (2 * nvq.m) nvq_mid_le (midProg nvq.m) nvData (Equiv.refl _) ())
      (LbN nvq.params (nvq.m + 1) (2 * nvq.m) nvq_mid_le (midProg nvq.m) nvData (Equiv.refl _) ())
      0 nvbf nvxs nvys 0 0 0 :=
  instanceN nvq (nvq.m + 1) (2 * nvq.m) nvq_mid_le (midProg nvq.m) nvq_ok nvData (Equiv.refl _)
    (pointData_range _ 1 1) () (fun _ _ _ => sampleOK_nv _) (fun _ => 1) nvWp nvwq nvfv 0 nvbf
    nvxs nvys 0 0 0 nvMF_restN

/-- **The budget in `𝔟` for computed nodes applies to explicit data** (its hypotheses are not
vacuous): the public data `withChoiceT pointPubT`, the one-point data on the grid of `2^(2m)`
points, the identity equivalence, the copy program and empty circuits `loadC`, `wpC` on the empty
source scratch satisfy, for some `b_data`, `PubT.OK`, the public rescaling, the accuracy bound,
`b ≤ b_data`, the four bit-length hypotheses, `NodeProg.OK`, the slot range, the decoder and the
validity of the circuits, and the gate bound `2·10²⁰ g [q* ((𝔟+μ+1)³ + |N|) + G_src + |Zs| + |Zn|]`
of `binary_nodes_budget_bits` holds for them. -/
theorem nodes_all_hyps : ∃ (q : PubT) (bd : ℕ) (hq : q.OK)
    (D : Data (Unit × Fin (2 ^ (2 * q.m))) (Cfg (Fin 0)) (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ Cfg (Fin 0))
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Empty)
      (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Empty) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query)),
    q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) ∧
    q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ ∧ q.b ≤ bd ∧
    HasBits bd q.c0 ∧ HasBits bd q.T ∧ HasBits bd q.etaH ∧ HasBits bd q.etaD ∧
    (copyProg q.m).OK ∧
    (∀ j, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u)) ∧
    (∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z) ∧ (∀ i ∈ loadC, i.Valid) ∧
    (∀ i ∈ wpC, i.Valid) ∧
    ((nprotocol (prepQN q q.m (2 * q.m) (by omega) (copyProg q.m) loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      2 * 10 ^ 20 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((bitN bd q q.m + 1) ^ 3 + (copyProg q.m).gates.length) +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Empty + Fintype.card Empty) := by
  obtain ⟨bd, hok, hγ, hζ, hb, hc0, hT, hH, hD⟩ :=
    withChoiceT_bits pointPubT pointPubT_ok
      ⟨1, 0, by norm_num [pointPubT, GateBitBudget.pointPubT₀]⟩
      ⟨1, 0, by norm_num [pointPubT, GateBitBudget.pointPubT₀]⟩
      ⟨1, 0, by norm_num [pointPubT, GateBitBudget.pointPubT₀]⟩
      ⟨0, 0, by norm_num [pointPubT, GateBitBudget.pointPubT₀]⟩
  refine ⟨withChoiceT pointPubT, bd, hok, pointData _ 1 1, Equiv.refl _, [], [], hγ, hζ, hb, hc0,
    hT, hH, hD, copyProg_ok _, pointData_range _ 1 1, nvData_dec, fun _ hi => by simp at hi,
    fun _ hi => by simp at hi, ?_⟩
  exact (binary_nodes_budget_bits (Zs := Empty) bd (withChoiceT pointPubT) hok hγ hζ hb hc0 hT hH
    hD _ (2 * (withChoiceT pointPubT).m) (by omega) (copyProg _) (copyProg_ok _) []
    (fun _ hi => by simp at hi) [] (fun _ hi => by simp at hi)).1

end Nodes

/-! ### Constant forcing on explicit data -/

section Const

/-- The branch solutions of the constant-forcing witness: constant, equal to the source vectors
of the constant forcing `b = seedV`. -/
def nvcys (s : Bool × (Fin nvq.m → Bool)) (_ : ℝ) : Reg (Fin nvq.kx) ℂ :=
  nvq.params.zsrc (nvxs 0) (fun _ => seedV) s

/-- With the zero path, the integrated sample error of the one-point data vanishes. -/
theorem nv_sampleErrQ (s : Bool × (Fin nvq.m → Bool)) :
    sampleErrQ nvq nvData (Equiv.refl _) ()
      (0 : ℝ → Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ) s ≤ 0 := by
  unfold sampleErrQ
  apply le_of_eq
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro r _
  rw [Pi.zero_apply, zero_sub, norm_neg]
  exact norm_eq_zero.mpr (nv_mLift_zero _)

/-- **Every condition of `RestLIConst` holds for constant forcing**: `x' = seedV` on `[0, 1]`
with `x(0) = 0` (`r₀ = 0`, `r_b = 1`, `B = 1`), the zero generator path (`Λ = βG = δI = 0`), the
loadings `1` and the constant branch solutions. -/
theorem nvc_restLIConst :
    RestLIConst nvq nvData (Equiv.refl _) () (fun _ => 1) 0 seedV nvxs nvcys 0 0 0 0 1 where
  norm_init := by rw [nvxs_zero, norm_zero]
  norm_forcing := norm_seedV
  load_unitary := fun _ => isUnitary_one
  init_load := fun h => absurd nvxs_zero h
  forcing_load := fun _ => by
    show (1 : Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ) seedV = unitDirection seedV
    simp [unitDirection, norm_seedV]
  solves := nv_restB.solves
  accretive := nv_restB.accretive
  lipG := nv_restB.lipG
  βG_nonneg := le_rfl
  sampleI := nv_sampleErrQ
  normG := fun u _ => by simp
  branch_sol := fun s u _ => (hasDerivWithinAt_const _ _ _).congr_deriv (by simp)
  branch_init := fun s => rfl
  target_ne := by
    rw [nvxs_T]
    exact seedV_ne
  budget := by
    rw [nvxs_T, norm_seedV, nvq_g, nvq_T]
    unfold srcB
    norm_num
  disc := by
    rw [nvq_ε, nvq_g, nvq_T]
    unfold srcB
    norm_num

/-- **The solver with constant forcing applies to explicit data**: for the public data `nvq`, the
one-point data on the grid of `2^(2m)` points, empty supplied loading circuits (which implement
the loadings `1` exactly, `ζ₀ = ζ₁ = 0`), the arithmetic budget `24 d ζ ≤ ν` and the
constant-forcing witness `nvc_restLIConst`, every hypothesis of `binary_select_solverLI_const`
holds, and the protocol with the constructed weight preparation `wpConst` (`r₀ = 0`, `r_b = 1`)
has the guarantees `NOutcome` for `x(T) = seedV`. -/
theorem nv_const_outcome :
    NOutcome (GateBinarySelect.prepQ nvq (loadConst nvq.params.m
        (fun _ => ([] : List (NInstr ((Unit ⊕ Fin nvq.kx) ⊕ Empty)
          (Fin (2 * nvq.m) ⊕ PY nvq.kx nvq.b) Query))))
        (wpConst nvq.params.m Empty (Fin (2 * nvq.m) ⊕ PY nvq.kx nvq.b) Query 0 1 nvq.T))
      nvq.params.ratio nvq.ε (nvq.params.ratio_ge nvq_ok.g_ge)
      (primsT (R := ℂ) (m := 2 * nvq.m) nvData (Equiv.refl _) ()) seedV := by
  obtain ⟨-, hd, -, -, -, -⟩ := binary_ode_time_sizes nvq nvq_ok nvq_γ
  have hd' : (nvq.params.d : ℝ) ≤
      4096 * qOf nvq.s nvq.T nvq.etaH nvq.etaD (2 * nvq.g) (nvq.ε / 2) := hd
  obtain ⟨-, -, -, hiff⟩ := withChoiceT_spec pointPubT pointPubT_ok
  have h0 := (hiff 0).mpr (by have := (nvq.params_ok nvq_ok).nu_pos; linarith)
  have hbud : 24 * (nvq.params.d : ℝ) * nvq.ζ + 3 * (0 + 0) ≤ nvq.params.nu := by
    have h1 := mul_le_mul_of_nonneg_right hd' nvq_ok.ζ_pos.le
    linarith
  have hI : ∀ c : Bool, srcIdeal (S := Fin nvq.kx) c
      (1 : Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ) = 1 := by
    intro c
    unfold srcIdeal
    simp only [ite_self]
    exact localOp_one _
  have hB : (0 : ℝ) < srcB 0 1 nvq.T := by
    rw [nvq_T]
    unfold srcB
    norm_num
  have h := binary_select_solverLI_const (X := Unit) (Zs := Empty) nvq nvq_ok nvData
    (Equiv.refl _) (pointData_range _ 1 1) nvData_dec (fun _ => []) (fun _ _ hi => by simp at hi)
    0 1 le_rfl zero_le_one hB () (fun _ _ _ => sampleOK_nv _) (fun _ => 1) 0 seedV nvxs nvcys
    0 0 0 0 0 le_rfl le_rfl ?_ ?_ hbud nvc_restLIConst
  · rwa [nvxs_T] at h
  · rw [nrun_nil, hI, liftB_one]
    intro ψ _
    simp
  · rw [nrun_nil, hI, liftB_one]
    intro ψ _
    simp

/-- **The one-point time-indexed binary data on the common mesh** of `2^m` points. -/
abbrev nvData1 : Data (Unit × Fin (2 ^ nvq.m)) (Cfg (Fin 0)) (Cfg (VW nvq.b)) nvq.s :=
  pointData _ 1 1

theorem nvData1_dec : ∀ e z, nvData1.decode e z = (nvq.c0 : ℂ) * gauss z := fun _ _ => by
  simp [pointData, withChoiceT, GateBitBudget.withChoiceT₀, pointPubT,
    GateBitBudget.pointPubT₀]
  rfl

theorem nv1_hamiltonianPart_zero (g : Unit × Fin (2 ^ nvq.m)) :
    ODEMatrixEnergy.hamiltonianPart (nvData1.matrix g) = 0 := by
  rw [pointData_matrix]
  simp [ODEMatrixEnergy.hamiltonianPart]

theorem nv1_dissipativePart_zero (g : Unit × Fin (2 ^ nvq.m)) :
    ODEMatrixEnergy.dissipativePart (nvData1.matrix g) = 0 := by
  rw [pointData_matrix]
  simp [ODEMatrixEnergy.dissipativePart]

theorem nv1_mLift_zero (g : Unit × Fin (2 ^ nvq.m)) :
    mLift (k := nvq.kx) nvData1 (Equiv.refl _) g = 0 := by
  have h0 : SparseStateOverlap.matrixOperator (0 : Matrix (Cfg (Fin 0)) (Cfg (Fin 0)) ℂ) = 0 := by
    ext v i
    simp [SparseStateOverlap.matrixOperator_apply]
  rw [mLift, pointData_matrix, h0]
  exact map_zero (qliftHom (R := ℂ) _)

/-- **Every condition of `RestConst` holds for the homogeneous witness with the constant-forcing
circuits**: `x' = 0` on `[0, 1]` with `x(0) = seedV` (`r₀ = 1`, forcing `b = 0`, `r_b = 0`,
`B = 1`), the zero generator path, the loadings `1` and `βG = δG = 0`. -/
theorem nvc_restConst :
    RestConst nvq nvData1 (Equiv.refl _) () (fun _ => 1) 0 0 nvhxs 0 0 1 0 where
  norm_init := norm_seedV
  norm_forcing := norm_zero
  load_unitary := fun _ => isUnitary_one
  init_load := fun _ => by
    show (1 : Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ) seedV = unitDirection (nvhxs 0)
    simp [nvhxs, unitDirection, norm_seedV]
  forcing_load := fun h => absurd rfl h
  solves := fun u _ => (hasDerivWithinAt_const _ _ _).congr_deriv (by simp)
  accretive := fun u _ v => by simp
  lipG := fun u _ u' _ => by simp
  sampleG := fun r hr => by simp [nv1_mLift_zero]
  βG_nonneg := le_rfl
  target_ne := seedV_ne
  budget := by
    show srcB 1 0 nvq.T ≤ nvq.g * ‖(seedV : Reg (Fin nvq.kx) ℂ)‖
    rw [norm_seedV, nvq_g, nvq_T]
    unfold srcB
    norm_num
  disc := by
    have e : nvq.params.discretisation 0 0 0 0 0 1 = 0 := by
      unfold GateODE.Time.TParams.discretisation
      ring
    rw [e, nvq_ε, nvq_g, nvq_T]
    unfold srcB
    norm_num

/-- **The common-mesh solver with the constant-forcing circuits applies to explicit data**: for the
public data `nvq`, the one-point data on the common mesh of `2^m` points, empty supplied loading
circuits, the arithmetic budget `24 d ζ ≤ ν` and the witness `nvc_restConst`, every hypothesis of
`binary_ode_time_solver_const` holds, and the protocol with the constructed weight preparation
`wpConst` (`r₀ = 1`, `r_b = 0`) has the guarantees `NOutcome` for `x(T) = seedV`. -/
theorem nv_const_common_outcome :
    NOutcome (nvq.prep (loadConst nvq.params.m
        (fun _ => ([] : List (NInstr ((Unit ⊕ Fin nvq.kx) ⊕ Empty)
          (Fin nvq.m ⊕ PY nvq.kx nvq.b) Query))))
        (wpConst nvq.params.m Empty (Fin nvq.m ⊕ PY nvq.kx nvq.b) Query 1 0 nvq.T))
      nvq.params.ratio nvq.ε (nvq.params.ratio_ge nvq_ok.g_ge)
      (primsT (R := ℂ) nvData1 (Equiv.refl _) ()) seedV := by
  obtain ⟨-, hd, -, -, -, -⟩ := binary_ode_time_sizes nvq nvq_ok nvq_γ
  have hd' : (nvq.params.d : ℝ) ≤
      4096 * qOf nvq.s nvq.T nvq.etaH nvq.etaD (2 * nvq.g) (nvq.ε / 2) := hd
  obtain ⟨-, -, -, hiff⟩ := withChoiceT_spec pointPubT pointPubT_ok
  have h0 := (hiff 0).mpr (by have := (nvq.params_ok nvq_ok).nu_pos; linarith)
  have hbud : 24 * (nvq.params.d : ℝ) * nvq.ζ + 3 * (0 + 0) ≤ nvq.params.nu := by
    have h1 := mul_le_mul_of_nonneg_right hd' nvq_ok.ζ_pos.le
    linarith
  have hI : ∀ c : Bool, srcIdeal (S := Fin nvq.kx) c
      (1 : Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ) = 1 := by
    intro c
    unfold srcIdeal
    simp only [ite_self]
    exact localOp_one _
  have hB : (0 : ℝ) < srcB 1 0 nvq.T := by
    unfold srcB
    norm_num
  have hE : ∀ (g : Fin (2 ^ nvq.m)) (i : Cfg (Fin 0)),
      ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (nvData1.matrix ((), g)) i j‖ ^ 2 ≤ nvq.etaH ^ 2 := by
    intro g i
    rw [nv1_hamiltonianPart_zero]
    simp only [Matrix.zero_apply, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity
  have hE' : ∀ (g : Fin (2 ^ nvq.m)) (j : Cfg (Fin 0)),
      ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (nvData1.matrix ((), g)) i j‖ ^ 2 ≤ nvq.etaH ^ 2 := by
    intro g j
    rw [nv1_hamiltonianPart_zero]
    simp only [Matrix.zero_apply, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity
  have hD : ∀ (g : Fin (2 ^ nvq.m)) (i : Cfg (Fin 0)),
      ∑ j, ‖ODEMatrixEnergy.dissipativePart (nvData1.matrix ((), g)) i j‖ ^ 2 ≤ nvq.etaD ^ 2 := by
    intro g i
    rw [nv1_dissipativePart_zero]
    simp only [Matrix.zero_apply, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity
  have hD' : ∀ (g : Fin (2 ^ nvq.m)) (j : Cfg (Fin 0)),
      ∑ i, ‖ODEMatrixEnergy.dissipativePart (nvData1.matrix ((), g)) i j‖ ^ 2 ≤ nvq.etaD ^ 2 := by
    intro g j
    rw [nv1_dissipativePart_zero]
    simp only [Matrix.zero_apply, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity
  have hP : ∀ (g : Fin (2 ^ nvq.m)) (w : EuclideanSpace ℂ (Cfg (Fin 0))),
      0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (nvData1.matrix ((), g))) w)).re := by
    intro g w
    have h0 : SparseStateOverlap.matrixOperator
        (0 : Matrix (Cfg (Fin 0)) (Cfg (Fin 0)) ℂ) = 0 := by
      ext v i
      simp [SparseStateOverlap.matrixOperator_apply]
    rw [nv1_dissipativePart_zero, h0]
    simp
  exact binary_ode_time_solver_const (X := Unit) (Zs := Empty) nvq nvq_ok nvData1 (Equiv.refl _)
    (pointData_range _ 1 1) nvData1_dec (fun _ => []) (fun _ _ hi => by simp at hi) 1 0
    zero_le_one le_rfl hB () hE hE' hD hD' hP (fun _ => 1) 0 0 nvhxs 0 0 0 0 le_rfl le_rfl
    (by rw [nrun_nil, hI, liftB_one]; intro ψ _; simp)
    (by rw [nrun_nil, hI, liftB_one]; intro ψ _; simp) hbud nvc_restConst

end Const

/-! ### The integrated certificate from binary data on explicit data -/

section Integrated

/-- **Every condition of `RestBI` holds for the homogeneous witness**: `x' = 0` on `[0, 1]` with
`x(0) = seedV`, all weights `0`, the zero generator path, the loading `1`, the identity weight
preparation, the constant branch solutions and `κ = βG = δI = 0`. -/
theorem nvh_restBI :
    RestBI nvq nvData (Equiv.refl _) () (fun _ => 1) 1 (fun _ => 0) nvfv 0 0 nvhxs nvhys 0 0 0 where
  weights := nvh_restB.weights
  load_unitary := nvh_restB.load_unitary
  prep_left := nvh_restB.prep_left
  prep_right := nvh_restB.prep_right
  prep := nvh_restB.prep
  init_load := nvh_restB.init_load
  forcing_load := nvh_restB.forcing_load
  solves := nvh_restB.solves
  accretive := nvh_restB.accretive
  lipG := nvh_restB.lipG
  βG_nonneg := nvh_restB.βG_nonneg
  sampleI := nv_sampleErrQ
  branch_sol := nvh_restB.branch_sol
  branch_init := nvh_restB.branch_init
  quad := nvh_restB.quad
  target_ne := nvh_restB.target_ne
  budget := nvh_restB.budget
  disc := by
    rw [nvh_mass, nvq_ε, nvq_g]
    norm_num

/-- **The solver with the integrated certificate from binary data applies to explicit data**: for
the public data `nvq`, the one-point data, empty loading and weight-preparation circuits, the
arithmetic budget `24 d ζ ≤ ν` and the witness `nvh_restBI`, every hypothesis of
`binary_select_solverI` holds, and the released protocol has the guarantees `NOutcome` for
`x(T) = seedV`. -/
theorem nv_selectI_outcome :
    NOutcome (GateBinarySelect.prepQ nvq
        ([] : List (NInstr ((Fin (nvq.params.m + 1) ⊕ Fin nvq.kx) ⊕ Empty)
          (Fin (2 * nvq.m) ⊕ PY nvq.kx nvq.b) Query)) [])
      nvq.params.ratio nvq.ε (nvq.params.ratio_ge nvq_ok.g_ge)
      (primsT (R := ℂ) (m := 2 * nvq.m) nvData (Equiv.refl _) ()) seedV := by
  obtain ⟨-, hd, -, -, -, -⟩ := binary_ode_time_sizes nvq nvq_ok nvq_γ
  have hd' : (nvq.params.d : ℝ) ≤
      4096 * qOf nvq.s nvq.T nvq.etaH nvq.etaD (2 * nvq.g) (nvq.ε / 2) := hd
  obtain ⟨-, -, -, hiff⟩ := withChoiceT_spec pointPubT pointPubT_ok
  have h0 := (hiff 0).mpr (by have := (nvq.params_ok nvq_ok).nu_pos; linarith)
  have hbud : 24 * (nvq.params.d : ℝ) * nvq.ζ + 3 * 0 ≤ nvq.params.nu := by
    have h1 := mul_le_mul_of_nonneg_right hd' nvq_ok.ζ_pos.le
    linarith
  have hL : ∀ k : ℕ, loadIdeal (k := k) (S := Fin nvq.kx)
      (fun _ => (1 : Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ)) = 1 := by
    intro k
    unfold loadIdeal
    exact localOp_one _
  refine binary_select_solverI (X := Unit) (Zs := Empty) nvq nvq_ok nvData (Equiv.refl _)
    (pointData_range _ 1 1) nvData_dec [] (fun _ hi => by simp at hi) []
    (fun _ hi => by simp at hi) () (fun _ _ _ => sampleOK_nv _)
    (fun _ : Bool × (Fin nvq.params.m → Bool) =>
      (1 : Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ))
    (1 : Matrix (Cfg (Fin (nvq.params.m + 1))) (Cfg (Fin (nvq.params.m + 1))) ℂ) (fun _ => 0)
    nvfv 0 0 nvhxs nvhys 0 0 0 0 le_rfl ?_ ?_ hbud nvh_restBI
  · rw [nrun_nil, hL, liftB_one]
    intro ψ _
    simp
  · rw [nrun_nil, matOp_one, liftB_one]
    intro ψ _
    simp

end Integrated

end

end SparseHamiltonian.GateBinaryNodes
