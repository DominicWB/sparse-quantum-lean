import GateEfficientODE.Circuit.Wires

/-!
# The two reflections of the amplification step

Both reflections test whether every wire except the flag and the pool is
zero, by one AND chain on the pool (`zeroLits`, `card (Wire a m r K) + 1 + k + l`
literals).

* `rgoodG`: the phase `-1` on the all-zero configuration, with any payload.
  On configurations with clean work wires it agrees with the reflection
  `1 - 2 F F†` about the clean output encoding `F` (`rgood_agrees`).
* `rseedC`: the zero test is written to the flag, the public payload
  reflection about the seed vector `v` is applied under the flag, and the
  test is uncomputed.  On clean work wires it agrees with the reflection
  about the seed state `|0⟩ ⊗ v` (`rseed_agrees`).

Both ideal reflections keep the work wires clean (`pres2_rgoodI`,
`pres2_rseedI`).
-/

namespace SparseHamiltonian.GateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire zMat zMat_unitary)
open scoped InnerProduct BigOperators

/-! ### The adjoint of the single-configuration embedding -/

section Generic

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

theorem basL_adjoint_apply (x : Cfg W) (ψ : Reg W Q) : ((basL (Q := Q) x)†) ψ = ψ x := by
  apply ext_inner_right ℂ
  intro q
  rw [adjoint_inner_left, basL_apply, inner_bas_right]

end Generic

variable {a m r K k l f : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### The zero test -/

/-- Every wire except the flag and the pool is zero. -/
def zeroLits : List (AW a m r K k l f × Bool) :=
  ((Finset.univ : Finset (Wire a m r K)).toList.map (fun s => (Sum.inl s, false))) ++
  [(Sum.inr OWire.ini, false)] ++
  (List.finRange k).map (fun i => (Sum.inr (OWire.src i), false)) ++
  (List.finRange l).map (fun j => (Sum.inr (OWire.lch j), false))

theorem zeroLits_length :
    (zeroLits (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)).length =
      Fintype.card (Wire a m r K) + 1 + k + l := by
  simp [zeroLits]
  omega

theorem mem_zeroLits (c : AW a m r K k l f × Bool) (hc : c ∈ zeroLits) :
    c.2 = false ∧ ((∃ s, c.1 = Sum.inl s) ∨ c.1 = Sum.inr OWire.ini ∨
      (∃ i, c.1 = Sum.inr (OWire.src i)) ∨ (∃ j, c.1 = Sum.inr (OWire.lch j))) := by
  simp only [zeroLits, List.mem_append, List.mem_map, Finset.mem_toList, Finset.mem_univ,
    true_and, List.mem_singleton, List.mem_finRange] at hc
  rcases hc with ((⟨s, rfl⟩ | rfl) | ⟨i, rfl⟩) | ⟨j, rfl⟩
  · exact ⟨rfl, Or.inl ⟨s, rfl⟩⟩
  · exact ⟨rfl, Or.inr (Or.inl rfl)⟩
  · exact ⟨rfl, Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))⟩
  · exact ⟨rfl, Or.inr (Or.inr (Or.inr ⟨j, rfl⟩))⟩

theorem zeroLits_ne_flg :
    ∀ c ∈ (zeroLits (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)),
      c.1 ≠ Sum.inr OWire.flg := by
  intro c hc
  rcases (mem_zeroLits c hc).2 with ⟨s, h⟩ | h | ⟨i, h⟩ | ⟨j, h⟩ <;> rw [h] <;> simp

theorem zeroLits_ne_pool :
    ∀ c ∈ (zeroLits (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)),
      ∀ w ∈ poolList, c.1 ≠ w := by
  intro c hc w hw
  obtain ⟨i, rfl⟩ := (mem_poolList w).mp hw
  rcases (mem_zeroLits c hc).2 with ⟨s, h⟩ | h | ⟨i', h⟩ | ⟨j, h⟩ <;> rw [h] <;> simp

/-- On clean work wires the zero test holds exactly at the zero configuration. -/
theorem ctrlOK_zeroLits (x : Cfg (AW a m r K k l f)) (hx : WorkClean x) :
    ctrlOK zeroLits x = true ↔ x = fun _ => false := by
  rw [ctrlOK_iff]
  constructor
  · intro h
    funext w
    rcases w with s | o
    · exact h (Sum.inl s, false) (by simp [zeroLits, Finset.mem_toList])
    · cases o with
      | ini => exact h (Sum.inr OWire.ini, false) (by simp [zeroLits])
      | src i => exact h (Sum.inr (OWire.src i), false) (by simp [zeroLits])
      | lch j => exact h (Sum.inr (OWire.lch j), false) (by simp [zeroLits])
      | flg => exact hx .flg rfl
      | pool i => exact hx (.pool i) rfl
  · rintro rfl c hc
    exact (mem_zeroLits c hc).1.symm

theorem zeroLits_length_le (hf : Fintype.card (Wire a m r K) + k + l ≤ f) :
    (zeroLits (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)).length ≤
      (poolList (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)).length + 1 := by
  rw [zeroLits_length, poolList_length]
  omega

theorem poolClean_update_flg (x : Cfg (AW a m r K k l f)) (b : Bool) (hx : PoolClean x) :
    PoolClean (Function.update x (Sum.inr OWire.flg) b) := by
  intro i
  rw [Function.update_of_ne (by simp)]
  exact hx i

theorem poolClean_clean (x : Cfg (AW a m r K k l f)) (hx : PoolClean x) :
    ∀ w ∈ poolList, x w = false := (poolClean_iff x).mp hx

/-- The many-controlled gate on the flag agrees with the ideal one on pool-clean
configurations. -/
theorem flagGate_agrees (hf : Fintype.card (Wire a m r K) + k + l ≤ f)
    (u : Matrix Bool Bool ℂ) :
    Agrees PoolClean (gRun (Q := P) (mcGate (zeroLits (a := a) (m := m) (r := r) (K := K)
      (k := k) (l := l) (f := f)) poolList (Sum.inr OWire.flg) u))
      (gateOp zeroLits (Sum.inr OWire.flg) u) :=
  mcGate_agrees _ _ _ _ (zeroLits_length_le hf) poolList_nodup zeroLits_ne_flg
    (fun w hw => by obtain ⟨i, rfl⟩ := (mem_poolList w).mp hw; simp)
    zeroLits_ne_pool PoolClean poolClean_clean poolClean_update_flg

/-! ### The good-subspace reflection -/

/-- The clean output encoding: every wire zero. -/
def goodF : P →L[ℂ] Reg (AW a m r K k l f) P := basL (fun _ => false)

theorem goodF_isometry :
    (goodF (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (P := P))† ∘L goodF = 1 :=
  basL_adjoint_comp _

/-- The reflection about the clean outputs, `1 - 2 F F†`. -/
def rgoodI : Reg (AW a m r K k l f) P →L[ℂ] Reg (AW a m r K k l f) P :=
  PhaseSubspaceGates.phase (ODEHeraldedSuccess.successProjector goodF) (-1)

/-- The gate list of the good-subspace reflection. -/
def rgoodG : List (Gate (AW a m r K k l f)) :=
  mcGate zeroLits poolList (Sum.inr OWire.flg) zMat

theorem rgoodI_bas (x : Cfg (AW a m r K k l f)) (p : P) :
    rgoodI (bas x p) = if x = (fun _ => false) then -bas x p else bas x p := by
  rw [rgoodI, PhaseSubspaceGates.phase, add_apply, one_apply_eq_self, smul_apply,
    ODEHeraldedSuccess.successProjector, comp_apply, goodF, basL_adjoint_apply, basL_apply,
    bas_apply]
  by_cases hx : x = fun _ => false
  · subst hx
    rw [if_pos rfl, if_pos rfl]
    module
  · rw [if_neg (Ne.symm hx), if_neg hx]
    have : bas (fun _ => false : Cfg (AW a m r K k l f)) (0 : P) = 0 := by
      rw [← smul_zero (0 : ℂ), bas_smul, zero_smul]
    rw [this, smul_zero, add_zero]

theorem rgood_agrees (hf : Fintype.card (Wire a m r K) + k + l ≤ f) :
    Agrees WorkClean (gRun (Q := P) (rgoodG (a := a) (m := m) (r := r) (K := K) (k := k)
      (l := l) (f := f))) rgoodI := by
  apply agrees_of_bas
  intro x hx p
  rw [rgoodG, flagGate_agrees hf zMat _ (supp_bas x (poolClean_of_workClean hx) p),
    gateOp_bas _ _ _ zeroLits_ne_flg, rgoodI_bas]
  have hflg : x (Sum.inr OWire.flg) = false := hx .flg rfl
  by_cases h0 : x = fun _ => false
  · rw [if_pos ((ctrlOK_zeroLits x hx).mpr h0), if_pos h0, Fintype.sum_bool, hflg]
    have hu : Function.update x (Sum.inr OWire.flg) false = x := by
      rw [← hflg, Function.update_eq_self]
    have hz1 : zMat true false = 0 := by simp [zMat]
    have hz0 : zMat false false = -1 := by simp [zMat]
    rw [hz1, hz0, zero_smul, zero_add, hu]
    module
  · rw [if_neg (fun h => h0 ((ctrlOK_zeroLits x hx).mp h)), if_neg h0]

theorem rgoodI_isUnitary :
    IsUnitary (rgoodI (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (P := P)) :=
  PhaseSubspaceGates.phase_unitary _
    (ODEHeraldedSuccess.successProjector_isOrthogonalProjection _ goodF_isometry) _ (by simp)

theorem rgoodI_adjoint :
    (rgoodI (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (P := P))† = rgoodI := by
  rw [← star_eq_adjoint, rgoodI, PhaseSubspaceGates.phase_adjoint _
    (ODEHeraldedSuccess.successProjector_isOrthogonalProjection _ goodF_isometry).1]
  simp

theorem workClean_zero : WorkClean (fun _ => false : Cfg (AW a m r K k l f)) :=
  fun _ _ => rfl

theorem pres2_rgoodI :
    Pres2 WorkClean (rgoodI (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
      (P := P)) := by
  have hpres : Preserves WorkClean (rgoodI (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
      (f := f) (P := P)) := by
    intro ψ hψ
    have hrep : rgoodI ψ = ψ + (-1 - 1 : ℂ) • bas (fun _ => false) (ψ (fun _ => false)) := by
      rw [rgoodI, PhaseSubspaceGates.phase, add_apply, one_apply_eq_self, smul_apply,
        ODEHeraldedSuccess.successProjector, comp_apply, goodF, basL_adjoint_apply, basL_apply]
    rw [hrep]
    exact supp_add hψ (supp_smul _ (supp_bas _ workClean_zero _))
  exact ⟨hpres, by rw [rgoodI_adjoint]; exact hpres⟩

/-! ### The seed reflection -/

/-- The seed state: every wire zero, payload `v`. -/
def seedState (v : P) : Reg (AW a m r K k l f) P := bas (fun _ => false) v

omit [InnerProductSpace ℂ P] [CompleteSpace P] in
theorem seedState_norm (v : P) (hv : ‖v‖ = 1) :
    ‖seedState (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) v‖ = 1 := by
  rw [seedState, norm_bas, hv]

/-- The reflection about the seed state. -/
def rseedI (v : P) : Reg (AW a m r K k l f) P →L[ℂ] Reg (AW a m r K k l f) P :=
  PhaseSubspaceGates.phase (ODEGroverRay.projector (seedState v)) (-1)

/-- The zero test on the flag. -/
def flagG : List (Gate (AW a m r K k l f)) :=
  mcGate zeroLits poolList (Sum.inr OWire.flg) pauliX

/-- The circuit of the seed reflection: zero test, controlled payload
reflection, uncomputation. -/
def rseedC : List (OInstr (Wire a m r K) (OWire k l f)) :=
  ofGates flagG ++ [OInstr.seed [(Sum.inr OWire.flg, true)]] ++ ofGates flagG

theorem rseedI_bas (v : P) (x : Cfg (AW a m r K k l f)) (p : P) :
    rseedI v (bas x p) = if x = (fun _ => false) then bas x (seedRefl v p) else bas x p := by
  rw [rseedI, PhaseSubspaceGates.phase, add_apply, one_apply_eq_self, smul_apply,
    ODEGroverRay.projector_apply, seedState, inner_bas_left, bas_apply]
  by_cases hx : x = fun _ => false
  · subst hx
    rw [if_pos rfl, if_pos rfl, seedRefl, PhaseSubspaceGates.phase, add_apply, one_apply_eq_self,
      smul_apply, ODEGroverRay.projector_apply, bas_add, bas_smul, bas_smul]
  · rw [if_neg (Ne.symm hx), if_neg hx, inner_zero_right, zero_smul, smul_zero, add_zero]

theorem flagG_bas (hf : Fintype.card (Wire a m r K) + k + l ≤ f) (x : Cfg (AW a m r K k l f))
    (hx : PoolClean x) (p : P) :
    gRun flagG (bas x p) = bas (flipCfg zeroLits (Sum.inr OWire.flg) x) p := by
  rw [flagG, flagGate_agrees hf pauliX _ (supp_bas x hx p),
    gateOp_pauliX_bas _ _ zeroLits_ne_flg]

theorem rseed_agrees (hf : Fintype.card (Wire a m r K) + k + l ≤ f) (v : P)
    (σ : Oracles a (Label k l) P) :
    Agrees WorkClean (run (wiring (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) v)
      σ rseedC) (rseedI v) := by
  apply agrees_of_bas
  intro x hx p
  have hpc := poolClean_of_workClean hx
  have hflg : x (Sum.inr OWire.flg) = false := hx .flg rfl
  rw [rseedC, run_append, run_append, run_ofGates, comp_apply, comp_apply,
    flagG_bas hf x hpc, run_singleton, OInstr.eval_seed, pctl_bas, rseedI_bas]
  have hctl : ctrlOK zeroLits (Function.update x (Sum.inr OWire.flg) true) = ctrlOK zeroLits x :=
    ctrlOK_update _ _ zeroLits_ne_flg x true
  by_cases h0 : x = fun _ => false
  · have hz := (ctrlOK_zeroLits x hx).mpr h0
    have hflip : flipCfg zeroLits (Sum.inr OWire.flg) x =
        Function.update x (Sum.inr OWire.flg) true := by
      rw [flipCfg, if_pos hz, hflg]
      rfl
    rw [hflip]
    have hc1 : ctrlOK [(Sum.inr OWire.flg, true)]
        (Function.update x (Sum.inr OWire.flg) true) = true := by
      simp [ctrlOK]
    rw [if_pos hc1, if_pos h0]
    rw [flagG_bas hf _ (poolClean_update_flg x true hpc)]
    congr 1
    rw [flipCfg, if_pos (by rw [hctl]; exact hz), Function.update_self, Bool.not_true,
      Function.update_idem, ← hflg, Function.update_eq_self]
  · have hz : ¬ ctrlOK zeroLits x = true := fun h => h0 ((ctrlOK_zeroLits x hx).mp h)
    have hflip : flipCfg zeroLits (Sum.inr OWire.flg) x = x := by
      rw [flipCfg, if_neg hz]
    rw [hflip]
    have hc1 : ¬ ctrlOK [(Sum.inr OWire.flg, true)] x = true := by
      simp [ctrlOK, hflg]
    rw [if_neg hc1, if_neg h0, flagG_bas hf x hpc, hflip]

theorem rseedI_isUnitary (v : P) (hv : ‖v‖ = 1) :
    IsUnitary (rseedI (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) v) :=
  PhaseSubspaceGates.phase_unitary _
    (ODEGroverRay.projector_isOrthogonalProjection _ (seedState_norm v hv)) _ (by simp)

theorem rseedI_adjoint (v : P) :
    (rseedI (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) v)† = rseedI v := by
  rw [← star_eq_adjoint, rseedI, PhaseSubspaceGates.phase_adjoint _ (projector_star _)]
  simp

theorem pres2_rseedI (v : P) :
    Pres2 WorkClean (rseedI (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) v) := by
  have hpres : Preserves WorkClean (rseedI (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
      (f := f) v) := by
    intro ψ hψ
    have hrep : rseedI v ψ = ψ + (-1 - 1 : ℂ) • (inner ℂ (seedState v) ψ • seedState v) := by
      rw [rseedI, PhaseSubspaceGates.phase, add_apply, one_apply_eq_self, smul_apply,
        ODEGroverRay.projector_apply]
    rw [hrep]
    exact supp_add hψ (supp_smul _ (supp_smul _ (supp_bas _ workClean_zero _)))
  exact ⟨hpres, by rw [rseedI_adjoint]; exact hpres⟩

end

end SparseHamiltonian.GateODE
