import GateEfficientNative.Native.Edge

/-!
# The rotation part of the private operation

Angle words are binary fractions: the `bT`-bit word `w` encodes
`θ(w) = Σ_j w_j π / 2^(j+1) ∈ [0, π)` (`thetaVal`) and the `bP`-bit word `v`
encodes `φ(v) = Σ_j v_j 2π / 2^(j+1) ∈ [0, 2π)` (`phiVal`).

Under the enable wire `e`, the rotation circuit `rotGates` applies
`-R_z(-φ) R_x(2θ) R_z(φ) = angMat θ φ` to the target wire, reading `θ` and `φ`
from the angle wires: one `R_z` gate per bit of `φ` (twice) and one `R_x`
gate per bit of `θ`, each controlled by the enable wire and its bit, and a
final `-1` under the enable wire (`gRun_rotGates`).  All gates have at most two
controls; there are `2 bP + bT + 1` of them.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open scoped InnerProduct BigOperators

/-- The angle `θ ∈ [0, π)` encoded by a binary word. -/
def thetaVal {n : ℕ} (w : Fin n → Bool) : ℝ :=
  ∑ j : Fin n, if w j then Real.pi / 2 ^ (j.val + 1) else 0

/-- The angle `φ ∈ [0, 2π)` encoded by a binary word. -/
def phiVal {n : ℕ} (w : Fin n → Bool) : ℝ :=
  ∑ j : Fin n, if w j then 2 * Real.pi / 2 ^ (j.val + 1) else 0

section Gates

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- The `R_z(s φ)` gates, one per bit of `φ`. -/
def rzGates {n : ℕ} (e o : W) (pw : Fin n → W) (s : ℝ) : List (Gate W) :=
  (List.finRange n).map (fun j =>
    ⟨[(e, true), (pw j, true)], o, rzMat (s * (2 * Real.pi / 2 ^ (j.val + 1)))⟩)

/-- The `R_x(2θ)` gates, one per bit of `θ`. -/
def rxGates {n : ℕ} (e o : W) (tw : Fin n → W) : List (Gate W) :=
  (List.finRange n).map (fun j =>
    ⟨[(e, true), (tw j, true)], o, rxMat (2 * (Real.pi / 2 ^ (j.val + 1)))⟩)

/-- The rotation circuit: `-R_z(-φ) R_x(2θ) R_z(φ)` under the enable wire. -/
def rotGates {bT bP : ℕ} (e o : W) (tw : Fin bT → W) (pw : Fin bP → W) : List (Gate W) :=
  rzGates e o pw 1 ++ rxGates e o tw ++ rzGates e o pw (-1) ++ [⟨[(e, true)], o, -1⟩]

omit [Fintype W] [DecidableEq W] in
theorem rotGates_length {bT bP : ℕ} (e o : W) (tw : Fin bT → W) (pw : Fin bP → W) :
    (rotGates e o tw pw).length = 2 * bP + bT + 1 := by
  simp [rotGates, rzGates, rxGates]
  ring

/-- The product of the selected matrices of a gate list, last gate leftmost. -/
def selProd : List (Gate W) → Cfg W → Matrix Bool Bool ℂ
  | [], _ => 1
  | g :: gs, x => selProd gs x * (if ctrlOK g.cs x then g.u else 1)

/-- Gates on one target compose to one controlled operation. -/
theorem gRun_same_target (o : W) (gs : List (Gate W)) (h : ∀ g ∈ gs, g.t = o) :
    gRun (Q := Q) gs = condOp o (selProd gs) := by
  induction gs with
  | nil =>
      rw [gRun_nil]
      exact (condOp_one o).symm
  | cons g gs ih =>
      rw [gRun_cons, ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg')), Gate.op, gateOp,
        h g List.mem_cons_self, condOp_comp]
      rfl

omit [Fintype W] [DecidableEq W] in
theorem selProd_append (gs hs : List (Gate W)) (x : Cfg W) :
    selProd (gs ++ hs) x = selProd hs x * selProd gs x := by
  induction gs with
  | nil => simp [selProd]
  | cons g gs ih => simp only [List.cons_append, selProd, ih, Matrix.mul_assoc]

omit [Fintype W] [DecidableEq W] in
theorem selProd_rz {n : ℕ} (e o : W) (pw : Fin n → W) (s : ℝ) (x : Cfg W) :
    selProd (rzGates e o pw s) x =
      if x e then rzMat (s * phiVal (fun j => x (pw j))) else 1 := by
  have key : ∀ l : List (Fin n), selProd (l.map (fun j =>
      (⟨[(e, true), (pw j, true)], o, rzMat (s * (2 * Real.pi / 2 ^ (j.val + 1)))⟩ : Gate W))) x =
      if x e then rzMat (s * (l.map (fun j => if x (pw j) then 2 * Real.pi / 2 ^ (j.val + 1)
        else 0)).sum) else 1 := by
    intro l
    induction l with
    | nil =>
        simp only [List.map_nil, selProd, List.sum_nil, mul_zero, rzMat_zero, ite_self]
    | cons j l ih =>
        simp only [List.map_cons, selProd, ih, List.sum_cons, ctrlOK_cons, ctrlOK_nil,
          Bool.and_true]
        cases hx : x e <;> cases hp : x (pw j) <;> simp [rzMat_mul, mul_add, add_comm]
  unfold rzGates phiVal
  rw [key, Fin.sum_univ_def]

omit [Fintype W] [DecidableEq W] in
theorem selProd_rx {n : ℕ} (e o : W) (tw : Fin n → W) (x : Cfg W) :
    selProd (rxGates e o tw) x =
      if x e then rxMat (2 * thetaVal (fun j => x (tw j))) else 1 := by
  have key : ∀ l : List (Fin n), selProd (l.map (fun j =>
      (⟨[(e, true), (tw j, true)], o, rxMat (2 * (Real.pi / 2 ^ (j.val + 1)))⟩ : Gate W))) x =
      if x e then rxMat ((l.map (fun j => if x (tw j) then 2 * (Real.pi / 2 ^ (j.val + 1))
        else 0)).sum) else 1 := by
    intro l
    induction l with
    | nil =>
        simp only [List.map_nil, selProd, List.sum_nil, rxMat_zero, ite_self]
    | cons j l ih =>
        simp only [List.map_cons, selProd, ih, List.sum_cons, ctrlOK_cons, ctrlOK_nil,
          Bool.and_true]
        cases hx : x e <;> cases hp : x (tw j) <;> simp [rxMat_mul, add_comm]
  unfold rxGates thetaVal
  rw [key, Finset.mul_sum, Fin.sum_univ_def]
  congr 3
  apply List.map_congr_left
  intro j _
  by_cases h : x (tw j) <;> simp [h]

omit [Fintype W] [DecidableEq W] in
theorem rotGates_targets {bT bP : ℕ} (e o : W) (tw : Fin bT → W) (pw : Fin bP → W) :
    ∀ g ∈ rotGates e o tw pw, g.t = o := by
  have h1 : ∀ s : ℝ, ∀ g ∈ rzGates e o pw s, g.t = o := by
    intro s g hg
    simp only [rzGates, List.mem_map] at hg
    obtain ⟨j, _, rfl⟩ := hg
    rfl
  have h2 : ∀ g ∈ rxGates e o tw, g.t = o := by
    intro g hg
    simp only [rxGates, List.mem_map] at hg
    obtain ⟨j, _, rfl⟩ := hg
    rfl
  intro g hg
  simp only [rotGates, List.mem_append, List.mem_singleton] at hg
  rcases hg with ((h | h) | h) | h
  · exact h1 1 g h
  · exact h2 g h
  · exact h1 (-1) g h
  · rw [h]

/-- **The rotation circuit** applies the angle form of the edge rotation,
read from the angle wires, under the enable wire. -/
theorem gRun_rotGates {bT bP : ℕ} (e o : W) (tw : Fin bT → W) (pw : Fin bP → W) :
    gRun (Q := Q) (rotGates e o tw pw) =
      condOp o (fun x => if x e then
        angMat (thetaVal (fun j => x (tw j))) (phiVal (fun j => x (pw j))) else 1) := by
  rw [gRun_same_target o _ (rotGates_targets e o tw pw)]
  congr 1
  funext x
  simp only [rotGates, selProd_append, selProd_rz, selProd_rx, selProd, ctrlOK_cons, ctrlOK_nil,
    Bool.and_true]
  cases hx : x e
  · simp
  · simp only [beq_self_eq_true, if_true, one_mul, neg_one_mul]
    rw [angMat_eq_rot, Matrix.mul_assoc]

omit [Fintype W] [DecidableEq W] in
/-- The rotation gates are elementary. -/
theorem rotGates_ok {bT bP : ℕ} (e o : W) (tw : Fin bT → W) (pw : Fin bP → W)
    (heo : e ≠ o) (hto : ∀ j, tw j ≠ o) (hpo : ∀ j, pw j ≠ o) :
    ∀ g ∈ rotGates e o tw pw, GateOK 3 g := by
  have h1 : ∀ s : ℝ, ∀ g ∈ rzGates e o pw s, GateOK 3 g := by
    intro s g hg
    simp only [rzGates, List.mem_map] at hg
    obtain ⟨j, _, rfl⟩ := hg
    refine ⟨by simp, ?_, rzMat_unitary _⟩
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact heo
    · exact hpo j
  have h2 : ∀ g ∈ rxGates e o tw, GateOK 3 g := by
    intro g hg
    simp only [rxGates, List.mem_map] at hg
    obtain ⟨j, _, rfl⟩ := hg
    refine ⟨by simp, ?_, rxMat_unitary _⟩
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact heo
    · exact hto j
  intro g hg
  simp only [rotGates, List.mem_append, List.mem_singleton] at hg
  rcases hg with ((h | h) | h) | h
  · exact h1 1 g h
  · exact h2 g h
  · exact h1 (-1) g h
  · subst h
    refine ⟨by simp, ?_, neg_one_unitaryMat⟩
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rw [hc]
    exact heo

end Gates

end

end SparseHamiltonian.GateNative
