import AdaptiveHamiltonianLowerBound.Weight.Search
import LinearSystemLowerBound.Hard.Native

set_option autoImplicit false

/-!
# Admissible native calls and their search-weight growth

The released native sparse access (`NativeSparseBlockEncoding.Data`, `oracles`) consists of
the in-place row and column location oracles and the additive entry-value oracle, all on the
common space `NSpace N Z`. The linear-system lower bound admits as oracle labels the
*admissible* operators (`LinearSystemLowerBound.Native.Admissible`): a native call — in a
fixed isometric layout `K ≃ ⊕_{σ ∈ S} NSpace`, every spectator branch applies the identity,
one native query or the inverse of one, with weight at least one — or an input-independent
unitary of any weight. Native calls include spectator registers, controlled and masked
versions, inverses and coherent choices of the native query (manuscript lines 2078-2081:
"with inverses and coherent controls").

That definition is stated for inputs `Fin n → Fin m`. The precision family of the
Hamiltonian-simulation lower bound has inputs `Fin n → Bool`, so `Access.Admissible`
restates it for native data over any input type; for inputs `Fin n → Fin m` it is the same
notion (`admissible_iff_native`).

**Growth along a map of inputs.** For a map `g : (Fin n → Fin m) → X`, data `D` over `X` has
`HardAccess D g` if its location oracles are input-independent and every table entry, read at
`g j`, is a fixed function of at most one bit `[j c = q₀]` (`Hard.BitDetermined`). Then every
admissible label `O`, read along `g`, has growth `(λ²)^w` in both directions for the search
weight (`λ = searchLam m a`, `wgrowth_admissible`): on every address block a value query is a
translation of the value register that depends on one bit (`wgrowth_lookup`), which costs one
factor `λ²` (`wgrowth_bit`).
-/

namespace AdaptiveHamiltonianLowerBound

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct
open SparseHamiltonian ContinuousLinearMap
open LinearSystemLowerBound

namespace Access

/-! ### Admissible labels over any input type -/

section Admissible

variable {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s : ℕ}

/-- One spectator branch of a native call: identity, a native query, or its inverse. -/
def callOp (D : NativeSparseBlockEncoding.Data X N Z s) :
    Option (NativeSparseBlockEncoding.Query × Bool) → X →
      Native.NSpace N Z →L[ℂ] Native.NSpace N Z
  | none, _ => 1
  | some (q, false), x => NativeSparseBlockEncoding.oracles D q x
  | some (q, true), x => star (NativeSparseBlockEncoding.oracles D q x)

/-- **A native call**: in a fixed isometric layout of the workspace as spectator branches of
the native space, every branch applies the identity, one native query, or its inverse. -/
def NativeCall {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (D : NativeSparseBlockEncoding.Data X N Z s) (O : X → K →L[ℂ] K) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (layout : K ≃ₗᵢ[ℂ] PiLp 2 (fun _ : S => Native.NSpace N Z))
    (call : S → Option (NativeSparseBlockEncoding.Query × Bool)),
    ∀ x, O x = layout.symm.conjStarAlgEquiv
      (WeightedClock.diagonal (fun σ : S => callOp D (call σ) x))

/-- **Admissible labels**: native calls of weight at least one, or input-independent
unitaries of any weight. -/
def Admissible {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (D : NativeSparseBlockEncoding.Data X N Z s) (O : X → K →L[ℂ] K) (w : ℕ) : Prop :=
  (NativeCall D O ∧ 1 ≤ w) ∨ ((∀ x x', O x = O x') ∧ ∀ x, OracleCircuit.IsUnitary (O x))

theorem callOp_eq_native {n m : ℕ} (D : NativeSparseBlockEncoding.Data (Fin n → Fin m) N Z s)
    (c : Option (NativeSparseBlockEncoding.Query × Bool)) (x : Fin n → Fin m) :
    callOp D c x = Native.callOp D c x := by
  rcases c with _ | ⟨q, _ | _⟩ <;> rfl

/-- For inputs `Fin n → Fin m`, admissibility is that of the linear-system lower bound. -/
theorem admissible_iff_native {n m : ℕ} {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (D : NativeSparseBlockEncoding.Data (Fin n → Fin m) N Z s) (O : (Fin n → Fin m) → K →L[ℂ] K)
    (w : ℕ) : Admissible D O w ↔ Native.Admissible D O w := by
  unfold Admissible Native.Admissible NativeCall Native.NativeCall
  simp only [callOp_eq_native]

theorem callOp_unitary (D : NativeSparseBlockEncoding.Data X N Z s)
    (c : Option (NativeSparseBlockEncoding.Query × Bool)) (x : X) :
    OracleCircuit.IsUnitary (callOp D c x) := by
  rcases c with _ | ⟨q, _ | _⟩
  · show OracleCircuit.IsUnitary (1 : Native.NSpace N Z →L[ℂ] Native.NSpace N Z)
    exact ⟨by simp, by simp⟩
  · exact NativeSparseBlockEncoding.oracles_unitary D q x
  · exact (NativeSparseBlockEncoding.oracles_unitary D q x).adjoint

theorem callOp_star (D : NativeSparseBlockEncoding.Data X N Z s)
    (c : Option (NativeSparseBlockEncoding.Query × Bool)) (x : X) :
    star (callOp D c x) = callOp D (c.map fun p => (p.1, !p.2)) x := by
  rcases c with _ | ⟨q, _ | _⟩
  · simp [callOp]
  · simp [callOp]
  · simp [callOp]

/-- Admissible labels are unitary on every input. -/
theorem admissible_unitary {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (D : NativeSparseBlockEncoding.Data X N Z s) (O : X → K →L[ℂ] K) (w : ℕ)
    (hO : Admissible D O w) (x : X) : OracleCircuit.IsUnitary (O x) := by
  rcases hO with ⟨⟨S, hS, layout, call, hcall⟩, -⟩ | ⟨-, hunit⟩
  · rw [hcall]
    exact (Native.diagonal_unitary _ (fun σ => callOp_unitary D (call σ) x)).transport
      layout.symm
  · exact hunit x

/-- **Access conditions along a map of inputs**: input-independent location oracles, and
table entries that, read at `g j`, are fixed functions of at most one bit of `j`. -/
structure HardAccess {n m : ℕ} (D : NativeSparseBlockEncoding.Data X N Z s)
    (g : (Fin n → Fin m) → X) : Prop where
  row_const : ∀ x x', D.rowOracle x = D.rowOracle x'
  column_const : ∀ x x', D.columnOracle x = D.columnOracle x'
  table_bit : ∀ α, Hard.BitDetermined (fun j => D.table (g j) α)

end Admissible

/-! ### Search-weight growth -/

section Growth

variable {n m : ℕ}

/-- An input-independent norm-preserving family has growth `1` for every weight. -/
theorem wgrowth_const_of_eq {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (a : Matrix (Fin m) (Fin m) ℂ) (U : (Fin n → Fin m) → K →L[ℂ] K)
    (hU : ∀ x x', U x = U x') (hn : ∀ x v, ‖U x v‖ = ‖v‖) : WGrowth a U 1 := by
  intro ψ
  have h : act (kron a) (joint U ψ) = joint U (act (kron a) ψ) := by
    ext j
    simp only [act_apply, joint_apply, map_sum, map_smul]
    exact Finset.sum_congr rfl fun j' _ => by rw [hU j' j]
  rw [h, norm_joint U hn, one_mul]

variable (hm : Even m) {a : ℝ} (ha : 1 ≤ a)
include hm ha

omit hm in
theorem one_le_searchLam_sq : 1 ≤ searchLam m a ^ 2 :=
  one_le_pow₀ (one_le_searchLam m (by linarith))

/-- **A one-bit translation** of the value register has growth `λ²`. -/
theorem wgrowth_transl {Z Q : Type*} [Fintype Z] [AddCommGroup Z] [NormedAddCommGroup Q]
    [InnerProductSpace ℂ Q] (g : (Fin n → Fin m) → Z) (hg : Hard.BitDetermined g) :
    WGrowth (SparseLowerBounds.SearchWeight.w m a)
      (fun x => (Native.transl (g x) : Native.VSpace Z Q →L[ℂ] Native.VSpace Z Q))
      (searchLam m a ^ 2) := by
  rcases hg with ⟨e, he⟩ | ⟨c, q₀, e₀, e₁, he⟩
  · exact wgrowth_mono (wgrowth_congr
      (wgrowth_const _ (Native.transl (Q := Q) e) (Native.norm_transl (Q := Q) e))
      (fun x => by rw [he]))
      (one_le_searchLam_sq ha)
  · exact wgrowth_congr (wgrowth_bit hm ha c q₀ (Native.transl (Q := Q) e₀)
      (Native.transl (Q := Q) e₁) (Native.norm_transl (Q := Q) e₀)
      (Native.norm_transl (Q := Q) e₁))
      (fun x => by rw [he]; split_ifs <;> rfl)

omit hm ha in
/-- Weight growth of a block-diagonal family of value translations. -/
theorem wgrowth_slots {A Z Q : Type*} [Fintype A] [Fintype Z] [AddCommGroup Z]
    [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] (W : Matrix (Fin m) (Fin m) ℂ)
    (O : (Fin n → Fin m) → PiLp 2 (fun _ : A × Z => Q) →L[ℂ] PiLp 2 (fun _ : A × Z => Q))
    (g : (Fin n → Fin m) → A → Z) (C : ℝ)
    (hslot : ∀ α ψ, Native.slot α (joint O ψ) =
      joint (fun x => Native.transl (g x α)) (Native.slot α ψ))
    (h : ∀ α, WGrowth W
      (fun x => (Native.transl (g x α) : Native.VSpace Z Q →L[ℂ] Native.VSpace Z Q)) C) :
    WGrowth W O C := by
  intro ψ
  rw [Native.norm_sq_slot, Native.norm_sq_slot, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro α _
  rw [Native.slot_act, hslot, Native.slot_act]
  exact h α _

/-- **An additive lookup** has the growth of its one-bit address blocks. -/
theorem wgrowth_lookup {A Z Q : Type*} [Fintype A] [Fintype Z] [AddCommGroup Z]
    [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] (f : (Fin n → Fin m) → A → Z)
    (hf : ∀ α, Hard.BitDetermined (fun x => f x α)) :
    WGrowth (SparseLowerBounds.SearchWeight.w m a)
      (fun x => LookupControlledGate.oracle (K := Q) f x) (searchLam m a ^ 2) :=
  wgrowth_slots _ _ f _ (Native.slot_lookup f) (fun α => wgrowth_transl hm ha _ (hf α))

theorem wgrowth_lookup_star {A Z Q : Type*} [Fintype A] [Fintype Z] [AddCommGroup Z]
    [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (f : (Fin n → Fin m) → A → Z) (hf : ∀ α, Hard.BitDetermined (fun x => f x α)) :
    WGrowth (SparseLowerBounds.SearchWeight.w m a)
      (fun x => star (LookupControlledGate.oracle (K := Q) f x)) (searchLam m a ^ 2) :=
  wgrowth_slots _ _ (fun x α => -(f x α)) _ (Native.slot_lookup_star f)
    (fun α => wgrowth_transl hm ha _ ((hf α).comp (fun z => -z)))

variable {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s : ℕ}

/-- Growth of one native query, read along `g`, in both directions. -/
theorem wgrowth_oracles (D : NativeSparseBlockEncoding.Data X N Z s)
    (g : (Fin n → Fin m) → X) (hD : HardAccess D g) (q : NativeSparseBlockEncoding.Query) :
    WGrowth (SparseLowerBounds.SearchWeight.w m a)
        (fun j => NativeSparseBlockEncoding.oracles D q (g j)) (searchLam m a ^ 2) ∧
      WGrowth (SparseLowerBounds.SearchWeight.w m a)
        (fun j => star (NativeSparseBlockEncoding.oracles D q (g j))) (searchLam m a ^ 2) := by
  have h1 := one_le_searchLam_sq (m := m) ha
  have hconst : ∀ (U : X → Native.NSpace N Z →L[ℂ] Native.NSpace N Z),
      (∀ x x', U x = U x') → (∀ x, OracleCircuit.IsUnitary (U x)) →
      WGrowth (SparseLowerBounds.SearchWeight.w m a) (fun j => U (g j)) (searchLam m a ^ 2) ∧
        WGrowth (SparseLowerBounds.SearchWeight.w m a) (fun j => star (U (g j)))
          (searchLam m a ^ 2) := by
    intro U hU hUu
    refine ⟨wgrowth_mono (wgrowth_const_of_eq _ _ (fun j j' => hU (g j) (g j'))
        (fun j => isUnitary_norm (hUu (g j)))) h1, ?_⟩
    exact wgrowth_mono (wgrowth_const_of_eq _ _ (fun j j' => by rw [hU (g j) (g j')])
      (fun j => isUnitary_norm (hUu (g j)).adjoint)) h1
  cases q with
  | rowLocation =>
      exact hconst _ (fun x x' => by
          simp only [NativeSparseBlockEncoding.oracles, SparseFlagEmbedding.location,
            hD.row_const x x'])
        (fun x => NativeSparseBlockEncoding.oracles_unitary D _ x)
  | columnLocation =>
      exact hconst _ (fun x x' => by
          simp only [NativeSparseBlockEncoding.oracles, SparseFlagEmbedding.location,
            hD.column_const x x'])
        (fun x => NativeSparseBlockEncoding.oracles_unitary D _ x)
  | value =>
      exact ⟨wgrowth_lookup (Q := SparseFlagEmbedding.Qutrit) hm ha
          (fun j α => D.table (g j) α) hD.table_bit,
        wgrowth_lookup_star (Q := SparseFlagEmbedding.Qutrit) hm ha
          (fun j α => D.table (g j) α) hD.table_bit⟩

theorem wgrowth_callOp (D : NativeSparseBlockEncoding.Data X N Z s)
    (g : (Fin n → Fin m) → X) (hD : HardAccess D g)
    (c : Option (NativeSparseBlockEncoding.Query × Bool)) :
    WGrowth (SparseLowerBounds.SearchWeight.w m a) (fun j => callOp D c (g j))
      (searchLam m a ^ 2) := by
  have h1 := one_le_searchLam_sq (m := m) ha
  rcases c with _ | ⟨q, _ | _⟩
  · exact wgrowth_mono (wgrowth_const _ 1 (fun v => by simp)) h1
  · exact (wgrowth_oracles hm ha D g hD q).1
  · exact (wgrowth_oracles hm ha D g hD q).2

set_option synthInstance.maxHeartbeats 200000 in
/-- **Search-weight growth of admissible labels**, read along `g`, in both directions:
`(λ²)^w`. -/
theorem wgrowth_admissible {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (D : NativeSparseBlockEncoding.Data X N Z s)
    (g : (Fin n → Fin m) → X) (hD : HardAccess D g) (O : X → K →L[ℂ] K) (w : ℕ)
    (hO : Admissible D O w) :
    WGrowth (SparseLowerBounds.SearchWeight.w m a) (fun j => O (g j))
        ((searchLam m a ^ 2) ^ w) ∧
      WGrowth (SparseLowerBounds.SearchWeight.w m a) (fun j => star (O (g j)))
        ((searchLam m a ^ 2) ^ w) := by
  set C := searchLam m a ^ 2
  have h1 : 1 ≤ C := one_le_searchLam_sq ha
  rcases hO with ⟨⟨S, hS, layout, call, hcall⟩, hw⟩ | ⟨hconst, hunit⟩
  · have hpow : C ≤ C ^ w := le_self_pow₀ h1 (by omega)
    have hdiag : WGrowth (SparseLowerBounds.SearchWeight.w m a)
        (fun j => WeightedClock.diagonal (fun σ : S => callOp D (call σ) (g j))) C :=
      wgrowth_diagonal _ (fun σ j => callOp D (call σ) (g j)) C
        (fun σ => wgrowth_callOp hm ha D g hD _)
    have hdiag' : WGrowth (SparseLowerBounds.SearchWeight.w m a) (fun j => WeightedClock.diagonal
        (fun σ : S => callOp D ((call σ).map fun p => (p.1, !p.2)) (g j))) C :=
      wgrowth_diagonal _ _ C (fun σ => wgrowth_callOp hm ha D g hD _)
    have hO : (fun j => O (g j)) = fun j => layout.symm.conjStarAlgEquiv
        (WeightedClock.diagonal (fun σ : S => callOp D (call σ) (g j))) :=
      funext fun j => hcall (g j)
    have hstar : (fun j => star (O (g j))) = fun j => layout.symm.conjStarAlgEquiv
        (WeightedClock.diagonal
          (fun σ : S => callOp D ((call σ).map fun p => (p.1, !p.2)) (g j))) := by
      funext j
      rw [hcall, ← map_star, star_eq_adjoint, WeightedClock.diagonal_adjoint]
      congr 2
      funext σ
      rw [← star_eq_adjoint, callOp_star]
    refine ⟨?_, ?_⟩
    · rw [hO]
      exact wgrowth_mono (wgrowth_conj _ layout.symm _ C hdiag) hpow
    · rw [hstar]
      exact wgrowth_mono (wgrowth_conj _ layout.symm _ C hdiag') hpow
  · have hCw : 1 ≤ C ^ w := one_le_pow₀ h1
    refine ⟨wgrowth_mono (wgrowth_const_of_eq _ _ (fun j j' => hconst (g j) (g j'))
        (fun j => isUnitary_norm (hunit (g j)))) hCw, ?_⟩
    exact wgrowth_mono (wgrowth_const_of_eq _ _ (fun j j' => by rw [hconst (g j) (g j')])
      (fun j => isUnitary_norm (hunit (g j)).adjoint)) hCw

end Growth

end Access

end

end AdaptiveHamiltonianLowerBound
