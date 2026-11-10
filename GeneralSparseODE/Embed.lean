import GeneralSparseODE.Subst
import GeneralSparseAccess.PadSpec
import SparseHamiltonian.ODEConstantForcing
import SparseHamiltonian.ODEStateNormalization
import TimeDependentODE.Continuous.Solution
import GateEfficientNative.ODE.Grover

/-!
# The marker embedding of the padded index register

The padded data of `GeneralSparseAccess.QData.padData` have `k + 1`-bit index words: the low `k`
wires and a marker (`GeneralSparseAccess.mark`, the top wire). A vector of the `k`-qubit index
register is embedded with a clean marker (`markEmb`), and an operator on it is extended by zero to
the marked words (`zext A = markEmb ∘ A ∘ lowPart`, `lowPart` the column at a clean marker, which
is the adjoint of `markEmb`) or by the identity on the marker (`lowOp`):

* `markEmb_apply`, `norm_markEmb`, `lowPart_markEmb`, `markEmb_adjoint`, `norm_lowPart_le`;
* `zext_markEmb`, `norm_zext_le`, `zext_sub`, `accretive_zext`: the zero extension intertwines
  the embedding, is a contraction in the operator and keeps accretivity;
* `lowOp_markEmb`, `lowOp_isUnitary`, `seedV_markEmb`: the operator on the low wires, the seed;
* `unitDirection_markEmb`, `solution_comp`, `solves_zext`: the normalised direction, the solution of
  the constant-forcing problem along an intertwining map, and a solution of the time-dependent
  problem for the zero-extended generator path.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralSparseODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateODE (overwrite_apply_ι overwrite_apply_out)
open scoped InnerProduct

/-! ### Sums over the words with a clear marker -/

theorem sum_mark_false {k : ℕ} {M : Type*} [AddCommMonoid M] (g : Cfg (Fin k) → M) :
    ∑ y : Cfg (Fin (k + 1)), (if mark y = false then g (lo y) else 0) = ∑ d, g d := by
  have hinj : ∀ d ∈ (Finset.univ : Finset (Cfg (Fin k))),
      ∀ d' ∈ (Finset.univ : Finset (Cfg (Fin k))), idx false d = idx false d' → d = d' :=
    fun d _ d' _ h => (idx_injective h).2
  calc ∑ y : Cfg (Fin (k + 1)), (if mark y = false then g (lo y) else 0)
      = ∑ y ∈ Finset.univ.image (idx false), (if mark y = false then g (lo y) else 0) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro y _ hy
        rw [if_neg]
        intro h
        apply hy
        exact Finset.mem_image.mpr ⟨lo y, Finset.mem_univ _, (idx_eq_iff _ _ _).mpr ⟨h.symm, rfl⟩⟩
    _ = ∑ d, (if mark (idx false d) = false then g (lo (idx false d)) else 0) :=
        Finset.sum_image hinj
    _ = ∑ d, g d := Finset.sum_congr rfl (fun d _ => by rw [mk_idx, if_pos rfl, lo_idx])

/-! ### The marker embedding and the low part -/

section Marker

variable {k : ℕ} {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R]

/-- **The marker embedding**: a vector of the `k` low wires of the `k + 1`-bit index register,
the marker clean. -/
def markEmb (k : ℕ) : Reg (Fin k) R →L[ℂ] Reg (Fin (k + 1)) R :=
  cleanOn (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))

theorem markEmb_apply (ψ : Reg (Fin k) R) (y : Cfg (Fin (k + 1))) :
    markEmb k ψ y = if mark y = false then ψ (lo y) else 0 := by
  rw [markEmb, cleanOn_apply]
  have hc : (∀ w, (∀ s, (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) s ≠ w) → y w = false) ↔
      mark y = false := by
    constructor
    · intro h
      exact h (Fin.last k) (fun s hs => (Fin.castSucc_lt_last s).ne hs)
    · intro h w hw
      rcases Fin.eq_castSucc_or_eq_last w with ⟨s, rfl⟩ | h'
      · exact absurd rfl (hw s)
      · rw [h']
        exact h
  by_cases h : mark y = false
  · rw [if_pos (hc.mpr h), if_pos h]
    rfl
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]

theorem norm_markEmb (ψ : Reg (Fin k) R) : ‖markEmb k ψ‖ = ‖ψ‖ := norm_cleanOn _ ψ

/-- **The low part**: the column of a vector of the `k + 1`-bit register at a clean marker. -/
def lowPart (k : ℕ) : Reg (Fin (k + 1)) R →L[ℂ] Reg (Fin k) R :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Cfg (Fin k) => R)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun d => coord (idx false d))

theorem lowPart_apply (ψ : Reg (Fin (k + 1)) R) (d : Cfg (Fin k)) :
    lowPart k ψ d = ψ (idx false d) := rfl

theorem lowPart_markEmb : (lowPart k : Reg (Fin (k + 1)) R →L[ℂ] Reg (Fin k) R) ∘L markEmb k = 1 := by
  refine ContinuousLinearMap.ext fun ψ => PiLp.ext fun d => ?_
  rw [comp_apply, lowPart_apply, markEmb_apply, mk_idx, if_pos rfl, lo_idx]
  rfl

theorem inner_markEmb (φ : Reg (Fin k) R) (ψ : Reg (Fin (k + 1)) R) :
    inner ℂ (markEmb k φ) ψ = inner ℂ φ (lowPart k ψ) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  have e : ∀ y : Cfg (Fin (k + 1)), inner ℂ (markEmb k φ y) (ψ y) =
      if mark y = false then inner ℂ (φ (lo y)) (ψ (idx false (lo y))) else 0 := by
    intro y
    rw [markEmb_apply]
    by_cases h : mark y = false
    · rw [if_pos h, if_pos h]
      have hy : idx false (lo y) = y := by
        rw [← h]
        exact idx_mark_lo y
      rw [hy]
    · rw [if_neg h, if_neg h, inner_zero_left]
  rw [Finset.sum_congr rfl (fun y _ => e y),
    sum_mark_false (fun d => inner ℂ (φ d) (ψ (idx false d)))]
  rfl

variable [CompleteSpace R]

/-- **The low part is the adjoint of the marker embedding.** -/
theorem markEmb_adjoint : (markEmb k : Reg (Fin k) R →L[ℂ] Reg (Fin (k + 1)) R)† = lowPart k := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro ψ φ
  rw [← inner_conj_symm, ← inner_markEmb, inner_conj_symm]

omit [CompleteSpace R] in
theorem norm_markEmb_le : ‖(markEmb k : Reg (Fin k) R →L[ℂ] Reg (Fin (k + 1)) R)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun ψ => by rw [one_mul, norm_markEmb])

theorem norm_lowPart_le : ‖(lowPart k : Reg (Fin (k + 1)) R →L[ℂ] Reg (Fin k) R)‖ ≤ 1 := by
  rw [← markEmb_adjoint, ContinuousLinearMap.adjoint.norm_map]
  exact norm_markEmb_le

/-- **The zero extension** of an operator on the low wires to the `k + 1`-bit register: the
operator on the words with a clean marker, zero on the marked words. -/
def zext (A : Reg (Fin k) R →L[ℂ] Reg (Fin k) R) : Reg (Fin (k + 1)) R →L[ℂ] Reg (Fin (k + 1)) R :=
  markEmb k ∘L A ∘L lowPart k

omit [CompleteSpace R] in
theorem zext_markEmb (A : Reg (Fin k) R →L[ℂ] Reg (Fin k) R) :
    zext A ∘L markEmb k = markEmb k ∘L A := by
  refine ContinuousLinearMap.ext fun v => ?_
  show markEmb k (A (lowPart k (markEmb k v))) = markEmb k (A v)
  rw [← comp_apply (lowPart k) (markEmb k), lowPart_markEmb]
  rfl

omit [CompleteSpace R] in
theorem zext_sub (A B : Reg (Fin k) R →L[ℂ] Reg (Fin k) R) : zext A - zext B = zext (A - B) := by
  rw [zext, zext, zext, ← comp_sub, ← sub_comp]

theorem norm_zext_le (A : Reg (Fin k) R →L[ℂ] Reg (Fin k) R) : ‖zext A‖ ≤ ‖A‖ := by
  calc ‖zext A‖ ≤ ‖(markEmb k : Reg (Fin k) R →L[ℂ] Reg (Fin (k + 1)) R)‖ * (‖A‖ *
        ‖(lowPart k : Reg (Fin (k + 1)) R →L[ℂ] Reg (Fin k) R)‖) := by
        rw [zext]
        exact (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _)
          (norm_nonneg _))
    _ ≤ 1 * (‖A‖ * 1) := by
        gcongr
        · exact norm_markEmb_le
        · exact norm_lowPart_le
    _ = ‖A‖ := by ring

end Marker

/-! ### Accretivity, the low wires and the seed -/

section Complex

variable {k : ℕ}

/-- **The zero extension keeps accretivity.** -/
theorem accretive_zext {A : Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ}
    (h : TimeDependentODE.Accretive A) : TimeDependentODE.Accretive (zext A) := by
  intro w
  show 0 ≤ (inner ℂ w (markEmb k (A (lowPart k w)))).re
  rw [← inner_conj_symm, inner_markEmb, Complex.conj_re, ← inner_conj_symm, Complex.conj_re]
  exact h (lowPart k w)

/-- **An operator on the low wires**, the identity on the marker. -/
def lowOp (O : Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) : Reg (Fin (k + 1)) ℂ →L[ℂ] Reg (Fin (k + 1)) ℂ :=
  localOp (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))
    (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)).injective (fun _ => O)

theorem lowOp_markEmb (O : Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) :
    lowOp O ∘L markEmb k = markEmb k ∘L O :=
  localOp_cleanOn _ O

theorem lowOp_isUnitary {O : Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ} (hO : IsUnitary O) :
    IsUnitary (lowOp O) :=
  localOp_isUnitary _ _ (fun _ => hO)

theorem lowOp_one : lowOp (1 : Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) = 1 := localOp_one _

/-- **The seed of the padded register** is the marker embedding of the seed. -/
theorem seedV_markEmb : (seedV : Reg (Fin (k + 1)) ℂ) = markEmb k (seedV : Reg (Fin k) ℂ) := by
  apply PiLp.ext
  intro y
  rw [markEmb_apply, seedV, seedV, bas_apply, bas_apply]
  by_cases h : mark y = false
  · rw [if_pos h]
    by_cases hy : y = fun _ => false
    · subst hy
      rw [if_pos rfl, if_pos (show lo (fun _ => false) = (fun _ : Fin k => false) from rfl)]
    · rw [if_neg hy, if_neg]
      intro hl
      apply hy
      rw [← idx_mark_lo y, h, hl]
      funext i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · show (idx false fun _ => false) (Fin.castSucc j) = false
        have := congrFun (lo_idx false (fun _ : Fin k => false)) j
        exact this
      · exact mk_idx false _
  · rw [if_neg h, if_neg]
    rintro rfl
    exact h rfl

/-- **The normalised direction of an embedded vector** is the embedded normalised direction. -/
theorem unitDirection_markEmb (ψ : Reg (Fin k) ℂ) :
    ODEStateNormalization.unitDirection (markEmb k ψ) =
      markEmb k (ODEStateNormalization.unitDirection ψ) := by
  unfold ODEStateNormalization.unitDirection
  rw [norm_markEmb, map_smul_of_tower]

end Complex

/-! ### The solutions along an intertwining map -/

section Solution

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- **The constant-forcing solution along an intertwining map**: for `A' ∘ L = L ∘ A`, the
solution of `x' = A' x + L b` from `L x₀` is `L` of the solution of `x' = A x + b` from `x₀`. -/
theorem solution_comp (A : V →L[ℂ] V) (A' : W →L[ℂ] W) (L : V →L[ℂ] W)
    (h : A' ∘L L = L ∘L A) (x0 b : V) (t : ℝ) :
    ODEConstantForcing.solution A' (L x0) (L b) t = L (ODEConstantForcing.solution A x0 b t) := by
  have hexp : ∀ s : ℝ, NormedSpace.exp (s • A') ∘L L = L ∘L NormedSpace.exp (s • A) := by
    intro s
    apply exp_comp_of_comp
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [comp_apply, smul_apply]
    rw [map_smul_of_tower]
    exact congrArg (fun u => s • u) (DFunLike.congr_fun h v)
  have htraj : ∀ (v : V) (s : ℝ), ODEDissipative.trajectory A' (L v) s =
      L (ODEDissipative.trajectory A v s) := fun v s =>
    DFunLike.congr_fun (hexp s) v
  unfold ODEConstantForcing.solution ODEConstantForcing.response
  rw [htraj, map_add]
  congr 1
  simp_rw [htraj]
  exact L.intervalIntegral_comp_comm
    ((ODEDissipative.trajectory_continuous A b).intervalIntegrable _ _)

end Solution

/-! ### The time-dependent problem for the zero-extended generator path -/

section Time

variable {k : ℕ}

/-- **A solution for the zero-extended generator path**: if `x` solves `x' = -G(t) x + b(t)` on
`[a, c]`, then `markEmb ∘ x` solves it for `zext ∘ G` and `markEmb ∘ b`. -/
theorem solves_zext {G : ℝ → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ} {bf xs : ℝ → Reg (Fin k) ℂ}
    {a c : ℝ} (h : TimeDependentODE.SolvesODE G bf xs a c) :
    TimeDependentODE.SolvesODE (fun u => zext (G u)) (fun u => markEmb k (bf u))
      (fun u => markEmb k (xs u)) a c := by
  intro u hu
  have h1 := (((markEmb k : Reg (Fin k) ℂ →L[ℂ] Reg (Fin (k + 1)) ℂ).restrictScalars ℝ).hasFDerivAt
    (x := xs u)).comp_hasDerivWithinAt u (h u hu)
  have e : ((markEmb k : Reg (Fin k) ℂ →L[ℂ] Reg (Fin (k + 1)) ℂ).restrictScalars ℝ)
      (-(G u (xs u)) + bf u) = -(zext (G u) (markEmb k (xs u))) + markEmb k (bf u) := by
    rw [ContinuousLinearMap.coe_restrictScalars', map_add, map_neg]
    congr 2
    exact (DFunLike.congr_fun (zext_markEmb (G u)) (xs u)).symm
  rw [e] at h1
  exact h1

end Time

end

end SparseHamiltonian.GeneralSparseODE
