import SparseHamiltonian.ChronologicalResolvent

/-!
# Two-sided inversion of chronological feedback

This module derives the forced inverse recurrence from the forward chronological
equations. It gives two-sided identities on sequences; restricting these causal
identities to a finite number of time slots is a separate representation step.
-/

namespace SparseHamiltonian.ChronologicalInverse

open ContinuousLinearMap
open SparseHamiltonian.ChronologicalResolvent

variable {P V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The chronological forward equations after moving the local diagonal term
to the left side. The auxiliary public state starts at zero. -/
def forwardResponse (X : V →L[ℂ] V) (A : P →L[ℂ] V)
    (c : P →L[ℂ] P) (B : V →L[ℂ] P) (x : ℕ → V) (n : ℕ) : V :=
  X (x n) - A (forcedPublicState c B x n)

/-- The explicit inverse obtained by local elimination of the private state. -/
def inverseResponse (R : V →L[ℂ] V) (A : P →L[ℂ] V)
    (c : P →L[ℂ] P) (B : V →L[ℂ] P) (y : ℕ → V) (n : ℕ) : V :=
  chronologicalPrivateState R (R ∘L A) (c + B ∘L R ∘L A) (B ∘L R) y n

/-- The reconstructed private trajectory drives exactly the forced public
trajectory used in the inverse construction. -/
theorem inverse_public_state (R : V →L[ℂ] V) (A : P →L[ℂ] V)
    (c : P →L[ℂ] P) (B : V →L[ℂ] P) (y : ℕ → V) (n : ℕ) :
    forcedPublicState c B (inverseResponse R A c B y) n =
      forcedPublicState (c + B ∘L R ∘L A) (B ∘L R) y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [forcedPublicState_succ, inverseResponse, chronologicalPrivateState,
        ih, comp_apply, add_apply, map_add]
      abel

/-- A right local inverse yields a right inverse of the complete chronological
equations, without an assumption about the final inverse formula. -/
theorem forward_inverse (X R : V →L[ℂ] V) (A : P →L[ℂ] V)
    (c : P →L[ℂ] P) (B : V →L[ℂ] P)
    (hXR : X ∘L R = 1) (y : ℕ → V) (n : ℕ) :
    forwardResponse X A c B (inverseResponse R A c B y) n = y n := by
  have hXRv (v : V) : X (R v) = v := by
    simpa using congrArg (fun M : V →L[ℂ] V => M v) hXR
  simp only [forwardResponse, inverse_public_state, inverseResponse,
    chronologicalPrivateState, map_add, comp_apply, hXRv, add_sub_cancel_right]

/-- If the local diagonal is injective then the chronological equations are
injective, by induction over the earlier private slots. -/
theorem forwardResponse_injective (X R : V →L[ℂ] V) (A : P →L[ℂ] V)
    (c : P →L[ℂ] P) (B : V →L[ℂ] P) (hRX : R ∘L X = 1) :
    Function.Injective (forwardResponse X A c B) := by
  intro x y hxy
  have hRXv (v : V) : R (X v) = v := by
    simpa using congrArg (fun M : V →L[ℂ] V => M v) hRX
  have hpair : ∀ n, forcedPublicState c B x n = forcedPublicState c B y n ∧ x n = y n := by
    intro n
    induction n with
    | zero =>
        constructor
        · rfl
        · have h := congrFun hxy 0
          simp only [forwardResponse, forcedPublicState_zero, map_zero, sub_zero] at h
          simpa only [hRXv] using congrArg R h
    | succ n ih =>
        have hp : forcedPublicState c B x (n + 1) = forcedPublicState c B y (n + 1) := by
          rw [forcedPublicState_succ, forcedPublicState_succ, ih.1, ih.2]
        refine ⟨hp, ?_⟩
        have h := congrFun hxy (n + 1)
        simp only [forwardResponse, hp, sub_left_inj] at h
        simpa only [hRXv] using congrArg R h
  funext n
  exact (hpair n).2

/-- Both local inverse identities give a genuine two-sided chronological
inverse. This also establishes uniqueness of the recovered trajectory. -/
theorem inverse_forward (X R : V →L[ℂ] V) (A : P →L[ℂ] V)
    (c : P →L[ℂ] P) (B : V →L[ℂ] P)
    (hXR : X ∘L R = 1) (hRX : R ∘L X = 1) (x : ℕ → V) :
    inverseResponse R A c B (forwardResponse X A c B x) = x := by
  apply forwardResponse_injective X R A c B hRX
  funext n
  exact forward_inverse X R A c B hXR (forwardResponse X A c B x) n

end SparseHamiltonian.ChronologicalInverse
