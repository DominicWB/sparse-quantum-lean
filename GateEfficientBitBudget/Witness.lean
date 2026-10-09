import GateEfficientBitBudget.Time

/-!
# The hypotheses of the endpoints in `𝔟` are satisfiable

The endpoints `binary_ode_budget_bits` and `binary_ode_time_budget_bits` (equations
`ode:eq:gate-main` and `ode:eq:gate-space` of Theorem `ode:thm:gates` in the word budget `𝔟` of
equation `ode:eq:gate-word-budget`) add to the released public conditions the public rescaling
`γ = gammaOf …`, the lower bound `ν ≤ 196608 q* ζ` of the arithmetic accuracy, `b ≤ b_data` and
the bit lengths `HasBits b_data` of `c₀`, `T`, `η_H`, `η_D`. The endpoints of equation
`hs:eq:gate-binary` add `b ≤ b_data`, `HasBits b_data c₀` and `ε ≤ 442368 q ζ`
(`exists_common_bits` with the list `[c₀]`, and `hs_zeta_spec`).

* `exists_common_bits`: finitely many dyadic rationals and a number `b` of stored bits have a
  common bit length `b_data ≥ b`.
* `withChoice_bits`, `withChoiceT_bits`: for public data with the released conditions whose `c₀`,
  `T`, `η_H`, `η_D` are dyadic rationals, the public choices `withChoice q`, `withChoiceT q`
  satisfy every hypothesis of the endpoints on the public parameters for some `b_data`.
* `pointPub`, `pointPub_ok`, `pointPubT₀`, `pointPubT`, `pointPubT_ok`: explicit public data
  (`k_x = σ = 0`, `b = 1`, `c₀ = T = η_H = g = 1`, `η_D = 0`, `ε = 1/2`; for time-dependent
  coefficients the least admissible mesh exponent `m = simM τ ν`) with the released public
  conditions.
* `bits_witness`, `bits_witnessT`: with the public choices of `γ` and `ζ`, these data satisfy all
  of them jointly. The data hypotheses of the endpoints are met as well, by one-point binary data
  (`NonVacuity`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBitBudget

noncomputable section
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateBinaryODE
open SparseHamiltonian.GateBinaryODETime
open GateODEBudget (gammaOf qOf)

/-- **A common bit length**: finitely many dyadic rationals `n / 2^f` and a number `b` of stored
bits have a common bit length `b_data ≥ b` (`exists_hasBits`, `HasBits.mono`), so the
bit-length hypotheses of the endpoints of equations `ode:eq:gate-main`, `ode:eq:gate-space` and
`hs:eq:gate-binary` hold jointly for dyadic public parameters. -/
theorem exists_common_bits (b : ℕ) (xs : List ℝ)
    (h : ∀ x ∈ xs, ∃ (n : ℤ) (f : ℕ), x = n / 2 ^ f) :
    ∃ bd : ℕ, b ≤ bd ∧ ∀ x ∈ xs, HasBits bd x := by
  induction xs with
  | nil => exact ⟨b, le_rfl, fun x hx => by simp at hx⟩
  | cons y ys ih =>
    obtain ⟨bd, hb, hys⟩ := ih fun x hx => h x (List.mem_cons.mpr (Or.inr hx))
    obtain ⟨n, f, hy⟩ := h y (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨b', hb'⟩ := exists_hasBits n f
    refine ⟨bd + b', by omega, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with hx | hx
    · rw [hx, hy]
      exact hb'.mono (by omega)
    · exact (hys x hx).mono (by omega)

/-- **The public choices satisfy the hypotheses of `binary_ode_budget_bits`** (equations
`ode:eq:gate-main`, `ode:eq:gate-space`, constant coefficients): for public data with the released
conditions `Pub.OK` whose decoder scale `c₀`, time `T` and energy bounds `η_H`, `η_D` are dyadic
rationals, there is a bit length `b_data` such that `withChoice q` satisfies `Pub.OK`, the public
rescaling `γ = gammaOf T η_H η_D g ε`, the accuracy bound `ν ≤ 196608 q* ζ`, `b ≤ b_data` and the
bit lengths `HasBits b_data` of `c₀`, `T`, `η_H`, `η_D`. -/
theorem withChoice_bits (q : Pub) (hq : q.OK) (hc0 : ∃ (n : ℤ) (f : ℕ), q.c0 = n / 2 ^ f)
    (hT : ∃ (n : ℤ) (f : ℕ), q.T = n / 2 ^ f) (hH : ∃ (n : ℤ) (f : ℕ), q.etaH = n / 2 ^ f)
    (hD : ∃ (n : ℤ) (f : ℕ), q.etaD = n / 2 ^ f) :
    ∃ bd : ℕ, (withChoice q).OK ∧
      (withChoice q).γ = gammaOf (withChoice q).T (withChoice q).etaH (withChoice q).etaD
        (withChoice q).g (withChoice q).ε ∧
      (withChoice q).params.nu ≤ 196608 * qOf (withChoice q).s (withChoice q).T
        (withChoice q).etaH (withChoice q).etaD (withChoice q).g (withChoice q).ε *
          (withChoice q).ζ ∧
      (withChoice q).b ≤ bd ∧ HasBits bd (withChoice q).c0 ∧ HasBits bd (withChoice q).T ∧
      HasBits bd (withChoice q).etaH ∧ HasBits bd (withChoice q).etaD := by
  obtain ⟨hok, hγ, hζ, -⟩ := withChoice_spec q hq
  obtain ⟨bd, hb, hall⟩ := exists_common_bits q.b [q.c0, q.T, q.etaH, q.etaD] (by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [hc0, hT, hH, hD])
  exact ⟨bd, hok, hγ, hζ, hb, hall q.c0 (by simp), hall q.T (by simp), hall q.etaH (by simp),
    hall q.etaD (by simp)⟩

/-- **The public choices satisfy the hypotheses of `binary_ode_time_budget_bits`** (equations
`ode:eq:gate-main`, `ode:eq:gate-space`, time-dependent coefficients): for public data with the
released conditions `PubT.OK` whose `c₀`, `T`, `η_H`, `η_D` are dyadic rationals, there is a bit
length `b_data` such that `withChoiceT q` satisfies `PubT.OK` (the mesh condition included), the
public rescaling `γ = gammaOf T η_H η_D (2g) (ε/2)`, the accuracy bound `ν ≤ 196608 q* ζ`,
`b ≤ b_data` and the bit lengths `HasBits b_data` of `c₀`, `T`, `η_H`, `η_D`. -/
theorem withChoiceT_bits (q : PubT) (hq : q.OK) (hc0 : ∃ (n : ℤ) (f : ℕ), q.c0 = n / 2 ^ f)
    (hT : ∃ (n : ℤ) (f : ℕ), q.T = n / 2 ^ f) (hH : ∃ (n : ℤ) (f : ℕ), q.etaH = n / 2 ^ f)
    (hD : ∃ (n : ℤ) (f : ℕ), q.etaD = n / 2 ^ f) :
    ∃ bd : ℕ, (withChoiceT q).OK ∧
      (withChoiceT q).γ = gammaOf (withChoiceT q).T (withChoiceT q).etaH (withChoiceT q).etaD
        (2 * (withChoiceT q).g) ((withChoiceT q).ε / 2) ∧
      (withChoiceT q).params.nu ≤ 196608 * qOf (withChoiceT q).s (withChoiceT q).T
        (withChoiceT q).etaH (withChoiceT q).etaD (2 * (withChoiceT q).g)
          ((withChoiceT q).ε / 2) * (withChoiceT q).ζ ∧
      (withChoiceT q).b ≤ bd ∧ HasBits bd (withChoiceT q).c0 ∧ HasBits bd (withChoiceT q).T ∧
      HasBits bd (withChoiceT q).etaH ∧ HasBits bd (withChoiceT q).etaD := by
  obtain ⟨hok, hγ, hζ, -⟩ := withChoiceT_spec q hq
  obtain ⟨bd, hb, hall⟩ := exists_common_bits q.b [q.c0, q.T, q.etaH, q.etaD] (by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [hc0, hT, hH, hD])
  exact ⟨bd, hok, hγ, hζ, hb, hall q.c0 (by simp), hall q.T (by simp), hall q.etaH (by simp),
    hall q.etaD (by simp)⟩

/-- **The explicit public data of the witnesses** (constant coefficients): `k_x = σ = 0`, `b = 1`,
`c₀ = η_H = γ = T = g = r₀ = 1`, `η_D = r_b = 0`, `ε = ζ = 1/2`. -/
def pointPub : Pub := ⟨0, 0, le_rfl, 1, 1, 1, 0, 1, 1, 1, 1 / 2, 1, 0, 1 / 2⟩

/-- The explicit public data `pointPub` satisfy the released public conditions `Pub.OK`. -/
theorem pointPub_ok : pointPub.OK := by
  constructor <;> norm_num [pointPub]

/-- The explicit public data of the time-dependent witnesses before the choice of the mesh:
`k_x = σ = 0`, `b = 1`, `c₀ = η_H = γ = T = g = 1`, `η_D = 0`, `ε = ζ = 1/2`, `m = 0`. -/
def pointPubT₀ : PubT := ⟨0, 0, le_rfl, 1, 1, 1, 0, 1, 1, 1, 1 / 2, 0, 1 / 2⟩

/-- **The explicit public data of the witnesses** (time-dependent coefficients): `pointPubT₀`
with the least admissible mesh exponent `m = simM τ ν` (the coarsest admissible mesh). -/
def pointPubT : PubT :=
  { pointPubT₀ with m := Sim.simM pointPubT₀.params.tau pointPubT₀.params.nu }

/-- The explicit public data `pointPubT` satisfy the released public conditions `PubT.OK`, the
mesh condition `steps τ (ν/3) ≤ 2^m` included (`Sim.simM_spec`). -/
theorem pointPubT_ok : pointPubT.OK := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (Sim.simM_spec pointPubT₀.params.tau pointPubT₀.params.nu).1⟩ <;>
    norm_num [pointPubT, pointPubT₀]

/-- **An explicit instance of the hypotheses of `binary_ode_budget_bits`** on the public
parameters (equations `ode:eq:gate-main`, `ode:eq:gate-space`, constant coefficients): the public
data `withChoice pointPub` (`k_x = σ = 0`, `b = 1`, `c₀ = T = η_H = g = r₀ = 1`, `η_D = r_b = 0`,
`ε = 1/2`, the public choices of `γ` and `ζ`) satisfy `Pub.OK`, the public rescaling, the accuracy
bound and, for some `b_data`, `b ≤ b_data` and the four bit-length hypotheses. -/
theorem bits_witness : ∃ (q : Pub) (bd : ℕ), q.OK ∧
    q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε ∧
    q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ ∧
    q.b ≤ bd ∧ HasBits bd q.c0 ∧ HasBits bd q.T ∧ HasBits bd q.etaH ∧ HasBits bd q.etaD := by
  obtain ⟨bd, h⟩ := withChoice_bits pointPub pointPub_ok ⟨1, 0, by norm_num [pointPub]⟩
    ⟨1, 0, by norm_num [pointPub]⟩ ⟨1, 0, by norm_num [pointPub]⟩ ⟨0, 0, by norm_num [pointPub]⟩
  exact ⟨withChoice pointPub, bd, h⟩

/-- **An explicit instance of the hypotheses of `binary_ode_time_budget_bits`** on the public
parameters (equations `ode:eq:gate-main`, `ode:eq:gate-space`, time-dependent coefficients): the
public data `withChoiceT pointPubT` (`k_x = σ = 0`, `b = 1`, `c₀ = T = η_H = g = 1`, `η_D = 0`,
`ε = 1/2`, the coarsest admissible mesh (least admissible exponent) and the public choices of `γ`,
`ζ` and the mesh) satisfy `PubT.OK`, the public rescaling, the accuracy bound and, for some
`b_data`, `b ≤ b_data` and the four bit-length hypotheses. -/
theorem bits_witnessT : ∃ (q : PubT) (bd : ℕ), q.OK ∧
    q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) ∧
    q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ ∧
    q.b ≤ bd ∧ HasBits bd q.c0 ∧ HasBits bd q.T ∧ HasBits bd q.etaH ∧ HasBits bd q.etaD := by
  obtain ⟨bd, h⟩ := withChoiceT_bits pointPubT pointPubT_ok
    ⟨1, 0, by norm_num [pointPubT, pointPubT₀]⟩ ⟨1, 0, by norm_num [pointPubT, pointPubT₀]⟩
    ⟨1, 0, by norm_num [pointPubT, pointPubT₀]⟩ ⟨0, 0, by norm_num [pointPubT, pointPubT₀]⟩
  exact ⟨withChoiceT pointPubT, bd, h⟩

end

end SparseHamiltonian.GateBitBudget
