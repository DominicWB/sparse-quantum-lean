import GateEfficientBinaryODE.Clock
import GateEfficientBinaryODETime.Arith
import GateEfficientNative.ODE.Time

/-!
# The LCHS grid and the integer layout of the time-dependent solver

The time-dependent solver (`GateODE.Time.TParams`) uses the released analytic Gaussian LCHS grid
with the internal ratio `2g` and accuracy `ε/2`. This is the grid of the constant-coefficient
parameters `gridP p` (`GateODE.Params` with `g := 2g`, `ε := ε/2` and the same `T`, `λ_D`): the
grid size `J`, the LCHS word length `l` and the padded nodes `nodeW` of `p` and of `gridP p`
agree by definition. The rounded LCHS step and its lemmas of `GateEfficientBinaryODE`
(`hStep`, `fOf`, `hRound`, `rhoL`, `rhoL_close`, `layOf_ok`, `nodeW_eq`) are therefore used for
`gridP p`.

* `layT p b F`: the integer layout `layOf (gridP p) b F` of the released arithmetic without node
  bits (`kq = 0`): the duration factor of the time-dependent program is the slot mask
  (`dv_lift`), a single bit; `layT_ok`: it is admissible.
* `kapT`: the decoder scale `κ = γ √(4s) c₀ / (2^(F + 10) ρ)`.
* `gridP_g`, `gridP_ε`, `gridP_ε1`, `hStepT_pos`, `rhoLT_close`, `hRoundT_ne`: the grid conditions
  for public data with `g ≥ 1` and `0 < ε ≤ 1`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinaryODETime

noncomputable section
open SparseHamiltonian.GateBinaryODE
open SparseHamiltonian.GateODE.Time (TParams)
open GatePointerEncoding (wordValue)

/-- **The grid parameters** of the time-dependent solver: the constant-coefficient parameters with
the internal ratio `2g` and accuracy `ε/2` (only `T`, `λ_D`, `g` and `ε` matter). -/
def gridP (p : TParams) : GateODE.Params := ⟨0, 0, 0, p.T, 0, p.lamD, p.ratio, p.acc, 0, 0⟩

theorem gridP_J (p : TParams) : (gridP p).J = p.J := rfl

theorem gridP_l (p : TParams) : (gridP p).l = p.l := rfl

theorem gridP_nodeW (p : TParams) (w : Fin p.l → Bool) : (gridP p).nodeW w = p.nodeW w := rfl

/-- The padded LCHS node of a word is `n_w h` for the rounded grid. -/
theorem nodeWT_eq (p : TParams) (w : Fin p.l → Bool) :
    p.nodeW w = ((if wordValue w < p.J then (wordValue w : ℤ) -
      GateODE.AnalyticLCHS.halfCount (p.T * p.lamD) p.ratio p.acc else 0 : ℤ) : ℝ) *
        hStep (gridP p) :=
  nodeW_eq (gridP p) w

/-- **The integer layout** of the time-dependent arithmetic: the released layout of the grid
(`layOf (gridP p) b F`), without node bits. -/
abbrev layT (p : TParams) (b F : ℕ) : Lay :=
  ⟨b, 0, p.l, GateODE.AnalyticLCHS.halfCount (p.T * p.lamD) p.ratio p.acc, p.J, F,
    hRound (gridP p) F⟩

theorem layT_kq (p : TParams) (b F : ℕ) : (layT p b F).kq = 0 := rfl

/-- **The decoder scale** `κ = γ √(4s) c₀ / (2^(F + 10) ρ)`. -/
def kapT (s : ℕ) (c0 ρ γ : ℝ) (F : ℕ) : ℝ :=
  γ * Real.sqrt (4 * s) * c0 / (2 ^ (F + 10) * ρ)

theorem kapT_pos (s : ℕ) (c0 ρ γ : ℝ) (F : ℕ) (hs : 0 < s) (hc0 : 0 < c0) (hρ : 0 < ρ)
    (hγ : 0 < γ) : 0 < kapT s c0 ρ γ F := by
  have : 0 < Real.sqrt (4 * (s : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  unfold kapT
  positivity

section Cond

variable (p : TParams)

theorem gridP_g (hg : 1 ≤ p.g) : 1 ≤ (gridP p).g := p.ratio_ge hg

theorem gridP_ε (hε : 0 < p.ε) : 0 < (gridP p).ε := p.acc_pos hε

theorem gridP_ε1 (hε1 : p.ε ≤ 1) : (gridP p).ε ≤ 1 := p.acc_le_one hε1

theorem hStepT_pos (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hε1 : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD) :
    0 < hStep (gridP p) :=
  hStep_pos (gridP p) (gridP_g p hg) (gridP_ε p hε) (gridP_ε1 p hε1) hTD

/-- The layout is admissible. -/
theorem layT_ok (b F : ℕ) (hb : 0 < b) (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hε1 : p.ε ≤ 1)
    (hTD : 0 ≤ p.T * p.lamD) : (layT p b F).OK := by
  have h := layOf_ok (gridP p) b F hb (gridP_g p hg) (gridP_ε p hε) (gridP_ε1 p hε1) hTD
  exact ⟨h.b_pos, h.J_le, h.K_lt, h.Hn_lt⟩

/-- **The rounded step factor** is within `ζ/4` of one for `F = fOf (gridP p) ζ`. -/
theorem rhoLT_close (ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hg : 1 ≤ p.g) (hε : 0 < p.ε)
    (hε1 : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD) :
    |rhoL (gridP p) (fOf (gridP p) ζ) - 1| ≤ ζ / 4 :=
  rhoL_close (gridP p) ζ hζ hζ1 (hStepT_pos p hg hε hε1 hTD)

/-- The rounded step is nonzero. -/
theorem hRoundT_ne (ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hg : 1 ≤ p.g) (hε : 0 < p.ε)
    (hε1 : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD) : hRound (gridP p) (fOf (gridP p) ζ) ≠ 0 := by
  have h1 : 2 / ζ ≤ (hRound (gridP p) (fOf (gridP p) ζ) : ℝ) :=
    hRound_ge (gridP p) ζ hζ hζ1 (hStepT_pos p hg hε hε1 hTD)
  have h2 : (0 : ℝ) < hRound (gridP p) (fOf (gridP p) ζ) :=
    lt_of_lt_of_le (div_pos two_pos hζ) h1
  have h3 : 0 < hRound (gridP p) (fOf (gridP p) ζ) := by exact_mod_cast h2
  exact h3.ne'

end Cond

end

end SparseHamiltonian.GateBinaryODETime
