import GateEfficientBinary.Cordic.Arith
import GateEfficientHamiltonian.GatePointerEncoding

/-!
# The pre-processing program of the angle arithmetic

The decoded value of the four-sector private operation is a positive multiple of the Gaussian
integer

`Z' = 256 c_t d μ (A_x + i A_y)`

computed from the stored bits: the two stored entries `W₁ = X₁ + i Y₁` (of the located edge) and
`W₂ = X₂ + i Y₂` (of the transposed edge), the part bit, the tag bit, the source label (`ini`,
the node word `u`) and the LCHS word. Here

* `c_t = χ₁ (2 - χ₂) ∈ {0, 1, 2}`, `χ_i = [W_i ≠ 0]` (the tag split of `ODETaggedSupport`);
* `d = u` for a source node and `d = 2^kq` for the initial sector (the branch duration in units of
  `T / 2^kq`);
* `μ = n_w Hn` in the dissipative part, `n_w = V - K` for an LCHS word of value `V < J` and `0`
  beyond, and `μ = 2^F` in the Hamiltonian part (`Hn ≈ 2^F h` approximates the LCHS step);
* `A = (X₁ + X₂, Y₁ - Y₂)` in the dissipative and `A = (Y₁ + Y₂, X₂ - X₁)` in the Hamiltonian part,
  with `A_y` negated in the transposed tag.

The register program (`prog`) is a single-assignment program of the register operations of
`GateEfficientBinary` (`dst := a ± b`): conditional negations and zero tests by the sign bit,
selections `2 (c ? v₁ : v₀)` by `v ± v`, and multiplications by a `m`-bit number `M` by the chain
`(v << m) - v ± v ± (v << 1) ± ⋯ = 2 M v` (`chain`). `progOK` is its single-assignment property.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinaryODE

open SparseHamiltonian.GateBinary
open GatePointerEncoding (wordValue)

/-! ### Public integer layout -/

/-- The public integer layout of the arithmetic: `b` bits per stored component, `kq` node bits,
`lq` LCHS bits, the half count `K` and the size `J` of the LCHS grid, and the rounded step `Hn`
with `F` fractional bits. -/
structure Lay where
  b : ℕ
  kq : ℕ
  lq : ℕ
  K : ℕ
  J : ℕ
  F : ℕ
  Hn : ℕ

namespace Lay

variable (L : Lay)

/-- The register width. -/
def w : ℕ := L.b + L.kq + L.F + L.lq + 14

/-- The bits of the multiplier `|μ|` (times eight). -/
def mA : ℕ := L.F + L.lq + 5

/-- The bits of the scalar factor `64 c_t d |μ|`. -/
def mS : ℕ := L.kq + L.F + L.lq + 9

end Lay

/-- The input wires of the arithmetic in a base register `B`. -/
structure Inp (B : Type) (L : Lay) where
  ini : B
  u : Fin L.kq → B
  wd : Fin L.lq → B
  pt : B
  tg : B
  x1 : Fin L.b → B
  y1 : Fin L.b → B
  x2 : Fin L.b → B
  y2 : Fin L.b → B

/-! ### The computed integers -/

/-- The indicator of a nonzero Gaussian integer. -/
def chi (X Y : ℤ) : ℤ := if X = 0 ∧ Y = 0 then 0 else 1

namespace Inp

variable {B : Type} {L : Lay} (I : Inp B L) (x : B → Bool)

/-- The stored components. -/
def X1 : ℤ := twos I.x1 x
def Y1 : ℤ := twos I.y1 x
def X2 : ℤ := twos I.x2 x
def Y2 : ℤ := twos I.y2 x

/-- The node word and the LCHS word. -/
def U : ℕ := wordValue (fun j => x (I.u j))
def V : ℕ := wordValue (fun j => x (I.wd j))

/-- The tag split `c_t = χ₁ (2 - χ₂)`. -/
def ct : ℤ := chi (I.X1 x) (I.Y1 x) * (2 - chi (I.X2 x) (I.Y2 x))

/-- The duration numerator. -/
def dv : ℤ := if x I.ini then (I.U x : ℤ) else 2 ^ L.kq

/-- The LCHS node index. -/
def nv : ℤ := if I.V x < L.J then (I.V x : ℤ) - L.K else 0

/-- The part multiplier. -/
def mu : ℤ := if x I.pt then I.nv x * L.Hn else 2 ^ L.F

/-- The two components of the combination of the stored entries. -/
def ax : ℤ := if x I.pt then I.X1 x + I.X2 x else I.Y1 x + I.Y2 x
def ay : ℤ :=
  (if x I.pt then I.Y1 x - I.Y2 x else I.X2 x - I.X1 x) * (if x I.tg then -1 else 1)

/-- The computed Gaussian integer `Z' = zx + i zy`. -/
def zx : ℤ := 256 * (I.ct x * (I.dv x * (I.mu x * I.ax x)))
def zy : ℤ := 256 * (I.ct x * (I.dv x * (I.mu x * I.ay x)))

end Inp

/-! ### Registers and wires -/

/-- The registers of the program: single registers and five multiplication chains. -/
inductive RO (L : Lay) where
  | ax1 | n1 | z1 | ax2 | n2 | z2 | q0 | q1 | du | de | dd | nw | rg | nn
  | hx | hy | lx | ly | sx | ex | ax | sy | ey | ay | ayt
  | hc (j : Fin (L.F + 2))
  | md | me | mu | am | axs | ays
  | cc (j : Fin 3)
  | ec (j : Fin (L.mA + 1))
  | xc (j : Fin (L.mS + 1))
  | yc (j : Fin (L.mS + 1))
  deriving DecidableEq, Fintype

/-- The levels: the order in which the registers are written. -/
def lvO (L : Lay) : RO L → ℕ
  | .ax1 => 0 | .n1 => 1 | .z1 => 2 | .ax2 => 3 | .n2 => 4 | .z2 => 5 | .q0 => 6 | .q1 => 7
  | .du => 8 | .de => 9 | .dd => 10 | .nw => 11 | .rg => 12 | .nn => 13 | .hx => 14
  | .hy => 15 | .lx => 16 | .ly => 17 | .sx => 18 | .ex => 19 | .ax => 20 | .sy => 21
  | .ey => 22 | .ay => 23 | .ayt => 24
  | .hc j => 25 + j.val
  | .md => L.F + 27 | .me => L.F + 28 | .mu => L.F + 29 | .am => L.F + 30 | .axs => L.F + 31
  | .ays => L.F + 32
  | .cc j => L.F + 33 + j.val
  | .ec j => L.F + 36 + j.val
  | .xc j => L.F + L.mA + 37 + j.val
  | .yc j => L.F + L.mA + L.mS + 38 + j.val

/-- The wires of the program. -/
abbrev PW (B : Type) (L : Lay) := B ⊕ CW (RO L) L.w

section Wires

variable {B : Type} {L : Lay}

/-- The zero wire everywhere. -/
def zA : ℕ → PW B L := fun _ => .inr .zero

/-- A register. -/
def rA (r : RO L) : ℕ → PW B L := regW r

/-- A register shifted left by `j`. -/
def shA (r : RO L) (j : ℕ) : ℕ → PW B L :=
  fun i => if i < j then .inr .zero else regW r (i - j)

/-- A signed input component, sign-extended. -/
def inA (r : Fin L.b → B) : ℕ → PW B L :=
  fun i => if h : 0 < L.b then .inl (r ⟨min i (L.b - 1), by omega⟩) else .inr .zero

/-- An unsigned input word, extended by zeros. -/
def uA {m : ℕ} (r : Fin m → B) : ℕ → PW B L :=
  fun i => if h : i < m then .inl (r ⟨i, h⟩) else .inr .zero

/-- A single bit at position `0`. -/
def b0A (u : PW B L) : ℕ → PW B L := fun i => if i = 0 then u else .inr .zero

/-- The sign bit of a register. -/
def msbO (r : RO L) : PW B L := regW r (L.w - 1)

/-- A register as an operand. -/
def rB (r : RO L) : ℕ → BSrc (PW B L) := fun i => .lit (regW r i) true

/-- A register shifted left by `j`, as an operand. -/
def shB (r : RO L) (j : ℕ) : ℕ → BSrc (PW B L) :=
  fun i => if i < j then .const false else .lit (regW r (i - j)) true

/-- A signed input component, as an operand. -/
def inB (r : Fin L.b → B) : ℕ → BSrc (PW B L) := fun i => .lit (inA r i) true

/-- A constant operand. -/
def cB (c : ℕ) : ℕ → BSrc (PW B L) := fun i => .const ((BitVec.ofNat L.w c).getLsbD i)

/-- A single source bit at position `0`, as an operand. -/
def b0B (src : BSrc (PW B L)) : ℕ → BSrc (PW B L) :=
  fun i => if i = 0 then src else .const false

/-- The sign bit of an input component, as a sign source. -/
def inMsb (r : Fin L.b → B) (pol : Bool) : BSrc (PW B L) := .lit (inA r (L.b - 1)) pol

/-- The negated bit source. -/
def negS : BSrc (PW B L) → BSrc (PW B L)
  | .lit u p => .lit u (!p)
  | .const c => .const (!c)

end Wires

/-! ### The program -/

section Ops

variable {B : Type} {L : Lay}

/-- **The multiplication chain** for an `m`-bit multiplier with digits `dg`:
`acc 0 := (v << m) - v`, `acc (j + 1) := acc j ± (v << j)`, minus when the digit is clear, so that
`acc m = 2 M v`. -/
def chain {m : ℕ} (acc : Fin (m + 1) → RO L) (v : RO L) (dg : ℕ → BSrc (PW B L)) :
    List (ROp B (RO L) L.w) :=
  ⟨acc 0, shA v m, rB v, .const true⟩ ::
    (List.finRange m).map (fun j : Fin m =>
      ⟨acc j.succ, rA (acc j.castSucc), shB v j.val, negS (dg j.val)⟩)

/-- The first block: zero tests, the tag split, the duration, the node and the components. -/
def opsA (I : Inp B L) : List (ROp B (RO L) L.w) :=
  [⟨.ax1, zA, inB I.x1, inMsb I.x1 true⟩,
   ⟨.n1, rA .ax1, inB I.y1, inMsb I.y1 true⟩,
   ⟨.z1, zA, rB .n1, .const true⟩,
   ⟨.ax2, zA, inB I.x2, inMsb I.x2 true⟩,
   ⟨.n2, rA .ax2, inB I.y2, inMsb I.y2 true⟩,
   ⟨.z2, zA, rB .n2, .const true⟩,
   ⟨.q0, b0A (msbO .z1), b0B (.lit (msbO .z2) true), .const false⟩,
   ⟨.q1, b0A (msbO .z1), b0B (.lit (msbO .z2) false), .const false⟩,
   ⟨.du, uA I.u, cB (2 ^ L.kq), .const true⟩,
   ⟨.de, rA .du, rB .du, .lit (.inl I.ini) false⟩,
   ⟨.dd, rA .de, cB (2 ^ (L.kq + 1)), .const false⟩,
   ⟨.nw, uA I.wd, cB L.K, .const true⟩,
   ⟨.rg, uA I.wd, cB L.J, .const true⟩,
   ⟨.nn, rA .nw, rB .nw, .lit (msbO .rg) false⟩,
   ⟨.hx, inA I.y1, inB I.y2, .const false⟩,
   ⟨.hy, inA I.x2, inB I.x1, .const true⟩,
   ⟨.lx, inA I.x1, inB I.x2, .const false⟩,
   ⟨.ly, inA I.y1, inB I.y2, .const true⟩,
   ⟨.sx, rA .lx, rB .hx, .const true⟩,
   ⟨.ex, rA .sx, rB .sx, .lit (.inl I.pt) false⟩,
   ⟨.ax, shA .hx 1, rB .ex, .const false⟩,
   ⟨.sy, rA .ly, rB .hy, .const true⟩,
   ⟨.ey, rA .sy, rB .sy, .lit (.inl I.pt) false⟩,
   ⟨.ay, shA .hy 1, rB .ey, .const false⟩,
   ⟨.ayt, zA, rB .ay, .lit (.inl I.tg) true⟩]

/-- The node multiplier chain: `2 Hn n_n`. -/
def chainB : List (ROp B (RO L) L.w) :=
  chain (m := L.F + 1) RO.hc .nn (fun j => .const (L.Hn.testBit j))

/-- The second block: the part multiplier and the signs. -/
def opsC (I : Inp B L) : List (ROp B (RO L) L.w) :=
  [⟨.md, rA (.hc (Fin.last _)), cB (2 ^ (L.F + 2)), .const true⟩,
   ⟨.me, rA .md, rB .md, .lit (.inl I.pt) false⟩,
   ⟨.mu, rA .me, cB (2 ^ (L.F + 3)), .const false⟩,
   ⟨.am, zA, rB .mu, .lit (msbO .mu) true⟩,
   ⟨.axs, zA, rB .ax, .lit (msbO .mu) true⟩,
   ⟨.ays, zA, rB .ayt, .lit (msbO .mu) true⟩]

/-- The tag-split chain: `2 c_t d₂`. -/
def chainD : List (ROp B (RO L) L.w) :=
  chain (m := 2) RO.cc .dd (fun j => if j = 0 then .lit (regW .q0 1) true else
    .lit (regW .q1 1) true)

/-- The multiplier chain: `2 |μ₈| s₁`. -/
def chainE : List (ROp B (RO L) L.w) :=
  chain (m := L.mA) RO.ec (.cc (Fin.last 2)) (fun j => .lit (regW .am j) true)

/-- The real component chain. -/
def chainF : List (ROp B (RO L) L.w) :=
  chain (m := L.mS) RO.xc .axs (fun j => .lit (regW (.ec (Fin.last _)) j) true)

/-- The imaginary component chain. -/
def chainG : List (ROp B (RO L) L.w) :=
  chain (m := L.mS) RO.yc .ays (fun j => .lit (regW (.ec (Fin.last _)) j) true)

/-- **The pre-processing program.** -/
def prog (I : Inp B L) : List (ROp B (RO L) L.w) :=
  opsA I ++ chainB ++ opsC I ++ chainD ++ chainE ++ chainF ++ chainG

end Ops

/-! ### Single assignment -/

/-- Close an inequality between register levels. -/
local macro "gbo_lv" : tactic =>
  `(tactic| first
    | (simp only [lvO, Lay.mA, Lay.mS]; omega)
    | (simp [lvO, Lay.mA, Lay.mS]; omega)
    | simp [lvO, Lay.mA, Lay.mS])

section OK

variable {B : Type} {L : Lay}

theorem readable_regW' {P : RO L → Prop} {r : RO L} (h : P r) (i : ℕ) :
    Readable P (regW r i : PW B L) := by
  unfold regW
  split_ifs
  · exact h
  · trivial

theorem readable_zA (P : RO L → Prop) (i : ℕ) : Readable P (zA i : PW B L) := trivial

theorem readable_rA {P : RO L → Prop} {r : RO L} (h : P r) (i : ℕ) :
    Readable P (rA r i : PW B L) := readable_regW' h i

theorem readable_shA {P : RO L → Prop} {r : RO L} (h : P r) (j i : ℕ) :
    Readable P (shA r j i : PW B L) := by
  unfold shA
  split_ifs
  · trivial
  · exact readable_regW' h _

theorem readable_inA (P : RO L → Prop) (r : Fin L.b → B) (i : ℕ) :
    Readable P (inA r i : PW B L) := by
  unfold inA
  split_ifs <;> trivial

theorem readable_uA (P : RO L → Prop) {m : ℕ} (r : Fin m → B) (i : ℕ) :
    Readable P (uA r i : PW B L) := by
  unfold uA
  split_ifs <;> trivial

theorem on_rB {P : RO L → Prop} {r : RO L} (h : P r) (i : ℕ) :
    (rB r i : BSrc (PW B L)).On (Readable P) := readable_regW' h i

theorem on_shB {P : RO L → Prop} {r : RO L} (h : P r) (j i : ℕ) :
    (shB r j i : BSrc (PW B L)).On (Readable P) := by
  unfold shB
  split_ifs
  · trivial
  · exact readable_regW' h _

theorem on_inB (P : RO L → Prop) (r : Fin L.b → B) (i : ℕ) :
    (inB r i : BSrc (PW B L)).On (Readable P) := readable_inA P r i

theorem on_cB (P : RO L → Prop) (c i : ℕ) : (cB c i : BSrc (PW B L)).On (Readable P) := trivial

theorem on_msbO {P : RO L → Prop} {r : RO L} (h : P r) (pol : Bool) :
    (BSrc.lit (msbO r) pol : BSrc (PW B L)).On (Readable P) := readable_regW' h _

theorem on_negS (P : PW B L → Prop) (s : BSrc (PW B L)) (h : s.On P) : (negS s).On P := by
  cases s <;> exact h

/-- The levels of a chain. -/
theorem chain_ok {m : ℕ} (acc : Fin (m + 1) → RO L) (v : RO L) (dg : ℕ → BSrc (PW B L))
    (base : ℕ) (hacc : ∀ j, lvO L (acc j) = base + j.val) (hv : lvO L v < base)
    (hdg : ∀ j, j < m → (dg j).On (Readable (fun r => lvO L r < base))) :
    (chain acc v dg).Pairwise (fun o o' => lvO L o.dst < lvO L o'.dst) ∧
      ∀ o ∈ chain acc v dg, o.OK (fun r => lvO L r < lvO L o.dst) ∧
        base ≤ lvO L o.dst ∧ lvO L o.dst ≤ base + m := by
  have hmono : ∀ {Q Q' : RO L → Prop}, (∀ r, Q r → Q' r) → ∀ u : PW B L,
      Readable Q u → Readable Q' u := by
    intro Q Q' h u hu
    rcases u with b | (_ | i | i | ⟨r, i⟩)
    · trivial
    · trivial
    · exact hu
    · exact hu
    · exact h r hu
  refine ⟨?_, ?_⟩
  · unfold chain
    rw [List.pairwise_cons]
    refine ⟨?_, ?_⟩
    · intro o ho
      simp only [List.mem_map, List.mem_finRange, true_and] at ho
      obtain ⟨j, rfl⟩ := ho
      simp only [hacc, Fin.val_succ, Fin.val_zero]
      omega
    · rw [List.pairwise_map]
      refine List.Pairwise.imp ?_ (List.pairwise_lt_finRange m)
      intro j j' hjj'
      simp only [hacc, Fin.val_succ]
      have : j.val < j'.val := hjj'
      omega
  · intro o ho
    unfold chain at ho
    rcases List.mem_cons.1 ho with rfl | ho
    · refine ⟨⟨lt_irrefl _, fun i _ => readable_shA (by simp only [hacc]; omega) m i,
        fun i _ => on_rB (by simp only [hacc]; omega) i, trivial⟩, ?_, ?_⟩
      · simp only [hacc, Fin.val_zero]
        omega
      · simp only [hacc, Fin.val_zero]
        omega
    · simp only [List.mem_map, List.mem_finRange, true_and] at ho
      obtain ⟨j, rfl⟩ := ho
      have h1 : lvO L (acc j.castSucc) < lvO L (acc j.succ) := by
        rw [hacc, hacc, Fin.val_succ, Fin.val_castSucc]
        omega
      have h2 : lvO L v < lvO L (acc j.succ) := by
        rw [hacc, Fin.val_succ]
        omega
      have h3 : ∀ r, lvO L r < base → lvO L r < lvO L (acc j.succ) := by
        intro r hr
        rw [hacc, Fin.val_succ]
        omega
      refine ⟨⟨lt_irrefl _, fun i _ => readable_rA h1 i, fun i _ => on_shB h2 j i,
        on_negS _ _ (BSrc.On.mono (hdg j j.isLt) (fun u hu => hmono h3 u hu))⟩, ?_, ?_⟩
      · rw [hacc, Fin.val_succ]
        omega
      · rw [hacc, Fin.val_succ]
        omega

theorem lvO_hc (j : Fin (L.F + 2)) : lvO L (RO.hc j) = 25 + j.val := rfl
theorem lvO_cc (j : Fin 3) : lvO L (RO.cc j) = L.F + 33 + j.val := rfl
theorem lvO_ec (j : Fin (L.mA + 1)) : lvO L (RO.ec j) = L.F + 36 + j.val := rfl
theorem lvO_xc (j : Fin (L.mS + 1)) : lvO L (RO.xc j) = L.F + L.mA + 37 + j.val := rfl
theorem lvO_yc (j : Fin (L.mS + 1)) : lvO L (RO.yc j) = L.F + L.mA + L.mS + 38 + j.val := rfl

theorem chainB_ok : (chainB (B := B) (L := L)).Pairwise (fun o o' => lvO L o.dst < lvO L o'.dst) ∧
    ∀ o ∈ chainB (B := B) (L := L), o.OK (fun r => lvO L r < lvO L o.dst) ∧
      25 ≤ lvO L o.dst ∧ lvO L o.dst ≤ 25 + (L.F + 1) :=
  chain_ok _ _ _ 25 lvO_hc (by gbo_lv) (fun _ _ => trivial)

theorem chainD_ok : (chainD (B := B) (L := L)).Pairwise (fun o o' => lvO L o.dst < lvO L o'.dst) ∧
    ∀ o ∈ chainD (B := B) (L := L), o.OK (fun r => lvO L r < lvO L o.dst) ∧
      L.F + 33 ≤ lvO L o.dst ∧ lvO L o.dst ≤ L.F + 33 + 2 := by
  refine chain_ok _ _ _ (L.F + 33) lvO_cc (by gbo_lv) (fun j _ => ?_)
  split_ifs
  · exact readable_regW' (B := B) (P := fun r => lvO L r < L.F + 33) (r := RO.q0) (by gbo_lv) 1
  · exact readable_regW' (B := B) (P := fun r => lvO L r < L.F + 33) (r := RO.q1) (by gbo_lv) 1

theorem chainE_ok : (chainE (B := B) (L := L)).Pairwise (fun o o' => lvO L o.dst < lvO L o'.dst) ∧
    ∀ o ∈ chainE (B := B) (L := L), o.OK (fun r => lvO L r < lvO L o.dst) ∧
      L.F + 36 ≤ lvO L o.dst ∧ lvO L o.dst ≤ L.F + 36 + L.mA :=
  chain_ok _ _ _ (L.F + 36) lvO_ec (by gbo_lv) (fun j _ => readable_regW' (by gbo_lv) j)

theorem chainF_ok : (chainF (B := B) (L := L)).Pairwise (fun o o' => lvO L o.dst < lvO L o'.dst) ∧
    ∀ o ∈ chainF (B := B) (L := L), o.OK (fun r => lvO L r < lvO L o.dst) ∧
      L.F + L.mA + 37 ≤ lvO L o.dst ∧ lvO L o.dst ≤ L.F + L.mA + 37 + L.mS :=
  chain_ok _ _ _ (L.F + L.mA + 37) lvO_xc (by gbo_lv) (fun j _ => readable_regW' (by gbo_lv) j)

theorem chainG_ok : (chainG (B := B) (L := L)).Pairwise (fun o o' => lvO L o.dst < lvO L o'.dst) ∧
    ∀ o ∈ chainG (B := B) (L := L), o.OK (fun r => lvO L r < lvO L o.dst) ∧
      L.F + L.mA + L.mS + 38 ≤ lvO L o.dst ∧ lvO L o.dst ≤ L.F + L.mA + L.mS + 38 + L.mS :=
  chain_ok _ _ _ (L.F + L.mA + L.mS + 38) lvO_yc (by gbo_lv)
    (fun j _ => readable_regW' (by gbo_lv) j)

theorem opsA_dsts (I : Inp B L) :
    (opsA I).map (fun o => lvO L o.dst) = List.range 25 := by
  rfl

theorem opsA_ok (I : Inp B L) :
    (opsA I).Pairwise (fun o o' => lvO L o.dst < lvO L o'.dst) ∧
      ∀ o ∈ opsA I, o.OK (fun r => lvO L r < lvO L o.dst) ∧ lvO L o.dst < 25 := by
  refine ⟨?_, ?_⟩
  · rw [← List.pairwise_map (R := fun a b : ℕ => a < b), opsA_dsts]
    exact List.pairwise_lt_range
  · intro o ho
    simp only [opsA, List.mem_cons, List.not_mem_nil, or_false] at ho
    have hb0 : ∀ (u : PW B L) (P : RO L → Prop), Readable P u →
        ∀ i, Readable P (b0A u i : PW B L) := by
      intro u P hu i
      unfold b0A
      split_ifs
      · exact hu
      · trivial
    have hb0B : ∀ (src : BSrc (PW B L)) (P : RO L → Prop), src.On (Readable P) →
        ∀ i, (b0B src i).On (Readable P) := by
      intro src P hs i
      unfold b0B
      split_ifs
      · exact hs
      · trivial
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals refine ⟨⟨lt_irrefl _, fun i _ => ?_, fun i _ => ?_, ?_⟩, by gbo_lv⟩
    all_goals first
      | exact readable_zA _ i
      | (apply readable_rA; gbo_lv)
      | (apply readable_shA; gbo_lv)
      | exact readable_inA _ _ i
      | exact readable_uA _ _ i
      | (apply hb0; apply readable_regW'; gbo_lv)
      | exact on_inB _ _ i
      | exact on_cB _ _ i
      | (apply hb0B; apply on_msbO; gbo_lv)
      | exact readable_inA _ _ _
      | trivial

theorem opsC_ok (I : Inp B L) :
    (opsC I).Pairwise (fun o o' => lvO L o.dst < lvO L o'.dst) ∧
      ∀ o ∈ opsC I, o.OK (fun r => lvO L r < lvO L o.dst) ∧
        L.F + 27 ≤ lvO L o.dst ∧ lvO L o.dst ≤ L.F + 32 := by
  refine ⟨?_, ?_⟩
  · simp only [opsC, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, IsEmpty.forall_iff, implies_true, and_true,
      lvO]
    omega
  · intro o ho
    simp only [opsC, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals refine ⟨⟨lt_irrefl _, fun i _ => ?_, fun i _ => ?_, ?_⟩, by gbo_lv, by gbo_lv⟩
    all_goals first
      | exact readable_zA _ i
      | (apply readable_rA; gbo_lv)
      | exact on_cB _ _ i
      | trivial

/-- **The pre-processing program is a single-assignment program.** -/
theorem progOK (I : Inp B L) : ProgOK (lvO L) (prog I) := by
  obtain ⟨hA1, hA2⟩ := opsA_ok I
  obtain ⟨hB1, hB2⟩ := chainB_ok (B := B) (L := L)
  obtain ⟨hC1, hC2⟩ := opsC_ok I
  obtain ⟨hD1, hD2⟩ := chainD_ok (B := B) (L := L)
  obtain ⟨hE1, hE2⟩ := chainE_ok (B := B) (L := L)
  obtain ⟨hF1, hF2⟩ := chainF_ok (B := B) (L := L)
  obtain ⟨hG1, hG2⟩ := chainG_ok (B := B) (L := L)
  have hmA : 0 < L.mA := by unfold Lay.mA; omega
  refine ⟨?_, ?_⟩
  · simp only [prog, List.pairwise_append]
    refine ⟨⟨⟨⟨⟨⟨hA1, hB1, ?_⟩, hC1, ?_⟩, hD1, ?_⟩, hE1, ?_⟩, hF1, ?_⟩, hG1, ?_⟩
    · intro o ho o' ho'
      have := (hA2 o ho).2
      have := (hB2 o' ho').2
      omega
    · intro o ho o' ho'
      have := (hC2 o' ho').2
      rcases List.mem_append.1 ho with ho | ho
      · have := (hA2 o ho).2
        omega
      · have := (hB2 o ho).2
        omega
    · intro o ho o' ho'
      have := (hD2 o' ho').2
      rcases List.mem_append.1 ho with ho | ho
      · rcases List.mem_append.1 ho with ho | ho
        · have := (hA2 o ho).2
          omega
        · have := (hB2 o ho).2
          omega
      · have := (hC2 o ho).2
        omega
    · intro o ho o' ho'
      have := (hE2 o' ho').2
      simp only [List.mem_append] at ho
      rcases ho with ((ho | ho) | ho) | ho
      · have := (hA2 o ho).2
        omega
      · have := (hB2 o ho).2
        omega
      · have := (hC2 o ho).2
        omega
      · have := (hD2 o ho).2
        omega
    · intro o ho o' ho'
      have := (hF2 o' ho').2
      simp only [List.mem_append] at ho
      rcases ho with (((ho | ho) | ho) | ho) | ho
      · have := (hA2 o ho).2
        omega
      · have := (hB2 o ho).2
        omega
      · have := (hC2 o ho).2
        omega
      · have := (hD2 o ho).2
        omega
      · have := (hE2 o ho).2
        omega
    · intro o ho o' ho'
      have := (hG2 o' ho').2
      simp only [List.mem_append] at ho
      rcases ho with ((((ho | ho) | ho) | ho) | ho) | ho
      · have := (hA2 o ho).2
        omega
      · have := (hB2 o ho).2
        omega
      · have := (hC2 o ho).2
        omega
      · have := (hD2 o ho).2
        omega
      · have := (hE2 o ho).2
        omega
      · have := (hF2 o ho).2
        omega
  · intro o ho
    simp only [prog, List.mem_append] at ho
    rcases ho with (((((ho | ho) | ho) | ho) | ho) | ho) | ho
    · exact (hA2 o ho).1
    · exact (hB2 o ho).1
    · exact (hC2 o ho).1
    · exact (hD2 o ho).1
    · exact (hE2 o ho).1
    · exact (hF2 o ho).1
    · exact (hG2 o ho).1

theorem length_prog (I : Inp B L) :
    (prog I).length = 31 + (L.F + 2) + 3 + (L.mA + 1) + 2 * (L.mS + 1) := by
  simp only [prog, chainB, chainD, chainE, chainF, chainG, chain, opsA, opsC, List.length_append,
    List.length_cons, List.length_map, List.length_finRange, List.length_nil]
  ring

end OK

end SparseHamiltonian.GateBinaryODE
