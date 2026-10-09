import SparseHamiltonian.NativeBandEncoding

set_option autoImplicit false

/-!
# The public entry bound of native sparse data (`odel:lem:dyson`, lines 4170-4176)

"Uniform row/column slot superpositions and a controlled entry rotation using the known bound
`|A_ij(t)| ≤ η` give normalisation `s η`. The actual maximum entry need not be known."

In the ODE lower-bound class the known bound is the row/column norm bound `η` of
`Family.InClass`, which bounds every entry; the native data carry their own public decoding bound
`D.scale`. The release's tail encoding `SparseHamiltonian.NativeBandEncoding.tail D η hη`
replaces the decoding bound by `η`: the decoder is clipped to `0` above `η` (a known gate), the
slots, table, locators and oracles are those of `D` (`NativeBandEncoding.tail_oracles`, by
definition), and the scale is `η` (by definition). When every entry is bounded by `η` the clip
removes nothing, so the decoded matrix is unchanged (`tail_matrix_of_le`).
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- **The known entry bound clips nothing**: if every entry is bounded by `η`, the release's tail
encoding at threshold `η` has the same matrix as `D` (and scale `η`, same oracles). -/
theorem tail_matrix_of_le (D : Data X n Z s) (η : ℝ) (hη : 0 < η)
    (h : ∀ x i j, ‖D.matrix x i j‖ ≤ η) :
    (NativeBandEncoding.tail D η hη).matrix = D.matrix := by
  funext x i j
  simp [NativeBandEncoding.tail, tailMatrix, magnitudeTail, h x i j]

end

end ODELowerBoundExtensions.Dyson
