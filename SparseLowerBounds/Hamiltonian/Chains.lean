import SparseLowerBounds.Helpers.Chains.Gauge

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Decorated chains and their parity amplitudes

Manuscript: the chain construction of Section `part:hsl` (eqs. `hsl:eq:dressed`, `hsl:eq:parityamp`)
and the signed scalar chain of Lemma `hsl:lem:precision`.

* **Search-decorated chain** on `ℂ^{n+1} ⊗ ℂ^m` (index `(clock, register)`):
  the `k`-th forward edge carries the gadget `U_{x^{(k+1)}}` of the `k`-th
  hidden one-hot string (`j k`), the reverse edge its adjoint (`searchChain`).
  With `V_0 = I`, `V_{k+1} = U_{j k} V_k` and the analysis-only gauge
  `G = Σ_k |k⟩⟨k| ⊗ V_k`, `G† H G = B ⊗ I_m` for the plain path `B` with the
  same weights. On the alternating vector `v` every `V_k` acts as a sign, so
  `⟨n, v| e^{-iτH} |0, v⟩ = σ(X) ⟨n| e^{-iτB} |0⟩` (`searchChain_amp`).
* **Signed scalar chain** on `ℂ^{n+1}`: edge `k` carries the sign
  `(-1)^{x_k}` of the `k`-th hidden bit (`scalarChain`); a diagonal sign gauge
  gives `⟨n| e^{-iτH} |0⟩ = σ(x) ⟨n| e^{-iτB} |0⟩` (`scalarChain_amp`).

Weights `c : ℕ → ℝ` are arbitrary here; the hard families use the rounded
weights of `Hamiltonian/Rounding`.
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace

variable {n m : ℕ}

/-- **Eq. `hsl:eq:dressed`**: the search-decorated chain with weights `c`;
entry `((k+1, a), (k, b))` is `c_k (U_{j k})_{ab}` and entry `((k, b), (k+1, a))`
is `c_k (U_{j k})_{ab}` as well (the gadget is real). -/
def searchChain (n m : ℕ) (c : ℕ → ℝ) (j : Fin n → Fin m) :
    Matrix (Fin (n + 1) × Fin m) (Fin (n + 1) × Fin m) ℂ :=
  Matrix.of fun p q =>
    if h : (p.1 : ℕ) = q.1 + 1 then
      (c q.1 : ℂ) * LinearSystems.gadget m (j ⟨q.1, by have := p.1.isLt; omega⟩) p.2 q.2
    else if h' : (q.1 : ℕ) = p.1 + 1 then
      (c p.1 : ℂ) * LinearSystems.gadget m (j ⟨p.1, by have := q.1.isLt; omega⟩) q.2 p.2
    else 0

/-- The sign `(-1)^b` of a bit. -/
def bitSign (b : Bool) : ℂ := if b then -1 else 1

/-- The signed scalar chain of Lemma `hsl:lem:precision`:
edge `k` carries `c_k (-1)^{x_k}`. -/
def scalarChain (n : ℕ) (c : ℕ → ℝ) (x : Fin n → Bool) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun i j =>
    if h : (i : ℕ) = j + 1 then (c j : ℂ) * bitSign (x ⟨j, by have := i.isLt; omega⟩)
    else if h' : (j : ℕ) = i + 1 then (c i : ℂ) * bitSign (x ⟨i, by have := j.isLt; omega⟩)
    else 0

/-- `|k⟩ ⊗ v` with the alternating vector `v` on the register. -/
def chainVec (n m : ℕ) (k : Fin (n + 1)) : EuclideanSpace ℂ (Fin (n + 1) × Fin m) :=
  WithLp.toLp 2 fun p => if p.1 = k then alt m p.2 else 0

/-! ### Symmetry and reality of the chains (Theorem `hsl:thm:main`) -/

/-- The decorated chain is symmetric (both edge directions carry `c_k U_{ab}`). -/
theorem searchChain_transpose (n m : ℕ) (c : ℕ → ℝ) (j : Fin n → Fin m) :
    (searchChain n m c j)ᵀ = searchChain n m c j := by
  ext p q
  simp only [Matrix.transpose_apply, searchChain, Matrix.of_apply]
  split_ifs <;> first | rfl | omega

/-- The decorated chain is real (`LinearSystems.star_gadget_apply`). -/
theorem star_searchChain_apply (c : ℕ → ℝ) (j : Fin n → Fin m) (p q : Fin (n + 1) × Fin m) :
    star (searchChain n m c j p q) = searchChain n m c j p q := by
  simp only [searchChain, Matrix.of_apply]
  split_ifs
  · rw [star_mul', LinearSystems.star_gadget_apply, Complex.star_def, Complex.conj_ofReal]
  · rw [star_mul', LinearSystems.star_gadget_apply, Complex.star_def, Complex.conj_ofReal]
  · exact star_zero _

theorem scalarChain_transpose (n : ℕ) (c : ℕ → ℝ) (x : Fin n → Bool) :
    (scalarChain n c x)ᵀ = scalarChain n c x := by
  ext p q
  simp only [Matrix.transpose_apply, scalarChain, Matrix.of_apply]
  split_ifs <;> first | rfl | omega

namespace Chains

/-- `(-1)^b` is real (used before `star_bitSign` is stated). -/
theorem star_bitSign' (b : Bool) : star (bitSign b) = bitSign b := by
  cases b <;> simp [bitSign]

end Chains

theorem star_scalarChain_apply (c : ℕ → ℝ) (x : Fin n → Bool) (i i' : Fin (n + 1)) :
    star (scalarChain n c x i i') = scalarChain n c x i i' := by
  simp only [scalarChain, Matrix.of_apply]
  split_ifs
  · rw [star_mul', Chains.star_bitSign', Complex.star_def, Complex.conj_ofReal]
  · rw [star_mul', Chains.star_bitSign', Complex.star_def, Complex.conj_ofReal]
  · exact star_zero _

/-- `|k, v⟩` is a unit vector for `m > 0` (`norm_alt`). -/
theorem norm_chainVec (hm0 : 0 < m) (k : Fin (n + 1)) : ‖chainVec n m k‖ = 1 := by
  exact Helpers.Chains.norm_cvec hm0 k

theorem isHermitian_searchChain (n m : ℕ) (c : ℕ → ℝ) (j : Fin n → Fin m) :
    (searchChain n m c j).IsHermitian := by
  refine Matrix.IsHermitian.ext fun p q => ?_
  rw [star_searchChain_apply]
  exact congrFun (congrFun (searchChain_transpose n m c j) p) q

theorem isHermitian_scalarChain (n : ℕ) (c : ℕ → ℝ) (x : Fin n → Bool) :
    (scalarChain n c x).IsHermitian := by
  refine Matrix.IsHermitian.ext fun p q => ?_
  rw [star_scalarChain_apply]
  exact congrFun (congrFun (scalarChain_transpose n c x) p) q

/-! ### Unitary similarity and `B ⊗ I` -/

section Conj

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Evolution under a unitary similarity: `e^{-iτ U K U†} = U e^{-iτK} U†`
(`NormedSpace.exp` commutes with the star-algebra equivalence
`matrixOperator_eq_toEuclideanCLM` and with unit conjugation). -/
theorem evolve_unitary_conj {U : Matrix S S ℂ} (hU : U ∈ Matrix.unitaryGroup S ℂ)
    (K : Matrix S S ℂ) (τ : ℝ) :
    evolve (U * K * Uᴴ) τ =
      SparseHamiltonian.SparseStateOverlap.matrixOperator U ∘L evolve K τ ∘L
        SparseHamiltonian.SparseStateOverlap.matrixOperator Uᴴ := by
  exact Helpers.Chains.evolve_unitary_conj hU K τ

/-- The `L²` operator norm is unitarily invariant. -/
theorem norm_unitary_conj {U : Matrix S S ℂ} (hU : U ∈ Matrix.unitaryGroup S ℂ)
    (K : Matrix S S ℂ) : ‖U * K * Uᴴ‖ = ‖K‖ := by
  exact Helpers.Chains.norm_unitary_conj hU K

/-- `‖B ⊗ I_m‖ = ‖B‖` for `m > 0`. -/
theorem norm_kronecker_one (hm0 : 0 < m) (B : Matrix S S ℂ) :
    ‖Matrix.kronecker B (1 : Matrix (Fin m) (Fin m) ℂ)‖ = ‖B‖ := by
  exact Helpers.Chains.norm_kronecker_one hm0 B

/-- `e^{-iτ(B ⊗ I)} = e^{-iτB} ⊗ I`, read on vectors: component `(k, a)` sees
only the register slice `a`. -/
theorem evolve_kronecker_one_apply (B : Matrix S S ℂ) (τ : ℝ)
    (v : EuclideanSpace ℂ (S × Fin m)) (p : S × Fin m) :
    evolve (Matrix.kronecker B (1 : Matrix (Fin m) (Fin m) ℂ)) τ v p =
      evolve B τ (WithLp.toLp 2 fun i => v (i, p.2)) p.1 := by
  exact Helpers.Chains.evolve_kronecker_one_apply B τ v p

end Conj

/-- The ungauged amplitude: `⟨k, v| e^{-iτ(B ⊗ I)} |k', v⟩ = ⟨k| e^{-iτB} |k'⟩`
for `m > 0` (`‖v‖ = 1`). -/
theorem inner_chainVec_evolve_kronecker (hm0 : 0 < m) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (τ : ℝ) (k k' : Fin (n + 1)) :
    ⟪chainVec n m k, evolve (Matrix.kronecker B (1 : Matrix (Fin m) (Fin m) ℂ)) τ
        (chainVec n m k')⟫_ℂ =
      evolve B τ (EuclideanSpace.single k' 1) k := by
  exact Helpers.Chains.inner_cvec_evolve_kronecker hm0 B τ k k'

/-! ### The search gauge `G = Σ_k |k⟩⟨k| ⊗ V_k` (the chain construction of Section `part:hsl`) -/

/-- The register blocks `V_0 = I`, `V_{k+1} = U_{j k} V_k` of the gauge
(the chain construction of Section `part:hsl`); constant after `k = n`. -/
def gaugeBlock (n m : ℕ) (j : Fin n → Fin m) : ℕ → Matrix (Fin m) (Fin m) ℂ
  | 0 => 1
  | k + 1 =>
    if h : k < n then LinearSystems.gadget m (j ⟨k, h⟩) * gaugeBlock n m j k
    else gaugeBlock n m j k

/-- The sign `∏_{i<k} (-1)^{j i}` by which `V_k` acts on `v`. -/
def gaugeSign (j : Fin n → Fin m) (k : ℕ) : ℂ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), (-1 : ℂ) ^ (j i : ℕ)

/-- The analysis-only gauge `G = Σ_k |k⟩⟨k| ⊗ V_k` (the chain construction of Section
`part:hsl`). -/
def searchGauge (n m : ℕ) (j : Fin n → Fin m) :
    Matrix (Fin (n + 1) × Fin m) (Fin (n + 1) × Fin m) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then gaugeBlock n m j p.1 p.2 q.2 else 0

namespace Chains

/-- `V_0 = I`. -/
theorem gaugeBlock_zero (j : Fin n → Fin m) : gaugeBlock n m j 0 = 1 := by
  rw [gaugeBlock]

/-- `V_{k+1} = U_{j k} V_k` for `k < n`. -/
theorem gaugeBlock_succ_of_lt (j : Fin n → Fin m) {k : ℕ} (hk : k < n) :
    gaugeBlock n m j (k + 1) = LinearSystems.gadget m (j ⟨k, hk⟩) * gaugeBlock n m j k := by
  rw [gaugeBlock, dif_pos hk]

/-- `V_{k+1} = V_k` after the last edge. -/
theorem gaugeBlock_succ_of_le (j : Fin n → Fin m) {k : ℕ} (hk : n ≤ k) :
    gaugeBlock n m j (k + 1) = gaugeBlock n m j k := by
  rw [gaugeBlock, dif_neg (by omega)]

/-- The gauge sign picks up `(-1)^{j k}` across edge `k`. -/
theorem gaugeSign_succ (j : Fin n → Fin m) {k : ℕ} (hk : k < n) :
    gaugeSign j (k + 1) = (-1 : ℂ) ^ (j ⟨k, hk⟩ : ℕ) * gaugeSign j k :=
  Helpers.Chains.prod_filter_lt_succ hk _

theorem gaugeSign_succ_of_le (j : Fin n → Fin m) {k : ℕ} (hk : n ≤ k) :
    gaugeSign j (k + 1) = gaugeSign j k := by
  unfold gaugeSign
  rw [Helpers.Chains.prod_filter_lt_of_le hk, Helpers.Chains.prod_filter_lt_of_le (by omega)]

end Chains

theorem gaugeBlock_mem_unitaryGroup (j : Fin n → Fin m) (k : ℕ) :
    gaugeBlock n m j k ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  induction k with
  | zero => rw [Chains.gaugeBlock_zero]; exact one_mem _
  | succ k ih =>
    by_cases hk : k < n
    · rw [Chains.gaugeBlock_succ_of_lt j hk]
      exact mul_mem (LinearSystems.gadget_mem_unitaryGroup _) ih
    · rw [Chains.gaugeBlock_succ_of_le j (by omega)]
      exact ih

theorem gaugeSign_zero (j : Fin n → Fin m) : gaugeSign j 0 = 1 := by
  exact Helpers.Chains.prod_filter_lt_zero _

/-- After the last edge the gauge sign is the hidden parity `σ(X)`. -/
theorem gaugeSign_of_le (j : Fin n → Fin m) {k : ℕ} (hk : n ≤ k) :
    gaugeSign j k = (parity j : ℂ) := by
  unfold gaugeSign
  rw [Helpers.Chains.prod_filter_lt_of_le hk, parity_eq_prod]
  push_cast
  rfl

/-- The gauge signs are real `±1`. -/
theorem star_gaugeSign (j : Fin n → Fin m) (k : ℕ) : star (gaugeSign j k) = gaugeSign j k := by
  unfold gaugeSign
  rw [← starRingEnd_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

theorem gaugeSign_mul_self (j : Fin n → Fin m) (k : ℕ) : gaugeSign j k * gaugeSign j k = 1 := by
  unfold gaugeSign
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

/-- `V_k v = (∏_{i<k} (-1)^{j i}) v` for even `m` (`gadget_mulVec_alt`). -/
theorem gaugeBlock_mulVec_alt (hm : Even m) (j : Fin n → Fin m) (k : ℕ) :
    gaugeBlock n m j k *ᵥ alt m = gaugeSign j k • alt m := by
  induction k with
  | zero => rw [Chains.gaugeBlock_zero, Matrix.one_mulVec, gaugeSign_zero, one_smul]
  | succ k ih =>
    by_cases hk : k < n
    · rw [Chains.gaugeBlock_succ_of_lt j hk, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul,
        gadget_mulVec_alt hm, smul_smul, Chains.gaugeSign_succ j hk, mul_comm]
    · rw [Chains.gaugeBlock_succ_of_le j (by omega), ih, Chains.gaugeSign_succ_of_le j (by omega)]

namespace Chains

/-- `V_k† V_k = I`. -/
theorem conjTranspose_gaugeBlock_mul (j : Fin n → Fin m) (k : ℕ) :
    (gaugeBlock n m j k)ᴴ * gaugeBlock n m j k = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff'.mp (gaugeBlock_mem_unitaryGroup j k)

/-- The decorated chain as a `clock × clock` block matrix. -/
theorem searchChain_eq_comp (c : ℕ → ℝ) (j : Fin n → Fin m) :
    searchChain n m c j = Matrix.comp _ _ _ _ ℂ (Helpers.Chains.searchBlocks n m c j) := by
  ext ⟨i, a⟩ ⟨k, b⟩
  simp only [searchChain, Helpers.Chains.searchBlocks, Matrix.of_apply, Matrix.comp_apply]
  split_ifs <;> rfl

end Chains

theorem searchGauge_mem_unitaryGroup (j : Fin n → Fin m) :
    searchGauge n m j ∈ Matrix.unitaryGroup (Fin (n + 1) × Fin m) ℂ := by
  rw [show searchGauge n m j = Helpers.Chains.blockDiag n m (gaugeBlock n m j) from rfl,
    Helpers.Chains.blockDiag_eq_comp]
  exact Helpers.Chains.comp_diagonal_mem_unitaryGroup _ fun i => gaugeBlock_mem_unitaryGroup j i

/-- **The gauge identity** `G† H_X G = B ⊗ I_m` (the chain construction of Section `part:hsl`):
`V_{k+1}† (c_k U_{j k}) V_k = c_k I`. -/
theorem searchGauge_conj (c : ℕ → ℝ) (j : Fin n → Fin m) :
    (searchGauge n m j)ᴴ * searchChain n m c j * searchGauge n m j =
      Matrix.kronecker (pathMatrix n c) (1 : Matrix (Fin m) (Fin m) ℂ) := by
  rw [show searchGauge n m j = Helpers.Chains.blockDiag n m (gaugeBlock n m j) from rfl,
    Helpers.Chains.blockDiag_eq_comp, Chains.searchChain_eq_comp,
    Helpers.Chains.conj_comp_diagonal, Helpers.Chains.kronecker_one_eq_comp]
  congr 1
  refine Matrix.ext fun i k => ?_
  rw [Matrix.of_apply, Matrix.of_apply]
  exact Helpers.Chains.gauge_block c j (gaugeBlock n m j)
    (fun k hk => Chains.gaugeBlock_succ_of_lt j hk) (Chains.conjTranspose_gaugeBlock_mul j) i k

/-- The gauge identity in the form `H_X = G (B ⊗ I) G†`. -/
theorem searchChain_eq_conj (c : ℕ → ℝ) (j : Fin n → Fin m) :
    searchChain n m c j =
      searchGauge n m j * Matrix.kronecker (pathMatrix n c) (1 : Matrix (Fin m) (Fin m) ℂ) *
        (searchGauge n m j)ᴴ := by
  have h1 : searchGauge n m j * (searchGauge n m j)ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp (searchGauge_mem_unitaryGroup j)
  calc searchChain n m c j
      = (searchGauge n m j * (searchGauge n m j)ᴴ) * searchChain n m c j *
          (searchGauge n m j * (searchGauge n m j)ᴴ) := by
        rw [h1, Matrix.one_mul, Matrix.mul_one]
    _ = searchGauge n m j * ((searchGauge n m j)ᴴ * searchChain n m c j * searchGauge n m j) *
          (searchGauge n m j)ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [searchGauge_conj]

/-- `G |k, v⟩ = (∏_{i<k} (-1)^{j i}) |k, v⟩` for even `m`. -/
theorem searchGauge_chainVec (hm : Even m) (j : Fin n → Fin m) (k : Fin (n + 1)) :
    SparseHamiltonian.SparseStateOverlap.matrixOperator (searchGauge n m j) (chainVec n m k) =
      gaugeSign j k • chainVec n m k := by
  exact Helpers.Chains.blockDiag_cvec _ _ (gaugeBlock_mulVec_alt hm j) k

/-- `G† |k, v⟩ = (∏_{i<k} (-1)^{j i}) |k, v⟩` for even `m` (real `±1` signs). -/
theorem conjTranspose_searchGauge_chainVec (hm : Even m) (j : Fin n → Fin m) (k : Fin (n + 1)) :
    SparseHamiltonian.SparseStateOverlap.matrixOperator (searchGauge n m j)ᴴ (chainVec n m k) =
      gaugeSign j k • chainVec n m k := by
  rw [show searchGauge n m j = Helpers.Chains.blockDiag n m (gaugeBlock n m j) from rfl,
    Helpers.Chains.conjTranspose_blockDiag]
  exact Helpers.Chains.blockDiag_cvec _ _
    (fun k => Helpers.Chains.conjTranspose_mulVec_of_mulVec
      (Chains.conjTranspose_gaugeBlock_mul j k) (gaugeSign_mul_self j k)
      (gaugeBlock_mulVec_alt hm j k)) k

/-! ### The diagonal sign gauge of the scalar chain (Lemma `hsl:lem:precision`) -/

theorem bitSign_mul_self (b : Bool) : bitSign b * bitSign b = 1 := by
  cases b <;> simp [bitSign]

theorem star_bitSign (b : Bool) : star (bitSign b) = bitSign b := by
  exact Chains.star_bitSign' b

/-- The gauge entry `d_k = ∏_{i<k} (-1)^{x_i}`. -/
def bitGaugeSign (x : Fin n → Bool) (k : ℕ) : ℂ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), bitSign (x i)

/-- The diagonal sign gauge `D = diag(d_0, …, d_n)`. -/
def signGauge (n : ℕ) (x : Fin n → Bool) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.diagonal fun k => bitGaugeSign x k

namespace Chains

/-- The sign-gauge entries square to one. -/
theorem bitGaugeSign_mul_self (x : Fin n → Bool) (k : ℕ) :
    bitGaugeSign x k * bitGaugeSign x k = 1 := by
  unfold bitGaugeSign
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => bitSign_mul_self _

end Chains

theorem bitGaugeSign_zero (x : Fin n → Bool) : bitGaugeSign x 0 = 1 := by
  exact Helpers.Chains.prod_filter_lt_zero _

/-- After the last edge the gauge entry is the bit parity `σ(x)`. -/
theorem bitGaugeSign_of_le (x : Fin n → Bool) {k : ℕ} (hk : n ≤ k) :
    bitGaugeSign x k = (BitDegree.bitParity x : ℂ) := by
  unfold bitGaugeSign
  rw [Helpers.Chains.prod_filter_lt_of_le hk, BitDegree.bitParity]
  simp only [bitSign]
  rw [Finset.prod_ite]
  simp

theorem signGauge_conjTranspose (x : Fin n → Bool) : (signGauge n x)ᴴ = signGauge n x := by
  rw [signGauge, Matrix.diagonal_conjTranspose]
  congr 1
  funext k
  unfold bitGaugeSign
  rw [Pi.star_apply, ← starRingEnd_apply, map_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [starRingEnd_apply, star_bitSign]

theorem signGauge_mem_unitaryGroup (x : Fin n → Bool) :
    signGauge n x ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, signGauge_conjTranspose, signGauge,
    Matrix.diagonal_mul_diagonal]
  have h : (fun k : Fin (n + 1) => bitGaugeSign x k * bitGaugeSign x k) = fun _ => 1 := by
    funext k
    exact Chains.bitGaugeSign_mul_self x k
  rw [h, Matrix.diagonal_one]

/-- **The sign gauge identity** `H_x = D B D†`: `d_{k+1} c_k d_k = c_k (-1)^{x_k}`. -/
theorem scalarChain_eq_conj (c : ℕ → ℝ) (x : Fin n → Bool) :
    scalarChain n c x = signGauge n x * pathMatrix n c * (signGauge n x)ᴴ := by
  rw [signGauge_conjTranspose]
  exact Helpers.Chains.signedPath_eq_conj c (fun i => bitSign (x i)) (bitGaugeSign x)
    (fun k hk => by unfold bitGaugeSign; exact Helpers.Chains.prod_filter_lt_succ hk _)
    (Chains.bitGaugeSign_mul_self x)

/-! ### Parity amplitudes -/

/-- **Eq. `hsl:eq:parityamp`** (the chain construction of Section `part:hsl`): for even `m > 0`,
`⟨n, v| e^{-iτ H_X} |0, v⟩ = σ(X) ⟨n| e^{-iτ B} |0⟩`. -/
theorem searchChain_amp (hm : Even m) (hm0 : 0 < m) (c : ℕ → ℝ) (j : Fin n → Fin m) (τ : ℝ) :
    ⟪chainVec n m (Fin.last n), evolve (searchChain n m c j) τ (chainVec n m 0)⟫_ℂ =
      (parity j : ℂ) * endAmp n c τ := by
  rw [searchChain_eq_conj, evolve_unitary_conj (searchGauge_mem_unitaryGroup j),
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    conjTranspose_searchGauge_chainVec hm j 0, ← ContinuousLinearMap.adjoint_inner_left,
    ← ContinuousLinearMap.star_eq_adjoint, ← Helpers.Chains.mO_conjTranspose,
    conjTranspose_searchGauge_chainVec hm j (Fin.last n), inner_smul_left, map_smul,
    inner_smul_right, inner_chainVec_evolve_kronecker hm0, Fin.val_last, Fin.val_zero,
    gaugeSign_zero, one_mul, starRingEnd_apply, star_gaugeSign, gaugeSign_of_le j le_rfl]
  rfl

/-- The scalar chain's endpoint amplitude is `σ(x) ⟨n| e^{-iτB} |0⟩` (Lemma `hsl:lem:precision`,
diagonal sign gauge). -/
theorem scalarChain_amp (c : ℕ → ℝ) (x : Fin n → Bool) (τ : ℝ) :
    evolve (scalarChain n c x) τ (EuclideanSpace.single 0 1) (Fin.last n) =
      (BitDegree.bitParity x : ℂ) * endAmp n c τ := by
  have h0 : (fun k : Fin (n + 1) => bitGaugeSign x k) 0 = 1 := by
    show bitGaugeSign x ((0 : Fin (n + 1)) : ℕ) = 1
    rw [Fin.val_zero, bitGaugeSign_zero]
  rw [scalarChain_eq_conj, evolve_unitary_conj (signGauge_mem_unitaryGroup x),
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, signGauge_conjTranspose,
    signGauge, Helpers.Chains.mO_diagonal_single (fun k : Fin (n + 1) => bitGaugeSign x k) 0 h0,
    Helpers.Chains.mO_diagonal_apply, Fin.val_last, bitGaugeSign_of_le x le_rfl]
  rfl

/-- The decorated chain has the norm of its plain path (common gauge, the chain construction of
Section `part:hsl`). -/
theorem norm_searchChain (hm0 : 0 < m) (c : ℕ → ℝ) (j : Fin n → Fin m) :
    ‖searchChain n m c j‖ = ‖pathMatrix n c‖ := by
  rw [searchChain_eq_conj, norm_unitary_conj (searchGauge_mem_unitaryGroup j),
    norm_kronecker_one hm0]

/-- The scalar chain has the norm of its plain path (sign gauge). -/
theorem norm_scalarChain (c : ℕ → ℝ) (x : Fin n → Bool) :
    ‖scalarChain n c x‖ = ‖pathMatrix n c‖ := by
  rw [scalarChain_eq_conj, norm_unitary_conj (signGauge_mem_unitaryGroup x)]

end

end SparseLowerBounds.Hamiltonian
end
