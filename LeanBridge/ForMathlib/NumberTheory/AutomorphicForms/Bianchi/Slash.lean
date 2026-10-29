import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.WeightTwo

/-!
# The weight `k` slash operator on hyperbolic 3-space

A Bianchi modular form of weight `k` is a function `F : ℋ₃ → ℂ^{k+1}`, and `γ ∈ SL(2, ℂ)` acts on
it by the weight `k` slash operator `(F ∣_k γ)(z) = Sym^k(J(γ, z)⁻¹) F(γ z)`, where
`J(γ, z) = (cx + d, -cy; c̄y, conj(cx + d))` for `γ = (a, b; c, d)` and `z = (x, y)`, and `Sym^k` is
the `k`-th symmetric power of the standard representation of `GL(2, ℂ)` on `ℂ²`.

## Main definitions

* `HyperbolicThreeSpace.symPowMatrix` (LMFDB `mf.bianchi`): the matrix `Sym^k(A)`.
* `HyperbolicThreeSpace.automorphyFactor` (LMFDB `mf.bianchi`): the matrix `J(γ, z)`.
* `HyperbolicThreeSpace.bianchiSlash` (LMFDB `mf.bianchi`): the weight `k` slash operator.
* `HyperbolicThreeSpace.extend`: a function on `ℋ₃`, extended by zero to `ℂ × ℝ`.

## Main results

* `HyperbolicThreeSpace.bianchiSlash_two`: in weight `2`, the slash operator is the one of LMFDB
  `mf.bianchi.weight2` divided by `det J(γ, z) = |cx + d|² + |c|² y²`.
-/

open Complex Matrix TauCeti WithLp
open scoped ComplexConjugate MatrixGroups

namespace HyperbolicThreeSpace

variable (k : ℕ) (γ : SL(2, ℂ)) (p : ℂ × ℝ) (z : HyperbolicThreeSpace)
  (F : HyperbolicThreeSpace → Fin (k + 1) → ℂ)

/-- The **symmetric power** `Sym^k(A)` (LMFDB `mf.bianchi`) of a `2 × 2` complex matrix
`A = (a, b; c, d)`: the matrix of the substitution `X ↦ aX + bY`, `Y ↦ cX + dY` on the homogeneous
polynomials of degree `k` in the basis `X^{k-i} Y^i`, whose entry `(i, j)` is the coefficient of
`X^{k-j} Y^j` in `(aX + bY)^{k-i} (cX + dY)^i`. It is multiplicative (not proved here), and
`Sym^2` is the matrix of LMFDB `mf.bianchi.weight2` (`bianchiSlash_two`). -/
def symPowMatrix (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  of fun i j ↦ ∑ q ∈ Finset.range (j + 1), ((k - i : ℕ).choose (j - q) * (i : ℕ).choose q : ℂ) *
    A 0 0 ^ (k - i - (j - q)) * A 0 1 ^ (j - q) * A 1 0 ^ (i - q) * A 1 1 ^ q

/-- The **automorphy factor** `J(γ, z) = (cx + d, -cy; c̄y, conj(cx + d))` (LMFDB `mf.bianchi`) of
`γ = (a, b; c, d) ∈ SL(2, ℂ)` at `p = (x, y)`: the image of the quaternion `cz + d`, where
`z = x + yj`, under the embedding `x + yj ↦ (x, -y; ȳ, x̄)` of the quaternions in `M₂(ℂ)`. -/
def automorphyFactor : Matrix (Fin 2) (Fin 2) ℂ :=
  !![γ 1 0 * p.1 + γ 1 1, -(γ 1 0 * p.2); conj (γ 1 0) * p.2, conj (γ 1 0 * p.1 + γ 1 1)]

lemma det_automorphyFactor : (automorphyFactor γ p).det = moebiusDenom γ p := by
  simp only [automorphyFactor, det_fin_two_of, moebiusDenom, ofReal_add, ofReal_mul, ofReal_pow,
    ← mul_conj]
  ring1

lemma inv_automorphyFactor : (automorphyFactor γ p)⁻¹ = (moebiusDenom γ p : ℂ)⁻¹ •
    !![conj (γ 1 0 * p.1 + γ 1 1), γ 1 0 * p.2; -(conj (γ 1 0) * p.2), γ 1 0 * p.1 + γ 1 1] := by
  rw [Matrix.inv_def, det_automorphyFactor, adjugate_fin_two, Ring.inverse_eq_inv']
  simp [automorphyFactor]

/-- The **weight `k` slash operator** `(F ∣_k γ)(z) = Sym^k(J(γ, z)⁻¹) F(γ z)` (LMFDB `mf.bianchi`)
of `γ ∈ SL(2, ℂ)` on `F : ℋ₃ → ℂ^{k+1}`.

The automorphy factor `J(γ, z)` is not normalised: its determinant is
`|cx + d|² + |c|² y² = y / y(γz)`. With the normalised factor `J(γ, z) / √det J(γ, z) ∈ SU(2)`,
as in LMFDB `mf.bianchi.weight2` and `mf.bianchi.fourierbessell`, a function `G` is invariant
exactly when `y^{-k/2} G` is invariant here, so both conventions give the same forms up to this
factor, and the same lifts to `SL(2, ℂ)`. Since
`Sym^k(-A) = (-1)^k Sym^k(A)`, the operator only depends on the image of `γ` in `PSL(2, ℂ)` when `k`
is even. -/
noncomputable def bianchiSlash : HyperbolicThreeSpace → Fin (k + 1) → ℂ :=
  fun z ↦ symPowMatrix k (automorphyFactor γ z.coords)⁻¹ *ᵥ F (γ • z)

lemma bianchiSlash_add (G : HyperbolicThreeSpace → Fin (k + 1) → ℂ) :
    bianchiSlash k γ (F + G) = bianchiSlash k γ F + bianchiSlash k γ G :=
  funext fun _ ↦ mulVec_add ..

lemma bianchiSlash_smul (c : ℂ) : bianchiSlash k γ (c • F) = c • bianchiSlash k γ F :=
  funext fun _ ↦ mulVec_smul _ c _

/-- The function `F : ℋ₃ → V`, extended by zero to `ℂ × ℝ`. -/
noncomputable def extend {V : Type*} [Zero V] (f : HyperbolicThreeSpace → V) : ℂ × ℝ → V :=
  fun q ↦ if h : 0 < q.2 then f (.mk (toLp 2 q) h) else 0

lemma extend_coords {V : Type*} [Zero V] (f : HyperbolicThreeSpace → V) :
    extend f z.coords = f z :=
  dite_eq_left z.height_pos

/-- **The weight 2 slash operator**: `F ∣_2 γ` is the weight 2 slash operator of LMFDB
`mf.bianchi.weight2`, divided by `det J(γ, z) = |cx + d|² + |c|² y²`. -/
lemma bianchiSlash_two (f : HyperbolicThreeSpace → Fin 3 → ℂ) :
    bianchiSlash 2 γ f z = (moebiusDenom γ z.coords : ℂ)⁻¹ • slashTwo (extend f) γ z.coords := by
  ext i
  rw [bianchiSlash, inv_automorphyFactor, slashTwo, ← coords_smul, extend_coords]
  fin_cases i <;>
    simp [symPowMatrix, mulVec, dotProduct, Fin.sum_univ_three, Finset.sum_range_succ,
      moebiusDenom, normSq_eq_conj_mul_self] <;>
    ring1

end HyperbolicThreeSpace
