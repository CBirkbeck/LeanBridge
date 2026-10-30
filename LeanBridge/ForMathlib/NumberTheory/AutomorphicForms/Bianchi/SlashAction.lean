import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.Slash
import Mathlib.Algebra.Polynomial.Roots
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# The weight `k` slash operator is a right action of `SL(2, ℂ)`

The weight `k` slash operator `(F ∣_k γ)(z) = Sym^k(J(γ, z)⁻¹) F(γ z)` of LMFDB `mf.bianchi` is a
right action of `SL(2, ℂ)` on functions `F : ℋ₃ → ℂ^{k+1}`: `F ∣_k gh = (F ∣_k g) ∣_k h`. This
rests on three facts, proved here.

* `Sym^k` is multiplicative: `Sym^k(A)` is the matrix of the substitution
  `X ↦ aX + bY`, `Y ↦ cX + dY` on the homogeneous polynomials of degree `k`, which is read off its
  action on the vectors `(x^{k-j} y^j)_j` of values of the monomials.
* The action `γ z = (az + b)(cz + d)⁻¹` of `SL(2, ℂ)` on `ℋ₃`, `z = x + yj` a quaternion, is an
  action: in terms of the matrices `Q(u, v; z)` of the quaternions `uz + v`, of which `J(γ, z)` is
  `Q(c, d; z)`, it is characterised by `Q(1, 0; γ z) J(γ, z) = Q(a, b; z)`.
* The automorphy factor is a cocycle, `J(gh, z) = J(g, hz) J(h, z)`: more generally
  `Q(u, v; hz) J(h, z) = Q((u, v) h; z)`, which is the identity `(u(hz) + v)(cz + d) = (u, v) h z`
  of quaternions.

## Main definitions

* `HyperbolicThreeSpace.monomialVector`: the vector `(x^{k-j} y^j)_j` of values of the monomials.
* `HyperbolicThreeSpace.quatMatrix`: the matrix `Q(u, v; z)` of the quaternion `uz + v`.
* The instance `MulAction SL(2, ℂ) HyperbolicThreeSpace`.

## Main results

* `HyperbolicThreeSpace.symPowMatrix_mulVec_monomialVector`: `Sym^k(A)` maps the values of the
  monomials at `(x, y)` to their values at `A (x, y)`.
* `HyperbolicThreeSpace.symPowMatrix_mul`: `Sym^k(AB) = Sym^k(A) Sym^k(B)`.
* `HyperbolicThreeSpace.automorphyFactor_mul`: the cocycle relation `J(gh, z) = J(g, hz) J(h, z)`.
* `HyperbolicThreeSpace.moebius_mul`: `(gh) z = g (h z)`.
* `HyperbolicThreeSpace.bianchiSlash_mul`: `F ∣_k gh = (F ∣_k g) ∣_k h`.
* `HyperbolicThreeSpace.bianchiSlash_neg`: `F ∣_k (-g) = (-1)^k F ∣_k g`.
-/

open Complex Matrix

open scoped ComplexConjugate MatrixGroups

namespace HyperbolicThreeSpace

variable (k : ℕ) (A B : Matrix (Fin 2) (Fin 2) ℂ) (x y u v : ℂ) (g h : SL(2, ℂ)) {p : ℂ × ℝ}
  (F : HyperbolicThreeSpace → Fin (k + 1) → ℂ)

/-- The vector `(x^{k-j} y^j)_{0 ≤ j ≤ k}` of values at `(x, y)` of the monomials `X^{k-j} Y^j`,
the basis of the homogeneous polynomials of degree `k` in which `Sym^k` is written. -/
def monomialVector : Fin (k + 1) → ℂ :=
  fun j ↦ x ^ (k - j : ℕ) * y ^ (j : ℕ)

lemma sum_range_sum_range_choose (n i : ℕ) (a b c d : ℂ) : ∑ j ∈ Finset.range (n + i + 1),
    (∑ q ∈ Finset.range (j + 1), ((n.choose (j - q) * i.choose q : ℂ) * a ^ (n - (j - q)) *
      b ^ (j - q) * c ^ (i - q) * d ^ q)) * (x ^ (n + i - j) * y ^ j) =
    (a * x + b * y) ^ n * (c * x + d * y) ^ i := by
  rw [add_comm (a * x), add_comm (c * x), add_pow, add_pow, Finset.sum_mul_sum,
    ← Finset.sum_product']
  simp only [Finset.sum_mul]
  rw [Finset.sum_sigma']
  refine (Finset.sum_bij_ne_zero (fun p _ _ ↦ ⟨p.1 + p.2, p.2⟩) ?_ ?_ ?_ ?_).symm
  · rintro p hp -
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_sigma] at hp ⊢
    omega
  · rintro p - - p' - - h
    simp only [Sigma.ext_iff, heq_eq_eq] at h
    ext <;> omega
  · rintro ⟨j, q⟩ hjq h
    simp only [Finset.mem_sigma, Finset.mem_range] at hjq
    have hq : q ≤ i := by
      by_contra hq
      exact h (by simp [Nat.choose_eq_zero_of_lt (not_le.mp hq)])
    have hjq' : j - q ≤ n := by
      by_contra hjq'
      exact h (by simp [Nat.choose_eq_zero_of_lt (not_le.mp hjq')])
    refine ⟨(j - q, q), ?_, fun h0 ↦ h ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]
      omega
    · dsimp only at h0 ⊢
      rw [← pow_sub_mul_pow y (by omega : q ≤ j), (by omega : n + i - j = n - (j - q) + (i - q)),
        pow_add]
      linear_combination h0
    · simp only [Sigma.ext_iff, heq_eq_eq, and_true]
      omega
  · rintro ⟨m, q⟩ hp -
    simp only [Finset.mem_product, Finset.mem_range] at hp
    rw [Nat.add_sub_cancel, (by omega : n + i - (m + q) = n - m + (i - q)), pow_add, pow_add]
    ring1

/-- **`Sym^k(A)` is the substitution `X ↦ aX + bY`, `Y ↦ cX + dY`**: it maps the values
`(x^{k-j} y^j)_j` of the monomials at `(x, y)` to their values at `A (x, y)`. -/
lemma symPowMatrix_mulVec_monomialVector : symPowMatrix k A *ᵥ monomialVector k x y =
    monomialVector k (A 0 0 * x + A 0 1 * y) (A 1 0 * x + A 1 1 * y) := by
  ext i
  have h : ∑ j ∈ Finset.range (k - i + i + 1), (∑ q ∈ Finset.range (j + 1),
      ((k - i : ℕ).choose (j - q) * (i : ℕ).choose q : ℂ) * A 0 0 ^ (k - i - (j - q)) *
        A 0 1 ^ (j - q) * A 1 0 ^ (i - q) * A 1 1 ^ q) * (x ^ (k - i + i - j) * y ^ j) =
      (A 0 0 * x + A 0 1 * y) ^ (k - i) * (A 1 0 * x + A 1 1 * y) ^ (i : ℕ) :=
    sum_range_sum_range_choose x y (k - i) i (A 0 0) (A 0 1) (A 1 0) (A 1 1)
  rw [Nat.sub_add_cancel i.is_le] at h
  simp only [mulVec, dotProduct, monomialVector, symPowMatrix, of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ (∑ q ∈ Finset.range (j + 1),
      ((k - i : ℕ).choose (j - q) * (i : ℕ).choose q : ℂ) *
        A 0 0 ^ (k - i - (j - q)) * A 0 1 ^ (j - q) * A 1 0 ^ (i - q) * A 1 1 ^ q) *
      (x ^ (k - j) * y ^ j)), h]

variable {k} in
lemma eq_of_mulVec_monomialVector {M M' : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (h : ∀ x, M *ᵥ monomialVector k x 1 = M' *ᵥ monomialVector k x 1) : M = M' := by
  ext i l
  have hp :
      (∑ j : Fin (k + 1), Polynomial.C (M i j - M' i j) * Polynomial.X ^ (k - j : ℕ)) = 0 := by
    refine Polynomial.funext fun x ↦ ?_
    have hx : ∑ j, M i j * x ^ (k - j : ℕ) = ∑ j, M' i j * x ^ (k - j : ℕ) := by
      simpa [mulVec, dotProduct, monomialVector] using congrFun (h x) i
    simp [Polynomial.eval_finsetSum, sub_mul, hx]
  have hc : (∑ j : Fin (k + 1), if k - l = k - j then M i j - M' i j else 0) = 0 := by
    simpa only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero]
      using congrArg (Polynomial.coeff · (k - l : ℕ)) hp
  rw [Finset.sum_eq_single l (fun j _ hj ↦ ite_eq_right fun e ↦ hj (Fin.ext (by omega))) (by simp),
    ite_eq_left rfl] at hc
  exact sub_eq_zero.mp hc

/-- **`Sym^k` is multiplicative**: `Sym^k(AB) = Sym^k(A) Sym^k(B)`, as the substitution of `AB` is
the substitution of `B` followed by that of `A`. -/
lemma symPowMatrix_mul : symPowMatrix k (A * B) = symPowMatrix k A * symPowMatrix k B := by
  refine eq_of_mulVec_monomialVector fun x ↦ ?_
  rw [← mulVec_mulVec, symPowMatrix_mulVec_monomialVector, symPowMatrix_mulVec_monomialVector,
    symPowMatrix_mulVec_monomialVector]
  simp only [mul_apply, Fin.sum_univ_two]
  congr 1 <;> ring1

lemma symPowMatrix_one : symPowMatrix k 1 = 1 := by
  refine eq_of_mulVec_monomialVector fun x ↦ ?_
  rw [symPowMatrix_mulVec_monomialVector, one_mulVec]
  simp

lemma monomialVector_neg : monomialVector k (-x) (-y) = (-1 : ℂ) ^ k • monomialVector k x y := by
  ext j
  rw [monomialVector, Pi.smul_apply, monomialVector, neg_pow x, neg_pow y, smul_eq_mul,
    ← pow_sub_mul_pow (-1 : ℂ) j.is_le]
  ring1

lemma symPowMatrix_neg : symPowMatrix k (-A) = (-1 : ℂ) ^ k • symPowMatrix k A := by
  refine eq_of_mulVec_monomialVector fun x ↦ ?_
  rw [smul_mulVec, symPowMatrix_mulVec_monomialVector, symPowMatrix_mulVec_monomialVector,
    ← monomialVector_neg]
  congr 1 <;> simp only [Matrix.neg_apply] <;> ring1

variable (p) in
/-- The matrix `Q(u, v; z) = (ux + v, -uy; ūy, conj(ux + v))` of the quaternion `uz + v`, where
`z = x + yj` for `p = (x, y)`, under the embedding `x + yj ↦ (x, -y; ȳ, x̄)` of the quaternions in
`M₂(ℂ)`. The automorphy factor `J(γ, z)` is `Q(c, d; z)` (`automorphyFactor_eq_quatMatrix`). -/
def quatMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![u * p.1 + v, -(u * p.2); conj u * p.2, conj (u * p.1 + v)]

variable (p) in
lemma automorphyFactor_eq_quatMatrix : automorphyFactor h p = quatMatrix (h 1 0) (h 1 1) p :=
  rfl

lemma quatMatrix_moebius_mul (hp : 0 < p.2) : quatMatrix u v (moebius h p) * automorphyFactor h p =
    quatMatrix (u * h 0 0 + v * h 1 0) (u * h 0 1 + v * h 1 1) p := by
  have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := h.fin_two_mul_sub_mul_eq_one
  have hdet' : conj (h 0 0) * conj (h 1 1) - conj (h 0 1) * conj (h 1 0) = 1 := by
    simpa using congrArg conj hdet
  have hN : (moebiusDenom h p : ℂ) ≠ 0 := ofReal_ne_zero.mpr (moebiusDenom_pos h hp).ne'
  have hN' : (moebiusDenom h p : ℂ) =
      (h 1 0 * p.1 + h 1 1) * (conj (h 1 0) * conj p.1 + conj (h 1 1)) +
        h 1 0 * conj (h 1 0) * (p.2 : ℂ) ^ 2 := by
    rw [moebiusDenom, ofReal_add, ofReal_mul, ← mul_conj, ← mul_conj]
    simp only [map_add, map_mul, ofReal_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatMatrix, moebius, automorphyFactor] <;>
    generalize (moebiusDenom h p : ℂ) = N at hN hN' ⊢ <;>
    field_simp
  · linear_combination u * conj (h 1 0) * (p.2 : ℂ) ^ 2 * hdet - u * (h 0 0 * p.1 + h 0 1) * hN'
  · linear_combination (p.2 : ℂ) * u * (conj (h 1 0) * conj p.1 + conj (h 1 1)) * hdet +
      (p.2 : ℂ) * u * h 0 0 * hN'
  · linear_combination -((p.2 : ℂ) * conj u * (h 1 0 * p.1 + h 1 1)) * hdet' -
      (p.2 : ℂ) * conj u * conj (h 0 0) * hN'
  · linear_combination conj u * (p.2 : ℂ) ^ 2 * h 1 0 * hdet' -
      conj u * (conj (h 0 0) * conj p.1 + conj (h 0 1)) * hN'

lemma moebius_snd_pos (hp : 0 < p.2) : 0 < (moebius h p).2 :=
  div_pos hp (moebiusDenom_pos h hp)

/-- **The automorphy factor is a cocycle**: `J(gh, z) = J(g, hz) J(h, z)` for `g, h ∈ SL(2, ℂ)`
and `z = (x, y)` with `y > 0`. -/
lemma automorphyFactor_mul (hp : 0 < p.2) :
    automorphyFactor (g * h) p = automorphyFactor g (moebius h p) * automorphyFactor h p := by
  rw [automorphyFactor_eq_quatMatrix g, quatMatrix_moebius_mul _ _ h hp]
  simp [automorphyFactor_eq_quatMatrix, mul_apply]

lemma quatMatrix_one_zero_moebius_mul (hp : 0 < p.2) :
    quatMatrix 1 0 (moebius h p) * automorphyFactor h p = quatMatrix (h 0 0) (h 0 1) p := by
  simpa using quatMatrix_moebius_mul 1 0 h hp

/-- **The action of `SL(2, ℂ)` on `ℋ₃` is an action**: `(gh) z = g (h z)` for `z = (x, y)` with
`y > 0`, as `Q(1, 0; γ z) J(γ, z) = Q(a, b; z)` determines `γ z`. -/
lemma moebius_mul (hp : 0 < p.2) : moebius (g * h) p = moebius g (moebius h p) := by
  have hJ : IsUnit (automorphyFactor (g * h) p).det := by
    rw [det_automorphyFactor]
    exact (ofReal_ne_zero.mpr (moebiusDenom_pos (g * h) hp).ne').isUnit
  have h₁ : quatMatrix 1 0 (moebius (g * h) p) * automorphyFactor (g * h) p =
      quatMatrix 1 0 (moebius g (moebius h p)) * automorphyFactor (g * h) p := by
    rw [quatMatrix_one_zero_moebius_mul _ hp, automorphyFactor_mul g h hp, ← mul_assoc,
      quatMatrix_one_zero_moebius_mul _ (moebius_snd_pos h hp), quatMatrix_moebius_mul _ _ h hp]
    simp [mul_apply]
  have h₂ : quatMatrix 1 0 (moebius (g * h) p) = quatMatrix 1 0 (moebius g (moebius h p)) := by
    simpa only [mul_nonsing_inv_cancel_right _ _ hJ] using
      congrArg (· * (automorphyFactor (g * h) p)⁻¹) h₁
  have h₀₀ : (moebius (g * h) p).1 = (moebius g (moebius h p)).1 := by
    simpa [quatMatrix] using congrFun (congrFun h₂ 0) 0
  have h₁₀ : (moebius (g * h) p).2 = (moebius g (moebius h p)).2 := by
    simpa [quatMatrix] using congrFun (congrFun h₂ 1) 0
  exact Prod.ext h₀₀ h₁₀

variable (p) in
lemma moebius_one : moebius 1 p = p := by
  simp [moebius, moebiusDenom]

lemma coords_snd_pos (z : HyperbolicThreeSpace) : 0 < z.coords.2 :=
  z.height_pos

noncomputable instance : MulAction SL(2, ℂ) HyperbolicThreeSpace where
  one_smul z := coords_injective <| by
    rw [coords_smul, moebius_one]
  mul_smul g h z := coords_injective <| by
    rw [coords_smul, coords_smul, coords_smul, moebius_mul g h (coords_snd_pos z)]

/-- **The slash operator is a right action**: `F ∣_k gh = (F ∣_k g) ∣_k h` for `g, h ∈ SL(2, ℂ)`,
by the cocycle relation and the multiplicativity of `Sym^k`. -/
lemma bianchiSlash_mul : bianchiSlash k (g * h) F = bianchiSlash k h (bianchiSlash k g F) := by
  ext z : 1
  rw [bianchiSlash, bianchiSlash, bianchiSlash, mul_smul, coords_smul,
    automorphyFactor_mul g h (coords_snd_pos z), Matrix.mul_inv_rev, symPowMatrix_mul,
    mulVec_mulVec]

lemma bianchiSlash_one : bianchiSlash k 1 F = F := by
  ext z : 1
  have hJ : automorphyFactor 1 z.coords = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [automorphyFactor]
  rw [bianchiSlash, hJ, inv_one, symPowMatrix_one, one_mulVec, one_smul]

lemma bianchiSlash_neg_one : bianchiSlash k (-1) F = (-1 : ℂ) ^ k • F := by
  ext z : 1
  have hJ : automorphyFactor (-1) z.coords = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [automorphyFactor]
  have hz : (-1 : SL(2, ℂ)) • z = z := coords_injective <| by
    rw [coords_smul, moebius_eq_of_coe_eq_smul (γ := 1) z.coords (s := -1) (by simp) (by simp),
      moebius_one]
  rw [bianchiSlash, hJ, inv_eq_left_inv (by simp : (-1 : Matrix (Fin 2) (Fin 2) ℂ) * -1 = 1),
    symPowMatrix_neg, symPowMatrix_one, smul_mulVec, one_mulVec, hz]
  rfl

/-- **The slash operator of `-g`**: `F ∣_k (-g) = (-1)^k F ∣_k g`, so the slash operator only
depends on the image of `g` in `PSL(2, ℂ)` when `k` is even. -/
lemma bianchiSlash_neg : bianchiSlash k (-g) F = (-1 : ℂ) ^ k • bianchiSlash k g F := by
  rw [← neg_one_mul, bianchiSlash_mul, bianchiSlash_neg_one, bianchiSlash_smul]

end HyperbolicThreeSpace
