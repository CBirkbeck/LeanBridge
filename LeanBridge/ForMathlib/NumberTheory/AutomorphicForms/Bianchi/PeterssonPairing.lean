import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.Newform

/-!
# The invariance of the Petersson-type pairing of Bianchi modular forms

For `A = (a, -b; b̄, ā)`, the image of a quaternion, `Aᴴ A = (|a|² + |b|²) 1`. Hence the Hermitian
form `⟨v, w⟩_k = ∑ᵢ C(k, i) vᵢ w̄ᵢ` (`symPowInner`) on `ℂ^{k+1} = Sym^k(ℂ²)`, which on the vectors
`(x^{k-i} y^i)_i` of values of the monomials is `⟨u, u'⟩ = (x x̄' + y ȳ')^k`, satisfies
`⟨Sym^k(A) v, Sym^k(A) w⟩_k = (|a|² + |b|²)^k ⟨v, w⟩_k`
(`symPowInner_symPowMatrix_mulVec_mulVec`). The automorphy factor `J(g, z)` being such a matrix, of
determinant `|cx + d|² + |c|² y² = y / y(gz)`, the function
`(F, G) ↦ y^k ⟨F(z), G(z)⟩_k` (`bianchiPairing`) satisfies
`y^k ⟨(F ∣_k g)(z), (G ∣_k g)(z)⟩_k = y(gz)^k ⟨F(gz), G(gz)⟩_k` (`bianchiPairing_bianchiSlash`). In
particular the integrand of the Petersson-type inner product of LMFDB `mf.bianchi.spaces`
(`IsBianchiPeterssonOrthogonal`) is invariant under the level, and the form is positive definite.

## Main definitions

* `HyperbolicThreeSpace.bianchiPairing` (LMFDB `mf.bianchi.spaces`): the integrand
  `y^k ⟨F(z), G(z)⟩_k` of the Petersson-type inner product.
* `HyperbolicThreeSpace.bianchiNormSq`: the invariant norm `y^k ⟨F(z), F(z)⟩_k` of `F(z)`.

## Main results

* `HyperbolicThreeSpace.symPowInner_symPowMatrix_mulVec_mulVec`: invariance of the Hermitian form
  under the images of the quaternions.
* `HyperbolicThreeSpace.bianchiPairing_bianchiSlash`: the invariance of the pairing under the slash
  operators.
* `HyperbolicThreeSpace.bianchiNormSq_bianchiSlash`: the invariance of the norm.
-/

open Complex Matrix

open scoped ComplexConjugate MatrixGroups

namespace HyperbolicThreeSpace

variable {k : ℕ} (x y x' y' a b : ℂ) (v w : Fin (k + 1) → ℂ) (g : SL(2, ℂ)) {p : ℂ × ℝ}
  (F G : HyperbolicThreeSpace → Fin (k + 1) → ℂ) (z : HyperbolicThreeSpace)

lemma symPowInner_monomialVector : symPowInner k (monomialVector k x y) (monomialVector k x' y') =
    (x * conj x' + y * conj y') ^ k := by
  rw [add_comm, add_pow, ← Fin.sum_univ_eq_sum_range
    (fun m ↦ (y * conj y') ^ m * (x * conj x') ^ (k - m) * (k.choose m : ℂ)) (k + 1), symPowInner]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [monomialVector, map_mul, map_pow]
  ring1

variable {v w} in
lemma eq_of_forall_dotProduct_monomialVector
    (h : ∀ x : ℂ, v ⬝ᵥ monomialVector k x 1 = w ⬝ᵥ monomialVector k x 1) : v = w := by
  have hM : (of fun _ j ↦ v j : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) = of fun _ j ↦ w j :=
    eq_of_mulVec_monomialVector fun x ↦ funext fun _ ↦ h x
  exact funext fun j ↦ congrFun (congrFun hM 0) j

lemma symPowInner_eq_dotProduct :
    symPowInner k v w = v ⬝ᵥ (diagonal (fun i : Fin (k + 1) ↦ (k.choose i : ℂ)) *ᵥ star w) := by
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, RCLike.star_def]
  exact Finset.sum_congr rfl fun i _ ↦ by ring1

lemma star_monomialVector : star (monomialVector k x y) = monomialVector k (conj x) (conj y) := by
  ext j
  simp [monomialVector]

lemma map_conj_mulVec_star (S : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    S.map (starRingEnd ℂ) *ᵥ star v = star (S *ᵥ v) := by
  ext i
  simp [mulVec, dotProduct]

/-- **The image of a quaternion preserves the Hermitian form up to a scalar**: for
`A = (a, -b; b̄, ā)`, `⟨Sym^k(A) v, Sym^k(A) w⟩_k = (|a|² + |b|²)^k ⟨v, w⟩_k`, as
`⟨Au, Au'⟩ = (|a|² + |b|²) ⟨u, u'⟩` on `ℂ²` and the vectors of values of the monomials span
`ℂ^{k+1}`. -/
lemma symPowInner_symPowMatrix_mulVec_mulVec :
    symPowInner k (symPowMatrix k !![a, -b; conj b, conj a] *ᵥ v)
      (symPowMatrix k !![a, -b; conj b, conj a] *ᵥ w) =
        (a * conj a + b * conj b) ^ k * symPowInner k v w := by
  let D : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := diagonal fun i ↦ (k.choose i : ℂ)
  let S : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := symPowMatrix k !![a, -b; conj b, conj a]
  have hS (x y : ℂ) :
      S *ᵥ monomialVector k x y = monomialVector k (a * x + -b * y) (conj b * x + conj a * y) :=
    symPowMatrix_mulVec_monomialVector k _ x y
  have hM : Sᵀ * D * S.map (starRingEnd ℂ) = (a * conj a + b * conj b) ^ k • D := by
    refine eq_of_mulVec_monomialVector fun x ↦ eq_of_forall_dotProduct_monomialVector fun x' ↦ ?_
    have hx : monomialVector k x 1 = star (monomialVector k (conj x) 1) := by
      rw [star_monomialVector, conj_conj, map_one]
    have h₁ : ((Sᵀ * D * S.map (starRingEnd ℂ)) *ᵥ monomialVector k x 1) ⬝ᵥ monomialVector k x' 1 =
        symPowInner k (S *ᵥ monomialVector k x' 1) (S *ᵥ monomialVector k (conj x) 1) := by
      rw [symPowInner_eq_dotProduct, ← map_conj_mulVec_star, ← hx, ← mulVec_mulVec, ← mulVec_mulVec,
        dotProduct_comm, dotProduct_mulVec, vecMul_transpose]
    have h₂ : (((a * conj a + b * conj b) ^ k • D) *ᵥ monomialVector k x 1) ⬝ᵥ
        monomialVector k x' 1 = (a * conj a + b * conj b) ^ k *
          symPowInner k (monomialVector k x' 1) (monomialVector k (conj x) 1) := by
      rw [symPowInner_eq_dotProduct, ← hx, smul_mulVec, smul_dotProduct, dotProduct_comm,
        smul_eq_mul]
    rw [h₁, h₂, hS, hS, symPowInner_monomialVector, symPowInner_monomialVector, ← mul_pow]
    congr 1
    simp only [map_add, map_mul, map_neg, conj_conj]
    ring1
  have h : symPowInner k (S *ᵥ v) (S *ᵥ w) = (a * conj a + b * conj b) ^ k * symPowInner k v w := by
    rw [symPowInner_eq_dotProduct, ← map_conj_mulVec_star, symPowInner_eq_dotProduct,
      ← smul_eq_mul, ← dotProduct_smul, ← smul_mulVec, ← hM, ← mulVec_mulVec, ← mulVec_mulVec,
      dotProduct_mulVec v, vecMul_transpose]
  exact h

lemma symPowInner_inv_automorphyFactor (hp : 0 < p.2) :
    symPowInner k (symPowMatrix k (automorphyFactor g p)⁻¹ *ᵥ v)
      (symPowMatrix k (automorphyFactor g p)⁻¹ *ᵥ w) =
        ((moebiusDenom g p : ℂ)⁻¹) ^ k * symPowInner k v w := by
  have hN : (moebiusDenom g p : ℂ) ≠ 0 := ofReal_ne_zero.mpr (moebiusDenom_pos g hp).ne'
  have hN' : (moebiusDenom g p : ℂ) = (g 1 0 * p.1 + g 1 1) * conj (g 1 0 * p.1 + g 1 1) +
      g 1 0 * p.2 * conj (g 1 0 * p.2) := by
    rw [moebiusDenom, ofReal_add, ofReal_mul, ← mul_conj, ← mul_conj]
    simp only [map_mul, conj_ofReal, ofReal_pow]
    ring1
  have hA : (automorphyFactor g p)⁻¹ = !![(moebiusDenom g p : ℂ)⁻¹ * conj (g 1 0 * p.1 + g 1 1),
        -(-((moebiusDenom g p : ℂ)⁻¹ * (g 1 0 * p.2)));
        conj (-((moebiusDenom g p : ℂ)⁻¹ * (g 1 0 * p.2))),
        conj ((moebiusDenom g p : ℂ)⁻¹ * conj (g 1 0 * p.1 + g 1 1))] := by
    rw [inv_automorphyFactor]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hA, symPowInner_symPowMatrix_mulVec_mulVec]
  congr 2
  simp only [map_mul, map_neg, map_inv₀, conj_ofReal, conj_conj, map_add]
  field_simp
  simp only [map_mul, conj_ofReal, map_add] at hN'
  linear_combination -hN'

/-- The integrand `y^k ⟨F(z), G(z)⟩_k` (LMFDB `mf.bianchi.spaces`) of the Petersson-type inner
product of `F, G : ℋ₃ → ℂ^{k+1}` (`IsBianchiPeterssonOrthogonal`), at `z = (x, y)`. It is invariant
under the slash operators (`bianchiPairing_bianchiSlash`). -/
noncomputable def bianchiPairing : ℂ :=
  (z.height ^ k : ℂ) * symPowInner k (F z) (G z)

lemma height_smul : (g • z).height = z.height / moebiusDenom g z.coords :=
  rfl

/-- **The Petersson-type pairing is invariant under the slash operators**:
`y^k ⟨(F ∣_k g)(z), (G ∣_k g)(z)⟩_k = y(gz)^k ⟨F(gz), G(gz)⟩_k` for `g ∈ SL(2, ℂ)`, as
`J(g, z)⁻¹` is the image of a quaternion of squared norm `1 / det J(g, z)` and
`det J(g, z) = y / y(gz)`. -/
lemma bianchiPairing_bianchiSlash :
    bianchiPairing (bianchiSlash k g F) (bianchiSlash k g G) z = bianchiPairing F G (g • z) := by
  simp only [bianchiPairing, bianchiSlash]
  rw [symPowInner_inv_automorphyFactor _ _ g (coords_snd_pos z), height_smul, ofReal_div,
    div_eq_mul_inv, mul_pow, mul_assoc]

/-- The **invariant norm** `y^k ⟨F(z), F(z)⟩_k = y^k ∑ᵢ C(k, i) |F(z)ᵢ|²` of `F(z)`, for
`F : ℋ₃ → ℂ^{k+1}` at `z = (x, y)`. For a function invariant under a level it is a function on the
quotient by the level (`bianchiNormSq_bianchiSlash`). -/
noncomputable def bianchiNormSq : ℝ :=
  z.height ^ k * ∑ i : Fin (k + 1), (k.choose i : ℝ) * ‖F z i‖ ^ 2

lemma bianchiPairing_self : bianchiPairing F F z = (bianchiNormSq F z : ℂ) := by
  simp only [bianchiPairing, bianchiNormSq, symPowInner, ofReal_mul, ofReal_pow, ofReal_sum,
    ofReal_natCast, mul_assoc, mul_conj, normSq_eq_norm_sq]

lemma bianchiNormSq_nonneg : 0 ≤ bianchiNormSq F z :=
  mul_nonneg (pow_nonneg z.height_pos.le k) (Finset.sum_nonneg fun _ _ ↦ by positivity)

lemma bianchiNormSq_eq_zero_iff : bianchiNormSq F z = 0 ↔ F z = 0 := by
  rw [bianchiNormSq, mul_eq_zero, or_iff_right (pow_pos z.height_pos k).ne',
    Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ by positivity]
  refine ⟨fun h ↦ funext fun i ↦ ?_, fun h i _ ↦ by simp [h]⟩
  have h₁ : (k.choose i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos i.is_le).ne'
  simpa [h₁] using h i (Finset.mem_univ i)

/-- **The invariant norm is invariant**: `‖(F ∣_k g)(z)‖² = ‖F(gz)‖²` for the norm `bianchiNormSq`
and `g ∈ SL(2, ℂ)`. -/
lemma bianchiNormSq_bianchiSlash : bianchiNormSq (bianchiSlash k g F) z = bianchiNormSq F (g • z) :=
  ofReal_injective <| by
    rw [← bianchiPairing_self, ← bianchiPairing_self, bianchiPairing_bianchiSlash]

lemma sq_norm_apply_le_bianchiNormSq (j : Fin (k + 1)) :
    z.height ^ k * ‖F z j‖ ^ 2 ≤ bianchiNormSq F z := by
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg z.height_pos.le k)
  have h₁ : (1 : ℝ) ≤ k.choose j := by
    exact_mod_cast Nat.choose_pos j.is_le
  have h₂ : (k.choose j : ℝ) * ‖F z j‖ ^ 2 ≤ ∑ i : Fin (k + 1), (k.choose i : ℝ) * ‖F z i‖ ^ 2 :=
    Finset.single_le_sum (f := fun i : Fin (k + 1) ↦ (k.choose i : ℝ) * ‖F z i‖ ^ 2)
      (fun _ _ ↦ by positivity) (Finset.mem_univ j)
  nlinarith [sq_nonneg ‖F z j‖]

end HyperbolicThreeSpace
