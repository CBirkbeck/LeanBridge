import LeanBridge.ForMathlib.AlgebraicGeometry.GenusTwo.MinimalEquation
import Mathlib.Algebra.Polynomial.Homogenize
import TauCeti.RingTheory.Polynomial.RootEnumeration

/-!
# The discriminant of a hyperelliptic equation under changes of variables

A change of variables `x = (aX + b) / (cX + d)`, `y = (eY + t(X)) / (cX + d)^(g + 1)` turns a
Weierstrass equation `y² + h(x)y = f(x)` of genus `g` into another one, whose binary form
`4f + h²` of degree `2g + 2` is `e⁻²` times the form `(4f + h²)(ax + bz, cx + dz)`. This file
proves the transformation law of the discriminant (LMFDB `g2c.discriminant`):
`Δ' = e^(-(8g + 4)) (ad - bc)^((2g + 2)(2g + 1)) Δ`, that is `Δ' = e⁻²⁰ (ad - bc)³⁰ Δ` for genus
two, with LeanBridge's discriminant, which uses `lc(f + h²/4)` when `f + h²/4` has degree `2g + 1`.
The factor is a square, so two minimal equations related by a change of variables have the same
discriminant, not only discriminants of the same absolute value.

The law rests on the transformation of the discriminant of a binary form `F` of degree `n` under
`(x, z) ↦ (ax + bz, cx + dz)`: it is multiplied by `(ad - bc)^(n(n - 1))`. Over an algebraically
closed field, `F` is a product of `n` linear forms `uᵢx + vᵢz`, roots at infinity included, and its
discriminant is `∏_{i < j} (uᵢvⱼ - uⱼvᵢ)²`, which scales by `(ad - bc)²` in each factor.

That two equations with isomorphic function fields are related by such a change of variables,
which would make the discriminant an invariant of the curve, is not proved here: it needs the
uniqueness of the hyperelliptic involution together with Lüroth's description of the generators of
`K(x)`. Nor is the converse, that a change of variables with `ad - bc ≠ 0` and `e ≠ 0` gives an
equation with an isomorphic function field.

## Main definitions

* `Polynomial.binaryComp`: the substitution `(x, z) ↦ (ax + bz, cx + dz)` in the binary form of
  degree `n` of a polynomial, at `z = 1`.
* `HyperellipticEquation.changeOfVariables` (LMFDB `g2c.discriminant`): the change of variables
  `x = (aX + b) / (cX + d)`, `y = (eY + t(X)) / (cX + d)^(g + 1)`.

## Main results

* `Polynomial.binaryDiscr_prod`: the discriminant of a product of `n` linear forms, as a binary
  form of degree `n`.
* `Polynomial.binaryDiscr_binaryComp`: the discriminant of a binary form of degree `n` is
  multiplied by `(ad - bc)^(n(n - 1))` under `(x, z) ↦ (ax + bz, cx + dz)`.
* `HyperellipticEquation.simplifiedPolynomial_changeOfVariables`: under a change of variables,
  `4f + h²` becomes `e⁻²` times the substituted binary form.
* `HyperellipticEquation.discriminant_changeOfVariables` (LMFDB `g2c.discriminant`): the
  transformation law of the discriminant of a Weierstrass equation.
* `HyperellipticEquation.IsMinimal.discriminant_eq_of_changeOfVariables` (LMFDB
  `g2c.discriminant`): two minimal equations of the same curve related by a change of variables
  have the same discriminant.
-/

open Finset Polynomial

namespace Polynomial

section CommRing

variable {R : Type*} [CommRing R] {n : ℕ} (p q : R[X]) {a b c d : R}

lemma binaryDiscr_zero (hn : 2 ≤ n) : (0 : R[X]).binaryDiscr n = 0 :=
  binaryDiscr_of_natDegree_add_one_lt (by rw [natDegree_zero]; omega)

variable (n a b c d) in
/-- The substitution `(x, z) ↦ (ax + bz, cx + dz)` in the binary form `p(x, z) = ∑ pᵢ xⁱ z^(n - i)`
of degree `n` of a polynomial `p`, at `z = 1`: the polynomial `∑ pᵢ (aX + b)ⁱ (cX + d)^(n - i)`. -/
noncomputable def binaryComp : R[X] :=
  MvPolynomial.aeval ![C a * X + C b, C c * X + C d] (p.homogenize n)

lemma binaryComp_C_mul (l : R) : (C l * p).binaryComp n a b c d = C l * p.binaryComp n a b c d := by
  rw [binaryComp, binaryComp, homogenize_C_mul, map_mul, MvPolynomial.aeval_C, algebraMap_eq]

lemma binaryComp_add :
    (p + q).binaryComp n a b c d = p.binaryComp n a b c d + q.binaryComp n a b c d := by
  rw [binaryComp, binaryComp, binaryComp, homogenize_add, map_add]

variable {p q} in
lemma binaryComp_mul {m : ℕ} (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) :
    (p * q).binaryComp (m + n) a b c d = p.binaryComp m a b c d * q.binaryComp n a b c d := by
  rw [binaryComp, binaryComp, binaryComp, homogenize_mul p q hp hq, map_mul]

lemma binaryComp_prod (f : Fin n → R[X]) (hf : ∀ i, (f i).natDegree ≤ 1) :
    (∏ i, f i).binaryComp n a b c d = ∏ i, (f i).binaryComp 1 a b c d := by
  have h : (∏ i, f i).homogenize (∑ _i : Fin n, 1) = ∏ i, (f i).homogenize 1 :=
    homogenize_finsetProd fun i _ ↦ hf i
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
  rw [binaryComp, h, map_prod]
  rfl

lemma binaryComp_C_mul_X_add_C (u v : R) :
    (C u * X + C v).binaryComp 1 a b c d = C (u * a + v * c) * X + C (u * b + v * d) := by
  rw [binaryComp, homogenize_add, homogenize_C_mul, homogenize_X one_ne_zero, homogenize_C]
  simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C, algebraMap_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring1

lemma natDegree_binaryComp_le : (p.binaryComp n a b c d).natDegree ≤ n := by
  rw [binaryComp, MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_eq']
  refine natDegree_sum_le_of_forall_le _ _ fun m hm ↦ ?_
  have hw : m 0 + m 1 = n := by
    have h : Finsupp.weight 1 m = n :=
      isHomogeneous_homogenize p (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using h
  have h₁ : (C a * X + C b).natDegree ≤ 1 := by
    compute_degree
  have h₂ : (C c * X + C d).natDegree ≤ 1 := by
    compute_degree
  have h₃ : ((C a * X + C b) ^ m 0).natDegree ≤ m 0 * 1 := natDegree_pow_le_of_le _ h₁
  have h₄ : ((C c * X + C d) ^ m 1).natDegree ≤ m 1 * 1 := natDegree_pow_le_of_le _ h₂
  rw [Fin.prod_univ_two]
  refine (natDegree_C_mul_le _ _).trans <| natDegree_mul_le.trans ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

lemma binaryComp_map {L : Type*} [CommRing L] (φ : R →+* L) :
    (p.binaryComp n a b c d).map φ = (p.map φ).binaryComp n (φ a) (φ b) (φ c) (φ d) := by
  rw [binaryComp, binaryComp, homogenize_map]
  generalize p.homogenize n = r
  induction r using MvPolynomial.induction_on with
  | C x => simp
  | add r₁ r₂ h₁ h₂ => rw [map_add, map_add, Polynomial.map_add, h₁, h₂, map_add]
  | mul_X r i h =>
    rw [map_mul, map_mul, Polynomial.map_mul, h, MvPolynomial.map_X, map_mul]
    fin_cases i <;> simp

end CommRing

section Field

variable {K : Type*} [Field K] {n : ℕ} {p : K[X]} {a b c d : K} (u v : Fin n → K)

lemma binaryDiscr_C_mul (hn : 2 ≤ n) (ha : a ≠ 0) :
    (C a * p).binaryDiscr n = a ^ (2 * n - 2) * p.binaryDiscr n := by
  rw [binaryDiscr, binaryDiscr, natDegree_C_mul ha, leadingCoeff_mul, leadingCoeff_C,
    TauCeti.discr_C_mul a ha]
  split_ifs with h₁ h₂
  · rw [h₁]
  · have h : 2 * p.natDegree - 2 + 2 = 2 * n - 2 := by
      omega
    rw [← h, pow_add]
    ring1
  · rw [mul_zero]

private lemma prod_prod_Ioi_mul (x : Fin n → K) :
    ∏ i, ∏ j ∈ Ioi i, (x i * x j) = (∏ i, x i) ^ (n - 1) := by
  have h : ∏ i, ∏ j ∈ Ioi i, (x i * x j) = ∏ i, ∏ _j ∈ ({i}ᶜ : Finset (Fin n)), x i :=
    prod_prod_Ioi_mul_eq_prod_prod_off_diag fun _ j ↦ x j
  simp only [prod_const, card_compl, card_singleton, Fintype.card_fin] at h
  exact h.trans (prod_pow _ _ _)

variable (c) in
private lemma prod_prod_Ioi_const : ∏ i : Fin n, ∏ _j ∈ Ioi i, c = c ^ (n * (n - 1) / 2) := by
  simp only [prod_const, prod_pow_eq_pow_sum, Fin.card_Ioi,
    Fin.sum_univ_eq_sum_range fun i ↦ n - 1 - i]
  rw [sum_range_reflect (fun i ↦ i) n, sum_range_id]

private lemma natDegree_prod_X_sub_C_fin (r : Fin n → K) : (∏ i, (X - C (r i))).natDegree = n := by
  rw [natDegree_finsetProd_X_sub_C_eq_card, card_univ, Fintype.card_fin]

variable {u} in
private lemma prod_C_mul_X_add_C (hu : ∀ i, u i ≠ 0) :
    ∏ i, (C (u i) * X + C (v i)) = C (∏ i, u i) * ∏ i, (X - C (-v i / u i)) := by
  rw [map_prod, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ ↦ ?_
  rw [mul_sub, ← C_mul, mul_div_cancel₀ _ (hu i), C_neg, sub_neg_eq_add]

variable {u} in
private lemma prod_prod_Ioi_sq_eq (hu : ∀ i, u i ≠ 0) :
    ∏ i, ∏ j ∈ Ioi i, (u i * v j - u j * v i) ^ 2 =
      (∏ i, u i) ^ (2 * n - 2) * ∏ i, ∏ j ∈ Ioi i, (-v i / u i - -v j / u j) ^ 2 := by
  have h2 : 2 * n - 2 = (n - 1) * 2 := by
    omega
  rw [h2, pow_mul, ← prod_prod_Ioi_mul]
  simp only [← prod_pow, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ ↦ prod_congr rfl fun j _ ↦ ?_
  rw [← mul_pow]
  congr 1
  have hi : u i * (-v i / u i) = -v i := mul_div_cancel₀ _ (hu i)
  have hj : u j * (-v j / u j) = -v j := mul_div_cancel₀ _ (hu j)
  linear_combination -u j * hi + u i * hj

variable {u} in
lemma binaryDiscr_prod_of_ne_zero (hn : 2 ≤ n) (hu : ∀ i, u i ≠ 0) :
    (∏ i, (C (u i) * X + C (v i))).binaryDiscr n =
      ∏ i, ∏ j ∈ Ioi i, (u i * v j - u j * v i) ^ 2 := by
  rw [prod_C_mul_X_add_C v hu, binaryDiscr_C_mul hn (prod_ne_zero_iff.mpr fun i _ ↦ hu i),
    binaryDiscr_of_natDegree_eq (natDegree_prod_X_sub_C_fin _), discr_prod_X_sub_C,
    prod_prod_Ioi_sq_eq v hu]

lemma binaryDiscr_prod_of_two_zero (hn : 2 ≤ n) {k l : Fin n} (hkl : k < l) (hk : u k = 0)
    (hl : u l = 0) : (∏ i, (C (u i) * X + C (v i))).binaryDiscr n =
      ∏ i, ∏ j ∈ Ioi i, (u i * v j - u j * v i) ^ 2 := by
  have h₀ : ∏ i, ∏ j ∈ Ioi i, (u i * v j - u j * v i) ^ 2 = 0 :=
    prod_eq_zero (mem_univ k) (prod_eq_zero (mem_Ioi.mpr hkl) (by rw [hk, hl]; ring1))
  rw [h₀]
  refine binaryDiscr_of_natDegree_add_one_lt ?_
  have hd (i : Fin n) : (C (u i) * X + C (v i)).natDegree ≤ 1 := by
    compute_degree
  have hd₀ (i : Fin n) (hi : u i = 0) : (C (u i) * X + C (v i)).natDegree = 0 := by
    rw [hi, C_0, zero_mul, zero_add, natDegree_C]
  have hp : (∏ i, (C (u i) * X + C (v i))).natDegree ≤
      ∑ i, (C (u i) * X + C (v i)).natDegree :=
    natDegree_prod_le _ _
  have hlk : l ∈ univ.erase k := mem_erase.mpr ⟨hkl.ne', mem_univ l⟩
  have he : ∑ i, (C (u i) * X + C (v i)).natDegree =
      ∑ i ∈ (univ.erase k).erase l, (C (u i) * X + C (v i)).natDegree := by
    rw [← add_sum_erase univ _ (mem_univ k), hd₀ k hk, zero_add, ← add_sum_erase _ _ hlk, hd₀ l hl,
      zero_add]
  have hc : #((univ.erase k).erase l) = n - 2 := by
    rw [card_erase_of_mem hlk, card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin]
    omega
  have hs : ∑ i ∈ (univ.erase k).erase l, (C (u i) * X + C (v i)).natDegree ≤
      #((univ.erase k).erase l) • 1 :=
    sum_le_card_nsmul _ _ 1 fun i _ ↦ hd i
  rw [he] at hp
  rw [hc, smul_eq_mul, mul_one] at hs
  omega

lemma binaryDiscr_prod_of_zero {m : ℕ} (hm : 1 ≤ m) (u' v' : Fin (m + 1) → K) (h₀ : u' 0 = 0)
    (hu : ∀ i : Fin m, u' i.succ ≠ 0) : (∏ i, (C (u' i) * X + C (v' i))).binaryDiscr (m + 1) =
      ∏ i, ∏ j ∈ Ioi i, (u' i * v' j - u' j * v' i) ^ 2 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_Ioi_zero, h₀, C_0, zero_mul, zero_add]
  simp only [Fin.prod_Ioi_succ]
  rcases eq_or_ne (v' 0) 0 with hv | hv
  · rw [hv, C_0, zero_mul, binaryDiscr_zero (by omega),
      prod_eq_zero (mem_univ (⟨0, hm⟩ : Fin m)) (by ring1), zero_mul]
  have hmon : (∏ i : Fin m, (X - C (-v' i.succ / u' i.succ))).Monic :=
    monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C _
  have hw : v' 0 * ∏ i : Fin m, u' i.succ ≠ 0 :=
    mul_ne_zero hv (prod_ne_zero_iff.mpr fun i _ ↦ hu i)
  have h₁ : ∏ j : Fin m, (0 * v' j.succ - u' j.succ * v' 0) ^ 2 =
      (∏ j : Fin m, u' j.succ) ^ 2 * v' 0 ^ (2 * m) := by
    rw [prod_congr rfl fun j _ ↦ (by ring1 :
      (0 * v' j.succ - u' j.succ * v' 0) ^ 2 = u' j.succ ^ 2 * v' 0 ^ 2), prod_mul_distrib,
      prod_pow, prod_const, card_univ, Fintype.card_fin, ← pow_mul]
  have h₂ : v' 0 ^ (2 * m) = v' 0 ^ 2 * v' 0 ^ (2 * m - 2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [prod_C_mul_X_add_C _ hu, ← mul_assoc, ← C_mul,
    binaryDiscr_of_natDegree_add_one_eq (by rw [natDegree_C_mul hw, natDegree_prod_X_sub_C_fin]),
    leadingCoeff_mul, leadingCoeff_C, hmon.leadingCoeff, TauCeti.discr_C_mul _ hw,
    natDegree_prod_X_sub_C_fin, discr_prod_X_sub_C, h₁, prod_prod_Ioi_sq_eq _ hu, h₂]
  ring1

/-- **The discriminant of a product of linear forms**: the product of the `n` linear forms
`uᵢx + vᵢz`, as a binary form of degree `n`, has discriminant `∏_{i < j} (uᵢvⱼ - uⱼvᵢ)²`, roots at
infinity (`uᵢ = 0`) included. -/
lemma binaryDiscr_prod (hn : 2 ≤ n) : (∏ i, (C (u i) * X + C (v i))).binaryDiscr n =
    ∏ i, ∏ j ∈ Ioi i, (u i * v j - u j * v i) ^ 2 := by
  by_cases hu : ∀ i, u i ≠ 0
  · exact binaryDiscr_prod_of_ne_zero v hn hu
  push Not at hu
  rcases hu with ⟨k, hk⟩
  by_cases hl : ∃ l, l ≠ k ∧ u l = 0
  · rcases hl with ⟨l, hlk, hl⟩
    rcases lt_or_gt_of_ne hlk with h | h
    · exact binaryDiscr_prod_of_two_zero u v hn h hl hk
    · exact binaryDiscr_prod_of_two_zero u v hn h hk hl
  push Not at hl
  rcases (⟨n - 1, by omega⟩ : ∃ m, n = m + 1) with ⟨m, rfl⟩
  let σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 k
  have hL : ∏ i, (C (u i) * X + C (v i)) = ∏ i, (C (u (σ i)) * X + C (v (σ i))) :=
    (Equiv.prod_comp σ fun i ↦ C (u i) * X + C (v i)).symm
  have hR : ∏ i, ∏ j ∈ Ioi i, (u i * v j - u j * v i) ^ 2 =
      ∏ i, ∏ j ∈ Ioi i, (u (σ i) * v (σ j) - u (σ j) * v (σ i)) ^ 2 := by
    simp only [prod_pow]
    rw [σ.prod_Ioi_comp_eq_sign_mul_prod (f := fun i j ↦ u i * v j - u j * v i)
      fun i j ↦ by ring1, mul_pow]
    rcases eq_or_ne 0 k with h | h <;> simp [σ, h]
  rw [hL, hR]
  refine binaryDiscr_prod_of_zero (by omega) _ _ (by simp [σ, hk]) fun i h ↦ hl _ ?_ h
  exact fun h' ↦ Fin.succ_ne_zero i <| σ.injective <| h'.trans (Equiv.swap_apply_left 0 k).symm

lemma binaryDiscr_binaryComp_of_prod {m k : ℕ} (hn : 2 ≤ m + k) (l : K) (r : Fin m → K) :
    ((C l * ∏ i, (X - C (r i))).binaryComp (m + k) a b c d).binaryDiscr (m + k) =
      (a * d - b * c) ^ ((m + k) * (m + k - 1)) *
          (C l * ∏ i, (X - C (r i))).binaryDiscr (m + k) := by
  rcases eq_or_ne l 0 with rfl | hl
  · rw [C_0, zero_mul, binaryComp, homogenize_zero, map_zero, binaryDiscr_zero hn, mul_zero]
  let u : Fin (m + k) → K := Fin.append (fun _ : Fin m ↦ (1 : K)) fun _ : Fin k ↦ 0
  let v : Fin (m + k) → K := Fin.append (fun i ↦ -r i) fun _ : Fin k ↦ (1 : K)
  have hq : ∏ i, (X - C (r i)) = ∏ i, (C (u i) * X + C (v i)) := by
    rw [Fin.prod_univ_add]
    simp [u, v, sub_eq_add_neg]
  have hd (i : Fin (m + k)) : (C (u i) * X + C (v i)).natDegree ≤ 1 := by
    compute_degree
  have hdet : (a * d - b * c) ^ ((m + k) * (m + k - 1)) =
      ∏ i : Fin (m + k), ∏ _j ∈ Ioi i, (a * d - b * c) ^ 2 := by
    rw [prod_prod_Ioi_const, ← pow_mul, Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd]
  rw [hq, binaryComp_C_mul, binaryComp_prod _ hd, binaryDiscr_C_mul hn hl, binaryDiscr_C_mul hn hl]
  simp only [binaryComp_C_mul_X_add_C]
  rw [binaryDiscr_prod _ _ hn, binaryDiscr_prod _ _ hn, mul_left_comm, hdet]
  congr 1
  simp only [← prod_mul_distrib]
  exact prod_congr rfl fun i _ ↦ prod_congr rfl fun j _ ↦ by ring1

variable (p) in
lemma binaryDiscr_map {L : Type*} [Field L] (φ : K →+* L) :
    (p.map φ).binaryDiscr n = φ (p.binaryDiscr n) := by
  rw [binaryDiscr, binaryDiscr, natDegree_map, leadingCoeff_map,
    discr_map_of_natDegree_eq φ (natDegree_map φ)]
  split_ifs <;> simp

lemma binaryDiscr_binaryComp_of_splits (hn : 2 ≤ n) (hp : p.natDegree ≤ n) (hs : p.Splits) :
    (p.binaryComp n a b c d).binaryDiscr n = (a * d - b * c) ^ (n * (n - 1)) * p.binaryDiscr n := by
  rcases (exists_isRootEnumeration_iff_splits (f := p) (L := K) (ι := Fin p.natDegree)
    (by rw [Fintype.card_fin, Algebra.algebraMap_self, map_id])).mpr
    (by rwa [Algebra.algebraMap_self, map_id]) with ⟨r, hr⟩
  have hr' : p.roots = univ.val.map r := by
    rw [← isRootEnumeration_iff.mp hr, Algebra.algebraMap_self, map_id]
  have hpr : p = C p.leadingCoeff * ∏ i, (X - C (r i)) := by
    conv_lhs => rw [hs.eq_prod_roots, hr', Multiset.map_map]
    rw [prod_eq_multiset_prod]
    rfl
  rcases Nat.exists_eq_add_of_le hp with ⟨k, hk⟩
  generalize p.leadingCoeff = l at hpr
  rw [hpr, hk]
  exact binaryDiscr_binaryComp_of_prod (hk ▸ hn) l r

/-- **The discriminant of a binary form under a linear substitution**: the discriminant of the
binary form of degree `n ≥ 2` of a polynomial `p`, under the substitution
`(x, z) ↦ (ax + bz, cx + dz)`, is multiplied by `(ad - bc)^(n(n - 1))`. -/
lemma binaryDiscr_binaryComp (hn : 2 ≤ n) (hp : p.natDegree ≤ n) :
    (p.binaryComp n a b c d).binaryDiscr n = (a * d - b * c) ^ (n * (n - 1)) * p.binaryDiscr n := by
  refine (algebraMap K (AlgebraicClosure K)).injective ?_
  rw [← binaryDiscr_map, binaryComp_map, map_mul, map_pow, ← binaryDiscr_map, map_sub, map_mul,
    map_mul]
  exact binaryDiscr_binaryComp_of_splits hn (natDegree_map_le.trans hp) (IsAlgClosed.splits _)

end Field

end Polynomial

namespace HyperellipticEquation

variable {g : ℕ} {K : Type*} [Field K]

section Field

variable (E : HyperellipticEquation g K) (a b c d e : K) {t : K[X]}

variable {E} in
lemma natDegree_h_changeOfVariables_le (ht : t.natDegree ≤ g + 1) :
    (C e⁻¹ * (E.h.binaryComp (g + 1) a b c d + C 2 * t)).natDegree ≤ g + 1 :=
  (natDegree_C_mul_le _ _).trans <| natDegree_add_le_of_degree_le (natDegree_binaryComp_le _) <|
    (natDegree_C_mul_le _ _).trans ht

variable {E} in
lemma natDegree_f_changeOfVariables_le (ht : t.natDegree ≤ g + 1) : (C (e⁻¹ ^ 2) *
    (E.f.binaryComp (2 * g + 2) a b c d - t ^ 2 - E.h.binaryComp (g + 1) a b c d * t)).natDegree ≤
    2 * g + 2 := by
  refine (natDegree_C_mul_le _ _).trans ?_
  have h₁ : (t ^ 2).natDegree ≤ 2 * g + 2 :=
    (natDegree_pow_le_of_le 2 ht).trans (by omega)
  have h₂ : (E.h.binaryComp (g + 1) a b c d * t).natDegree ≤ 2 * g + 2 :=
    (natDegree_mul_le_of_le (natDegree_binaryComp_le _) ht).trans (by omega)
  exact (natDegree_sub_le _ _).trans <| max_le ((natDegree_sub_le _ _).trans <|
    max_le (natDegree_binaryComp_le _) h₁) h₂

variable (t) (ht : t.natDegree ≤ g + 1)

/-- The **change of variables** `x = (aX + b) / (cX + d)`, `y = (eY + t(X)) / (cX + d)^(g + 1)`
(LMFDB `g2c.discriminant`) of a Weierstrass equation `y² + h(x)y = f(x)` of genus `g`, for `e ≠ 0`
and `t` of degree at most `g + 1`: the Weierstrass equation `Y² + h'(X)Y = f'(X)` with
`h' = (H + 2t) / e` and `f' = (F - t² - Ht) / e²`, where `H(X) = h(aX + b, cX + d)` and
`F(X) = f(aX + b, cX + d)` are the substituted binary forms of degrees `g + 1` and `2g + 2`. For
`ad - bc ≠ 0` and `e ≠ 0` the substitution is invertible, so that both equations define the same
curve (not formalised here). -/
noncomputable def changeOfVariables : HyperellipticEquation g K where
  h := C e⁻¹ * (E.h.binaryComp (g + 1) a b c d + C 2 * t)
  f := C (e⁻¹ ^ 2) * (E.f.binaryComp (2 * g + 2) a b c d - t ^ 2 -
    E.h.binaryComp (g + 1) a b c d * t)
  natDegree_h_le := natDegree_h_changeOfVariables_le a b c d e ht
  natDegree_f_le := natDegree_f_changeOfVariables_le a b c d e ht

/-- **The simplified polynomial under a change of variables**: `4f' + h'²` is `e⁻²` times the
binary form `(4f + h²)(aX + b, cX + d)` of degree `2g + 2`. -/
lemma simplifiedPolynomial_changeOfVariables :
    (E.changeOfVariables a b c d e t ht).simplifiedPolynomial =
      C (e⁻¹ ^ 2) * E.simplifiedPolynomial.binaryComp (2 * g + 2) a b c d := by
  have hg : 2 * g + 2 = g + 1 + (g + 1) := by
    ring1
  have hh : (E.h ^ 2).binaryComp (2 * g + 2) a b c d = E.h.binaryComp (g + 1) a b c d ^ 2 := by
    rw [sq, sq, hg, binaryComp_mul E.natDegree_h_le E.natDegree_h_le]
  rw [simplifiedPolynomial, simplifiedPolynomial, binaryComp_add, hh, ← map_ofNat C 4,
    binaryComp_C_mul]
  simp only [changeOfVariables, map_pow, map_ofNat]
  ring1

variable [Invertible (2 : K)]

lemma rhs_changeOfVariables : (E.changeOfVariables a b c d e t ht).rhs =
    C (e⁻¹ ^ 2) * E.rhs.binaryComp (2 * g + 2) a b c d := by
  have h4 : IsUnit (4 : K[X]) := by
    rw [← map_ofNat C 4]
    exact isUnit_C.mpr isUnit_four
  refine h4.mul_left_cancel ?_
  rw [four_mul_rhs, simplifiedPolynomial_changeOfVariables, ← four_mul_rhs, ← map_ofNat C 4,
    binaryComp_C_mul]
  ring1

variable {e} in
/-- **The discriminant under a change of variables** (LMFDB `g2c.discriminant`): the change of
variables `x = (aX + b) / (cX + d)`, `y = (eY + t(X)) / (cX + d)^(g + 1)` multiplies the
discriminant by `e^(-(8g + 4)) (ad - bc)^((2g + 2)(2g + 1))`, that is by `e⁻²⁰ (ad - bc)³⁰` in
genus two. -/
lemma discriminant_changeOfVariables (he : e ≠ 0) :
    (E.changeOfVariables a b c d e t ht).discriminant =
      e⁻¹ ^ (8 * g + 4) * (a * d - b * c) ^ ((2 * g + 2) * (2 * g + 1)) * E.discriminant := by
  have h₁ : 2 * (2 * (2 * g + 2) - 2) = 8 * g + 4 := by
    omega
  have h₂ : 2 * g + 2 - 1 = 2 * g + 1 := by
    omega
  rw [discriminant, discriminant, rhs_changeOfVariables,
    binaryDiscr_C_mul (by omega) (pow_ne_zero 2 (inv_ne_zero he)),
    binaryDiscr_binaryComp (by omega) E.natDegree_rhs_le, ← pow_mul, h₁, h₂]
  ring1

end Field

variable {E E' : HyperellipticEquation g ℤ}

/-- **Minimal equations related by a change of variables have the same discriminant** (LMFDB
`g2c.discriminant`): if two minimal equations of the same curve, with isomorphic function fields,
are related by a change of variables, the factor `e^(-(8g + 4)) (ad - bc)^((2g + 2)(2g + 1))`
relating their discriminants is a square, so it is `1` as the discriminants have the same absolute
value, and the discriminants are equal. That any two equations of the same curve are related by a
change of variables is not proved here, nor that a change of variables gives an isomorphic function
field. -/
lemma IsMinimal.discriminant_eq_of_changeOfVariables (hE : E.IsMinimal) (hE' : E'.IsMinimal)
    (eF : E'.toRat.FunctionField ≃ₐ[ℚ] E.toRat.FunctionField) {a b c d e : ℚ} (he : e ≠ 0)
    {t : ℚ[X]} (ht : t.natDegree ≤ g + 1)
    (hc : E'.toRat = E.toRat.changeOfVariables a b c d e t ht) :
    E.toRat.discriminant = E'.toRat.discriminant := by
  have hd : E'.toRat.discriminant =
      (e⁻¹ ^ (4 * g + 2) * (a * d - b * c) ^ ((g + 1) * (2 * g + 1))) ^ 2 *
          E.toRat.discriminant := by
    rw [hc, E.toRat.discriminant_changeOfVariables a b c d t ht he]
    ring1
  have h : |E.toRat.discriminant| = |E'.toRat.discriminant| := hE.abs_discriminant_eq hE' eF
  rw [hd, abs_mul, abs_sq] at h
  rw [hd, (mul_eq_right₀ (abs_ne_zero.mpr hE.discriminant_ne_zero)).mp h.symm, one_mul]

end HyperellipticEquation
