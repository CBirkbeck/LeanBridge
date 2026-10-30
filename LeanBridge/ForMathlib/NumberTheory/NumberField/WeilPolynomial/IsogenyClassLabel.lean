import Mathlib.Analysis.Complex.Polynomial.Basic
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Label.LMFDB
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial

/-!
# The LMFDB label of an isogeny class of abelian varieties over a finite field

The LMFDB labels the isogeny class of abelian varieties of dimension `g` over `𝔽_q` with Weil
polynomial `h` by `g.q.isog`, where `isog` lists the coefficients `a₁, …, a_g` of the L-polynomial
`1 + a₁x + ⋯ + a_g x^g + q a_{g-1} x^{g+1} + ⋯ + q^{g-1} a₁ x^{2g-1} + q^g x^{2g}`, the reverse of
`h` (LMFDB `av.fq.l-polynomial`): each is written in base `26` with the letters `a`, …, `z` as the
digits `0`, …, `25`, a negative number with a leading `a`, and they are separated by underscores,
so that `ae_j_ap` stands for `a₁ = -4`, `a₂ = 9`, `a₃ = -15`. The knowl calls this L-polynomial
the Weil `q`-polynomial of the isogeny class; the Weil polynomial (LMFDB `av.fq.weil_polynomial`)
is its reverse, the monic polynomial `x^{2g} + a₁ x^{2g-1} + ⋯ + q^g`, with the same `a₁, …, a_g`.

The Weil polynomial of an abelian variety is not available here, so, as in
`LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.FrobeniusOrder`, the label is defined
for a polynomial `h ∈ ℤ[x]`; it has its meaning when `h` is a Weil `q`-polynomial of degree `2g`
with constant term `q^g`, as the Weil polynomial of a `g`-dimensional abelian variety over `𝔽_q`
is. For such `h`, the functional equation `xⁿ h(q/x) = h(0) h(x)` of Weil polynomials gives the
L-polynomial the shape above, so that `a₁, …, a_g` determine `h`: the label determines the
isogeny class, by Tate's theorem that isogeny classes are determined by their Weil polynomials.

The LMFDB extends the label to endomorphism rings (`g.q.isog.N.i`), weak equivalence classes
(`g.q.isog.N.i.w`), Deligne modules (`g.q.isog.N.i.w.j`) and polarizations
(`g.q.isog.N.i.w.j.d.k`). Of their components, the index `N` of the endomorphism ring in the maximal
order of `ℚ[F]` is `Subalgebra.maximalOrderIndex`, and the degree `d` of a polarization would need
polarizations (LMFDB `av.polarization`), which are not available. The indices `i`, `w`, `j` and
`k` are enumerations of the LMFDB's database that the knowl does not define: these database
numberings are not formalised.

## Main definitions

* `Polynomial.weilCoeffLetters` (LMFDB `av.fq.lmfdb_label`): the letters encoding an integer.
* `Polynomial.weilLabelCoeffs` (LMFDB `av.fq.lmfdb_label`): the coefficients `a₁, …, a_g`.
* `Polynomial.isogenyClassLabel` (LMFDB `av.fq.lmfdb_label`): the label `g.q.isog`.

## Main results

* `WeierstrassCurve.isogenyClassLetters_injective` and `Polynomial.weilCoeffLetters_injective`: the
  letters determine the natural number, and the integer, that they encode.
* `Polynomial.IsWeilPolynomial.pow_mul_coeff`: the functional equation `q^k c_k = c_0 c_{n-k}` of
  the coefficients `c_k` of a Weil `q`-polynomial of degree `n`.
* `Polynomial.IsWeilPolynomial.coeff_reverse_add`: the L-polynomial of a Weil `q`-polynomial of
  degree `2g` with constant term `q^g` has the shape above.
* `Polynomial.IsWeilPolynomial.eq_of_weilLabelCoeffs_eq` and
  `Polynomial.IsWeilPolynomial.eq_of_isogenyClassLabel_eq`: the coefficients `a₁, …, a_g`, and so
  the label `g.q.isog`, determine such a Weil polynomial.
-/

open ComplexConjugate WeierstrassCurve

namespace WeierstrassCurve

lemma ofDigits_isogenyClassLetters (n : ℕ) :
    Nat.ofDigits 26 ((isogenyClassLetters n).toList.reverse.map (·.toNat - 'a'.toNat)) = n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rfl
  have hf : ∀ d : Fin 26, (Char.ofNat ('a'.toNat + d)).toNat - 'a'.toNat = d := by
    decide
  rw [isogenyClassLetters, ite_eq_right hn, String.toList_ofList, ← List.map_reverse,
    List.reverse_reverse, List.map_map]
  conv_rhs => rw [← Nat.ofDigits_digits 26 n]
  refine congr_arg _ <| (List.map_congr_left fun d hd ↦ ?_).trans (List.map_id _)
  exact hf ⟨d, Nat.digits_lt_base (by norm_num) hd⟩

/-- **The isogeny class letters determine the isogeny class index**: the base `26` encoding by the
letters `a`, …, `z` is injective. -/
lemma isogenyClassLetters_injective : Function.Injective isogenyClassLetters :=
  fun m n h ↦ by rw [← ofDigits_isogenyClassLetters m, h, ofDigits_isogenyClassLetters]

end WeierstrassCurve

namespace Polynomial

variable {q g : ℕ} {h h' : ℤ[X]}

/-- The **letters** (LMFDB `av.fq.lmfdb_label`) encoding an integer `a` in the label of an isogeny
class of abelian varieties over a finite field: `|a|` in base `26` with the letters `a`, …, `z` as
the digits `0`, …, `25` (`WeierstrassCurve.isogenyClassLetters`), preceded by an `a` when `a` is
negative, so that `-4`, `9` and `-15` are `ae`, `j` and `ap`. A positive number has no leading
digit `a`, so the letters determine `a` (`weilCoeffLetters_injective`). -/
def weilCoeffLetters (a : ℤ) : String :=
  (if a < 0 then "a" else "") ++ isogenyClassLetters a.natAbs

/-- **The letters of an integer determine it**: the leading `a` that marks a negative number is a
leading zero digit, which does not change the absolute value that the letters encode, so the
letters determine the absolute value, and then the sign. -/
lemma weilCoeffLetters_injective : Function.Injective weilCoeffLetters := by
  have hdec (x : ℤ) : Nat.ofDigits 26 ((weilCoeffLetters x).toList.reverse.map
      (·.toNat - 'a'.toNat)) = x.natAbs := by
    rw [weilCoeffLetters, String.toList_append, List.reverse_append, List.map_append,
      Nat.ofDigits_append, ofDigits_isogenyClassLetters]
    split_ifs <;> rfl
  intro a b hab
  have hn : a.natAbs = b.natAbs := by
    rw [← hdec a, hab, hdec b]
  rw [weilCoeffLetters, weilCoeffLetters, hn, String.append_left_inj] at hab
  split_ifs at hab <;> grind

variable (h) in
/-- The **label coefficients** `a₁, …, a_g` (LMFDB `av.fq.lmfdb_label`) of a polynomial `h ∈ ℤ[x]`
of degree `2g`: the coefficients of `x, …, x^g` in its reverse. For the Weil polynomial `h` of an
isogeny class of abelian varieties over `𝔽_q`, the reverse is the L-polynomial
`1 + a₁x + ⋯ + a_g x^g + q a_{g-1} x^{g+1} + ⋯ + q^g x^{2g}` (LMFDB `av.fq.l-polynomial`),
and they determine `h` (`IsWeilPolynomial.eq_of_weilLabelCoeffs_eq`). -/
noncomputable def weilLabelCoeffs : List ℤ :=
  (List.range (h.natDegree / 2)).map fun i ↦ h.reverse.coeff (i + 1)

variable (q h) in
/-- The **LMFDB label** `g.q.isog` (LMFDB `av.fq.lmfdb_label`) of the isogeny class of abelian
varieties over `𝔽_q` with Weil polynomial `h`: the dimension `g`, half the degree of `h`, the field
size `q`, and `isog`, the label coefficients `a₁, …, a_g` (`weilLabelCoeffs`) written with
`weilCoeffLetters` and separated by underscores, as in `3.5.ae_j_ap`. The LMFDB's `h` is the Weil
polynomial of an isogeny class (LMFDB `av.fq.weil_polynomial`); here `h` is any polynomial, and
the label has its meaning when `h` is a Weil `q`-polynomial of degree `2g` with constant term `q^g`,
which it then determines (`IsWeilPolynomial.eq_of_isogenyClassLabel_eq`). -/
noncomputable def isogenyClassLabel : String :=
  toString (h.natDegree / 2) ++ "." ++ toString q ++ "." ++
    "_".intercalate (h.weilLabelCoeffs.map weilCoeffLetters)

namespace IsWeilPolynomial

lemma pow_natDegree_mul_eval_div (hh : h.IsWeilPolynomial q) {x : ℂ} (hx : x ≠ 0) :
    x ^ h.natDegree * (h.map (Int.castRingHom ℂ)).eval (q / x) =
    h.coeff 0 * (h.map (Int.castRingHom ℂ)).eval x := by
  have hs : (h.map (Int.castRingHom ℂ)).Splits := IsAlgClosed.splits _
  have hm : (h.map (Int.castRingHom ℂ)).Monic := hh.1.map _
  have hn : (h.map (Int.castRingHom ℂ)).roots.card = h.natDegree := by
    rw [← hs.natDegree_eq_card_roots, hh.1.natDegree_map]
  have hα : ∀ α ∈ (h.map (Int.castRingHom ℂ)).roots, x * (q / x - α) = -α * (x - conj α) := by
    intro α hα
    have hq : α * conj α = q := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hh.2 α hα, Real.sq_sqrt (Nat.cast_nonneg q),
        Complex.ofReal_natCast]
    rw [mul_sub, mul_div_cancel₀ _ hx, neg_mul, mul_sub, hq]
    ring1
  have h0 : ((h.map (Int.castRingHom ℂ)).roots.map Neg.neg).prod = h.coeff 0 := by
    rw [Multiset.prod_map_neg, hn, ← hh.1.natDegree_map (Int.castRingHom ℂ),
      ← hs.coeff_zero_eq_prod_roots_of_monic hm, coeff_map, eq_intCast]
  have hconj :
      (h.map (Int.castRingHom ℂ)).eval (conj x) = conj ((h.map (Int.castRingHom ℂ)).eval x) := by
    rw [eval_map, eval_map, hom_eval₂, RingHom.ext_int ((starRingEnd ℂ).comp (Int.castRingHom ℂ))
      (Int.castRingHom ℂ)]
  have hc : ((h.map (Int.castRingHom ℂ)).roots.map fun α ↦ x - conj α).prod =
      (h.map (Int.castRingHom ℂ)).eval x := by
    rw [← Complex.conj_conj ((h.map (Int.castRingHom ℂ)).eval x), ← hconj,
      hs.eval_eq_prod_roots_of_monic hm, map_multiset_prod, Multiset.map_map]
    simp
  rw [hs.eval_eq_prod_roots_of_monic hm (q / x), ← hn, ← Multiset.prod_replicate,
    ← Multiset.map_const', ← Multiset.prod_map_mul, Multiset.map_congr rfl hα,
    Multiset.prod_map_mul, h0, hc]

lemma reflect_comp_C_mul_X (hh : h.IsWeilPolynomial q) :
    ((h.map (Int.castRingHom ℂ)).comp (C (q : ℂ) * X)).reflect h.natDegree =
    C (h.coeff 0 : ℂ) * h.map (Int.castRingHom ℂ) := by
  refine eq_of_infinite_eval_eq _ _ ((Set.finite_singleton 0).infinite_compl.mono fun x hx ↦ ?_)
  let i : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
  have hd : ((h.map (Int.castRingHom ℂ)).comp (C (q : ℂ) * X)).natDegree ≤ h.natDegree := by
    refine natDegree_comp_le.trans ?_
    rw [hh.1.natDegree_map]
    exact mul_le_of_le_one_right' (natDegree_C_mul_le _ _ |>.trans natDegree_X_le)
  have h₁ : (((h.map (Int.castRingHom ℂ)).comp (C (q : ℂ) * X)).reflect h.natDegree).eval x *
      x⁻¹ ^ h.natDegree = (h.map (Int.castRingHom ℂ)).eval (q / x) := by
    simpa only [invOf_eq_inv, inv_inv, eval₂_id, eval_comp, eval_mul, eval_C, eval_X,
      div_eq_mul_inv] using eval₂_reflect_mul_pow (RingHom.id ℂ) x⁻¹ h.natDegree _ hd
  rw [Set.mem_ofPred_eq, eval_mul, eval_C, ← hh.pow_natDegree_mul_eval_div hx, ← h₁, mul_left_comm,
    ← mul_pow, mul_inv_cancel₀ hx, one_pow, mul_one]

/-- **Functional equation of a Weil polynomial**: the coefficients `c_k` of a Weil `q`-polynomial
`h` of degree `n` satisfy `q^k c_k = c_0 c_{n-k}`, as `xⁿ h(q/x) = h(0) h(x)`: on the complex
roots of `h`, which have absolute value `√q`, the map `α ↦ q/α` is complex conjugation. -/
lemma pow_mul_coeff (hh : h.IsWeilPolynomial q) {k : ℕ} (hk : k ≤ h.natDegree) :
    q ^ k * h.coeff k = h.coeff 0 * h.coeff (h.natDegree - k) := by
  have h₁ : (h.coeff k : ℂ) * q ^ k = h.coeff 0 * h.coeff (h.natDegree - k) := by
    simpa only [coeff_reflect, revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hk, comp_C_mul_X_coeff,
      coeff_C_mul, coeff_map, eq_intCast] using
      congr_arg (coeff · (h.natDegree - k)) hh.reflect_comp_C_mul_X
  exact_mod_cast (mul_comm _ _).trans h₁

/-- **The L-polynomial of a Weil polynomial has the LMFDB's shape**: for a Weil `q`-polynomial `h`
of degree `2g` with constant term `q^g`, `q ≠ 0`, the coefficients `L_k` of its reverse, the
L-polynomial, satisfy `L_{g+j} = q^j L_{g-j}`, so that it is
`1 + a₁x + ⋯ + a_g x^g + q a_{g-1} x^{g+1} + ⋯ + q^{g-1} a₁ x^{2g-1} + q^g x^{2g}`. -/
lemma coeff_reverse_add (hh : h.IsWeilPolynomial q) (hq : q ≠ 0) (hn : h.natDegree = 2 * g)
    (h0 : h.coeff 0 = q ^ g) {j : ℕ} (hj : j ≤ g) :
    h.reverse.coeff (g + j) = q ^ j * h.reverse.coeff (g - j) := by
  have hg : 2 * g - (g - j) = g + j := by
    omega
  have h₁ : (q : ℤ) ^ (g - j) * h.coeff (g - j) = q ^ g * h.coeff (g + j) := by
    rw [hh.pow_mul_coeff (by omega), h0, hn, hg]
  rw [coeff_reverse, coeff_reverse, revAt_le (by omega), revAt_le (by omega), hn,
    (by omega : 2 * g - (g + j) = g - j), hg]
  refine mul_left_cancel₀ (pow_ne_zero (g - j) (Nat.cast_ne_zero.mpr hq)) ?_
  rw [h₁, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hj]

/-- **The label coefficients determine the Weil polynomial**: two Weil `q`-polynomials of degree
`2g` with constant term `q^g`, `q ≠ 0`, such as the Weil polynomials of two isogeny classes of
`g`-dimensional abelian varieties over `𝔽_q`, are equal if they have the same label coefficients
`a₁, …, a_g`. -/
lemma eq_of_weilLabelCoeffs_eq (hh : h.IsWeilPolynomial q) (hh' : h'.IsWeilPolynomial q)
    (hq : q ≠ 0) (hn : h.natDegree = 2 * g) (hn' : h'.natDegree = 2 * g) (h0 : h.coeff 0 = q ^ g)
    (h0' : h'.coeff 0 = q ^ g) (ha : h.weilLabelCoeffs = h'.weilLabelCoeffs) : h = h' := by
  have h₁ : ∀ i ≤ g, h.reverse.coeff i = h'.reverse.coeff i := by
    rintro (_ | i) hi
    · rw [coeff_zero_reverse, coeff_zero_reverse, hh.1.leadingCoeff, hh'.1.leadingCoeff]
    rw [weilLabelCoeffs, weilLabelCoeffs, hn, hn', List.map_inj_left] at ha
    exact ha i (List.mem_range.mpr (by omega))
  have h₂ : h.reverse = h'.reverse := by
    ext i
    rcases le_or_gt i g with hi | hi
    · exact h₁ i hi
    rcases le_or_gt i (2 * g) with hi' | hi'
    · rw [(by omega : i = g + (i - g)), hh.coeff_reverse_add hq hn h0 (by omega),
        hh'.coeff_reverse_add hq hn' h0' (by omega), h₁ _ (Nat.sub_le _ _)]
    · rw [coeff_eq_zero_of_natDegree_lt ((reverse_natDegree_le h).trans_lt (hn ▸ hi')),
        coeff_eq_zero_of_natDegree_lt ((reverse_natDegree_le h').trans_lt (hn' ▸ hi'))]
  rw [reverse, reverse, hn, hn'] at h₂
  simpa using congr_arg (reflect (2 * g)) h₂

/-- **The label determines the Weil polynomial**: two Weil `q`-polynomials of degree `2g` with
constant term `q^g`, `q ≠ 0`, such as the Weil polynomials of two isogeny classes of
`g`-dimensional abelian varieties over `𝔽_q`, are equal if they have the same label `g.q.isog`. -/
lemma eq_of_isogenyClassLabel_eq (hh : h.IsWeilPolynomial q) (hh' : h'.IsWeilPolynomial q)
    (hq : q ≠ 0) (hn : h.natDegree = 2 * g) (hn' : h'.natDegree = 2 * g) (h0 : h.coeff 0 = q ^ g)
    (h0' : h'.coeff 0 = q ^ g) (hl : h.isogenyClassLabel q = h'.isogenyClassLabel q) : h = h' := by
  refine hh.eq_of_weilLabelCoeffs_eq hh' hq hn hn' h0 h0' ?_
  rcases eq_or_ne g 0 with rfl | hg
  · rw [weilLabelCoeffs, weilLabelCoeffs, hn, hn']
    rfl
  have hf : ∀ d : Fin 26, Char.ofNat ('a'.toNat + d) ≠ '_' := by
    decide
  have hu (a : ℤ) : '_' ∉ (weilCoeffLetters a).toList := by
    rw [weilCoeffLetters, String.toList_append, List.mem_append, not_or]
    refine ⟨by split_ifs <;> decide, ?_⟩
    rw [isogenyClassLetters]
    split_ifs
    · decide
    rw [String.toList_ofList, List.mem_map, not_exists]
    rintro d ⟨hd, hd'⟩
    exact hf ⟨d, Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp hd)⟩ hd'
  have hs (p : ℤ[X]) (hp : p.natDegree = 2 * g) :
      ("_".intercalate (p.weilLabelCoeffs.map weilCoeffLetters)).toList.splitOn '_' =
      (p.weilLabelCoeffs.map weilCoeffLetters).map String.toList := by
    rw [String.toList_intercalate]
    refine List.splitOn_intercalate '_' ?_ ?_
    · simp only [List.map_map, List.mem_map]
      rintro _ ⟨a, -, rfl⟩
      exact hu a
    · simp [weilLabelCoeffs, hp, hg]
  rw [isogenyClassLabel, isogenyClassLabel, hn, hn', String.append_right_inj] at hl
  have h₁ : (h.weilLabelCoeffs.map weilCoeffLetters).map String.toList =
      (h'.weilLabelCoeffs.map weilCoeffLetters).map String.toList := by
    rw [← hs h hn, hl, hs h' hn']
  rw [List.map_map, List.map_map] at h₁
  exact (List.map_inj_right fun a b hab ↦ weilCoeffLetters_injective (String.ext hab)).mp h₁

end IsWeilPolynomial

end Polynomial
