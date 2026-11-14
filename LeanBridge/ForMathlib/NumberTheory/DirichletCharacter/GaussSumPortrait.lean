import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.QuadraticGaussSum
import LeanBridge.ForMathlib.NumberTheory.MulChar.Order
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import TauCeti.NumberTheory.DirichletCharacter.GaussSum

/-!
# The Gauss sum portrait of a Dirichlet character

The LMFDB draws a Dirichlet character `χ` of modulus `N` through its partial Gauss sums
`S_a(k) = ∑_{n = 1}^{k} χ(n) e^{2πian/N}`, for the residues `a` modulo `N` (LMFDB
`portrait.character.dirichlet`). This file proves the mathematical statements of that knowl.

* The complete Gauss sum `τ_a(χ) = ∑_{r ∈ ℤ/Nℤ} χ(r) e^{2πiar/N}` (Mathlib's
  `gaussSum χ (ZMod.stdAddChar.mulShift a)`) is `S_a(N)`, which is `S_a(N - 1)` for `N > 1`. The
  knowl's `τ_a(χ) = S_a(N - 1)` fails for `N = 1`, where `S_0(0) = 0` but `τ_0 = 1`.
* A stage `k` not coprime to `N` repeats the previous one, as `χ(k) = 0`. For `N > 1` there are
  `φ(N)` stages `k ∈ [1, N - 1]` coprime to `N`, so the portrait has `N φ(N)` segments.
* If `χ` is primitive, then `|τ_a(χ)| = √N` for `a` coprime to `N` and `τ_a(χ) = 0` otherwise, so
  exactly `φ(N)` of the complete Gauss sums lie on the circle of radius `√N`. Conversely, if
  `|τ_a(χ)| = √N` for one `a` coprime to `N`, then `χ` is primitive; an imprimitive character has
  `|τ_a(χ)| < √N` for every `a` coprime to `N`.
* For `a` coprime to `N`, `τ_a(χ) = χ̄(a) τ_1(χ)`, so the complete Gauss sums at the units are the
  points `τ_1(χ) ζ`, `ζ` an `n`-th root of unity, `n` the order of `χ`: the vertices
  `τ_1(χ) e^{2πik/n}` of a regular `n`-gon. When `χ` is primitive, they are `n` distinct points,
  and they are the complete Gauss sums on the circle of radius `√N`.
* `S_{-a}(k)` is the complex conjugate of `S_a(k)` when `χ` is real, so the points `S_a(k)` of a
  real character are symmetric about the real axis.
* For the principal character, `S_0(k)` is the number of integers in `[1, k]` coprime to `N`, and
  `S_0(N) = τ_0 = φ(N)`.

The converse for imprimitive characters rests on Parseval's identity
`∑_a |τ_a(χ)|² = N φ(N)` and on a nonzero Gauss sum at a non-unit: if `χ` is induced by the
primitive character `ψ` of modulus `d < N`, then `τ_{N/d}(χ)` is a positive multiple of `τ(ψ) ≠ 0`.
That the Gauss sum of a primitive character does not vanish is, for any primitive additive
character, `DirichletCharacter.gaussSum_ne_zero_of_isPrimitive` on Tau Ceti's main, which is not at
its pin; the case of the standard additive character is proved here and should be replaced by it
after the bump.

## Main definitions

* `DirichletCharacter.partialGaussSum` (LMFDB `portrait.character.dirichlet`): the partial Gauss
  sum `S_a(k)`.

## Main results

* `ZMod.card_univ_product_filter_coprime`: for `N > 1`, the portrait has `N φ(N)` segments.
* `DirichletCharacter.partialGaussSum_modulus` (LMFDB `portrait.character.dirichlet`):
  `S_a(N) = τ_a(χ)`.
* `DirichletCharacter.partialGaussSum_modulus_sub_one`: `S_a(N - 1) = τ_a(χ)` for `N > 1`.
* `DirichletCharacter.partialGaussSum_modOne_sub_one_ne`: `S_a(N - 1) ≠ τ_a(χ)` for `N = 1`.
* `DirichletCharacter.partialGaussSum_succ_of_not_coprime`: a stage not coprime to `N` repeats the
  previous one.
* `DirichletCharacter.partialGaussSum_neg`: `S_{-a}(k) = conj (S_a(k))` for a real character.
* `DirichletCharacter.image_conj_range_partialGaussSum`: the points `S_a(k)` of a real character
  are symmetric about the real axis.
* `DirichletCharacter.partialGaussSum_one_zero`: for the principal character, `S_0(k)` counts the
  integers in `[1, k]` coprime to `N`.
* `DirichletCharacter.gaussSum_one_mulShift_zero`: for the principal character, `τ_0 = φ(N)`.
* `DirichletCharacter.partialGaussSum_one_zero_modulus`: for the principal character,
  `S_0(N) = φ(N)`.
* `DirichletCharacter.gaussSum_mulShift_unit`: `τ_a(χ) = χ̄(a) τ_1(χ)` for `a` coprime to `N`.
* `DirichletCharacter.norm_gaussSum_mulShift_of_isPrimitive` (LMFDB
  `portrait.character.dirichlet`): `|τ_a(χ)| = √N` for primitive `χ` and `a` coprime to `N`.
* `DirichletCharacter.gaussSum_mulShift_eq_zero_of_isPrimitive`: `τ_a(χ) = 0` for primitive `χ`
  and `a` not coprime to `N`.
* `DirichletCharacter.ncard_setOf_norm_gaussSum_mulShift_eq_sqrt_of_isPrimitive`: for primitive
  `χ`, exactly `φ(N)` of the `τ_a(χ)` lie on the circle of radius `√N`.
* `DirichletCharacter.range_gaussSum_mulShift_units`: the complete Gauss sums at the units are the
  points `τ_1(χ) ζ`, `ζ` an `n`-th root of unity, `n` the order of `χ`.
* `DirichletCharacter.range_gaussSum_mulShift_units_eq_image_exp`: they are the points
  `τ_1(χ) e^{2πik/n}`, `0 ≤ k < n`.
* `DirichletCharacter.image_setOf_norm_gaussSum_mulShift_eq_sqrt_of_isPrimitive` (LMFDB
  `portrait.character.dirichlet`): for primitive `χ`, the complete Gauss sums on the circle of
  radius `√N` are these points.
* `DirichletCharacter.ncard_range_gaussSum_mulShift_units_of_isPrimitive`: for primitive `χ`, there
  are `n` of them.
* `DirichletCharacter.sum_norm_sq_gaussSum_mulShift`: Parseval's identity
  `∑_a |τ_a(χ)|² = N φ(N)`.
* `DirichletCharacter.isPrimitive_iff_forall_norm_gaussSum_mulShift_eq_sqrt` (LMFDB
  `portrait.character.dirichlet`): `χ` is primitive if and only if `|τ_a(χ)| = √N` for every `a`
  coprime to `N`.
* `DirichletCharacter.norm_gaussSum_mulShift_lt_sqrt_of_not_isPrimitive`: for imprimitive `χ`,
  `|τ_a(χ)| < √N` for every `a` coprime to `N`.
-/

open AddChar ComplexConjugate Finset ZMod

variable {N : ℕ} [NeZero N]

namespace ZMod

/-- **The number of segments of the portrait**: for `N > 1`, there are `N φ(N)` pairs of a residue
`a` modulo `N` and a stage `k ∈ [1, N - 1]` coprime to `N`. -/
lemma card_univ_product_filter_coprime (hN : 1 < N) :
    #((univ : Finset (ZMod N)) ×ˢ {k ∈ Icc 1 (N - 1) | k.Coprime N}) = N * N.totient := by
  have h : {k ∈ Icc 1 (N - 1) | k.Coprime N} = {k ∈ range N | N.Coprime k} := by
    refine Finset.ext fun k ↦ ?_
    rw [mem_filter, mem_filter, mem_Icc, mem_range, Nat.coprime_comm]
    refine ⟨fun h ↦ ⟨by omega, h.2⟩, fun h ↦ ⟨⟨Nat.pos_of_ne_zero ?_, by omega⟩, h.2⟩⟩
    rintro rfl
    exact hN.ne' <| (Nat.coprime_zero_right N).mp h.2
  rw [card_product, card_univ, ZMod.card, h, ← Nat.totient_eq_card_coprime]

end ZMod

namespace DirichletCharacter

variable (χ : DirichletCharacter ℂ N) (a : ZMod N) (k : ℕ) (u : (ZMod N)ˣ)
  (ψ : DirichletCharacter ℂ 1) (b : ZMod 1)

/-- The **partial Gauss sum** `S_a(k) = ∑_{n = 1}^{k} χ(n) e^{2πian/N}` (LMFDB
`portrait.character.dirichlet`) of a Dirichlet character `χ` of modulus `N`, at a residue `a`
modulo `N`. -/
noncomputable def partialGaussSum : ℂ :=
  ∑ n ∈ Icc 1 k, χ n * stdAddChar (a * (n : ZMod N))

lemma partialGaussSum_natCast (m : ℕ) : χ.partialGaussSum m k =
    ∑ n ∈ Icc 1 k, χ n * Complex.exp (2 * Real.pi * Complex.I * m * n / N) := by
  refine sum_congr rfl fun n _ ↦ ?_
  rw [stdAddChar_apply, ← Nat.cast_mul, toCircle_natCast, Nat.cast_mul, mul_assoc _ (m : ℂ)]

lemma partialGaussSum_zero : χ.partialGaussSum a 0 = 0 := by
  simp [partialGaussSum]

/-- **The complete Gauss sum is the partial Gauss sum at `N`**: `S_a(N) = τ_a(χ)`. -/
lemma partialGaussSum_modulus : χ.partialGaussSum a N = gaussSum χ (stdAddChar.mulShift a) := by
  rw [partialGaussSum, sum_Icc_one_natCast fun x ↦ χ x * stdAddChar (a * x), gaussSum]
  rfl

lemma partialGaussSum_succ : χ.partialGaussSum a (k + 1) = χ.partialGaussSum a k +
    χ (k + 1 : ℕ) * stdAddChar (a * ((k + 1 : ℕ) : ZMod N)) :=
  sum_Icc_succ_top (Nat.le_add_left 1 k) _

variable {k} in
/-- **A stage `k + 1` not coprime to `N` repeats the previous one**: `χ(k + 1) = 0`, so
`S_a(k + 1) = S_a(k)`. -/
lemma partialGaussSum_succ_of_not_coprime (hk : ¬(k + 1).Coprime N) :
    χ.partialGaussSum a (k + 1) = χ.partialGaussSum a k := by
  rw [partialGaussSum_succ, χ.map_nonunit <| (isUnit_iff_coprime _ _).not.mpr hk, zero_mul,
    add_zero]

/-- **For `N > 1`, the complete Gauss sum is the partial Gauss sum at `N - 1`**:
`S_a(N - 1) = τ_a(χ)`, as `χ(N) = 0`. -/
lemma partialGaussSum_modulus_sub_one (hN : 1 < N) :
    χ.partialGaussSum a (N - 1) = gaussSum χ (stdAddChar.mulShift a) := by
  have hk : ¬(N - 1 + 1).Coprime N := by
    rw [Nat.sub_add_cancel hN.le, Nat.coprime_self]
    exact hN.ne'
  rw [← χ.partialGaussSum_succ_of_not_coprime a hk, Nat.sub_add_cancel hN.le,
    partialGaussSum_modulus]

lemma gaussSum_mulShift_modOne : gaussSum ψ (stdAddChar.mulShift b) = 1 := by
  rw [gaussSum, Fintype.sum_subsingleton _ (1 : ZMod 1), map_one, mulShift_apply,
    Subsingleton.elim (b * 1) 0, map_zero_eq_one, mul_one]

/-- **For `N = 1`, the complete Gauss sum is not the partial Gauss sum at `N - 1`**: the character
of modulus `1` has `S_0(0) = 0` and `τ_0 = 1`, so the equation `τ_a(χ) = S_a(N - 1)` of LMFDB
`portrait.character.dirichlet` needs `N > 1`. -/
lemma partialGaussSum_modOne_sub_one_ne :
    ψ.partialGaussSum b (1 - 1) ≠ gaussSum ψ (stdAddChar.mulShift b) := by
  rw [gaussSum_mulShift_modOne, Nat.sub_self, partialGaussSum_zero]
  exact zero_ne_one

/-- **The partial Gauss sums of a real character at `-a` are the complex conjugates of those at
`a`**: `S_{-a}(k) = conj (S_a(k))` if the values of `χ` are real. -/
lemma partialGaussSum_neg (hχ : ∀ x, conj (χ x) = χ x) :
    χ.partialGaussSum (-a) k = conj (χ.partialGaussSum a k) := by
  simp only [partialGaussSum, map_sum]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [map_mul (starRingEnd ℂ), hχ, neg_mul, map_neg_eq_conj]

lemma partialGaussSum_neg_of_isQuadratic (hχ : χ.IsQuadratic) :
    χ.partialGaussSum (-a) k = conj (χ.partialGaussSum a k) :=
  χ.partialGaussSum_neg a k fun x ↦ by rcases hχ x with h | h | h <;> simp [h]

/-- **The portrait of a real character is symmetric about the real axis**: at each stage `k`, the
set of the points `S_a(k)` is stable under complex conjugation. -/
lemma image_conj_range_partialGaussSum (hχ : ∀ x, conj (χ x) = χ x) :
    conj '' Set.range (χ.partialGaussSum · k) = Set.range (χ.partialGaussSum · k) := by
  refine Set.ext fun z ↦ ⟨?_, ?_⟩
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    exact ⟨-b, χ.partialGaussSum_neg b k hχ⟩
  · rintro ⟨b, rfl⟩
    exact ⟨_, ⟨-b, rfl⟩,
      (congrArg conj <| χ.partialGaussSum_neg b k hχ).trans <| Complex.conj_conj _⟩

/-- **For the principal character, `S_0(k)` counts the integers in `[1, k]` coprime to `N`.** -/
lemma partialGaussSum_one_zero :
    (1 : DirichletCharacter ℂ N).partialGaussSum 0 k = #{n ∈ Icc 1 k | n.Coprime N} := by
  rw [partialGaussSum, natCast_card_filter]
  refine sum_congr rfl fun n _ ↦ ?_
  split_ifs with h
  · rw [zero_mul, map_zero_eq_one, mul_one, MulChar.one_apply ((isUnit_iff_coprime n N).mpr h)]
  · rw [MulChar.map_nonunit _ ((isUnit_iff_coprime n N).not.mpr h), zero_mul]

/-- **For the principal character, the complete Gauss sum at `0` is `φ(N)`.** -/
lemma gaussSum_one_mulShift_zero :
    gaussSum (1 : DirichletCharacter ℂ N) (stdAddChar.mulShift 0) = N.totient := by
  rw [mulShift_zero, gaussSum_one_one, Nat.card_eq_fintype_card, card_units_eq_totient]

/-- **For the principal character, `S_0(N) = φ(N)`**: the partial Gauss sums at `0` grow along the
positive real axis up to `φ(N)`. -/
lemma partialGaussSum_one_zero_modulus :
    (1 : DirichletCharacter ℂ N).partialGaussSum 0 N = N.totient := by
  rw [partialGaussSum_modulus, gaussSum_one_mulShift_zero]

/-- **For `a` coprime to `N`, `τ_a(χ) = χ̄(a) τ_1(χ)`.** -/
lemma gaussSum_mulShift_unit :
    gaussSum χ (stdAddChar.mulShift (u : ZMod N)) = conj (χ u) * gaussSum χ stdAddChar := by
  rw [gaussSum_mulShift_eq, ← MulChar.star_apply', Complex.star_def]

lemma norm_gaussSum_mulShift_unit :
    ‖gaussSum χ (stdAddChar.mulShift (u : ZMod N))‖ = ‖gaussSum χ stdAddChar‖ := by
  rw [gaussSum_mulShift_unit, norm_mul, Complex.norm_conj, χ.unit_norm_eq_one, one_mul]

lemma gaussSum_mul_conj_of_isPrimitive (hχ : χ.IsPrimitive) :
    gaussSum χ stdAddChar * conj (gaussSum χ stdAddChar) = N := by
  rw [← Complex.star_def, star_gaussSum_eq,
    gaussSum_mul_gaussSum_inv_eq_card_of_isPrimitive hχ (isPrimitive_stdAddChar N), ZMod.card]

lemma gaussSum_stdAddChar_ne_zero_of_isPrimitive (hχ : χ.IsPrimitive) : gaussSum χ stdAddChar ≠ 0 :=
  left_ne_zero_of_mul <| (χ.gaussSum_mul_conj_of_isPrimitive hχ).trans_ne <|
    Nat.cast_ne_zero.mpr <| NeZero.ne N

lemma norm_gaussSum_of_isPrimitive (hχ : χ.IsPrimitive) : ‖gaussSum χ stdAddChar‖ = √N := by
  have h : ‖gaussSum χ stdAddChar‖ ^ 2 = N := by
    have h' : gaussSum χ stdAddChar * conj (gaussSum χ stdAddChar) = N :=
      χ.gaussSum_mul_conj_of_isPrimitive hχ
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h'
    exact_mod_cast h'
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

variable {a} in
/-- **If `χ` is primitive, then `|τ_a(χ)| = √N` for every `a` coprime to `N`.** -/
lemma norm_gaussSum_mulShift_of_isPrimitive (hχ : χ.IsPrimitive) (ha : IsUnit a) :
    ‖gaussSum χ (stdAddChar.mulShift a)‖ = √N := by
  rw [← ha.unit_spec, norm_gaussSum_mulShift_unit, χ.norm_gaussSum_of_isPrimitive hχ]

variable {a} in
/-- **If `χ` is primitive, then `τ_a(χ) = 0` for every `a` not coprime to `N`.** -/
lemma gaussSum_mulShift_eq_zero_of_isPrimitive (hχ : χ.IsPrimitive) (ha : ¬IsUnit a) :
    gaussSum χ (stdAddChar.mulShift a) = 0 := by
  rw [gaussSum_mulShift_of_isPrimitive _ hχ, MulChar.map_nonunit _ ha, zero_mul]

variable {a} in
lemma norm_gaussSum_mulShift_eq_sqrt_iff_of_isPrimitive (hχ : χ.IsPrimitive) :
    ‖gaussSum χ (stdAddChar.mulShift a)‖ = √N ↔ IsUnit a := by
  refine ⟨fun h ↦ ?_, χ.norm_gaussSum_mulShift_of_isPrimitive hχ⟩
  by_contra ha
  rw [χ.gaussSum_mulShift_eq_zero_of_isPrimitive hχ ha, norm_zero] at h
  exact (Real.sqrt_pos.mpr <| Nat.cast_pos.mpr <| NeZero.pos N).ne h

lemma setOf_norm_gaussSum_mulShift_eq_sqrt_of_isPrimitive (hχ : χ.IsPrimitive) :
    {a : ZMod N | ‖gaussSum χ (stdAddChar.mulShift a)‖ = √N} =
      Set.range ((↑) : (ZMod N)ˣ → ZMod N) :=
  Set.ext fun _ ↦ χ.norm_gaussSum_mulShift_eq_sqrt_iff_of_isPrimitive hχ

/-- **The portrait of a primitive character has `φ(N)` dots on the circle**: exactly `φ(N)` of
the complete Gauss sums `τ_a(χ)` have absolute value `√N`, those with `a` coprime to `N`. -/
lemma ncard_setOf_norm_gaussSum_mulShift_eq_sqrt_of_isPrimitive (hχ : χ.IsPrimitive) :
    {a : ZMod N | ‖gaussSum χ (stdAddChar.mulShift a)‖ = √N}.ncard = N.totient := by
  rw [χ.setOf_norm_gaussSum_mulShift_eq_sqrt_of_isPrimitive hχ,
    Set.ncard_range_of_injective Units.val_injective, Nat.card_eq_fintype_card,
    card_units_eq_totient]

/-- **The complete Gauss sums at the units are the points `τ_1(χ) ζ`, `ζ` an `n`-th root of unity,
`n` the order of `χ`**: the vertices of a regular `n`-gon centred at `0`. -/
lemma range_gaussSum_mulShift_units :
    Set.range (fun u : (ZMod N)ˣ ↦ gaussSum χ (stdAddChar.mulShift (u : ZMod N))) =
      (gaussSum χ stdAddChar * ·) '' ((↑) '' (rootsOfUnity (orderOf χ) ℂ : Set ℂˣ)) := by
  rw [← orderOf_inv, ← χ⁻¹.range_toUnitHom_eq_rootsOfUnity, MonoidHom.coe_range,
    ← Set.range_comp, ← Set.range_comp]
  refine congrArg Set.range <| funext fun u ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, MulChar.coe_toUnitHom, ← MulChar.star_apply',
    Complex.star_def, mul_comm, gaussSum_mulShift_unit]

/-- **The complete Gauss sums at the units are the vertices `τ_1(χ) e^{2πik/n}`, `0 ≤ k < n`, of a
regular `n`-gon centred at `0`**, `n` the order of `χ`. -/
lemma range_gaussSum_mulShift_units_eq_image_exp :
    Set.range (fun u : (ZMod N)ˣ ↦ gaussSum χ (stdAddChar.mulShift (u : ZMod N))) =
      (fun k : ℕ ↦ gaussSum χ stdAddChar *
          Complex.exp (2 * Real.pi * Complex.I * (k / orderOf χ))) '' Set.Iio (orderOf χ) := by
  have : NeZero (orderOf χ) := ⟨χ.orderOf_pos.ne'⟩
  rw [range_gaussSum_mulShift_units]
  refine Set.ext fun z ↦ ⟨?_, ?_⟩
  · rintro ⟨_, ⟨ζ, hζ, rfl⟩, rfl⟩
    rcases (Complex.mem_rootsOfUnity _ ζ).mp hζ with ⟨k, hk, hk'⟩
    exact ⟨k, hk, congrArg _ hk'⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨Units.mk0 _ (Complex.exp_ne_zero _),
      (Complex.mem_rootsOfUnity _ _).mpr ⟨k, hk, rfl⟩, rfl⟩, rfl⟩

/-- **The dots on the circle of a primitive character are the vertices of a regular `n`-gon**, `n`
the order of `χ`: the complete Gauss sums `τ_a(χ)` of absolute value `√N` are the points
`τ_1(χ) e^{2πik/n}`, `0 ≤ k < n`. -/
lemma image_setOf_norm_gaussSum_mulShift_eq_sqrt_of_isPrimitive (hχ : χ.IsPrimitive) :
    (fun a ↦ gaussSum χ (stdAddChar.mulShift a)) ''
        {a : ZMod N | ‖gaussSum χ (stdAddChar.mulShift a)‖ = √N} =
      (fun k : ℕ ↦ gaussSum χ stdAddChar *
          Complex.exp (2 * Real.pi * Complex.I * (k / orderOf χ))) '' Set.Iio (orderOf χ) := by
  rw [χ.setOf_norm_gaussSum_mulShift_eq_sqrt_of_isPrimitive hχ, ← Set.range_comp,
    ← χ.range_gaussSum_mulShift_units_eq_image_exp]
  rfl

/-- **For a primitive character, the regular `n`-gon has `n` distinct vertices**, `n` the order
of `χ`. -/
lemma ncard_range_gaussSum_mulShift_units_of_isPrimitive (hχ : χ.IsPrimitive) :
    (Set.range fun u : (ZMod N)ˣ ↦ gaussSum χ (stdAddChar.mulShift (u : ZMod N))).ncard =
      orderOf χ := by
  have : NeZero (orderOf χ) := ⟨χ.orderOf_pos.ne'⟩
  rw [range_gaussSum_mulShift_units, Set.ncard_image_of_injective _ <| mul_right_injective₀ <|
      χ.gaussSum_stdAddChar_ne_zero_of_isPrimitive hχ,
    Set.ncard_image_of_injective _ Units.val_injective, ← Nat.card_coe_set_eq]
  exact Complex.card_rootsOfUnity _

lemma gaussSum_mulShift_mul_conj :
    gaussSum χ (stdAddChar.mulShift a) * conj (gaussSum χ (stdAddChar.mulShift a)) =
      ∑ x, ∑ y, χ x * conj (χ y) * stdAddChar (a * (x - y)) := by
  simp only [gaussSum, mulShift_apply, map_sum, map_mul, sum_mul_sum]
  refine sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ ?_
  rw [← map_neg_eq_conj, mul_mul_mul_comm, ← map_add_eq_mul, mul_sub, sub_eq_add_neg]

lemma sum_mul_conj : ∑ x, χ x * conj (χ x) = N.totient := by
  simp_rw [starRingEnd_apply, MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel,
    MulChar.sum_one_eq_card_units, card_units_eq_totient]

/-- **Parseval's identity for Gauss sums**: `∑_a |τ_a(χ)|² = N φ(N)`. -/
lemma sum_norm_sq_gaussSum_mulShift :
    ∑ a, ‖gaussSum χ (stdAddChar.mulShift a)‖ ^ 2 = N * N.totient := by
  have h : ∑ a, gaussSum χ (stdAddChar.mulShift a) * conj (gaussSum χ (stdAddChar.mulShift a)) =
      N * N.totient := by
    simp_rw [gaussSum_mulShift_mul_conj]
    rw [sum_comm, sum_congr rfl fun x _ ↦ sum_comm]
    simp_rw [← mul_sum, sum_mulShift _ (isPrimitive_stdAddChar N)]
    simp only [Nat.cast_ite, Nat.cast_zero, sub_eq_zero, mul_ite, mul_zero, sum_ite_eq, mem_univ,
      ite_true, ZMod.card]
    rw [← sum_mul, sum_mul_conj, mul_comm]
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

lemma gaussSum_mulShift_div_conductor_ne_zero :
    gaussSum χ (stdAddChar.mulShift ((N / χ.conductor : ℕ) : ZMod N)) ≠ 0 := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hd : χ.conductor ∣ N := χ.conductor_dvd_level
  let ψ : DirichletCharacter ℂ χ.conductor := χ.primitiveCharacter
  let F : (ZMod χ.conductor)ˣ → ℂ := fun v ↦ ψ v * stdAddChar (v : ZMod χ.conductor)
  have hχu (u : (ZMod N)ˣ) : χ u = ψ (cast (u : ZMod N)) :=
    (congrArg (· (u : ZMod N)) χ.changeLevel_primitiveCharacter).symm.trans <|
      changeLevel_eq_cast_of_dvd ψ hd u
  have h1 : gaussSum χ (stdAddChar.mulShift ((N / χ.conductor : ℕ) : ZMod N)) =
      ∑ u : (ZMod N)ˣ, F (unitsMap hd u) := by
    rw [gaussSum, sum_eq_sum_units fun x hx ↦ by rw [χ.map_nonunit hx, zero_mul]]
    refine sum_congr rfl fun u _ ↦ ?_
    rw [mulShift_apply, stdAddChar_natCast_div_mul hd, hχu, ← unitsMap_val hd u]
  have hfib (v : (ZMod χ.conductor)ˣ) :
      #{u : (ZMod N)ˣ | unitsMap hd u = v} = #{u : (ZMod N)ˣ | unitsMap hd u = 1} :=
    MonoidHom.card_fiber_eq_of_mem_range _ (unitsMap_surjective hd v) (unitsMap_surjective hd 1)
  have h2 : ∑ u : (ZMod N)ˣ, F (unitsMap hd u) =
      #{u : (ZMod N)ˣ | unitsMap hd u = 1} • gaussSum ψ stdAddChar := by
    rw [sum_comp, image_univ_of_surjective (unitsMap_surjective hd)]
    simp_rw [hfib]
    rw [← smul_sum, gaussSum, sum_eq_sum_units fun x hx ↦ by rw [ψ.map_nonunit hx, zero_mul]]
  have hc : #{u : (ZMod N)ˣ | unitsMap hd u = 1} ≠ 0 :=
    (card_pos.mpr ⟨1, by simp⟩).ne'
  rw [h1, h2, nsmul_eq_mul]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hc) <|
    ψ.gaussSum_stdAddChar_ne_zero_of_isPrimitive χ.primitiveCharacter_isPrimitive

lemma not_isUnit_natCast_div_conductor (hχ : ¬χ.IsPrimitive) :
    ¬IsUnit ((N / χ.conductor : ℕ) : ZMod N) := by
  have hd : χ.conductor ∣ N := χ.conductor_dvd_level
  have hlt : χ.conductor < N :=
    (Nat.le_of_dvd (NeZero.pos N) hd).lt_of_ne fun h ↦ hχ <| (isPrimitive_def χ).mpr h
  rw [isUnit_iff_coprime]
  intro h
  have h1 : N / χ.conductor = 1 := h.eq_one_of_dvd (Nat.div_dvd_of_dvd hd)
  rw [Nat.div_eq_iff_eq_mul_left χ.conductor_ne_zero.bot_lt hd, one_mul] at h1
  exact hlt.ne h1.symm

lemma norm_gaussSum_lt_sqrt_of_not_isPrimitive (hχ : ¬χ.IsPrimitive) :
    ‖gaussSum χ stdAddChar‖ < √N := by
  let b : ZMod N := ((N / χ.conductor : ℕ) : ZMod N)
  have hnu : ¬IsUnit b := χ.not_isUnit_natCast_div_conductor hχ
  have hb : b ∉ univ.map ⟨((↑) : (ZMod N)ˣ → ZMod N), Units.val_injective⟩ := fun h ↦ hnu <| by
    rcases mem_map.mp h with ⟨u, -, hu⟩
    rw [← hu]
    exact u.isUnit
  have hpos : 0 < ‖gaussSum χ (stdAddChar.mulShift b)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr χ.gaussSum_mulShift_div_conductor_ne_zero) 2
  have hmap : ∑ a ∈ univ.map ⟨((↑) : (ZMod N)ˣ → ZMod N), Units.val_injective⟩,
      ‖gaussSum χ (stdAddChar.mulShift a)‖ ^ 2 =
        ∑ u : (ZMod N)ˣ, ‖gaussSum χ (stdAddChar.mulShift (u : ZMod N))‖ ^ 2 :=
    sum_map _ _ _
  have hle : ‖gaussSum χ (stdAddChar.mulShift b)‖ ^ 2 +
      ∑ u : (ZMod N)ˣ, ‖gaussSum χ (stdAddChar.mulShift (u : ZMod N))‖ ^ 2 ≤
        ∑ a, ‖gaussSum χ (stdAddChar.mulShift a)‖ ^ 2 := by
    rw [← hmap, ← sum_insert (f := fun a ↦ ‖gaussSum χ (stdAddChar.mulShift a)‖ ^ 2) hb]
    exact sum_le_univ_sum_of_nonneg fun _ ↦ by positivity
  simp_rw [norm_gaussSum_mulShift_unit] at hle
  rw [sum_const, card_univ, card_units_eq_totient, nsmul_eq_mul,
    sum_norm_sq_gaussSum_mulShift] at hle
  have hφ : (0 : ℝ) < N.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos N))
  exact (Real.lt_sqrt (norm_nonneg _)).mpr <| lt_of_mul_lt_mul_left (by linarith) hφ.le

/-- **A Dirichlet character is primitive exactly when its coprime dots reach the circle**: `χ` is
primitive if and only if `|τ_a(χ)| = √N` for every `a` coprime to `N`. -/
lemma isPrimitive_iff_forall_norm_gaussSum_mulShift_eq_sqrt :
    χ.IsPrimitive ↔ ∀ a : ZMod N, IsUnit a → ‖gaussSum χ (stdAddChar.mulShift a)‖ = √N := by
  refine ⟨fun hχ _ ↦ χ.norm_gaussSum_mulShift_of_isPrimitive hχ, fun h ↦ ?_⟩
  by_contra hχ
  have h1 : ‖gaussSum χ (stdAddChar.mulShift (1 : ZMod N))‖ = √N := h 1 isUnit_one
  rw [mulShift_one] at h1
  exact (χ.norm_gaussSum_lt_sqrt_of_not_isPrimitive hχ).ne h1

variable {a} in
/-- **The coprime dots of an imprimitive character lie strictly inside the circle**:
`|τ_a(χ)| < √N` for every `a` coprime to `N`. -/
lemma norm_gaussSum_mulShift_lt_sqrt_of_not_isPrimitive (hχ : ¬χ.IsPrimitive) (ha : IsUnit a) :
    ‖gaussSum χ (stdAddChar.mulShift a)‖ < √N := by
  rw [← ha.unit_spec, norm_gaussSum_mulShift_unit]
  exact χ.norm_gaussSum_lt_sqrt_of_not_isPrimitive hχ

end DirichletCharacter
