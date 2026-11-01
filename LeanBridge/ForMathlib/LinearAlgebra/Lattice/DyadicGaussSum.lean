import LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolDyadic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import TauCeti.GroupTheory.Coset.Fiber
import TauCeti.LinearAlgebra.BilinearForm.LocalRing
import TauCeti.LinearAlgebra.PerfectPairing.Basis

/-!
# Dyadic Gauss sums of unimodular forms

For a bilinear form `C` over `ℤ_2` on a finite free module `K` of rank `n` and `k ∈ ℕ`, the dyadic
Gauss sum `Σ_(x ∈ K / 2 ^ k K) exp(2 π i C(x, x) / 2 ^ k)` is an isometry invariant that is
multiplicative over orthogonal direct sums, and the Gauss sum of level `a + b` of `2 ^ b C` is
`2 ^ (b n)` times the Gauss sum of level `a` of `C`. This file evaluates it for a unimodular
symmetric form `f` with sign `ε = χ₈(det f)` and oddity `t` (the dyadic data of a Jordan
constituent in the Conway genus symbol, LMFDB `lattice.conway_genus_symbol`): for every `k ≥ 2`
it is `√2 ^ ((k + 1) n) ε ^ (k - 1) ζ₈ ^ t`, with `ζ₈ = exp(2 π i / 8)`. Equivalently, the Gauss
sum `Σ_(x ∈ K / 2 ^ s K) exp(2 π i f(x, x) / 2 ^ (s + 1))` is `2 ^ (n s / 2) ε ^ s ζ₈ ^ t` for
`s ≥ 1`; for `s = 1` this is the classical `Σ_(x mod 2) i ^ f(x) = 2 ^ (n / 2) ε ζ₈ ^ t`.

The evaluation modulo `4` and `8` is an induction on the rank along the rank-`1`/rank-`2` normal
form of unimodular dyadic forms: a vector of odd norm spans an orthogonal summand, and an even form
splits off a perfect binary summand (Tau Ceti's binary splitting step). The Gauss sum, the sign
and the oddity are multiplicative, multiplicative and additive over such a splitting, and the
Gauss sums of the summands `⟨u⟩` and `[2a, b; b, 2c]` are computed directly. The higher levels
follow from the recursion `Σ_(k + 2) = 2 ^ n Σ_k`, `k ≥ 2`: averaging over the translations by
`2 ^ k K`, only the vectors of `2 K` survive, on which the form is `4 f`.

These sums are the local ingredient of the genus invariance of the Gauss oddities `Θ_m` of
`LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolOddity`, the hypothesis under which the
canonical `2`-adic symbol and the label (LMFDB `lattice.genus_label`) are proved to be genus
invariants there: the Gauss sums of the dyadic localization of a lattice are genus invariants,
they factor over a Jordan splitting, and the Gauss sum of level `m + 1` of a Jordan constituent
`2 ^ j f_j` is a positive real times `ε_j ^ (m - j) ζ₈ ^ t_j` for `j < m`, and a positive real
for `j > m` and for `j = m` when `f_m` is even. The invariance itself is
`LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolGaussSum`.

## Main definitions

* `Matrix.quadGaussSum`: the quadratic Gauss sum of a square matrix over `ℤ / N`.
* `LinearMap.BilinForm.dyadicGaussSum` (LMFDB `lattice.conway_genus_symbol`): the dyadic Gauss sum
  of level `k` of a bilinear form over `ℤ_2`.
* `LinearMap.BilinForm.dyadicDetSign` (LMFDB `lattice.conway_genus_symbol`): the sign `χ₈(det)` of a
  bilinear form over `ℤ_2`.

## Main results

* `Matrix.quadGaussSum_transpose_mul_mul`: the quadratic Gauss sum is a congruence invariant.
* `Matrix.quadGaussSum_fromBlocks`: it is multiplicative over block diagonal matrices.
* `LinearMap.BilinForm.dyadicGaussSum_eq`: the dyadic Gauss sum can be computed in any basis.
* `LinearMap.BilinForm.dyadicGaussSum_eq_of_equivalent`: it is an isometry invariant.
* `LinearMap.BilinForm.dyadicGaussSum_eq_mul_of_isCompl`: it is multiplicative over orthogonal
  direct sums.
* `LinearMap.BilinForm.dyadicGaussSum_two_pow_smul`: the scaling by a power of `2`.
* `LinearMap.BilinForm.dyadicGaussSum_eq_of_forall_dvd`: the Gauss sum of level `k` of a form
  whose norms are divisible by `2 ^ k`.
* `LinearMap.BilinForm.dyadicGaussSum_eq_prod_of_isInternal`: it is multiplicative over finite
  orthogonal internal direct sums.
* `Matrix.quadGaussSum_blockDiagonal'`: the quadratic Gauss sum of a block diagonal matrix.
* `LinearMap.BilinForm.dyadicGaussSum_of_eq_two_or_eq_three`: the dyadic Gauss sums modulo `4` and
  `8` of a unimodular symmetric form.
* `LinearMap.BilinForm.dyadicGaussSum_add_two`: the recursion from level `k` to level `k + 2`.
* `LinearMap.BilinForm.dyadicGaussSum_eq_of_isPerfPair`: the dyadic Gauss sums of every level
  `k ≥ 2` of a unimodular symmetric form.
* `LinearMap.BilinForm.IsJordanSplitting.dyadicGaussSum_unitForm`: those of the unit forms of the
  constituents of a dyadic Jordan splitting, in terms of their ranks, signs and oddities.
* `LinearMap.BilinForm.IsJordanSplitting.dyadicGaussSum_restrict`: the Gauss sum of a constituent
  in terms of that of its unit form.
* `LinearMap.BilinForm.IsJordanSplitting.dyadicGaussSum_eq_prod`: the Gauss sum factors over a
  Jordan splitting.
* `TauCeti.IntegralLattice.SameGenus.dyadicGaussSum_eq`: the dyadic Gauss sums of a lattice are
  genus invariants.
-/

open Matrix Module

open LinearMap (BilinForm)

open scoped Finset

namespace Complex

lemma sqrt_two_pow_two_mul (n : ℕ) : (√2 : ℂ) ^ (2 * n) = 2 ^ n := by
  rw [pow_mul, ← ofReal_pow, Real.sq_sqrt zero_le_two, ofReal_ofNat]

end Complex

namespace ZMod

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ} [NeZero N] (k : ℕ)

lemma sum_comp_cast (a b : ℕ) (g : (ι → ZMod (2 ^ a)) → ℂ) :
    ∑ y : ι → ZMod (2 ^ (a + b)), g (fun i ↦ ZMod.cast (y i)) =
      2 ^ (b * Fintype.card ι) * ∑ y, g y := by
  let φ : (ι → ZMod (2 ^ (a + b))) →+ (ι → ZMod (2 ^ a)) :=
    (castHom (pow_dvd_pow 2 (Nat.le_add_right a b)) (ZMod (2 ^ a))).toAddMonoidHom.compLeft ι
  have hφ : Function.Surjective φ := fun y ↦
    ⟨fun i ↦ (castHom_surjective (pow_dvd_pow 2 (Nat.le_add_right a b)) (y i)).choose,
      funext fun i ↦ (castHom_surjective (pow_dvd_pow 2 (Nat.le_add_right a b)) (y i)).choose_spec⟩
  have hcard : (Fintype.card (ι → ZMod (2 ^ (a + b))) : ℂ) =
      Nat.card φ.ker * Fintype.card (ι → ZMod (2 ^ a)) := by
    simpa using φ.sum_comp_of_surjective hφ fun _ ↦ (1 : ℂ)
  have hker : (Nat.card φ.ker : ℂ) = 2 ^ (b * Fintype.card ι) := by
    simp only [Fintype.card_fun, ZMod.card] at hcard
    push_cast at hcard
    refine mul_right_cancel₀ (pow_ne_zero (Fintype.card ι) (pow_ne_zero a two_ne_zero)) ?_
    linear_combination -hcard
  rw [← hker, ← nsmul_eq_mul]
  exact φ.sum_comp_of_surjective hφ g

lemma stdAddChar_two_pow_mul (a b : ℕ) (x : ZMod (2 ^ (a + b))) :
    stdAddChar (2 ^ b * x) = stdAddChar (ZMod.cast x : ZMod (2 ^ a)) := by
  rcases ZMod.intCast_surjective x with ⟨j, rfl⟩
  rw [ZMod.cast_intCast (pow_dvd_pow 2 (Nat.le_add_right a b)),
    (by push_cast; ring1 : (2 : ZMod (2 ^ (a + b))) ^ b * (j : ZMod (2 ^ (a + b))) =
      ((2 ^ b * j : ℤ) : ZMod (2 ^ (a + b)))), stdAddChar_coe, stdAddChar_coe]
  congr 1
  push_cast
  field_simp
  ring1

lemma stdAddChar_sum {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ZMod N) :
    stdAddChar (∑ i ∈ s, f i) = ∏ i ∈ s, stdAddChar (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, AddChar.map_add_eq_mul, ih, Finset.prod_insert ha]

lemma stdAddChar_dotProduct (z w : ι → ZMod N) :
    stdAddChar (z ⬝ᵥ w) = ∏ i, stdAddChar (z i * w i) :=
  stdAddChar_sum Finset.univ fun i ↦ z i * w i

lemma sum_stdAddChar_dotProduct (w : ι → ZMod N) :
    ∑ z : ι → ZMod N, stdAddChar (z ⬝ᵥ w) = if w = 0 then (N : ℂ) ^ Fintype.card ι else 0 := by
  simp_rw [stdAddChar_dotProduct, ← Fintype.prod_sum fun i x ↦ stdAddChar (x * w i),
    AddChar.sum_mulShift _ (isPrimitive_stdAddChar N), ZMod.card]
  split_ifs with hw
  · simp [hw]
  · rcases Function.ne_iff.mp hw with ⟨i, hi⟩
    have hi' : w i ≠ 0 := hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi'])

lemma two_pow_mul_eq_zero_iff (x : ZMod (2 ^ (k + 2))) : 2 ^ (k + 1) * x = 0 ↔ ∃ y, x = 2 * y := by
  constructor
  · intro h
    rw [← ZMod.natCast_zmod_val x] at h ⊢
    have h' : 2 ^ (k + 1) * 2 ∣ 2 ^ (k + 1) * x.val := by
      rw [← pow_succ, ← ZMod.natCast_eq_zero_iff]
      exact_mod_cast h
    rcases Nat.dvd_of_mul_dvd_mul_left (pow_pos two_pos _) h' with ⟨m, hm⟩
    exact ⟨m, by rw [hm]; push_cast; ring1⟩
  · rintro ⟨y, rfl⟩
    rw [← mul_assoc, ← pow_succ,
      (by exact_mod_cast ZMod.natCast_self (2 ^ (k + 2)) : (2 : ZMod (2 ^ (k + 2))) ^ (k + 2) = 0),
      zero_mul]

lemma card_two_smul_eq_zero : #{y : ι → ZMod (2 ^ (k + 2)) | 2 • y = 0} = 2 ^ Fintype.card ι := by
  have hiff (y : ι → ZMod (2 ^ (k + 2))) :
      2 • y = 0 ↔ (fun i ↦ (ZMod.cast (y i) : ZMod (2 ^ (k + 1)))) = 0 := by
    simp only [funext_iff, Pi.smul_apply, Pi.zero_apply]
    refine forall_congr' fun i ↦ ?_
    rw [← ZMod.natCast_zmod_val (y i), ZMod.cast_natCast (pow_dvd_pow 2 (Nat.le_succ (k + 1))),
      ← Nat.cast_smul_eq_nsmul (ZMod (2 ^ (k + 2))), smul_eq_mul, ← Nat.cast_mul,
      ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff]
    generalize (y i).val = v
    rw [pow_succ', Nat.mul_dvd_mul_iff_left two_pos]
  have h : ∑ y : ι → ZMod (2 ^ (k + 1 + 1)),
      (if (fun i ↦ (ZMod.cast (y i) : ZMod (2 ^ (k + 1)))) = 0 then (1 : ℂ) else 0) =
        2 ^ (1 * Fintype.card ι) * ∑ y : ι → ZMod (2 ^ (k + 1)), if y = 0 then (1 : ℂ) else 0 :=
    sum_comp_cast (k + 1) 1 fun y' ↦ if y' = 0 then (1 : ℂ) else 0
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_one, one_mul] at h
  have hc : (#{y : ι → ZMod (2 ^ (k + 2)) | 2 • y = 0} : ℂ) = 2 ^ Fintype.card ι := by
    rw [Finset.natCast_card_filter]
    simp_rw [hiff]
    exact h
  exact_mod_cast hc

lemma sum_univ_two_pow_two (f : ZMod (2 ^ 2) → ℂ) : ∑ a, f a = f 0 + f 1 + f 2 + f 3 :=
  Fin.sum_univ_four f

lemma sum_univ_two_pow_three (f : ZMod (2 ^ 3) → ℂ) :
    ∑ a, f a = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 :=
  Fin.sum_univ_eight f

lemma sqrt_two_mul_stdAddChar_one : (√2 : ℂ) * stdAddChar (1 : ZMod 8) = 1 + Complex.I := by
  have h : 2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ) / ((8 : ℕ) : ℂ) =
      ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring1
  rw [← Int.cast_one, stdAddChar_coe, h, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have h2 : (√2 : ℂ) * √2 = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two, Complex.ofReal_ofNat]
  push_cast
  linear_combination (1 + Complex.I) / 2 * h2

lemma stdAddChar_two_eq_I : stdAddChar (2 : ZMod 8) = Complex.I := by
  have h : 2 * Real.pi * Complex.I * ((2 : ℤ) : ℂ) / ((8 : ℕ) : ℂ) =
      ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring1
  rw [← Int.cast_ofNat, stdAddChar_coe, h, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

lemma stdAddChar_one_eq_I : stdAddChar (1 : ZMod (2 ^ 2)) = Complex.I := by
  have h : 2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ) / ((2 ^ 2 : ℕ) : ℂ) =
      ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring1
  rw [← Int.cast_one, stdAddChar_coe, h, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

lemma stdAddChar_four_eq_neg_one : stdAddChar (4 : ZMod (2 ^ 3)) = -1 := by
  have h : 2 * Real.pi * Complex.I * ((4 : ℤ) : ℂ) / ((2 ^ 3 : ℕ) : ℂ) = Real.pi * Complex.I := by
    push_cast
    ring1
  rw [← Int.cast_ofNat, stdAddChar_coe, h, Complex.exp_pi_mul_I]

lemma sum_stdAddChar_mul_mul (w : ZMod (2 ^ 2)) :
    ∑ a : ZMod (2 ^ 2), stdAddChar (a * w * a) = 2 + 2 * stdAddChar w := by
  have h4 : (4 : ZMod (2 ^ 2)) = 0 := by decide
  have h2 : (2 : ZMod (2 ^ 2)) * w * 2 = 0 := by linear_combination w * h4
  have h3 : (3 : ZMod (2 ^ 2)) * w * 3 = w := by linear_combination 2 * w * h4
  rw [sum_univ_two_pow_two, h2, h3]
  simp
  ring1

lemma sum_stdAddChar_mul_cast_mul (v : ZMod 8) (hv : IsUnit v) :
    ∑ a : ZMod (2 ^ 2), stdAddChar (a * (ZMod.cast v : ZMod (2 ^ 2)) * a) =
      (√2 : ℂ) ^ 3 * χ₈ v * stdAddChar v := by
  have h2 : (√2 : ℂ) * √2 = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two, Complex.ofReal_ofNat]
  have hs3 : (√2 : ℂ) ^ 3 * stdAddChar (1 : ZMod 8) = 2 * (1 + Complex.I) := by
    linear_combination √2 ^ 2 * sqrt_two_mul_stdAddChar_one + (1 + Complex.I) * h2
  have h3 : stdAddChar (3 : ZMod (2 ^ 2)) = -Complex.I := by
    rw [(by decide : (3 : ZMod (2 ^ 2)) = 1 + 1 + 1), AddChar.map_add_eq_mul,
      AddChar.map_add_eq_mul, stdAddChar_one_eq_I]
    linear_combination Complex.I * Complex.I_sq
  rw [sum_stdAddChar_mul_mul]
  rcases (by decide : ∀ v : ZMod 8, IsUnit v → v = 1 ∨ v = 3 ∨ v = 5 ∨ v = 7) v hv with
    rfl | rfl | rfl | rfl
  · rw [(by decide : (ZMod.cast (1 : ZMod 8) : ZMod (2 ^ 2)) = 1), stdAddChar_one_eq_I,
      (by decide : χ₈ 1 = 1)]
    linear_combination -hs3
  · rw [(by decide : (ZMod.cast (3 : ZMod 8) : ZMod (2 ^ 2)) = 3), h3, (by decide : χ₈ 3 = -1),
      (by decide : (3 : ZMod 8) = 1 + 2), AddChar.map_add_eq_mul, stdAddChar_two_eq_I]
    push_cast
    linear_combination Complex.I * hs3 + 2 * Complex.I_sq
  · rw [(by decide : (ZMod.cast (5 : ZMod 8) : ZMod (2 ^ 2)) = 1), stdAddChar_one_eq_I,
      (by decide : χ₈ 5 = -1), (by decide : (5 : ZMod 8) = 1 + 2 + 2), AddChar.map_add_eq_mul,
      AddChar.map_add_eq_mul, stdAddChar_two_eq_I]
    push_cast
    linear_combination Complex.I ^ 2 * hs3 + (2 + 2 * Complex.I) * Complex.I_sq
  · rw [(by decide : (ZMod.cast (7 : ZMod 8) : ZMod (2 ^ 2)) = 3), h3, (by decide : χ₈ 7 = 1),
      (by decide : (7 : ZMod 8) = 1 + 2 + 2 + 2), AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
      AddChar.map_add_eq_mul, stdAddChar_two_eq_I]
    push_cast
    linear_combination -Complex.I ^ 3 * hs3 + (2 - 2 * Complex.I ^ 2 - 2 * Complex.I) *
      Complex.I_sq

lemma sum_stdAddChar_mul_mul_eight (u : ZMod (2 ^ 3)) (hu : IsUnit u) :
    ∑ a : ZMod (2 ^ 3), stdAddChar (a * (u * a)) = 4 * stdAddChar u := by
  have h8 : (8 : ZMod (2 ^ 3)) = 0 := by decide
  have h4 : 4 * u = 4 := (by decide : ∀ u : ZMod (2 ^ 3), IsUnit u → 4 * u = 4) u hu
  rw [sum_univ_two_pow_three, (by linear_combination h4 : (2 : ZMod (2 ^ 3)) * (u * 2) = 4),
    (by linear_combination u * h8 : (3 : ZMod (2 ^ 3)) * (u * 3) = u),
    (by linear_combination 2 * u * h8 : (4 : ZMod (2 ^ 3)) * (u * 4) = 0),
    (by linear_combination 3 * u * h8 : (5 : ZMod (2 ^ 3)) * (u * 5) = u),
    (by linear_combination 4 * u * h8 + h4 : (6 : ZMod (2 ^ 3)) * (u * 6) = 4),
    (by linear_combination 6 * u * h8 : (7 : ZMod (2 ^ 3)) * (u * 7) = u),
    stdAddChar_four_eq_neg_one]
  simp
  ring1

end ZMod

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {N : ℕ} [NeZero N]
  (A : Matrix ι ι (ZMod N))

/-- The **quadratic Gauss sum** `Σ_(c ∈ (ℤ / N) ^ ι) exp(2 π i cᵀ A c / N)` of a square matrix `A`
over `ℤ / N`. -/
noncomputable def quadGaussSum : ℂ :=
  ∑ c : ι → ZMod N, ZMod.stdAddChar (c ⬝ᵥ A *ᵥ c)

/-- **The quadratic Gauss sum is a congruence invariant**: `Pᵀ A P` and `A` have the same Gauss
sum for an invertible `P`. -/
lemma quadGaussSum_transpose_mul_mul {P : Matrix ι κ (ZMod N)} {Q : Matrix κ ι (ZMod N)}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) : (Pᵀ * A * P).quadGaussSum = A.quadGaussSum := by
  refine Fintype.sum_equiv ⟨(P *ᵥ ·), (Q *ᵥ ·), fun c ↦ by simp [hQP], fun c ↦ by simp [hPQ]⟩
    _ _ fun c ↦ ?_
  simp only [Equiv.coe_fn_mk]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- **The quadratic Gauss sum is multiplicative over block diagonal matrices.** -/
lemma quadGaussSum_fromBlocks (D : Matrix κ κ (ZMod N)) :
    (fromBlocks A 0 0 D).quadGaussSum = A.quadGaussSum * D.quadGaussSum := by
  rw [quadGaussSum, quadGaussSum, quadGaussSum, Finset.sum_mul_sum,
    ← (Equiv.sumArrowEquivProdArrow ι κ (ZMod N)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun d _ ↦ ?_
  have h : (Equiv.sumArrowEquivProdArrow ι κ (ZMod N)).symm (a, d) = Sum.elim a d := rfl
  rw [← AddChar.map_add_eq_mul, h]
  simp [fromBlocks_mulVec, dotProduct]

/-- **The quadratic Gauss sum is multiplicative over block diagonal matrices** with blocks of
any sizes. -/
lemma quadGaussSum_blockDiagonal' {o : Type*} [Fintype o] [DecidableEq o] {m' : o → Type*}
    [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)] (G : ∀ i, Matrix (m' i) (m' i) (ZMod N)) :
    (blockDiagonal' G).quadGaussSum = ∏ i, (G i).quadGaussSum := by
  have hq (c : (Σ i, m' i) → ZMod N) : c ⬝ᵥ blockDiagonal' G *ᵥ c =
      ∑ i, (fun a ↦ c ⟨i, a⟩) ⬝ᵥ G i *ᵥ fun a ↦ c ⟨i, a⟩ := by
    simp [dotProduct, mulVec, Fintype.sum_sigma, blockDiagonal'_apply]
  simp_rw [quadGaussSum, hq, ZMod.stdAddChar_sum, Fintype.prod_sum]
  exact (Equiv.sum_comp (Equiv.piCurry fun i (_ : m' i) ↦ ZMod N).symm _).symm.trans rfl

lemma quadGaussSum_eq_sum_card :
    A.quadGaussSum = ∑ j : ZMod N, (#{c | c ⬝ᵥ A *ᵥ c = j} : ℂ) * ZMod.stdAddChar j := by
  rw [quadGaussSum, ← Finset.sum_fiberwise Finset.univ fun c ↦ c ⬝ᵥ A *ᵥ c]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_congr rfl fun c hc ↦ by rw [(Finset.mem_filter.mp hc).2], Finset.sum_const,
    nsmul_eq_mul]

lemma quadGaussSum_cast_of_four_mul_eq_zero (a b c : ZMod 8) (ha : 4 * a = 0) (hc : 4 * c = 0)
    (hdet : IsUnit (a * c - b * b)) :
    (!![(ZMod.cast a : ZMod (2 ^ 2)), ZMod.cast b; ZMod.cast b, ZMod.cast c]).quadGaussSum =
      8 * ZMod.χ₈ (a * c - b * b) := by
  have key : ∀ a b c : ZMod 8, 4 * a = 0 → 4 * c = 0 → IsUnit (a * c - b * b) →
      (#{x | x ⬝ᵥ !![(ZMod.cast a : ZMod (2 ^ 2)), ZMod.cast b; ZMod.cast b, ZMod.cast c] *ᵥ x =
        1} = 0 ∧ #{x | x ⬝ᵥ !![(ZMod.cast a : ZMod (2 ^ 2)), ZMod.cast b; ZMod.cast b,
          ZMod.cast c] *ᵥ x = 3} = 0) ∧
      (#{x | x ⬝ᵥ !![(ZMod.cast a : ZMod (2 ^ 2)), ZMod.cast b; ZMod.cast b, ZMod.cast c] *ᵥ x =
        0} : ℤ) - #{x | x ⬝ᵥ !![(ZMod.cast a : ZMod (2 ^ 2)), ZMod.cast b; ZMod.cast b,
          ZMod.cast c] *ᵥ x = 2} = 8 * ZMod.χ₈ (a * c - b * b) := by
    decide +kernel
  rcases key a b c ha hc hdet with ⟨⟨h1, h3⟩, h02⟩
  have hψ : ZMod.stdAddChar (2 : ZMod (2 ^ 2)) = -1 := by
    rw [(by decide : (2 : ZMod (2 ^ 2)) = 1 + 1), AddChar.map_add_eq_mul, ZMod.stdAddChar_one_eq_I,
      Complex.I_mul_I]
  rw [quadGaussSum_eq_sum_card, ZMod.sum_univ_two_pow_two, h1, h3, hψ, AddChar.map_zero_eq_one]
  simp only [Nat.cast_zero, zero_mul, add_zero, mul_one, mul_neg_one, ← sub_eq_add_neg]
  exact_mod_cast h02

lemma quadGaussSum_of_four_mul_eq_zero (a b c : ZMod (2 ^ 3)) (ha : 4 * a = 0) (hc : 4 * c = 0)
    (hdet : IsUnit (a * c - b * b)) : (!![a, b; b, c]).quadGaussSum = 16 := by
  have key : ∀ a b c : ZMod (2 ^ 3), 4 * a = 0 → 4 * c = 0 → IsUnit (a * c - b * b) →
      ((#{x | x ⬝ᵥ !![a, b; b, c] *ᵥ x = 1} = 0 ∧ #{x | x ⬝ᵥ !![a, b; b, c] *ᵥ x = 3} = 0) ∧
        (#{x | x ⬝ᵥ !![a, b; b, c] *ᵥ x = 5} = 0 ∧ #{x | x ⬝ᵥ !![a, b; b, c] *ᵥ x = 7} = 0)) ∧
      #{x | x ⬝ᵥ !![a, b; b, c] *ᵥ x = 2} = #{x | x ⬝ᵥ !![a, b; b, c] *ᵥ x = 6} ∧
      (#{x | x ⬝ᵥ !![a, b; b, c] *ᵥ x = 0} : ℤ) - #{x | x ⬝ᵥ !![a, b; b, c] *ᵥ x = 4} = 16 := by
    decide +kernel
  rcases key a b c ha hc hdet with ⟨⟨⟨h1, h3⟩, h5, h7⟩, h26, h04⟩
  have h2 : ZMod.stdAddChar (2 : ZMod (2 ^ 3)) = Complex.I := ZMod.stdAddChar_two_eq_I
  have h6 : ZMod.stdAddChar (6 : ZMod (2 ^ 3)) = -Complex.I := by
    rw [(by decide : (6 : ZMod (2 ^ 3)) = 4 + 2), AddChar.map_add_eq_mul,
      ZMod.stdAddChar_four_eq_neg_one, h2, neg_one_mul]
  rw [quadGaussSum_eq_sum_card, ZMod.sum_univ_two_pow_three, h1, h3, h5, h7, h26, h2, h6,
    ZMod.stdAddChar_four_eq_neg_one, AddChar.map_zero_eq_one]
  simp only [Nat.cast_zero, zero_mul, add_zero, mul_one, mul_neg, ← sub_eq_add_neg]
  rw [sub_right_comm, add_sub_cancel_right]
  exact_mod_cast h04

lemma quadGaussSum_add_two (k : ℕ) (hk : 2 ≤ k) (G : Matrix ι ι (ZMod (2 ^ (k + 2)))) (hG : Gᵀ = G)
    (hdet : IsUnit G.det) : 2 ^ Fintype.card ι * G.quadGaussSum = (4 • G).quadGaussSum := by
  have ht : (2 : ZMod (2 ^ (k + 2))) ^ k * 2 ^ k = 0 := by
    rw [← pow_add]
    exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mpr (pow_dvd_pow 2 (by omega))
  have hexp (c z : ι → ZMod (2 ^ (k + 2))) :
      (c + (2 : ZMod (2 ^ (k + 2))) ^ k • z) ⬝ᵥ G *ᵥ (c + (2 : ZMod (2 ^ (k + 2))) ^ k • z) =
        c ⬝ᵥ G *ᵥ c + z ⬝ᵥ ((2 : ZMod (2 ^ (k + 2))) ^ (k + 1) • G *ᵥ c) := by
    have hsym : c ⬝ᵥ G *ᵥ z = z ⬝ᵥ G *ᵥ c := by
      rw [dotProduct_mulVec, ← vecMul_transpose, hG, dotProduct_comm]
    simp only [mulVec_add, add_dotProduct, dotProduct_add, mulVec_smul, smul_dotProduct,
      dotProduct_smul]
    linear_combination (2 : ZMod (2 ^ (k + 2))) ^ k * hsym + (z ⬝ᵥ G *ᵥ z) * ht
  have hF (z : ι → ZMod (2 ^ (k + 2))) : G.quadGaussSum = ∑ c, ZMod.stdAddChar (c ⬝ᵥ G *ᵥ c) *
      ZMod.stdAddChar (z ⬝ᵥ ((2 : ZMod (2 ^ (k + 2))) ^ (k + 1) • G *ᵥ c)) := by
    rw [quadGaussSum, ← Equiv.sum_comp (Equiv.addRight ((2 : ZMod (2 ^ (k + 2))) ^ k • z))]
    simp only [Equiv.coe_addRight, hexp, AddChar.map_add_eq_mul]
  have hsum : ((2 ^ (k + 2) : ℕ) : ℂ) ^ Fintype.card ι * G.quadGaussSum =
      ∑ c, ZMod.stdAddChar (c ⬝ᵥ G *ᵥ c) *
        if (2 : ZMod (2 ^ (k + 2))) ^ (k + 1) • G *ᵥ c = 0 then
          ((2 ^ (k + 2) : ℕ) : ℂ) ^ Fintype.card ι else 0 := by
    have h : ∑ z : ι → ZMod (2 ^ (k + 2)), G.quadGaussSum = ∑ z : ι → ZMod (2 ^ (k + 2)),
        ∑ c, ZMod.stdAddChar (c ⬝ᵥ G *ᵥ c) *
          ZMod.stdAddChar (z ⬝ᵥ ((2 : ZMod (2 ^ (k + 2))) ^ (k + 1) • G *ᵥ c)) :=
      Finset.sum_congr rfl fun z _ ↦ hF z
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, nsmul_eq_mul,
      Finset.sum_comm] at h
    simp_rw [← Finset.mul_sum, ZMod.sum_stdAddChar_dotProduct] at h
    push_cast at h ⊢
    exact h
  have hcond (c : ι → ZMod (2 ^ (k + 2))) :
      (2 : ZMod (2 ^ (k + 2))) ^ (k + 1) • G *ᵥ c = 0 ↔ ∃ y, c = 2 • y := by
    rw [← mulVec_smul]
    constructor
    · intro h
      have hc : (2 : ZMod (2 ^ (k + 2))) ^ (k + 1) • c = 0 := by
        simpa [mulVec_mulVec, nonsing_inv_mul G hdet] using congrArg (G⁻¹ *ᵥ ·) h
      choose y hy using fun i ↦ (ZMod.two_pow_mul_eq_zero_iff k (c i)).mp (by
        simpa using congrFun hc i)
      exact ⟨y, funext fun i ↦ by simpa using hy i⟩
    · rintro ⟨y, rfl⟩
      have h0 : (2 : ZMod (2 ^ (k + 2))) * 2 ^ (k + 1) = 0 := by
        rw [← pow_succ']
        exact_mod_cast ZMod.natCast_self (2 ^ (k + 2))
      rw [smul_comm, ← smul_assoc, nsmul_eq_mul, Nat.cast_ofNat, h0, zero_smul, mulVec_zero]
  have h4 : (4 • G).quadGaussSum =
      ∑ y : ι → ZMod (2 ^ (k + 2)), ZMod.stdAddChar ((2 • y) ⬝ᵥ G *ᵥ (2 • y)) := by
    refine Finset.sum_congr rfl fun y _ ↦ congrArg _ ?_
    simp only [smul_mulVec, mulVec_smul, smul_dotProduct, dotProduct_smul]
    ring1
  have hfib : ∑ y : ι → ZMod (2 ^ (k + 2)), ZMod.stdAddChar ((2 • y) ⬝ᵥ G *ᵥ (2 • y)) =
      ∑ c, (#{y | 2 • y = c} : ℂ) * ZMod.stdAddChar (c ⬝ᵥ G *ᵥ c) := by
    rw [← Finset.sum_fiberwise Finset.univ fun y : ι → ZMod (2 ^ (k + 2)) ↦ 2 • y]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [Finset.sum_congr rfl fun y hy ↦ by rw [(Finset.mem_filter.mp hy).2], Finset.sum_const,
      nsmul_eq_mul]
  have hcard (c : ι → ZMod (2 ^ (k + 2))) :
      (#{y | 2 • y = c} : ℂ) = if ∃ y, c = 2 • y then 2 ^ Fintype.card ι else 0 := by
    split_ifs with h
    · rcases h with ⟨y₀, rfl⟩
      have hfiber : #{y : ι → ZMod (2 ^ (k + 2)) | 2 • y = 2 • y₀} =
          #{y : ι → ZMod (2 ^ (k + 2)) | 2 • y = 0} :=
        AddMonoidHom.card_fiber_eq_of_mem_range
          (DistribSMul.toAddMonoidHom (ι → ZMod (2 ^ (k + 2))) (2 : ℕ)) ⟨y₀, rfl⟩ ⟨0, map_zero _⟩
      rw [hfiber]
      exact_mod_cast ZMod.card_two_smul_eq_zero k
    · rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun y _ hy ↦ h ⟨y, hy.symm⟩
  have hS : G.quadGaussSum =
      ∑ c, if ∃ y, c = 2 • y then ZMod.stdAddChar (c ⬝ᵥ G *ᵥ c) else 0 := by
    refine mul_left_cancel₀ (pow_ne_zero (Fintype.card ι)
      (by norm_num : ((2 ^ (k + 2) : ℕ) : ℂ) ≠ 0)) (hsum.trans ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    split_ifs with h1 h2 h2
    · ring1
    · exact absurd ((hcond c).mp h1) h2
    · exact absurd ((hcond c).mpr h2) h1
    · ring1
  rw [h4, hfib, hS, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [hcard c]
  split_ifs <;> ring1

end Matrix

namespace LinearMap.BilinForm

variable {K K' : Type*} [AddCommGroup K] [Module ℤ_[2] K] [AddCommGroup K'] [Module ℤ_[2] K']
  (C : BilinForm ℤ_[2] K) {C' : BilinForm ℤ_[2] K'} {S T : Submodule ℤ_[2] K} (k : ℕ)

lemma toMatrix₂_map_prodEquivOfIsCompl {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (bS : Basis ι ℤ_[2] S) (bT : Basis κ ℤ_[2] T) (hST : IsCompl S T)
    (horth : ∀ x ∈ S, ∀ y ∈ T, C x y = 0) (horth' : ∀ x ∈ T, ∀ y ∈ S, C x y = 0) :
    toMatrix₂ ((bS.prod bT).map (S.prodEquivOfIsCompl T hST))
      ((bS.prod bT).map (S.prodEquivOfIsCompl T hST)) C =
      fromBlocks (toMatrix₂ bS bS (C.restrict S)) 0 0 (toMatrix₂ bT bT (C.restrict T)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [horth, horth']

lemma apply_orthogonal_eq_zero : ∀ x ∈ S, ∀ y ∈ C.orthogonal S, C x y = 0 :=
  fun x hx _ hy ↦ (mem_orthogonal_iff.mp hy) x hx

lemma IsSymm.orthogonal_apply_eq_zero (hCs : C.IsSymm) :
    ∀ x ∈ C.orthogonal S, ∀ y ∈ S, C x y = 0 :=
  fun x hx y hy ↦ (hCs.eq x y).trans ((mem_orthogonal_iff.mp hx) y hy)

variable [Free ℤ_[2] K] [Module.Finite ℤ_[2] K] [Free ℤ_[2] K'] [Module.Finite ℤ_[2] K']

/-- The **dyadic Gauss sum** of level `k` (LMFDB `lattice.conway_genus_symbol`) of a bilinear form
`C` over `ℤ_2` on a finite free module `K`: `Σ_(x ∈ K / 2 ^ k K) exp(2 π i C(x, x) / 2 ^ k)`,
computed in a basis, on which it does not depend (`dyadicGaussSum_eq`). For `k = m + 1 ≥ 2` it is
`2 ^ rank` times the Gauss sum `Σ_(x ∈ K / 2 ^ m K) exp(2 π i C(x, x) / 2 ^ (m + 1))` of Conway and
Sloane, whose argument at a scale `2 ^ m` of type `II` is `ζ₈ ^ Θ_m` for a lattice. -/
noncomputable def dyadicGaussSum : ℂ :=
  ((toMatrix₂ (finBasis ℤ_[2] K) (finBasis ℤ_[2] K) C).map (PadicInt.toZModPow k)).quadGaussSum

/-- **The dyadic Gauss sum can be computed in any basis.** -/
lemma dyadicGaussSum_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ_[2] K) :
    C.dyadicGaussSum k = ((toMatrix₂ b b C).map (PadicInt.toZModPow k)).quadGaussSum := by
  have h : toMatrix₂ b b C = ((finBasis ℤ_[2] K).toMatrix b)ᵀ *
      toMatrix₂ (finBasis ℤ_[2] K) (finBasis ℤ_[2] K) C * (finBasis ℤ_[2] K).toMatrix b :=
    (LinearMap.toMatrix₂_mul_basis_toMatrix _ _ b b C).symm
  rw [dyadicGaussSum, h, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  refine (quadGaussSum_transpose_mul_mul _
    (Q := (b.toMatrix (finBasis ℤ_[2] K)).map (PadicInt.toZModPow k)) ?_ ?_).symm
  · rw [← Matrix.map_mul, Basis.toMatrix_mul_toMatrix_flip, Matrix.map_one _ (map_zero _)
      (map_one _)]
  · rw [← Matrix.map_mul, Basis.toMatrix_mul_toMatrix_flip, Matrix.map_one _ (map_zero _)
      (map_one _)]

/-- **The dyadic Gauss sum is an isometry invariant.** -/
lemma dyadicGaussSum_eq_of_equivalent (h : C.Equivalent C') :
    C.dyadicGaussSum k = C'.dyadicGaussSum k := by
  rcases h with ⟨e⟩
  rw [C'.dyadicGaussSum_eq k ((finBasis ℤ_[2] K).map e.toLinearEquiv), dyadicGaussSum]
  congr 2
  ext i j
  simp [e.map_app]

/-- **The dyadic Gauss sum is multiplicative over orthogonal direct sums.** -/
lemma dyadicGaussSum_eq_mul_of_isCompl (hST : IsCompl S T) (horth : ∀ x ∈ S, ∀ y ∈ T, C x y = 0)
    (horth' : ∀ x ∈ T, ∀ y ∈ S, C x y = 0) :
    C.dyadicGaussSum k = (C.restrict S).dyadicGaussSum k * (C.restrict T).dyadicGaussSum k := by
  rw [C.dyadicGaussSum_eq k (((finBasis ℤ_[2] S).prod (finBasis ℤ_[2] T)).map
    (S.prodEquivOfIsCompl T hST)), C.toMatrix₂_map_prodEquivOfIsCompl _ _ hST horth horth',
    fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _),
    quadGaussSum_fromBlocks, dyadicGaussSum, dyadicGaussSum]

/-- **The dyadic Gauss sum is multiplicative over orthogonal internal direct sums** with finitely
many summands. -/
lemma dyadicGaussSum_eq_prod_of_isInternal {o : Type*} [Fintype o] [DecidableEq o]
    {P : o → Submodule ℤ_[2] K} (hP : DirectSum.IsInternal P)
    (horth : ∀ i j, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, C x y = 0) :
    C.dyadicGaussSum k = ∏ i, (C.restrict (P i)).dyadicGaussSum k := by
  rw [C.dyadicGaussSum_eq k (hP.collectedBasis fun i ↦ finBasis ℤ_[2] (P i))]
  have hG : (toMatrix₂ (hP.collectedBasis fun i ↦ finBasis ℤ_[2] (P i))
      (hP.collectedBasis fun i ↦ finBasis ℤ_[2] (P i)) C).map (PadicInt.toZModPow k) =
        blockDiagonal' fun i ↦ (toMatrix₂ (finBasis ℤ_[2] (P i)) (finBasis ℤ_[2] (P i))
          (C.restrict (P i))).map (PadicInt.toZModPow k) := by
    ext ⟨i, a⟩ ⟨j, c⟩
    simp only [map_apply, blockDiagonal'_apply, LinearMap.toMatrix₂_apply, hP.collectedBasis_coe,
      restrict_apply, LinearMap.domRestrict_apply]
    split_ifs with hij
    · subst hij
      rfl
    · rw [horth i j hij _ ((finBasis ℤ_[2] (P i)) a).2 _ ((finBasis ℤ_[2] (P j)) c).2, map_zero]
  rw [hG, quadGaussSum_blockDiagonal']
  rfl

/-- **Scaling of the dyadic Gauss sum**: the Gauss sum of level `a + b` of `2 ^ b C` is
`2 ^ (b n)` times the Gauss sum of level `a` of `C`, `n` being the rank. -/
lemma dyadicGaussSum_two_pow_smul (a b : ℕ) : ((2 : ℤ_[2]) ^ b • C).dyadicGaussSum (a + b) =
    2 ^ (b * finrank ℤ_[2] K) * C.dyadicGaussSum a := by
  rw [dyadicGaussSum, dyadicGaussSum, quadGaussSum, quadGaussSum,
    (by rw [Fintype.card_fin] : (2 : ℂ) ^ (b * finrank ℤ_[2] K) =
      2 ^ (b * Fintype.card (Fin (finrank ℤ_[2] K)))), ← ZMod.sum_comp_cast a b]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  have hmap : ((2 : ℤ_[2]) ^ b • toMatrix₂ (finBasis ℤ_[2] K) (finBasis ℤ_[2] K) C).map
      (PadicInt.toZModPow (a + b)) = (2 ^ b : ZMod (2 ^ (a + b))) •
        (toMatrix₂ (finBasis ℤ_[2] K) (finBasis ℤ_[2] K) C).map (PadicInt.toZModPow (a + b)) := by
    ext i j
    rw [map_apply, Matrix.smul_apply, Matrix.smul_apply, map_apply, smul_eq_mul, smul_eq_mul,
      map_mul, map_pow, map_ofNat]
  have hcast : (toMatrix₂ (finBasis ℤ_[2] K) (finBasis ℤ_[2] K) C).map (PadicInt.toZModPow a) =
      ((toMatrix₂ (finBasis ℤ_[2] K) (finBasis ℤ_[2] K) C).map (PadicInt.toZModPow (a + b))).map
        (ZMod.castHom (pow_dvd_pow 2 (Nat.le_add_right a b)) (ZMod (2 ^ a))) := by
    ext i j
    simp [PadicInt.cast_toZModPow a (a + b) (Nat.le_add_right a b)]
  rw [map_smul, hmap, smul_mulVec, dotProduct_smul, smul_eq_mul, ZMod.stdAddChar_two_pow_mul, hcast,
    ← ZMod.castHom_apply (h := pow_dvd_pow 2 (Nat.le_add_right a b)), RingHom.map_dotProduct]
  congr 2
  exact funext fun i ↦ RingHom.map_mulVec _ _ c i

/-- **The dyadic Gauss sum of a form divisible enough**: if `2 ^ k` divides the norm of every
vector, every term of the Gauss sum of level `k` is `1`, and the sum is `2 ^ (k n)`. -/
lemma dyadicGaussSum_eq_of_forall_dvd (hC : ∀ x, (2 : ℤ_[2]) ^ k ∣ C x x) :
    C.dyadicGaussSum k = 2 ^ (k * finrank ℤ_[2] K) := by
  have hq (c : Fin (finrank ℤ_[2] K) → ZMod (2 ^ k)) :
      c ⬝ᵥ (toMatrix₂ (finBasis ℤ_[2] K) (finBasis ℤ_[2] K) C).map (PadicInt.toZModPow k) *ᵥ c =
        0 := by
    have hx : c ⬝ᵥ (toMatrix₂ (finBasis ℤ_[2] K) (finBasis ℤ_[2] K) C).map
        (PadicInt.toZModPow k) *ᵥ c = PadicInt.toZModPow k
          (C (∑ i, ((c i).val : ℤ_[2]) • finBasis ℤ_[2] K i)
            (∑ i, ((c i).val : ℤ_[2]) • finBasis ℤ_[2] K i)) := by
      simp [dotProduct, mulVec, Finset.mul_sum, mul_comm]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ mul_left_comm _ _ _
    rcases hC (∑ i, ((c i).val : ℤ_[2]) • finBasis ℤ_[2] K i) with ⟨t, ht⟩
    rw [hx, ht, map_mul, map_pow, map_ofNat,
      (by exact_mod_cast ZMod.natCast_self (2 ^ k) : (2 : ZMod (2 ^ k)) ^ k = 0), zero_mul]
  rw [dyadicGaussSum, quadGaussSum]
  simp [hq, ← pow_mul]

/-- The **dyadic sign** (LMFDB `lattice.conway_genus_symbol`) of a bilinear form `C` over `ℤ_2`
on a finite free module: the Jacobi symbol `(2 | d) = χ₈(d)` of the determinant `d` of `C` in a
basis, on which it does not depend (`dyadicDetSign_eq`). For the unit form of a constituent of a
dyadic Jordan splitting it is the sign `ε_q` of the constituent
(`LinearMap.BilinForm.IsJordanSplitting.dyadicSign`). -/
noncomputable def dyadicDetSign : ℤ :=
  ZMod.χ₈ (PadicInt.toZModPow 3 (toMatrix₂ (finBasis ℤ_[2] K) (finBasis ℤ_[2] K) C).det)

lemma dyadicDetSign_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ_[2] K) :
    C.dyadicDetSign = ZMod.χ₈ (PadicInt.toZModPow 3 (toMatrix₂ b b C).det) := by
  have hcard : Fintype.card (Fin (finrank ℤ_[2] K)) = Fintype.card ι := by
    rw [Fintype.card_fin, finrank_eq_card_basis b]
  rw [dyadicDetSign, ← det_toMatrix₂_reindex _ (Fintype.equivOfCardEq hcard),
    ← LinearMap.toMatrix₂_mul_basis_toMatrix
    ((finBasis ℤ_[2] K).reindex (Fintype.equivOfCardEq hcard))
    ((finBasis ℤ_[2] K).reindex (Fintype.equivOfCardEq hcard)) b b, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_transpose, PadicInt.χ₈_toZModPow_mul_mul
    (Matrix.isUnit_det_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip _ _))]

lemma dyadicDetSign_eq_mul_of_isCompl (hST : IsCompl S T) (horth : ∀ x ∈ S, ∀ y ∈ T, C x y = 0)
    (horth' : ∀ x ∈ T, ∀ y ∈ S, C x y = 0) :
    C.dyadicDetSign = (C.restrict S).dyadicDetSign * (C.restrict T).dyadicDetSign := by
  rw [C.dyadicDetSign_eq (((finBasis ℤ_[2] S).prod (finBasis ℤ_[2] T)).map
    (S.prodEquivOfIsCompl T hST)), C.toMatrix₂_map_prodEquivOfIsCompl _ _ hST horth horth',
    det_fromBlocks_zero₂₁, map_mul, map_mul, dyadicDetSign, dyadicDetSign]

lemma dyadicDetSign_sq (hC : C.IsPerfPair) : C.dyadicDetSign ^ 2 = 1 := by
  rcases (isUnit_det_toMatrix₂_of_isPerfPair (finBasis ℤ_[2] K) hC).map
    (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod 8) with ⟨U, hU⟩
  rw [dyadicDetSign, ← hU, ← MulChar.pow_apply_coe, ZMod.isQuadratic_χ₈.sq_eq_one,
    MulChar.one_apply_coe]

lemma isPerfPair_restrict_of_isCompl (hC : C.IsPerfPair) (hST : IsCompl S T)
    (horth : ∀ x ∈ S, ∀ y ∈ T, C x y = 0) (horth' : ∀ x ∈ T, ∀ y ∈ S, C x y = 0) :
    (C.restrict T).IsPerfPair := by
  have h : IsUnit (toMatrix₂ (((finBasis ℤ_[2] S).prod (finBasis ℤ_[2] T)).map
      (S.prodEquivOfIsCompl T hST)) (((finBasis ℤ_[2] S).prod (finBasis ℤ_[2] T)).map
      (S.prodEquivOfIsCompl T hST)) C).det :=
    isUnit_det_toMatrix₂_of_isPerfPair _ hC
  rw [C.toMatrix₂_map_prodEquivOfIsCompl _ _ hST horth horth', det_fromBlocks_zero₂₁] at h
  exact (finBasis ℤ_[2] T).isPerfPair_of_isUnit_det _ (isUnit_of_mul_isUnit_right h)

lemma dyadicOddity_eq_add_of_isCompl (hC : C.IsPerfPair) (hCs : C.IsSymm)
    (hS : (C.restrict S).IsPerfPair) (hT : (C.restrict T).IsPerfPair) (hST : IsCompl S T)
    (horth : ∀ x ∈ S, ∀ y ∈ T, C x y = 0) (horth' : ∀ x ∈ T, ∀ y ∈ S, C x y = 0) :
    C.dyadicOddity = (C.restrict S).dyadicOddity + (C.restrict T).dyadicOddity := by
  rcases exists_isDyadicCharacteristic hS (hCs.restrict S) with ⟨u, hu⟩
  rcases exists_isDyadicCharacteristic hT (hCs.restrict T) with ⟨v, hv⟩
  have hw : C.IsDyadicCharacteristic (u + v) := fun x ↦ by
    rcases Submodule.mem_sup.mp (hST.sup_eq_top ▸ Submodule.mem_top : x ∈ S ⊔ T) with
      ⟨a, ha, b, hb, rfl⟩
    have h : C (↑u + ↑v) (a + b) - C (a + b) (a + b) =
        (C.restrict S u ⟨a, ha⟩ - C.restrict S ⟨a, ha⟩ ⟨a, ha⟩) +
          (C.restrict T v ⟨b, hb⟩ - C.restrict T ⟨b, hb⟩ ⟨b, hb⟩) := by
      simp [horth _ u.2 _ hb, horth' _ v.2 _ ha, horth _ ha _ hb, horth' _ hb _ ha]
      ring1
    rw [h]
    exact dvd_add (hu _) (hv _)
  rw [dyadicOddity_eq hC hCs hw, dyadicOddity_eq hS (hCs.restrict S) hu,
    dyadicOddity_eq hT (hCs.restrict T) hv]
  simp [horth _ u.2 _ v.2, horth' _ v.2 _ u.2]

lemma finrank_add_finrank_of_isCompl (hST : IsCompl S T) :
    finrank ℤ_[2] S + finrank ℤ_[2] T = finrank ℤ_[2] K := by
  rw [← finrank_prod, (S.prodEquivOfIsCompl T hST).finrank_eq]

lemma isPerfPair_restrict_of_isCompl_orthogonal (hC : C.IsPerfPair) (hCs : C.IsSymm)
    (hST : IsCompl S (C.orthogonal S)) : (C.restrict S).IsPerfPair :=
  C.isPerfPair_restrict_of_isCompl hC hST.symm hCs.orthogonal_apply_eq_zero
    C.apply_orthogonal_eq_zero

lemma isPerfPair_restrict_orthogonal (hC : C.IsPerfPair) (hCs : C.IsSymm)
    (hST : IsCompl S (C.orthogonal S)) : (C.restrict (C.orthogonal S)).IsPerfPair :=
  C.isPerfPair_restrict_of_isCompl hC hST C.apply_orthogonal_eq_zero hCs.orthogonal_apply_eq_zero

lemma dyadicGaussSum_of_isCompl_orthogonal (hC : C.IsPerfPair) (hCs : C.IsSymm)
    (hST : IsCompl S (C.orthogonal S))
    (hS : (C.restrict S).dyadicGaussSum k = (√2 : ℂ) ^ ((k + 1) * finrank ℤ_[2] S) *
      (C.restrict S).dyadicDetSign ^ (k - 1) * ZMod.stdAddChar (C.restrict S).dyadicOddity)
    (hT : (C.restrict (C.orthogonal S)).dyadicGaussSum k =
      (√2 : ℂ) ^ ((k + 1) * finrank ℤ_[2] (C.orthogonal S)) *
        (C.restrict (C.orthogonal S)).dyadicDetSign ^ (k - 1) *
          ZMod.stdAddChar (C.restrict (C.orthogonal S)).dyadicOddity) :
    C.dyadicGaussSum k = (√2 : ℂ) ^ ((k + 1) * finrank ℤ_[2] K) * C.dyadicDetSign ^ (k - 1) *
      ZMod.stdAddChar C.dyadicOddity := by
  rw [C.dyadicGaussSum_eq_mul_of_isCompl k hST C.apply_orthogonal_eq_zero
    hCs.orthogonal_apply_eq_zero, hS, hT, C.dyadicDetSign_eq_mul_of_isCompl hST
    C.apply_orthogonal_eq_zero hCs.orthogonal_apply_eq_zero,
    C.dyadicOddity_eq_add_of_isCompl hC hCs (C.isPerfPair_restrict_of_isCompl_orthogonal hC hCs hST)
      (C.isPerfPair_restrict_orthogonal hC hCs hST) hST C.apply_orthogonal_eq_zero
      hCs.orthogonal_apply_eq_zero,
    ← finrank_add_finrank_of_isCompl hST, AddChar.map_add_eq_mul, mul_add, pow_add]
  push_cast
  ring1

lemma dyadicGaussSum_of_finrank_eq_zero (hC : C.IsPerfPair) (hCs : C.IsSymm)
    (h0 : finrank ℤ_[2] K = 0) :
    C.dyadicGaussSum k = (√2 : ℂ) ^ ((k + 1) * finrank ℤ_[2] K) * C.dyadicDetSign ^ (k - 1) *
      ZMod.stdAddChar C.dyadicOddity := by
  have : Subsingleton K := finrank_zero_iff.mp h0
  rw [C.dyadicGaussSum_eq k (Basis.empty K : Basis (Fin 0) ℤ_[2] K),
    C.dyadicDetSign_eq (Basis.empty K : Basis (Fin 0) ℤ_[2] K), det_isEmpty, map_one, map_one,
    dyadicOddity_eq_zero_of_forall_two_dvd hC hCs fun x ↦ by simp [Subsingleton.elim x 0], h0]
  simp [quadGaussSum]

lemma dyadicGaussSum_two_of_finrank_eq_one (hC : C.IsPerfPair) (hCs : C.IsSymm)
    (h1 : finrank ℤ_[2] K = 1) :
    C.dyadicGaussSum 2 =
      (√2 : ℂ) ^ (3 * finrank ℤ_[2] K) * C.dyadicDetSign * ZMod.stdAddChar C.dyadicOddity := by
  let b : Basis (Fin 1) ℤ_[2] K := finBasisOfFinrankEq ℤ_[2] K h1
  have hu : IsUnit (C (b 0) (b 0)) := by
    simpa using isUnit_det_toMatrix₂_of_isPerfPair b hC
  rw [C.dyadicGaussSum_eq 2 b, C.dyadicDetSign_eq b,
    dyadicOddity_eq_sum hC hCs b fun i j hij ↦ absurd (Subsingleton.elim i j) hij, h1, det_unique,
    LinearMap.toMatrix₂_apply, Fin.default_eq_zero, Fin.sum_univ_one, mul_one,
    ← ZMod.sum_stdAddChar_mul_cast_mul _ (hu.map (PadicInt.toZModPow 3)), quadGaussSum,
    ← (Equiv.funUnique (Fin 1) (ZMod (2 ^ 2))).symm.sum_comp]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  simp [dotProduct, mulVec, PadicInt.cast_toZModPow 2 3 (by norm_num), mul_assoc]

lemma dyadicGaussSum_two_of_finrank_eq_two (hC : C.IsPerfPair) (hCs : C.IsSymm)
    (h2 : finrank ℤ_[2] K = 2) (heven : ∀ x, (2 : ℤ_[2]) ∣ C x x) :
    C.dyadicGaussSum 2 =
      (√2 : ℂ) ^ (3 * finrank ℤ_[2] K) * C.dyadicDetSign * ZMod.stdAddChar C.dyadicOddity := by
  let b : Basis (Fin 2) ℤ_[2] K := finBasisOfFinrankEq ℤ_[2] K h2
  have hmat : (toMatrix₂ b b C).map (PadicInt.toZModPow 2) =
      !![(ZMod.cast (PadicInt.toZModPow 3 (C (b 0) (b 0))) : ZMod (2 ^ 2)),
        ZMod.cast (PadicInt.toZModPow 3 (C (b 0) (b 1)));
        ZMod.cast (PadicInt.toZModPow 3 (C (b 0) (b 1))),
        ZMod.cast (PadicInt.toZModPow 3 (C (b 1) (b 1)))] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [PadicInt.cast_toZModPow 2 3 (by norm_num), hCs.eq (b 1) (b 0)]
  have hdet : PadicInt.toZModPow 3 (toMatrix₂ b b C).det =
      PadicInt.toZModPow 3 (C (b 0) (b 0)) * PadicInt.toZModPow 3 (C (b 1) (b 1)) -
        PadicInt.toZModPow 3 (C (b 0) (b 1)) * PadicInt.toZModPow 3 (C (b 0) (b 1)) := by
    simp [det_fin_two, hCs.eq (b 1) (b 0)]
  have h4 (x : K) : 4 * PadicInt.toZModPow 3 (C x x) = 0 := by
    rcases heven x with ⟨t, ht⟩
    rw [ht, map_mul, map_ofNat, ← mul_assoc, (by decide : (4 * 2 : ZMod (2 ^ 3)) = 0), zero_mul]
  rw [C.dyadicGaussSum_eq 2 b, C.dyadicDetSign_eq b,
    dyadicOddity_eq_zero_of_forall_two_dvd hC hCs heven, h2, hmat, hdet,
    (by norm_num : 3 * 2 = 2 * 3), Complex.sqrt_two_pow_two_mul, AddChar.map_zero_eq_one, mul_one]
  exact_mod_cast quadGaussSum_cast_of_four_mul_eq_zero _ _ _ (h4 _) (h4 _)
    (hdet ▸ (isUnit_det_toMatrix₂_of_isPerfPair b hC).map (PadicInt.toZModPow 3))

lemma dyadicGaussSum_three_of_finrank_eq_one (hC : C.IsPerfPair) (hCs : C.IsSymm)
    (h1 : finrank ℤ_[2] K = 1) : C.dyadicGaussSum 3 = 4 * ZMod.stdAddChar C.dyadicOddity := by
  let b : Basis (Fin 1) ℤ_[2] K := finBasisOfFinrankEq ℤ_[2] K h1
  have hu : IsUnit (C (b 0) (b 0)) := by
    simpa using isUnit_det_toMatrix₂_of_isPerfPair b hC
  rw [C.dyadicGaussSum_eq 3 b,
    dyadicOddity_eq_sum hC hCs b fun i j hij ↦ absurd (Subsingleton.elim i j) hij,
    Fin.sum_univ_one, quadGaussSum, ← (Equiv.funUnique (Fin 1) (ZMod (2 ^ 3))).symm.sum_comp]
  refine (Finset.sum_congr rfl fun a _ ↦ ?_).trans
    (ZMod.sum_stdAddChar_mul_mul_eight _ (hu.map (PadicInt.toZModPow 3)))
  simp [dotProduct, mulVec]

lemma dyadicGaussSum_three_of_finrank_eq_two (hC : C.IsPerfPair) (hCs : C.IsSymm)
    (h2 : finrank ℤ_[2] K = 2) (heven : ∀ x, (2 : ℤ_[2]) ∣ C x x) : C.dyadicGaussSum 3 = 16 := by
  let b : Basis (Fin 2) ℤ_[2] K := finBasisOfFinrankEq ℤ_[2] K h2
  have hmat : (toMatrix₂ b b C).map (PadicInt.toZModPow 3) =
      !![PadicInt.toZModPow 3 (C (b 0) (b 0)), PadicInt.toZModPow 3 (C (b 0) (b 1));
        PadicInt.toZModPow 3 (C (b 0) (b 1)), PadicInt.toZModPow 3 (C (b 1) (b 1))] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hCs.eq (b 1) (b 0)]
  have hdet : PadicInt.toZModPow 3 (toMatrix₂ b b C).det =
      PadicInt.toZModPow 3 (C (b 0) (b 0)) * PadicInt.toZModPow 3 (C (b 1) (b 1)) -
        PadicInt.toZModPow 3 (C (b 0) (b 1)) * PadicInt.toZModPow 3 (C (b 0) (b 1)) := by
    simp [det_fin_two, hCs.eq (b 1) (b 0)]
  have h4 (x : K) : 4 * PadicInt.toZModPow 3 (C x x) = 0 := by
    rcases heven x with ⟨t, ht⟩
    rw [ht, map_mul, map_ofNat, ← mul_assoc, (by decide : (4 * 2 : ZMod (2 ^ 3)) = 0), zero_mul]
  rw [C.dyadicGaussSum_eq 3 b, hmat]
  exact quadGaussSum_of_four_mul_eq_zero _ _ _ (h4 _) (h4 _)
    (hdet ▸ (isUnit_det_toMatrix₂_of_isPerfPair b hC).map (PadicInt.toZModPow 3))

lemma dyadicGaussSum_of_finrank_eq_one (hk : k = 2 ∨ k = 3) (hC : C.IsPerfPair) (hCs : C.IsSymm)
    (h1 : finrank ℤ_[2] K = 1) :
    C.dyadicGaussSum k = (√2 : ℂ) ^ ((k + 1) * finrank ℤ_[2] K) * C.dyadicDetSign ^ (k - 1) *
      ZMod.stdAddChar C.dyadicOddity := by
  rcases hk with rfl | rfl
  · simpa using C.dyadicGaussSum_two_of_finrank_eq_one hC hCs h1
  · rw [C.dyadicGaussSum_three_of_finrank_eq_one hC hCs h1, h1,
      (by norm_num : (3 + 1) * 1 = 2 * 2), Complex.sqrt_two_pow_two_mul, (by norm_num : 3 - 1 = 2),
      ← Int.cast_pow, C.dyadicDetSign_sq hC]
    norm_num

lemma dyadicGaussSum_of_finrank_eq_two (hk : k = 2 ∨ k = 3) (hC : C.IsPerfPair) (hCs : C.IsSymm)
    (h2 : finrank ℤ_[2] K = 2) (heven : ∀ x, (2 : ℤ_[2]) ∣ C x x) :
    C.dyadicGaussSum k = (√2 : ℂ) ^ ((k + 1) * finrank ℤ_[2] K) * C.dyadicDetSign ^ (k - 1) *
      ZMod.stdAddChar C.dyadicOddity := by
  rcases hk with rfl | rfl
  · simpa using C.dyadicGaussSum_two_of_finrank_eq_two hC hCs h2 heven
  · rw [C.dyadicGaussSum_three_of_finrank_eq_two hC hCs h2 heven, h2,
      (by norm_num : (3 + 1) * 2 = 2 * 4), Complex.sqrt_two_pow_two_mul, (by norm_num : 3 - 1 = 2),
      ← Int.cast_pow, C.dyadicDetSign_sq hC,
      dyadicOddity_eq_zero_of_forall_two_dvd hC hCs heven]
    norm_num

/-- **The dyadic Gauss sums of a unimodular form modulo `4` and `8`.** For a unimodular symmetric
form `C` over `ℤ_2` of rank `n`, with sign `ε = χ₈(det C)` and oddity `t`, and `k = 2, 3`, the sum
`Σ_(x ∈ K / 2 ^ k K) exp(2 π i C(x, x) / 2 ^ k)` is `√2 ^ ((k + 1) n) ε ^ (k - 1) ζ₈ ^ t`. The
proof splits off a vector of odd norm or an even perfect binary summand, the rank-`1`/rank-`2`
normal form of unimodular dyadic forms. -/
lemma dyadicGaussSum_of_eq_two_or_eq_three (hk : k = 2 ∨ k = 3) (hC : C.IsPerfPair)
    (hCs : C.IsSymm) :
    C.dyadicGaussSum k = (√2 : ℂ) ^ ((k + 1) * finrank ℤ_[2] K) * C.dyadicDetSign ^ (k - 1) *
      ZMod.stdAddChar C.dyadicOddity := by
  induction hn : finrank ℤ_[2] K using Nat.strong_induction_on generalizing K with
  | _ n ih =>
  rw [← hn]
  rcases n with _ | n
  · exact C.dyadicGaussSum_of_finrank_eq_zero k hC hCs hn
  by_cases hodd : ∃ x, IsUnit (C x x)
  · rcases hodd with ⟨x, hx⟩
    have hST : IsCompl (ℤ_[2] ∙ x) (C.orthogonal (ℤ_[2] ∙ x)) :=
      C.isCompl_span_singleton_orthogonal_of_isUnit x hx
    have hx0 : x ≠ 0 := fun h ↦ by simp [h] at hx
    have h1 : finrank ℤ_[2] (ℤ_[2] ∙ x) = 1 :=
      le_antisymm ((finrank_span_le_card ({x} : Set K)).trans (by simp))
        (Nat.one_le_iff_ne_zero.mpr fun h ↦
          hx0 (Submodule.span_singleton_eq_bot.mp (Submodule.finrank_eq_zero.mp h)))
    have hrank : finrank ℤ_[2] (ℤ_[2] ∙ x) + finrank ℤ_[2] (C.orthogonal (ℤ_[2] ∙ x)) =
        finrank ℤ_[2] K :=
      finrank_add_finrank_of_isCompl hST
    refine C.dyadicGaussSum_of_isCompl_orthogonal k hC hCs hST ?_ ?_
    · exact (C.restrict _).dyadicGaussSum_of_finrank_eq_one k hk
        (C.isPerfPair_restrict_of_isCompl_orthogonal hC hCs hST) (hCs.restrict _) h1
    · exact ih _ (by omega) (C.restrict _) (C.isPerfPair_restrict_orthogonal hC hCs hST)
        (hCs.restrict _) rfl
  have heven (y : K) : (2 : ℤ_[2]) ∣ C y y := by
    exact_mod_cast (PadicInt.norm_lt_one_iff_dvd (C y y)).mp
      (PadicInt.mem_nonunits.mp (mem_nonunits_iff.mpr fun hy ↦ hodd ⟨y, hy⟩))
  rcases n with _ | n
  · have hdet : IsUnit (toMatrix₂ (finBasisOfFinrankEq ℤ_[2] K hn)
        (finBasisOfFinrankEq ℤ_[2] K hn) C).det :=
      isUnit_det_toMatrix₂_of_isPerfPair _ hC
    exact absurd ⟨_, by simpa using hdet⟩ hodd
  rcases hCs.exists_binary_isPerfPair_isCompl_orthogonal _ (finBasisOfFinrankEq ℤ_[2] K hn) heven
    (mem_nonunits_iff.mp PadicInt.p_nonunit) (isUnit_det_toMatrix₂_of_isPerfPair _ hC) with
    ⟨S, hS2, hSperf, hST⟩
  have hrank : finrank ℤ_[2] S + finrank ℤ_[2] (C.orthogonal S) = finrank ℤ_[2] K :=
    finrank_add_finrank_of_isCompl hST
  refine C.dyadicGaussSum_of_isCompl_orthogonal k hC hCs hST ?_ ?_
  · exact (C.restrict S).dyadicGaussSum_of_finrank_eq_two k hk hSperf (hCs.restrict S) hS2
      fun y ↦ heven y
  · exact ih _ (by omega) (C.restrict _) (C.isPerfPair_restrict_orthogonal hC hCs hST)
      (hCs.restrict _) rfl

/-- **The recursion of the dyadic Gauss sums of a unimodular form**: for a unimodular symmetric
form of rank `n` and `k ≥ 2`, the Gauss sum of level `k + 2` is `2 ^ n` times that of level `k`.
Only the vectors of `2 K` contribute to the sum of level `k + 2` (the others cancel in pairs of
characters), and the form on `2 K` is `4` times the form on `K`. -/
lemma dyadicGaussSum_add_two (hk : 2 ≤ k) (hC : C.IsPerfPair) (hCs : C.IsSymm) :
    C.dyadicGaussSum (k + 2) = 2 ^ finrank ℤ_[2] K * C.dyadicGaussSum k := by
  have hsymm : ((toMatrix₂ (finBasis ℤ_[2] K) (finBasis ℤ_[2] K) C).map
      (PadicInt.toZModPow (k + 2)))ᵀ =
        (toMatrix₂ (finBasis ℤ_[2] K) (finBasis ℤ_[2] K) C).map (PadicInt.toZModPow (k + 2)) := by
    ext i j
    simp [hCs.eq ((finBasis ℤ_[2] K) i) ((finBasis ℤ_[2] K) j)]
  have hdet : IsUnit ((toMatrix₂ (finBasis ℤ_[2] K) (finBasis ℤ_[2] K) C).map
      (PadicInt.toZModPow (k + 2))).det := by
    have hu : IsUnit (PadicInt.toZModPow (k + 2)
        (toMatrix₂ (finBasis ℤ_[2] K) (finBasis ℤ_[2] K) C).det) :=
      (isUnit_det_toMatrix₂_of_isPerfPair _ hC).map _
    rwa [RingHom.map_det, RingHom.mapMatrix_apply] at hu
  have h4 : (4 • (toMatrix₂ (finBasis ℤ_[2] K) (finBasis ℤ_[2] K) C).map
      (PadicInt.toZModPow (k + 2))).quadGaussSum =
        ((2 : ℤ_[2]) ^ 2 • C).dyadicGaussSum (k + 2) := by
    rw [dyadicGaussSum, map_smul]
    congr 1
    ext i j
    rw [Matrix.smul_apply, map_apply, map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow,
      map_ofNat, nsmul_eq_mul, Nat.cast_ofNat]
    ring1
  have h : 2 ^ Fintype.card (Fin (finrank ℤ_[2] K)) * C.dyadicGaussSum (k + 2) =
      ((2 : ℤ_[2]) ^ 2 • C).dyadicGaussSum (k + 2) :=
    (quadGaussSum_add_two k hk _ hsymm hdet).trans h4
  rw [dyadicGaussSum_two_pow_smul, Fintype.card_fin] at h
  refine mul_left_cancel₀ (pow_ne_zero (finrank ℤ_[2] K) (two_ne_zero : (2 : ℂ) ≠ 0)) ?_
  rw [h]
  ring1

/-- **The dyadic Gauss sums of a unimodular form.** For a unimodular symmetric form `C` over
`ℤ_2` of rank `n`, with sign `ε = χ₈(det C)` and oddity `t`, and every `k ≥ 2`, the Gauss sum
`Σ_(x ∈ K / 2 ^ k K) exp(2 π i C(x, x) / 2 ^ k)` is `√2 ^ ((k + 1) n) ε ^ (k - 1) ζ₈ ^ t`; that is,
`Σ_(x ∈ K / 2 ^ s K) exp(2 π i C(x, x) / 2 ^ (s + 1)) = 2 ^ (n s / 2) ε ^ s ζ₈ ^ t` for `s ≥ 1`. -/
lemma dyadicGaussSum_eq_of_isPerfPair (hk : 2 ≤ k) (hC : C.IsPerfPair) (hCs : C.IsSymm) :
    C.dyadicGaussSum k = (√2 : ℂ) ^ ((k + 1) * finrank ℤ_[2] K) * C.dyadicDetSign ^ (k - 1) *
      ZMod.stdAddChar C.dyadicOddity := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases (by omega : k = 2 ∨ k = 3 ∨ 4 ≤ k) with h | h | h
  · exact C.dyadicGaussSum_of_eq_two_or_eq_three k (Or.inl h) hC hCs
  · exact C.dyadicGaussSum_of_eq_two_or_eq_three k (Or.inr h) hC hCs
  rcases Nat.exists_eq_add_of_le' h with ⟨m, rfl⟩
  have hε : (C.dyadicDetSign : ℂ) ^ 2 = 1 := by
    exact_mod_cast C.dyadicDetSign_sq hC
  rw [(by omega : m + 4 = m + 2 + 2), C.dyadicGaussSum_add_two (m + 2) (by omega) hC hCs,
    ih (m + 2) (by omega) (by omega), (by omega : m + 2 - 1 = m + 1),
    (by omega : m + 2 + 2 - 1 = m + 1 + 2), pow_add (C.dyadicDetSign : ℂ) (m + 1) 2, hε,
    ← Complex.sqrt_two_pow_two_mul]
  ring1

variable {B : BilinForm ℤ_[2] K} {N : ℕ → Submodule ℤ_[2] K}
  (hN : B.IsJordanSplitting ((2 : ℕ) : ℤ_[2]) N)

/-- **The dyadic Gauss sum factors over a Jordan splitting**: if the constituents `N j`,
`j ≥ J`, vanish, the Gauss sum of `B` is the product of those of its restrictions to the
constituents `N j`, `j < J`. -/
lemma IsJordanSplitting.dyadicGaussSum_eq_prod (h : B.IsJordanSplitting ((2 : ℕ) : ℤ_[2]) N) {J : ℕ}
    (hJ : ∀ j, J ≤ j → N j = ⊥) :
    B.dyadicGaussSum k = ∏ j : Fin J, (B.restrict (N j)).dyadicGaussSum k := by
  refine B.dyadicGaussSum_eq_prod_of_isInternal k
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨iSupIndep.comp h.isInternal.submodule_iSupIndep Fin.val_injective, ?_⟩)
    fun i j hij x hx y hy ↦ h.apply_eq_zero i j (fun hij' ↦ hij (Fin.ext hij')) x hx y hy
  refine eq_top_iff.mpr (h.isInternal.submodule_iSup_eq_top ▸ iSup_le fun i ↦ ?_)
  by_cases hi : i < J
  · exact le_iSup_of_le (⟨i, hi⟩ : Fin J) le_rfl
  · rw [hJ i (not_lt.mp hi)]
    exact bot_le

/-- **The dyadic Gauss sums of the constituents of a dyadic Jordan splitting**: for the unit form
`f` of the constituent of scale `2 ^ j`, of rank `n`, sign `ε_q` and oddity `t_q`, and `k ≥ 2`,
the Gauss sum of level `k` is `√2 ^ ((k + 1) n) ε_q ^ (k - 1) ζ₈ ^ t_q`. -/
lemma IsJordanSplitting.dyadicGaussSum_unitForm (hB : B.IsSymm) (j : ℕ) (hk : 2 ≤ k) :
    (hN.unitForm j).dyadicGaussSum k = (√2 : ℂ) ^ ((k + 1) * finrank ℤ_[2] (N j)) *
      hN.dyadicSign j ^ (k - 1) * ZMod.stdAddChar (hN.dyadicOddity j) :=
  (hN.unitForm j).dyadicGaussSum_eq_of_isPerfPair k hk (hN.isPerfPair_unitForm j)
    (hN.isSymm_unitForm hB)

/-- **The dyadic Gauss sum of a Jordan constituent**: the restriction of `B` to the constituent
`N j` of a dyadic Jordan splitting, of rank `n`, has Gauss sum of level `a + j` equal to
`2 ^ (j n)` times the Gauss sum of level `a` of its unit form. -/
lemma IsJordanSplitting.dyadicGaussSum_restrict (a j : ℕ) :
    (B.restrict (N j)).dyadicGaussSum (a + j) =
      2 ^ (j * finrank ℤ_[2] (N j)) * (hN.unitForm j).dyadicGaussSum a := by
  rw [← hN.pow_smul_unitForm, Nat.cast_ofNat, dyadicGaussSum_two_pow_smul]

end LinearMap.BilinForm

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {L : IntegralLattice V} {M : IntegralLattice W}

/-- **The dyadic Gauss sums are genus invariants**: lattices in the same genus have the same
Gauss sum `Σ_(x ∈ L ⊗ ℤ_2 / 2 ^ k) exp(2 π i B(x, x) / 2 ^ k)` for every `k`. -/
lemma SameGenus.dyadicGaussSum_eq (h : L.SameGenus M) (k : ℕ) :
    (L.localIntegralForm 2).dyadicGaussSum k = (M.localIntegralForm 2).dyadicGaussSum k :=
  BilinForm.dyadicGaussSum_eq_of_equivalent _ k (h.localIntegralForm_equivalent 2)

end TauCeti.IntegralLattice
