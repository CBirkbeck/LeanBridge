import LeanBridge.ForMathlib.NumberTheory.Hypergeometric.BezoutModule
import LeanBridge.ForMathlib.NumberTheory.Hypergeometric.GammaVector
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The gamma vector of a hypergeometric family is unique

The LMFDB (`hgm.defining_parameters`) characterises the gamma vector `γ` of defining parameters
`(A, B)` as the list of nonzero integers in ascending order with
`∏_{g ∈ γ, g > 0} (x^g - 1) / ∏_{g ∈ γ, g < 0} (x^{-g} - 1) = Φ_A / Φ_B`, where
`Φ_C = ∏_{c ∈ C} Φ_c` (`Hypergeometric.CuspIndex.cyclotomicProd`). This identity alone does not
determine `γ`: a pair `n, -n` contributes `(x^n - 1) / (x^n - 1) = 1`, so for `A = [2]` and
`B = [1]` both `[-1, -1, 2]` and `[-3, -1, -1, 2, 3]` satisfy it. It determines `γ` among the
reduced lists, those never containing both `n` and `-n`, and `Hypergeometric.Parameters.gammaVector`
is reduced.

The proof rests on the multiplicative independence of the polynomials `x^n - 1`, `n ≥ 1`, in the
field `ℚ(x)` of rational functions over `ℤ`. If `∏_n (x^n - 1)^{e(n)} = 1` and `n` is the largest
index with `e(n) ≠ 0`, say `e(n) > 0`, then after clearing denominators a primitive `n`-th root of
unity is a root of the side containing `x^n - 1` but not of the other side, whose factors
`x^m - 1` all have `0 < m < n`. Hence the rational function of a list `γ` determines the
differences `count n γ - count (-n) γ` for `n ≥ 1`, and these determine a reduced list up to order.

## Main definitions

* `Hypergeometric.gammaRatFunc` (LMFDB `hgm.defining_parameters`): the rational function
  `∏_{g ∈ γ, g > 0} (x^g - 1) / ∏_{g ∈ γ, g < 0} (x^{-g} - 1)` of a list `γ` of integers.

## Main results

* `Hypergeometric.eq_zero_of_prod_zpow_eq_one`: the polynomials `x^n - 1`, `n ≥ 1`, are
  multiplicatively independent in `ℚ(x)`.
* `Hypergeometric.perm_of_gammaRatFunc_eq`: two reduced lists with the same rational function are
  equal up to order.
* `Hypergeometric.Parameters.neg_notMem_gammaVector` (LMFDB `hgm.defining_parameters`): the gamma
  vector is reduced.
* `Hypergeometric.Parameters.gammaRatFunc_gammaVector` (LMFDB `hgm.defining_parameters`): the
  rational function of the gamma vector is `Φ_A / Φ_B`.
* `Hypergeometric.Parameters.eq_gammaVector` (LMFDB `hgm.defining_parameters`): the gamma vector is
  the only reduced list in ascending order whose rational function is `Φ_A / Φ_B`.
-/

open Finset Polynomial

namespace Hypergeometric

variable {S : Finset ℕ} {e : ℕ → ℤ} {n : ℕ} {g : ℤ} {γ γ' : List ℤ}

variable (γ) in
/-- The rational function `∏_{g ∈ γ, g > 0} (x^g - 1) / ∏_{g ∈ γ, g < 0} (x^{-g} - 1)` of a list
`γ` of integers (LMFDB `hgm.defining_parameters`), in the field `ℚ(x)` of rational functions over
`ℤ`. The gamma vector of defining parameters `(A, B)` is the only reduced list in ascending order
whose rational function is `Φ_A / Φ_B` (`Hypergeometric.Parameters.eq_gammaVector`). -/
noncomputable def gammaRatFunc : RatFunc ℤ :=
  algebraMap ℤ[X] (RatFunc ℤ) ((γ.filter (0 < ·)).map fun g ↦ X ^ g.natAbs - 1).prod /
    algebraMap ℤ[X] (RatFunc ℤ) ((γ.filter (· < 0)).map fun g ↦ X ^ g.natAbs - 1).prod

variable (γ) in
lemma gammaRatFunc_eq_prod : gammaRatFunc γ =
    (γ.map fun g ↦ algebraMap ℤ[X] (RatFunc ℤ) (X ^ g.natAbs - 1) ^ g.sign).prod := by
  induction γ with
  | nil => simp [gammaRatFunc]
  | cons g γ ih =>
    rw [List.map_cons, List.prod_cons, ← ih, gammaRatFunc, gammaRatFunc]
    rcases lt_trichotomy g 0 with hg | rfl | hg
    · rw [List.filter_cons_of_neg (by simpa using hg.le),
        List.filter_cons_of_pos (by simpa using hg), List.map_cons, List.prod_cons, map_mul,
        Int.sign_eq_neg_one_of_neg hg, zpow_neg_one]
      ring1
    · simp
    · rw [List.filter_cons_of_pos (by simpa using hg),
        List.filter_cons_of_neg (by simpa using hg.le), List.map_cons, List.prod_cons, map_mul,
        Int.sign_eq_one_of_pos hg, zpow_one, mul_div_assoc]

variable (γ) in
private lemma prod_zpow_sign_eq_prod (hS : ∀ n ∈ S, 0 < n) (hγ : ∀ g ∈ γ, g ≠ 0 → g.natAbs ∈ S) :
    (γ.map fun g ↦ algebraMap ℤ[X] (RatFunc ℤ) (X ^ g.natAbs - 1) ^ g.sign).prod =
      ∏ n ∈ S, algebraMap ℤ[X] (RatFunc ℤ) (X ^ n - 1) ^
        (γ.map fun g ↦ if g.natAbs = n then g.sign else 0).sum := by
  induction γ with
  | nil => simp
  | cons g γ ih =>
    rw [List.map_cons, List.prod_cons, ih fun g' hg' ↦ hγ g' (List.mem_cons_of_mem g hg')]
    simp_rw [List.map_cons, List.sum_cons]
    rw [prod_congr rfl fun n hn ↦
      zpow_add₀ (algebraMap_X_pow_sub_one_ne_zero (hS n hn)) _ _, prod_mul_distrib]
    congr 1
    rcases eq_or_ne g 0 with rfl | hg
    · simp only [Int.sign_zero, ite_self, zpow_zero, prod_const_one]
    · rw [prod_eq_single_of_mem _ (hγ g List.mem_cons_self hg) fun n _ hn ↦ by
        rw [ite_eq_right (Ne.symm hn), zpow_zero], ite_eq_left rfl]

variable (γ) in
private lemma sum_ite_natAbs_eq (hn : 0 < n) :
    (γ.map fun g ↦ if g.natAbs = n then g.sign else 0).sum = γ.count (n : ℤ) -
      γ.count (-n : ℤ) := by
  induction γ with
  | nil => simp
  | cons g γ ih =>
    rw [List.map_cons, List.sum_cons, ih, List.count_cons, List.count_cons]
    rcases lt_trichotomy g 0 with hg | rfl | hg
    · rw [Int.sign_eq_neg_one_of_neg hg]
      split_ifs <;> simp_all <;> omega
    · simp
      omega
    · rw [Int.sign_eq_one_of_pos hg]
      split_ifs <;> simp_all <;> omega

private lemma count_eq_toNat (hγ : ∀ g ∈ γ, -g ∉ γ) :
    γ.count g = ((γ.count g : ℤ) - γ.count (-g)).toNat := by
  have h : γ.count g = 0 ∨ γ.count (-g) = 0 := by
    by_contra! h
    exact hγ g (List.count_pos_iff.mp (Nat.pos_of_ne_zero h.1))
      (List.count_pos_iff.mp (Nat.pos_of_ne_zero h.2))
  omega

private lemma nonpos_of_prod_zpow_eq_one (hS : ∀ n ∈ S, 0 < n)
    (h : ∏ n ∈ S, algebraMap ℤ[X] (RatFunc ℤ) (X ^ n - 1) ^ e n = 1) (hn : n ∈ S)
    (hmax : ∀ m ∈ S, e m ≠ 0 → m ≤ n) : e n ≤ 0 := by
  by_contra! hpos
  have hPQ : ∏ m ∈ S, (X ^ m - 1 : ℤ[X]) ^ (e m).toNat = ∏ m ∈ S, (X ^ m - 1) ^ (-e m).toNat := by
    refine IsFractionRing.injective ℤ[X] (RatFunc ℤ) ?_
    rw [map_prod, map_prod, ← div_eq_one_iff_eq, ← prod_div_distrib, ← h]
    · refine prod_congr rfl fun m hm ↦ ?_
      rw [map_pow, map_pow, ← zpow_natCast, ← zpow_natCast,
        ← zpow_sub₀ (algebraMap_X_pow_sub_one_ne_zero (hS m hm)), Int.toNat_sub_toNat_neg]
    · refine prod_ne_zero_iff.mpr fun m hm ↦ ?_
      rw [map_pow]
      exact pow_ne_zero _ (algebraMap_X_pow_sub_one_ne_zero (hS m hm))
  rcases (⟨_, Complex.isPrimitiveRoot_exp n (hS n hn).ne'⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ n) with
    ⟨ζ, hζ⟩
  have hζPQ : ∏ m ∈ S, (ζ ^ m - 1) ^ (e m).toNat = ∏ m ∈ S, (ζ ^ m - 1) ^ (-e m).toNat := by
    simpa using congrArg (aeval ζ) hPQ
  refine prod_ne_zero_iff.mpr (fun m hm ↦ ?_) (hζPQ ▸ prod_eq_zero hn ?_)
  · by_cases hm' : e m < 0
    · refine pow_ne_zero _ (sub_ne_zero.mpr <| hζ.pow_ne_one_of_pos_of_lt (hS m hm).ne' ?_)
      refine (hmax m hm hm'.ne).lt_of_ne fun hmn ↦ ?_
      subst hmn
      omega
    · rw [show (-e m).toNat = 0 by omega, pow_zero]
      exact one_ne_zero
  · rw [hζ.pow_eq_one, sub_self, zero_pow]
    omega

/-- **The polynomials `x^n - 1`, `n ≥ 1`, are multiplicatively independent** in the field `ℚ(x)`
of rational functions over `ℤ`: if `∏_{n ∈ S} (x^n - 1)^{e(n)} = 1` for a finite set `S` of
positive integers, then `e(n) = 0` for every `n ∈ S`. -/
lemma eq_zero_of_prod_zpow_eq_one (hS : ∀ n ∈ S, 0 < n)
    (h : ∏ n ∈ S, algebraMap ℤ[X] (RatFunc ℤ) (X ^ n - 1) ^ e n = 1) (hn : n ∈ S) : e n = 0 := by
  by_contra hen
  have hT : (S.filter (e · ≠ 0)).Nonempty := ⟨n, mem_filter.mpr ⟨hn, hen⟩⟩
  rcases mem_filter.mp ((S.filter (e · ≠ 0)).max'_mem hT) with ⟨hm, hem⟩
  have hmax (k : ℕ) (hk : k ∈ S) (hek : e k ≠ 0) : k ≤ (S.filter (e · ≠ 0)).max' hT :=
    le_max' _ k (mem_filter.mpr ⟨hk, hek⟩)
  exact hem <| le_antisymm (nonpos_of_prod_zpow_eq_one hS h hm hmax) <| neg_nonpos.mp <|
    nonpos_of_prod_zpow_eq_one hS (e := fun k ↦ -e k)
      (by simp_rw [zpow_neg, prod_inv_distrib, h, inv_one]) hm fun k hk hek ↦
        hmax k hk (neg_ne_zero.mp hek)

/-- **Two reduced lists with the same rational function are equal up to order**: if neither `γ`
nor `γ'` contains both `g` and `-g` (in particular `0`), and
`∏_{g ∈ γ, g > 0} (x^g - 1) / ∏_{g ∈ γ, g < 0} (x^{-g} - 1)` is the same for `γ` and `γ'`, then `γ`
is a permutation of `γ'`. -/
lemma perm_of_gammaRatFunc_eq (hγ : ∀ g ∈ γ, -g ∉ γ) (hγ' : ∀ g ∈ γ', -g ∉ γ')
    (h : gammaRatFunc γ = gammaRatFunc γ') : γ.Perm γ' := by
  let S : Finset ℕ := ((γ ++ γ').map Int.natAbs).toFinset.erase 0
  have hS (n : ℕ) (hn : n ∈ S) : 0 < n := Nat.pos_of_ne_zero (mem_erase.mp hn).1
  have hmem (g : ℤ) (hg : g ∈ γ ++ γ') (hg0 : g ≠ 0) : g.natAbs ∈ S :=
    mem_erase.mpr ⟨Int.natAbs_ne_zero.mpr hg0, List.mem_toFinset.mpr (List.mem_map_of_mem hg)⟩
  rw [gammaRatFunc_eq_prod, gammaRatFunc_eq_prod,
    prod_zpow_sign_eq_prod γ hS fun g hg ↦ hmem g (List.mem_append_left _ hg),
    prod_zpow_sign_eq_prod γ' hS fun g hg ↦ hmem g (List.mem_append_right _ hg)] at h
  have he (n : ℕ) (hn : n ∈ S) : (γ.count (n : ℤ) : ℤ) - γ.count (-n : ℤ) =
      (γ'.count (n : ℤ) : ℤ) - γ'.count (-n : ℤ) := by
    rw [← sum_ite_natAbs_eq γ (hS n hn), ← sum_ite_natAbs_eq γ' (hS n hn), ← sub_eq_zero]
    refine eq_zero_of_prod_zpow_eq_one hS (e := fun k ↦
      (γ.map fun g ↦ if g.natAbs = k then g.sign else 0).sum -
        (γ'.map fun g ↦ if g.natAbs = k then g.sign else 0).sum) ?_ hn
    rw [prod_congr rfl fun n hn ↦ zpow_sub₀ (algebraMap_X_pow_sub_one_ne_zero (hS n hn)) _ _,
      prod_div_distrib, h, div_self]
    exact prod_ne_zero_iff.mpr fun n hn ↦
      zpow_ne_zero _ (algebraMap_X_pow_sub_one_ne_zero (hS n hn))
  refine List.perm_iff_count.mpr fun g ↦ ?_
  rcases eq_or_ne g 0 with rfl | hg
  · rw [List.count_eq_zero.mpr fun h ↦ hγ 0 h (by rwa [neg_zero]),
      List.count_eq_zero.mpr fun h ↦ hγ' 0 h (by rwa [neg_zero])]
  by_cases hgS : g.natAbs ∈ S
  · have hg' : (γ.count (g.natAbs : ℤ) : ℤ) - γ.count (-g.natAbs : ℤ) =
        (γ'.count (g.natAbs : ℤ) : ℤ) - γ'.count (-g.natAbs : ℤ) :=
      he _ hgS
    rw [count_eq_toNat hγ, count_eq_toNat hγ']
    rcases Int.natAbs_eq g with h | h <;> rw [h]
    · omega
    · rw [neg_neg]
      omega
  · rw [List.count_eq_zero.mpr fun h ↦ hgS (hmem g (List.mem_append_left _ h) hg),
      List.count_eq_zero.mpr fun h ↦ hgS (hmem g (List.mem_append_right _ h) hg)]

variable {d : ℕ} (P : Parameters d)

lemma Parameters.sortedLE_gammaVector : P.gammaVector.SortedLE :=
  (Multiset.pairwise_sort _ _).sortedLE

lemma Parameters.count_gammaVector_zero : P.gammaVector.count 0 = 0 := by
  rw [count_gammaVector]
  refine sum_eq_zero fun m hm ↦ ite_eq_right_iff.mpr fun h ↦ ?_
  rcases mul_eq_zero.mp h with h | h
  · rw [Int.sign_eq_zero_iff_zero.mp h, Int.natAbs_zero]
  · exact absurd h (Nat.cast_ne_zero.mpr (P.pos_of_mem_gammaSupport hm).ne')

private lemma Parameters.count_gammaVector_eq (hg : g ≠ 0) : P.gammaVector.count g =
    if 0 < g then (P.gammaExponent g.natAbs).toNat else (-P.gammaExponent g.natAbs).toNat := by
  rcases Int.natAbs_eq g with h | h
  · rw [ite_eq_left (by omega)]
    nth_rw 1 [h]
    exact P.count_gammaVector_pos (by omega)
  · rw [ite_eq_right (by omega)]
    nth_rw 1 [h]
    exact P.count_gammaVector_neg (by omega)

/-- **The gamma vector is reduced** (LMFDB `hgm.defining_parameters`): it never contains both `g`
and `-g`, so in particular all its entries are nonzero. -/
lemma Parameters.neg_notMem_gammaVector (hg : g ∈ P.gammaVector) : -g ∉ P.gammaVector := by
  intro hg'
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact (List.count_pos_iff.mpr hg).ne' P.count_gammaVector_zero
  have h : 0 < P.gammaVector.count g := List.count_pos_iff.mpr hg
  have h' : 0 < P.gammaVector.count (-g) := List.count_pos_iff.mpr hg'
  rw [P.count_gammaVector_eq hg0] at h
  rw [P.count_gammaVector_eq (neg_ne_zero.mpr hg0), Int.natAbs_neg] at h'
  split_ifs at h h' <;> omega

private lemma Parameters.natAbs_mem_gammaSupport (hg : g ∈ P.gammaVector) (hg0 : g ≠ 0) :
    g.natAbs ∈ P.gammaSupport := by
  by_contra hS
  have h : 0 < P.gammaVector.count g := List.count_pos_iff.mpr hg
  rw [P.count_gammaVector_eq hg0, P.gammaExponent_eq_zero hS] at h
  split_ifs at h <;> simp at h

/-- **The gamma vector satisfies the LMFDB's identity** (LMFDB `hgm.defining_parameters`): in the
field `ℚ(x)` of rational functions over `ℤ`,
`∏_{g ∈ γ, g > 0} (x^g - 1) / ∏_{g ∈ γ, g < 0} (x^{-g} - 1) = Φ_A / Φ_B` for the gamma vector `γ`
of defining parameters `(A, B)`, where `Φ_C = ∏_{c ∈ C} Φ_c` is
`Hypergeometric.CuspIndex.cyclotomicProd`, which is `∏_{a ∈ α} (x - e^{2πia})` over `ℂ`
(`Hypergeometric.CuspIndex.map_cyclotomicProd_eq_prod_exp`). -/
lemma Parameters.gammaRatFunc_gammaVector : gammaRatFunc P.gammaVector =
    algebraMap ℤ[X] (RatFunc ℤ) P.A.cyclotomicProd /
      algebraMap ℤ[X] (RatFunc ℤ) P.B.cyclotomicProd := by
  rw [CuspIndex.cyclotomicProd, CuspIndex.cyclotomicProd, P.algebraMap_div_eq_prod_gammaExponent,
    gammaRatFunc_eq_prod,
    prod_zpow_sign_eq_prod _ (fun _ ↦ P.pos_of_mem_gammaSupport) fun _ ↦
      P.natAbs_mem_gammaSupport]
  refine prod_congr rfl fun n hn ↦ ?_
  rw [sum_ite_natAbs_eq _ (P.pos_of_mem_gammaSupport hn),
    P.count_gammaVector_pos (P.pos_of_mem_gammaSupport hn),
    P.count_gammaVector_neg (P.pos_of_mem_gammaSupport hn), Int.toNat_sub_toNat_neg]

lemma Parameters.perm_gammaVector (hγ : ∀ g ∈ γ, -g ∉ γ) (h : gammaRatFunc γ =
    algebraMap ℤ[X] (RatFunc ℤ) P.A.cyclotomicProd /
      algebraMap ℤ[X] (RatFunc ℤ) P.B.cyclotomicProd) : γ.Perm P.gammaVector :=
  perm_of_gammaRatFunc_eq hγ (fun _ ↦ P.neg_notMem_gammaVector) <|
    h.trans P.gammaRatFunc_gammaVector.symm

/-- **The gamma vector is unique** (LMFDB `hgm.defining_parameters`): a list `γ` of integers in
ascending order that never contains both `g` and `-g` (in particular `0`) and satisfies
`∏_{g ∈ γ, g > 0} (x^g - 1) / ∏_{g ∈ γ, g < 0} (x^{-g} - 1) = Φ_A / Φ_B` is the gamma vector of
`(A, B)`. Without the second condition `γ` is not unique. -/
lemma Parameters.eq_gammaVector (hs : γ.SortedLE) (hγ : ∀ g ∈ γ, -g ∉ γ) (h : gammaRatFunc γ =
    algebraMap ℤ[X] (RatFunc ℤ) P.A.cyclotomicProd /
      algebraMap ℤ[X] (RatFunc ℤ) P.B.cyclotomicProd) : γ = P.gammaVector :=
  (P.perm_gammaVector hγ h).eq_of_sortedLE hs P.sortedLE_gammaVector

end Hypergeometric
