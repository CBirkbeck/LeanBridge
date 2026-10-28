import LeanBridge.ForMathlib.NumberTheory.NumberField.Place
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.Ostrowski

/-!
# Ostrowski's theorem for number fields

Every place of a number field `K` (LMFDB `nf.place`) comes from an infinite place, real or complex,
when it is archimedean, and from a maximal ideal of `𝓞 K` when it is nonarchimedean. With the
injectivity results of `LeanBridge.ForMathlib.NumberTheory.NumberField.Place`, the places of `K`
are thus in bijection with its infinite and finite places.

A nonarchimedean nontrivial absolute value `v` is at most `1` on `𝓞 K`, the integers where it is
less than `1` form a nonzero prime ideal `𝔭`, and every element of `K` is `n / d` or `d / n` with
`d ∉ 𝔭`, which shows that `v` is equivalent to the `𝔭`-adic absolute value. For an archimedean
absolute value `v`, `v` is unbounded on `ℕ`, so its restriction to `ℚ` is a power `|·| ^ t` of
the usual absolute value (Mathlib's Ostrowski theorem for `ℚ`). If `v` were equivalent to no
infinite place, the approximation theorem would give `a` with `1 < v a` and `|φ a| < 1` for every
complex embedding `φ`; the coefficients of the minimal polynomials of the powers `aⁿ`, bounded
through their complex roots `φ (aⁿ)`, tend to `0`, which bounds `v (aⁿ) ≥ 1` by a quantity tending
to `0`.

The completion of `K` at a place is the completion `AbsoluteValue.Completion` of `K` for any of
its absolute values; for infinite and finite places it is `NumberField.InfinitePlace.Completion`
and `IsDedekindDomain.HeightOneSpectrum.adicCompletion`.

## Main definitions

* `AbsoluteValue.integerIdeal`: the integers of `K` where a nonarchimedean absolute value is less
  than `1`.
* `AbsoluteValue.heightOneSpectrum`: that ideal, as a maximal ideal of `𝓞 K`, for a nontrivial
  absolute value.
* `AbsoluteValue.Place.IsReal`, `AbsoluteValue.Place.IsComplex` (LMFDB `nf.place`): real and
  complex places of a number field.

## Main results

* `AbsoluteValue.isNonarchimedean_of_natCast_le_one`: an absolute value bounded by `1` on `ℕ` is
  nonarchimedean.
* `AbsoluteValue.isEquiv_finitePlace`: a nonarchimedean nontrivial absolute value on a number field
  is equivalent to a finite place.
* `AbsoluteValue.exists_infinitePlace_isEquiv`: an archimedean absolute value on a number field is
  equivalent to an infinite place.
* `AbsoluteValue.Place.isArchimedean_iff_exists_infinitePlace`,
  `AbsoluteValue.Place.not_isArchimedean_iff_exists_finitePlace`: Ostrowski's theorem for number
  fields.
* `AbsoluteValue.Place.isArchimedean_iff_isReal_or_isComplex`: the archimedean (infinite) places
  are the real and the complex places.
-/

open Filter Finset IsDedekindDomain Module NumberField Polynomial Topology

namespace AbsoluteValue

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}

/-- An absolute value that is at most `1` on the natural numbers is nonarchimedean. -/
lemma isNonarchimedean_of_natCast_le_one (h : ∀ n : ℕ, v n ≤ 1) : IsNonarchimedean v := by
  intro x y
  by_contra hlt
  push Not at hlt
  have hM : 0 < max (v x) (v y) := by
    by_contra h0
    push Not at h0
    have hx : x = 0 := v.eq_zero.mp <| le_antisymm ((le_max_left _ _).trans h0) (v.nonneg x)
    have hy : y = 0 := v.eq_zero.mp <| le_antisymm ((le_max_right _ _).trans h0) (v.nonneg y)
    simp [hx, hy] at hlt
  have hr : 1 < v (x + y) / max (v x) (v y) := (one_lt_div hM).mpr hlt
  have hbd (n : ℕ) : (v (x + y) / max (v x) (v y)) ^ n ≤ n + 1 := by
    rw [div_pow, div_le_iff₀ (pow_pos hM n), ← map_pow, add_pow]
    refine (v.sum_le _ _).trans <| (sum_le_card_nsmul _ _ (max (v x) (v y) ^ n) fun k hk ↦ ?_).trans
      (by rw [card_range, nsmul_eq_mul, Nat.cast_add_one])
    rw [map_mul, map_mul, map_pow, map_pow, ← pow_mul_pow_sub _ (mem_range_succ_iff.mp hk)]
    exact (mul_le_of_le_one_right (by positivity) (h _)).trans <| mul_le_mul
      (pow_le_pow_left₀ (v.nonneg x) (le_max_left _ _) k)
      (pow_le_pow_left₀ (v.nonneg y) (le_max_right _ _) _) (by positivity) (by positivity)
  rcases ((tendsto_pow_const_div_const_pow_of_one_lt 1 hr).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).and (eventually_ge_atTop 2) |>.exists
    with ⟨n, hn, hn2⟩
  rw [pow_one, div_lt_iff₀ (pow_pos (by linarith) n)] at hn
  have hn2' : (2 : ℝ) ≤ n := mod_cast hn2
  linarith [hbd n]

lemma pow_natDegree_eq_neg_sum {R : Type*} [CommRing R] [Algebra R K] {p : R[X]} (hp : p.Monic)
    {y : K} (hy : p.aeval y = 0) :
    y ^ p.natDegree = -∑ i ∈ range p.natDegree, algebraMap R K (p.coeff i) * y ^ i := by
  rw [hp.as_sum] at hy
  simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C] at hy
  exact eq_neg_of_add_eq_zero_left hy

lemma le_one_of_isIntegral (hv : IsNonarchimedean v) {y : K} (hy : IsIntegral ℤ y) : v y ≤ 1 := by
  rcases hy with ⟨p, hp, hpy⟩
  by_contra h1
  push Not at h1
  have he : y ^ p.natDegree = -∑ i ∈ range p.natDegree, algebraMap ℤ K (p.coeff i) * y ^ i :=
    pow_natDegree_eq_neg_sum hp hpy
  rcases (range p.natDegree).eq_empty_or_nonempty with h0 | hne
  · rw [h0, sum_empty, neg_zero] at he
    exact pow_ne_zero _ (v.ne_zero_iff.mp (zero_lt_one.trans h1).ne') he
  have hle : v (∑ i ∈ range p.natDegree, algebraMap ℤ K (p.coeff i) * y ^ i) ≤
      (range p.natDegree).sup' hne fun i ↦ v (algebraMap ℤ K (p.coeff i) * y ^ i) :=
    hv.apply_sum_le_sup hne
  rw [← map_neg_eq_map, ← he, map_pow, le_sup'_iff] at hle
  rcases hle with ⟨i, hi, hle⟩
  rw [map_mul, map_pow, eq_intCast] at hle
  have hc : v (p.coeff i) ≤ 1 :=
    hv.apply_intCast_le_one (by simp) v.map_one fun a ↦ v.map_neg a
  exact (hle.trans (mul_le_of_le_one_left (by positivity) hc)).not_gt <|
    pow_lt_pow_right₀ h1 (mem_range.mp hi)

variable (hv : IsNonarchimedean v)

/-- The ideal of the integers `x ∈ 𝓞 K` with `v x < 1`, for a nonarchimedean absolute value `v`
on `K`. -/
def integerIdeal : Ideal (𝓞 K) where
  carrier := {x | v x < 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
    exact (hv _ _).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at hx ⊢
    exact (mul_le_of_le_one_left (v.nonneg _) (le_one_of_isIntegral hv c.isIntegral_coe)).trans_lt
      hx

lemma mem_integerIdeal {x : 𝓞 K} : x ∈ integerIdeal hv ↔ v x < 1 :=
  Iff.rfl

variable [NumberField K]

/-- The maximal ideal of `𝓞 K` of a nontrivial nonarchimedean absolute value `v` on a number field
`K`: the integers `x` with `v x < 1`. Its finite place is equivalent to `v`
(`isEquiv_finitePlace`). -/
def heightOneSpectrum (hn : v.IsNontrivial) : HeightOneSpectrum (𝓞 K) where
  asIdeal := integerIdeal hv
  isPrime := by
    refine ⟨(Ideal.ne_top_iff_one _).mpr fun h ↦ ?_, fun {x y} h ↦ ?_⟩
    · simp [mem_integerIdeal] at h
    by_contra hxy
    simp only [mem_integerIdeal, map_mul, not_or, not_lt] at h hxy
    exact h.not_ge (one_le_mul_of_one_le_of_one_le hxy.1 hxy.2)
  ne_bot := by
    rcases hn.exists_abv_lt_one with ⟨x, hx0, hx1⟩
    rcases IsFractionRing.div_surjective (A := 𝓞 K) x with ⟨a, b, hb, rfl⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hx0
    rw [Submodule.ne_bot_iff]
    by_cases ha : v a < 1
    · exact ⟨a, ha, ha0⟩
    refine ⟨b, ?_, nonZeroDivisors.ne_zero hb⟩
    by_contra hb1
    rw [map_div₀, le_antisymm (le_one_of_isIntegral hv a.isIntegral_coe) (not_lt.mp ha),
      le_antisymm (le_one_of_isIntegral hv b.isIntegral_coe) (not_lt.mp hb1), div_one] at hx1
    exact hx1.false

/-- A nontrivial nonarchimedean absolute value on a number field is equivalent to the finite place
of its maximal ideal. -/
lemma isEquiv_finitePlace (hn : v.IsNontrivial) :
    (FinitePlace.mk (heightOneSpectrum hv hn)).1.IsEquiv v := by
  refine isEquiv_of_lt_one_imp (FinitePlace.isNontrivial _) fun x hx ↦ ?_
  rw [← FinitePlace.coe_apply, FinitePlace.mk_apply] at hx
  rcases (heightOneSpectrum hv hn).exists_primeCompl_mul_eq_or_mul_eq x with ⟨n, d, h | h⟩
  · have hd : ‖FinitePlace.embedding (heightOneSpectrum hv hn) (algebraMap (𝓞 K) K d.1)‖ = 1 :=
      (FinitePlace.norm_eq_one_iff_notMem K _ d.1).mpr (Ideal.mem_primeCompl_iff.mp d.2)
    have hw : FinitePlace.mk (heightOneSpectrum hv hn) (x * algebraMap (𝓞 K) K d.1) =
        FinitePlace.mk (heightOneSpectrum hv hn) (algebraMap (𝓞 K) K n) :=
      congrArg _ h
    simp only [map_mul, FinitePlace.mk_apply, hd, mul_one] at hw
    have hvn : v (algebraMap (𝓞 K) K n) < 1 :=
      (FinitePlace.norm_lt_one_iff_mem K (heightOneSpectrum hv hn) n).mp (hw ▸ hx)
    have hvd : v (algebraMap (𝓞 K) K d.1) = 1 := le_antisymm
      (le_one_of_isIntegral hv d.1.isIntegral_coe) (not_lt.mp (Ideal.mem_primeCompl_iff.mp d.2))
    have hvx : v (x * algebraMap (𝓞 K) K d.1) = v (algebraMap (𝓞 K) K n) :=
      congrArg v h
    rw [map_mul, hvd, mul_one] at hvx
    exact hvx ▸ hvn
  · have hw : FinitePlace.mk (heightOneSpectrum hv hn) (x * algebraMap (𝓞 K) K n) =
        FinitePlace.mk (heightOneSpectrum hv hn) (algebraMap (𝓞 K) K d.1) :=
      congrArg _ h
    simp only [map_mul, FinitePlace.mk_apply,
      (FinitePlace.norm_eq_one_iff_notMem K _ d.1).mpr (Ideal.mem_primeCompl_iff.mp d.2)] at hw
    exact absurd hw ((mul_le_of_le_one_right (norm_nonneg _)
      (FinitePlace.norm_le_one K _ n)).trans_lt hx).ne

lemma one_le_finrank_mul_rpow {t : ℝ} (ht : 0 < t)
    (hvt : ∀ q : ℚ, v (algebraMap ℚ K q) = |(q : ℝ)| ^ t) {a : K} (ha : 1 < v a) {B : ℝ}
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (hB : ∀ φ : K →+* ℂ, ‖φ a‖ ≤ B) (n : ℕ) :
    1 ≤ finrank ℚ K * (2 ^ finrank ℚ K * B ^ n) ^ t := by
  have hi : IsIntegral ℚ (a ^ n) := Algebra.IsIntegral.isIntegral _
  have he : (a ^ n) ^ (minpoly ℚ (a ^ n)).natDegree = -∑ i ∈ range (minpoly ℚ (a ^ n)).natDegree,
      algebraMap ℚ K ((minpoly ℚ (a ^ n)).coeff i) * (a ^ n) ^ i :=
    pow_natDegree_eq_neg_sum (minpoly.monic hi) (minpoly.aeval ℚ (a ^ n))
  have hm : 0 < (minpoly ℚ (a ^ n)).natDegree := minpoly.natDegree_pos hi
  have hmd : (minpoly ℚ (a ^ n)).natDegree ≤ finrank ℚ K := minpoly.natDegree_le _
  have hy1 : 1 ≤ v (a ^ n) := by
    rw [map_pow]
    exact one_le_pow₀ ha.le
  have hroots (z : ℂ) (hz : z ∈ ((minpoly ℚ (a ^ n)).map (algebraMap ℚ ℂ)).roots) :
      ‖z‖ ≤ B ^ n := by
    have hz' : z ∈ (minpoly ℚ (a ^ n)).rootSet ℂ := by
      simpa [rootSet_def, aroots_def] using hz
    rw [← Embeddings.range_eval_eq_rootSet_minpoly] at hz'
    rcases hz' with ⟨φ, rfl⟩
    simp only [map_pow, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB φ) n
  have hc (i : ℕ) (hin : i < (minpoly ℚ (a ^ n)).natDegree) :
      v (algebraMap ℚ K ((minpoly ℚ (a ^ n)).coeff i)) ≤ (2 ^ finrank ℚ K * B ^ n) ^ t := by
    have hcb : ‖((minpoly ℚ (a ^ n)).map (algebraMap ℚ ℂ)).coeff i‖ ≤
        (B ^ n) ^ ((minpoly ℚ (a ^ n)).natDegree - i) * (minpoly ℚ (a ^ n)).natDegree.choose i :=
      coeff_le_of_roots_le i (minpoly.monic hi) (IsAlgClosed.splits _) hroots
    rw [coeff_map, eq_ratCast, Complex.norm_ratCast, mul_comm] at hcb
    rw [hvt]
    refine Real.rpow_le_rpow (abs_nonneg _) (hcb.trans <| mul_le_mul ?_
      (pow_le_of_le_one (pow_nonneg hB0 n) (pow_le_one₀ hB0 hB1) (by omega)) (by positivity)
      (by positivity)) ht.le
    exact_mod_cast (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right two_pos hmd)
  have hle : v (a ^ n) ^ (minpoly ℚ (a ^ n)).natDegree ≤ (minpoly ℚ (a ^ n)).natDegree *
      (2 ^ finrank ℚ K * B ^ n) ^ t * v (a ^ n) ^ ((minpoly ℚ (a ^ n)).natDegree - 1) := by
    rw [← map_pow, he, map_neg_eq_map]
    refine (v.sum_le _ _).trans <| (sum_le_card_nsmul _ _ _ fun i hi ↦ ?_).trans
      (by rw [card_range, nsmul_eq_mul, mul_assoc])
    rw [map_mul, map_pow]
    exact mul_le_mul (hc i (mem_range.mp hi)) (pow_le_pow_right₀ hy1
      (Nat.le_sub_one_of_lt (mem_range.mp hi))) (by positivity) (by positivity)
  rw [← Nat.sub_one_add_one hm.ne', pow_succ, Nat.add_sub_cancel, mul_comm] at hle
  have hle' : v (a ^ n) ≤ ((minpoly ℚ (a ^ n)).natDegree - 1 + 1 : ℕ) *
      (2 ^ finrank ℚ K * B ^ n) ^ t :=
    le_of_mul_le_mul_right hle (by positivity)
  rw [Nat.sub_one_add_one hm.ne'] at hle'
  exact hy1.trans <| hle'.trans <| mul_le_mul_of_nonneg_right (by exact_mod_cast hmd)
    (by positivity)

/-- An archimedean absolute value on a number field is equivalent to an infinite place. -/
lemma exists_infinitePlace_isEquiv (hv : ¬IsNonarchimedean v) :
    ∃ w : InfinitePlace K, w.1.IsEquiv v := by
  by_contra hne
  push Not at hne
  have hbdd : ¬∀ n : ℕ, v.comp (algebraMap ℚ K).injective n ≤ 1 :=
    fun h ↦ hv <| isNonarchimedean_of_natCast_le_one fun n ↦ by simpa using h n
  rcases isEquiv_iff_exists_rpow_eq.mp (Rat.AbsoluteValue.equiv_real_of_unbounded hbdd).symm with
    ⟨t, ht, hrt⟩
  have hvt (q : ℚ) : v (algebraMap ℚ K q) = |(q : ℝ)| ^ t := by
    simpa using (congrFun hrt q).symm
  have hn : v.IsNontrivial := by
    push Not at hbdd
    rcases hbdd with ⟨n, hn⟩
    simp only [comp_apply, map_natCast] at hn
    refine ⟨n, fun h ↦ ?_, hn.ne'⟩
    rw [h, map_zero] at hn
    exact zero_lt_one.not_gt hn
  rcases exists_one_lt_lt_one_pi_of_not_isEquiv
    (v := fun o : Option (InfinitePlace K) ↦ o.elim v fun w ↦ w.1)
    (by rintro (_ | w); exacts [hn, w.isNontrivial]) (by
      rintro (_ | w) (_ | w') hww' h
      · exact hww' rfl
      · exact hne w' h.symm
      · exact hne w h
      · exact hww' <| congrArg some <| InfinitePlace.eq_iff_isEquiv.mpr h) none with ⟨a, ha, haw⟩
  have hB (φ : K →+* ℂ) : ‖φ a‖ ≤ (univ.sup fun φ : K →+* ℂ ↦ ‖φ a‖₊ : NNReal) :=
    NNReal.coe_le_coe.mpr <| le_sup (f := fun φ : K →+* ℂ ↦ ‖φ a‖₊) (mem_univ φ)
  have hB1 : (univ.sup fun φ : K →+* ℂ ↦ ‖φ a‖₊) < 1 :=
    (Finset.sup_lt_iff zero_lt_one).mpr fun φ _ ↦ NNReal.coe_lt_coe.mp <|
      haw (some (InfinitePlace.mk φ)) (Option.some_ne_none _)
  have hlim : Tendsto (fun n : ℕ ↦ finrank ℚ K * (2 ^ finrank ℚ K *
      ((univ.sup fun φ : K →+* ℂ ↦ ‖φ a‖₊ : NNReal) : ℝ) ^ n) ^ t) atTop (𝓝 0) := by
    simpa [Real.zero_rpow ht.ne'] using (((tendsto_pow_atTop_nhds_zero_of_lt_one
      (NNReal.coe_nonneg _) (NNReal.coe_lt_one.mpr hB1)).const_mul _).rpow_const
        (.inr ht.le)).const_mul _
  rcases (hlim.eventually (gt_mem_nhds one_pos)).exists with ⟨n, hn⟩
  exact hn.not_ge <|
    one_le_finrank_mul_rpow ht hvt ha (NNReal.coe_nonneg _) (NNReal.coe_le_one.mpr hB1.le) hB n

namespace Place

variable (p : Place K)

/-- **Ostrowski's theorem** for number fields, archimedean case: the archimedean places of a
number field are those given by its infinite places. -/
lemma isArchimedean_iff_exists_infinitePlace :
    p.IsArchimedean ↔ ∃ w : InfinitePlace K, w.toPlace = p := by
  refine ⟨fun hp ↦ ?_, fun ⟨w, hw⟩ ↦ hw ▸ w.isArchimedean_toPlace⟩
  rcases p.exists_mk with ⟨u, hu, rfl⟩
  rcases exists_infinitePlace_isEquiv hp with ⟨w, hw⟩
  exact ⟨w, mk_eq_mk_iff.mpr hw⟩

/-- **Ostrowski's theorem** for number fields, nonarchimedean case: the nonarchimedean places of a
number field are those given by its finite places, that is by the maximal ideals of `𝓞 K`. -/
lemma not_isArchimedean_iff_exists_finitePlace :
    ¬p.IsArchimedean ↔ ∃ w : FinitePlace K, w.toPlace = p := by
  refine ⟨fun hp ↦ ?_, fun ⟨w, hw⟩ ↦ hw ▸ w.not_isArchimedean_toPlace⟩
  rcases p.exists_mk with ⟨u, hu, rfl⟩
  exact ⟨_, mk_eq_mk_iff.mpr <| isEquiv_finitePlace (not_not.mp hp) hu⟩

/-- A place of a number field is **real** (LMFDB `nf.place`) when it is given by a real infinite
place, that is by a real embedding. -/
def IsReal : Prop :=
  ∃ w : InfinitePlace K, w.IsReal ∧ w.toPlace = p

/-- A place of a number field is **complex** (LMFDB `nf.place`) when it is given by a complex
infinite place, that is by a conjugate pair of non-real complex embeddings. -/
def IsComplex : Prop :=
  ∃ w : InfinitePlace K, w.IsComplex ∧ w.toPlace = p

/-- The archimedean places of a number field, also called its **infinite places**, are its real
and its complex places. -/
lemma isArchimedean_iff_isReal_or_isComplex : p.IsArchimedean ↔ p.IsReal ∨ p.IsComplex := by
  rw [isArchimedean_iff_exists_infinitePlace]
  refine ⟨fun ⟨w, hw⟩ ↦ w.isReal_or_isComplex.imp (⟨w, ·, hw⟩) (⟨w, ·, hw⟩), ?_⟩
  rintro (⟨w, -, hw⟩ | ⟨w, -, hw⟩) <;> exact ⟨w, hw⟩

end Place

end AbsoluteValue
