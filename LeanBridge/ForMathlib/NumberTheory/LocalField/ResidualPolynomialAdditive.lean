import LeanBridge.ForMathlib.NumberTheory.LocalField.ResidualPolynomialInvariance

/-!
# The additive polynomials of the residual polynomials of segments of positive slope

Let `L / K` be a totally ramified extension of nonarchimedean local fields with residue
characteristic `p`, `α` a uniformiser of `L` with minimal polynomial `φ` over `K`, and `ρ` the
ramification polynomial `α ^ (-n) φ(α x + α)`, whose coefficients lie in `𝒪_L`. For a segment `S`
of the ramification polygon with right end `(-k, v_L(ρ_k))` and slope `h / m > 0`, the knowl LMFDB
`lf.residual_polynomials` says that `x ^ k A(x ^ m)` is an additive polynomial, for the residual
polynomial `A` of `S`. This file proves it: the coefficient of `x ^ (k + j m)` is the residue of
`ρ_{k + j m} α ^ (j h - v_L(ρ_k))`, which is nonzero only when the point
`(-(k + j m), v_L(ρ_{k + j m}))` lies on `S`, and such an abscissa is a power of `p`. Indeed, by
Monge's binomial argument (the first statement of his Proposition 2), for `i ≥ 1` and the largest
power `s = p ^ v_p(i)` of `p` dividing `i`, every power of `α` dividing the coefficient of `x ^ s`
of `φ(α x + α)` divides that of `x ^ i`, so `v_L(ρ_s) ≤ v_L(ρ_i)`; if `s < i`, the point at `-i`
lies strictly above every line of positive slope through the point at `-s`, so not on `S`. So the
coefficients of `x ^ k A(x ^ m)` vanish away from the powers of `p`, and the polynomial is additive
on the residue field, of characteristic `p`.

## Main results

* `IsNonarchimedeanLocalField.pow_dvd_coeff_mongeShift_zero` (Monge's binomial argument): the
  coefficient of `x ^ i` of `g(π + π x)` is divisible by every power of `π` dividing the
  coefficient of `x ^ s`, `s = p ^ v_p(i)`.
* `IsNonarchimedeanLocalField.mem_integer_coeff_ramificationPolynomial` (LMFDB
  `lf.residual_polynomials`): the ramification polynomial has its coefficients in `𝒪_L`.
* `IsNonarchimedeanLocalField.coeffVal_pow_padicValNat_le`: `v_L(ρ_s) ≤ v_L(ρ_i)` for the
  ramification polynomial.
* `IsNonarchimedeanLocalField.coeff_X_pow_mul_comp_residualPolynomial_eq_zero` and
  `IsNonarchimedeanLocalField.aeval_add_X_pow_mul_comp_residualPolynomial` (LMFDB
  `lf.residual_polynomials`): for a segment of positive slope, the coefficients of `x ^ k A(x ^ m)`
  vanish away from the powers of `p`, and it is an additive polynomial: additive on every
  commutative algebra over the residue field.

## References

* J. Monge, *Determination of the number of isomorphism classes of extensions of a p-adic field*,
  J. Number Theory 131 (2011); arXiv:1109.4617, Proposition 2.
-/

open Finset IntermediateField IsDiscreteValuationRing Polynomial TauCeti ValuativeRel

namespace IsNonarchimedeanLocalField

open HerbrandInvariant

section Monge

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S]
  [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S] {g : R[X]} {π : S} {p r k : ℕ}

/-- **Monge's binomial argument**: for a root `π` of `g` with the hypotheses of Monge's reduction
and `r ≥ 1`, every power `π ^ k` dividing the coefficient of `x ^ s` of `g(π + π x)`, for the
largest power `s = p ^ v_p(r)` of `p` dividing `r`, divides the coefficient of `x ^ r`. -/
lemma pow_dvd_coeff_mongeShift_zero (h : IsMongeRoot g π p) [Fact p.Prime] (hr : r ≠ 0)
    (hk : π ^ k ∣ (mongeShift g π 0).coeff (p ^ padicValNat p r)) :
    π ^ k ∣ (mongeShift g π 0).coeff r := by
  have hp : p.Prime :=
    Fact.out
  rcases pow_padicValNat_dvd (p := p) (n := r) with ⟨u, hu⟩
  have hcop : p.Coprime u := by
    refine hp.coprime_iff_not_dvd.mpr fun hd ↦ pow_succ_padicValNat_not_dvd (p := p) hr ?_
    rw [pow_succ]
    conv_rhs => rw [hu]
    exact mul_dvd_mul_left _ hd
  have hq : p ^ padicValNat p r ≠ 0 :=
    pow_ne_zero _ hp.ne_zero
  rw [coeff_mongeShift h hq, zero_mul, pow_zero, one_mul] at hk
  rw [coeff_mongeShift h hr, zero_mul, pow_zero, one_mul]
  have hterm {i : ℕ} (hi : i ∈ Icc 1 g.natDegree) :
      π ^ k ∣ algebraMap R S ((i.choose (p ^ padicValNat p r) : R) * g.coeff i) * π ^ i :=
    pow_dvd_of_pow_dvd_sum h.irreducible
      (fun i ↦ algebraMap R S ((i.choose (p ^ padicValNat p r) : R) * g.coeff i) * π ^ i)
      (fun _ hi _ hj hij heq ↦ addVal_term_ne h
        (a := fun i ↦ (i.choose (p ^ padicValNat p r) : R) * g.coeff i)
        (not_modEq_of_mem_Icc hi hj hij) heq) hk hi
  refine dvd_sum fun i hi ↦ ?_
  have hw : IsUnit ((r.choose (p ^ padicValNat p r) : ℕ) : S) := by
    have h₁ : p.Coprime ((p ^ padicValNat p r * u).choose (p ^ padicValNat p r)) :=
      coprime_choose_pow_mul _ hcop
    rw [← hu] at h₁
    exact h.isUnit_natCast h₁
  have hchoose : ((i.choose r : ℕ) : S) * (r.choose (p ^ padicValNat p r) : ℕ) =
      (i.choose (p ^ padicValNat p r) : ℕ) *
        ((i - p ^ padicValNat p r).choose (r - p ^ padicValNat p r) : ℕ) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_mul (Nat.le_of_dvd (Nat.pos_of_ne_zero hr)
      pow_padicValNat_dvd)]
  refine (hw.dvd_mul_left).mp ?_
  have heq : ((r.choose (p ^ padicValNat p r) : ℕ) : S) *
      (algebraMap R S ((i.choose r : R) * g.coeff i) * π ^ i) =
      ((i - p ^ padicValNat p r).choose (r - p ^ padicValNat p r) : ℕ) *
        (algebraMap R S ((i.choose (p ^ padicValNat p r) : R) * g.coeff i) * π ^ i) := by
    simp only [map_mul, map_natCast]
    linear_combination (algebraMap R S (g.coeff i) * π ^ i) * hchoose
  rw [heq]
  exact (hterm hi).mul_left _

end Monge

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] {α : 𝒪[L]} {kl : ℕ × ℕ}
  {i : ℕ}

lemma isMongeRoot_minpoly (hKL : IsTotallyRamified K L) (hα : Irreducible α) :
    IsMongeRoot (minpoly 𝒪[K] α) α (ringChar 𝓀[K]) := by
  have hfin : FiniteDimensional K L :=
    finite_of_valuativeExtension K L
  have hp : Fact (ringChar 𝓀[K]).Prime :=
    ⟨CharP.prime_ringChar _⟩
  have hc : CharP 𝓀[L] (ringChar 𝓀[K]) :=
    charP_of_injective_algebraMap (algebraMap 𝓀[K] 𝓀[L]).injective _
  have hint : IsIntegral 𝒪[K] α :=
    IsIntegral.of_finite 𝒪[K] α
  have hgen : K⟮(α : L)⟯ = ⊤ := by
    have h₁ : K⟮algebraMap 𝒪[L] L α⟯ = ⊤ :=
      IntermediateField.adjoin_eq_top_of_algebra_adjoin_eq_top (hKL.adjoin_eq_top_of_irreducible hα)
    rwa [Algebra.algebraMap_ofSubsemiring_apply] at h₁
  refine isMongeRoot_of_isEisensteinAt (minpoly.monic hint) (hKL.isEisensteinAt_minpoly hα) ?_ hgen
  rw [IsRoot, eval_map, ← aeval_def, minpoly.aeval]

/-- **The ramification polynomial has integral coefficients** (LMFDB `lf.residual_polynomials`,
`ρ ∈ 𝒪_L[x]`): for a totally ramified extension `L / K` of nonarchimedean local fields and a
uniformiser `α` of `L`, the coefficients of `ρ(x) = α ^ (-n) φ(α x + α)` lie in `𝒪_L`, as the
coefficients of `φ(α x + α)` are divisible by `α ^ n`. -/
lemma mem_integer_coeff_ramificationPolynomial (hKL : IsTotallyRamified K L) (hα : Irreducible α)
    (j : ℕ) : (ramificationPolynomial (minpoly K (α : L)) (α : L)).coeff j ∈ 𝒪[L] := by
  have h : IsMongeRoot (minpoly 𝒪[K] α) α (ringChar 𝓀[K]) :=
    isMongeRoot_minpoly hKL hα
  have hα₀ : (α : L) ≠ 0 :=
    fun h ↦ hα.ne_zero (Subtype.ext h)
  rcases eq_or_ne j 0 with rfl | hj
  · rw [coeff_zero_ramificationPolynomial (minpoly.aeval K (α : L))]
    exact zero_mem _
  have hdvd : α ^ (minpoly 𝒪[K] α).natDegree ∣ (mongeShift (minpoly 𝒪[K] α) α 0).coeff j := by
    rw [coeff_mongeShift h hj, zero_mul, pow_zero, one_mul]
    refine dvd_sum fun i hi ↦ ?_
    rcases (mem_Icc.mp hi).2.lt_or_eq with hlt | rfl
    · have hmem : (minpoly 𝒪[K] α).coeff i ∈ 𝓂[K] :=
        (hKL.isEisensteinAt_minpoly hα).mem hlt
      have h₂ : 1 ≤ addVal 𝒪[K] ((minpoly 𝒪[K] α).coeff i) :=
        Order.one_le_iff_ne_zero.mpr fun h₀ ↦
          mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem) (addVal_eq_zero_iff.mp h₀)
      have h₁ :
          α ^ (minpoly 𝒪[K] α).natDegree ∣ algebraMap 𝒪[K] 𝒪[L] ((minpoly 𝒪[K] α).coeff i) := by
        rw [pow_dvd_iff_le_addVal h.irreducible, h.addVal_algebraMap]
        have h₃ : (minpoly 𝒪[K] α).natDegree • (1 : ℕ∞) ≤
            (minpoly 𝒪[K] α).natDegree • addVal 𝒪[K] ((minpoly 𝒪[K] α).coeff i) :=
          nsmul_le_nsmul_right h₂ (minpoly 𝒪[K] α).natDegree
        rwa [nsmul_one] at h₃
      rw [map_mul, mul_assoc]
      exact (h₁.mul_right _).mul_left _
    · exact dvd_mul_left _ _
  rcases hdvd with ⟨w, hw⟩
  have h₁ : (((mongeShift (minpoly 𝒪[K] α) α 0).coeff j : 𝒪[L]) : L) =
      (α : L) ^ (minpoly 𝒪[K] α).natDegree *
        (ramificationPolynomial (minpoly K (α : L)) (α : L)).coeff j :=
    coe_coeff_mongeShift_minpoly hα j
  rw [hw, Subring.coe_mul, Subring.coe_pow] at h₁
  have h₂ : (ramificationPolynomial (minpoly K (α : L)) (α : L)).coeff j = (w : L) :=
    mul_left_cancel₀ (pow_ne_zero _ hα₀) h₁.symm
  rw [h₂]
  exact w.2

lemma coeff_pow_padicValNat_ne_zero (hKL : IsTotallyRamified K L) (hα : Irreducible α) (hi : i ≠ 0)
    (hρ : (ramificationPolynomial (minpoly K (α : L)) (α : L)).coeff i ≠ 0) :
    (ramificationPolynomial (minpoly K (α : L)) (α : L)).coeff
      (ringChar 𝓀[K] ^ padicValNat (ringChar 𝓀[K]) i) ≠ 0 := by
  have hp : Fact (ringChar 𝓀[K]).Prime :=
    ⟨CharP.prime_ringChar _⟩
  have h : IsMongeRoot (minpoly 𝒪[K] α) α (ringChar 𝓀[K]) :=
    isMongeRoot_minpoly hKL hα
  refine mt (coeff_mongeShift_eq_zero_iff hα).mpr fun hs ↦
    mt (coeff_mongeShift_eq_zero_iff hα).mp hρ ?_
  refine addVal_eq_top_iff.mp (ENat.eq_top_iff_forall_ge.mpr fun k ↦ ?_)
  exact (pow_dvd_iff_le_addVal h.irreducible).mp
    (pow_dvd_coeff_mongeShift_zero h hi (hs ▸ dvd_zero _))

/-- **The valuations of the coefficients at the powers of `p`** (Monge's Proposition 2): for a
totally ramified extension `L / K` of nonarchimedean local fields of residue characteristic `p`, a
uniformiser `α` with ramification polynomial `ρ` and `i ≥ 1` with `ρ_i ≠ 0`, the coefficient `ρ_s`
at the largest power `s = p ^ v_p(i)` of `p` dividing `i`, which is nonzero, has valuation at most
`v_L(ρ_i)`. -/
lemma coeffVal_pow_padicValNat_le (hKL : IsTotallyRamified K L) (hα : Irreducible α) (hi : i ≠ 0)
    (hρ : (ramificationPolynomial (minpoly K (α : L)) (α : L)).coeff i ≠ 0) :
    coeffVal (ramificationPolynomial (minpoly K (α : L)) (α : L))
        (ringChar 𝓀[K] ^ padicValNat (ringChar 𝓀[K]) i) ≤
      coeffVal (ramificationPolynomial (minpoly K (α : L)) (α : L)) i := by
  have hp : Fact (ringChar 𝓀[K]).Prime :=
    ⟨CharP.prime_ringChar _⟩
  have h : IsMongeRoot (minpoly 𝒪[K] α) α (ringChar 𝓀[K]) :=
    isMongeRoot_minpoly hKL hα
  have hρs : (ramificationPolynomial (minpoly K (α : L)) (α : L)).coeff
      (ringChar 𝓀[K] ^ padicValNat (ringChar 𝓀[K]) i) ≠ 0 :=
    coeff_pow_padicValNat_ne_zero hKL hα hi hρ
  have hTi : (mongeShift (minpoly 𝒪[K] α) α 0).coeff i ≠ 0 :=
    mt (coeff_mongeShift_eq_zero_iff hα).mp hρ
  have hTs :
      (mongeShift (minpoly 𝒪[K] α) α 0).coeff (ringChar 𝓀[K] ^ padicValNat (ringChar 𝓀[K]) i) ≠ 0 :=
    mt (coeff_mongeShift_eq_zero_iff hα).mp hρs
  have hdvd : α ^ (addVal 𝒪[L] ((mongeShift (minpoly 𝒪[K] α) α 0).coeff
      (ringChar 𝓀[K] ^ padicValNat (ringChar 𝓀[K]) i))).toNat ∣
        (mongeShift (minpoly 𝒪[K] α) α 0).coeff i :=
    pow_dvd_coeff_mongeShift_zero h hi ((pow_dvd_iff_le_addVal h.irreducible).mpr
      (ENat.natCast_toNat_le_self _))
  rw [pow_dvd_iff_le_addVal h.irreducible, ENat.natCast_toNat (mt addVal_eq_top_iff.mp hTs)] at hdvd
  have hle : (addVal 𝒪[L] ((mongeShift (minpoly 𝒪[K] α) α 0).coeff
      (ringChar 𝓀[K] ^ padicValNat (ringChar 𝓀[K]) i))).toNat ≤
        (addVal 𝒪[L] ((mongeShift (minpoly 𝒪[K] α) α 0).coeff i)).toNat :=
    ENat.toNat_le_toNat hdvd (mt addVal_eq_top_iff.mp hTi)
  have h₁ : ((addVal 𝒪[L] ((mongeShift (minpoly 𝒪[K] α) α 0).coeff
      (ringChar 𝓀[K] ^ padicValNat (ringChar 𝓀[K]) i))).toNat : ℤ) =
        (minpoly 𝒪[K] α).natDegree + coeffVal (ramificationPolynomial (minpoly K (α : L)) (α : L))
          (ringChar 𝓀[K] ^ padicValNat (ringChar 𝓀[K]) i) :=
    toNat_addVal_coeff_mongeShift hα hρs
  have h₂ : ((addVal 𝒪[L] ((mongeShift (minpoly 𝒪[K] α) α 0).coeff i)).toNat : ℤ) =
      (minpoly 𝒪[K] α).natDegree +
        coeffVal (ramificationPolynomial (minpoly K (α : L)) (α : L)) i :=
    toNat_addVal_coeff_mongeShift hα hρ
  omega

/-- **The coefficients of `x ^ k A(x ^ m)` vanish away from the powers of `p`** (LMFDB
`lf.residual_polynomials`): for a totally ramified extension `L / K` of nonarchimedean local fields
of residue characteristic `p`, a uniformiser `α` with ramification polynomial `ρ` and a segment of
the ramification polygon with right end `(-k, v_L(ρ_k))` and slope `h / m > 0`, the coefficient of
`x ^ r` in `x ^ k A(x ^ m)` is `0` unless `r` is a power of `p`, for the residual polynomial `A` of
the segment. -/
lemma coeff_X_pow_mul_comp_residualPolynomial_eq_zero (hKL : IsTotallyRamified K L)
    (hα : Irreducible α)
    (hkl : kl ∈ residualSegments (ramificationPolynomial (minpoly K (α : L)) (α : L)))
    (hpos : 0 < residualSlope (ramificationPolynomial (minpoly K (α : L)) (α : L)) kl.1 kl.2)
    {r : ℕ} (hr : ∀ e, r ≠ ringChar 𝓀[K] ^ e) :
    (X ^ kl.1 * (residualPolynomial (ramificationPolynomial (minpoly K (α : L)) (α : L)) (α : L)
      kl.1 kl.2).comp (X ^ (residualSlope (ramificationPolynomial (minpoly K (α : L)) (α : L))
        kl.1 kl.2).den)).coeff r = 0 := by
  set ρ : L[X] := ramificationPolynomial (minpoly K (α : L)) (α : L)
  set sl : ℚ := residualSlope ρ kl.1 kl.2
  rw [coeff_X_pow_mul', ← expand_eq_comp_X_pow, coeff_expand sl.den_pos]
  split_ifs with h₁ h₂
  · rw [coeff_residualPolynomial]
    split_ifs with h₃
    · by_contra hne
      have hmem : ρ.coeff ((r - kl.1) / sl.den * sl.den + kl.1) *
          (α : L) ^ ((((r - kl.1) / sl.den : ℕ) : ℤ) * sl.num - coeffVal ρ kl.1) ∈ 𝒪[L] :=
        mem_integer_residualPolynomial hα hkl ((r - kl.1) / sl.den)
      have hdiv : (r - kl.1) / sl.den * sl.den + kl.1 = r := by
        rw [Nat.div_mul_cancel h₂]
        omega
      rw [hdiv] at hmem hne
      have hρr : ρ.coeff r ≠ 0 := by
        rintro h
        rw [h, zero_mul] at hne
        exact hne (by simpa using residueOf_coe (0 : 𝒪[L]))
      have hx₀ :
          ρ.coeff r * (α : L) ^ ((((r - kl.1) / sl.den : ℕ) : ℤ) * sl.num - coeffVal ρ kl.1) ≠ 0 :=
        mul_ne_zero hρr (zpow_ne_zero _ fun h ↦ hα.ne_zero (Subtype.ext h))
      have hv : addValuation L (ρ.coeff r * (α : L) ^ ((((r - kl.1) / sl.den : ℕ) : ℤ) * sl.num -
          coeffVal ρ kl.1)) = 0 := by
        refine le_antisymm (not_lt.mp fun hlt ↦ hne ?_)
          ((mem_integer_iff_zero_le_addValuation hx₀).mp hmem)
        rw [residueOf, dite_eq_left hmem]
        exact residue_eq_zero_of_pos hlt
      rw [addValuation_mul_zpow hα hρr, addValuation_coeff hρr, ← WithTop.coe_add,
        WithTop.coe_eq_zero] at hv
      have hr₀ : r ≠ 0 := by
        rintro rfl
        have h₄ : kl.1 = 0 := by
          omega
        have h₅ : ρ.coeff kl.1 ≠ 0 :=
          coeff_fst_ne_zero_of_mem_residualSegments hkl
        rw [h₄, coeff_zero_ramificationPolynomial (minpoly.aeval K (α : L))] at h₅
        exact h₅ rfl
      have hs₀ : ρ.coeff (ringChar 𝓀[K] ^ padicValNat (ringChar 𝓀[K]) r) ≠ 0 :=
        coeff_pow_padicValNat_ne_zero hKL hα hr₀ hρr
      have hs : coeffVal ρ (ringChar 𝓀[K] ^ padicValNat (ringChar 𝓀[K]) r) ≤ coeffVal ρ r :=
        coeffVal_pow_padicValNat_le hKL hα hr₀ hρr
      have hsr : ringChar 𝓀[K] ^ padicValNat (ringChar 𝓀[K]) r < r :=
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hr₀) pow_padicValNat_dvd).lt_of_ne fun h ↦ hr _ h.symm
      have hline : (coeffVal ρ kl.1 : ℚ) -
          sl * (((ringChar 𝓀[K] ^ padicValNat (ringChar 𝓀[K]) r : ℕ) : ℚ) - kl.1) ≤
            coeffVal ρ (ringChar 𝓀[K] ^ padicValNat (ringChar 𝓀[K]) r) :=
        coeffVal_sub_mul_le hkl hs₀
      have hj : sl * (((r - kl.1) / sl.den : ℕ) : ℚ) * sl.den = sl * ((r : ℚ) - kl.1) := by
        rw [mul_assoc, ← Nat.cast_mul, Nat.div_mul_cancel h₂, Nat.cast_sub h₁]
      have hnum : sl * (((r - kl.1) / sl.den : ℕ) : ℚ) * sl.den =
          (((r - kl.1) / sl.den : ℕ) : ℚ) * sl.num := by
        rw [mul_comm sl, mul_assoc, Rat.mul_den_eq_num]
      have hvq : ((coeffVal ρ r : ℤ) : ℚ) = coeffVal ρ kl.1 - sl * ((r : ℚ) - kl.1) := by
        rw [← hj, hnum]
        have h₄ : ((coeffVal ρ r + ((((r - kl.1) / sl.den : ℕ) : ℤ) * sl.num - coeffVal ρ kl.1) :
            ℤ) : ℚ) = ((0 : ℤ) : ℚ) :=
          congrArg (fun z : ℤ ↦ (z : ℚ)) hv
        simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast] at h₄
        linarith
      have hsq :
          (coeffVal ρ (ringChar 𝓀[K] ^ padicValNat (ringChar 𝓀[K]) r) : ℚ) ≤ coeffVal ρ r := by
        exact_mod_cast hs
      have hsr' : ((ringChar 𝓀[K] ^ padicValNat (ringChar 𝓀[K]) r : ℕ) : ℚ) < r := by
        exact_mod_cast hsr
      nlinarith
    · rfl
  · rfl
  · rfl

/-- **`x ^ k A(x ^ m)` is an additive polynomial** (LMFDB `lf.residual_polynomials`): for a totally
ramified extension `L / K` of nonarchimedean local fields, a uniformiser `α` and a segment of the
ramification polygon with right end `(-k, v_L(ρ_k))` and slope `h / m > 0`, the polynomial
`B(x) = x ^ k A(x ^ m)` over the residue field, for the residual polynomial `A` of the segment,
satisfies `B(x + y) = B(x) + B(y)` in every commutative algebra over the residue field, such as the
polynomials in `x` and `y`: its monomials are the `x ^ (p ^ e)` for the residue characteristic
`p`. -/
lemma aeval_add_X_pow_mul_comp_residualPolynomial (hKL : IsTotallyRamified K L) (hα : Irreducible α)
    (hkl : kl ∈ residualSegments (ramificationPolynomial (minpoly K (α : L)) (α : L)))
    (hpos : 0 < residualSlope (ramificationPolynomial (minpoly K (α : L)) (α : L)) kl.1 kl.2)
    {A : Type*} [CommRing A] [Algebra 𝓀[L] A] (x y : A) :
    aeval (x + y) (X ^ kl.1 * (residualPolynomial (ramificationPolynomial (minpoly K (α : L))
      (α : L)) (α : L) kl.1 kl.2).comp (X ^ (residualSlope (ramificationPolynomial
        (minpoly K (α : L)) (α : L)) kl.1 kl.2).den)) =
      aeval x (X ^ kl.1 * (residualPolynomial (ramificationPolynomial (minpoly K (α : L))
        (α : L)) (α : L) kl.1 kl.2).comp (X ^ (residualSlope (ramificationPolynomial
          (minpoly K (α : L)) (α : L)) kl.1 kl.2).den)) +
      aeval y (X ^ kl.1 * (residualPolynomial (ramificationPolynomial (minpoly K (α : L))
        (α : L)) (α : L) kl.1 kl.2).comp (X ^ (residualSlope (ramificationPolynomial
          (minpoly K (α : L)) (α : L)) kl.1 kl.2).den)) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  have hp : Fact (ringChar 𝓀[K]).Prime :=
    ⟨CharP.prime_ringChar _⟩
  have hc : CharP 𝓀[L] (ringChar 𝓀[K]) :=
    charP_of_injective_algebraMap (algebraMap 𝓀[K] 𝓀[L]).injective _
  have hcA : CharP A (ringChar 𝓀[K]) :=
    charP_of_injective_algebraMap (algebraMap 𝓀[L] A).injective _
  have he : ExpChar A (ringChar 𝓀[K]) :=
    .prime Fact.out
  rw [aeval_eq_sum_range, aeval_eq_sum_range, aeval_eq_sum_range, ← sum_add_distrib]
  refine sum_congr rfl fun r _ ↦ ?_
  by_cases hrp : ∀ e, r ≠ ringChar 𝓀[K] ^ e
  · rw [coeff_X_pow_mul_comp_residualPolynomial_eq_zero hKL hα hkl hpos hrp, zero_smul,
      zero_smul, zero_smul, add_zero]
  · push Not at hrp
    rcases hrp with ⟨e, rfl⟩
    rw [add_pow_expChar_pow, smul_add]

end IsNonarchimedeanLocalField
