import LeanBridge.ForMathlib.NumberTheory.LocalField.MongeReduction
import Mathlib.Data.Nat.Choose.Lucas
import TauCeti.NumberTheory.LocalField.Eisenstein.PowerBasis

/-!
# Monge's additive polynomials and the change of digits under a change of uniformiser

Let `R` and `S` be discrete valuation rings with `S` an `R`-algebra, `g` a monic polynomial of
degree `n ≥ 1` over `R` and `π` a uniformiser of `S` which is a root of `g`, with `v_S = n v_R` on
`R` and with the integers prime to a prime `p` invertible in `S`
(`IsNonarchimedeanLocalField.HerbrandInvariant.IsMongeRoot`). This is the situation of a monic
Eisenstein polynomial over the ring of integers of a nonarchimedean local field `K`, with a root
generating an extension `L / K`, for the residue characteristic `p`
(`IsNonarchimedeanLocalField.HerbrandInvariant.isMongeRoot_of_isEisensteinAt`).

This file proves the steps of Monge's reduction (arXiv:1109.4617, Int. J. Number Theory 10 (2014);
Proposition 2, p. 5, and Lemma 3 and Definition 1, p. 6) that do not involve the Herbrand function,
which is the subject of `LeanBridge.ForMathlib.NumberTheory.LocalField.RamificationPolygon`. By
Monge's Proposition 2, for `m ≥ 1` the reduction `S_m` of `π ^ (-N) g(π + π ^ (m + 1) T)`, for the
level `N` of `g` at `π` and `m`, is an additive polynomial: the terms of the coefficient of `T ^ r`
in `g(π + T)` have distinct valuations modulo `n`, and the coefficients at `r` and at the largest
power of `p` dividing `r` are compared by the identity
`binom(i, r) binom(r, s) = binom(i, s) binom(i - s, r - s)`, for `s = p ^ v_p(r)`, with
`binom(p ^ l u, p ^ l)` prime to `p` for `u` prime to `p`, by Lucas' theorem. So the image of
`θ ↦ (-d̄_0) ^ (j + 1) S_m(θ)` is an additive subgroup, Monge's subgroup `W_σ`, and it comes from
a single `m`, as the level is strictly increasing in `m`. By Monge's Lemma 3 and the discussion
after it, if `π + π ^ (m + 1) θ` is a root of a monic polynomial `g'` of degree `n`, then the digits
of `g` and `g'` below the level `N = σ + n` are the same, and their digits at `σ` differ by an
element of Monge's image. The second statement of Proposition 2 (`S_m` has more than one monomial
exactly at the ramification breaks) and its statement for `m = 0` are not formalised.

## Main definitions

* `IsNonarchimedeanLocalField.HerbrandInvariant.IsMongeRoot`: the hypotheses of Monge's reduction.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.pow_succ_dvd_coeff_mongeShift`,
  `IsNonarchimedeanLocalField.HerbrandInvariant.coeff_mongePolynomial_eq_zero` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.eval_mongePolynomial_add` (the first statement of
  Monge's Proposition 2): `S_m` is an additive polynomial.
* `IsNonarchimedeanLocalField.HerbrandInvariant.eq_of_mongeLevel_eq`: Monge's level is strictly
  increasing.
* `IsNonarchimedeanLocalField.HerbrandInvariant.coe_mongeSubgroup` (LMFDB `lf.family_polynomial`):
  Monge's subgroup `W_σ` is Monge's image.
* `IsNonarchimedeanLocalField.HerbrandInvariant.pow_dvd_sub_coeff_mul_pow`,
  `IsNonarchimedeanLocalField.HerbrandInvariant.pow_dvd_sub_coeff`,
  `IsNonarchimedeanLocalField.HerbrandInvariant.dvd_digit_sub` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.algebraMap_mem_mongeImage` (Monge's Lemma 3 and the
  discussion after it): the change of the digits under a change of uniformiser.
* `IsNonarchimedeanLocalField.HerbrandInvariant.isMongeRoot_of_isEisensteinAt`: Eisenstein
  generators of local fields satisfy the hypotheses of Monge's reduction.
-/

open Finset Ideal IntermediateField IsDiscreteValuationRing Polynomial TauCeti ValuativeRel

namespace IsNonarchimedeanLocalField.HerbrandInvariant

variable {ι R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S]
  [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S] {g : R[X]} {π : S} {ϖ : R} {p m r N : ℕ}

lemma pow_dvd_iff_le_addVal (hπ : Irreducible π) {n : ℕ} {y : S} :
    π ^ n ∣ y ↔ (n : ℕ∞) ≤ addVal S y := by
  rw [← addVal_le_iff_dvd, addVal_pow, addVal_uniformizer hπ, nsmul_one]

lemma pow_dvd_of_pow_dvd_sum (hπ : Irreducible π) {A : Finset ι} (x : ι → S)
    (hx : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → addVal S (x i) = addVal S (x j) → x i = 0) {k : ℕ}
    (hk : π ^ k ∣ ∑ i ∈ A, x i) {i : ι} (hi : i ∈ A) : π ^ k ∣ x i := by
  rw [pow_dvd_iff_le_addVal hπ, ← sum_coe_sort, addVal_sum_eq_iInf_of_ne (fun j : A ↦ x j)
    fun a b hab ha _ h ↦ ha (hx a a.2 b b.2 (Subtype.coe_ne_coe.mpr hab) h)] at hk
  exact (pow_dvd_iff_le_addVal hπ).mpr (hk.trans (iInf_le (fun j : A ↦ addVal S (x j)) ⟨i, hi⟩))

variable [Fact p.Prime] in
lemma coprime_choose_pow_mul (l : ℕ) {u : ℕ} (hu : p.Coprime u) :
    p.Coprime ((p ^ l * u).choose (p ^ l)) := by
  induction l with
  | zero => simpa using hu
  | succ l ih =>
    have hp : 0 < p :=
      (Fact.out : p.Prime).pos
    have h₁ : (p ^ (l + 1) * u) % p = 0 := by
      rw [pow_succ', mul_assoc]
      exact Nat.mul_mod_right _ _
    have h₂ : p ^ (l + 1) % p = 0 := by
      rw [pow_succ']
      exact Nat.mul_mod_right _ _
    have h₃ : (p ^ (l + 1) * u) / p = p ^ l * u := by
      rw [pow_succ', mul_assoc, Nat.mul_div_cancel_left _ hp]
    have h₄ : p ^ (l + 1) / p = p ^ l := by
      rw [pow_succ', Nat.mul_div_cancel_left _ hp]
    have hmod : (p ^ (l + 1) * u).choose (p ^ (l + 1)) ≡ ((p ^ (l + 1) * u) % p).choose
        (p ^ (l + 1) % p) * ((p ^ (l + 1) * u) / p).choose (p ^ (l + 1) / p) [MOD p] :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat
    rw [h₁, h₂, h₃, h₄, Nat.choose_self, one_mul] at hmod
    rw [Nat.Coprime, Nat.gcd_comm, hmod.gcd_eq, Nat.gcd_comm]
    exact ih

variable (g π p) in
/-- The **hypotheses of Monge's reduction** (Monge, arXiv:1109.4617, §2) for a polynomial `g` over a
discrete valuation ring `R`, an element `π` of a discrete valuation ring `S` over `R` and a natural
number `p`: `g` is monic of degree `n ≥ 1`, `π` is a uniformiser of `S` and a root of `g`, the
valuation of `S` restricts to `n` times the valuation of `R`, and the integers prime to `p` are
invertible in `S`. -/
structure IsMongeRoot : Prop where
  irreducible : Irreducible π
  monic : g.Monic
  natDegree_pos : 0 < g.natDegree
  aeval_eq_zero : aeval π g = 0
  addVal_algebraMap (a : R) : addVal S (algebraMap R S a) = g.natDegree • addVal R a
  isUnit_natCast {c : ℕ} (hc : p.Coprime c) : IsUnit (c : S)

lemma coeff_taylor_mul_pow (h : IsMongeRoot g π p) (hr : r ≠ 0) :
    (taylor π (g.map (algebraMap R S))).coeff r * π ^ r = ∑ i ∈ Icc 1 g.natDegree,
      algebraMap R S ((i.choose r : R) * g.coeff i) * π ^ i := by
  have hdeg : (g.map (algebraMap R S)).natDegree = g.natDegree :=
    h.monic.natDegree_map _
  have hI : Icc 1 g.natDegree = Ico 1 (g.natDegree + 1) := by
    ext i
    simp
  rw [taylor_coeff, hasseDeriv_apply, sum_over_range _ (by simp), hdeg, eval_finsetSum, sum_mul,
    range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos _), hI]
  simp only [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hr), Nat.cast_zero, zero_mul,
    monomial_zero_right, eval_zero, zero_add]
  refine sum_congr rfl fun i _ ↦ ?_
  rcases lt_or_ge i r with hi | hi
  · simp [Nat.choose_eq_zero_of_lt hi]
  · rw [eval_monomial, mul_assoc, ← pow_add, Nat.sub_add_cancel hi, coeff_map, map_mul,
      map_natCast]

lemma coeff_mongeShift (h : IsMongeRoot g π p) (hr : r ≠ 0) : (mongeShift g π m).coeff r =
    π ^ (m * r) * ∑ i ∈ Icc 1 g.natDegree,
      algebraMap R S ((i.choose r : R) * g.coeff i) * π ^ i := by
  have hcomp :
      mongeShift g π m = (taylor π (g.map (algebraMap R S))).comp (C (π ^ (m + 1)) * X) := by
    rw [mongeShift, taylor_apply, comp_assoc]
    simp [add_comm]
  rw [hcomp, comp_C_mul_X_coeff, ← coeff_taylor_mul_pow h hr, ← pow_mul, add_mul, one_mul, pow_add]
  ring1

lemma addVal_term_ne (h : IsMongeRoot g π p) {a : ℕ → R} {i j : ℕ} (hij : ¬i ≡ j [MOD g.natDegree])
    (heq : addVal S (algebraMap R S (a i) * π ^ i) = addVal S (algebraMap R S (a j) * π ^ j)) :
    algebraMap R S (a i) * π ^ i = 0 := by
  by_contra hne
  have hval (l : ℕ) :
      addVal S (algebraMap R S (a l) * π ^ l) = g.natDegree • addVal R (a l) + (l : ℕ∞) := by
    rw [addVal_mul, addVal_pow, addVal_uniformizer h.irreducible, nsmul_one, h.addVal_algebraMap]
  have htop {l : ℕ} (hl : addVal R (a l) = ⊤) : algebraMap R S (a l) * π ^ l = 0 := by
    rw [addVal_eq_top_iff.mp hl, map_zero, zero_mul]
  rcases ENat.ne_top_iff_exists.mp fun hi ↦ hne (htop hi) with ⟨k, hk⟩
  have hj : addVal R (a j) ≠ ⊤ := fun hj ↦ hne <| addVal_eq_top_iff.mp <| heq.trans <|
    addVal_eq_top_iff.mpr (htop hj)
  rcases ENat.ne_top_iff_exists.mp hj with ⟨k', hk'⟩
  rw [hval, hval, ← hk, ← hk'] at heq
  have heq' : g.natDegree * k + i = g.natDegree * k' + j := by
    exact_mod_cast (by simpa using heq :
      ((g.natDegree : ℕ∞) * k + i : ℕ∞) = (g.natDegree : ℕ∞) * k' + j)
  refine hij ?_
  rw [Nat.ModEq, ← Nat.mul_add_mod g.natDegree k i, heq', Nat.mul_add_mod]

lemma not_modEq_of_mem_Icc {n i j : ℕ} (hi : i ∈ Icc 1 n) (hj : j ∈ Icc 1 n) (hij : i ≠ j) :
    ¬i ≡ j [MOD n] := by
  intro h
  rw [mem_Icc] at hi hj
  refine hij ?_
  have h₁ : i - 1 + 1 ≡ j - 1 + 1 [MOD n] := by
    rwa [Nat.sub_add_cancel hi.1, Nat.sub_add_cancel hj.1]
  have h₂ : i - 1 = j - 1 :=
    (h₁.add_right_cancel' 1).eq_of_lt_of_lt (by omega) (by omega)
  omega

lemma addVal_coeff_taylor_add_le (h : IsMongeRoot g π p) (hr : r ≠ 0) {i : ℕ}
    (hi : i ∈ Icc 1 g.natDegree) : addVal S ((taylor π (g.map (algebraMap R S))).coeff r) + r ≤
      addVal S (algebraMap R S ((i.choose r : R) * g.coeff i) * π ^ i) := by
  refine ENat.forall_natCast_le_iff_le.mp fun k hk ↦ (pow_dvd_iff_le_addVal h.irreducible).mp ?_
  have hsum :
      π ^ k ∣ ∑ i ∈ Icc 1 g.natDegree, algebraMap R S ((i.choose r : R) * g.coeff i) * π ^ i := by
    rw [← coeff_taylor_mul_pow h hr, pow_dvd_iff_le_addVal h.irreducible, addVal_mul, addVal_pow,
      addVal_uniformizer h.irreducible, nsmul_one]
    exact hk
  exact pow_dvd_of_pow_dvd_sum h.irreducible
    (fun i ↦ algebraMap R S ((i.choose r : R) * g.coeff i) * π ^ i)
    (fun _ hi _ hj hij heq ↦ addVal_term_ne h (a := fun i ↦ (i.choose r : R) * g.coeff i)
      (not_modEq_of_mem_Icc hi hj hij) heq) hsum hi

/-- **Monge's Proposition 2 (additivity)**, in terms of coefficients: for `m ≥ 1`, the coefficient
of `T ^ r` in `g(π + π ^ (m + 1) T)` has a valuation larger than the level `N` of `g` at `π` and
`m`, unless `r` is a power of `p`. -/
lemma pow_succ_dvd_coeff_mongeShift (h : IsMongeRoot g π p) [Fact p.Prime] (hm : 1 ≤ m)
    (hN : mongeLevel g π m = N) (hr : r ≠ 0) (hrp : ∀ i, r ≠ p ^ i) :
    π ^ (N + 1) ∣ (mongeShift g π m).coeff r := by
  have hp : p.Prime :=
    Fact.out
  rcases pow_padicValNat_dvd (p := p) (n := r) with ⟨u, hu⟩
  have hu₀ : u ≠ 0 := by
    rintro rfl
    exact hr (hu.trans (mul_zero _))
  have hu₁ : u ≠ 1 := by
    rintro rfl
    exact hrp _ (hu.trans (mul_one _))
  have hu₂ : 2 ≤ u := by
    omega
  have hcop : p.Coprime u := by
    refine hp.coprime_iff_not_dvd.mpr fun hd ↦ pow_succ_padicValNat_not_dvd (p := p) hr ?_
    rw [pow_succ]
    conv_rhs => rw [hu]
    exact mul_dvd_mul_left _ hd
  have hq : p ^ padicValNat p r ≠ 0 :=
    pow_ne_zero _ hp.ne_zero
  have hle : p ^ padicValNat p r * 2 ≤ r := by
    conv_rhs => rw [hu]
    exact Nat.mul_le_mul_left _ hu₂
  have hmr : m * (p ^ padicValNat p r * 2) ≤ m * r :=
    Nat.mul_le_mul_left m hle
  have hmq : 1 ≤ m * p ^ padicValNat p r :=
    Nat.mul_pos hm (Nat.pos_of_ne_zero hq)
  have hmq₂ : m * (p ^ padicValNat p r * 2) = m * p ^ padicValNat p r * 2 := by
    ring1
  rw [coeff_mongeShift h hr]
  by_cases hNq : N < m * p ^ padicValNat p r
  · exact Dvd.dvd.mul_right (pow_dvd_pow π (by omega)) _
  have hdvd : π ^ N ∣ (mongeShift g π m).coeff (p ^ padicValNat p r) :=
    pow_dvd_of_le_emultiplicity (hN ▸ iInf_le _ _)
  rw [coeff_mongeShift h hq] at hdvd
  rcases Nat.exists_eq_add_of_le (not_lt.mp hNq) with ⟨k, rfl⟩
  rw [pow_add, mul_dvd_mul_iff_left (pow_ne_zero _ h.irreducible.ne_zero)] at hdvd
  have hterm {i : ℕ} (hi : i ∈ Icc 1 g.natDegree) :
      π ^ k ∣ algebraMap R S ((i.choose (p ^ padicValNat p r) : R) * g.coeff i) * π ^ i :=
    pow_dvd_of_pow_dvd_sum h.irreducible
      (fun i ↦ algebraMap R S ((i.choose (p ^ padicValNat p r) : R) * g.coeff i) * π ^ i)
      (fun _ hi _ hj hij heq ↦ addVal_term_ne h
        (a := fun i ↦ (i.choose (p ^ padicValNat p r) : R) * g.coeff i)
        (not_modEq_of_mem_Icc hi hj hij) heq) hdvd hi
  have hc :
      π ^ k ∣ ∑ i ∈ Icc 1 g.natDegree, algebraMap R S ((i.choose r : R) * g.coeff i) * π ^ i := by
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
        (pow_padicValNat_dvd))]
    refine (hw.dvd_mul_left).mp ?_
    have h₁ : π ^ k ∣ ((i - p ^ padicValNat p r).choose (r - p ^ padicValNat p r) : ℕ) *
        (algebraMap R S ((i.choose (p ^ padicValNat p r) : R) * g.coeff i) * π ^ i) :=
      (hterm hi).mul_left _
    have heq : ((r.choose (p ^ padicValNat p r) : ℕ) : S) *
        (algebraMap R S ((i.choose r : R) * g.coeff i) * π ^ i) =
        ((i - p ^ padicValNat p r).choose (r - p ^ padicValNat p r) : ℕ) *
          (algebraMap R S ((i.choose (p ^ padicValNat p r) : R) * g.coeff i) * π ^ i) := by
      simp only [map_mul, map_natCast]
      linear_combination (algebraMap R S (g.coeff i) * π ^ i) * hchoose
    rwa [heq]
  refine (pow_dvd_pow π ?_).trans ((pow_add π (m * r) k).symm ▸ mul_dvd_mul_left _ hc)
  omega

lemma coeff_mongeShift_zero (h : IsMongeRoot g π p) : (mongeShift g π m).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, eval_mongeShift, mul_zero, add_zero, h.aeval_eq_zero]

/-- **Monge's Proposition 2 (additivity)**: for `m ≥ 1`, the coefficients of Monge's polynomial
`S_m` vanish except at the powers of `p`. So `S_m` is an additive polynomial over the residue field
(`eval_mongePolynomial_add`). -/
lemma coeff_mongePolynomial_eq_zero (h : IsMongeRoot g π p) [Fact p.Prime] (hm : 1 ≤ m)
    (hN : mongeLevel g π m = N) (hrp : ∀ i, r ≠ p ^ i) : (mongePolynomial g π m).coeff r = 0 := by
  rw [mongePolynomial, finsetSum_coeff]
  refine sum_eq_zero fun k hk ↦ ?_
  rw [coeff_C_mul_X_pow]
  by_cases hrk : r = k
  · subst hrk
    rw [ite_eq_left rfl]
    have hr : r ≠ 0 := by
      rintro rfl
      exact mem_support_iff.mp hk (coeff_mongeShift_zero h)
    have hN' : (mongeLevel g π m).toNat = N := by
      rw [hN, ENat.toNat_natCast]
    have hdvd : π ^ (N + 1) ∣ (mongeShift g π m).coeff r :=
      pow_succ_dvd_coeff_mongeShift h hm hN hr hrp
    have hdvd₀ : π ^ (mongeLevel g π m).toNat ∣ (mongeShift g π m).coeff r := by
      rw [hN']
      exact (pow_dvd_pow π N.le_succ).trans hdvd
    rw [dite_eq_left hdvd₀, Quotient.algebraMap_eq, Quotient.eq_zero_iff_mem, mem_span_singleton]
    have hq : (mongeShift g π m).coeff r = π ^ (mongeLevel g π m).toNat *
        (exists_eq_mul_right_of_dvd hdvd₀).choose :=
      (exists_eq_mul_right_of_dvd hdvd₀).choose_spec
    generalize (exists_eq_mul_right_of_dvd hdvd₀).choose = q at hq ⊢
    rw [hq, hN', pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ h.irreducible.ne_zero)] at hdvd
    exact hdvd
  · exact ite_eq_right hrk

/-- **Monge's polynomial `S_m` is additive** (Monge, the first statement of Proposition 2), for
`m ≥ 1` and a residue field of characteristic `p`. So its image is an additive subgroup of the
residue field. -/
lemma eval_mongePolynomial_add (h : IsMongeRoot g π p) [Fact p.Prime] [CharP (S ⧸ span {π}) p]
    (hm : 1 ≤ m) (hN : mongeLevel g π m = N) (x y : S ⧸ span {π}) :
    (mongePolynomial g π m).eval (x + y) = (mongePolynomial g π m).eval x +
      (mongePolynomial g π m).eval y := by
  have he : ExpChar (S ⧸ span {π}) p :=
    .prime Fact.out
  rw [eval_eq_sum, eval_eq_sum, eval_eq_sum, sum_def, sum_def, sum_def, ← sum_add_distrib]
  refine sum_congr rfl fun r hr ↦ ?_
  by_cases hrp : ∀ i, r ≠ p ^ i
  · exact absurd (coeff_mongePolynomial_eq_zero h hm hN hrp) (mem_support_iff.mp hr)
  · push Not at hrp
    rcases hrp with ⟨i, rfl⟩
    rw [add_pow_expChar_pow, mul_add]

lemma emultiplicity_eq_addVal (hπ : Irreducible π) (y : S) : emultiplicity π y = addVal S y :=
  ENat.eq_of_forall_natCast_le_iff fun n ↦ by
    rw [← pow_dvd_iff_le_emultiplicity, ← addVal_le_iff_dvd, addVal_pow, addVal_uniformizer hπ,
      nsmul_one]

lemma mongeLevel_add_le (h : IsMongeRoot g π p) (m k : ℕ) :
    mongeLevel g π m + k ≤ mongeLevel g π (m + k) := by
  refine le_iInf fun r ↦ ?_
  rcases eq_or_ne r 0 with rfl | hr
  · rw [coeff_mongeShift_zero h, emultiplicity_zero_right]
    exact le_top
  have hle : mongeLevel g π m ≤ addVal S ((mongeShift g π m).coeff r) := by
    rw [← emultiplicity_eq_addVal h.irreducible]
    exact iInf_le _ r
  have hcoeff : (mongeShift g π (m + k)).coeff r = π ^ (k * r) * (mongeShift g π m).coeff r := by
    rw [coeff_mongeShift h hr, coeff_mongeShift h hr, ← mul_assoc, ← pow_add]
    ring1
  rw [emultiplicity_eq_addVal h.irreducible, hcoeff, addVal_mul, addVal_pow,
    addVal_uniformizer h.irreducible, nsmul_one, add_comm]
  refine add_le_add ?_ hle
  exact_mod_cast Nat.le_mul_of_pos_right k (Nat.pos_of_ne_zero hr)

lemma natCast_lt_mongeLevel (h : IsMongeRoot g π p) (hN : mongeLevel g π m = N) {m' : ℕ}
    (hmm' : m < m') : (N : ℕ∞) < mongeLevel g π m' := by
  rcases Nat.exists_eq_add_of_lt hmm' with ⟨k, rfl⟩
  refine lt_of_lt_of_le ?_ (mongeLevel_add_le h m (k + 1))
  rw [hN]
  exact_mod_cast Nat.lt_add_of_pos_right k.succ_pos

/-- **Monge's level is strictly increasing**: for a root `π` of `g`, there is at most one `m` with a
given finite level. So Monge's image at `σ` comes from a single `m`. -/
lemma eq_of_mongeLevel_eq (h : IsMongeRoot g π p) (hN : mongeLevel g π m = N) {m' : ℕ}
    (hN' : mongeLevel g π m' = N) : m = m' := by
  rcases lt_trichotomy m m' with hlt | heq | hlt
  · exact absurd hN'.symm (natCast_lt_mongeLevel h hN hlt).ne
  · exact heq
  · exact absurd hN.symm (natCast_lt_mongeLevel h hN' hlt).ne

/-- **Monge's subgroup is Monge's image** (Monge, Proposition 2, Definition 1): for a root `π` of
`g`, if `g(0) = ϖ d_0` with `ϖ ≠ 0` and the level of `g` at `π` and some `m ≥ 1` is `σ + n`, then
the additive subgroup `W_σ` generated by the image of `θ ↦ (-d̄_0) ^ (j + 1) S_m(θ)` is that image,
since `S_m` is additive. -/
lemma coe_mongeSubgroup (h : IsMongeRoot g π p) [Fact p.Prime] [CharP (S ⧸ span {π}) p]
    (𝔪 : Ideal R) (hϖ : ϖ ≠ 0) {d : R} (hd : g.coeff 0 = ϖ * d) {σ : ℕ} (hm : 1 ≤ m)
    (hN : mongeLevel g π m = (σ + g.natDegree : ℕ)) :
    (mongeSubgroup ϖ 𝔪 g π σ : Set (R ⧸ 𝔪)) = mongeImage ϖ 𝔪 g π σ := by
  have hπ : π ≠ 0 :=
    h.irreducible.ne_zero
  have hadd (k : ℕ) (hk : 1 ≤ k) (hl : mongeLevel g π k = (σ + g.natDegree : ℕ))
      (x y : S ⧸ span {π}) : (mongePolynomial g π k).eval (x + y) =
        (mongePolynomial g π k).eval x + (mongePolynomial g π k).eval y :=
    eval_mongePolynomial_add h hk hl x y
  have hzero (k : ℕ) (hk : 1 ≤ k) (hl : mongeLevel g π k = (σ + g.natDegree : ℕ)) :
      (mongePolynomial g π k).eval 0 = 0 := by
    have h₀ : (mongePolynomial g π k).eval (0 + 0) =
        (mongePolynomial g π k).eval 0 + (mongePolynomial g π k).eval 0 :=
      hadd k hk hl 0 0
    rwa [add_zero, left_eq_add] at h₀
  have hneg (k : ℕ) (hk : 1 ≤ k) (hl : mongeLevel g π k = (σ + g.natDegree : ℕ))
      (x : S ⧸ span {π}) : (mongePolynomial g π k).eval (-x) = -(mongePolynomial g π k).eval x := by
    rw [eq_neg_iff_add_eq_zero, ← hadd k hk hl, neg_add_cancel, hzero k hk hl]
  let W : AddSubgroup (R ⧸ 𝔪) :=
    { carrier := mongeImage ϖ 𝔪 g π σ
      add_mem' := by
        intro x y hx hy
        rcases (mem_mongeImage_iff hπ).mp hx with ⟨k, hk, hl, d₁, r₁, θ₁, hd₁, rfl, h₁⟩
        rcases (mem_mongeImage_iff hπ).mp hy with ⟨k', -, hl', d₂, r₂, θ₂, hd₂, rfl, h₂⟩
        have hk' : k' = k :=
          eq_of_mongeLevel_eq h hl' hl
        subst hk'
        have hd' : d₂ = d₁ :=
          mul_left_cancel₀ hϖ (hd₂.symm.trans hd₁)
        subst hd'
        refine (mem_mongeImage_iff hπ).mpr
          ⟨k', hk, hl, d₂, r₁ + r₂, θ₁ + θ₂, hd₁, map_add _ _ _, ?_⟩
        rw [map_add, map_add, h₁, h₂, map_add, map_add, hadd k' hk hl, mul_add]
      zero_mem' := by
        refine (mem_mongeImage_iff hπ).mpr ⟨m, hm, hN, d, 0, 0, hd, map_zero _, ?_⟩
        simp only [map_zero, hzero m hm hN, mul_zero]
      neg_mem' := by
        intro x hx
        rcases (mem_mongeImage_iff hπ).mp hx with ⟨k, hk, hl, d₁, r₁, θ₁, hd₁, rfl, h₁⟩
        refine (mem_mongeImage_iff hπ).mpr ⟨k, hk, hl, d₁, -r₁, -θ₁, hd₁, map_neg _ _, ?_⟩
        rw [map_neg, map_neg, h₁, map_neg, map_neg, hneg k hk hl, mul_neg] }
  have hW : mongeSubgroup ϖ 𝔪 g π σ = W :=
    AddSubgroup.closure_eq W
  rw [hW]
  rfl

variable {g' : R[X]} {x u : S} {a : ℕ → R} {j i₀ : ℕ}

variable (x) in
lemma isUnit_one_add_pow_mul (hπ : Irreducible π) (hm : 1 ≤ m) : IsUnit (1 + π ^ m * x) := by
  have h₁ : -(π ^ m * x) ∈ nonunits S := by
    refine fun hu ↦ hπ.not_isUnit (isUnit_of_dvd_unit ?_ hu)
    exact (dvd_neg.mpr (Dvd.dvd.mul_right (dvd_pow_self π (by omega)) x))
  simpa using IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ h₁

lemma eval_mongeShift_eq_sum (h : IsMongeRoot g π p) (hg' : g'.Monic)
    (hdeg : g'.natDegree = g.natDegree) (hρ : aeval (π + π ^ (m + 1) * x) g' = 0) :
    (mongeShift g π m).eval x = ∑ i ∈ range g.natDegree,
      algebraMap R S (g.coeff i - g'.coeff i) * (π + π ^ (m + 1) * x) ^ i := by
  have hsum {f : R[X]} (hf : f.Monic) (y : S) : aeval y f =
      ∑ i ∈ range f.natDegree, algebraMap R S (f.coeff i) * y ^ i + y ^ f.natDegree := by
    rw [aeval_eq_sum_range, sum_range_succ, hf.coeff_natDegree, one_smul]
    simp only [Algebra.smul_def]
  rw [eval_mongeShift, ← sub_zero (aeval _ g), ← hρ, hsum h.monic, hsum hg', hdeg,
    add_sub_add_right_eq_sub, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [map_sub, sub_mul]

lemma addVal_ne_of_not_modEq (h : IsMongeRoot g π p) {i : ℕ} {b : R} {v : ℕ} (hm : 1 ≤ m)
    (hi : ¬i ≡ v [MOD g.natDegree]) :
    addVal S (algebraMap R S b * (π + π ^ (m + 1) * x) ^ i) ≠ v := by
  have hρ : π + π ^ (m + 1) * x = π * (1 + π ^ m * x) := by
    ring1
  rcases isUnit_one_add_pow_mul x h.irreducible hm with ⟨w, hw⟩
  intro heq
  rw [hρ, mul_pow, ← mul_assoc, addVal_mul, ← hw, ← Units.val_pow_eq_pow_val,
    addVal_eq_zero_of_unit, add_zero, addVal_mul, addVal_pow, addVal_uniformizer h.irreducible,
    nsmul_one, h.addVal_algebraMap] at heq
  rcases ENat.ne_top_iff_exists.mp (fun htop : addVal R b = ⊤ ↦ ENat.natCast_ne_top v <| by
    rw [← heq, htop]
    simp [h.natDegree_pos.ne']) with ⟨k, hk⟩
  rw [← hk] at heq
  refine hi ?_
  have heq' : g.natDegree * k + i = v := by
    exact_mod_cast (by simpa using heq : ((g.natDegree : ℕ∞) * k + i : ℕ∞) = v)
  rw [Nat.ModEq, ← heq', Nat.mul_add_mod]

/-- **The terms below the level** (Monge, the discussion after Lemma 3, p. 6): if
`π + π ^ (m + 1) x`, `m ≥ 1`, is a root of a monic polynomial `g'` of the degree of `g`, then the
difference of the coefficients of `g` and `g'` at `T ^ i` has level at least the level `N` of `g` at
`π` and `m`: `π ^ N ∣ (g_i - g'_i) π ^ i`. So the digits of `g` and `g'` below the level `N` are the
same. -/
lemma pow_dvd_sub_coeff_mul_pow (h : IsMongeRoot g π p) (hg' : g'.Monic)
    (hdeg : g'.natDegree = g.natDegree) (hρ : aeval (π + π ^ (m + 1) * x) g' = 0) (hm : 1 ≤ m)
    (hN : mongeLevel g π m = N) {i : ℕ} (hi : i < g.natDegree) :
    π ^ N ∣ algebraMap R S (g.coeff i - g'.coeff i) * π ^ i := by
  have hdvd : π ^ N ∣ (mongeShift g π m).eval x := by
    have hC : C (π ^ N) ∣ mongeShift g π m :=
      (C_dvd_iff_dvd_coeff _ _).mpr fun i ↦ pow_dvd_of_le_emultiplicity (hN ▸ iInf_le _ i)
    simpa using eval_dvd (x := x) hC
  rw [eval_mongeShift_eq_sum h hg' hdeg hρ] at hdvd
  have hterm : π ^ N ∣ algebraMap R S (g.coeff i - g'.coeff i) * (π + π ^ (m + 1) * x) ^ i := by
    refine pow_dvd_of_pow_dvd_sum h.irreducible
      (fun i ↦ algebraMap R S (g.coeff i - g'.coeff i) * (π + π ^ (m + 1) * x) ^ i)
      (fun i hi j hj hij heq ↦ ?_) hdvd (mem_range.mpr hi)
    by_contra hne
    rcases ENat.ne_top_iff_exists.mp (fun htop ↦ hne (addVal_eq_top_iff.mp htop)) with ⟨v, hv⟩
    have hiv : i ≡ v [MOD g.natDegree] :=
      by_contra fun hc ↦ addVal_ne_of_not_modEq h hm hc hv.symm
    have hjv : j ≡ v [MOD g.natDegree] :=
      by_contra fun hc ↦ addVal_ne_of_not_modEq h hm hc (heq.symm.trans hv.symm)
    exact hij ((hiv.trans hjv.symm).eq_of_lt_of_lt (mem_range.mp hi) (mem_range.mp hj))
  have hρ' : π + π ^ (m + 1) * x = π * (1 + π ^ m * x) := by
    ring1
  rw [hρ', mul_pow, ← mul_assoc] at hterm
  exact ((isUnit_one_add_pow_mul x h.irreducible hm).pow i).dvd_mul_right.mp hterm

/-- **Monge's Lemma 3 for the digits** (Monge, Lemma 3, p. 6, with the computation after Algorithm
2, p. 7): if `π + π ^ (m + 1) x`, `m ≥ 1`, is a root of a monic polynomial `g'` of the degree of
`g`, where `g(0) = ϖ a_0`, the coefficients of `g` are `g_i = ϖ a_i` and the level of `g` at `π` and
`m` is `(j + 1) n + i₀`, `i₀ < n`, then the digit `δ` of the difference of the coefficients of
`T ^ i₀` of `g` and `g'`, `g_i₀ - g'_i₀ = ϖ ^ (j + 1) δ`, satisfies `δ ≡ (-a_0) ^ (j + 1) u` modulo
`π`, where `g(π + π ^ (m + 1) x) = π ^ ((j + 1) n + i₀) u`. -/
lemma dvd_digit_sub (h : IsMongeRoot g π p) (ha : ∀ i < g.natDegree, g.coeff i = ϖ * a i)
    (hg' : g'.Monic) (hdeg : g'.natDegree = g.natDegree) (hρ : aeval (π + π ^ (m + 1) * x) g' = 0)
    (hm : 1 ≤ m) (hN : mongeLevel g π m = ((j + 1) * g.natDegree + i₀ : ℕ)) (hi₀ : i₀ < g.natDegree)
    {δ₀ : R} (hδ : g.coeff i₀ - g'.coeff i₀ = ϖ ^ (j + 1) * δ₀)
    (hu : (mongeShift g π m).eval x = π ^ ((j + 1) * g.natDegree + i₀) * u) :
    π ∣ algebraMap R S δ₀ - algebraMap R S ((-a 0) ^ (j + 1)) * u := by
  have hsum : (mongeShift g π m).eval x = ∑ i ∈ range g.natDegree,
      algebraMap R S (g.coeff i - g'.coeff i) * (π + π ^ (m + 1) * x) ^ i :=
    eval_mongeShift_eq_sum h hg' hdeg hρ
  have hρ' : π + π ^ (m + 1) * x = π * (1 + π ^ m * x) := by
    ring1
  have hother {i : ℕ} (hi : i ∈ (range g.natDegree).erase i₀) :
      π ^ ((j + 1) * g.natDegree + i₀ + 1) ∣
        algebraMap R S (g.coeff i - g'.coeff i) * (π + π ^ (m + 1) * x) ^ i := by
    have hi' : i < g.natDegree :=
      mem_range.mp (mem_of_mem_erase hi)
    have hdvd : π ^ ((j + 1) * g.natDegree + i₀) ∣
        algebraMap R S (g.coeff i - g'.coeff i) * (π + π ^ (m + 1) * x) ^ i := by
      rw [hρ', mul_pow, ← mul_assoc]
      exact (pow_dvd_sub_coeff_mul_pow h hg' hdeg hρ hm hN hi').mul_right _
    have hmod : ¬i ≡ (j + 1) * g.natDegree + i₀ [MOD g.natDegree] := fun hc ↦
      ne_of_mem_erase hi <| (hc.trans (by
        simp)).eq_of_lt_of_lt hi' hi₀
    rw [pow_dvd_iff_le_addVal h.irreducible] at hdvd ⊢
    exact_mod_cast Order.add_one_le_of_lt (lt_of_le_of_ne hdvd
      (addVal_ne_of_not_modEq h hm hmod).symm)
  have htop : π ^ ((j + 1) * g.natDegree + i₀ + 1) ∣
      algebraMap R S (g.coeff i₀ - g'.coeff i₀) * (π + π ^ (m + 1) * x) ^ i₀ -
        π ^ ((j + 1) * g.natDegree + i₀) * u := by
    rw [← hu, hsum, ← add_sum_erase _ _ (mem_range.mpr hi₀), sub_add_cancel_left]
    exact (dvd_neg.mpr (dvd_sum fun i hi ↦ hother hi))
  have hπn :
      π ^ g.natDegree = algebraMap R S ϖ * -∑ i ∈ range g.natDegree, algebraMap R S (a i) * π ^ i :=
    pow_natDegree_eq_mul_neg_sum h.monic ha h.aeval_eq_zero
  have hv : π ∣ -∑ i ∈ range g.natDegree, algebraMap R S (a i) * π ^ i + algebraMap R S (a 0) :=
    mem_span_singleton.mp (neg_sum_add_mem_span_singleton h.natDegree_pos)
  generalize -∑ i ∈ range g.natDegree, algebraMap R S (a i) * π ^ i = v at hπn hv
  have hP :
      π ^ ((j + 1) * g.natDegree + i₀) = algebraMap R S ϖ ^ (j + 1) * π ^ i₀ * v ^ (j + 1) := by
    rw [pow_add, mul_comm (j + 1), pow_mul, hπn, mul_pow]
    ring1
  have hX : π ^ ((j + 1) * g.natDegree + i₀ + 1) ∣ π ^ ((j + 1) * g.natDegree + i₀) *
      (algebraMap R S δ₀ * (1 + π ^ m * x) ^ i₀ - v ^ (j + 1) * u) := by
    have heq : π ^ ((j + 1) * g.natDegree + i₀) *
        (algebraMap R S δ₀ * (1 + π ^ m * x) ^ i₀ - v ^ (j + 1) * u) =
        (algebraMap R S (g.coeff i₀ - g'.coeff i₀) * (π + π ^ (m + 1) * x) ^ i₀ -
          π ^ ((j + 1) * g.natDegree + i₀) * u) * v ^ (j + 1) := by
      rw [hδ, hρ', hP, map_mul, map_pow, mul_pow]
      ring1
    rw [heq]
    exact htop.mul_right _
  rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ h.irreducible.ne_zero)] at hX
  have hw : π ∣ (1 + π ^ m * x) ^ i₀ - 1 ^ i₀ := by
    refine dvd_trans ?_ (sub_dvd_pow_sub_pow _ _ i₀)
    rw [add_sub_cancel_left]
    exact (dvd_pow_self π (by omega)).mul_right x
  have hv' : π ∣ v ^ (j + 1) - (-algebraMap R S (a 0)) ^ (j + 1) := by
    refine dvd_trans ?_ (sub_dvd_pow_sub_pow _ _ (j + 1))
    rwa [sub_neg_eq_add]
  have heq : algebraMap R S δ₀ - algebraMap R S ((-a 0) ^ (j + 1)) * u =
      (algebraMap R S δ₀ * (1 + π ^ m * x) ^ i₀ - v ^ (j + 1) * u) -
        algebraMap R S δ₀ * ((1 + π ^ m * x) ^ i₀ - 1 ^ i₀) +
          (v ^ (j + 1) - (-algebraMap R S (a 0)) ^ (j + 1)) * u := by
    rw [map_pow, map_neg, one_pow]
    ring1
  rw [heq]
  exact dvd_add (dvd_sub hX (hw.mul_left _)) (hv'.mul_right _)

/-- **The term at the level** (Monge, the discussion after Lemma 3, p. 6): if `π + π ^ (m + 1) x`,
`m ≥ 1`, is a root of a monic polynomial `g'` of the degree of `g`, and the level of `g` at `π` and
`m` is `(j + 1) n + i₀`, `i₀ < n`, then the difference of the coefficients of `T ^ i₀` of `g` and
`g'` is divisible by `ϖ ^ (j + 1)`, for a uniformiser `ϖ` of `R`. -/
lemma pow_dvd_sub_coeff (h : IsMongeRoot g π p) (hg' : g'.Monic) (hdeg : g'.natDegree = g.natDegree)
    (hρ : aeval (π + π ^ (m + 1) * x) g' = 0) (hm : 1 ≤ m)
    (hN : mongeLevel g π m = ((j + 1) * g.natDegree + i₀ : ℕ)) (hi₀ : i₀ < g.natDegree)
    (hϖ : Irreducible ϖ) : ϖ ^ (j + 1) ∣ g.coeff i₀ - g'.coeff i₀ := by
  have hle : (((j + 1) * g.natDegree + i₀ : ℕ) : ℕ∞) ≤
      addVal S (algebraMap R S (g.coeff i₀ - g'.coeff i₀) * π ^ i₀) :=
    (pow_dvd_iff_le_addVal h.irreducible).mp (pow_dvd_sub_coeff_mul_pow h hg' hdeg hρ hm hN hi₀)
  rw [addVal_mul, addVal_pow, addVal_uniformizer h.irreducible, nsmul_one,
    h.addVal_algebraMap] at hle
  rw [pow_dvd_iff_le_addVal hϖ]
  rcases eq_or_ne (addVal R (g.coeff i₀ - g'.coeff i₀)) ⊤ with htop | htop
  · rw [htop]
    exact le_top
  rcases ENat.ne_top_iff_exists.mp htop with ⟨k, hk⟩
  rw [← hk] at hle ⊢
  have hle' : (j + 1) * g.natDegree + i₀ ≤ g.natDegree * k + i₀ := by
    exact_mod_cast (by simpa using hle :
      (((j + 1) * g.natDegree + i₀ : ℕ) : ℕ∞) ≤ (g.natDegree : ℕ∞) * k + i₀)
  rw [mul_comm] at hle'
  exact_mod_cast Nat.le_of_mul_le_mul_left (Nat.le_of_add_le_add_right hle') h.natDegree_pos

/-- **The change of a digit lies in Monge's image** (Monge, Lemma 3, p. 6, and the computation after
Algorithm 2, p. 7): if `π + π ^ (m + 1) θ`, `m ≥ 1`, `θ ∈ R`, is a root of a monic polynomial `g'`
of the degree of `g`, and the level of `g` at `π` and `m` is `σ + n` for `σ = j n + i₀`, `i₀ < n`,
then the digit at `σ` of the difference of `g` and `g'` lies in Monge's image at `σ`, the image of
`θ ↦ (-d̄_0) ^ (j + 1) S_m(θ)`. -/
lemma algebraMap_mem_mongeImage (𝔪 : Ideal R) {θ : R} (h : IsMongeRoot g π p)
    (ha : ∀ i < g.natDegree, g.coeff i = ϖ * a i) (hg' : g'.Monic)
    (hdeg : g'.natDegree = g.natDegree) (hρ : aeval (π + π ^ (m + 1) * algebraMap R S θ) g' = 0)
    (hm : 1 ≤ m) (hN : mongeLevel g π m = ((j + 1) * g.natDegree + i₀ : ℕ)) (hi₀ : i₀ < g.natDegree)
    {δ₀ : R} (hδ : g.coeff i₀ - g'.coeff i₀ = ϖ ^ (j + 1) * δ₀) :
    algebraMap R (R ⧸ 𝔪) δ₀ ∈ mongeImage ϖ 𝔪 g π (j * g.natDegree + i₀) := by
  have hdvd : π ^ ((j + 1) * g.natDegree + i₀) ∣ (mongeShift g π m).eval (algebraMap R S θ) := by
    have hC : C (π ^ ((j + 1) * g.natDegree + i₀)) ∣ mongeShift g π m :=
      (C_dvd_iff_dvd_coeff _ _).mpr fun i ↦ pow_dvd_of_le_emultiplicity (hN ▸ iInf_le _ i)
    simpa using eval_dvd (x := algebraMap R S θ) hC
  rcases hdvd with ⟨u, hu⟩
  have hsum : j * g.natDegree + i₀ + g.natDegree = (j + 1) * g.natDegree + i₀ := by
    ring1
  have hdiv : (j * g.natDegree + i₀) / g.natDegree = j := by
    rw [mul_comm, Nat.mul_add_div h.natDegree_pos, Nat.div_eq_of_lt hi₀, add_zero]
  refine ⟨m, hm, by rw [hsum]; exact hN, a 0, δ₀, θ, u, ha 0 h.natDegree_pos, rfl, ?_,
    mem_span_singleton.mpr ?_⟩
  · rw [hsum]
    exact hu
  · rw [hdiv]
    exact dvd_digit_sub h ha hg' hdeg hρ hm hN hi₀ hδ hu

lemma charP_quotient (h : IsMongeRoot g π p) [Fact p.Prime] (hp : π ∣ p) :
    CharP (S ⧸ span {π}) p := by
  have hne : Nontrivial (S ⧸ span {π}) :=
    Quotient.nontrivial_iff.mpr (span_singleton_eq_top.not.mpr h.irreducible.not_isUnit)
  have h₀ : ((p : ℕ) : S ⧸ span {π}) = 0 := by
    rw [← map_natCast (algebraMap S (S ⧸ span {π})), Quotient.algebraMap_eq,
      Quotient.eq_zero_iff_mem, mem_span_singleton]
    exact hp
  exact ringChar.of_eq (CharP.ringChar_of_prime_eq_zero Fact.out h₀)

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- **An Eisenstein generator of a local field gives the data of Monge's reduction**: for a monic
Eisenstein polynomial `f` over `𝒪[K]` with a root `ξ ∈ 𝒪[L]` generating `L` over `K`, for a residue
field of `L` of characteristic `p`. -/
lemma isMongeRoot_of_isEisensteinAt {f : 𝒪[K][X]} (hm : f.Monic) (hf : f.IsEisensteinAt 𝓂[K])
    {ξ : 𝒪[L]} (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ) (hgen : K⟮(ξ : L)⟯ = ⊤)
    [Fact p.Prime] [CharP 𝓀[L] p] : IsMongeRoot f ξ p where
  irreducible := irreducible_of_eisenstein_adjoin_eq_top f hf ξ hroot hgen
  monic := hm
  natDegree_pos := by
    refine Nat.pos_of_ne_zero fun h₀ ↦ ?_
    have h₁ : f = 1 :=
      hm.natDegree_eq_zero.mp h₀
    simp [h₁] at hroot
  aeval_eq_zero := by
    rw [aeval_def, eval₂_eq_eval_map]
    exact hroot
  addVal_algebraMap a := by
    rw [TauCeti.addVal_algebraMap,
      ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top f hf ξ hroot hgen]
  isUnit_natCast {c} hc := by
    refine (IsLocalRing.residue_ne_zero_iff_isUnit _).mp fun h₀ ↦ ?_
    rw [map_natCast, CharP.cast_eq_zero_iff 𝓀[L] p c] at h₀
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hc h₀

end IsNonarchimedeanLocalField.HerbrandInvariant
