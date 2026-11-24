import LeanBridge.ForMathlib.NumberTheory.LocalField.AssociatedInertia
import LeanBridge.ForMathlib.NumberTheory.LocalField.ResidualPolynomialAdditive
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Ore's theorem: the residual polynomials split over the residue field of a Galois closure

Let `L / K` be a totally ramified extension of nonarchimedean local fields, `α` a uniformiser of
`L` with minimal polynomial `φ` over `K`, `ρ(x) = α ^ (-n) φ(α x + α)` its ramification polynomial
and `M` a finite Galois extension of `K` containing `L`. For a segment `S` of the ramification
polygon, of slope `h / m` in lowest terms, Ore's theorem says that the residual polynomial `A_S` of
`S` (LMFDB `lf.residual_polynomials`) splits over the residue field of `M`, its roots being the
residues of `β ^ m / α ^ h` for the roots `β` of `ρ` of valuation `h / m`. This file proves the
splitting, not the description of the roots. Consequently the degrees of the irreducible factors of
`A_S`, and so the associated inertia of `S` (LMFDB `lf.associated_inertia`), divide the residue
degree `f(M / L)`.

The proof works with the Gauss norms `‖P‖_c = max_j |P_j| c ^ j` of polynomials over `𝒪_M`, for the
absolute value `|x| = 2 ^ (-v_M(x))`, which are multiplicative, and the factorisation
`φ(α + y x) = ∏_σ (α - σ α + y x)` over the cosets `σ` of `Gal(M / L)` in `Gal(M / K)`.
* **A root of valuation `h / m`.** At the radius `c = |α| ^ (h / m)` the coefficients `α ^ n ρ_k`
  and `α ^ n ρ_{k + l}` of `φ(α + α x)` are both dominant, for the ends `(-k, v(ρ_k))` and
  `(-k - l, v(ρ_{k + l}))` of `S`. If no factor `α - σ α + α x` had two dominant coefficients, each
  would be close to a monomial and so would their product, which would then have a single dominant
  coefficient. So some conjugate gives `γ = α - σ α` with `|γ| = |α| c`, that is
  `γ ^ m = α ^ (m + h) w` for a unit `w`.
* **The reduction.** The factors of `G(z) = φ(α + γ z)` are close to constants or are `γ (z - r)`
  with `r ∈ 𝒪_M`, so `G = E Q` with `Q` congruent to a product of linear polynomials modulo the
  maximal ideal. On the other hand `G_j α ^ j = γ ^ j α ^ n ρ_j`, so the coefficient `|G_j|` is
  `|α ^ n ρ_j| c ^ j`, the largest on the points of `S`, and the reduction of `Q` is
  `κ z ^ k A_S(w̄ z ^ m)` for some `κ ≠ 0`. So `A_S(w̄ z ^ m)` splits over the residue field of `M`,
  and every irreducible factor of `A_S` has a root there, hence splits, the residue extension being
  normal.

Over the maximal unramified subextension of a finite extension, this is the divisibility stated in
the knowl `lf.associated_inertia`: the associated inertias divide the residue degree of the
splitting field of `φ`, and so also the residue degree of the Galois closure of the extension, the
Galois unramified degree (`ResidualPolynomialSplittingInertia.lean`).

## Main results

* `Polynomial.not_gaussNorm_sub_C_mul_X_pow_lt`: a polynomial with two dominant coefficients at a
  radius is not close to a monomial.
* `IsNonarchimedeanLocalField.exists_addValAbs_eq_mul_of_dominant`: if a product of linear
  polynomials `u_c + y x` over a discrete valuation ring has two dominant coefficients at the radius
  `c`, one factor has `|u_c| = |y| c`.
* `IsNonarchimedeanLocalField.exists_eq_C_mul_splits`: a product of linear polynomials `u_c + y x`
  over a discrete valuation ring is a constant times a polynomial whose reduction splits.
* `IsNonarchimedeanLocalField.coeffVal_sub_mul_lt_of_ne`: the points of `ρ` other than the points
  `(-(k + i m), v(ρ_{k + i m}))` of a segment lie strictly above its line.
* `IsNonarchimedeanLocalField.exists_addValAbs_sub_smul_eq`: a conjugate `σ α` with
  `|α - σ α| = |α| c` at the radius `c` of a segment: `ρ` has a root of valuation `h / m`.
* `IsNonarchimedeanLocalField.splits_map_residualPolynomial` (LMFDB `lf.associated_inertia`, Ore's
  theorem): the residual polynomial of a segment splits over the residue field of `M`.
* `IsNonarchimedeanLocalField.associatedInertia_dvd_inertiaDegree` (LMFDB `lf.associated_inertia`):
  the associated inertia of a segment divides `f(M / L)`.

## References

* O. Ore, *Newtonsche Polygone in der Theorie der algebraischen Körper*, Math. Ann. 99 (1928).
* S. Pauli and B. Sinclair, *Enumerating extensions of (π)-adic fields with given invariants*,
  Int. J. Number Theory 13 (2017); arXiv:1504.06671, Section 4.
* J. Guàrdia, J. Montes and E. Nart, *Newton polygons of higher order in algebraic number theory*,
  Trans. Amer. Math. Soc. 364 (2012), Theorem 1.15.
-/

open Finset IsDiscreteValuationRing Polynomial TauCeti UniqueFactorizationMonoid ValuativeRel

namespace Polynomial

variable {R : Type*} [CommRing R] {v : AbsoluteValue R ℝ} {c : ℝ} {G : R[X]} {i j : ℕ}

/-- **A polynomial with two dominant coefficients is not close to a monomial**: for a
nonarchimedean absolute value `v`, a radius `c > 0` and a polynomial `G` whose coefficients of
degrees `i ≠ j` both attain `max_n v(G_n) c ^ n`, no monomial `d x ^ s` satisfies
`‖G - d x ^ s‖ < ‖d x ^ s‖` for the Gauss norm at `c`: that would make `s` the only dominant degree
of `G`. -/
lemma not_gaussNorm_sub_C_mul_X_pow_lt (hv : IsNonarchimedean v) (hc : 0 < c) (hij : i ≠ j)
    (hi : ∀ n, v (G.coeff n) * c ^ n ≤ v (G.coeff i) * c ^ i)
    (hj : v (G.coeff j) * c ^ j = v (G.coeff i) * c ^ i) (d : R) (s : ℕ) :
    ¬(G - C d * X ^ s).gaussNorm v c < (C d * X ^ s).gaussNorm v c := by
  intro hlt
  rw [C_mul_X_pow_eq_monomial, gaussNorm_monomial] at hlt
  have hcoeff (n : ℕ) : v ((G - monomial s d).coeff n) * c ^ n < v d * c ^ s :=
    (le_gaussNorm v _ hc.le n).trans_lt hlt
  have hs : v d ≤ v (G.coeff s) := by
    have h₁ : v (G.coeff s - d) < v d := by
      have h₂ : v ((G - monomial s d).coeff s) * c ^ s < v d * c ^ s :=
        hcoeff s
      rw [coeff_sub, coeff_monomial_same] at h₂
      exact lt_of_mul_lt_mul_right h₂ (pow_nonneg hc.le s)
    have h₂ : v d ≤ max (v (G.coeff s)) (v (G.coeff s - d)) := by
      have h₃ : v (G.coeff s + (d - G.coeff s)) ≤ max (v (G.coeff s)) (v (d - G.coeff s)) :=
        hv _ _
      rwa [add_sub_cancel, v.map_sub d] at h₃
    by_contra h₃
    exact (max_lt (not_le.mp h₃) h₁).not_ge h₂
  have key (n : ℕ) (hn : n ≠ s) (hn' : v (G.coeff n) * c ^ n = v (G.coeff i) * c ^ i) : False := by
    have h₁ : v ((G - monomial s d).coeff n) * c ^ n < v d * c ^ s :=
      hcoeff n
    rw [coeff_sub, coeff_monomial_of_ne d hn, sub_zero] at h₁
    have h₂ : v d * c ^ s ≤ v (G.coeff s) * c ^ s :=
      mul_le_mul_of_nonneg_right hs (pow_nonneg hc.le s)
    linarith [hi s]
  rcases eq_or_ne i s with rfl | his
  · exact key j hij.symm hj
  · exact key i his rfl

end Polynomial

namespace IsNonarchimedeanLocalField

open HerbrandInvariant (isScalarTower_integerRing map_eq_prod_quotient mongeShift)

section AddValAbs

variable {T : Type*} [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] {x y E : T}
  {G Q : T[X]} {k : ℕ} {ι : Type*} (s : Finset ι) (u : ι → T)

lemma addValAbs_le_one : addValAbs T x ≤ 1 :=
  (addValAbs_le_of_dvd (one_dvd x)).trans_eq (addValAbs T).map_one

lemma isUnit_of_one_le_addValAbs (hx : 1 ≤ addValAbs T x) : IsUnit x :=
  not_not.mp fun h ↦ (addValAbs_lt_one h).not_ge hx

lemma residue_eq_zero_of_addValAbs_lt_one (hx : addValAbs T x < 1) : IsLocalRing.residue T x = 0 :=
  not_not.mp fun h ↦
    hx.ne (addValAbs_eq_one_of_isUnit ((IsLocalRing.residue_ne_zero_iff_isUnit x).mp h))

lemma addValAbs_eq_rpow (hx : x ≠ 0) : addValAbs T x = (2 : ℝ) ^ (-((addVal T x).toNat : ℝ)) := by
  rw [addValAbs_apply, addValAbsFun_of_ne_zero hx, inv_pow, ← Real.rpow_natCast,
    Real.rpow_neg zero_le_two]

lemma dvd_of_addValAbs_le (hy : y ≠ 0) (h : addValAbs T x ≤ addValAbs T y) : y ∣ x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact dvd_zero y
  rw [addValAbs_eq_rpow hx, addValAbs_eq_rpow hy, Real.rpow_le_rpow_left_iff one_lt_two,
    neg_le_neg_iff, Nat.cast_le] at h
  rw [← addVal_le_iff_dvd, ← ENat.natCast_toNat (mt addVal_eq_top_iff.mp hy),
    ← ENat.natCast_toNat (mt addVal_eq_top_iff.mp hx)]
  exact_mod_cast h

lemma dvd_of_addValAbs_lt (h : addValAbs T x < addValAbs T y) : y ∣ x := by
  refine dvd_of_addValAbs_le (fun hy ↦ ?_) h.le
  rw [hy, map_zero] at h
  exact h.not_ge ((addValAbs T).nonneg x)

lemma addValAbs_lt_of_not_dvd (hy : y ≠ 0) (h : ¬y ∣ x) : addValAbs T y < addValAbs T x :=
  not_le.mp fun h' ↦ h (dvd_of_addValAbs_le hy h')

lemma gaussNorm_addValAbs_one_of_monic {P : T[X]} (hP : P.Monic) :
    P.gaussNorm (addValAbs T) 1 = 1 := by
  refine le_antisymm ?_ ?_
  · rcases exists_eq_gaussNorm (addValAbs T) 1 P with ⟨i, hi⟩
    rw [hi, one_pow, mul_one]
    exact addValAbs_le_one
  · have h : addValAbs T (P.coeff P.natDegree) * 1 ^ P.natDegree ≤ P.gaussNorm (addValAbs T) 1 :=
      le_gaussNorm (addValAbs T) P zero_le_one P.natDegree
    rwa [coeff_natDegree, hP.leadingCoeff, map_one, one_pow, mul_one] at h

/-- **A product of linear polynomials with two dominant coefficients has a balanced factor**: over
a discrete valuation ring with the absolute value `|x| = 2 ^ (-v(x))`, if the product `G` of the
polynomials `u_c + y x` has two dominant coefficients `G_i`, `G_j`, `i ≠ j`, at the radius
`r > 0`, then `|u_c| = |y| r` for some `c`. Otherwise each factor is close to the monomial `u_c` or
`y x`, and so is their product to a monomial, at the radius `r`. -/
lemma exists_addValAbs_eq_mul_of_dominant {r : ℝ} (hr : 0 < r)
    (hG : ∏ c ∈ s, (C (u c) + C y * X) = G) {i j : ℕ} (hij : i ≠ j)
    (hi : ∀ n, addValAbs T (G.coeff n) * r ^ n ≤ addValAbs T (G.coeff i) * r ^ i)
    (hj : addValAbs T (G.coeff j) * r ^ j = addValAbs T (G.coeff i) * r ^ i) :
    ∃ c ∈ s, addValAbs T (u c) = addValAbs T y * r := by
  classical
  by_contra hne
  push Not at hne
  let d : ι → T := fun c ↦ if addValAbs T y * r < addValAbs T (u c) then u c else y
  let e : ι → ℕ := fun c ↦ if addValAbs T y * r < addValAbs T (u c) then 0 else 1
  have hF (c : ι) (hc : c ∈ s) : (C (u c) + C y * X - C (d c) * X ^ e c).gaussNorm (addValAbs T) r <
      (C (d c) * X ^ e c).gaussNorm (addValAbs T) r := by
    dsimp only [d, e]
    split_ifs with h
    · rw [pow_zero, mul_one, add_sub_cancel_left, C_mul_X_eq_monomial, gaussNorm_monomial,
        gaussNorm_C, pow_one]
      exact h
    · rw [pow_one, add_sub_cancel_right, gaussNorm_C, C_mul_X_eq_monomial, gaussNorm_monomial,
        pow_one]
      exact (not_lt.mp h).lt_of_ne (hne c hc)
  have hprod : ∏ c ∈ s, C (d c) * X ^ e c = C (∏ c ∈ s, d c) * X ^ ∑ c ∈ s, e c := by
    rw [prod_mul_distrib, ← map_prod, prod_pow_eq_pow_sum]
  have h : (∏ c ∈ s, (C (u c) + C y * X) - ∏ c ∈ s, C (d c) * X ^ e c).gaussNorm (addValAbs T) r <
      (∏ c ∈ s, C (d c) * X ^ e c).gaussNorm (addValAbs T) r :=
    gaussNorm_prod_sub_prod_lt hr isNonarchimedean_addValAbs s (fun c ↦ C (d c) * X ^ e c)
      (fun c ↦ C (u c) + C y * X) hF
  rw [hprod, hG] at h
  exact not_gaussNorm_sub_C_mul_X_pow_lt isNonarchimedean_addValAbs hr hij hi hj _ _ h

/-- **A product of linear polynomials is a constant times a polynomial with split reduction**:
over a discrete valuation ring, the product of the polynomials `u_c + y x`, `y ≠ 0`, is `E Q` for
some `E ≠ 0` and some `Q` whose reduction modulo the maximal ideal is nonzero and splits. At the
radius `1`, a factor with `y ∤ u_c` is close to the constant `u_c`, and the other factors are
`y (x + r_c)`; the product of the approximations is `E` times a monic polynomial, which `Q`
approaches. -/
lemma exists_eq_C_mul_splits (hy : y ≠ 0) : ∃ E Q, E ≠ 0 ∧ ∏ c ∈ s, (C (u c) + C y * X) = C E * Q ∧
    (Q.map (IsLocalRing.residue T)).Splits ∧ Q.map (IsLocalRing.residue T) ≠ 0 := by
  classical
  let d : ι → T := fun c ↦ if y ∣ u c then y else u c
  let N : ι → T[X] := fun c ↦ if h : y ∣ u c then X + C h.choose else 1
  have hN (c : ι) : (N c).Monic := by
    dsimp only [N]
    split_ifs
    · exact monic_X_add_C _
    · exact monic_one
  have hF (c : ι) (_ : c ∈ s) : (C (u c) + C y * X - C (d c) * N c).gaussNorm (addValAbs T) 1 <
      (C (d c) * N c).gaussNorm (addValAbs T) 1 := by
    rw [gaussNorm_mul isNonarchimedean_addValAbs one_pos, gaussNorm_C,
      gaussNorm_addValAbs_one_of_monic (hN c), mul_one]
    dsimp only [d, N]
    split_ifs with h
    · have h₀ : C (u c) + C y * X - C y * (X + C h.choose) = 0 := by
        rw [mul_add, ← map_mul, ← h.choose_spec]
        ring1
      rw [h₀, gaussNorm_zero]
      exact addValAbs_pos hy
    · rw [mul_one, add_sub_cancel_left, C_mul_X_eq_monomial, gaussNorm_monomial, one_pow, mul_one]
      exact addValAbs_lt_of_not_dvd hy h
  have hE : ∏ c ∈ s, d c ≠ 0 := by
    refine prod_ne_zero_iff.mpr fun c _ ↦ ?_
    dsimp only [d]
    split_ifs with h
    · exact hy
    · exact fun h₀ ↦ h (h₀ ▸ dvd_zero y)
  have hmonic : (∏ c ∈ s, N c).Monic :=
    monic_prod_of_monic _ _ fun c _ ↦ hN c
  have hlt : (∏ c ∈ s, (C (u c) + C y * X) - C (∏ c ∈ s, d c) * ∏ c ∈ s, N c).gaussNorm
      (addValAbs T) 1 < addValAbs T (∏ c ∈ s, d c) := by
    have h : (∏ c ∈ s, (C (u c) + C y * X) - ∏ c ∈ s, C (d c) * N c).gaussNorm (addValAbs T) 1 <
        (∏ c ∈ s, C (d c) * N c).gaussNorm (addValAbs T) 1 :=
      gaussNorm_prod_sub_prod_lt one_pos isNonarchimedean_addValAbs s (fun c ↦ C (d c) * N c)
        (fun c ↦ C (u c) + C y * X) hF
    rwa [prod_mul_distrib, ← map_prod, gaussNorm_mul isNonarchimedean_addValAbs one_pos,
      gaussNorm_C, gaussNorm_addValAbs_one_of_monic hmonic, mul_one] at h
  set E : T := ∏ c ∈ s, d c
  set N' : T[X] := ∏ c ∈ s, N c
  set G : T[X] := ∏ c ∈ s, (C (u c) + C y * X)
  have hcoeff (n : ℕ) : addValAbs T ((G - C E * N').coeff n) < addValAbs T E := by
    have h :
        addValAbs T ((G - C E * N').coeff n) * 1 ^ n ≤ (G - C E * N').gaussNorm (addValAbs T) 1 :=
      le_gaussNorm (addValAbs T) _ zero_le_one n
    rw [one_pow, mul_one] at h
    exact h.trans_lt hlt
  have hdvd : C E ∣ G := by
    refine (C_dvd_iff_dvd_coeff _ _).mpr fun n ↦ ?_
    have h₁ : E ∣ (C E * N').coeff n := by
      rw [coeff_C_mul]
      exact dvd_mul_right _ _
    have h₂ : E ∣ (G - C E * N').coeff n + (C E * N').coeff n :=
      dvd_add (dvd_of_addValAbs_lt (hcoeff n)) h₁
    rwa [← coeff_add, sub_add_cancel] at h₂
  rcases hdvd with ⟨Q, hQ⟩
  have hres : Q.map (IsLocalRing.residue T) = N'.map (IsLocalRing.residue T) := by
    ext n
    rw [coeff_map, coeff_map, ← sub_eq_zero, ← map_sub, ← coeff_sub]
    refine residue_eq_zero_of_addValAbs_lt_one ?_
    have h : addValAbs T ((G - C E * N').coeff n) < addValAbs T E :=
      hcoeff n
    rw [hQ, ← mul_sub, coeff_C_mul, map_mul] at h
    exact (mul_lt_iff_lt_one_right (addValAbs_pos hE)).mp h
  refine ⟨E, Q, hE, hQ, ?_, ?_⟩
  · rw [hres]
    simp only [N', Polynomial.map_prod]
    refine Splits.prod fun c _ ↦ ?_
    dsimp only [N]
    split_ifs
    · rw [Polynomial.map_add, map_X, map_C]
      exact Splits.X_add_C _
    · rw [Polynomial.map_one]
      exact Splits.one
  · rw [hres]
    exact (hmonic.map _).ne_zero

lemma isUnit_coeff_of_forall_le (hE : E ≠ 0) (hG : G = C E * Q)
    (hQ : Q.map (IsLocalRing.residue T) ≠ 0)
    (hk : ∀ n, addValAbs T (G.coeff n) ≤ addValAbs T (G.coeff k)) : IsUnit (Q.coeff k) := by
  have hj : ∃ j, (Q.map (IsLocalRing.residue T)).coeff j ≠ 0 := by
    by_contra h
    push Not at h
    exact hQ (Polynomial.ext fun n ↦ by rw [h n, coeff_zero])
  rcases hj with ⟨j, hj⟩
  rw [coeff_map] at hj
  have h₁ : addValAbs T (G.coeff j) ≤ addValAbs T (G.coeff k) :=
    hk j
  rw [hG, coeff_C_mul, coeff_C_mul, map_mul, map_mul,
    addValAbs_eq_one_of_isUnit ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp hj), mul_one] at h₁
  exact isUnit_of_one_le_addValAbs ((le_mul_iff_one_le_right (addValAbs_pos hE)).mp h₁)

lemma residue_coeff_eq_zero_of_lt (hG : G = C E * Q) {n : ℕ} (hk : IsUnit (Q.coeff k))
    (hn : addValAbs T (G.coeff n) < addValAbs T (G.coeff k)) :
    IsLocalRing.residue T (Q.coeff n) = 0 := by
  rw [hG, coeff_C_mul, coeff_C_mul, map_mul, map_mul, addValAbs_eq_one_of_isUnit hk, mul_one] at hn
  have hE : 0 < addValAbs T E :=
    (mul_nonneg ((addValAbs T).nonneg _) ((addValAbs T).nonneg _)).trans_lt hn
  exact residue_eq_zero_of_addValAbs_lt_one ((mul_lt_iff_lt_one_right hE).mp hn)

end AddValAbs

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

variable [IsDomain R] in
lemma coeff_mul_mul_eq {G Q : R[X]} {E a γ w c₀ c : R} {b : ℕ → R} {k m h i : ℕ} (hE : E ≠ 0)
    (ha : a ≠ 0) (hb : b k ≠ 0) (hG : G = C E * Q) (hkey : ∀ n, G.coeff n * a ^ n = γ ^ n * b n)
    (hw : γ ^ m = a ^ (m + h) * w) (hc : c₀ * a ^ (i * h) * b (i * m + k) = c * b k) :
    Q.coeff (i * m + k) * c₀ = Q.coeff k * w ^ i * c := by
  have h₁ : G.coeff (i * m + k) * a ^ (i * m + k) = γ ^ (i * m + k) * b (i * m + k) :=
    hkey (i * m + k)
  have h₂ : G.coeff k * a ^ k = γ ^ k * b k :=
    hkey k
  rw [hG, coeff_C_mul] at h₁ h₂
  have hw' : γ ^ (i * m) = a ^ (i * (m + h)) * w ^ i := by
    rw [mul_comm i m, pow_mul, hw, mul_pow, ← pow_mul, mul_comm (m + h)]
  refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hE (pow_ne_zero (i * m + k) ha)) hb) ?_
  linear_combination (b k * c₀) * h₁ - (a ^ (i * m) * b k * w ^ i * c) * h₂ +
    (a ^ (i * m) * w ^ i * γ ^ k * b k) * hc + (γ ^ k * b k * c₀ * b (i * m + k)) * hw'

variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] in
lemma coeff_map_comp_mul_pow (f : R[X]) (π : S) (z : T) (n : ℕ) :
    ((f.map (algebraMap R T)).comp (C (algebraMap S T π) + C z * X)).coeff n *
      algebraMap S T π ^ n = z ^ n * algebraMap S T ((mongeShift f π 0).coeff n) := by
  have h₁ : C (algebraMap S T π) + C z * X = (X + C (algebraMap S T π)).comp (C z * X) := by
    rw [add_comp, X_comp, C_comp, add_comm]
  have h₂ : (mongeShift f π 0).map (algebraMap S T) = ((f.map (algebraMap R T)).comp
      (X + C (algebraMap S T π))).comp (C (algebraMap S T π) * X) := by
    rw [mongeShift, Polynomial.map_comp, Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
      comp_assoc, add_comp, X_comp, C_comp, Polynomial.map_add, Polynomial.map_mul, map_C, map_C,
      map_X, zero_add, pow_one, add_comm]
  rw [h₁, ← comp_assoc, comp_C_mul_X_coeff, ← coeff_map, h₂, comp_C_mul_X_coeff]
  ring1

open minpoly in
lemma splits_map_of_dvd_expand {k F : Type*} [Field k] [Field F] [Algebra k F] [Normal k F]
    {A : k[X]} (hA : A ≠ 0) {B : F[X]} (hB : B.Splits) (hB₀ : B ≠ 0) {w : F} (hw : w ≠ 0) {m : ℕ}
    (hm : 0 < m) (hdvd : expand F m ((A.map (algebraMap k F)).comp (C w * X)) ∣ B) :
    (A.map (algebraMap k F)).Splits := by
  classical
  have hq (q : k[X]) (hq : q ∈ normalizedFactors A) : (q.map (algebraMap k F)).Splits := by
    have hirr : Irreducible q :=
      irreducible_of_normalized_factor q hq
    have h₁ : expand F m ((q.map (algebraMap k F)).comp (C w * X)) ∣ B := by
      rcases dvd_of_mem_normalizedFactors hq with ⟨t, ht⟩
      refine (Dvd.intro (expand F m ((t.map (algebraMap k F)).comp (C w * X))) ?_).trans hdvd
      rw [← map_mul, ← mul_comp, ← Polynomial.map_mul, ← ht]
    have h₂ : (expand F m ((q.map (algebraMap k F)).comp (C w * X))).natDegree ≠ 0 := by
      rw [natDegree_expand, natDegree_comp, natDegree_map, natDegree_C_mul_X w hw, mul_one]
      exact mul_ne_zero hirr.natDegree_pos.ne' hm.ne'
    rcases (hB.of_dvd hB₀ h₁).exists_eval_eq_zero
      (fun h ↦ h₂ (natDegree_eq_of_degree_eq_some h)) with ⟨z, hz⟩
    rw [expand_eval, eval_comp, eval_mul, eval_C, eval_X, eval_map_algebraMap] at hz
    rw [Irreducible.eq_minpoly hirr hz, Polynomial.map_mul, map_C]
    exact (Normal.splits inferInstance (w * z ^ m)).C_mul _
  rcases prod_normalizedFactors hA with ⟨u, hu⟩
  rw [← hu, Polynomial.map_mul, Polynomial.map_multiset_prod]
  refine (Splits.multisetProd fun f hf ↦ ?_).mul ?_
  · rcases Multiset.mem_map.mp hf with ⟨q, hq', rfl⟩
    exact hq q hq'
  · exact (u.isUnit.map (mapRingHom (algebraMap k F))).splits

variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Field M] [ValuativeRel M]
  [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra L M] [ValuativeExtension L M]
  [Algebra K M] [ValuativeExtension K M] [Module.Finite K M] [IsScalarTower K L M] {α : 𝒪[L]}
  {kl : ℕ × ℕ} {ρ : L[X]} {N n : ℕ} {b : ℕ → 𝒪[L]}

lemma residualSlope_mul_snd (hkl : kl ∈ residualSegments ρ) :
    (residualSlope ρ kl.1 kl.2 : ℝ) * kl.2 = coeffVal ρ kl.1 - coeffVal ρ (kl.1 + kl.2) := by
  rw [residualSlope]
  push_cast
  exact div_mul_cancel₀ _ (Nat.cast_pos.mpr (pos_of_mem_residualSegments hkl)).ne'

lemma coeffVal_sub_mul_lt (hkl : kl ∈ residualSegments ρ) (hn : ρ.coeff n ≠ 0)
    (hout : n < kl.1 ∨ kl.1 + kl.2 < n) :
    (coeffVal ρ kl.1 : ℚ) - residualSlope ρ kl.1 kl.2 * ((n : ℚ) - kl.1) < coeffVal ρ n := by
  rcases exists_of_mem_residualSegments hkl with ⟨s, hs, hK, hU⟩
  have hl₀ : 0 < kl.2 :=
    pos_of_mem_residualSegments hkl
  have hl : (0 : ℝ) < kl.2 :=
    Nat.cast_pos.mpr hl₀
  have hle : coeffEnvelope ρ ≤ coeffHeight ρ :=
    lowerConvexEnvelope_le (isAdmissible_of_finite finite_coeffHeight_ne_top)
  have hfin (i : ℕ) (hi : ρ.coeff i ≠ 0) : coeffEnvelope ρ i ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (hle i)
    rw [coeffHeight_of_coeff_ne_zero hi]
    exact WithTop.coe_ne_top
  have hval : (coeffEnvelope ρ n).untop₀ ≤ coeffVal ρ n := by
    have h₁ : coeffEnvelope ρ n ≤ coeffHeight ρ n :=
      hle n
    rwa [coeffHeight_of_coeff_ne_zero hn, ← WithTop.coe_untop₀_of_ne_top (hfin n hn),
      WithTop.coe_le_coe] at h₁
  have hk : (coeffEnvelope ρ kl.1).untop₀ = coeffVal ρ kl.1 := by
    rw [coeffEnvelope_fst_of_mem_residualSegments hkl, untop₀_coeffHeight]
  have hk' : (coeffEnvelope ρ (kl.1 + kl.2)).untop₀ = coeffVal ρ (kl.1 + kl.2) := by
    rw [coeffEnvelope_add_of_mem_residualSegments hkl, untop₀_coeffHeight]
  have hslope :
      (residualSlope ρ kl.1 kl.2 : ℝ) * kl.2 = coeffVal ρ kl.1 - coeffVal ρ (kl.1 + kl.2) :=
    residualSlope_mul_snd hkl
  have hgoal : (coeffVal ρ kl.1 : ℝ) - (residualSlope ρ kl.1 kl.2 : ℝ) * ((n : ℝ) - kl.1) <
      coeffVal ρ n := by
    rcases hout with hout | hout
    · rcases exists_lt_of_sInf_slopeIndices isConvexSeq_coeffEnvelope hs with ⟨σ, hσ⟩
      rw [hK] at hσ
      have h₁ : (coeffEnvelope ρ kl.1).untop₀ + σ * (((kl.1 + kl.2 : ℕ) : ℝ) - kl.1) <
          (coeffEnvelope ρ (kl.1 + kl.2)).untop₀ :=
        hσ _ (by omega) (hfin _ (coeff_add_ne_zero_of_mem_residualSegments hkl))
      have h₂ : (coeffEnvelope ρ kl.1).untop₀ + σ * ((n : ℝ) - kl.1) < (coeffEnvelope ρ n).untop₀ :=
        hσ n (by omega) (hfin n hn)
      rw [hk, hk', Nat.cast_add, add_sub_cancel_left] at h₁
      rw [hk] at h₂
      have h₃ : (n : ℝ) < kl.1 :=
        Nat.cast_lt.mpr hout
      have h₅ : (σ + residualSlope ρ kl.1 kl.2) * kl.2 < 0 := by
        rw [add_mul]
        linarith
      have h₆ : 0 < (σ + residualSlope ρ kl.1 kl.2) * ((n : ℝ) - kl.1) :=
        mul_pos_of_neg_of_neg (lt_of_mul_lt_mul_right (h₅.trans_eq (zero_mul _).symm) hl.le)
          (sub_neg.mpr h₃)
      rw [add_mul] at h₆
      linarith
    · rcases exists_lt_of_sSup_slopeIndices_add_one isConvexSeq_coeffEnvelope
        finite_coeffEnvelope_ne_top hs with ⟨σ, hσ⟩
      rw [hU] at hσ
      have h₁ : (coeffEnvelope ρ (kl.1 + kl.2)).untop₀ +
          σ * ((kl.1 : ℝ) - ((kl.1 + kl.2 : ℕ) : ℝ)) < (coeffEnvelope ρ kl.1).untop₀ :=
        hσ _ (by omega) (hfin _ (coeff_fst_ne_zero_of_mem_residualSegments hkl))
      have h₂ : (coeffEnvelope ρ (kl.1 + kl.2)).untop₀ +
          σ * ((n : ℝ) - ((kl.1 + kl.2 : ℕ) : ℝ)) < (coeffEnvelope ρ n).untop₀ :=
        hσ n (by omega) (hfin n hn)
      rw [hk, hk', Nat.cast_add, sub_add_cancel_left, mul_neg] at h₁
      rw [hk'] at h₂
      have h₃ : ((kl.1 + kl.2 : ℕ) : ℝ) < n :=
        Nat.cast_lt.mpr hout
      have h₅ : 0 < (σ + residualSlope ρ kl.1 kl.2) * kl.2 := by
        rw [add_mul]
        linarith
      have h₆ : 0 < (σ + residualSlope ρ kl.1 kl.2) * ((n : ℝ) - ((kl.1 + kl.2 : ℕ) : ℝ)) :=
        mul_pos (lt_of_mul_lt_mul_right ((zero_mul _).trans_lt h₅) hl.le) (sub_pos.mpr h₃)
      have h₇ : (residualSlope ρ kl.1 kl.2 : ℝ) * ((n : ℝ) - kl.1) =
          (residualSlope ρ kl.1 kl.2 : ℝ) * ((n : ℝ) - ((kl.1 + kl.2 : ℕ) : ℝ)) +
            (residualSlope ρ kl.1 kl.2 : ℝ) * kl.2 := by
        push_cast
        ring1
      rw [add_mul] at h₆
      linarith
  exact_mod_cast hgoal

lemma coeffVal_sub_mul_lt_of_not_dvd (hkl : kl ∈ residualSegments ρ) (hn : ρ.coeff n ≠ 0)
    (hdvd : ¬((residualSlope ρ kl.1 kl.2).den : ℤ) ∣ (n : ℤ) - kl.1) :
    (coeffVal ρ kl.1 : ℚ) - residualSlope ρ kl.1 kl.2 * ((n : ℚ) - kl.1) < coeffVal ρ n := by
  refine (coeffVal_sub_mul_le hkl hn).lt_of_ne fun heq ↦ hdvd ?_
  have h₁ : (residualSlope ρ kl.1 kl.2).num * ((n : ℤ) - kl.1) =
      (residualSlope ρ kl.1 kl.2).den * (coeffVal ρ kl.1 - coeffVal ρ n) := by
    have h₂ : ((residualSlope ρ kl.1 kl.2).num : ℚ) =
        residualSlope ρ kl.1 kl.2 * (residualSlope ρ kl.1 kl.2).den :=
      (Rat.mul_den_eq_num _).symm
    have h₃ : ((residualSlope ρ kl.1 kl.2).num : ℚ) * ((n : ℚ) - kl.1) =
        (residualSlope ρ kl.1 kl.2).den * ((coeffVal ρ kl.1 : ℚ) - coeffVal ρ n) := by
      rw [h₂]
      linear_combination (-((residualSlope ρ kl.1 kl.2).den : ℚ)) * heq
    exact_mod_cast h₃
  have hcop : IsCoprime ((residualSlope ρ kl.1 kl.2).den : ℤ) (residualSlope ρ kl.1 kl.2).num := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact Rat.reduced _
  exact hcop.dvd_of_dvd_mul_left ⟨_, h₁⟩

/-- **The points off a segment lie strictly above its line**: for a segment `(k, l)` of slope
`h / m` of the ramification polygon of `ρ`, every point `(-n, v(ρ_n))` with `ρ_n ≠ 0` other than
the points `(-(i m + k), v(ρ_{i m + k}))`, `0 ≤ i ≤ l / m`, lies strictly above the line of the
segment: `v(ρ_k) - (h / m) (n - k) < v(ρ_n)`. Outside the segment because it is an edge of the
lower convex hull, and inside it because `v(ρ_n)` is an integer. -/
lemma coeffVal_sub_mul_lt_of_ne (hkl : kl ∈ residualSegments ρ) (hn : ρ.coeff n ≠ 0)
    (hne : ∀ i ≤ kl.2 / (residualSlope ρ kl.1 kl.2).den,
      n ≠ i * (residualSlope ρ kl.1 kl.2).den + kl.1) :
    (coeffVal ρ kl.1 : ℚ) - residualSlope ρ kl.1 kl.2 * ((n : ℚ) - kl.1) < coeffVal ρ n := by
  by_cases hout : n < kl.1 ∨ kl.1 + kl.2 < n
  · exact coeffVal_sub_mul_lt hkl hn hout
  refine coeffVal_sub_mul_lt_of_not_dvd hkl hn fun hd ↦ ?_
  push Not at hout
  have hd' : (residualSlope ρ kl.1 kl.2).den ∣ n - kl.1 := by
    rw [← Int.natCast_dvd_natCast, Nat.cast_sub hout.1]
    exact hd
  exact hne ((n - kl.1) / (residualSlope ρ kl.1 kl.2).den) (Nat.div_le_div_right (by omega))
    (by rw [Nat.div_mul_cancel hd']; omega)

lemma residualSlope_nonneg (hρ : ρ.Monic) (hint : ∀ i, ρ.coeff i ∈ 𝒪[L])
    (hkl : kl ∈ residualSegments ρ) : 0 ≤ residualSlope ρ kl.1 kl.2 := by
  have h₁ : (coeffVal ρ kl.1 : ℚ) - residualSlope ρ kl.1 kl.2 * ((ρ.natDegree : ℚ) - kl.1) ≤
      coeffVal ρ ρ.natDegree :=
    coeffVal_sub_mul_le hkl (ne_of_eq_of_ne hρ.coeff_natDegree one_ne_zero)
  have hn : coeffVal ρ ρ.natDegree = 0 := by
    rw [coeffVal, coeff_natDegree, hρ.leadingCoeff, ← Subring.coe_one 𝒪[L],
      addValuation_coe (IsDiscreteValuationRing.addVal_one), Nat.cast_zero]
    rfl
  have hk : (0 : ℚ) ≤ coeffVal ρ kl.1 := by
    have h₂ : 0 ≤ addValuation L (ρ.coeff kl.1) :=
      (mem_integer_iff_zero_le_addValuation (coeff_fst_ne_zero_of_mem_residualSegments hkl)).mp
        (hint kl.1)
    rw [addValuation_coeff (coeff_fst_ne_zero_of_mem_residualSegments hkl)] at h₂
    exact_mod_cast h₂
  have hdeg : kl.1 + kl.2 ≤ ρ.natDegree :=
    le_natDegree_of_ne_zero (coeff_add_ne_zero_of_mem_residualSegments hkl)
  have hl : 0 < kl.2 :=
    pos_of_mem_residualSegments hkl
  have h₃ : (0 : ℚ) < (ρ.natDegree : ℚ) - kl.1 := by
    have h₄ : kl.1 < ρ.natDegree := by
      omega
    exact sub_pos.mpr (by exact_mod_cast h₄)
  rw [hn, Int.cast_zero] at h₁
  by_contra h₄
  have h₅ : residualSlope ρ kl.1 kl.2 * ((ρ.natDegree : ℚ) - kl.1) < 0 :=
    mul_neg_of_neg_of_pos (not_le.mp h₄) h₃
  linarith

variable (M) in
lemma addValAbs_algebraMap_mul_rpow_pow (hα : Irreducible α) {z : 𝒪[L]}
    (hz : (z : L) = (α : L) ^ N * ρ.coeff n) (hn : ρ.coeff n ≠ 0) (t : ℝ) :
    addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] z) * (2 ^ ((ramificationIndex L M : ℝ) * t)) ^ n =
      2 ^ (-((ramificationIndex L M : ℝ) * ((N : ℝ) + coeffVal ρ n - t * n))) := by
  have hα₀ : (α : L) ≠ 0 :=
    fun h ↦ hα.ne_zero (Subtype.ext h)
  have hz₀ : z ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (pow_ne_zero N hα₀) hn (by rw [← hz, ZeroMemClass.coe_zero])
  have hv : ((addVal 𝒪[L] z).toNat : ℝ) = N + coeffVal ρ n := by
    have h₁ : addValuation L (z : L) = (((addVal 𝒪[L] z).toNat : ℤ) : WithTop ℤ) :=
      addValuation_coe_eq_toNat hz₀
    rw [hz, addValuation_mul (pow_ne_zero N hα₀) hn, ← zpow_natCast, addValuation_zpow hα,
      addValuation_coeff hn, ← WithTop.coe_add] at h₁
    exact_mod_cast (WithTop.coe_injective h₁).symm
  rw [addValAbs_algebraMap_mul_pow M hz₀ t n, hv]
  congr 1
  ring1

variable (M n) in
lemma addValAbs_algebraMap_mul_pow_le (hα : Irreducible α)
    (hb : ∀ n, (b n : L) = (α : L) ^ N * ρ.coeff n) (hkl : kl ∈ residualSegments ρ) :
    addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] (b n)) *
      (2 ^ ((ramificationIndex L M : ℝ) * -(residualSlope ρ kl.1 kl.2 : ℝ))) ^ n ≤
        addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] (b kl.1)) *
          (2 ^ ((ramificationIndex L M : ℝ) * -(residualSlope ρ kl.1 kl.2 : ℝ))) ^ kl.1 := by
  have he : (0 : ℝ) < ramificationIndex L M := by
    exact_mod_cast ramificationIndex_pos
  have hk : ρ.coeff kl.1 ≠ 0 :=
    coeff_fst_ne_zero_of_mem_residualSegments hkl
  rcases eq_or_ne (ρ.coeff n) 0 with hn | hn
  · have h₀ : b n = 0 :=
      Subtype.ext (by rw [hb, hn, mul_zero, ZeroMemClass.coe_zero])
    rw [h₀, map_zero, map_zero, zero_mul]
    exact mul_nonneg ((addValAbs _).nonneg _) (pow_nonneg (Real.rpow_pos_of_pos two_pos _).le _)
  rw [addValAbs_algebraMap_mul_rpow_pow M hα (hb n) hn,
    addValAbs_algebraMap_mul_rpow_pow M hα (hb kl.1) hk, Real.rpow_le_rpow_left_iff one_lt_two,
    neg_le_neg_iff]
  have h₁ : (coeffVal ρ kl.1 : ℝ) - (residualSlope ρ kl.1 kl.2 : ℝ) * ((n : ℝ) - kl.1) ≤
      coeffVal ρ n := by
    exact_mod_cast coeffVal_sub_mul_le hkl hn
  refine mul_le_mul_of_nonneg_left ?_ he.le
  linarith [mul_sub (residualSlope ρ kl.1 kl.2 : ℝ) n kl.1,
    neg_mul (residualSlope ρ kl.1 kl.2 : ℝ) n, neg_mul (residualSlope ρ kl.1 kl.2 : ℝ) kl.1]

variable (M) in
lemma addValAbs_algebraMap_mul_pow_add_eq (hα : Irreducible α)
    (hb : ∀ n, (b n : L) = (α : L) ^ N * ρ.coeff n) (hkl : kl ∈ residualSegments ρ) :
    addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] (b (kl.1 + kl.2))) *
      (2 ^ ((ramificationIndex L M : ℝ) * -(residualSlope ρ kl.1 kl.2 : ℝ))) ^ (kl.1 + kl.2) =
        addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] (b kl.1)) *
          (2 ^ ((ramificationIndex L M : ℝ) * -(residualSlope ρ kl.1 kl.2 : ℝ))) ^ kl.1 := by
  have hk : ρ.coeff kl.1 ≠ 0 :=
    coeff_fst_ne_zero_of_mem_residualSegments hkl
  rw [addValAbs_algebraMap_mul_rpow_pow M hα (hb _) (coeff_add_ne_zero_of_mem_residualSegments hkl),
    addValAbs_algebraMap_mul_rpow_pow M hα (hb kl.1) hk]
  congr 1
  push_cast
  linear_combination (-(ramificationIndex L M : ℝ)) * residualSlope_mul_snd hkl

variable (M) in
lemma addValAbs_algebraMap_mul_pow_lt (hα : Irreducible α)
    (hb : ∀ n, (b n : L) = (α : L) ^ N * ρ.coeff n) (hkl : kl ∈ residualSegments ρ)
    (hne : ∀ i ≤ kl.2 / (residualSlope ρ kl.1 kl.2).den,
      n ≠ i * (residualSlope ρ kl.1 kl.2).den + kl.1) :
    addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] (b n)) *
      (2 ^ ((ramificationIndex L M : ℝ) * -(residualSlope ρ kl.1 kl.2 : ℝ))) ^ n <
        addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] (b kl.1)) *
          (2 ^ ((ramificationIndex L M : ℝ) * -(residualSlope ρ kl.1 kl.2 : ℝ))) ^ kl.1 := by
  have he : (0 : ℝ) < ramificationIndex L M := by
    exact_mod_cast ramificationIndex_pos
  have hk : ρ.coeff kl.1 ≠ 0 :=
    coeff_fst_ne_zero_of_mem_residualSegments hkl
  rcases eq_or_ne (ρ.coeff n) 0 with hn | hn
  · have h₀ : b n = 0 :=
      Subtype.ext (by rw [hb, hn, mul_zero, ZeroMemClass.coe_zero])
    have hbk : b kl.1 ≠ 0 := fun h ↦ mul_ne_zero (pow_ne_zero N fun h' ↦ hα.ne_zero
      (Subtype.ext h')) hk (by rw [← hb, h, ZeroMemClass.coe_zero])
    rw [h₀, map_zero, map_zero, zero_mul]
    exact mul_pos (addValAbs_pos ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr
      hbk)) (pow_pos (Real.rpow_pos_of_pos two_pos _) _)
  rw [addValAbs_algebraMap_mul_rpow_pow M hα (hb n) hn,
    addValAbs_algebraMap_mul_rpow_pow M hα (hb kl.1) hk, Real.rpow_lt_rpow_left_iff one_lt_two,
    neg_lt_neg_iff]
  have h₁ : (coeffVal ρ kl.1 : ℝ) - (residualSlope ρ kl.1 kl.2 : ℝ) * ((n : ℝ) - kl.1) <
      coeffVal ρ n := by
    exact_mod_cast coeffVal_sub_mul_lt_of_ne hkl hn hne
  refine mul_lt_mul_of_pos_left ?_ he
  linarith [mul_sub (residualSlope ρ kl.1 kl.2 : ℝ) n kl.1,
    neg_mul (residualSlope ρ kl.1 kl.2 : ℝ) n, neg_mul (residualSlope ρ kl.1 kl.2 : ℝ) kl.1]

variable (M) in
lemma exists_pow_den_eq_mul (hα : Irreducible α) {q : ℚ} (hq : 0 ≤ q) {γ : 𝒪[M]}
    (hγ : addValAbs 𝒪[M] γ =
      addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] α) * 2 ^ ((ramificationIndex L M : ℝ) * -(q : ℝ))) :
    ∃ w : 𝒪[M]ˣ, γ ^ q.den = algebraMap 𝒪[L] 𝒪[M] α ^ (q.den + q.num.toNat) * w := by
  have ha : addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] α) = 2 ^ (-(ramificationIndex L M : ℝ)) := by
    rw [addValAbs_eq_rpow ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr
      hα.ne_zero), addVal_algebraMap, addVal_uniformizer hα, nsmul_eq_mul, mul_one,
      ENat.toNat_natCast]
  have hnum : (q.num.toNat : ℝ) = (q : ℝ) * q.den := by
    have h₁ : ((q.num.toNat : ℤ) : ℚ) = q * q.den := by
      rw [Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq), Rat.mul_den_eq_num]
    exact_mod_cast h₁
  have hR : ((2 : ℝ) ^ ((ramificationIndex L M : ℝ) * -(q : ℝ))) ^ q.den =
      ((2 : ℝ) ^ (-(ramificationIndex L M : ℝ))) ^ q.num.toNat := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two,
      ← Real.rpow_mul zero_le_two, hnum]
    congr 1
    ring1
  have habs : addValAbs 𝒪[M] (γ ^ q.den) =
      addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] α ^ (q.den + q.num.toNat)) := by
    rw [map_pow, map_pow, hγ, ha, mul_pow, hR, ← pow_add]
  have hne : algebraMap 𝒪[L] 𝒪[M] α ^ (q.den + q.num.toNat) ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hα.ne_zero)
  have hγ₀ : γ ^ q.den ≠ 0 := by
    intro h
    rw [h, map_zero] at habs
    exact (addValAbs_pos hne).ne habs
  rcases associated_of_dvd_dvd (dvd_of_addValAbs_le hne habs.le)
    (dvd_of_addValAbs_le hγ₀ habs.ge) with ⟨w, hw⟩
  exact ⟨w, hw.symm⟩

variable [Module.Finite L M]

variable [IsGalois K M] [Fintype ((M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range)] in
lemma map_minpoly_comp_eq_prod (hKL : IsTotallyRamified K L) (hα : Irreducible α) (z : 𝒪[M]) :
    ((minpoly 𝒪[K] α).map (algebraMap 𝒪[K] 𝒪[M])).comp (C (algebraMap 𝒪[L] 𝒪[M] α) + C z * X) =
      ∏ c : (M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range,
        (C (algebraMap 𝒪[L] 𝒪[M] α - c.out • algebraMap 𝒪[L] 𝒪[M] α) + C z * X) := by
  have hfin : Module.Finite K L :=
    finite_of_valuativeExtension K L
  rw [map_eq_prod_quotient (M := M) (hKL.adjoin_eq_top_of_irreducible hα)
    (minpoly.monic (IsIntegral.of_finite 𝒪[K] α)) (natDegree_minpoly_of_isTotallyRamified hKL hα)
    (minpoly.aeval 𝒪[K] α), Polynomial.prod_comp]
  refine prod_congr rfl fun c _ ↦ ?_
  rw [sub_comp, X_comp, C_comp, map_sub]
  ring1

variable (M) [IsGalois K M] in
/-- **The ramification polynomial has a root of the valuation of each segment** (the root–slope
step of Ore's theorem): for a totally ramified extension `L / K` of nonarchimedean local fields, a
uniformiser `α` of `L`, a finite Galois extension `M / K` containing `L` and a segment of slope
`h / m` of the ramification polygon, some `σ ∈ Gal(M / K)` has `|α - σ α| = |α| c`, for
`|x| = 2 ^ (-v_M(x))` and `c = 2 ^ (-e(M / L) h / m)`: the root `σ α / α - 1` of `ρ` has valuation
`h / m`. -/
lemma exists_addValAbs_sub_smul_eq (hKL : IsTotallyRamified K L) (hα : Irreducible α)
    (hkl : kl ∈ residualSegments (ramificationPolynomial (minpoly K (α : L)) (α : L))) :
    ∃ σ : M ≃ₐ[K] M, addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] α - σ • algebraMap 𝒪[L] 𝒪[M] α) =
      addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] α) * 2 ^ ((ramificationIndex L M : ℝ) *
        -(residualSlope (ramificationPolynomial (minpoly K (α : L)) (α : L)) kl.1 kl.2 : ℝ)) := by
  classical
  have hT : IsScalarTower 𝒪[K] 𝒪[L] 𝒪[M] :=
    isScalarTower_integerRing K L M
  have ha : algebraMap 𝒪[L] 𝒪[M] α ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hα.ne_zero
  have hcoeff (n : ℕ) : (((minpoly 𝒪[K] α).map (algebraMap 𝒪[K] 𝒪[M])).comp
      (C (algebraMap 𝒪[L] 𝒪[M] α) + C (algebraMap 𝒪[L] 𝒪[M] α) * X)).coeff n =
        algebraMap 𝒪[L] 𝒪[M] ((mongeShift (minpoly 𝒪[K] α) α 0).coeff n) :=
    mul_right_cancel₀ (pow_ne_zero n ha)
      ((coeff_map_comp_mul_pow _ _ _ n).trans (mul_comm _ _))
  rcases exists_addValAbs_eq_mul_of_dominant univ
    (fun c : (M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range ↦
      algebraMap 𝒪[L] 𝒪[M] α - c.out • algebraMap 𝒪[L] 𝒪[M] α)
    (r := 2 ^ ((ramificationIndex L M : ℝ) *
      -(residualSlope (ramificationPolynomial (minpoly K (α : L)) (α : L)) kl.1 kl.2 : ℝ)))
    (Real.rpow_pos_of_pos two_pos _) (map_minpoly_comp_eq_prod hKL hα _).symm
    (i := kl.1) (j := kl.1 + kl.2) (Nat.lt_add_of_pos_right (pos_of_mem_residualSegments hkl)).ne
    (fun n ↦ by
      rw [hcoeff, hcoeff]
      exact addValAbs_algebraMap_mul_pow_le M n hα (coe_coeff_mongeShift_minpoly hα) hkl)
    (by
      rw [hcoeff, hcoeff]
      exact addValAbs_algebraMap_mul_pow_add_eq M hα (coe_coeff_mongeShift_minpoly hα) hkl) with
    ⟨c, -, hc⟩
  exact ⟨c.out, hc⟩

variable (M) [IsGalois K M] in
open IsLocalRing in
/-- **Ore's theorem: the residual polynomials split over the residue field of a Galois extension**
(LMFDB `lf.associated_inertia`): for a totally ramified extension `L / K` of nonarchimedean local
fields, a uniformiser `α` of `L` with ramification polynomial `ρ`, a finite Galois extension `M / K`
containing `L` and a segment `S` of the ramification polygon, the residual polynomial `A_S` of `S`
splits over the residue field of `M`. -/
lemma splits_map_residualPolynomial (hKL : IsTotallyRamified K L) (hα : Irreducible α)
    (hkl : kl ∈ residualSegments (ramificationPolynomial (minpoly K (α : L)) (α : L))) :
    ((residualPolynomial (ramificationPolynomial (minpoly K (α : L)) (α : L)) (α : L) kl.1 kl.2).map
      (algebraMap 𝓀[L] 𝓀[M])).Splits := by
  classical
  have hfin : Module.Finite K L :=
    finite_of_valuativeExtension K L
  have hT : IsScalarTower 𝒪[K] 𝒪[L] 𝒪[M] :=
    isScalarTower_integerRing K L M
  set ρ : L[X] := ramificationPolynomial (minpoly K (α : L)) (α : L)
  set q : ℚ := residualSlope ρ kl.1 kl.2
  set a : 𝒪[M] := algebraMap 𝒪[L] 𝒪[M] α
  set P : 𝒪[L][X] := mongeShift (minpoly 𝒪[K] α) α 0
  have hι : Function.Injective (algebraMap 𝒪[L] 𝒪[M]) :=
    FaithfulSMul.algebraMap_injective _ _
  have ha : a ≠ 0 :=
    (map_ne_zero_iff _ hι).mpr hα.ne_zero
  have hα₀ : (α : L) ≠ 0 :=
    fun h ↦ hα.ne_zero (Subtype.ext h)
  have hb (n : ℕ) : ((P.coeff n : 𝒪[L]) : L) = (α : L) ^ (minpoly 𝒪[K] α).natDegree * ρ.coeff n :=
    coe_coeff_mongeShift_minpoly hα n
  have hk : ρ.coeff kl.1 ≠ 0 :=
    coeff_fst_ne_zero_of_mem_residualSegments hkl
  have hPk : algebraMap 𝒪[L] 𝒪[M] (P.coeff kl.1) ≠ 0 := by
    refine (map_ne_zero_iff _ hι).mpr fun h ↦
      mul_ne_zero (pow_ne_zero (minpoly 𝒪[K] α).natDegree hα₀) hk ?_
    rw [← hb, h, ZeroMemClass.coe_zero]
  have hq₀ : 0 ≤ q :=
    residualSlope_nonneg (monic_ramificationPolynomial_minpoly K hα)
      (mem_integer_coeff_ramificationPolynomial hKL hα) hkl
  have hm : 0 < q.den :=
    q.den_pos
  rcases exists_addValAbs_sub_smul_eq M hKL hα hkl with ⟨σ, hσ⟩
  have hr : (0 : ℝ) < 2 ^ ((ramificationIndex L M : ℝ) * -(q : ℝ)) :=
    Real.rpow_pos_of_pos two_pos _
  have hγ : a - σ • a ≠ 0 := by
    intro h
    rw [h, map_zero] at hσ
    exact (mul_pos (addValAbs_pos ha) hr).ne' hσ.symm
  rcases exists_pow_den_eq_mul M hα hq₀ hσ with ⟨w, hw⟩
  rcases exists_eq_C_mul_splits univ
    (fun c : (M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range ↦ a - c.out • a) hγ with
    ⟨E, Q, hE, hEQ, hsplit, hQ₀⟩
  have hG :
      ((minpoly 𝒪[K] α).map (algebraMap 𝒪[K] 𝒪[M])).comp (C a + C (a - σ • a) * X) = C E * Q :=
    (map_minpoly_comp_eq_prod hKL hα _).trans hEQ
  have hkey (n : ℕ) : (((minpoly 𝒪[K] α).map (algebraMap 𝒪[K] 𝒪[M])).comp
      (C a + C (a - σ • a) * X)).coeff n * a ^ n =
        (a - σ • a) ^ n * algebraMap 𝒪[L] 𝒪[M] (P.coeff n) :=
    coeff_map_comp_mul_pow _ _ _ n
  have habs (n : ℕ) : addValAbs 𝒪[M] ((((minpoly 𝒪[K] α).map (algebraMap 𝒪[K] 𝒪[M])).comp
      (C a + C (a - σ • a) * X)).coeff n) = addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] (P.coeff n)) *
        (2 ^ ((ramificationIndex L M : ℝ) * -(q : ℝ))) ^ n := by
    have h₁ : addValAbs 𝒪[M] ((((minpoly 𝒪[K] α).map (algebraMap 𝒪[K] 𝒪[M])).comp
        (C a + C (a - σ • a) * X)).coeff n) * addValAbs 𝒪[M] a ^ n =
          addValAbs 𝒪[M] (a - σ • a) ^ n * addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] (P.coeff n)) := by
      rw [← AbsoluteValue.map_pow, ← AbsoluteValue.map_pow, ← map_mul, ← map_mul, hkey]
    rw [hσ, mul_pow] at h₁
    refine mul_right_cancel₀ (pow_pos (addValAbs_pos ha) n).ne' (h₁.trans ?_)
    ring1
  have hunit : IsUnit (Q.coeff kl.1) :=
    isUnit_coeff_of_forall_le hE hG hQ₀ fun n ↦ by
      rw [habs, habs]
      exact addValAbs_algebraMap_mul_pow_le M n hα hb hkl
  let c : ℕ → 𝒪[L] := fun i ↦ ⟨ρ.coeff (i * q.den + kl.1) *
    (α : L) ^ ((i : ℤ) * q.num - coeffVal ρ kl.1), mem_integer_residualPolynomial hα hkl i⟩
  have hcA (i : ℕ) (hi : i ≤ kl.2 / q.den) :
      IsLocalRing.residue 𝒪[L] (c i) = (residualPolynomial ρ (α : L) kl.1 kl.2).coeff i := by
    rw [coeff_residualPolynomial, ite_eq_left hi, ← residueOf_coe]
  have hc₀ : algebraMap 𝓀[L] 𝓀[M] (IsLocalRing.residue 𝒪[L] (c 0)) ≠ 0 := by
    rw [hcA 0 (Nat.zero_le _), map_ne_zero_iff _ (algebraMap 𝓀[L] 𝓀[M]).injective]
    exact coeff_zero_residualPolynomial_ne_zero hα hkl
  have hcP (i : ℕ) :
      c 0 * α ^ (i * q.num.toNat) * P.coeff (i * q.den + kl.1) = c i * P.coeff kl.1 := by
    refine Subtype.ext ?_
    simp only [Subring.coe_mul, Subring.coe_pow]
    rw [hb, hb]
    dsimp only [c]
    have h₁ : (α : L) ^ ((i : ℤ) * q.num - coeffVal ρ kl.1) =
        (α : L) ^ (i * q.num.toNat) * (α : L) ^ (-coeffVal ρ kl.1) := by
      rw [sub_eq_add_neg, zpow_add₀ hα₀, ← zpow_natCast, Nat.cast_mul,
        Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq₀)]
    rw [h₁, zero_mul, zero_add, Nat.cast_zero, zero_mul, zero_sub]
    ring1
  have hlat (i : ℕ) : Q.coeff (i * q.den + kl.1) * algebraMap 𝒪[L] 𝒪[M] (c 0) =
      Q.coeff kl.1 * (w : 𝒪[M]) ^ i * algebraMap 𝒪[L] 𝒪[M] (c i) := by
    have hc : algebraMap 𝒪[L] 𝒪[M] (c 0) * a ^ (i * q.num.toNat) *
        algebraMap 𝒪[L] 𝒪[M] (P.coeff (i * q.den + kl.1)) =
          algebraMap 𝒪[L] 𝒪[M] (c i) * algebraMap 𝒪[L] 𝒪[M] (P.coeff kl.1) := by
      simpa only [map_mul, map_pow] using congrArg (algebraMap 𝒪[L] 𝒪[M]) (hcP i)
    exact coeff_mul_mul_eq (b := fun n ↦ algebraMap 𝒪[L] 𝒪[M] (P.coeff n)) hE ha hPk hG hkey hw hc
  have hid : Q.map (IsLocalRing.residue 𝒪[M]) = C (IsLocalRing.residue 𝒪[M] (Q.coeff kl.1) *
      (algebraMap 𝓀[L] 𝓀[M] (IsLocalRing.residue 𝒪[L] (c 0)))⁻¹) * (X ^ kl.1 *
        expand 𝓀[M] q.den (((residualPolynomial ρ (α : L) kl.1 kl.2).map
          (algebraMap 𝓀[L] 𝓀[M])).comp (C (IsLocalRing.residue 𝒪[M] (w : 𝒪[M])) * X))) := by
    ext j
    rw [coeff_map, coeff_C_mul, coeff_X_pow_mul', coeff_expand hm]
    by_cases hj : ∃ i ≤ kl.2 / q.den, j = i * q.den + kl.1
    · rcases hj with ⟨i, hi, rfl⟩
      rw [ite_eq_left (Nat.le_add_left _ _), Nat.add_sub_cancel, ite_eq_left (dvd_mul_left _ _),
        Nat.mul_div_cancel _ hm, comp_C_mul_X_coeff, coeff_map, ← hcA i hi]
      have h₁ : IsLocalRing.residue 𝒪[M] (Q.coeff (i * q.den + kl.1)) *
          algebraMap 𝓀[L] 𝓀[M] (IsLocalRing.residue 𝒪[L] (c 0)) =
            IsLocalRing.residue 𝒪[M] (Q.coeff kl.1) * IsLocalRing.residue 𝒪[M] (w : 𝒪[M]) ^ i *
              algebraMap 𝓀[L] 𝓀[M] (IsLocalRing.residue 𝒪[L] (c i)) := by
        simpa only [map_mul, map_pow, ResidueField.algebraMap_residue] using
          congrArg (IsLocalRing.residue 𝒪[M]) (hlat i)
      field_simp
      linear_combination h₁
    · push Not at hj
      rw [residue_coeff_eq_zero_of_lt hG hunit (by
        rw [habs, habs]
        exact addValAbs_algebraMap_mul_pow_lt M hα hb hkl hj)]
      split_ifs with h₁ h₂
      · have h₃ : (residualPolynomial ρ (α : L) kl.1 kl.2).coeff ((j - kl.1) / q.den) = 0 := by
          refine coeff_eq_zero_of_natDegree_lt ?_
          rw [natDegree_residualPolynomial hα hkl]
          by_contra h₄
          have h₅ : (j - kl.1) / q.den * q.den = j - kl.1 :=
            Nat.div_mul_cancel h₂
          exact hj _ (not_lt.mp h₄) (by omega)
        rw [comp_C_mul_X_coeff, coeff_map, h₃, map_zero, zero_mul, mul_zero]
      · rw [mul_zero]
      · rw [mul_zero]
  refine splits_map_of_dvd_expand (fun h ↦ coeff_zero_residualPolynomial_ne_zero hα hkl
    (by rw [h, coeff_zero])) hsplit hQ₀ ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr w.isUnit)
      hm ?_
  rw [hid]
  exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _

variable (M) [IsGalois K M] in
/-- **The associated inertia of a segment divides the residue degree of a Galois extension**
(LMFDB `lf.associated_inertia`): for a totally ramified extension `L / K` of nonarchimedean local
fields, a uniformiser `α` of `L` with ramification polynomial `ρ`, a finite Galois extension `M / K`
containing `L` and a segment `S` of the ramification polygon, every irreducible factor of the
residual polynomial `A_S` splits over the residue field of `M`, so its degree divides `f(M / L)`,
and so does the associated inertia of `S`, the least common multiple of these degrees. -/
lemma associatedInertia_dvd_inertiaDegree (hKL : IsTotallyRamified K L) (hα : Irreducible α)
    (hkl : kl ∈ residualSegments (ramificationPolynomial (minpoly K (α : L)) (α : L))) :
    associatedInertia (ramificationPolynomial (minpoly K (α : L)) (α : L)) (α : L) kl ∣
      inertiaDegree L M := by
  classical
  have hA : residualPolynomial (ramificationPolynomial (minpoly K (α : L)) (α : L)) (α : L) kl.1
      kl.2 ≠ 0 :=
    fun h ↦ coeff_zero_residualPolynomial_ne_zero hα hkl (by rw [h, coeff_zero])
  rw [associatedInertia, factorDegreeLcm]
  refine Finset.lcm_dvd fun q hq ↦ ?_
  have hq' : q ∈ normalizedFactors (residualPolynomial
      (ramificationPolynomial (minpoly K (α : L)) (α : L)) (α : L) kl.1 kl.2) :=
    Multiset.mem_toFinset.mp hq
  exact Irreducible.natDegree_dvd_finrank (irreducible_of_normalized_factor q hq')
    ((splits_map_residualPolynomial M hKL hα hkl).of_dvd (Polynomial.map_ne_zero hA)
      (map_dvd (mapRingHom _) (dvd_of_mem_normalizedFactors hq')))

end IsNonarchimedeanLocalField
