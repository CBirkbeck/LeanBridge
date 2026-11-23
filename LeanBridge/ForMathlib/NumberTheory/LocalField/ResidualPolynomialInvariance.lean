import LeanBridge.ForMathlib.NumberTheory.LocalField.MongeInvariance
import LeanBridge.ForMathlib.NumberTheory.LocalField.ResidualPolynomial
import Mathlib.RingTheory.Polynomial.GaussNorm

/-!
# The invariance of the class of residual polynomials

Let `L / K` be a totally ramified extension of nonarchimedean local fields, `α` and `α'` two
uniformisers of `L`, with minimal polynomials `φ` and `φ'` over `K` and ramification polynomials
`ρ(x) = α ^ (-n) φ(α x + α)` and `ρ'(x) = α' ^ (-n) φ'(α' x + α')`, and `α' = u α` with `u` a unit
of `𝒪_L`. This file proves that the equivalence class `𝒜` of the list of residual polynomials of
the segments of the ramification polygon (LMFDB `lf.residual_polynomials`) does not depend on the
uniformiser, which is the knowl's "Then `𝒜` is an invariant of the extension `K[x]/(φ)`" (Pauli and
Sinclair, Theorem 4.8), and that the list itself changes as
`A_i' (x) = u̲ ^ (-v_L(ρ_{k_i})) A_i(u̲ ^ h_i x)`, for the right end `(-k_i, v_L(ρ_{k_i}))` of the
segment `S_i` of slope `h_i / m_i`: the knowl's `γ_{δ,i} A_i(δ ^ h_i x)` for `δ = u̲`.

The proof follows Monge's proof of the invariance of his additive polynomials
(`LeanBridge.ForMathlib.NumberTheory.LocalField.MongeInvariance`): in a finite Galois extension `M`
of `K` containing `L`, `φ(α + α x) = ∏_σ (α - σ α + α x)` over the cosets `σ` of `Gal(M / L)` in
`Gal(M / K)`, and the factor of `φ'(α' + α' x)` at `σ` is `u` times the factor of `φ(α + α x)` up to
`σ(α) (u - σ u)`, which is divisible by `α (σ α - α)` since `σ α - α` divides `σ u - u`. For every
real `c > 0`, the Gauss norm `max_i |a_i| c ^ i` is multiplicative (Mathlib's
`Polynomial.gaussNorm_mul`), so `φ'(α' + α' x) - u ^ n φ(α + α x)` has a smaller Gauss norm than
`φ(α + α x)`. With `c = 2 ^ (e t)` for a real slope `t`, this says that every point of the
difference `ρ' - ρ` lies strictly above every supporting line of the points of `ρ`. So the Newton
polygons of `ρ` and `ρ'` agree, with the same vertices, and at the points of a segment of slope
`h / m` the coefficients of `ρ` and `ρ'` agree to first order, which gives the change of the
residual polynomials. Rational slopes need the real Gauss norm: Monge's comparison uses the integer
slopes `m` of the substitutions `x ↦ α ^ m x`. The Galois extension `M` is the normal closure of `L`
in an algebraic closure, for a separable `L / K`, which covers every extension of `p`-adic fields.

## Main definitions

* `IsNonarchimedeanLocalField.addValAbs`: the absolute value `x ↦ 2 ^ (-v(x))` of a discrete
  valuation ring.

## Main results

* `IsNonarchimedeanLocalField.gaussNorm_prod_sub_prod_lt`: a product of polynomials changes by
  less than its Gauss norm when each factor does.
* `IsNonarchimedeanLocalField.coeffEnvelope_eq_of_forall` and
  `IsNonarchimedeanLocalField.residualPolynomial_mul_eq`: two polynomials with the comparison
  property have the same Newton polygon, and their residual polynomials differ by the change of
  uniformiser.
* `IsNonarchimedeanLocalField.residualAct_residualPairs`: the constants `γ_{δ,i}` of the knowl are
  `δ ^ (-v_L(ρ_{k_i}))`.
* `IsNonarchimedeanLocalField.exists_coeffVal_sub_lt`: the points of `ρ' - ρ` lie strictly above
  the supporting lines of the points of `ρ`.
* `IsNonarchimedeanLocalField.coeffEnvelope_eq_of_irreducible` and
  `IsNonarchimedeanLocalField.residualSegments_eq_of_irreducible` (LMFDB
  `lf.residual_polynomials`): the Newton polygon and the segments of the ramification polygon do
  not depend on the uniformiser.
* `IsNonarchimedeanLocalField.residualPolynomial_eq_of_irreducible` (LMFDB
  `lf.residual_polynomials`): the change of the residual polynomial of a segment under a change of
  uniformiser.
* `IsNonarchimedeanLocalField.residualPolynomials_mem_residualPolynomialClass`,
  `IsNonarchimedeanLocalField.residualPolynomialClass_eq_of_irreducible` and
  `IsNonarchimedeanLocalField.residualPolynomialClass_eq_of_irreducible_of_charZero` (LMFDB
  `lf.residual_polynomials`, Pauli and Sinclair's Theorem 4.8): the list of residual polynomials at
  any uniformiser lies in the class `𝒜` at any other, and `𝒜` does not depend on the uniformiser,
  for a separable extension, such as an extension of `p`-adic fields.

## References

* S. Pauli and B. Sinclair, *Enumerating extensions of (π)-adic fields with given invariants*,
  Int. J. Number Theory 13 (2017); arXiv:1504.06671, Lemma 4.7 and Theorem 4.8.
* J. Monge, *Determination of the number of isomorphism classes of extensions of a p-adic field*,
  J. Number Theory 131 (2011); arXiv:1109.4617, p. 6.
-/

open Finset IsDiscreteValuationRing Polynomial TauCeti ValuativeRel

namespace IsNonarchimedeanLocalField

open HerbrandInvariant

lemma coe_coeff_mongeShift_zero {F E : Type*} [Field F] [ValuativeRel F] [Field E] [ValuativeRel E]
    [Algebra F E] [ValuativeExtension F E] {g : 𝒪[F][X]} (hg : g.Monic) {π : 𝒪[E]} (hπ : π ≠ 0)
    (j : ℕ) : (((mongeShift g π 0).coeff j : 𝒪[E]) : E) =
      (π : E) ^ g.natDegree *
        (ramificationPolynomial (g.map (algebraMap 𝒪[F] F)) (π : E)).coeff j := by
  rw [← coeff_C_mul, ← map_mongeShift_zero hg hπ, coeff_map]
  rfl

section AddValAbs

variable {T : Type*} [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] {x y : T}

open Classical in
variable (T) in
/-- The function `x ↦ 2 ^ (-v(x))` of a discrete valuation ring, for its normalised valuation `v`,
and `0` at `0`. -/
noncomputable def addValAbsFun (x : T) : ℝ :=
  if x = 0 then 0 else 2⁻¹ ^ (addVal T x).toNat

lemma addValAbsFun_of_ne_zero (hx : x ≠ 0) : addValAbsFun T x = 2⁻¹ ^ (addVal T x).toNat :=
  ite_eq_right hx

lemma addValAbsFun_nonneg : 0 ≤ addValAbsFun T x := by
  rw [addValAbsFun]
  split_ifs <;> positivity

lemma addValAbsFun_eq_zero_iff : addValAbsFun T x = 0 ↔ x = 0 := by
  rw [addValAbsFun]
  split_ifs with h
  · exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩
  · exact ⟨fun h' ↦ absurd h' (by positivity), fun h' ↦ absurd h' h⟩

lemma addValAbsFun_mul : addValAbsFun T (x * y) = addValAbsFun T x * addValAbsFun T y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [addValAbsFun]
  rcases eq_or_ne y 0 with rfl | hy
  · simp [addValAbsFun]
  rw [addValAbsFun_of_ne_zero (mul_ne_zero hx hy), addValAbsFun_of_ne_zero hx,
    addValAbsFun_of_ne_zero hy, addVal_mul, ENat.toNat_add (mt addVal_eq_top_iff.mp hx)
      (mt addVal_eq_top_iff.mp hy), pow_add]

lemma addValAbsFun_add_le : addValAbsFun T (x + y) ≤ max (addValAbsFun T x) (addValAbsFun T y) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_add, (addValAbsFun_eq_zero_iff (T := T)).mpr rfl]
    exact le_max_right _ _
  rcases eq_or_ne y 0 with rfl | hy
  · rw [add_zero, (addValAbsFun_eq_zero_iff (T := T)).mpr rfl]
    exact le_max_left _ _
  rcases eq_or_ne (x + y) 0 with hxy | hxy
  · rw [hxy, (addValAbsFun_eq_zero_iff (T := T)).mpr rfl]
    exact le_max_of_le_left addValAbsFun_nonneg
  rw [addValAbsFun_of_ne_zero hx, addValAbsFun_of_ne_zero hy, addValAbsFun_of_ne_zero hxy]
  rcases ENat.ne_top_iff_exists.mp (mt addVal_eq_top_iff.mp hx) with ⟨a, ha⟩
  rcases ENat.ne_top_iff_exists.mp (mt addVal_eq_top_iff.mp hy) with ⟨b, hb⟩
  rcases ENat.ne_top_iff_exists.mp (mt addVal_eq_top_iff.mp hxy) with ⟨c, hc⟩
  have h₂ : min (addVal T x) (addVal T y) ≤ addVal T (x + y) :=
    addVal_add
  rw [← ha, ← hb, ← hc] at h₂
  rw [← ha, ← hb, ← hc, ENat.toNat_natCast, ENat.toNat_natCast, ENat.toNat_natCast]
  rcases le_total a b with hab | hab
  · rw [min_eq_left (by exact_mod_cast hab : (a : ℕ∞) ≤ b)] at h₂
    exact le_max_of_le_left
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by exact_mod_cast h₂))
  · rw [min_eq_right (by exact_mod_cast hab : (b : ℕ∞) ≤ a)] at h₂
    exact le_max_of_le_right
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by exact_mod_cast h₂))

variable (T) in
/-- The **absolute value `x ↦ 2 ^ (-v(x))`** of a discrete valuation ring, for its normalised
valuation `v`. It is nonarchimedean, so Mathlib's Gauss norms of polynomials over the ring for it
are multiplicative. -/
noncomputable def addValAbs : AbsoluteValue T ℝ where
  toFun := addValAbsFun T
  map_mul' _ _ := addValAbsFun_mul
  nonneg' _ := addValAbsFun_nonneg
  eq_zero' _ := addValAbsFun_eq_zero_iff
  add_le' _ _ := addValAbsFun_add_le.trans (max_le_add_of_nonneg addValAbsFun_nonneg
    addValAbsFun_nonneg)

lemma addValAbs_apply : addValAbs T x = addValAbsFun T x :=
  rfl

lemma isNonarchimedean_addValAbs : IsNonarchimedean (addValAbs T) :=
  fun _ _ ↦ addValAbsFun_add_le

lemma addValAbs_pos (hx : x ≠ 0) : 0 < addValAbs T x :=
  (addValAbs T).pos hx

lemma addValAbs_lt_one (hx : ¬IsUnit x) : addValAbs T x < 1 := by
  rcases eq_or_ne x 0 with rfl | hx₀
  · rw [map_zero]
    exact zero_lt_one
  rw [addValAbs_apply, addValAbsFun_of_ne_zero hx₀]
  refine pow_lt_one₀ (by norm_num) (by norm_num) fun h ↦ hx ?_
  rcases ENat.ne_top_iff_exists.mp (mt addVal_eq_top_iff.mp hx₀) with ⟨a, ha⟩
  rw [← ha, ENat.toNat_natCast] at h
  rw [← addVal_eq_zero_iff, ← ha, h, Nat.cast_zero]

lemma addValAbs_eq_one_of_isUnit (hx : IsUnit x) : addValAbs T x = 1 := by
  rw [addValAbs_apply, addValAbsFun_of_ne_zero hx.ne_zero, addVal_eq_zero_iff.mpr hx,
    ENat.toNat_zero, pow_zero]

lemma addValAbs_le_of_dvd (h : x ∣ y) : addValAbs T y ≤ addValAbs T x := by
  rcases h with ⟨z, rfl⟩
  rw [map_mul]
  refine mul_le_of_le_one_right ((addValAbs T).nonneg _) ?_
  by_cases hz : IsUnit z
  · exact (addValAbs_eq_one_of_isUnit hz).le
  · exact (addValAbs_lt_one hz).le

end AddValAbs

section GaussNorm

variable {R : Type*} [CommRing R] [Nontrivial R] {v : AbsoluteValue R ℝ} {c : ℝ} {P Q : R[X]}

lemma gaussNorm_neg (hc : 0 < c) (hv : IsNonarchimedean v) :
    (-P).gaussNorm v c = P.gaussNorm v c := by
  rw [← neg_one_mul, ← C_1, ← C_neg, gaussNorm_mul hv hc, gaussNorm_C, map_neg_eq_map, map_one,
    one_mul]

lemma gaussNorm_add_eq_of_lt (hc : 0 < c) (hv : IsNonarchimedean v)
    (h : Q.gaussNorm v c < P.gaussNorm v c) : (P + Q).gaussNorm v c = P.gaussNorm v c := by
  have h₁ : (P + Q).gaussNorm v c ≤ max (P.gaussNorm v c) (Q.gaussNorm v c) :=
    isNonarchimedean_gaussNorm v hv hc.le P Q
  have h₂ : (P + Q + -Q).gaussNorm v c ≤ max ((P + Q).gaussNorm v c) ((-Q).gaussNorm v c) :=
    isNonarchimedean_gaussNorm v hv hc.le (P + Q) (-Q)
  rw [add_neg_cancel_right, gaussNorm_neg hc hv] at h₂
  refine le_antisymm (h₁.trans (max_le le_rfl h.le)) ?_
  rcases le_total ((P + Q).gaussNorm v c) (Q.gaussNorm v c) with h₃ | h₃
  · rw [max_eq_right h₃] at h₂
    exact absurd (h₂.trans_lt h) (lt_irrefl _)
  · rwa [max_eq_left h₃] at h₂

/-- **A product of polynomials changes by less than its Gauss norm when each factor does**: for a
nonarchimedean absolute value `v` on `R`, a real `c > 0` and polynomials `F_i`, `F'_i` with
`‖F'_i - F_i‖ < ‖F_i‖` for the Gauss norm `‖P‖ = max_j v(P_j) c ^ j`, the products satisfy
`‖∏ F'_i - ∏ F_i‖ < ‖∏ F_i‖`, by the multiplicativity of the Gauss norm (Gauss's lemma). -/
lemma gaussNorm_prod_sub_prod_lt (hc : 0 < c) (hv : IsNonarchimedean v) {ι : Type*} (A : Finset ι)
    (F F' : ι → R[X]) (hF : ∀ i ∈ A, (F' i - F i).gaussNorm v c < (F i).gaussNorm v c) :
    (∏ i ∈ A, F' i - ∏ i ∈ A, F i).gaussNorm v c < (∏ i ∈ A, F i).gaussNorm v c := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    rw [prod_empty, prod_empty, sub_self, gaussNorm_zero, ← C_1, gaussNorm_C, map_one]
    exact zero_lt_one
  | insert i A hi ih =>
    have ih' : (∏ j ∈ A, F' j - ∏ j ∈ A, F j).gaussNorm v c < (∏ j ∈ A, F j).gaussNorm v c :=
      ih fun j hj ↦ hF j (mem_insert_of_mem hj)
    have hFi : (F' i - F i).gaussNorm v c < (F i).gaussNorm v c :=
      hF i (mem_insert_self i A)
    have hpos : 0 < (∏ j ∈ A, F j).gaussNorm v c :=
      (gaussNorm_nonneg v _ hc.le).trans_lt ih'
    have hposi : 0 < (F i).gaussNorm v c :=
      (gaussNorm_nonneg v _ hc.le).trans_lt hFi
    have hA' : (∏ j ∈ A, F' j).gaussNorm v c = (∏ j ∈ A, F j).gaussNorm v c := by
      rw [← add_sub_cancel (∏ j ∈ A, F j) (∏ j ∈ A, F' j)]
      exact gaussNorm_add_eq_of_lt hc hv ih'
    have heq : ∏ j ∈ insert i A, F' j - ∏ j ∈ insert i A, F j =
        (F' i - F i) * ∏ j ∈ A, F' j + F i * (∏ j ∈ A, F' j - ∏ j ∈ A, F j) := by
      rw [prod_insert hi, prod_insert hi]
      ring1
    rw [heq, prod_insert hi, gaussNorm_mul hv hc]
    refine (isNonarchimedean_gaussNorm v hv hc.le _ _).trans_lt (max_lt ?_ ?_)
    · rw [gaussNorm_mul hv hc, hA']
      exact mul_lt_mul_of_pos_right hFi hpos
    · rw [gaussNorm_mul hv hc]
      exact mul_lt_mul_of_pos_left ih' hposi

end GaussNorm

section Comparison

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  {ρ ρ' : L[X]} {kl : ℕ × ℕ} {n : ℕ} {ϖ : 𝒪[L]}

lemma coeff_ne_zero_and_le_or (h : ρ'.coeff n ≠ 0) :
    (ρ.coeff n ≠ 0 ∧ coeffVal ρ n ≤ coeffVal ρ' n) ∨
      ((ρ' - ρ).coeff n ≠ 0 ∧ coeffVal (ρ' - ρ) n ≤ coeffVal ρ' n) := by
  have hm : min (addValuation L (ρ.coeff n)) (addValuation L ((ρ' - ρ).coeff n)) ≤
      addValuation L (ρ.coeff n + (ρ' - ρ).coeff n) :=
    min_addValuation_le_addValuation_add _ _
  have heq : ρ.coeff n + (ρ' - ρ).coeff n = ρ'.coeff n := by
    rw [coeff_sub, add_sub_cancel]
  rw [heq, addValuation_coeff h] at hm
  have hne {x : L} (hx : addValuation L x ≤ (coeffVal ρ' n : WithTop ℤ)) : x ≠ 0 := by
    rintro rfl
    rw [addValuation_zero, top_le_iff] at hx
    exact WithTop.coe_ne_top hx
  rcases min_le_iff.mp hm with h₁ | h₁
  · refine .inl ⟨hne h₁, ?_⟩
    rw [addValuation_coeff (hne h₁)] at h₁
    exact_mod_cast h₁
  · refine .inr ⟨hne h₁, ?_⟩
    rw [addValuation_coeff (hne h₁)] at h₁
    exact_mod_cast h₁

lemma coeffEnvelope_le_coeffHeight (hkey : ∀ (t : ℝ) (i : ℕ), (ρ' - ρ).coeff i ≠ 0 →
    ∃ j, ρ.coeff j ≠ 0 ∧ (coeffVal ρ j : ℝ) - t * j < coeffVal (ρ' - ρ) i - t * i) :
    coeffEnvelope ρ ≤ coeffHeight ρ' := by
  intro n
  rcases eq_or_ne (ρ'.coeff n) 0 with h | h
  · rw [coeffHeight_eq_top_iff.mpr h]
    exact le_top
  have hle : coeffEnvelope ρ ≤ coeffHeight ρ :=
    lowerConvexEnvelope_le (isAdmissible_of_finite finite_coeffHeight_ne_top)
  rw [coeffHeight_of_coeff_ne_zero h]
  by_contra hlt
  rw [not_le] at hlt
  have hr : ∃ r : ℝ, (coeffVal ρ' n : ℝ) < r ∧ (r : WithTop ℝ) ≤ coeffEnvelope ρ n := by
    rcases eq_or_ne (coeffEnvelope ρ n) ⊤ with htop | htop
    · exact ⟨coeffVal ρ' n + 1, by linarith, htop ▸ le_top⟩
    · refine ⟨(coeffEnvelope ρ n).untop₀, ?_, (WithTop.coe_untop₀_of_ne_top htop).le⟩
      rw [← WithTop.coe_untop₀_of_ne_top htop, WithTop.coe_lt_coe] at hlt
      exact hlt
  rcases hr with ⟨r, hr₁, hr₂⟩
  rcases (isConvexSeq_coeffEnvelope.coe_le_iff_exists_affine_minorant n r).mp hr₂ with
    ⟨c, σ, hline, hrc⟩
  rcases coeff_ne_zero_and_le_or h with ⟨h₀, h₁⟩ | ⟨hd, h₁⟩
  · have h₂ : coeffEnvelope ρ n ≤ (coeffVal ρ' n : ℝ) := by
      refine (hle n).trans ?_
      rw [coeffHeight_of_coeff_ne_zero h₀, WithTop.coe_le_coe]
      exact_mod_cast h₁
    exact absurd (hlt.trans_le h₂) (lt_irrefl _)
  · rcases hkey σ n hd with ⟨j, hj, hlt'⟩
    have h₃ : ((c + σ * j : ℝ) : WithTop ℝ) ≤ coeffHeight ρ j :=
      (hline j).trans (hle j)
    rw [coeffHeight_of_coeff_ne_zero hj, WithTop.coe_le_coe] at h₃
    have h₄ : (coeffVal (ρ' - ρ) n : ℝ) ≤ coeffVal ρ' n := by
      exact_mod_cast h₁
    linarith

/-- **Two polynomials with the comparison property have the same Newton polygon**: if every point
`(i, v_L(ρ'_i - ρ_i))` with `ρ'_i ≠ ρ_i` lies strictly above a line of each real slope through a
point of `ρ`, and symmetrically, then the lower convex envelopes of the heights of `ρ` and `ρ'`
agree. -/
lemma coeffEnvelope_eq_of_forall (hkey : ∀ (t : ℝ) (i : ℕ), (ρ' - ρ).coeff i ≠ 0 →
    ∃ j, ρ.coeff j ≠ 0 ∧ (coeffVal ρ j : ℝ) - t * j < coeffVal (ρ' - ρ) i - t * i)
    (hkey' : ∀ (t : ℝ) (i : ℕ), (ρ - ρ').coeff i ≠ 0 →
      ∃ j, ρ'.coeff j ≠ 0 ∧ (coeffVal ρ' j : ℝ) - t * j < coeffVal (ρ - ρ') i - t * i) :
    coeffEnvelope ρ' = coeffEnvelope ρ :=
  le_antisymm
    (le_lowerConvexEnvelope isConvexSeq_coeffEnvelope (coeffEnvelope_le_coeffHeight hkey'))
    (le_lowerConvexEnvelope isConvexSeq_coeffEnvelope (coeffEnvelope_le_coeffHeight hkey))

lemma residualSegments_eq_of_coeffEnvelope_eq (h : coeffEnvelope ρ' = coeffEnvelope ρ) :
    residualSegments ρ' = residualSegments ρ := by
  have hU : residualUnitSlopes ρ' = residualUnitSlopes ρ :=
    Finset.ext fun s ↦ by rw [mem_residualUnitSlopes, mem_residualUnitSlopes, h]
  rw [residualSegments, residualSegments, residualSlopeList, residualSlopeList, hU]
  congr 1
  funext s
  rw [residualSegmentOf, residualSegmentOf, h]

lemma coeffVal_fst_eq_of_coeffEnvelope_eq (h : coeffEnvelope ρ' = coeffEnvelope ρ)
    (hkl : kl ∈ residualSegments ρ) : coeffVal ρ' kl.1 = coeffVal ρ kl.1 := by
  have hkl' : kl ∈ residualSegments ρ' := by
    rwa [residualSegments_eq_of_coeffEnvelope_eq h]
  have h₁ : (coeffHeight ρ' kl.1).untop₀ = (coeffHeight ρ kl.1).untop₀ :=
    congrArg WithTop.untop₀ ((coeffEnvelope_fst_of_mem_residualSegments hkl').symm.trans
      ((congrFun h kl.1).trans (coeffEnvelope_fst_of_mem_residualSegments hkl)))
  rw [untop₀_coeffHeight, untop₀_coeffHeight] at h₁
  exact_mod_cast h₁

lemma coeffVal_add_eq_of_coeffEnvelope_eq (h : coeffEnvelope ρ' = coeffEnvelope ρ)
    (hkl : kl ∈ residualSegments ρ) : coeffVal ρ' (kl.1 + kl.2) = coeffVal ρ (kl.1 + kl.2) := by
  have hkl' : kl ∈ residualSegments ρ' := by
    rwa [residualSegments_eq_of_coeffEnvelope_eq h]
  have h₁ : (coeffHeight ρ' (kl.1 + kl.2)).untop₀ = (coeffHeight ρ (kl.1 + kl.2)).untop₀ :=
    congrArg WithTop.untop₀ ((coeffEnvelope_add_of_mem_residualSegments hkl').symm.trans
      ((congrFun h (kl.1 + kl.2)).trans (coeffEnvelope_add_of_mem_residualSegments hkl)))
  rw [untop₀_coeffHeight, untop₀_coeffHeight] at h₁
  exact_mod_cast h₁

lemma residualSlope_eq_of_coeffEnvelope_eq (h : coeffEnvelope ρ' = coeffEnvelope ρ)
    (hkl : kl ∈ residualSegments ρ) : residualSlope ρ' kl.1 kl.2 = residualSlope ρ kl.1 kl.2 := by
  rw [residualSlope, residualSlope, coeffVal_fst_eq_of_coeffEnvelope_eq h hkl,
    coeffVal_add_eq_of_coeffEnvelope_eq h hkl]

/-- **The change of a residual polynomial under the comparison property**: let `ρ'` have the
Newton polygon of `ρ`, every point of `ρ' - ρ` lying strictly above the supporting lines of `ρ`,
and let `ϖ` be a uniformiser of `L` and `u` a unit of `𝒪_L`. Then the residual polynomial at `u ϖ`
of the segment `(k, l)` of slope `h / m` of the ramification polygon of `ρ'` is
`u̲ ^ (-v_L(ρ_k)) A(u̲ ^ h x)`, for the residual polynomial `A` at `ϖ` of the segment of `ρ`. -/
lemma residualPolynomial_mul_eq (hϖ : Irreducible ϖ) (u : 𝒪[L]ˣ)
    (hkey : ∀ (t : ℝ) (i : ℕ), (ρ' - ρ).coeff i ≠ 0 →
      ∃ j, ρ.coeff j ≠ 0 ∧ (coeffVal ρ j : ℝ) - t * j < coeffVal (ρ' - ρ) i - t * i)
    (h : coeffEnvelope ρ' = coeffEnvelope ρ) (hkl : kl ∈ residualSegments ρ) :
    residualPolynomial ρ' (((u : 𝒪[L]) * ϖ : 𝒪[L]) : L) kl.1 kl.2 =
      C (IsLocalRing.residue 𝒪[L] (u : 𝒪[L]) ^ (-coeffVal ρ kl.1)) *
        (residualPolynomial ρ ϖ kl.1 kl.2).comp
          (C (IsLocalRing.residue 𝒪[L] (u : 𝒪[L]) ^ (residualSlope ρ kl.1 kl.2).num) * X) := by
  have hu₀ : IsLocalRing.residue 𝒪[L] (u : 𝒪[L]) ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr u.isUnit
  ext j
  rw [coeff_C_mul, comp_C_mul_X_coeff, coeff_residualPolynomial, coeff_residualPolynomial,
    residualSlope_eq_of_coeffEnvelope_eq h hkl, coeffVal_fst_eq_of_coeffEnvelope_eq h hkl]
  split_ifs with hj
  · set E : ℤ := (j : ℤ) * (residualSlope ρ kl.1 kl.2).num - coeffVal ρ kl.1 with hE
    have hmem : ρ.coeff (j * (residualSlope ρ kl.1 kl.2).den + kl.1) * (ϖ : L) ^ E ∈ 𝒪[L] :=
      mem_integer_residualPolynomial hϖ hkl j
    have hpos : 0 < addValuation L ((ρ' - ρ).coeff (j * (residualSlope ρ kl.1 kl.2).den + kl.1) *
        (ϖ : L) ^ E) := by
      rcases eq_or_ne ((ρ' - ρ).coeff (j * (residualSlope ρ kl.1 kl.2).den + kl.1)) 0 with h₀ | h₀
      · rw [h₀, zero_mul, addValuation_zero]
        exact WithTop.coe_lt_top 0
      rcases hkey (-(residualSlope ρ kl.1 kl.2 : ℝ)) _ h₀ with ⟨j₀, hj₀, hlt⟩
      have h₁ :
          (coeffVal ρ kl.1 : ℚ) - residualSlope ρ kl.1 kl.2 * ((j₀ : ℚ) - kl.1) ≤ coeffVal ρ j₀ :=
        coeffVal_sub_mul_le hkl hj₀
      have h₂ : (residualSlope ρ kl.1 kl.2) *
          (((j * (residualSlope ρ kl.1 kl.2).den + kl.1 : ℕ) : ℚ) - kl.1) =
            j * (residualSlope ρ kl.1 kl.2).num := by
        push_cast
        rw [add_sub_cancel_right, mul_comm (j : ℚ), ← mul_assoc, Rat.mul_den_eq_num, mul_comm]
      have h₃ : (0 : ℝ) < coeffVal (ρ' - ρ) (j * (residualSlope ρ kl.1 kl.2).den + kl.1) + E := by
        have h₄ : ((coeffVal ρ kl.1 : ℚ) : ℝ) -
            (residualSlope ρ kl.1 kl.2 : ℝ) * ((j₀ : ℝ) - kl.1) ≤ (coeffVal ρ j₀ : ℝ) := by
          exact_mod_cast h₁
        have h₅ : ((residualSlope ρ kl.1 kl.2 : ℚ) : ℝ) *
            (((j * (residualSlope ρ kl.1 kl.2).den + kl.1 : ℕ) : ℝ) - kl.1) =
              j * (residualSlope ρ kl.1 kl.2).num := by
          exact_mod_cast h₂
        rw [hE]
        push_cast at h₄ h₅ hlt ⊢
        nlinarith
      rw [addValuation_mul_zpow hϖ h₀, addValuation_coeff h₀, ← WithTop.coe_add,
        WithTop.coe_pos]
      exact_mod_cast h₃
    have hmem' :
        (ρ' - ρ).coeff (j * (residualSlope ρ kl.1 kl.2).den + kl.1) * (ϖ : L) ^ E ∈ 𝒪[L] := by
      rcases eq_or_ne ((ρ' - ρ).coeff (j * (residualSlope ρ kl.1 kl.2).den + kl.1) * (ϖ : L) ^ E)
        0 with h₀ | h₀
      · rw [h₀]
        exact zero_mem _
      · exact (mem_integer_iff_zero_le_addValuation h₀).mpr hpos.le
    have hsplit : ρ'.coeff (j * (residualSlope ρ kl.1 kl.2).den + kl.1) * (ϖ : L) ^ E =
        ρ.coeff (j * (residualSlope ρ kl.1 kl.2).den + kl.1) * (ϖ : L) ^ E +
          (ρ' - ρ).coeff (j * (residualSlope ρ kl.1 kl.2).den + kl.1) * (ϖ : L) ^ E := by
      rw [coeff_sub]
      ring1
    have hmem'' : ρ'.coeff (j * (residualSlope ρ kl.1 kl.2).den + kl.1) * (ϖ : L) ^ E ∈ 𝒪[L] := by
      rw [hsplit]
      exact add_mem hmem hmem'
    have hunit : ((u : 𝒪[L]) : L) ^ E ∈ 𝒪[L] := by
      rw [coe_units_zpow]
      exact Subtype.coe_prop _
    have hcoe : (((u : 𝒪[L]) * ϖ : 𝒪[L]) : L) ^ E = (ϖ : L) ^ E * ((u : 𝒪[L]) : L) ^ E := by
      rw [Subring.coe_mul, mul_zpow, mul_comm]
    have hr : IsLocalRing.residue 𝒪[L] (u : 𝒪[L]) ^ E =
        IsLocalRing.residue 𝒪[L] (u : 𝒪[L]) ^ (-coeffVal ρ kl.1) *
          (IsLocalRing.residue 𝒪[L] (u : 𝒪[L]) ^ (residualSlope ρ kl.1 kl.2).num) ^ j := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hu₀, hE]
      congr 1
      ring1
    rw [hcoe, ← mul_assoc, residueOf_mul hmem'' hunit, residueOf_unit_zpow,
      residueOf_eq_of_pos hmem'' hmem (by rw [hsplit, add_sub_cancel_left]; exact hpos), hr]
    ring1
  · rw [zero_mul, mul_zero]

lemma residualGammas_map {F : Type*} [Field F] {δ : F} (hδ : δ ≠ 0) (g : ℕ × ℕ → ℤ × F[X])
    (w : ℕ → ℤ) {e₀ : ℕ} (S : List (ℕ × ℕ)) (hS : S.IsChain fun a b ↦ b.1 = a.1 + a.2)
    (hg : ∀ kl ∈ S, (g kl).1 * (g kl).2.natDegree = w kl.1 - w (kl.1 + kl.2))
    (hlast : ∀ kl ∈ S.getLast?, kl.1 + kl.2 = e₀) :
    residualGammas δ (S.map g) = S.map fun kl ↦ δ ^ (-(w kl.1 - w e₀)) := by
  induction hS with
  | nil => rfl
  | singleton kl =>
    simp only [List.map_cons, List.map_nil, residualGammas, List.headD_nil, one_mul]
    rw [hg kl (List.mem_singleton_self kl), hlast kl rfl]
  | @cons_cons kl kl' S hkl hS ih =>
    have ih' :
        residualGammas δ ((kl' :: S).map g) = (kl' :: S).map fun kl ↦ δ ^ (-(w kl.1 - w e₀)) :=
      ih (fun x hx ↦ hg x (List.mem_cons_of_mem _ hx)) fun x hx ↦ hlast x <| by
        rwa [List.getLast?_cons_cons]
    rw [List.map_cons, residualGammas, ih']
    simp only [List.map_cons, List.headD_cons]
    rw [hg kl List.mem_cons_self, ← zpow_add₀ hδ, hkl]
    congr 2
    ring1

lemma residualSegments_isChain : (residualSegments ρ).IsChain fun a b ↦ b.1 = a.1 + a.2 :=
  List.isChain_iff_getElem.mpr fun _ h ↦ residualSegments_succ_fst h

lemma add_eq_natDegree_of_mem_getLast? (hρ : ρ ≠ 0) (hkl : kl ∈ (residualSegments ρ).getLast?) :
    kl.1 + kl.2 = ρ.natDegree := by
  rw [residualSegments, List.getLast?_map, Option.mem_def, Option.map_eq_some_iff] at hkl
  rcases hkl with ⟨s, hs, rfl⟩
  have hsmem : s ∈ residualSlopeList ρ :=
    List.mem_of_getLast? hs
  have hs' : s ∈ unitSlope (coeffEnvelope ρ) '' finiteEdges (coeffEnvelope ρ) :=
    mem_residualSlopeList.mp hsmem
  have hmax (r : ℝ) (hr : r ∈ unitSlope (coeffEnvelope ρ) '' finiteEdges (coeffEnvelope ρ)) :
      r ≤ s := by
    rcases List.mem_iff_getElem.mp (mem_residualSlopeList.mpr hr) with ⟨i, hi, rfl⟩
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega), Option.some_inj] at hs
    rw [← hs]
    exact sortedLT_residualSlopeList.getElem_le_getElem_iff.mpr (by omega)
  rw [residualSegmentOf_fst_add_snd hs']
  have hU : sSup (slopeIndices (coeffEnvelope ρ) s) ∈ slopeIndices (coeffEnvelope ρ) s :=
    sSup_mem_slopeIndices finite_coeffEnvelope_ne_top hs'
  have hR : sSup (slopeIndices (coeffEnvelope ρ) s) + 1 ∉ finiteEdges (coeffEnvelope ρ) := by
    intro hR
    have h₁ : unitSlope (coeffEnvelope ρ) (sSup (slopeIndices (coeffEnvelope ρ) s)) ≤
        unitSlope (coeffEnvelope ρ) (sSup (slopeIndices (coeffEnvelope ρ) s) + 1) :=
      isConvexSeq_coeffEnvelope.monotoneOn hU.1 hR (Nat.le_succ _)
    rw [hU.2] at h₁
    have h₂ :
        sSup (slopeIndices (coeffEnvelope ρ) s) + 1 ≤ sSup (slopeIndices (coeffEnvelope ρ) s) :=
      le_csSup (bddAbove_slopeIndices s finite_coeffEnvelope_ne_top)
        ⟨hR, le_antisymm (hmax _ ⟨_, hR, rfl⟩) h₁⟩
    omega
  have htop : coeffEnvelope ρ (sSup (slopeIndices (coeffEnvelope ρ) s) + 1 + 1) = ⊤ := by
    by_contra h
    exact hR ⟨hU.1.2, h⟩
  have hlead : coeffEnvelope ρ ρ.natDegree ≠ ⊤ :=
    ne_top_of_le_ne_top (fun h ↦ leadingCoeff_ne_zero.mpr hρ (coeffHeight_eq_top_iff.mp h))
      (lowerConvexEnvelope_le (isAdmissible_of_finite finite_coeffHeight_ne_top) _)
  rcases lt_trichotomy (sSup (slopeIndices (coeffEnvelope ρ) s) + 1) ρ.natDegree with
    hlt | heq | hgt
  · exact absurd (isConvexSeq_coeffEnvelope.ne_top_of_le_of_le hU.1.2 hlead (Nat.le_succ _) hlt)
      (not_not.mpr htop)
  · exact heq
  · rcases (lowerConvexEnvelope_ne_top_iff (isAdmissible_of_finite finite_coeffHeight_ne_top)).mp
      hU.1.2 with ⟨-, -, j, hj, -, hjt⟩
    have hjn : j ≤ ρ.natDegree :=
      le_natDegree_of_ne_zero fun h ↦ hjt (coeffHeight_eq_top_iff.mpr h)
    omega

/-- **The constants `γ_{δ,i}` of the equivalence of residual polynomials**: for a monic `ρ` and a
uniformiser `ϖ`, the knowl's `γ_{δ,i}`, defined by `γ_{δ,ℓ} = δ ^ (-h_ℓ deg A_ℓ)` and
`γ_{δ,i} = γ_{δ,i+1} δ ^ (-h_i deg A_i)`, is `δ ^ (-v_L(ρ_k))` for the right end `(-k, v_L(ρ_k))`
of the segment `S_i`, since `h_i deg A_i = v_L(ρ_k) - v_L(ρ_{k + l})`, the segments are consecutive
and the last one ends at the point `(-n, 0)` of the leading coefficient. So the action of `δ` on the
list of residual polynomials is `A_i ↦ δ ^ (-v_L(ρ_k)) A_i(δ ^ h_i x)`. -/
lemma residualAct_residualPairs (hρ : ρ.Monic) (hϖ : Irreducible ϖ) {δ : 𝓀[L]} (hδ : δ ≠ 0) :
    residualAct δ (residualPairs ρ ϖ) = (residualSegments ρ).map fun kl ↦
      C (δ ^ (-coeffVal ρ kl.1)) * (residualPolynomial ρ ϖ kl.1 kl.2).comp
        (C (δ ^ (residualSlope ρ kl.1 kl.2).num) * X) := by
  have hn : coeffVal ρ ρ.natDegree = 0 := by
    rw [coeffVal, coeff_natDegree, hρ.leadingCoeff, ← Subring.coe_one 𝒪[L],
      addValuation_coe (IsDiscreteValuationRing.addVal_one), Nat.cast_zero]
    rfl
  have hγ : residualGammas δ ((residualSegments ρ).map fun kl ↦
      ((residualSlope ρ kl.1 kl.2).num, residualPolynomial ρ ϖ kl.1 kl.2)) =
        (residualSegments ρ).map fun kl ↦ δ ^ (-(coeffVal ρ kl.1 - coeffVal ρ ρ.natDegree)) :=
    residualGammas_map hδ _ (coeffVal ρ) (residualSegments ρ) residualSegments_isChain
      (fun kl hkl ↦ by
        dsimp only
        rw [natDegree_residualPolynomial hϖ hkl,
          num_mul_div_den kl.1 (pos_of_mem_residualSegments hkl).ne'])
      fun kl hkl ↦ add_eq_natDegree_of_mem_getLast? hρ.ne_zero hkl
  rw [residualAct, residualPairs, hγ, List.zipWith_map, List.zipWith_self]
  simp only [hn, sub_zero]

end Comparison

section Tower

variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Field M] [ValuativeRel M]
  [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra L M] [ValuativeExtension L M]
  [Algebra K M] [ValuativeExtension K M] [Module.Finite K M] [IsScalarTower K L M] {α u : 𝒪[L]}
  {f f' : 𝒪[K][X]} {c : ℝ}

variable (M) in
lemma addValAbs_algebraMap_mul_pow {x : 𝒪[L]} (hx : x ≠ 0) (t : ℝ) (k : ℕ) :
    addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] x) *
      ((2 : ℝ) ^ ((TauCeti.ramificationIndex L M : ℝ) * t)) ^ k = (2 : ℝ) ^
        (-((TauCeti.ramificationIndex L M : ℝ) * (addVal 𝒪[L] x).toNat) +
          (TauCeti.ramificationIndex L M : ℝ) * t * k) := by
  have hx' : algebraMap 𝒪[L] 𝒪[M] x ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hx
  rcases ENat.ne_top_iff_exists.mp (mt addVal_eq_top_iff.mp hx) with ⟨a, ha⟩
  rw [addValAbs_apply, addValAbsFun_of_ne_zero hx', TauCeti.addVal_algebraMap, ← ha, nsmul_eq_mul,
    ← Nat.cast_mul, ENat.toNat_natCast, ENat.toNat_natCast, inv_pow, ← Real.rpow_natCast,
    ← Real.rpow_neg (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_add two_pos, Nat.cast_mul]

variable [Module.Finite L M]

lemma gaussNorm_C_add_C_mul_X_sub_lt (hα : Irreducible α) (hy : Algebra.adjoin 𝒪[K] {α} = ⊤)
    (hu : IsUnit u) (σ : M ≃ₐ[K] M) (hc : 0 < c) :
    (C (algebraMap 𝒪[L] 𝒪[M] (u * α) - σ • algebraMap 𝒪[L] 𝒪[M] (u * α)) +
      C (algebraMap 𝒪[L] 𝒪[M] (u * α)) * X - C (algebraMap 𝒪[L] 𝒪[M] u) *
        (C (algebraMap 𝒪[L] 𝒪[M] α - σ • algebraMap 𝒪[L] 𝒪[M] α) +
          C (algebraMap 𝒪[L] 𝒪[M] α) * X)).gaussNorm (addValAbs 𝒪[M]) c <
    (C (algebraMap 𝒪[L] 𝒪[M] u) * (C (algebraMap 𝒪[L] 𝒪[M] α - σ • algebraMap 𝒪[L] 𝒪[M] α) +
      C (algebraMap 𝒪[L] 𝒪[M] α) * X)).gaussNorm (addValAbs 𝒪[M]) c := by
  have hdiff : C (algebraMap 𝒪[L] 𝒪[M] (u * α) - σ • algebraMap 𝒪[L] 𝒪[M] (u * α)) +
      C (algebraMap 𝒪[L] 𝒪[M] (u * α)) * X - C (algebraMap 𝒪[L] 𝒪[M] u) *
        (C (algebraMap 𝒪[L] 𝒪[M] α - σ • algebraMap 𝒪[L] 𝒪[M] α) +
          C (algebraMap 𝒪[L] 𝒪[M] α) * X) = C (σ • algebraMap 𝒪[L] 𝒪[M] α *
            (algebraMap 𝒪[L] 𝒪[M] u - σ • algebraMap 𝒪[L] 𝒪[M] u)) := by
    rw [map_mul, smul_mul']
    simp only [map_sub, map_mul]
    ring1
  have hw : addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] u) = 1 :=
    addValAbs_eq_one_of_isUnit (hu.map _)
  have hα₀ : algebraMap 𝒪[L] 𝒪[M] α ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hα.ne_zero
  have hle₀ : addValAbs 𝒪[M] ((C (algebraMap 𝒪[L] 𝒪[M] α - σ • algebraMap 𝒪[L] 𝒪[M] α) +
      C (algebraMap 𝒪[L] 𝒪[M] α) * X).coeff 0) * c ^ 0 ≤
        (C (algebraMap 𝒪[L] 𝒪[M] α - σ • algebraMap 𝒪[L] 𝒪[M] α) +
          C (algebraMap 𝒪[L] 𝒪[M] α) * X).gaussNorm (addValAbs 𝒪[M]) c :=
    le_gaussNorm _ _ hc.le 0
  have hle₁ : addValAbs 𝒪[M] ((C (algebraMap 𝒪[L] 𝒪[M] α - σ • algebraMap 𝒪[L] 𝒪[M] α) +
      C (algebraMap 𝒪[L] 𝒪[M] α) * X).coeff 1) * c ^ 1 ≤
        (C (algebraMap 𝒪[L] 𝒪[M] α - σ • algebraMap 𝒪[L] 𝒪[M] α) +
          C (algebraMap 𝒪[L] 𝒪[M] α) * X).gaussNorm (addValAbs 𝒪[M]) c :=
    le_gaussNorm _ _ hc.le 1
  simp only [coeff_add, coeff_C_zero, coeff_C_succ, coeff_C_mul, coeff_X_zero, coeff_X_one,
    mul_zero, add_zero, zero_add, mul_one, pow_zero, pow_one] at hle₀ hle₁
  rw [hdiff, gaussNorm_C, map_mul, gaussNorm_mul (isNonarchimedean_addValAbs) hc, gaussNorm_C, hw,
    one_mul]
  have hdvd : σ • algebraMap 𝒪[L] 𝒪[M] α - algebraMap 𝒪[L] 𝒪[M] α ∣
      σ • algebraMap 𝒪[L] 𝒪[M] u - algebraMap 𝒪[L] 𝒪[M] u :=
    smul_sub_dvd_smul_algebraMap_sub σ hy u
  rcases eq_or_ne (σ • algebraMap 𝒪[L] 𝒪[M] α) (algebraMap 𝒪[L] 𝒪[M] α) with heq | hne
  · rw [heq, sub_self, zero_dvd_iff, sub_eq_zero] at hdvd
    rw [hdvd, sub_self, map_zero, mul_zero]
    exact (mul_pos (addValAbs_pos hα₀) hc).trans_le hle₁
  · have hσ : ¬IsUnit (σ • algebraMap 𝒪[L] 𝒪[M] α) := fun hσu ↦
      not_isUnit_algebraMap (M := M) hα <| by
        simpa using hσu.map (MulSemiringAction.toRingHom (M ≃ₐ[K] M) 𝒪[M] σ⁻¹)
    have h₁ : addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] u - σ • algebraMap 𝒪[L] 𝒪[M] u) ≤
        addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] α - σ • algebraMap 𝒪[L] 𝒪[M] α) := by
      rw [(addValAbs 𝒪[M]).map_sub, (addValAbs 𝒪[M]).map_sub (algebraMap 𝒪[L] 𝒪[M] α)]
      exact addValAbs_le_of_dvd hdvd
    have h₂ : 0 < addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] α - σ • algebraMap 𝒪[L] 𝒪[M] α) :=
      addValAbs_pos (sub_ne_zero.mpr hne.symm)
    have h₃ : addValAbs 𝒪[M] (σ • algebraMap 𝒪[L] 𝒪[M] α) *
        addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] u - σ • algebraMap 𝒪[L] 𝒪[M] u) ≤
          addValAbs 𝒪[M] (σ • algebraMap 𝒪[L] 𝒪[M] α) *
            addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] α - σ • algebraMap 𝒪[L] 𝒪[M] α) :=
      mul_le_mul_of_nonneg_left h₁ ((addValAbs _).nonneg _)
    exact (h₃.trans_lt (mul_lt_of_lt_one_left h₂ (addValAbs_lt_one hσ))).trans_le hle₀

variable [IsGalois K M] in
lemma gaussNorm_map_mongeShift_sub_lt (hα : Irreducible α) (hy : Algebra.adjoin 𝒪[K] {α} = ⊤)
    (hy' : Algebra.adjoin 𝒪[K] {u * α} = ⊤) (hf : f.Monic) (hdeg : f.natDegree = Module.finrank K L)
    (hroot : aeval α f = 0) (hf' : f'.Monic) (hdeg' : f'.natDegree = Module.finrank K L)
    (hroot' : aeval (u * α) f' = 0) (hu : IsUnit u) (hc : 0 < c) :
    ((mongeShift f' (u * α) 0 - C (u ^ f.natDegree) * mongeShift f α 0).map
      (algebraMap 𝒪[L] 𝒪[M])).gaussNorm (addValAbs 𝒪[M]) c <
        ((mongeShift f α 0).map (algebraMap 𝒪[L] 𝒪[M])).gaussNorm (addValAbs 𝒪[M]) c := by
  classical
  have hT : IsScalarTower 𝒪[K] 𝒪[L] 𝒪[M] :=
    isScalarTower_integerRing K L M
  have hcard : Fintype.card ((M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range) =
      f.natDegree := by
    have h₁ : (f.map (algebraMap 𝒪[K] 𝒪[M])).natDegree =
        (∏ c : (M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range,
          (X - C (c.out • algebraMap 𝒪[L] 𝒪[M] α))).natDegree :=
      congrArg natDegree (map_eq_prod_quotient (M := M) hy hf hdeg hroot)
    rw [natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective _ _),
      natDegree_prod_of_monic _ _ fun c _ ↦ monic_X_sub_C _] at h₁
    simpa using h₁.symm
  have hfactor (r y : 𝒪[M]) : (X - C r).comp (C y + C (y ^ (0 + 1)) * X) = C (y - r) + C y * X := by
    simp only [sub_comp, X_comp, C_comp, C_sub, zero_add, pow_one]
    ring1
  have hprod : C (algebraMap 𝒪[L] 𝒪[M] (u ^ f.natDegree)) *
      ∏ c : (M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range,
        (C (algebraMap 𝒪[L] 𝒪[M] α - c.out • algebraMap 𝒪[L] 𝒪[M] α) +
          C (algebraMap 𝒪[L] 𝒪[M] α) * X) =
      ∏ c : (M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range,
        C (algebraMap 𝒪[L] 𝒪[M] u) *
          (C (algebraMap 𝒪[L] 𝒪[M] α - c.out • algebraMap 𝒪[L] 𝒪[M] α) +
            C (algebraMap 𝒪[L] 𝒪[M] α) * X) := by
    rw [prod_mul_distrib, prod_const, card_univ, hcard, ← map_pow, map_pow]
  rw [Polynomial.map_sub, Polynomial.map_mul, map_C,
    map_mongeShift_eq_prod univ _ (map_eq_prod_quotient (M := M) hy' hf' hdeg' hroot'),
    map_mongeShift_eq_prod univ _ (map_eq_prod_quotient (M := M) hy hf hdeg hroot),
    Polynomial.prod_comp, Polynomial.prod_comp]
  simp only [hfactor]
  rw [hprod]
  refine (gaussNorm_prod_sub_prod_lt hc isNonarchimedean_addValAbs univ
    (fun c : (M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range ↦
      C (algebraMap 𝒪[L] 𝒪[M] u) *
        (C (algebraMap 𝒪[L] 𝒪[M] α - c.out • algebraMap 𝒪[L] 𝒪[M] α) +
          C (algebraMap 𝒪[L] 𝒪[M] α) * X))
    (fun c : (M ≃ₐ[K] M) ⧸ (AlgEquiv.restrictScalarsHom (S := L) K).range ↦
      C (algebraMap 𝒪[L] 𝒪[M] (u * α) - c.out • algebraMap 𝒪[L] 𝒪[M] (u * α)) +
        C (algebraMap 𝒪[L] 𝒪[M] (u * α)) * X)
    fun c _ ↦ gaussNorm_C_add_C_mul_X_sub_lt hα hy hu c.out hc).trans_eq ?_
  rw [← hprod, gaussNorm_mul isNonarchimedean_addValAbs hc, gaussNorm_C,
    addValAbs_eq_one_of_isUnit ((hu.pow _).map _), one_mul]

end Tower

section Invariance

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] {α α' : 𝒪[L]}

lemma addValuation_coe_eq_toNat {x : 𝒪[L]} (hx : x ≠ 0) :
    addValuation L (x : L) = (((addVal 𝒪[L] x).toNat : ℤ) : WithTop ℤ) := by
  rcases ENat.ne_top_iff_exists.mp (mt addVal_eq_top_iff.mp hx) with ⟨a, ha⟩
  rw [addValuation_coe ha.symm, ← ha, ENat.toNat_natCast]

lemma addValuation_pow_mul (hα : Irreducible α) (v : 𝒪[L]ˣ) (n : ℕ) {x : L} (hx : x ≠ 0) :
    addValuation L (((v : 𝒪[L]) : L) ^ n * (α : L) ^ n * x) = n + addValuation L x := by
  have hv : ((v : 𝒪[L]) : L) ^ n = (((v ^ n : 𝒪[L]ˣ) : 𝒪[L]) : L) := by
    push_cast
    rfl
  have hα₀ : (α : L) ≠ 0 :=
    fun h ↦ hα.ne_zero (Subtype.ext h)
  have hv₀ : ((v : 𝒪[L]) : L) ^ n ≠ 0 := by
    rw [hv]
    exact fun h ↦ (v ^ n).ne_zero (Subtype.ext h)
  rw [addValuation_mul (mul_ne_zero hv₀ (pow_ne_zero _ hα₀)) hx, addValuation_mul hv₀
    (pow_ne_zero _ hα₀), hv, addValuation_coe_unit, zero_add, ← zpow_natCast, addValuation_zpow hα]
  rfl

lemma natDegree_minpoly_of_isTotallyRamified (hKL : IsTotallyRamified K L) (hα : Irreducible α) :
    (minpoly 𝒪[K] α).natDegree = Module.finrank K L := by
  have h :
      (minpoly 𝒪[K] (hKL.integralPowerBasis hα).gen).natDegree = (hKL.integralPowerBasis hα).dim :=
    (hKL.integralPowerBasis hα).natDegree_minpoly
  rw [hKL.integralPowerBasis_gen, hKL.integralPowerBasis_dim] at h
  exact h.trans hKL

variable (α) in
lemma minpoly_eq_map : minpoly K (α : L) = (minpoly 𝒪[K] α).map (algebraMap 𝒪[K] K) := by
  have : Module.Finite K L :=
    finite_of_valuativeExtension K L
  exact minpoly.isIntegrallyClosed_eq_field_fractions K L (IsIntegral.of_finite 𝒪[K] α)

lemma coe_coeff_mongeShift_minpoly (hα : Irreducible α) (j : ℕ) :
    (((mongeShift (minpoly 𝒪[K] α) α 0).coeff j : 𝒪[L]) : L) =
      (α : L) ^ (minpoly 𝒪[K] α).natDegree *
        (ramificationPolynomial (minpoly K (α : L)) (α : L)).coeff j := by
  have hfin : FiniteDimensional K L :=
    finite_of_valuativeExtension K L
  rw [minpoly_eq_map]
  exact coe_coeff_mongeShift_zero (minpoly.monic (IsIntegral.of_finite 𝒪[K] α)) hα.ne_zero j

lemma coeff_mongeShift_eq_zero_iff (hα : Irreducible α) {j : ℕ} :
    (mongeShift (minpoly 𝒪[K] α) α 0).coeff j = 0 ↔
      (ramificationPolynomial (minpoly K (α : L)) (α : L)).coeff j = 0 := by
  rw [← Subtype.coe_inj, coe_coeff_mongeShift_minpoly hα, ZeroMemClass.coe_zero, mul_eq_zero,
    or_iff_right (pow_ne_zero _ fun h ↦ hα.ne_zero (Subtype.ext h))]

lemma toNat_addVal_coeff_mongeShift (hα : Irreducible α) {j : ℕ}
    (hj : (ramificationPolynomial (minpoly K (α : L)) (α : L)).coeff j ≠ 0) :
    ((addVal 𝒪[L] ((mongeShift (minpoly 𝒪[K] α) α 0).coeff j)).toNat : ℤ) =
      (minpoly 𝒪[K] α).natDegree +
        coeffVal (ramificationPolynomial (minpoly K (α : L)) (α : L)) j := by
  have h₁ : addValuation L (((mongeShift (minpoly 𝒪[K] α) α 0).coeff j : 𝒪[L]) : L) =
      (((addVal 𝒪[L] ((mongeShift (minpoly 𝒪[K] α) α 0).coeff j)).toNat : ℤ) : WithTop ℤ) :=
    addValuation_coe_eq_toNat (mt (coeff_mongeShift_eq_zero_iff hα).mp hj)
  rw [coe_coeff_mongeShift_minpoly hα, addValuation_mul (pow_ne_zero _ fun h ↦
    hα.ne_zero (Subtype.ext h)) hj, ← zpow_natCast, addValuation_zpow hα, addValuation_coeff hj,
    ← WithTop.coe_add] at h₁
  exact_mod_cast (WithTop.coe_injective h₁).symm

/-- **The points of `ρ' - ρ` lie strictly above the supporting lines of the points of `ρ`**: for a
totally ramified extension `L / K` of nonarchimedean local fields, inside a finite Galois extension
`M / K`, and two uniformisers `α`, `α'` of `L`, with the ramification polynomials `ρ` and `ρ'` of
their minimal polynomials over `K`, every point `(i, v_L(ρ'_i - ρ_i))` with `ρ'_i ≠ ρ_i` lies
strictly above the line of slope `t` through some point `(j, v_L(ρ_j))` of `ρ`, for every real `t`:
`v_L(ρ_j) - t j < v_L(ρ'_i - ρ_i) - t i`. -/
lemma exists_coeffVal_sub_lt (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M] [Algebra L M] [ValuativeExtension L M] [Module.Finite L M]
    [Algebra K M] [ValuativeExtension K M] [Module.Finite K M] [IsGalois K M] [IsScalarTower K L M]
    (hKL : IsTotallyRamified K L) (hα : Irreducible α) (hα' : Irreducible α') (t : ℝ) {i : ℕ}
    (hi : (ramificationPolynomial (minpoly K (α' : L)) (α' : L) -
      ramificationPolynomial (minpoly K (α : L)) (α : L)).coeff i ≠ 0) :
    ∃ j, (ramificationPolynomial (minpoly K (α : L)) (α : L)).coeff j ≠ 0 ∧
      (coeffVal (ramificationPolynomial (minpoly K (α : L)) (α : L)) j : ℝ) - t * j <
        (coeffVal (ramificationPolynomial (minpoly K (α' : L)) (α' : L) -
          ramificationPolynomial (minpoly K (α : L)) (α : L)) i : ℝ) - t * i := by
  have hfin : Module.Finite K L :=
    finite_of_valuativeExtension K L
  have hint : IsIntegral 𝒪[K] α :=
    IsIntegral.of_finite 𝒪[K] α
  rcases associated_of_irreducible _ hα hα' with ⟨v, hv⟩
  have hα'eq : α' = (v : 𝒪[L]) * α := by
    rw [← hv, mul_comm]
  subst hα'eq
  have hint' : IsIntegral 𝒪[K] ((v : 𝒪[L]) * α) :=
    IsIntegral.of_finite 𝒪[K] _
  have hn : (minpoly 𝒪[K] ((v : 𝒪[L]) * α)).natDegree = (minpoly 𝒪[K] α).natDegree := by
    rw [natDegree_minpoly_of_isTotallyRamified hKL hα,
      natDegree_minpoly_of_isTotallyRamified hKL hα']
  have he : (0 : ℝ) < TauCeti.ramificationIndex L M := by
    exact_mod_cast TauCeti.ramificationIndex_pos
  set c : ℝ := (2 : ℝ) ^ ((TauCeti.ramificationIndex L M : ℝ) * t) with hcdef
  have hc : 0 < c :=
    Real.rpow_pos_of_pos two_pos _
  set P : 𝒪[L][X] := mongeShift (minpoly 𝒪[K] α) α 0 with hPdef
  set Q : 𝒪[L][X] := mongeShift (minpoly 𝒪[K] ((v : 𝒪[L]) * α)) ((v : 𝒪[L]) * α) 0 -
    C ((v : 𝒪[L]) ^ (minpoly 𝒪[K] α).natDegree) * P with hQdef
  have hG : (Q.map (algebraMap 𝒪[L] 𝒪[M])).gaussNorm (addValAbs 𝒪[M]) c <
      (P.map (algebraMap 𝒪[L] 𝒪[M])).gaussNorm (addValAbs 𝒪[M]) c :=
    gaussNorm_map_mongeShift_sub_lt hα (hKL.adjoin_eq_top_of_irreducible hα)
      (hKL.adjoin_eq_top_of_irreducible hα') (minpoly.monic hint)
      (natDegree_minpoly_of_isTotallyRamified hKL hα) (minpoly.aeval 𝒪[K] α) (minpoly.monic hint')
      (natDegree_minpoly_of_isTotallyRamified hKL hα') (minpoly.aeval 𝒪[K] _) v.isUnit hc
  have hP (j : ℕ) : ((P.coeff j : 𝒪[L]) : L) = (α : L) ^ (minpoly 𝒪[K] α).natDegree *
      (ramificationPolynomial (minpoly K (α : L)) (α : L)).coeff j :=
    coe_coeff_mongeShift_minpoly hα j
  have hQ (j : ℕ) : ((Q.coeff j : 𝒪[L]) : L) = ((v : 𝒪[L]) : L) ^ (minpoly 𝒪[K] α).natDegree *
      (α : L) ^ (minpoly 𝒪[K] α).natDegree *
        (ramificationPolynomial (minpoly K (((v : 𝒪[L]) * α : 𝒪[L]) : L))
          (((v : 𝒪[L]) * α : 𝒪[L]) : L) - ramificationPolynomial (minpoly K (α : L))
            (α : L)).coeff j := by
    rw [hQdef, coeff_sub, coeff_C_mul, AddSubgroupClass.coe_sub,
      Subring.coe_mul _ ((v : 𝒪[L]) ^ (minpoly 𝒪[K] α).natDegree), Subring.coe_pow,
      coe_coeff_mongeShift_minpoly hα' j, hn, hP,
      coeff_sub, Subring.coe_mul, mul_pow]
    ring1
  have hv₀ : ((v : 𝒪[L]) : L) ≠ 0 :=
    fun h ↦ v.ne_zero (Subtype.ext h)
  have hα₀ : (α : L) ≠ 0 :=
    fun h ↦ hα.ne_zero (Subtype.ext h)
  have hQi : Q.coeff i ≠ 0 :=
    fun h ↦ mul_ne_zero (mul_ne_zero (pow_ne_zero _ hv₀) (pow_ne_zero _ hα₀)) hi <| by
      rw [← hQ, h, ZeroMemClass.coe_zero]
  have hlt : addValAbs 𝒪[M] ((Q.map (algebraMap 𝒪[L] 𝒪[M])).coeff i) * c ^ i <
      (P.map (algebraMap 𝒪[L] 𝒪[M])).gaussNorm (addValAbs 𝒪[M]) c :=
    (le_gaussNorm (addValAbs 𝒪[M]) _ hc.le i).trans_lt hG
  rcases exists_eq_gaussNorm (addValAbs 𝒪[M]) c (P.map (algebraMap 𝒪[L] 𝒪[M])) with ⟨j, hj⟩
  have hPj : P.coeff j ≠ 0 := by
    intro h
    have h₀ : (P.map (algebraMap 𝒪[L] 𝒪[M])).coeff j = 0 := by
      rw [coeff_map, h, map_zero]
    rw [hj, h₀, map_zero, zero_mul] at hlt
    exact absurd hlt (not_lt.mpr (mul_nonneg ((addValAbs _).nonneg _) (pow_nonneg hc.le _)))
  have hlt' : addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] (Q.coeff i)) * c ^ i <
      addValAbs 𝒪[M] (algebraMap 𝒪[L] 𝒪[M] (P.coeff j)) * c ^ j := by
    rw [hj] at hlt
    simpa only [coeff_map] using hlt
  rw [hcdef, addValAbs_algebraMap_mul_pow M hQi, addValAbs_algebraMap_mul_pow M hPj,
    Real.rpow_lt_rpow_left_iff one_lt_two] at hlt'
  have hρj : (ramificationPolynomial (minpoly K (α : L)) (α : L)).coeff j ≠ 0 :=
    mt (coeff_mongeShift_eq_zero_iff hα).mpr hPj
  refine ⟨j, hρj, ?_⟩
  have hvQ : addValuation L ((Q.coeff i : 𝒪[L]) : L) =
      (((addVal 𝒪[L] (Q.coeff i)).toNat : ℤ) : WithTop ℤ) :=
    addValuation_coe_eq_toNat hQi
  rw [hQ, addValuation_pow_mul hα v _ hi, addValuation_coeff hi] at hvQ
  have hQ' : ((addVal 𝒪[L] (Q.coeff i)).toNat : ℝ) = (minpoly 𝒪[K] α).natDegree +
      coeffVal (ramificationPolynomial (minpoly K (((v : 𝒪[L]) * α : 𝒪[L]) : L))
        (((v : 𝒪[L]) * α : 𝒪[L]) : L) - ramificationPolynomial (minpoly K (α : L)) (α : L)) i := by
    exact_mod_cast WithTop.coe_injective (hvQ.symm.trans (WithTop.coe_add _ _).symm)
  have hP' : ((addVal 𝒪[L] (P.coeff j)).toNat : ℝ) = (minpoly 𝒪[K] α).natDegree +
      coeffVal (ramificationPolynomial (minpoly K (α : L)) (α : L)) j := by
    exact_mod_cast toNat_addVal_coeff_mongeShift hα hρj
  rw [hQ', hP'] at hlt'
  nlinarith

variable (K) in
lemma monic_ramificationPolynomial_minpoly (hα : Irreducible α) :
    (ramificationPolynomial (minpoly K (α : L)) (α : L)).Monic := by
  have hfin : FiniteDimensional K L :=
    finite_of_valuativeExtension K L
  exact monic_ramificationPolynomial (minpoly.monic (IsIntegral.of_finite K _))
    fun h ↦ hα.ne_zero (Subtype.ext h)

lemma residualAct_one_residualPairs (hα : Irreducible α) :
    residualAct 1 (residualPairs (ramificationPolynomial (minpoly K (α : L)) (α : L)) α) =
      residualPolynomials (ramificationPolynomial (minpoly K (α : L)) (α : L)) α := by
  rw [residualAct_residualPairs (monic_ramificationPolynomial_minpoly K hα) hα one_ne_zero,
    residualPolynomials]
  refine List.map_congr_left fun kl _ ↦ ?_
  rw [one_zpow, one_zpow, C_1, one_mul, one_mul, comp_X]

variable [Algebra.IsSeparable K L]

lemma exists_coeffVal_sub_lt_of_isSeparable (hKL : IsTotallyRamified K L) (hα : Irreducible α)
    (hα' : Irreducible α') (t : ℝ) {i : ℕ} (hi : (ramificationPolynomial (minpoly K (α' : L))
      (α' : L) - ramificationPolynomial (minpoly K (α : L)) (α : L)).coeff i ≠ 0) :
    ∃ j, (ramificationPolynomial (minpoly K (α : L)) (α : L)).coeff j ≠ 0 ∧
      (coeffVal (ramificationPolynomial (minpoly K (α : L)) (α : L)) j : ℝ) - t * j <
        (coeffVal (ramificationPolynomial (minpoly K (α' : L)) (α' : L) -
          ramificationPolynomial (minpoly K (α : L)) (α : L)) i : ℝ) - t * i := by
  have hfin : FiniteDimensional K L :=
    finite_of_valuativeExtension K L
  have hcl : IsAlgClosure K (AlgebraicClosure L) :=
    IsAlgClosure.ofAlgebraic K L (AlgebraicClosure L)
  let vM : ValuativeRel (IntermediateField.normalClosure K L (AlgebraicClosure L)) :=
    finiteIntermediateFieldValuativeRel K _ _
  let tM : TopologicalSpace (IntermediateField.normalClosure K L (AlgebraicClosure L)) :=
    finiteIntermediateFieldTopology K _ _
  have hM : IsNonarchimedeanLocalField (IntermediateField.normalClosure K L (AlgebraicClosure L)) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  have hKM : ValuativeExtension K (IntermediateField.normalClosure K L (AlgebraicClosure L)) :=
    finiteIntermediateField_valuativeExtension K _ _
  have hLM : ValuativeExtension L (IntermediateField.normalClosure K L (AlgebraicClosure L)) :=
    ⟨(IsScalarTower.toAlgHom K L _).valuativeExtension.vle_iff_vle⟩
  have hfinLM : Module.Finite L (IntermediateField.normalClosure K L (AlgebraicClosure L)) :=
    .of_restrictScalars_finite K L _
  exact exists_coeffVal_sub_lt (IntermediateField.normalClosure K L (AlgebraicClosure L)) hKL hα
    hα' t hi

/-- **The Newton polygon of the ramification polynomial does not depend on the uniformiser**: for
a totally ramified separable extension `L / K` of nonarchimedean local fields and two uniformisers
`α`, `α'` of `L`, the ramification polynomials `ρ`, `ρ'` of their minimal polynomials over `K`
have the same Newton polygon, the lower convex envelope of the heights of their coefficients. -/
lemma coeffEnvelope_eq_of_irreducible (hKL : IsTotallyRamified K L) (hα : Irreducible α)
    (hα' : Irreducible α') :
    coeffEnvelope (ramificationPolynomial (minpoly K (α' : L)) (α' : L)) =
      coeffEnvelope (ramificationPolynomial (minpoly K (α : L)) (α : L)) :=
  coeffEnvelope_eq_of_forall (fun t _ hi ↦ exists_coeffVal_sub_lt_of_isSeparable hKL hα hα' t hi)
    fun t _ hi ↦ exists_coeffVal_sub_lt_of_isSeparable hKL hα' hα t hi

/-- **The segments of the ramification polygon do not depend on the uniformiser** (LMFDB
`lf.residual_polynomials`): for a totally ramified separable extension `L / K` of nonarchimedean
local fields and two uniformisers `α`, `α'` of `L`, the segments `S_1, …, S_ℓ` of the ramification
polygons of `L / K` at `α` and at `α'` are the same. -/
lemma residualSegments_eq_of_irreducible (hKL : IsTotallyRamified K L) (hα : Irreducible α)
    (hα' : Irreducible α') :
    residualSegments (ramificationPolynomial (minpoly K (α' : L)) (α' : L)) =
      residualSegments (ramificationPolynomial (minpoly K (α : L)) (α : L)) :=
  residualSegments_eq_of_coeffEnvelope_eq (coeffEnvelope_eq_of_irreducible hKL hα hα')

/-- **The change of a residual polynomial under a change of uniformiser** (LMFDB
`lf.residual_polynomials`, Pauli and Sinclair's Lemma 4.7): for a totally ramified separable
extension `L / K` of nonarchimedean local fields and two uniformisers `α` and `α' = u α` of `L`,
`u` a unit, the residual polynomial at `α'` of the segment `(k, l)` of slope `h / m` of the
ramification polygon is `u̲ ^ (-v_L(ρ_k)) A(u̲ ^ h x)`, for its residual polynomial `A` at `α`. -/
lemma residualPolynomial_eq_of_irreducible (hKL : IsTotallyRamified K L) (hα : Irreducible α)
    (hα' : Irreducible α') (u : 𝒪[L]ˣ) (hu : α' = u * α) {kl : ℕ × ℕ}
    (hkl : kl ∈ residualSegments (ramificationPolynomial (minpoly K (α : L)) (α : L))) :
    residualPolynomial (ramificationPolynomial (minpoly K (α' : L)) (α' : L)) (α' : L) kl.1 kl.2 =
      C (IsLocalRing.residue 𝒪[L] (u : 𝒪[L]) ^
        (-coeffVal (ramificationPolynomial (minpoly K (α : L)) (α : L)) kl.1)) *
          (residualPolynomial (ramificationPolynomial (minpoly K (α : L)) (α : L)) (α : L) kl.1
            kl.2).comp (C (IsLocalRing.residue 𝒪[L] (u : 𝒪[L]) ^ (residualSlope
              (ramificationPolynomial (minpoly K (α : L)) (α : L)) kl.1 kl.2).num) * X) := by
  subst hu
  exact residualPolynomial_mul_eq hα u
    (fun t _ hi ↦ exists_coeffVal_sub_lt_of_isSeparable hKL hα hα' t hi)
    (coeffEnvelope_eq_of_irreducible hKL hα hα') hkl

lemma residualAct_residualPairs_eq (hKL : IsTotallyRamified K L) (hα : Irreducible α)
    (hα' : Irreducible α') (u : 𝒪[L]ˣ) (hu : α' = u * α) {δ : 𝓀[L]} (hδ : δ ≠ 0) :
    residualAct δ (residualPairs (ramificationPolynomial (minpoly K (α' : L)) (α' : L)) α') =
      residualAct (δ * IsLocalRing.residue 𝒪[L] (u : 𝒪[L]))
        (residualPairs (ramificationPolynomial (minpoly K (α : L)) (α : L)) α) := by
  have hu₀ : IsLocalRing.residue 𝒪[L] (u : 𝒪[L]) ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr u.isUnit
  rw [residualAct_residualPairs (monic_ramificationPolynomial_minpoly K hα') hα' hδ,
    residualAct_residualPairs (monic_ramificationPolynomial_minpoly K hα) hα (mul_ne_zero hδ hu₀),
    residualSegments_eq_of_irreducible hKL hα hα']
  refine List.map_congr_left fun kl hkl ↦ ?_
  rw [residualPolynomial_eq_of_irreducible hKL hα hα' u hu hkl,
    coeffVal_fst_eq_of_coeffEnvelope_eq (coeffEnvelope_eq_of_irreducible hKL hα hα') hkl,
    residualSlope_eq_of_coeffEnvelope_eq (coeffEnvelope_eq_of_irreducible hKL hα hα') hkl,
    mul_comp, C_comp, ← mul_assoc, ← C_mul, ← mul_zpow, comp_assoc, mul_comp, C_comp, X_comp,
    ← mul_assoc, ← C_mul, ← mul_zpow, mul_comm (IsLocalRing.residue 𝒪[L] (u : 𝒪[L]))]

/-- **The list of residual polynomials at a uniformiser lies in the class at any other** (LMFDB
`lf.residual_polynomials`): for a totally ramified separable extension `L / K` of nonarchimedean
local fields and two uniformisers `α`, `α'` of `L`, the list of residual polynomials of the
segments of the ramification polygon at `α'` is
`(γ_{δ,1} A_1(δ ^ h_1 x), …, γ_{δ,ℓ} A_ℓ(δ ^ h_ℓ x))` for the residual polynomials `A_i` at `α`
and the residue `δ ∈ K̲ ^ ×` of `α' / α`. -/
lemma residualPolynomials_mem_residualPolynomialClass (hKL : IsTotallyRamified K L)
    (hα : Irreducible α) (hα' : Irreducible α') :
    residualPolynomials (ramificationPolynomial (minpoly K (α' : L)) (α' : L)) α' ∈
      residualPolynomialClass K (ramificationPolynomial (minpoly K (α : L)) (α : L)) α := by
  rcases associated_of_irreducible _ hα hα' with ⟨u, hu⟩
  have hu' : α' = u * α := by
    rw [← hu, mul_comm]
  rcases (isTotallyRamified_iff_surjective_algebraMap_residueField K L).1 hKL
    (IsLocalRing.residue 𝒪[L] (u : 𝒪[L])) with ⟨d, hd⟩
  have hu₀ : IsLocalRing.residue 𝒪[L] (u : 𝒪[L]) ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr u.isUnit
  have hd₀ : d ≠ 0 := by
    rintro rfl
    rw [map_zero] at hd
    exact hu₀ hd.symm
  refine ⟨Units.mk0 d hd₀, ?_⟩
  have h₁ : residualAct 1
      (residualPairs (ramificationPolynomial (minpoly K (α' : L)) (α' : L)) α') =
        residualAct (1 * IsLocalRing.residue 𝒪[L] (u : 𝒪[L]))
          (residualPairs (ramificationPolynomial (minpoly K (α : L)) (α : L)) α) :=
    residualAct_residualPairs_eq hKL hα hα' u hu' one_ne_zero
  rw [one_mul, residualAct_one_residualPairs hα'] at h₁
  dsimp only
  rw [Units.val_mk0, hd, h₁]

/-- **The equivalence class of residual polynomials does not depend on the uniformiser** (LMFDB
`lf.residual_polynomials`, Pauli and Sinclair's Theorem 4.8): for a totally ramified separable
extension `L / K` of nonarchimedean local fields and two uniformisers `α`, `α'` of `L`, the classes
`𝒜 = {(γ_{δ,1} A_1(δ ^ h_1 x), …, γ_{δ,ℓ} A_ℓ(δ ^ h_ℓ x)) : δ ∈ K̲ ^ ×}` of the lists of residual
polynomials of the segments of the ramification polygon at `α` and at `α'` agree. So `𝒜` is an
invariant of the extension `K[x]/(φ)`, for the minimal polynomial `φ` of any uniformiser. -/
lemma residualPolynomialClass_eq_of_irreducible (hKL : IsTotallyRamified K L) (hα : Irreducible α)
    (hα' : Irreducible α') :
    residualPolynomialClass K (ramificationPolynomial (minpoly K (α' : L)) (α' : L)) α' =
      residualPolynomialClass K (ramificationPolynomial (minpoly K (α : L)) (α : L)) α := by
  have hsub {β β' : 𝒪[L]} (hβ : Irreducible β) (hβ' : Irreducible β') :
      residualPolynomialClass K (ramificationPolynomial (minpoly K (β' : L)) (β' : L)) β' ⊆
        residualPolynomialClass K (ramificationPolynomial (minpoly K (β : L)) (β : L)) β := by
    rintro _ ⟨δ, rfl⟩
    rcases associated_of_irreducible _ hβ hβ' with ⟨u, hu⟩
    have hu' : β' = u * β := by
      rw [← hu, mul_comm]
    rcases (isTotallyRamified_iff_surjective_algebraMap_residueField K L).1 hKL
      (IsLocalRing.residue 𝒪[L] (u : 𝒪[L])) with ⟨d, hd⟩
    have hu₀ : IsLocalRing.residue 𝒪[L] (u : 𝒪[L]) ≠ 0 :=
      (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr u.isUnit
    have hd₀ : d ≠ 0 := by
      rintro rfl
      rw [map_zero] at hd
      exact hu₀ hd.symm
    refine ⟨δ * Units.mk0 d hd₀, ?_⟩
    dsimp only
    rw [residualAct_residualPairs_eq hKL hβ hβ' u hu' ((map_ne_zero (algebraMap 𝓀[K] 𝓀[L])).mpr
      δ.ne_zero), Units.val_mul, Units.val_mk0, map_mul, hd]
  exact subset_antisymm (hsub hα hα') (hsub hα' hα)

end Invariance

section CharZero

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [CharZero K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] {α α' : 𝒪[L]}

/-- **The equivalence class of residual polynomials of an extension of `p`-adic fields** (LMFDB
`lf.residual_polynomials`): for a totally ramified extension `L / K` of nonarchimedean local fields
of characteristic `0`, such as `p`-adic fields, and two uniformisers `α`, `α'` of `L`, the classes
`𝒜` of the lists of residual polynomials at `α` and at `α'` agree. -/
lemma residualPolynomialClass_eq_of_irreducible_of_charZero (hKL : IsTotallyRamified K L)
    (hα : Irreducible α) (hα' : Irreducible α') :
    residualPolynomialClass K (ramificationPolynomial (minpoly K (α' : L)) (α' : L)) α' =
      residualPolynomialClass K (ramificationPolynomial (minpoly K (α : L)) (α : L)) α := by
  have hfin : FiniteDimensional K L :=
    finite_of_valuativeExtension K L
  exact residualPolynomialClass_eq_of_irreducible hKL hα hα'

end CharZero

end IsNonarchimedeanLocalField
