import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.SecondMoment

/-!
# The multiplicativity of the coefficients of a Bianchi newform

Let `K` be an imaginary quadratic field of class number `1`, embedded in `ℂ` by `σ`, and `F` a
Bianchi newform of weight `k ≥ 1` and level `𝔑`, with Hecke eigenvalues `a_𝔭` and coefficients
`c(𝔞)` at the nonzero ideals of `𝒪_K`. At every prime `𝔭`, dividing the level or not, the Hecke
relation is
`a_𝔭 c(𝔞) = c(𝔭𝔞) + w(𝔭) c(𝔞 / 𝔭)`, where `w(𝔭) = N(𝔭)^{k/2}` for `𝔭 ∤ 𝔑` and `w(𝔭) = 0` for
`𝔭 ∣ 𝔑` (`HyperbolicThreeSpace.BianchiNewformOfWeight.heckeWeight`). So the coefficients are
multiplicative (`HyperbolicThreeSpace.BianchiNewformOfWeight.idealCoeff_mul`) and real
(`HyperbolicThreeSpace.BianchiNewformOfWeight.conj_idealCoeff`), and they satisfy the recursion at
the powers of a prime (`HyperbolicThreeSpace.BianchiNewformOfWeight.idealCoeff_pow_add_two`).

## Main definitions

* `HyperbolicThreeSpace.BianchiNewformOfWeight.heckeWeight`: the weight of the Hecke relation at a
  prime.

## Main results

* `HyperbolicThreeSpace.BianchiNewformOfWeight.eigenvalue_mul_coeff`: the Hecke relation at every
  prime.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.idealCoeff_mul`: the coefficients are multiplicative.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.conj_idealCoeff`: the coefficients are real.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.idealCoeff_pow_add_two`: the recursion at the powers
  of a prime.
-/

open Complex Module NumberField

open Submodule (IsPrincipal)

open scoped ComplexConjugate

namespace HyperbolicThreeSpace.BianchiNewformOfWeight

lemma mul_span_eq {R : Type*} [CommRing R] [IsPrincipalIdealRing R] {𝔭 : Ideal R} (a : R) :
    𝔭 * Ideal.span {a} = Ideal.span {IsPrincipal.generator 𝔭 * a} := by
  conv_lhs => rw [← Ideal.span_singleton_generator 𝔭]
  exact Ideal.span_singleton_mul_span_singleton _ _

variable {K : Type*} [Field K] [NumberField K] {k : ℕ} {𝔑 𝔞 𝔟 : Ideal (𝓞 K)}

open scoped Classical in
variable (k 𝔑) in
/-- The weight of the Hecke relation at a prime `𝔭`: `w(𝔭) = N(𝔭)^{k/2}` for `𝔭 ∤ 𝔑`, and
`w(𝔭) = 0` for `𝔭 ∣ 𝔑`, the coefficient of `X²` in the local factor `1 - a_𝔭 X + w(𝔭) X²` of the
L-function of a newform. -/
noncomputable def heckeWeight (𝔭 : Ideal (𝓞 K)) : ℂ :=
  if 𝔑 ≤ 𝔭 then 0 else (Ideal.absNorm 𝔭 : ℂ) ^ (k / 2)

lemma heckeWeight_of_le {𝔭 : Ideal (𝓞 K)} (h : 𝔑 ≤ 𝔭) : heckeWeight k 𝔑 𝔭 = 0 :=
  ite_eq_left h

lemma heckeWeight_of_not_le {𝔭 : Ideal (𝓞 K)} (h : ¬𝔑 ≤ 𝔭) :
    heckeWeight k 𝔑 𝔭 = (Ideal.absNorm 𝔭 : ℂ) ^ (k / 2) :=
  ite_eq_right h

lemma conj_heckeWeight (𝔭 : Ideal (𝓞 K)) : conj (heckeWeight k 𝔑 𝔭) = heckeWeight k 𝔑 𝔭 := by
  by_cases h : 𝔑 ≤ 𝔭
  · rw [heckeWeight_of_le h, map_zero]
  · rw [heckeWeight_of_not_le h, map_pow, map_natCast]

lemma absNorm_lt_absNorm_mul {𝔭 𝔠 : Ideal (𝓞 K)} (h𝔭 : 𝔭.IsMaximal) (h𝔭₀ : 𝔭 ≠ ⊥) (h𝔠 : 𝔠 ≠ ⊥) :
    Ideal.absNorm 𝔠 < Ideal.absNorm (𝔭 * 𝔠) := by
  have hP : Ideal.absNorm 𝔭 ≠ 1 := fun h ↦ h𝔭.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hP₀ : Ideal.absNorm 𝔭 ≠ 0 := (Ideal.absNorm_eq_zero_iff).not.mpr h𝔭₀
  rw [map_mul]
  exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero ((Ideal.absNorm_eq_zero_iff).not.mpr h𝔠))
    (by omega)

variable [IsPrincipalIdealRing (𝓞 K)] [IsTotallyComplex K] {σ : K →+* ℂ} [NeZero 𝔑]
  (N : BianchiNewformOfWeight σ k 𝔑) {α : 𝓞 K}

lemma eigenvalue_mul_coeff_eq_of_le (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (h𝔑𝔭 : 𝔑 ≤ 𝔭.1) (hα : α ≠ 0) :
    N.eigenvalue 𝔭 * N.coeff α = N.coeff (IsPrincipal.generator 𝔭.1 * α) := by
  rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
  have h₁ : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
      (extend (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭.1 𝔭.2.2
        ⟨N.toFun, bianchiNewSubspace_le σ k 𝔑 N.mem_bianchiNewSubspace⟩))
      (bianchiCoeffHecke σ k (IsPrincipal.generator 𝔭.1) (Ideal.absNorm 𝔭.1) 0 N.coeff) :=
    hasBianchiWhittakerExpansion_bianchiHeckeTPrimeCusp_of_le hK hk (N.even hK) 𝔭.2.2 𝔭.2.1 h𝔑𝔭 _
      N.hasWhittakerExpansion
  have hT : (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭.1 𝔭.2.2
      ⟨N.toFun, bianchiNewSubspace_le σ k 𝔑 N.mem_bianchiNewSubspace⟩ :
        HyperbolicThreeSpace → Fin (k + 1) → ℂ) =
      (((((Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ)⁻¹ * N.eigenvalue 𝔭) • N.toFun) :=
    congrArg Subtype.val (N.coe_bianchiHeckeTPrimeCusp_toFun hK 𝔭)
  rw [hT] at h₁
  have h₂ : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
      (extend (((((Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ)⁻¹ * N.eigenvalue 𝔭) •
        N.toFun))
      (((((Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ)⁻¹ * N.eigenvalue 𝔭) • N.coeff) :=
    N.hasWhittakerExpansion.smul _
  have h₃ : (((((Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ)⁻¹ * N.eigenvalue 𝔭) •
      N.coeff) α = bianchiCoeffHecke σ k (IsPrincipal.generator 𝔭.1) (Ideal.absNorm 𝔭.1) 0
        N.coeff α :=
    h₂.coeff_eq hK hx (cpow_ofNat_inv_pow _ 2) h₁ hα
  have hr : (((Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ) ≠ 0 := absNorm_rpow_ne_zero 𝔭
  have ht : 0 < ‖σ ((IsPrincipal.generator 𝔭.1 : 𝓞 K) : K)‖ :=
    norm_pos_iff.mpr ((map_ne_zero σ).mpr (RingOfIntegers.coe_ne_zero_iff.mpr
      (generator_ne_zero 𝔭.2.2)))
  have hfac : (Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) * (Ideal.absNorm 𝔭.1 : ℝ) *
      (‖σ ((IsPrincipal.generator 𝔭.1 : 𝓞 K) : K)‖ ^ (k / 2 + 1))⁻¹ = 1 := by
    rcases N.even hK with ⟨m, hm⟩
    have e : ((2 : ℕ) : ℝ) * (((k : ℝ) - 2) / 4) + ((2 : ℕ) : ℝ) + -((k / 2 + 1 : ℕ) : ℝ) = 0 := by
      have e₁ : k / 2 = m := by
        omega
      rw [e₁, hm]
      push_cast
      ring1
    rw [← sq_norm_generator σ hK 𝔭.1, ← Real.rpow_natCast _ 2, ← Real.rpow_mul ht.le,
      ← Real.rpow_natCast _ (k / 2 + 1), ← Real.rpow_neg ht.le, ← Real.rpow_add ht,
      ← Real.rpow_add ht, e, Real.rpow_zero]
  simp only [Pi.smul_apply, smul_eq_mul, bianchiCoeffHecke, zero_mul, add_zero] at h₃
  have hfac' : (((Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) *
      ((‖σ ((IsPrincipal.generator 𝔭.1 : 𝓞 K) : K)‖ ^ (k / 2 + 1))⁻¹ : ℝ) = 1 := by
    exact_mod_cast hfac
  have h₄ : N.eigenvalue 𝔭 * N.coeff α =
      ((((Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ) *
        (((((Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ)⁻¹ * N.eigenvalue 𝔭) *
          N.coeff α)) := by
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hr, one_mul]
  rw [h₄, h₃, ← mul_assoc, ← mul_assoc, hfac', one_mul]

/-- **The Hecke relation at every prime** (LMFDB `mf.bianchi.newform`): for `𝔭 = (ϖ)` and `α ≠ 0`,
`a_𝔭 c(α) = c(ϖα) + w(𝔭) c(α / ϖ)`, where `c(α / ϖ) = 0` unless `ϖ ∣ α`. -/
lemma eigenvalue_mul_coeff (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (hα : α ≠ 0) : N.eigenvalue 𝔭 * N.coeff α =
    N.coeff (IsPrincipal.generator 𝔭.1 * α) +
      heckeWeight k 𝔑 𝔭.1 * Function.extend (IsPrincipal.generator 𝔭.1 * ·) N.coeff 0 α := by
  by_cases h : 𝔑 ≤ 𝔭.1
  · rw [N.eigenvalue_mul_coeff_eq_of_le hK hk 𝔭 h hα, heckeWeight_of_le h, zero_mul, add_zero]
  · rw [N.eigenvalue_mul_coeff_eq 𝔭 hK h hα, heckeWeight_of_not_le h]

lemma idealCoeff_mul_of_not_le (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (h𝔞 : 𝔞 ≠ ⊥) (h : ¬𝔞 ≤ 𝔭.1) :
    N.idealCoeff (𝔭.1 * 𝔞) = N.eigenvalue 𝔭 * N.idealCoeff 𝔞 := by
  rcases (IsPrincipalIdealRing.principal 𝔞).principal with ⟨a, rfl⟩
  have ha : a ≠ 0 := fun h₀ ↦ h𝔞 (by simp [h₀])
  have hp : IsPrincipal.generator 𝔭.1 ≠ 0 := generator_ne_zero 𝔭.2.2
  have hnd : ¬IsPrincipal.generator 𝔭.1 ∣ a := fun hd ↦ h <| by
    conv_rhs => rw [← Ideal.span_singleton_generator 𝔭.1]
    exact Ideal.span_singleton_le_span_singleton.mpr hd
  have e : (Submodule.span (𝓞 K) {a} : Ideal (𝓞 K)) = Ideal.span {a} :=
    rfl
  rw [e, mul_span_eq, N.idealCoeff_span hK (mul_ne_zero hp ha), N.idealCoeff_span hK ha,
    N.eigenvalue_mul_coeff hK hk 𝔭 ha, extend_mul_of_not_dvd hnd, mul_zero, add_zero]

lemma idealCoeff_mul_mul (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (h𝔞 : 𝔞 ≠ ⊥) : N.idealCoeff (𝔭.1 * (𝔭.1 * 𝔞)) =
    N.eigenvalue 𝔭 * N.idealCoeff (𝔭.1 * 𝔞) - heckeWeight k 𝔑 𝔭.1 * N.idealCoeff 𝔞 := by
  rcases (IsPrincipalIdealRing.principal 𝔞).principal with ⟨a, rfl⟩
  have ha : a ≠ 0 := fun h₀ ↦ h𝔞 (by simp [h₀])
  have hp : IsPrincipal.generator 𝔭.1 ≠ 0 := generator_ne_zero 𝔭.2.2
  have e : (Submodule.span (𝓞 K) {a} : Ideal (𝓞 K)) = Ideal.span {a} :=
    rfl
  rw [e, mul_span_eq, mul_span_eq, N.idealCoeff_span hK (mul_ne_zero hp (mul_ne_zero hp ha)),
    N.idealCoeff_span hK (mul_ne_zero hp ha), N.idealCoeff_span hK ha,
    N.eigenvalue_mul_coeff hK hk 𝔭 (mul_ne_zero hp ha), extend_mul_apply hp, add_sub_cancel_right]

/-- **The coefficients of a Bianchi newform are multiplicative** (LMFDB `mf.bianchi.newform`):
`c(𝔞𝔟) = c(𝔞) c(𝔟)` for coprime nonzero ideals `𝔞` and `𝔟`, by the Hecke relation. -/
lemma idealCoeff_mul (hK : finrank ℚ K = 2) (hk : k ≠ 0) (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥)
    (hc : IsCoprime 𝔞 𝔟) : N.idealCoeff (𝔞 * 𝔟) = N.idealCoeff 𝔞 * N.idealCoeff 𝔟 := by
  induction hn : Ideal.absNorm 𝔞 using Nat.strong_induction_on generalizing 𝔞 with
  | _ m ih =>
    by_cases htop : 𝔞 = ⊤
    · rw [htop, Ideal.top_mul, N.idealCoeff_top hK, one_mul]
    rcases Ideal.exists_le_maximal 𝔞 htop with ⟨𝔭, h𝔭, h𝔞𝔭⟩
    have h𝔭₀ : 𝔭 ≠ ⊥ := fun h ↦ h𝔞 (le_bot_iff.mp (h ▸ h𝔞𝔭))
    have h𝔟𝔭 : ¬𝔟 ≤ 𝔭 := fun h ↦ h𝔭.ne_top (top_unique
      ((Ideal.isCoprime_iff_sup_eq.mp hc).symm.le.trans (sup_le h𝔞𝔭 h)))
    rcases Ideal.dvd_iff_le.mpr h𝔞𝔭 with ⟨𝔞', rfl⟩
    have h𝔞' : 𝔞' ≠ ⊥ := right_ne_zero_of_mul h𝔞
    have hlt {𝔠 : Ideal (𝓞 K)} (h𝔠 : 𝔠 ≠ ⊥) : Ideal.absNorm 𝔠 < Ideal.absNorm (𝔭 * 𝔠) :=
      absNorm_lt_absNorm_mul h𝔭 h𝔭₀ h𝔠
    rcases (⟨⟨𝔭, h𝔭.isPrime, h𝔭₀⟩, rfl⟩ : ∃ 𝔮 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, 𝔮.1 = 𝔭)
      with ⟨𝔮, h𝔮⟩
    subst h𝔮
    have hc' : IsCoprime 𝔞' 𝔟 := hc.of_mul_left_right
    by_cases h𝔞'𝔭 : 𝔞' ≤ 𝔮.1
    · rcases Ideal.dvd_iff_le.mpr h𝔞'𝔭 with ⟨𝔞'', rfl⟩
      have h𝔞'' : 𝔞'' ≠ ⊥ := right_ne_zero_of_mul h𝔞'
      have h₁ : N.idealCoeff (𝔮.1 * 𝔞'' * 𝔟) = N.idealCoeff (𝔮.1 * 𝔞'') * N.idealCoeff 𝔟 :=
        ih _ (hn ▸ hlt h𝔞') h𝔞' hc' rfl
      have h₂ : N.idealCoeff (𝔞'' * 𝔟) = N.idealCoeff 𝔞'' * N.idealCoeff 𝔟 :=
        ih _ (hn ▸ (hlt h𝔞'').trans (hlt h𝔞')) h𝔞'' hc'.of_mul_left_right rfl
      have e : 𝔮.1 * (𝔮.1 * 𝔞'') * 𝔟 = 𝔮.1 * (𝔮.1 * (𝔞'' * 𝔟)) := by
        rw [mul_assoc, mul_assoc]
      have e₂ : 𝔮.1 * (𝔞'' * 𝔟) = 𝔮.1 * 𝔞'' * 𝔟 := (mul_assoc _ _ _).symm
      rw [e, N.idealCoeff_mul_mul hK hk 𝔮 (mul_ne_zero h𝔞'' h𝔟),
        N.idealCoeff_mul_mul hK hk 𝔮 h𝔞'', e₂, h₁, h₂]
      ring1
    · have h₁ : N.idealCoeff (𝔞' * 𝔟) = N.idealCoeff 𝔞' * N.idealCoeff 𝔟 :=
        ih _ (hn ▸ hlt h𝔞') h𝔞' hc' rfl
      have hnle : ¬𝔞' * 𝔟 ≤ 𝔮.1 := fun h ↦ (𝔮.2.1.mul_le.mp h).elim h𝔞'𝔭 h𝔟𝔭
      rw [mul_assoc, N.idealCoeff_mul_of_not_le hK hk 𝔮 (mul_ne_zero h𝔞' h𝔟) hnle, h₁,
        N.idealCoeff_mul_of_not_le hK hk 𝔮 h𝔞' h𝔞'𝔭]
      ring1

/-- **The coefficients of a Bianchi newform are real** (LMFDB `mf.bianchi.newform`), in the given
embedding `σ`, by the Hecke relation, as the Hecke eigenvalues are real. -/
lemma conj_idealCoeff (hK : finrank ℚ K = 2) (hk : k ≠ 0) (h𝔞 : 𝔞 ≠ ⊥) :
    conj (N.idealCoeff 𝔞) = N.idealCoeff 𝔞 := by
  induction hn : Ideal.absNorm 𝔞 using Nat.strong_induction_on generalizing 𝔞 with
  | _ m ih =>
    by_cases htop : 𝔞 = ⊤
    · rw [htop, N.idealCoeff_top hK, map_one]
    rcases Ideal.exists_le_maximal 𝔞 htop with ⟨𝔭, h𝔭, h𝔞𝔭⟩
    have h𝔭₀ : 𝔭 ≠ ⊥ := fun h ↦ h𝔞 (le_bot_iff.mp (h ▸ h𝔞𝔭))
    rcases Ideal.dvd_iff_le.mpr h𝔞𝔭 with ⟨𝔞', rfl⟩
    have h𝔞' : 𝔞' ≠ ⊥ := right_ne_zero_of_mul h𝔞
    have hlt {𝔠 : Ideal (𝓞 K)} (h𝔠 : 𝔠 ≠ ⊥) : Ideal.absNorm 𝔠 < Ideal.absNorm (𝔭 * 𝔠) :=
      absNorm_lt_absNorm_mul h𝔭 h𝔭₀ h𝔠
    rcases (⟨⟨𝔭, h𝔭.isPrime, h𝔭₀⟩, rfl⟩ : ∃ 𝔮 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, 𝔮.1 = 𝔭)
      with ⟨𝔮, h𝔮⟩
    subst h𝔮
    have ha : conj (N.eigenvalue 𝔮) = N.eigenvalue 𝔮 := N.conj_eigenvalue hK hk 𝔮
    by_cases h𝔞'𝔭 : 𝔞' ≤ 𝔮.1
    · rcases Ideal.dvd_iff_le.mpr h𝔞'𝔭 with ⟨𝔞'', rfl⟩
      have h𝔞'' : 𝔞'' ≠ ⊥ := right_ne_zero_of_mul h𝔞'
      rw [N.idealCoeff_mul_mul hK hk 𝔮 h𝔞'', map_sub, map_mul, map_mul, ha, conj_heckeWeight,
        ih _ (hn ▸ hlt h𝔞') h𝔞' rfl, ih _ (hn ▸ (hlt h𝔞'').trans (hlt h𝔞')) h𝔞'' rfl]
    · rw [N.idealCoeff_mul_of_not_le hK hk 𝔮 h𝔞' h𝔞'𝔭, map_mul, ha, ih _ (hn ▸ hlt h𝔞') h𝔞' rfl]

/-- **The recursion at the powers of a prime** (LMFDB `mf.bianchi.newform`):
`c(𝔭^{j+2}) = a_𝔭 c(𝔭^{j+1}) - w(𝔭) c(𝔭^j)`. -/
lemma idealCoeff_pow_add_two (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (j : ℕ) : N.idealCoeff (𝔭.1 ^ (j + 2)) =
    N.eigenvalue 𝔭 * N.idealCoeff (𝔭.1 ^ (j + 1)) -
      heckeWeight k 𝔑 𝔭.1 * N.idealCoeff (𝔭.1 ^ j) := by
  have h : 𝔭.1 ^ j ≠ ⊥ := pow_ne_zero j 𝔭.2.2
  have e₁ : 𝔭.1 ^ (j + 2) = 𝔭.1 * (𝔭.1 * 𝔭.1 ^ j) := by
    ring1
  have e₂ : 𝔭.1 ^ (j + 1) = 𝔭.1 * 𝔭.1 ^ j := pow_succ' _ _
  rw [e₁, e₂, N.idealCoeff_mul_mul hK hk 𝔭 h]

lemma idealCoeff_self (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) : N.idealCoeff 𝔭.1 = N.eigenvalue 𝔭 := by
  have h : ¬(⊤ : Ideal (𝓞 K)) ≤ 𝔭.1 := fun h ↦ 𝔭.2.1.ne_top (top_unique h)
  have h₁ : N.idealCoeff (𝔭.1 * ⊤) = N.eigenvalue 𝔭 * N.idealCoeff ⊤ :=
    N.idealCoeff_mul_of_not_le hK hk 𝔭 top_ne_bot h
  rwa [Ideal.mul_top, N.idealCoeff_top hK, mul_one] at h₁

end HyperbolicThreeSpace.BianchiNewformOfWeight
