import LeanBridge.ForMathlib.NumberTheory.ModularForms.GaloisAction.CharPoly
import LeanBridge.ForMathlib.NumberTheory.ModularForms.GaloisAction.Division
import LeanBridge.ForMathlib.NumberTheory.ModularForms.GaloisAction.LevelOne

/-!
# Conjugating a modular form by a field automorphism through a primitive element

Let `σ` be a field endomorphism of `ℂ`, and `𝒢 ≤ SL₂(ℤ)` a group of finite index containing the
translation `T`. Suppose that `θ` is a primitive element for `𝒢`, a modular form of level `𝒢` with
distinct translates by `𝒢 \ SL₂(ℤ)`, and that the series `σ(θ)` is the `q`-expansion of a modular
form `θ'` of level `𝒢` and the same weight. Then the series `σ(f)` is the `q`-expansion of a modular
form of level `𝒢`, for every modular form `f` of level `𝒢`, and of a cusp form if `f` is one.

The point is that level one is stable under `σ`
(`TauCeti.GaloisAction.exists_qExpansion_eq_map_levelOne`), and that `f` is algebraic over level one
in two ways. It is a polynomial in `θ` with coefficients in the fractions of level one forms, with a
denominator `D`, the discriminant of `θ`: so `σ(f)` is a meromorphic form, the same polynomial with
`σ` applied to its coefficients, evaluated at `θ'`. It is a root of a monic polynomial over level
one, its characteristic polynomial: so `σ(f)` is a root of a monic polynomial over level one too, is
therefore bounded where the denominator vanishes and at the cusps, and is a holomorphic form.

This argument works in every weight. It needs no Eichler–Shimura isomorphism. What it does need is
a primitive element `θ` whose conjugate `σ(θ)` is known to be modular: this is a real condition,
false for general noncongruence subgroups, and it comes from Eisenstein series at the congruence
subgroups.

## Main definitions

* `TauCeti.GaloisAction.ConjData`: conjugates under `σ` of the level one forms attached to `f`.
* `TauCeti.GaloisAction.ConjData.num`: the numerator of the conjugate of `f`.

## Main results

* `TauCeti.GaloisAction.exists_modularForm_qExpansion_eq_map`: the conjugate of a modular form by
  `σ`, given a primitive element with a conjugate, which is a cusp form if the form is one.
-/

open UpperHalfPlane ModularForm SlashInvariantForm Filter

open scoped MatrixGroups Topology

namespace TauCeti.GaloisAction

variable (σ : ℂ →+* ℂ) {𝒢 : Subgroup (GL (Fin 2) ℝ)} {w k K : ℤ} {a : ℍ → ℂ}

local notation "𝒬" => 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ

lemma IsForm.exists_qExpansion_eq_map (ha : IsForm 𝒮ℒ w a) :
    ∃ a', IsForm 𝒮ℒ w a' ∧ qExpansion 1 a' = PowerSeries.map σ (qExpansion 1 a) := by
  rcases ha with ⟨g, rfl⟩
  rcases exists_qExpansion_eq_map_levelOne σ g with ⟨g', hg'⟩
  exact ⟨g', isForm_coe g', hg'⟩

lemma IsForm.eq_zero_of_qExpansion_eq_zero (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) (ha : IsForm 𝒢 w a)
    (h : qExpansion 1 a = 0) : a = 0 := by
  rcases ha with ⟨g, rfl⟩
  rw [(ModularForm.qExpansion_eq_zero_iff one_pos h1 g).mp h]
  rfl

variable [𝒢.HasDetOne] [𝒢.IsFiniteRelIndex 𝒮ℒ]

/-- Conjugates under a field endomorphism `σ` of `ℂ` of the level one forms attached to modular
forms `f` and `θ` of level `𝒢`: of the discriminant of `θ`, of the forms expressing `f` as a
polynomial in `θ`, and of the coefficients of the characteristic polynomial of `f`. Such conjugates
exist, as level one is stable under `σ`. -/
structure ConjData (f : ModularForm 𝒢 k) (θ : ModularForm 𝒢 K) where
  /-- The conjugate of the discriminant of `θ`. -/
  den : ℍ → ℂ
  isForm_den : IsForm 𝒮ℒ (discWeight 𝒢 K) den
  qExpansion_den : qExpansion 1 den = PowerSeries.map σ (qExpansion 1 (discForm θ))
  /-- The conjugates of the forms expressing `f` as a polynomial in `θ`. -/
  cramer : Fin (Nat.card 𝒬) → ℍ → ℂ
  isForm_cramer (j : Fin (Nat.card 𝒬)) :
    IsForm 𝒮ℒ (discWeight 𝒢 K + k - (j : ℕ) * K) (cramer j)
  qExpansion_cramer (j : Fin (Nat.card 𝒬)) :
    qExpansion 1 (cramer j) = PowerSeries.map σ (qExpansion 1 (cramerForm f θ j))
  /-- The conjugates of the coefficients of the characteristic polynomial of `f`. -/
  esymm : ℕ → ℍ → ℂ
  isForm_esymm (j : ℕ) : IsForm 𝒮ℒ (j * k) (esymm j)
  qExpansion_esymm (j : ℕ) :
    qExpansion 1 (esymm j) = PowerSeries.map σ (qExpansion 1 (esymmForm f j))
  esymm_zero : esymm 0 = 1

lemma nonempty_conjData (f : ModularForm 𝒢 k) (θ : ModularForm 𝒢 K) :
    Nonempty (ConjData σ f θ) := by
  rcases (isForm_discForm θ).exists_qExpansion_eq_map σ with ⟨D', hD', hQD'⟩
  choose r' hr' hQr' using fun j ↦ (isForm_cramerForm f θ j).exists_qExpansion_eq_map σ
  have hc (j : ℕ) : ∃ c', IsForm 𝒮ℒ (j * k) c' ∧
      qExpansion 1 c' = PowerSeries.map σ (qExpansion 1 (esymmForm f j)) ∧ (j = 0 → c' = 1) := by
    rcases eq_or_ne j 0 with rfl | hj
    · refine ⟨1, by simpa using isForm_one, ?_, fun _ ↦ rfl⟩
      rw [esymmForm_zero, qExpansion_one, map_one]
    · rcases (isForm_esymmForm f j).exists_qExpansion_eq_map σ with ⟨c', hc', hQc'⟩
      exact ⟨c', hc', hQc', fun h ↦ absurd h hj⟩
  choose c' hc' hQc' h0 using hc
  exact ⟨⟨D', hD', hQD', r', hr', hQr', c', hc', hQc', h0 0 rfl⟩⟩

variable {σ} {f : ModularForm 𝒢 k} {θ θ' : ModularForm 𝒢 K} (C : ConjData σ f θ) {F : ℍ → ℂ}

lemma hasQExpansion_of_isForm_levelOne (ha : IsForm 𝒮ℒ w a) : HasQExpansion a :=
  ha.hasQExpansion one_mem_strictPeriods_SL

/-- The numerator: the polynomial expressing `f` in `θ`, with its coefficients conjugated, evaluated
at the conjugate of `θ`. -/
noncomputable def ConjData.num (y : ℍ → ℂ) : ℍ → ℂ :=
  ∑ j, C.cramer j * y ^ (j : ℕ)

lemma qExpansion_mul_eq_sum {n : ℕ} {D x y : ℍ → ℂ} {r : Fin n → ℍ → ℂ} (hD : HasQExpansion D)
    (hx : HasQExpansion x) (hy : HasQExpansion y) (hr : ∀ j, HasQExpansion (r j))
    (h : D * x = ∑ j, r j * y ^ (j : ℕ)) :
    qExpansion 1 D * qExpansion 1 x = ∑ j, qExpansion 1 (r j) * qExpansion 1 y ^ (j : ℕ) := by
  rw [← qExpansion_mul hD hx, h, qExpansion_sum_of_hasQExpansion fun j _ ↦ (hr j).mul (hy.pow _)]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [qExpansion_mul (hr j) (hy.pow _), hy.qExpansion_pow]

lemma discForm_mul_slash (δ : SL(2, ℤ)) :
    discForm θ * (⇑f ∣[k] δ) = ∑ j, cramerForm f θ j * (⇑θ ∣[K] δ) ^ (j : ℕ) := by
  ext τ
  have h : discForm θ τ * quotientFunc f (cosetOf 𝒢 δ) τ =
      ∑ j, cramerForm f θ j τ * quotientFunc θ (cosetOf 𝒢 δ) τ ^ (j : ℕ) :=
    discForm_mul_quotientFunc f θ τ (cosetOf 𝒢 δ)
  rw [quotientFunc_cosetOf, quotientFunc_cosetOf] at h
  simpa using h

lemma qExpansion_den_mul {y y' x : ℍ → ℂ} (hy : HasQExpansion y) (hy' : HasQExpansion y')
    (hyy' : qExpansion 1 y' = PowerSeries.map σ (qExpansion 1 y)) (hx : HasQExpansion x)
    (hrel : discForm θ * x = ∑ j, cramerForm f θ j * y ^ (j : ℕ)) :
    qExpansion 1 (C.num y') = qExpansion 1 C.den * PowerSeries.map σ (qExpansion 1 x) := by
  have h₁ : qExpansion 1 (discForm θ) * qExpansion 1 x =
      ∑ j, qExpansion 1 (cramerForm f θ j) * qExpansion 1 y ^ (j : ℕ) :=
    qExpansion_mul_eq_sum (hasQExpansion_of_isForm_levelOne (isForm_discForm θ)) hx hy
      (fun j ↦ hasQExpansion_of_isForm_levelOne (isForm_cramerForm f θ j)) hrel
  have h₂ : PowerSeries.map σ (qExpansion 1 (discForm θ) * qExpansion 1 x) = PowerSeries.map σ
      (∑ j, qExpansion 1 (cramerForm f θ j) * qExpansion 1 y ^ (j : ℕ)) := by
    rw [h₁]
  rw [map_mul, map_sum, ← C.qExpansion_den] at h₂
  rw [h₂, ConjData.num, qExpansion_sum_of_hasQExpansion fun j _ ↦
    (hasQExpansion_of_isForm_levelOne (C.isForm_cramer j)).mul (hy'.pow _)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [qExpansion_mul (hasQExpansion_of_isForm_levelOne (C.isForm_cramer j)) (hy'.pow _),
    hy'.qExpansion_pow, map_mul, map_pow, ← hyy', ← C.qExpansion_cramer]

lemma qExpansion_den_ne_zero (hθ : ∀ q q' : 𝒬, q ≠ q' → quotientFunc θ q ≠ quotientFunc θ q') :
    qExpansion 1 C.den ≠ 0 := by
  rw [C.qExpansion_den]
  intro h
  refine discForm_ne_zero θ hθ <| (isForm_discForm θ).eq_zero_of_qExpansion_eq_zero
    one_mem_strictPeriods_SL ?_
  ext n
  simpa using congrArg (PowerSeries.coeff n) h

lemma den_ne_zero (hθ : ∀ q q' : 𝒬, q ≠ q' → quotientFunc θ q ≠ quotientFunc θ q') : C.den ≠ 0 :=
  fun h ↦ qExpansion_den_ne_zero C hθ <| by rw [h, qExpansion_zero]

lemma sum_qExpansion_esymmForm_eq_zero (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) :
    ∑ j ∈ Finset.range (Nat.card 𝒬 + 1), ((-1) ^ j : ℂ) •
      (qExpansion 1 (esymmForm f j) * qExpansion 1 f ^ (Nat.card 𝒬 - j)) = 0 := by
  have hf : HasQExpansion f := (isForm_coe f).hasQExpansion h1
  have hc (j : ℕ) : HasQExpansion (esymmForm f j) :=
    hasQExpansion_of_isForm_levelOne (isForm_esymmForm f j)
  have h : qExpansion 1 (∑ j ∈ Finset.range (Nat.card 𝒬 + 1),
      ((-1) ^ j : ℂ) • (esymmForm f j * ⇑f ^ (Nat.card 𝒬 - j))) = qExpansion 1 (0 : ℍ → ℂ) := by
    rw [sum_esymmForm_smul_mul_pow_eq_zero]
  rw [qExpansion_sum_of_hasQExpansion fun j _ ↦ ((hc j).mul (hf.pow _)).smul _,
    qExpansion_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [qExpansion_smul ((hc j).mul (hf.pow _)), qExpansion_mul (hc j) (hf.pow _), hf.qExpansion_pow]

lemma ConjData.isIntegralQuotient (h𝒢 : 𝒢 ≤ 𝒮ℒ) (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods)
    (hθ : ∀ q q' : 𝒬, q ≠ q' → quotientFunc θ q ≠ quotientFunc θ q')
    (hθ' : qExpansion 1 θ' = PowerSeries.map σ (qExpansion 1 θ)) :
    IsIntegralQuotient 𝒢 (discWeight 𝒢 K) k (Nat.card 𝒬) C.esymm (C.num θ') C.den := by
  have hA : IsForm 𝒢 (discWeight 𝒢 K + k) (C.num θ') := IsForm.sum fun j _ ↦
    (((C.isForm_cramer j).restrict h𝒢).mul ((isForm_coe θ').pow j)).cast (by ring1)
  have hDr : IsForm 𝒢 (discWeight 𝒢 K) C.den := C.isForm_den.restrict h𝒢
  refine ⟨hA, C.isForm_den, den_ne_zero C hθ, C.isForm_esymm, C.esymm_zero, fun τ ↦ ?_⟩
  have hH : IsForm 𝒢 ((Nat.card 𝒬 : ℤ) * (discWeight 𝒢 K + k))
      (∑ j ∈ Finset.range (Nat.card 𝒬 + 1), ((-1) ^ j : ℂ) •
        (C.esymm j * C.num θ' ^ (Nat.card 𝒬 - j) * C.den ^ j)) := IsForm.sum fun j hj ↦ by
    refine (((((C.isForm_esymm j).restrict h𝒢).mul (hA.pow _)).mul (hDr.pow j)).cast ?_).smul _
    have hj' : j ≤ Nat.card 𝒬 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Nat.cast_sub hj']
    ring1
  have hf : HasQExpansion f := (isForm_coe f).hasQExpansion h1
  have hAq : HasQExpansion (C.num θ') := hA.hasQExpansion h1
  have hDq : HasQExpansion C.den := hDr.hasQExpansion h1
  have hcq (j : ℕ) : HasQExpansion (C.esymm j) :=
    hasQExpansion_of_isForm_levelOne (C.isForm_esymm j)
  have hQA : qExpansion 1 (C.num θ') = qExpansion 1 C.den * PowerSeries.map σ (qExpansion 1 f) :=
    qExpansion_den_mul C ((isForm_coe θ).hasQExpansion h1) ((isForm_coe θ').hasQExpansion h1) hθ' hf
      (by simpa using discForm_mul_slash (f := f) (θ := θ) 1)
  have hQ : qExpansion 1 (∑ j ∈ Finset.range (Nat.card 𝒬 + 1), ((-1) ^ j : ℂ) •
      (C.esymm j * C.num θ' ^ (Nat.card 𝒬 - j) * C.den ^ j)) = 0 := by
    have h₀ : PowerSeries.map σ (∑ j ∈ Finset.range (Nat.card 𝒬 + 1), ((-1) ^ j : ℂ) •
        (qExpansion 1 (esymmForm f j) * qExpansion 1 f ^ (Nat.card 𝒬 - j))) =
          PowerSeries.map σ 0 := by
      rw [sum_qExpansion_esymmForm_eq_zero h1]
    rw [map_sum, map_zero] at h₀
    rw [qExpansion_sum_of_hasQExpansion fun j _ ↦
      (((hcq j).mul (hAq.pow _)).mul (hDq.pow _)).smul _,
      ← mul_zero (qExpansion 1 C.den ^ Nat.card 𝒬), ← h₀, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' : Nat.card 𝒬 - j + j = Nat.card 𝒬 :=
      Nat.sub_add_cancel (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    rw [qExpansion_smul (((hcq j).mul (hAq.pow _)).mul (hDq.pow _)),
      qExpansion_mul ((hcq j).mul (hAq.pow _)) (hDq.pow _), qExpansion_mul (hcq j) (hAq.pow _),
      hAq.qExpansion_pow, hDq.qExpansion_pow, hQA, C.qExpansion_esymm, map_smul_powerSeries,
      map_mul, map_pow, map_pow, map_neg, map_one, mul_pow]
    nth_rw 3 [← hj']
    rw [pow_add]
    simp only [mul_smul_comm]
    congr 1
    ring1
  have hzero : ∑ j ∈ Finset.range (Nat.card 𝒬 + 1), ((-1) ^ j : ℂ) •
      (C.esymm j * C.num θ' ^ (Nat.card 𝒬 - j) * C.den ^ j) = 0 :=
    hH.eq_zero_of_qExpansion_eq_zero h1 hQ
  simpa using congrFun hzero τ

lemma ConjData.den_mul_slash (hF : ∀ τ, C.den τ * F τ = C.num θ' τ) (δ : SL(2, ℤ)) :
    C.den * (F ∣[k] δ) = C.num (⇑θ' ∣[K] δ) := by
  have hfun : C.den * F = C.num θ' := funext hF
  have h₁ : (C.den * F) ∣[discWeight 𝒢 K + k] δ = C.den ∣[discWeight 𝒢 K] δ * F ∣[k] δ :=
    mul_slash_SL2 (discWeight 𝒢 K) k δ C.den F
  rw [hfun, C.isForm_den.slash_eq] at h₁
  rw [← h₁, ConjData.num, SlashAction.sum_slash, ConjData.num]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hw : discWeight 𝒢 K + k = (discWeight 𝒢 K + k - (j : ℕ) * K) + (j : ℕ) * K := by ring1
  rw [hw, mul_slash_SL2, (C.isForm_cramer j).slash_eq, pow_slash]

lemma ConjData.qExpansion_slash_eq_map
    (hθ : ∀ q q' : 𝒬, q ≠ q' → quotientFunc θ q ≠ quotientFunc θ q')
    (hF : ∀ τ, C.den τ * F τ = C.num θ' τ) {δ : SL(2, ℤ)} (hfδ : HasQExpansion (⇑f ∣[k] δ))
    (hθδ : HasQExpansion (⇑θ ∣[K] δ)) (hθ'δ : HasQExpansion (⇑θ' ∣[K] δ))
    (hFδ : HasQExpansion (F ∣[k] δ))
    (hδ : qExpansion 1 (⇑θ' ∣[K] δ) = PowerSeries.map σ (qExpansion 1 (⇑θ ∣[K] δ))) :
    qExpansion 1 (F ∣[k] δ) = PowerSeries.map σ (qExpansion 1 (⇑f ∣[k] δ)) := by
  refine mul_left_cancel₀ (qExpansion_den_ne_zero C hθ) ?_
  rw [← qExpansion_den_mul C hθδ hθ'δ hδ hfδ (discForm_mul_slash δ), ← C.den_mul_slash hF δ,
    qExpansion_mul (hasQExpansion_of_isForm_levelOne C.isForm_den) hFδ]

variable (f) in
/-- **The conjugate of a modular form by a field endomorphism of `ℂ`, given a primitive element with
a conjugate.** Let `𝒢 ≤ SL₂(ℤ)` be an arithmetic group containing the translation `T`, `σ` a field
endomorphism of `ℂ`, and `θ` a modular form of level `𝒢` with distinct translates by `𝒢 \ SL₂(ℤ)`
such that the series `σ(θ)` is the `q`-expansion of a modular form `θ'` of level `𝒢`. Then for every
modular form `f` of level `𝒢` and weight `k`, the series `σ(f)` is the `q`-expansion of a modular
form `F` of level `𝒢` and weight `k`. If `f` is a cusp form, so is `F`. And the construction is
compatible with the translates: if `σ(θ ∣ δ)` is the `q`-expansion of `θ' ∣ δ` for some
`δ ∈ SL₂(ℤ)`, and all these translates have `q`-expansions at period one, then `σ(f ∣ δ)` is the
`q`-expansion of `F ∣ δ`. -/
lemma exists_modularForm_qExpansion_eq_map [𝒢.IsArithmetic] (h𝒢 : 𝒢 ≤ 𝒮ℒ)
    (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods)
    (hθ : ∀ q q' : 𝒬, q ≠ q' → quotientFunc θ q ≠ quotientFunc θ q')
    (hθ' : qExpansion 1 θ' = PowerSeries.map σ (qExpansion 1 θ)) : ∃ F : ModularForm 𝒢 k,
      qExpansion 1 F = PowerSeries.map σ (qExpansion 1 f) ∧
      (IsCuspForm 𝒢 k f → IsCuspForm 𝒢 k F) ∧ ∀ δ : SL(2, ℤ), HasQExpansion (⇑f ∣[k] δ) →
        HasQExpansion (⇑θ ∣[K] δ) → HasQExpansion (⇑θ' ∣[K] δ) → HasQExpansion (⇑F ∣[k] δ) →
        qExpansion 1 (⇑θ' ∣[K] δ) = PowerSeries.map σ (qExpansion 1 (⇑θ ∣[K] δ)) →
        qExpansion 1 (⇑F ∣[k] δ) = PowerSeries.map σ (qExpansion 1 (⇑f ∣[k] δ)) := by
  rcases nonempty_conjData σ f θ with ⟨C⟩
  have hI : IsIntegralQuotient 𝒢 (discWeight 𝒢 K) k (Nat.card 𝒬) C.esymm (C.num θ') C.den :=
    C.isIntegralQuotient h𝒢 h1 hθ hθ'
  rcases hI.exists_modularForm h𝒢 with ⟨F, hF⟩
  refine ⟨F, ?_, fun hfc ↦ hI.isCuspForm hF fun j hj ↦ ?_, fun δ hfδ hθδ hθ'δ hFδ hδ ↦
    C.qExpansion_slash_eq_map hθ hF hfδ hθδ hθ'δ hFδ hδ⟩
  · simpa using C.qExpansion_slash_eq_map hθ hF (δ := 1)
      (by simpa using (isForm_coe f).hasQExpansion h1)
      (by simpa using (isForm_coe θ).hasQExpansion h1)
      (by simpa using (isForm_coe θ').hasQExpansion h1)
      (by simpa using (isForm_coe F).hasQExpansion h1) (by simpa using hθ')
  · rcases isCuspForm_esymmForm f hfc hj with ⟨g, hg⟩
    rcases C.isForm_esymm j with ⟨g', hg'⟩
    have h₀ : (qExpansion 1 (C.esymm j)).coeff 0 = 0 := by
      rw [C.qExpansion_esymm, PowerSeries.coeff_map, ← hg,
        CuspFormClass.qExpansion_coeff_zero g one_pos one_mem_strictPeriods_SL, map_zero]
    have hlim : Tendsto g' atImInfty (𝓝 ((qExpansion 1 g').coeff 0)) :=
      ModularFormClass.tendsto_atImInfty g' one_pos one_mem_strictPeriods_SL
    rwa [hg', h₀] at hlim

end TauCeti.GaloisAction
