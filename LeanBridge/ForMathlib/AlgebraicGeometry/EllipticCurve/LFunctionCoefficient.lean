import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Reduction
import LeanBridge.ForMathlib.NumberTheory.Padics.HeightOneSpectrum
import TauCeti.AlgebraicGeometry.EllipticCurve.LocalPolynomial
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.OrdinaryReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Curve
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Localization
import TauCeti.RingTheory.DedekindDomain.LocalizationAtPrime

/-!
# The coefficient `a(p)` of the L-function of an elliptic curve over `ℚ`

Mathlib's `WeierstrassCurve.LFunction` is the formal Euler product, over the primes `v` of a number
field, of the local factors `1 / fᵥ(N(v)⁻ˢ)`, where `fᵥ` is `1 - aᵥ T + N(v) T²`, `1 - T`, `1 + T`
or `1` at good, split multiplicative, non-split multiplicative or additive reduction of a minimal
equation over the completion `𝓞_v` at `v`. Over `ℚ`, the prime `v` above `p` is the only prime of
norm `p`, so the coefficient of `p⁻ˢ` is the coefficient `aᵥ` of `T` in `1 / fᵥ(T)`
(`WeierstrassCurve.LFunction_apply_absNorm`), which is the Frobenius trace `p + 1 − #Ẽ(𝔽_p)` of the
reduction of a minimal equation, its singular point counted
(`WeierstrassCurve.coeff_one_localPowerSeries`, from Tau Ceti's `localPolynomial` lemmas).

The LMFDB reduces a minimal equation over `ℤ` modulo `p`, as Round ZY's reduction types do over
the local ring `𝓞_(v) = ℤ_(p)`. The trace does not change on passing to the completion
(`WeierstrassCurve.frobeniusTrace_reduction_minimal_baseChange_adicCompletion`): an equation over
`𝓞_(v)` on which Tate's algorithm stops stays a stopping equation over `𝓞_v`, since `𝓞_(v) → 𝓞_v`
preserves the valuation, so its base change is minimal there; it reduces to the same curve over the
common residue field. So `a(p)` is the trace of the reduction of a minimal equation over `ℤ_(p)`
(`WeierstrassCurve.LFunction_apply_absNorm_eq_frobeniusTrace`), and Tau Ceti's computation of that
trace gives the values the knowl states: `1`, `-1` and `0` at split multiplicative, non-split
multiplicative and additive reduction, and at good reduction a multiple of `p` exactly at
supersingular reduction.

## Main results

* `WeierstrassCurve.coeff_one_localPowerSeries`: the coefficient of `T` in the local power series
  is the Frobenius trace of the reduction.
* `WeierstrassCurve.frobeniusTrace_reduction_minimal_baseChange_adicCompletion`: the trace of the
  reduction at a prime of a number field is the same over the local ring and over its completion.
* `WeierstrassCurve.LFunction_apply_absNorm`: over `ℚ`, the coefficient of `L(E, s)` at the norm
  `p` of a prime `v` is the coefficient of `T` in the local power series at `v`.
* `WeierstrassCurve.LFunction_apply_absNorm_eq_frobeniusTrace` (LMFDB `ec.q.reduction_type`):
  `a(p)` is the Frobenius trace of the reduction modulo `p` of a minimal equation over `ℤ_(p)`.
* `WeierstrassCurve.LFunction_apply_absNorm_eq_one`,
  `WeierstrassCurve.LFunction_apply_absNorm_eq_neg_one` and
  `WeierstrassCurve.LFunction_apply_absNorm_eq_zero` (LMFDB `ec.q.reduction_type`): `a(p)` is `1`,
  `-1` and `0` at split multiplicative, non-split multiplicative and additive reduction.
* `WeierstrassCurve.hasGoodSupersingularReduction_iff_dvd_LFunction_apply` and
  `WeierstrassCurve.hasGoodOrdinaryReduction_iff_not_dvd_LFunction_apply` (LMFDB
  `ec.q.reduction_type`): at good reduction, `p ∣ a(p)` exactly when the reduction is supersingular,
  and `p ∤ a(p)` exactly when it is ordinary.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5 and Appendix C.16.
-/

open ArithmeticFunction IsDedekindDomain NumberField Rat HeightOneSpectrum

namespace ArithmeticFunction

variable {R : Type*} [CommSemiring R] {p : ℕ} {ι : Type*} (f : ι → ArithmeticFunction R)

lemma mul_apply_prime (hp : p.Prime) (g h : ArithmeticFunction R) :
    (g * h) p = g 1 * h p + g p * h 1 := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal fun a b ↦ g a * h b, hp.divisors,
    Finset.sum_pair hp.one_lt.ne, Nat.div_one, Nat.div_self hp.pos]

lemma prod_apply_one (hf : ∀ i, f i 1 = 1) (s : Finset ι) : (∏ i ∈ s, f i) 1 = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, mul_apply_one, hf, ih, one_mul]

lemma prod_apply_prime (hf : ∀ i, f i 1 = 1) (hp : p.Prime) (s : Finset ι) :
    (∏ i ∈ s, f i) p = ∑ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [one_apply_ne hp.ne_one]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, mul_apply_prime hp, hf, ih, prod_apply_one f hf, one_mul, mul_one,
      Finset.sum_insert hi, add_comm]

end ArithmeticFunction

namespace PowerSeries

variable {R : Type*} [CommRing R]

lemma coeff_one_invOfUnit_one (φ : R⟦X⟧) (h : constantCoeff φ = 1) :
    coeff 1 (invOfUnit φ 1) = -coeff 1 φ := by
  have key : coeff 1 (φ * invOfUnit φ 1) = coeff 1 1 :=
    congrArg (coeff 1) (mul_invOfUnit φ 1 (by rw [h, Units.val_one]))
  rw [coeff_one_mul, constantCoeff_invOfUnit, h, coeff_one] at key
  simp only [inv_one, Units.val_one, mul_one] at key
  exact eq_neg_of_add_eq_zero_right key

end PowerSeries

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

lemma isLocalHom_localizationToCompletionIntegers :
    IsLocalHom (v.localizationToCompletionIntegers (K := K)) := by
  refine ⟨fun a ha ↦ ?_⟩
  by_contra hna
  have hm : v.localizationToCompletionIntegers (K := K) a ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [← v.maximalIdeal_map_completion]
    exact Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal a).mpr hna)
  exact (IsLocalRing.mem_maximalIdeal _).mp hm ha

lemma irreducible_localizationToCompletionIntegers {ϖ : Localization.AtPrime v.asIdeal}
    (hϖ : Irreducible ϖ) : Irreducible (v.localizationToCompletionIntegers (K := K) ϖ) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hϖ ⊢
  rw [← v.maximalIdeal_map_completion, hϖ, Ideal.map_span, Set.image_singleton]

lemma addVal_localizationToCompletionIntegers (x : Localization.AtPrime v.asIdeal) :
    IsDiscreteValuationRing.addVal (v.adicCompletionIntegers K)
      (v.localizationToCompletionIntegers (K := K) x) =
        IsDiscreteValuationRing.addVal (Localization.AtPrime v.asIdeal) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime v.asIdeal) with ⟨ϖ, hϖ⟩
  rcases IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ with ⟨n, u, rfl⟩
  rw [IsDiscreteValuationRing.addVal_def _ u hϖ n rfl, IsDiscreteValuationRing.addVal_def _
    (Units.map (v.localizationToCompletionIntegers (K := K)).toMonoidHom u)
    (v.irreducible_localizationToCompletionIntegers hϖ) n (by simp)]

lemma pow_dvd_localizationToCompletionIntegers_iff {ϖ : Localization.AtPrime v.asIdeal}
    (hϖ : Irreducible ϖ) (n : ℕ) (x : Localization.AtPrime v.asIdeal) :
    v.localizationToCompletionIntegers (K := K) ϖ ^ n ∣
      v.localizationToCompletionIntegers (K := K) x ↔ ϖ ^ n ∣ x := by
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, ← IsDiscreteValuationRing.addVal_le_iff_dvd,
    (v.irreducible_localizationToCompletionIntegers hϖ).addVal_pow, hϖ.addVal_pow,
    v.addVal_localizationToCompletionIntegers]

lemma card_residueField_localizationAtPrime :
    Nat.card (IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal)) =
      Nat.card (R ⧸ v.asIdeal) :=
  (Nat.card_congr (IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal
    (Localization.AtPrime v.asIdeal)).toEquiv).symm

lemma card_residueField_adicCompletionIntegers :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = Nat.card (R ⧸ v.asIdeal) :=
  (Nat.card_congr (v.residueFieldEquivAdicCompletionIntegers (K := K)).toEquiv).symm

end IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve

section LocalField

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K)

lemma constantCoeff_localPolynomial : (W.localPolynomial R).coeff 0 = 1 := by
  rw [localPolynomial]
  split_ifs <;> simp

lemma constantCoeff_localPowerSeries : PowerSeries.constantCoeff (W.localPowerSeries R) = 1 := by
  simp [localPowerSeries]

/-- **The coefficient of `T` in the local power series is the Frobenius trace** of the reduction of
a minimal equation, the local `a(p)` (`1`, `-1` or `0` at split multiplicative, non-split
multiplicative or additive reduction). -/
lemma coeff_one_localPowerSeries [Finite (IsLocalRing.ResidueField R)] :
    PowerSeries.coeff 1 (W.localPowerSeries R) = ((W.minimal R).reduction R).frobeniusTrace := by
  rw [localPowerSeries, PowerSeries.coeff_one_invOfUnit_one _ (by
    rw [Polynomial.constantCoeff_coe, constantCoeff_localPolynomial]), Polynomial.coeff_coe]
  by_cases hg : (W.minimal R).HasGoodReduction R
  · rw [localPolynomial_eq_of_hasGoodReduction R W hg]
    simp [Polynomial.coeff_one]
  · rw [localPolynomial_eq_of_not_hasGoodReduction R W hg]
    simp [Polynomial.coeff_one]

end LocalField

lemma frobeniusTrace_map_of_bijective {F F' : Type*} [Field F] [Field F'] [Finite F] [Finite F']
    {φ : F →+* F'} (hφ : Function.Bijective φ) (V : WeierstrassCurve F) :
    (V.map φ).frobeniusTrace = V.frobeniusTrace := by
  rw [frobeniusTrace_def, frobeniusTrace_def, pointCount_def, pointCount_def,
    Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_congr <|
      ((Equiv.ofBijective φ hφ).prodCongr (Equiv.ofBijective φ hφ)).subtypeEquiv
        (q := fun q ↦ (V.map φ).toAffine.Equation q.1 q.2) fun p ↦
          (Affine.map_equation V hφ.1 p.1 p.2).symm]

/-- **The Frobenius trace of the reduction at a prime is the same over the completion**: for an
elliptic curve `E` over a number field and a prime `v`, a minimal equation of `E` over the local
ring `𝓞_(v)` and one of its base change over the completed ring `𝓞_v` reduce to curves over the
same residue field with the same Frobenius trace. The equation on which Tate's algorithm stops
over `𝓞_(v)` stays a stopping equation over `𝓞_v`, hence minimal there, and its reduction is the
same curve. -/
lemma frobeniusTrace_reduction_minimal_baseChange_adicCompletion {K : Type*} [Field K]
    [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (E : WeierstrassCurve K) [E.IsElliptic] :
    (((E.baseChange (v.adicCompletion K)).minimal (v.adicCompletionIntegers K)).reduction
      (v.adicCompletionIntegers K)).frobeniusTrace =
        ((E.minimal (Localization.AtPrime v.asIdeal)).reduction
          (Localization.AtPrime v.asIdeal)).frobeniusTrace := by
  rcases E.exists_isTateTerminal_reductionSymbol (Localization.AtPrime v.asIdeal) with
    ⟨W', D, ϖ, hmin, hD, hϖ, h⟩
  let _ : Algebra (Localization.AtPrime v.asIdeal) (v.adicCompletionIntegers K) :=
    (v.localizationToCompletionIntegers (K := K)).toAlgebra
  have : IsLocalHom (algebraMap (Localization.AtPrime v.asIdeal) (v.adicCompletionIntegers K)) :=
    v.isLocalHom_localizationToCompletionIntegers
  have hRS : (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).comp
      (algebraMap (Localization.AtPrime v.asIdeal) (v.adicCompletionIntegers K)) =
        (algebraMap K (v.adicCompletion K)).comp (algebraMap (Localization.AtPrime v.asIdeal) K) :=
    IsLocalization.ringHom_ext v.asIdeal.primeCompl <| RingHom.ext fun x ↦ by
      simp only [RingHom.comp_apply]
      rw [RingHom.algebraMap_toAlgebra, v.localizationToCompletionIntegers_algebraMap,
        ← IsScalarTower.algebraMap_apply (𝓞 K) (Localization.AtPrime v.asIdeal) K,
        v.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers]
  -- the stopping equation stays a stopping equation over `𝓞_v`, so its base change is minimal
  have hbc : (W'.map (v.localizationToCompletionIntegers (K := K))).baseChange
      (v.adicCompletion K) = (W'.baseChange K).baseChange (v.adicCompletion K) := by
    rw [baseChange, baseChange, baseChange, map_map, map_map]
    exact congrArg W'.map hRS
  have hminS : IsMinimal (v.adicCompletionIntegers K)
      ((W'.baseChange K).baseChange (v.adicCompletion K)) := by
    have hmap : IsMinimal (v.adicCompletionIntegers K)
        ((W'.map (v.localizationToCompletionIntegers (K := K))).baseChange (v.adicCompletion K)) :=
      ((isTateTerminal_map_iff _ (v.pow_dvd_localizationToCompletionIntegers_iff (K := K) hϖ)).mpr
        h).isMinimal_baseChange (v.irreducible_localizationToCompletionIntegers (K := K) hϖ)
    rwa [hbc] at hmap
  have : (W'.baseChange K).IsElliptic := hD ▸ inferInstance
  have hL : (W'.baseChange K).baseChange (v.adicCompletion K) =
      D.map (algebraMap K (v.adicCompletion K)) • E.baseChange (v.adicCompletion K) := by
    rw [← hD, baseChange, baseChange, map_variableChange]
  -- the residue fields of `𝓞_(v)` and `𝓞_v` are both `𝓞 K ⧸ v`
  have hbij : Function.Bijective (algebraMap (IsLocalRing.ResidueField
      (Localization.AtPrime v.asIdeal)) (IsLocalRing.ResidueField (v.adicCompletionIntegers K))) :=
    (algebraMap (IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal))
      (IsLocalRing.ResidueField (v.adicCompletionIntegers K))).injective.bijective_of_nat_card_le
        (v.card_residueField_adicCompletionIntegers.trans
          v.card_residueField_localizationAtPrime.symm).le
  rcases (E.baseChange (v.adicCompletion K)).exists_smul_eq_minimal (v.adicCompletionIntegers K)
    with ⟨C₀, hC₀⟩
  rcases E.exists_smul_eq_minimal (Localization.AtPrime v.asIdeal) with ⟨C₁, hC₁⟩
  rcases exists_smul_reduction_eq_of_isMinimal_smul (v.adicCompletionIntegers K)
    (W₁ := (W'.baseChange K).baseChange (v.adicCompletion K))
    (W₂ := (E.baseChange (v.adicCompletion K)).minimal (v.adicCompletionIntegers K))
    (C₀ * (D.map (algebraMap K (v.adicCompletion K)))⁻¹) (by rw [mul_smul, hL, inv_smul_smul, hC₀])
      with ⟨CS, hCS⟩
  rcases exists_smul_reduction_eq_of_isMinimal_smul (Localization.AtPrime v.asIdeal)
    (W₁ := W'.baseChange K) (W₂ := E.minimal (Localization.AtPrime v.asIdeal)) (C₁ * D⁻¹)
    (by rw [mul_smul, ← hD, inv_smul_smul, hC₁]) with ⟨CR, hCR⟩
  rw [← hCS, variableChange_frobeniusTrace,
    reduction_baseChange (Localization.AtPrime v.asIdeal) (v.adicCompletionIntegers K) hRS,
    ← hCR, variableChange_frobeniusTrace]
  exact frobeniusTrace_map_of_bijective hbij _

variable (W : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ))

/-- **The coefficient of `L(E, s)` at a prime `p`**, for `E` over `ℚ`: if `p` is the norm of the
prime `v` of `ℚ`, the coefficient of `p⁻ˢ` in the Euler product is the coefficient of `T` in the
local power series at `v`, the only prime of norm `p`. -/
lemma LFunction_apply_absNorm : W.LFunction (Ideal.absNorm v.asIdeal) = PowerSeries.coeff 1
    ((W.baseChange (v.adicCompletion ℚ)).localPowerSeries (v.adicCompletionIntegers ℚ)) := by
  have hq (w : HeightOneSpectrum (𝓞 ℚ)) : Nat.card (IsLocalRing.ResidueField
      (w.adicCompletionIntegers ℚ)) = Ideal.absNorm w.asIdeal := by
    rw [w.card_residueField_adicCompletionIntegers, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Northcott fun w : HeightOneSpectrum (𝓞 ℚ) ↦
      Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers ℚ)) :=
    funext hq ▸ inferInstance
  rcases ((tendsTo_eulerProduct_ofPowerSeries (fun w : HeightOneSpectrum (𝓞 ℚ) ↦
    Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers ℚ)))
    (fun w ↦ (W.baseChange (w.adicCompletion ℚ)).localPowerSeries (w.adicCompletionIntegers ℚ))
    (fun w ↦ constantCoeff_localPowerSeries _ _) (Ideal.absNorm v.asIdeal)).and
      (Filter.eventually_ge_atTop {v})).exists with ⟨s, hs, hvs⟩
  -- `LFunction` was elaborated with the completion's own `ℚ`-algebra structure, while here the
  -- characteristic-zero instance `DivisionRing.toRatAlgebra` is found; the two are equal
  have hL : W.LFunction = eulerProduct fun w : HeightOneSpectrum (𝓞 ℚ) ↦
      ofPowerSeries (Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers ℚ)))
        ((W.baseChange (w.adicCompletion ℚ)).localPowerSeries (w.adicCompletionIntegers ℚ)) := by
    unfold LFunction localEulerFactor
    congr!
    exact Subsingleton.elim _ _
  rw [hL, ← hs, prod_apply_prime _ (fun w ↦ by
    rw [ofPowerSeries_apply_one, constantCoeff_localPowerSeries]) (prime_absNorm_asIdeal v),
    Finset.sum_eq_single_of_mem v (Finset.singleton_subset_iff.mp hvs) fun w _ hw ↦ ?_]
  · rw [← hq v]
    have key : ofPowerSeries (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)))
        ((W.baseChange (v.adicCompletion ℚ)).localPowerSeries (v.adicCompletionIntegers ℚ))
          (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) ^ 1) =
            PowerSeries.coeff 1
              ((W.baseChange (v.adicCompletion ℚ)).localPowerSeries (v.adicCompletionIntegers ℚ)) :=
      ofPowerSeries_apply_pow (hq v ▸ (prime_absNorm_asIdeal v).one_lt) _ 1
    rwa [pow_one] at key
  · rw [ofPowerSeries_apply (hq w ▸ (prime_absNorm_asIdeal w).one_lt), Function.extend_apply',
      Pi.zero_apply]
    rintro ⟨k, hk⟩
    rw [hq w, (prime_absNorm_asIdeal v).pow_eq_iff, absNorm_asIdeal, absNorm_asIdeal] at hk
    exact hw <| primesEquiv.injective <| Subtype.ext hk.1

lemma expChar_residueField_localizationAtPrime : ExpChar
    (IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal)) (Ideal.absNorm v.asIdeal) := by
  have : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨prime_absNorm_asIdeal v⟩
  have : Fintype (IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal)) := Fintype.ofFinite _
  have : CharP (IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal))
      (Ideal.absNorm v.asIdeal) := charP_of_card_eq_prime <| by
    rw [← Nat.card_eq_fintype_card, v.card_residueField_localizationAtPrime, Ideal.absNorm_apply,
      Submodule.cardQuot_apply]
  exact ExpChar.prime (prime_absNorm_asIdeal v)

variable [W.IsElliptic]

/-- **The coefficient `a(p)` of `L(E, s)` is the Frobenius trace of the reduction at `p`** (LMFDB
`ec.q.reduction_type`): for an elliptic curve over `ℚ` and the prime `v` above `p`, the coefficient
of `p⁻ˢ` in Mathlib's `WeierstrassCurve.LFunction` is `p + 1 − #Ẽ(𝔽_p)`, where `Ẽ` is the reduction
modulo `p` of a minimal equation over `ℤ_(p)`, its singular point counted. -/
lemma LFunction_apply_absNorm_eq_frobeniusTrace : W.LFunction (Ideal.absNorm v.asIdeal) =
    ((W.minimal (Localization.AtPrime v.asIdeal)).reduction
      (Localization.AtPrime v.asIdeal)).frobeniusTrace := by
  rw [LFunction_apply_absNorm, coeff_one_localPowerSeries,
    ← frobeniusTrace_reduction_minimal_baseChange_adicCompletion]
  congr!
  exact Subsingleton.elim _ _

/-- **`a(p) = 1` at split multiplicative reduction** (LMFDB `ec.q.reduction_type`). -/
lemma LFunction_apply_absNorm_eq_one
    (h : (W.minimal (Localization.AtPrime v.asIdeal)).HasSplitMultiplicativeReduction
      (Localization.AtPrime v.asIdeal)) : W.LFunction (Ideal.absNorm v.asIdeal) = 1 := by
  rw [LFunction_apply_absNorm_eq_frobeniusTrace]
  exact h.frobeniusTrace_reduction_eq_one _

/-- **`a(p) = -1` at non-split multiplicative reduction** (LMFDB `ec.q.reduction_type`). -/
lemma LFunction_apply_absNorm_eq_neg_one
    (h : (W.minimal (Localization.AtPrime v.asIdeal)).IsNonsplitMultiplicativeReduction
      (Localization.AtPrime v.asIdeal)) : W.LFunction (Ideal.absNorm v.asIdeal) = -1 := by
  rw [LFunction_apply_absNorm_eq_frobeniusTrace]
  exact h.1.frobeniusTrace_reduction_eq_neg_one _ h.2

/-- **`a(p) = 0` at additive reduction** (LMFDB `ec.q.reduction_type`). -/
lemma LFunction_apply_absNorm_eq_zero
    (h : (W.minimal (Localization.AtPrime v.asIdeal)).HasAdditiveReduction
      (Localization.AtPrime v.asIdeal)) : W.LFunction (Ideal.absNorm v.asIdeal) = 0 := by
  rw [LFunction_apply_absNorm_eq_frobeniusTrace]
  exact h.frobeniusTrace_reduction_eq_zero _

variable [(W.minimal (Localization.AtPrime v.asIdeal)).HasGoodReduction
  (Localization.AtPrime v.asIdeal)]

/-- **At good reduction, `p` divides `a(p)` exactly when the reduction is supersingular** (LMFDB
`ec.q.reduction_type`). -/
lemma hasGoodSupersingularReduction_iff_dvd_LFunction_apply :
    (W.minimal (Localization.AtPrime v.asIdeal)).HasGoodSupersingularReduction
      (Localization.AtPrime v.asIdeal) (Ideal.absNorm v.asIdeal) ↔
        (Ideal.absNorm v.asIdeal : ℤ) ∣ W.LFunction (Ideal.absNorm v.asIdeal) := by
  have : ExpChar (IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal))
      (Ideal.absNorm v.asIdeal) := expChar_residueField_localizationAtPrime v
  rw [LFunction_apply_absNorm_eq_frobeniusTrace]
  exact hasGoodSupersingularReduction_iff_dvd_frobeniusTrace

/-- **At good reduction, `p` does not divide `a(p)` exactly when the reduction is ordinary** (LMFDB
`ec.q.reduction_type`). -/
lemma hasGoodOrdinaryReduction_iff_not_dvd_LFunction_apply :
    (W.minimal (Localization.AtPrime v.asIdeal)).HasGoodOrdinaryReduction
      (Localization.AtPrime v.asIdeal) (Ideal.absNorm v.asIdeal) ↔
        ¬(Ideal.absNorm v.asIdeal : ℤ) ∣ W.LFunction (Ideal.absNorm v.asIdeal) := by
  have : ExpChar (IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal))
      (Ideal.absNorm v.asIdeal) := expChar_residueField_localizationAtPrime v
  rw [LFunction_apply_absNorm_eq_frobeniusTrace]
  exact hasGoodOrdinaryReduction_iff_not_dvd_frobeniusTrace

end WeierstrassCurve
