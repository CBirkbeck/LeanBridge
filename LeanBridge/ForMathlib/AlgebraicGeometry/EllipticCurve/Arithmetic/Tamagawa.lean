import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.GoodReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic

/-!
# Tamagawa numbers of an elliptic curve over a number field

Let `E` be an elliptic curve over a number field `K` and `𝔭` a prime of `K`, with completion `K_𝔭`
and valuation ring `O_𝔭`. The Tamagawa number of `E` at `𝔭` (LMFDB `ec.tamagawa_number`) is the
index `c_𝔭(E) = [E(K_𝔭) : E⁰(K_𝔭)]`, where `E⁰(K_𝔭)` is the subgroup of points whose reduction
modulo `𝔭` is a nonsingular point, the reduction being taken on a minimal Weierstrass equation over
`O_𝔭`. Here the minimal equation is Mathlib's chosen one, `WeierstrassCurve.minimal`, and `E⁰(K_𝔭)`
is Tau Ceti's `WeierstrassCurve.Affine.nonsingularReduction`. That the index does not depend on
the minimal equation, that it is finite (so positive), and that Tate's algorithm computes it
(Tau Ceti's `WeierstrassCurve.tateLocalIndex`) are not formalised here; an infinite index would
have the value `0` of `AddSubgroup.index`. The Tamagawa number is `1` at every prime of good
reduction, so only finitely many of them differ from `1`, and their product over all primes is the
Tamagawa product.

## Main definitions

* `WeierstrassCurve.tamagawaNumber`: the Tamagawa number `c_𝔭(E)` (LMFDB `ec.tamagawa_number`).
* `WeierstrassCurve.tamagawaProduct`: the Tamagawa product `∏_𝔭 c_𝔭(E)`
  (LMFDB `ec.tamagawa_number`).

## Main results

* `WeierstrassCurve.tamagawaNumber_eq_one_of_hasGoodReduction`: `c_𝔭(E) = 1` when `E` has good
  reduction at `𝔭`.
* `WeierstrassCurve.tamagawaNumber_eq_one_of_Δ_notMem`: `c_𝔭(E) = 1` when `E` has an integral
  equation over the ring of integers whose discriminant is not in `𝔭`.
* `WeierstrassCurve.hasFiniteMulSupport_tamagawaNumber`: `c_𝔭(E) = 1` for all but finitely many
  primes `𝔭`, so the Tamagawa product is a finite product.
-/

open IsDedekindDomain HeightOneSpectrum NumberField

namespace WeierstrassCurve

variable {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)
  (p : HeightOneSpectrum (𝓞 K))

instance {W' : WeierstrassCurve (p.adicCompletion K)} [IsIntegral (p.adicCompletionIntegers K) W'] :
    IsIntegral (Valued.v : Valuation (p.adicCompletion K) _).valuationSubring W' :=
  ‹_›

open scoped Classical in
/-- The **Tamagawa number** `c_𝔭(E) = [E(K_𝔭) : E⁰(K_𝔭)]` (LMFDB `ec.tamagawa_number`) of a
Weierstrass curve `W` over a number field `K` at a prime `𝔭`, where `E(K_𝔭)` is the group of points
of Mathlib's chosen minimal equation, over the valuation ring of the completion `K_𝔭`, of the base
change of `W` to `K_𝔭`, and `E⁰(K_𝔭)` is its subgroup of points whose reduction modulo `𝔭` is
nonsingular. An infinite index would read `0`; the index is finite, but that is not formalised. -/
noncomputable def tamagawaNumber : ℕ :=
  (((W⁄(p.adicCompletion K)).minimal (p.adicCompletionIntegers K)).toAffine.nonsingularReduction
    Valued.v).index

/-- The **Tamagawa product** `∏_𝔭 c_𝔭(E)` (LMFDB `ec.tamagawa_number`) of a Weierstrass curve over
a number field: the product of its Tamagawa numbers over all primes, a finite product for an
elliptic curve (`WeierstrassCurve.hasFiniteMulSupport_tamagawaNumber`). -/
noncomputable def tamagawaProduct : ℕ :=
  ∏ᶠ p : HeightOneSpectrum (𝓞 K), W.tamagawaNumber p

/-- **The Tamagawa number is `1` at good reduction**: if Mathlib's chosen minimal equation of `W`
over the valuation ring of `K_𝔭` has good reduction, then every point of `E(K_𝔭)` has nonsingular
reduction, and `c_𝔭(E) = 1`. -/
lemma tamagawaNumber_eq_one_of_hasGoodReduction (h : ((W⁄(p.adicCompletion K)).minimal
    (p.adicCompletionIntegers K)).HasGoodReduction (p.adicCompletionIntegers K)) :
    W.tamagawaNumber p = 1 := by
  classical
  have : (integralModel (Valued.v : Valuation (p.adicCompletion K) _).valuationSubring
      ((W⁄(p.adicCompletion K)).minimal (p.adicCompletionIntegers K))).IsElliptic :=
    ⟨(hasGoodReduction_iff_isUnit_integralModel_Δ _ _).mp h⟩
  rw [tamagawaNumber, Affine.nonsingularReduction_eq_top, AddSubgroup.index_top]

/-- **The Tamagawa number is `1` at a prime not dividing an integral discriminant**: if `C • W` is
the base change of an equation `W₀` over the ring of integers whose discriminant is not in `𝔭`,
then `W` has good reduction at `𝔭` and `c_𝔭(E) = 1`. -/
lemma tamagawaNumber_eq_one_of_Δ_notMem {W₀ : WeierstrassCurve (𝓞 K)} (C : VariableChange K)
    (hC : C • W = W₀⁄K) (hΔ : W₀.Δ ∉ p.asIdeal) : W.tamagawaNumber p = 1 := by
  have : IsIntegral (𝓞 K) (C • W) := ⟨⟨W₀, hC⟩⟩
  have hRS : (algebraMap (p.adicCompletionIntegers K) (p.adicCompletion K)).comp
      (algebraMap (𝓞 K) (p.adicCompletionIntegers K)) = (algebraMap K (p.adicCompletion K)).comp
      (algebraMap (𝓞 K) K) :=
    RingHom.ext fun _ ↦ rfl
  have : IsIntegral (p.adicCompletionIntegers K) ((C • W)⁄(p.adicCompletion K)) :=
    IsIntegral.baseChange hRS (C • W)
  have hgood : ((C • W)⁄(p.adicCompletion K)).HasGoodReduction (p.adicCompletionIntegers K) := by
    rw [hasGoodReduction_iff_isUnit_integralModel_Δ, integralModel_baseChange hRS, map_Δ,
      integralModel_eq_of_baseChange_eq hC.symm]
    simp [adicCompletionIntegers.isUnit_iff_valued_eq_one, hΔ]
  refine W.tamagawaNumber_eq_one_of_hasGoodReduction p
    ((hasGoodReduction_minimal_smul_iff _ (C.baseChange (p.adicCompletion K)) _).mp ?_)
  rw [VariableChange.baseChange, baseChange, map_variableChange]
  exact hgood.hasGoodReduction_minimal

/-- **Only finitely many Tamagawa numbers differ from `1`**, as `c_𝔭(E) = 1` at every prime of good
reduction. -/
lemma hasFiniteMulSupport_tamagawaNumber [W.IsElliptic] : W.tamagawaNumber.HasFiniteMulSupport := by
  rcases exists_smul_isIntegral (𝓞 K) W with ⟨C, hC⟩
  have hΔ : (integralModel (𝓞 K) (C • W)).Δ ≠ 0 :=
    fun h0 ↦ (C • W).isUnit_Δ.ne_zero <| by rw [← integralModel_Δ_eq (𝓞 K) (C • W), h0, map_zero]
  refine (Ideal.finite_factors (Ideal.span_singleton_eq_bot.not.mpr hΔ)).subset fun p hp ↦ ?_
  rw [Set.mem_ofPred_eq, Ideal.dvd_span_singleton]
  by_contra hΔp
  exact hp (W.tamagawaNumber_eq_one_of_Δ_notMem p C (baseChange_integralModel_eq _ _).symm hΔp)

end WeierstrassCurve
