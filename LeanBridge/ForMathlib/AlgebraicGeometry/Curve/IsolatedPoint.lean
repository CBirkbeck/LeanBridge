import TauCeti.FieldTheory.FunctionField.Consequences.HighDegree
import TauCeti.FieldTheory.FunctionField.Consequences.PointSeparation

/-!
# `ℙ¹`-parametrized closed points of a curve

A closed point `x` of degree `d` on a curve `C` over a field `k` is isolated (LMFDB
`ag.isolated_point`) if it is not contained in a family of effective divisors of degree `d`
parametrized by `ℙ¹` or by a positive-rank abelian variety (Bourdon, Ejder, Liu, Odumodu and
Viray): `x` is neither `ℙ¹`-parametrized nor AV-parametrized. This file formalises the first
condition. The second asks for a positive-rank abelian subvariety `A` of the Jacobian with
`[x] + A ⊆ W_d`, the image of the `d`-th symmetric power of `C` in `Pic^d`, and needs the Jacobian
of `C`, its abelian subvarieties and their Mordell–Weil ranks, which are out of reach.

The closed points of a smooth projective curve `C` over `k` with function field `F = k(C)` are the
places of `F / k` (Tau Ceti's `TauCeti.Place`), and a closed point `x` of degree `d` is the
effective divisor `x` of degree `d`. A family of effective divisors parametrized by `ℙ¹` containing
`x` lies in a linear system, as there is no nonconstant map from `ℙ¹` to an abelian variety, so
`x` is `ℙ¹`-parametrized exactly when it moves in its linear system `|x|`, that is, when its
Riemann–Roch space `L(x)` has dimension `ℓ(x) ≥ 2`. Equivalently, over an exact constant field,
there is a nonconstant function `f` with `div f + x ≥ 0`: a morphism `f : C → ℙ¹` of degree `d`
with `f^* ∞ = x`, which is the definition of Bourdon et al.

## Main definitions

* `TauCeti.Place.IsP1Parametrized` (LMFDB `ag.isolated_point`): a closed point, as a place of the
  function field, is `ℙ¹`-parametrized.

## Main results

* `TauCeti.Place.isP1Parametrized_iff`: over an exact constant field, a closed point `x` is
  `ℙ¹`-parametrized exactly when some nonconstant function has its poles bounded by `x`.
* `TauCeti.Place.isP1Parametrized_of_genus_eq_zero`: on a curve of genus `0`, every closed point is
  `ℙ¹`-parametrized.
* `TauCeti.Place.not_isP1Parametrized_of_genus_pos`: on a curve of positive genus, no rational
  point is `ℙ¹`-parametrized.
-/

open TauCeti AlgebraicGeometry

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (P : Place k F)

/-- A closed point `x` of a curve over `k` with function field `F`, viewed as a place `P` of
`F / k`, is **`ℙ¹`-parametrized** (LMFDB `ag.isolated_point`) if it is contained in a family of
effective divisors of degree `d = deg x` parametrized by `ℙ¹`, that is, if it moves in its linear
system: its Riemann–Roch space `L(x)` has dimension `ℓ(x) ≥ 2`. Over an exact constant field this
says that some nonconstant function has its poles bounded by `x` (`isP1Parametrized_iff`), a
morphism `C → ℙ¹` of degree `d` with fibre `x` above `∞`. An isolated point is one that is neither
`ℙ¹`-parametrized nor parametrized by a positive-rank abelian variety. -/
def IsP1Parametrized : Prop :=
  2 ≤ Divisor.dim (WeilDivisor.ofPoint P : Divisor k F)

variable {P}

/-- **A closed point is `ℙ¹`-parametrized exactly when some nonconstant function has its poles
bounded by it**, over an exact constant field: the function `f`, transcendental over `k`, with
`div f + x ≥ 0` is a morphism to `ℙ¹` of degree `deg x` with fibre `x` above `∞`. -/
lemma isP1Parametrized_iff (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) :
    P.IsP1Parametrized ↔ ∃ f ∈ riemannRochSpace (WeilDivisor.ofPoint P : Divisor k F),
      Transcendental k f := by
  have hfin : FiniteDimensional k (riemannRochSpace (WeilDivisor.ofPoint P : Divisor k F)) :=
    finiteDimensional_riemannRochSpace hF _
  refine ⟨fun h ↦ ?_, fun ⟨f, hf, hft⟩ ↦ ?_⟩
  · by_contra! hc
    have hle : riemannRochSpace (WeilDivisor.ofPoint P : Divisor k F) ≤
        LinearMap.range (Algebra.linearMap k F) :=
      fun f hf ↦ (hF.isAlgebraic_iff_mem_range_algebraMap hF hex).mp (not_not.mp (hc f hf))
    have h₁ : Divisor.dim (WeilDivisor.ofPoint P : Divisor k F) ≤
        Module.finrank k (LinearMap.range (Algebra.linearMap k F)) :=
      Submodule.finrank_mono hle
    have h₂ : Module.finrank k (LinearMap.range (Algebra.linearMap k F)) ≤ 1 :=
      (LinearMap.finrank_range_le (Algebra.linearMap k F)).trans_eq (Module.finrank_self k)
    rw [IsP1Parametrized] at h
    omega
  · have h₁ : (1 : F) ∈ riemannRochSpace (WeilDivisor.ofPoint P : Divisor k F) :=
      one_mem_riemannRochSpace_iff.mpr (WeilDivisor.zero_le_ofPoint P)
    have hli : LinearIndependent k
        ![(⟨1, h₁⟩ : riemannRochSpace (WeilDivisor.ofPoint P : Divisor k F)), ⟨f, hf⟩] := by
      refine LinearIndependent.pair_iff.mpr fun s t hst ↦ ?_
      have hst' : s • (1 : F) + t • f = 0 :=
        congrArg Subtype.val hst
      by_cases ht : t = 0
      · subst ht
        simpa using hst'
      · have hf' : f = algebraMap k F (-(s / t)) := by
          rw [Algebra.algebraMap_eq_smul_one, ← inv_smul_smul₀ ht f,
            eq_neg_of_add_eq_zero_right hst', smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
        exact absurd (hf' ▸ isAlgebraic_algebraMap _) hft
    rw [IsP1Parametrized, Divisor.dim_def]
    simpa using hli.fintype_card_le_finrank

/-- **On a curve of genus `0`, every closed point is `ℙ¹`-parametrized**: by Riemann–Roch, a closed
point `x` of degree `d ≥ 1` has `ℓ(x) = d + 1 ≥ 2`. -/
lemma isP1Parametrized_of_genus_eq_zero (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hg : genus k F = 0) : P.IsP1Parametrized := by
  have h : (Divisor.dim (WeilDivisor.ofPoint P : Divisor k F) : ℤ) =
      Divisor.degree (WeilDivisor.ofPoint P : Divisor k F) + 1 - genus k F :=
    Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree hF hex <| by
      rw [hg, Divisor.degree_ofPoint]
      omega
  have h₁ : 1 ≤ P.degree :=
    P.one_le_degree_of_isFunctionField hF
  rw [Divisor.degree_ofPoint, hg] at h
  rw [IsP1Parametrized]
  omega

/-- **On a curve of positive genus, no rational point is `ℙ¹`-parametrized**: a rational point `x`
has `ℓ(x) = 1`, since no nonconstant function has a single simple pole. -/
lemma not_isP1Parametrized_of_genus_pos (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hg : 0 < genus k F) (hP : P.degree = 1) : ¬P.IsP1Parametrized := by
  rw [IsP1Parametrized, Divisor.dim_ofPoint_eq_one_of_genus_pos hF hex hg hP]
  omega

end TauCeti.Place
