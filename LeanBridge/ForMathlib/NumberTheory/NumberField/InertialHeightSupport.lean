import LeanBridge.ForMathlib.NumberTheory.NumberField.InertialHeight
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Map
import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import TauCeti.NumberTheory.LocalField.Unramified.Criterion
import TauCeti.NumberTheory.LocalField.Unramified.Maximal

/-!
# The inertial height is a finite product

Let `G` be a finite group and `φ : Gal(ℚ̄/ℚ) → G` a continuous homomorphism. The inertial height of
`φ` (LMFDB `nf.inertial_height_function`, `NumberField.WeightFunction.inertialHeight`) is a
`finprod` over all primes `ℓ` of local heights, which would be `1` if infinitely many factors
differed from `1`. At a prime `ℓ ∤ #G` the local height is `1` as soon as the restriction `φ_ℓ` of
`φ` to `Gal(ℚ̄_ℓ/ℚ_ℓ)` kills the inertia subgroup. This holds at all but finitely many primes, so
the product has finitely many factors different from `1`.

The kernel of `φ` is open, so it contains the subgroup fixing `ℚ(α)` for some algebraic integer
`α`. Let `g` be the minimal polynomial of `α` over `ℤ`. Then `g'(α) ≠ 0`, and the constant
coefficient of the minimal polynomial of `g'(α)` over `ℤ` gives a nonzero integer `N` with
`g'(α) h(α) = N` for some `h ∈ ℤ[X]`. At a prime `ℓ ∤ N`, the image `x` of `α` in `ℚ̄_ℓ` is a root
of `g` at which `g'` is a unit, so `ℚ_ℓ(x)` is unramified over `ℚ_ℓ` (Tau Ceti's
`TauCeti.isUnramified_of_adjoin_eq_top_of_isUnit_aeval_derivative`) and `x` lies in the maximal
unramified extension of `ℚ_ℓ`, which inertia fixes. So the image of inertia in `Gal(ℚ̄/ℚ)` fixes
`α`, hence lies in the kernel of `φ`.

## Main results

* `Padic.mem_maximalUnramifiedExtension_of_aeval_derivative_mul_eq`: a root `x ∈ ℚ̄_ℓ` of a monic
  `g ∈ ℤ[X]` with `g'(x) h(x) = N` for some `h ∈ ℤ[X]` and an integer `N` prime to `ℓ` lies in the
  maximal unramified extension of `ℚ_ℓ`.
* `NumberField.exists_apply_map_eq_one_of_mem_inertiaSubgroup`: a continuous homomorphism from
  `Gal(ℚ̄/ℚ)` to a discrete group kills the inertia subgroups at all the primes outside a finite
  set.
* `NumberField.WeightFunction.finite_mulSupport_inertialHeight` (LMFDB
  `nf.inertial_height_function`): the product defining the inertial height has finitely many
  factors different from `1`.
-/

open Field IntermediateField Polynomial TauCeti ValuativeRel

open scoped NNReal Topology

namespace Padic

variable {ℓ : ℕ} [Fact ℓ.Prime]

lemma isUnit_intCast_integer {N : ℤ} (hN : ¬(ℓ : ℤ) ∣ N) : IsUnit (N : 𝒪[ℚ_[ℓ]]) := by
  let : Fintype 𝓀[ℚ_[ℓ]] := Fintype.ofFinite _
  have : CharP 𝓀[ℚ_[ℓ]] ℓ :=
    charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, natCard_residueField])
  have h : IsUnit (N.natAbs : 𝒪[ℚ_[ℓ]]) := by
    rwa [IsLocalRing.isUnit_natCast_iff_not_dvd, ringChar.eq 𝓀[ℚ_[ℓ]] ℓ, ← Int.natCast_dvd]
  rcases Int.natAbs_eq N with hN' | hN'
  · rwa [hN', Int.cast_natCast]
  · rw [hN', Int.cast_neg, Int.cast_natCast]
    exact h.neg

/-- **A root of an integer polynomial at which the derivative is a unit is unramified**: a root
`x ∈ ℚ̄_ℓ` of a monic `g ∈ ℤ[X]` such that `g'(x) h(x) = N` for some `h ∈ ℤ[X]` and an integer `N`
prime to `ℓ` lies in the maximal unramified extension of `ℚ_ℓ`. -/
lemma mem_maximalUnramifiedExtension_of_aeval_derivative_mul_eq {x : AlgebraicClosure ℚ_[ℓ]}
    {g h : ℤ[X]} (hg : g.Monic) (hx : aeval x g = 0) {N : ℤ}
    (hN : aeval x (derivative g) * aeval x h = N) (hℓN : ¬(ℓ : ℤ) ∣ N) :
    x ∈ maximalUnramifiedExtension ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]) := by
  have hxint : IsIntegral ℤ x := ⟨g, hg, hx⟩
  have : Module.Finite ℚ_[ℓ] ℚ_[ℓ]⟮x⟯ := adjoin.finiteDimensional hxint.tower_top
  let : ValuativeRel ℚ_[ℓ]⟮x⟯ := finiteIntermediateFieldValuativeRel ℚ_[ℓ] _ ℚ_[ℓ]⟮x⟯
  let : TopologicalSpace ℚ_[ℓ]⟮x⟯ := finiteIntermediateFieldTopology ℚ_[ℓ] _ ℚ_[ℓ]⟮x⟯
  have : ValuativeExtension ℚ_[ℓ] ℚ_[ℓ]⟮x⟯ :=
    finiteIntermediateField_valuativeExtension ℚ_[ℓ] _ ℚ_[ℓ]⟮x⟯
  have : IsNonarchimedeanLocalField ℚ_[ℓ]⟮x⟯ :=
    finiteIntermediateField_isNonarchimedeanLocalField ℚ_[ℓ] _ ℚ_[ℓ]⟮x⟯
  let j : 𝒪[ℚ_[ℓ]⟮x⟯] →+* AlgebraicClosure ℚ_[ℓ] :=
    ℚ_[ℓ]⟮x⟯.val.toRingHom.comp (algebraMap 𝒪[ℚ_[ℓ]⟮x⟯] ℚ_[ℓ]⟮x⟯)
  have hj : Function.Injective j :=
    ℚ_[ℓ]⟮x⟯.val.injective.comp (IsFractionRing.injective 𝒪[ℚ_[ℓ]⟮x⟯] ℚ_[ℓ]⟮x⟯)
  have hgen : IsIntegral ℤ (AdjoinSimple.gen ℚ_[ℓ] x) :=
    (isIntegral_algHom_iff ℚ_[ℓ]⟮x⟯.val.toRingHom.toIntAlgHom ℚ_[ℓ]⟮x⟯.val.injective).mp hxint
  rcases IsIntegrallyClosed.isIntegral_iff.mp (hgen.tower_top (A := 𝒪[ℚ_[ℓ]⟮x⟯])) with ⟨b, hb⟩
  have hjaeval (q : ℤ[X]) : j (aeval b q) = aeval x q :=
    (aeval_algHom_apply j.toIntAlgHom b q).symm.trans
      (congrArg (aeval · q) (congrArg Subtype.val hb))
  have hb0 : aeval b g = 0 := hj (by rw [hjaeval, hx, map_zero])
  have hbN : aeval b (derivative g) * aeval b h = N :=
    hj (by rw [map_mul, hjaeval, hjaeval, hN, map_intCast])
  have hunit : IsUnit (aeval b (derivative g)) := isUnit_of_mul_isUnit_left <| hbN ▸
    (map_intCast (algebraMap 𝒪[ℚ_[ℓ]] 𝒪[ℚ_[ℓ]⟮x⟯]) N ▸ (isUnit_intCast_integer hℓN).map _)
  have : IsUnramified ℚ_[ℓ] ℚ_[ℓ]⟮x⟯ :=
    isUnramified_of_adjoin_eq_top_of_isUnit_aeval_derivative (p := g.map (algebraMap ℤ _))
      (by rw [hb]; exact lift_injective _ ((lift_adjoin_simple _ _ _).trans (lift_top _ _).symm))
      (by rw [aeval_map_algebraMap, hb0]) (by rwa [derivative_map, aeval_map_algebraMap])
  exact ℚ_[ℓ]⟮x⟯.le_maximalUnramifiedExtension (mem_adjoin_simple_self ℚ_[ℓ] x)

end Padic

namespace NumberField

variable {G : Type*} [Group G] [TopologicalSpace G]

lemma exists_absoluteGaloisGroup_map_commutes {K L : Type*} [Field K] [Field L] (f : K →+* L) :
    ∃ ι : AlgebraicClosure K →+* AlgebraicClosure L, ∀ (σ : absoluteGaloisGroup L) x,
      ι (DFunLike.coe (F := Gal(AlgebraicClosure K/K)) (absoluteGaloisGroup.map f σ) x) =
        DFunLike.coe (F := Gal(AlgebraicClosure L/L)) σ (ι x) := by
  let : Algebra K L := f.toAlgebra
  let : Algebra (AlgebraicClosure K) (AlgebraicClosure L) :=
    (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L).toAlgebra
  exact ⟨algebraMap _ _, absoluteGaloisGroup_mapOfAlgebra_commutes K L⟩

variable [DiscreteTopology G] in
/-- **A continuous homomorphism from `Gal(ℚ̄/ℚ)` to a discrete group is unramified outside a finite
set of primes**: there is a positive integer `N` such that, at every prime `ℓ ∤ N`, the restriction
of `φ` to `Gal(ℚ̄_ℓ/ℚ_ℓ)` kills the inertia subgroup. -/
lemma exists_apply_map_eq_one_of_mem_inertiaSubgroup (φ : absoluteGaloisGroup ℚ →ₜ* G) :
    ∃ N ≠ 0, ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ℓ ∣ N →
      ∀ σ ∈ inertiaSubgroup ℚ_[ℓ], φ (absoluteGaloisGroup.map (algebraMap ℚ ℚ_[ℓ]) σ) = 1 := by
  -- The kernel of `φ` contains the subgroup fixing a finite subextension `E`, and `E ≤ ℚ(α)` for
  -- an algebraic integer `α`.
  have hker : ((φ : absoluteGaloisGroup ℚ →* G).ker : Set (absoluteGaloisGroup ℚ)) ∈
      𝓝 (1 : Gal(AlgebraicClosure ℚ/ℚ)) :=
    ((isOpen_discrete {1}).preimage φ.continuous).mem_nhds (map_one φ)
  rcases (krullTopology_mem_nhds_one_iff ℚ (AlgebraicClosure ℚ) _).mp hker with ⟨E, _, hE⟩
  rcases Field.exists_primitive_element ℚ E with ⟨α, hα⟩
  have hαalg : IsAlgebraic ℤ (α : AlgebraicClosure ℚ) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ _).mpr ((IsIntegral.of_finite ℚ α).map E.val).isAlgebraic
  rcases hαalg.exists_integral_multiple with ⟨d, hd, ha⟩
  set a : AlgebraicClosure ℚ := d • (α : AlgebraicClosure ℚ) with had
  have hEa : E ≤ ℚ⟮a⟯ := by
    rw [← lift_top ℚ E, ← hα, lift_adjoin_simple, adjoin_simple_le_iff]
    have h : (α : AlgebraicClosure ℚ) = (d : ℚ)⁻¹ • a := by
      rw [had, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ (Int.cast_ne_zero.mpr hd),
        one_smul]
    rw [h]
    exact smul_mem _ (mem_adjoin_simple_self ℚ a)
  -- `φ` kills every automorphism fixing `a`.
  have hfix (σ : Gal(AlgebraicClosure ℚ/ℚ)) (hσ : σ a = a) : φ σ = 1 := by
    have h : σ.toAlgHom.comp ℚ⟮a⟯.val = ℚ⟮a⟯.val :=
      adjoin_algHom_ext ℚ fun y hy ↦ by
        rcases Set.mem_singleton_iff.mp hy with rfl
        exact hσ
    exact hE (fixingSubgroup_antitone hEa ((IntermediateField.mem_fixingSubgroup_iff _ σ).mpr
      fun y hy ↦ DFunLike.congr_fun h ⟨y, hy⟩))
  -- The integer `N`: the constant coefficient of the minimal polynomial of `g'(a)` over `ℤ`.
  have hint (p : ℤ[X]) : IsIntegral ℤ (aeval a p) :=
    Algebra.adjoin_le (S := integralClosure ℤ (AlgebraicClosure ℚ))
      (Set.singleton_subset_iff.mpr ha) (aeval_mem_adjoin_singleton ℤ a)
  have hβ : aeval a (derivative (minpoly ℤ a)) ≠ 0 := by
    have h : aeval a (derivative (minpoly ℚ a)) ≠ 0 :=
      (minpoly.irreducible (ha.tower_top (A := ℚ))).separable.aeval_derivative_ne_zero
        (minpoly.aeval ℚ a)
    rwa [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ ha, derivative_map,
      aeval_map_algebraMap] at h
  set β : AlgebraicClosure ℚ := aeval a (derivative (minpoly ℤ a)) with hβdef
  have hN0 : (minpoly ℤ β).coeff 0 ≠ 0 := by
    have h : (minpoly ℚ β).coeff 0 ≠ 0 :=
      minpoly.coeff_zero_ne_zero ((hint (derivative (minpoly ℤ a))).tower_top (A := ℚ)) hβ
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (hint _), coeff_map] at h
    exact fun h0 ↦ h (by rw [h0, map_zero])
  have hβm : β * aeval β (-divX (minpoly ℤ β)) = (minpoly ℤ β).coeff 0 := by
    have h : aeval β (minpoly ℤ β) = 0 := minpoly.aeval ℤ β
    rw [← X_mul_divX_add (minpoly ℤ β), map_add, map_mul, aeval_X, aeval_C, eq_intCast] at h
    rw [map_neg, mul_neg, neg_eq_iff_add_eq_zero]
    exact h
  refine ⟨(minpoly ℤ β).coeff 0 |>.natAbs, Int.natAbs_ne_zero.mpr hN0, fun ℓ _ hℓ ↦ ?_⟩
  rcases exists_absoluteGaloisGroup_map_commutes (algebraMap ℚ ℚ_[ℓ]) with ⟨ι, hι⟩
  have hιaeval (p : ℤ[X]) (x : AlgebraicClosure ℚ) : aeval (ι x) p = ι (aeval x p) :=
    aeval_algHom_apply ι.toIntAlgHom x p
  have hιa : ι a ∈ maximalUnramifiedExtension ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]) := by
    refine Padic.mem_maximalUnramifiedExtension_of_aeval_derivative_mul_eq
      (h := (-divX (minpoly ℤ β)).comp (derivative (minpoly ℤ a))) (minpoly.monic ha) ?_ ?_
      fun h ↦ hℓ (Int.natCast_dvd.mp h)
    · rw [hιaeval, minpoly.aeval, map_zero]
    · rw [aeval_comp, hιaeval, hιaeval, ← hβdef, ← map_mul, hβm, map_intCast]
  exact fun σ hσ ↦ hfix _ <| ι.injective ((hι σ a).trans (mem_inertiaSubgroup_iff.mp hσ _ hιa))

namespace WeightFunction

variable (w : WeightFunction G)

lemma localHeight_eq_one {p : ℕ} [Fact p.Prime] {ψ : absoluteGaloisGroup ℚ_[p] →ₜ* G}
    (hψ : ∀ σ ∈ inertiaSubgroup ℚ_[p], ψ σ = 1) : w.localHeight p ψ = 1 := by
  have h (τ : inertiaSubgroup ℚ_[p]) : w.toFun (ψ τ) = 0 := (w.toFun_eq_zero_iff _).mpr (hψ τ τ.2)
  rw [localHeight, h, NNReal.coe_zero, NNReal.rpow_zero]

variable [DiscreteTopology G] in
/-- **The product defining the inertial height has finitely many factors different from `1`**
(LMFDB `nf.inertial_height_function`): for a finite group `G`, the inertial height of a continuous
homomorphism `φ : Gal(ℚ̄/ℚ) → G` is the `finprod` over the primes `ℓ` of `H ℓ (φ_ℓ)` if `ℓ ∣ #G`
and of the local height `H_{w,ℓ}(φ_ℓ)` if `ℓ ∤ #G`, and these factors are `1` outside a finite set
of primes, since `φ` is unramified outside a finite set of primes. -/
lemma finite_mulSupport_inertialHeight [Finite G]
    (H : ∀ (ℓ : ℕ) [Fact ℓ.Prime], (absoluteGaloisGroup ℚ_[ℓ] →ₜ* G) → ℝ≥0)
    (φ : absoluteGaloisGroup ℚ →ₜ* G) :
    (Function.mulSupport fun ℓ : ℕ ↦ ∏ᶠ (hℓ : ℓ.Prime),
      haveI : Fact ℓ.Prime := ⟨hℓ⟩
      letI φℓ : absoluteGaloisGroup ℚ_[ℓ] →ₜ* G :=
        φ.comp (absoluteGaloisGroup.map (algebraMap ℚ ℚ_[ℓ]))
      if ℓ ∣ Nat.card G then H ℓ φℓ else w.localHeight ℓ φℓ).Finite := by
  rcases exists_apply_map_eq_one_of_mem_inertiaSubgroup φ with ⟨N, hN, hφ⟩
  have hM : N * Nat.card G ≠ 0 := mul_ne_zero hN Nat.card_pos.ne'
  refine (Nat.divisors (N * Nat.card G)).finite_toSet.subset fun ℓ hℓ ↦ ?_
  rw [Finset.mem_coe, Nat.mem_divisors]
  refine ⟨by_contra fun hdvd ↦ hℓ ?_, hM⟩
  dsimp only
  rw [finprod_eq_dif]
  split_ifs with hp hG
  · exact absurd (dvd_mul_of_dvd_right hG N) hdvd
  · have : Fact ℓ.Prime := ⟨hp⟩
    exact w.localHeight_eq_one <| hφ ℓ fun h ↦ hdvd (dvd_mul_of_dvd_left h _)
  · rfl

end WeightFunction

end NumberField
