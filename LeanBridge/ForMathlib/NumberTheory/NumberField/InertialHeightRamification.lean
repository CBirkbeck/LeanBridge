import LeanBridge.ForMathlib.NumberTheory.Artin.Basic
import LeanBridge.ForMathlib.NumberTheory.ModEllGaloisRep.TopSlopeRamification
import LeanBridge.ForMathlib.NumberTheory.NumberField.InertialHeightSupport
import TauCeti.NumberTheory.NumberField.RamifiedPrimes

/-!
# The primes at which a Galois representation ramifies

Let `φ : Gal(ℚ̄/ℚ) → G` be a continuous homomorphism to a discrete group and `L` the number field
it cuts out, the subfield of `ℚ̄` fixed by its kernel. The restriction `φ_ℓ` of `φ` to
`Gal(ℚ̄_ℓ/ℚ_ℓ)`, along Mathlib's chosen embedding `ι : ℚ̄ → ℚ̄_ℓ`, kills the inertia subgroup
exactly when the prime `ℓ` is unramified in `L`. Indeed `φ_ℓ` kills inertia exactly when inertia
fixes `ι(L)`, that is, when the compositum `ℚ_ℓ · ι(L)` is unramified over `ℚ_ℓ` (Tau Ceti). This
compositum is the factor `(ℚ_ℓ ⊗ L) / 𝔪` of the local algebra of `L` cut out by `ι`, which is the
completion `L_w` of `L` at a place `w` above `ℓ` and has ramification index `e(w | ℓ)` over `ℚ_ℓ`.
As `L` is Galois over `ℚ`, all the places above `ℓ` have the same ramification index.

So the inertial height of the weight function equal to `1` away from the identity (LMFDB
`nf.inertial_height_function`), with the auxiliary local heights `ℓ` or `1` according as `φ_ℓ`
ramifies or not, is the radical discriminant of `L`: the product of the primes ramified in `L`,
which are the prime divisors of its discriminant. Local and inertial heights are positive, as the
knowl's codomain `ℝ_{>0}` says, once the auxiliary local heights are.

## Main results

* `NumberField.exists_forall_apply_eq_self_iff_ramificationIdx_eq_one`: for an embedding `j` of a
  number field `L` in `ℚ̄_ℓ`, inertia fixes `j(L)` exactly when the place of `L` induced by `j` is
  unramified over `ℓ`.
* `NumberField.forall_apply_map_eq_one_iff_notMem_ramifiedPrimes` (LMFDB
  `nf.inertial_height_function`): `φ` kills the inertia at `ℓ` exactly when `ℓ` is unramified in the
  number field cut out by `φ`.
* `NumberField.finprod_mem_ramifiedPrimes_eq_prod_primeFactors`: the product of the primes ramified
  in a number field is the product of the prime divisors of its discriminant.
* `NumberField.WeightFunction.localHeight_pos` and `NumberField.WeightFunction.inertialHeight_pos`
  (LMFDB `nf.inertial_height_function`): local heights are positive, and so are inertial heights
  with positive auxiliary local heights.
* `NumberField.WeightFunction.inertialHeight_indicator_eq_finprod_ramifiedPrimes` (LMFDB
  `nf.inertial_height_function`): for the weight function equal to `1` away from the identity, an
  inertial height is the radical discriminant, the product of the primes ramified in the number
  field cut out by `φ`.
-/

open IsDedekindDomain NumberField ValuativeRel TauCeti IsNonarchimedeanLocalField Ideal Algebra
  TensorProduct IntermediateField Field

open scoped NNReal

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace NumberField

variable (L : Type*) [Field L] [NumberField L] (ℓ : ℕ) [Fact ℓ.Prime] {G : Type*} [Group G]
  [TopologicalSpace G] (φ : absoluteGaloisGroup ℚ →ₜ* G)

/-- **Inertia fixes an embedding of a number field exactly when the place it induces is
unramified**: for an embedding `j : L → ℚ̄_ℓ` of a number field `L`, there is a prime `w` of `𝓞 L`
above `ℓ`, the place induced by `j`, such that the inertia subgroup of `Gal(ℚ̄_ℓ/ℚ_ℓ)` fixes `j(L)`
pointwise exactly when `e(w | ℓ) = 1`. The compositum `ℚ_ℓ · j(L)` is the factor of the local
algebra `ℚ_ℓ ⊗ L` cut out by `j`, the completion `L_w`, whose ramification index over `ℚ_ℓ` is
`e(w | ℓ)`. -/
lemma exists_forall_apply_eq_self_iff_ramificationIdx_eq_one (j : L →+* AlgebraicClosure ℚ_[ℓ]) :
    ∃ w : HeightOneSpectrum (𝓞 L), (ℓ : 𝓞 L) ∈ w.asIdeal ∧
      ((∀ σ : Gal(AlgebraicClosure ℚ_[ℓ]/ℚ_[ℓ]), σ ∈ inertiaSubgroup ℚ_[ℓ] → ∀ x, σ (j x) = j x) ↔
        w.asIdeal.ramificationIdx ℤ = 1) := by
  let ψ : ℚ_[ℓ] ⊗[ℚ] L →ₐ[ℚ_[ℓ]] AlgebraicClosure ℚ_[ℓ] :=
    Algebra.TensorProduct.lift (ofId _ _) j.toRatAlgHom fun _ _ ↦ .all _ _
  have : IsArtinianRing (ℚ_[ℓ] ⊗[ℚ] L) := IsArtinianRing.of_finite ℚ_[ℓ] _
  have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have : (RingHom.ker ψ).IsMaximal := IsArtinianRing.isMaximal_of_isPrime (RingHom.ker ψ)
  let 𝔪 : MaximalSpectrum (ℚ_[ℓ] ⊗[ℚ] L) := ⟨RingHom.ker ψ, inferInstance⟩
  rcases exists_eq_ker_localAlgebraToCompletion L ℓ (Padic.ringEquivAdicCompletion ℓ) 𝔪 with
    ⟨⟨w, hw⟩, hw𝔪⟩
  refine ⟨w, (liesOver_primesEquiv_symm_iff L ℓ w).mp hw, ?_⟩
  let _ : Field (ℚ_[ℓ] ⊗[ℚ] L ⧸ RingHom.ker ψ) := Quotient.field _
  let _ : ValuativeRel (ℚ_[ℓ] ⊗[ℚ] L ⧸ RingHom.ker ψ) := algebraicExtensionValuativeRel ℚ_[ℓ] _
  let _ : TopologicalSpace (ℚ_[ℓ] ⊗[ℚ] L ⧸ RingHom.ker ψ) :=
    algebraicExtensionNormedFieldTopology ℚ_[ℓ] _
  have : IsNonarchimedeanLocalField (ℚ_[ℓ] ⊗[ℚ] L ⧸ RingHom.ker ψ) :=
    finiteExtension_isNonarchimedeanLocalField ℚ_[ℓ] _
  have : ValuativeExtension ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] L ⧸ RingHom.ker ψ) :=
    algebraicExtension_valuativeExtension ℚ_[ℓ] _
  have he :
      ramificationIndex ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] L ⧸ RingHom.ker ψ) = w.asIdeal.ramificationIdx (𝓞 ℚ) :=
    ramificationIndex_quotient_eq L ℓ _ w (Padic.continuous_ringEquivAdicCompletion ℓ) 𝔪 hw𝔪
  -- The compositum `ℚ_ℓ · j(L)`, the image of `ℚ_ℓ ⊗ L`.
  let E : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]) := (kerLiftAlg ψ).fieldRange
  let σE : (ℚ_[ℓ] ⊗[ℚ] L ⧸ RingHom.ker ψ) ≃ₐ[ℚ_[ℓ]] E := (kerLiftAlg ψ).equivFieldRange
  have : FiniteDimensional ℚ_[ℓ] E := σE.toLinearEquiv.finiteDimensional
  have hE : IsUnramified ℚ_[ℓ] E ↔ IsUnramified ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] L ⧸ RingHom.ker ψ) :=
    ⟨fun _ ↦ IsUnramified.of_algEquiv σE.symm, fun _ ↦ IsUnramified.of_algEquiv σE⟩
  rw [← ramificationIdx_ringOfIntegers_rat, ← he, ← isUnramified_iff_ramificationIndex_eq_one,
    ← hE, ← inertiaSubgroup_le_fixingSubgroup_iff E]
  refine ⟨fun h (σ : Gal(AlgebraicClosure ℚ_[ℓ]/ℚ_[ℓ])) hσ ↦ (mem_fixingSubgroup_iff _ _).mpr
    fun y hy ↦ ?_, fun h σ hσ x ↦ ?_⟩
  · rcases AlgHom.mem_fieldRange.mp hy with ⟨q, rfl⟩
    rcases Quotient.mkₐ_surjective ℚ_[ℓ] (RingHom.ker ψ) q with ⟨t, rfl⟩
    clear hy
    rw [Quotient.mkₐ_eq_mk, kerLiftAlg_mk]
    induction t using TensorProduct.inductionOn with
    | tmul a x => simp [ψ, h σ hσ x]
    | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  · refine (mem_fixingSubgroup_iff _ _).mp (h hσ) (j x) (AlgHom.mem_fieldRange.mpr
      ⟨Quotient.mkₐ ℚ_[ℓ] (RingHom.ker ψ) (1 ⊗ₜ x), ?_⟩)
    rw [Quotient.mkₐ_eq_mk, kerLiftAlg_mk]
    simp [ψ]

lemma isUnramifiedIn_span_iff_forall_ramificationIdx_eq_one :
    IsUnramifiedIn (𝓞 L) (span {(ℓ : ℤ)}) ↔ ∀ P : HeightOneSpectrum (𝓞 L), (ℓ : 𝓞 L) ∈ P.asIdeal →
      P.asIdeal.ramificationIdx ℤ = 1 := by
  have hℓ : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  refine ⟨fun h P hP ↦ h P.asIdeal ((liesOver_span_iff P.isPrime.ne_top hℓ).mpr (by simpa)),
    fun h P _ hP ↦ ?_⟩
  have hPℓ : (ℓ : 𝓞 L) ∈ P := by simpa using (liesOver_span_iff IsPrime.ne_top' hℓ).mp hP
  have hP0 : P ≠ ⊥ := fun h0 ↦ by
    rw [h0, Submodule.mem_bot, Nat.cast_eq_zero] at hPℓ
    exact (Fact.out : ℓ.Prime).ne_zero hPℓ
  exact h ⟨P, inferInstance, hP0⟩ hPℓ

variable [DiscreteTopology G] in
/-- **A Galois representation is unramified at `ℓ` exactly when `ℓ` is unramified in the field it
cuts out** (LMFDB `nf.inertial_height_function`): a continuous homomorphism `φ : Gal(ℚ̄/ℚ) → G` to
a discrete group kills the image of the inertia subgroup of `Gal(ℚ̄_ℓ/ℚ_ℓ)`, along Mathlib's
chosen embedding `ℚ̄ → ℚ̄_ℓ`, exactly when `ℓ` is unramified in the subfield of `ℚ̄` fixed by the
kernel of `φ`. -/
lemma forall_apply_map_eq_one_iff_notMem_ramifiedPrimes :
    (∀ σ ∈ inertiaSubgroup ℚ_[ℓ], φ (absoluteGaloisGroup.map (algebraMap ℚ ℚ_[ℓ]) σ) = 1) ↔
      ℓ ∉ ramifiedPrimes (fixedField (φ : absoluteGaloisGroup ℚ →* G).ker) := by
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    fixedField (φ : absoluteGaloisGroup ℚ →* G).ker
  have hker : IsOpen ((φ : absoluteGaloisGroup ℚ →* G).ker : Set (absoluteGaloisGroup ℚ)) :=
    (isOpen_discrete {1}).preimage φ.continuous
  have : FiniteDimensional ℚ K := MonoidHom.finiteDimensional_fixedField_ker _ hker
  have : IsGalois ℚ K := MonoidHom.isGalois_fixedField_ker _ hker
  have : NumberField K := ⟨⟩
  rcases exists_absoluteGaloisGroup_map_commutes (algebraMap ℚ ℚ_[ℓ]) with ⟨ι, hι⟩
  rcases exists_forall_apply_eq_self_iff_ramificationIdx_eq_one K ℓ (ι.comp (algebraMap K _)) with
    ⟨w, hw, hwe⟩
  -- `φ` kills the image of `σ` exactly when `σ` fixes the image of `K` in `ℚ̄_ℓ`.
  have hφ (σ : Gal(AlgebraicClosure ℚ_[ℓ]/ℚ_[ℓ])) :
      φ (absoluteGaloisGroup.map (algebraMap ℚ ℚ_[ℓ]) σ) = 1 ↔ ∀ x : K, σ (ι x) = ι x := by
    have h : φ (absoluteGaloisGroup.map (algebraMap ℚ ℚ_[ℓ]) σ) = 1 ↔
        absoluteGaloisGroup.map (algebraMap ℚ ℚ_[ℓ]) σ ∈ K.fixingSubgroup :=
      (SetLike.ext_iff.mp (MonoidHom.fixingSubgroup_fixedField_ker _ hker) _).symm
    refine h.trans ⟨fun h x ↦ (hι σ x).symm.trans (congrArg ι
      ((IntermediateField.mem_fixingSubgroup_iff _ _).mp h x x.2)),
      fun h ↦ (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx ↦ ?_⟩
    exact ι.injective ((hι σ x).trans (h ⟨x, hx⟩))
  have hℓ : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have : w.asIdeal.LiesOver (span {(ℓ : ℤ)}) :=
    (liesOver_span_iff w.isPrime.ne_top hℓ).mpr (by simpa using hw)
  rw [mem_ramifiedPrimes_iff, not_and, imp_iff_right Fact.out, not_not,
    isUnramifiedIn_span_iff_forall_ramificationIdx_eq_one]
  refine ⟨fun h P hP ↦ ?_, fun h σ hσ ↦ (hφ σ).mpr (hwe.mpr (h w hw) σ hσ)⟩
  have : P.asIdeal.LiesOver (span {(ℓ : ℤ)}) :=
    (liesOver_span_iff P.isPrime.ne_top hℓ).mpr (by simpa using hP)
  rw [ramificationIdx_eq_of_isGaloisGroup (span {(ℓ : ℤ)}) P.asIdeal w.asIdeal Gal(K/ℚ)]
  exact hwe.mp fun σ hσ ↦ (hφ σ).mp (h σ hσ)

/-- **The product of the primes ramified in a number field is the product of the prime divisors of
its discriminant**, the radical of the discriminant: a prime ramifies exactly when it divides the
discriminant. -/
lemma finprod_mem_ramifiedPrimes_eq_prod_primeFactors :
    ∏ᶠ p ∈ ramifiedPrimes L, (p : ℝ≥0) = ∏ p ∈ (discr L).natAbs.primeFactors, (p : ℝ≥0) := by
  have h : ramifiedPrimes L = ↑(discr L).natAbs.primeFactors := by
    ext p
    rw [Finset.mem_coe, Nat.mem_primeFactors]
    refine ⟨fun h ↦ ⟨prime_of_mem_ramifiedPrimes h, Int.natCast_dvd.mp
      ((mem_ramifiedPrimes_iff_dvd_discr (prime_of_mem_ramifiedPrimes h)).mp h),
      Int.natAbs_ne_zero.mpr (discr_ne_zero L)⟩,
      fun h ↦ (mem_ramifiedPrimes_iff_dvd_discr h.1).mpr (Int.natCast_dvd.mpr h.2.1)⟩
  rw [h, finprod_mem_coe_finset]

namespace WeightFunction

variable (w : WeightFunction G)

/-- **Local heights are positive** (LMFDB `nf.inertial_height_function`): `H_{w,ℓ}(ψ)` is a real
power of the prime `ℓ`. -/
lemma localHeight_pos (ψ : absoluteGaloisGroup ℚ_[ℓ] →ₜ* G) : 0 < w.localHeight ℓ ψ := by
  rw [localHeight]
  exact NNReal.rpow_pos (Nat.cast_pos.mpr (Fact.out : ℓ.Prime).pos)

/-- **Inertial heights are positive** (LMFDB `nf.inertial_height_function`) when the auxiliary local
heights at the primes dividing `#G` are: an inertial height is a product of positive local
heights. -/
lemma inertialHeight_pos {H : ∀ (ℓ : ℕ) [Fact ℓ.Prime], (absoluteGaloisGroup ℚ_[ℓ] →ₜ* G) → ℝ≥0}
    (hH : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (χ : absoluteGaloisGroup ℚ_[ℓ] →ₜ* G), 0 < H ℓ χ) :
    0 < w.inertialHeight H φ :=
  finprod_induction (0 < ·) one_pos (fun _ _ ↦ mul_pos) fun p ↦
    finprod_induction (0 < ·) one_pos (fun _ _ ↦ mul_pos) fun hp ↦ by
      have : Fact p.Prime := ⟨hp⟩
      split_ifs
      exacts [hH p _, w.localHeight_pos p _]

variable [DiscreteTopology G] [DecidableEq G]

open scoped Classical in
/-- **The radical discriminant is an inertial height** (LMFDB `nf.inertial_height_function`): for
the weight function equal to `1` away from the identity, with the auxiliary local heights `ℓ` or `1`
at the primes `ℓ ∣ #G` according as `χ : Gal(ℚ̄_ℓ/ℚ_ℓ) → G` ramifies or not, the inertial height of
`φ` is the product of the primes ramified in the number field cut out by `φ`. By
`NumberField.finprod_mem_ramifiedPrimes_eq_prod_primeFactors` this is the product of the prime
divisors of its discriminant. -/
lemma inertialHeight_indicator_eq_finprod_ramifiedPrimes :
    letI H (ℓ : ℕ) [Fact ℓ.Prime] (χ : absoluteGaloisGroup ℚ_[ℓ] →ₜ* G) : ℝ≥0 :=
      if (inertiaSubgroup ℚ_[ℓ]).map (χ : absoluteGaloisGroup ℚ_[ℓ] →* G) = ⊥ then 1 else ℓ
    indicator.inertialHeight H φ =
      ∏ᶠ ℓ ∈ ramifiedPrimes (fixedField (φ : absoluteGaloisGroup ℚ →* G).ker), (ℓ : ℝ≥0) := by
  refine (inertialHeight_indicator φ).trans ?_
  rw [finprod_mem_def]
  refine finprod_congr fun p ↦ ?_
  rw [finprod_eq_dif]
  split_ifs with hp
  · have : Fact p.Prime := ⟨hp⟩
    have h : (inertiaSubgroup ℚ_[p]).map
        ((φ.comp (absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])) : absoluteGaloisGroup ℚ_[p] →ₜ* G) :
          absoluteGaloisGroup ℚ_[p] →* G) = ⊥ ↔
        p ∉ ramifiedPrimes (fixedField (φ : absoluteGaloisGroup ℚ →* G).ker) := by
      rw [Subgroup.map_eq_bot_iff, ← forall_apply_map_eq_one_iff_notMem_ramifiedPrimes]
      rfl
    dsimp only
    by_cases hS : p ∈ ramifiedPrimes (fixedField (φ : absoluteGaloisGroup ℚ →* G).ker)
    · rw [Set.mulIndicator_of_mem hS, ite_eq_right (h.not.mpr (not_not.mpr hS))]
    · rw [Set.mulIndicator_of_notMem hS, ite_eq_left (h.mpr hS)]
  · exact (Set.mulIndicator_of_notMem (fun h ↦ hp (prime_of_mem_ramifiedPrimes h)) _).symm

end WeightFunction

end NumberField
