import LeanBridge.ForMathlib.NumberTheory.ModEllGaloisRep.TopSlope
import LeanBridge.ForMathlib.NumberTheory.LocalField.GaloisClosureRamification
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import TauCeti.NumberTheory.LocalField.Padic
import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic
import TauCeti.RingTheory.DedekindDomain.AdicValuation.IntegralClosure
import TauCeti.RingTheory.DedekindDomain.AdicValuation.RamificationIndex
import TauCeti.Topology.Algebra.ValuativeRel.ContinuousRingHom

/-!
# Top Artin slopes `0` and `1` of a number field: unramified and tamely ramified primes

Let `L` be a number field and `ℓ` a prime, and let `v` be the place of `ℚ` at `ℓ`. The local algebra
`ℚ_ℓ ⊗ L` (LMFDB `nf.local_algebra`) is the product of the completions `L_w` of `L` at the places
`w` above `v` (Tau Ceti's semi-local decomposition, with `ℚ_ℓ ≅ ℚ_v`): the map
`ℚ_ℓ ⊗ L → L_w`, `a ⊗ x ↦ a x`, is onto, and its kernels are the maximal ideals of `ℚ_ℓ ⊗ L`. So
the factors `(ℚ_ℓ ⊗ L) / 𝔪` of the local algebra are the completions `L_w`, and the ramification
index of `L_w / ℚ_ℓ` is the ramification index `e(w | ℓ)` (Tau Ceti). With the top Artin slope of
an extension of local fields being `0` exactly for unramified and at most `1` exactly for tamely
ramified extensions, this gives the statements of LMFDB `modlgal.top_slope`: the top Artin slope
of `L` at `ℓ` (`NumberField.topArtinSlopeAt`) is `0` exactly when `L` is unramified at `ℓ`, at most
`1` exactly when `L` is tamely ramified at `ℓ` (`ℓ ∤ e(w | ℓ)` for every `w`), and `1` exactly when
`L` is tamely ramified but not unramified at `ℓ`. These hold for every number field `L`, Galois
over `ℚ` or not.

## Main definitions

* `Padic.ringEquivAdicCompletion`: Mathlib's isomorphism `ℚ_ℓ ≃ ℚ_v`, as a ring isomorphism.
* `NumberField.localAlgebraToCompletion`: the map `ℚ_ℓ ⊗ L → L_w`, `a ⊗ x ↦ a x`.

## Main results

* `NumberField.ramificationIndex_quotient_eq`: the factor of `ℚ_ℓ ⊗ L` that is the completion `L_w`
  has ramification index over `ℚ_ℓ` the ramification index of `w`.
* `NumberField.exists_eq_ker_localAlgebraToCompletion`: every maximal ideal of `ℚ_ℓ ⊗ L` is the
  kernel of the map to some completion `L_w`.
* `NumberField.topArtinSlopeAt_eq_zero_iff` (LMFDB `modlgal.top_slope`): the top Artin slope of
  `L` at `ℓ` is `0` exactly when `L` is unramified at `ℓ`.
* `NumberField.topArtinSlopeAt_le_one_iff` (LMFDB `modlgal.top_slope`): it is at most `1` exactly
  when `L` is tamely ramified at `ℓ`.
* `NumberField.topArtinSlopeAt_eq_one_iff` (LMFDB `modlgal.top_slope`): it is `1` exactly when `L`
  is tamely ramified but not unramified at `ℓ`.
* `MonoidHom.topArtinSlope_eq_zero_iff`, `MonoidHom.topArtinSlope_eq_one_iff` (LMFDB
  `modlgal.top_slope`): the same for the top Artin slope of a mod-`ℓ` Galois representation and
  its splitting field.
-/

open IsDedekindDomain NumberField ValuativeRel TauCeti IsNonarchimedeanLocalField Ideal Algebra
  TensorProduct Rat Ring

open scoped AdicCompletionExtension

namespace Padic

variable (ℓ : ℕ) [Fact ℓ.Prime]

-- Mathlib's isomorphism `ℚ_ℓ ≃A[ℚ] ℚ_v` is stated for the `ℚ`-algebra structure of `ℚ_v` as a
-- completion of `ℚ`, which instance search does not find here; only its ring structure is used.
attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion in
/-- The isomorphism `ℚ_ℓ ≃ ℚ_v` of the `ℓ`-adic numbers with the completion of `ℚ` at the place `v`
at `ℓ` (Mathlib's `Padic.adicCompletionEquiv`), as a ring isomorphism. -/
noncomputable def ringEquivAdicCompletion :
    ℚ_[ℓ] ≃+* ((HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨ℓ, Fact.out⟩).adicCompletion ℚ :=
  (adicCompletionEquiv (𝓞 ℚ) ⟨ℓ, Fact.out⟩).toAlgEquiv.toRingEquiv

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion in
lemma continuous_ringEquivAdicCompletion : Continuous (ringEquivAdicCompletion ℓ) :=
  (adicCompletionEquiv (𝓞 ℚ) ⟨ℓ, Fact.out⟩).continuous

lemma ringChar_residueField : ringChar 𝓀[ℚ_[ℓ]] = ℓ :=
  CharP.ringChar_of_prime_eq_zero Fact.out <| by
    rw [← map_natCast (IsLocalRing.residue 𝒪[ℚ_[ℓ]]), IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mpr (Padic.irreducible_natCast_self ℓ).not_isUnit

end Padic

namespace NumberField

variable (L : Type*) [Field L] [NumberField L] (ℓ : ℕ) [Fact ℓ.Prime] {v : HeightOneSpectrum (𝓞 ℚ)}
  (e : ℚ_[ℓ] ≃+* v.adicCompletion ℚ) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- The map `ℚ_ℓ ⊗ L → L_w`, `a ⊗ x ↦ e(a) x`, from the local algebra of a number field `L` to its
completion `L_w` at a place `w` above a finite place `v` of `ℚ`, through an isomorphism
`e : ℚ_ℓ ≃ ℚ_v`. -/
noncomputable def localAlgebraToCompletion : ℚ_[ℓ] ⊗[ℚ] L →ₐ[ℚ] w.adicCompletion L :=
  lift ((algebraMap (v.adicCompletion ℚ) (w.adicCompletion L)).comp (e : ℚ_[ℓ] →+* _)).toRatAlgHom
    (algebraMap L (w.adicCompletion L)).toRatAlgHom fun _ _ ↦ .all _ _

lemma localAlgebraToCompletion_tmul (a : ℚ_[ℓ]) (x : L) :
    localAlgebraToCompletion L ℓ e w (a ⊗ₜ x) =
      algebraMap (v.adicCompletion ℚ) (w.adicCompletion L) (e a) * algebraMap L _ x :=
  lift_tmul _ _ _ a x

lemma localAlgebraToCompletion_surjective :
    Function.Surjective (localAlgebraToCompletion L ℓ e w) := by
  classical
  intro y
  rcases semilocalHom_surjective (K := ℚ) L v (Pi.single ⟨w, ‹_›⟩ y) with ⟨t, ht⟩
  -- The tensor product of `semilocalHom` is taken for the `ℚ`-algebra structure of `ℚ_v` as a
  -- completion of `ℚ`, which is not the one found by instance search; we pass it explicitly.
  rcases @TensorProduct.inductionOn ℚ _ _ _ _ _
    (HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v).toModule _
    (fun t ↦ ∃ s, localAlgebraToCompletion L ℓ e w s = semilocalHom L v t ⟨w, ‹_›⟩) t
    (fun a x ↦ ⟨e.symm a ⊗ₜ x, by
      rw [localAlgebraToCompletion_tmul, semilocalHom_tmul, RingEquiv.apply_symm_apply]⟩)
    (fun _ _ ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩ ↦ ⟨s₁ + s₂, by rw [map_add, map_add, Pi.add_apply, hs₁, hs₂]⟩)
    with ⟨s, hs⟩
  exact ⟨s, by rw [hs, ht, Pi.single_eq_same]⟩

/-- **The ramification index of a factor of the local algebra is the global one**: for a maximal
ideal `𝔪` of `ℚ_ℓ ⊗ L`, the kernel of the map to the completion `L_w` at a place `w` above `ℓ`, the
ramification index of `(ℚ_ℓ ⊗ L) / 𝔪 ≅ L_w` over `ℚ_ℓ` is the ramification index of `w` over
`𝓞 ℚ ≅ ℤ`. -/
lemma ramificationIndex_quotient_eq (he : Continuous e) (𝔪 : MaximalSpectrum (ℚ_[ℓ] ⊗[ℚ] L))
    (h : 𝔪.asIdeal = RingHom.ker (localAlgebraToCompletion L ℓ e w)) :
    haveI : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
    letI : Field ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := Quotient.field _
    letI : ValuativeRel ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := algebraicExtensionValuativeRel ℚ_[ℓ] _
    letI : TopologicalSpace ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) :=
      algebraicExtensionNormedFieldTopology ℚ_[ℓ] _
    haveI : IsNonarchimedeanLocalField ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) :=
      finiteExtension_isNonarchimedeanLocalField ℚ_[ℓ] _
    ramificationIndex ℚ_[ℓ] ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) = w.asIdeal.ramificationIdx (𝓞 ℚ) := by
  have : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
  let _ : Field ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := Quotient.field _
  let _ : ValuativeRel ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := algebraicExtensionValuativeRel ℚ_[ℓ] _
  let _ : TopologicalSpace ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) :=
    algebraicExtensionNormedFieldTopology ℚ_[ℓ] _
  have : IsNonarchimedeanLocalField ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) :=
    finiteExtension_isNonarchimedeanLocalField ℚ_[ℓ] _
  have : ValuativeExtension ℚ_[ℓ] ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) :=
    algebraicExtension_valuativeExtension ℚ_[ℓ] _
  have : Finite (𝓞 ℚ ⧸ v.asIdeal) := HasFiniteQuotients.finiteQuotient v.ne_bot
  have : Finite (𝓞 L ⧸ w.asIdeal) := HasFiniteQuotients.finiteQuotient w.ne_bot
  let _ : Algebra ℚ_[ℓ] (v.adicCompletion ℚ) := (e : ℚ_[ℓ] →+* v.adicCompletion ℚ).toAlgebra
  let _ : Algebra ℚ_[ℓ] (w.adicCompletion L) :=
    ((algebraMap (v.adicCompletion ℚ) (w.adicCompletion L)).comp
      (e : ℚ_[ℓ] →+* v.adicCompletion ℚ)).toAlgebra
  have : IsScalarTower ℚ_[ℓ] (v.adicCompletion ℚ) (w.adicCompletion L) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : ValuativeExtension ℚ_[ℓ] (v.adicCompletion ℚ) := .of_continuous_algebraMap he
  have : ValuativeExtension ℚ_[ℓ] (w.adicCompletion L) :=
    .trans ℚ_[ℓ] (v.adicCompletion ℚ) (w.adicCompletion L)
  have h1 : Module.finrank ℚ_[ℓ] (v.adicCompletion ℚ) = 1 :=
    Module.finrank_of_bijective_algebraMap e.bijective
  let ψ : ℚ_[ℓ] ⊗[ℚ] L →ₐ[ℚ_[ℓ]] w.adicCompletion L :=
    { localAlgebraToCompletion L ℓ e w with
      commutes' := fun a ↦ by
        simp [localAlgebraToCompletion_tmul, RingHom.algebraMap_toAlgebra] }
  let σ : ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) ≃ₐ[ℚ_[ℓ]] w.adicCompletion L :=
    (Ideal.quotientEquivAlgOfEq ℚ_[ℓ] h).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := ψ) (localAlgebraToCompletion_surjective L ℓ e w))
  rw [ramificationIndex_eq_of_algEquiv σ,
    ramificationIndex_tower (K := ℚ_[ℓ]) (L := v.adicCompletion ℚ) (w.adicCompletion L),
    (mul_eq_one.mp ((ramificationIndex_mul_inertiaDegree ℚ_[ℓ] (v.adicCompletion ℚ)).trans h1)).1,
    one_mul, HeightOneSpectrum.ramificationIndex_adicCompletion v w]

lemma topArtinSlope_quotient_eq_zero_iff (he : Continuous e) (𝔪 : MaximalSpectrum (ℚ_[ℓ] ⊗[ℚ] L))
    (h : 𝔪.asIdeal = RingHom.ker (localAlgebraToCompletion L ℓ e w)) :
    haveI : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
    letI : Field ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := Quotient.field _
    topArtinSlope ℚ_[ℓ] ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) = 0 ↔ w.asIdeal.ramificationIdx (𝓞 ℚ) = 1 := by
  have : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
  let _ : Field ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := Quotient.field _
  let _ : ValuativeRel ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := algebraicExtensionValuativeRel ℚ_[ℓ] _
  let _ : TopologicalSpace ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) :=
    algebraicExtensionNormedFieldTopology ℚ_[ℓ] _
  have : IsNonarchimedeanLocalField ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) :=
    finiteExtension_isNonarchimedeanLocalField ℚ_[ℓ] _
  have : ValuativeExtension ℚ_[ℓ] ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) :=
    algebraicExtension_valuativeExtension ℚ_[ℓ] _
  rw [topArtinSlope_eq_zero_iff_isUnramified, isUnramified_iff_ramificationIndex_eq_one,
    ramificationIndex_quotient_eq L ℓ e w he 𝔪 h]

lemma topArtinSlope_quotient_le_one_iff (he : Continuous e) (𝔪 : MaximalSpectrum (ℚ_[ℓ] ⊗[ℚ] L))
    (h : 𝔪.asIdeal = RingHom.ker (localAlgebraToCompletion L ℓ e w)) :
    haveI : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
    letI : Field ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := Quotient.field _
    topArtinSlope ℚ_[ℓ] ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) ≤ 1 ↔
      ¬ℓ ∣ w.asIdeal.ramificationIdx (𝓞 ℚ) := by
  have : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
  let _ : Field ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := Quotient.field _
  let _ : ValuativeRel ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := algebraicExtensionValuativeRel ℚ_[ℓ] _
  let _ : TopologicalSpace ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) :=
    algebraicExtensionNormedFieldTopology ℚ_[ℓ] _
  have : IsNonarchimedeanLocalField ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) :=
    finiteExtension_isNonarchimedeanLocalField ℚ_[ℓ] _
  have : ValuativeExtension ℚ_[ℓ] ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) :=
    algebraicExtension_valuativeExtension ℚ_[ℓ] _
  rw [topArtinSlope_le_one_iff_isTamelyRamified, isTamelyRamified_iff,
    ramificationIndex_quotient_eq L ℓ e w he 𝔪 h, Padic.ringChar_residueField]

/-- **The maximal ideals of the local algebra are the kernels of the maps to the completions**:
every maximal ideal of `ℚ_ℓ ⊗ L` is the kernel of `ℚ_ℓ ⊗ L → L_w` for a place `w` above `ℓ`. The
map `ℚ_ℓ ⊗ L → ∏_{w ∣ ℓ} L_w` is onto (Tau Ceti's semi-local decomposition) between spaces of the
same dimension `[L : ℚ]` over `ℚ_ℓ`, hence injective, so the intersection of the kernels is `0`. -/
lemma exists_eq_ker_localAlgebraToCompletion (𝔪 : MaximalSpectrum (ℚ_[ℓ] ⊗[ℚ] L)) :
    ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}, 𝔪.asIdeal =
      RingHom.ker (localAlgebraToCompletion L ℓ e w.1) := by
  classical
  let W : Type _ := {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}
  let _ : Fintype W := Fintype.ofFinite W
  have : Finite (𝓞 ℚ ⧸ v.asIdeal) := HasFiniteQuotients.finiteQuotient v.ne_bot
  let _ : Algebra ℚ_[ℓ] (v.adicCompletion ℚ) := (e : ℚ_[ℓ] →+* v.adicCompletion ℚ).toAlgebra
  let _ (w : W) : Algebra ℚ_[ℓ] (w.1.adicCompletion L) :=
    ((algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion L)).comp
      (e : ℚ_[ℓ] →+* v.adicCompletion ℚ)).toAlgebra
  have (w : W) : IsScalarTower ℚ_[ℓ] (v.adicCompletion ℚ) (w.1.adicCompletion L) :=
    .of_algebraMap_eq fun _ ↦ rfl
  let ψ (w : W) : ℚ_[ℓ] ⊗[ℚ] L →ₐ[ℚ_[ℓ]] w.1.adicCompletion L :=
    { localAlgebraToCompletion L ℓ e w.1 with
      commutes' := fun a ↦ by
        simp [localAlgebraToCompletion_tmul, RingHom.algebraMap_toAlgebra] }
  let Φ : ℚ_[ℓ] ⊗[ℚ] L →ₐ[ℚ_[ℓ]] ∀ w : W, w.1.adicCompletion L := AlgHom.pi ψ
  have hsurj : Function.Surjective Φ := by
    intro y
    rcases semilocalHom_surjective (K := ℚ) L v y with ⟨t, ht⟩
    -- The tensor product of `semilocalHom` is taken for the `ℚ`-algebra structure of `ℚ_v` as a
    -- completion of `ℚ`, which is not the one found by instance search; we pass it explicitly.
    rcases @TensorProduct.inductionOn ℚ _ _ _ _ _
      (HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v).toModule _
      (fun t ↦ ∃ s, Φ s = semilocalHom L v t) t
      (fun a x ↦ ⟨e.symm a ⊗ₜ x, funext fun w ↦ by
        simp [Φ, ψ, localAlgebraToCompletion_tmul]⟩)
      (fun _ _ ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩ ↦ ⟨s₁ + s₂, by rw [map_add, map_add, hs₁, hs₂]⟩)
      with ⟨s, hs⟩
    exact ⟨s, hs.trans ht⟩
  have h1 : Module.finrank ℚ_[ℓ] (v.adicCompletion ℚ) = 1 :=
    Module.finrank_of_bijective_algebraMap e.bijective
  have : Module.Finite ℚ_[ℓ] (v.adicCompletion ℚ) := Module.finite_of_finrank_eq_succ h1
  have (w : W) : Finite (𝓞 L ⧸ w.1.asIdeal) := HasFiniteQuotients.finiteQuotient w.1.ne_bot
  have (w : W) : Module.Finite ℚ_[ℓ] (w.1.adicCompletion L) :=
    .trans (v.adicCompletion ℚ) (w.1.adicCompletion L)
  have hdim : Module.finrank ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] L) =
      Module.finrank ℚ_[ℓ] (∀ w : W, w.1.adicCompletion L) := by
    rw [Module.finrank_baseChange, Module.finrank_pi_fintype,
      ← sum_finrank_adicCompletion_eq_finrank (K := ℚ) L v]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [← Module.finrank_mul_finrank ℚ_[ℓ] (v.adicCompletion ℚ), h1, one_mul]
  have hinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := Φ.toLinearMap)).mpr hsurj
  have hle : Finset.univ.inf (fun w : W ↦ RingHom.ker (localAlgebraToCompletion L ℓ e w.1)) ≤
      𝔪.asIdeal := by
    intro x hx
    rw [Submodule.mem_finsetInf] at hx
    have hx0 : x = 0 := hinj <| funext fun w ↦ by simpa [Φ, ψ] using hx w (Finset.mem_univ w)
    exact hx0 ▸ 𝔪.asIdeal.zero_mem
  rcases 𝔪.isMaximal.isPrime.inf_le'.mp hle with ⟨w, -, hw⟩
  exact ⟨w, ((RingHom.ker_isMaximal_of_surjective _
    (localAlgebraToCompletion_surjective L ℓ e w.1)).eq_of_le 𝔪.isMaximal.ne_top hw).symm⟩

lemma topArtinSlopeAt_eq_zero_iff_forall : topArtinSlopeAt L ℓ = 0 ↔
    ∀ 𝔪 : MaximalSpectrum (ℚ_[ℓ] ⊗[ℚ] L),
      haveI : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
      letI : Field ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := Quotient.field _
      topArtinSlope ℚ_[ℓ] ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) = 0 := by
  have : IsArtinianRing (ℚ_[ℓ] ⊗[ℚ] L) := IsArtinianRing.of_finite ℚ_[ℓ] _
  rw [topArtinSlopeAt]
  refine ⟨fun h 𝔪 ↦ ?_, fun h ↦ (iSup_congr h).trans ciSup_const⟩
  have : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
  let _ : Field ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := Quotient.field _
  exact le_antisymm ((le_ciSup (Set.finite_range _).bddAbove 𝔪).trans_eq h)
    (topArtinSlope_nonneg _)

lemma topArtinSlopeAt_le_one_iff_forall : topArtinSlopeAt L ℓ ≤ 1 ↔
    ∀ 𝔪 : MaximalSpectrum (ℚ_[ℓ] ⊗[ℚ] L),
      haveI : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
      letI : Field ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := Quotient.field _
      topArtinSlope ℚ_[ℓ] ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) ≤ 1 := by
  have : IsArtinianRing (ℚ_[ℓ] ⊗[ℚ] L) := IsArtinianRing.of_finite ℚ_[ℓ] _
  exact ciSup_le_iff (Set.finite_range _).bddAbove

lemma natCast_mem_primesEquiv_symm :
    (ℓ : 𝓞 ℚ) ∈ ((HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨ℓ, Fact.out⟩).asIdeal := by
  have h : (IsIntegralClosure.intEquiv (𝓞 ℚ)).symm (ℓ : ℤ) ∈ (span {(ℓ : ℤ)}).map
      (IsIntegralClosure.intEquiv (𝓞 ℚ)).symm :=
    mem_map_of_mem _ (mem_span_singleton_self (ℓ : ℤ))
  rwa [map_natCast] at h

lemma liesOver_primesEquiv_symm_iff :
    w.asIdeal.LiesOver ((HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨ℓ, Fact.out⟩).asIdeal ↔
      (ℓ : 𝓞 L) ∈ w.asIdeal := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨?_⟩⟩
  · have hmem : (ℓ : 𝓞 ℚ) ∈ w.asIdeal.under (𝓞 ℚ) := h.over ▸ natCast_mem_primesEquiv_symm ℓ
    rwa [Ideal.under, Ideal.mem_comap, map_natCast] at hmem
  refine (HeightOneSpectrum.isMaximal _).eq_of_le (IsPrime.ne_top inferInstance) ?_
  refine Ideal.map_le_of_le_comap ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  rwa [Ideal.mem_comap, map_natCast, Ideal.under, Ideal.mem_comap, map_natCast]

lemma ramificationIdx_ringOfIntegers_rat (P : Ideal (𝓞 L)) [P.IsPrime] :
    P.ramificationIdx (𝓞 ℚ) = P.ramificationIdx ℤ := by
  have h1 : P.under ℤ = (P.under (𝓞 ℚ)).comap (algebraMap ℤ (𝓞 ℚ)) := by
    rw [Ideal.under, Ideal.under, Ideal.comap_comap, RingHom.ext_int (algebraMap ℤ (𝓞 L))]
  have h2 : algebraMap ℤ (Localization.AtPrime P) =
      (algebraMap (𝓞 ℚ) (Localization.AtPrime P)).comp (algebraMap ℤ (𝓞 ℚ)) :=
    RingHom.ext_int _ _
  rw [Ideal.ramificationIdx_def, Ideal.ramificationIdx_def, h1, h2, ← Ideal.map_map,
    Ideal.map_comap_of_surjective _ (Rat.int_algebraMap_surjective (𝓞 ℚ))]

/-- **Top Artin slope `0` at `ℓ` means unramified at `ℓ`** (LMFDB `modlgal.top_slope`): the top
Artin slope of a number field `L` at a prime `ℓ` is `0` exactly when `L` is unramified at `ℓ`, that
is when every prime of `𝓞 L` above `ℓ` has ramification index `1` over `ℤ`. -/
lemma topArtinSlopeAt_eq_zero_iff : topArtinSlopeAt L ℓ = 0 ↔ ∀ P : HeightOneSpectrum (𝓞 L),
    (ℓ : 𝓞 L) ∈ P.asIdeal → P.asIdeal.ramificationIdx ℤ = 1 := by
  rw [topArtinSlopeAt_eq_zero_iff_forall]
  refine ⟨fun h P hP ↦ ?_, fun h 𝔪 ↦ ?_⟩
  · have : P.asIdeal.LiesOver _ := (liesOver_primesEquiv_symm_iff L ℓ P).mpr hP
    let 𝔪 : MaximalSpectrum (ℚ_[ℓ] ⊗[ℚ] L) := ⟨_, RingHom.ker_isMaximal_of_surjective _
      (localAlgebraToCompletion_surjective L ℓ (Padic.ringEquivAdicCompletion ℓ) P)⟩
    rw [← ramificationIdx_ringOfIntegers_rat]
    exact (topArtinSlope_quotient_eq_zero_iff L ℓ _ P (Padic.continuous_ringEquivAdicCompletion ℓ)
      𝔪 rfl).mp (h 𝔪)
  rcases exists_eq_ker_localAlgebraToCompletion L ℓ (Padic.ringEquivAdicCompletion ℓ) 𝔪 with
    ⟨⟨P, hP⟩, hP'⟩
  refine (topArtinSlope_quotient_eq_zero_iff L ℓ _ P (Padic.continuous_ringEquivAdicCompletion ℓ)
    𝔪 hP').mpr ?_
  rw [ramificationIdx_ringOfIntegers_rat]
  exact h P ((liesOver_primesEquiv_symm_iff L ℓ P).mp hP)

/-- **Top Artin slope at most `1` at `ℓ` means tamely ramified at `ℓ`** (LMFDB
`modlgal.top_slope`): the top Artin slope of a number field `L` at a prime `ℓ` is at most `1`
exactly when `L` is tamely ramified at `ℓ`, that is when `ℓ` divides the ramification index over
`ℤ` of no prime of `𝓞 L` above `ℓ`. -/
lemma topArtinSlopeAt_le_one_iff : topArtinSlopeAt L ℓ ≤ 1 ↔ ∀ P : HeightOneSpectrum (𝓞 L),
    (ℓ : 𝓞 L) ∈ P.asIdeal → ¬ℓ ∣ P.asIdeal.ramificationIdx ℤ := by
  rw [topArtinSlopeAt_le_one_iff_forall]
  refine ⟨fun h P hP ↦ ?_, fun h 𝔪 ↦ ?_⟩
  · have : P.asIdeal.LiesOver _ := (liesOver_primesEquiv_symm_iff L ℓ P).mpr hP
    let 𝔪 : MaximalSpectrum (ℚ_[ℓ] ⊗[ℚ] L) := ⟨_, RingHom.ker_isMaximal_of_surjective _
      (localAlgebraToCompletion_surjective L ℓ (Padic.ringEquivAdicCompletion ℓ) P)⟩
    rw [← ramificationIdx_ringOfIntegers_rat]
    exact (topArtinSlope_quotient_le_one_iff L ℓ _ P (Padic.continuous_ringEquivAdicCompletion ℓ)
      𝔪 rfl).mp (h 𝔪)
  rcases exists_eq_ker_localAlgebraToCompletion L ℓ (Padic.ringEquivAdicCompletion ℓ) 𝔪 with
    ⟨⟨P, hP⟩, hP'⟩
  refine (topArtinSlope_quotient_le_one_iff L ℓ _ P (Padic.continuous_ringEquivAdicCompletion ℓ)
    𝔪 hP').mpr ?_
  rw [ramificationIdx_ringOfIntegers_rat]
  exact h P ((liesOver_primesEquiv_symm_iff L ℓ P).mp hP)

/-- **Top Artin slope `1` at `ℓ` means tamely ramified but not unramified at `ℓ`** (LMFDB
`modlgal.top_slope`): the top Artin slope of a number field `L` at a prime `ℓ` is `1` exactly when
`L` is tamely ramified at `ℓ` (`NumberField.topArtinSlopeAt_le_one_iff`) but not unramified at `ℓ`
(`NumberField.topArtinSlopeAt_eq_zero_iff`). -/
lemma topArtinSlopeAt_eq_one_iff : topArtinSlopeAt L ℓ = 1 ↔ (∀ P : HeightOneSpectrum (𝓞 L),
    (ℓ : 𝓞 L) ∈ P.asIdeal → ¬ℓ ∣ P.asIdeal.ramificationIdx ℤ) ∧ ¬∀ P : HeightOneSpectrum (𝓞 L),
      (ℓ : 𝓞 L) ∈ P.asIdeal → P.asIdeal.ramificationIdx ℤ = 1 := by
  rw [← topArtinSlopeAt_le_one_iff, ← topArtinSlopeAt_eq_zero_iff]
  refine ⟨fun h ↦ ⟨h.le, by rw [h]; exact one_ne_zero⟩, fun ⟨h1, h0⟩ ↦ le_antisymm h1 ?_⟩
  rcases not_forall.mp (mt (topArtinSlopeAt_eq_zero_iff_forall L ℓ).mpr h0) with ⟨𝔪, h𝔪⟩
  have : IsArtinianRing (ℚ_[ℓ] ⊗[ℚ] L) := IsArtinianRing.of_finite ℚ_[ℓ] _
  have : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
  let _ : Field ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := Quotient.field _
  have h𝔪1 : topArtinSlope ℚ_[ℓ] ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) ≤ 1 :=
    (topArtinSlopeAt_le_one_iff_forall L ℓ).mp h1 𝔪
  rw [topArtinSlopeAt]
  exact le_ciSup_of_le (Set.finite_range _).bddAbove 𝔪 (topArtinSlope_eq_one_of_le_one h𝔪1 h𝔪).ge

end NumberField

namespace MonoidHom

variable {K : Type*} [Field K] [NumberField K] {n ℓ : ℕ} [Fact ℓ.Prime]
  {ρ : Gal(AlgebraicClosure K/K) →* GL (Fin n) (ZMod ℓ)}
  (hρ : IsOpen (ρ.ker : Set Gal(AlgebraicClosure K/K)))

/-- **Top slope `0` means an unramified splitting field** (LMFDB `modlgal.top_slope`): the top
Artin slope of a mod-`ℓ` Galois representation `ρ` is `0` exactly when its splitting field `L` is
unramified at `ℓ`: every prime of `𝓞 L` above `ℓ` has ramification index `1` over `ℤ`. -/
lemma topArtinSlope_eq_zero_iff : ρ.topArtinSlope hρ = 0 ↔
    ∀ P : HeightOneSpectrum (𝓞 (splittingField ρ hρ)), (ℓ : 𝓞 (splittingField ρ hρ)) ∈ P.asIdeal →
      P.asIdeal.ramificationIdx ℤ = 1 :=
  NumberField.topArtinSlopeAt_eq_zero_iff _ ℓ

/-- **Top slope `1` means a tamely ramified, ramified splitting field** (LMFDB
`modlgal.top_slope`): the top Artin slope of a mod-`ℓ` Galois representation `ρ` is `1` exactly
when its splitting field `L` is tamely ramified but not unramified at `ℓ`. -/
lemma topArtinSlope_eq_one_iff : ρ.topArtinSlope hρ = 1 ↔
    (∀ P : HeightOneSpectrum (𝓞 (splittingField ρ hρ)), (ℓ : 𝓞 (splittingField ρ hρ)) ∈ P.asIdeal →
      ¬ℓ ∣ P.asIdeal.ramificationIdx ℤ) ∧ ¬∀ P : HeightOneSpectrum (𝓞 (splittingField ρ hρ)),
        (ℓ : 𝓞 (splittingField ρ hρ)) ∈ P.asIdeal → P.asIdeal.ramificationIdx ℤ = 1 :=
  NumberField.topArtinSlopeAt_eq_one_iff _ ℓ

end MonoidHom
