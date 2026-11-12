import LeanBridge.ForMathlib.NumberTheory.ModEllGaloisRep.TopSlope
import LeanBridge.ForMathlib.NumberTheory.LocalField.TopArtinSlopeCompositum

/-!
# The top Artin slope of a number field is that of the compositum of its local fields

Let `L` be a number field and `ℓ` a prime. The top Artin slope of `L` at `ℓ`
(`NumberField.topArtinSlopeAt`, LMFDB `modlgal.top_slope`) is the largest top Artin slope of the
`ℓ`-adic fields `(ℚ_ℓ ⊗ L) / 𝔪` of which the local algebra `ℚ_ℓ ⊗ L` is the product. The Galois
closure of the algebra `ℚ_ℓ ⊗ L` in `ℚ̄_ℓ` (`Algebra.galoisClosure`) is the compositum of the Galois
closures of these fields, since every `ℚ_ℓ`-algebra map `ℚ_ℓ ⊗ L → ℚ̄_ℓ` factors through one of
them, and it is the Galois closure of the compositum of the fields. Its top Artin slope is the
largest of theirs (`IsNonarchimedeanLocalField.topArtinSlopeOfIsGalois_iSup`, from Herbrand's
theorem), so the top Artin slope of `L` at `ℓ` is the top Artin slope of the compositum of the
`ℓ`-adic fields, for every number field `L`; for `L` Galois over `ℚ` this was
`NumberField.topArtinSlopeAt_eq`.

## Main definitions

* `NumberField.galoisClosureFactor`: the Galois closure in `ℚ̄_ℓ` of a factor of `ℚ_ℓ ⊗ L`.

## Main results

* `NumberField.isGreatest_topArtinSlopeAt` (LMFDB `modlgal.top_slope`): the top Artin slope of `L`
  at `ℓ` is the largest top Artin slope of the factors of `ℚ_ℓ ⊗ L`.
* `NumberField.galoisClosure_localAlgebra_eq_iSup`: the Galois closure of `ℚ_ℓ ⊗ L` is the
  compositum of the Galois closures of its factors.
* `NumberField.topArtinSlopeAt_eq_topArtinSlopeOfIsGalois` (LMFDB `modlgal.top_slope`): the top
  Artin slope of `L` at `ℓ` is the top Artin slope of the compositum of the factors of `ℚ_ℓ ⊗ L`.
* `NumberField.isGreatest_wildArtinSlopesOfIsGalois_topArtinSlopeAt` (LMFDB `modlgal.top_slope`):
  when it is neither `0` nor `1`, the top Artin slope of `L` at `ℓ` is the largest wild Artin slope
  of that compositum.
-/

open Algebra Ideal TensorProduct ValuativeRel TauCeti IsNonarchimedeanLocalField
  LocalFieldsRamification

namespace NumberField

variable (L : Type*) [Field L] [NumberField L] (ℓ : ℕ) [Fact ℓ.Prime]

/-- **The top Artin slope at `ℓ` is the largest top Artin slope of the factors** (LMFDB
`modlgal.top_slope`): the local algebra `ℚ_ℓ ⊗ L` has finitely many factors `(ℚ_ℓ ⊗ L) / 𝔪`, at
least one, so the supremum `NumberField.topArtinSlopeAt` of their top Artin slopes is the largest
of them. -/
lemma isGreatest_topArtinSlopeAt : IsGreatest (Set.range fun 𝔪 : MaximalSpectrum (ℚ_[ℓ] ⊗[ℚ] L) ↦
    haveI : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
    letI : Field ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := Quotient.field _
    IsNonarchimedeanLocalField.topArtinSlope ℚ_[ℓ] ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal))
    (topArtinSlopeAt L ℓ) := by
  have : IsArtinianRing (ℚ_[ℓ] ⊗[ℚ] L) := IsArtinianRing.of_finite ℚ_[ℓ] _
  exact ⟨(Set.range_nonempty _).csSup_mem (Set.finite_range _),
    fun _ ⟨𝔪, h⟩ ↦ h ▸ le_ciSup_of_le (Set.finite_range _).bddAbove 𝔪 le_rfl⟩

/-- The Galois closure in `ℚ̄_ℓ` of the factor `(ℚ_ℓ ⊗ L) / 𝔪` of the local algebra of `L`. -/
noncomputable def galoisClosureFactor (𝔪 : MaximalSpectrum (ℚ_[ℓ] ⊗[ℚ] L)) :
    IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]) :=
  haveI : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
  letI : Field ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := Quotient.field _
  galoisClosure ℚ_[ℓ] ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal)

instance (𝔪 : MaximalSpectrum (ℚ_[ℓ] ⊗[ℚ] L)) :
    FiniteDimensional ℚ_[ℓ] (galoisClosureFactor L ℓ 𝔪) := by
  have : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
  let _ : Field ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := Quotient.field _
  exact inferInstanceAs (FiniteDimensional ℚ_[ℓ] (galoisClosure ℚ_[ℓ] ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal)))

instance (𝔪 : MaximalSpectrum (ℚ_[ℓ] ⊗[ℚ] L)) : IsGalois ℚ_[ℓ] (galoisClosureFactor L ℓ 𝔪) := by
  have : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
  let _ : Field ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := Quotient.field _
  exact inferInstanceAs (IsGalois ℚ_[ℓ] (galoisClosure ℚ_[ℓ] ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal)))

/-- **The Galois closure of the local algebra is the compositum of the Galois closures of its
factors**: every `ℚ_ℓ`-algebra map `ℚ_ℓ ⊗ L → ℚ̄_ℓ` has a prime, hence maximal, kernel `𝔪` and
factors through `(ℚ_ℓ ⊗ L) / 𝔪`. -/
lemma galoisClosure_localAlgebra_eq_iSup :
    galoisClosure ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] L) = ⨆ 𝔪, galoisClosureFactor L ℓ 𝔪 := by
  have : IsArtinianRing (ℚ_[ℓ] ⊗[ℚ] L) := IsArtinianRing.of_finite ℚ_[ℓ] _
  refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_) (iSup_le fun 𝔪 ↦ ?_)
  · rintro _ ⟨_, ⟨f, rfl⟩, r, rfl⟩
    have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
    have hmax : (RingHom.ker f).IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
    refine le_iSup (galoisClosureFactor L ℓ) ⟨_, hmax⟩ <| IntermediateField.subset_adjoin _ _
      ⟨_, ⟨Quotient.liftₐ (RingHom.ker f) f fun _ h ↦ h, rfl⟩, Quotient.mk _ r, rfl⟩
  have : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro _ ⟨_, ⟨g, rfl⟩, x, rfl⟩
  rcases Quotient.mkₐ_surjective ℚ_[ℓ] 𝔪.asIdeal x with ⟨r, rfl⟩
  exact IntermediateField.subset_adjoin _ _
    ⟨_, ⟨g.comp (Quotient.mkₐ ℚ_[ℓ] 𝔪.asIdeal), rfl⟩, r, rfl⟩

instance : FiniteDimensional ℚ_[ℓ] (galoisClosure ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] L)) := by
  have : IsArtinianRing (ℚ_[ℓ] ⊗[ℚ] L) := IsArtinianRing.of_finite ℚ_[ℓ] _
  rw [galoisClosure_localAlgebra_eq_iSup]
  infer_instance

instance : IsGalois ℚ_[ℓ] (galoisClosure ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] L)) := by
  have : IsArtinianRing (ℚ_[ℓ] ⊗[ℚ] L) := IsArtinianRing.of_finite ℚ_[ℓ] _
  rw [galoisClosure_localAlgebra_eq_iSup]
  infer_instance

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

/-- **The top Artin slope of a number field at `ℓ` is that of the compositum of its `ℓ`-adic
fields** (LMFDB `modlgal.top_slope`): for every number field `L`, the largest top Artin slope of
the factors `(ℚ_ℓ ⊗ L) / 𝔪` of the local algebra is the top Artin slope of their compositum, whose
Galois closure in `ℚ̄_ℓ` is the Galois closure of `ℚ_ℓ ⊗ L`. -/
lemma topArtinSlopeAt_eq_topArtinSlopeOfIsGalois :
    topArtinSlopeAt L ℓ = topArtinSlopeOfIsGalois ℚ_[ℓ] (galoisClosure ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] L)) := by
  have : IsArtinianRing (ℚ_[ℓ] ⊗[ℚ] L) := IsArtinianRing.of_finite ℚ_[ℓ] _
  have key (N N' : IntermediateField ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])) [FiniteDimensional ℚ_[ℓ] N]
      [IsGalois ℚ_[ℓ] N] [FiniteDimensional ℚ_[ℓ] N'] [IsGalois ℚ_[ℓ] N'] (h : N = N') :
      topArtinSlopeOfIsGalois ℚ_[ℓ] N = topArtinSlopeOfIsGalois ℚ_[ℓ] N' := by
    subst h
    rfl
  rw [key _ _ (galoisClosure_localAlgebra_eq_iSup L ℓ), topArtinSlopeOfIsGalois_iSup]
  rfl

/-- **Otherwise the top Artin slope at `ℓ` is the largest wild Artin slope** (LMFDB
`modlgal.top_slope`): when the top Artin slope of `L` at `ℓ` is neither `0` nor `1`, the compositum
of the factors of `ℚ_ℓ ⊗ L` is wildly ramified, and the top Artin slope is the largest of its wild
Artin slopes. -/
lemma isGreatest_wildArtinSlopesOfIsGalois_topArtinSlopeAt (h0 : topArtinSlopeAt L ℓ ≠ 0)
    (h1 : topArtinSlopeAt L ℓ ≠ 1) : IsGreatest
      {s | s ∈ wildArtinSlopesOfIsGalois ℚ_[ℓ] (galoisClosure ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] L))}
      (topArtinSlopeAt L ℓ) := by
  rw [topArtinSlopeAt_eq_topArtinSlopeOfIsGalois] at h0 h1 ⊢
  have hG : lowerRamificationGroup ℚ_[ℓ] (galoisClosure ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] L)) 1 ≠ ⊥ := fun hG ↦
    h1 <| (topArtinSlopeOfIsGalois_eq_one_iff _ _).mpr
      ⟨(lowerRamificationGroup_one_eq_bot_iff_isTamelyRamified _ _).mp hG,
        fun hU ↦ h0 <| (topArtinSlopeOfIsGalois_eq_zero_iff _ _).mpr hU⟩
  exact ⟨topArtinSlopeOfIsGalois_mem _ _ hG, fun _ hs ↦ le_topArtinSlopeOfIsGalois _ _ hs⟩

end NumberField
