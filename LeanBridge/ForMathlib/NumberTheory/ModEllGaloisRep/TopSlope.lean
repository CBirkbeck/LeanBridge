import LeanBridge.ForMathlib.NumberTheory.LocalField.TopArtinSlope
import LeanBridge.ForMathlib.NumberTheory.ModEllGaloisRep.Frobenius
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import TauCeti.FieldTheory.Galois.Restriction

/-!
# The top Artin slope of a mod-`ℓ` Galois representation

Let `L` be a number field and `ℓ` a prime. The local algebra `ℚ_ℓ ⊗ L` (LMFDB `nf.local_algebra`)
is a finite product of `ℓ`-adic fields, its quotients `(ℚ_ℓ ⊗ L) / 𝔪` by its maximal ideals `𝔪`,
and the top Artin slope of `L` at `ℓ` is the largest top Artin slope (LMFDB `lf.top_slope`) of these
fields over `ℚ_ℓ`. The top Artin slope of a mod-`ℓ` Galois representation `ρ` is that of its
splitting field at `ℓ`.

The top Artin slope of an `ℓ`-adic field `F` is the largest `s` with `G^{(s)}` nontrivial, for the
Galois group `G` of the Galois closure of `F / ℚ_ℓ`, and the Galois closure of the algebra
`ℚ_ℓ ⊗ L` (`Algebra.galoisClosure`) is the compositum of those of its factors. When `L` is Galois
over `ℚ`, as is the splitting field of a representation of `Gal(ℚ̄/ℚ)`, every factor has this
compositum as its Galois closure, so the top Artin slope of `L` at `ℓ` is the top Artin slope of
the compositum, and of every factor. For a non-Galois `L` the equality with the top Artin slope of
the compositum rests on the compatibility of the upper numbering with quotients (Herbrand's
theorem), which is not formalised here.

## Main definitions

* `NumberField.topArtinSlopeAt` (LMFDB `modlgal.top_slope`): the top Artin slope of a number field
  at `ℓ`.
* `MonoidHom.topArtinSlope` (LMFDB `modlgal.top_slope`): the top Artin slope of a mod-`ℓ` Galois
  representation.

## Main results

* `IsNonarchimedeanLocalField.topArtinSlope_eq_of_galoisClosure_eq`: the top Artin slope of a
  finite separable extension depends only on its Galois closure.
* `NumberField.galoisClosure_quotient_eq`: for `L` Galois over `ℚ`, each factor of `ℚ_ℓ ⊗ L` has
  the compositum of all the factors as its Galois closure.
* `NumberField.topArtinSlopeAt_eq`: for `L` Galois over `ℚ`, the top Artin slope of `L` at `ℓ` is
  that of each factor of `ℚ_ℓ ⊗ L`.
-/

open Algebra Ideal TensorProduct ValuativeRel TauCeti

namespace IsNonarchimedeanLocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {E E' : Type*} [Field E] [Algebra K E] [FiniteDimensional K E] [Algebra.IsSeparable K E]
  [Field E'] [Algebra K E'] [FiniteDimensional K E'] [Algebra.IsSeparable K E']

/-- **The top Artin slope depends only on the Galois closure**: two finite separable extensions of
a nonarchimedean local field with the same Galois closure in `K̄` have the same top Artin slope. -/
lemma topArtinSlope_eq_of_galoisClosure_eq
    (h : Algebra.galoisClosure K E = Algebra.galoisClosure K E') :
    topArtinSlope K E = topArtinSlope K E' := by
  have key (M M' : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K M] [IsGalois K M]
      [FiniteDimensional K M'] [IsGalois K M'] (hM : M = M') :
      (letI : ValuativeRel M := finiteIntermediateFieldValuativeRel K _ M
       letI : TopologicalSpace M := finiteIntermediateFieldTopology K _ M
       haveI : IsNonarchimedeanLocalField M :=
         finiteIntermediateField_isNonarchimedeanLocalField K _ M
       haveI : ValuativeExtension K M := finiteIntermediateField_valuativeExtension K _ M
       topArtinSlopeOfIsGalois K M) =
      (letI : ValuativeRel M' := finiteIntermediateFieldValuativeRel K _ M'
       letI : TopologicalSpace M' := finiteIntermediateFieldTopology K _ M'
       haveI : IsNonarchimedeanLocalField M' :=
         finiteIntermediateField_isNonarchimedeanLocalField K _ M'
       haveI : ValuativeExtension K M' := finiteIntermediateField_valuativeExtension K _ M'
       topArtinSlopeOfIsGalois K M') := by
    subst hM
    rfl
  exact key _ _ h

end IsNonarchimedeanLocalField

namespace NumberField

variable (L : Type*) [Field L] [NumberField L] (ℓ : ℕ) [Fact ℓ.Prime]
  (𝔪 : MaximalSpectrum (ℚ_[ℓ] ⊗[ℚ] L))

/-- The **top Artin slope at `ℓ`** (LMFDB `modlgal.top_slope`) of a number field `L`: the largest
top Artin slope (LMFDB `lf.top_slope`) over `ℚ_ℓ` of the `ℓ`-adic fields of which the local
algebra `ℚ_ℓ ⊗ L` (LMFDB `nf.local_algebra`) is the product, its quotients `(ℚ_ℓ ⊗ L) / 𝔪` by its
maximal ideals `𝔪`. The LMFDB writes the local algebra `L ⊗ ℚ_ℓ`; we put `ℚ_ℓ` on the left, for
its `ℚ_ℓ`-algebra structure. -/
noncomputable def topArtinSlopeAt : ℝ :=
  ⨆ 𝔪 : MaximalSpectrum (ℚ_[ℓ] ⊗[ℚ] L),
    haveI : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
    letI : Field ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := Quotient.field _
    IsNonarchimedeanLocalField.topArtinSlope ℚ_[ℓ] ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal)

variable [IsGalois ℚ L] in
/-- **The factors of the local algebra of a Galois number field have the compositum as Galois
closure**: for `L` Galois over `ℚ`, the Galois closure of each factor `(ℚ_ℓ ⊗ L) / 𝔪` is the Galois
closure of the algebra `ℚ_ℓ ⊗ L`, the compositum of the images of all its factors in `ℚ̄_ℓ`. -/
lemma galoisClosure_quotient_eq : Algebra.galoisClosure ℚ_[ℓ] ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) =
    Algebra.galoisClosure ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] L) := by
  have : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
  let _ : Field ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := Quotient.field _
  refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_)
    (IntermediateField.adjoin_le_iff.mpr ?_)
  · rintro _ ⟨_, ⟨g, rfl⟩, x, rfl⟩
    rcases Quotient.mkₐ_surjective ℚ_[ℓ] 𝔪.asIdeal x with ⟨r, rfl⟩
    exact IntermediateField.subset_adjoin _ _
      ⟨_, ⟨g.comp (Quotient.mkₐ ℚ_[ℓ] 𝔪.asIdeal), rfl⟩, r, rfl⟩
  · rintro _ ⟨_, ⟨f, rfl⟩, r, rfl⟩
    let g : (ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal →ₐ[ℚ_[ℓ]] AlgebraicClosure ℚ_[ℓ] := IsAlgClosed.lift
    let σ : L →ₐ[ℚ] AlgebraicClosure ℚ_[ℓ] := (f.restrictScalars ℚ).comp includeRight
    let τ : L →ₐ[ℚ] AlgebraicClosure ℚ_[ℓ] :=
      ((g.comp (Quotient.mkₐ ℚ_[ℓ] 𝔪.asIdeal)).restrictScalars ℚ).comp includeRight
    have hστ : σ.fieldRange = τ.fieldRange :=
      (IntermediateField.normalClosure_eq_fieldRange σ).symm.trans
        (IntermediateField.normalClosure_eq_fieldRange τ)
    induction r with
    | tmul a y =>
      rcases AlgHom.mem_fieldRange.mp (hστ.le <| AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩) with ⟨z, hz⟩
      have h : f (a ⊗ₜ y) = algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]) a * f (1 ⊗ₜ y) := by
        rw [← smul_def, ← map_smul, smul_tmul', smul_eq_mul, mul_one]
      have hσ : f (1 ⊗ₜ y) = σ y := rfl
      rw [h, hσ, ← hz]
      exact mul_mem (IntermediateField.algebraMap_mem _ a)
        (IntermediateField.subset_adjoin _ _ ⟨_, ⟨g, rfl⟩, _, rfl⟩)
    | add r s hr hs =>
      rw [map_add]
      exact add_mem hr hs

variable [IsGalois ℚ L] in
/-- **The top Artin slope of a Galois number field is that of each factor of its local algebra**:
for `L` Galois over `ℚ`, the top Artin slope of `L` at `ℓ` is the top Artin slope of each factor
`(ℚ_ℓ ⊗ L) / 𝔪`, hence that of their compositum, the common Galois closure of the factors
(`NumberField.galoisClosure_quotient_eq`). -/
lemma topArtinSlopeAt_eq :
    haveI : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
    letI : Field ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := Quotient.field _
    topArtinSlopeAt L ℓ =
      IsNonarchimedeanLocalField.topArtinSlope ℚ_[ℓ] ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := by
  have : Nonempty (MaximalSpectrum (ℚ_[ℓ] ⊗[ℚ] L)) := ⟨𝔪⟩
  refine (iSup_congr fun 𝔪' ↦ ?_).trans ciSup_const
  have : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
  have : 𝔪'.asIdeal.IsMaximal := 𝔪'.isMaximal
  let _ : Field ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪.asIdeal) := Quotient.field _
  let _ : Field ((ℚ_[ℓ] ⊗[ℚ] L) ⧸ 𝔪'.asIdeal) := Quotient.field _
  exact IsNonarchimedeanLocalField.topArtinSlope_eq_of_galoisClosure_eq <|
    (galoisClosure_quotient_eq L ℓ 𝔪').trans (galoisClosure_quotient_eq L ℓ 𝔪).symm

end NumberField

namespace MonoidHom

variable {K : Type*} [Field K] [NumberField K] {n ℓ : ℕ} [Fact ℓ.Prime]
  {ρ : Gal(AlgebraicClosure K/K) →* GL (Fin n) (ZMod ℓ)}

/-- The **top Artin slope** (LMFDB `modlgal.top_slope`) of a mod-`ℓ` Galois representation `ρ` of a
number field `K`: the top Artin slope at `ℓ` (`NumberField.topArtinSlopeAt`) of its splitting field
`L`, the largest top Artin slope of the `ℓ`-adic fields of which the local algebra `ℚ_ℓ ⊗ L` is the
product. For `K = ℚ`, as in the LMFDB, `L` is Galois over `ℚ` and this is the top Artin slope of
their compositum (`NumberField.topArtinSlopeAt_eq`): `0` if `L` is unramified at `ℓ`, `1` if it is
tamely but not unramified, and the largest wild Artin slope otherwise. -/
noncomputable def topArtinSlope (hρ : IsOpen (ρ.ker : Set Gal(AlgebraicClosure K/K))) : ℝ :=
  NumberField.topArtinSlopeAt (splittingField ρ hρ) ℓ

end MonoidHom
