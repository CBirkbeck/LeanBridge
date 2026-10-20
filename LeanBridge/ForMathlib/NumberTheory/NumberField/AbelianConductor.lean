import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.NumberField.Cyclotomic.CharacterSubfield

/-!
# The conductor and the Dirichlet character group of an abelian number field

By the Kronecker–Weber theorem every abelian number field `K` embeds in a cyclotomic field
`ℚ(ζ_n)`; the least such `n` is the conductor of `K`. The Galois group `Gal(K/ℚ)` is then a
quotient of `Gal(ℚ(ζ_n)/ℚ) ≅ (ℤ/nℤ)ˣ`, so its dual is a group of Dirichlet characters modulo `n`,
the Dirichlet character group of `K`; Mathlib's
`IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar` is this correspondence for the
subfields of `ℚ(ζ_n)`.

The Kronecker–Weber theorem is not available (Tau Ceti proves the multiquadratic case), so the
conductor is defined as an infimum over the levels `n` of the cyclotomic fields into which `K`
embeds, with the junk value `0` when there is none, which by the Kronecker–Weber theorem happens
exactly when `K` is not abelian. Every statement below is proved for the fields that do embed in a
cyclotomic field.

## Main definitions

* `NumberField.abelianConductor` (LMFDB `nf.conductor`).
* `NumberField.dirichletCharacterGroup` (LMFDB `nf.dirichlet_group`).

## Main results

* `NumberField.nonempty_algHom_cyclotomicField_iff`: `K` embeds in `ℚ(ζ_n)` exactly when its
  conductor divides `n`.
* `NumberField.isAbelianGalois_of_abelianConductor_pos`: a field with a positive conductor is
  abelian.
* `NumberField.dirichletCharacterGroup_eq`: the Dirichlet character group does not depend on the
  embedding of `K` into `ℚ(ζ_f)`.
* `NumberField.card_dirichletCharacterGroup`: the Dirichlet character group of `K` has `[K : ℚ]`
  elements.
* `NumberField.dirichletConductor_dirichletCharacterGroup`: the conductor of `K` is the least
  common multiple of the conductors of its Dirichlet characters.
-/

open IsCyclotomicExtension IsCyclotomicExtension.Rat IntermediateField

namespace NumberField

variable (K : Type*) [Field K] [NumberField K] {n d : ℕ} (N : ℕ) [NeZero N]
  (ψ : K →ₐ[ℚ] CyclotomicField N ℚ) {F L M : Type*} [Field F] [Algebra F K] [Field L] [Algebra F L]
  [Field M] [Algebra F M] (f : K →ₐ[F] L)

/-- The **conductor** of an abelian number field `K` (LMFDB `nf.conductor`): the least positive
integer `n` such that `K` embeds in the cyclotomic field `ℚ(ζ_n)`.

By the Kronecker–Weber theorem, which is not available, such an `n` exists exactly when `K` is
abelian; when there is none the conductor takes the junk value `0`. -/
noncomputable def abelianConductor : ℕ :=
  sInf {n | 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ)}

lemma abelianConductor_pos_iff :
    0 < abelianConductor K ↔ ∃ n, 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ) :=
  ⟨Nat.nonempty_of_pos_sInf, fun h ↦
    (Nat.sInf_mem (s := {n | 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ)}) h).1⟩

lemma nonempty_algHom_cyclotomicField_abelianConductor (h : 0 < abelianConductor K) :
    Nonempty (K →ₐ[ℚ] CyclotomicField (abelianConductor K) ℚ) :=
  (Nat.sInf_mem <| Nat.nonempty_of_pos_sInf h).2

lemma abelianConductor_le (hn : 0 < n) (h : Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ)) :
    abelianConductor K ≤ n :=
  Nat.sInf_le ⟨hn, h⟩

/-! The `ℚ`-algebra structure that instance search finds on `CyclotomicField n ℚ` is not the one
of Mathlib's instances, so we restate those instances for it. -/

variable [NeZero n] in
local instance : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
  CyclotomicField.isCyclotomicExtension n ℚ

variable [NeZero n] in
local instance : IsAbelianGalois ℚ (CyclotomicField n ℚ) :=
  IsCyclotomicExtension.isAbelianGalois {n} ℚ _

/-- A number field that embeds in a cyclotomic field is abelian. -/
lemma isAbelianGalois_of_abelianConductor_pos (h : 0 < abelianConductor K) : IsAbelianGalois ℚ K :=
  have : NeZero (abelianConductor K) := ⟨h.ne'⟩
  IsAbelianGalois.of_algHom (nonempty_algHom_cyclotomicField_abelianConductor K h).some

omit [NumberField K] in
private lemma fieldRange_comp_algEquiv {E : Type*} [Field E] [Algebra F E] (e : E ≃ₐ[F] K) :
    (f.comp e.toAlgHom).fieldRange = f.fieldRange :=
  SetLike.ext' <| e.surjective.range_comp f

omit [NumberField K] in
private lemma fieldRange_eq_fieldRange [Normal F K] (g : K →ₐ[F] L) :
    g.fieldRange = f.fieldRange := by
  have : Normal F f.fieldRange := Normal.of_algEquiv f.equivFieldRange
  rw [← fieldRange_comp_algEquiv K g f.equivFieldRange.symm, AlgHom.fieldRange_of_normal]

omit [NumberField K] in
private lemma fieldRange_comp_le (g : L →ₐ[F] M) : (g.comp f).fieldRange ≤ g.fieldRange :=
  fun _ ⟨a, ha⟩ ↦ ⟨f a, ha⟩

/-! ### The cyclotomic subfields of `ℚ(ζ_N)` -/

private lemma neZero_of_dvd (hd : d ∣ N) : NeZero d :=
  ⟨fun h ↦ NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hd))⟩

private lemma isCyclotomicExtension_adjoin (hd : d ∣ N) :
    IsCyclotomicExtension {d} ℚ ℚ⟮zeta N ℚ (CyclotomicField N ℚ) ^ (N / d)⟯ := by
  have : NeZero d := neZero_of_dvd N hd
  have h : IsPrimitiveRoot (zeta N ℚ (CyclotomicField N ℚ) ^ (N / d)) (N / (N / d)) :=
    (zeta_spec N ℚ (CyclotomicField N ℚ)).pow_of_dvd
      (Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hd) (NeZero.pos d)).ne' (Nat.div_dvd_of_dvd hd)
  rw [Nat.div_div_self hd (NeZero.ne N)] at h
  exact h.intermediateField_adjoin_isCyclotomicExtension ℚ

/-- The isomorphism of `ℚ(ζ_d)` with the subfield `ℚ(ζ_N ^ (N / d))` of `ℚ(ζ_N)`, for `d ∣ N`. -/
private noncomputable def adjoinEquiv (hd : d ∣ N) :
    CyclotomicField d ℚ ≃ₐ[ℚ] ℚ⟮zeta N ℚ (CyclotomicField N ℚ) ^ (N / d)⟯ :=
  haveI : NeZero d := neZero_of_dvd N hd
  haveI : IsCyclotomicExtension {d} ℚ ℚ⟮zeta N ℚ (CyclotomicField N ℚ) ^ (N / d)⟯ :=
    isCyclotomicExtension_adjoin N hd
  algEquiv {d} ℚ _ _

private lemma nonempty_algHom_of_dvd (hd : d ∣ N) :
    Nonempty (CyclotomicField d ℚ →ₐ[ℚ] CyclotomicField N ℚ) :=
  ⟨(IntermediateField.val _).comp (adjoinEquiv N hd).toAlgHom⟩

private lemma fieldRange_eq_adjoin (hd : d ∣ N)
    (j : CyclotomicField d ℚ →ₐ[ℚ] CyclotomicField N ℚ) :
    j.fieldRange = ℚ⟮zeta N ℚ (CyclotomicField N ℚ) ^ (N / d)⟯ := by
  have : NeZero d := neZero_of_dvd N hd
  have : IsCyclotomicExtension {d} ℚ ℚ⟮zeta N ℚ (CyclotomicField N ℚ) ^ (N / d)⟯ :=
    isCyclotomicExtension_adjoin N hd
  have : Normal ℚ ℚ⟮zeta N ℚ (CyclotomicField N ℚ) ^ (N / d)⟯ := (isGalois {d} ℚ _).to_normal
  rw [← fieldRange_comp_algEquiv _ j (adjoinEquiv N hd).symm, AlgHom.fieldRange_of_normal]

private lemma fieldRange_le_adjoin_iff (hd : d ∣ N) : ψ.fieldRange ≤
    ℚ⟮zeta N ℚ (CyclotomicField N ℚ) ^ (N / d)⟯ ↔ (intermediateFieldEquivSubgroupChar N
    (CyclotomicField N ℚ) ℂ ψ.fieldRange).dirichletConductor ∣ d := by
  have : NeZero d := neZero_of_dvd N hd
  have : IsCyclotomicExtension {d} ℚ ℚ⟮zeta N ℚ (CyclotomicField N ℚ) ^ (N / d)⟯ :=
    isCyclotomicExtension_adjoin N hd
  have : IsGalois ℚ ℚ⟮zeta N ℚ (CyclotomicField N ℚ) ^ (N / d)⟯ := isGalois {d} ℚ _
  conv_lhs => rw [← OrderIso.symm_apply_apply
    (intermediateFieldEquivSubgroupChar N (CyclotomicField N ℚ) ℂ) ψ.fieldRange]
  exact Subgroup.characterSubfield_le_iff_dirichletConductor_dvd _ _ hd

private lemma nonempty_algHom_of_fieldRange_le (hd : d ∣ N)
    (h : ψ.fieldRange ≤ ℚ⟮zeta N ℚ (CyclotomicField N ℚ) ^ (N / d)⟯) :
    Nonempty (K →ₐ[ℚ] CyclotomicField d ℚ) :=
  ⟨(adjoinEquiv N hd).symm.toAlgHom.comp <| ψ.codRestrict _ fun x ↦ h ⟨x, rfl⟩⟩

/-- **The conductor divides every admissible level.** A number field `K` embeds in the cyclotomic
field `ℚ(ζ_n)` exactly when its conductor divides `n`. -/
lemma nonempty_algHom_cyclotomicField_iff (hn : 0 < n) :
    Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ) ↔ abelianConductor K ∣ n := by
  have : NeZero n := ⟨hn.ne'⟩
  refine ⟨fun ⟨ι⟩ ↦ ?_, fun h ↦ ?_⟩
  swap
  · have : NeZero (abelianConductor K) := neZero_of_dvd n h
    exact ⟨(nonempty_algHom_of_dvd n h).some.comp
      (nonempty_algHom_cyclotomicField_abelianConductor K (NeZero.pos _)).some⟩
  have hf : 0 < abelianConductor K := (abelianConductor_pos_iff K).mpr ⟨n, hn, ⟨ι⟩⟩
  rcases nonempty_algHom_cyclotomicField_abelianConductor K hf with ⟨ιf⟩
  have : NeZero (n * abelianConductor K) := ⟨(Nat.mul_pos hn hf).ne'⟩
  have : IsAbelianGalois ℚ K := isAbelianGalois_of_abelianConductor_pos K hf
  rcases nonempty_algHom_of_dvd (n * abelianConductor K) (dvd_mul_right n _) with ⟨jn⟩
  rcases nonempty_algHom_of_dvd (n * abelianConductor K) (dvd_mul_left (abelianConductor K) n)
    with ⟨jf⟩
  have hg : n.gcd (abelianConductor K) ∣ n * abelianConductor K :=
    (Nat.gcd_dvd_left _ _).trans (dvd_mul_right n _)
  have hle : abelianConductor K ≤ n.gcd (abelianConductor K) :=
    abelianConductor_le K (Nat.gcd_pos_of_pos_left _ hn) <|
      nonempty_algHom_of_fieldRange_le K _ (jn.comp ι) hg <|
        (fieldRange_le_adjoin_iff K _ (jn.comp ι) hg).mpr <| Nat.dvd_gcd
          ((fieldRange_le_adjoin_iff K _ (jn.comp ι) (dvd_mul_right n _)).mp <|
            (fieldRange_comp_le K ι jn).trans (fieldRange_eq_adjoin _ (dvd_mul_right n _) jn).le)
          ((fieldRange_le_adjoin_iff K _ (jn.comp ι) (dvd_mul_left _ n)).mp <|
            fieldRange_eq_fieldRange K (jf.comp ιf) (jn.comp ι) ▸
              (fieldRange_comp_le K ιf jf).trans (fieldRange_eq_adjoin _ (dvd_mul_left _ n) jf).le)
  exact le_antisymm (Nat.le_of_dvd hf (Nat.gcd_dvd_right _ _)) hle ▸ Nat.gcd_dvd_left _ _

/-- The **Dirichlet character group** of an abelian number field `K` (LMFDB `nf.dirichlet_group`):
for an embedding of `K` into `ℚ(ζ_f)`, where `f` is the conductor of `K`, the group of Dirichlet
characters modulo `f` that are trivial on the subgroup of `(ℤ/fℤ)ˣ ≅ Gal(ℚ(ζ_f)/ℚ)` fixing the image
of `K`; that is, the dual of the quotient `Gal(K/ℚ)` of `Gal(ℚ(ζ_f)/ℚ)`. The characters take values
in `ℂ`. By `dirichletCharacterGroup_eq` it does not depend on the embedding.

When `K` embeds in no cyclotomic field, so that its conductor is the junk value `0`, this is the
junk value `⊥`. -/
noncomputable def dirichletCharacterGroup : Subgroup (DirichletCharacter ℂ (abelianConductor K)) :=
  if h : 0 < abelianConductor K then
    haveI : NeZero (abelianConductor K) := ⟨h.ne'⟩
    intermediateFieldEquivSubgroupChar (abelianConductor K) (CyclotomicField (abelianConductor K) ℚ)
      ℂ (nonempty_algHom_cyclotomicField_abelianConductor K h).some.fieldRange
  else ⊥

/-- The Dirichlet character group of `K` is the group of characters attached to the image of any
embedding of `K` into `ℚ(ζ_f)`. -/
lemma dirichletCharacterGroup_eq [NeZero (abelianConductor K)]
    (φ : K →ₐ[ℚ] CyclotomicField (abelianConductor K) ℚ) :
    dirichletCharacterGroup K = intermediateFieldEquivSubgroupChar _ _ ℂ φ.fieldRange := by
  have : IsAbelianGalois ℚ K := isAbelianGalois_of_abelianConductor_pos K (NeZero.pos _)
  rw [dirichletCharacterGroup, dite_eq_left (NeZero.pos _), fieldRange_eq_fieldRange K φ]

/-- The Dirichlet character group of `K` has `[K : ℚ]` elements. -/
lemma card_dirichletCharacterGroup (h : 0 < abelianConductor K) :
    Nat.card (dirichletCharacterGroup K) = Module.finrank ℚ K := by
  have : NeZero (abelianConductor K) := ⟨h.ne'⟩
  rcases nonempty_algHom_cyclotomicField_abelianConductor K h with ⟨φ⟩
  rw [dirichletCharacterGroup_eq K φ, card_intermediateFieldEquivSubgroupChar]
  exact φ.equivFieldRange.toLinearEquiv.finrank_eq.symm

/-- The conductor of `K` is the conductor of its Dirichlet character group, the least common
multiple of the conductors of the characters of `K`. -/
lemma dirichletConductor_dirichletCharacterGroup (h : 0 < abelianConductor K) :
    (dirichletCharacterGroup K).dirichletConductor = abelianConductor K := by
  have : NeZero (abelianConductor K) := ⟨h.ne'⟩
  rcases nonempty_algHom_cyclotomicField_abelianConductor K h with ⟨φ⟩
  rw [dirichletCharacterGroup_eq K φ]
  have hc : (intermediateFieldEquivSubgroupChar _ _ ℂ φ.fieldRange).dirichletConductor ∣
      abelianConductor K :=
    Subgroup.dirichletConductor_dvd_level _
  exact le_antisymm (Nat.le_of_dvd h hc) <| abelianConductor_le K (Nat.pos_of_dvd_of_pos hc h) <|
    nonempty_algHom_of_fieldRange_le K _ φ hc <| (fieldRange_le_adjoin_iff K _ φ hc).mpr dvd_rfl

end NumberField
