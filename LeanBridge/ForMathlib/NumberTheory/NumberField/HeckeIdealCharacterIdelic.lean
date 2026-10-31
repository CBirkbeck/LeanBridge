import LeanBridge.ForMathlib.NumberTheory.NumberField.HeckeIdealCharacter

/-!
# Ideal-theoretic Hecke characters come from idelic Hecke characters

Let `𝔪` be a modulus of a number field `K` and `χ : I(𝔪) → ℂˣ` a Hecke character modulo `𝔪` in the
ideal-theoretic sense (`TauCeti.GlobalNumberFields.IsIdealHeckeCharacter`): there are continuous
characters `φ_w` of the completions `K_wˣ` at the infinite places with `χ((α)) = ∏_w φ_w(α)` for
`α ≡ 1 mod* 𝔪`. On the ideles `x` congruent to one modulo `𝔪`, the formula
`ψ(x) = χ(ideal of x) ∏_w φ_w(x_w)⁻¹` defines a character that is trivial on the principal ideles
congruent to one. Every idele is congruent to one after multiplication by a principal idele (weak
approximation), so `ψ` extends to a character of the idele class group, continuous because it is
`∏_w φ_w(x_w)⁻¹` on the open idele congruence subgroup of `𝔪`. Its conductor divides `𝔪` and its
ideal character is `χ`.

Together with `TauCeti.GlobalNumberFields.HeckeCharacter.isIdealHeckeCharacter_idealCharacter`,
this identifies the ideal-theoretic Hecke characters modulo `𝔪` with the ideal characters of the
idelic Hecke characters (Tau Ceti's `TauCeti.GlobalNumberFields.HeckeCharacter`) of conductor
dividing `𝔪`.

## Main definitions

* `TauCeti.GlobalNumberFields.idealHeckeInfinitePart`: the character `x ↦ ∏_w φ_w(x_w)` of the
  ideles.
* `TauCeti.GlobalNumberFields.idealHeckeCongrOne`: the character
  `x ↦ χ(ideal of x) ∏_w φ_w(x_w)⁻¹` of the ideles congruent to one modulo `𝔪`.
* `TauCeti.GlobalNumberFields.ideleCongrOneOfFiniteIdele`: an idele congruent to one modulo `𝔪`
  representing a given fractional ideal prime to `𝔪`.
* `TauCeti.GlobalNumberFields.IsIdealHeckeCharacter.idealHeckeIdeleFun` and
  `TauCeti.GlobalNumberFields.IsIdealHeckeCharacter.idealHeckeIdele`: its extension to all ideles.
* `TauCeti.GlobalNumberFields.IsIdealHeckeCharacter.heckeCharacter`: the idelic Hecke character
  of an ideal-theoretic one.

## Main results

* `TauCeti.GlobalNumberFields.IsIdealHeckeCharacter.conductorExponent_heckeCharacter_le`: its
  conductor divides `𝔪`.
* `TauCeti.GlobalNumberFields.IsIdealHeckeCharacter.idealCharacter_comp_heckeCharacter`: its
  ideal character is `χ`.
* `TauCeti.GlobalNumberFields.isIdealHeckeCharacter_iff` (LMFDB `character.hecke`): a character of
  `I(𝔪)` is a Hecke character modulo `𝔪` exactly when it is the ideal character of an idelic Hecke
  character of conductor dividing `𝔪`.
-/

open IsDedekindDomain HeightOneSpectrum FiniteAdeleRing NumberField
open scoped NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K} {χ : idealsPrimeTo 𝔪 →* ℂˣ}
  (φ : ∀ w : InfinitePlace K, w.Completionˣ →ₜ* ℂˣ) {a : 𝔸ᶠ[(𝓞 K), K]ˣ}
  {v : HeightOneSpectrum (𝓞 K)}

/-- The **infinite part** `x ↦ ∏_w φ_w(x_w)`, a character of the idele group, given by characters
`φ_w` of the completions at the infinite places. -/
noncomputable def idealHeckeInfinitePart : IdeleGroup (𝓞 K) K →* ℂˣ :=
  ∏ w, (φ w : w.Completionˣ →* ℂˣ).comp w.ideleInfiniteCoord

lemma idealHeckeInfinitePart_apply (x : IdeleGroup (𝓞 K) K) :
    idealHeckeInfinitePart φ x = ∏ w, φ w (w.ideleInfiniteCoord x) := by
  simp [idealHeckeInfinitePart]

lemma continuous_idealHeckeInfinitePart : Continuous (idealHeckeInfinitePart φ) := by
  have h (w : InfinitePlace K) :
      Continuous fun x : IdeleGroup (𝓞 K) K ↦ (IdeleGroup.localUnitsEquiv (𝓞 K) K x).1 w :=
    (continuous_apply w).comp (continuous_fst.comp (IdeleGroup.localUnitsEquiv (𝓞 K) K).continuous)
  simp only [IdeleGroup.localUnitsEquiv_apply_fst] at h
  rw [funext (idealHeckeInfinitePart_apply φ)]
  exact continuous_finsetProd Finset.univ fun w _ ↦ (φ w).continuous.comp (h w)

variable (χ) in
/-- The **character** `x ↦ χ(ideal of x) ∏_w φ_w(x_w)⁻¹` of the ideles congruent to one modulo
`𝔪`, whose fractional ideals are prime to `𝔪`. -/
noncomputable def idealHeckeCongrOne : ideleCongrOneSubgroup 𝔪 →* ℂˣ :=
  χ.comp (MonoidHom.codRestrict ((toFractionalIdeal.comp (IdeleGroup.toFiniteIdele (𝓞 K) K)).comp
    (ideleCongrOneSubgroup 𝔪).subtype) (idealsPrimeTo 𝔪)
      fun x ↦ toFractionalIdeal_toFiniteIdele_mem_idealsPrimeTo x.2) *
    ((idealHeckeInfinitePart φ).comp (ideleCongrOneSubgroup 𝔪).subtype)⁻¹

variable (χ) in
lemma idealHeckeCongrOne_apply (y : ideleCongrOneSubgroup 𝔪) : idealHeckeCongrOne χ φ y =
    χ ⟨toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 K) K y),
      toFractionalIdeal_toFiniteIdele_mem_idealsPrimeTo y.2⟩ * (idealHeckeInfinitePart φ y)⁻¹ :=
  rfl

variable (𝔪 a) in
/-- The **idele congruent to one** obtained from a finite idele `a` by changing its components at
the primes dividing `𝔪` to `1`, with trivial infinite components. When `a` is a unit at those
primes, it is an idele congruent to one modulo `𝔪` with the same fractional ideal as `a`. -/
noncomputable def ideleCongrOneOfFiniteIdele : IdeleGroup (𝓞 K) K :=
  IdeleGroup.ofFiniteIdele (𝓞 K) K a * ∏ v ∈ 𝔪.support, IdeleGroup.ofAdicCompletion (𝓞 K) K v
    (v.ideleFiniteCoord (IdeleGroup.ofFiniteIdele (𝓞 K) K a))⁻¹

variable (𝔪 a) in
lemma ideleFiniteCoord_ideleCongrOneOfFiniteIdele (hv : v ∈ 𝔪.support) :
    v.ideleFiniteCoord (ideleCongrOneOfFiniteIdele 𝔪 a) = 1 := by
  classical
  rw [ideleCongrOneOfFiniteIdele, map_mul, v.ideleFiniteCoord_prod_ofAdicCompletion 𝔪.support _]
  simp [hv]

variable (𝔪 a) in
lemma ideleInfiniteCoord_ideleCongrOneOfFiniteIdele (w : InfinitePlace K) :
    w.ideleInfiniteCoord (ideleCongrOneOfFiniteIdele 𝔪 a) = 1 := by
  simp [ideleCongrOneOfFiniteIdele]

lemma toFractionalIdeal_ideleCongrOneOfFiniteIdele (ha : a ∈ adicOrdAway 𝔪.support) :
    toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 K) K (ideleCongrOneOfFiniteIdele 𝔪 a)) =
      toFractionalIdeal a := by
  classical
  have hz : toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 K) K (∏ v ∈ 𝔪.support,
      IdeleGroup.ofAdicCompletion (𝓞 K) K v
        (v.ideleFiniteCoord (IdeleGroup.ofFiniteIdele (𝓞 K) K a))⁻¹)) = 1 := by
    refine toFractionalIdeal_toFiniteIdele_eq_one_iff.mpr fun v ↦ ?_
    rw [v.ideleFiniteCoord_prod_ofAdicCompletion 𝔪.support _]
    split_ifs with hv
    · rw [Units.val_inv_eq_inv_val, map_inv₀, inv_eq_one, HeightOneSpectrum.coe_ideleFiniteCoord,
        ← IdeleGroup.coe_toFiniteIdele, IdeleGroup.toFiniteIdele_ofFiniteIdele]
      exact adicOrd_eq_zero_iff.mp ((mem_adicOrdAway_iff _ a).mp ha v hv)
    · simp
  rw [ideleCongrOneOfFiniteIdele, map_mul, map_mul, hz, mul_one,
    IdeleGroup.toFiniteIdele_ofFiniteIdele]

namespace IsIdealHeckeCharacter

variable (hχ : IsIdealHeckeCharacter 𝔪 χ) {x y : IdeleGroup (𝓞 K) K} (α β : Kˣ)
  (hα : IdeleGroup.unitEmbedding (𝓞 K) K α * x ∈ ideleCongrOneSubgroup 𝔪)

lemma idealHeckeCongrOne_unitEmbedding
    (hβ : IdeleGroup.unitEmbedding (𝓞 K) K β ∈ ideleCongrOneSubgroup 𝔪) :
    idealHeckeCongrOne χ hχ.choose ⟨_, hβ⟩ = 1 := by
  rw [idealHeckeCongrOne_apply, mul_inv_eq_one, idealHeckeInfinitePart_apply]
  simp only [InfinitePlace.ideleInfiniteCoord_unitEmbedding]
  rw [← hχ.choose_spec β (unitEmbedding_mem_ideleCongrOneSubgroup_iff.mp hβ)]
  exact congrArg χ (Subtype.ext ((congrArg toFractionalIdeal
    (IdeleGroup.toFiniteIdele_unitEmbedding (𝓞 K) K β)).trans (toFractionalIdeal_unitEmbedding β)))

lemma idealHeckeCongrOne_eq
    (hβ : IdeleGroup.unitEmbedding (𝓞 K) K β * x ∈ ideleCongrOneSubgroup 𝔪) :
    idealHeckeCongrOne χ hχ.choose ⟨_, hα⟩ = idealHeckeCongrOne χ hχ.choose ⟨_, hβ⟩ := by
  have hγ : IdeleGroup.unitEmbedding (𝓞 K) K (α * β⁻¹) ∈ ideleCongrOneSubgroup 𝔪 := by
    convert (ideleCongrOneSubgroup 𝔪).mul_mem hα ((ideleCongrOneSubgroup 𝔪).inv_mem hβ) using 1
    rw [map_mul, map_inv]
    group
  have hsplit : (⟨_, hα⟩ : ideleCongrOneSubgroup 𝔪) = ⟨_, hγ⟩ * ⟨_, hβ⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, map_mul, map_inv]; group)
  rw [hsplit, map_mul, hχ.idealHeckeCongrOne_unitEmbedding, one_mul]

variable (x) in
/-- The **value of the idelic character** at an idele `x`: that of `idealHeckeCongrOne` at `α x`,
for `α ∈ Kˣ` making `α x` congruent to one modulo `𝔪`. -/
noncomputable def idealHeckeIdeleFun : ℂˣ :=
  idealHeckeCongrOne χ hχ.choose
    ⟨_, (exists_unitEmbedding_mul_mem_ideleCongrOneSubgroup 𝔪 x).choose_spec⟩

lemma idealHeckeIdeleFun_eq : hχ.idealHeckeIdeleFun x = idealHeckeCongrOne χ hχ.choose ⟨_, hα⟩ :=
  hχ.idealHeckeCongrOne_eq _ _ _ hα

/-- The **idelic character** `x ↦ χ(ideal of α x) ∏_w φ_w((α x)_w)⁻¹` of the idele group, for
`α ∈ Kˣ` making `α x` congruent to one modulo `𝔪`. -/
noncomputable def idealHeckeIdele : IdeleGroup (𝓞 K) K →* ℂˣ where
  toFun := hχ.idealHeckeIdeleFun
  map_one' := by
    rw [hχ.idealHeckeIdeleFun_eq 1 (by simp)]
    exact (congrArg (idealHeckeCongrOne χ hχ.choose) (Subtype.ext (by simp))).trans (map_one _)
  map_mul' x y := by
    rcases exists_unitEmbedding_mul_mem_ideleCongrOneSubgroup 𝔪 x with ⟨α, hα⟩
    rcases exists_unitEmbedding_mul_mem_ideleCongrOneSubgroup 𝔪 y with ⟨β, hβ⟩
    have hmul : IdeleGroup.unitEmbedding (𝓞 K) K (α * β) * (x * y) =
        IdeleGroup.unitEmbedding (𝓞 K) K α * x * (IdeleGroup.unitEmbedding (𝓞 K) K β * y) := by
      rw [map_mul, mul_mul_mul_comm]
    have hαβ : IdeleGroup.unitEmbedding (𝓞 K) K (α * β) * (x * y) ∈ ideleCongrOneSubgroup 𝔪 :=
      hmul ▸ (ideleCongrOneSubgroup 𝔪).mul_mem hα hβ
    rw [hχ.idealHeckeIdeleFun_eq _ hαβ, hχ.idealHeckeIdeleFun_eq _ hα,
      hχ.idealHeckeIdeleFun_eq _ hβ, ← map_mul]
    exact congrArg (idealHeckeCongrOne χ hχ.choose) (Subtype.ext hmul)

lemma idealHeckeIdele_of_mem (hy : y ∈ ideleCongrOneSubgroup 𝔪) :
    hχ.idealHeckeIdele y = idealHeckeCongrOne χ hχ.choose ⟨y, hy⟩ :=
  (hχ.idealHeckeIdeleFun_eq 1 (by simpa using hy)).trans
    (congrArg (idealHeckeCongrOne χ hχ.choose) (Subtype.ext (by simp)))

lemma idealHeckeIdele_of_mem_ideleCongruenceSubgroup (hy : y ∈ ideleCongruenceSubgroup 𝔪) :
    hχ.idealHeckeIdele y = (idealHeckeInfinitePart hχ.choose y)⁻¹ := by
  rw [hχ.idealHeckeIdele_of_mem (ideleCongruenceSubgroup_le_ideleCongrOneSubgroup 𝔪 hy),
    idealHeckeCongrOne_apply]
  have h : (⟨toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 K) K y),
      toFractionalIdeal_toFiniteIdele_mem_idealsPrimeTo
        (ideleCongruenceSubgroup_le_ideleCongrOneSubgroup 𝔪 hy)⟩ : idealsPrimeTo 𝔪) = 1 :=
    Subtype.ext (toFractionalIdeal_toFiniteIdele_eq_one_iff.mpr
      (ideleCongruenceSubgroup.valued_ideleFiniteCoord_eq_one hy))
  rw [h, map_one, one_mul]

lemma principalSubgroup_le_ker_idealHeckeIdele :
    IdeleGroup.principalSubgroup (𝓞 K) K ≤ hχ.idealHeckeIdele.ker := by
  rintro _ ⟨β, rfl⟩
  rw [MonoidHom.mem_ker]
  refine (hχ.idealHeckeIdeleFun_eq β⁻¹ (by simp)).trans ?_
  exact (congrArg (idealHeckeCongrOne χ hχ.choose) (Subtype.ext (by simp))).trans (map_one _)

lemma continuous_idealHeckeIdele : Continuous hχ.idealHeckeIdele := by
  refine continuous_of_continuousAt_one _ <|
    (continuous_idealHeckeInfinitePart hχ.choose).continuousAt.inv.congr ?_
  filter_upwards [(isOpen_ideleCongruenceSubgroup 𝔪).mem_nhds (one_mem _)] with y hy
  exact (hχ.idealHeckeIdele_of_mem_ideleCongruenceSubgroup hy).symm

/-- The **idelic Hecke character of an ideal-theoretic Hecke character** `χ` modulo `𝔪`, with
characters `φ_w` at the infinite places: the character of the idele class group whose value at the
class of an idele `x` congruent to one modulo `𝔪` is `χ(ideal of x) ∏_w φ_w(x_w)⁻¹`. Every idele
class has such a representative, and the value does not depend on it since
`χ((α)) = ∏_w φ_w(α)` for `α ≡ 1 mod* 𝔪`. Its ideal character is `χ`
(`TauCeti.GlobalNumberFields.IsIdealHeckeCharacter.idealCharacter_comp_heckeCharacter`). -/
noncomputable def heckeCharacter : HeckeCharacter K where
  toMonoidHom := QuotientGroup.lift _ hχ.idealHeckeIdele hχ.principalSubgroup_le_ker_idealHeckeIdele
  continuous_toFun :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr hχ.continuous_idealHeckeIdele

variable (x) in
lemma heckeCharacter_mk : hχ.heckeCharacter (x : IdeleClassGroup (𝓞 K) K) = hχ.idealHeckeIdele x :=
  rfl

variable (v) in
/-- **The conductor of the idelic Hecke character divides `𝔪`**: at every finite place `v`, its
conductor exponent is at most the exponent of `v` in `𝔪`, since the idelic character is trivial
on the units of `K_v` congruent to one modulo `𝔪`. -/
lemma conductorExponent_heckeCharacter_le : hχ.heckeCharacter.conductorExponent v ≤ 𝔪.exponent v :=
  (HeckeCharacter.conductorExponent_le_iff _ v _).mpr fun u hu ↦ by
    rw [HeckeCharacter.finiteComponent_apply, IdeleClassGroup.ofAdicCompletion_apply,
      heckeCharacter_mk, hχ.idealHeckeIdele_of_mem_ideleCongruenceSubgroup
        (ofAdicCompletion_mem_ideleCongruenceSubgroup_iff.mpr hu), idealHeckeInfinitePart_apply]
    simp

lemma support_finiteConductor_heckeCharacter_subset : (⟨hχ.heckeCharacter.finiteConductor,
    hχ.heckeCharacter.finiteConductor_ne_bot, ∅⟩ : Modulus K).support ⊆ 𝔪.support := fun v hv ↦ by
  have h₁ : hχ.heckeCharacter.conductorExponent v ≠ 0 :=
    (hχ.heckeCharacter.dvd_finiteConductor_iff v).mp ((Modulus.mem_support_iff _ v).mp hv)
  have h₂ : hχ.heckeCharacter.conductorExponent v ≤ 𝔪.exponent v :=
    hχ.conductorExponent_heckeCharacter_le v
  rw [Modulus.mem_support_iff_exponent_ne_zero]
  omega

/-- **The ideal character of the idelic Hecke character of `χ` is `χ`**: on an ideal `I` prime to
`𝔪`, represented by an idele congruent to one modulo `𝔪` with trivial infinite components, both
are `χ(I)`. -/
lemma idealCharacter_comp_heckeCharacter : hχ.heckeCharacter.idealCharacter.comp
    (NumberFieldArithmetic.idealsAwayInclusion K hχ.support_finiteConductor_heckeCharacter_subset) =
      χ := by
  refine MonoidHom.ext fun I ↦ ?_
  rcases toIdealsAway_surjective 𝔪.support I with ⟨⟨a, ha⟩, rfl⟩
  have hyf (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ 𝔪.support) :
      v.ideleFiniteCoord (ideleCongrOneOfFiniteIdele 𝔪 a) = 1 :=
    ideleFiniteCoord_ideleCongrOneOfFiniteIdele 𝔪 a hv
  have hyi (w : InfinitePlace K) : w.ideleInfiniteCoord (ideleCongrOneOfFiniteIdele 𝔪 a) = 1 :=
    ideleInfiniteCoord_ideleCongrOneOfFiniteIdele 𝔪 a w
  have hmem : ideleCongrOneOfFiniteIdele 𝔪 a ∈ ideleCongrOneSubgroup 𝔪 := by
    refine mem_ideleCongrOneSubgroup_iff.mpr ⟨fun v hv ↦ ?_, fun w _ ↦ ?_⟩
    · rw [hyf v ((𝔪.mem_support_iff v).mpr hv)]
      simp
    · rw [hyi]
      simp
  have hideal : toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 K) K
      (ideleCongrOneOfFiniteIdele 𝔪 a)) = toFractionalIdeal a :=
    toFractionalIdeal_ideleCongrOneOfFiniteIdele ha
  have ha' : IdeleGroup.toFiniteIdele (𝓞 K) K (ideleCongrOneOfFiniteIdele 𝔪 a) ∈
      adicOrdAway (⟨hχ.heckeCharacter.finiteConductor, hχ.heckeCharacter.finiteConductor_ne_bot,
        ∅⟩ : Modulus K).support := by
    refine (mem_adicOrdAway_iff _ _).mpr fun v hv ↦ adicOrd_eq_zero_iff.mpr ?_
    rw [IdeleGroup.coe_toFiniteIdele, ← HeightOneSpectrum.coe_ideleFiniteCoord,
      hyf v (hχ.support_finiteConductor_heckeCharacter_subset hv)]
    simp
  have hI : NumberFieldArithmetic.idealsAwayInclusion K
      hχ.support_finiteConductor_heckeCharacter_subset (toIdealsAway 𝔪.support ⟨a, ha⟩) =
        toIdealsAway _ ⟨_, ha'⟩ :=
    Subtype.ext (by rw [NumberFieldArithmetic.coe_idealsAwayInclusion, toIdealsAway_apply,
      toIdealsAway_apply, hideal])
  have hyfin : IdeleGroup.ofFiniteIdele (𝓞 K) K (IdeleGroup.toFiniteIdele (𝓞 K) K
      (ideleCongrOneOfFiniteIdele 𝔪 a)) = ideleCongrOneOfFiniteIdele 𝔪 a :=
    IdeleGroup.ext (fun w ↦ by rw [InfinitePlace.ideleInfiniteCoord_ofFiniteIdele, hyi])
      fun v ↦ Units.ext (by simp only [HeightOneSpectrum.coe_ideleFiniteCoord,
        IdeleGroup.coe_ofFiniteIdele, IdeleGroup.coe_toFiniteIdele])
  rw [MonoidHom.comp_apply, hI, HeckeCharacter.idealCharacter_apply_toIdealsAway_of_eq_one _ _
    fun v hv ↦ by rw [hyfin, hyf v (hχ.support_finiteConductor_heckeCharacter_subset hv)],
    Subgroup.coe_mk, hyfin, heckeCharacter_mk, hχ.idealHeckeIdele_of_mem hmem,
    idealHeckeCongrOne_apply, idealHeckeInfinitePart_apply]
  simp only [hyi, map_one, Finset.prod_const_one, inv_one, mul_one]
  refine congrArg χ (Subtype.ext ?_)
  rw [toIdealsAway_apply]
  exact hideal

end IsIdealHeckeCharacter

lemma HeckeCharacter.isCongrOne_of_conductorExponent_le {ψ : HeckeCharacter K}
    (hexp : ∀ v, ψ.conductorExponent v ≤ 𝔪.exponent v) {x : Kˣ} (hx : IsCongrOne 𝔪 x) :
    IsCongrOne ⟨ψ.finiteConductor, ψ.finiteConductor_ne_bot, ∅⟩ x := by
  refine ⟨fun v hv ↦ ?_, fun w hw ↦ absurd hw (Finset.notMem_empty w)⟩
  have he : (⟨ψ.finiteConductor, ψ.finiteConductor_ne_bot, ∅⟩ : Modulus K).exponent v =
      ψ.conductorExponent v := by
    rw [Modulus.exponent_def]
    exact ψ.count_finiteConductor v
  have h₁ : ψ.conductorExponent v ≠ 0 := (ψ.dvd_finiteConductor_iff v).mp hv
  have h₂ : ψ.conductorExponent v ≤ 𝔪.exponent v := hexp v
  have hv' : v.asIdeal ∣ 𝔪.finitePart :=
    (𝔪.mem_support_iff v).mp ((𝔪.mem_support_iff_exponent_ne_zero v).mpr (by omega))
  rw [he]
  exact (hx.1 v hv').trans (WithZero.exp_le_exp.mpr (by omega))

/-- **Ideal-theoretic Hecke characters are the ideal characters of idelic Hecke characters**
(LMFDB `character.hecke`): a character `χ` of the group `I(𝔪)` of fractional ideals prime to a
modulus `𝔪` is a Hecke character modulo `𝔪` in the ideal-theoretic sense exactly when there is a
Hecke character `ψ` of the idele class group whose conductor divides `𝔪` (its conductor exponents
are at most those of `𝔪`) and whose ideal character, restricted to `I(𝔪)`, is `χ`. -/
lemma isIdealHeckeCharacter_iff : IsIdealHeckeCharacter 𝔪 χ ↔ ∃ (ψ : HeckeCharacter K)
    (h : (⟨ψ.finiteConductor, ψ.finiteConductor_ne_bot, ∅⟩ : Modulus K).support ⊆ 𝔪.support),
    (∀ v, ψ.conductorExponent v ≤ 𝔪.exponent v) ∧
      ψ.idealCharacter.comp (NumberFieldArithmetic.idealsAwayInclusion K h) = χ := by
  refine ⟨fun hχ ↦ ⟨hχ.heckeCharacter, hχ.support_finiteConductor_heckeCharacter_subset,
    hχ.conductorExponent_heckeCharacter_le, hχ.idealCharacter_comp_heckeCharacter⟩, ?_⟩
  rintro ⟨ψ, h, hexp, rfl⟩
  rcases ψ.isIdealHeckeCharacter_idealCharacter with ⟨φ, hφ⟩
  exact ⟨φ, fun x hx ↦ hφ x (ψ.isCongrOne_of_conductorExponent_le hexp hx)⟩

end TauCeti.GlobalNumberFields
