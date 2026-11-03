import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Valuation.LocalSubring
import TauCeti.AlgebraicGeometry.Modules.RationalFunctions
import TauCeti.AlgebraicGeometry.Scheme.FunctionField
import TauCeti.FieldTheory.FunctionField.Place.Approximation
import TauCeti.FieldTheory.FunctionField.Place.OfValuationSubring
import TauCeti.FieldTheory.FunctionField.Place.Zeros
import TauCeti.RingTheory.IntegralClosure.MvPolynomial

/-!
# A finite set of closed points of a curve lies in an affine open subset

Every finite set of closed points of an integral separated scheme of finite type and dimension one
over a field `K` lies in an affine open subset. This is the input that gives a stable affine cover
of a curve with an action of a finite group, hence the quotient curve (LMFDB `ag.quotient_curve`),
without quasi-projectivity: the classical statement that a curve is quasi-projective is not used,
and the argument stays inside the local rings of the curve.

Let `S` be such a finite set, and `F` the function field. Finitely many places of `F / K` have a
valuation ring containing the local ring `𝒪_x` of a point `x` of `S`. The integral closure of `𝒪_x`
in `F` is the intersection of these valuation rings, and multiplying it by some nonzero element
`c_x`, a conductor, brings it into `𝒪_x`, since the integral closure of a finitely generated
`K`-algebra is finite over it. By weak approximation, there is a nonzero `y` in `F` of large order
at these finitely many places, so `y` lies in the maximal ideal of `𝒪_x` for every `x` in `S`.

On the open subset `U` of `X` where `y` is regular, the fibre of `U ⟶ Spec Γ(X, U)` through a point
`x` of `S` lies in the zero locus of `y`, a finite set. Thus `U ⟶ Spec Γ(X, U)` is quasi-finite at
the points of `S`, and Zariski's main theorem embeds an open neighbourhood of `S` in `U` as an open
subset of a scheme integral over `Spec Γ(X, U)`, which is affine. Prime avoidance finishes the
proof: a finite subset of an open subset of an affine scheme lies in a basic open subset of the
affine scheme, contained in that open subset.

## Main results

* `AlgebraicGeometry.Scheme.exists_isAffineOpen_of_isOpenImmersion`: a finite subset of a
  quasi-affine scheme lies in an affine open subset.
* `AlgebraicGeometry.Scheme.exists_isAffineOpen_forall_mem`: a finite set of closed points of a
  curve lies in an affine open subset.
-/

open TauCeti CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing Order Scheme RingHom

universe u

lemma IsFractionRing.exists_mul_mem_of_isIntegral (K : Type*) [Field K] {A F : Type*} [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Field F] [Algebra A F]
    [IsFractionRing A F] :
    ∃ c : A, c ≠ 0 ∧ ∀ z : F, IsIntegral A z → algebraMap A F c * z ∈ (algebraMap A F).range := by
  classical
  rcases exists_finite_inj_algHom_of_fg K A with ⟨s, g, hg, hfin⟩
  let P : Type _ := MvPolynomial (Fin s) K
  let _ : Algebra P A := g.toRingHom.toAlgebra
  let _ : Algebra P F := ((algebraMap A F).comp g.toRingHom).toAlgebra
  have : IsScalarTower P A F := .of_algebraMap_eq' rfl
  have : Module.Finite P A := hfin
  have hinj : Function.Injective (algebraMap P F) := (IsFractionRing.injective A F).comp hg
  have : FaithfulSMul P F := (faithfulSMul_iff_algebraMap_injective P F).mpr hinj
  let E : Type _ := FractionRing P
  let _ : Algebra E F := FractionRing.liftAlgebra P F
  have : IsScalarTower P E F := FractionRing.isScalarTower_liftAlgebra P F
  have : Algebra.EssFiniteType A F := .of_isLocalization F (nonZeroDivisors A)
  have : Algebra.EssFiniteType P F := .comp P A F
  have : Algebra.EssFiniteType E F := .of_comp P E F
  have : Algebra.IsAlgebraic A F := IsLocalization.isAlgebraic F (nonZeroDivisors A)
  have : Algebra.IsAlgebraic P F := .trans P A F
  have : Algebra.IsAlgebraic E F := .extendScalars (IsFractionRing.injective P E)
  have : FiniteDimensional E F := Algebra.finite_of_essFiniteType_of_isAlgebraic
  have hC : Module.Finite P (integralClosure P F) :=
    IsIntegralClosure.finite_mvPolynomial K E F (integralClosure P F)
  rcases hC.fg_top with ⟨t, ht⟩
  rcases IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
    (t.image (algebraMap (integralClosure P F) F)) with ⟨b, hb⟩
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, fun z hz ↦ ?_⟩
  have hmem : (⟨z, isIntegral_trans z hz⟩ : integralClosure P F) ∈
      Submodule.span P (t : Set (integralClosure P F)) := ht ▸ Submodule.mem_top
  have key : ∀ x ∈ Submodule.span P (t : Set (integralClosure P F)),
      algebraMap A F b * (x : F) ∈ (algebraMap A F).range := fun x hx ↦ by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases hb _ (Finset.mem_image_of_mem _ hx) with ⟨a, ha⟩
      exact ⟨a, ha.trans (Algebra.smul_def _ _)⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      exact (congrArg (· ∈ (algebraMap A F).range) (mul_add _ (x : F) y)).mpr (add_mem hx hy)
    | smul p x _ hx =>
      rcases hx with ⟨a, ha⟩
      have h₁ : ((p • x : integralClosure P F) : F) = algebraMap A F (g p) * x :=
        Algebra.smul_def p (x : F)
      refine ⟨g p * a, ?_⟩
      rw [map_mul, ha, h₁]
      ring1
  exact key _ hmem

namespace AlgebraicGeometry.Scheme

variable {Z : Scheme.{u}} [IsAffine Z]

lemma exists_basicOpen_of_finite (W : Z.Opens) {T : Set Z} (hT : T.Finite) (hTW : T ⊆ W) :
    ∃ g : Γ(Z, ⊤), T ⊆ Z.basicOpen g ∧ Z.basicOpen g ≤ W := by
  classical
  have hmem (g : Γ(Z, ⊤)) (z : Z) :
      z ∈ Z.basicOpen g ↔ g ∉ (Z.toSpecΓ z : PrimeSpectrum Γ(Z, ⊤)).asIdeal := by
    rw [← Z.toSpecΓ_preimage_basicOpen g]
    rfl
  let C : Set (PrimeSpectrum Γ(Z, ⊤)) := Z.toSpecΓ '' (W : Set Z)ᶜ
  have hC : IsClosed C := Z.toSpecΓ.homeomorph.isClosedMap _ W.isOpen.isClosed_compl
  let I : Ideal Γ(Z, ⊤) := PrimeSpectrum.vanishingIdeal C
  let s : Finset (Ideal Γ(Z, ⊤)) :=
    hT.toFinset.image fun t ↦ (Z.toSpecΓ t : PrimeSpectrum _).asIdeal
  have hs : ¬(I : Set Γ(Z, ⊤)) ⊆ ⋃ i ∈ (s : Set (Ideal Γ(Z, ⊤))), (i : Set Γ(Z, ⊤)) := by
    refine (Ideal.subset_union_prime ⊥ ⊥ fun i hi _ _ ↦ ?_).not.mpr ?_
    · rcases Finset.mem_image.mp hi with ⟨t, -, rfl⟩
      exact (Z.toSpecΓ t : PrimeSpectrum _).isPrime
    · rintro ⟨i, hi, hIi⟩
      rcases Finset.mem_image.mp hi with ⟨t, ht, rfl⟩
      have h₁ : (Z.toSpecΓ t : PrimeSpectrum _) ∈ PrimeSpectrum.zeroLocus (I : Set Γ(Z, ⊤)) := hIi
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hC.closure_eq] at h₁
      rcases h₁ with ⟨z, hz, hzt⟩
      exact hz (Z.toSpecΓ.homeomorph.injective hzt ▸ hTW (hT.mem_toFinset.mp ht))
  rcases Set.not_subset.mp hs with ⟨g, hgI, hg⟩
  refine ⟨g, fun t ht ↦ (hmem g t).mpr fun hgt ↦ hg ?_, fun z hz ↦ ?_⟩
  · exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (hT.mem_toFinset.mpr ht)))
      hgt
  · by_contra hzW
    exact (hmem g z).mp hz ((PrimeSpectrum.mem_vanishingIdeal _ _).mp hgI _ ⟨z, hzW, rfl⟩)

/-- **A finite subset of a quasi-affine scheme lies in an affine open subset.** -/
lemma exists_isAffineOpen_of_isOpenImmersion {L : Scheme.{u}} (j : L ⟶ Z) [IsOpenImmersion j]
    {T : Set L} (hT : T.Finite) : ∃ V : L.Opens, IsAffineOpen V ∧ T ⊆ V := by
  rcases exists_basicOpen_of_finite j.opensRange (hT.image j)
    (Set.image_subset_range _ _) with ⟨g, hg, hle⟩
  exact ⟨j ⁻¹ᵁ Z.basicOpen g, ((isAffineOpen_top Z).basicOpen g).preimage_of_isOpenImmersion j hle,
    fun t ht ↦ hg ⟨t, ht, rfl⟩⟩

variable {X : Scheme.{u}}

lemma toSpecΓ_comp_specMap {R : CommRingCat.{u}} (U : X.Opens) (h : U.toScheme ⟶ Spec R) :
    U.toSpecΓ ≫ Spec.map ((ΓSpecIso R).inv ≫ h.appTop ≫ U.topIso.hom) = h := by
  have h₁ : U.toScheme.toSpecΓ ≫ Spec.map h.appTop ≫ Spec.map (ΓSpecIso R).inv = h := by
    rw [← toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.comp_id]
  rw [Opens.toSpecΓ, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    ← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp, h₁]

variable [IsIntegral X] {x : X} {S : Set X}

lemma valuation_lt_one_of_mem_maximalIdeal {K : Type u} [Field K] [X.Over (Spec (.of K))]
    (hX : topologicalKrullDim X = 1) (P : Place K X.functionField)
    (hP : ∀ a : X.presheaf.stalk x, algebraMap _ X.functionField a ∈ P.integers)
    {w : X.presheaf.stalk x} (hw : w ∈ maximalIdeal (X.presheaf.stalk x)) :
    P.valuation (algebraMap _ X.functionField w) < 1 := by
  have hdim : ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
    rw [ringKrullDim_stalk_eq_coheight, ← hX]
    exact coheight_le_topologicalKrullDim x
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := Ring.krullDimLE_iff.mpr (by exact_mod_cast hdim)
  let ψ : X.presheaf.stalk x →+* P.integers :=
    (algebraMap (X.presheaf.stalk x) X.functionField).codRestrict P.integers hP
  let q : Ideal (X.presheaf.stalk x) := (maximalIdeal P.integers).comap ψ
  have hq : q.IsPrime := Ideal.comap_isPrime _ _
  have hne : q ≠ ⊥ := by
    intro hb
    have hunit (a : X.presheaf.stalk x) (ha : a ≠ 0) :
        P.valuation (algebraMap _ X.functionField a) = 1 := by
      refine (P.isUnit_iff_valuation_eq_one (x := ψ a)).mp (of_not_not fun h₁ ↦ ha ?_)
      have h₂ : a ∈ q := h₁
      exact Ideal.mem_bot.mp (hb ▸ h₂)
    rcases IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr P.integers_ne_top) with ⟨t, -, ht⟩
    rcases IsFractionRing.div_surjective (A := X.presheaf.stalk x) t with ⟨a, b, hb, rfl⟩
    refine ht (P.mem_integers_iff.mpr ?_)
    rw [map_div₀, hunit b (nonZeroDivisors.ne_zero hb), div_one]
    exact hP a
  have hm : q = maximalIdeal (X.presheaf.stalk x) :=
    eq_maximalIdeal (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp this q hne hq)
  exact P.mem_maximalIdeal_iff_valuation_lt_one.mp (hm ▸ hw : w ∈ q)

lemma exists_ne_zero_mem_maximalIdeal (hx : x ≠ genericPoint X) :
    ∃ w ∈ maximalIdeal (X.presheaf.stalk x), w ≠ 0 := by
  by_contra! h
  have h₁ : maximalIdeal (X.presheaf.stalk x) = ⊥ := (Submodule.eq_bot_iff _).mpr h
  have h₂ : ringKrullDim (X.presheaf.stalk x) = 0 :=
    ringKrullDim_eq_zero_of_isField ((isField_iff_maximalIdeal_eq).mpr h₁)
  rw [ringKrullDim_stalk_eq_coheight] at h₂
  have h₃ : IsMax x := coheight_eq_zero.mp (by exact_mod_cast h₂)
  have h₄ : x ≤ ⊤ := le_top
  exact hx (Specializes.antisymm (h₃ h₄) h₄).eq

lemma isIntegralElem_of_forall_mem_integers (K : Type u) [Field K] [X.Over (Spec (.of K))]
    (hF : IsFunctionField K X.functionField) {z : X.functionField}
    (hz : ∀ P : Place K X.functionField,
      (∀ a : X.presheaf.stalk x, algebraMap _ X.functionField a ∈ P.integers) → z ∈ P.integers) :
    (algebraMap (X.presheaf.stalk x) X.functionField).IsIntegralElem z := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  let R : Subring X.functionField := (algebraMap (X.presheaf.stalk x) X.functionField).range
  have hz₁ : z ∈ (integralClosure (Subring.closure (R : Set X.functionField))
      X.functionField).toSubring := by
    rw [← iInf_valuationSubring_superset]
    refine Subring.mem_iInf.mpr fun V ↦ ?_
    by_cases hV : V.1 = ⊤
    · exact hV ▸ ValuationSubring.mem_top z
    have hk (c : K) : algebraMap K X.functionField c ∈ V.1 :=
      V.2 ⟨X.presheaf.germ ⊤ x trivial (Modules.baseRingToGlobalSections K X c),
        algebraMap_germ_eq_germToFunctionField X trivial _⟩
    have hP : (Place.ofValuationSubring hF hk hV).integers = V.1 :=
      Place.integers_ofValuationSubring hF hk hV
    have h₁ : z ∈ (Place.ofValuationSubring hF hk hV).integers := hz _ fun a ↦ by
      rw [hP]
      exact V.2 ⟨a, rfl⟩
    rw [hP] at h₁
    exact h₁
  rw [Subring.closure_eq] at hz₁
  let _ : Algebra (X.presheaf.stalk x) R :=
    (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict.toAlgebra
  have : IsScalarTower (X.presheaf.stalk x) R X.functionField := .of_algebraMap_eq' rfl
  have : Algebra.IsIntegral (X.presheaf.stalk x) R := Algebra.isIntegral_of_surjective
    (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict_surjective
  exact isIntegral_trans z hz₁

lemma finite_of_isClosed_of_genericPoint_notMem [NoetherianSpace X] (hX : topologicalKrullDim X = 1)
    {T : Set X} (hT : IsClosed T) (hη : genericPoint X ∉ T) : T.Finite := by
  have hdim (y : X) : coheight y ≤ 1 := by
    have h₁ : (coheight y : WithBot ℕ∞) ≤ topologicalKrullDim X := coheight_le_topologicalKrullDim y
    rw [hX] at h₁
    exact_mod_cast h₁
  have hcl (y : X) (hy : y ≠ genericPoint X) : IsClosed {y} := by
    refine isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one hdim ?_
    refine le_antisymm (hdim y) (one_le_iff_ne_zero.mpr fun h₀ ↦ hy ?_)
    have h₄ : y ≤ ⊤ := le_top
    exact (Specializes.antisymm (coheight_eq_zero.mp h₀ h₄) h₄).eq
  rcases NoetherianSpace.exists_finite_set_isClosed_irreducible hT with ⟨A, hA, hc, hirr, rfl⟩
  refine hA.sUnion fun t ht ↦ ?_
  have hζ : IsGenericPoint (hirr t ht).genericPoint t := by
    simpa [(hc t ht).closure_eq] using (hirr t ht).isGenericPoint_genericPoint_closure
  have hmem : (hirr t ht).genericPoint ∈ t := hζ.mem
  have hne : (hirr t ht).genericPoint ≠ genericPoint X :=
    fun h₀ ↦ hη ⟨t, ht, h₀ ▸ hmem⟩
  have hsingle : t = {(hirr t ht).genericPoint} := hζ.def.symm.trans (hcl _ hne).closure_eq
  exact hsingle ▸ Set.finite_singleton _

lemma isOpen_setOf_mem_range_stalk (y : X.functionField) :
    IsOpen {x : X | y ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range} := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  rcases hx with ⟨g, rfl⟩
  rcases X.presheaf.exists_germ_eq g with ⟨W, hxW, s, rfl⟩
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  refine ⟨W, fun u hu ↦ ⟨X.presheaf.germ W u hu s, ?_⟩, W.isOpen, hxW⟩
  rw [algebraMap_germ_eq_germToFunctionField, algebraMap_germ_eq_germToFunctionField]

variable (x) in
lemma exists_mul_mem_stalk (K : Type u) [Field K] [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] : ∃ c : X.functionField, c ≠ 0 ∧ ∀ z : X.functionField,
      (algebraMap (X.presheaf.stalk x) X.functionField).IsIntegralElem z →
        c * z ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  rcases X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ with
    ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let φ : K →+* Γ(X, U) :=
    ((X ↘ Spec (.of K)).appLE ⊤ U le_top).hom.comp (ΓSpecIso (.of K)).inv.hom
  let _ : Algebra K Γ(X, U) := φ.toAlgebra
  have h₀ : ((X ↘ Spec (.of K)).appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType (X ↘ Spec (.of K)) inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have hft : Algebra.FiniteType K Γ(X, U) := h₀.comp (FiniteType.of_surjective _
    (ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv.surjective)
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  rcases IsFractionRing.exists_mul_mem_of_isIntegral K (A := Γ(X, U)) (F := X.functionField) with
    ⟨c, hc, hcz⟩
  have hinj : Function.Injective (algebraMap Γ(X, U) X.functionField) :=
    IsFractionRing.injective _ _
  refine ⟨algebraMap _ _ c, (map_ne_zero_iff _ hinj).mpr hc, fun z hz ↦ ?_⟩
  let x' : U := ⟨x, hxU⟩
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x') := X.presheaf.algebra_section_stalk x'
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x') (hU.primeIdealOf x').asIdeal :=
    hU.isLocalization_stalk x'
  have htw : IsScalarTower Γ(X, U) (X.presheaf.stalk x') X.functionField :=
    functionField_isScalarTower X U x'
  rcases IsIntegral.exists_multiple_integral_of_isLocalization
    (hU.primeIdealOf x').asIdeal.primeCompl (Rₘ := X.presheaf.stalk x') z hz with ⟨s, hs⟩
  rcases hcz _ hs with ⟨a, ha⟩
  have hs0 : algebraMap Γ(X, U) X.functionField s ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr fun h₀ ↦ s.2 (h₀ ▸ zero_mem _)
  have h₁ : algebraMap (X.presheaf.stalk x') X.functionField
      (IsLocalization.mk' (X.presheaf.stalk x') a s * algebraMap Γ(X, U) _ s) =
        algebraMap (X.presheaf.stalk x') X.functionField (algebraMap Γ(X, U) _ a) :=
    congrArg _ (IsLocalization.mk'_spec (X.presheaf.stalk x') a s)
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h₁
  refine ⟨IsLocalization.mk' (X.presheaf.stalk x') a s, mul_right_cancel₀ hs0 (h₁.trans ?_)⟩
  refine ha.trans ?_
  rw [Submonoid.smul_def, Algebra.smul_def]
  ring1

lemma exists_ne_zero_forall_mem_maximalIdeal (K : Type u) [Field K] [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] (hX : topologicalKrullDim X = 1) (hS : S.Finite)
    (hη : genericPoint X ∉ S) : ∃ y : X.functionField, y ≠ 0 ∧ ∀ x ∈ S,
      ∃ w ∈ maximalIdeal (X.presheaf.stalk x), algebraMap _ X.functionField w = y := by
  classical
  have hF : IsFunctionField K X.functionField := (isFunctionField_functionField_iff K).mpr hX
  have hinj (x : X) : Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) :=
    IsFractionRing.injective _ _
  have h₁ (x : X) (hx : x ∈ S) : ∃ c w : X.functionField, c ≠ 0 ∧ w ≠ 0 ∧
      (∃ w₀ ∈ maximalIdeal (X.presheaf.stalk x), algebraMap _ X.functionField w₀ = w) ∧
      ∀ z : X.functionField, (algebraMap (X.presheaf.stalk x) X.functionField).IsIntegralElem z →
        c * z ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by
    rcases exists_mul_mem_stalk x K with ⟨c, hc, hcz⟩
    rcases exists_ne_zero_mem_maximalIdeal (ne_of_mem_of_not_mem hx hη) with ⟨w, hw, hw0⟩
    exact ⟨c, algebraMap _ _ w, hc, (map_ne_zero_iff _ (hinj x)).mpr hw0, ⟨w, hw, rfl⟩, hcz⟩
  choose! c w hc hw hw₀ hcz using h₁
  let Pl (x : X) : Set (Place K X.functionField) :=
    {P | ∀ a : X.presheaf.stalk x, algebraMap _ X.functionField a ∈ P.integers}
  have hPl (x : X) (hx : x ∈ S) : (Pl x).Finite := by
    refine (Place.finite_setOf_ord_pos hF (w x)).subset fun P hP ↦ ?_
    rcases hw₀ x hx with ⟨w₀, hw₁, hw₂⟩
    exact (P.valuation_lt_one_iff_ord_pos (hw x hx)).mp
      (hw₂ ▸ valuation_lt_one_of_mem_maximalIdeal hX P hP hw₁)
  let r (P : Place K X.functionField) : ℤ := ∑ x ∈ hS.toFinset, (|P.ord (c x)| + |P.ord (w x)|)
  rcases Place.exists_ne_zero_forall_mem_ord_eq (hS.biUnion hPl).toFinset r with ⟨y, hy0, hy⟩
  refine ⟨y, hy0, fun x hx ↦ ?_⟩
  have hcw : c x * w x ≠ 0 := mul_ne_zero (hc x hx) (hw x hx)
  have hz : (algebraMap (X.presheaf.stalk x) X.functionField).IsIntegralElem (y / (c x * w x)) := by
    refine isIntegralElem_of_forall_mem_integers K hF fun P hP ↦ ?_
    have hPZ : P ∈ (hS.biUnion hPl).toFinset :=
      (hS.biUnion hPl).mem_toFinset.mpr (Set.mem_biUnion hx hP)
    have h₂ : |P.ord (c x)| + |P.ord (w x)| ≤ r P :=
      Finset.single_le_sum (f := fun x ↦ |P.ord (c x)| + |P.ord (w x)|)
        (fun _ _ ↦ add_nonneg (abs_nonneg _) (abs_nonneg _)) (hS.mem_toFinset.mpr hx)
    rw [P.mem_integers_iff_ord_nonneg, P.ord_div hy0 hcw, P.ord_mul (hc x hx) (hw x hx), hy P hPZ]
    linarith [le_abs_self (P.ord (c x)), le_abs_self (P.ord (w x))]
  rcases hcz x hx _ hz with ⟨v, hv⟩
  rcases hw₀ x hx with ⟨w₀, hw₁, hw₂⟩
  refine ⟨w₀ * v, Ideal.mul_mem_right _ _ hw₁, ?_⟩
  rw [map_mul, hw₂, hv]
  field_simp [hc x hx, hw x hx]

/-- **A finite set of closed points of a curve lies in an affine open subset.** The closed points
are the points other than the generic point, and the curve need not be proper or regular. -/
lemma exists_isAffineOpen_forall_mem (K : Type u) [Field K] [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [CompactSpace X] [IsSeparated (X ↘ Spec (.of K))]
    (hX : topologicalKrullDim X = 1) (hS : S.Finite) (hη : genericPoint X ∉ S) :
    ∃ U : X.Opens, IsAffineOpen U ∧ S ⊆ U := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨⊥, isAffineOpen_bot X, Set.empty_subset _⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have : IsNoetherian X := {}
  rcases exists_ne_zero_forall_mem_maximalIdeal K hX hS hη with ⟨y, hy0, hy⟩
  let U : X.Opens := ⟨_, isOpen_setOf_mem_range_stalk y⟩
  have hSU : S ⊆ U := fun x hx ↦ (hy x hx).elim fun w hw ↦ ⟨w, hw.2⟩
  have : Nonempty U := ⟨⟨x₀, hSU hx₀⟩⟩
  rcases exists_germToFunctionField_eq_of_forall_mem_range (U := U) (f := y) fun u hu ↦ hu with
    ⟨a, ha⟩
  let h : U.toScheme ⟶ Spec (.of K) := U.ι ≫ (X ↘ Spec (.of K))
  let g : Spec Γ(X, U) ⟶ Spec (.of K) :=
    Spec.map ((ΓSpecIso (.of K)).inv ≫ h.appTop ≫ U.topIso.hom)
  have hcomp : U.toSpecΓ ≫ g = h := toSpecΓ_comp_specMap U h
  have : LocallyOfFiniteType (U.toSpecΓ ≫ g) := by
    rw [hcomp]
    infer_instance
  have : LocallyOfFiniteType U.toSpecΓ := locallyOfFiniteType_of_comp U.toSpecΓ g
  have : IsSeparated (U.toSpecΓ ≫ g) := by
    rw [hcomp]
    infer_instance
  have : IsSeparated U.toSpecΓ := .of_comp U.toSpecΓ g
  have : NoetherianSpace U.toScheme := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  have hnot (x : X) (hx : x ∈ S) : x ∉ X.basicOpen a := by
    rcases hy x hx with ⟨w, hw, hwy⟩
    refine fun hb ↦ (mem_maximalIdeal w).mp hw ?_
    have h₁ : algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x (hSU hx) a) =
        algebraMap (X.presheaf.stalk x) X.functionField w :=
      (algebraMap_germ_eq_germToFunctionField X (hSU hx) a).trans (ha.trans hwy.symm)
    exact IsFractionRing.injective _ _ h₁ ▸ (mem_basicOpen _ _ x (hSU hx)).mp hb
  have hTf : ((X.basicOpen a : Set X)ᶜ).Finite := by
    refine finite_of_isClosed_of_genericPoint_notMem hX (X.basicOpen a).isOpen.isClosed_compl
      fun hη' ↦ hη' ?_
    have hηU : genericPoint X ∈ U := genericPoint_mem U
    refine (mem_basicOpen _ _ _ hηU).mpr (isUnit_iff_ne_zero.mpr ?_)
    exact ha ▸ hy0
  have hq (x : X) (hx : x ∈ S) : U.toSpecΓ.QuasiFiniteAt (⟨x, hSU hx⟩ : U) := by
    have hfin : (U.toSpecΓ ⁻¹' {U.toSpecΓ ⟨x, hSU hx⟩}).Finite := by
      refine (hTf.preimage U.ι.isOpenEmbedding.injective.injOn).subset fun u hu hub ↦ ?_
      have h₁ : u ∈ U.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen a := by
        rw [Opens.toSpecΓ_preimage_basicOpen]
        exact hub
      have h₂ : U.toSpecΓ u ∈ PrimeSpectrum.basicOpen a := h₁
      rw [Set.mem_singleton_iff.mp hu] at h₂
      have h₃ : (⟨x, hSU hx⟩ : U) ∈ U.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen a := h₂
      rw [Opens.toSpecΓ_preimage_basicOpen] at h₃
      exact hnot x hx h₃
    have : Finite (U.toSpecΓ.fiber (U.toSpecΓ ⟨x, hSU hx⟩)) :=
      (U.toSpecΓ.fiberHomeo _).finite_iff.mpr hfin
    exact Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)
  have : IsAffine U.toSpecΓ.normalization := isAffine_of_isAffineHom U.toSpecΓ.fromNormalization
  let i : U.toSpecΓ.quasiFiniteLocus.toScheme ⟶ X := U.toSpecΓ.quasiFiniteLocus.ι ≫ U.ι
  rcases exists_isAffineOpen_of_isOpenImmersion
    (U.toSpecΓ.quasiFiniteLocus.ι ≫ U.toSpecΓ.toNormalization)
    (hS.preimage i.isOpenEmbedding.injective.injOn) with ⟨V, hV, hTV⟩
  refine ⟨i ''ᵁ V, hV.image_of_isOpenImmersion i, fun x hx ↦ ?_⟩
  exact ⟨⟨⟨x, hSU hx⟩, hq x hx⟩, hTV hx, rfl⟩

end AlgebraicGeometry.Scheme
