import TauCeti.NumberTheory.NumberField.Global.Orders.Gorenstein

/-!
# The Cohen–Macaulay type of an order

An order `R` in an étale algebra `K` over `ℚ`, a finite product of number fields, is a subring of
`K` whose additive group is a lattice of full rank, such as an order in a number field or an
overorder of the Frobenius order of an isogeny class of abelian varieties over a finite field. It
is a one-dimensional Noetherian ring, the coordinate ring of an affine arithmetic curve, and its
trace dual `Rᵗ = {a ∈ K | Tr(aR) ⊆ ℤ}` is a canonical module. The Cohen–Macaulay type of `R` is the
minimal number of generators of a canonical module, read locally: at a maximal ideal `𝔩`, the
minimal number of generators of `Rᵗ_𝔩` over `R_𝔩` is, by Nakayama's lemma, the dimension of
`Rᵗ / 𝔩Rᵗ` over `R / 𝔩`, and the type of `R` is the largest of these. The definitions make sense
for any subring of a commutative `ℚ`-algebra; their basic properties are proved for orders in
number fields, Tau Ceti's `TauCeti.GlobalNumberFields.NumberFieldOrder`, whose trace dual is the
trace dual here.

An order in a number field is Gorenstein, that is `Rᵗ` is invertible (Tau Ceti's
`TauCeti.GlobalNumberFields.NumberFieldOrder.IsGorenstein`), exactly when its Cohen–Macaulay type
is `1`: an invertible fractional ideal `I` has `I / 𝔩I` of dimension one at every maximal ideal, and
conversely a fractional ideal with `I / 𝔩I` of dimension at most one at every maximal ideal is
locally principal by Nakayama's lemma, hence invertible.

## Main definitions

* `Subalgebra.traceDual`: the trace dual `Rᵗ` of a subring `R` of a commutative `ℚ`-algebra.
* `Subalgebra.cohenMacaulayTypeAt`: the dimension of `Rᵗ / 𝔩Rᵗ` over `R / 𝔩`.
* `Subalgebra.cohenMacaulayType` (LMFDB `ag.cohen_macaulay_type`): the Cohen–Macaulay type.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.cohenMacaulayTypeAt_le_cohenMacaulayType` and
  `TauCeti.GlobalNumberFields.NumberFieldOrder.exists_cohenMacaulayTypeAt_eq_cohenMacaulayType`:
  the Cohen–Macaulay type of an order in a number field is the largest of its local types,
  attained at some maximal ideal.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.cohenMacaulayType_eq_one_iff_isGorenstein`: an
  order in a number field has Cohen–Macaulay type `1` if and only if it is Gorenstein.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.cohenMacaulayType_eq_one_iff_forall_isUnit`: an order
  in a number field has Cohen–Macaulay type `1` if and only if its proper fractional ideals are
  invertible.
-/

open FractionalIdeal Module Submodule
open Ideal.Quotient (field)
open scoped nonZeroDivisors Pointwise

attribute [local instance] field

namespace FractionalIdeal

variable {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] {I : FractionalIdeal R⁰ K} (𝔩 : Ideal R) [𝔩.IsMaximal]

lemma finite_of_isNoetherianRing : Module.Finite R I :=
  Finite.iff_fg.mpr (fg_of_isNoetherianRing le_rfl I)

attribute [local instance] finite_of_isNoetherianRing

omit [𝔩.IsMaximal] in
lemma finite_quotient_smul_top : Module.Finite (R ⧸ 𝔩) (I ⧸ 𝔩 • (⊤ : Submodule R I)) :=
  Finite.of_restrictScalars_finite R _ _

attribute [local instance] finite_quotient_smul_top

lemma finrank_quotient_smul_top_le_one_of_isUnit (hI : IsUnit I) :
    finrank (R ⧸ 𝔩) (I ⧸ 𝔩 • (⊤ : Submodule R I)) ≤ 1 := by
  have h1 : I * I⁻¹ = 1 := (mul_inv_cancel_iff_isUnit K).mpr hI
  have hle : ¬I * I⁻¹ ≤ (𝔩 : FractionalIdeal R⁰ K) := by
    rw [h1, ← coeIdeal_top, coeIdeal_le_coeIdeal' R⁰ le_rfl, top_le_iff]
    exact ‹𝔩.IsMaximal›.ne_top
  rw [mul_le] at hle
  push Not at hle
  rcases hle with ⟨a, ha, b, hb, hab⟩
  rcases (mem_one_iff R⁰).mp (h1 ▸ mul_mem_mul ha hb) with ⟨u, hu⟩
  rcases ‹𝔩.IsMaximal›.exists_inv fun h ↦ hab (hu ▸ mem_coeIdeal_of_mem R⁰ h) with
    ⟨v, i, hi, hvi⟩
  have hvi' : algebraMap R K v * algebraMap R K u + algebraMap R K i = 1 := by
    rw [← map_mul, ← map_add, hvi, map_one]
  rw [finrank_le_one_iff]
  refine ⟨(𝔩 • ⊤ : Submodule R I).mkQ ⟨a, ha⟩, fun w ↦ ?_⟩
  rcases (𝔩 • ⊤ : Submodule R I).mkQ_surjective w with ⟨⟨x, hx⟩, rfl⟩
  rcases (mem_one_iff R⁰).mp (h1 ▸ mul_mem_mul hx hb) with ⟨c, hc⟩
  refine ⟨algebraMap R (R ⧸ 𝔩) (v * c), ?_⟩
  rw [algebraMap_smul, ← map_smul, ← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, ker_mkQ]
  convert neg_mem (smul_mem_smul hi mem_top : i • (⟨x, hx⟩ : (I : Submodule R K)) ∈ 𝔩 • ⊤)
    using 1
  ext
  push_cast [Algebra.smul_def]
  linear_combination algebraMap R K v * a * hc - algebraMap R K v * x * hu + x * hvi'

lemma one_le_finrank_quotient_smul_top (hI : I ≠ 0) :
    1 ≤ finrank (R ⧸ 𝔩) (I ⧸ 𝔩 • (⊤ : Submodule R I)) := by
  have : Nontrivial (I ⧸ 𝔩 • (⊤ : Submodule R I)) := by
    refine Quotient.nontrivial_iff.mpr fun h ↦ ?_
    rcases exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔩 ⊤ Finite.fg_top h.ge with
      ⟨r, hr1, hr⟩
    rcases exists_mem_ne_zero_of_ne_bot (coeToSubmodule_ne_bot.mpr hI) with ⟨y, hy, hy0⟩
    have hr0 : r = 0 := by
      have h0 : r • y = 0 := congrArg Subtype.val (hr ⟨y, hy⟩ mem_top)
      rw [Algebra.smul_def, mul_eq_zero, or_iff_left hy0] at h0
      exact IsFractionRing.injective R K (h0.trans (map_zero _).symm)
    rw [hr0, zero_sub, neg_mem_iff] at hr1
    exact ‹𝔩.IsMaximal›.ne_top (𝔩.eq_top_iff_one.mpr hr1)
  exact finrank_pos

lemma isUnit_of_forall_finrank_quotient_smul_top_le_one (hI : I ≠ 0)
    (h : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → finrank (R ⧸ 𝔪) (I ⧸ 𝔪 • (⊤ : Submodule R I)) ≤ 1) :
    IsUnit I := by
  rw [← mul_inv_cancel_iff_isUnit K]
  rcases le_one_iff_exists_coeIdeal.mp (mul_one_div_le_one (I := I)) with ⟨𝔞, h𝔞⟩
  rw [inv_eq, ← h𝔞, ← coeIdeal_top, coeIdeal_inj]
  by_contra h𝔞top
  rcases 𝔞.exists_le_maximal h𝔞top with ⟨𝔪, h𝔪, h𝔞𝔪⟩
  rcases finrank_le_one_iff.mp (h 𝔪 h𝔪) with ⟨v, hv⟩
  rcases (𝔪 • ⊤ : Submodule R I).mkQ_surjective v with ⟨x, rfl⟩
  have hle : (⊤ : Submodule R (I ⧸ R ∙ x)) ≤ 𝔪 • ⊤ := by
    rintro m -
    rcases (R ∙ x).mkQ_surjective m with ⟨y, rfl⟩
    rcases hv ((𝔪 • ⊤ : Submodule R I).mkQ y) with ⟨c, hc⟩
    rcases 𝔪.mkQ_surjective c with ⟨s, rfl⟩
    have hs : s • (𝔪 • ⊤ : Submodule R I).mkQ x = (𝔪 • ⊤ : Submodule R I).mkQ y :=
      (algebraMap_smul (R ⧸ 𝔪) s _).symm.trans hc
    rw [← map_smul, ← LinearMap.sub_mem_ker_iff, ker_mkQ, ← neg_mem_iff, neg_sub] at hs
    have hmem : (R ∙ x).mkQ (y - s • x) ∈ 𝔪 • (⊤ : Submodule R (I ⧸ R ∙ x)) := by
      rw [← (R ∙ x).range_mkQ, ← Submodule.map_top, ← map_smul'']
      exact mem_map_of_mem hs
    have hsx : (R ∙ x).mkQ (s • x) = 0 :=
      (Quotient.mk_eq_zero _).mpr <| smul_mem _ s <| mem_span_singleton_self x
    rwa [map_sub, hsx, sub_zero] at hmem
  rcases exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 ⊤ Finite.fg_top hle with
    ⟨r, hr1, hr⟩
  have hrx (y : K) (hy : y ∈ I) : ∃ t : R, t • (x : K) = r • y := by
    have hy' : (R ∙ x).mkQ (r • ⟨y, hy⟩) = 0 := (map_smul _ r _).trans (hr _ mem_top)
    rw [← LinearMap.mem_ker, ker_mkQ, mem_span_singleton] at hy'
    exact hy'.imp fun t ↦ congrArg Subtype.val
  have hr𝔪 : r ∉ 𝔪 := fun h ↦
    h𝔪.ne_top (𝔪.eq_top_iff_one.mpr (sub_sub_cancel r 1 ▸ sub_mem h hr1))
  have hx0 : (x : K) ≠ 0 := by
    intro hx
    rcases exists_mem_ne_zero_of_ne_bot (coeToSubmodule_ne_bot.mpr hI) with ⟨y, hy, hy0⟩
    rcases hrx y hy with ⟨t, h0⟩
    rw [hx, smul_zero, Algebra.smul_def, eq_comm, mul_eq_zero, or_iff_left hy0] at h0
    exact hr𝔪 (IsFractionRing.injective R K (h0.trans (map_zero _).symm) ▸ 𝔪.zero_mem)
  have hinv : algebraMap R K r * (x : K)⁻¹ ∈ 1 / I := by
    rw [← inv_eq, mem_inv_iff hI]
    intro y hy
    rcases hrx y hy with ⟨t, h0⟩
    rw [Algebra.smul_def, Algebra.smul_def] at h0
    refine (mem_one_iff R⁰).mpr ⟨t, ?_⟩
    field_simp
    linear_combination h0
  have hmem : algebraMap R K r ∈ (𝔞 : FractionalIdeal R⁰ K) := by
    rw [h𝔞]
    convert mul_mem_mul x.2 hinv using 1
    field_simp
  rcases (mem_coeIdeal R⁰).mp hmem with ⟨r', hr', hrr'⟩
  exact hr𝔪 (h𝔞𝔪 (IsFractionRing.injective R K hrr' ▸ hr'))

end FractionalIdeal

namespace Subalgebra

variable {K : Type*} [CommRing K] [Algebra ℚ K] (R : Subalgebra ℤ K)

/-- The **trace dual** `Rᵗ = {a ∈ K | Tr(aR) ⊆ ℤ}` of a subring `R` of a commutative `ℚ`-algebra
`K`, for the trace `Tr` of `K` over `ℚ`: the dual of `R` for the trace form, as an `R`-submodule of
`K`. For an order in a number field it is, by definition, Tau Ceti's
`TauCeti.GlobalNumberFields.NumberFieldOrder.traceDual`. -/
noncomputable def traceDual : Submodule R K where
  __ := (Algebra.traceForm ℚ K).dualSubmodule ((1 : Submodule R K).restrictScalars ℤ)
  smul_mem' c x hx a ha := by
    rw [Algebra.traceForm_apply, smul_mul_assoc, mul_comm, ← smul_mul_assoc, mul_comm]
    exact hx _ (Submodule.smul_mem _ c ha)

lemma mem_traceDual {x : K} :
    x ∈ R.traceDual ↔ ∀ y ∈ R, Algebra.trace ℚ K (x * y) ∈ (algebraMap ℤ ℚ).range := by
  refine ⟨fun h y hy ↦ mem_one.mp (h y (mem_one.mpr ⟨⟨y, hy⟩, rfl⟩)), fun h y hy ↦ ?_⟩
  rcases mem_one.mp hy with ⟨y, rfl⟩
  exact mem_one.mpr (h _ y.2)

variable (𝔩 : Ideal R)

/-- The **Cohen–Macaulay type of `R` at a maximal ideal `𝔩`**, for a subring `R` of a commutative
`ℚ`-algebra: the dimension of `Rᵗ / 𝔩Rᵗ` over the residue field `R / 𝔩`, for the trace dual `Rᵗ`.
For an order in an étale algebra over `ℚ` it is, by Nakayama's lemma, the minimal number of
generators of the localisation `Rᵗ_𝔩`, a canonical module of the local ring `R_𝔩`, so it is the
Cohen–Macaulay type of `R_𝔩`. -/
noncomputable def cohenMacaulayTypeAt : ℕ :=
  finrank (R ⧸ 𝔩) (R.traceDual ⧸ 𝔩 • (⊤ : Submodule R R.traceDual))

/-- The **Cohen–Macaulay type** (LMFDB `ag.cohen_macaulay_type`) of an order `R` in an étale algebra
`K` over `ℚ`, a finite product of number fields: the largest dimension of `Rᵗ / 𝔩Rᵗ` over `R / 𝔩`,
for `𝔩` running over the maximal ideals of `R` and `Rᵗ = {a ∈ K | Tr(aR) ⊆ ℤ}` the trace dual. The
LMFDB defines it as the minimal number of generators of a canonical module of `R`, which `Rᵗ` is,
and computes it by this formula; that minimal number must be read locally, as the largest of the
minimal numbers of generators of the localisations `Rᵗ_𝔩` (`Subalgebra.cohenMacaulayTypeAt`), since
a canonical module is only determined up to an invertible module, which need not be principal.
Canonical modules are not available, so the formula is the definition, here for any subring of a
commutative `ℚ`-algebra. For an order in an étale algebra the trace form is nondegenerate, so `Rᵗ`
is a finitely generated `R`-module and the supremum is attained; this is proved here for orders in
number fields (Tau Ceti's `TauCeti.GlobalNumberFields.NumberFieldOrder`). -/
noncomputable def cohenMacaulayType : ℕ :=
  ⨆ 𝔩 : MaximalSpectrum R, R.cohenMacaulayTypeAt 𝔩.asIdeal

end Subalgebra

namespace TauCeti.GlobalNumberFields.NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K] (O : NumberFieldOrder K) (𝔩 : Ideal O.toSubalgebra)

lemma traceDual_toSubalgebra : O.toSubalgebra.traceDual = O.traceDual :=
  rfl

lemma cohenMacaulayTypeAt_toSubalgebra : O.toSubalgebra.cohenMacaulayTypeAt 𝔩 = finrank
    (O.toSubalgebra ⧸ 𝔩) (O.traceDual ⧸ 𝔩 • (⊤ : Submodule O.toSubalgebra O.traceDual)) :=
  rfl

lemma isNoetherianRing_toSubalgebra : IsNoetherianRing O.toSubalgebra :=
  isNoetherian_of_tower ℤ inferInstance

attribute [local instance] isNoetherianRing_toSubalgebra finite_of_isNoetherianRing

lemma bddAbove_range_cohenMacaulayTypeAt :
    BddAbove (Set.range (O.toSubalgebra.cohenMacaulayTypeAt ∘ MaximalSpectrum.asIdeal)) := by
  rcases Finite.exists_fin (R := O.toSubalgebra) (M := O.traceDual) with ⟨n, f, hf⟩
  refine ⟨n, ?_⟩
  rintro - ⟨𝔩, rfl⟩
  have : 𝔩.asIdeal.IsMaximal := 𝔩.isMaximal
  rw [Function.comp_apply, cohenMacaulayTypeAt_toSubalgebra]
  refine (finrank_le_of_span_eq_top (v := (𝔩.asIdeal • ⊤ : Submodule O.toSubalgebra
    O.traceDual).mkQ ∘ f) ?_).trans_eq (Fintype.card_fin n)
  rw [← restrictScalars_eq_top_iff O.toSubalgebra, eq_top_iff]
  refine le_trans ?_ (span_le_restrictScalars O.toSubalgebra (O.toSubalgebra ⧸ 𝔩.asIdeal) _)
  rw [Set.range_comp, ← map_span, hf, Submodule.map_top, range_mkQ]

/-- **The Cohen–Macaulay type of an order in a number field bounds its local Cohen–Macaulay
types.** -/
lemma cohenMacaulayTypeAt_le_cohenMacaulayType [𝔩.IsMaximal] :
    O.toSubalgebra.cohenMacaulayTypeAt 𝔩 ≤ O.toSubalgebra.cohenMacaulayType :=
  le_ciSup O.bddAbove_range_cohenMacaulayTypeAt ⟨𝔩, ‹_›⟩

/-- **The Cohen–Macaulay type of an order in a number field is attained at some maximal ideal.** -/
lemma exists_cohenMacaulayTypeAt_eq_cohenMacaulayType : ∃ 𝔩 : MaximalSpectrum O.toSubalgebra,
    O.toSubalgebra.cohenMacaulayTypeAt 𝔩.asIdeal = O.toSubalgebra.cohenMacaulayType :=
  Nat.sSup_mem (Set.range_nonempty _) O.bddAbove_range_cohenMacaulayTypeAt

lemma one_le_cohenMacaulayTypeAt [𝔩.IsMaximal] : 1 ≤ O.toSubalgebra.cohenMacaulayTypeAt 𝔩 := by
  rw [cohenMacaulayTypeAt_toSubalgebra]
  exact one_le_finrank_quotient_smul_top 𝔩 O.traceDual_ne_zero

lemma one_le_cohenMacaulayType : 1 ≤ O.toSubalgebra.cohenMacaulayType := by
  rcases O.exists_cohenMacaulayTypeAt_eq_cohenMacaulayType with ⟨𝔩, h𝔩⟩
  have : 𝔩.asIdeal.IsMaximal := 𝔩.isMaximal
  exact h𝔩 ▸ O.one_le_cohenMacaulayTypeAt 𝔩.asIdeal

/-- **An order in a number field has Cohen–Macaulay type `1` if and only if it is Gorenstein**,
that is its trace dual is invertible. -/
lemma cohenMacaulayType_eq_one_iff_isGorenstein :
    O.toSubalgebra.cohenMacaulayType = 1 ↔ O.IsGorenstein := by
  refine ⟨fun h ↦ ⟨isUnit_of_forall_finrank_quotient_smul_top_le_one O.traceDual_ne_zero
    fun 𝔪 _ ↦ (O.cohenMacaulayTypeAt_toSubalgebra 𝔪).symm.trans_le
      (h ▸ O.cohenMacaulayTypeAt_le_cohenMacaulayType 𝔪)⟩, fun h ↦ ?_⟩
  refine le_antisymm (ciSup_le fun 𝔩 ↦ ?_) O.one_le_cohenMacaulayType
  have : 𝔩.asIdeal.IsMaximal := 𝔩.isMaximal
  rw [cohenMacaulayTypeAt_toSubalgebra]
  exact finrank_quotient_smul_top_le_one_of_isUnit 𝔩.asIdeal h.isUnit_traceDual

/-- **An order in a number field has Cohen–Macaulay type `1` if and only if its proper fractional
ideals are invertible**, the fractional ideals `I` with `(I : I) = R`. -/
lemma cohenMacaulayType_eq_one_iff_forall_isUnit :
    O.toSubalgebra.cohenMacaulayType = 1 ↔ ∀ I, O.IsProperFractionalIdeal I → IsUnit I :=
  O.cohenMacaulayType_eq_one_iff_isGorenstein.trans O.isGorenstein_iff_forall_isUnit

end TauCeti.GlobalNumberFields.NumberFieldOrder
