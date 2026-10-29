import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Galois module structure of the units of real biquadratic fields

A real biquadratic field `K` is a totally real Galois extension of `ℚ` whose Galois group is the
Klein four-group `V₄`. It has exactly three quadratic subfields `k₁, k₂, k₃`
(`NumberField.card_quadraticSubfield`), all real, and its units `U` have rank `3`
(`NumberField.Units.rank_eq_three`) and torsion `{±1}`
(`TauCeti.NumberField.Units.torsion_eq_one_or_neg_one_of_isReal`). Mazur and Ullom (Galois module
structure of units in real biquadratic number fields, Acta Arith. 111 (2004)) sort the
`ℤ[V₄]`-modules `U/{±1}` into four types I–IV, and their subtypes say which square roots of
products of fundamental units `e₁, e₂, e₃` of `k₁, k₂, k₃` generate `U/{±1}`. Every real
biquadratic field has exactly one of the seven subtypes, which are the possible positions of
`⟨e₁, e₂, e₃⟩` in `U/{±1}` (its index is `1`, `2` or `4`, never `8`); this is not proved here.

The predicates are stated for every number field `K`, but they are the LMFDB's types only for a
real biquadratic field, the setting of the knowls (whose `U/{±1}` has rank `3`): for an imaginary
biquadratic field, say, the units modulo torsion have rank `1` and the predicates mean something
else. We work in the units modulo torsion `(𝓞 K)ˣ ⧸ torsion K`, which is `U/{±1}` for a real
field, and read the knowls' square roots there: a square root of the class of `e` is the class of
a unit `u` with `u ^ 2 = ±e`. As fundamental units are only defined up to sign, for a real field
this is the same as a square root in `U` of suitably signed fundamental units. For type III the
three signs in `u ^ 2 = ±e₁e₂`, `v ^ 2 = ±e₂e₃` and `w ^ 2 = ±e₃e₁` can all be absorbed, as their
product `(uvw / e₁e₂e₃) ^ 2` is a square in the real field `K`, hence `1`.

## Main definitions

* `NumberField.Units.IsFundamentalUnit` (LMFDB `nf.fundamental_units`): a fundamental unit of a
  number field of unit rank one, such as a real quadratic field.
* `NumberField.Units.QuadraticUnitFrame`: a labelling `k₁, k₂, k₃` of the three quadratic subfields
  of `K` together with fundamental units `e₁, e₂, e₃` of them.
* `NumberField.Units.QuadraticUnitFrame.unitClass`: the class of `eᵢ` in `U/{±1}`.
* `NumberField.Units.IsMazurUllomTypeI₁` (LMFDB `nf.galois_group.gmodule_v4_type_i_i`),
  `NumberField.Units.IsMazurUllomTypeI₂` (LMFDB `nf.galois_group.gmodule_v4_type_i_ii`),
  `NumberField.Units.IsMazurUllomTypeI₃` (LMFDB `nf.galois_group.gmodule_v4_type_i_iii`),
  `NumberField.Units.IsMazurUllomTypeII₁` (LMFDB `nf.galois_group.gmodule_v4_type_ii_i`),
  `NumberField.Units.IsMazurUllomTypeII₂` (LMFDB `nf.galois_group.gmodule_v4_type_ii_ii`),
  `NumberField.Units.IsMazurUllomTypeIII` (LMFDB `nf.galois_group.gmodule_v4_type_iii`) and
  `NumberField.Units.IsMazurUllomTypeIV` (LMFDB `nf.galois_group.gmodule_v4_type_iv`): the
  subtypes of the unit group of a real biquadratic field.

## Main results

* `NumberField.card_quadraticSubfield`: a Galois extension of `ℚ` with Galois group `V₄` has exactly
  three quadratic subfields.
* `NumberField.Units.isFundamentalUnit_fundSystem`: in unit rank one, the unit of Mathlib's
  fundamental system `NumberField.Units.fundSystem` is a fundamental unit.
* `NumberField.Units.rank_eq_finrank_sub_one`: the units of a totally real field `K` have rank
  `[K : ℚ] - 1`.
* `NumberField.Units.rank_eq_three`: the units of a real biquadratic field have rank `3`.
* `NumberField.Units.nonempty_quadraticUnitFrame`: a real biquadratic field has frames of quadratic
  units, so that the types are conditions on fundamental units that exist.
-/

open Module IntermediateField

open scoped NumberField

lemma IsKleinFour.card_subgroup_card_eq_two (G : Type*) [Group G] [IsKleinFour G] :
    Nat.card {H : Subgroup G // Nat.card H = 2} = 3 := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  have hord (g : {g : G // g ≠ 1}) : orderOf g.1 = 2 :=
    orderOf_eq_prime ((sq g.1).trans (IsKleinFour.mul_self g.1)) g.2
  have hmem (g : {g : G // g ≠ 1}) (x : G) : x ∈ Subgroup.zpowers g.1 ↔ x = g.1 ∨ x = 1 := by
    rw [mem_zpowers_iff_mem_range_orderOf, hord g]
    simp [Finset.range_add_one]
  let f (g : {g : G // g ≠ 1}) : {H : Subgroup G // Nat.card H = 2} :=
    ⟨Subgroup.zpowers g.1, (Nat.card_zpowers g.1).trans (hord g)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun g g' h ↦ Subtype.ext ?_, fun H ↦ ?_⟩
    · have hzp : Subgroup.zpowers g.1 = Subgroup.zpowers g'.1 := congrArg Subtype.val h
      exact ((hmem g' g.1).mp (hzp ▸ Subgroup.mem_zpowers g.1)).resolve_right g.2
    · have : Nontrivial H.1 := Finite.one_lt_card_iff_nontrivial.mp (by rw [H.2]; exact one_lt_two)
      rcases exists_ne (1 : H.1) with ⟨g, hg⟩
      have hg1 : (g : G) ≠ 1 := fun h ↦ hg (Subtype.ext h)
      refine ⟨⟨g, hg1⟩, Subtype.ext ?_⟩
      exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr g.2)
        (H.2.trans ((Nat.card_zpowers (g : G)).trans (hord ⟨g, hg1⟩)).symm).le
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card]
  exact (Set.card_ne_eq (1 : G)).trans (by rw [IsKleinFour.card_four'])

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

variable [IsGalois ℚ K] [IsKleinFour Gal(K/ℚ)] in
lemma finrank_eq_four_of_isKleinFour : finrank ℚ K = 4 :=
  (IsGalois.card_aut_eq_finrank ℚ K).symm.trans IsKleinFour.card_four

variable [IsGalois ℚ K] [IsKleinFour Gal(K/ℚ)] in
/-- **A Galois extension `K` of `ℚ` with Galois group `V₄` has exactly three quadratic
subfields.** -/
lemma card_quadraticSubfield : Nat.card {k : IntermediateField ℚ K // finrank ℚ k = 2} = 3 := by
  rw [← IsKleinFour.card_subgroup_card_eq_two Gal(K/ℚ)]
  refine Nat.card_congr <| (Equiv.mk fixingSubgroup fixedField
    (fun k ↦ IsGalois.fixedField_fixingSubgroup k) fun H ↦ fixingSubgroup_fixedField H)
    |>.subtypeEquiv fun k ↦ ?_
  have hk : finrank ℚ k * finrank k K = 4 :=
    (finrank_mul_finrank ℚ k K).trans (finrank_eq_four_of_isKleinFour K)
  rw [Equiv.coe_fn_mk, IsGalois.card_fixingSubgroup_eq_finrank]
  constructor <;> intro h <;> rw [h] at hk <;> omega

namespace Units

variable {K} in
/-- A unit `ε` of a number field `K` of unit rank one, such as a real quadratic field, is a
**fundamental unit** (LMFDB `nf.fundamental_units`) if it generates the units of `𝓞 K` modulo
torsion: every unit is `ζ ε ^ n` for a root of unity `ζ` and an integer `n`. In general rank the
LMFDB's fundamental units are a basis of the units modulo torsion; this is the rank-one case. In
unit rank `0` every unit satisfies the predicate, and in unit rank at least `2` none does. -/
def IsFundamentalUnit (ε : (𝓞 K)ˣ) : Prop :=
  Subgroup.zpowers (ε : (𝓞 K)ˣ ⧸ torsion K) = ⊤

/-- **In unit rank one, the unit of Mathlib's fundamental system is a fundamental unit.** -/
lemma isFundamentalUnit_fundSystem (h : rank K = 1) :
    IsFundamentalUnit (fundSystem K ⟨0, by omega⟩) := by
  rw [IsFundamentalUnit, eq_top_iff]
  rintro x -
  induction x using QuotientGroup.induction_on with | H u => ?_
  rcases exist_unique_eq_mul_prod K u with ⟨⟨ζ, n⟩, hu, -⟩
  dsimp only at hu
  rw [Fintype.prod_eq_single ⟨0, by omega⟩ fun i hi ↦ absurd (Fin.ext (by omega)) hi, mul_comm]
    at hu
  refine Subgroup.mem_zpowers_iff.mpr ⟨n ⟨0, by omega⟩, ?_⟩
  rw [← QuotientGroup.mk_zpow, hu, QuotientGroup.mk_mul_of_mem _ ζ.2]

variable [IsTotallyReal K] in
/-- **The units of a totally real field `K` have rank `[K : ℚ] - 1`**, so `1` for a real quadratic
field. -/
lemma rank_eq_finrank_sub_one : rank K = finrank ℚ K - 1 := by
  rw [rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, IsTotallyReal.finrank]

variable [IsGalois ℚ K] [IsKleinFour Gal(K/ℚ)] [IsTotallyReal K] in
/-- **The units of a real biquadratic field have rank `3`.** -/
lemma rank_eq_three : rank K = 3 := by
  rw [rank_eq_finrank_sub_one, finrank_eq_four_of_isKleinFour]

/-- A **frame of quadratic units** of `K`: a labelling `k₁, k₂, k₃` of the quadratic subfields of
`K`, together with a fundamental unit `eᵢ` of each `kᵢ`. A frame exists exactly when `K` has three
quadratic subfields, all with fundamental units, as a real biquadratic field has
(`nonempty_quadraticUnitFrame`). The indices `0, 1, 2` stand for `1, 2, 3`. -/
structure QuadraticUnitFrame where
  /-- The labelling `i ↦ kᵢ` of the quadratic subfields of `K`. -/
  subfield : Fin 3 ≃ {k : IntermediateField ℚ K // finrank ℚ k = 2}
  /-- The fundamental unit `eᵢ` of `kᵢ`. -/
  unit (i : Fin 3) : (𝓞 (subfield i).1)ˣ
  isFundamentalUnit_unit (i : Fin 3) : IsFundamentalUnit (unit i)

variable [IsGalois ℚ K] [IsKleinFour Gal(K/ℚ)] [IsTotallyReal K] in
/-- **A real biquadratic field has a frame of quadratic units**: its three quadratic subfields are
real, so of unit rank one, and Mathlib's fundamental systems give fundamental units of them. -/
lemma nonempty_quadraticUnitFrame : Nonempty (QuadraticUnitFrame K) := by
  have : Finite {k : IntermediateField ℚ K // finrank ℚ k = 2} :=
    Nat.finite_of_card_ne_zero (by rw [card_quadraticSubfield]; norm_num)
  let e : Fin 3 ≃ {k : IntermediateField ℚ K // finrank ℚ k = 2} :=
    (Finite.equivFinOfCardEq (card_quadraticSubfield K)).symm
  have he (i : Fin 3) : rank (e i).1 = 1 := by
    rw [rank_eq_finrank_sub_one, (e i).2]
  exact ⟨⟨e, fun i ↦ fundSystem (e i).1 ⟨0, by rw [he i]; exact one_pos⟩,
    fun i ↦ isFundamentalUnit_fundSystem _ (he i)⟩⟩

namespace QuadraticUnitFrame

variable {K} (f : QuadraticUnitFrame K)

/-- The class `ēᵢ` in the units modulo torsion `(𝓞 K)ˣ ⧸ torsion K`, which is `U/{±1}` for a real
field `K`, of the fundamental unit `eᵢ` of the quadratic subfield `kᵢ` of `K`. -/
def unitClass (i : Fin 3) : (𝓞 K)ˣ ⧸ torsion K :=
  Units.map (algebraMap (𝓞 (f.subfield i).1) (𝓞 K)).toMonoidHom (f.unit i)

end QuadraticUnitFrame

/-- The units `U` of a real biquadratic field `K` have **type I (i)** in the notation of Mazur and
Ullom (LMFDB `nf.galois_group.gmodule_v4_type_i_i`): `U/{±1}` is generated by fundamental units
`e₁, e₂, e₃` of the three quadratic subfields of `K`. Only meaningful for real biquadratic `K`,
where `(𝓞 K)ˣ ⧸ torsion K` is `U/{±1}`. -/
def IsMazurUllomTypeI₁ : Prop :=
  ∃ f : QuadraticUnitFrame K, Subgroup.closure {f.unitClass 0, f.unitClass 1, f.unitClass 2} = ⊤

/-- The units `U` of a real biquadratic field `K` have **type I (ii)** in the notation of Mazur and
Ullom (LMFDB `nf.galois_group.gmodule_v4_type_i_ii`): for some fundamental units `e₁, e₂, e₃` of
the three quadratic subfields of `K`, the classes `√e₁, e₂, e₃` generate `U/{±1}`. Only
meaningful for real biquadratic `K`, where `(𝓞 K)ˣ ⧸ torsion K` is `U/{±1}`. -/
def IsMazurUllomTypeI₂ : Prop :=
  ∃ (f : QuadraticUnitFrame K) (x : (𝓞 K)ˣ ⧸ torsion K), x ^ 2 = f.unitClass 0 ∧
    Subgroup.closure {x, f.unitClass 1, f.unitClass 2} = ⊤

/-- The units `U` of a real biquadratic field `K` have **type I (iii)** in the notation of Mazur and
Ullom (LMFDB `nf.galois_group.gmodule_v4_type_i_iii`): for some fundamental units `e₁, e₂, e₃` of
the three quadratic subfields of `K`, the classes `√e₁, √e₂, e₃` generate `U/{±1}`. Only
meaningful for real biquadratic `K`, where `(𝓞 K)ˣ ⧸ torsion K` is `U/{±1}`. -/
def IsMazurUllomTypeI₃ : Prop :=
  ∃ (f : QuadraticUnitFrame K) (x y : (𝓞 K)ˣ ⧸ torsion K), x ^ 2 = f.unitClass 0 ∧
    y ^ 2 = f.unitClass 1 ∧ Subgroup.closure {x, y, f.unitClass 2} = ⊤

/-- The units `U` of a real biquadratic field `K` have **type II (i)** in the notation of Mazur and
Ullom (LMFDB `nf.galois_group.gmodule_v4_type_ii_i`): for some fundamental units `e₁, e₂, e₃` of
the three quadratic subfields of `K`, the classes `√(e₁e₂), e₂, e₃` generate `U/{±1}`. Only
meaningful for real biquadratic `K`, where `(𝓞 K)ˣ ⧸ torsion K` is `U/{±1}`. -/
def IsMazurUllomTypeII₁ : Prop :=
  ∃ (f : QuadraticUnitFrame K) (x : (𝓞 K)ˣ ⧸ torsion K), x ^ 2 = f.unitClass 0 * f.unitClass 1 ∧
    Subgroup.closure {x, f.unitClass 1, f.unitClass 2} = ⊤

/-- The units `U` of a real biquadratic field `K` have **type II (ii)** in the notation of Mazur
and Ullom (LMFDB `nf.galois_group.gmodule_v4_type_ii_ii`): for some fundamental units `e₁, e₂, e₃`
of the three quadratic subfields of `K`, the classes `√(e₁e₂), e₂, √e₃` generate `U/{±1}`. Only
meaningful for real biquadratic `K`, where `(𝓞 K)ˣ ⧸ torsion K` is `U/{±1}`. -/
def IsMazurUllomTypeII₂ : Prop :=
  ∃ (f : QuadraticUnitFrame K) (x y : (𝓞 K)ˣ ⧸ torsion K), x ^ 2 = f.unitClass 0 * f.unitClass 1 ∧
    y ^ 2 = f.unitClass 2 ∧ Subgroup.closure {x, f.unitClass 1, y} = ⊤

/-- The units `U` of a real biquadratic field `K` have **type III** in the notation of Mazur and
Ullom (LMFDB `nf.galois_group.gmodule_v4_type_iii`): for some fundamental units `e₁, e₂, e₃` of the
three quadratic subfields of `K`, the classes `√(e₁e₂), √(e₂e₃), √(e₃e₁)` generate `U/{±1}`.
Only meaningful for real biquadratic `K`, where `(𝓞 K)ˣ ⧸ torsion K` is `U/{±1}`. -/
def IsMazurUllomTypeIII : Prop :=
  ∃ (f : QuadraticUnitFrame K) (x y z : (𝓞 K)ˣ ⧸ torsion K),
    x ^ 2 = f.unitClass 0 * f.unitClass 1 ∧ y ^ 2 = f.unitClass 1 * f.unitClass 2 ∧
      z ^ 2 = f.unitClass 2 * f.unitClass 0 ∧ Subgroup.closure {x, y, z} = ⊤

/-- The units `U` of a real biquadratic field `K` have **type IV** in the notation of Mazur and
Ullom (LMFDB `nf.galois_group.gmodule_v4_type_iv`): for some fundamental units `e₁, e₂, e₃` of the
three quadratic subfields of `K`, the classes `√(e₁e₂e₃), e₂, e₃` generate `U/{±1}`. Only
meaningful for real biquadratic `K`, where `(𝓞 K)ˣ ⧸ torsion K` is `U/{±1}`. -/
def IsMazurUllomTypeIV : Prop :=
  ∃ (f : QuadraticUnitFrame K) (x : (𝓞 K)ˣ ⧸ torsion K),
    x ^ 2 = f.unitClass 0 * f.unitClass 1 * f.unitClass 2 ∧
      Subgroup.closure {x, f.unitClass 1, f.unitClass 2} = ⊤

end Units

end NumberField
