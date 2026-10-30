import LeanBridge.ForMathlib.FieldTheory.AlgebraGaloisClosure
import LeanBridge.ForMathlib.NumberTheory.NumberField.Polredabs
import TauCeti.FieldTheory.GaloisGroups.Label
import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Classification

/-!
# Minimal siblings of number fields

The minimal sibling of a number field `K` (LMFDB `nf.minimal_sibling`) is, among `K` and its
siblings (`Algebra.IsSibling`), that is among the number fields whose Galois closure is isomorphic
to that of `K`, the one that is least for the lexicographic order on

* its degree `n`,
* the T-number of its Galois group,
* the absolute value of its discriminant,
* the vector `(a₀, a₁, …, a_{n-1})` of coefficients of its normalised defining polynomial
  `xⁿ + a_{n-1} xⁿ⁻¹ + ⋯ + a₀` (LeanBridge's `NumberField.polredabs`).

A field can be its own minimal sibling: the LMFDB records whether a field "is its own minimal
sibling" (LMFDB `columns.nf_fields.is_minimal_sibling`), so `K` itself is among the candidates.

The T-number (LMFDB `gg.tnumber`) of a transitive subgroup of `S_n` is its position in the
classification of the transitive groups of degree `n` up to conjugacy, ordered weakly increasingly
by order, as in GAP's library (Butler–McKay). The candidates have isomorphic Galois closures, so
their Galois groups have the same order, and the T-numbers compared are those of transitive groups
of the same degree and the same order: they are compared by the order in which GAP's library lists
the groups of the same order, a convention of that library and not mathematics, which is not
formalised. It enters as a parameter, a numbering `t : NumberField.TNumbering` of the subgroups of
the symmetric groups that is invariant under conjugation and agrees with Tau Ceti's
transitive-group labels `nTj` (`TauCeti.TransitiveGroupLabel`, `TauCeti.HasGaloisLabel`) in
degrees at most five, where they are defined. As every transitive group of degree at most five has
such a label (Tau Ceti's classification), the T-numbers of the candidates of degree at most five
are those of the LMFDB for every numbering
(`NumberField.TNumbering.galoisNum_eq_of_hasGaloisLabel`). With the T-numbers of GAP, the
definition is that of the LMFDB. A numbering exists
(`NumberField.TNumbering.ofTransitiveGroupLabel`), and for every numbering, a minimal sibling
exists (`NumberField.exists_isMinimalSibling`) and is unique up to isomorphism
(`NumberField.IsMinimalSibling.nonempty_algEquiv`), the last key, the normalised defining
polynomial, determining the field.

## Main definitions

* `NumberField.TNumbering` (LMFDB `gg.tnumber`): numberings of the subgroups of the symmetric
  groups, invariant under conjugation and extending Tau Ceti's labels.
* `NumberField.TNumbering.ofTransitiveGroupLabel`: the numbering by Tau Ceti's labels.
* `NumberField.TNumbering.galoisNum`: the number of the Galois group of a polynomial.
* `NumberField.siblingKey` (LMFDB `nf.minimal_sibling`): the key compared to find the minimal
  sibling.
* `NumberField.IsMinimalSibling` (LMFDB `nf.minimal_sibling`): minimal siblings.
* `NumberField.IsMinimalSiblingPolynomial` (LMFDB `nf.minimal_sibling`): the normalised defining
  polynomial of the minimal sibling.

## Main results

* `Algebra.galoisClosure_eq_of_nonempty_algEquiv`: isomorphic Galois closures inside
  `AlgebraicClosure F` are equal.
* `NumberField.TNumbering.galoisNum_eq_of_hasGaloisLabel`: in degrees at most five, the number of
  the Galois group of a polynomial with the Tau Ceti label `nTj` is `j`.
* `NumberField.siblingKey_eq_of_ringEquiv`: the key is an isomorphism invariant.
* `NumberField.nonempty_algEquiv_galoisClosure_iff`: the candidates are `K` and its siblings.
* `NumberField.exists_isMinimalSibling`: every number field has a minimal sibling.
* `NumberField.IsMinimalSibling.nonempty_algEquiv`: the minimal sibling is unique up to
  isomorphism.
* `NumberField.IsMinimalSibling.isSibling_or_nonempty_algEquiv`: the minimal sibling is a sibling
  of `K` or `K` itself.
* `NumberField.exists_isMinimalSiblingPolynomial` and `NumberField.IsMinimalSiblingPolynomial.eq`:
  the normalised defining polynomial of the minimal sibling exists and is unique.
-/

open Module Polynomial TauCeti

open Algebra (galoisClosure IsSibling)

namespace Algebra

variable {F A B K₁ K₂ : Type*} [Field F] [CommRing A] [Algebra F A] [CommRing B] [Algebra F B]
  [Field K₁] [Algebra F K₁] [Field K₂] [Algebra F K₂]

lemma galoisClosure_eq_of_algEquiv (e : A ≃ₐ[F] B) : galoisClosure F A = galoisClosure F B := by
  refine congrArg (IntermediateField.adjoin F) (Set.ext fun x ↦ ?_)
  simp only [Set.mem_iUnion]
  exact ⟨fun ⟨f, y, hy⟩ ↦ ⟨f.comp e.symm.toAlgHom, e y, by simpa using hy⟩,
    fun ⟨f, y, hy⟩ ↦ ⟨f.comp e.toAlgHom, e.symm y, by simpa using hy⟩⟩

lemma fieldRange_le_galoisClosure (φ : K₁ →ₐ[F] AlgebraicClosure F) :
    φ.fieldRange ≤ galoisClosure F K₁ :=
  fun _ ⟨y, hy⟩ ↦ IntermediateField.subset_adjoin F _ (Set.mem_iUnion.mpr ⟨φ, y, hy⟩)

/-- **Isomorphic Galois closures are equal**: the Galois closures of algebraic extensions inside
`AlgebraicClosure F` are normal, and an isomorphism between normal subextensions of
`AlgebraicClosure F` maps one onto the other. -/
lemma galoisClosure_eq_of_nonempty_algEquiv [Algebra.IsAlgebraic F K₁]
    (h : Nonempty (galoisClosure F K₁ ≃ₐ[F] galoisClosure F K₂)) :
    galoisClosure F K₁ = galoisClosure F K₂ := by
  rcases h with ⟨e⟩
  have : Normal F (galoisClosure F K₁) := (isNormalClosure_galoisClosure K₁).normal
  rw [← AlgHom.fieldRange_of_normal ((galoisClosure F K₂).val.comp e.toAlgHom)]
  ext x
  exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ (e y).2, fun hx ↦ ⟨e.symm ⟨x, hx⟩, by simp⟩⟩

end Algebra

namespace NumberField

/-- A **numbering of transitive groups** (LMFDB `gg.tnumber`): a function `num n` on the subgroups
of the symmetric group `S_n`, constant on conjugacy classes, that gives the number `j` to the
subgroups with Tau Ceti's transitive-group label `nTj` (`TauCeti.TransitiveGroupLabel`, whose
index `j - 1` counts from `0`), defined in degrees at most five. The LMFDB uses the T-numbers of the
classification of transitive groups in GAP's library, which sorts the transitive groups of each
degree up to `47` weakly increasingly by order, and the groups of the same order in an order of the
library, a database convention not formalised here; they form such a numbering. A numbering exists
(`TNumbering.ofTransitiveGroupLabel`). -/
structure TNumbering where
  /-- The number of a subgroup of `S_n`, its T-number for a transitive subgroup. -/
  num (n : ℕ) : Subgroup (Equiv.Perm (Fin n)) → ℕ
  num_map_conj (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))) (τ : Equiv.Perm (Fin n)) :
    num n (G.map (MulAut.conj τ)) = num n G
  num_eq_of_transitiveGroupLabel {n : ℕ} {j : TransitiveGroupIndex n}
    {G : Subgroup (Equiv.Perm (Fin n))} : TransitiveGroupLabel j G → num n G = (j : ℕ) + 1

private lemma transitiveGroupLabel_eq {n : ℕ} {j k : TransitiveGroupIndex n}
    {G : Subgroup (Equiv.Perm (Fin n))} (hj : TransitiveGroupLabel j G)
    (hk : TransitiveGroupLabel k G) : j = k := by
  rcases n with _ | _ | _ | _ | _ | _ | n
  case zero | succ.succ.succ.succ.succ.succ => exact j.elim0
  case succ.zero | succ.succ.zero =>
    exact Fin.ext <| (Nat.lt_one_iff.mp j.isLt).trans (Nat.lt_one_iff.mp k.isLt).symm
  · exact hj.eq_of_three hk
  · exact hj.eq_of_four hk
  · exact hj.eq_of_five hk

open scoped Classical in
/-- The **numbering of transitive groups by Tau Ceti's labels**: a subgroup of `S_n` with the
transitive-group label `nTj` gets the number `j`, and the other subgroups the number `0`. Labels are
unique where they are defined, by Tau Ceti's classification of the transitive groups of degree at
most five, and invariant under conjugation, so this is a numbering. -/
noncomputable def TNumbering.ofTransitiveGroupLabel : TNumbering where
  num n G :=
    if h : ∃ j : TransitiveGroupIndex n, TransitiveGroupLabel j G then (h.choose : ℕ) + 1 else 0
  num_map_conj n G τ := by
    simp only [transitiveGroupLabel_map_conj_iff]
  num_eq_of_transitiveGroupLabel {n j G} h := by
    have h' : ∃ j : TransitiveGroupIndex n, TransitiveGroupLabel j G := ⟨j, h⟩
    rw [dite_eq_left h', transitiveGroupLabel_eq h'.choose_spec h]

namespace TNumbering

variable (t : TNumbering)

lemma num_map_permCongrHom {X : Type*} (G : Subgroup (Equiv.Perm X)) {m m' : ℕ} (e : X ≃ Fin m)
    (e' : X ≃ Fin m') :
    t.num m (G.map e.permCongrHom.toMonoidHom) = t.num m' (G.map e'.permCongrHom.toMonoidHom) := by
  have h : m = m' := by
    simpa using Fintype.card_congr (e.symm.trans e')
  subst h
  rw [Equiv.map_permCongrHom_eq_map_conj e e' G, t.num_map_conj]

/-- The **number of the Galois group** of a polynomial `f` over `ℚ` for a numbering `t` (LMFDB
`gg.tnumber`, `nf.minimal_sibling`): the number of the image of the Galois group of `f` in the
permutations of the roots of `f` in its splitting field, numbered by `Fin m` for their number `m`,
which is the degree of `f` when `f` is separable. It does not depend on the numbering of the roots
(`num_map_permCongrHom`), and for the T-numbers of GAP it is the T-number of the Galois group of
`f`. -/
noncomputable def galoisNum (f : ℚ[X]) : ℕ :=
  haveI : Fact ((f.map (algebraMap ℚ f.SplittingField)).Splits) := ⟨SplittingField.splits f⟩
  t.num _ ((Gal.galActionHom f f.SplittingField).range.map
    (Fintype.equivFin (f.rootSet f.SplittingField)).permCongrHom.toMonoidHom)

/-- **The number of a Galois group with a Tau Ceti label `nTj` is `j`**, whatever the numbering:
in degrees at most five, numberings agree with the T-numbers. -/
lemma galoisNum_eq_of_hasGaloisLabel {f : ℚ[X]} {n : ℕ} {j : TransitiveGroupIndex n}
    (h : HasGaloisLabel f j) : t.galoisNum f = (j : ℕ) + 1 := by
  rcases h with ⟨-, -, e, he⟩
  rw [galoisNum, t.num_map_permCongrHom _ _ e, t.num_eq_of_transitiveGroupLabel he]

end TNumbering

variable (t : TNumbering) {K F F' : Type*} [Field K] [NumberField K] [Field F] [NumberField F]
  [Field F'] [NumberField F'] {P Q : ℤ[X]}

variable (F) in
/-- The **key** (LMFDB `nf.minimal_sibling`) of a number field `F` of degree `n` for a numbering `t`
of transitive groups, whose least value among `K` and its siblings singles out the minimal sibling
of `K`: its degree `n`, the number (`TNumbering.galoisNum`) of the Galois group of its normalised
defining polynomial `xⁿ + a_{n-1} xⁿ⁻¹ + ⋯ + a₀` (`polredabs`), the absolute value of its
discriminant, and the vector `(a₀, a₁, …, a_{n-1})`, ordered lexicographically. For the T-numbers
of GAP, the second entry is the T-number of the Galois group of `F`. -/
noncomputable def siblingKey : Lex (ℕ × Lex (ℕ × Lex (ℕ × List ℤ))) :=
  toLex (finrank ℚ F, toLex (t.galoisNum ((polredabs F).map (Int.castRingHom ℚ)),
    toLex ((discr F).natAbs, (List.range (finrank ℚ F)).map (polredabs F).coeff)))

variable (K F) in
/-- `F` is a **minimal sibling** of a number field `K` (LMFDB `nf.minimal_sibling`) for a numbering
`t` of transitive groups: the Galois closures of `F` and `K` are isomorphic, that is, `F` is `K`
itself or a sibling of `K` up to isomorphism (`nonempty_algEquiv_galoisClosure_iff`), and the key
(`siblingKey`) of `F` is the least among such fields: its degree, then the T-number of its Galois
group, then its absolute discriminant, then the coefficients of its normalised defining polynomial
are minimal. The competitors are taken in `Type`, where every number field has an isomorphic copy
(`IsMinimalSibling.siblingKey_le` compares with fields in any universe). With the T-numbers of
GAP, a database convention not formalised here, this is the LMFDB's minimal sibling. It exists
(`exists_isMinimalSibling`) and is unique up to isomorphism (`IsMinimalSibling.nonempty_algEquiv`).
-/
def IsMinimalSibling : Prop :=
  Nonempty (galoisClosure ℚ F ≃ₐ[ℚ] galoisClosure ℚ K) ∧ ∀ (F' : Type) [Field F'] [NumberField F'],
    Nonempty (galoisClosure ℚ F' ≃ₐ[ℚ] galoisClosure ℚ K) → siblingKey t F ≤ siblingKey t F'

variable (K P) in
/-- `P` is the **normalised defining polynomial of the minimal sibling** of a number field `K`
(LMFDB `nf.minimal_sibling`, whose database stores the minimal sibling by it) for a numbering `t`
of transitive groups: the reduced defining polynomial (`polredabs`) of a minimal sibling of `K`. It
exists (`exists_isMinimalSiblingPolynomial`) and is unique (`IsMinimalSiblingPolynomial.eq`). -/
def IsMinimalSiblingPolynomial : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : NumberField F), IsMinimalSibling t K F ∧ polredabs F = P

lemma isDefiningPolynomial_iff_of_ringEquiv (e : F ≃+* F') :
    IsDefiningPolynomial F P ↔ IsDefiningPolynomial F' P :=
  and_congr_right' ⟨fun ⟨f⟩ ↦ ⟨f.trans e.toRatAlgEquiv⟩, fun ⟨f⟩ ↦ ⟨f.trans e.symm.toRatAlgEquiv⟩⟩

lemma polredabs_eq_of_ringEquiv (e : F ≃+* F') : polredabs F = polredabs F' := by
  have h : IsPolredabs F' (polredabs F) := by
    simpa only [IsPolredabs, isDefiningPolynomial_iff_of_ringEquiv e] using isPolredabs_polredabs F
  exact h.eq (isPolredabs_polredabs F')

/-- **The key of a number field is an isomorphism invariant**, as its degree, its normalised
defining polynomial and its discriminant are. -/
lemma siblingKey_eq_of_ringEquiv (e : F ≃+* F') : siblingKey t F = siblingKey t F' := by
  rw [siblingKey, siblingKey, e.toRatAlgEquiv.toLinearEquiv.finrank_eq,
    polredabs_eq_of_ringEquiv e, discr_eq_discr_of_algEquiv F e.toRatAlgEquiv]

lemma nonempty_algEquiv_of_polredabs_eq (h : polredabs F = polredabs F') :
    Nonempty (F ≃ₐ[ℚ] F') := by
  rcases (isPolredabs_polredabs F).1.2 with ⟨e⟩
  rcases (isPolredabs_polredabs F').1.2 with ⟨e'⟩
  rw [h] at e
  exact ⟨e.symm.trans e'⟩

/-- **The candidates for the minimal sibling of `K` are `K` and its siblings**: a number field has
a Galois closure isomorphic to that of `K` exactly when it is a sibling of `K` or isomorphic to
`K`. -/
lemma nonempty_algEquiv_galoisClosure_iff : Nonempty (galoisClosure ℚ F ≃ₐ[ℚ] galoisClosure ℚ K) ↔
    IsSibling ℚ K F ∨ Nonempty (K ≃ₐ[ℚ] F) := by
  refine ⟨fun h ↦ (isEmpty_or_nonempty (K ≃ₐ[ℚ] F)).imp (fun h' ↦ ⟨h', h.map AlgEquiv.symm⟩) id,
    fun h ↦ h.elim (fun h' ↦ h'.2.map AlgEquiv.symm) fun ⟨e⟩ ↦ ?_⟩
  exact ⟨IntermediateField.equivOfEq (Algebra.galoisClosure_eq_of_algEquiv e).symm⟩

lemma exists_ringEquiv_intermediateField (h : galoisClosure ℚ F = galoisClosure ℚ K) :
    ∃ E : IntermediateField ℚ (galoisClosure ℚ K), Nonempty (F ≃+* E) := by
  let φ : F →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  have hle : φ.fieldRange ≤ galoisClosure ℚ K := h ▸ Algebra.fieldRange_le_galoisClosure φ
  exact ⟨IntermediateField.restrict hle,
    ⟨(φ.equivFieldRange.trans (IntermediateField.inclusion hle).equivFieldRange).toRingEquiv⟩⟩

variable (K) in
/-- **Every number field has a minimal sibling**, for every numbering of transitive groups: the
number fields whose Galois closure is isomorphic to that of `K` embed into this Galois closure
`L`, a finite extension of `ℚ` with finitely many subfields, so their keys take finitely many
values, and the subfield of `L` of least key is a minimal sibling. -/
lemma exists_isMinimalSibling :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F), IsMinimalSibling t K F := by
  have : NumberField (galoisClosure ℚ K) := { to_finiteDimensional := inferInstance }
  have : Finite (IntermediateField ℚ (galoisClosure ℚ K)) :=
    Field.finite_intermediateField_of_exists_primitive_element ℚ _
      (Field.exists_primitive_element ℚ _)
  rcases exists_ringEquiv_intermediateField (F := K) rfl with ⟨E₀, ⟨e₀⟩⟩
  rcases Set.exists_min_image {E : IntermediateField ℚ (galoisClosure ℚ K) |
      galoisClosure ℚ E = galoisClosure ℚ K} (fun E ↦ siblingKey t E) (Set.toFinite _)
      ⟨E₀, (Algebra.galoisClosure_eq_of_algEquiv e₀.toRatAlgEquiv).symm⟩ with ⟨E, hE, hmin⟩
  refine ⟨E, inferInstance, inferInstance, ⟨IntermediateField.equivOfEq hE⟩, fun F' _ _ hF' ↦ ?_⟩
  have hF'' : galoisClosure ℚ F' = galoisClosure ℚ K :=
    Algebra.galoisClosure_eq_of_nonempty_algEquiv hF'
  rcases exists_ringEquiv_intermediateField hF'' with ⟨E', ⟨e'⟩⟩
  rw [siblingKey_eq_of_ringEquiv t e']
  exact hmin E' ((Algebra.galoisClosure_eq_of_algEquiv e'.toRatAlgEquiv).symm.trans hF'')

variable (K) in
/-- **The normalised defining polynomial of the minimal sibling exists.** -/
lemma exists_isMinimalSiblingPolynomial : ∃ P, IsMinimalSiblingPolynomial t K P := by
  rcases exists_isMinimalSibling t K with ⟨F, _, _, h⟩
  exact ⟨polredabs F, F, inferInstance, inferInstance, h, rfl⟩

variable {t}

lemma polredabs_eq_of_siblingKey_eq (h : siblingKey t F = siblingKey t F') :
    polredabs F = polredabs F' := by
  simp only [siblingKey, toLex_inj, Prod.mk.injEq] at h
  rcases h with ⟨h₁, -, -, h₂⟩
  rw [← h₁, List.map_inj_left] at h₂
  have hP : (polredabs F).natDegree = finrank ℚ F := (isPolredabs_polredabs F).1.natDegree_eq
  have hQ : (polredabs F').natDegree = finrank ℚ F :=
    h₁ ▸ (isPolredabs_polredabs F').1.natDegree_eq
  ext i
  rcases lt_trichotomy i (finrank ℚ F) with hi | rfl | hi
  · exact h₂ i (List.mem_range.mpr hi)
  · rw [← hP, (isPolredabs_polredabs F).1.1.coeff_natDegree, hP, ← hQ,
      (isPolredabs_polredabs F').1.1.coeff_natDegree]
  · rw [coeff_eq_zero_of_natDegree_lt (hP ▸ hi), coeff_eq_zero_of_natDegree_lt (hQ ▸ hi)]

lemma IsMinimalSibling.siblingKey_le (h : IsMinimalSibling t K F)
    (hF' : Nonempty (galoisClosure ℚ F' ≃ₐ[ℚ] galoisClosure ℚ K)) :
    siblingKey t F ≤ siblingKey t F' := by
  let φ : F' →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  have : NumberField φ.fieldRange :=
    { to_finiteDimensional := φ.equivFieldRange.toLinearEquiv.finiteDimensional }
  have hE : galoisClosure ℚ F' = galoisClosure ℚ φ.fieldRange :=
    Algebra.galoisClosure_eq_of_algEquiv φ.equivFieldRange
  rw [siblingKey_eq_of_ringEquiv t φ.equivFieldRange.toRingEquiv]
  exact h.2 _ <| hF'.map (IntermediateField.equivOfEq hE).symm.trans

lemma IsMinimalSibling.polredabs_eq (h : IsMinimalSibling t K F) (h' : IsMinimalSibling t K F') :
    polredabs F = polredabs F' :=
  polredabs_eq_of_siblingKey_eq <| (h.siblingKey_le h'.1).antisymm (h'.siblingKey_le h.1)

/-- **The minimal sibling is unique up to isomorphism**: two minimal siblings have the same key,
hence the same normalised defining polynomial. -/
lemma IsMinimalSibling.nonempty_algEquiv (h : IsMinimalSibling t K F)
    (h' : IsMinimalSibling t K F') : Nonempty (F ≃ₐ[ℚ] F') :=
  nonempty_algEquiv_of_polredabs_eq (h.polredabs_eq h')

/-- **The minimal sibling of `K` is a sibling of `K`, or `K` itself.** -/
lemma IsMinimalSibling.isSibling_or_nonempty_algEquiv (h : IsMinimalSibling t K F) :
    IsSibling ℚ K F ∨ Nonempty (K ≃ₐ[ℚ] F) :=
  nonempty_algEquiv_galoisClosure_iff.mp h.1

/-- **The normalised defining polynomial of the minimal sibling is unique.** -/
lemma IsMinimalSiblingPolynomial.eq (hP : IsMinimalSiblingPolynomial t K P)
    (hQ : IsMinimalSiblingPolynomial t K Q) : P = Q := by
  rcases hP with ⟨F, _, _, hF, rfl⟩
  rcases hQ with ⟨F', _, _, hF', rfl⟩
  exact hF.polredabs_eq hF'

end NumberField
