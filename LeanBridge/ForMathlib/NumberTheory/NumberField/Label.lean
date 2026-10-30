import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# The label of a number field

The LMFDB label of a number field `K` has the form `d.r.D.i` (LMFDB `nf.label`), where `d` is the
degree of `K`, `r` its number of real places (its real signature; the signature of `K` is then
`[r, (d - r) / 2]`), `D` the absolute value of its discriminant, and `i` an index, counting from
`1`, that tells apart the fields with the same degree, signature and absolute discriminant, such
as `4.0.1008.1` and `4.0.1008.2`.

The prefix `d.r.D` is a function of `K`, invariant under isomorphism, and it determines the three
invariants. By Hermite's theorem (`NumberField.finite_of_discr_bdd`) only finitely many number
fields share it, so they can be numbered. The index `i` is that numbering, which the knowl does not
specify: it is a database convention, not mathematics, and is not formalised. Neither is the
optional factored form `a₁ e ε₁ _ ⋯ _ aₖ e εₖ` of the part `D`, a display convention for
`D = a₁ ^ ε₁ ⋯ aₖ ^ εₖ`; here `D` is written in decimal.

## Main definitions

* `NumberField.labelPrefix` (LMFDB `nf.label`): the prefix `d.r.D` of the label of a number field.

## Main results

* `NumberField.nrComplexPlaces_eq_finrank_sub_nrRealPlaces_div_two`: the signature is
  `[r, (d - r) / 2]`.
* `NumberField.labelPrefix_eq_iff`: the prefix determines the degree, the number of real places
  and the absolute discriminant.
* `NumberField.labelPrefix_eq_of_algEquiv`: isomorphic number fields have the same prefix.
* `NumberField.finite_setOf_labelPrefix_eq`: finitely many number fields have a given prefix.
* `NumberField.labelPrefix_rat`: the prefix of `ℚ` is `1.1.1`, as in its label `1.1.1.1`.
-/

open Module NumberField InfinitePlace

namespace NumberField

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]

/-- The **label prefix** `d.r.D` of a number field `K` (LMFDB `nf.label`): its degree `d`, its
number `r` of real places, and the absolute value `D` of its discriminant, in decimal and separated
by dots. The LMFDB label of `K` is `d.r.D.i`, where the index `i` numbers the finitely many fields
with the same prefix (`finite_setOf_labelPrefix_eq`) by a database convention that the knowl does
not specify and that is not formalised. -/
noncomputable def labelPrefix : String :=
  toString (finrank ℚ K) ++ "." ++ toString (nrRealPlaces K) ++ "." ++ toString (discr K).natAbs

/-- **The signature of a number field of degree `d` with `r` real places is `[r, (d - r) / 2]`**:
it has `(d - r) / 2` complex places. -/
lemma nrComplexPlaces_eq_finrank_sub_nrRealPlaces_div_two :
    nrComplexPlaces K = (finrank ℚ K - nrRealPlaces K) / 2 := by
  have h : nrRealPlaces K + 2 * nrComplexPlaces K = finrank ℚ K := card_add_two_mul_card_eq_rank K
  omega

private lemma takeWhile_append_dot {l m : List Char} (h : '.' ∉ l) :
    (l ++ '.' :: m).takeWhile (· != '.') = l := by
  rw [List.takeWhile_append_of_pos fun a ha ↦ by simpa using ne_of_mem_of_not_mem ha h]
  simp

private lemma dropWhile_append_dot {l m : List Char} (h : '.' ∉ l) :
    (l ++ '.' :: m).dropWhile (· != '.') = '.' :: m := by
  rw [List.dropWhile_append_of_pos fun a ha ↦ by simpa using ne_of_mem_of_not_mem ha h]
  simp

private lemma append_dot_inj {l₁ l₂ m₁ m₂ : List Char} (h₁ : '.' ∉ l₁) (h₂ : '.' ∉ l₂) :
    l₁ ++ '.' :: m₁ = l₂ ++ '.' :: m₂ ↔ l₁ = l₂ ∧ m₁ = m₂ := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ h.1 ▸ h.2 ▸ rfl⟩
  · rw [← takeWhile_append_dot h₁ (m := m₁), h, takeWhile_append_dot h₂]
  · have h' : '.' :: m₁ = '.' :: m₂ := by
      rw [← dropWhile_append_dot h₁, h, dropWhile_append_dot h₂]
    exact List.cons_injective h'

private lemma dot_notMem_toList_toString (n : ℕ) : '.' ∉ (toString n).toList := by
  rw [Nat.toString_eq_repr, Nat.toList_repr]
  exact fun h ↦ absurd (Nat.isDigit_of_mem_toDigits (by decide) (by decide) h) (by decide)

private lemma toString_injective : Function.Injective (toString : ℕ → String) :=
  fun _ _ h ↦ by simpa using congrArg (fun s : String ↦ Nat.ofDigitChars 10 s.toList 0) h

private lemma toList_toString_append_dot (n : ℕ) (s : String) :
    (toString n ++ ("." ++ s)).toList = (toString n).toList ++ '.' :: s.toList := by
  simp

private lemma toString_append_dot_inj {a b : ℕ} {s t : String} :
    toString a ++ ("." ++ s) = toString b ++ ("." ++ t) ↔ a = b ∧ s = t := by
  rw [← String.toList_inj, toList_toString_append_dot, toList_toString_append_dot,
    append_dot_inj (dot_notMem_toList_toString a) (dot_notMem_toList_toString b),
    String.toList_inj, String.toList_inj, toString_injective.eq_iff]

/-- **The label prefix determines the degree, the number of real places and the absolute
discriminant**: two number fields have the same prefix `d.r.D` exactly when these invariants
agree. -/
lemma labelPrefix_eq_iff : labelPrefix K = labelPrefix L ↔ finrank ℚ K = finrank ℚ L ∧
    nrRealPlaces K = nrRealPlaces L ∧ (discr K).natAbs = (discr L).natAbs := by
  simp only [labelPrefix, String.append_assoc, toString_append_dot_inj, toString_injective.eq_iff]

variable {K L}

open scoped Classical in
lemma nrRealPlaces_eq_of_ringEquiv (e : K ≃+* L) : nrRealPlaces K = nrRealPlaces L := by
  let f : InfinitePlace L ≃ InfinitePlace K :=
    { toFun w := w.comap e
      invFun w := w.comap e.symm
      left_inv w := by
        dsimp only
        rw [← comap_comp, RingEquiv.comp_symm, comap_id]
      right_inv w := by
        dsimp only
        rw [← comap_comp, RingEquiv.symm_comp, comap_id] }
  exact (Fintype.card_congr (f.subtypeEquiv fun w ↦ (isReal_comap_iff e).symm)).symm

/-- **Isomorphic number fields have the same label prefix.** -/
lemma labelPrefix_eq_of_algEquiv (e : K ≃ₐ[ℚ] L) : labelPrefix K = labelPrefix L :=
  (labelPrefix_eq_iff K L).mpr ⟨e.toLinearEquiv.finrank_eq, nrRealPlaces_eq_of_ringEquiv e,
    congrArg Int.natAbs (discr_eq_discr_of_algEquiv K e)⟩

/-- **Finitely many number fields have a given label prefix**: inside a field `A` of characteristic
zero, the subfields of finite degree over `ℚ` with label prefix `s` all have the same absolute
discriminant, and there are finitely many of them by Hermite's theorem
(`NumberField.finite_of_discr_bdd`). As every number field embeds into an algebraic closure of `ℚ`,
there are finitely many isomorphism classes of number fields with a given prefix, which the index
of the label numbers. -/
lemma finite_setOf_labelPrefix_eq (A : Type*) [Field A] [CharZero A] (s : String) :
    {F : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
      haveI : NumberField F := { to_finiteDimensional := F.prop }
      labelPrefix F = s}.Finite := by
  refine (Set.finite_or_infinite _).elim id fun h ↦ ?_
  rcases h.nonempty with ⟨F₀, hF₀⟩
  have : NumberField F₀ := { to_finiteDimensional := F₀.prop }
  refine (finite_of_discr_bdd A (discr F₀).natAbs).subset fun F hF ↦ ?_
  have : NumberField F := { to_finiteDimensional := F.prop }
  have hD : (discr F).natAbs = (discr F₀).natAbs :=
    ((labelPrefix_eq_iff F F₀).mp (hF.trans hF₀.symm)).2.2
  rw [Set.mem_ofPred_eq, ← Int.natCast_natAbs, hD]

/-- **The label prefix of `ℚ` is `1.1.1`**, as in its LMFDB label `1.1.1.1`: `ℚ` has degree `1`,
one real place and discriminant `1`. -/
lemma labelPrefix_rat : labelPrefix ℚ = "1.1.1" := by
  rw [labelPrefix, ← IsTotallyReal.finrank, finrank_self, Rat.numberField_discr]
  rfl

end NumberField
