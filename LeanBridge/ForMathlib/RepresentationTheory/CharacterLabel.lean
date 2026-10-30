import LeanBridge.ForMathlib.GroupTheory.Label.Group
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.ComplexAutomorphism
import LeanBridge.ForMathlib.RepresentationTheory.RationalCharacterTable
import Mathlib.FieldTheory.PrimitiveElement
import TauCeti.RepresentationTheory.CharacterTable.CoefficientAction
import TauCeti.RepresentationTheory.CharacterTable.Table

/-!
# LMFDB labels of complex and rational characters of finite groups

The LMFDB labels an irreducible complex character `χ` of a finite group `G` (LMFDB
`group.label_complex_group_char`) by `N.i.dcj`: `N.i` is the label of `G` (LMFDB `group.label`),
`d = χ(1)` is the degree of `χ`, `c` is a lower-case letter code for the rational class of `χ`, the
set `FDRep.rationalClass χ` of its Galois conjugates `σ ∘ χ`, and `j` numbers the characters in that
rational class, omitted when the class is the single character `χ`. The Galois conjugates of `χ` are
irreducible characters (`FDRep.algEquiv_comp_mem_irreducibleCharacters`) of the same degree
(`FDRep.apply_one_eq_of_mem_rationalClass`), so `d` is a function of the rational class, and the
rational class is the single character `χ` exactly when `χ` is rational valued
(`FDRep.rationalClass_subsingleton_iff`).

It labels an irreducible rational character `ψ` of `G` (LMFDB `group.label_rational_group_char`),
the sum of the Galois conjugates of an irreducible complex character (`FDRep.rationalCharacter`,
LMFDB `group.representation.rational_character`), by `N.i.oj`, with `j` a lower-case letter code.
The knowl describes `o` as "the order of elements in this class", words that have no meaning for a
character and that describe instead the labels `NA` of the rational conjugacy classes heading the
columns of the rational character table (LMFDB `group.label_conjugacy_class`). In the LMFDB's data
`o` is the degree of the complex characters of the rational class of `ψ`, its irreducible complex
constituents (the column `cdim` of the table `gps_qchar`), not `ψ(1)` (the column `qdim`): the
rational characters of `C₃` are `3.1.1a` and `3.1.1b`, of degrees `ψ(1) = 1` and `2`, those of `C₄`
are `4.1.1a`, `4.1.1b` and `4.1.1c`, of degrees `1`, `1` and `2`, and that of `D₄` of degree `2` is
`8.3.2a`, whose class is a single character. So the label of `ψ` is the part `N.i.dc` shared by the
labels of the characters of its rational class. The degree `ψ(1)` is the size of the class times
`o` (`FDRep.rationalCharacter_apply_one`), and `o` is well defined: simple representations with the
same rational character have the same dimension (`FDRep.finrank_eq_of_rationalCharacter_eq`).

The letter codes `c` and `j` and the numbers `j` come from the LMFDB's orderings of the rational
classes and of the characters within them, database numberings which are not formalised: we record
them as data, say when a label is consistent with a character, and when an assignment of labels to
all irreducible characters is a labelling: its labels are consistent, `d` and `c` together identify
exactly the rational classes, and distinct characters have distinct labels.

## Main definitions

* `FDRep.rationalClass` (LMFDB `group.label_complex_group_char`): the rational class of a character.
* `FDRep.ComplexCharacterLabel`, `FDRep.ComplexCharacterLabel.toString`,
  `FDRep.ComplexCharacterLabel.IsConsistent` and `FDRep.IsComplexCharacterLabelling` (LMFDB
  `group.label_complex_group_char`): labels `N.i.dcj` of irreducible complex characters.
* `FDRep.RationalCharacterLabel`, `FDRep.RationalCharacterLabel.toString`,
  `FDRep.RationalCharacterLabel.IsConsistent` and `FDRep.IsRationalCharacterLabelling` (LMFDB
  `group.label_rational_group_char`): labels `N.i.oj` of irreducible rational characters.

## Main results

* `FDRep.rationalClass_eq_of_mem`: Galois conjugacy is an equivalence relation, whose classes are
  the rational classes.
* `FDRep.apply_one_eq_of_mem_rationalClass`: Galois conjugate characters have the same degree.
* `FDRep.algEquiv_comp_mem_irreducibleCharacters`: the Galois conjugates of an irreducible
  character are irreducible characters.
* `FDRep.rationalClass_eq_singleton`: the rational class of a rational valued function is the
  single function.
* `FDRep.rationalClass_subsingleton_iff`: the rational class of a character of a finite group is a
  single character exactly when the character is rational valued, so that its label has no `j`.
* `FDRep.rationalCharacter_apply_one`: the degree of the irreducible rational character attached
  to an irreducible representation is the size of the rational class times the dimension.
* `FDRep.finrank_eq_of_rationalCharacter_eq`: simple representations with the same irreducible
  rational character have the same dimension.
* `FDRep.exists_isComplexCharacterLabelling` and `FDRep.exists_isRationalCharacterLabelling`: the
  irreducible complex and rational characters of a finite group have labellings.
-/

open CategoryTheory Module TauCeti

namespace FDRep

variable {G : Type} {χ ψ : G → ℂ} {n : ℕ}

variable (χ) in
/-- The **rational class** of a complex function `χ` on `G` (LMFDB
`group.label_complex_group_char`): the set of its Galois conjugates `σ ∘ χ` for the field
automorphisms `σ` of `ℂ`. For the character of a representation `X` this is the set
`FDRep.galoisConjugates X`, whose sum is the rational character of `X`. -/
def rationalClass : Set (G → ℂ) :=
  Set.range fun σ : ℂ ≃ₐ[ℚ] ℂ ↦ σ ∘ χ

variable (χ) in
lemma mem_rationalClass_self : χ ∈ rationalClass χ :=
  ⟨1, rfl⟩

/-- **The rational classes are the classes of an equivalence relation**: a Galois conjugate of `χ`
has the same rational class as `χ`. -/
lemma rationalClass_eq_of_mem (h : ψ ∈ rationalClass χ) : rationalClass ψ = rationalClass χ := by
  rcases h with ⟨σ, rfl⟩
  refine Set.ext fun f ↦ ⟨fun ⟨τ, hτ⟩ ↦ ⟨τ * σ, hτ⟩, fun ⟨τ, hτ⟩ ↦ ⟨τ * σ⁻¹, ?_⟩⟩
  rw [← hτ]
  exact funext fun g ↦ congrArg τ (σ.symm_apply_apply (χ g))

lemma mem_rationalClass_comm : ψ ∈ rationalClass χ ↔ χ ∈ rationalClass ψ :=
  ⟨fun h ↦ rationalClass_eq_of_mem h ▸ mem_rationalClass_self χ,
    fun h ↦ rationalClass_eq_of_mem h ▸ mem_rationalClass_self ψ⟩

/-- **The rational class of a rational valued function is the single function**, so that the
LMFDB label of a rational valued character has no part `j`. -/
lemma rationalClass_eq_singleton (hχ : ∀ g, ∃ q : ℚ, χ g = q) : rationalClass χ = {χ} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_rationalClass_self χ, fun f ⟨σ, hσ⟩ ↦ ?_⟩
  rw [← hσ]
  refine funext fun g ↦ ?_
  rcases hχ g with ⟨q, hq⟩
  exact (congrArg σ hq).trans <| (map_ratCast σ q).trans hq.symm

variable [Group G] (X : FDRep ℂ G)

lemma galoisConjugates_eq_rationalClass : X.galoisConjugates = rationalClass X.character :=
  rfl

/-- **Galois conjugate characters have the same degree**: if `χ(1)` is a natural number, then so is
every Galois conjugate `σ (χ(1))`. -/
lemma apply_one_eq_of_mem_rationalClass (h : ψ ∈ rationalClass χ) (hχ : χ 1 = n) : ψ 1 = n := by
  rcases h with ⟨σ, rfl⟩
  exact (congrArg σ hχ).trans <| map_natCast σ n

lemma exists_apply_one_eq_natCast (hχ : χ ∈ irreducibleCharacters ℂ G) : ∃ n : ℕ, χ 1 = n := by
  rcases mem_irreducibleCharacters_iff.mp hχ with ⟨n, ρ, -, rfl⟩
  exact ⟨n, by rw [Representation.char_one, finrank_fin_fun]⟩

/-- The **label** `N.i.dcj` of an irreducible complex character of a finite group (LMFDB
`group.label_complex_group_char`), as data: the label `N.i` of the group, the degree `d`, the letter
code `c` of the rational class and the number `j` of the character in its rational class, omitted
(`none`) when the class is a single character. The codes `c` and the numbers `j` come from the
LMFDB's orderings of the rational classes and of the characters within them, database numberings
recorded here but not determined. -/
@[ext]
structure ComplexCharacterLabel where
  /-- The label `N.i` of the group. -/
  group : Group.Label
  /-- The degree `d`. -/
  degree : ℕ
  /-- The letter code `c` of the rational class. -/
  classCode : String
  /-- The number `j` of the character in its rational class, if the class has several elements. -/
  index : Option ℕ

namespace ComplexCharacterLabel

variable (ℓ : ComplexCharacterLabel)

/-- The string `N.i.dcj` of the label of an irreducible complex character, as in `4.1.1c2`. -/
def toString : String :=
  ℓ.group.toString ++ "." ++ ℓ.degree.repr ++ ℓ.classCode ++ (ℓ.index.map Nat.repr).getD ""

variable (χ) in
/-- A label `N.i.dcj` is **consistent** with a character `χ` of `G` (LMFDB
`group.label_complex_group_char`) if `N.i` is consistent with `G`, `d = χ(1)`, `c` is a letter
code, and `j` is omitted exactly when the rational class of `χ` is the single character `χ`. -/
def IsConsistent : Prop :=
  ℓ.group.IsConsistent G ∧ (ℓ.degree : ℂ) = χ 1 ∧ Group.IsLetterCode ℓ.classCode ∧
    (ℓ.index = none ↔ (rationalClass χ).Subsingleton)

end ComplexCharacterLabel

variable {ℓG : Group.Label}

variable (ℓG) in
/-- An assignment `ℓ` of labels `N.i.dcj` to the irreducible complex characters of `G` is a
**labelling** (LMFDB `group.label_complex_group_char`), with group label `ℓG`, if every label starts
with `ℓG` and is consistent with its character, two characters have the same degree and letter code
exactly when they lie in the same rational class, and distinct characters have distinct labels. -/
structure IsComplexCharacterLabelling (ℓ : irreducibleCharacters ℂ G → ComplexCharacterLabel) :
    Prop where
  /-- Every label starts with the label of the group. -/
  group_eq : ∀ χ, (ℓ χ).group = ℓG
  /-- Every label is consistent with its character. -/
  isConsistent : ∀ χ, (ℓ χ).IsConsistent (χ : G → ℂ)
  /-- The degree and the letter code identify the rational classes. -/
  degree_classCode_eq_iff : ∀ χ ψ,
    (ℓ χ).degree = (ℓ ψ).degree ∧ (ℓ χ).classCode = (ℓ ψ).classCode ↔ (ψ : G → ℂ) ∈ rationalClass χ
  /-- Distinct characters have distinct labels. -/
  injective : Function.Injective ℓ

/-- The **label** `N.i.oj` of an irreducible rational character of a finite group (LMFDB
`group.label_rational_group_char`), as data: the label `N.i` of the group, the degree `o` of the
complex characters of its rational class (not the degree of the rational character, see the module
docstring) and a letter code `j`, which comes from the LMFDB's ordering of the rational characters,
a database numbering recorded here but not determined. -/
@[ext]
structure RationalCharacterLabel where
  /-- The label `N.i` of the group. -/
  group : Group.Label
  /-- The degree `o` of the irreducible complex constituents of the rational character. -/
  degree : ℕ
  /-- The letter code `j`. -/
  code : String

namespace RationalCharacterLabel

variable (ℓ : RationalCharacterLabel)

/-- The string `N.i.oj` of the label of an irreducible rational character, as in `3.1.1b`. -/
def toString : String :=
  ℓ.group.toString ++ "." ++ ℓ.degree.repr ++ ℓ.code

variable (ψ) in
/-- A label `N.i.oj` is **consistent** with an irreducible rational character `ψ` of `G` (LMFDB
`group.label_rational_group_char`) if `N.i` is consistent with `G`, `o` is the common degree of the
irreducible complex constituents of `ψ`, that is, the dimension of every simple representation whose
rational character is `ψ` (these have one dimension, `FDRep.finrank_eq_of_rationalCharacter_eq`),
and `j` is a letter code. -/
def IsConsistent : Prop :=
  ℓ.group.IsConsistent G ∧
    (∀ X : FDRep ℂ G, Simple X → X.rationalCharacter = ψ → ℓ.degree = finrank ℂ X) ∧
    Group.IsLetterCode ℓ.code

end RationalCharacterLabel

variable (ℓG) in
/-- An assignment `ℓ` of labels `N.i.oj` to the irreducible rational characters of `G` is a
**labelling** (LMFDB `group.label_rational_group_char`), with group label `ℓG`, if every label
starts with `ℓG` and is consistent with its character, and distinct characters have distinct
labels, so that `j` distinguishes the irreducible rational characters whose constituents have the
same degree. -/
structure IsRationalCharacterLabelling
    (ℓ : irreducibleRationalCharacters G → RationalCharacterLabel) : Prop where
  /-- Every label starts with the label of the group. -/
  group_eq : ∀ ψ, (ℓ ψ).group = ℓG
  /-- Every label is consistent with its character. -/
  isConsistent : ∀ ψ, (ℓ ψ).IsConsistent (ψ : G → ℂ)
  /-- Distinct characters have distinct labels. -/
  injective : Function.Injective ℓ

variable [Finite G]

/-- **The Galois conjugates of an irreducible character are irreducible characters**: `σ ∘ χ` is a
virtual character of norm `1` whose degree is a natural number. -/
lemma algEquiv_comp_mem_irreducibleCharacters (σ : ℂ ≃ₐ[ℚ] ℂ) (hχ : χ ∈ irreducibleCharacters ℂ G) :
    σ ∘ χ ∈ irreducibleCharacters ℂ G := by
  let _ : Fintype G := Fintype.ofFinite G
  rcases mem_irreducibleCharacters_iff.mp hχ with ⟨n, ρ, hρ, rfl⟩
  have hf : ρ.character ∈ virtualCharacters ℂ G :=
    AddSubgroup.subset_closure <| irreducibleCharacters_subset_range hχ
  refine mem_irreducibleCharacters_of_characterPairing_self_eq_one
    (f := ClassFunction.map σ.toRingHom (ClassFunction.ofCharacter ρ))
    (σ.toRingHom.comp_mem_virtualCharacters hf) ?_ (n := n) ?_
  · rw [ClassFunction.characterPairing_map, ClassFunction.characterPairing_ofCharacter_self,
      map_one]
  · rw [ClassFunction.map_apply, ClassFunction.ofCharacter_apply, Representation.char_one,
      finrank_fin_fun, map_natCast]

lemma rationalClass_subset_irreducibleCharacters (hχ : χ ∈ irreducibleCharacters ℂ G) :
    rationalClass χ ⊆ irreducibleCharacters ℂ G :=
  fun _ ⟨σ, hσ⟩ ↦ hσ ▸ algEquiv_comp_mem_irreducibleCharacters σ hχ

instance : Countable (X.characterField ℚ) := by
  rw [characterField_def, ← Cardinal.mk_le_aleph0_iff]
  exact (IntermediateField.cardinalMk_adjoin_le ℚ _).trans <|
    sup_le (sup_le Cardinal.mk_le_aleph0 (Set.countable_range _).le_aleph0) le_rfl

/-- **The rational class of a character of a finite group is the single character exactly when
the character is rational valued**, so that the LMFDB label of an irreducible character has no
part `j` exactly when the character is rational valued. If the class is a single character, every
automorphism of `ℂ` fixes the field of values `ℚ(χ)`, so `ℚ(χ)` has a single embedding into `ℂ`,
the embeddings of the countable field `ℚ(χ)` extending to automorphisms of `ℂ`, and `ℚ(χ) = ℚ`. -/
lemma rationalClass_subsingleton_iff :
    (rationalClass X.character).Subsingleton ↔ X.IsRationalCharacter := by
  refine ⟨fun h ↦ ?_, fun h ↦ rationalClass_eq_singleton h ▸ Set.subsingleton_singleton⟩
  have hι (ι : X.characterField ℚ →ₐ[ℚ] ℂ) : ι = (X.characterField ℚ).val := by
    rcases IntermediateField.exists_algEquiv_apply_eq_of_countable ι with ⟨σ, hσ⟩
    have hχ : σ ∘ X.character = X.character := h ⟨σ, rfl⟩ (mem_rationalClass_self _)
    have hfix : ∀ x ∈ X.characterField ℚ, σ x = x :=
      (X.forall_mem_characterField_apply_eq_self_iff ℚ σ).mpr fun g ↦ congrFun hχ g
    exact AlgHom.ext fun x ↦ (hσ x).symm.trans (hfix x x.2)
  have hrank : Module.finrank ℚ (X.characterField ℚ) = 1 := by
    rw [← AlgHom.card ℚ (X.characterField ℚ) ℂ, Fintype.card_eq_one_iff]
    exact ⟨_, hι⟩
  intro g
  rcases IntermediateField.mem_bot.mp <| IntermediateField.finrank_eq_one_iff.mp hrank ▸
    X.character_mem_characterField ℚ g with ⟨q, hq⟩
  exact ⟨q, hq.symm.trans <| eq_ratCast (algebraMap ℚ ℂ) q⟩

/-- **The degree of the irreducible rational character attached to `X`** is the number of Galois
conjugates of the character of `X` times the dimension of `X`. -/
lemma rationalCharacter_apply_one :
    X.rationalCharacter 1 = X.galoisConjugates.ncard * finrank ℂ X := by
  rw [rationalCharacter, finsum_mem_eq_finite_toFinset_sum _ X.finite_galoisConjugates,
    Finset.sum_apply, Set.ncard_eq_toFinset_card _ X.finite_galoisConjugates, ← nsmul_eq_mul,
    ← Finset.sum_const]
  refine Finset.sum_congr rfl fun f hf ↦ ?_
  exact apply_one_eq_of_mem_rationalClass (X.finite_galoisConjugates.mem_toFinset.mp hf) X.char_one

variable [Simple X]

private lemma rationalCharacter_eq_sum : X.rationalCharacter = ∑ i,
    ((irreducibleCharacter ℂ ⁻¹' X.galoisConjugates).indicator 1 i : ℂ) •
        irreducibleCharacter ℂ i := by
  have hsub : X.galoisConjugates ⊆ Set.range (irreducibleCharacter (G := G) ℂ) :=
    fun f hf ↦ exists_irreducibleCharacter_eq ℂ <|
      rationalClass_subset_irreducibleCharacters X.character_mem_irreducibleCharacters hf
  rw [rationalCharacter, ← Set.image_preimage_eq_of_subset hsub,
    finsum_mem_image (irreducibleCharacter_injective ℂ).injOn, finsum_mem_def,
    finsum_eq_sum_of_fintype, Set.preimage_image_eq _ (irreducibleCharacter_injective ℂ)]
  simp only [← Set.indicator_smul_apply_left, Pi.one_apply, one_smul]

/-- **Simple representations with the same irreducible rational character have the same
dimension**, the common degree of the irreducible complex constituents of the rational character:
the rational character is the sum of a rational class of irreducible characters, which it
determines since the irreducible characters are linearly independent. -/
lemma finrank_eq_of_rationalCharacter_eq {Y : FDRep ℂ G} [Simple Y]
    (h : X.rationalCharacter = Y.rationalCharacter) : finrank ℂ X = finrank ℂ Y := by
  rcases exists_irreducibleCharacter_eq ℂ X.character_mem_irreducibleCharacters with ⟨i, hi⟩
  have hiX : i ∈ irreducibleCharacter ℂ ⁻¹' X.galoisConjugates := by
    rw [Set.mem_preimage, hi]
    exact mem_rationalClass_self _
  have hc : ((irreducibleCharacter ℂ ⁻¹' X.galoisConjugates).indicator 1 i : ℂ) =
      (irreducibleCharacter ℂ ⁻¹' Y.galoisConjugates).indicator 1 i :=
    (linearIndependent_irreducibleCharacter (k := ℂ)).eq_coords_of_eq
      ((rationalCharacter_eq_sum X).symm.trans <| h.trans <| rationalCharacter_eq_sum Y) i
  rw [Set.indicator_of_mem hiX, Pi.one_apply] at hc
  have hiY : i ∈ irreducibleCharacter ℂ ⁻¹' Y.galoisConjugates :=
    Set.mem_of_indicator_ne_zero <| hc ▸ one_ne_zero
  rw [Set.mem_preimage, hi] at hiY
  exact Nat.cast_injective <| X.char_one.symm.trans <|
    apply_one_eq_of_mem_rationalClass hiY Y.char_one

variable (G) in
lemma finite_irreducibleRationalCharacters : (irreducibleRationalCharacters G).Finite := by
  refine ((irreducibleCharacters ℂ G).toFinite.image fun χ ↦ ∑ᶠ f ∈ rationalClass χ, f).subset ?_
  rintro - ⟨Y, hY, rfl⟩
  exact ⟨Y.character, Y.character_mem_irreducibleCharacters, rfl⟩

variable (n) in
/-- A letter code for each natural number, injectively: `n + 1` letters `a`. -/
private def lowerCode : String :=
  String.ofList (List.replicate (n + 1) 'a')

private lemma lowerCode_injective : Function.Injective lowerCode := fun m n h ↦ by
  simpa using congrArg List.length <| String.ofList_injective h

variable (n) in
private lemma isLetterCode_lowerCode : Group.IsLetterCode (lowerCode n) := by
  refine ⟨by simp [lowerCode], fun c hc ↦ ?_⟩
  rw [lowerCode, String.toList_ofList, List.mem_replicate] at hc
  rw [hc.2]
  decide

/-- **The irreducible complex characters of a finite group have a labelling** (LMFDB
`group.label_complex_group_char`), for any group label consistent with the group: for instance with
distinct letter codes for the rational classes and distinct numbers `j` for the characters in
rational classes with several elements. -/
lemma exists_isComplexCharacterLabelling (hG : ℓG.IsConsistent G) :
    ∃ ℓ : irreducibleCharacters ℂ G → ComplexCharacterLabel, IsComplexCharacterLabelling ℓG ℓ := by
  classical
  let r : Setoid (irreducibleCharacters ℂ G) := ⟨fun χ ψ ↦ (ψ : G → ℂ) ∈ rationalClass χ,
    ⟨fun χ ↦ mem_rationalClass_self _, mem_rationalClass_comm.mp,
      fun h h' ↦ rationalClass_eq_of_mem h ▸ h'⟩⟩
  rcases exists_injective_nat (Quotient r) with ⟨e, he⟩
  rcases exists_injective_nat (irreducibleCharacters ℂ G) with ⟨e', he'⟩
  choose n hn using fun χ : irreducibleCharacters ℂ G ↦ exists_apply_one_eq_natCast χ.2
  have hclass (χ ψ : irreducibleCharacters ℂ G) (h : lowerCode (e ⟦χ⟧) = lowerCode (e ⟦ψ⟧)) :
      (ψ : G → ℂ) ∈ rationalClass χ :=
    Quotient.exact <| he <| lowerCode_injective h
  refine ⟨fun χ ↦ ⟨ℓG, n χ, lowerCode (e ⟦χ⟧),
    if (rationalClass (χ : G → ℂ)).Subsingleton then none else some (e' χ)⟩, fun χ ↦ rfl,
    fun χ ↦ ⟨hG, (hn χ).symm, isLetterCode_lowerCode _, by simp⟩, fun χ ψ ↦ ⟨fun h ↦ hclass χ ψ h.2,
    fun h ↦ ⟨Nat.cast_injective <| (apply_one_eq_of_mem_rationalClass h (hn χ)).symm.trans (hn ψ),
    congrArg (lowerCode ∘ e) <| Quotient.sound h⟩⟩, fun χ ψ h ↦ ?_⟩
  have hψ : (ψ : G → ℂ) ∈ rationalClass χ :=
    hclass χ ψ <| congrArg ComplexCharacterLabel.classCode h
  have hj : (if (rationalClass (χ : G → ℂ)).Subsingleton then none else some (e' χ)) =
      if (rationalClass (ψ : G → ℂ)).Subsingleton then none else some (e' ψ) :=
    congrArg ComplexCharacterLabel.index h
  rw [rationalClass_eq_of_mem hψ] at hj
  split_ifs at hj with hs
  · exact Subtype.ext <| hs (mem_rationalClass_self _) hψ
  · exact he' <| Option.some_injective _ hj

/-- **The irreducible rational characters of a finite group have a labelling** (LMFDB
`group.label_rational_group_char`), for any group label consistent with the group: for instance
with distinct letter codes `j`. -/
lemma exists_isRationalCharacterLabelling (hG : ℓG.IsConsistent G) :
    ∃ ℓ : irreducibleRationalCharacters G → _, IsRationalCharacterLabelling ℓG ℓ := by
  have : Countable (irreducibleRationalCharacters G) :=
    (finite_irreducibleRationalCharacters G).countable.to_subtype
  rcases exists_injective_nat (irreducibleRationalCharacters G) with ⟨e, he⟩
  choose Y hY hψ using fun ψ : irreducibleRationalCharacters G ↦ ψ.2
  refine ⟨fun ψ ↦ ⟨ℓG, finrank ℂ (Y ψ), lowerCode (e ψ)⟩, fun ψ ↦ rfl,
    fun ψ ↦ ⟨hG, fun X hX h ↦ ?_, isLetterCode_lowerCode _⟩,
    fun ψ ψ' h ↦ he <| lowerCode_injective <| congrArg RationalCharacterLabel.code h⟩
  have : Simple (Y ψ) := hY ψ
  exact finrank_eq_of_rationalCharacter_eq (Y ψ) <| (hψ ψ).trans h.symm

end FDRep
