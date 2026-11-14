import LeanBridge.ForMathlib.NumberTheory.NumberField.Units.BiquadraticUnitIndex

/-!
# The classification of the units of real biquadratic fields

Kubota's list, as Mazur and Ullom quote it, sorts the units `U` of a real biquadratic field `K`
modulo `±1` into the subtypes I (i), I (ii), I (iii), II (i), II (ii), III and IV (LMFDB
`nf.galois_group.gmodule_v4_type_i_i` to `nf.galois_group.gmodule_v4_type_iv`; Mazur and Ullom
split type IV further by the norms of the fundamental units), defined by which square roots of
products of fundamental units `e₁, e₂, e₃` of the three quadratic subfields generate `U/{±1}`:
the predicates `IsMazurUllomTypeI₁` to `IsMazurUllomTypeIV`. Every real biquadratic field has
exactly one of the seven subtypes (`existsUnique_isMazurUllomType`). Mazur and Ullom's description
of the four basic types I–IV as the isomorphism classes of the `ℤ[V₄]`-module `U/{±1}` (their
Theorem 1 and Remark 1) is proved in `Units/BiquadraticGaloisModule.lean`.

The predicates say "for some fundamental units `e₁, e₂, e₃` of the three quadratic subfields", that
is for some frame of quadratic units: some labelling of the subfields and some choice of their
fundamental units, which are unique up to sign. For a real biquadratic field this is the same as
"for every frame, after relabelling its subfields" (`isMazurUllomType_iff_forall`), and the subtype
is read off any frame from the products of fundamental units that are squares
(`isMazurUllomType_iff_forall_isSquare`).

The proof: the classes of the fundamental units of a frame form a square basis of `U/{±1}`
(`QuadraticUnitFrame.isSquareBasis_unitClass`, from the norms to the subfields), they are not all
squares (`QuadraticUnitFrame.not_forall_isSquare_unitClass`, Kubota's arithmetic argument), and two
frames differ by a relabelling and signs (`QuadraticUnitFrame.unitClass_eq_or_eq_inv`). The group
theory of square bases (`MazurUllomType.IsSquareBasis.exists_isTypeOf_comp` and
`MazurUllomType.IsSquareBasis.eq_of_isTypeOf`) then gives existence and uniqueness.

## Main definitions

* `NumberField.Units.IsMazurUllomType`: the units of `K` have the subtype `t`, one of the seven
  predicates `IsMazurUllomTypeI₁ K`, …, `IsMazurUllomTypeIV K`.

## Main results

* `NumberField.Units.existsUnique_isMazurUllomType`: **every real biquadratic field has exactly one
  of the seven subtypes.**
* `NumberField.Units.exists_isMazurUllomType`, `NumberField.Units.eq_of_isMazurUllomType`: the
  subtypes are exhaustive and exclusive.
* `NumberField.Units.isMazurUllomType_iff_forall`: a subtype holds for some frame iff it holds for
  every frame after relabelling.
* `NumberField.Units.isMazurUllomType_iff_forall_isSquare`: the subtype in terms of the products of
  fundamental units that are squares.

## References

* M. Mazur and S. V. Ullom, *Galois module structure of units in real biquadratic number fields*,
  Acta Arith. 111 (2004), 105–124.
* T. Kubota, *Über den bizyklischen biquadratischen Zahlkörper*, Nagoya Math. J. 10 (1956), 65–85.
-/

open scoped NumberField

namespace NumberField.Units

variable (K : Type*) [Field K] [NumberField K]

/-- The units of `K` have the subtype `t` of Mazur and Ullom: `IsMazurUllomTypeI₁ K`, …,
`IsMazurUllomTypeIV K` as `t` is `I₁`, …, `IV`. Only meaningful for a real biquadratic field `K`,
which has exactly one of them (`existsUnique_isMazurUllomType`). -/
def IsMazurUllomType : MazurUllomType → Prop
  | .I₁ => IsMazurUllomTypeI₁ K
  | .I₂ => IsMazurUllomTypeI₂ K
  | .I₃ => IsMazurUllomTypeI₃ K
  | .II₁ => IsMazurUllomTypeII₁ K
  | .II₂ => IsMazurUllomTypeII₂ K
  | .III => IsMazurUllomTypeIII K
  | .IV => IsMazurUllomTypeIV K

variable {K} (t : MazurUllomType)

lemma isMazurUllomType_iff :
    IsMazurUllomType K t ↔ ∃ f : QuadraticUnitFrame K, t.IsTypeOf f.unitClass := by
  cases t <;> rfl

variable [IsGalois ℚ K] [IsKleinFour Gal(K/ℚ)] [IsTotallyReal K]

/-- **The subtypes are exhaustive**: every real biquadratic field has one of the seven subtypes. -/
lemma exists_isMazurUllomType : ∃ t, IsMazurUllomType K t := by
  rcases nonempty_quadraticUnitFrame K with ⟨f⟩
  rcases f.isSquareBasis_unitClass.exists_isTypeOf_comp f.not_forall_isSquare_unitClass
    with ⟨t, π, h⟩
  exact ⟨t, (isMazurUllomType_iff t).mpr ⟨f.relabel π, h⟩⟩

variable {t} in
/-- **The subtypes are exclusive**: a real biquadratic field has at most one of the seven
subtypes. -/
lemma eq_of_isMazurUllomType {t' : MazurUllomType} (h : IsMazurUllomType K t)
    (h' : IsMazurUllomType K t') : t = t' := by
  rcases (isMazurUllomType_iff t).mp h with ⟨f, hf⟩
  rcases (isMazurUllomType_iff t').mp h' with ⟨f', hf'⟩
  exact f.isSquareBasis_unitClass.eq_of_isTypeOf f'.isSquareBasis_unitClass
    (π := f'.subfield.trans f.subfield.symm) (fun i ↦ f.unitClass_eq_or_eq_inv i f') hf hf'

/-- **The classification of Kubota and of Mazur and Ullom**: every real biquadratic field has
exactly one of the seven subtypes I (i), I (ii), I (iii), II (i), II (ii), III and IV, which say
how square roots of products of fundamental units of its quadratic subfields generate its units
modulo `±1`. -/
lemma existsUnique_isMazurUllomType : ∃! t, IsMazurUllomType K t := by
  rcases exists_isMazurUllomType (K := K) with ⟨t, ht⟩
  exact ⟨t, ht, fun _ h ↦ eq_of_isMazurUllomType h ht⟩

/-- **"For some frame" is "for every frame, after relabelling"**: a real biquadratic field has the
subtype `t` iff every frame of quadratic units has the subtype `t` once its subfields are suitably
relabelled. -/
lemma isMazurUllomType_iff_forall : IsMazurUllomType K t ↔ ∀ f : QuadraticUnitFrame K,
    ∃ π : Equiv.Perm (Fin 3), t.IsTypeOf (f.relabel π).unitClass := by
  refine ⟨fun h f ↦ ?_, fun h ↦ ?_⟩
  · rcases f.isSquareBasis_unitClass.exists_isTypeOf_comp f.not_forall_isSquare_unitClass
      with ⟨t', π, h'⟩
    rcases eq_of_isMazurUllomType ((isMazurUllomType_iff t').mpr ⟨f.relabel π, h'⟩) h
    exact ⟨π, h'⟩
  · rcases nonempty_quadraticUnitFrame K with ⟨f⟩
    rcases h f with ⟨π, hπ⟩
    exact (isMazurUllomType_iff t).mpr ⟨f.relabel π, hπ⟩

/-- **The subtype from the squares among products of fundamental units**: a real biquadratic field
has the subtype `t` iff for every frame, after relabelling, the product
`e₀ ^ v₀ * e₁ ^ v₁ * e₂ ^ v₂` of the classes of its fundamental units is a square exactly for the
exponent vectors `v` of the parity pattern of `t`. -/
lemma isMazurUllomType_iff_forall_isSquare : IsMazurUllomType K t ↔ ∀ f : QuadraticUnitFrame K,
    ∃ π : Equiv.Perm (Fin 3), ∀ v, IsSquare (∏ i, f.unitClass (π i) ^ v i) ↔ t.Parity v := by
  rw [isMazurUllomType_iff_forall]
  exact forall_congr' fun f ↦ exists_congr fun π ↦
    (f.relabel π).isSquareBasis_unitClass.isTypeOf_iff t

end NumberField.Units
