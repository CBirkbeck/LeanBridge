import LeanBridge.ForMathlib.NumberTheory.NumberField.Units.BiquadraticClassification
import LeanBridge.ForMathlib.NumberTheory.NumberField.Units.MazurUllomModule

/-!
# The Galois module structure of the units of real biquadratic fields

Let `K` be a real biquadratic field, with units `U`. Its Galois group `Gal(K/ℚ)` is a Klein
four-group and acts on the units modulo torsion `(𝓞 K)ˣ ⧸ torsion K`, which is `U/{±1}`; written
additively, this is a `ℤ[Gal(K/ℚ)]`-module (`NumberField.Units.modTorsionRep`). Mazur and Ullom
show that it has one of four isomorphism types, the basic types I–IV (Theorem 1 and Remark 1 of
their paper). This file proves it, with the module `T.rep` of each basic type `T` defined in
`Units/MazurUllomModule.lean` over `V₄ = ℤˣ × ℤˣ`:
* a field whose units have a subtype of basic type `T` (for instance I (ii), of basic type I) has
  `U/{±1}` isomorphic to `T.rep`, along an isomorphism `Gal(K/ℚ) ≃* V₄`
  (`NumberField.Units.IsMazurUllomBasicType.exists_equiv`, Theorem 1);
* the basic type is the isomorphism class: `K` has basic type `T` iff `U/{±1}` is isomorphic to
  `T.rep` along some isomorphism `Gal(K/ℚ) ≃* V₄` (`NumberField.Units.isMazurUllomBasicType_iff`);
* two real biquadratic fields have isomorphic Galois modules, along an isomorphism of their Galois
  groups, iff they have the same basic type (`NumberField.Units.exists_equiv_iff`).

The isomorphism of Theorem 1 is explicit (`NumberField.Units.QuadraticUnitFrame.galoisModuleEquiv`):
for a frame of quadratic units whose classes `ē₀, ē₁, ē₂` have the subtype `t`, it sends `x` to the
vector `v` with `x ^ 2 = ∏ i, (ēᵢ ^ sᵢ) ^ vᵢ`, `s = t.scale`, and it is equivariant along the
isomorphism `Gal(K/ℚ) ≃* V₄` sending the automorphism fixing the `i`-th quadratic subfield to `σᵢ`
(`NumberField.Units.QuadraticUnitFrame.kleinEquiv`). That automorphism fixes `ēᵢ` and inverts the
other two classes, as `σᵢ` multiplies the `i`-th coordinate by `1` and the two others by `-1`. In
the frame's labelling this is the paper's statement: for the subtypes II (i) and II (ii), where
`√(e₀e₁)` is a generator, the module is `B₂ ⊕ A₂`.

The instance `Module ℤ (Additive ((𝓞 K)ˣ ⧸ torsion K))` is stated explicitly here: outside the
module system, Lean does not find the general instance for this type. With it, Mathlib's Dirichlet
unit theorem says that `U/{±1}` has rank `3` (`NumberField.Units.finrank_modTorsion_eq_three`).

## Main definitions

* `NumberField.Units.modTorsionRep`: the units modulo torsion of `K` as a `ℤ[Gal(K/ℚ)]`-module.
* `NumberField.Units.IsMazurUllomBasicType`: the units of `K` have the basic type `T`.
* `NumberField.Units.QuadraticUnitFrame.kleinEquiv`: the isomorphism `Gal(K/ℚ) ≃* V₄` of a frame.
* `NumberField.Units.QuadraticUnitFrame.galoisModuleEquiv`: Theorem 1 of Mazur and Ullom for a
  frame of quadratic units of subtype `t`.

## Main results

* `NumberField.Units.finrank_modTorsion_eq_three`: the units modulo torsion of a real biquadratic
  field have rank `3`.
* `NumberField.Units.existsUnique_isMazurUllomBasicType`: every real biquadratic field has exactly
  one basic type.
* `NumberField.Units.IsMazurUllomBasicType.exists_equiv`: **Theorem 1 of Mazur and Ullom.**
* `NumberField.Units.isMazurUllomBasicType_iff`: **the basic type is the isomorphism class of the
  Galois module `U/{±1}`.**
* `NumberField.Units.exists_equiv_iff`: **two real biquadratic fields have isomorphic Galois
  modules iff they have the same basic type.**

## References

* M. Mazur and S. V. Ullom, *Galois module structure of units in real biquadratic number fields*,
  Acta Arith. 111 (2004), 105–124.
-/

open scoped NumberField

namespace NumberField.Units

open MazurUllomBasicType (kleinChar kleinSigma kleinChar_kleinSigma bijective_elim_kleinSigma)

variable {K : Type*} [Field K] [NumberField K]

@[nolint defsWithUnderscore]
instance : Module ℤ (Additive ((𝓞 K)ˣ ⧸ torsion K)) :=
  AddCommGroup.toIntModule (Additive ((𝓞 K)ˣ ⧸ torsion K))

@[nolint defsWithUnderscore]
noncomputable instance : MulDistribMulAction Gal(K/ℚ) ((𝓞 K)ˣ ⧸ torsion K) where
  smul σ := modTorsionMap σ
  one_smul x := by
    induction x using QuotientGroup.induction_on with
    | H u => exact congrArg QuotientGroup.mk (one_smul _ u)
  mul_smul σ τ x := by
    induction x using QuotientGroup.induction_on with
    | H u => exact congrArg QuotientGroup.mk (mul_smul σ τ u)
  smul_mul σ := map_mul (modTorsionMap σ)
  smul_one σ := map_one (modTorsionMap σ)

lemma smul_eq_modTorsionMap (σ : Gal(K/ℚ)) (x : (𝓞 K)ˣ ⧸ torsion K) : σ • x = modTorsionMap σ x :=
  rfl

variable (K) in
/-- The units modulo torsion of `K` as a `ℤ[Gal(K/ℚ)]`-module: the Galois group acting on
`Additive ((𝓞 K)ˣ ⧸ torsion K)`, which is `U/{±1}` written additively when `K` is real. -/
noncomputable abbrev modTorsionRep : Representation ℤ Gal(K/ℚ) (Additive ((𝓞 K)ˣ ⧸ torsion K)) :=
  Representation.ofMulDistribMulAction Gal(K/ℚ) ((𝓞 K)ˣ ⧸ torsion K)

variable (K) in
/-- The units of `K` have the **basic type** `T` of Mazur and Ullom: they have a subtype whose
roman numeral is `T`. Only meaningful for a real biquadratic field `K`, which has exactly one basic
type, and then it is the isomorphism class of the Galois module `U/{±1}`. -/
def IsMazurUllomBasicType (T : MazurUllomBasicType) : Prop :=
  ∃ t : MazurUllomType, t.basicType = T ∧ IsMazurUllomType K t

namespace QuadraticUnitFrame

variable [IsGalois ℚ K] [IsKleinFour Gal(K/ℚ)] (f : QuadraticUnitFrame K) (σ : Gal(K/ℚ)) (j : Fin 3)

lemma eq_one_or_exists_aut : σ = 1 ∨ ∃ i, f.aut i = σ := by
  by_contra! h
  exact h.2 2 <| f.aut_two.trans <| (IsKleinFour.eq_mul_of_ne_all (f.aut_ne_one 0) (f.aut_ne_one 1)
    (f.aut_injective.ne (by decide)) h.1 (fun h' ↦ h.2 0 h'.symm) fun h' ↦ h.2 1 h'.symm).symm

lemma bijective_elim_aut : Function.Bijective fun o : Option (Fin 3) ↦ o.elim 1 f.aut := by
  refine ⟨fun o o' h ↦ ?_, fun σ ↦ ?_⟩
  · rcases o with _ | i <;> rcases o' with _ | i'
    · rfl
    · exact absurd h.symm (f.aut_ne_one i')
    · exact absurd h (f.aut_ne_one i)
    · exact congrArg some (f.aut_injective h)
  · rcases f.eq_one_or_exists_aut σ with rfl | ⟨i, rfl⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some i, rfl⟩

/-- The isomorphism `Gal(K/ℚ) ≃* ℤˣ × ℤˣ` of the frame `f`: it sends the automorphism fixing the
`i`-th quadratic subfield of `f` to `σᵢ = kleinSigma i`. -/
noncomputable def kleinEquiv : Gal(K/ℚ) ≃* ℤˣ × ℤˣ :=
  IsKleinFour.mulEquiv ((Equiv.ofBijective _ f.bijective_elim_aut).symm.trans
    (Equiv.ofBijective _ bijective_elim_kleinSigma)) <|
      congrArg (Equiv.ofBijective _ bijective_elim_kleinSigma)
        (Equiv.ofBijective_symm_apply_apply _ f.bijective_elim_aut none)

lemma kleinEquiv_aut (i : Fin 3) : f.kleinEquiv (f.aut i) = kleinSigma i :=
  congrArg (Equiv.ofBijective _ bijective_elim_kleinSigma)
    (Equiv.ofBijective_symm_apply_apply _ f.bijective_elim_aut (some i))

lemma modTorsionMap_unitClass :
    modTorsionMap σ (f.unitClass j) = f.unitClass j ^ (kleinChar j (f.kleinEquiv σ) : ℤ) := by
  rcases f.eq_one_or_exists_aut σ with rfl | ⟨i, rfl⟩
  · rw [map_one, map_one, Units.val_one, zpow_one]
    exact one_smul Gal(K/ℚ) (f.unitClass j)
  · rw [f.kleinEquiv_aut, kleinChar_kleinSigma]
    split_ifs with hij
    · rw [Units.val_one, zpow_one, hij, f.modTorsionMap_aut_unitClass]
    · rw [Units.val_neg, Units.val_one, zpow_neg_one]
      exact eq_inv_of_mul_eq_one_right (α := (𝓞 K)ˣ ⧸ torsion K)
        (f.unitClass_mul_modTorsionMap_aut (Ne.symm hij))

lemma modTorsionMap_unitClass_zpow (n : ℤ) : modTorsionMap σ (f.unitClass j ^ n) =
    (f.unitClass j ^ n) ^ (kleinChar j (f.kleinEquiv σ) : ℤ) := by
  rw [map_zpow, f.modTorsionMap_unitClass]
  exact (zpow_mul (f.unitClass j) _ n).symm.trans (zpow_mul' (f.unitClass j) _ n)

variable [IsTotallyReal K] {t : MazurUllomType}

/-- **Theorem 1 of Mazur and Ullom, for a frame**: if the classes `ē₀, ē₁, ē₂` of the fundamental
units of the frame `f` have the subtype `t`, the units modulo torsion of `K` are isomorphic, as a
module over the Galois group, to the module of the basic type of `t`, along `f.kleinEquiv`, which
sends the automorphism fixing the `i`-th quadratic subfield to `σᵢ`. The isomorphism sends `x` to
the vector `v` with `x ^ 2 = ∏ i, (ēᵢ ^ t.scale i) ^ vᵢ`. -/
noncomputable def galoisModuleEquiv (ht : t.IsTypeOf f.unitClass) :
    (modTorsionRep K).Equiv (t.basicType.rep.comp f.kleinEquiv.toMonoidHom) :=
  haveI he : MazurUllomType.IsSquareBasis fun i ↦ f.unitClass i ^ t.scale i :=
    f.isSquareBasis_unitClass.rescale ht
  .mk (he.sqVecEquiv fun _ ↦ f.isSquareBasis_unitClass.isSquare_prod_rescale_iff ht) fun σ ↦
    LinearMap.ext fun x ↦ Subtype.ext <| he.sqVec_map x.toMul fun j ↦
      f.modTorsionMap_unitClass_zpow σ j (t.scale j)

end QuadraticUnitFrame

variable [IsGalois ℚ K] [IsKleinFour Gal(K/ℚ)] [IsTotallyReal K] {T : MazurUllomBasicType}

/-- **The units modulo torsion of a real biquadratic field have rank `3`**: `U/{±1}` has rank `3`
over `ℤ`, by Mathlib's Dirichlet unit theorem and `NumberField.Units.rank_eq_three`. -/
lemma finrank_modTorsion_eq_three : Module.finrank ℤ (Additive ((𝓞 K)ˣ ⧸ torsion K)) = 3 :=
  (finrank_modTorsion K).trans (rank_eq_three K)

/-- **Theorem 1 of Mazur and Ullom**: if a real biquadratic field `K` has the basic type `T`, its
units modulo torsion `U/{±1}` are isomorphic, as a `ℤ[Gal(K/ℚ)]`-module, to the module `T.rep` of
type `T`, along some isomorphism `Gal(K/ℚ) ≃* V₄` (any labelling of the quadratic subfields can be
used, up to an automorphism of `V₄`). -/
lemma IsMazurUllomBasicType.exists_equiv (h : IsMazurUllomBasicType K T) :
    ∃ φ : Gal(K/ℚ) ≃* ℤˣ × ℤˣ, Nonempty ((modTorsionRep K).Equiv (T.rep.comp φ.toMonoidHom)) := by
  rcases h with ⟨t, rfl, ht⟩
  rcases (isMazurUllomType_iff t).mp ht with ⟨f, hf⟩
  exact ⟨f.kleinEquiv, ⟨f.galoisModuleEquiv hf⟩⟩

/-- **Every real biquadratic field has exactly one basic type** I, II, III or IV. -/
lemma existsUnique_isMazurUllomBasicType : ∃! T, IsMazurUllomBasicType K T := by
  rcases existsUnique_isMazurUllomType (K := K) with ⟨t, ht, hu⟩
  exact ⟨t.basicType, ⟨t, rfl, ht⟩, fun T ⟨t', ht', h'⟩ ↦ ht'.symm.trans (congrArg _ (hu t' h'))⟩

/-- **The basic type is the isomorphism class of the Galois module** (Mazur and Ullom, Theorem 1
and Remark 1): a real biquadratic field `K` has the basic type `T` iff its units modulo torsion
`U/{±1}` are isomorphic, as a `ℤ[Gal(K/ℚ)]`-module, to the module `T.rep` along some isomorphism
`Gal(K/ℚ) ≃* V₄`. -/
lemma isMazurUllomBasicType_iff : IsMazurUllomBasicType K T ↔
    ∃ φ : Gal(K/ℚ) ≃* ℤˣ × ℤˣ, Nonempty ((modTorsionRep K).Equiv (T.rep.comp φ.toMonoidHom)) := by
  refine ⟨IsMazurUllomBasicType.exists_equiv, fun ⟨φ, ⟨e⟩⟩ ↦ ?_⟩
  rcases (existsUnique_isMazurUllomBasicType (K := K)).exists with ⟨T₀, h₀⟩
  rcases h₀.exists_equiv with ⟨φ₀, ⟨e₀⟩⟩
  rwa [T.eq_of_equiv_comp φ φ₀ (e.symm.trans e₀)]

variable {K' : Type*} [Field K'] [NumberField K'] [IsGalois ℚ K'] [IsKleinFour Gal(K'/ℚ)]
  [IsTotallyReal K']

/-- **Two real biquadratic fields have isomorphic Galois modules iff they have the same basic
type**: the units modulo torsion of `K` and `K'` are isomorphic, along some isomorphism
`ψ : Gal(K/ℚ) ≃* Gal(K'/ℚ)` of their Galois groups, iff `K` and `K'` have the same basic type. So
the basic type is an invariant of the Galois module, and determines it. -/
lemma exists_equiv_iff : (∃ ψ : Gal(K/ℚ) ≃* Gal(K'/ℚ),
    Nonempty ((modTorsionRep K).Equiv ((modTorsionRep K').comp ψ.toMonoidHom))) ↔
      ∀ T, IsMazurUllomBasicType K T ↔ IsMazurUllomBasicType K' T := by
  refine ⟨fun ⟨ψ, ⟨e⟩⟩ T₁ ↦ ?_, fun h ↦ ?_⟩
  · have key (T₂ : MazurUllomBasicType) (hT₂ : IsMazurUllomBasicType K' T₂) :
        IsMazurUllomBasicType K T₂ := by
      rcases hT₂.exists_equiv with ⟨φ', ⟨e'⟩⟩
      exact isMazurUllomBasicType_iff.mpr ⟨ψ.trans φ', ⟨e.trans <|
        .mk e'.toLinearEquiv fun σ ↦ e'.isIntertwining' (ψ σ)⟩⟩
    refine ⟨fun hK ↦ ?_, key T₁⟩
    rcases (existsUnique_isMazurUllomBasicType (K := K')).exists with ⟨T', hT'⟩
    rwa [(existsUnique_isMazurUllomBasicType (K := K)).unique hK (key T' hT')]
  · rcases (existsUnique_isMazurUllomBasicType (K := K)).exists with ⟨T₁, hT₁⟩
    rcases hT₁.exists_equiv with ⟨φ, ⟨e⟩⟩
    rcases ((h T₁).mp hT₁).exists_equiv with ⟨φ', ⟨e'⟩⟩
    refine ⟨φ.trans φ'.symm, ⟨.mk (e.toLinearEquiv.trans e'.symm.toLinearEquiv) fun σ ↦
      LinearMap.ext fun x ↦ ?_⟩⟩
    have h₁ : e.toLinearEquiv (modTorsionRep K σ x) = T₁.rep (φ σ) (e.toLinearEquiv x) :=
      LinearMap.congr_fun (e.isIntertwining' σ) x
    have h₂ : e'.symm.toLinearEquiv (T₁.rep (φ σ) (e.toLinearEquiv x)) =
        modTorsionRep K' (φ'.symm (φ σ)) (e'.symm.toLinearEquiv (e.toLinearEquiv x)) := by
      simpa using LinearMap.congr_fun (e'.symm.isIntertwining' (φ'.symm (φ σ))) (e.toLinearEquiv x)
    exact (congrArg e'.symm.toLinearEquiv h₁).trans h₂

end NumberField.Units
