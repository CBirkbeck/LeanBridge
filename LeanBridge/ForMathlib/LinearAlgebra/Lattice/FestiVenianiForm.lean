import LeanBridge.ForMathlib.LinearAlgebra.Lattice.FestiVeniani
import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic

/-!
# The Festi–Veniani index and the discriminant form

The Festi–Veniani index (LMFDB `lattice.festi_veniani_index`) of an integral lattice `L` is, in the
knowl's words, the index of the automorphism group `O(L)` of `L` in the automorphism group of the
discriminant group `A_L = L^∨ / L`. The homomorphism `O(L) → Aut(A_L)` need not be injective, so
this is the index of its image, `TauCeti.IntegralLattice.festiVenianiIndex`. Festi and Veniani, who
count elliptic fibrations on K3 surfaces with it, write `O(L^♯)` for the group of automorphisms of
`A_L` that respect its bilinear or quadratic form, `O^♯(L)` for the image of `O(L)` in it, and use
the index `[O(L^♯) : O^♯(L)]`. This file formalises that reading.

For an even lattice `L`, Festi and Veniani's form is the discriminant quadratic form
`q_L : A_L → ℚ/2ℤ`, `q_L(x + L) = x² + 2ℤ`; its isometries also preserve its polar form, the
discriminant bilinear form `b_L : A_L × A_L → ℚ/ℤ`, `b_L(x + L, y + L) = x · y + ℤ`. Tau Ceti's
discriminant quadratic map is the half-norm `x²/2 + ℤ`, the image of `q_L` under the isomorphism
`ℚ/2ℤ ≅ ℚ/ℤ`, `t ↦ t/2`, so it has the same isometries. For an odd lattice `x² + 2ℤ` is not well
defined on `A_L` (Festi and Veniani only use even lattices), and we take the isometries of `b_L`. In
both cases `O(q_L)` is the group of automorphisms of `A_L` that preserve `b_L` and, if `L` is even,
`q_L`.

Every isometry of `L` induces an isometry of the discriminant form, which gives the homomorphism
`O(L) → O(q_L)` and the index `[O(q_L) : im O(L)]`. The literal index of the knowl is this index
times `[Aut(A_L) : O(q_L)]`, so the two readings agree exactly when every automorphism of `A_L`
preserves the discriminant form. They differ for the root lattice `A₄`: `A_L ≅ ℤ/5` with
`q_L(x) = 4x²/5`, `O(q_L) = {±1}` is the image of `O(L)` and `Aut(A_L)` has order `4`, so the
literal index is `2` and Festi and Veniani's is `1`; this example is not formalised.

## Main definitions

* `TauCeti.IntegralLattice.discriminantFormIsometries` (LMFDB `lattice.festi_veniani_index`): the
  isometry group `O(q_L)` of the discriminant form.
* `TauCeti.IntegralLattice.discriminantFormAction` (LMFDB `lattice.festi_veniani_index`): the
  homomorphism `O(L) → O(q_L)`.
* `TauCeti.IntegralLattice.discriminantFormIndex` (LMFDB `lattice.festi_veniani_index`): the
  Festi–Veniani index `[O(q_L) : im O(L)]`.

## Main results

* `TauCeti.IntegralLattice.mem_discriminantFormIsometries_iff_of_isEven`: for an even lattice,
  `O(q_L)` is the group of automorphisms of `A_L` that preserve `q_L`.
* `TauCeti.IntegralLattice.mem_discriminantFormIsometries_iff_of_not_isEven`: for an odd lattice, it
  is the group of automorphisms that preserve `b_L`.
* `TauCeti.IntegralLattice.festiVenianiIndex_eq_discriminantFormIndex_mul_index`: the literal index
  is `[O(q_L) : im O(L)] [Aut(A_L) : O(q_L)]`.
* `TauCeti.IntegralLattice.discriminantFormIndex_ne_zero`: the Festi–Veniani index of a
  nondegenerate lattice is finite.

## References

* D. Festi, D. C. Veniani, *Counting elliptic fibrations on K3 surfaces*, J. Math. Soc. Japan 75
  (2023), no. 4, 1195–1225, §2.1.
-/

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V) (e : Isometry L L)
  (hL : L.IsEven) (f : L.DiscriminantGroup ≃ₗ[ℤ] L.DiscriminantGroup) (x y : L.DiscriminantGroup)

/-- The **isometry group** `O(q_L)` (LMFDB `lattice.festi_veniani_index`) of the discriminant form
of an integral lattice `L`: the automorphisms of the discriminant group `A_L = L^∨ / L` that
preserve the discriminant bilinear form `b_L` and, if `L` is even, the discriminant quadratic form
`q_L`. For an even lattice this is Festi and Veniani's `O(L^♯)`
(`TauCeti.IntegralLattice.mem_discriminantFormIsometries_iff_of_isEven`); for an odd one, the
isometry group of `b_L`. -/
def discriminantFormIsometries : Subgroup (L.DiscriminantGroup ≃ₗ[ℤ] L.DiscriminantGroup) where
  carrier := {f | (∀ x y, L.discriminantPairing (f x) (f y) = L.discriminantPairing x y) ∧
    ∀ (hL : L.IsEven) x, L.discriminantQuadraticMap hL (f x) = L.discriminantQuadraticMap hL x}
  one_mem' := ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  mul_mem' {f g} hf hg :=
    ⟨fun x y ↦ (hf.1 (g x) (g y)).trans (hg.1 x y), fun hL x ↦ (hf.2 hL (g x)).trans (hg.2 hL x)⟩
  inv_mem' {f} hf := ⟨fun x y ↦ by simpa using (hf.1 (f.symm x) (f.symm y)).symm,
    fun hL x ↦ by simpa using (hf.2 hL (f.symm x)).symm⟩

variable {L} in
lemma Isometry.discriminantPairing_discriminantGroupEquiv :
    L.discriminantPairing (e.discriminantGroupEquiv x) (e.discriminantGroupEquiv y) =
      L.discriminantPairing x y := by
  rcases L.carrierInDual.mkQ_surjective x with ⟨x, rfl⟩
  rcases L.carrierInDual.mkQ_surjective y with ⟨y, rfl⟩
  simp only [Submodule.mkQ_apply, discriminantGroupEquiv_mk, discriminantPairing_mk,
    coe_dualCarrierEquiv_apply, e.map_app]

variable {L} in
lemma Isometry.discriminantQuadraticMap_discriminantGroupEquiv :
    L.discriminantQuadraticMap hL (e.discriminantGroupEquiv x) =
      L.discriminantQuadraticMap hL x := by
  rcases L.carrierInDual.mkQ_surjective x with ⟨x, rfl⟩
  simp only [Submodule.mkQ_apply, discriminantGroupEquiv_mk, discriminantQuadraticMap_mk,
    coe_dualCarrierEquiv_apply, e.map_app]

lemma range_discriminantGroupAction_le :
    L.discriminantGroupAction.range ≤ L.discriminantFormIsometries := by
  rintro _ ⟨e, rfl⟩
  exact ⟨e.discriminantPairing_discriminantGroupEquiv,
    fun hL ↦ e.discriminantQuadraticMap_discriminantGroupEquiv hL⟩

/-- The **homomorphism** `O(L) → O(q_L)` (LMFDB `lattice.festi_veniani_index`) from the automorphism
group of an integral lattice `L` to the isometry group of its discriminant form: an isometry `e` of
`L` acts on `A_L` by `u + L ↦ e(u) + L`. Its image is Festi and Veniani's `O^♯(L)`. -/
def discriminantFormAction : Isometry L L →* L.discriminantFormIsometries :=
  L.discriminantGroupAction.codRestrict _ fun e ↦ L.range_discriminantGroupAction_le ⟨e, rfl⟩

/-- The **Festi–Veniani index** (LMFDB `lattice.festi_veniani_index`) of an integral lattice `L` in
the sense of Festi and Veniani: the index `[O(q_L) : O^♯(L)]` of the image of the automorphism group
`O(L)` of `L` in the isometry group `O(q_L)` of its discriminant form, or `0` if it is infinite. -/
noncomputable def discriminantFormIndex : ℕ :=
  L.discriminantFormAction.range.index

/-- **For an even lattice, `O(q_L)` is the group of automorphisms of `A_L` that preserve the
discriminant quadratic form `q_L`**: they preserve its polar form `b_L`. This is Festi and Veniani's
`O(L^♯)`. -/
lemma mem_discriminantFormIsometries_iff_of_isEven : f ∈ L.discriminantFormIsometries ↔
    ∀ x, L.discriminantQuadraticMap hL (f x) = L.discriminantQuadraticMap hL x := by
  refine ⟨fun hf ↦ hf.2 hL, fun hf ↦ ⟨fun x y ↦ ?_, fun _ x ↦ hf x⟩⟩
  rw [← polar_discriminantQuadraticMap L hL, ← polar_discriminantQuadraticMap L hL,
    QuadraticMap.polar, QuadraticMap.polar, ← map_add, hf, hf, hf]

/-- **For an odd lattice, `O(q_L)` is the group of automorphisms of `A_L` that preserve the
discriminant bilinear form `b_L`.** -/
lemma mem_discriminantFormIsometries_iff_of_not_isEven (hodd : ¬L.IsEven) :
    f ∈ L.discriminantFormIsometries ↔
      ∀ x y, L.discriminantPairing (f x) (f y) = L.discriminantPairing x y :=
  ⟨fun hf ↦ hf.1, fun hf ↦ ⟨hf, fun h ↦ absurd h hodd⟩⟩

lemma discriminantFormIndex_eq_relIndex : L.discriminantFormIndex =
    L.discriminantGroupAction.range.relIndex L.discriminantFormIsometries := by
  rw [Subgroup.relIndex, MonoidHom.subgroupOf_range_eq_of_le _ L.range_discriminantGroupAction_le]
  rfl

/-- **The literal Festi–Veniani index `[Aut(A_L) : im O(L)]` is the Festi–Veniani index
`[O(q_L) : im O(L)]` times `[Aut(A_L) : O(q_L)]`.** -/
lemma festiVenianiIndex_eq_discriminantFormIndex_mul_index :
    L.festiVenianiIndex = L.discriminantFormIndex * L.discriminantFormIsometries.index := by
  rw [discriminantFormIndex_eq_relIndex, festiVenianiIndex,
    Subgroup.relIndex_mul_index L.range_discriminantGroupAction_le]

/-- **The Festi–Veniani index of a nondegenerate lattice is finite.** -/
lemma discriminantFormIndex_ne_zero [L.IsNondegenerate] : L.discriminantFormIndex ≠ 0 :=
  left_ne_zero_of_mul <| L.festiVenianiIndex_eq_discriminantFormIndex_mul_index ▸
    L.festiVenianiIndex_ne_zero

end TauCeti.IntegralLattice
