import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

/-!
# The dihedral group as the symmetry group of a regular polygon

The regular `n`-gon inscribed in the unit circle of the Euclidean plane `ℂ` is the convex hull of
the `n`-th roots of unity. Its symmetries are the isometries of `ℂ` mapping it onto itself, under
composition. For `n ≥ 2` they form a group isomorphic to the dihedral group `Dₙ` (LMFDB
`group.dihedral`): the `n` rotations `z ↦ ζᵏ z` and the `n` reflections `z ↦ conj (ζᵏ z)`, for
`ζ = e^{2πi/n}`. A symmetry permutes the vertices, the extreme points of the polygon, since it is
affine (Mazur–Ulam); it fixes their average `0`, so it is a linear isometry of `ℂ`, `z ↦ a z` or
`z ↦ a conj z`, with `a` the image of the vertex `1`.

## Main definitions

* `regularPolygon`: the regular `n`-gon, the convex hull of the `n`-th roots of unity.
* `regularPolygonSymmetries` (LMFDB `group.dihedral`): the symmetry group of the regular `n`-gon.
* `regularPolygonSymmetriesMulEquiv` (LMFDB `group.dihedral`): `Dₙ ≃* Sym(regular n-gon)`.
-/

open Complex ComplexConjugate Metric Real Set

variable (n : ℕ)

/-- The vertices of the regular `n`-gon inscribed in the unit circle of `ℂ`: the `n`-th roots of
unity `e^{2πik/n}`. -/
def regularPolygonVertices : Set ℂ :=
  {z | z ^ n = 1}

/-- The regular `n`-gon inscribed in the unit circle of the Euclidean plane `ℂ`, as a closed region:
the convex hull of its vertices, the `n`-th roots of unity. -/
noncomputable def regularPolygon : Set ℂ :=
  convexHull ℝ (regularPolygonVertices n)

/-- The **symmetry group of the regular `n`-gon** (LMFDB `group.dihedral`): the isometries of the
Euclidean plane `ℂ` mapping `regularPolygon n` onto itself, under composition. -/
def regularPolygonSymmetries : Subgroup (ℂ ≃ᵢ ℂ) where
  carrier := {f | f '' regularPolygon n = regularPolygon n}
  mul_mem' {f g} hf hg := (image_comp f g _).trans ((congrArg (image f) hg).trans hf)
  one_mem' := image_id _
  inv_mem' {f} hf := (congrArg (image ⇑f⁻¹) hf).symm.trans (f.symm_image_image _)

/-- The rotation `z ↦ a z` of the Euclidean plane `ℂ` by an element `a` of the unit circle, as an
isometry. -/
noncomputable def rotationIsometryEquiv : Circle →* ℂ ≃ᵢ ℂ where
  toFun a := (rotation a).toIsometryEquiv
  map_one' := by
    ext z
    simp
  map_mul' a b := by
    ext z
    simp

variable {n} {f : ℂ ≃ᵢ ℂ} (s : Set ℂ) {a : Circle}

lemma mem_regularPolygonSymmetries :
    f ∈ regularPolygonSymmetries n ↔ f '' regularPolygon n = regularPolygon n :=
  Iff.rfl

lemma image_convexHull_isometryEquiv : f '' convexHull ℝ s = convexHull ℝ (f '' s) := by
  simpa using f.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap.image_convexHull s

lemma image_extremePoints_subset_isometryEquiv :
    f '' extremePoints ℝ s ⊆ extremePoints ℝ (f '' s) := by
  rintro - ⟨x, hx, rfl⟩
  refine ⟨mem_image_of_mem f hx.1, ?_⟩
  rintro - ⟨y, hy, rfl⟩ - ⟨z, hz, rfl⟩ hxyz
  have h : f '' openSegment ℝ y z = openSegment ℝ (f y) (f z) := by
    simpa using image_openSegment ℝ f.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap y z
  rw [← h, f.injective.mem_set_image] at hxyz
  rw [hx.2 hy hz hxyz]

lemma extremePoints_regularPolygon (hn : n ≠ 0) :
    extremePoints ℝ (regularPolygon n) = regularPolygonVertices n := by
  refine extremePoints_convexHull_subset.antisymm fun z hz ↦
    inter_extremePoints_subset_extremePoints_of_subset
      (convexHull_min (fun w hw ↦ ?_) (convex_closedBall 0 1))
      ⟨subset_convexHull ℝ _ hz, StrictConvexSpace.sphere_subset_extremePoints_closedBall 0
        one_ne_zero ?_⟩
  · exact mem_closedBall_zero_iff.mpr (norm_eq_one_of_pow_eq_one hw hn).le
  · exact mem_sphere_zero_iff_norm.mpr (norm_eq_one_of_pow_eq_one hz hn)

lemma finite_regularPolygonVertices (hn : n ≠ 0) : (regularPolygonVertices n).Finite :=
  (Polynomial.nthRootsFinset n (1 : ℂ)).finite_toSet.subset fun _ hz ↦
    (Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hn) 1).mpr hz

lemma image_regularPolygonVertices (hn : n ≠ 0) (hf : f ∈ regularPolygonSymmetries n) :
    f '' regularPolygonVertices n = regularPolygonVertices n := by
  refine eq_of_subset_of_ncard_le ?_ (ncard_image_of_injective _ f.injective).ge
    (finite_regularPolygonVertices hn)
  rw [← extremePoints_regularPolygon hn]
  exact (image_extremePoints_subset_isometryEquiv _).trans (congrArg (extremePoints ℝ) hf).subset

lemma mem_regularPolygonSymmetries_of_mapsTo (hn : n ≠ 0) (hf : ∀ z : ℂ, z ^ n = 1 → f z ^ n = 1) :
    f ∈ regularPolygonSymmetries n := by
  have h : f '' regularPolygonVertices n = regularPolygonVertices n :=
    eq_of_subset_of_ncard_le (image_subset_iff.mpr hf) (ncard_image_of_injective _ f.injective).ge
      (finite_regularPolygonVertices hn)
  rw [mem_regularPolygonSymmetries, regularPolygon, image_convexHull_isometryEquiv, h]

lemma map_zero_of_mem_regularPolygonSymmetries (hn : 2 ≤ n) (hf : f ∈ regularPolygonSymmetries n) :
    f 0 = 0 := by
  have hn0 : n ≠ 0 := by omega
  have : NeZero n := ⟨hn0⟩
  have hζ : IsPrimitiveRoot (exp (2 * π * I / n)) n := isPrimitiveRoot_exp n hn0
  have hinj : InjOn (exp (2 * π * I / n) ^ ·) (Finset.range n) := fun i hi j hj h ↦
    hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h
  let T : Finset ℂ := (Finset.range n).image (exp (2 * π * I / n) ^ ·)
  have hT : (T : Set ℂ) = regularPolygonVertices n := by
    ext z
    simp only [T, Finset.coe_image, Finset.coe_range]
    constructor
    · rintro ⟨i, -, rfl⟩
      exact (pow_right_comm _ _ _).trans (by rw [hζ.pow_eq_one, one_pow])
    · intro hz
      rcases hζ.eq_pow_of_pow_eq_one hz with ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
  have hsum : ∑ v ∈ T, v = 0 := by
    rw [Finset.sum_image hinj]
    exact hζ.geom_sum_eq_zero (by omega)
  have hTf : T.image f = T := Finset.coe_injective <| by
    rw [Finset.coe_image, hT]
    exact image_regularPolygonVertices hn0 hf
  have hsumf : ∑ v ∈ T, f v = 0 := by
    rw [← Finset.sum_image (f := fun x ↦ x) fun x _ y _ h ↦ f.injective h, hTf, hsum]
  have hdec (z : ℂ) : f z = f.toRealAffineIsometryEquiv.linearIsometryEquiv z + f 0 := by
    simpa using f.toRealAffineIsometryEquiv.map_vadd 0 z
  have h : ∑ v ∈ T, f v = n • f 0 := by
    rw [Finset.sum_congr rfl fun z _ ↦ hdec z, Finset.sum_add_distrib, ← map_sum, hsum, map_zero,
      zero_add, Finset.sum_const, Finset.card_image_of_injOn hinj, Finset.card_range]
  rw [hsumf, nsmul_eq_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (Nat.cast_ne_zero.mpr hn0)

lemma coe_circleExp : (Circle.exp (2 * π / n) : ℂ) = exp (2 * π * I / n) := by
  rw [Circle.coe_exp]
  congr 1
  push_cast
  ring1

lemma isPrimitiveRoot_circleExp (hn : n ≠ 0) : IsPrimitiveRoot (Circle.exp (2 * π / n) : ℂ) n := by
  rw [coe_circleExp]
  exact isPrimitiveRoot_exp n hn

lemma conjLIE_mul_self : conjLIE.toIsometryEquiv * conjLIE.toIsometryEquiv = 1 := by
  ext z
  simp

variable (a) in
lemma conjLIE_mul_rotationIsometryEquiv_mul_self :
    conjLIE.toIsometryEquiv * rotationIsometryEquiv a *
      (conjLIE.toIsometryEquiv * rotationIsometryEquiv a) = 1 := by
  ext z
  simp [rotationIsometryEquiv, ← Circle.coe_inv_eq_conj]

lemma injective_rotationIsometryEquiv : Function.Injective rotationIsometryEquiv := fun a b h ↦
  Circle.coe_injective <| by simpa [rotationIsometryEquiv] using DFunLike.congr_fun h 1

lemma conjLIE_ne_one : conjLIE.toIsometryEquiv ≠ 1 := fun h ↦ by
  simpa [CharZero.neg_eq_self_iff] using DFunLike.congr_fun h I

lemma conjLIE_mul_rotationIsometryEquiv_ne_one (ha : a ≠ 1) :
    conjLIE.toIsometryEquiv * rotationIsometryEquiv a ≠ 1 := fun h ↦
  ha <| Circle.coe_injective <| by
    simpa [rotationIsometryEquiv] using congrArg conj (DFunLike.congr_fun h 1)

lemma conjLIE_mem_regularPolygonSymmetries (hn : n ≠ 0) :
    conjLIE.toIsometryEquiv ∈ regularPolygonSymmetries n :=
  mem_regularPolygonSymmetries_of_mapsTo hn fun z hz ↦ by
    simp [← map_pow, hz]

lemma rotationIsometryEquiv_mem_regularPolygonSymmetries (hn : n ≠ 0) (ha : (a : ℂ) ^ n = 1) :
    rotationIsometryEquiv a ∈ regularPolygonSymmetries n :=
  mem_regularPolygonSymmetries_of_mapsTo hn fun z hz ↦ by
    simp [rotationIsometryEquiv, mul_pow, ha, hz]

lemma orderOf_conjLIE_mul_conjLIE_mul_rotationIsometryEquiv (hn : n ≠ 0) :
    orderOf (conjLIE.toIsometryEquiv *
      (conjLIE.toIsometryEquiv * rotationIsometryEquiv (Circle.exp (2 * π / n)))) = n := by
  rw [← mul_assoc, conjLIE_mul_self, one_mul,
    orderOf_injective rotationIsometryEquiv injective_rotationIsometryEquiv,
    ← orderOf_injective Circle.coeHom Circle.coe_injective]
  exact (isPrimitiveRoot_circleExp hn).eq_orderOf.symm

lemma circleExp_ne_one (hn : 2 ≤ n) : Circle.exp (2 * π / n) ≠ 1 := fun h ↦
  (isPrimitiveRoot_circleExp (by omega : n ≠ 0)).ne_one (by omega) (by rw [h, Circle.coe_one])

lemma rotationIsometryEquiv_mem_closure (hn : n ≠ 0) (ha : (a : ℂ) ^ n = 1) :
    rotationIsometryEquiv a ∈ Subgroup.closure {conjLIE.toIsometryEquiv,
      conjLIE.toIsometryEquiv * rotationIsometryEquiv (Circle.exp (2 * π / n))} := by
  have : NeZero n := ⟨hn⟩
  rcases (isPrimitiveRoot_circleExp hn).eq_pow_of_pow_eq_one ha with ⟨k, -, hk⟩
  have hak : a = Circle.exp (2 * π / n) ^ k := Circle.coe_injective <| by
    rw [Circle.coe_pow, hk]
  rw [hak, map_pow]
  exact pow_mem ((Subgroup.mul_mem_cancel_left _ (Subgroup.subset_closure (mem_insert _ _))).mp
    (Subgroup.subset_closure (mem_insert_of_mem _ rfl))) k

lemma mem_closure_of_mem_regularPolygonSymmetries (hn : 2 ≤ n)
    (hf : f ∈ regularPolygonSymmetries n) : f ∈ Subgroup.closure {conjLIE.toIsometryEquiv,
      conjLIE.toIsometryEquiv * rotationIsometryEquiv (Circle.exp (2 * π / n))} := by
  have hn0 : n ≠ 0 := by omega
  have h0 : f 0 = 0 := map_zero_of_mem_regularPolygonSymmetries hn hf
  have h1 : f 1 ^ n = 1 :=
    (image_regularPolygonVertices hn0 hf).subset (mem_image_of_mem f (one_pow n))
  rcases linear_isometry_complex (f.toRealLinearIsometryEquivOfMapZero h0) with ⟨a, ha | ha⟩
  · have hfa : f = rotationIsometryEquiv a := by
      ext z
      simpa [rotationIsometryEquiv] using DFunLike.congr_fun ha z
    rw [hfa] at h1 ⊢
    exact rotationIsometryEquiv_mem_closure hn0 (by simpa [rotationIsometryEquiv] using h1)
  · have hfa : f = rotationIsometryEquiv a * conjLIE.toIsometryEquiv := by
      ext z
      simpa [rotationIsometryEquiv] using DFunLike.congr_fun ha z
    rw [hfa] at h1 ⊢
    refine mul_mem (rotationIsometryEquiv_mem_closure hn0 ?_)
      (Subgroup.subset_closure (mem_insert _ _))
    simpa [rotationIsometryEquiv] using h1

lemma closure_eq_regularPolygonSymmetries (hn : 2 ≤ n) :
    Subgroup.closure {conjLIE.toIsometryEquiv,
      conjLIE.toIsometryEquiv * rotationIsometryEquiv (Circle.exp (2 * π / n))} =
      regularPolygonSymmetries n := by
  have hn0 : n ≠ 0 := by omega
  refine le_antisymm ((Subgroup.closure_le _).mpr (insert_subset_iff.mpr
    ⟨conjLIE_mem_regularPolygonSymmetries hn0, singleton_subset_iff.mpr
      (mul_mem (conjLIE_mem_regularPolygonSymmetries hn0)
        (rotationIsometryEquiv_mem_regularPolygonSymmetries hn0
          (isPrimitiveRoot_circleExp hn0).pow_eq_one))⟩))
    fun f hf ↦ mem_closure_of_mem_regularPolygonSymmetries hn hf

/-- **The dihedral group `Dₙ` is the symmetry group of the regular `n`-gon** (LMFDB
`group.dihedral`), for `n ≥ 2`: the rotation `r i` acts as the rotation `z ↦ e^{2πii/n} z` and the
reflection `sr i` as the reflection `z ↦ conj (e^{2πii/n} z)`. -/
noncomputable def regularPolygonSymmetriesMulEquiv (hn : 2 ≤ n) :
    DihedralGroup n ≃* regularPolygonSymmetries n :=
  (MonoidHom.ofInjective (TauCeti.dihedralHom_injective conjLIE_mul_self
    (conjLIE_mul_rotationIsometryEquiv_mul_self _) conjLIE_ne_one
    (conjLIE_mul_rotationIsometryEquiv_ne_one (circleExp_ne_one hn))
    (orderOf_conjLIE_mul_conjLIE_mul_rotationIsometryEquiv (by omega)))).trans
    (MulEquiv.subgroupCongr ((TauCeti.range_dihedralHom _ _ _).trans
      (closure_eq_regularPolygonSymmetries hn)))

lemma regularPolygonSymmetriesMulEquiv_r (hn : 2 ≤ n) (i : ZMod n) (z : ℂ) :
    (regularPolygonSymmetriesMulEquiv hn (.r i) : ℂ ≃ᵢ ℂ) z = exp (2 * π * I / n) ^ i.val * z := by
  have : NeZero n := ⟨by omega⟩
  simp only [regularPolygonSymmetriesMulEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply, TauCeti.dihedralHom_r]
  rw [← mul_assoc, conjLIE_mul_self, one_mul, ZMod.cast_eq_val, zpow_natCast, ← map_pow,
    ← coe_circleExp, ← Circle.coe_pow]
  exact rotation_apply _ z

lemma regularPolygonSymmetriesMulEquiv_sr (hn : 2 ≤ n) (i : ZMod n) (z : ℂ) :
    (regularPolygonSymmetriesMulEquiv hn (.sr i) : ℂ ≃ᵢ ℂ) z =
      conj (exp (2 * π * I / n) ^ i.val * z) := by
  have : NeZero n := ⟨by omega⟩
  simp only [regularPolygonSymmetriesMulEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply, TauCeti.dihedralHom_sr]
  rw [← mul_assoc conjLIE.toIsometryEquiv, conjLIE_mul_self, one_mul, ZMod.cast_eq_val,
    zpow_natCast, ← map_pow, ← coe_circleExp, ← Circle.coe_pow]
  exact congrArg conj (rotation_apply _ z)

lemma nat_card_regularPolygonSymmetries (hn : 2 ≤ n) :
    Nat.card (regularPolygonSymmetries n) = 2 * n :=
  (Nat.card_congr (regularPolygonSymmetriesMulEquiv hn).toEquiv).symm.trans DihedralGroup.nat_card
