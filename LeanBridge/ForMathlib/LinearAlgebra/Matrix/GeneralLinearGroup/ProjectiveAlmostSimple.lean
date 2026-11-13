import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.AlmostSimple
import LeanBridge.ForMathlib.LinearAlgebra.Projectivization.PSLSimple
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# `PGL(n, q)` is almost simple

The projective general linear group `PGL(n, F) = GL(n, F) / {scalars}` contains the projective
special linear group `PSL(n, F) = SL(n, F) / Z(SL(n, F))` as a normal subgroup, through Mathlib's
`Matrix.ProjectiveSpecialLinearGroup.toPGL`, the image of `SL(n, F)` being normal as the kernel of
the determinant is. The centraliser of this subgroup is trivial: if the class of `g ∈ GL(n, F)`
commutes with that of a transvection `t`, then `t g = u g t` for a scalar `u`, and comparing the
column of `g` on which `t` acts trivially shows `u = 1` (otherwise that column vanishes); so `g`
commutes with every transvection and is a scalar matrix. A group with a non-abelian simple normal
subgroup `S` of trivial centraliser acts faithfully on `S` by conjugation, through automorphisms
that include the inner ones, so it lies between `S` and `Aut(S)`: it is almost simple. Hence
`PGL(n, F)` is almost simple whenever `PSL(n, F)` is simple: for `n ≥ 3`, and for `n = 2` when `F`
is finite with at least `4` elements (Jordan, Dickson).

Over a finite field `𝔽_q` the image of `PSL(n, q)` is all of `PGL(n, q)` exactly when every element
of `𝔽_q^×` is an `n`-th power (Mathlib's `Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_iff`), so
`PGL(n, q)` is itself simple exactly when the `n`-th power map of `𝔽_q^×` is onto, that is when
`gcd(n, q - 1) = 1`. These are the statements behind "often simple or almost simple" in LMFDB
`group.linear`: in the range above, `PGL(n, q)` is always almost simple, and simple exactly when
`gcd(n, q - 1) = 1`.

## Main results

* `Matrix.ProjectiveSpecialLinearGroup.centralizer_range_toPGL` (LMFDB `group.linear`): the image
  of `PSL(n, F)` in `PGL(n, F)` has trivial centraliser.
* `Matrix.ProjGenLinGroup.isAlmostSimple_of_isSimpleGroup` (LMFDB `group.linear`): `PGL(n, F)` is
  almost simple when `PSL(n, F)` is simple.
* `Matrix.ProjGenLinGroup.isAlmostSimple_fin` (LMFDB `group.linear`): `PGL(n, F)` is almost simple
  for `n ≥ 3`, and for `n = 2` when `|F| ≥ 4`.
* `Matrix.ProjGenLinGroup.isSimpleGroup_iff_coprime` (LMFDB `group.linear`): over a finite field,
  `PGL(n, q)` is simple, when `PSL(n, q)` is, exactly when `gcd(n, q - 1) = 1`.
* `Matrix.ProjGenLinGroup.isSimpleGroup_fin_iff` (LMFDB `group.linear`): for `n ≥ 3`, and for
  `n = 2` when `q ≥ 4`, `PGL(n, q)` is simple exactly when `gcd(n, q - 1) = 1`.

## References

* L. E. Dickson, *Linear groups, with an exposition of the Galois field theory* (1901).
-/

open Subgroup

open scoped MatrixGroups

variable {G : Type*} [Group G] {n : ℕ}

namespace Nat.Coprime

lemma of_forall_exists_pow_eq [Finite G] (h : ∀ r : G, ∃ k, k ^ n = r) :
    (Nat.card G).Coprime n := by
  refine Nat.coprime_of_dvd fun p hp hpG hpn ↦ ?_
  have : Fact p.Prime := ⟨hp⟩
  rcases exists_prime_orderOf_dvd_card' p hpG with ⟨x, hx⟩
  have hinj : Function.Injective (· ^ n : G → G) := Finite.injective_iff_surjective.mpr h
  have hx1 : x = 1 := hinj <| (orderOf_dvd_iff_pow_eq_one.mp (hx ▸ hpn)).trans (one_pow n).symm
  rw [hx1, orderOf_one] at hx
  exact hp.one_lt.ne hx

end Nat.Coprime

namespace Matrix

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]

lemma TransvectionStruct.eq_one_of_mul_mul_scalar_eq {t : TransvectionStruct ι F} {g : GL ι F}
    {u : F} (h : t.toMatrix * g * scalar ι u = g * t.toMatrix) : u = 1 := by
  by_contra hu
  have hz {x : F} (hx : x * u = x) : x = 0 :=
    (mul_eq_zero.mp (by linear_combination hx : x * (u - 1) = 0)).resolve_right (sub_ne_zero.mpr hu)
  have hcol (k : ι) (hk : k ≠ t.i) : (g : Matrix ι ι F) k t.i = 0 := by
    have hk' : (t.toMatrix * g * scalar ι u) k t.i = (g * t.toMatrix) k t.i :=
      congrFun (congrFun h k) t.i
    rw [scalar_apply, mul_diagonal, toMatrix, transvection_mul_apply_of_ne _ _ _ _ hk,
      mul_transvection_apply_of_ne _ _ _ _ t.hij] at hk'
    exact hz hk'
  have hii : (g : Matrix ι ι F) t.i t.i = 0 := by
    have hi : (t.toMatrix * g * scalar ι u) t.i t.i = (g * t.toMatrix) t.i t.i :=
      congrFun (congrFun h t.i) t.i
    rw [scalar_apply, mul_diagonal, toMatrix, transvection_mul_apply_same,
      mul_transvection_apply_of_ne _ _ _ _ t.hij, hcol t.j t.hij.symm, mul_zero, add_zero] at hi
    exact hz hi
  refine g.det.ne_zero ?_
  rw [GeneralLinearGroup.val_det_apply]
  exact det_eq_zero_of_column_eq_zero t.i fun k ↦ by
    rcases eq_or_ne k t.i with rfl | hk
    · exact hii
    · exact hcol k hk

namespace ProjectiveSpecialLinearGroup

lemma range_toPGL : (toPGL : _ →* PGL(ι, F)).range =
    (GeneralLinearGroup.det.ker : Subgroup (GL ι F)).map ProjGenLinGroup.mk := by
  rw [← SpecialLinearGroup.range_toGL_eq_ker_det, ← MonoidHom.range_comp]
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    induction s using QuotientGroup.induction_on with | H s => exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨QuotientGroup.mk s, rfl⟩

instance : (toPGL : _ →* PGL(ι, F)).range.Normal := by
  rw [range_toPGL]
  exact Normal.map inferInstance _ ProjGenLinGroup.mk_surjective

/-- **The image of `PSL(n, F)` in `PGL(n, F)` has trivial centraliser** (LMFDB `group.linear`): if
the class of `g ∈ GL(n, F)` commutes with that of a transvection `t`, then `t g = u g t` for a
scalar `u`, which must be `1`, so `g` commutes with every transvection and is a scalar matrix. -/
lemma centralizer_range_toPGL :
    centralizer ((toPGL : _ →* PGL(ι, F)).range : Set PGL(ι, F)) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  induction x using ProjGenLinGroup.induction_on with | mk g => ?_
  rw [mem_bot, ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  refine mem_range_scalar_of_commute_transvectionStruct fun t ↦ ?_
  have hs : ProjGenLinGroup.mk (SpecialLinearGroup.toGL t.toSpecialLinearGroup * g) =
      ProjGenLinGroup.mk (g * SpecialLinearGroup.toGL t.toSpecialLinearGroup) := by
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.mp hx _ ⟨QuotientGroup.mk t.toSpecialLinearGroup, rfl⟩
  rcases ProjGenLinGroup.mk_eq_mk_iff.mp hs with ⟨u, hu⟩
  have hu' : t.toMatrix * g * scalar ι (u : F) = g * t.toMatrix := by
    simpa only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix,
      TransvectionStruct.toSpecialLinearGroup_coe, GeneralLinearGroup.coe_scalar] using
      Units.ext_iff.mp hu
  rwa [TransvectionStruct.eq_one_of_mul_mul_scalar_eq hu', map_one, mul_one] at hu'

end ProjectiveSpecialLinearGroup

namespace ProjGenLinGroup

open ProjectiveSpecialLinearGroup

/-- **`PGL(n, F)` is almost simple when `PSL(n, F)` is simple** (LMFDB `group.linear`): the image of
`PSL(n, F)` is a simple normal subgroup of `PGL(n, F)` with trivial centraliser. -/
lemma isAlmostSimple_of_isSimpleGroup [IsSimpleGroup (ProjectiveSpecialLinearGroup ι F)] :
    IsAlmostSimple PGL(ι, F) :=
  have : IsSimpleGroup (toPGL : _ →* PGL(ι, F)).range :=
    (MonoidHom.ofInjective toPGL_injective).symm.isSimpleGroup
  IsAlmostSimple.of_centralizer_eq_bot centralizer_range_toPGL

/-- **`PGL(n, F)` is almost simple for `n ≥ 3`, and for `n = 2` when `F` has at least `4`
elements** (LMFDB `group.linear`): it lies between the simple group `PSL(n, F)` and its
automorphism group. The bound is on `Nat.card F`, so for `n = 2` the field is finite. Over
`F = 𝔽_q` this covers every `PGL(n, q)` with `n ≥ 2` other than `PGL(2, 2)` and `PGL(2, 3)`. -/
lemma isAlmostSimple_fin (hn : 2 ≤ n) (hF : n = 2 → 4 ≤ Nat.card F) : IsAlmostSimple PGL(n, F) :=
  have : IsSimpleGroup PSL(n, F) := ProjectiveSpecialLinearGroup.isSimpleGroup_fin hn hF
  isAlmostSimple_of_isSimpleGroup

variable [Finite F]

/-- **`PGL(n, q)` is simple exactly when `gcd(n, q - 1) = 1`**, when `PSL(n, q)` is simple (LMFDB
`group.linear`). The image of `PSL(n, q)` is a nontrivial normal subgroup, the whole group exactly
when every element of `𝔽_q^×` is an `n`-th power, which is the case exactly when the order
`q - 1` of `𝔽_q^×` is prime to `n`. -/
lemma isSimpleGroup_iff_coprime [Nontrivial ι] [IsSimpleGroup (ProjectiveSpecialLinearGroup ι F)] :
    IsSimpleGroup PGL(ι, F) ↔ (Nat.card F - 1).Coprime (Fintype.card ι) := by
  rw [← Nat.card_units]
  refine ⟨fun h ↦ .of_forall_exists_pow_eq (toPGL_surj_iff.mp ?_), fun h ↦ ?_⟩
  · refine MonoidHom.range_eq_top.mp <| (Normal.eq_bot_or_eq_top _).resolve_left fun hb ↦ ?_
    rcases exists_ne (1 : ProjectiveSpecialLinearGroup ι F) with ⟨x, hx⟩
    have hmem : toPGL x ∈ (toPGL : _ →* PGL(ι, F)).range := ⟨x, rfl⟩
    rw [hb, mem_bot, map_eq_one_iff _ toPGL_injective] at hmem
    exact hx hmem
  · have : Nontrivial PGL(ι, F) := toPGL_injective.nontrivial
    exact IsSimpleGroup.isSimpleGroup_of_surjective toPGL <|
      toPGL_surj_of_roots h.pow_left_bijective.2

/-- **`PGL(n, q)` is simple exactly when `gcd(n, q - 1) = 1`**, for `n ≥ 3`, and for `n = 2` when
`q ≥ 4` (LMFDB `group.linear`); it is almost simple in all these cases
(`Matrix.ProjGenLinGroup.isAlmostSimple_fin`). -/
lemma isSimpleGroup_fin_iff (hn : 2 ≤ n) (hF : n = 2 → 4 ≤ Nat.card F) :
    IsSimpleGroup PGL(n, F) ↔ (Nat.card F - 1).Coprime n := by
  have : IsSimpleGroup PSL(n, F) := ProjectiveSpecialLinearGroup.isSimpleGroup_fin hn hF
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [isSimpleGroup_iff_coprime, Fintype.card_fin]

end ProjGenLinGroup

end Matrix
