import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.NumberTheory.Height.EllipticCurve
import Mathlib.NumberTheory.Height.NumberField
import TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Torsion growth of an elliptic curve in field extensions

Let `E` be an elliptic curve over a field `k` and `K` an extension of `k`. Base change embeds
`E(k)` in `E(K)` (`WeierstrassCurve.Affine.Point.baseChange`), and with it `E(k)_tors` in
`E(K)_tors`. There is **torsion growth** from `k` to `K` (LMFDB `ec.q.torsion_growth`, where
`k = ℚ` and `K` is a number field) when `E(K)_tors` is strictly larger than the image of
`E(k)_tors`, and the torsion growth in `K` is **primitive** when moreover `E(K)_tors` is strictly
larger than `E(K')_tors` for every proper subfield `K'` of `K` containing `k`; over `k = ℚ` these
are all the proper subfields of `K`. Here `E(k)` is the group of points of the base change `W⁄k`,
which is `W` itself.

## Main definitions

* `WeierstrassCurve.HasTorsionGrowth`: torsion growth from `k` to `K` (LMFDB `ec.q.torsion_growth`).
* `WeierstrassCurve.HasPrimitiveTorsionGrowth`: primitive torsion growth in `K`
  (LMFDB `ec.q.torsion_growth`).

## Main results

* `WeierstrassCurve.hasTorsionGrowth_iff`: there is torsion growth from `k` to `K` exactly when some
  torsion point of `E(K)` is not the base change of a point of `E(k)`.
* `WeierstrassCurve.HasTorsionGrowth.of_isScalarTower`: torsion growth in `K` persists in every
  extension of `K`.
* `WeierstrassCurve.hasTorsionGrowth_iff_natCard_lt`: over number fields, there is torsion growth
  from `k` to `K` exactly when `#E(k)_tors < #E(K)_tors`.
-/

open WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {k : Type*} [Field k] [DecidableEq k] (W : WeierstrassCurve k) (K : Type*) [Field K]
  [DecidableEq K] [Algebra k K]

/-- There is **torsion growth** from `k` to `K` (LMFDB `ec.q.torsion_growth`) if the torsion
subgroup `E(K)_tors` is strictly larger than the image of `E(k)_tors` under base change. -/
def HasTorsionGrowth : Prop :=
  (AddCommGroup.torsion (W⁄k).toAffine.Point).map (Point.baseChange k K) <
    AddCommGroup.torsion (W⁄K).toAffine.Point

/-- The torsion growth in `K` is **primitive** (LMFDB `ec.q.torsion_growth`) if there is torsion
growth from `k` to `K` and `E(K)_tors` is strictly larger than the image of `E(K')_tors` for every
proper subfield `K'` of `K` containing `k`. Over `k = ℚ`, these are all the proper subfields of
`K`. -/
def HasPrimitiveTorsionGrowth : Prop :=
  W.HasTorsionGrowth K ∧ ∀ K' : IntermediateField k K, K' ≠ ⊤ →
    (AddCommGroup.torsion (W⁄K').toAffine.Point).map (Point.map K'.val) <
    AddCommGroup.torsion (W⁄K).toAffine.Point

private lemma map_torsion_lt_torsion_iff {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {f : A →+ B} (hf : Function.Injective f) : (AddCommGroup.torsion A).map f < AddCommGroup.torsion
    B ↔ ∃ P : B, IsOfFinAddOrder P ∧ P ∉ Set.range f := by
  rw [IsConcreteLE.lt_iff_le_and_exists]
  constructor
  · rintro ⟨-, P, hP, hPf⟩
    refine ⟨P, hP, ?_⟩
    rintro ⟨Q, rfl⟩
    exact hPf ⟨Q, hf.isOfFinAddOrder_iff.mp hP, rfl⟩
  · rintro ⟨P, hP, hPf⟩
    refine ⟨AddCommGroup.map_torsion_le f, P, hP, ?_⟩
    rintro ⟨Q, -, rfl⟩
    exact hPf ⟨Q, rfl⟩

/-- **Torsion growth is a new torsion point**: there is torsion growth from `k` to `K` exactly when
some torsion point of `E(K)` is not the base change of a point of `E(k)`. -/
lemma hasTorsionGrowth_iff : W.HasTorsionGrowth K ↔ ∃ P : (W⁄K).toAffine.Point, IsOfFinAddOrder P ∧
    P ∉ Set.range (Point.baseChange k K) :=
  map_torsion_lt_torsion_iff (Point.map_injective (Algebra.ofId k K))

variable {W K} in
/-- **Torsion growth persists in extensions**: if there is torsion growth from `k` to `K`, then
there is torsion growth from `k` to every extension `L` of `K`. -/
lemma HasTorsionGrowth.of_isScalarTower {L : Type*} [Field L] [DecidableEq L] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] (h : W.HasTorsionGrowth K) : W.HasTorsionGrowth L := by
  rcases (W.hasTorsionGrowth_iff K).mp h with ⟨P, hP, hPk⟩
  refine (W.hasTorsionGrowth_iff L).mpr
    ⟨_, (Point.map (IsScalarTower.toAlgHom k K L)).isOfFinAddOrder hP, ?_⟩
  rintro ⟨Q, hQ⟩
  rw [← Point.map_baseChange (IsScalarTower.toAlgHom k K L)] at hQ
  exact hPk ⟨Q, Point.map_injective _ hQ⟩

/-- **Over a number field, torsion growth is growth of the torsion order**: there is torsion growth
from `k` to a number field `K` exactly when `#E(k)_tors < #E(K)_tors`. -/
lemma hasTorsionGrowth_iff_natCard_lt [NumberField K] [W.IsElliptic] : W.HasTorsionGrowth K ↔
    Nat.card (AddCommGroup.torsion (W⁄k).toAffine.Point) < Nat.card (AddCommGroup.torsion
    (W⁄K).toAffine.Point) := by
  have : Finite (AddCommGroup.torsion (W⁄K).toAffine.Point) := finite_torsion
  rw [HasTorsionGrowth, ← AddSubgroup.card_map_of_injective
    (Point.map_injective (Algebra.ofId k K))]
  exact ⟨AddSubgroup.card_lt_of_lt,
    fun h ↦ lt_of_le_of_ne (AddCommGroup.map_torsion_le _) fun heq ↦ lt_irrefl _ (heq ▸ h)⟩

end WeierstrassCurve
