import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.ZMod
import TauCeti.Topology.Algebra.Group.Profinite.ZHat.ZMod

/-!
# `GL₂(ℤ̂)` is the inverse limit of the groups `GL₂(ℤ/nℤ)`

The finite groups `GL₂(ℤ/nℤ)`, `n ≥ 1`, ordered by divisibility with the reduction maps
`GL₂(ℤ/nℤ) → GL₂(ℤ/mℤ)` for `m ∣ n`, form an inverse system; its inverse limit (LMFDB
`gl2.profinite`), the group of compatible families in `∏_n GL₂(ℤ/nℤ)` with the topology induced by
the discrete topologies, is a profinite group. It is isomorphic, as a topological group, to the
group of invertible `2 × 2` matrices over the topological ring `ℤ̂` of profinite integers, Tau
Ceti's `TauCeti.zHat` (in its additive form, a ring), itself the inverse limit of the finite rings
`ℤ/nℤ` (`TauCeti.zHat.existsUnique_forall_toZMod_eq`). The isomorphism reduces a matrix modulo
every `n`. It is injective because a profinite integer is determined by its reductions, and
surjective because a compatible family of matrices has compatible entries, and so do the inverse
matrices; it is continuous, and `GL₂(ℤ̂)` is compact, so it is a homeomorphism.

## Main definitions

* `Matrix.GeneralLinearGroup.gl2ZModLimit` (LMFDB `gl2.profinite`): the inverse limit of the
  `GL₂(ℤ/nℤ)`, and `Matrix.GeneralLinearGroup.gl2ZModLimitProfiniteGrp`, the same as a profinite
  group.
* `Matrix.GeneralLinearGroup.gl2ZHatToLimit`: reduction modulo every `n`, `GL₂(ℤ̂) → lim GL₂(ℤ/nℤ)`.
* `Matrix.GeneralLinearGroup.gl2ZHatContinuousMulEquiv` (LMFDB `gl2.profinite`): the isomorphism of
  topological groups `GL₂(ℤ̂) ≃ lim GL₂(ℤ/nℤ)`.

## Main results

* `Matrix.GeneralLinearGroup.isClosed_gl2ZModLimit`: the inverse limit is closed in the product.
* `Matrix.GeneralLinearGroup.continuous_gl2ZHatToLimit`: reduction modulo every `n` is continuous.
* `Matrix.GeneralLinearGroup.gl2ZHatToLimit_bijective` (LMFDB `gl2.profinite`): it is bijective.
-/

open Matrix TauCeti

namespace Matrix.GeneralLinearGroup

universe u

/-- The **inverse limit** `lim_n GL₂(ℤ/nℤ)` (LMFDB `gl2.profinite`) of the finite groups
`GL₂(ℤ/nℤ)`, `n ≥ 1`, ordered by divisibility, along the reduction maps `GL₂(ℤ/nℤ) → GL₂(ℤ/mℤ)` for
`m ∣ n`: the subgroup of the families in `∏_n GL₂(ℤ/nℤ)` compatible with the reduction maps, with
the topology induced by the discrete topologies of the `GL₂(ℤ/nℤ)`. -/
def gl2ZModLimit : Subgroup (∀ n : ℕ+, GL (Fin 2) (ZMod n)) where
  carrier := {x | ∀ (m n : ℕ+) (h : (m : ℕ) ∣ n), map (ZMod.castHom h (ZMod m)) (x n) = x m}
  mul_mem' {x y} hx hy m n h := by
    rw [Pi.mul_apply, map_mul, hx m n h, hy m n h, Pi.mul_apply]
  one_mem' m n h := map_one _
  inv_mem' {x} hx m n h := by
    rw [Pi.inv_apply, map_inv, hx m n h, Pi.inv_apply]

lemma mem_gl2ZModLimit {x : ∀ n : ℕ+, GL (Fin 2) (ZMod n)} :
    x ∈ gl2ZModLimit ↔ ∀ (m n : ℕ+) (h : (m : ℕ) ∣ n), map (ZMod.castHom h (ZMod m)) (x n) = x m :=
  Iff.rfl

/-- **The inverse limit of the `GL₂(ℤ/nℤ)` is closed in their product**: each compatibility
condition is an equation between continuous maps to a discrete group. -/
lemma isClosed_gl2ZModLimit : IsClosed (gl2ZModLimit : Set (∀ n : ℕ+, GL (Fin 2) (ZMod n))) := by
  have h : (gl2ZModLimit : Set (∀ n : ℕ+, GL (Fin 2) (ZMod n))) = ⋂ (m : ℕ+) (n : ℕ+)
      (h : (m : ℕ) ∣ n), {x | map (ZMod.castHom h (ZMod m)) (x n) = x m} := by
    ext x
    simp [mem_gl2ZModLimit]
  rw [h]
  exact isClosed_iInter fun m ↦ isClosed_iInter fun n ↦ isClosed_iInter fun h ↦ isClosed_eq
    (continuous_of_discreteTopology.comp (continuous_pi_iff.mp continuous_id n))
    (continuous_pi_iff.mp continuous_id m)

instance : CompactSpace gl2ZModLimit :=
  isCompact_iff_compactSpace.mp isClosed_gl2ZModLimit.isCompact

/-- The inverse limit `lim_n GL₂(ℤ/nℤ)` (LMFDB `gl2.profinite`) as a **profinite group**: a closed
subgroup of a product of finite discrete groups, so a compact totally disconnected topological
group. -/
noncomputable def gl2ZModLimitProfiniteGrp : ProfiniteGrp :=
  .of gl2ZModLimit

/-- **Reduction modulo every `n`**, `GL₂(ℤ̂) → lim_n GL₂(ℤ/nℤ)`, `ℤ̂` being Tau Ceti's ring of
profinite integers `Additive zHat`: the family of the reductions `GL₂(ℤ̂) → GL₂(ℤ/nℤ)`, which is
compatible with the reduction maps. -/
noncomputable def gl2ZHatToLimit : GL (Fin 2) (Additive zHat.{u}) →* gl2ZModLimit :=
  (MonoidHom.pi fun n : ℕ+ ↦ map (zHat.toZMod n)).codRestrict gl2ZModLimit fun g _ _ h ↦
    congrArg (fun f ↦ map f g) (zHat.castHom_comp_toZMod h)

lemma continuous_map_toZMod (n : ℕ+) :
    Continuous (map (zHat.toZMod n) : GL (Fin 2) (Additive zHat.{u}) → GL (Fin 2) (ZMod n)) := by
  refine Units.continuous_iff.mpr ⟨Units.continuous_val.matrix_map (zHat.continuous_toZMod n),
    (Units.continuous_coe_inv.matrix_map (zHat.continuous_toZMod n)).congr fun g ↦ ?_⟩
  rw [← map_inv]
  rfl

/-- **Reduction modulo every `n` is continuous** on `GL₂(ℤ̂)`. -/
lemma continuous_gl2ZHatToLimit : Continuous (gl2ZHatToLimit.{u}) :=
  (continuous_pi continuous_map_toZMod).subtype_mk _

lemma gl2ZHatToLimit_injective : Function.Injective (gl2ZHatToLimit.{u}) := fun _ _ h ↦
  Units.ext <| Matrix.ext fun i j ↦ zHat.ext_of_toZMod fun n ↦
    congrArg (fun x : gl2ZModLimit ↦ ((x : ∀ n : ℕ+, GL (Fin 2) (ZMod n)) n :
      Matrix (Fin 2) (Fin 2) (ZMod n)) i j) h

lemma exists_forall_toZMod_eq_apply (y : ∀ n : ℕ+, Matrix (Fin 2) (Fin 2) (ZMod n))
    (hy : ∀ (m n : ℕ+) (h : (m : ℕ) ∣ n), (y n).map (ZMod.castHom h (ZMod m)) = y m) (i j : Fin 2) :
    ∃ a : Additive zHat.{u}, ∀ n : ℕ+, zHat.toZMod n a = y n i j :=
  (zHat.existsUnique_forall_toZMod_eq (fun n ↦ y n i j) fun m n h ↦
    congrFun (congrFun (hy m n h) i) j).exists

lemma gl2ZHatToLimit_surjective : Function.Surjective (gl2ZHatToLimit.{u}) := by
  rintro ⟨x, hx⟩
  choose a ha using exists_forall_toZMod_eq_apply.{u} (fun n ↦ (x n : Matrix (Fin 2) (Fin 2)
    (ZMod n))) fun m n h ↦ congrArg Units.val (hx m n h)
  choose b hb using exists_forall_toZMod_eq_apply.{u} (fun n ↦ (((x n)⁻¹ : GL (Fin 2) (ZMod n)) :
    Matrix (Fin 2) (Fin 2) (ZMod n))) fun m n h ↦
      congrArg Units.val ((map_inv _ _).trans (congrArg Inv.inv (hx m n h)))
  have hA (n : ℕ+) : (Matrix.of a).map (zHat.toZMod n) = (x n : Matrix (Fin 2) (Fin 2) (ZMod n)) :=
    Matrix.ext fun i j ↦ ha i j n
  have hB (n : ℕ+) : (Matrix.of b).map (zHat.toZMod n) =
      (((x n)⁻¹ : GL (Fin 2) (ZMod n)) : Matrix (Fin 2) (Fin 2) (ZMod n)) :=
    Matrix.ext fun i j ↦ hb i j n
  have hmul {M N : Matrix (Fin 2) (Fin 2) (Additive zHat.{u})}
      (h : ∀ n : ℕ+, (M * N).map (zHat.toZMod n) = 1) : M * N = 1 :=
    Matrix.ext fun i j ↦ zHat.ext_of_toZMod fun n ↦ by
      rw [← Matrix.map_apply (f := zHat.toZMod n), h n, ← Matrix.map_apply (f := zHat.toZMod n),
        Matrix.map_one _ (map_zero _) (map_one _)]
  have hAB : Matrix.of a * Matrix.of b = 1 :=
    hmul fun n ↦ by rw [Matrix.map_mul, hA, hB, Units.mul_inv]
  have hBA : Matrix.of b * Matrix.of a = 1 :=
    hmul fun n ↦ by rw [Matrix.map_mul, hA, hB, Units.inv_mul]
  exact ⟨⟨Matrix.of a, Matrix.of b, hAB, hBA⟩, Subtype.ext <| funext fun n ↦ Units.ext (hA n)⟩

/-- **Reduction modulo every `n` is a bijection** `GL₂(ℤ̂) → lim_n GL₂(ℤ/nℤ)` (LMFDB
`gl2.profinite`): a profinite integer is determined by its reductions, and a compatible family of
matrices, with their inverses, has compatible entries. -/
lemma gl2ZHatToLimit_bijective : Function.Bijective (gl2ZHatToLimit.{u}) :=
  ⟨gl2ZHatToLimit_injective, gl2ZHatToLimit_surjective⟩

/-- **The isomorphism of topological groups `GL₂(ℤ̂) ≃ lim_n GL₂(ℤ/nℤ)`** (LMFDB `gl2.profinite`):
reduction modulo every `n`, a continuous bijection from the compact group `GL₂(ℤ̂)` to the
Hausdorff inverse limit, hence a homeomorphism. -/
noncomputable def gl2ZHatContinuousMulEquiv : GL (Fin 2) (Additive zHat.{u}) ≃ₜ* gl2ZModLimit :=
  letI e : GL (Fin 2) (Additive zHat.{u}) ≃* gl2ZModLimit :=
    MulEquiv.ofBijective _ gl2ZHatToLimit_bijective
  haveI : CompactSpace (Additive zHat.{u}) := inferInstanceAs (CompactSpace zHat.{u})
  haveI : CompactSpace (Matrix (Fin 2) (Fin 2) (Additive zHat.{u})) :=
    inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → Additive zHat.{u}))
  { e with
    continuous_toFun := continuous_gl2ZHatToLimit
    continuous_invFun :=
      continuous_gl2ZHatToLimit.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) }

end Matrix.GeneralLinearGroup
