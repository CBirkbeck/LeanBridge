import Mathlib.GroupTheory.Sylow
import TauCeti.GroupTheory.GroupAction.Transitive

/-!
# The centralizer of a transitive permutation group

Let a finite group `Γ` act transitively on a set `X`, with image `G` in the symmetric group
`Sym(X)`, and let `H = Γ_x` be the stabilizer of a point `x`. A permutation `c` of `X` commuting
with `G` is determined by `c x`, a point fixed by `H`, and every point fixed by `H` is `c x` for
such a `c`. The points fixed by `H` are the `g • x` with `g` in the normalizer `N_Γ(H)`, and
`g • x = g' • x` exactly when `g` and `g'` differ by `H`. So the centralizer `C_{Sym(X)}(G)` has
order `[N_Γ(H) : H]`: this is the group-theoretic count of the automorphisms of the stem field of a
Galois extension with Galois group `G` (LMFDB `gg.field_automorphisms`).

## Main results

* `MulAction.card_centralizer_eq_card_fixedPoints`: `|C_{Sym(X)}(G)|` is the number of points
  fixed by `H`.
* `MulAction.card_fixedPoints_stabilizer_eq_relIndex`: that number is `[N_Γ(H) : H]`.
* `MulAction.card_centralizer_eq_relIndex`: `|C_{Sym(X)}(G)| = [N_Γ(H) : H]`.
-/

open Subgroup

open TauCeti (quotientStabilizerEquiv quotientStabilizerEquiv_smul)

namespace MulAction

variable {Γ X : Type*} [Group Γ] [MulAction Γ X]

lemma smul_apply_of_mem_centralizer {c : Equiv.Perm X} (hc : c ∈ centralizer (toPermHom Γ X).range)
    (g : Γ) (y : X) : c (g • y) = g • c y :=
  (congrArg (· y) (mem_centralizer_iff.mp hc (toPermHom Γ X g) ⟨g, rfl⟩)).symm

variable [IsPretransitive Γ X] (x : X) [Finite Γ]

/-- **The points fixed by the stabilizer `H` of a point in a transitive action of a finite group
`Γ` are counted by `[N_Γ(H) : H]`**: they are the images of the cosets `g H` fixed by `H`, which
are those with `g` in the normalizer of `H`. -/
lemma card_fixedPoints_stabilizer_eq_relIndex : Nat.card (fixedPoints (stabilizer Γ x) X) =
    (stabilizer Γ x).relIndex (normalizer (stabilizer Γ x)) := by
  refine (Nat.card_congr <| ((quotientStabilizerEquiv Γ x).subtypeEquiv fun q ↦ ?_).symm).trans
    (Nat.card_congr (Sylow.fixedPointsMulLeftCosetsEquivQuotient _))
  simp only [mem_fixedPoints, Subgroup.smul_def]
  refine forall_congr' fun h ↦ ?_
  rw [← quotientStabilizerEquiv_smul, (quotientStabilizerEquiv Γ x).injective.eq_iff]

/-- **The centralizer of a transitive permutation group has as many elements as there are points
fixed by a point stabilizer**: for a transitive action of a finite group `Γ` on `X`, a permutation
of `X` commuting with the image of `Γ` is determined by the image of `x`, which can be any point
fixed by the stabilizer of `x`. -/
lemma card_centralizer_eq_card_fixedPoints :
    Nat.card (centralizer ((toPermHom Γ X).range : Set (Equiv.Perm X))) =
      Nat.card (fixedPoints (stabilizer Γ x) X) := by
  have : Finite X := Finite.of_surjective _ (surjective_smul Γ x)
  refine Nat.card_congr (Equiv.ofBijective (fun c ↦ ⟨(c : Equiv.Perm X) x, ?_⟩) ⟨?_, ?_⟩)
  · exact mem_fixedPoints.mpr fun h ↦
      (smul_apply_of_mem_centralizer c.2 h x).symm.trans (congrArg (c : Equiv.Perm X) h.2)
  · intro c c' h
    have h' : (c : Equiv.Perm X) x = (c' : Equiv.Perm X) x := congrArg Subtype.val h
    refine Subtype.ext <| Equiv.ext fun y ↦ ?_
    rcases exists_smul_eq Γ x y with ⟨g, rfl⟩
    rw [smul_apply_of_mem_centralizer c.2, smul_apply_of_mem_centralizer c'.2, h']
  · rintro ⟨y, hy⟩
    let f : X → X := fun z ↦ (exists_smul_eq Γ x z).choose • y
    have hf (g : Γ) : f (g • x) = g • y := by
      have h : g⁻¹ * (exists_smul_eq Γ x (g • x)).choose ∈ stabilizer Γ x := by
        rw [mem_stabilizer_iff, mul_smul, (exists_smul_eq Γ x (g • x)).choose_spec, inv_smul_smul]
      simpa [mul_smul] using congrArg (g • ·) (mem_fixedPoints.mp hy ⟨_, h⟩)
    have hle : stabilizer Γ y ≤ stabilizer Γ x := by
      rcases exists_smul_eq Γ x y with ⟨σ, rfl⟩
      refine (Subgroup.eq_of_le_of_card_ge (fun h hh ↦ mem_fixedPoints.mp hy ⟨h, hh⟩) ?_).ge
      rw [stabilizer_smul_eq_stabilizer_map_conj, card_map_of_injective (MulAut.conj σ).injective]
    have hinj : Function.Injective f := by
      intro z z' h
      rcases exists_smul_eq Γ x z with ⟨g, rfl⟩
      rcases exists_smul_eq Γ x z' with ⟨g', rfl⟩
      rw [hf, hf] at h
      have h' : g⁻¹ * g' ∈ stabilizer Γ y := by
        rw [mem_stabilizer_iff, mul_smul, ← h, inv_smul_smul]
      have h'' : g⁻¹ * g' ∈ stabilizer Γ x := hle h'
      rw [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff] at h''
      exact h''.symm
    refine ⟨⟨Equiv.ofBijective f hinj.bijective_of_finite, ?_⟩, ?_⟩
    · refine mem_centralizer_iff.mpr ?_
      rintro _ ⟨k, rfl⟩
      ext z
      rcases exists_smul_eq Γ x z with ⟨g, rfl⟩
      simp [hf, smul_smul]
    · ext
      simpa using hf 1

/-- **The centralizer of a transitive permutation group** (LMFDB `gg.field_automorphisms`): for a
transitive action of a finite group `Γ` on `X`, the centralizer of the image of `Γ` in `Sym(X)` has
order `[N_Γ(H) : H]`, for `H` the stabilizer of a point. -/
lemma card_centralizer_eq_relIndex :
    Nat.card (centralizer ((toPermHom Γ X).range : Set (Equiv.Perm X))) =
      (stabilizer Γ x).relIndex (normalizer (stabilizer Γ x)) :=
  (card_centralizer_eq_card_fixedPoints x).trans (card_fixedPoints_stabilizer_eq_relIndex x)

end MulAction
