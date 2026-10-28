import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.Basic

/-!
# Necklaces on the `p`-torsion of an elliptic curve

Let `E` be an elliptic curve over a field `F`, let `p` be a prime and let `E[p]` be the `p`-torsion
of `E` over a separable closure `F^s` of `F`, a vector space over `𝔽_p` on which `Gal(F^s/F)` acts
through the mod-`p` Galois representation. Its cyclic subgroups of order `p` are its lines, the
points of the projective line `ℙ(E[p])`; there are `p + 1` of them when `p` is not the
characteristic of `F`. An **oriented necklace** is a cyclic permutation of these `p + 1` lines, that
is, a `(p + 1)`-cycle, induced by an automorphism of `E[p]`, and a **necklace** is an unordered pair
`{c, c⁻¹}` of mutually inverse oriented necklaces. They are **`F`-rational** if they are stable
under the action of `Gal(F^s/F)` by conjugation. Following Rebolledo and Wuthrich, the LMFDB knowls
`modcurve.xns.remarks` and `modcurve.xns_plus.remarks` describe the non-cuspidal points of the
modular curves `X_ns(p)` and `X_ns⁺(p)`, attached to a non-split Cartan subgroup of `GL₂(𝔽_p)` and
to its normalizer, as the pairs of an elliptic curve and an `F`-rational oriented necklace,
respectively necklace, up to isomorphism over `F^s`. This moduli interpretation needs the modular
curves `X_H` and is not formalised.

The knowls ask only for a cyclic permutation of the lines. For `p ≥ 5` most `(p + 1)`-cycles of the
lines are not induced by automorphisms of `E[p]`: `20` of the `120` six-cycles for `p = 5`, and `84`
of the `5040` eight-cycles for `p = 7`. The stabilizer in `GL(E[p])` of any other cycle, for the
action by conjugation, is not a non-split Cartan subgroup, so the moduli interpretation fails for
them, and the definitions here require the cycle to be induced by an automorphism of `E[p]`. For
`p ≤ 5` these cycles form a single orbit of `p (p - 1)` cycles under conjugation by `GL(E[p])`, the
stabilizer of each being a non-split Cartan subgroup, as the moduli interpretation of `X_ns(p)`
requires. For `p ≥ 7` they form `φ(p + 1) / 2` such orbits, each giving a copy of `X_ns(p)`, and the
moduli interpretation needs one of them to be fixed, a choice that neither the knowls nor these
definitions make.

The LMFDB's cyclic subgroups of order `p` of `E[p]` are indexed here by `ℙ(E[p])`, Mathlib's
`Projectivization`, which `Gal(F^s/F)` acts on through the mod-`p` representation; a subgroup of
order `p` of an `𝔽_p`-vector space is a line, and a line has `p` elements.

## Main definitions

* `WeierstrassCurve.TorsionLine`: the lines of `E[p]`, that is, the points of `ℙ(E[p])`.
* `WeierstrassCurve.torsionLineEquiv`: the lines of `E[p]` are its subgroups of order `p`.
* `WeierstrassCurve.linePerm`: the action of the automorphisms of `E[p]` on its lines.
* `WeierstrassCurve.lineGaloisAction`: the action of `Gal(F^s/F)` on the lines of `E[p]`.
* `WeierstrassCurve.IsOrientedNecklace` and `WeierstrassCurve.IsRationalOrientedNecklace` (LMFDB
  `modcurve.xns.remarks`).
* `WeierstrassCurve.IsNecklace` and `WeierstrassCurve.IsRationalNecklace` (LMFDB
  `modcurve.xns_plus.remarks`).

## Main results

* `WeierstrassCurve.natCard_torsionLine`: if `p` is not the characteristic of `F`, `E[p]` has
  `p + 1` lines.
* `WeierstrassCurve.IsRationalOrientedNecklace.isRationalNecklace`: an `F`-rational oriented
  necklace `c` gives the `F`-rational necklace `{c, c⁻¹}`.
-/

open Equiv
open scoped LinearAlgebra.Projectivization WeierstrassCurve

variable (p : ℕ) [Fact p.Prime]

variable {p} in
lemma Submodule.finrank_eq_one_iff_natCard_eq {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (H : Submodule (ZMod p) V) : Module.finrank (ZMod p) H = 1 ↔ Nat.card H = p := by
  have hp : p.Prime := Fact.out
  have h₁ (_ : Module.Finite (ZMod p) H) : Nat.card H = p ^ Module.finrank (ZMod p) H := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  refine ⟨fun h ↦ (h₁ (Module.finite_of_finrank_eq_succ h)).trans (by rw [h, pow_one]), fun h ↦ ?_⟩
  have : Finite H := Nat.finite_of_card_ne_zero (ne_of_eq_of_ne h hp.ne_zero)
  exact (Nat.pow_eq_self_iff hp.one_lt).mp ((h₁ .of_finite).symm.trans h)

namespace WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq (SeparableClosure F)] (W : WeierstrassCurve F)

/-- The **lines** of the `p`-torsion `E[p]` of `W` over a separable closure `F^s`: the points of the
projective line `ℙ(E[p])` of the `𝔽_p`-vector space `E[p]`, which are its cyclic subgroups of order
`p` (`torsionLineEquiv`). -/
abbrev TorsionLine : Type _ :=
  ℙ (ZMod p) (AddSubgroup.torsionBy (W⁄(SeparableClosure F)).toAffine.Point (p : ℤ))

variable (c : Perm (W.TorsionLine p)) (s : Set (Perm (W.TorsionLine p)))

/-- The lines of `E[p]` are its subgroups of order `p`, which are cyclic: a line is sent to its
underlying subgroup. -/
noncomputable def torsionLineEquiv : W.TorsionLine p ≃
    {C : AddSubgroup (AddSubgroup.torsionBy (W⁄(SeparableClosure F)).toAffine.Point (p : ℤ)) //
    Nat.card C = p} :=
  (Projectivization.equivSubmodule _ _).trans <|
    (AddSubgroup.toZModSubmodule p).symm.toEquiv.subtypeEquiv
      Submodule.finrank_eq_one_iff_natCard_eq

/-- **`E[p]` has `p + 1` lines** if `p` is not the characteristic of `F`, as it is then a plane over
`𝔽_p`. -/
lemma natCard_torsionLine [W.IsElliptic] (hp : (p : SeparableClosure F) ≠ 0) :
    Nat.card (W.TorsionLine p) = p + 1 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rcases (W⁄(SeparableClosure F)).nonempty_basis_torsionBy p hp with ⟨b⟩
  rw [Projectivization.card_of_finrank_two _ _
    (Module.finrank_eq_card_basis b |>.trans (Fintype.card_fin 2)), Nat.card_zmod]

/-- The action of the automorphisms of `E[p]`, the `𝔽_p`-linear ones, on the lines of `E[p]`. -/
noncomputable def linePerm : LinearMap.GeneralLinearGroup (ZMod p)
    (AddSubgroup.torsionBy (W⁄(SeparableClosure F)).toAffine.Point (p : ℤ)) →*
    Perm (W.TorsionLine p) :=
  MulAction.toPermHom _ _

/-- The action of `Gal(F^s/F)` on the lines of `E[p]`, through the mod-`p` Galois representation. -/
noncomputable def lineGaloisAction :
    (SeparableClosure F ≃ₐ[F] SeparableClosure F) →* Perm (W.TorsionLine p) :=
  (W.linePerm p).comp (W.modGaloisRepresentation p)

/-- An **oriented necklace** on `E[p]` (LMFDB `modcurve.xns.remarks`): a cyclic permutation of the
lines of `E[p]`, that is, a cycle moving every line, a `(p + 1)`-cycle when there are `p + 1` lines,
which is induced by an automorphism of `E[p]`. The knowl does not ask for the last condition, but
the moduli interpretation of `X_ns(p)` needs it, and for `p ≥ 7` also a choice among the
`φ(p + 1) / 2` conjugacy classes of such cycles; see the module docstring. -/
def IsOrientedNecklace : Prop :=
  c.IsCycle ∧ (∀ L, c L ≠ L) ∧ c ∈ (W.linePerm p).range

/-- An **`F`-rational oriented necklace** on `E[p]` (LMFDB `modcurve.xns.remarks`): an oriented
necklace stable under the action of `Gal(F^s/F)` by conjugation, that is, commuting with the action
of every Galois automorphism on the lines of `E[p]`. -/
def IsRationalOrientedNecklace : Prop :=
  W.IsOrientedNecklace p c ∧ ∀ σ, Commute (W.lineGaloisAction p σ) c

/-- A **necklace** on `E[p]` (LMFDB `modcurve.xns_plus.remarks`), or unoriented necklace: a pair
`{d, d⁻¹}` of mutually inverse oriented necklaces, that is, of mutually inverse cyclic permutations
of the lines of `E[p]` induced by automorphisms of `E[p]`. -/
def IsNecklace : Prop :=
  ∃ d, W.IsOrientedNecklace p d ∧ s = {d, d⁻¹}

/-- An **`F`-rational necklace** on `E[p]` (LMFDB `modcurve.xns_plus.remarks`): a necklace
`{d, d⁻¹}` stable under the action of `Gal(F^s/F)` by conjugation, so that every Galois
automorphism conjugates `d` to `d` or to `d⁻¹`. -/
def IsRationalNecklace : Prop :=
  W.IsNecklace p s ∧ ∀ σ, ∀ d ∈ s, W.lineGaloisAction p σ * d * (W.lineGaloisAction p σ)⁻¹ ∈ s

variable {W p c}

lemma IsOrientedNecklace.inv (hc : W.IsOrientedNecklace p c) : W.IsOrientedNecklace p c⁻¹ :=
  ⟨hc.1.inv, fun L h ↦ hc.2.1 L (Perm.inv_eq_iff_eq.mp h).symm, inv_mem hc.2.2⟩

/-- **An `F`-rational oriented necklace `c` gives the `F`-rational necklace `{c, c⁻¹}`.** -/
lemma IsRationalOrientedNecklace.isRationalNecklace (hc : W.IsRationalOrientedNecklace p c) :
    W.IsRationalNecklace p {c, c⁻¹} := by
  refine ⟨⟨c, hc.1, rfl⟩, fun σ d hd ↦ ?_⟩
  rcases hd with rfl | rfl
  · exact Or.inl ((hc.2 σ).eq ▸ mul_inv_cancel_right _ _)
  · exact Or.inr ((hc.2 σ).inv_right.eq ▸ mul_inv_cancel_right _ _)

end WeierstrassCurve
