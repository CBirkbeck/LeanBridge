import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Isogeny.Basic

/-!
# The isogeny class of an elliptic curve

The isogeny class of an elliptic curve `W` over a field `K` is the set of isomorphism classes of
elliptic curves over `K` that are isogenous to `W` over `K`. Isomorphisms of Weierstrass curves over
`K` are the changes of variables `WeierstrassCurve.VariableChange K`, so the isomorphism classes are
their orbits.

Over a number field the isogeny class is finite (Shafarevich), and over `ℚ` it has at most `8`
elements (Kenku). Neither theorem is proved here.

## Main definitions

* `WeierstrassCurve.IsomorphismClass`: the isomorphism classes of Weierstrass curves over `K`.
* `WeierstrassCurve.isogenyClass` (LMFDB `ec.isogeny_class`): the isomorphism classes of the
  elliptic curves over `K` isogenous to a given one.

## Main results

* `WeierstrassCurve.mk_mem_isogenyClass_iff`: the class of an elliptic curve lies in the isogeny
  class of `W` exactly when the curve is isogenous to `W`.
* `WeierstrassCurve.isogenyClass_eq_iff`: two elliptic curves have the same isogeny class exactly
  when they are isogenous.
-/

open MulAction (orbitRel)

namespace WeierstrassCurve

variable (K : Type*) [Field K]

/-- The **isomorphism classes** (LMFDB `ec.isomorphism`) of Weierstrass curves over `K`: the orbits
of the changes of variables `WeierstrassCurve.VariableChange K`, which are the isomorphisms of
Weierstrass curves over `K`. -/
abbrev IsomorphismClass : Type _ :=
  orbitRel.Quotient (VariableChange K) (WeierstrassCurve K)

variable {K} {W W' : WeierstrassCurve K} {c : IsomorphismClass K}

lemma IsomorphismClass.mk_eq_mk_iff :
    (⟦W⟧ : IsomorphismClass K) = ⟦W'⟧ ↔ ∃ C : VariableChange K, C • W' = W :=
  Quotient.eq

variable (W) in
/-- The **isogeny class** (LMFDB `ec.isogeny_class`) of an elliptic curve `W` over `K`: the set of
isomorphism classes of elliptic curves over `K` that are isogenous to `W` over `K`. It contains the
class of `W`, and two elliptic curves have the same isogeny class exactly when they are isogenous
(`isogenyClass_eq_iff`). -/
def isogenyClass : Set (IsomorphismClass K) :=
  Quotient.mk _ '' {W' | W'.IsElliptic ∧ W.IsIsogenous W'}

lemma mem_isogenyClass_iff :
    c ∈ W.isogenyClass ↔ ∃ W' : WeierstrassCurve K, W'.IsElliptic ∧ W.IsIsogenous W' ∧ ⟦W'⟧ = c :=
  ⟨fun ⟨W', h, hc⟩ ↦ ⟨W', h.1, h.2, hc⟩, fun ⟨W', hW', h, hc⟩ ↦ ⟨W', ⟨hW', h⟩, hc⟩⟩

lemma exists_isElliptic_of_mem_isogenyClass (hc : c ∈ W.isogenyClass) :
    ∃ W' : WeierstrassCurve K, W'.IsElliptic ∧ ⟦W'⟧ = c :=
  hc.imp fun _ h ↦ ⟨h.1.1, h.2⟩

lemma isElliptic_of_mk_mem_isogenyClass (hW' : (⟦W'⟧ : IsomorphismClass K) ∈ W.isogenyClass) :
    W'.IsElliptic := by
  rcases hW' with ⟨W'', ⟨hW'', -⟩, h⟩
  rcases IsomorphismClass.mk_eq_mk_iff.mp h with ⟨C, rfl⟩
  rw [← inv_smul_smul C W']
  infer_instance

lemma isogenyClass_smul (C : VariableChange K) : (C • W).isogenyClass = W.isogenyClass := by
  simp only [isogenyClass, smul_isIsogenous_iff]

variable [W'.IsElliptic]

/-- **The class of an elliptic curve lies in the isogeny class of `W` exactly when the curve is
isogenous to `W`**: being isogenous to `W` does not depend on the curve within its isomorphism
class. -/
lemma mk_mem_isogenyClass_iff :
    (⟦W'⟧ : IsomorphismClass K) ∈ W.isogenyClass ↔ W.IsIsogenous W' := by
  grind [isogenyClass, IsomorphismClass.mk_eq_mk_iff, isIsogenous_smul_iff]

variable [W.IsElliptic]

variable (W) in
lemma mk_mem_isogenyClass_self : (⟦W⟧ : IsomorphismClass K) ∈ W.isogenyClass :=
  mk_mem_isogenyClass_iff.mpr <| .refl W

/-- **Two elliptic curves have the same isogeny class exactly when they are isogenous.** -/
lemma isogenyClass_eq_iff : W.isogenyClass = W'.isogenyClass ↔ W.IsIsogenous W' := by
  grind [isogenyClass, mk_mem_isogenyClass_iff, mk_mem_isogenyClass_self, IsIsogenous.symm,
    IsIsogenous.trans]

end WeierstrassCurve
